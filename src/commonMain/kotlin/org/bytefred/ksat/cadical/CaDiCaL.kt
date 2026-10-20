package org.bytefred.ksat.cadical

import org.bytefred.ksat.ExternalPropagation
import org.bytefred.ksat.ExternalPropagator
import org.bytefred.ksat.FixedAssignmentListener
import org.bytefred.ksat.FixedListening
import org.bytefred.ksat.ForcedPhases
import org.bytefred.ksat.OutBoolean
import org.bytefred.ksat.SatResult
import org.bytefred.ksat.SatSolver
import org.bytefred.ksat.Traceable

/**
 * Kotlin port of CaDiCaL's core CDCL solver by Manfred Scheucher, 2026.
 * Upstream CaDiCaL: 2.1.3 (github.com/arminbiere/cadical, VERSION 2.1.3,
 * master @ f13d74439a5b5c963ac5b02d05ce93a8098018b8); MIT, (c) 2016-2024 Armin Biere and contributors.
 *
 * Only the CDCL core is ported, with all inprocessing off, so the run is plain and
 * deterministic and can be shadow-tested against the C. The instrumented reference is
 * ../shadow/cadical-c/cadical_trace.cc; the code follows its structure, not idiomatic Kotlin,
 * so the two line up.
 *
 * Ported (as the C reference documents each part):
 *   - watched literals with blocking literals and Ian Gent's saved-position search
 *     (propagate.cpp);
 *   - 1st-UIP conflict analysis via CaDiCaL's 'open'-counter loop over the trail
 *     (analyze.cpp); glue/LBD = distinct decision levels touched - 1;
 *   - recursive clause minimization with poison/removable/keep flags (minimize.cpp);
 *   - EVSIDS scores in a binary max-heap (stable mode) and the VMTF 'bumped' queue
 *     (focused mode) (score.cpp/queue.hpp);
 *   - bias-corrected EMAs of the glue (ema.cpp) driving Glucose restarts; stabilizing
 *     phases toggle stable/focused, with reluctant (Luby) doubling in stable mode
 *     (restart.cpp);
 *   - LBD-tiered reduce: keep tier1 (glue<=2) and recently-used tier2 (glue<=6), sort the
 *     rest by (glue,size), drop a fraction (reduce.cpp);
 *   - phase saving with target/best phases updated on backtrack (backtrack.cpp, phases.cpp);
 *   - IPASIR-UP external propagator (external_propagate.cpp + its hooks in analyze/minimize/
 *     assume/backtrack/decide/reduce/clause.cpp); every hook is guarded like upstream, so with
 *     no propagator connected the run (and the trace) is unchanged;
 *   - forced decision phases (Solver::phase/unphase, phases.cpp, decide.cpp) and the
 *     FixedAssignmentListener (Solver::connect_fixed_listener, flags.cpp mark_fixed); with no
 *     phase forced and no listener connected the run (and the trace) is unchanged.
 *
 * Off (so C and Kotlin match): chronological backtracking, on-the-fly self-subsumption,
 * clause shrinking beyond recursive minimize, proofs, rephasing, and all inprocessing.
 * The C reference header lists the full set.
 *
 * Floating point: EVSIDS scores (`stab`) and the glue EMAs are `double`. JVM `Double` is
 * IEEE-754, the same as C's, and every score/EMA update runs in the same order, so the trace
 * matches at L1 (byte-for-byte). Precision is a knob, as in MiniSat: [ActivityPrecision.FLOAT64]
 * matches the C reference (default); [ActivityPrecision.FLOAT32] rounds every score write via
 * toFloat().toDouble(), for a hypothetical float build or standalone experiments.
 */
enum class ActivityPrecision { FLOAT32, FLOAT64 }

class CaDiCaL(
    numVarsHint: Int,
    private val activityPrecision: ActivityPrecision = ActivityPrecision.FLOAT64,
    // TEST-ONLY knobs for standalone experiments: lower them to trigger REDUCE/RESTART/
    // stabilization on small CNFs. Defaults == upstream CaDiCaL. NOTE: the C reference
    // (cadical_trace.cc) has NO matching env counterpart -- its reduce/restart/stabilize
    // intervals are fixed `const`s and only LSTRACE is env-read -- so these knobs must be
    // left at their defaults for any run shadowed against the golden C traces (which they
    // are in ShadowTraceFilesTest). They exist purely for Kotlin-side exploration.
    reduceIntInit: Long = 25L,
    restartIntInit: Long = 2L,
    stabilizeInit: Long = 1000L,
) : SatSolver, Traceable, ExternalPropagation, FixedListening, ForcedPhases {

    // ---- options (core configuration; see the C reference header) ----
    private companion object {
        const val OPT_score = true          // use EVSIDS in stable mode
        const val OPT_stabilize = true
        const val OPT_stabilizefactor = 200 // percent (unused with reluctant path)
        const val OPT_reluctant = true
        const val OPT_reluctantint = 1024L
        const val OPT_reluctantmax = 1048576L
        const val OPT_restart = true
        const val OPT_restartmarginfocused = 10 // percent
        const val OPT_restartmarginstable = 25  // percent
        const val OPT_reduce = true
        const val OPT_reducetarget = 75         // percent
        const val OPT_reducetier1glue = 2
        const val OPT_reducetier2glue = 6
        const val OPT_minimize = true
        const val OPT_minimizedepth = 1000
        const val OPT_bump = true
        const val OPT_scorefactor = 950         // per mille
        const val OPT_phase = true              // initial phase positive
        const val OPT_target = 1                // target phases (stable only)
        const val OPT_emagluefast = 33.0
        const val OPT_emaglueslow = 1e5
        const val OPT_exteagerreasons = true    // eagerly ask for all reasons (upstream default 1)
        const val OPT_exteagerrecalc = true     // recalculate levels after eager reasons (default 1)
    }

    private val OPT_stabilizeinit: Long = stabilizeInit
    private val OPT_restartint: Long = restartIntInit
    private val OPT_reduceint: Long = reduceIntInit

    /** Round an EVSIDS score to the configured precision (C `double` vs experimental `float`). */
    private fun scoreRound(x: Double): Double =
        if (activityPrecision == ActivityPrecision.FLOAT32) x.toFloat().toDouble() else x

    override var numVars: Int = 0
        private set

    // ---- trace sink ----
    private var trace: ((String) -> Unit)? = null
    override fun setTraceSink(sink: ((String) -> Unit)?) { trace = sink }
    private inline fun tr(line: String) { trace?.invoke(line) }

    // =========================================================================
    // EMA (ema.cpp): ADAM-style bias-corrected exponential moving average.
    // =========================================================================
    private class Ema {
        var value = 0.0
        var biased = 0.0
        var alpha = 0.0
        var beta = 0.0
        var exp = 0.0

        constructor()
        constructor(a: Double) {
            alpha = a; beta = 1 - a; exp = if (a != 1.0) 1.0 else 0.0
        }

        fun update(y: Double) {
            val oldBiased = biased
            val delta = y - oldBiased
            val scaledDelta = alpha * delta
            val newBiased = oldBiased + scaledDelta
            biased = newBiased
            val oldExp = exp
            if (oldExp != 0.0) {
                val newExp = oldExp * beta
                exp = newExp
                val div = 1 - newExp
                value = newBiased / div
            } else {
                value = newBiased
            }
        }

        fun copyFrom(o: Ema) { value = o.value; biased = o.biased; alpha = o.alpha; beta = o.beta; exp = o.exp }
    }

    private fun initEma(window: Double): Ema = Ema(1.0 / window)

    // =========================================================================
    // Clauses. The C reference uses heap-allocated Clause* with pointer identity; we
    // mirror that with an object arena of parallel columns indexed by an Int handle
    // (a "clause ref" = index). Clause literals are the signed DIMACS lits, as in C.
    // A ref of -1 means "no clause"; DECISION is a sentinel for a decision reason.
    // =========================================================================
    private var cRedundant = BooleanArray(64)
    private var cGarbage = BooleanArray(64)
    private var cReason = BooleanArray(64)   // currently a reason clause (protect from reduce)
    private var cGlue = IntArray(64)
    private var cUsed = IntArray(64)
    private var cPos = IntArray(64)          // Gent saved search position
    private var cSize = IntArray(64)
    private var cLits = arrayOfNulls<IntArray>(64)
    private var cCount = 0

    private val CREF_NONE = -1
    private val CREF_DECISION = -2           // decision_reason sentinel
    private val CREF_EXTERNAL = -3           // external_reason sentinel (reason not yet learned)

    private fun cEnsure(cap: Int) {
        if (cap <= cRedundant.size) return
        var n = cRedundant.size
        while (n < cap) n *= 2
        cRedundant = cRedundant.copyOf(n)
        cGarbage = cGarbage.copyOf(n)
        cReason = cReason.copyOf(n)
        cGlue = cGlue.copyOf(n)
        cUsed = cUsed.copyOf(n)
        cPos = cPos.copyOf(n)
        cSize = cSize.copyOf(n)
        cLits = cLits.copyOf(n)
    }

    private fun newClauseArena(lits: IntArray, redundant: Boolean, glue: Int): Int {
        cEnsure(cCount + 1)
        val cr = cCount++
        cRedundant[cr] = redundant
        cGarbage[cr] = false
        cReason[cr] = false
        cGlue[cr] = glue
        cUsed[cr] = if (redundant) 1 else 0
        cPos[cr] = 2
        cSize[cr] = lits.size
        cLits[cr] = lits.copyOf()
        return cr
    }

    private fun lits(cr: Int): IntArray = cLits[cr]!!

    // =========================================================================
    // Watches. wtab is indexed by literal offset: litoff(l) = 2*|l| + (l<0).
    // Each watcher stores (clauseRef, blockingLit, bin).
    // =========================================================================
    private var wClause = arrayOfNulls<IntArrayList>(0)
    private var wBlit = arrayOfNulls<IntArrayList>(0)
    private var wBin = arrayOfNulls<BooleanList>(0)

    private fun litoff(lit: Int): Int = 2 * vidx(lit) + (if (lit < 0) 1 else 0)

    private fun ensureWatchTables(size: Int) {
        if (wClause.size >= size) return
        val nc = arrayOfNulls<IntArrayList>(size)
        val nb = arrayOfNulls<IntArrayList>(size)
        val nn = arrayOfNulls<BooleanList>(size)
        for (i in wClause.indices) { nc[i] = wClause[i]; nb[i] = wBlit[i]; nn[i] = wBin[i] }
        for (i in wClause.size until size) { nc[i] = IntArrayList(); nb[i] = IntArrayList(); nn[i] = BooleanList() }
        wClause = nc; wBlit = nb; wBin = nn
    }

    private fun wc(lit: Int): IntArrayList = wClause[litoff(lit)]!!
    private fun wbl(lit: Int): IntArrayList = wBlit[litoff(lit)]!!
    private fun wbn(lit: Int): BooleanList = wBin[litoff(lit)]!!

    // =========================================================================
    // Per-variable state (index 1..max_var, 0 unused).
    // =========================================================================
    private var maxVar = 0
    private var vals = signedCharArray(1)        // {-1,0,+1} per variable index
    private var vLevel = IntArray(1)
    private var vTrail = IntArray(1)
    private var vReason = IntArray(1) { CREF_NONE }   // reason clause ref, or CREF_NONE

    // trail / control
    private val trail = IntArrayList()
    // control (decision levels): decision lit, trail start, seen_count, seen_trail per frame
    private val ctlDecision = IntArrayList()
    private val ctlTrail = IntArrayList()
    private val ctlSeenCount = IntArrayList()
    private val ctlSeenTrail = IntArrayList()
    private var level = 0
    private var propagated = 0
    private var numAssigned = 0
    private var conflict = CREF_NONE

    // clauses list (all clauses, irredundant + redundant), as arena refs
    private val clauses = IntArrayList()

    // EVSIDS scores (stable mode)
    private var stab = DoubleArray(1)
    private var scoreInc = 1.0
    // binary max-heap over variables by score
    private val heapArr = IntArrayList()
    private var heapPos = IntArray(1) { HEAP_INVALID }

    // VMTF queue (focused mode)
    private var linkPrev = IntArray(1)
    private var linkNext = IntArray(1)
    private var qFirst = 0
    private var qLast = 0
    private var qUnassigned = 0
    private var qBumped = 0L
    private var btab = LongArray(1)
    private var bumpedCounter = 0L

    // phases
    private var phaseSaved = signedCharArray(1)
    private var phaseTarget = signedCharArray(1)
    private var phaseBest = signedCharArray(1)
    private var phaseForced = signedCharArray(1) // phases.forced (Solver::phase)
    private var targetAssigned = 0
    private var bestAssigned = 0
    private var noConflictUntil = 0

    // analyze scratch
    private var seen = signedCharArray(1)
    private val analyzed = IntArrayList()
    private val levelsSeen = IntArrayList()
    private val clause = IntArrayList()           // learned clause literals
    private var removable = signedCharArray(1)
    private var poison = signedCharArray(1)
    private var keepFlag = signedCharArray(1)
    private val minimized = IntArrayList()

    // failed-assumption core (IPASIR failed(), assume.cpp failing()). Per-variable bitmask
    // with upstream `bign` semantics: bit value 1 == positive phase failed, 2 == negative
    // phase failed (bign(lit) = 1 + (lit<0)). Computed eagerly at the UNSAT-under-assumptions
    // exit (see solveLoop) because solve() rolls the trail back to level 0 right after, which
    // would destroy the level/reason state failing() needs. `failingSeen` is BFS scratch,
    // cleared after use. `failedValid` guards failed() against stale/absent cores.
    private var failedBits = signedCharArray(1)
    private var failingSeen = signedCharArray(1)
    private var failedValid = false
    // solver.cpp state(): UNSATISFIED after a solve returned 20, until the next add/solve.
    private var unsatisfiedState = false
    // upstream `marked_failed` (internal.cpp ctor: true): decide() clears it when an assumption is
    // falsified (decide.cpp), learning the empty clause sets it (analyze.cpp learn_empty_clause,
    // clause.cpp falsified original). failing() only runs while it is false.
    private var markedFailed = true

    // IPASIR-UP state (internal.hpp / external.hpp). `relevantTab` is Internal::relevanttab
    // (observation reference counts), `isObserved` is External::is_observed; with the identity
    // e2i map both are indexed by the DIMACS variable. `private_steps` is not ported: only
    // lucky phases / local search / lookahead / preprocessing set it, none of which exist here.
    // `did_external_prop` is not ported either: upstream only reads it in a backtrack assert.
    private var propagator: ExternalPropagator? = null   // External::propagator
    private var fixedListener: FixedAssignmentListener? = null // External::fixed_listener
    private var externalProp = false
    private var externalPropIsLazy = true
    private var forcedBacktAllowed = false
    private var newestClause = CREF_NONE
    private var forceNoBacktrack = false
    private var fromPropagator = false
    private var extClauseForgettable = false
    private val extClauseForgettableOut = OutBoolean()
    private var notified = 0
    private var relevantTab = IntArray(1)
    private var isObserved = BooleanArray(1)
    private val extOriginal = IntArrayList()  // Internal::original while reading an external clause
    // Solver state SOLVING (REQUIRE_VALID_STATE vs REQUIRE_VALID_OR_SOLVING_STATE in solver.cpp).
    private var solving = false

    // averages / restarts / reduce
    private var glueFast = Ema()
    private var glueSlow = Ema()
    private var stable = false
    private var conflicts = 0L
    private var restarts = 0L
    private var reductions = 0L
    private var stabphases = 0L
    private var limRestart = 0L
    private var limReduce = 0L
    private var limStabilize = 0L
    private var lastStabilizeConflicts = 0L
    // reluctant doubling (Luby) for stable restarts
    private var relU = 1L
    private var relV = 1L
    private var relPeriod = 0L
    private var relTrigger = false
    private var incStabilizeSet = false
    private var incStabilize = 0L

    private var unsat = false
    private var iterating = false

    // model (per variable index 1..max_var)
    private var model = signedCharArray(1)

    // averages swap on mode switch
    private var averagesSwapped = false
    private val savedGlueFast = Ema()
    private val savedGlueSlow = Ema()

    init {
        // variable 0 is unused (1-based like CaDiCaL). Root control frame.
        ctlDecision.add(0); ctlTrail.add(0); ctlSeenCount.add(0); ctlSeenTrail.add(0)
        // reserve numVarsHint capacity but create variables lazily.
        val cap = maxOf(numVarsHint + 1, 1)
        ensureVarArrays(cap)
    }

    // =========================================================================
    // literal / watch helpers
    // =========================================================================
    private fun vidx(lit: Int): Int = if (lit < 0) -lit else lit
    private fun valOfLit(lit: Int): Int {
        val v = vals[vidx(lit)].toInt()
        return if (lit < 0) -v else v
    }
    private fun valOfVar(idx: Int): Int = vals[idx].toInt()

    // =========================================================================
    // heap (max-heap by score, heap.hpp)
    // =========================================================================
    private fun heapContains(e: Int): Boolean {
        if (e >= heapPos.size) return false
        return heapPos[e] != HEAP_INVALID
    }
    private fun heapLess(a: Int, b: Int): Boolean {
        // 'less' means a is worse. Max-heap keeps larger score on top; tie-break larger index.
        if (stab[a] < stab[b]) return true
        if (stab[a] > stab[b]) return false
        return a < b
    }
    private fun heapExchange(a: Int, b: Int) {
        val i = heapPos[a]; val j = heapPos[b]
        val ta = heapArr[i]; heapArr[i] = heapArr[j]; heapArr[j] = ta
        heapPos[a] = j; heapPos[b] = i
    }
    private fun heapUp(e: Int) {
        var p: Int
        while (heapPos[e] > 0) {
            p = heapArr[(heapPos[e] - 1) / 2]
            if (!heapLess(p, e)) break
            heapExchange(p, e)
        }
    }
    private fun heapDown(e: Int) {
        while (2 * heapPos[e] + 1 < heapArr.size) {
            var c = heapArr[2 * heapPos[e] + 1]
            if (2 * heapPos[e] + 2 < heapArr.size) {
                val r = heapArr[2 * heapPos[e] + 2]
                if (heapLess(c, r)) c = r
            }
            if (!heapLess(e, c)) break
            heapExchange(e, c)
        }
    }
    private fun heapPush(e: Int) {
        val i = heapArr.size
        heapArr.add(e)
        heapPos[e] = i
        heapUp(e)
        heapDown(e)
    }
    private fun heapFront(): Int = heapArr[0]
    private fun heapPop(): Int {
        val res = heapArr[0]; val last = heapArr[heapArr.size - 1]
        if (heapArr.size > 1) heapExchange(res, last)
        heapPos[res] = HEAP_INVALID
        heapArr.removeLast()
        if (heapArr.size > 1) heapDown(last)
        return res
    }
    private fun heapUpdate(e: Int) { heapUp(e); heapDown(e) }

    // =========================================================================
    // VMTF queue
    // =========================================================================
    private fun updateQueueUnassigned(idx: Int) {
        qUnassigned = idx
        qBumped = btab[idx]
    }
    private fun qDequeue(idx: Int) {
        val prev = linkPrev[idx]; val next = linkNext[idx]
        if (prev != 0) linkNext[prev] = next else qFirst = next
        if (next != 0) linkPrev[next] = prev else qLast = prev
    }
    private fun qEnqueue(idx: Int) {
        linkPrev[idx] = qLast
        if (qLast != 0) linkNext[qLast] = idx else qFirst = idx
        qLast = idx
        linkNext[idx] = 0
    }
    private fun initEnqueue(idx: Int) {
        linkNext[idx] = 0
        if (qLast != 0) linkNext[qLast] = idx else qFirst = idx
        btab[idx] = ++bumpedCounter
        linkPrev[idx] = qLast
        qLast = idx
        updateQueueUnassigned(qLast)
    }

    private fun useScores(): Boolean = OPT_score && stable

    // =========================================================================
    // new variable (lazy)
    // =========================================================================
    private fun ensureVarArrays(cap: Int) {
        if (vals.size >= cap) return
        var n = vals.size
        while (n < cap) n *= 2
        vals = vals.copyOf(n)
        vLevel = vLevel.copyOf(n)
        vTrail = vTrail.copyOf(n)
        vReason = vReason.copyOf(n).also { for (i in vReason.size until n) it[i] = CREF_NONE }
        stab = stab.copyOf(n)
        heapPos = heapPos.copyOf(n).also { for (i in heapPos.size until n) it[i] = HEAP_INVALID }
        linkPrev = linkPrev.copyOf(n)
        linkNext = linkNext.copyOf(n)
        btab = btab.copyOf(n)
        phaseSaved = phaseSaved.copyOf(n)
        phaseTarget = phaseTarget.copyOf(n)
        phaseBest = phaseBest.copyOf(n)
        phaseForced = phaseForced.copyOf(n)
        seen = seen.copyOf(n)
        removable = removable.copyOf(n)
        poison = poison.copyOf(n)
        keepFlag = keepFlag.copyOf(n)
        failedBits = failedBits.copyOf(n)
        failingSeen = failingSeen.copyOf(n)
        relevantTab = relevantTab.copyOf(n)
        isObserved = isObserved.copyOf(n)
    }

    private fun newVar() {
        val idx = ++maxVar
        ensureVarArrays(idx + 1)
        vals[idx] = 0
        vLevel[idx] = 0
        vTrail[idx] = 0
        vReason[idx] = CREF_NONE
        ensureWatchTables(2 * (maxVar + 1))
        stab[idx] = 0.0
        heapPos[idx] = HEAP_INVALID
        btab[idx] = 0
        phaseSaved[idx] = 0
        phaseTarget[idx] = 0
        phaseBest[idx] = 0
        phaseForced[idx] = 0
        seen[idx] = 0
        removable[idx] = 0
        poison[idx] = 0
        keepFlag[idx] = 0
        failedBits[idx] = 0
        failingSeen[idx] = 0
        relevantTab[idx] = 0
        isObserved[idx] = false
        // register in both structures (queue always, heap always) so both modes work
        initEnqueue(idx)
        heapPush(idx)
        numVars = maxVar
    }
    private fun ensureVar(idx: Int) {
        while (maxVar < idx) newVar()
    }

    // =========================================================================
    // scores (EVSIDS)
    // =========================================================================
    private fun evsidsLimitHit(s: Double): Boolean = s > 1e150
    private fun rescaleVariableScores() {
        var divider = scoreInc
        for (idx in 1..maxVar) {
            val tmp = stab[idx]
            if (tmp > divider) divider = tmp
        }
        val factor = 1.0 / divider
        for (idx in 1..maxVar) stab[idx] = scoreRound(stab[idx] * factor)
        scoreInc *= factor
    }
    private fun bumpVariableScore(lit: Int) {
        val idx = vidx(lit)
        var oldScore = stab[idx]
        var newScore = scoreRound(oldScore + scoreInc)
        if (evsidsLimitHit(newScore)) {
            rescaleVariableScores()
            oldScore = stab[idx]
            newScore = scoreRound(oldScore + scoreInc)
        }
        stab[idx] = newScore
        if (heapContains(idx)) heapUpdate(idx)
    }
    private fun bumpVariableScoreInc() {
        val f = 1e3 / OPT_scorefactor.toDouble()
        var newScoreInc = scoreInc * f
        if (evsidsLimitHit(newScoreInc)) {
            rescaleVariableScores()
            newScoreInc = scoreInc * f
        }
        scoreInc = newScoreInc
    }

    // VMTF bump
    private fun bumpQueue(lit: Int) {
        val idx = vidx(lit)
        if (linkNext[idx] == 0) return
        qDequeue(idx)
        qEnqueue(idx)
        btab[idx] = ++bumpedCounter
        if (vals[idx].toInt() == 0) updateQueueUnassigned(idx)
    }
    private fun bumpVariable(lit: Int) {
        if (useScores()) bumpVariableScore(lit) else bumpQueue(lit)
    }
    private fun bumpedOf(lit: Int): Long = btab[vidx(lit)]

    private fun bumpVariables() {
        if (!useScores()) {
            // stable sort analyzed by bumped ascending -- CaDiCaL bumps in queue order.
            stableSortByBumped(analyzed)
        }
        for (t in 0 until analyzed.size) bumpVariable(analyzed[t])
        if (useScores()) bumpVariableScoreInc()
    }

    /** Stable insertion sort of [list] by bumped stamp ascending (matches std::stable_sort). */
    private fun stableSortByBumped(list: IntArrayList) {
        val a = list.toArray()
        for (i in 1 until a.size) {
            val key = a[i]; val kb = bumpedOf(key)
            var j = i - 1
            while (j >= 0 && bumpedOf(a[j]) > kb) { a[j + 1] = a[j]; j-- }
            a[j + 1] = key
        }
        list.clear()
        for (x in a) list.add(x)
    }

    // =========================================================================
    // assign
    // =========================================================================
    // propagate.cpp search_assign; with [originalUnit] it is clause.cpp assign_original_unit
    // (only addClauseInternal passes it). A learned unit (analyze: driving clause CREF_NONE)
    // is a search_assign at level 0 and takes the learn_unit_clause route.
    private fun assign(lit: Int, reasonIn: Int, rc: Char, originalUnit: Boolean = false) {
        val idx = vidx(lit)
        var reason = reasonIn
        val fromExternal = reasonIn == CREF_EXTERNAL
        val litLevel: Int
        if (reason == CREF_NONE) {
            litLevel = 0 // unit: always fixed at level 0 (makes a post-solve added unit survive backtrack(0); see addClauseInternal)
        } else if (reason == CREF_DECISION) {
            litLevel = level
            reason = CREF_NONE
        } else {
            // no chrono: assignment level == current level (also for CREF_EXTERNAL, whose
            // reason is unknown, exactly as upstream search_assign assumes)
            litLevel = level
        }
        val actualReason = if (litLevel == 0) CREF_NONE else reason
        vLevel[idx] = litLevel
        vTrail[idx] = trail.size
        vReason[idx] = actualReason
        numAssigned++
        // search_assign: `if (!lit_level && !from_external) learn_unit_clause (lit);`
        // (before set_val). assign_original_unit calls mark_fixed after the trail push instead.
        if (!originalUnit && litLevel == 0 && !fromExternal) learnUnitClause(lit)
        check(litLevel != 0 || !fromExternal) { "external propagation assigned at the root" } // propagate.cpp:146
        val tmp: Byte = if (lit < 0) (-1).toByte() else 1.toByte()
        vals[idx] = tmp
        phaseSaved[idx] = tmp
        trail.add(lit)
        tr("ASSIGN $lit reason=$rc")
        if (originalUnit) markFixed(lit) // clause.cpp assign_original_unit
    }

    // analyze.cpp learn_unit_clause: the checker / LRAT unit ids / proof are not ported, which
    // leaves mark_fixed.
    private fun learnUnitClause(lit: Int) {
        check(!unsat) { "learn_unit_clause: already unsat" } // analyze.cpp assert (!unsat)
        markFixed(lit)
    }

    // flags.cpp mark_fixed: only the fixed-listener notification is ported (Flags status and
    // the fixed/active stats do not exist here; Internal::fixed reads the root-level value).
    // externalize is the identity (DIMACS var N == internal idx N).
    private fun markFixed(lit: Int) {
        val listener = fixedListener
        if (listener != null) {
            val elit = lit
            check(elit != 0) { "mark_fixed: zero literal" } // flags.cpp assert (elit)
            listener.notifyFixedAssignment(elit)
        }
    }

    private fun newTrailLevel(lit: Int) {
        level++
        ctlDecision.add(lit); ctlTrail.add(trail.size); ctlSeenCount.add(0); ctlSeenTrail.add(trail.size)
    }

    // =========================================================================
    // watch
    // =========================================================================
    private fun watchLiteral(lit: Int, blit: Int, cr: Int) {
        wc(lit).add(cr); wbl(lit).add(blit); wbn(lit).add(cSize[cr] == 2)
    }
    private fun watchClause(cr: Int) {
        val l0 = lits(cr)[0]; val l1 = lits(cr)[1]
        watchLiteral(l0, l1, cr)
        watchLiteral(l1, l0, cr)
    }
    private fun removeWatch(lit: Int, cr: Int) {
        val a = wc(lit); val b = wbl(lit); val c = wbn(lit)
        var i = 0
        while (i < a.size) {
            if (a[i] == cr) { a.removeAt(i); b.removeAt(i); c.removeAt(i); return }
            i++
        }
    }
    private fun unwatchClause(cr: Int) {
        removeWatch(lits(cr)[0], cr)
        removeWatch(lits(cr)[1], cr)
    }

    // =========================================================================
    // new clause
    // =========================================================================
    private fun newClause(litsIn: IntArray, redundant: Boolean, glue: Int): Int {
        val cr = newClauseArena(litsIn, redundant, glue)
        clauses.add(cr)
        if (cSize[cr] >= 2) watchClause(cr)
        return cr
    }

    // =========================================================================
    // propagate (propagate.cpp)
    // =========================================================================
    private fun propagate(): Boolean {
        while (conflict == CREF_NONE && propagated != trail.size) {
            val lit = -trail[propagated++]
            val ws = wc(lit); val bs = wbl(lit); val ns = wbn(lit)
            var i = 0; var j = 0
            while (i != ws.size) {
                // Watch w = ws[j++] = ws[i++]
                val wcr = ws[i]; val wblit = bs[i]; val wbinv = ns[i]
                ws[j] = wcr; bs[j] = wblit; ns[j] = wbinv; j++; i++
                val b = valOfLit(wblit)
                if (b > 0) continue // blocking literal satisfied
                if (wbinv) {
                    if (b < 0) conflict = wcr
                    else assign(wblit, wcr, 'C')
                } else {
                    if (conflict != CREF_NONE) break
                    if (cGarbage[wcr]) { j--; continue }
                    val ls = lits(wcr)
                    val other = ls[0] xor ls[1] xor lit
                    val u = valOfLit(other)
                    if (u > 0) {
                        bs[j - 1] = other
                    } else {
                        val size = cSize[wcr]
                        val mid = cPos[wcr]
                        var k = mid
                        var r = 0
                        var v = -1
                        while (k != size) {
                            r = ls[k]; v = valOfLit(r)
                            if (v >= 0) break
                            k++
                        }
                        if (v < 0) {
                            k = 2
                            while (k != mid) {
                                r = ls[k]; v = valOfLit(r)
                                if (v >= 0) break
                                k++
                            }
                        }
                        cPos[wcr] = k
                        if (v > 0) {
                            bs[j - 1] = r
                        } else if (v == 0) {
                            // found new unassigned replacement literal to watch
                            ls[0] = other
                            ls[1] = r
                            ls[k] = lit
                            watchLiteral(r, lit, wcr)
                            j--
                        } else if (u == 0) {
                            // other watch unassigned, rest false -> unit
                            assign(other, wcr, 'C')
                        } else {
                            conflict = wcr
                            break
                        }
                    }
                }
            }
            if (j != i) {
                while (i != ws.size) { ws[j] = ws[i]; bs[j] = bs[i]; ns[j] = ns[i]; j++; i++ }
                ws.shrinkTo(j); bs.shrinkTo(j); ns.shrinkTo(j)
            }
        }
        if (conflict == CREF_NONE) {
            noConflictUntil = propagated
        } else {
            conflicts++
            noConflictUntil = ctlTrail[level]
            tr("CONFLICT")
        }
        return conflict == CREF_NONE
    }

    // =========================================================================
    // analyze support
    // =========================================================================
    private var glueStampCounter = 0L
    private var gtab = LongArray(1)
    private fun recomputeGlue(cr: Int): Int {
        val stamp = ++glueStampCounter
        if (gtab.size < level + 1) gtab = gtab.copyOf(level + 1)
        var res = 0
        for (lit in lits(cr)) {
            val lv = vLevel[vidx(lit)]
            if (lv >= gtab.size) gtab = gtab.copyOf(lv + 1)
            if (gtab[lv] == stamp) continue
            gtab[lv] = stamp
            res++
        }
        return res
    }
    private fun promoteClause(cr: Int, newGlue: Int) {
        if (newGlue < cGlue[cr]) cGlue[cr] = newGlue
    }
    private fun maxUsedVal(): Int = 2
    private fun bumpClause(cr: Int) {
        cUsed[cr] = maxUsedVal()
        if (!cRedundant[cr]) return
        val newGlue = recomputeGlue(cr)
        if (newGlue < cGlue[cr]) promoteClause(cr, newGlue)
    }

    private fun analyzeLiteral(lit: Int, openBox: IntArray) {
        val idx = vidx(lit)
        val lv = vLevel[idx]
        if (lv == 0) return
        if (seen[idx].toInt() != 0) return
        // analyze.cpp analyze_literal: learn a lazily explained external reason before marking
        // (upstream asserts !opts.exteagerreasons here; with eager reasons it is not reached)
        if (vReason[idx] == CREF_EXTERNAL) {
            vReason[idx] = learnExternalReasonClause(-lit, 0, true)
            if (vReason[idx] == CREF_NONE) return // actually a unit (no LRAT unit chain here)
        }
        seen[idx] = 1
        analyzed.add(lit)
        if (lv < level) clause.add(lit)
        // control frame lv: seen_count / seen_trail
        val sc = ctlSeenCount[lv]
        if (sc == 0) {
            levelsSeen.add(lv)
            ctlSeenTrail[lv] = vTrail[idx]
        }
        ctlSeenCount[lv] = sc + 1
        if (vTrail[idx] < ctlSeenTrail[lv]) ctlSeenTrail[lv] = vTrail[idx]
        if (lv == level) openBox[0]++
    }
    private fun analyzeReason(lit: Int, reasonCr: Int, openBox: IntArray) {
        bumpClause(reasonCr)
        for (other in lits(reasonCr)) if (other != lit) analyzeLiteral(other, openBox)
    }

    private fun clearAnalyzedLiterals() {
        for (t in 0 until analyzed.size) seen[vidx(analyzed[t])] = 0
        analyzed.clear()
    }
    private fun clearAnalyzedLevels() {
        for (t in 0 until levelsSeen.size) {
            val l = levelsSeen[t]
            if (l < ctlSeenCount.size) {
                ctlSeenCount[l] = 0
                ctlSeenTrail[l] = ctlTrail[l]
            }
        }
        levelsSeen.clear()
    }

    // =========================================================================
    // failing assumptions / IPASIR failed() core (assume.cpp Internal::failing()).
    //
    // 1:1 translation of the NON-LRAT path of failing(). Proof/LRAT bookkeeping
    // (proof, lrat, lrat_chain, conclusion, conclude_unsat, check_learned_clause) is
    // omitted as vacuous here, exactly as the port already
    // omits chrono/ILB: this build has no proof. The external_reason branches (an
    // assumption or BFS literal propagated by the IPASIR-UP propagator whose reason is
    // not learned yet) are translated. The unsat_constraint branch is omitted — there
    // is no constraint API. external->e2i / externalize is the
    // identity map here (DIMACS var N == internal idx N), so elit == lit throughout.
    //
    // Runs EAGERLY at the UNSAT-under-assumptions exit while level/reason/trail are
    // still intact (solve() rolls back to level 0 immediately after). The result is
    // stored in failedBits and read later by failed(lit). `bit` uses upstream bign():
    // bign(lit) = 1 + (lit<0), i.e. value 1 for a positive lit, 2 for a negative one.
    // =========================================================================
    private fun bign(lit: Int): Int = 1 + (if (lit < 0) 1 else 0)

    private fun computeFailed() {
        // Mirrors failing()'s classification loop (assume.cpp:102-156): walk the
        // assumption stack, bucket each falsified assumption into one of three cases.
        var failedUnit = 0
        var failedClashing = 0
        var firstFailed = 0
        var failedLevel = Int.MAX_VALUE

        for (lit in assumptions) {
            if (valOfLit(lit) >= 0) continue
            val idx = vidx(lit)
            if (vLevel[idx] == 0) { failedUnit = lit; break }   // case (1)
            if (failedClashing != 0) continue
            if (vReason[idx] == CREF_EXTERNAL) {
                vReason[idx] = learnExternalReasonClause(-lit, 0, false)
                if (vReason[idx] == CREF_NONE) {
                    vLevel[idx] = 0
                    failedUnit = lit
                    break
                }
                vLevel[idx] = 0
                // Recalculate assignment level
                for (other in lits(vReason[idx])) {
                    if (other == -lit) continue
                    val tmp = vLevel[vidx(other)]
                    if (tmp > vLevel[idx]) vLevel[idx] = tmp
                }
                if (vLevel[idx] == 0) {
                    failedUnit = lit
                    break
                }
            }
            if (vReason[idx] == CREF_NONE) {                    // case (2): no reason
                failedClashing = lit
            } else if (firstFailed == 0 || vLevel[idx] < failedLevel) { // case (3)
                firstFailed = lit
                failedLevel = vLevel[idx]
            }
        }

        // Pick the failed assumption for whichever case triggered (assume.cpp:160-177).
        val failed = when {
            failedUnit != 0 -> failedUnit
            failedClashing != 0 -> failedClashing
            else -> firstFailed
        }
        // Upstream asserts `failed`: UNSAT under assumptions must have a failing one.
        if (failed == 0) error("failing(): no failed assumption found despite UNSAT under assumptions")

        // In any case mark 'failed' as a failed assumption (assume.cpp:172-177).
        failedBits[vidx(failed)] = (failedBits[vidx(failed)].toInt() or bign(failed)).toByte()

        // Case (1): root-level falsified unit assumption (assume.cpp:180-202).
        if (failedUnit != 0) return

        // Case (2): two clashing assumptions, also mark the negation (assume.cpp:205-218).
        if (failedClashing != 0) {
            failedBits[vidx(-failed)] = (failedBits[vidx(-failed)].toInt() or bign(-failed)).toByte()
            return
        }

        // Case (3): BFS the implication graph from -first_failed until decisions
        // (which are all assumptions) or units are reached (assume.cpp:225-311).
        failingSeen[vidx(firstFailed)] = 1
        val work = IntArrayList()
        work.add(-firstFailed)

        var next = 0
        while (next < work.size) {
            val lit = work[next++]
            // assert(val(lit) > 0)
            if (valOfLit(lit) <= 0) error("failing() BFS popped a non-true literal $lit")
            val idx = vidx(lit)
            if (vLevel[idx] == 0) continue
            if (vReason[idx] == CREF_EXTERNAL) {
                // wrapped_learn_external_reason_clause: its clause/LRAT stashing is vacuous
                // here (the add path uses its own buffer, no LRAT)
                vReason[idx] = learnExternalReasonClause(lit, 0, true)
                if (vReason[idx] == CREF_NONE) {
                    vLevel[idx] = 0
                    continue
                }
            }
            if (vReason[idx] != CREF_NONE) {
                for (other in lits(vReason[idx])) {
                    val oidx = vidx(other)
                    if (failingSeen[oidx].toInt() != 0) continue
                    failingSeen[oidx] = 1
                    // assert(val(other) < 0)
                    if (valOfLit(other) >= 0) error("failing() BFS reason literal $other is not false")
                    work.add(-other)
                }
            } else {
                // No reason => decision == assumption. Mark its failed bit.
                failedBits[idx] = (failedBits[idx].toInt() or bign(lit)).toByte()
            }
        }

        // clear_analyzed_literals() equivalent: reset the BFS scratch (assume.cpp:312).
        // work[0] is -firstFailed and the rest are the -other lits, so vidx over `work`
        // covers every var whose failingSeen bit was set.
        for (t in 0 until work.size) failingSeen[vidx(work[t])] = 0
    }

    // =========================================================================
    // recursive minimization (minimize.cpp)
    // =========================================================================
    private fun minimizeLiteral(lit: Int, depth: Int): Boolean {
        val idx = vidx(lit)
        val lv = vLevel[idx]
        if (lv == 0 || removable[idx].toInt() != 0 || keepFlag[idx].toInt() != 0) return true
        if (vReason[idx] == CREF_NONE || poison[idx].toInt() != 0 || lv == level) return false
        val seenCount = ctlSeenCount[lv]
        if (depth == 0 && seenCount < 2) return false
        if (vTrail[idx] <= ctlSeenTrail[lv]) return false
        if (depth > OPT_minimizedepth) return false
        var res = true
        // minimize.cpp: lazily explained external reason (upstream asserts !opts.exteagerreasons)
        if (vReason[idx] == CREF_EXTERNAL) {
            vReason[idx] = learnExternalReasonClause(lit, 0, true)
            if (vReason[idx] == CREF_NONE) return true // became a root-level unit
        }
        for (other in lits(vReason[idx])) {
            if (other == lit) continue
            res = minimizeLiteral(-other, depth + 1)
            if (!res) break
        }
        if (res) removable[idx] = 1 else poison[idx] = 1
        minimized.add(idx)
        return res
    }

    private fun minimizeClause() {
        // sort clause by trail order (ascending trail)
        sortClauseByTrailAsc()
        var j = 0
        for (i in 0 until clause.size) {
            val lit = clause[i]
            if (minimizeLiteral(-lit, 0)) {
                // removed
            } else {
                keepFlag[vidx(lit)] = 1
                clause[j] = lit; j++
            }
        }
        clause.shrinkTo(j)
        for (t in 0 until minimized.size) {
            val idx = minimized[t]
            removable[idx] = 0
            poison[idx] = 0
        }
        for (t in 0 until clause.size) keepFlag[vidx(clause[t])] = 0
        minimized.clear()
    }

    private fun sortClauseByTrailAsc() {
        // std::sort with comparator var(a).trail < var(b).trail. std::sort is not stable, but
        // the trail index is a strict total order over distinct variables, so any correct sort
        // gives the identical result. Use a plain insertion sort for determinism.
        val a = clause.toArray()
        for (i in 1 until a.size) {
            val key = a[i]; val kt = vTrail[vidx(key)]
            var j = i - 1
            while (j >= 0 && vTrail[vidx(a[j])] > kt) { a[j + 1] = a[j]; j-- }
            a[j + 1] = key
        }
        clause.clear()
        for (x in a) clause.add(x)
    }

    // =========================================================================
    // new driving clause
    // =========================================================================
    private var jump = 0
    private fun newDrivingClause(glue: Int): Int {
        val size = clause.size
        val res: Int
        if (size == 0) { jump = 0; res = CREF_NONE }
        else if (size == 1) { jump = 0; res = CREF_NONE }
        else {
            // sort clause by decreasing (level,trail) so highest-level lits go first.
            // The (level,trail) pair is a strict total order over distinct vars -> any sort
            // yields the same order; insertion sort for determinism.
            sortClauseByLevelTrailDesc()
            jump = vLevel[vidx(clause[1])]
            res = newClause(clause.toArray(), true, glue)
        }
        return res
    }
    private fun sortClauseByLevelTrailDesc() {
        val a = clause.toArray()
        for (i in 1 until a.size) {
            val key = a[i]
            val kl = vLevel[vidx(key)]; val kt = vTrail[vidx(key)]
            var j = i - 1
            while (j >= 0) {
                val al = vLevel[vidx(a[j])]; val at = vTrail[vidx(a[j])]
                // a[j] should come after key iff key is "greater": (kl>al) || (kl==al && kt>at)
                val keyGreater = if (kl != al) kl > al else kt > at
                if (!keyGreater) break
                a[j + 1] = a[j]; j--
            }
            a[j + 1] = key
        }
        clause.clear()
        for (x in a) clause.add(x)
    }

    // =========================================================================
    // backtrack
    // =========================================================================
    private fun copyPhases(dst: ByteArray) {
        for (i in 1..maxVar) {
            val tmp = phaseSaved[i]
            if (tmp.toInt() != 0) dst[i] = tmp
        }
    }
    private fun updateTargetAndBest() {
        if (!stable) return
        if (noConflictUntil > targetAssigned) {
            copyPhases(phaseTarget)
            targetAssigned = noConflictUntil
        }
        if (noConflictUntil > bestAssigned) {
            copyPhases(phaseBest)
            bestAssigned = noConflictUntil
        }
    }
    private fun unassign(lit: Int) {
        val idx = vidx(lit)
        vals[idx] = 0
        numAssigned--
        if (!heapContains(idx)) heapPush(idx)
        if (qBumped < btab[idx]) updateQueueUnassigned(idx)
    }
    private fun backtrack(newLevel: Int) {
        if (newLevel == level) return
        updateTargetAndBest()
        val assigned = ctlTrail[newLevel + 1]
        val end = trail.size
        var j = assigned
        var reassigned = 0
        notifyBacktrack(newLevel)
        if (externalProp && !externalPropIsLazy && notified > assigned) notified = assigned
        for (i in assigned until end) {
            val lit = trail[i]
            if (vLevel[vidx(lit)] > newLevel) {
                unassign(lit)
            } else {
                // Out-of-order assigned literal kept on the trail. Without chrono this only
                // happens with an external propagator (units learned during explanation).
                trail[j] = lit
                vTrail[vidx(lit)] = j++
                reassigned++
            }
        }
        trail.shrinkTo(j)
        if (propagated > assigned) propagated = assigned
        if (noConflictUntil > assigned) noConflictUntil = assigned
        if (reassigned != 0) notifyAssignments()
        // control.resize(new_level + 1)
        val newSize = newLevel + 1
        ctlDecision.shrinkTo(newSize); ctlTrail.shrinkTo(newSize)
        ctlSeenCount.shrinkTo(newSize); ctlSeenTrail.shrinkTo(newSize)
        level = newLevel
    }

    // =========================================================================
    // analyze (analyze.cpp, no-chrono/no-otfs path)
    // =========================================================================
    private val analyzeOpen = IntArray(1)
    private val analyzeForced = IntArray(1)
    private fun analyze() {
        if (externalProp && !externalPropIsLazy && OPT_exteagerreasons) {
            explainExternalPropagations()
        }

        // analyze.cpp: `if (opts.chrono || external_prop)`; chrono is off, so only the
        // propagator enables finding the actual conflict level.
        if (externalProp) {
            val conflictLevel = findConflictLevel(analyzeForced)
            val forced = analyzeForced[0]
            if (forced != 0) {
                // single highest level literal: reuse the conflict as driving clause
                backtrack(conflictLevel - 1)
                searchAssignDriving(forced, conflict)
                conflict = CREF_NONE
                return
            }
            backtrack(conflictLevel)
        }

        if (level == 0) {
            unsat = true
            markedFailed = true // learn_empty_clause
            conflict = CREF_NONE
            return
        }

        var reason = conflict
        var i = trail.size
        analyzeOpen[0] = 0
        var uip = 0

        while (true) {
            analyzeReason(uip, reason, analyzeOpen)
            uip = 0
            while (uip == 0) {
                val lit = trail[--i]
                if (seen[vidx(lit)].toInt() == 0) continue
                if (vLevel[vidx(lit)] == level) uip = lit
            }
            analyzeOpen[0]--
            if (analyzeOpen[0] == 0) break
            reason = vReason[vidx(uip)]
            if (reason == CREF_EXTERNAL) {
                // upstream asserts !opts.exteagerreasons here
                reason = learnExternalReasonClause(-uip, 0, true)
                vReason[vidx(uip)] = reason
            }
        }
        clause.add(-uip)

        var size = clause.size
        val glue = levelsSeen.size - 1
        glueFast.update(glue.toDouble())
        glueSlow.update(glue.toDouble())

        if (size > 1) {
            if (OPT_minimize) minimizeClause()
            size = clause.size
            if (OPT_bump) bumpVariables()
        }

        val driving = newDrivingClause(glue)
        backtrack(jump)

        if (uip != 0) {
            searchAssignDriving(-uip, driving)
        } else {
            unsat = true
            markedFailed = true // learn_empty_clause
        }

        if (stable) reluctantTick()

        clearAnalyzedLiterals()
        clearAnalyzedLevels()
        clause.clear()
        conflict = CREF_NONE

        if (size == 1) iterating = true
    }

    // analyze.cpp: find_conflict_level. Determines the maximum level in the conflict, moves
    // the two highest level literals to the watched positions and sets forced[0] to the
    // single literal on that level (0 if there are several).
    private fun findConflictLevel(forced: IntArray): Int {
        val ls = lits(conflict)
        var res = 0
        var count = 0
        forced[0] = 0
        for (lit in ls) {
            val tmp = vLevel[vidx(lit)]
            if (tmp > res) {
                res = tmp
                forced[0] = lit
                count = 1
            } else if (tmp == res) {
                count++
                if (res == level && count > 1) break
            }
        }
        val size = cSize[conflict]
        for (i in 0 until 2) {
            val lit = ls[i]
            var highestPosition = i
            var highestLiteral = lit
            var highestLevel = vLevel[vidx(highestLiteral)]
            for (j in i + 1 until size) {
                val other = ls[j]
                val tmp = vLevel[vidx(other)]
                if (highestLevel >= tmp) continue
                highestLiteral = other
                highestPosition = j
                highestLevel = tmp
                if (highestLevel == res) break
            }
            // No unwatched higher assignment level literal.
            if (highestPosition == i) continue
            if (highestPosition > 1) removeWatch(lit, conflict)
            ls[highestPosition] = lit
            ls[i] = highestLiteral
            if (highestPosition > 1) watchLiteral(highestLiteral, ls[1 - i], conflict)
        }
        if (count != 1) forced[0] = 0
        return res
    }

    // =========================================================================
    // reluctant (Luby) doubling
    // =========================================================================
    private fun reluctantEnable() {
        relU = 1; relV = 1
        relPeriod = OPT_reluctantint
        relTrigger = false
    }
    private fun reluctantDisable() {
        relU = 0; relV = 0; relPeriod = 0
        relTrigger = false
    }
    private fun reluctantTick() {
        if (relPeriod == 0L) return
        relPeriod--
        if (relPeriod != 0L) return
        if ((relU and -relU) == relV) {
            relU++
            relV = 1
        } else {
            relV *= 2
        }
        var p = relV
        if (OPT_reluctantmax != 0L && p > OPT_reluctantmax / OPT_reluctantint) {
            relU = 1; relV = 1
            p = 1
        }
        relPeriod = p * OPT_reluctantint
        relTrigger = true
    }

    // =========================================================================
    // stabilizing (restart.cpp)
    // =========================================================================
    private fun stabilizing(): Boolean {
        if (!OPT_stabilize) return false
        if (conflicts <= limStabilize) return stable
        val deltaConflicts = conflicts - lastStabilizeConflicts
        if (!incStabilizeSet) {
            incStabilize = deltaConflicts
            if (incStabilize < 1) incStabilize = 1
            incStabilizeSet = true
        }
        var nextDelta = incStabilize
        val sp = stabphases + 1
        nextDelta *= sp * sp
        limStabilize = conflicts + nextDelta
        if (limStabilize <= conflicts) limStabilize = conflicts + 1
        lastStabilizeConflicts = conflicts
        stable = !stable
        if (stable) stabphases++
        swapAverages()
        if (stable) reluctantEnable() else reluctantDisable()
        return stable
    }

    // =========================================================================
    // restart (restart.cpp)
    // =========================================================================
    private fun restarting(): Boolean {
        if (!OPT_restart) return false
        if (level < 2) return false
        if (stabilizing() && OPT_reluctant) return relTrigger
        if (conflicts <= limRestart) return false
        val f = glueFast.value
        val p = if (stable) OPT_restartmarginstable else OPT_restartmarginfocused
        val m = (100.0 + p) / 100.0
        val s = glueSlow.value
        val l = m * s
        return l <= f
    }
    private fun restart() {
        restarts++
        relTrigger = false
        backtrack(0)
        limRestart = conflicts + OPT_restartint
        tr("RESTART")
    }

    // =========================================================================
    // averages swap on mode switch
    // =========================================================================
    private fun initAverages() {
        glueFast = initEma(OPT_emagluefast)
        glueSlow = initEma(OPT_emaglueslow)
    }
    private fun swapAverages() {
        val tf = Ema(); tf.copyFrom(glueFast); glueFast.copyFrom(savedGlueFast); savedGlueFast.copyFrom(tf)
        val ts = Ema(); ts.copyFrom(glueSlow); glueSlow.copyFrom(savedGlueSlow); savedGlueSlow.copyFrom(ts)
        if (!averagesSwapped) initAverages()
        averagesSwapped = true
    }

    // =========================================================================
    // reduce (reduce.cpp)
    // =========================================================================
    private fun reducing(): Boolean {
        if (!OPT_reduce) return false
        var any = false
        for (t in 0 until clauses.size) {
            val c = clauses[t]
            if (cRedundant[c] && !cGarbage[c]) { any = true; break }
        }
        if (!any) return false
        return conflicts >= limReduce
    }
    private fun protectReasons() {
        for (t in 0 until trail.size) {
            val r = vReason[vidx(trail[t])]
            if (r != CREF_NONE && r != CREF_DECISION && r != CREF_EXTERNAL) cReason[r] = true
        }
    }
    private fun unprotectReasons() {
        for (t in 0 until clauses.size) cReason[clauses[t]] = false
    }
    // reduce.cpp: units assigned out of order (only possible here through the external
    // propagator) are propagated at the root before reducing.
    private fun propagateOutOfOrderUnits(): Boolean {
        if (level == 0) return true
        var oou = 0
        var i = ctlTrail[1]
        while (oou == 0 && i < trail.size) {
            val lit = trail[i++]
            if (vLevel[vidx(lit)] != 0) continue
            oou = lit
        }
        if (oou == 0) return true
        backtrack(0)
        if (propagate()) return true
        unsat = true // learn_empty_clause
        markedFailed = true
        return false
    }

    private fun reduce() {
        reductions++
        if (!propagateOutOfOrderUnits()) {
            tr("REDUCE") // upstream DONE: report, no limit update
            return
        }
        protectReasons()

        val tier1 = OPT_reducetier1glue
        val tier2 = maxOf(tier1, OPT_reducetier2glue)
        val stack = IntArrayList()
        for (t in 0 until clauses.size) {
            val c = clauses[t]
            if (!cRedundant[c]) continue
            if (cGarbage[c]) continue
            if (cReason[c]) continue
            val used = cUsed[c]
            if (used != 0) cUsed[c] = used - 1
            if (cGlue[c] <= tier1 && used != 0) continue
            if (cGlue[c] <= tier2 && used >= maxUsedVal() - 1) continue
            stack.add(c)
        }
        stableSortReduce(stack)
        var target = (1e-2 * OPT_reducetarget * stack.size).toInt()
        if (target > stack.size) target = stack.size
        for (t in 0 until target) cGarbage[stack[t]] = true

        garbageCollect()
        unprotectReasons()

        var delta = OPT_reduceint
        var factor = kotlin.math.sqrt(conflicts.toDouble())
        if (factor < 1) factor = 1.0
        delta = (delta * factor).toLong()
        if (delta < 1) delta = 1
        limReduce = conflicts + delta
        tr("REDUCE")
    }

    /**
     * Stable sort of reduce candidates by (glue desc, size desc). The C reference uses
     * std::stable_sort with this one-directional predicate; we mirror it with a stable
     * insertion sort so incomparable clauses keep input order identically (same lesson as
     * MiniSat's reduceDB non-total-order sort).
     */
    private fun stableSortReduce(stack: IntArrayList) {
        val a = stack.toArray()
        // predicate: c precedes d iff (c.glue>d.glue) || (c.glue==d.glue && c.size>d.size)
        for (i in 1 until a.size) {
            val key = a[i]
            var j = i - 1
            while (j >= 0 && reduceLess(key, a[j])) { a[j + 1] = a[j]; j-- }
            a[j + 1] = key
        }
        stack.clear()
        for (x in a) stack.add(x)
    }
    private fun reduceLess(c: Int, d: Int): Boolean {
        if (cGlue[c] > cGlue[d]) return true
        if (cGlue[c] < cGlue[d]) return false
        return cSize[c] > cSize[d]
    }

    private fun garbageCollect() {
        // unwatch garbage clauses, drop them from the clause list, keep the rest.
        // First unwatch (needs live lits[0]/lits[1]).
        for (t in 0 until clauses.size) {
            val c = clauses[t]
            if (cGarbage[c] && cSize[c] >= 2) unwatchClause(c)
        }
        val kept = IntArrayList()
        for (t in 0 until clauses.size) {
            val c = clauses[t]
            if (!cGarbage[c]) kept.add(c)
        }
        clauses.clear()
        for (t in 0 until kept.size) clauses.add(kept[t])
    }

    // =========================================================================
    // decide (decide.cpp / phases.cpp)
    // =========================================================================
    private fun nextDecisionVariableOnQueue(): Int {
        var res = qUnassigned
        while (vals[res].toInt() != 0) res = linkPrev[res]
        if (res != qUnassigned) updateQueueUnassigned(res)
        return res
    }
    private fun nextDecisionVariableWithBestScore(): Int {
        var res: Int
        while (true) {
            res = heapFront()
            if (vals[res].toInt() == 0) break
            heapPop()
        }
        return res
    }
    private fun nextDecisionVariable(): Int =
        if (useScores()) nextDecisionVariableWithBestScore() else nextDecisionVariableOnQueue()

    private fun decidePhase(idx: Int, target: Boolean): Int {
        val initialPhase = if (OPT_phase) 1 else -1
        var phase = 0
        // `if (force_saved_phase) phase = phases.saved[idx];` omitted: only lucky/local search
        // set force_saved_phase. opts.forcephase (default 0) is not ported either.
        if (phase == 0) phase = phaseForced[idx].toInt() // swapped with opts.forcephase case!
        if (phase == 0 && target) phase = phaseTarget[idx].toInt()
        if (phase == 0) phase = phaseSaved[idx].toInt()
        if (phase == 0) phase = initialPhase
        return phase * idx
    }
    // ---- assumptions (decision literals forced before free search) ----
    // CaDiCaL consumes assumptions in decide(): while level < assumptions.size the next
    // decision is assumptions[level] instead of a heuristic pick, so satisfied() must also
    // wait for all assumptions to be on the trail. A falsified assumption ends the solve
    // as UNSAT (decide returns 20, like the C loop). Only the verdict + model are needed
    // here, so CaDiCaL's frozen-literal / failed-core bookkeeping is not ported. After the
    // solve the trail is rolled back, so the same instance can be solved again under other
    // assumptions on the same clause set. Signed DIMACS literals.
    private var assumptions: IntArray = IntArray(0)

    private fun satisfied(): Boolean {
        // not satisfied until every assumption has been forced onto its own level
        if (level < assumptions.size) return false
        if (numAssigned < maxVar) return false
        // decide.cpp: also not before everything is propagated (only observable when an external
        // propagator re-checks satisfied() after its callbacks; the CDCL loop propagates first)
        if (propagated < trail.size) return false
        return numAssigned == maxVar
    }

    // returns 0 to continue, 20 if an assumption is falsified (-> UNSAT for this solve)
    private fun decide(): Int {
        if (level < assumptions.size) {
            val lit = assumptions[level]
            ensureVar(vidx(lit))
            val v = valOfLit(lit)
            if (v < 0) {
                // assumption falsified under the current (assumption-forced) prefix
                markedFailed = false // decide.cpp: if (res) marked_failed = false
                return 20
            } else if (v > 0) {
                // already satisfied: add a pseudo decision level, like CaDiCaL. This is not
                // a real branch, so no DECIDE trace is emitted (matches new_trail_level(0)).
                newTrailLevel(0)
                notifyDecision()
                return 0
            } else {
                // search_assume_decision
                newTrailLevel(lit)
                notifyDecision()
                tr("DECIDE $lit")
                assign(lit, CREF_DECISION, 'D')
                return 0
            }
        }
        var decision = askDecision()
        if (level < assumptions.size) {
            // Forced backtrack below pseudo decision levels; the branch above handles it.
            return decide()
        }
        if (decision == 0) {
            val idx = nextDecisionVariable()
            val target = (OPT_target > 1 || (stable && OPT_target != 0))
            decision = decidePhase(idx, target)
        }
        // search_assume_decision
        newTrailLevel(decision)
        notifyDecision()
        tr("DECIDE $decision")
        assign(decision, CREF_DECISION, 'D')
        return 0
    }

    // =========================================================================
    // add clause (root-level simplification)
    // =========================================================================
    private val addBuf = IntArrayList()
    private val learnedLevels = IntArrayList()
    // clause.cpp add_new_original_clause; also the add path of external clauses, where
    // fromPropagator / forceNoBacktrack change the behaviour and newestClause is set.
    private fun addClauseInternal(raw: IntArray): Boolean {
        // Process original clauses at the root, as upstream add_new_original_clause does
        // (clause.cpp: `if (level) backtrack();`). Adding a clause while a previous solve left a
        // level>0 trail would otherwise place a unit at the wrong trail position (past the
        // level-0 cut) so backtrack(0) later unassigns it and the fixed literal is lost; the
        // root-false / taut checks below also rely on vLevel being the real root level.
        // Clauses from the propagator are added on the current level. (The ILB
        // tainted_literal branch is omitted: no ILB.)
        if (!fromPropagator && level > 0) backtrack(0)
        newestClause = CREF_NONE
        if (unsat) return true // skipping clause since formula is already inconsistent
        addBuf.clear()
        learnedLevels.clear()
        var unassigned = 0
        var taut = false
        for (lit in raw) {
            ensureVar(vidx(lit))
            val v = valOfLit(lit)
            if (v > 0 && vLevel[vidx(lit)] == 0) { taut = true; break }
            if (v < 0 && vLevel[vidx(lit)] == 0) continue // drop root-false
            var dup = false
            var i = 0
            while (i < addBuf.size) {
                val q = addBuf[i]
                if (q == lit) { dup = true; break }
                if (q == -lit) { taut = true; break }
                i++
            }
            if (taut) break
            if (!dup) {
                addBuf.add(lit)
                if (v != 0) {
                    val lv = vLevel[vidx(lit)]
                    if (!learnedLevels.contains(lv)) learnedLevels.add(lv)
                } else {
                    unassigned++
                }
            }
        }
        if (taut) return true
        if (addBuf.size == 0) { unsat = true; markedFailed = true; return false }
        if (addBuf.size == 1) {
            val lit = addBuf[0]
            if (forceNoBacktrack) {
                // unit reason learned during analysis: stays on the trail, now at level 0
                check(level > 0 && valOfLit(lit) > 0) { "forced unit $lit must be true above the root" } // clause.cpp asserts
                val idx = vidx(lit)
                vLevel[idx] = 0
                vReason[idx] = CREF_NONE
                markFixed(lit) // clause.cpp: mark_fixed (clause[0])
                return true
            }
            if (valOfLit(lit) < 0) backtrack(vLevel[vidx(lit)] - 1)
            handleExternalClause(CREF_NONE)
            // assign_original_unit: a root conflict learns the empty clause
            assign(lit, CREF_NONE, 'U', originalUnit = true)
            if (propagate()) return true
            unsat = true
            markedFailed = true // learn_empty_clause
            return false
        }
        moveLiteralsToWatch()
        val glue = minOf(learnedLevels.size + unassigned, addBuf.size) // new_clause clamps glue to size
        val forgettable = fromPropagator && extClauseForgettable
        val cr = newClause(addBuf.toArray(), forgettable, glue)
        if (forgettable) cUsed[cr] = 0 // clause.cpp new_clause: used = 0 (not a learned clause)
        handleExternalClause(cr)
        newestClause = cr
        return true
    }

    // =========================================================================
    // IPASIR-UP external propagation (external_propagate.cpp + the External/Solver
    // wrappers of external.cpp / solver.cpp). The external->internal map is the identity
    // here (DIMACS var N == internal idx N), so e2i/i2e/externalize/internalize vanish.
    // Not ported, as the features do not exist in this port: ILB (set_tainted_literal,
    // renotify_trail_after_ilb), local search (renotify_trail_after_local_search,
    // renotify_full_trail), solution reconstruction (reset_extended/extend: external_check_solution
    // reads the internal values directly), freeze/melt (no elimination), proof/LRAT/check
    // (forgettable_original, lrat_chain stashing), stats, and the mobical-only debug helpers.
    // =========================================================================

    // Internal::fixed: root-level value of [lit], 0 if not fixed.
    private fun fixed(lit: Int): Int {
        val idx = vidx(lit)
        if (vals[idx].toInt() != 0 && vLevel[idx] != 0) return 0
        return valOfLit(lit)
    }

    // External::observed (bounds-checked is_observed lookup).
    private fun externalObserved(elit: Int): Boolean {
        val eidx = vidx(elit)
        if (eidx > maxVar) return false
        return isObserved[eidx]
    }

    // external_propagate.cpp: add_observed_var
    private fun internalAddObservedVar(ilit: Int) {
        val idx = vidx(ilit)
        if (relevantTab[idx] < Int.MAX_VALUE) relevantTab[idx]++ // else: observed forever
        if (valOfLit(ilit) != 0 && level > 0 && fixed(ilit) == 0) {
            // Assigned on an earlier level, which can not be notified anymore: backtrack to
            // undo this unnotifiable assignment.
            val assignmentLevel = vLevel[idx]
            backtrack(assignmentLevel - 1)
        } else if (level > 0 && fixed(ilit) != 0) {
            backtrack(0)
        }
    }

    // external_propagate.cpp: remove_observed_var
    private fun internalRemoveObservedVar(ilit: Int) {
        if (fixed(ilit) == 0 && level > 0) backtrack(0)
        val idx = vidx(ilit)
        check(fixed(ilit) != 0 || relevantTab[idx] > 0) { "remove_observed_var: variable $idx is not observed" }
        if (fixed(ilit) != 0) relevantTab[idx] = 0
        else if (relevantTab[idx] < Int.MAX_VALUE) relevantTab[idx]--
    }

    // external_propagate.cpp: observed
    private fun observed(ilit: Int): Boolean = relevantTab[vidx(ilit)] > 0

    // external_propagate.cpp: is_decision
    private fun internalIsDecision(ilit: Int): Boolean {
        if (level == 0 || fixed(ilit) != 0 || valOfLit(ilit) == 0) return false
        val idx = vidx(ilit)
        if (vLevel[idx] == 0 || vReason[idx] != CREF_NONE) return false
        return true
    }

    // external_propagate.cpp: force_backtrack
    private fun internalForceBacktrack(newLevel: Int) {
        if (!forcedBacktAllowed || level <= 0 || newLevel >= level) return
        backtrack(newLevel)
    }

    // external_propagate.cpp: external_propagate. Asks the propagator for literals to
    // propagate (their reasons are learned lazily) and for external clauses.
    private fun externalPropagate(): Boolean {
        check(!unsat)
        var cbRepropagateNeeded = true
        while (cbRepropagateNeeded && conflict == CREF_NONE && externalProp && !externalPropIsLazy) {
            cbRepropagateNeeded = false
            notifyAssignments()
            val p = propagator!!
            var elit = p.cbPropagate()
            while (elit != 0) {
                check(externalObserved(elit)) { "cb_propagate returned $elit over an unobserved variable" }
                val ilit = elit
                val tmp = valOfLit(ilit)
                if (tmp == 0) {
                    // variable is not assigned, it can be propagated
                    if (level == 0) learnExternalReasonClause(ilit, elit, false)
                    else searchAssignExternal(ilit)
                    if (unsat || conflict != CREF_NONE) break
                    propagate()
                    if (unsat || conflict != CREF_NONE) break
                    notifyAssignments()
                } else if (tmp < 0) {
                    // external propagation is falsified under the current trail
                    val levelBefore = level
                    val assigned = numAssigned
                    learnExternalReasonClause(ilit, elit, false)
                    val trailChanged = (numAssigned != assigned || level != levelBefore ||
                        propagated < trail.size)
                    if (unsat || conflict != CREF_NONE) break
                    if (trailChanged) {
                        propagate()
                        if (unsat || conflict != CREF_NONE) break
                        notifyAssignments()
                    }
                } // else (tmp > 0) -> the case of a satisfied literal is ignored
                elit = p.cbPropagate()
            }

            if (!unsat && conflict == CREF_NONE) {
                var levelBefore = level
                var assigned = numAssigned
                var hasExternalClause = askExternalClause()
                // New observed variable might have triggered a backtrack during this
                // askExternalClause call, so we need to propagate before continuing
                var trailChanged = (numAssigned != assigned || level != levelBefore ||
                    propagated < trail.size)
                if (trailChanged) {
                    propagate() // unsat or conflict will be caught later
                    if (!unsat || conflict == CREF_NONE) notifyAssignments() // upstream: `!unsat || !conflict`
                }
                while (hasExternalClause) {
                    levelBefore = level
                    assigned = numAssigned
                    addExternalClause(0, false)
                    trailChanged = (numAssigned != assigned || level != levelBefore ||
                        propagated < trail.size)
                    cbRepropagateNeeded = true
                    if (unsat || conflict != CREF_NONE) {
                        cbRepropagateNeeded = false
                        break
                    }
                    if (trailChanged) {
                        propagate()
                        if (unsat || conflict != CREF_NONE) {
                            cbRepropagateNeeded = false
                            break
                        }
                        notifyAssignments()
                    }
                    hasExternalClause = askExternalClause()
                }
            }
        }
        return conflict == CREF_NONE
    }

    // external_propagate.cpp: ask_external_clause
    private fun askExternalClause(): Boolean {
        extClauseForgettable = false
        extClauseForgettableOut.value = extClauseForgettable
        val res = propagator!!.cbHasExternalClause(extClauseForgettableOut)
        extClauseForgettable = extClauseForgettableOut.value
        return res
    }

    // external_propagate.cpp: move_literals_to_watch. Reorders the simplified external
    // clause (addBuf) so the two literals to watch come first.
    private fun moveLiteralsToWatch() {
        if (addBuf.size < 2) return
        if (level == 0) return
        for (i in 0 until 2) {
            var highestPosition = i
            var highestLiteral = addBuf[i]
            var highestLevel = vLevel[vidx(highestLiteral)]
            var highestValue = valOfLit(highestLiteral)
            for (j in i + 1 until addBuf.size) {
                val other = addBuf[j]
                val otherLevel = vLevel[vidx(other)]
                val otherValue = valOfLit(other)
                if (otherValue < 0) {
                    if (highestValue >= 0) continue
                    if (otherLevel <= highestLevel) continue
                } else if (otherValue > 0) {
                    if (highestValue > 0 && otherLevel >= highestLevel) continue
                } else {
                    if (highestValue >= 0) continue
                }
                highestPosition = j
                highestLiteral = other
                highestLevel = otherLevel
                highestValue = otherValue
            }
            if (highestPosition == i) continue
            if (highestPosition > i) {
                val t = addBuf[i]; addBuf[i] = addBuf[highestPosition]; addBuf[highestPosition] = t
            }
        }
    }

    // external_propagate.cpp: add_external_clause. Reads a reason clause of
    // [propagatedElit] (cb_add_reason_clause_lit) or, if it is 0, an external clause
    // (cb_add_external_clause_lit), and adds it through add_new_original_clause.
    private fun addExternalClause(propagatedElit: Int, noBacktrack: Boolean) {
        val p = propagator!!
        var elit: Int
        if (propagatedElit != 0) {
            // reason clauses are forgettable unless the propagator says otherwise
            extClauseForgettable = p.areReasonsForgettable
            elit = p.cbAddReasonClauseLit(propagatedElit)
        } else {
            elit = p.cbAddExternalClauseLit()
        }
        check(!forceNoBacktrack && !fromPropagator)
        forceNoBacktrack = noBacktrack
        fromPropagator = true
        extOriginal.clear()
        while (elit != 0) {
            check(externalObserved(elit)) { "external clause literal $elit is over an unobserved variable" }
            extOriginal.add(elit)
            elit = if (propagatedElit != 0) p.cbAddReasonClauseLit(propagatedElit) else p.cbAddExternalClauseLit()
        }
        addClauseInternal(extOriginal.toArray())
        forceNoBacktrack = false
        fromPropagator = false
    }

    // external_propagate.cpp: explain_reason. Learns the reasons of every externally
    // propagated literal of [reason] and marks the not yet explained ones.
    private fun explainReason(ilit: Int, reason: Int, open: IntArray) {
        if (!OPT_exteagerreasons) return
        for (other in lits(reason)) {
            if (other == ilit) continue
            val idx = vidx(other)
            if (seen[idx].toInt() != 0) continue
            if (vLevel[idx] == 0) continue
            if (vReason[idx] == CREF_EXTERNAL) {
                vReason[idx] = learnExternalReasonClause(-other, 0, true)
            }
            if (vLevel[idx] != 0 && vReason[idx] != CREF_NONE) {
                seen[idx] = 1
                open[0]++
            }
        }
    }

    // external_propagate.cpp: explain_external_propagations. Before conflict analysis, learns
    // every external reason backward reachable from the conflict, then recalculates the
    // assignment levels of the touched literals from lower to higher levels.
    private val explainOpen = IntArray(1)
    private fun explainExternalPropagations() {
        val reason = conflict
        val seenLits = IntArrayList()
        explainOpen[0] = 0 // seen but not explained literals
        explainReason(0, reason, explainOpen) // marks conflict clause lits as seen
        var i = trail.size
        while (i > 0) {
            val lit = trail[--i]
            val idx = vidx(lit)
            if (seen[idx].toInt() == 0) continue
            seenLits.add(lit)
            if (vLevel[idx] == 0) continue
            if (vReason[idx] != CREF_NONE) {
                explainOpen[0]--
                explainReason(lit, vReason[idx], explainOpen)
            }
            if (explainOpen[0] == 0) break
        }
        check(explainOpen[0] == 0)

        if (!OPT_exteagerrecalc) {
            for (t in 0 until seenLits.size) seen[vidx(seenLits[t])] = 0
        }

        // Traverse in the opposite direction (from lower to higher levels) and calculate the
        // actual assignment level for the seen assignments.
        for (t in seenLits.size - 1 downTo 0) {
            val lit = seenLits[t]
            val idx = vidx(lit)
            if (vReason[idx] != CREF_NONE) {
                var realLevel = 0
                for (other in lits(vReason[idx])) {
                    if (other == lit) continue
                    val tmp = vLevel[vidx(other)]
                    if (tmp > realLevel) realLevel = tmp
                }
                if (vLevel[idx] != 0 && realLevel == 0) {
                    learnUnitClause(lit) // build_chain_for_units / lrat_chain: no LRAT here
                    vReason[idx] = CREF_NONE
                }
                if (vLevel[idx] > realLevel) vLevel[idx] = realLevel
            }
            seen[idx] = 0
        }
    }

    // external_propagate.cpp: learn_external_reason_clause. Upstream moves `clause` aside
    // first; the port's add path uses its own addBuf, so the analysis clause is untouched.
    private fun learnExternalReasonClause(ilit: Int, falsifiedElit: Int, noBacktrack: Boolean): Int {
        val elit = if (falsifiedElit == 0) ilit else falsifiedElit
        addExternalClause(elit, noBacktrack)
        return newestClause
    }

    // external_propagate.cpp: handle_external_clause. Checks if the new clause forces
    // backtracking, new assignments or conflict analysis (chrono off: backtrack first).
    private fun handleExternalClause(res: Int) {
        // at level 0 we have to do nothing...
        if (level == 0) return
        if (res == CREF_NONE) {
            // new unit clause. For now just backtrack.
            check(!forceNoBacktrack) { "handle_external_clause: unit with force_no_backtrack" } // upstream assert
            backtrack(0)
            return
        }
        val pos0 = lits(res)[0]
        val pos1 = lits(res)[1]
        if (forceNoBacktrack) {
            check(valOfLit(pos1) < 0 && valOfLit(pos0) >= 0) { "forced reason clause is not propagating" } // upstream assert
            return
        }
        val l1 = vLevel[vidx(pos1)]
        if (valOfLit(pos0) < 0) { // conflicting or propagating clause
            backtrack(l1)
            if (valOfLit(pos0) < 0) {
                // The `!from_propagator` sub-branch (backtrack below the clause) is omitted:
                // without ILB, clauses not from the propagator are added at level 0.
                conflict = res
            } else {
                searchAssignDriving(pos0, res)
            }
            return
        }
        if (valOfLit(pos1) < 0 && valOfLit(pos0) == 0) { // propagating clause
            backtrack(l1)
            searchAssignDriving(pos0, res)
            return
        }
    }

    // external_propagate.cpp: external_check_solution. Asks the propagator to approve the
    // found model; it may reject it by adding clauses (or observing new variables).
    private fun externalCheckSolution(): Boolean {
        if (!externalProp) return true
        val p = propagator!!
        var trailChanged = true
        var addedNewClauses = false
        while (trailChanged || addedNewClauses) {
            notifyAssignments()
            if (!satisfied()) break
            trailChanged = false // to be on the safe side
            addedNewClauses = false
            // Filtered by is_observed: fixed variables are internally not necessarily observed.
            val etrail = IntArrayList()
            for (idx in 1..maxVar) {
                if (!isObserved[idx]) continue
                etrail.add(if (vals[idx].toInt() > 0) idx else -idx) // External::ival
            }
            val isConsistent = p.cbCheckFoundModel(etrail.toArray())
            if (isConsistent) return true

            var hasExternalClause = askExternalClause()
            while (hasExternalClause) {
                val levelBefore = level
                val assigned = numAssigned
                addExternalClause(0, false)
                // upstream declares a new (shadowing) trail_changed here; the outer one stays false
                val clauseTrailChanged = (numAssigned != assigned || level != levelBefore ||
                    propagated < trail.size)
                addedNewClauses = true
                if (unsat || conflict != CREF_NONE || clauseTrailChanged) break
                hasExternalClause = askExternalClause()
            }
            if (unsat || conflict != CREF_NONE) break
        }
        if (!unsat && conflict != CREF_NONE) {
            val conflictLevel = vLevel[vidx(lits(conflict)[0])]
            if (conflictLevel != level) backtrack(conflictLevel)
        }
        return conflict == CREF_NONE
    }

    // external_propagate.cpp: notify_assignments. Notifies the observed literals assigned
    // since the last notification (upstream calls notify_assignment even with none).
    private fun notifyAssignments() {
        if (!externalProp || externalPropIsLazy) return
        val endOfTrail = trail.size
        if (notified >= endOfTrail) return
        val assigned = IntArrayList()
        while (notified < endOfTrail) {
            val ilit = trail[notified++]
            if (!observed(ilit)) continue
            assigned.add(ilit)
        }
        propagator!!.notifyAssignment(assigned.toArray())
    }

    // external_propagate.cpp: connect_propagator
    private fun connectPropagator() {
        if (level > 0) backtrack(0)
    }

    // external_propagate.cpp: notify_decision
    private fun notifyDecision() {
        if (!externalProp || externalPropIsLazy) return
        propagator!!.notifyNewDecisionLevel()
    }

    // external_propagate.cpp: notify_backtrack
    private fun notifyBacktrack(newLevel: Int) {
        if (!externalProp || externalPropIsLazy) return
        propagator!!.notifyBacktrack(newLevel)
    }

    // external_propagate.cpp: ask_decision. A suggested decision literal, or 0.
    private fun askDecision(): Int {
        if (!externalProp || externalPropIsLazy) return 0
        check(!unsat && conflict == CREF_NONE)
        notifyAssignments()
        val levelBefore = level
        forcedBacktAllowed = true
        val elit = propagator!!.cbDecide()
        forcedBacktAllowed = false
        if (levelBefore != level) {
            propagate()
            check(!unsat && conflict == CREF_NONE) { "propagation after force_backtrack produced a conflict" }
            notifyAssignments()
            // In case the propagator forced to backtrack below the pseudo decision levels,
            // we must go back to the CDCL loop instead of making a decision.
            if (level < assumptions.size) return 0
        }
        if (elit == 0) return 0
        check(externalObserved(elit)) { "cb_decide returned $elit over an unobserved variable" }
        val ilit = elit
        // Proposed decision variable is already assigned, falling back to internal decision.
        if (fixed(ilit) != 0 || valOfLit(ilit) != 0) return 0
        return ilit
    }

    // propagate.cpp: search_assign_driving
    private fun searchAssignDriving(lit: Int, c: Int) {
        assign(lit, c, 'C')
        notifyAssignments()
    }

    // propagate.cpp: search_assign_external
    private fun searchAssignExternal(lit: Int) {
        assign(lit, CREF_EXTERNAL, 'E')
        notifyAssignments()
    }

    // =========================================================================
    // solve loop (internal.cpp cdcl_loop, inprocessing disabled)
    // =========================================================================
    private fun solveLoop(): Int {
        // These two early UNSAT returns are root-level UNSAT independent of any assumptions
        // (empty formula / root-propagation conflict), so no assumption is falsified on the
        // trail: the failed-assumption core is empty and failed() stays all-false, which is the
        // correct IPASIR answer here. Only the assumption-dependent UNSAT below runs computeFailed().
        if (unsat) { tr("RESULT UNSAT"); return 20 }
        // Restore to the root before (re-)solving, as upstream already_solved() does
        // (internal.cpp: backtrack to level 0, then propagate). A previous solve may have
        // returned SAT with a dirty level>0 trail; without this a clause added since then
        // would be examined over a stale trail instead of as a normal root propagation.
        // backtrack(0) also clamps `propagated` to the level-0 trail, so the propagate()
        // below re-scans the new clause at level 0.
        if (level > 0) backtrack(0)
        initAverages()
        averagesSwapped = false
        if (!propagate()) {
            analyze()
            if (unsat) { tr("RESULT UNSAT"); return 20 }
        }
        limStabilize = OPT_stabilizeinit

        var res = 0
        while (res == 0) {
            if (unsat) res = 20
            else if (!propagate()) analyze()
            else if (iterating) iterating = false
            else if (!externalPropagate() || unsat) { // external propagation
                if (unsat) continue
                else analyze()
            } else if (satisfied()) { // found model
                if (!externalCheckSolution() || unsat) {
                    if (unsat) continue
                    else analyze()
                } else if (satisfied()) res = 10
            }
            else if (restarting()) restart()
            else if (reducing()) reduce()
            else res = decide() // 0 continue, 20 if an assumption is falsified
        }

        if (res == 10) {
            captureModel()
            tr("RESULT SAT")
        } else {
            // Compute the failed-assumption core eagerly, while level/reason/trail are
            // still intact (solve() backtracks to level 0 immediately after this returns).
            // assume.cpp lazily calls failing() from failed(); here it must run before the
            // rollback. failed(): if (!marked_failed) { failing (); marked_failed = true; }
            if (!markedFailed) {
                computeFailed()
                markedFailed = true
                failedValid = true
            }
            tr("RESULT UNSAT")
        }
        return res
    }

    private fun captureModel() {
        model = signedCharArray(maxVar + 1)
        for (i in 1..maxVar) model[i] = vals[i]
    }

    // =========================================================================
    // Public SatSolver API
    // =========================================================================
    override fun addClause(literals: IntArray) {
        require(!solving) { "addClause: not allowed during solving (e.g. from a propagator callback)" } // REQUIRE_VALID_STATE
        unsatisfiedState = false
        if (unsat) return
        addClauseInternal(literals)
    }

    override fun solve(): SatResult {
        require(!solving) { "solve: not allowed during solving" } // REQUIRE_READY_STATE
        resetFailed()
        solving = true
        val r = try {
            solveLoop()
        } finally {
            solving = false
        }
        unsatisfiedState = r == 20
        return if (r == 10) SatResult.SAT else SatResult.UNSAT
    }

    // Drop any core from a previous UNSAT solve so a stale result can't leak into failed()
    // (assume.cpp clears failed bits per incremental phase in reset_assumptions).
    private fun resetFailed() {
        failedValid = false
        for (i in 1..maxVar) failedBits[i] = 0
    }

    /**
     * Solve UNDER the given [assumptions] (signed DIMACS literals); see [SatSolver.solve].
     * The assumptions are consumed as forced decisions in [decide]; after the solve the trail
     * is rolled back to level 0 so the same instance can be solved again under different
     * assumptions on the same clause set. On SAT, [valueOf] is the model of this solve; on
     * UNSAT, [failed] gives the failed-assumption core.
     */
    override fun solve(assumptions: IntArray): SatResult {
        require(!solving) { "solve: not allowed during solving" } // REQUIRE_READY_STATE
        this.assumptions = assumptions
        resetFailed()
        solving = true
        val r = try {
            solveLoop()
        } finally {
            // roll back the assumption-forced prefix so the instance is reusable
            if (level > 0) backtrack(0)
            this.assumptions = IntArray(0)
            solving = false
        }
        unsatisfiedState = r == 20
        return if (r == 10) SatResult.SAT else SatResult.UNSAT
    }

    override fun valueOf(v: Int): Boolean {
        // v is 1..numVars DIMACS. A variable that appeared in no clause was never created
        // (lazy, like the C reference); report false for it (a don't-care).
        if (v < 1 || v >= model.size) return false
        return model[v].toInt() > 0
    }

    /**
     * IPASIR failed(): true iff the signed DIMACS assumption [lit] is in the failed core of
     * the last UNSAT-under-assumptions solve (assume.cpp Internal::failed). The core is
     * computed eagerly at the UNSAT exit (see solveLoop); here we just read the stored bit.
     * As in solver.cpp, only allowed in the unsatisfied state (last solve returned UNSAT, no
     * clause added since); an UNSAT that no assumption caused has an empty core.
     */
    override fun failed(lit: Int): Boolean {
        require(!solving) { "failed: not allowed during solving" } // REQUIRE_VALID_STATE
        require(lit != 0 && lit != Int.MIN_VALUE) { "invalid literal $lit" } // REQUIRE_VALID_LIT
        check(unsatisfiedState) { "can only get failed assumptions in unsatisfied state" } // solver.cpp: REQUIRE
        if (!failedValid) return false
        val idx = vidx(lit)
        if (idx < 1 || idx > maxVar) return false // External::failed: eidx > max_var -> 0
        return (failedBits[idx].toInt() and bign(lit)) != 0
    }

    // =========================================================================
    // Public IPASIR-UP API (solver.cpp / external.cpp, "IPASIR-UP BEGIN".."END").
    // REQUIRE_VALID_STATE == not while solving (i.e. not from inside a callback).
    // =========================================================================

    // solver.cpp: connect_external_propagator. A previously connected propagator is
    // disconnected first, as upstream does.
    override fun connectExternalPropagator(propagator: ExternalPropagator) {
        require(!solving) { "connectExternalPropagator: not allowed during solving" }
        if (this.propagator != null) disconnectExternalPropagator()
        this.propagator = propagator
        connectPropagator()
        externalProp = true
        externalPropIsLazy = propagator.isLazy
    }

    // solver.cpp: disconnect_external_propagator (set_tainted_literal is ILB-only: omitted)
    override fun disconnectExternalPropagator() {
        require(!solving) { "disconnectExternalPropagator: not allowed during solving" }
        if (propagator != null) resetObservedVars()
        propagator = null
        externalProp = false
        externalPropIsLazy = true
    }

    // external.cpp: External::add_observed_var. Upstream silently ignores the call without a
    // propagator; cadical.hpp states a variable can not be observed without one, so fail.
    override fun addObservedVar(v: Int) {
        require(v != 0 && v != Int.MIN_VALUE) { "addObservedVar: invalid literal $v" }
        // external.cpp: without a connected propagator there is nothing to observe for, so the
        // observed flag is not set (upstream only logs this).
        val p = propagator ?: return
        val eidx = vidx(v)
        if (eidx <= maxVar && isObserved[eidx]) return
        ensureVar(eidx) // freeze -> internalize: creates the variable
        isObserved[eidx] = true
        internalAddObservedVar(v)
        if (p.isLazy) return
        // An already fixed variable can not be unassigned, so notify it explicitly now.
        val tmp = fixed(v)
        if (tmp == 0) return
        val unit = if (tmp < 0) -v else v
        check(level == 0) { "add_observed_var must have backtracked to the root" } // external.cpp assert
        p.notifyAssignment(intArrayOf(unit))
    }

    // external.cpp: External::remove_observed_var (no-op without a propagator, as upstream)
    override fun removeObservedVar(v: Int) {
        require(!solving) { "removeObservedVar: not allowed during solving" }
        require(v != 0 && v != Int.MIN_VALUE) { "removeObservedVar: invalid literal $v" }
        if (propagator == null) return
        val eidx = vidx(v)
        if (eidx > maxVar) return
        if (isObserved[eidx]) {
            internalRemoveObservedVar(v)
            isObserved[eidx] = false
        }
    }

    // external.cpp: External::reset_observed_vars (upstream asserts a connected propagator)
    override fun resetObservedVars() {
        checkNotNull(propagator) { "resetObservedVars: no external propagator connected" }
        notified = 0
        for (eidx in 1..maxVar) {
            if (isObserved[eidx]) {
                internalRemoveObservedVar(eidx)
                isObserved[eidx] = false
            }
        }
    }

    // =========================================================================
    // Fixed-assignment listener (solver.cpp connect_fixed_listener /
    // disconnect_fixed_listener). REQUIRE_VALID_STATE == not while solving.
    // =========================================================================
    override fun connectFixedListener(listener: FixedAssignmentListener) {
        require(!solving) { "connectFixedListener: not allowed during solving" }
        if (fixedListener != null) disconnectFixedListener()
        fixedListener = listener
        // Listeners are treated as real-time listeners, thus previously found fixed
        // assignments are not sent out (solver.cpp).
    }

    override fun disconnectFixedListener() {
        require(!solving) { "disconnectFixedListener: not allowed during solving" }
        fixedListener = null
    }

    // =========================================================================
    // Forced phases (solver.cpp / external.cpp / phases.cpp phase, unphase).
    // REQUIRE_VALID_OR_SOLVING_STATE: also allowed during solving. e2i is the identity.
    // =========================================================================
    override fun phase(lit: Int) {
        require(lit != 0 && lit != Int.MIN_VALUE) { "phase: invalid literal $lit" } // REQUIRE_VALID_LIT
        // External::phase: internalize creates the variable if it is new
        ensureVar(vidx(lit))
        // Internal::phase
        val idx = vidx(lit)
        val oldForcedPhase = phaseForced[idx]
        val newForcedPhase: Byte = if (lit < 0) (-1).toByte() else 1.toByte()
        if (oldForcedPhase == newForcedPhase) return // forced phase remains
        phaseForced[idx] = newForcedPhase
    }

    override fun unphase(lit: Int) {
        require(lit != 0 && lit != Int.MIN_VALUE) { "unphase: invalid literal $lit" } // REQUIRE_VALID_LIT
        // External::unphase: resetting the forced phase of an unused external is ignored
        val eidx = vidx(lit)
        if (eidx > maxVar) return
        // Internal::unphase
        val idx = eidx
        val oldForcedPhase = phaseForced[idx]
        if (oldForcedPhase.toInt() == 0) return // forced phase already reset
        phaseForced[idx] = 0
    }

    // external.cpp: External::is_decision
    override fun isDecision(lit: Int): Boolean {
        require(lit != 0 && lit != Int.MIN_VALUE) { "isDecision: invalid literal $lit" }
        if (vidx(lit) > maxVar) return false
        return internalIsDecision(lit)
    }

    // external.cpp: External::force_backtrack. Upstream takes a size_t level.
    override fun forceBacktrack(newLevel: Int) {
        require(newLevel >= 0) { "forceBacktrack: negative level $newLevel" }
        if (propagator == null) return
        internalForceBacktrack(newLevel)
    }
}

private const val HEAP_INVALID = -1

private fun signedCharArray(n: Int): ByteArray = ByteArray(n)

/** Minimal growable int list (avoids boxing; mirrors the flat-array style of the C port). */
class IntArrayList {
    private var a = IntArray(16)
    var size = 0
        private set
    fun add(x: Int) { if (size == a.size) a = a.copyOf(a.size * 2); a[size++] = x }
    operator fun get(i: Int): Int = a[i]
    operator fun set(i: Int, v: Int) { a[i] = v }
    fun removeLast() { size-- }
    fun removeAt(i: Int) { for (k in i until size - 1) a[k] = a[k + 1]; size-- }
    fun clear() { size = 0 }
    fun shrinkTo(n: Int) { size = n }
    fun toArray(): IntArray = a.copyOf(size)
    fun contains(x: Int): Boolean { for (k in 0 until size) if (a[k] == x) return true; return false }
}

/** Minimal growable boolean list, parallel to [IntArrayList] for the watcher 'bin' flag. */
class BooleanList {
    private var a = BooleanArray(16)
    var size = 0
        private set
    fun add(x: Boolean) { if (size == a.size) a = a.copyOf(a.size * 2); a[size++] = x }
    operator fun get(i: Int): Boolean = a[i]
    operator fun set(i: Int, v: Boolean) { a[i] = v }
    fun removeAt(i: Int) { for (k in i until size - 1) a[k] = a[k + 1]; size-- }
    fun clear() { size = 0 }
    fun shrinkTo(n: Int) { size = n }
}
