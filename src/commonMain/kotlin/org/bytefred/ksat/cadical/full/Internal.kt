package org.bytefred.ksat.cadical.full

import kotlin.math.abs
import org.bytefred.ksat.cadical.IntArrayList

/*
 * internal.cpp (CaDiCaL 2.1.3): growing the per-variable tables, adding original clauses,
 * the CDCL loop with interleaved inprocessing, limit initialization, preprocessing, local
 * search, 'solve', 'lookahead', 'finalize' and clause traversal.
 *
 * Not here: the constructor (InternalHpp.kt, 'init' block, and 'external_reason_clause'
 * there). The destructor only frees memory (garbage collected in Kotlin) and stops active
 * profiles (not ported), so it has no counterpart.
 *
 * Dropped as PORTING.md says: LOG, PHASE, START/STOP, 'report (...)'.
 */

/*------------------------------------------------------------------------*/

// Values in 'vals' can be accessed in the range '[-max_var,max_var]' that
// is directly by a literal.  Upstream shifts the start of 'vals' by 'vsize';
// in Kotlin 'vals' is indexed by 'vsize + lit' (see InternalHpp.kt).

internal fun Internal.enlargeVals(newVsize: Int) {
    val bytes = 2 * newVsize
    val newVals = ByteArray(bytes) // zero initialized as with 'memset'
    // 'new_vals += new_vsize' -> offset 'newVsize'.

    if (vals.isNotEmpty()) {
        // memcpy (new_vals - max_var, vals - max_var, 2u * max_var + 1u);
        vals.copyInto(newVals, newVsize - maxVar, vsize - maxVar, vsize - maxVar + 2 * maxVar + 1)
    } else
        check(vsize == 0) { "vals unallocated but vsize = $vsize" }
    vals = newVals
}

/*------------------------------------------------------------------------*/

// The three 'enlarge_init', 'enlarge_only', 'enlarge_zero' templates: grow only if the table
// is smaller than 'N', new elements get the init value ('T ()' for objects, zero for numbers).

private fun enlargeInit(v: IntArray, n: Int, i: Int): IntArray = if (v.size < n) v.resized(n, i) else v

private fun enlargeInit(v: ByteArray, n: Int, i: Byte): ByteArray = if (v.size < n) v.resized(n, i) else v

private inline fun <T> enlargeOnly(v: MutableList<T>, n: Int, init: () -> T) {
    if (v.size < n) v.resize(n, init)
}

private fun enlargeZero(v: IntArray, n: Int): IntArray = enlargeInit(v, n, 0)

private fun enlargeZero(v: ByteArray, n: Int): ByteArray = enlargeInit(v, n, 0)

private fun enlargeZero(v: LongArray, n: Int): LongArray = if (v.size < n) v.resized(n, 0L) else v

private fun enlargeZero(v: DoubleArray, n: Int): DoubleArray = if (v.size < n) v.resized(n, 0.0) else v

/*------------------------------------------------------------------------*/

internal fun Internal.enlarge(newMaxVar: Int) {
    // New variables can be created that can invoke enlarge anytime (via calls
    // during ipasir-up call-backs), thus assuming (!level) is not correct
    var newVsize = if (vsize != 0) 2 * vsize else 1 + newMaxVar
    while (newVsize <= newMaxVar) newVsize *= 2
    // Ordered in the size of allocated memory (larger block first).
    if (lrat || frat) unitClausesIdx = enlargeZero(unitClausesIdx, 2 * newVsize)
    enlargeOnly(wtab, 2 * newVsize) { Watches() }
    enlargeOnly(vtab, newVsize) { Var() }
    parents = enlargeZero(parents, newVsize)
    enlargeOnly(links, newVsize) { Link() }
    btab = enlargeZero(btab, newVsize)
    gtab = enlargeZero(gtab, newVsize)
    stab = enlargeZero(stab, newVsize)
    ptab = enlargeInit(ptab, 2 * newVsize, -1)
    enlargeOnly(ftab, newVsize) { Flags() }
    enlargeVals(newVsize)
    vsize = newVsize
    if (external != null) relevanttab = enlargeZero(relevanttab, newVsize)
    val v: Byte = if (opts.phase != 0) 1 else -1
    phases.saved = enlargeInit(phases.saved, newVsize, v)
    phases.forced = enlargeZero(phases.forced, newVsize)
    phases.target = enlargeZero(phases.target, newVsize)
    phases.best = enlargeZero(phases.best, newVsize)
    phases.prev = enlargeZero(phases.prev, newVsize)
    phases.min = enlargeZero(phases.min, newVsize)
    marks = enlargeZero(marks, newVsize)
}

internal fun Internal.initVars(newMaxVar: Int) {
    if (newMaxVar <= maxVar) return
    // New variables can be created that can invoke enlarge anytime (via calls
    // during ipasir-up call-backs), thus assuming (!level) is not correct
    if (newMaxVar >= vsize) enlarge(newMaxVar)
    // '#ifndef NDEBUG' check that the new table slots are cleared: not in the release reference.
    check(btab[0] == 0L) { "btab[0] set" }
    val oldMaxVar = maxVar
    maxVar = newMaxVar
    initQueue(oldMaxVar, newMaxVar)
    initScores(oldMaxVar, newMaxVar)
    val initialized = newMaxVar - oldMaxVar
    stats.vars += initialized
    stats.unused += initialized
    stats.inactive += initialized
}

internal fun Internal.addOriginalLit(lit: Int) {
    check(abs(lit) <= maxVar) { "literal $lit exceeds max_var $maxVar" }
    if (lit != 0) {
        original.add(lit)
    } else {
        val id = if (originalId < reservedIds) ++originalId else ++clauseId
        val external = external!!
        proof?.let { proof ->
            // Use the external form of the clause for printing in proof
            // Externalize(internalized literal) != external literal
            check(original.size == 0 || !external.eclause.isEmpty()) { "missing external clause" }
            proof.addExternalOriginalClause(id, false, external.eclause)
        }
        if (opts.check != 0 && (opts.checkwitness != 0 || opts.checkfailed != 0)) {
            val forgettable = fromPropagator && extClauseForgettable
            if (forgettable && opts.check != 0) {
                check(original.size == 0 || !external.eclause.isEmpty()) { "missing external clause" }

                // First integer is the presence-flag (even if the clause is empty)
                val saved = IntArrayList()
                saved.add(1)
                external.forgettableOriginal[id] = saved

                for (k in 0 until external.eclause.size) external.forgettableOriginal[id]!!.add(external.eclause[k])
            }
        }

        addNewOriginalClause(id)
        original.clear()
    }
}

internal fun Internal.finishAddedClauseWithId(lit: Long, restore: Boolean = false) {
    // Upstream names the parameter 'id' in the definition ('lit' in the declaration).
    val id = lit
    proof?.let { proof ->
        // Use the external form of the clause for printing in proof
        // Externalize(internalized literal) != external literal
        check(original.size == 0 || !external!!.eclause.isEmpty()) { "missing external clause" }
        proof.addExternalOriginalClause(id, false, external!!.eclause, restore)
    }
    addNewOriginalClause(id)
    original.clear()
}

/*------------------------------------------------------------------------*/

internal fun Internal.reserveIds(number: Int) {
    // return;
    check(number >= 0) { "negative number of reserved ids" }
    check(clauseId == 0L && reservedIds == 0L && originalId == 0L) { "ids already in use" }
    reservedIds = number.toLong()
    clauseId = reservedIds
    proof?.beginProof(reservedIds)
}

/*------------------------------------------------------------------------*/

// This is the main CDCL loop with interleaved inprocessing.

internal fun Internal.cdclLoopWithInprocessing(): Int {

    var res = 0

    while (res == 0) {
        if (unsat) res = 20
        else if (unsatConstraint) res = 20
        else if (!propagate()) analyze() // propagate and analyze
        else if (iterating) iterate() // report learned unit
        else if (!externalPropagate() || unsat) { // external propagation
            if (unsat) continue
            else analyze()
        } else if (satisfied()) { // found model
            if (!externalCheckSolution() || unsat) {
                if (unsat) continue
                else analyze()
            } else if (satisfied()) res = 10
        } else if (searchLimitsHit()) break // decision or conflict limit
        else if (terminatedAsynchronously()) // externally terminated
            break
        else if (restarting()) restart() // restart by backtracking
        else if (rephasing()) rephase() // reset variable phases
        else if (reducing()) reduce() // collect useless clauses
        else if (probing()) probe() // failed literal probing
        else if (subsuming()) subsume() // subsumption algorithm
        else if (eliminating()) elim() // variable elimination
        else if (compacting()) compact() // collect variables
        else if (conditioning()) condition() // globally blocked clauses
        else res = decide() // next decision
    }

    return res
}

internal fun Internal.propagateAssumptions(): Int {
    proof?.solveQuery()
    if (opts.ilb != 0) {
        if (opts.ilbassumptions != 0) sortAndReuseAssumptions()
        stats.ilbtriggers++
        stats.ilbsuccess += if (level > 0) 1 else 0
        stats.levelsreused += level
        if (level != 0) {
            check(control.size > 1) { "missing control level" }
            stats.literalsreused += numAssigned - control[1].trail
        }
    }
    initSearchLimits()
    initReportLimits()

    var res = alreadySolved() // root-level propagation is done here

    var lastAssumptionLevel = assumptions.size
    if (constraint.size != 0) lastAssumptionLevel++

    if (res == 0) {
        restoreClauses()
        while (res == 0) {
            if (unsat) res = 20
            else if (unsatConstraint) res = 20
            else if (!propagate()) {
                // let analyze run to get failed assumptions
                analyze()
            } else if (!externalPropagate() || unsat) { // external propagation
                if (unsat) continue
                else analyze()
            } else if (satisfied()) { // found model
                if (!externalCheckSolution() || unsat) {
                    if (unsat) continue
                    else analyze()
                } else if (satisfied()) res = 10
            } else if (searchLimitsHit()) break // decision or conflict limit
            else if (terminatedAsynchronously()) // externally terminated
                break
            else {
                if (level >= lastAssumptionLevel) break
                res = decide()
            }
        }
    }

    if (unsat || unsatConstraint) res = 20

    if (res == 0 && satisfied()) res = 10

    finalize(res)
    resetSolving()
    reportSolving(res)

    return res
}

internal fun Internal.getEntrailedLiterals(entrailed: IntArrayList) {

    for (i in 0 until trail.size) entrailed.add(trail[i])
}

/*------------------------------------------------------------------------*/

// Most of the limits are only initialized in the first 'solve' call and
// increased as in a stand-alone non-incremental SAT call except for those
// explicitly marked as being reset below.

internal fun Internal.initReportLimits() {
    reported = false
    lim.report = 0
}

internal fun Internal.initPreprocessingLimits() {

    val incremental = lim.initialized

    /*----------------------------------------------------------------------*/

    if (!incremental) {
        // int64_t + double: computed in double, truncated on assignment.
        lim.subsume = (stats.conflicts + scale(opts.subsumeint.toDouble())).toLong()
    }

    /*----------------------------------------------------------------------*/

    if (!incremental) {
        last.elim.marked = -1
        lim.elim = (stats.conflicts + scale(opts.elimint.toDouble())).toLong()
    }

    // Initialize and reset elimination bounds in any case.

    lim.elimbound = opts.elimboundmin.toLong()

    /*----------------------------------------------------------------------*/

    if (!incremental) {

        last.ternary.marked = -1 // TODO explain why this is necessary.

        lim.compact = stats.conflicts + opts.compactint
    }

    /*----------------------------------------------------------------------*/

    if (!incremental) {
        lim.probe = stats.conflicts + opts.probeint
    }

    /*----------------------------------------------------------------------*/

    if (!incremental) {
        lim.condition = stats.conflicts + opts.conditionint
    }

    /*----------------------------------------------------------------------*/

    // Initial preprocessing rounds.

    if (inc.preprocessing <= 0) {
        lim.preprocessing = 0
    } else {
        lim.preprocessing = inc.preprocessing
    }
}

internal fun Internal.initSearchLimits() {

    val incremental = lim.initialized

    /*----------------------------------------------------------------------*/

    if (!incremental) {
        last.reduce.conflicts = -1
        lim.reduce = stats.conflicts + opts.reduceint
    }

    /*----------------------------------------------------------------------*/

    if (!incremental) {
        lim.flush = opts.flushint.toLong()
        inc.flush = opts.flushint.toLong()
    }

    /*----------------------------------------------------------------------*/

    // Initialize or reset 'rephase' limits in any case.

    lim.rephase = stats.conflicts + opts.rephaseint
    lim.rephased[1] = 0
    lim.rephased[0] = lim.rephased[1]

    /*----------------------------------------------------------------------*/

    // Initialize or reset 'restart' limits in any case.

    lim.restart = stats.conflicts + opts.restartint

    /*----------------------------------------------------------------------*/

    if (!incremental) {
        stable = opts.stabilize != 0 && opts.stabilizeonly != 0
        initAverages()
    } else if (opts.stabilize != 0 && opts.stabilizeonly != 0) {
        check(stable) { "forced stable phase lost" }
    } else if (stable) {
        stable = false
        swapAverages()
    }

    inc.stabilize = opts.stabilizeint.toLong()
    lim.stabilize = stats.conflicts + inc.stabilize

    if (opts.stabilize != 0 && opts.reluctant != 0) {
        reluctant.enable(opts.reluctant, opts.reluctantmax.toLong())
    } else
        reluctant.disable()

    /*----------------------------------------------------------------------*/

    // Conflict and decision limits.

    if (inc.conflicts < 0) {
        lim.conflicts = -1
    } else {
        lim.conflicts = stats.conflicts + inc.conflicts
    }

    if (inc.decisions < 0) {
        lim.decisions = -1
    } else {
        lim.decisions = stats.decisions + inc.decisions
    }

    /*----------------------------------------------------------------------*/

    // Initial preprocessing rounds.

    if (inc.localsearch <= 0) {
        lim.localsearch = 0
    } else {
        lim.localsearch = inc.localsearch
    }

    /*----------------------------------------------------------------------*/

    lim.initialized = true
}

/*------------------------------------------------------------------------*/

// 'round' only feeds the (dropped) PHASE messages, as upstream's '(void) round'.
internal fun Internal.preprocessRound(round: Int): Boolean = tracePhase("preprocess") {
    preprocessRoundBody()
}

// Body of 'preprocess_round' inside the 'LSTRACE_PHASE ("preprocess")' guard.
private fun Internal.preprocessRoundBody(): Boolean {
    if (unsat) return false
    if (maxVar == 0) return false
    // 'before.clauses' / 'after.clauses' (stats.current.irredundant) only feed PHASE messages.
    val beforeVars: Long = active().toLong()
    stats.preprocessings++
    check(!preprocessing) { "already preprocessing" }
    preprocessing = true
    val oldElimbound = lim.elimbound.toInt() // 'int old_elimbound = lim.elimbound;'
    if (opts.probe != 0) probe(false)
    if (opts.elim != 0) elim(false)
    if (opts.condition != 0) condition(false)
    val afterVars: Long = active().toLong()
    check(preprocessing) { "preprocessing flag lost" }
    preprocessing = false
    if (unsat) return false
    if (afterVars < beforeVars) return true
    if (oldElimbound.toLong() < lim.elimbound) return true
    return false
}

internal fun Internal.preprocess(): Int {
    var i = 0
    while (i < lim.preprocessing) {
        if (!preprocessRound(i)) break
        i++
    }
    if (unsat) return 20
    return 0
}

/*------------------------------------------------------------------------*/

internal fun Internal.tryToSatisfyFormulaBySavedPhases(): Int {
    check(level == 0) { "not on root level" }
    check(!forceSavedPhase) { "saved phase already forced" }
    check(propagated == trail.size) { "not fully propagated" }
    forceSavedPhase = true
    if (externalProp) {
        check(level == 0) { "not on root level" }
        privateSteps = true
    }
    var res = 0
    while (res == 0) {
        if (satisfied()) {
            res = 10
        } else if (decide() != 0) {
            res = 20
        } else if (!propagate()) {
            check(level > 0) { "conflict on root level" }
            backtrack()
            conflict = null // ignore conflict
            check(res == 0)
            break
        }
    }
    check(forceSavedPhase) { "saved phase not forced" }
    forceSavedPhase = false
    if (externalProp) {
        privateSteps = false
        if (level == 0) notifyAssignments() // In case fixed assignments were found.
        else {
            renotifyTrailAfterLocalSearch()
        }
    }
    return res
}

/*------------------------------------------------------------------------*/

internal fun Internal.produceFailedAssumptions() {
    check(level == 0) { "not on root level" }
    check(!assumptions.isEmpty()) { "no assumptions" }
    while (!unsat) {
        check(!satisfied()) { "satisfied while producing failed assumptions" }
        notifyAssignments()
        if (decide() != 0) break
        while (!unsat && !propagate()) analyze()
    }
    notifyAssignments()
}

/*------------------------------------------------------------------------*/

internal fun Internal.localSearchRound(round: Int): Int {

    check(round > 0) { "non-positive local search round" }

    if (unsat) return 0 // 'return false'
    if (maxVar == 0) return 0 // 'return false'

    startOuterWalk()
    check(!localsearching) { "already local searching" }
    localsearching = true

    // Determine propagation limit quadratically scaled with rounds.
    //
    var limit: Long = opts.walkmineff.toLong()
    limit *= round
    if (Long.MAX_VALUE / round > limit) limit *= round
    else limit = Long.MAX_VALUE

    val res = walkRound(limit, true)

    check(localsearching) { "local search flag lost" }
    localsearching = false
    stopOuterWalk()

    return res
}

internal fun Internal.localSearch(): Int {

    if (unsat) return 0
    if (maxVar == 0) return 0
    if (opts.walk == 0) return 0
    if (constraint.size != 0) return 0

    var res = 0

    var i = 1
    while (res == 0 && i <= lim.localsearch) {
        res = localSearchRound(i)
        i++
    }

    if (res == 10) {
        check(stats.walk.minimum == 0L) { "walk minimum not zero on satisfiable local search" }
        res = tryToSatisfyFormulaBySavedPhases()
    } else if (res == 20) {
        check(!assumptions.isEmpty()) { "inconsistent local search without assumptions" }
        produceFailedAssumptions()
    }

    return res
}

/*------------------------------------------------------------------------*/

// if preprocess_only is false and opts.ilb is true we do not preprocess
// such that we do not have to backtrack to level 0.
// TODO: check restore_clauses works on higher level
//
internal fun Internal.solve(preprocessOnly: Boolean = false): Int {
    check(clause.isEmpty()) { "clause not empty at solve" }
    proof?.solveQuery()
    if (opts.ilb != 0) {
        if (opts.ilbassumptions != 0) sortAndReuseAssumptions()
        stats.ilbtriggers++
        stats.ilbsuccess += if (level > 0) 1 else 0
        stats.levelsreused += level
        if (level != 0) {
            check(control.size > 1) { "missing control level" }
            stats.literalsreused += numAssigned - control[1].trail
        }
        if (external!!.propagator != null) renotifyTrailAfterIlb()
    }
    initReportLimits()
    var res = alreadySolved()
    if (res == 0 && preprocessOnly && level != 0) backtrack()
    if (res == 0) res = restoreClauses()
    if (res == 0) {
        initPreprocessingLimits()
        if (!preprocessOnly) initSearchLimits()
    }
    if (res == 0 && level == 0) res = preprocess()
    if (!preprocessOnly) {
        if (res == 0 && level == 0) res = localSearch()
        if (res == 0 && level == 0) res = luckyPhases()
        if (res == 0 || (res == 10 && externalProp)) {
            if (res == 10 && externalProp && level != 0) backtrack()
            res = cdclLoopWithInprocessing()
        }
    }
    finalize(res)
    resetSolving()
    reportSolving(res)
    return res
}

internal fun Internal.alreadySolved(): Int {
    var res = 0
    if (unsat || unsatConstraint) {
        res = 20
    } else {
        if (level != 0 && opts.ilb == 0) backtrack()
        if (level == 0 && !propagate()) {
            learnEmptyClause()
            res = 20
        }
        if (maxVar == 0 && res == 0) res = 10
    }
    return res
}

// Upstream: report ('1'), report ('0') or report ('?') depending on 'res'; 'report' is
// dropped (PORTING.md), so nothing remains.
internal fun Internal.reportSolving(res: Int) {
}

internal fun Internal.resetSolving() {
    if (terminationForced) {

        // TODO this leads potentially to a data race if the external
        // user is calling 'terminate' twice within one 'solve' call.
        // A proper solution would be to guard / protect setting the
        // 'termination_forced' flag and only allow it during solving and
        // ignore it otherwise thus also the second time it is called during a
        // 'solve' call.  We could move resetting it also the start of
        // 'solve'.
        //
        terminationForced = false
    }
}

internal fun Internal.restoreClauses(): Int {
    var res = 0
    if (opts.restoreall <= 1 && external!!.tainted.isEmpty()) {
        // report ('*');
    } else {
        // report ('+');
        // remove_garbage_binaries ();
        external!!.restoreClauses()
        // internal->report ('r');
        if (!unsat && level == 0 && !propagate()) {
            learnEmptyClause()
            res = 20
        }
    }
    return res
}

internal fun Internal.lookahead(): Int {
    check(clause.isEmpty()) { "clause not empty at lookahead" }
    check(!lookingahead) { "already looking ahead" }
    lookingahead = true
    if (externalProp) {
        if (level != 0) {
            // Combining lookahead with external propagator is limited
            // Note that lookahead_probing (); would also force backtrack anyway
            backtrack()
        }
        privateSteps = true
    }
    var tmp = alreadySolved()
    if (tmp == 0) tmp = restoreClauses()
    var res = 0
    if (tmp == 0) res = lookaheadProbing()
    if (res == Int.MIN_VALUE) res = 0
    resetSolving()
    reportSolving(tmp)
    check(lookingahead) { "lookahead flag lost" }
    lookingahead = false
    if (externalProp) {
        privateSteps = false
        notifyAssignments() // In case fixed assignments were found.
    }
    return res
}

/*------------------------------------------------------------------------*/

internal fun Internal.finalize(res: Int) {
    val proof = proof ?: return
    val external = external!!
    // finalize external units
    if (frat) {
        for (evar in external.vars) {
            check(evar > 0)
            val eidx = 2 * evar
            var sign = 1
            var id = external.extUnits[eidx]
            if (id == 0L) {
                sign = -1
                id = external.extUnits[eidx + 1]
            }
            if (id != 0L) {
                proof.finalizeExternalUnit(id, evar * sign)
            }
        }
        // finalize internal units
        for (lit in lits) {
            val elit = externalize(lit)
            if (elit != 0) {
                val eidx = (if (elit < 0) 1 else 0) + 2 * abs(elit)
                val id = external.extUnits[eidx]
                if (id != 0L) {
                    check(unitClauses(vlit(lit)) == id) { "unit id mismatch" }
                    continue
                }
            }
            val uidx = vlit(lit)
            val id = unitClauses(uidx)
            if (id == 0L) continue
            proof.finalizeUnit(id, lit)
        }
        // See the discussion in 'propagate' on why garbage binary clauses stick
        // around.
        for (c in clauses) if (!c.garbage || c.size == 2) proof.finalizeClause(c)

        // finalize conflict and proof
        if (conflictId != 0L) {
            proof.finalizeClause(conflictId, IntArrayList())
        }
    }
    proof.reportStatus(res, conflictId)
    if (res == 10) external.concludeSat()
    else if (res == 20) concludeUnsat()
    else if (res == 0) external.concludeUnknown()
}

/*------------------------------------------------------------------------*/

internal fun Internal.printStatistics() {
    // stats.print (this);  (statistics printing is not ported, see PORTING.md)
    for (st in statTracers) st.printStats()
}

/*------------------------------------------------------------------------*/

// Only useful for debugging purposes.

internal fun Internal.dump(c: Clause) {
    for (k in 0 until c.size) print("${c.literals[k]} ")
    print("0\n")
}

internal fun Internal.dump() {
    var m: Long = assumptions.size.toLong()
    for (idx in vars) if (fixed(idx) != 0) m++
    for (c in clauses) if (!c.garbage) m++
    print("p cnf $maxVar $m\n")
    for (idx in vars) {
        val tmp = fixed(idx)
        if (tmp != 0) print("${if (tmp < 0) -idx else idx} 0\n")
    }
    for (c in clauses) if (!c.garbage) dump(c)
    for (k in 0 until assumptions.size) print("${assumptions[k]} 0\n")
}

/*------------------------------------------------------------------------*/

internal fun Internal.traverseConstraint(it: ClauseIterator): Boolean {
    if (constraint.isEmpty() && !unsatConstraint) return true

    val eclause = ArrayList<Int>()
    if (unsat) return it.clause(eclause)

    var satisfied = false
    for (k in 0 until constraint.size) {
        val ilit = constraint[k]
        val tmp = fixed(ilit)
        if (tmp > 0) {
            satisfied = true
            break
        }
        if (tmp < 0) continue
        val elit = externalize(ilit)
        eclause.add(elit)
    }
    if (!satisfied && !it.clause(eclause)) return false

    return true
}

/*------------------------------------------------------------------------*/

internal fun Internal.traverseClauses(it: ClauseIterator): Boolean {
    val eclause = ArrayList<Int>()
    if (unsat) return it.clause(eclause)
    for (c in clauses) {
        if (c.garbage) continue
        if (c.redundant) continue
        var satisfied = false
        for (k in 0 until c.size) {
            val ilit = c.literals[k]
            val tmp = fixed(ilit)
            if (tmp > 0) {
                satisfied = true
                break
            }
            if (tmp < 0) continue
            val elit = externalize(ilit)
            eclause.add(elit)
        }
        if (!satisfied && !it.clause(eclause)) return false
        eclause.clear()
    }
    return true
}
