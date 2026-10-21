package org.bytefred.ksat.cadical.full

import kotlin.concurrent.Volatile
import kotlin.math.abs
import org.bytefred.ksat.cadical.IntArrayList

/*
 * internal.hpp: the 'Internal' solver state, plus its constructor from internal.cpp and the
 * inline member functions defined in the header (including 'score_smaller' in ScoreHpp.kt,
 * 'terminated_asynchronously' and 'search_limits_hit').
 *
 * All other member functions of 'Internal' are declared in internal.hpp but defined in the
 * '.cpp' files; they are Kotlin extension functions 'internal fun Internal.foo (...)' in the
 * matching '.kt' file (see PORTING.md). Every field is therefore 'internal' (module) visible.
 *
 * Mapping of the fields (same names in camelCase, same initial values as the constructor):
 *  - 'size_t' counters and trail positions ('vsize', 'propagated', 'notified', ...) -> Int:
 *    they index Kotlin arrays and lists, which are Int indexed anyhow.
 *  - 'uint64_t' ids ('clause_id', ...) -> Long (ids stay below 2^63).
 *  - 'unsigned' table entries ('frozentab', 'relevanttab') -> IntArray holding the unsigned
 *    bit pattern ('UINT_MAX' is -1); compare with 'toUInt ()' where the sign matters.
 *  - 'signed char *vals' with the pointer shifted by 'vsize' (so 'vals[lit]' works for
 *    '-max_var <= lit <= max_var') -> ByteArray of size '2 * vsize' indexed by 'vsize + lit'.
 *    The offset is always the current 'vsize': 'enlarge_vals' (internal.cpp) allocates the
 *    new array with offset 'new_vsize' and 'enlarge' sets 'vsize = new_vsize' right after.
 *  - Per-variable / per-literal 'vector' tables that upstream only grows in 'enlarge' or
 *    rebuilds in 'compact' -> primitive arrays ('btab', 'gtab', 'stab', 'ptab', 'ntab',
 *    'parents', 'marks', 'unit_clauses_idx', 'phases.*') or ArrayLists of objects ('vtab',
 *    'ftab', 'links', 'otab', 'big', 'wtab'). 'occurring ()' / 'watching ()' test emptiness,
 *    so 'reset_occs' etc. must empty the list (or assign a zero sized array for 'ntab').
 *  - Functions returning a reference ('int64_t &bumped (lit)', 'double &score (lit)',
 *    'int &propfixed (lit)', 'int64_t &noccs (lit)', 'uint64_t &unit_clauses (lit)') -> a
 *    getter here; writes go to the table directly ('btab[vidx (lit)] = ...').
 *  - Kotlin keywords: 'Internal::val (lit)' -> [value], 'Internal::var (lit)' -> [variable].
 *  - 'Internal *internal' (proxy to 'this' in macros) -> 'this'.
 *  - Not ported (message output, see PORTING.md): 'profiles', 'error_message'.
 *  - 'static Clause external_reason_clause' (internal.cpp) is one static object shared by all
 *    solvers upstream -> [externalReasonClause].
 *  - The anonymous 'enum Mode' -> Int constants in the companion object.
 */

// static Clause external_reason_clause;
private val externalReasonClause = Clause(0)

internal class CubesWithStatus {
    var status = 0
    val cubes = ArrayList<IntArrayList>()
}

internal class Internal {

    /*----------------------------------------------------------------------*/

    // The actual internal state of the solver is set and maintained in this
    // section.  This is currently only used for debugging and testing.

    fun inMode(m: Int): Boolean = (mode and m) != 0

    fun setMode(m: Int) {
        check((mode and m) == 0)
        mode = mode or m
    }

    fun resetMode(m: Int) {
        check((mode and m) != 0)
        mode = mode and m.inv()
    }

    fun requireMode(m: Int) {
        check((mode and m) != 0)
    }

    /*----------------------------------------------------------------------*/

    var mode = SEARCH // current internal state (written only by setMode / resetMode)
        private set
    var unsat = false // empty clause found or learned
    var iterating = false // report learned unit ('i' line)
    var localsearching = false // true during local search
    var lookingahead = false // true during look ahead
    var preprocessing = false // true during preprocessing
    var protectedReasons = false // referenced reasons are protected
    var forceSavedPhase = false // force saved phase in decision
    var searchingLuckyPhases = false // during 'lucky_phases'
    var stable = false // true during stabilization phase
    var reported = false // reported in this solving call
    var externalProp = false // true if an external propagator is connected
    var didExternalProp = false // true if ext. propagation happened
    var externalPropIsLazy = true // true if the external propagator is lazy
    var forcedBacktAllowed = false // external propagator can force backtracking
    var privateSteps = false // no notification of ext. prop during these steps
    var rephased = '\u0000' // last type of resetting phases
    val reluctant = Reluctant() // restart counter in stable mode
    var vsize = 0 // actually allocated variable data size
    var maxVar = 0 // internal maximum variable index
    var clauseId = 0L // last used id for clauses
    var originalId = 0L // ids for original clauses to produce LRAT
    var reservedIds = 0L // number of reserved ids for original clauses
    var conflictId = 0L // store conflict id for finalize (frat)
    var concluded = false // keeps track of conclude
    val conclusion = ArrayList<Long>() // store ids of conclusion clauses
    var unitClausesIdx = LongArray(0) // keep track of unit_clauses (LRAT/FRAT)
    val lratChain = ArrayList<Long>() // create LRAT in solver: option lratdirect
    val miniChain = ArrayList<Long>() // used to create LRAT in minimize
    val minimizeChain = ArrayList<Long>() // used to create LRAT in minimize
    val unitChain = ArrayList<Long>() // used to avoid duplicate units
    val instChain = ArrayList<Clause>() // for LRAT in instantiate
    val probehbrChains = ArrayList<ArrayList<ArrayList<Long>>>() // only used if opts.probehbr=false
    var lrat = false // generate LRAT internally
    var frat = false // finalize non-deleted clauses in proof
    var level = 0 // decision level ('control.size () - 1')
    val phases = Phases() // saved, target and best phases
    var vals = ByteArray(0) // assignment [-max_var,max_var], index 'vsize + lit'
    var marks = ByteArray(0) // signed marks [1,max_var]
    var frozentab = IntArray(0) // frozen counters [1,max_var] (unsigned)
    val i2e = IntArrayList() // maps internal 'idx' to external 'lit'
    var relevanttab = IntArray(0) // Reference counts for observed variables (unsigned)
    val queue = Queue() // variable move to front decision queue
    val links = Links() // table of links for decision queue
    var scoreInc = 1.0 // current score increment
    val scores = ScoreSchedule(ScoreSmaller(this)) // score based decision priority queue
    var stab = DoubleArray(0) // table of variable scores [1,max_var]
    val vtab = ArrayList<Var>() // variable table [1,max_var]
    var parents = IntArray(0) // parent literals during probing
    val ftab = ArrayList<Flags>() // variable and literal flags
    var btab = LongArray(0) // enqueue time stamps for queue
    var gtab = LongArray(0) // time stamp table to recompute glue
    val otab = ArrayList<Occs>() // table of occurrences for all literals
    var ptab = IntArray(0) // table for caching probing attempts
    var ntab = LongArray(0) // number of one-sided occurrences table
    val big = ArrayList<Bins>() // binary implication graph
    val wtab = ArrayList<Watches>() // table of watches for all literals
    var conflict: Clause? = null // set in 'propagation', reset in 'analyze'
    var ignore: Clause? = null // ignored during 'vivify_propagate'
    val dummyBinary: Clause // Dummy binary clause for subsumption
    var externalReason: Clause = externalReasonClause // used as reason at external propagations
    var newestClause: Clause? = null // used in external_propagate
    var forceNoBacktrack = false // for new clauses with external propagator
    var fromPropagator = false // differentiate new clauses...
    var extClauseForgettable = false // Is new clause from propagator forgettable
    var taintedLiteral = 0 // used for ILB
    var notified = 0 // next trail position to notify external prop
    var probeReason: Clause? = null // set during probing
    var propagated = 0 // next trail position to propagate
    var propagated2 = 0 // next binary trail position to propagate
    var propergated = 0 // propagated without blocking literals
    var bestAssigned = 0 // best maximum assigned ever
    var targetAssigned = 0 // maximum assigned without conflict
    var noConflictUntil = 0 // largest trail prefix without conflict
    val trail = IntArrayList() // currently assigned literals
    val clause = IntArrayList() // simplified in parsing & learning
    val assumptions = IntArrayList() // assumed literals
    val constraint = IntArrayList() // literals of the constraint
    var unsatConstraint = false // constraint used for unsatisfiability?
    var markedFailed = true // are the failed assumptions marked?
    val original = IntArrayList() // original added literals
    val levels = IntArrayList() // decision levels in learned clause
    val analyzed = IntArrayList() // analyzed literals in 'analyze'
    val unitAnalyzed = IntArrayList() // to avoid duplicate units in lrat_chain
    val decomposed = IntArrayList() // literals skipped in 'decompose'
    val minimized = IntArrayList() // removable or poison in 'minimize'
    val shrinkable = IntArrayList() // removable or poison in 'shrink'
    val reap = Reap() // radix heap for shrink

    var numAssigned = 0 // check for satisfied

    val probes = IntArrayList() // remaining scheduled probes
    val control = ArrayList<Level>() // 'level + 1 == control.size ()'
    val clauses = ArrayList<Clause>() // ordered collection of all clauses
    val averages = Averages() // glue, size, jump moving averages
    val lim = Limit() // limits for various phases
    val last = Last() // statistics at last occurrence
    val inc = Inc() // increments on limits

    var proof: Proof? = null // abstraction layer between solver and tracers
    var lratbuilder: LratBuilder? = null // special proof tracer
    val tracers = ArrayList<Tracer>() // proof tracing objects (ie interpolant calculator)
    val fileTracers = ArrayList<FileTracer>() // file proof tracers (ie DRAT, LRAT...)
    val statTracers = ArrayList<StatTracer>() // checkers

    val opts = Options() // run-time options
    val stats = Stats() // statistics
    var forcePhaseMessages = false // force 'phase (...)' messages
    val arena = Arena() // memory arena for moving garbage collector
    var prefix = "c " // verbose messages prefix

    var external: External? = null // proxy to 'external' buddy in 'Solver'

    // Shadow trace sink (LstraceHpp.kt, not upstream): null = tracing off.
    var trace: TraceSink? = null

    /*----------------------------------------------------------------------*/

    // Asynchronous termination flag written by 'terminate' and read by
    // 'terminated_asynchronously' (the latter at the end of this header).
    @Volatile
    var terminationForced = false

    /*----------------------------------------------------------------------*/

    val vars = Range { maxVar } // Provides safe variable iteration.
    val lits = Sange { maxVar } // Provides safe literal iteration.

    init {
        control.add(Level(0, 0))

        // The 'dummy_binary' is used in 'try_to_subsume_clause' to fake a real
        // clause, which then can be used to subsume or strengthen the given
        // clause in one routine for both binary and non binary clauses.  This
        // fake binary clause is always kept non-redundant (and not-moved etc.)
        // due to the zero initialization.  Only literals will be changed.
        dummyBinary = Clause(2)
        dummyBinary.size = 2
    }

    /*----------------------------------------------------------------------*/

    // A variable is 'active' if it is not eliminated nor fixed.
    fun active(lit: Int): Boolean = flags(lit).active()

    fun active(): Int {
        val res = stats.active.toInt()
        var tmp = maxVar.toLong()
        tmp -= stats.unused
        tmp -= stats.now.fixed
        tmp -= stats.now.eliminated
        tmp -= stats.now.substituted
        tmp -= stats.now.pure
        check(tmp >= 0)
        check(tmp == res.toLong())
        return res
    }

    // Currently remaining active redundant and irredundant clauses.

    fun redundant(): Long = stats.current.redundant

    fun irredundant(): Long = stats.current.irredundant

    fun clauseVariableRatio(): Double = relative(irredundant().toDouble(), active().toDouble())

    // Unsigned literals (abs) with checks.
    fun vidx(lit: Int): Int {
        check(lit != 0)
        check(lit != Int.MIN_VALUE)
        val idx = abs(lit)
        check(idx <= maxVar)
        return idx
    }

    // Unsigned version with LSB denoting sign.  This is used in indexing
    // arrays by literals.  The idea is to keep the elements in such an array
    // for both the positive and negated version of a literal close together.
    fun vlit(lit: Int): Int = (if (lit < 0) 1 else 0) + 2 * vidx(lit)

    fun u2i(u: Int): Int {
        check(u > 1)
        var res = u / 2
        check(res <= maxVar)
        if ((u and 1) != 0) res = -res
        return res
    }

    fun unitClauses(lit: Int): Long {
        check(lrat || frat)
        return unitClausesIdx[lit]
    }

    // Helper functions to access variable and literal data.
    fun variable(lit: Int): Var = vtab[vidx(lit)]
    fun link(lit: Int): Link = links[vidx(lit)]
    fun flags(lit: Int): Flags = ftab[vidx(lit)]
    fun bumped(lit: Int): Long = btab[vidx(lit)]
    fun propfixed(lit: Int): Int = ptab[vlit(lit)]
    fun score(lit: Int): Double = stab[vidx(lit)]

    fun occurring(): Boolean = otab.isNotEmpty()
    fun watching(): Boolean = wtab.isNotEmpty()

    fun bins(lit: Int): Bins = big[vlit(lit)]
    fun occs(lit: Int): Occs = otab[vlit(lit)]
    fun noccs(lit: Int): Long = ntab[vlit(lit)]
    fun watches(lit: Int): Watches = wtab[vlit(lit)]

    // Variable bumping through exponential VSIDS (EVSIDS) as in MiniSAT.
    fun useScores(): Boolean = opts.score != 0 && stable

    // Marking variables with a sign (positive or negative).
    fun marked(lit: Int): Int {
        var res = marks[vidx(lit)].toInt()
        if (lit < 0) res = -res
        return res
    }

    fun mark(lit: Int) {
        check(marked(lit) == 0)
        marks[vidx(lit)] = sign(lit).toByte()
        check(marked(lit) > 0)
        check(marked(-lit) < 0)
    }

    fun unmark(lit: Int) {
        marks[vidx(lit)] = 0
        check(marked(lit) == 0)
    }

    // Use only bits 6 and 7 to store the sign or zero.  The remaining
    // bits can be used as additional flags.
    fun marked67(lit: Int): Int {
        var res = marks[vidx(lit)].toInt() shr 6
        if (lit < 0) res = -res
        return res
    }

    fun mark67(lit: Int) {
        val idx = vidx(lit)
        val mask = 0x3f
        val m = marks[idx].toInt()
        val bits = m and mask
        val newM = ((m and mask) or (sign(lit) shl 6)).toByte()
        marks[idx] = newM
        check(marked(lit) > 0)
        check(marked(-lit) < 0)
        check((newM.toInt() and mask) == bits)
        check(marked67(lit) > 0)
        check(marked67(-lit) < 0)
    }

    fun unmark67(lit: Int) {
        val idx = vidx(lit)
        val mask = 0x3f
        val bits = marks[idx].toInt() and mask
        marks[idx] = (marks[idx].toInt() and mask).toByte()
        check((marks[idx].toInt() and mask) == bits)
    }

    fun unmark(lits: IntArrayList) {
        for (k in 0 until lits.size) unmark(lits[k])
    }

    // The other 6 bits of the 'marks' bytes can be used as additional
    // (unsigned) marking bits.  Currently we only use the least significant
    // bit in 'condition' to mark variables in the conditional part.
    fun getbit(lit: Int, bit: Int): Boolean {
        check(0 <= bit)
        check(bit < 6)
        return (marks[vidx(lit)].toInt() and (1 shl bit)) != 0
    }

    fun setbit(lit: Int, bit: Int) {
        check(0 <= bit)
        check(bit < 6)
        check(!getbit(lit, bit))
        val idx = vidx(lit)
        marks[idx] = (marks[idx].toInt() or (1 shl bit)).toByte()
        check(getbit(lit, bit))
    }

    fun unsetbit(lit: Int, bit: Int) {
        check(0 <= bit)
        check(bit < 6)
        check(getbit(lit, bit))
        val idx = vidx(lit)
        marks[idx] = (marks[idx].toInt() and (1 shl bit).inv()).toByte()
        check(!getbit(lit, bit))
    }

    // Marking individual literals.
    fun marked2(lit: Int): Boolean {
        val res = marks[vidx(lit)].toInt()
        check(res in 0..3)
        val bit = bign(lit)
        return (res and bit) != 0
    }

    fun mark2(lit: Int) {
        val idx = vidx(lit)
        marks[idx] = (marks[idx].toInt() or bign(lit)).toByte()
        check(marked2(lit))
    }

    // Watch literal 'lit' in clause with blocking literal 'blit'.
    // Inlined here, since it occurs in the tight inner loop of 'propagate'.
    fun watchLiteral(lit: Int, blit: Int, c: Clause) {
        check(lit != blit)
        val ws = watches(lit)
        ws.add(Watch(blit, c))
    }

    // Add two watches to a clause.  This is used initially during allocation
    // of a clause and during connecting back all watches after preprocessing.
    fun watchClause(c: Clause) {
        val l0 = c.literals[0]
        val l1 = c.literals[1]
        watchLiteral(l0, l1, c)
        watchLiteral(l1, l0, c)
    }

    fun unwatchClause(c: Clause) {
        val l0 = c.literals[0]
        val l1 = c.literals[1]
        removeWatch(watches(l0), c)
        removeWatch(watches(l1), c)
    }

    // Update queue to point to last potentially still unassigned variable.
    // All variables after 'queue.unassigned' in bump order are assumed to be
    // assigned.  Then update the 'queue.bumped' field and log it.  This is
    // inlined here since it occurs in several inner loops.
    fun updateQueueUnassigned(idx: Int) {
        check(0 < idx)
        check(idx <= maxVar)
        queue.unassigned = idx
        queue.bumped = btab[idx]
    }

    // We monitor the maximum size and glue of clauses during 'reduce' and
    // thus can predict if a redundant extended clause is likely to be kept in
    // the next 'reduce' phase.  These clauses are target of subsumption and
    // vivification checks, in addition to irredundant clauses.  Their
    // variables are also marked as being 'added'.
    fun likelyToBeKeptClause(c: Clause): Boolean {
        if (!c.redundant) return true
        if (c.keep) return true
        if (c.glue > lim.keptglue) return false
        if (c.size > lim.keptsize) return false
        return true
    }

    // We mark variables in added or shrunken clauses as 'subsume' candidates
    // if the clause is likely to be kept in the next 'reduce' phase (see last
    // function above).  This gives a persistent (across consecutive
    // interleaved search and inprocessing phases) set of variables which have
    // to be reconsidered in subsumption checks, i.e., only clauses with
    // 'subsume' marked variables are checked to be forward subsumed.
    // A similar technique is used to reduce the effort in hyper ternary
    // resolution to focus on variables in new ternary clauses.
    fun markSubsume(lit: Int) {
        val f = flags(lit)
        if (f.subsume) return
        stats.mark.subsume++
        f.subsume = true
    }

    fun markTernary(lit: Int) {
        val f = flags(lit)
        if (f.ternary) return
        stats.mark.ternary++
        f.ternary = true
    }

    fun markedSubsume(lit: Int): Boolean = flags(lit).subsume

    // If irredundant clauses are removed or literals in clauses are removed,
    // then variables in such clauses should be reconsidered to be eliminated
    // through bounded variable elimination.  In contrast to 'subsume' the
    // 'elim' flag is restricted to 'irredundant' clauses only. For blocked
    // clause elimination it is better to have a more precise signed version,
    // which allows to independently mark positive and negative literals.
    fun markElim(lit: Int) {
        val f = flags(lit)
        if (f.elim) return
        stats.mark.elim++
        f.elim = true
    }

    fun markBlock(lit: Int) {
        val f = flags(lit)
        val bit = bign(lit)
        if ((f.block and bit) != 0) return
        stats.mark.block++
        f.block = f.block or bit
    }

    fun markRemoved(lit: Int) {
        markElim(lit)
        markBlock(-lit)
    }

    // The following two functions are only used for testing & debugging.

    fun markedBlock(lit: Int): Boolean {
        val f = flags(lit)
        val bit = bign(lit)
        return (f.block and bit) != 0
    }

    fun unmarkBlock(lit: Int) {
        val f = flags(lit)
        val bit = bign(lit)
        f.block = f.block and bit.inv()
    }

    // During scheduling literals for blocked clause elimination we skip those
    // literals which occur negated in a too large clause.
    fun markSkip(lit: Int) {
        val f = flags(lit)
        val bit = bign(lit)
        if ((f.skip and bit) != 0) return
        f.skip = f.skip or bit
    }

    fun markedSkip(lit: Int): Boolean {
        val f = flags(lit)
        val bit = bign(lit)
        return (f.skip and bit) != 0
    }

    // During decompose ignore literals where we already built LRAT chains
    fun markDecomposed(lit: Int) {
        val f = flags(lit)
        val bit = bign(lit)
        check((f.decompose and bit) == 0)
        decomposed.add(lit)
        f.decompose = f.decompose or bit
    }

    fun unmarkDecompose(lit: Int) {
        val f = flags(lit)
        val bit = bign(lit)
        f.decompose = f.decompose and bit.inv()
    }

    fun markedDecompose(lit: Int): Boolean {
        val f = flags(lit)
        val bit = bign(lit)
        return (f.decompose and bit) != 0
    }

    // Marked as assumption.
    fun assumed(lit: Int): Boolean {
        val f = flags(lit)
        val bit = bign(lit)
        return (f.assumed and bit) != 0
    }

    fun terminate() {
        terminationForced = true
    }

    // Get the value of an internal literal: -1=false, 0=unassigned, 1=true.
    // We use a redundant table for both negative and positive literals.  This
    // allows a branch-less check for the value of literal and is considered
    // substantially faster than negating the result if the argument is
    // negative.  We also avoid taking the absolute value.
    fun value(lit: Int): Int {
        check(-maxVar <= lit)
        check(lit != 0)
        check(lit <= maxVar)
        return vals[vsize + lit].toInt()
    }

    // As suggested by Matt Ginsberg it might be useful to factor-out a common
    // setter function for setting and resetting the value of a literal.
    fun setVal(lit: Int, v: Int) {
        check(-1 <= v)
        check(v <= 1)
        check(-maxVar <= lit)
        check(lit != 0)
        check(lit <= maxVar)
        vals[vsize + lit] = v.toByte()
        vals[vsize - lit] = (-v).toByte()
    }

    // As 'val' but restricted to the root-level value of a literal.
    // It is not that time critical and also needs to check the decision level
    // of the variable anyhow.
    fun fixed(lit: Int): Int {
        check(-maxVar <= lit)
        check(lit != 0)
        check(lit <= maxVar)
        val idx = vidx(lit)
        var res = vals[vsize + idx].toInt()
        if (res != 0 && vtab[idx].level != 0) res = 0
        if (lit < 0) res = -res
        return res
    }

    // Map back an internal literal to an external.
    fun externalize(lit: Int): Int {
        check(lit != Int.MIN_VALUE)
        val idx = abs(lit)
        check(idx != 0)
        check(idx <= maxVar)
        var res = i2e[idx]
        if (lit < 0) res = -res
        return res
    }

    // Explicit freezing and melting of variables.
    fun freeze(lit: Int) {
        val idx = vidx(lit)
        if (idx >= frozentab.size) {
            var newVsize = if (vsize != 0) 2 * vsize else 1 + maxVar
            while (newVsize <= maxVar) newVsize *= 2
            frozentab = frozentab.resized(newVsize)
        }
        val ref = frozentab[idx]
        if (ref != UINT_MAX) frozentab[idx] = ref + 1
    }

    fun melt(lit: Int) {
        val idx = vidx(lit)
        var ref = frozentab[idx]
        if (ref != UINT_MAX) {
            if (--ref == 0) {
                if (relevanttab[idx] != 0) ref++
            }
            frozentab[idx] = ref
        }
    }

    fun frozen(lit: Int): Boolean = vidx(lit) < frozentab.size && frozentab[vidx(lit)] != 0

    // We want to have termination checks inlined, particularly the first
    // function which appears in preprocessor loops.  Even though this first
    // 'termination_forced' is set asynchronously, this should not lead to a
    // data race issue (it also has been declared 'volatile').
    fun terminatedAsynchronously(factor: Int = 1): Boolean {
        // First way of asynchronous termination is through 'terminate' which sets
        // the 'termination_forced' flag directly.  The second way is through a
        // call back to a 'terminator' if it is non-zero, which however is costly.
        if (terminationForced) return true

        // This is only for testing and debugging asynchronous termination calls.
        // In production code this could be removed but then should not be costly
        // and keeping it will allow to test correctness of asynchronous
        // termination on the production platform too.  After this triggers we
        // have to set the 'termination_forced' flag, such that subsequent calls
        // to this function do not check this again.
        if (lim.terminate.forced != 0) {
            check(lim.terminate.forced > 0)
            if (lim.terminate.forced-- == 1) {
                terminationForced = true
                return true
            }
        }

        // The second way of asynchronous termination is through registering and
        // calling an external 'Terminator' object.  This is of course more costly
        // than just checking a (volatile though) boolean flag, particularly in
        // tight loops.  To avoid this cost we only call the terminator in
        // intervals of 'opts.terminateint', which in addition can be scaled up by
        // the argument 'factor'.  If the terminator returns 'true' we set the
        // 'termination_forced' flag to 'true' in order to remember the
        // termination status and to avoid the terminator again.  Setting this
        // flag leads to the first test above to succeed in subsequent calls.
        val terminator = external!!.terminator
        if (terminator != null && lim.terminate.check-- == 0) {
            check(factor > 0)
            check(Int.MAX_VALUE / factor > opts.terminateint)
            lim.terminate.check = factor * opts.terminateint
            if (terminator.terminate()) {
                terminationForced = true // Cache it.
                return true
            }
        }

        return false
    }

    fun searchLimitsHit(): Boolean {
        check(!preprocessing)
        check(!localsearching)

        if (lim.conflicts >= 0 && stats.conflicts >= lim.conflicts) return true

        if (lim.decisions >= 0 && stats.decisions >= lim.decisions) return true

        return false
    }

    companion object {
        // enum Mode
        const val BLOCK = 1 shl 0
        const val CONDITION = 1 shl 1
        const val COVER = 1 shl 2
        const val DECOMP = 1 shl 3
        const val DEDUP = 1 shl 4
        const val ELIM = 1 shl 5
        const val LUCKY = 1 shl 6
        const val PROBE = 1 shl 7
        const val SEARCH = 1 shl 8
        const val SIMPLIFY = 1 shl 9
        const val SUBSUME = 1 shl 10
        const val TERNARY = 1 shl 11
        const val TRANSRED = 1 shl 12
        const val VIVIFY = 1 shl 13
        const val WALK = 1 shl 14

        /** UINT_MAX as the bit pattern stored in the unsigned IntArray tables. */
        const val UINT_MAX = -1
    }
}
