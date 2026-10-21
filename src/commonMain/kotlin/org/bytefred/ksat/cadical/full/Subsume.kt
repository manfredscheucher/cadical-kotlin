package org.bytefred.ksat.cadical.full

import kotlin.math.abs
import kotlin.math.max

/*
 * subsume.cpp
 *
 * Mapping:
 *  - Clause literal iterators -> indices into 'c.literals'.
 *  - 'std::remove (c->begin (), c->end (), lit)' -> the same left shift written out.
 *  - 'int64_t x *= double' -> product in double, truncated back to Long.
 *  - 'int old_marked_candidate_variables_for_elimination = stats.mark.elim' truncates the
 *    int64 counter to int as upstream ('toInt ()').
 *  - The 'goto UPDATE_LIMITS' in 'subsume' -> a flag skipping the body.
 *  - The '#ifndef QUIET' / 'PHASE' only values ('scheduled', 'total') are not ported.
 */

/*------------------------------------------------------------------------*/

// This file implements a global forward subsumption algorithm, which is run
// frequently during search.  It works both on original (irredundant)
// clauses and on 'sticky' learned clauses which are likely to be kept.
// This is abstracted away in the 'likely_to_be_kept_clause' function, which
// implicitly relies on 'opts.reducetier1glue' (glucose level of clauses
// which are not reduced) as well as dynamically determined size and glucose
// level ('lim.keptglue' and 'lim.keptsize') of clauses kept in 'reduce'.
//
// Note, that 'forward' means that the clause from which the subsumption
// check is started is checked for being subsumed by other (smaller or equal
// size) clauses.  Since 'vivification' is an extended version of subsume,
// more powerful, but also slower, we schedule 'vivify' right after
// 'subsume', which in contrast to 'subsume' is not run until to completion.
//
// (See upstream subsume.cpp for the full discussion of the algorithm.)

internal fun Internal.subsuming(): Boolean {

    if (opts.subsume == 0 && opts.vivify == 0) return false
    if (!preprocessing && opts.inprocessing == 0) return false
    if (preprocessing) check(lim.preprocessing != 0L) { "subsuming: preprocessing limit" }

    // Only perform global subsumption checking immediately after a clause
    // reduction happened where the overall allocated memory is small and we
    // got a limit on the number of kept clause in terms of size and glue.
    //
    if (opts.reduce != 0 && stats.conflicts != last.reduce.conflicts) return false

    if (stats.conflicts < lim.subsume) return false

    return true
}

// This is the actual subsumption and strengthening check.  We assume that
// all the literals of the candidate clause to be subsumed or strengthened
// are marked, so we only have to check that all the literals of the
// argument clause 'subsuming', which is checked for subsuming the candidate
// clause 'subsumed', has all its literals marked (in the correct phase).
// If exactly one is in the opposite phase we can still strengthen the
// candidate clause by this single literal which occurs in opposite phase.
//
// The result is INT_MIN if all literals are marked and thus the candidate
// clause can be subsumed.  It is zero if neither subsumption nor
// strengthening is possible.  Otherwise the candidate clause can be
// strengthened and as a result the negation of the literal which can be
// removed is returned.

internal fun Internal.subsumeCheck(subsuming: Clause, subsumed: Clause): Int {
    // Only use 'subsumed' for these following assertion checks.  Otherwise we
    // only require that 'subsumed' has all its literals marked.
    //
    check(!subsumed.garbage) { "subsume_check: subsumed garbage" }
    check(!subsuming.garbage) { "subsume_check: subsuming garbage" }
    check(subsuming !== subsumed) { "subsume_check: same clause" }
    check(subsuming.size <= subsumed.size) { "subsume_check: size" }

    stats.subchecks++
    if (subsuming.size == 2) stats.subchecks2++

    var flipped = 0
    var prev = 0
    var failed = false
    val eoc = subsuming.size
    var i = 0
    while (!failed && i != eoc) {
        val lit = subsuming.literals[i]
        subsuming.literals[i] = prev
        prev = lit
        val tmp = marked(lit)
        if (tmp == 0) failed = true
        else if (tmp > 0) {
            i++
            continue
        } else if (flipped != 0) failed = true
        else flipped = lit
        i++
    }
    check(prev != 0) { "subsume_check: prev" }
    check(subsuming.literals[0] == 0) { "subsume_check: literals[0]" }
    subsuming.literals[0] = prev
    if (failed) return 0

    return if (flipped == 0) Int.MIN_VALUE // subsumed!!
    else if (opts.subsumestr == 0) 0
    else flipped // strengthen!!
}

/*------------------------------------------------------------------------*/

// Candidate clause 'subsumed' is subsumed by 'subsuming'.

internal fun Internal.subsumeClause(subsuming: Clause, subsumed: Clause) {
    stats.subsumed++
    check(subsuming.size <= subsumed.size) { "subsume_clause: size" }
    if (subsumed.redundant) stats.subred++
    else stats.subirr++
    if (subsumed.redundant || !subsuming.redundant) {
        markGarbage(subsumed)
        return
    }
    subsuming.redundant = false
    proof?.strengthen(subsuming.id)
    markGarbage(subsumed)
    stats.current.irredundant++
    stats.added.irredundant++
    stats.irrlits += subsuming.size
    check(stats.current.redundant > 0) { "subsume_clause: current redundant" }
    stats.current.redundant--
    check(stats.added.redundant > 0) { "subsume_clause: added redundant" }
    stats.added.redundant--
    // ... and keep 'stats.added.total'.
}

/*------------------------------------------------------------------------*/

// Candidate clause 'c' is strengthened by removing 'lit'.

internal fun Internal.strengthenClause(c: Clause, lit: Int) {
    stats.strengthened++
    check(c.size > 2) { "strengthen_clause: size" }
    proof?.strengthenClause(c, lit, lratChain)
    if (!c.redundant) markRemoved(lit)
    // auto new_end = remove (c->begin (), c->end (), lit);
    val end = c.size
    var newEnd = 0
    for (k in 0 until end) {
        val other = c.literals[k]
        if (other != lit) c.literals[newEnd++] = other
    }
    check(newEnd + 1 == end) { "strengthen_clause: literal not removed once" }
    shrinkClause(c, c.size - 1)
    // In an earlier version (probably from the time where the used flag was a
    // single bit) the code was
    //
    // c->used = 1
    //
    // This code was subsequently removed leading to a performance regression
    // that can be solved by the simpler (there is a more meaningfull way, but
    // it is not yet part of the master branch of CaDiCaL):
    c.used = 0
    external!!.checkShrunkenClause(c)
}

/*------------------------------------------------------------------------*/

// Find clauses connected in the occurrence lists 'occs' which subsume the
// candidate clause 'c' given as first argument.  If this is the case the
// clause is subsumed and the result is positive.   If the clause was
// strengthened the result is negative.  Otherwise the candidate clause
// can not be subsumed nor strengthened and zero is returned.

internal fun Internal.tryToSubsumeClause(c: Clause, shrunken: ArrayList<Clause>): Int {

    stats.subtried++
    check(level == 0) { "try_to_subsume_clause: level" }

    mark(c) // signed!

    var d: Clause? = null
    var flipped = 0

    for (ci in 0 until c.size) {
        val lit = c.literals[ci]

        // Only clauses which have a variable which has recently been added are
        // checked for being subsumed.  The idea is that all these newly added
        // clauses are candidates for subsuming the clause.  Then we also only
        // need to check occurrences of these variables.  The occurrence lists
        // of other literal do not have to be checked.
        //
        if (!flags(lit).subsume) continue

        var sign = -1
        while (d == null && sign <= 1) {

            // First we check against all binary clauses.  The other literals of
            // all binary clauses of 'sign*lit' are stored in one consecutive
            // array, which is way faster than storing clause pointers and
            // dereferencing them.  Since this binary clause array is also not
            // shrunken, we also can bail out earlier if subsumption or
            // strengthening is determined.

            // In both cases the (self-)subsuming clause is stored in 'd', which
            // makes it nonzero and forces aborting both the outer and inner loop.
            // If the binary clause can strengthen the candidate clause 'c'
            // (through self-subsuming resolution), then 'filled' is set to the
            // literal which can be removed in 'c', otherwise to 'INT_MIN' which
            // is a non-valid literal.

            for (bin in bins(sign * lit)) {
                val other = bin.lit
                val tmp = marked(other)
                if (tmp == 0) continue
                if (tmp < 0 && sign < 0) continue
                if (tmp < 0) {
                    if (sign < 0) continue // tautological resolvent
                    dummyBinary.literals[0] = lit
                    dummyBinary.literals[1] = other
                    flipped = other
                } else {
                    dummyBinary.literals[0] = sign * lit
                    dummyBinary.literals[1] = other
                    flipped = if (sign < 0) -lit else Int.MIN_VALUE
                }

                // This dummy binary clauses is initialized in 'Internal::Internal'
                // and only changes it literals in the lines above.   By using such
                // a faked binary clause we can simply reuse 'subsume_clause' as
                // well as the code around 'strengthen_clause' uniform for both real
                // clauses and this special case for binary clauses

                dummyBinary.id = bin.id
                d = dummyBinary

                break
            }

            if (d != null) break

            // In this second loop we check for larger than binary clauses to
            // subsume or strengthen the candidate clause.   This is more costly,
            // and needs a call to 'subsume_check'.  Otherwise the same contract
            // as above for communicating 'subsumption' or 'strengthening' to the
            // code after the loop is used.
            //
            val os = occs(sign * lit)
            for (e in os) {
                check(!e.garbage) { "try_to_subsume_clause: garbage occurrence" } // sanity check
                if (e.garbage) continue // defensive: not needed
                flipped = subsumeCheck(e, c)
                if (flipped == 0) continue
                d = e // leave also outer loop
                break
            }
            sign += 2
        }

        if (d != null) break
    }

    unmark(c)

    if (flipped == Int.MIN_VALUE) {
        subsumeClause(d!!, c)
        return 1
    }

    if (flipped != 0) {
        if (lrat) {
            check(lratChain.isEmpty()) { "try_to_subsume_clause: lrat chain" }
            lratChain.add(c.id)
            lratChain.add(d!!.id)
        }
        strengthenClause(c, -flipped)
        lratChain.clear()
        check(likelyToBeKeptClause(c)) { "try_to_subsume_clause: not likely kept" }
        shrunken.add(c)
        return -1
    }

    return 0
}

/*------------------------------------------------------------------------*/

// Sorting the scheduled clauses is way faster if we compute and save the
// clause size in the schedule to avoid pointer access to clauses during
// sorting.  This slightly increases the schedule size though.

private class ClauseSize(
    val size: Long, // size_t
    val clause: Clause,
)

private val smallerClauseSizeRank = Rank<ClauseSize> { a -> a.size }

/*------------------------------------------------------------------------*/

private class SubsumeLessNoccs(private val internal: Internal) : IntLess {
    override fun less(a: Int, b: Int): Boolean {
        val u = internal.value(a)
        val v = internal.value(b)
        if (u == 0 && v != 0) return true
        if (u != 0 && v == 0) return false
        val m = internal.noccs(a)
        val n = internal.noccs(b)
        if (m < n) return true
        if (m > n) return false
        return abs(a) < abs(b)
    }
}

/*------------------------------------------------------------------------*/

// Usually called from 'subsume' below if 'subsuming' triggered it.  Then
// the idea is to subsume both redundant and irredundant clauses. It is also
// called in the elimination loop in 'elim' in which case we focus on
// irredundant clauses only to help bounded variable elimination.  The
// function returns true of an irredundant clause was removed or
// strengthened, which might then in the second usage scenario trigger new
// variable eliminations.

internal fun Internal.subsumeRound(): Boolean {

    if (opts.subsume == 0) return false
    if (unsat) return false
    if (terminatedAsynchronously()) return false
    if (stats.current.redundant == 0L && stats.current.irredundant == 0L) return false

    startSimplifier(Internal.SUBSUME)
    stats.subsumerounds++

    val checkLimit: Long
    if (opts.subsumelimited != 0) {
        var delta = stats.propagations.search
        delta = (delta * (1e-3 * opts.subsumereleff)).toLong()
        if (delta < opts.subsumemineff) delta = opts.subsumemineff.toLong()
        if (delta > opts.subsumemaxeff) delta = opts.subsumemaxeff.toLong()
        delta = max(delta, 2L * active())

        checkLimit = stats.subchecks + delta
    } else {
        checkLimit = Long.MAX_VALUE
    }

    val oldMarkedCandidateVariablesForElimination = stats.mark.elim.toInt()

    check(level == 0) { "subsume_round: level" }

    // Allocate schedule and occurrence lists.
    //
    val schedule = ArrayList<ClauseSize>()
    initNoccs()

    // Determine candidate clauses and sort them by size.
    //
    var leftOverFromLastSubsumptionRound = 0L

    for (c in clauses) {

        if (c.garbage) continue
        if (c.size > opts.subsumeclslim) continue
        if (!likelyToBeKeptClause(c)) continue

        var fixed = false
        var subsume = 0
        for (k in 0 until c.size) {
            val lit = c.literals[k]
            if (value(lit) != 0) fixed = true
            else if (flags(lit).subsume) subsume++
        }

        // If the clause contains a root level assigned (fixed) literal we will
        // not work on it.  This simplifies the code substantially since we do
        // not have to care about assignments at all.  Strengthening becomes
        // much simpler too.
        //
        if (fixed) {
            continue
        }

        // Further, if less than two variables in the clause were added since
        // the last subsumption round, the clause is ignored too.
        //
        if (subsume < 2) {
            continue
        }

        if (c.subsume) leftOverFromLastSubsumptionRound++
        schedule.add(ClauseSize(c.size.toLong(), c))
        for (k in 0 until c.size) ntab[vlit(c.literals[k])]++
    }
    schedule.trimToSize()

    // Smaller clauses are checked and connected first.
    //
    rsort(schedule, smallerClauseSizeRank)

    if (leftOverFromLastSubsumptionRound == 0L)
        for (cs in schedule)
            if (cs.clause.size > 2) cs.clause.subsume = true

    // Now go over the scheduled clauses in the order of increasing size and
    // try to forward subsume and strengthen them. Forward subsumption tries
    // to find smaller or same size clauses which subsume or might strengthen
    // the candidate.  After the candidate has been processed connect one
    // of its literals (with smallest number of occurrences at this point) in
    // a one-watched scheme.

    var checked = 0L // 'subsumed' and 'strengthened' only feed messages

    val shrunken = ArrayList<Clause>()
    initOccs()
    initBins()

    for (s in schedule) {

        if (terminatedAsynchronously()) break
        if (stats.subchecks >= checkLimit) break

        val c = s.clause
        check(!c.garbage) { "subsume_round: garbage scheduled" }

        checked++

        // First try to subsume or strengthen this candidate clause.  For binary
        // clauses this could be done much faster by hashing and is costly due
        // to a usually large number of binary clauses.  There is further the
        // issue, that strengthening binary clauses (through double
        // self-subsuming resolution) would produce units, which needs much more
        // care. In the same (lazy) spirit we also ignore clauses with fixed
        // literals (false or true).
        //
        if (c.size > 2 && c.subsume) {
            c.subsume = false
            val tmp = tryToSubsumeClause(c, shrunken)
            if (tmp > 0) {
                continue
            }
        }

        // If not subsumed connect smallest occurring literal, where occurring
        // means the number of times it was used to connect (as a one-watch) a
        // previous smaller or equal sized clause.  This minimizes the length of
        // the occurrence lists traversed during 'try_to_subsume_clause'. Also
        // note that this number is usually way smaller than the number of
        // occurrences computed before and stored in 'noccs'.
        //
        var minlit = 0
        var minoccs = 0L
        var minsize = 0
        var subsume = true
        val binary = (c.size == 2 && !c.redundant)

        for (k in 0 until c.size) {
            val lit = c.literals[k]

            if (!flags(lit).subsume) subsume = false
            val size = if (binary) bins(lit).size else occs(lit).size
            if (minlit != 0 && minsize <= size) continue
            val tmp = noccs(lit)
            if (minlit != 0 && minsize == size && tmp <= minoccs) continue
            minlit = lit
            minsize = size
            minoccs = tmp
        }

        // If there is a variable in a clause different from is not 'subsume'
        // (has been added since the last subsumption round), then this clause
        // can not serve to strengthen or subsume another clause, since all
        // shrunken or added clauses mark all their variables as 'subsume'.
        //
        if (!subsume) continue

        if (!binary) {

            // If smallest occurring literal occurs too often do not connect.
            //
            if (minsize > opts.subsumeocclim) continue

            occs(minlit).add(c)

            // This sorting should give faster failures for assumption checks
            // since the less occurring variables are put first in a clause and
            // thus will make it more likely to be found as witness for a clause
            // not to be subsuming.  One could in principle (see also the
            // discussion on 'subsumption' in our 'Splatz' solver) replace marking
            // by a kind of merge sort, as also suggested by Bayardo.  It would
            // avoid 'marked' calls and thus might be slightly faster but could
            // not take benefit of this sorting optimization.
            //
            cxxSort(c.literals, 0, c.size, SubsumeLessNoccs(this))

        } else {

            // If smallest occurring literal occurs too often do not connect.
            //
            if (minsize > opts.subsumebinlim) continue

            val minlitPos = if (c.literals[1] == minlit) 1 else 0
            val other = c.literals[if (minlitPos == 0) 1 else 0]
            bins(minlit).add(Bin(other, c.id))
        }
    }

    val remain = schedule.size - checked
    val completed = remain == 0L

    // Release occurrence lists and schedule.
    //
    schedule.clear()
    resetNoccs()
    resetOccs()
    resetBins()

    // Reset all old 'added' flags and mark variables in shrunken
    // clauses as 'added' for the next subsumption round.
    //
    if (completed) resetSubsumeBits()

    for (c in shrunken) markAdded(c)
    shrunken.clear()

    // report ('s', !opts.reportall && !(subsumed + strengthened)) dropped (message output).

    stopSimplifier(Internal.SUBSUME)

    return oldMarkedCandidateVariablesForElimination < stats.mark.elim
}

/*------------------------------------------------------------------------*/

internal fun Internal.subsume(updateLimits: Boolean = true): Unit = tracePhase("subsume") {

    stats.subsumephases++

    // 'goto UPDATE_LIMITS' skips the body below.
    val gotoUpdateLimits = stats.current.redundant == 0L && stats.current.irredundant == 0L

    if (!gotoUpdateLimits) {

        if (unsat) return

        backtrack()
        if (!propagate()) {
            learnEmptyClause()
            return
        }

        if (externalProp) {
            check(level == 0) { "subsume: level" }
            privateSteps = true
        }

        if (opts.subsume != 0) {
            resetWatches()
            subsumeRound()
            initWatches()
            connectWatches()
            if (!unsat && !propagate()) {
                learnEmptyClause()
            }
        }

        // Schedule 'vivification' in 'subsume' as well as 'transitive reduction'.
        //
        if (opts.vivify != 0) vivify()
        if (opts.transred != 0) transred()

        if (externalProp) {
            check(level == 0) { "subsume: level" }
            privateSteps = false
        }
    }

    // UPDATE_LIMITS:

    if (!updateLimits) return

    val delta = scale((opts.subsumeint * (stats.subsumephases + 1)).toDouble()).toLong()
    lim.subsume = stats.conflicts + delta
}
