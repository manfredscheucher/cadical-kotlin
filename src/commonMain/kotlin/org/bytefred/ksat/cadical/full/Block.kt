package org.bytefred.ksat.cadical.full

/*
 * block.cpp
 *
 * Mapping:
 *  - 'block_more_occs_size::operator ()' -> [BlockMoreOccsSize] (an [IntLess] passed to the
 *    [Blocker] heap). Its 'size_t s = noccs (..)' are non-negative counts -> Long.
 *  - Occurrence list and literal iterators -> indices. The compaction idiom
 *    'Clause *c = *j++ = *i; ... j--' -> two indices and 'shrinkTo (j)'.
 *  - 'is_blocked_clause' moves clauses to the front with '*i = prev_d' where 'prev_d' starts
 *    as the null pointer. 'Occs' holds non-null clauses, so the single write of null (slot 0
 *    in the first iteration) is skipped: slot 0 is overwritten before anything reads it
 *    ('os[0] = d' when not blocked, the restore loop when blocked; the value the restore
 *    loop reads there only becomes the dead 'prev_d'), so the list ends up identical.
 *  - 'block_literal_with_one_negative_occ': the reference is built with NDEBUG, so the
 *    '#ifndef NDEBUG break; #endif' is not taken and 'd' is the last non-garbage clause;
 *    the 'assert (!d)' before it is kept as a check (there is exactly one such clause).
 */

// This implements an inprocessing version of blocked clause elimination and
// is assumed to be triggered just before bounded variable elimination.  It
// has a separate 'block' flag while variable elimination uses 'elim'.
// Thus it only tries to block clauses on a literal which was removed in an
// irredundant clause in negated form before and has not been tried to use
// as blocking literal since then.

/*------------------------------------------------------------------------*/

internal class BlockMoreOccsSize(private val internal: Internal) : IntLess {
    override fun less(a: Int, b: Int): Boolean {
        var s = internal.noccs(-internal.u2i(a))
        var t = internal.noccs(-internal.u2i(b))
        if (s > t) return true
        if (s < t) return false
        s = internal.noccs(internal.u2i(a))
        t = internal.noccs(internal.u2i(b))
        if (s > t) return true
        if (s < t) return false
        return a.toUInt() > b.toUInt()
    }
}

/*------------------------------------------------------------------------*/

// Determine whether 'c' is blocked on 'lit', by first marking all its
// literals and then checking all resolvents with negative clauses (with
// '-lit') are tautological.  We use a move-to-front scheme for both the
// occurrence list of negative clauses (with '-lit') and then for literals
// within each such clause.  The clause move-to-front scheme has the goal to
// find non-tautological clauses faster in the future, while the literal
// move-to-front scheme has the goal to faster find the matching literal,
// which makes the resolvent tautological (again in the future).

internal fun Internal.isBlockedClause(c: Clause, pivot: Int): Boolean {
    val lit = pivot

    check(c.size >= opts.blockminclslim) { "isBlockedClause: too small" }
    check(c.size <= opts.blockmaxclslim) { "isBlockedClause: too large" }
    check(active(lit)) { "isBlockedClause: inactive" }
    check(value(lit) == 0) { "isBlockedClause: assigned" }
    check(!c.garbage) { "isBlockedClause: garbage" }
    check(!c.redundant) { "isBlockedClause: redundant" }
    check(level == 0) { "isBlockedClause: level" }

    mark(c) // First mark all literals in 'c'.

    val os = occs(-lit)

    var res = true // Result is true if all resolvents tautological.

    // Can not use 'auto' here since we update 'os' during traversal.
    //
    val endOfOs = os.size
    var i = 0

    var prevD: Clause? = null // Previous non-tautological clause.

    while (i != endOfOs) {
        // Move the first clause with non-tautological resolvent to the front of
        // the occurrence list to improve finding it faster later.
        //
        val d = os[i]

        check(!d.garbage) { "isBlockedClause: d garbage" }
        check(!d.redundant) { "isBlockedClause: d redundant" }
        check(d.size <= opts.blockmaxclslim) { "isBlockedClause: d too large" }

        if (prevD != null) os[i] = prevD // Move previous non-tautological clause
        prevD = d // backwards but remember clause at this position.

        stats.blockres++

        var prevOther = 0 // Previous non-tautological literal.

        // No 'auto' since we update literals of 'd' during traversal.
        //
        val endOfD = d.size
        var l = 0
        while (l != endOfD) {
            // Same move-to-front mechanism for literals within a clause.  It
            // moves the first negatively marked literal to the front to find it
            // faster in the future.
            //
            val other = d.literals[l]
            d.literals[l] = prevOther
            prevOther = other
            if (other == -lit) {
                l++
                continue
            }
            check(other != lit) { "isBlockedClause: lit in d" }
            check(active(other)) { "isBlockedClause: other inactive" }
            check(value(other) == 0) { "isBlockedClause: other assigned" }
            if (marked(other) < 0) {
                d.literals[0] = other // Move to front of 'd'.
                break
            }
            l++
        }

        if (l == endOfD) {
            //
            // Since we did not find a tautological literal we restore the old
            // order of literals in the clause.
            //
            while (l-- != 0) {
                val other = d.literals[l]
                d.literals[l] = prevOther
                prevOther = other
            }
            res = false // Now 'd' is a witness that 'c' is not blocked.
            os[0] = d // Move it to the front of the occurrence list.
            break
        }
        i++
    }
    unmark(c) // ... all literals of the candidate clause.

    // If all resolvents are tautological and thus the clause is blocked we
    // restore the old order of clauses in the occurrence list of '-lit'.
    //
    if (res) {
        check(i == endOfOs) { "isBlockedClause: i != end" }
        while (i != 0) {
            val d = os[--i]
            os[i] = prevD!!
            prevD = d
        }
    }

    return res
}

/*------------------------------------------------------------------------*/

internal fun Internal.blockSchedule(blocker: Blocker) {
    // Set skip flags for all literals in too large clauses.
    //
    for (n in 0 until clauses.size) {
        val c = clauses[n]

        if (c.garbage) continue
        if (c.redundant) continue
        if (c.size <= opts.blockmaxclslim) continue

        for (k in 0 until c.size) markSkip(-c.literals[k])
    }

    // Connect all literal occurrences in irredundant clauses.
    //
    for (n in 0 until clauses.size) {
        val c = clauses[n]

        if (c.garbage) continue
        if (c.redundant) continue

        for (k in 0 until c.size) {
            val lit = c.literals[k]
            check(active(lit)) { "blockSchedule: inactive" }
            check(value(lit) == 0) { "blockSchedule: assigned" }
            occs(lit).add(c)
        }
    }

    // We establish the invariant that 'noccs' gives the number of actual
    // occurrences of 'lit' in non-garbage clauses,  while 'occs' might still
    // refer to garbage clauses, thus 'noccs (lit) <= occs (lit).size ()'.  It
    // is expensive to remove references to garbage clauses from 'occs' during
    // blocked clause elimination, but decrementing 'noccs' is cheap.

    for (lit in lits) {
        if (!active(lit)) continue
        check(value(lit) == 0) { "blockSchedule: assigned" }
        val os = occs(lit)
        ntab[vlit(lit)] = os.size.toLong()
    }

    // Now we fill the schedule (priority queue) of candidate literals to be
    // tried as blocking literals.  It is probably slightly faster to do this
    // in one go after all occurrences have been determined, instead of
    // filling the priority queue during pushing occurrences.  Filling the
    // schedule can not be fused with the previous loop (easily) since we
    // first have to initialize 'noccs' for both 'lit' and '-lit'.

    for (idx in vars) {
        if (!active(idx)) continue
        if (frozen(idx)) continue
        check(value(idx) == 0) { "blockSchedule: idx assigned" }
        var sign = -1
        while (sign <= 1) {
            val lit = sign * idx
            if (markedSkip(lit)) {
                sign += 2
                continue
            }
            if (!markedBlock(lit)) {
                sign += 2
                continue
            }
            unmarkBlock(lit)
            blocker.schedule.pushBack(vlit(lit))
            sign += 2
        }
    }
}

/*------------------------------------------------------------------------*/

// A literal is pure if it only occurs positive.  Then all clauses in which
// it occurs are blocked on it. This special case can be implemented faster
// than trying to block literals with at least one negative occurrence and
// is thus handled separately.  It also allows to avoid pushing blocked
// clauses onto the extension stack.

internal fun Internal.blockPureLiteral(blocker: Blocker, lit: Int) {
    if (frozen(lit)) return
    check(active(lit)) { "blockPureLiteral: inactive" }

    val pos = occs(lit)
    val nos = occs(-lit)

    check(noccs(-lit) == 0L) { "blockPureLiteral: negative occurrences" }
    for (k in 0 until nos.size) check(nos[k].garbage) { "blockPureLiteral: non-garbage negative" }
    stats.blockpurelits++
    for (n in 0 until pos.size) {
        val c = pos[n]
        if (c.garbage) continue
        check(!c.redundant) { "blockPureLiteral: redundant" }
        blocker.reschedule.add(c)
        proof?.weakenMinus(c)
        external!!.pushClauseOnExtensionStack(c, lit)
        stats.blockpured++
        markGarbage(c)
    }

    pos.clear()
    nos.clear()

    markPure(lit)
    stats.blockpured++
}

/*------------------------------------------------------------------------*/

// If there is only one negative clause with '-lit' it is faster to mark it
// instead of marking all the positive clauses with 'lit' one after the
// other and then resolving against the negative clause.

internal fun Internal.blockLiteralWithOneNegativeOcc(blocker: Blocker, lit: Int) {
    check(active(lit)) { "blockLiteralWithOneNegativeOcc: inactive" }
    check(!frozen(lit)) { "blockLiteralWithOneNegativeOcc: frozen" }
    check(noccs(lit) > 0) { "blockLiteralWithOneNegativeOcc: no positive" }
    check(noccs(-lit) == 1L) { "blockLiteralWithOneNegativeOcc: not one negative" }

    val nos = occs(-lit)
    check(nos.size >= 1) { "blockLiteralWithOneNegativeOcc: nos empty" }

    var d: Clause? = null
    for (n in 0 until nos.size) {
        val c = nos[n]
        if (c.garbage) continue
        check(d == null) { "blockLiteralWithOneNegativeOcc: two negative clauses" }
        d = c
        // '#ifndef NDEBUG break; #endif' is not taken in the NDEBUG reference.
    }
    check(d != null) { "blockLiteralWithOneNegativeOcc: no negative clause" }
    nos.shrinkTo(1)
    nos[0] = d

    if (d.size > opts.blockmaxclslim) {
        return
    }

    check(!d.garbage) { "blockLiteralWithOneNegativeOcc: d garbage" }
    check(!d.redundant) { "blockLiteralWithOneNegativeOcc: d redundant" }
    check(d.size <= opts.blockmaxclslim) { "blockLiteralWithOneNegativeOcc: d too large" }

    mark(d)
    var blocked = 0L
    val pos = occs(lit)

    // Again no 'auto' since 'pos' is update during traversal.
    //
    val eop = pos.size
    var j = 0
    var i = 0

    while (i != eop) {
        val c = pos[i]
        pos[j++] = c

        if (c.garbage) {
            j--
            i++
            continue
        }
        if (c.size > opts.blockmaxclslim) {
            i++
            continue
        }
        if (c.size < opts.blockminclslim) {
            i++
            continue
        }

        // We use the same literal move-to-front strategy as in
        // 'is_blocked_clause'.  See there for more explanations.

        var prevOther = 0 // Previous non-tautological literal.

        // No 'auto' since literals of 'c' are updated during traversal.
        //
        val endOfC = c.size
        var l = 0

        while (l != endOfC) {
            val other = c.literals[l]
            c.literals[l] = prevOther
            prevOther = other
            if (other == lit) {
                l++
                continue
            }
            check(other != -lit) { "blockLiteralWithOneNegativeOcc: -lit in c" }
            check(active(other)) { "blockLiteralWithOneNegativeOcc: other inactive" }
            check(value(other) == 0) { "blockLiteralWithOneNegativeOcc: other assigned" }
            if (marked(other) < 0) {
                c.literals[0] = other // Move to front of 'c'.
                break
            }
            l++
        }

        if (l == endOfC) {
            // Restore old literal order in the clause because.

            while (l-- != 0) {
                val other = c.literals[l]
                c.literals[l] = prevOther
                prevOther = other
            }

            i++
            continue // ... with next candidate 'c' in 'pos'.
        }

        blocked++
        proof?.weakenMinus(c)
        external!!.pushClauseOnExtensionStack(c, lit)
        blocker.reschedule.add(c)
        markGarbage(c)
        j--
        i++
    }
    if (j == 0) pos.clear()
    else pos.shrinkTo(j)

    stats.blocked += blocked

    unmark(d)
}

/*------------------------------------------------------------------------*/

// Determine the set of candidate clauses with 'lit', which are checked to
// be blocked by 'lit'.  Filter out too large and small clauses and which do
// not have any negated other literal in any of the clauses with '-lit'.

internal fun Internal.blockCandidates(blocker: Blocker, lit: Int): Int {

    check(blocker.candidates.isEmpty()) { "blockCandidates: candidates not empty" }

    val pos = occs(lit) // Positive occurrences of 'lit'.
    val nos = occs(-lit)

    check(noccs(lit) <= pos.size.toLong()) { "blockCandidates: noccs (lit)" }
    check(noccs(-lit) == nos.size.toLong()) { "blockCandidates: noccs (-lit)" } // Already flushed.

    // Mark all literals in clauses with '-lit'.  Note that 'mark2' uses
    // separate bits for 'lit' and '-lit'.
    //
    for (n in 0 until nos.size) mark2(nos[n])

    val eop = pos.size
    var j = 0
    var i = 0

    while (i != eop) {
        val c = pos[i]
        pos[j++] = c
        if (c.garbage) {
            j--
            i++
            continue
        }
        check(!c.redundant) { "blockCandidates: redundant" }
        if (c.size > opts.blockmaxclslim) {
            i++
            continue
        }
        if (c.size < opts.blockminclslim) {
            i++
            continue
        }
        val eoc = c.size
        var l = 0
        while (l != eoc) {
            val other = c.literals[l]
            if (other == lit) {
                l++
                continue
            }
            check(other != -lit) { "blockCandidates: -lit in c" }
            check(active(other)) { "blockCandidates: other inactive" }
            check(value(other) == 0) { "blockCandidates: other assigned" }
            if (marked2(-other)) break
            l++
        }
        if (l != eoc) blocker.candidates.add(c)
        i++
    }
    if (j == 0) pos.clear()
    else pos.shrinkTo(j)

    check(pos.size.toLong() == noccs(lit)) { "blockCandidates: not flushed" } // Now also flushed.

    for (n in 0 until nos.size) unmark(nos[n])

    return blocker.candidates.size
}

/*------------------------------------------------------------------------*/

// Try to find a clause with '-lit' which does not have any literal in
// clauses with 'lit'.  If such a clause exists no candidate clause can be
// blocked on 'lit' since all candidates would produce a non-tautological
// resolvent with that clause.

internal fun Internal.blockImpossible(blocker: Blocker, lit: Int): Clause? {
    check(noccs(-lit) > 1) { "blockImpossible: noccs (-lit)" }
    check(blocker.candidates.size > 1) { "blockImpossible: candidates" }

    for (n in 0 until blocker.candidates.size) mark2(blocker.candidates[n])

    val nos = occs(-lit)
    var res: Clause? = null

    for (n in 0 until nos.size) {
        val c = nos[n]
        check(!c.garbage) { "blockImpossible: garbage" }
        check(!c.redundant) { "blockImpossible: redundant" }
        check(c.size <= opts.blockmaxclslim) { "blockImpossible: too large" }
        val eoc = c.size
        var l = 0
        while (l != eoc) {
            val other = c.literals[l]
            if (other == -lit) {
                l++
                continue
            }
            check(other != lit) { "blockImpossible: lit in c" }
            check(active(other)) { "blockImpossible: other inactive" }
            check(value(other) == 0) { "blockImpossible: other assigned" }
            if (marked2(-other)) break
            l++
        }
        if (l == eoc) res = c
    }

    for (n in 0 until blocker.candidates.size) unmark(blocker.candidates[n])

    if (res != null) {
        blocker.candidates.clear()
    }

    return res
}

/*------------------------------------------------------------------------*/

// In the general case we have at least two negative occurrences.

internal fun Internal.blockLiteralWithAtLeastTwoNegativeOccs(blocker: Blocker, lit: Int) {
    check(active(lit)) { "blockLiteralWithAtLeastTwoNegativeOccs: inactive" }
    check(!frozen(lit)) { "blockLiteralWithAtLeastTwoNegativeOccs: frozen" }
    check(noccs(lit) > 0) { "blockLiteralWithAtLeastTwoNegativeOccs: no positive" }
    check(noccs(-lit) > 1) { "blockLiteralWithAtLeastTwoNegativeOccs: negative" }

    val nos = occs(-lit)
    check(noccs(-lit) <= nos.size.toLong()) { "blockLiteralWithAtLeastTwoNegativeOccs: noccs" }

    var maxSize = 0

    // Flush all garbage clauses in occurrence list 'nos' of '-lit' and
    // determine the maximum size of negative clauses (with '-lit').
    //
    val eon = nos.size
    var j = 0
    var i = 0
    while (i != eon) {
        val c = nos[i]
        nos[j++] = c
        if (c.garbage) j--
        else if (c.size > maxSize) maxSize = c.size
        i++
    }
    if (j == 0) nos.clear()
    else nos.shrinkTo(j)

    check(nos.size.toLong() == noccs(-lit)) { "blockLiteralWithAtLeastTwoNegativeOccs: not flushed" }
    check(nos.size > 1) { "blockLiteralWithAtLeastTwoNegativeOccs: nos size" }

    // If the maximum size of a negative clause (with '-lit') exceeds the
    // maximum clause size limit ignore this candidate literal.
    //
    if (maxSize > opts.blockmaxclslim) {
        return
    }

    // We filter candidate clauses with positive occurrence of 'lit' in
    // 'blocker.candidates' and return if no candidate clause remains.
    // Candidates should be small enough and should have at least one literal
    // which occurs negated in one of the clauses with '-lit'.
    //
    val candidates = blockCandidates(blocker, lit)
    if (candidates == 0) {
        return
    }

    // We further search for a clause with '-lit' that has no literal
    // negated in any of the candidate clauses (except 'lit').  If such a
    // clause exists, we know that none of the candidates is blocked.
    //
    if (candidates > 1 && blockImpossible(blocker, lit) != null) {
        check(blocker.candidates.isEmpty()) { "blockLiteralWithAtLeastTwoNegativeOccs: candidates" }
        return
    }

    var blocked = 0L

    // Go over all remaining candidates and try to block them on 'lit'.
    //
    for (n in 0 until blocker.candidates.size) {
        val c = blocker.candidates[n]
        check(!c.garbage) { "blockLiteralWithAtLeastTwoNegativeOccs: garbage" }
        check(!c.redundant) { "blockLiteralWithAtLeastTwoNegativeOccs: redundant" }
        if (!isBlockedClause(c, lit)) continue
        blocked++
        proof?.weakenMinus(c)
        external!!.pushClauseOnExtensionStack(c, lit)
        blocker.reschedule.add(c)
        markGarbage(c)
    }

    blocker.candidates.clear()
    stats.blocked += blocked
    if (blocked != 0L) flushOccs(lit)
}

/*------------------------------------------------------------------------*/

// Reschedule literals in a clause (except 'lit') which was blocked.

internal fun Internal.blockRescheduleClause(blocker: Blocker, lit: Int, c: Clause) {
    check(c.garbage) { "blockRescheduleClause: not garbage" }

    for (k in 0 until c.size) {
        val other = c.literals[k]

        check(noccs(other) > 0) { "blockRescheduleClause: noccs" }
        ntab[vlit(other)]--

        if (blocker.schedule.contains(vlit(-other))) blocker.schedule.update(vlit(-other))
        else if (active(other) && !frozen(other) && !markedSkip(-other)) {
            blocker.schedule.pushBack(vlit(-other))
        }

        if (blocker.schedule.contains(vlit(other))) {
            check(other != lit) { "blockRescheduleClause: other == lit" }
            blocker.schedule.update(vlit(other))
        }
    }
}

// Reschedule all literals in clauses blocked by 'lit' (except 'lit').

internal fun Internal.blockReschedule(blocker: Blocker, lit: Int) {
    while (blocker.reschedule.isNotEmpty()) {
        val c = blocker.reschedule.last()
        blocker.reschedule.removeAt(blocker.reschedule.size - 1)
        blockRescheduleClause(blocker, lit, c)
    }
}

/*------------------------------------------------------------------------*/

internal fun Internal.blockLiteral(blocker: Blocker, lit: Int) {
    check(!markedSkip(lit)) { "blockLiteral: skipped" }

    if (!active(lit)) return // Pure literal '-lit'.
    if (frozen(lit)) return

    check(value(lit) == 0) { "blockLiteral: assigned" }

    // If the maximum number of a negative clauses (with '-lit') exceeds the
    // occurrence limit ignore this candidate literal.
    //
    if (noccs(-lit) > opts.blockocclim) return

    stats.blockcands++

    check(blocker.reschedule.isEmpty()) { "blockLiteral: reschedule not empty" }
    check(blocker.candidates.isEmpty()) { "blockLiteral: candidates not empty" }

    if (noccs(-lit) == 0L) blockPureLiteral(blocker, lit)
    else if (noccs(lit) == 0L) {
        // Rare situation, where the clause length limit was hit for 'lit' and
        // '-lit' is skipped and then it becomes pure.  Can be ignored.  We also
        // so it once happening for a 'elimboundmin=-1' and zero positive and
        // one negative occurrence.
    } else if (noccs(-lit) == 1L) blockLiteralWithOneNegativeOcc(blocker, lit)
    else blockLiteralWithAtLeastTwoNegativeOccs(blocker, lit)

    // Done with blocked clause elimination on this literal and we do not
    // have to try blocked clause elimination on it again until irredundant
    // clauses with its negation are removed.
    //
    check(!frozen(lit)) { "blockLiteral: frozen" } // just to be sure ...
    unmarkBlock(lit)
}

/*------------------------------------------------------------------------*/

internal fun Internal.block(): Boolean = tracePhase("block") {

    if (opts.block == 0) return false
    if (unsat) return false
    if (stats.current.irredundant == 0L) return false
    if (terminatedAsynchronously()) return false

    if (propagated < trail.size) {
        initWatches()
        connectWatches()
        if (!propagate()) {
            learnEmptyClause()
            check(unsat) { "block: not unsat" }
        }
        clearWatches()
        resetWatches()
        if (unsat) return false
    }

    startSimplifier(Internal.BLOCK)

    stats.blockings++

    check(level == 0) { "block: level" }
    check(!watching()) { "block: watching" }
    check(!occurring()) { "block: occurring" }

    markSatisfiedClausesAsGarbage()

    initOccs() // Occurrence lists for all literals.
    initNoccs() // Number of occurrences to avoid flushing garbage clauses.

    val blocker = Blocker(BlockMoreOccsSize(this))
    blockSchedule(blocker)

    var blocked = stats.blocked
    // 'resolutions', 'purelits' only feed messages ('PHASE').
    var pured = stats.blockpured

    while (!terminatedAsynchronously() && !blocker.schedule.empty()) {
        val lit = u2i(blocker.schedule.front())
        blocker.schedule.popFront()
        blockLiteral(blocker, lit)
        blockReschedule(blocker, lit)
    }

    blocker.erase()
    resetNoccs()
    resetOccs()

    blocked = stats.blocked - blocked

    pured = stats.blockpured - pured

    if (pured != 0L) markRedundantClausesWithEliminatedVariablesAsGarbage()

    stopSimplifier(Internal.BLOCK)

    blocked != 0L
}
