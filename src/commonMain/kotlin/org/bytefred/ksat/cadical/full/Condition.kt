package org.bytefred.ksat.cadical.full

import org.bytefred.ksat.cadical.IntArrayList

/*
 * condition.cpp: globally blocked clause elimination ('conditioning').
 *
 * Mapping notes:
 *  - 'long' (64 bit on the reference platform) -> Long, 'size_t' counters -> Long.
 *  - The anonymous structs 'initial, remain' / 'next' / 'check' -> [CondAssignment] and
 *    locals; 'remain = initial' copies the fields.
 *  - 'long *= double' ('limit *= 2.0 * active () / (double) irredundant') -> convert to
 *    double, multiply, truncate with 'toLong ()'.
 *  - LOG / PHASE messages and 'report' are dropped; the '#ifndef QUIET' counters 'props',
 *    'watched', 'untried' only feed PHASE messages and are dropped too.
 *  - The '#if defined(LOGGING) || !defined(NDEBUG)' consistency checks are ported as checks.
 */

/*------------------------------------------------------------------------*/

// Globally blocked clause elimination (which we call here 'conditioning')
// is described first in the PhD thesis of Benjamin Kiesl from 2019.  An
// extended version, which in particular describes the algorithm implemented
// below is in our invited ATVA'19 paper [KieslHeuleBiere-ATVA'19].  This
// accordingly needs witnesses consisting potentially of more than one
// literal.  It is the first technique implemented in CaDiCaL with this
// feature (PR clause elimination thus should work in principle too).

// Basically globally blocked clauses are like set blocked clauses, except
// that the witness cube (of literals to be flipped during reconstruction)
// can contain variables which are not in the blocked clause.  This
// can simulate some interesting global optimizations like 'headlines' from
// the FAN algorithm for ATPG.  The technique was actually motivated to
// simulate this optimization.  It turns out that globally blocked clauses
// can be seen as 'conditional autarkies', where in essence the condition
// cube is the negation of the globally blocked redundant clause (it
// needs to contain one autarky literal though) and the autarky part
// represents the witness.

/*------------------------------------------------------------------------*/

// Elimination of globally blocked clauses is first tried in regular
// intervals in terms of the number of conflicts.  Then the main heuristics
// is to trigger 'condition' if the decision level is above the current
// moving average of the back jump level.

// TODO We might need to consider less frequent conditioning.

internal fun Internal.conditioning(): Boolean {

    if (opts.condition == 0) return false
    if (!preprocessing && opts.inprocessing == 0) return false
    if (preprocessing) check(lim.preprocessing != 0L) { "condition: no preprocessing limit" }

    // Triggered in regular 'opts.conditionint' conflict intervals.
    //
    if (lim.condition > stats.conflicts) return false

    if (level == 0) return false // One decision necessary.

    if (level <= averages.current.jump.value) return false // Main heuristic.

    if (stats.current.irredundant == 0L) return false
    val remain = active().toDouble()
    if (remain == 0.0) return false
    val ratio = stats.current.irredundant / remain
    return ratio <= opts.conditionmaxrat
}

/*------------------------------------------------------------------------*/

// We start with the current assignment and then temporarily unassign
// literals.  They are reassigned afterwards.  The global state of the CDCL
// solver should not change though.  Thus we copied from 'search_unassign'
// in 'backtrack.cpp' what is needed to unassign literals and then from
// 'search_assign' in 'propagate.cpp' what is needed for reassigning
// literals, but restricted the copied code to only updating the actual
// assignment (in 'vals') and not changing anything else.

// We use temporarily unassigning for two purposes.  First, if a conditional
// literal does not occur negated in a candidate clause it is unassigned.
// Second, as a minor optimization, we first unassign all root-level
// assigned (fixed) literals, to avoid checking the decision level of
// literals during the procedure.

internal fun Internal.conditionUnassign(lit: Int) {
    check(value(lit) > 0) { "condition: unassigning non-true literal" }
    setVal(lit, 0)
}

internal fun Internal.conditionAssign(lit: Int) {
    check(value(lit) == 0) { "condition: assigning assigned literal" }
    setVal(lit, 1)
}

/*------------------------------------------------------------------------*/

// The current partition into conditional part and autarky part during
// refinement is represented through a conditional bit in 'marks'.

internal fun Internal.isConditionalLiteral(lit: Int): Boolean = value(lit) > 0 && getbit(lit, 0)

internal fun Internal.isAutarkyLiteral(lit: Int): Boolean = value(lit) > 0 && !getbit(lit, 0)

internal fun Internal.markAsConditionalLiteral(lit: Int) {
    check(value(lit) > 0) { "condition: marking non-true literal conditional" }
    setbit(lit, 0)
    check(isConditionalLiteral(lit)) { "condition: literal not conditional" }
    check(!isAutarkyLiteral(lit)) { "condition: conditional literal is autarky" }
}

internal fun Internal.unmarkAsConditionalLiteral(lit: Int) {
    check(isConditionalLiteral(lit)) { "condition: unmarking non-conditional literal" }
    unsetbit(lit, 0)
}

/*------------------------------------------------------------------------*/

// We also need to know the literals which are in the current clause.  These
// are just marked (also in 'marks' but with the (signed) upper two bits).
// We need a signed mark here, since we have to distinguish positive and
// negative occurrences of literals in the candidate clause.

internal fun Internal.isInCandidateClause(lit: Int): Boolean = marked67(lit) > 0

internal fun Internal.markInCandidateClause(lit: Int) {
    mark67(lit)
    check(isInCandidateClause(lit)) { "condition: literal not in candidate" }
    check(!isInCandidateClause(-lit)) { "condition: negation in candidate" }
}

internal fun Internal.unmarkInCandidateClause(lit: Int) {
    check(isInCandidateClause(lit)) { "condition: unmarking literal not in candidate" }
    unmark67(lit)
}

/*------------------------------------------------------------------------*/

private val lessConditioned = Less<Clause> { a, b -> !a.conditioned && b.conditioned }

// struct { size_t assigned, conditional, autarky; }
private class CondAssignment {
    var assigned = 0L
    var conditional = 0L
    var autarky = 0L

    fun copyFrom(other: CondAssignment) {
        assigned = other.assigned
        conditional = other.conditional
        autarky = other.autarky
    }
}

// This is the function for eliminating globally blocked clauses.  It is
// triggered during CDCL search according to 'conditioning' above and uses
// the current assignment as basis to find globally blocked clauses.

internal fun Internal.conditionRound(unassignedLiteralPropagationLimit: Long): Long {

    val delta = unassignedLiteralPropagationLimit // parameter name of the definition

    val limit: Long
    if (Long.MAX_VALUE - delta < stats.condprops) limit = Long.MAX_VALUE
    else limit = stats.condprops + delta

    val initialTrailLevel = trail.size
    val initialLevel = level

    protectReasons()

    var additionallyAssigned = 0

    for (idx in 1..maxVar) {
        val tmp = value(idx)
        val v = variable(idx)
        if (tmp != 0) {
            if (v.level != 0) {
                val lit = if (tmp < 0) -idx else idx
                if (!active(idx)) {
                    // temporarily unassigning inactive literal
                    conditionUnassign(lit)
                }
                if (frozen(idx)) {
                    // temporarily unassigning frozen literal
                    conditionUnassign(lit)
                }
            }
        } else if (frozen(idx)) {
            // keeping frozen literal unassigned
        } else if (!active(idx)) {
            // keeping inactive literal unassigned
        } else { // if (preprocessing) {
            if (initialLevel == level) {
                level++
            }
            val lit = decidePhase(idx, true)
            conditionAssign(lit)
            v.level = level
            trail.add(lit)
            additionallyAssigned++
        }
    }

    // We compute statistics about the size of the assignments.
    //
    // The initial assignment consists of the non-root-level assigned literals
    // split into a conditional and an autarky part.  The conditional part
    // consists of literals assigned true and occurring negated in a clause
    // (touch the clause), which does not contain another literal assigned to
    // true.  This initial partition is the same for all refinements used in
    // checking whether a candidate clause is globally blocked.
    //
    // For each candidate clause some of the conditional literals have to be
    // unassigned, and the autarky is shrunken by turning some of the autarky
    // literals into conditional literals (which might get unassigned in a
    // later refinement though).
    //
    // The fix-point of this procedure produces a final assignment, which
    // consists of the remaining assigned literals, again split into a
    // conditional and an autarky part.
    //
    val initial = CondAssignment()
    val remain = CondAssignment()

    initial.assigned = 0
    for (idx in 1..maxVar) {
        val tmp = value(idx)
        if (tmp == 0) continue
        if (variable(idx).level == 0) continue
        initial.assigned++
    }

    // For each candidate clause we refine the assignment (monotonically),
    // by unassigning some conditional literals and turning some autarky
    // literals into conditionals.
    //
    // As the conditional part is usually smaller than the autarky part our
    // implementation only explicitly maintains the initial conditional part,
    // with conditional bit set to true through 'mark_as_conditional_literal'.
    // The autarky part consists of all literals assigned true which do not
    // have their conditional bit set to true.  Since in both cases the
    // literal has to be assigned true, we only need a single bit for both the
    // literal as well as its negation (it does not have to be 'signed').
    //
    val conditional = IntArrayList()

    val candidates = ArrayList<Clause>() // Gather candidate clauses.

    initial.autarky = initial.assigned // Initially all are in autarky
    initial.conditional = 0 // and none in conditional part.

    // Upper bound on the number of watched clauses. In principle one could
    // use 'SIZE_MAX' but this is not available by default (yet).
    //
    val sizeMax = clauses.size + 1

    // Initialize additional occurrence lists.
    //
    initOccs()

    // Number of previously conditioned and unconditioned candidates.
    //
    var conditioned = 0L
    var unconditioned = 0L

    // Now go over all (non-garbage) irredundant clauses and check whether
    // they are candidates, have to be watched, or whether they force the
    // negation of some of their literals to be conditional initially.
    //
    for (c in clauses) {
        if (c.garbage) continue // Can already be ignored.
        if (c.redundant) continue // Ignore redundant clauses too.

        // First determine the following numbers for the candidate clause
        // (restricted to non-root-level assignments).
        //
        var positive = 0 // Number true literals.
        var negative = 0 // Number false literals.
        var watch = 0 // True Literal to watch.
        //
        var minsize = sizeMax // Number of occurrences of 'watch'.
        //
        // But also ignore root-level satisfied but not yet garbage clauses.
        //
        var satisfied = false // Root level satisfied.
        //
        var l = 0
        while (!satisfied && l != c.size) {
            val lit = c.literals[l]
            val tmp = value(lit)
            if (tmp != 0 && variable(lit).level == 0) satisfied = (tmp > 0)
            else if (tmp < 0) negative++
            else if (tmp > 0) {
                val size = occs(lit).size
                if (size < minsize) {
                    watch = lit
                    minsize = size
                }
                positive++
            }
            l++
        }
        if (satisfied) { // Ignore root-level satisfied clauses.
            markGarbage(c) // But mark them as garbage already now.
            continue // ... with next clause 'c'.
        }

        // Candidates are clauses with at least a positive literal in it.
        //
        if (positive > 0) {
            candidates.add(c)
            if (c.conditioned) conditioned++
            else unconditioned++
        }

        // Only one positive literal in each clauses with also at least one
        // negative literal has to be watched in occurrence lists.  These
        // watched clauses will be checked to contain only negative literals as
        // soon such a positive literal is unassigned.  If this is the case
        // these false literals have to be unassigned and potentially new
        // conditional literals have to be determined.
        //
        // Note that only conditional literals are unassigned. However it does
        // not matter that we might also watch autarky literals, because either
        // such an autarky literal remains a witness that the clause is
        // satisfied as long it remains an autarky literal. Otherwise at one
        // point it becomes conditional and is unassigned, but then a
        // replacement watch will be searched.
        //
        if (negative > 0 && positive > 0) {
            check(watch != 0) { "condition: no watch" }
            check(value(watch) > 0) { "condition: watch not true" }
            val os = occs(watch)
            check(os.size == minsize) { "condition: watch occurrences mismatch" }
            os.add(c)
        }

        // The initial global conditional part for the current assignment is
        // extracted from clauses with only negative literals.  It is the same
        // for all considered candidate clauses. These negative literals make up
        // the global conditional part, are marked here.
        //
        if (negative > 0 && positive == 0) {

            var newConditionals = 0L

            for (k in 0 until c.size) {
                val lit = c.literals[k]
                val tmp = value(lit)
                if (tmp == 0) continue
                check(tmp < 0) { "condition: non-false literal in negative clause" }
                if (variable(lit).level == 0) continue // Not unassigned yet!
                if (isConditionalLiteral(-lit)) continue
                markAsConditionalLiteral(-lit)
                conditional.add(-lit)
                newConditionals++
            }

            initial.conditional += newConditionals
            check(initial.autarky >= newConditionals) { "condition: autarky underflow" }
            initial.autarky -= newConditionals
        }
    } // End of loop over all clauses to collect candidates etc.

    // '#ifdef LOGGING' loop over 'conditional' (logging plus this assert; the trail loop
    // there only logs):
    for (i in 0 until conditional.size) check(isConditionalLiteral(conditional[i])) { "condition: initial conditional" }
    check(initial.conditional == conditional.size.toLong()) { "condition: conditional size mismatch" }
    check(initial.assigned == initial.conditional + initial.autarky) { "condition: initial partition mismatch" }

    stats.condassinit += initial.assigned
    stats.condcondinit += initial.conditional
    stats.condautinit += initial.autarky
    stats.condassvars += active()

    // To speed-up and particularly simplify the code we unassign all
    // root-level variables temporarily, actually all inactive assigned
    // variables.  This allows us to avoid tests on whether an assigned
    // literal is actually root-level assigned and thus should be ignored (not
    // considered to be assigned).  For this to work we have to ignore root
    // level satisfied clauses as done above.  These are neither candidates
    // nor have to be watched.  Remaining originally root-level assigned
    // literals in clauses are only set to false.
    //
    for (k in 0 until trail.size) {
        val lit = trail[k]
        if (fixed(lit) != 0) conditionUnassign(lit)
    }

    // Stack to save temporarily unassigned (conditional) literals.
    //
    val unassigned = IntArrayList()

    // Make sure to focus on clauses not tried before by marking clauses which
    // have been checked before using the 'conditioned' bit of clauses. If all
    // candidates have their bit set, we have to reset it.  Since the
    // assignment might be completely different then last time and thus also
    // the set of candidates this method does not really exactly lead to a
    // round robin scheme of scheduling clauses.
    //
    // TODO consider computing conditioned and unconditioned over all clauses.
    //
    check(conditioned + unconditioned == candidates.size.toLong()) { "condition: candidate count mismatch" }
    if (conditioned != 0L && unconditioned != 0L) {
        stableSort(candidates, lessConditioned)
    } else if (conditioned != 0L && unconditioned == 0L) {
        for (c in candidates) {
            check(c.conditioned) { "condition: candidate not conditioned" }
            c.conditioned = false // Reset 'conditioned' bit.
        }
    } else {
        check(conditioned == 0L) { "condition: unexpected conditioned candidates" }
    }

    // TODO prune assignments further!
    // And thus might result in less watched clauses.
    // So watching should be done here and not earlier.
    // Also, see below, we might need to consider the negation of unassigned
    // literals in candidate clauses as being watched.

    // Now try to block all candidate clauses.
    //
    var blocked = 0L // Number of Successfully blocked clauses.
    //
    for (c in candidates) {

        if (initial.autarky <= 0) break

        if (c.reason) continue

        var terminatedOrLimitHit = true
        if (terminatedAsynchronously()) {
            // asynchronous termination detected
        } else if (stats.condprops >= limit) {
            // condition propagation limit hit
        } else {
            terminatedOrLimitHit = false
        }

        if (terminatedOrLimitHit) {
            break
        }
        check(!c.garbage) { "condition: garbage candidate" }
        check(!c.redundant) { "condition: redundant candidate" }

        c.conditioned = true // Next time later.

        // We watch an autarky literal in the clause, and can stop trying to
        // globally block the clause as soon it turns into a conditional
        // literal and we can not find another one.  If the fix-point assignment
        // is reached and we still have an autarky literal left the watched one
        // is reported as witness for this clause being globally blocked.
        //
        var watchedAutarkyLiteral = 0

        // First mark all true literals in the candidate clause and find an
        // autarky literal which witnesses that this clause has still a chance
        // to be globally blocked.
        //
        for (k in 0 until c.size) {
            val lit = c.literals[k]
            markInCandidateClause(lit)
            if (watchedAutarkyLiteral != 0) continue
            if (!isAutarkyLiteral(lit)) continue
            watchedAutarkyLiteral = lit

            // TODO assign non-assigned literals to false?
            // Which might need to trigger watching additional clauses.
        }

        if (watchedAutarkyLiteral == 0) {
            for (k in 0 until c.size) unmarkInCandidateClause(c.literals[k])
            continue
        }

        stats.condcands++ // Only now ...

        // Save assignment sizes for statistics, logging and checking.
        //
        remain.copyFrom(initial)

        // Position of next conditional and unassigned literal to process in the
        // 'conditional' and the 'unassigned' stack.
        //
        var nextConditional = 0
        var nextUnassigned = 0

        check(unassigned.isEmpty()) { "condition: unassigned not empty" }
        check(conditional.size.toLong() == initial.conditional) { "condition: conditional size changed" }

        while (watchedAutarkyLiteral != 0 && stats.condprops < limit &&
            nextConditional < conditional.size
        ) {

            check(nextUnassigned == unassigned.size) { "condition: unprocessed unassigned literals" }

            val conditionalLit = conditional[nextConditional++]
            check(isConditionalLiteral(conditionalLit)) { "condition: processing non-conditional" }

            if (isInCandidateClause(-conditionalLit)) {
                // conditional negated in candidate clause
                continue
            }

            // conditional does not occur negated in candidate clause

            conditionUnassign(conditionalLit)
            check(!isConditionalLiteral(conditionalLit)) { "condition: unassigned still conditional" }
            unassigned.add(conditionalLit)

            check(remain.assigned > 0) { "condition: remain assigned underflow" }
            check(remain.conditional > 0) { "condition: remain conditional underflow" }
            remain.conditional--
            remain.assigned--

            while (watchedAutarkyLiteral != 0 && stats.condprops < limit &&
                nextUnassigned < unassigned.size
            ) {
                val unassignedLit = unassigned[nextUnassigned++]
                check(value(unassignedLit) == 0) { "condition: unassigned literal assigned" }
                stats.condprops++

                val os = occs(unassignedLit)
                if (os.isEmpty()) continue

                // Traverse all watched clauses of 'unassigned_lit' and find
                // replacement watches or if none is found turn the negation of all
                // false autarky literals in that clause into conditional literals.
                // If one of those autarky literals is the watched autarky literal
                // in the candidate clause, that one has to be updated too.
                //
                // We expect that this loop is a hot-spot for the procedure and thus
                // are more careful about accessing end points for iterating.
                //
                var i = 0
                var j = i
                while (watchedAutarkyLiteral != 0 && j != os.size) {
                    val d = os[j]
                    os[i++] = d

                    var replacement = 0 // New watched literal in 'd'.
                    var negative = 0 // Negative autarky literals in 'd'.

                    for (k in 0 until d.size) {
                        val lit = d.literals[k]
                        val tmp = value(lit)
                        if (tmp > 0) replacement = lit
                        if (tmp < 0 && isAutarkyLiteral(-lit)) negative++
                    }

                    if (replacement != 0) {
                        i-- // Drop watch!

                        check(replacement != unassignedLit) { "condition: replacement is unassigned literal" }
                        occs(replacement).add(d)

                        j++
                        continue // ... with next watched clause 'd'.
                    }

                    // Keep watching 'd' by 'unassigned_lit' if no replacement found.

                    if (negative == 0) {
                        j++
                        continue // ... with next watched clause 'd'.
                    }

                    var l = 0
                    while (watchedAutarkyLiteral != 0 && l != d.size) {
                        val lit = d.literals[l]
                        l++
                        if (!isAutarkyLiteral(-lit)) continue
                        markAsConditionalLiteral(-lit)
                        conditional.add(-lit)

                        remain.conditional++
                        check(remain.autarky > 0) { "condition: remain autarky underflow" }
                        remain.autarky--

                        if (-lit != watchedAutarkyLiteral) continue

                        // need to replace autarky literal in candidate
                        replacement = 0

                        // TODO save starting point because we only move it forward?

                        var k = 0
                        while (replacement == 0 && k != c.size) {
                            val other = c.literals[k]
                            if (isAutarkyLiteral(other)) replacement = other
                            k++
                        }
                        watchedAutarkyLiteral = replacement

                        if (replacement != 0) {
                            watchedAutarkyLiteral = replacement
                        } else {
                            // failed to find an autarky replacement
                            watchedAutarkyLiteral = 0 // Breaks out of 4 loops!!!!!
                        }
                    } // End of loop of turning autarky literals into conditionals.
                    j++
                } // End of loop of all watched clauses of an unassigned literal.
                //
                // We might abort the occurrence traversal early but already
                // removed some watches, thus have to just copy the rest.
                //
                if (i < j) {
                    while (j != os.size) os[i++] = os[j++]
                    os.shrinkTo(i)
                }
            } // End of loop which goes over all unprocessed unassigned literals.
        } // End of loop which goes over all unprocessed conditional literals.

        // We are still processing the candidate 'c' and now have reached a
        // final fix-point assignment partitioned into a conditional and an
        // autarky part, or during unassigned literals figured that there is no
        // positive autarky literal left in 'c'.

        check(remain.assigned - remain.conditional == remain.autarky) { "condition: remain partition mismatch" }

        // This is a sanity check, that the size of our implicit representation
        // of the autarky part matches our 'remain' counts.  We need the same
        // code for determining autarky literals as in the loop below which adds
        // autarky literals to the extension stack.
        //
        run {
            var checkAssigned = 0L
            var checkConditional = 0L
            var checkAutarky = 0L
            for (k in 0 until trail.size) {
                val lit = trail[k]
                if (value(lit) != 0) {
                    checkAssigned++
                    if (isConditionalLiteral(lit)) {
                        check(!isAutarkyLiteral(lit)) { "condition: conditional is autarky" }
                        checkConditional++
                    } else {
                        check(isAutarkyLiteral(lit)) { "condition: assigned neither conditional nor autarky" }
                        checkAutarky++
                    }
                } else {
                    check(!isAutarkyLiteral(lit)) { "condition: unassigned autarky" }
                    check(!isConditionalLiteral(lit)) { "condition: unassigned conditional" }
                }
            }
            check(remain.assigned == checkAssigned) { "condition: remain assigned mismatch" }
            check(remain.conditional == checkConditional) { "condition: remain conditional mismatch" }
            check(remain.autarky == checkAutarky) { "condition: remain autarky mismatch" }
        }

        // Success if an autarky literal is left in the clause and
        // we did not abort the loop too early because the propagation
        // limit was hit.
        //
        if (watchedAutarkyLiteral != 0 && stats.condprops < limit) {
            check(isAutarkyLiteral(watchedAutarkyLiteral)) { "condition: witness not autarky" }
            check(isInCandidateClause(watchedAutarkyLiteral)) { "condition: witness not in candidate" }

            blocked++
            stats.conditioned++

            // A satisfying assignment of a formula after removing a globally
            // blocked clause might not satisfy that clause.  As for variable
            // elimination and classical blocked clauses, we thus maintain an
            // extension stack for reconstructing an assignment which both
            // satisfies the remaining formula as well as the clause.
            //
            // For globally blocked clauses we simply have to flip all literals in
            // the autarky part and thus save the autarky on the extension stack
            // in addition to the removed clause.  In the classical situation (in
            // bounded variable elimination etc.) we simply save one literal on
            // the extension stack.
            //
            // TODO find a way to shrink the autarky part or some other way to
            // avoid pushing too many literals on the extension stack.
            //
            val ext = external!!
            ext.pushZeroOnExtensionStack()
            for (k in 0 until trail.size) {
                val lit = trail[k]
                if (isAutarkyLiteral(lit)) ext.pushWitnessLiteralOnExtensionStack(lit)
            }
            proof?.weakenMinus(c)
            ext.pushClauseOnExtensionStack(c)

            markGarbage(c)

            stats.condassrem += remain.assigned
            stats.condcondrem += remain.conditional
            stats.condautrem += remain.autarky
            stats.condassirem += initial.assigned
        }

        // In this last part specific to one candidate clause, we have to get
        // back to the initial assignment and reset conditionals.  First we
        // assign all the unassigned literals (if necessary).
        //
        if (!unassigned.isEmpty()) {
            while (!unassigned.isEmpty()) {
                val lit = unassigned.back()
                unassigned.removeLast()
                conditionAssign(lit)
            }
        }

        // Then we remove from the conditional stack autarky literals which
        // became conditional and also reset their 'conditional' bit.
        //
        if (initial.conditional < conditional.size) {
            while (initial.conditional < conditional.size) {
                val lit = conditional.back()
                conditional.removeLast()
                unmarkAsConditionalLiteral(lit)
            }
        }

        // Finally unmark all literals in the candidate clause.
        //
        for (k in 0 until c.size) unmarkInCandidateClause(c.literals[k])
    } // End of loop over all candidate clauses.

    // Unmark initial conditional variables.
    //
    for (k in 0 until conditional.size) unmarkAsConditionalLiteral(conditional[k])

    unassigned.clear()
    conditional.clear()
    candidates.clear()

    // Unassign additionally assigned literals.
    //
    var additionallyUnassigned = 0
    while (trail.size > initialTrailLevel) {
        val lit = trail.back()
        trail.removeLast()
        conditionUnassign(lit)
        additionallyUnassigned++
    }
    check(additionallyUnassigned == additionallyAssigned) { "condition: unassigned count mismatch" }

    if (level > initialLevel) {
        level = initialLevel
    }

    resetOccs()
    deleteGarbageClauses()

    // Reassign previously assigned variables again.
    //
    for (i in 0 until initialTrailLevel) {
        val lit = trail[i]
        val tmp = value(lit)
        check(tmp >= 0) { "condition: previously assigned literal false" }
        if (tmp == 0) conditionAssign(lit)
    }

    for (k in 0 until trail.size) check(marked(trail[k]) == 0) { "condition: marked literal on trail" }

    unprotectReasons()

    return blocked
}

internal fun Internal.condition(updateLimits: Boolean = true): Unit = tracePhase("condition") {

    if (unsat) return
    if (stats.current.irredundant == 0L) return

    startSimplifier(Internal.CONDITION)
    stats.conditionings++

    // Propagation limit to avoid too much work in 'condition'.  We mark
    // tried candidate clauses after giving up, such that next time we run
    // 'condition' we can try them.
    //
    var limit = stats.propagations.search
    limit *= opts.conditionreleff
    limit /= 1000
    if (limit < opts.conditionmineff) limit = opts.conditionmineff.toLong()
    if (limit > opts.conditionmaxeff) limit = opts.conditionmaxeff.toLong()
    check(stats.current.irredundant != 0L) { "condition: no irredundant clauses" }
    limit = (limit.toDouble() * (2.0 * active() / stats.current.irredundant.toDouble())).toLong()
    limit = maxOf(limit, 2L * active())

    conditionRound(limit) // 'long blocked' only feeds 'report ('g', !blocked)' (dropped)

    stopSimplifier(Internal.CONDITION)

    if (!updateLimits) return

    val delta = opts.conditionint.toLong() * (stats.conditionings + 1)
    lim.condition = stats.conflicts + delta
}
