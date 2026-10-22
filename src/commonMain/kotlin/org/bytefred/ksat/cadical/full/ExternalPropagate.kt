package org.bytefred.ksat.cadical.full

import kotlin.math.abs
import org.bytefred.ksat.cadical.IntArrayList

/*
 * external_propagate.cpp: the IPASIR-UP layer of the internal solver (observed variables,
 * notifications, external propagation, external clauses and reasons, final model check).
 *
 * Mapping:
 *  - 'external->propagator->...' -> 'external!!.propagator!!....' (the call backs are only
 *    reached with a connected propagator, as upstream dereferences without a check). The
 *    interface is the ksat-common 'ExternalPropagator' (CadicalHpp.kt): 'std::vector<int>'
 *    arguments are passed as 'IntArray', 'bool &is_forgettable' as 'OutFlag' (OutBoolean).
 *  - 'std::move (v)' of a vector into a local followed by 'v.clear ()' -> copy into a fresh
 *    list and clear the field; moving back ('v = std::move (tmp)') -> clear + copy back.
 *  - 'learn_external_reason_clause' and 'wrapped_learn_external_reason_clause' return
 *    'Clause?': upstream returns 'newest_clause', which is 0 for satisfied, unit and empty
 *    external clauses, and the callers (assume.cpp, analyze.cpp, ...) test for that.
 *  - 'size_t new_level' -> Int (a negative value stands for a huge 'size_t').
 *  - 'get_merged_literals' / 'get_all_fixed_literals' are '#ifndef NDEBUG' debugging helpers
 *    for mobical: not in release, not ported (PORTING.md).
 */

/*----------------------------------------------------------------------------*/
//
// Mark a variable as an observed one. It can be a new variable. It is
// assumed to be clean (not eliminated by previous simplifications).
//
internal fun Internal.addObservedVar(ilit: Int) {
    val idx = vidx(ilit)
    if (idx.toLong() >= relevanttab.size.toLong())
        relevanttab = relevanttab.resized(1 + idx, 0)
    val ref = relevanttab[idx]
    if (ref.toUInt() < UInt.MAX_VALUE) {
        relevanttab[idx] = ref + 1
        // variable idx is observed ref times
    } else {
        // variable idx remains observed forever
    }
    // TODO: instead of actually backtracking, it would be enough to notify
    // backtrack and re-play again every levels' notification to the
    // propagator
    if (value(ilit) != 0 && level != 0 && fixed(ilit) == 0) {
        // The variable is already assigned, but we can not send a notification
        // about it because it happened on an earlier decision level.
        // To not break the stack-like view of the trail, we simply backtrack to
        // undo this unnotifiable assignment.
        val assignmentLevel = variable(ilit).level
        backtrack(assignmentLevel - 1)
    } else if (level != 0 && fixed(ilit) != 0) {
        backtrack(0)
    }
}

/*----------------------------------------------------------------------------*/
//
// Removing an observed variable should happen only once it is ensured
// that there is no unexplained propagation in the implication
// graph involving this variable.
//
internal fun Internal.removeObservedVar(ilit: Int) {
    if (fixed(ilit) == 0 && level != 0) {
        backtrack()
    }

    check(fixed(ilit) != 0 || level == 0) { "remove_observed_var: not at root level" }

    val idx = vidx(ilit)
    check(idx < relevanttab.size) { "remove_observed_var: relevanttab too small" }
    var ref = relevanttab[idx]
    check(fixed(ilit) != 0 || ref.toUInt() > 0u) { "remove_observed_var: not observed" }
    if (fixed(ilit) != 0)
        ref = 0
    else if (ref.toUInt() < UInt.MAX_VALUE) {
        if (--ref == 0) {
            // variable idx is not observed anymore
        } else {
            // variable is unobserved once but remains observed ref times
        }
    } else {
        // variable idx remains observed forever
    }
    relevanttab[idx] = ref
}

/*----------------------------------------------------------------------------*/
//
// Supposed to be used only by mobical.
//
internal fun Internal.observed(ilit: Int): Boolean {
    check(vidx(ilit) < relevanttab.size) { "observed: relevanttab too small" }
    return relevanttab[vidx(ilit)] != 0
}

/*----------------------------------------------------------------------------*/
//
// Check for unexplained propagations upon disconnecting external propagator
//
internal fun Internal.setTaintedLiteral() {
    if (opts.ilb == 0) {
        return
    }
    for (idx in vars) {
        if (value(idx) == 0)
            continue
        if (variable(idx).reason !== externalReason)
            continue
        if (taintedLiteral == 0) {
            taintedLiteral = idx
            continue
        }
        check(value(taintedLiteral) != 0) { "set_tainted_literal: tainted literal unassigned" }
        if (variable(idx).level < variable(taintedLiteral).level) {
            taintedLiteral = idx
        }
    }
}

internal fun Internal.renotifyTrailAfterIlb() {
    if (!externalProp || externalPropIsLazy || trail.size == 0 ||
        opts.ilb == 0
    ) {
        return
    }
    // notify external propagator about new assignments (after ilb)
    renotifyFullTrail()
}

internal fun Internal.renotifyTrailAfterLocalSearch() {
    if (!externalProp || externalPropIsLazy || trail.size == 0) {
        return
    }
    // notify external propagator about new assignments (after local search)
    renotifyFullTrail()
}

// It repeats ALL assignments of the trail, so the already notified
// root-level assignments will be notified multiple times.

internal fun Internal.renotifyFullTrail() {
    val external = external!!
    val endOfTrail = trail.size
    if (level != 0) {
        notified = 0 // TODO: save the last notified root-level position
        // somewhere and use it here
        notifyBacktrack(0)
    }
    val assigned = IntArrayList()

    var prevMaxLevel = 0
    var currentLevel: Int
    var propagatorLevel = 0

    while (notified < endOfTrail) {
        val ilit = trail[notified++]
        // In theory, 0 ilit can happen due to pseudo-decision levels
        if (ilit == 0)
            currentLevel = prevMaxLevel + 1
        else
            currentLevel = variable(ilit).level

        if (currentLevel > propagatorLevel) {
            if (assigned.size != 0)
                external.propagator!!.notifyAssignment(assigned.toArray())
            while (currentLevel > propagatorLevel) {
                external.propagator!!.notifyNewDecisionLevel()
                propagatorLevel++
            }
            assigned.clear()
        }
        // Current level can be smaller than prev_max_level due to chrono
        if (currentLevel > prevMaxLevel)
            prevMaxLevel = currentLevel

        if (!observed(ilit))
            continue

        val elit = externalize(ilit) // TODO: double-check tainting
        check(elit != 0)
        // Fixed variables might get mapped (during compact) to another
        // non-observed but fixed variable.
        // This happens on root level, so notification about their assignment is
        // already done.
        check(external.observed(elit) || fixed(ilit) != 0) { "renotify_full_trail: not observed" }
        assigned.add(elit)
    }
    if (assigned.size != 0)
        external.propagator!!.notifyAssignment(assigned.toArray())
    assigned.clear()

    // In case there are some left over empty levels on the top of the trail,
    // the external propagtor must be notified about them so the levels are
    // synced
    while (level > propagatorLevel) {
        external.propagator!!.notifyNewDecisionLevel()
        propagatorLevel++
    }

    return
}

/*----------------------------------------------------------------------------*/
//
// Check if the variable is assigned by decision.
//
internal fun Internal.isDecision(ilit: Int): Boolean {
    if (level == 0 || fixed(ilit) != 0 || value(ilit) == 0)
        return false

    val idx = vidx(ilit)
    val v = variable(idx)
    if (v.level == 0 || v.reason != null)
        return false
    check(v.reason == null)
    return true
}

internal fun Internal.forceBacktrack(newLevel: Int) {
    // 'new_level >= (size_t) level' with 'size_t new_level': negative is huge.
    if (!forcedBacktAllowed || level <= 0 || newLevel < 0 || newLevel >= level)
        return

    // external propagator forces backtrack to decision level newLevel
    backtrack(newLevel)
}

/*----------------------------------------------------------------------------*/
//
// Call external propagator to check if there is a literal to be propagated.
// The reason of the propagation is not necessarily asked at that point.
//
// In case the externally propagated literal is already falsified, the
// reason is asked and conflict analysis starts. In case the externally
// propagated literal is already satisfied, nothing happens.
//
internal fun Internal.externalPropagate(): Boolean {
    val external = external!!
    if (level != 0)
        requireMode(Internal.SEARCH)
    check(!unsat) { "external_propagate: unsat" }

    val before = numAssigned
    var cbRepropagateNeeded = true
    while (cbRepropagateNeeded && conflict == null && externalProp &&
        !externalPropIsLazy && !privateSteps
    ) {
        cbRepropagateNeeded = false
        // external->reset_extended (); //TODO for inprocessing

        notifyAssignments()

        var elit = external.propagator!!.cbPropagate()
        stats.extProp.extCb++
        stats.extProp.epropCall++
        while (elit != 0) {
            check(external.isObserved[abs(elit)]) { "external_propagate: not observed" }
            var ilit = external.e2i[abs(elit)]
            if (elit < 0)
                ilit = -ilit
            val tmp = value(ilit)
            // '#ifndef NDEBUG' upstream: 'assert (fixed (ilit) || observed (ilit))', not in release.
            if (tmp == 0) {
                // variable is not assigned, it can be propagated
                if (level == 0) {
                    learnExternalReasonClause(ilit, elit)
                } else
                    searchAssignExternal(ilit)
                stats.extProp.epropProp++

                if (unsat || conflict != null)
                    break
                propagate()
                if (unsat || conflict != null)
                    break
                notifyAssignments()
            } else if (tmp < 0) {
                // External propagation of ilit is falsified under current trail
                stats.extProp.epropConf++
                val levelBefore = level
                val assigned = numAssigned
                learnExternalReasonClause(ilit, elit)
                val trailChanged =
                    (numAssigned != assigned || level != levelBefore ||
                        propagated < trail.size)

                if (unsat || conflict != null)
                    break

                if (trailChanged) {
                    propagate()
                    if (unsat || conflict != null)
                        break
                    notifyAssignments()
                }
            } // else (tmp > 0) -> the case of a satisfied literal is ignored
            elit = external.propagator!!.cbPropagate()
            stats.extProp.extCb++
            stats.extProp.epropCall++
        }

        if (!unsat && conflict == null) {
            var levelBefore = level
            var assigned = numAssigned
            var hasExternalClause = askExternalClause()
            // New observed variable might have triggered a backtrack during this
            // ask_external_clause call, so we need to propagate before continuing
            stats.extProp.extCb++
            stats.extProp.elearnCall++

            var trailChanged =
                (numAssigned != assigned || level != levelBefore ||
                    propagated < trail.size)
            if (trailChanged) {
                propagate() // unsat or conflict will be caught later
                if (!unsat || conflict == null)
                    notifyAssignments()
            }

            while (hasExternalClause) {
                levelBefore = level
                assigned = numAssigned

                addExternalClause(0)
                trailChanged =
                    (numAssigned != assigned || level != levelBefore ||
                        propagated < trail.size)
                cbRepropagateNeeded = true

                if (unsat || conflict != null) {
                    cbRepropagateNeeded = false
                    break
                }

                if (trailChanged) {
                    propagate()
                    if (unsat || conflict != null) {
                        cbRepropagateNeeded = false
                        break
                    }

                    notifyAssignments()
                }
                hasExternalClause = askExternalClause()
                stats.extProp.extCb++
                stats.extProp.elearnCall++
            }
        }
    }
    if (before < numAssigned)
        didExternalProp = true
    return conflict == null
}

/*----------------------------------------------------------------------------*/
//
// Helper function, calls 'cb_has_external_clause', while maintains the
// related redundancy type of the clause.
//

internal fun Internal.askExternalClause(): Boolean {
    extClauseForgettable = false
    val isForgettable = OutFlag(extClauseForgettable)
    val res =
        external!!.propagator!!.cbHasExternalClause(isForgettable)
    extClauseForgettable = isForgettable.value

    return res
}
/*----------------------------------------------------------------------------*/
//
// Literals of the externally learned clause must be reordered based on the
// assignment levels of the literals.
//
internal fun Internal.moveLiteralsToWatch() {
    if (clause.size < 2)
        return
    if (level == 0)
        return

    for (i in 0 until 2) {
        var highestPosition = i
        var highestLiteral = clause[i]

        var highestLevel = variable(highestLiteral).level
        var highestValue = value(highestLiteral)

        for (j in i + 1 until clause.size) {
            val other = clause[j]
            val otherLevel = variable(other).level
            val otherValue = value(other)

            if (otherValue < 0) {
                if (highestValue >= 0)
                    continue
                if (otherLevel <= highestLevel)
                    continue
            } else if (otherValue > 0) {
                if (highestValue > 0 && otherLevel >= highestLevel)
                    continue
            } else {
                if (highestValue >= 0)
                    continue
            }

            highestPosition = j
            highestLiteral = other
            highestLevel = otherLevel
            highestValue = otherValue
        }

        if (highestPosition == i)
            continue
        if (highestPosition > i) {
            val tmp = clause[i]
            clause[i] = clause[highestPosition]
            clause[highestPosition] = tmp
        }
    }
}

/*----------------------------------------------------------------------------*/
//
// Reads out from the external propagator the lemma/proapgation reason
// clause literal by literal. In case propagated_elit is 0, it is about an
// external clause via 'cb_add_external_clause_lit'. Otherwise, it is about
// learning the reason of 'propagated_elit' via 'cb_add_reason_clause_lit'.
// The learned clause is simplified by the current root-level assignment
// (i.e. root-level falsified literals are removed, root satisfied clauses
// are skipped). Duplicate literals are removed, tauotologies are detected
// and skipped. It always adds the original (un-simplified) external clause
// to the proof as an input clause and
// the simplified version of it (except exceptions below) as a derived
// clause.
//
// In case the external clause, after simplifications, is satisfied, no
// clause is constructed, and the function returns 0. In case the external
// clause, after simplifications, is empty, no clause is constructed, unsat
// is set true and the function returns 0. In case the external clause,
// after simplifications, is unit, no clause is constructed,
// 'Internal::clause' has the unit literal (without 0) and the function
// returns 0.
//
// In every other cases a new clause is constructed and the pointer is in
// newest_clause
//
// (upstream parameter name 'propagated_elit', SIGNATURES.md name 'propagatedLit')
internal fun Internal.addExternalClause(propagatedLit: Int = 0, noBacktrack: Boolean = false) {
    val external = external!!
    val propagatedElit = propagatedLit
    check(original.isEmpty()) { "add_external_clause: original not empty" }
    var elit: Int

    if (propagatedElit != 0) {
        // Propagation reason clauses are by default assumed to be forgettable
        // irredundant. In case they would be unforgettably important, the
        // propagator can add them as an explicit unforgettable external clause
        // or set 'are_reasons_forgettable' to false.
        extClauseForgettable = external.propagator!!.areReasonsForgettable
        elit = external.propagator!!.cbAddReasonClauseLit(propagatedElit)
    } else
        elit = external.propagator!!.cbAddExternalClauseLit()

    // we need to be build a new LRAT chain if we are already in the middle of
    // the analysis (like during failed assumptions)
    val lratChainExt = ArrayList(lratChain) // std::move (lrat_chain)
    lratChain.clear()
    clause.clear()

    // Read out the external lemma into original and simplify it into clause
    check(clause.isEmpty())
    check(original.isEmpty())

    check(!forceNoBacktrack) { "add_external_clause: force_no_backtrack set" }
    check(!fromPropagator) { "add_external_clause: from_propagator set" }
    forceNoBacktrack = noBacktrack
    fromPropagator = true
    while (elit != 0) {
        check(external.isObserved[abs(elit)]) { "add_external_clause: not observed" }
        external.add(elit)
        if (propagatedElit != 0)
            elit =
                external.propagator!!.cbAddReasonClauseLit(propagatedElit)
        else
            elit = external.propagator!!.cbAddExternalClauseLit()
    }
    external.add(elit)
    check(original.isEmpty()) { "add_external_clause: original not empty after add" }
    check(clause.isEmpty()) { "add_external_clause: clause not empty after add" }
    forceNoBacktrack = false
    fromPropagator = false
    lratChain.clear() // lrat_chain = std::move (lrat_chain_ext)
    lratChain.addAll(lratChainExt)
}

/*----------------------------------------------------------------------------*/
//
// Recursively calls 'learn_external_reason_clause' to explain every
// backward reachable externally propagated literal starting from 'ilit'.
//
// (upstream parameter name 'ilit', SIGNATURES.md name 'lit')
internal fun Internal.explainReason(lit: Int, reason: Clause, open: IntRef) {
    val ilit = lit
    if (opts.exteagerreasons == 0)
        return
    check(reason !== externalReason) { "explain_reason: external reason" }
    for (k in 0 until reason.size) {
        val other = reason.literals[k]
        if (other == ilit)
            continue
        val f = flags(other)
        if (f.seen)
            continue
        val v = variable(other)
        if (v.level == 0)
            continue
        check(value(other) < 0) { "explain_reason: literal not false" }
        check(v.level <= level) { "explain_reason: level above current" }
        if (v.reason === externalReason) {
            v.reason = learnExternalReasonClause(-other, 0, true)
        }
        if (v.level != 0 && v.reason != null) {
            f.seen = true
            open.value++
        }
    }
}

/*----------------------------------------------------------------------------*/
//
// In case external propagation was used, the reason clauses of the relevant
// propagations must be learned lazily before/during conflict analysis.
// While conflict analysis needs to analyze only the current level, lazy
// clause learning must check every clause on every level that is backward
// reachable from the conflicting clause to guarantee that the assignment
// levels of the variables are accurate. So this explanation round is
// separated from the conflict analysis, thereby guranteeing that the flags
// and datastructures can be properly used later.
//
// This function must be called before the conflict analysis, in order to
// guarantee that every relevant reason clause is indeed learned already and
// to be sure that the levels of assignments are set correctly.
//
// Later TODO: experiment with bounded explanation (explain only those
// literals that are directly used during conflict analysis +
// minimizing/shrinking). The assignment levels are then only
// over-approximated.
//
internal fun Internal.explainExternalPropagations() {
    check(conflict != null) { "explain_external_propagations: no conflict" }
    check(clause.isEmpty()) { "explain_external_propagations: clause not empty" }

    val reason = conflict!!
    val seenLits = IntArrayList()
    val open = IntRef(0) // Seen but not explained literal

    explainReason(0, reason, open) // marks conflict clause lits as seen
    var i = trail.size // Start at end-of-trail
    while (i > 0) {
        val lit = trail[--i]
        if (!flags(lit).seen)
            continue
        seenLits.add(lit)
        val v = variable(lit)
        if (v.level == 0)
            continue
        val r = v.reason
        if (r != null) {
            open.value--
            explainReason(lit, r, open)
        }
        if (open.value == 0)
            break
    }
    check(open.value == 0) { "explain_external_propagations: open literals left" }

    if (opts.exteagerrecalc == 0) {
        for (k in 0 until seenLits.size) {
            val f = flags(seenLits[k])
            f.seen = false
        }
        // '#ifndef NDEBUG' check that no variable is 'seen' skipped (scans all variables
        // on every conflict).
    }

    // Traverse now in the opposite direction (from lower to higher levels)
    // and calculate the actual assignment level for the seen assignments.
    for (it in seenLits.size - 1 downTo 0) {
        val lit = seenLits[it]
        val f = flags(lit)
        val v = variable(lit)
        val r = v.reason
        if (r != null) {
            var realLevel = 0
            for (k in 0 until r.size) {
                val other = r.literals[k]
                if (other == lit)
                    continue
                val tmp = variable(other).level
                if (tmp > realLevel)
                    realLevel = tmp
            }
            if (v.level != 0 && realLevel == 0) {
                buildChainForUnits(lit, r, true)
                learnUnitClause(lit)
                lratChain.clear()
                v.reason = null
            }
            check(v.level >= realLevel) { "explain_external_propagations: level below real level" }
            if (v.level > realLevel) {
                v.level = realLevel
            }
        }
        f.seen = false
    }

    // '#ifndef NDEBUG' check that no variable is 'seen' skipped (scans all variables on
    // every conflict).
}

/*----------------------------------------------------------------------------*/
//
// Learns the reason clause of the propagation of ilit from the
// external propagator via 'add_external_clause'.
// In case of falsified propagation steps, if the propagated literal is
// already fixed to the opposite value, externalize will not necessarily
// give back the original elit (but an equivalent one). To avoid that, in
// falsified propagation cases the propagated elit is added as a second
// argument.
//
// (upstream parameter name 'ilit', SIGNATURES.md name 'lit')
internal fun Internal.learnExternalReasonClause(
    lit: Int,
    falsifiedElit: Int = 0,
    noBacktrack: Boolean = false,
): Clause? {
    val ilit = lit
    check(external!!.propagator != null) { "learn_external_reason_clause: no propagator" }
    // we cannot modify clause during analysis
    val clauseTmp = IntArrayList() // auto clause_tmp = std::move (clause)
    clauseTmp.assign(clause)
    clause.clear()

    check(clause.isEmpty())
    check(original.isEmpty()) { "learn_external_reason_clause: original not empty" }

    stats.extProp.epropExpl++

    var elit: Int
    if (falsifiedElit == 0) {
        check(fixed(ilit) == 0) { "learn_external_reason_clause: fixed literal" }
        elit = externalize(ilit)
    } else
        elit = falsifiedElit

    addExternalClause(elit, noBacktrack)

    // '#ifndef NDEBUG' upstream (trail-order check of the propagator's reason): not in the
    // release reference, not ported.

    clause.assign(clauseTmp) // clause = std::move (clause_tmp)
    return newestClause
}

/*----------------------------------------------------------------------------*/
//
// Helper function to be able to call learn_external_reason_clause when the
// internal clause is already used in the caller side (for example during
// proof checking). These calls are assumed to be without a falsified elit.
// Dont use it in general instead of learn_external_reason_clause because it
// does not support the corner cases where a literal remains in clause.
//
// (upstream parameter name 'ilit', SIGNATURES.md name 'lit')
internal fun Internal.wrappedLearnExternalReasonClause(lit: Int): Clause? {
    val ilit = lit
    val res: Clause?
    val chainTmp = ArrayList(lratChain) // std::vector<uint64_t> chain_tmp{std::move (lrat_chain)}
    lratChain.clear()
    if (clause.isEmpty()) {
        res = learnExternalReasonClause(ilit, 0, true)
    } else {
        val clauseTmp = IntArrayList() // std::vector<int> clause_tmp{std::move (clause)}
        clauseTmp.assign(clause)
        clause.clear()
        res = learnExternalReasonClause(ilit, 0, true)
        // The learn_external_reason clause can leave a literal in clause when
        // there is a falsified elit arg. Here it is not allowed to
        // happen.
        check(clause.isEmpty()) { "wrapped_learn_external_reason_clause: clause not empty" }

        clause.assign(clauseTmp)
        clauseTmp.clear()
    }
    check(lratChain.isEmpty()) { "wrapped_learn_external_reason_clause: chain not empty" }
    lratChain.clear() // lrat_chain = std::move (chain_tmp)
    lratChain.addAll(chainTmp)
    chainTmp.clear()
    return res
}

/*----------------------------------------------------------------------------*/
//
// Checks if the new clause forces backtracking, new assignments or conflict
// analysis
//
internal fun Internal.handleExternalClause(res: Clause?) {
    if (fromPropagator)
        stats.extProp.elearned++
    // at level 0 we have to do nothing...
    if (level == 0)
        return
    if (res == null) {
        if (fromPropagator)
            stats.extProp.elearnProp++
        // new unit clause. For now just backtrack.
        check(!forceNoBacktrack) { "handle_external_clause: unit with force_no_backtrack" }
        check(level != 0)
        // if (!opts.chrono) {
        backtrack()
        // }
        return
    }
    if (fromPropagator)
        stats.extProp.elearned++
    check(res.size >= 2) { "handle_external_clause: clause too small" }
    val pos0 = res.literals[0]
    val pos1 = res.literals[1]
    if (forceNoBacktrack) {
        check(value(pos1) < 0) { "handle_external_clause: second watch not false" }
        check(value(pos0) >= 0) { "handle_external_clause: first watch false" }
        return
        // TODO: maybe fix levels
    }
    val l1 = variable(pos1).level
    if (value(pos0) < 0) { // conflicting or propagating clause
        check(0 < l1 && l1 <= variable(pos0).level) { "handle_external_clause: levels" }
        if (opts.chrono == 0) {
            backtrack(l1)
        }
        if (value(pos0) < 0) {
            conflict = res
            if (!fromPropagator) {
                // analyze (); // TODO: is it good to do conflict analysis?
                // apparently its better to backtrack :(
                backtrack(l1 - 1)
                conflict = null
                check(value(pos0) == 0 && value(pos1) == 0) { "handle_external_clause: watches assigned" }
            }
        } else {
            searchAssignDriving(pos0, res)
        }
        if (fromPropagator)
            stats.extProp.elearnConf++
        return
    }
    if (value(pos1) < 0 && value(pos0) == 0) { // propagating clause
        if (opts.chrono == 0) {
            backtrack(l1)
        }
        searchAssignDriving(pos0, res)
        if (fromPropagator)
            stats.extProp.elearnConf++
        return
    }
}

/*----------------------------------------------------------------------------*/
//
// Asks the external propagator if the current solution is OK
// by calling 'cb_check_found_model (model)'.
//
// The checked model is built up after everything is restored
// from the reconstruction stack and every variable is reactivated
// and so it is not just simply the trail (i.e. it can be expensive).
//
// If the external propagator approves the model, the function
// returns true.
//
// If the propagator does not approve the model, the solver asks
// the propagator to add an external clause.
// This external clause, however, does NOT have to be falsified by
// the current model. The possible cases and reactions are described
// below in the function. The possible states after that function:
// - A solution was found and accepted by the external propagator
// - A conflicting clause was learned from the external propagator
// - The empty clause was learned due to something new learned from
// the external propagator.
//
// In case only new variables were introduced, but no new clauses were
// added, the function will return without a conflict to the outer CDCL
// loop, where the new (not yet satisfied) variables are recognized and
// the search continues.
internal fun Internal.externalCheckSolution(): Boolean {
    if (!externalProp)
        return true
    val external = external!!

    var trailChanged = true
    var addedNewClauses = false
    while (trailChanged || addedNewClauses) {
        notifyAssignments()
        if (!satisfied())
            break
        trailChanged = false // to be on the safe side
        addedNewClauses = false
        // Final check by external propagator is invoked.
        stats.extProp.echeckCall++
        external.resetExtended()
        external.extend()

        val etrail = IntArrayList()

        // Here the variables must be filtered by external->is_observed,
        // because fixed variables are internally not necessarily observed
        // anymore.
        for (idx in 1..external.maxVar) {
            if (!external.isObserved[idx])
                continue
            val lit = external.ival(idx)
            etrail.add(lit)
        }

        val isConsistent =
            external.propagator!!.cbCheckFoundModel(etrail.toArray())
        stats.extProp.extCb++
        if (isConsistent) {
            // Found solution is approved by external propagator.
            return true
        }

        var hasExternalClause = askExternalClause()

        stats.extProp.extCb++
        stats.extProp.elearnCall++

        while (hasExternalClause) {
            val levelBefore = level
            val assigned = numAssigned
            addExternalClause(0)
            // Upstream declares a NEW local 'bool trail_changed' here, shadowing the
            // outer loop variable (which thus stays false).
            val innerTrailChanged =
                (numAssigned != assigned || level != levelBefore ||
                    propagated < trail.size)
            addedNewClauses = true
            //
            // There are many possible scenarios here:
            // - Learned conflicting clause: return to CDCL loop (conflict true)
            // - Learned conflicting unit clause that after backtrack+BCP leads to
            //   a new complete solution: force the outer loop to check the new
            //   model (trail_changed is true, but (conflict & unsat) is false)
            // - Learned empty clause: return to CDCL loop (unsat true)
            // - Learned a non-conflicting unit clause:
            //   Though it does not invalidate the current solution, the solver
            //   will backtrack to the root level and will repropagate it. The
            //   search will start again (saved phases hopefully make it quick),
            //   but it is needed in order to guarantee that every fixed variable
            //   is properly handled+notified (important for incremental use
            //   cases).
            // - Otherwise: the solution is considered approved and the CDCL-loop
            //   can return with res = 10.
            //
            if (unsat || conflict != null || innerTrailChanged)
                break
            hasExternalClause = askExternalClause()
            stats.extProp.extCb++
            stats.extProp.elearnCall++
        }
        // No more external clause to add.
        if (unsat || conflict != null)
            break
    }

    val c = conflict
    if (!unsat && c != null) {
        val conflictLevel = variable(c.literals[0]).level
        if (conflictLevel != level) {
            backtrack(conflictLevel)
        }
    }

    return conflict == null
}

/*----------------------------------------------------------------------------*/
//
// Notify the external propagator that an observed variable got assigned.
//
internal fun Internal.notifyAssignments() {
    if (!externalProp || externalPropIsLazy || privateSteps)
        return
    val external = external!!

    val endOfTrail = trail.size

    if (notified >= endOfTrail)
        return

    // notify external propagator about new assignments
    val assigned = IntArrayList()

    while (notified < endOfTrail) {
        val ilit = trail[notified++]
        if (!observed(ilit))
            continue

        val elit = externalize(ilit) // TODO: double-check tainting
        check(elit != 0)
        // Fixed variables might get mapped (during compact) to another
        // non-observed but fixed variable.
        // This happens on root level, so notification about their assignment is
        // already done.
        check(external.observed(elit) || fixed(ilit) != 0) { "notify_assignments: not observed" }
        assigned.add(elit)
    }

    external.propagator!!.notifyAssignment(assigned.toArray())
    return
}

/*----------------------------------------------------------------------------*/

internal fun Internal.connectPropagator() {
    if (level != 0)
        backtrack()
}

/*----------------------------------------------------------------------------*/
//
// Notify the external propagator that a new decision level is started.
//
internal fun Internal.notifyDecision() {
    if (!externalProp || externalPropIsLazy || privateSteps)
        return
    external!!.propagator!!.notifyNewDecisionLevel()
}

/*----------------------------------------------------------------------------*/
//
// Notify the external propagator that backtrack to new_level.
//
internal fun Internal.notifyBacktrack(newLevel: Int) {
    if (!externalProp || externalPropIsLazy || privateSteps)
        return
    external!!.propagator!!.notifyBacktrack(newLevel)
}

/*----------------------------------------------------------------------------*/
//
// Ask the external propagator if there is a suggested literal as next
// decision.
//
internal fun Internal.askDecision(): Int {
    if (!externalProp || externalPropIsLazy || privateSteps)
        return 0
    val external = external!!

    check(!unsat) { "ask_decision: unsat" }
    check(conflict == null) { "ask_decision: conflict" }
    notifyAssignments()
    val levelBefore = level
    forcedBacktAllowed = true
    val elit = external.propagator!!.cbDecide()
    forcedBacktAllowed = false
    stats.extProp.extCb++

    if (levelBefore != level) {

        propagate()
        check(!unsat) { "ask_decision: unsat after forced backtrack" }
        check(conflict == null) { "ask_decision: conflict after forced backtrack" }
        notifyAssignments()

        // In case the external propagator forced to backtrack below the
        // pseduo decision levels, we must go back to the CDCL loop instead of
        // making a decision.
        if (level < assumptions.size ||
            (level == assumptions.size && constraint.size != 0)
        ) {
            return 0
        }
    }

    if (elit == 0)
        return 0
    // external propagator proposes decision elit
    check(external.isObserved[abs(elit)]) { "ask_decision: decision not observed" }
    if (!external.isObserved[abs(elit)])
        return 0

    var ilit = external.e2i[abs(elit)]
    if (elit < 0)
        ilit = -ilit

    check(fixed(ilit) != 0 || observed(ilit)) { "ask_decision: decision not observed" }

    if (fixed(ilit) != 0 || value(ilit) != 0) {
        // Proposed decision variable is already assigned, falling back to
        // internal decision.
        return 0
    }

    return ilit
}

/*----------------------------------------------------------------------------*/
//
// Check if the clause is a forgettable clause coming from the external
// propagator.
//
internal fun Internal.isExternalForgettable(id: Long): Boolean {
    check(opts.check != 0) { "is_external_forgettable: without check" }
    return external!!.forgettableOriginal.containsKey(id)
}

/*----------------------------------------------------------------------------*/
//
// When an external forgettable clause is deleted, it is marked in the
// 'forgettable_original' hash, so that the internal model checking can
// ignore it.
//
internal fun Internal.markGarbageExternalForgettable(id: Long) {
    check(opts.check != 0) { "mark_garbage_external_forgettable: without check" }
    check(isExternalForgettable(id)) { "mark_garbage_external_forgettable: not forgettable" }

    // Mark as removed by flipping the first flag to false.
    external!!.forgettableOriginal.getValue(id)[0] = 0
}

/*----------------------------------------------------------------------------*/
//
// Check that the literals in the clause are properly ordered. Used only
// internally for debug purposes.
//
// (Its only call, in clause.cpp, is '#ifndef NDEBUG': never called in the release build.)
internal fun Internal.checkWatchedLiteralInvariants() {
    // '#ifndef NDEBUG' upstream (watch value order 'v0 >= v1'): not in release.
    if (value(clause[0]) > 0) {
        if (value(clause[1]) > 0) { // Case 1: Both literals are satisfied
            // They are ordered by lower to higher decision level
            check(variable(clause[0]).level <= variable(clause[1]).level) { "watch invariant case 1" }

            // Every other literal of the clause is either
            //    - satisfied at higher level
            //    - unassigned
            //    - falsified
            for (i in 2 until clause.size)
                check(
                    value(clause[i]) <= 0 ||
                        (variable(clause[1]).level <= variable(clause[i]).level)
                ) { "watch invariant case 1" }
        } else if (value(clause[1]) ==
            0
        ) { // Case 2: First satisfied, next unassigned

            // Every other literal of the clause is either
            //    - unassigned
            //    - falsified
            for (i in 2 until clause.size)
                check(value(clause[i]) <= 0) { "watch invariant case 2" }
        } else { // Case 3: First satisfied, next falsified -> could have been a
            // reason of a previous propagation
            // Every other literal of the clause is falsified but at a lower
            // decision level
            for (i in 2 until clause.size)
                check(
                    value(clause[i]) < 0 &&
                        (variable(clause[1]).level >= variable(clause[i]).level)
                ) { "watch invariant case 3" }
        }
    } else if (value(clause[0]) == 0) {
        if (value(clause[1]) == 0) { // Case 4: Both literals are unassigned

            // Every other literal of the clause is either
            //    - unassigned
            //    - falsified
            for (i in 2 until clause.size)
                check(value(clause[i]) <= 0) { "watch invariant case 4" }
        } else { // Case 5: First unassigned, next falsified -> PROPAGATE
            // Every other literal of the clause is falsified but at a lower
            // decision level
            for (i in 2 until clause.size)
                check(
                    value(clause[i]) < 0 &&
                        (variable(clause[1]).level >= variable(clause[i]).level)
                ) { "watch invariant case 5" }
        }
    } else {
        check(
            value(clause[0]) < 0 &&
                value(clause[1]) < 0
        ) { "watch invariant case 6" } // Case 6: Both literals are falsified

        // They are ordered by higher to lower decision level
        check(variable(clause[0]).level >= variable(clause[1]).level) { "watch invariant case 6" }

        // Every other literal of the clause is falsified, but at a lower level
        for (i in 2 until clause.size)
            check(
                value(clause[i]) < 0 &&
                    (variable(clause[1]).level >= variable(clause[i]).level)
            ) { "watch invariant case 6" }
    }
}

// 'get_merged_literals' / 'get_all_fixed_literals': '#ifndef NDEBUG' debugging helpers for
// mobical upstream, not in release, not ported.

