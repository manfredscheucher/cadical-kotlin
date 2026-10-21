package org.bytefred.ksat.cadical.full

/*
 * backtrack.cpp: unassigning literals, saving target / best phases, backtracking.
 */

// The global assignment stack can only be (partially) reset through
// 'backtrack' which is the only function using 'unassign' (inlined and thus
// local to this file).  It turns out that 'unassign' does not need a
// specialization for 'probe' nor 'vivify' and thus it is shared.

internal fun Internal.unassign(lit: Int) {
    check(value(lit) > 0) { "unassign of non-true literal" }
    setVal(lit, 0)

    val idx = vidx(lit)
    numAssigned--

    // In the standard EVSIDS variable decision heuristic of MiniSAT, we need
    // to push variables which become unassigned back to the heap.
    //
    if (!scores.contains(idx)) scores.pushBack(idx)

    // For VMTF we need to update the 'queue.unassigned' pointer in case this
    // variable sits after the variable to which 'queue.unassigned' currently
    // points.  See our SAT'15 paper for more details on this aspect.
    //
    if (queue.bumped < btab[idx]) updateQueueUnassigned(idx)
}

/*------------------------------------------------------------------------*/

// Update the current target maximum assignment and also the very best
// assignment.  Whether a trail produces a conflict is determined during
// propagation.  Thus that all functions in the 'search' loop after
// propagation can assume that 'no_conflict_until' is valid.  If a conflict
// is found then the trail before the last decision is used (see the end of
// 'propagate').  During backtracking we can then save this largest
// propagation conflict free assignment.  It is saved as both 'target'
// assignment for picking decisions in 'stable' mode and if it is the
// largest ever such assignment also as 'best' assignment. This 'best'
// assignment can then be used in future stable decisions after the next
// 'rephase_best' overwrites saved phases with it.

internal fun Internal.updateTargetAndBest() {

    val reset = (rephased != '\u0000' && stats.conflicts > last.rephase.conflicts)

    if (reset) {
        targetAssigned = 0
        if (rephased == 'B') bestAssigned = 0 // update it again
    }

    if (noConflictUntil > targetAssigned) {
        copyPhases(phases.target)
        targetAssigned = noConflictUntil
    }

    if (noConflictUntil > bestAssigned) {
        copyPhases(phases.best)
        bestAssigned = noConflictUntil
    }

    if (reset) {
        // report (rephased): message output, not ported
        rephased = '\u0000'
    }
}

/*------------------------------------------------------------------------*/

internal fun Internal.backtrack(targetLevel: Int = 0) {
    val newLevel = targetLevel

    check(newLevel <= level) { "backtrack above current level" }
    if (newLevel == level) return
    trace?.line("BACKTRACK $newLevel") // LSTRACE

    stats.backtracks++
    updateTargetAndBest()

    check(numAssigned == trail.size) { "num_assigned out of sync" }

    val assigned = control[newLevel + 1].trail

    val endOfTrail = trail.size
    var i = assigned
    var j = i

    var reassigned = 0

    notifyBacktrack(newLevel)
    if (externalProp && !externalPropIsLazy && !privateSteps && notified > assigned) {
        notified = assigned
    }

    while (i < endOfTrail) {
        val lit = trail[i++]
        val v = variable(lit)
        if (v.level > newLevel) {
            unassign(lit)
        } else {
            // This is the essence of the SAT'18 paper on chronological
            // backtracking.  It is possible to just keep out-of-order assigned
            // literals on the trail without breaking the solver (after some
            // modifications to 'analyze' - see 'opts.chrono' guarded code there).
            check(opts.chrono != 0 || externalProp || didExternalProp) { "out-of-order literal without chrono" }
            trail[j] = lit
            v.trail = j++
            reassigned++
        }
    }
    trail.resize(j)

    if (propagated > assigned) propagated = assigned
    if (propagated2 > assigned) propagated2 = assigned
    if (noConflictUntil > assigned) noConflictUntil = assigned

    propergated = 0 // Always go back to root-level.

    check(notified <= assigned + reassigned) { "notified beyond trail" }
    if (reassigned != 0) {
        notifyAssignments()
    }

    control.shrinkTo(newLevel + 1)
    level = newLevel
    if (taintedLiteral != 0) {
        check(opts.ilb != 0) { "tainted literal without ilb" }
        if (value(taintedLiteral) == 0) {
            taintedLiteral = 0
        }
    }
    check(numAssigned == trail.size) { "num_assigned out of sync" }
}
