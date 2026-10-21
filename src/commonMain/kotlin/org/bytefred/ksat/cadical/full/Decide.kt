package org.bytefred.ksat.cadical.full

import kotlin.math.abs

/*
 * decide.cpp: picking the next decision variable and its phase, assumption and constraint
 * decisions.
 */

// This function determines the next decision variable on the queue, without
// actually removing it from the decision queue, e.g., calling it multiple
// times without any assignment will return the same result.  This is of
// course used below in 'decide' but also in 'reuse_trail' to determine the
// largest decision level to backtrack to during 'restart' without changing
// the assigned variables (if 'opts.restartreusetrail' is non-zero).

internal fun Internal.nextDecisionVariableOnQueue(): Int {
    var searched = 0L
    var res = queue.unassigned
    while (value(res) != 0) {
        res = link(res).prev
        searched++
    }
    if (searched != 0L) {
        stats.searched += searched
        updateQueueUnassigned(res)
    }
    return res
}

// This function determines the best decision with respect to score.
//
internal fun Internal.nextDecisionVariableWithBestScore(): Int {
    var res: Int
    while (true) {
        res = scores.front()
        if (value(res) == 0) break
        scores.popFront()
    }
    return res
}

internal fun Internal.nextDecisionVariable(): Int {
    if (useScores()) return nextDecisionVariableWithBestScore()
    else return nextDecisionVariableOnQueue()
}

/*------------------------------------------------------------------------*/

// Implements phase saving as well using a target phase during
// stabilization unless decision phase is forced to the initial value
// of a phase is forced through the 'phase' option.

internal fun Internal.decidePhase(idx: Int, target: Boolean): Int {
    val initialPhase = if (opts.phase != 0) 1 else -1
    var phase = 0
    if (forceSavedPhase) phase = phases.saved[idx].toInt()
    if (phase == 0) phase = phases.forced[idx].toInt() // swapped with opts.forcephase case!
    if (phase == 0 && opts.forcephase != 0) phase = initialPhase
    if (phase == 0 && target) phase = phases.target[idx].toInt()
    if (phase == 0) phase = phases.saved[idx].toInt()

    // The following should not be necessary and in some version we had even
    // a hard 'COVER' assertion here to check for this.   Unfortunately it
    // triggered for some users and we could not get to the root cause of
    // 'phase' still not being set here.  The logic for phase and target
    // saving is pretty complex, particularly in combination with local
    // search, and to avoid running in such an issue in the future again, we
    // now use this 'defensive' code here, even though such defensive code is
    // considered bad programming practice.
    //
    if (phase == 0) phase = initialPhase

    return phase * idx
}

// The likely phase of an variable used in 'collect' for optimizing
// co-location of clauses likely accessed together during search.

internal fun Internal.likelyPhase(idx: Int): Int = decidePhase(idx, false)

/*------------------------------------------------------------------------*/

// adds new level to control and trail
//
internal fun Internal.newTrailLevel(lit: Int) {
    level++
    if (lit == 0) // LSTRACE
        trace?.line("DECIDE 0")
    control.add(Level(lit, trail.size))
}

/*------------------------------------------------------------------------*/

internal fun Internal.satisfied(): Boolean {
    if (level < assumptions.size + (if (constraint.size != 0) 1 else 0)) return false
    if (numAssigned < maxVar) return false
    check(numAssigned == maxVar) { "more assigned than variables" }
    if (propagated < trail.size) return false
    val assigned = numAssigned
    return (assigned == maxVar)
}

internal fun Internal.betterDecision(lit: Int, other: Int): Boolean {
    val litIdx = abs(lit)
    val otherIdx = abs(other)
    if (stable) return stab[litIdx] > stab[otherIdx]
    else return btab[litIdx] > btab[otherIdx]
}

// Search for the next decision and assign it to the saved phase.  Requires
// that not all variables are assigned.

internal fun Internal.decide(): Int {
    check(!satisfied()) { "decide on satisfied formula" }
    var res = 0
    if (level < assumptions.size) {
        val lit = assumptions[level]
        check(assumed(lit)) { "assumption not marked as assumed" }
        val tmp = value(lit)
        if (tmp < 0) {
            // assumption falsified
            res = 20
        } else if (tmp > 0) {
            // assumption already satisfied
            newTrailLevel(0)
            // added pseudo decision level
            notifyDecision()
        } else {
            // deciding assumption
            searchAssumeDecision(lit)
        }
    } else if (level == assumptions.size && constraint.size != 0) {

        var satisfiedLit = 0 // The literal satisfying the constrain.
        var unassignedLit = 0 // Highest score unassigned literal.
        var previousLit = 0 // Move satisfied literals to the front.

        val sizeConstraint = constraint.size

        var sum = 0 // unsigned checksum (NDEBUG-only upstream)
        for (k in 0 until constraint.size) sum += constraint[k]
        for (i in 0 until sizeConstraint) {

            // Get literal and move 'constraint[i] = constraint[i-1]'.

            val lit = constraint[i]
            constraint[i] = previousLit
            previousLit = lit

            val tmp = value(lit)
            if (tmp < 0) {
                // constraint literal falsified
                continue
            }

            if (tmp > 0) {
                // constraint literal satisfied
                satisfiedLit = lit
                break
            }

            check(tmp == 0)
            // constraint literal unassigned

            if (unassignedLit == 0 || betterDecision(lit, unassignedLit)) unassignedLit = lit
        }

        if (satisfiedLit != 0) {

            constraint[0] = satisfiedLit // Move satisfied to the front.

            // literal satisfies constraint and is implied by assumptions

            newTrailLevel(0)
            // added pseudo decision level for constraint
            notifyDecision()

        } else {

            // Just move all the literals back.  If we found an unsatisfied
            // literal then it will be satisfied (most likely) at the next
            // decision and moved then to the first position.

            if (sizeConstraint != 0) {

                var i = 0
                while (i + 1 != sizeConstraint) {
                    constraint[i] = constraint[i + 1]
                    i++
                }

                constraint[sizeConstraint - 1] = previousLit
            }

            if (unassignedLit != 0) {

                // deciding 'unassignedLit' to satisfy constraint
                searchAssumeDecision(unassignedLit)

            } else {

                // failing constraint
                unsatConstraint = true
                res = 20
            }
        }

        for (k in 0 until constraint.size) sum -= constraint[k]
        check(sum == 0) { "constraint checksum changed" } // Checksum of literal should not change!

    } else {

        var decision = askDecision()
        if (level < assumptions.size || (level == assumptions.size && constraint.size != 0)) {
            // Forced backtrack below pseudo decision levels.
            // So one of the two branches above will handle it.
            res = decide() // STARTS and STOPS profiling
        } else {
            stats.decisions++
            if (decision == 0) {
                val idx = nextDecisionVariable()
                val target = (opts.target > 1 || (stable && opts.target != 0))
                decision = decidePhase(idx, target)
            }
            searchAssumeDecision(decision)
        }
    }
    if (res != 0) markedFailed = false
    return res
}
