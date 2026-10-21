package org.bytefred.ksat.cadical.full

/*
 * lucky.cpp: lucky phases, i.e., trying simple assignments (all false, all true, forward /
 * backward in variable order, horn like) before the CDCL search.
 */

// It turns out that even in the competition there are formulas which are
// easy to satisfy by either setting all variables to the same truth value
// or by assigning variables to the same value and propagating it.  In the
// latter situation this can be done either in the order of all variables
// (forward or backward) or in the order of all clauses.  These lucky
// assignments can be tested initially in a kind of pre-solving step.

// This function factors out clean up code common among the 'lucky'
// functions for backtracking and resetting a potential conflict.  One could
// also use exceptions here, but there are two different reasons for
// aborting early.  The first kind of aborting is due to asynchronous
// termination and the second kind due to a situation in which it is clear
// that a particular function will not be successful (for instance a
// completely negative clause is found).  The latter situation returns zero
// and will just abort the particular lucky function, while the former will
// abort all (by returning '-1').

internal fun Internal.unlucky(res: Int): Int {
    if (level > 0)
        backtrack()
    if (conflict != null)
        conflict = null
    return res
}

internal fun Internal.triviallyFalseSatisfiable(): Int {
    check(level == 0) { "lucky: not at root level" }
    check(assumptions.isEmpty()) { "lucky: assumptions" }
    for (c in clauses) {
        if (terminatedAsynchronously(100))
            return unlucky(-1)
        if (c.garbage)
            continue
        if (c.redundant)
            continue
        var satisfied = false
        var foundNegativeLiteral = false
        for (k in 0 until c.size) {
            val lit = c.literals[k]
            val tmp = value(lit)
            if (tmp > 0) {
                satisfied = true
                break
            }
            if (tmp < 0)
                continue
            if (lit > 0)
                continue
            foundNegativeLiteral = true
            break
        }
        if (satisfied || foundNegativeLiteral)
            continue
        return unlucky(0)
    }
    for (idx in vars) {
        if (terminatedAsynchronously(10))
            return unlucky(-1)
        if (value(idx) != 0)
            continue
        searchAssumeDecision(-idx)
        if (propagate())
            continue
        check(level > 0) { "lucky: conflict at root level" }
        return unlucky(0)
    }
    stats.lucky.constant.zero++
    return 10
}

internal fun Internal.triviallyTrueSatisfiable(): Int {
    check(level == 0) { "lucky: not at root level" }
    check(assumptions.isEmpty()) { "lucky: assumptions" }
    for (c in clauses) {
        if (terminatedAsynchronously(100))
            return unlucky(-1)
        if (c.garbage)
            continue
        if (c.redundant)
            continue
        var satisfied = false
        var foundPositiveLiteral = false
        for (k in 0 until c.size) {
            val lit = c.literals[k]
            val tmp = value(lit)
            if (tmp > 0) {
                satisfied = true
                break
            }
            if (tmp < 0)
                continue
            if (lit < 0)
                continue
            foundPositiveLiteral = true
            break
        }
        if (satisfied || foundPositiveLiteral)
            continue
        return unlucky(0)
    }
    for (idx in vars) {
        if (terminatedAsynchronously(10))
            return unlucky(-1)
        if (value(idx) != 0)
            continue
        searchAssumeDecision(idx)
        if (propagate())
            continue
        check(level > 0) { "lucky: conflict at root level" }
        return unlucky(0)
    }
    stats.lucky.constant.one++
    return 10
}

/*------------------------------------------------------------------------*/

internal fun Internal.forwardFalseSatisfiable(): Int {
    check(!unsat) { "lucky: unsat" }
    check(level == 0) { "lucky: not at root level" }
    check(assumptions.isEmpty()) { "lucky: assumptions" }
    for (idx in vars) {
        if (terminatedAsynchronously(100))
            return unlucky(-1)
        if (value(idx) != 0)
            continue
        searchAssumeDecision(-idx)
        if (!propagate())
            return unlucky(0)
    }
    check(satisfied()) { "lucky: not satisfied" }
    stats.lucky.forward.zero++
    return 10
}

internal fun Internal.forwardTrueSatisfiable(): Int {
    check(!unsat) { "lucky: unsat" }
    check(level == 0) { "lucky: not at root level" }
    check(assumptions.isEmpty()) { "lucky: assumptions" }
    for (idx in vars) {
        if (terminatedAsynchronously(10))
            return unlucky(-1)
        if (value(idx) != 0)
            continue
        searchAssumeDecision(idx)
        if (!propagate())
            return unlucky(0)
    }
    check(satisfied()) { "lucky: not satisfied" }
    stats.lucky.forward.one++
    return 10
}

/*------------------------------------------------------------------------*/

internal fun Internal.backwardFalseSatisfiable(): Int {
    check(!unsat) { "lucky: unsat" }
    check(level == 0) { "lucky: not at root level" }
    check(assumptions.isEmpty()) { "lucky: assumptions" }
    for (idx in maxVar downTo 1) {
        if (terminatedAsynchronously(10))
            return unlucky(-1)
        if (value(idx) != 0)
            continue
        searchAssumeDecision(-idx)
        if (!propagate())
            return unlucky(0)
    }
    check(satisfied()) { "lucky: not satisfied" }
    stats.lucky.backward.zero++
    return 10
}

internal fun Internal.backwardTrueSatisfiable(): Int {
    check(!unsat) { "lucky: unsat" }
    check(level == 0) { "lucky: not at root level" }
    check(assumptions.isEmpty()) { "lucky: assumptions" }
    for (idx in maxVar downTo 1) {
        if (terminatedAsynchronously(10))
            return unlucky(-1)
        if (value(idx) != 0)
            continue
        searchAssumeDecision(idx)
        if (!propagate())
            return unlucky(0)
    }
    check(satisfied()) { "lucky: not satisfied" }
    stats.lucky.backward.one++
    return 10
}

/*------------------------------------------------------------------------*/

// The following two functions test if the formula is a satisfiable horn
// formula.  Actually the test is slightly more general.  It goes over all
// clauses and assigns the first positive literal to true and propagates.
// Already satisfied clauses are of course skipped.  A reverse function
// is not implemented yet.

internal fun Internal.positiveHornSatisfiable(): Int {
    check(level == 0) { "lucky: not at root level" }
    check(assumptions.isEmpty()) { "lucky: assumptions" }
    for (c in clauses) {
        if (terminatedAsynchronously(10))
            return unlucky(-1)
        if (c.garbage)
            continue
        if (c.redundant)
            continue
        var positiveLiteral = 0
        var satisfied = false
        for (k in 0 until c.size) {
            val lit = c.literals[k]
            val tmp = value(lit)
            if (tmp > 0) {
                satisfied = true
                break
            }
            if (tmp < 0)
                continue
            if (lit < 0)
                continue
            positiveLiteral = lit
            break
        }
        if (satisfied)
            continue
        if (positiveLiteral == 0) {
            return unlucky(0)
        }
        check(positiveLiteral > 0) { "lucky: horn literal sign" }
        searchAssumeDecision(positiveLiteral)
        if (propagate())
            continue
        return unlucky(0)
    }
    for (idx in vars) {
        if (terminatedAsynchronously(10))
            return unlucky(-1)
        if (value(idx) != 0)
            continue
        searchAssumeDecision(-idx)
        if (propagate())
            continue
        return unlucky(0)
    }
    check(conflict == null) { "lucky: conflict" }
    check(satisfied()) { "lucky: not satisfied" }
    stats.lucky.horn.positive++
    return 10
}

internal fun Internal.negativeHornSatisfiable(): Int {
    check(level == 0) { "lucky: not at root level" }
    check(assumptions.isEmpty()) { "lucky: assumptions" }
    for (c in clauses) {
        if (terminatedAsynchronously(10))
            return unlucky(-1)
        if (c.garbage)
            continue
        if (c.redundant)
            continue
        var negativeLiteral = 0
        var satisfied = false
        for (k in 0 until c.size) {
            val lit = c.literals[k]
            val tmp = value(lit)
            if (tmp > 0) {
                satisfied = true
                break
            }
            if (tmp < 0)
                continue
            if (lit > 0)
                continue
            negativeLiteral = lit
            break
        }
        if (satisfied)
            continue
        if (negativeLiteral == 0) {
            if (level > 0)
                backtrack()
            return unlucky(0)
        }
        check(negativeLiteral < 0) { "lucky: horn literal sign" }
        searchAssumeDecision(negativeLiteral)
        if (propagate())
            continue
        return unlucky(0)
    }
    for (idx in vars) {
        if (terminatedAsynchronously(10))
            return unlucky(-1)
        if (value(idx) != 0)
            continue
        searchAssumeDecision(idx)
        if (propagate())
            continue
        return unlucky(0)
    }
    check(conflict == null) { "lucky: conflict" }
    check(satisfied()) { "lucky: not satisfied" }
    stats.lucky.horn.negative++
    return 10
}

/*------------------------------------------------------------------------*/

internal fun Internal.luckyPhases(): Int = tracePhase("lucky") {
    check(level == 0) { "lucky: not at root level" }
    requireMode(Internal.SEARCH)
    if (opts.lucky == 0)
        return@tracePhase 0

    // TODO: Some of the lucky assignments can also be found if there are
    // assumptions, but this is not completely implemented nor tested yet.
    // Nothing done for constraint either.
    // External propagator assumes a CDCL loop, so lucky is not tried here.
    if (!assumptions.isEmpty() || !constraint.isEmpty() || externalProp)
        return@tracePhase 0

    check(!searchingLuckyPhases) { "lucky: nested" }
    searchingLuckyPhases = true
    stats.lucky.tried++
    var res = triviallyFalseSatisfiable()
    if (res == 0)
        res = triviallyTrueSatisfiable()
    if (res == 0)
        res = forwardTrueSatisfiable()
    if (res == 0)
        res = forwardFalseSatisfiable()
    if (res == 0)
        res = backwardFalseSatisfiable()
    if (res == 0)
        res = backwardTrueSatisfiable()
    if (res == 0)
        res = positiveHornSatisfiable()
    if (res == 0)
        res = negativeHornSatisfiable()
    if (res < 0) {
        check(terminationForced) { "lucky: aborted without termination" }
        res = 0
    }
    if (res == 10)
        stats.lucky.succeeded++
    // report ('l', !res) dropped (message output)
    check(searchingLuckyPhases) { "lucky: flag lost" }
    searchingLuckyPhases = false

    res
}
