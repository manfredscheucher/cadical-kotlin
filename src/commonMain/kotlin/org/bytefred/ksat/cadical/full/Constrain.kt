package org.bytefred.ksat.cadical.full

/*
 * constrain.cpp: the constraint clause of the incremental API (literals are collected
 * by 'constrain (lit)' and the clause is simplified on the terminating zero).
 */

internal fun Internal.constrain(lit: Int) {
    if (lit != 0)
        constraint.add(lit)
    else {
        if (level != 0)
            backtrack()
        var satisfiedConstraint = false
        val end = constraint.size
        var i = 0
        for (j in 0 until end) {
            val lj = constraint[j]
            var tmp = marked(lj)
            if (tmp > 0) {
                // removing duplicated literal from constraint
            } else if (tmp < 0) {
                // tautological since both -lj and lj occur in constraint
                satisfiedConstraint = true
                break
            } else {
                tmp = value(lj)
                if (tmp < 0) {
                    // removing falsified literal from constraint clause
                } else if (tmp > 0) {
                    // satisfied constraint with literal lj
                    satisfiedConstraint = true
                    break
                } else {
                    constraint[i++] = lj
                    mark(lj)
                }
            }
        }
        constraint.resize(i)
        for (k in 0 until constraint.size)
            unmark(constraint[k])
        if (satisfiedConstraint)
            constraint.clear()
        else if (constraint.isEmpty()) {
            unsatConstraint = true
            if (conflictId == 0L)
                markedFailed = false // allow to trigger failing ()
        } else
            for (k in 0 until constraint.size)
                freeze(constraint[k])
    }
}

internal fun Internal.failedConstraint(): Boolean = unsatConstraint

internal fun Internal.resetConstraint() {
    for (k in 0 until constraint.size)
        melt(constraint[k])
    constraint.clear()
    unsatConstraint = false
    markedFailed = true
}
