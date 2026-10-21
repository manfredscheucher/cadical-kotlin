package org.bytefred.ksat.cadical.full

import kotlin.math.ln

/*
 * reduce.cpp: reducing (and flushing) redundant learned clauses.
 *
 * Mapping notes: 'goto DONE' in 'reduce' -> a labeled 'run' block. The shadow trace line
 * 'REDUCE' / 'FLUSH' (trace.patch) is emitted right after 'flushing ()'.
 */

/*------------------------------------------------------------------------*/

// Once in a while we reduce, e.g., we remove learned clauses which are
// supposed to be less useful in the future.  This is done in increasing
// intervals, which has the effect of allowing more and more learned clause
// to be kept for a longer period.  The number of learned clauses kept
// in memory corresponds to an upper bound on the 'space' of a resolution
// proof needed to refute a formula in proof complexity sense.

internal fun Internal.reducing(): Boolean {
    if (opts.reduce == 0) return false
    if (stats.current.redundant == 0L) return false
    return stats.conflicts >= lim.reduce
}

/*------------------------------------------------------------------------*/

// Even less regularly we are flushing all redundant clauses.

internal fun Internal.flushing(): Boolean {
    if (opts.flush == 0) return false
    return stats.conflicts >= lim.flush
}

/*------------------------------------------------------------------------*/

internal fun Internal.markClausesToBeFlushed() {
    for (c in clauses) {
        if (!c.redundant) continue // keep irredundant
        if (c.garbage) continue // already marked as garbage
        if (c.reason) continue // need to keep reasons
        val used = c.used
        if (used != 0) c.used--
        if (used != 0) continue // but keep recently used clauses
        markGarbage(c) // flush unused clauses
        if (c.hyper) stats.flush.hyper++
        else stats.flush.learned++
    }
    // No change to 'lim.kept{size,glue}'.
}

/*------------------------------------------------------------------------*/

// Clauses of larger glue or larger size are considered less useful.
//
// We also follow the observations made by the Glucose team in their
// IJCAI'09 paper and keep all low glue clauses limited by
// 'options.keepglue' (typically '2').
//
// In earlier versions we pre-computed a 64-bit sort key per clause and
// wrapped a pointer to the clause and the 64-bit sort key into a separate
// data structure for sorting.  This was probably faster but awkward and
// so we moved back to a simpler scheme which also uses 'stable_sort'
// instead of 'rsort' below.  Sorting here is not a hot-spot anyhow.

private class ReduceLessUseful : Less<Clause> {
    override fun less(a: Clause, b: Clause): Boolean {
        val c = a
        val d = b
        if (c.glue > d.glue) return true
        if (c.glue < d.glue) return false
        return c.size > d.size
    }
}

// This function implements the important reduction policy. It determines
// which redundant clauses are considered not useful and thus will be
// collected in a subsequent garbage collection phase.

internal fun Internal.markUselessRedundantClausesAsGarbage() {

    // We use a separate stack for sorting candidates for removal.  This uses
    // (slightly) more memory but has the advantage to keep the relative order
    // in 'clauses' intact, which actually due to using stable sorting goes
    // into the candidate selection (more recently learned clauses are kept if
    // they otherwise have the same glue and size).

    val stack = ArrayList<Clause>()

    stack.ensureCapacity(stats.current.redundant.toInt())

    for (c in clauses) {
        if (!c.redundant) continue // Keep irredundant.
        if (c.garbage) continue // Skip already marked.
        if (c.reason) continue // Need to keep reasons.
        val used = c.used
        if (used != 0) c.used--
        if (c.hyper) { // Hyper binary and ternary resolvents
            check(c.size <= 3) // are only kept for one reduce round
            if (used == 0) markGarbage(c) // (even if 'c->keep' is true) unless
            continue //  used recently.
        }
        if (used != 0) continue // Do keep recently used clauses.
        if (c.keep) continue // Forced to keep (see above).

        stack.add(c)
    }

    stableSort(stack, ReduceLessUseful())

    var target = (1e-2 * opts.reducetarget * stack.size).toLong()

    // This is defensive code, which I usually consider a bug, but here I am
    // just not sure that using floating points in the line above is precise
    // in all situations and instead of figuring that out, I just use this.
    //
    if (target > stack.size) target = stack.size.toLong()

    // PHASE: reducing target clauses

    var i = 0
    val t = i + target.toInt()
    while (i != t) {
        val c = stack[i++]
        // LOG: marking useless to be collected
        markGarbage(c)
        stats.reduced++
    }

    lim.keptglue = 0
    lim.keptsize = lim.keptglue

    val end = stack.size
    i = t
    while (i != end) {
        val c = stack[i]
        // LOG: keeping
        if (c.size > lim.keptsize) lim.keptsize = c.size
        if (c.glue > lim.keptglue) lim.keptglue = c.glue
        i++
    }

    stack.clear()

    // PHASE: maximum kept size and glue
}

/*------------------------------------------------------------------------*/

// If chronological backtracking produces out-of-order assigned units, then
// it is necessary to completely propagate them at the root level in order
// to derive all implied units.  Otherwise the blocking literals in
// 'flush_watches' are messed up and assertion 'FW1' fails.

internal fun Internal.propagateOutOfOrderUnits(): Boolean {
    if (level == 0) return true
    var oou = 0
    var i = control[1].trail
    while (oou == 0 && i < trail.size) {
        val lit = trail[i]
        check(value(lit) > 0)
        if (variable(lit).level != 0) {
            i++
            continue
        }
        // LOG: found out-of-order assigned unit
        oou = lit
        i++
    }
    if (oou == 0) return true
    check(opts.chrono != 0 || externalProp)
    backtrack(0)
    if (propagate()) return true
    learnEmptyClause()
    return false
}

/*------------------------------------------------------------------------*/

internal fun Internal.reduce() {
    stats.reductions++
    // report ('.', 1)

    val flush = flushing()
    trace?.line(if (flush) "FLUSH" else "REDUCE")
    if (flush) stats.flush.count++

    run done@{
        if (!propagateOutOfOrderUnits()) return@done // goto DONE

        markSatisfiedClausesAsGarbage()
        protectReasons()
        if (flush) markClausesToBeFlushed()
        else markUselessRedundantClausesAsGarbage()
        garbageCollection()

        run {
            var delta: Long = opts.reduceint * (stats.reductions + 1)
            if (irredundant() > 1e5) {
                delta = (delta * (ln(irredundant() / 1e4) / ln(10.0))).toLong()
                if (delta < 1) delta = 1
            }
            lim.reduce = stats.conflicts + delta
            // PHASE: new reduce limit
        }

        if (flush) {
            // PHASE: new flush increment
            inc.flush *= opts.flushfactor
            lim.flush = stats.conflicts + inc.flush
            // PHASE: new flush limit
        }

        last.reduce.conflicts = stats.conflicts
    }

    // DONE:

    // report (flush ? 'f' : '-')
}
