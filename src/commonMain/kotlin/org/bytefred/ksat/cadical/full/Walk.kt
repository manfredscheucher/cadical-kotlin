package org.bytefred.ksat.cadical.full

import kotlin.math.abs

/*
 * walk.cpp: random walk local search based on 'ProbSAT' ideas.
 *
 * Mapping notes:
 *  - 'struct Walker' -> class [Walker] (private to this file in spirit; 'internal' because
 *    the cross-file signatures in SIGNATURES.md take it as a parameter).
 *  - 'vector<double> table, scores' -> ArrayList<Double>; 'vector<Clause *> broken' ->
 *    ArrayList<Clause>.
 *  - 'unsigned' break values -> Int holding the bit pattern (compared with 'toUInt ()').
 *  - No libm call ('pow', 'log', 'exp') is used here: the score table is built by repeated
 *    multiplication, exactly as upstream.
 *  - 'int64_t *= double' ('limit *= 1e-3 * opts.walkreleff') -> convert to double, multiply,
 *    truncate back with 'toLong ()' (the C conversion; the value is always in range).
 *  - LOG / PHASE / VERBOSE messages are dropped (see PORTING.md).
 */

/*------------------------------------------------------------------------*/

// Random walk local search based on 'ProbSAT' ideas.

internal class Walker(internal: Internal, size: Double, l: Long) {

    val random: Random // local random number generator
    var propagations: Long // number of propagations
    var limit: Long // limit on number of propagations
    val broken = ArrayList<Clause>() // currently unsatisfied clauses
    var epsilon: Double // smallest considered score
    val table = ArrayList<Double>() // break value to score table
    val scores = ArrayList<Double>() // scores of candidate literals

    // Initialize the data structures for one local search round.
    init {
        random = Random(internal.opts.seed.toULong()) // global random seed
        propagations = 0
        limit = l
        random += internal.stats.walk.count.toULong() // different seed every time

        // This is the magic constant in ProbSAT (also called 'CB'), which we pick
        // according to the average size every second invocation and otherwise
        // just the default '2.0', which turns into the base '0.5'.
        //
        val useSizeBasedCb = (internal.stats.walk.count and 1L) != 0L
        val cb = if (useSizeBasedCb) fitcbval(size) else 2.0
        check(cb != 0.0) { "walk: zero CB value" }
        val base = 1 / cb // scores are 'base^0,base^1,base^2,...

        // for (epsilon = next; next; next = epsilon * base)
        //   table.push_back (epsilon = next);
        var next = 1.0
        epsilon = next
        while (next != 0.0) {
            epsilon = next
            table.add(epsilon)
            next = epsilon * base
        }
    }

    // The scores are tabulated for faster computation (to avoid 'pow').

    fun score(i: Int): Double {
        val res = if (i.toUInt() < table.size.toUInt()) table[i] else epsilon
        return res
    }
}

// These are in essence the CB values from Adrian Balint's thesis.  They
// denote the inverse 'cb' of the base 'b' of the (probability) weight
// 'b^-i' for picking a literal with the break value 'i' (first column is
// the 'size', second the 'CB' value).

private val cbvals = arrayOf(
    doubleArrayOf(0.0, 2.00), doubleArrayOf(3.0, 2.50), doubleArrayOf(4.0, 2.85), doubleArrayOf(5.0, 3.70),
    doubleArrayOf(6.0, 5.10), doubleArrayOf(7.0, 7.40), // Adrian has '5.4', but '7.4' looks better.
)

private val ncbvals = cbvals.size

// We interpolate the CB values for uniform random SAT formula to the non
// integer situation of average clause size by piecewise linear functions.
//
//   y2 - y1
//   ------- * (x - x1) + y1
//   x2 - x1
//
// where 'x' is the average size of clauses and 'y' the CB value.

private fun fitcbval(size: Double): Double {
    var i = 0
    while (i + 2 < ncbvals &&
        (cbvals[i][0] > size || cbvals[i + 1][0] < size)
    ) i++
    val x2 = cbvals[i + 1][0]
    val x1 = cbvals[i][0]
    val y2 = cbvals[i + 1][1]
    val y1 = cbvals[i][1]
    val dx = x2 - x1
    val dy = y2 - y1
    check(dx != 0.0) { "fitcbval: zero dx" }
    val res = dy * (size - x1) / dx + y1
    check(res > 0) { "fitcbval: non-positive CB value" }
    return res
}

/*------------------------------------------------------------------------*/

internal fun Internal.walkPickClause(walker: Walker): Clause {
    requireMode(Internal.WALK)
    check(walker.broken.isNotEmpty()) { "walk: no broken clause to pick" }
    var size = walker.broken.size.toLong()
    if (size > Int.MAX_VALUE) size = Int.MAX_VALUE.toLong()
    val pos = walker.random.pickInt(0, (size - 1).toInt())
    val res = walker.broken[pos]
    return res
}

/*------------------------------------------------------------------------*/

// Compute the number of clauses which would be become unsatisfied if 'lit'
// is flipped and set to false.  This is called the 'break-count' of 'lit'.

internal fun Internal.walkBreakValue(lit: Int): Int {

    requireMode(Internal.WALK)
    check(value(lit) > 0) { "walk: break value of non-true literal" }

    var res = 0 // The computed break-count of 'lit' (unsigned).

    val ws = watches(lit)
    for (wi in 0 until ws.size) {
        val w = ws[wi]
        check(w.blit != lit) { "walk: blocking literal equals watched literal" }
        if (value(w.blit) > 0) continue
        if (w.binary()) {
            res++
            continue
        }

        val c = w.clause
        val literals = c.literals
        check(lit == literals[0]) { "walk: watched literal not first" }

        // Now try to find a second satisfied literal starting at 'literals[1]'
        // shifting all the traversed literals to right by one position in order
        // to move such a second satisfying literal to 'literals[1]'.  This move
        // to front strategy improves the chances to find the second satisfying
        // literal earlier in subsequent break-count computations.
        //
        val begin = 1
        val end = c.size
        var i = begin
        var prev = 0
        while (i != end) {
            val other = literals[i]
            literals[i++] = prev
            prev = other
            if (value(other) < 0) continue

            // Found 'other' as second satisfying literal.

            w.blit = other // Update 'blit'
            literals[begin] = other // and move to front.

            break
        }

        if (i != end) continue // Double satisfied!

        // Otherwise restore literals (undo shift to the right).
        //
        while (i != begin) {
            val other = literals[--i]
            literals[i] = prev
            prev = other
        }

        res++ // Literal 'lit' single satisfies clause 'c'.
    }

    return res
}

/*------------------------------------------------------------------------*/

// Given an unsatisfied clause 'c', in which we want to flip a literal, we
// first determine the exponential score based on the break-count of its
// literals and then sample the literals based on these scores.  The CB
// value is smaller than one and thus the score is exponentially decreasing
// with the break-count increasing.  The sampling works as in 'ProbSAT' and
// 'YalSAT' by summing up the scores and then picking a random limit in the
// range of zero to the sum, then summing up the scores again and picking
// the first literal which reaches the limit.  Note, that during incremental
// SAT solving we can not flip assumed variables.  Those are assigned at
// decision level one, while the other variables are assigned at two.

internal fun Internal.walkPickLit(walker: Walker, c: Clause): Int {
    check(walker.scores.isEmpty()) { "walk: scores not empty" }
    var sum = 0.0
    var propagations = 0L
    for (k in 0 until c.size) {
        val lit = c.literals[k]
        check(active(lit)) { "walk: inactive literal in clause" }
        if (variable(lit).level == 1) {
            continue
        }
        check(active(lit)) { "walk: inactive literal in clause" }
        propagations++
        val tmp = walkBreakValue(-lit)
        val score = walker.score(tmp)
        walker.scores.add(score)
        sum += score
    }
    check(walker.scores.isNotEmpty()) { "walk: no literal scored" }
    walker.propagations += propagations
    stats.propagations.walk += propagations
    check(walker.scores.size <= c.size) { "walk: more scores than literals" }
    val lim = sum * walker.random.generateDouble()
    val end = c.size
    var i = 0
    var j = 0
    var res: Int
    while (true) {
        check(i != end) { "walk: no non-assumption literal in clause" }
        res = c.literals[i++]
        if (variable(res).level > 1) break
    }
    sum = walker.scores[j++]
    while (sum <= lim && i != end) {
        res = c.literals[i++]
        if (variable(res).level == 1) {
            continue
        }
        sum += walker.scores[j++]
    }
    walker.scores.clear()
    return res
}

/*------------------------------------------------------------------------*/

internal fun Internal.walkFlipLit(walker: Walker, lit: Int) {

    requireMode(Internal.WALK)
    check(value(lit) < 0) { "walk: flipping non-false literal" }

    // First flip the literal value.
    //
    val tmp = sign(lit)
    val idx = abs(lit)
    setVal(idx, tmp)
    check(value(lit) > 0) { "walk: flipped literal not true" }

    // Then remove 'c' and all other now satisfied (made) clauses.
    run {
        // Simply go over all unsatisfied (broken) clauses.

        // We need to measure (and bound) the memory accesses during traversing
        // broken clauses in terms of 'propagations'. This is tricky since we
        // are not actually propagating literals.  Instead we use the clause
        // variable 'ratio' as an approximation to the number of clauses used
        // during propagating a literal.  Note that we use a one-watch scheme.
        // Accordingly the number of broken clauses traversed divided by that
        // ratio is an approximation of the number of propagation this would
        // correspond to (in terms of memory access).  To eagerly update these
        // statistics we simply increment the propagation counter after every
        // 'ratio' traversed clause.  These propagations are particularly
        // expensive if the number of broken clauses is large which usually
        // happens initially.
        //
        val ratio = clauseVariableRatio()
        val broken = walker.broken
        val eou = broken.size
        var j = 0
        var i = j
        var count = 0L

        while (i != eou) {

            val d = broken[i++]
            broken[j++] = d

            val literals = d.literals
            var prev = 0

            // Find 'lit' in 'd'.
            //
            val size = d.size
            for (k in 0 until size) {
                val other = literals[k]
                check(active(other)) { "walk: inactive literal in broken clause" }
                literals[k] = prev
                prev = other
                if (other == lit) break
                check(value(other) < 0) { "walk: non-false literal in broken clause" }
            }

            // If 'lit' is in 'd' then move it to the front to watch it.
            //
            if (prev == lit) {
                literals[0] = lit
                watchLiteral(literals[0], literals[1], d)
                j--
            } else { // Otherwise the clause is not satisfied, undo shift.

                for (k in size - 1 downTo 0) {
                    val other = literals[k]
                    literals[k] = prev
                    prev = other
                }
            }

            if (count-- != 0L) continue

            // Update these counters eagerly.  Otherwise if we delay the update
            // until all clauses are traversed, interrupting the solver has a high
            // chance of giving bogus statistics on the number of 'propagations'
            // in 'walk', if it is interrupted in this loop.

            count = ratio.toLong() // Starting counting down again.
            walker.propagations++
            stats.propagations.walk++
        }
        broken.shrinkTo(j)
    }

    // Finally add all new unsatisfied (broken) clauses.
    run {
        walker.propagations++ // This really corresponds now to one
        stats.propagations.walk++ // propagation (in a one-watch scheme).

        val ws = watches(-lit)

        for (wi in 0 until ws.size) {
            val w = ws[wi]
            val d = w.clause
            val literals = d.literals
            var replacement = 0
            var prev = -lit
            check(literals[0] == -lit) { "walk: unwatched literal not first" }
            val size = d.size
            for (k in 1 until size) {
                val other = literals[k]
                check(active(other)) { "walk: inactive literal in watched clause" }
                literals[k] = prev // shift all to right
                prev = other
                val tmp2 = value(other)
                if (tmp2 < 0) continue
                replacement = other // satisfying literal
                break
            }
            if (replacement != 0) {
                literals[1] = -lit
                literals[0] = replacement
                check(-lit != replacement) { "walk: replacement equals flipped literal" }
                watchLiteral(replacement, -lit, d)
            } else {
                for (k in size - 1 downTo 1) { // undo shift
                    val other = literals[k]
                    literals[k] = prev
                    prev = other
                }
                check(literals[0] == -lit) { "walk: undo shift failed" }
                walker.broken.add(d)
            }
        }
        ws.clear()
    }
}

/*------------------------------------------------------------------------*/

// Check whether to save the current phases as new global minimum.

internal fun Internal.walkSaveMinimum(walker: Walker) {
    val broken = walker.broken.size.toLong()
    if (broken >= stats.walk.minimum) return
    stats.walk.minimum = broken
    for (i in 1..maxVar) {
        val tmp = vals[vsize + i]
        if (tmp.toInt() != 0) {
            phases.saved[i] = tmp
            phases.min[i] = tmp
        }
    }
}

/*------------------------------------------------------------------------*/

internal fun Internal.walkRound(limit: Long, prev: Boolean): Int = tracePhase("walk") {

    backtrack()
    if (propagated < trail.size && !propagate()) {
        learnEmptyClause()
        return 20
    }

    stats.walk.count++

    clearWatches()

    // Remove all fixed variables first (assigned at decision level zero).
    //
    if (last.collect.fixed < stats.all.fixed) garbageCollection()

    // We want to see more messages during initial local search.
    //
    if (localsearching) {
        check(!forcePhaseMessages) { "walk: phase messages already forced" }
        forcePhaseMessages = true
    }

    // First compute the average clause size for picking the CB constant.
    //
    var size = 0.0
    var n = 0L
    for (c in clauses) {
        if (c.garbage) continue
        if (c.redundant) {
            if (opts.walkredundant == 0) continue
            if (!likelyToBeKeptClause(c)) continue
        }
        size += c.size
        n++
    }
    val averageSize = relative(size, n.toDouble())

    // Instantiate data structures for this local search round.
    //
    val walker = Walker(this, averageSize, limit)

    var failed = false // Inconsistent assumptions?

    level = 1 // Assumed variables assigned at level 1.

    if (assumptions.isEmpty()) {
        // no assumptions so assigning all variables to decision phase
    } else {
        // assigning assumptions to their forced phase first
        for (k in 0 until assumptions.size) {
            val lit = assumptions[k]
            var tmp = value(lit)
            if (tmp > 0) continue
            if (tmp < 0) {
                failed = true
                break
            }
            if (!active(lit)) continue
            tmp = sign(lit)
            val idx = abs(lit)
            setVal(idx, tmp)
            check(level == 1) { "walk: assumption level not one" }
            variable(idx).level = 1
        }
    }

    level = 2 // All other non assumed variables assigned at level 2.

    if (!failed) {

        for (idx in 1..maxVar) {
            if (!active(idx)) {
                continue
            }
            if (vals[vsize + idx].toInt() != 0) {
                check(variable(idx).level == 1) { "walk: assigned variable not assumed" }
                continue
            }
            var tmp = 0
            if (prev) tmp = phases.prev[idx].toInt()
            if (tmp == 0) tmp = sign(decidePhase(idx, true))
            check(tmp == 1 || tmp == -1) { "walk: invalid initial phase" }
            setVal(idx, tmp)
            check(level == 2) { "walk: decision level not two" }
            variable(idx).level = 2
        }

        // watching satisfied and registering broken clauses
        for (c in clauses) {

            if (c.garbage) continue
            if (c.redundant) {
                if (opts.walkredundant == 0) continue
                if (!likelyToBeKeptClause(c)) continue
            }

            var satisfiable = false // contains not only assumptions
            var satisfied = 0 // clause satisfied?

            val lits = c.literals
            val size2 = c.size

            // Move to front satisfied literals and determine whether there
            // is at least one (non-assumed) literal that can be flipped.
            //
            var i = 0
            while (satisfied < 2 && i < size2) {
                val lit = lits[i]
                check(active(lit)) { "walk: inactive literal after collection" } // Due to garbage collection.
                if (value(lit) > 0) {
                    val t = lits[satisfied]
                    lits[satisfied] = lits[i]
                    lits[i] = t
                    satisfied++
                } else if (!satisfiable && variable(lit).level > 1) {
                    satisfiable = true
                }
                i++
            }

            if (satisfied == 0 && !satisfiable) {
                // due to assumptions unsatisfiable, stopping local search
                failed = true
                break
            }

            if (satisfied != 0) {
                watchLiteral(lits[0], lits[1], c)
            } else {
                check(satisfiable) { "walk: broken clause without flippable literal" } // at least one non-assumed variable ...
                walker.broken.add(c)
            }
        }
    }

    // 'int64_t old_global_minimum = stats.walk.minimum' only feeds PHASE messages (dropped).

    val res: Int // Tells caller to continue with local search.

    if (!failed) {

        var broken = walker.broken.size.toLong()

        walkSaveMinimum(walker)

        var minimum = broken
        while (!terminatedAsynchronously() && walker.broken.isNotEmpty() &&
            walker.propagations < walker.limit
        ) {
            stats.walk.flips++
            stats.walk.broken += broken
            val c = walkPickClause(walker)
            val lit = walkPickLit(walker, c)
            walkFlipLit(walker, lit)
            broken = walker.broken.size.toLong()
            if (broken >= minimum) continue
            minimum = broken
            walkSaveMinimum(walker)
        }

        if (minimum > 0) {
            // minimum non-zero thus potentially continue
            res = 0
        } else {
            // minimum is zero thus stop local search
            res = 10
        }

    } else {

        res = 20

        // aborted due to inconsistent assumptions
    }

    copyPhases(phases.prev)

    for (idx in 1..maxVar) if (active(idx)) setVal(idx, 0)

    check(level == 2) { "walk: decision level not two at end" }
    level = 0

    clearWatches()
    connectWatches()

    if (localsearching) {
        check(forcePhaseMessages) { "walk: phase messages not forced" }
        forcePhaseMessages = false
    }

    res
}

internal fun Internal.walk() {
    startInnerWalk()
    var limit = stats.propagations.search
    limit = (limit.toDouble() * (1e-3 * opts.walkreleff)).toLong()
    if (limit < opts.walkmineff) limit = opts.walkmineff.toLong()
    if (limit > opts.walkmaxeff) limit = opts.walkmaxeff.toLong()
    walkRound(limit, false)
    stopInnerWalk()
}
