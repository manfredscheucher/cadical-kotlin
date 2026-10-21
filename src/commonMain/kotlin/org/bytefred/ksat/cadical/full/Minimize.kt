package org.bytefred.ksat.cadical.full

import org.bytefred.ksat.cadical.IntArrayList

/*
 * minimize.cpp: recursive learned clause minimization (with poison / removable marks,
 * Knuth's early abort and the trail based early abort), its LRAT chain and the sorting of
 * the clause along the trail.
 */

// Functions for learned clause minimization. We only have the recursive
// version, which actually really is implemented recursively.  We also
// played with a derecursified version, which however was more complex and
// slower.  The trick to keep potential stack exhausting recursion under
// guards is to explicitly limit the recursion depth.

// Instead of signatures as in the original implementation in MiniSAT and
// our corresponding paper, we use the 'poison' idea of Allen Van Gelder to
// mark unsuccessful removal attempts, then Donald Knuth's idea to abort
// minimization if only one literal was seen on the level and a new idea of
// also aborting if the earliest seen literal was assigned afterwards.

internal fun Internal.minimizeLiteral(lit: Int, depth: Int = 0): Boolean {
    check(value(lit) > 0) { "minimize_literal of non-true literal" }
    val f = flags(lit)
    val v = variable(lit)
    if (v.level == 0 || f.removable || f.keep) return true
    if (v.reason == null || f.poison || v.level == level) return false
    val l = control[v.level]
    if (depth == 0 && l.seenCount < 2) return false // Don Knuth's idea
    if (v.trail <= l.seenTrail) return false // new early abort
    if (depth > opts.minimizedepth) return false
    var res = true
    check(v.reason != null)
    if (v.reason === externalReason) {
        check(opts.exteagerreasons == 0)
        v.reason = learnExternalReasonClause(lit, 0, true)
        if (v.reason == null) {
            check(v.level == 0)
            return true
        }
    }
    val reason = v.reason!!
    check(reason !== externalReason)
    val end = reason.size
    var i = 0
    while (res && i != end) {
        val other = reason.literals[i]
        i++
        if (other == lit) continue
        res = minimizeLiteral(-other, depth + 1)
    }
    if (res) f.removable = true
    else f.poison = true
    minimized.add(lit)
    return res
}

// Sorting the clause before minimization with respect to the trail order
// (literals with smaller trail height first) is necessary but natural and
// might help to minimize the required recursion depth too.

private class MinimizeTrailPositiveRank(private val internal: Internal) : IntRank {
    // typedef unsigned Type;
    override val bits: Int get() = 32

    override fun rank(a: Int): Long {
        check(internal.value(a) != 0)
        return internal.variable(a).trail.toLong() and 0xffffffffL
    }
}

private class MinimizeTrailSmaller(private val internal: Internal) : IntLess {
    override fun less(a: Int, b: Int): Boolean =
        internal.variable(a).trail < internal.variable(b).trail
}

// 'minimize_trail_level_positive_rank' and 'minimize_trail_level_smaller' are defined
// upstream in minimize.cpp but not used anywhere; ported for completeness.
private class MinimizeTrailLevelPositiveRank(private val internal: Internal) : IntRank {
    // typedef uint64_t Type;
    override fun rank(a: Int): Long {
        check(internal.value(a) != 0)
        val v = internal.variable(a)
        var res = v.level.toLong() and 0xffffffffL
        res = res shl 32
        res = res or (v.trail.toLong() and 0xffffffffL)
        return res
    }
}

private class MinimizeTrailLevelSmaller(private val internal: Internal) : IntLess {
    override fun less(a: Int, b: Int): Boolean =
        MinimizeTrailLevelPositiveRank(internal).rank(a).toULong() <
            MinimizeTrailLevelPositiveRank(internal).rank(b).toULong()
}

internal fun Internal.minimizeClause() {

    external!!.checkLearnedClause() // check 1st UIP learned clause first
    minimizeSortClause()

    check(minimized.isEmpty())
    check(minimizeChain.isEmpty())
    val end = clause.size
    var j = 0
    var i = j
    val stack = IntArrayList()
    while (i != end) {
        if (minimizeLiteral(-clause[i])) {
            if (lrat) {
                check(miniChain.isEmpty())
                calculateMinimizeChain(-clause[i], stack)
                for (p in miniChain) {
                    minimizeChain.add(p)
                }
                miniChain.clear()
            }
            stats.minimized++
        } else {
            clause[j] = clause[i]
            flags(clause[j++]).keep = true
        }
        i++
    }
    if (j != end) clause.resize(j)
    clearMinimizedLiterals()
    var p = minimizeChain.size - 1
    while (p != -1) {
        lratChain.add(minimizeChain[p])
        p--
    }
    minimizeChain.clear()
}

// go backwards in reason graph and add ids
// mini_chain is in correct order so we have to add it to minimize_chain
// and then reverse when we put it on lrat_chain
//
// We have to use the non-recursive as we cannot limit the depth like the
// minimize version. Unlike the minimize version, we have to keep literals
// on the stack in order to push its reason later.
internal fun Internal.calculateMinimizeChain(lit: Int, stack: IntArrayList) {
    check(stack.isEmpty())
    stack.add(vidx(lit))

    while (!stack.isEmpty()) {
        val idx = stack.back()
        check(idx != 0)
        stack.removeLast()
        if (idx < 0) {
            val v = variable(idx)
            miniChain.add(v.reason!!.id)
            continue
        }
        check(idx != 0)
        val f = flags(idx)
        val v = variable(idx)
        if (f.keep || f.added || f.poison) {
            continue
        }
        if (v.level == 0) {
            if (f.seen) continue
            f.seen = true
            unitAnalyzed.add(idx)
            val unitLit = if (value(idx) > 0) idx else -idx
            val uidx = vlit(unitLit) // I didn't clean added flag
            val id = unitClauses(uidx)
            check(id != 0L)
            unitChain.add(id)
            continue
        }
        f.added = true
        val reason = v.reason
        check(reason != null && f.removable)
        val end = reason.size
        stack.add(-idx)
        for (i in 0 until end) {
            val other = reason.literals[i]
            if (other == idx) continue
            stack.add(vidx(other))
        }
    }
    check(stack.isEmpty())
}

// Sort the literals in reverse assignment order (thus trail order) to
// establish the base case of the recursive minimization algorithm in the
// positive case (where a literal with 'keep' true is hit).
//
internal fun Internal.minimizeSortClause() {
    msort(opts.radixsortlim, clause, MinimizeTrailPositiveRank(this), MinimizeTrailSmaller(this))
}

internal fun Internal.clearMinimizedLiterals() {
    for (k in 0 until minimized.size) {
        val lit = minimized[k]
        val f = flags(lit)
        f.poison = false
        f.removable = false
        f.shrinkable = false
        f.added = false
    }
    for (k in 0 until clause.size) {
        val lit = clause[k]
        check(!flags(lit).shrinkable)
        flags(lit).keep = false
        flags(lit).shrinkable = false
        flags(lit).added = false
    }
    minimized.clear()
}
