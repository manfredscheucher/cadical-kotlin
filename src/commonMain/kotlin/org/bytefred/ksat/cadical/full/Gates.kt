package org.bytefred.ksat.cadical.full

import org.bytefred.ksat.cadical.IntArrayList
import kotlin.math.abs

/*
 * gates.cpp
 *
 * Mapping: 'goto DONE' (jump to the final 'unmark_binary_literals') -> the code between the
 * jump and the label is skipped by an 'if'. 'int &a' out parameters -> IntRef. 'swap' of
 * locals / value parameters -> local vars. 'marks[vidx (lit)] *= 2' -> on the signed byte.
 * Occurrence lists are iterated by index up to the size taken at loop entry (range for).
 */

// As in our original SATeLite published at SAT'05 we are trying to find
// gates in order to restrict the number of resolutions that need to be
// tried.  If there is such a gate, we only need to consider resolvents
// among gate and one non-gate clauses.  Resolvents between definitions will
// be tautological anyhow and resolvents among non-gates can actually be
// shown to be redundant too.

/*------------------------------------------------------------------------*/

// The next function returns a non-zero if the clause 'c', which is assumed
// to contain the literal 'first', after removing falsified literals is a
// binary clause.  Then the actual second literal is returned.

internal fun Internal.secondLiteralInBinaryClause(eliminator: Eliminator, c: Clause, first: Int): Int {
    check(!c.garbage) { "secondLiteralInBinaryClause: garbage" }
    var second = 0
    for (k in 0 until c.size) {
        val lit = c.literals[k]
        if (lit == first) continue
        val tmp = value(lit)
        if (tmp < 0) continue
        if (tmp > 0) {
            markGarbage(c)
            elimUpdateRemovedClause(eliminator, c)
            return 0
        }
        if (second != 0) {
            second = Int.MIN_VALUE
            break
        }
        second = lit
    }
    if (second == 0) return 0
    if (second == Int.MIN_VALUE) return 0
    check(active(second)) { "secondLiteralInBinaryClause: inactive" }
    return second
}

/*------------------------------------------------------------------------*/

// need a copy from above that does not care about garbage

internal fun Internal.secondLiteralInBinaryClauseLrat(c: Clause, first: Int): Int {
    // TODO: this seems to work
    if (c.garbage) return 0
    var second = 0
    for (k in 0 until c.size) {
        val lit = c.literals[k]
        if (lit == first) continue
        val tmp = value(lit)
        if (tmp == 0) {
            if (second != 0) {
                second = Int.MIN_VALUE
                break
            }
            second = lit
        }
    }
    if (second == 0) return 0
    if (second == Int.MIN_VALUE) return 0
    return second
}

// I needed to find the second clause for hyper unary resolution to build
// LRAT this is not efficient but I could not find a better way then just
// finding the corresponding clause in all possible clauses
//
internal fun Internal.findBinaryClause(first: Int, second: Int): Clause? {
    var best = first
    var other = second
    if (occs(first).size > occs(second).size) {
        best = second
        other = first
    }
    val os = occs(best)
    val end = os.size
    for (n in 0 until end) {
        val c = os[n]
        if (secondLiteralInBinaryClauseLrat(c, best) == other) return c
    }
    return null
}

/*------------------------------------------------------------------------*/

// Mark all other literals in binary clauses with 'first'.  During this
// marking we might also detect hyper unary resolvents producing a unit.
// If such a unit is found we propagate it and return immediately.

internal fun Internal.markBinaryLiterals(eliminator: Eliminator, pivot: Int) {
    val first = pivot

    if (unsat) return
    if (value(first) != 0) return
    if (eliminator.gates.isNotEmpty()) return

    check(marked(first) == 0) { "markBinaryLiterals: first marked" }
    check(eliminator.marked.isEmpty()) { "markBinaryLiterals: marked not empty" }

    val os = occs(first)
    val end = os.size
    for (n in 0 until end) {
        val c = os[n]
        if (c.garbage) continue
        val second = secondLiteralInBinaryClause(eliminator, c, first)
        if (second == 0) continue
        val tmp = marked(second)
        if (tmp < 0) {
            // had a bug where units could occur multiple times here
            // solved with flags
            if (lrat) {
                val d = findBinaryClause(first, -second)
                check(d != null) { "markBinaryLiterals: no binary clause" }
                for (k in 0 until d.size) {
                    val lit = d.literals[k]
                    if (lit == first || lit == -second) continue
                    check(value(lit) < 0) { "markBinaryLiterals: d literal not false" }
                    val f = flags(lit)
                    if (f.seen) continue
                    analyzed.add(lit)
                    f.seen = true
                    val uidx = vlit(-lit)
                    val id = unitClauses(uidx)
                    check(id != 0L) { "markBinaryLiterals: unit id" }
                    lratChain.add(id)
                }
                for (k in 0 until c.size) {
                    val lit = c.literals[k]
                    if (lit == first || lit == second) continue
                    check(value(lit) < 0) { "markBinaryLiterals: c literal not false" }
                    val f = flags(lit)
                    if (f.seen) continue
                    analyzed.add(lit)
                    f.seen = true
                    val uidx = vlit(-lit)
                    val id = unitClauses(uidx)
                    check(id != 0L) { "markBinaryLiterals: unit id" }
                    lratChain.add(id)
                }
                lratChain.add(c.id)
                lratChain.add(d.id)
                clearAnalyzedLiterals()
            }
            assignUnit(first)
            elimPropagate(eliminator, first)
            return
        }
        if (tmp > 0) {
            elimUpdateRemovedClause(eliminator, c)
            markGarbage(c)
            continue
        }
        eliminator.marked.add(second)
        mark(second)
    }
}

// Unmark all literals saved on the 'marked' stack.

internal fun Internal.unmarkBinaryLiterals(eliminator: Eliminator) {
    for (k in 0 until eliminator.marked.size) unmark(eliminator.marked[k])
    eliminator.marked.clear()
}

/*------------------------------------------------------------------------*/

// Find equivalence for 'pivot'.  Requires that all other literals in binary
// clauses with 'pivot' are marked (through 'mark_binary_literals');

internal fun Internal.findEquivalence(eliminator: Eliminator, pivot: Int) {

    if (opts.elimequivs == 0) return

    check(opts.elimsubst != 0) { "findEquivalence: elimsubst" }

    if (unsat) return
    if (value(pivot) != 0) return
    if (eliminator.gates.isNotEmpty()) return

    markBinaryLiterals(eliminator, pivot)
    if (!(unsat || value(pivot) != 0)) { // else 'goto DONE'

        val os = occs(-pivot)
        val end = os.size
        for (n in 0 until end) {
            val c = os[n]

            if (c.garbage) continue

            val second = secondLiteralInBinaryClause(eliminator, c, -pivot)
            if (second == 0) continue
            val tmp = marked(second)
            if (tmp > 0) {
                // did not find a bug where units could occur multiple times here
                // still solved potential issues with flags
                if (lrat) {
                    val d = findBinaryClause(pivot, second)
                    check(d != null) { "findEquivalence: no binary clause" }
                    for (k in 0 until d.size) {
                        val lit = d.literals[k]
                        if (lit == pivot || lit == second) continue
                        check(value(lit) < 0) { "findEquivalence: d literal not false" }
                        val f = flags(lit)
                        if (f.seen) continue
                        analyzed.add(lit)
                        f.seen = true
                        val uidx = vlit(-lit)
                        val id = unitClauses(uidx)
                        check(id != 0L) { "findEquivalence: unit id" }
                        lratChain.add(id)
                    }
                    for (k in 0 until c.size) {
                        val lit = c.literals[k]
                        if (lit == -pivot || lit == second) continue
                        check(value(lit) < 0) { "findEquivalence: c literal not false" }
                        val f = flags(lit)
                        if (f.seen) continue
                        analyzed.add(lit)
                        f.seen = true
                        val uidx = vlit(-lit)
                        val id = unitClauses(uidx)
                        check(id != 0L) { "findEquivalence: unit id" }
                        lratChain.add(id)
                    }
                    lratChain.add(c.id)
                    lratChain.add(d.id)
                    clearAnalyzedLiterals()
                }
                assignUnit(second)
                elimPropagate(eliminator, second)
                if (value(pivot) != 0) break
                if (unsat) break
            }
            if (tmp >= 0) continue

            stats.elimequivs++
            stats.elimgates++

            check(!c.gate) { "findEquivalence: c gate" }
            c.gate = true
            eliminator.gates.add(c)

            var d: Clause? = null
            val ps = occs(pivot)
            val pend = ps.size
            for (m in 0 until pend) {
                val e = ps[m]
                if (e.garbage) continue
                val other = secondLiteralInBinaryClause(eliminator, e, pivot)
                if (other == -second) {
                    d = e
                    break
                }
            }
            check(d != null) { "findEquivalence: no second gate clause" }

            check(!d.gate) { "findEquivalence: d gate" }
            d.gate = true
            eliminator.gates.add(d)

            break
        }
    }

    // DONE:
    unmarkBinaryLiterals(eliminator)
}

/*------------------------------------------------------------------------*/

// Find and gates for 'pivot' with a long clause, in which the pivot occurs
// positively.  Requires that all other literals in binary clauses with
// 'pivot' are marked (through 'mark_binary_literals');

internal fun Internal.findAndGate(eliminator: Eliminator, pivot: Int) {

    if (opts.elimands == 0) return

    check(opts.elimsubst != 0) { "findAndGate: elimsubst" }

    if (unsat) return
    if (value(pivot) != 0) return
    if (eliminator.gates.isNotEmpty()) return

    markBinaryLiterals(eliminator, pivot)
    if (!(unsat || value(pivot) != 0)) { // else 'goto DONE'

        val ns = occs(-pivot)
        val end = ns.size
        for (n in 0 until end) {
            val c = ns[n]

            if (c.garbage) continue
            if (c.size < 3) continue

            var allLiteralsMarked = true
            var arity = 0 // unsigned
            var satisfied = 0

            for (k in 0 until c.size) {
                val lit = c.literals[k]
                if (lit == -pivot) continue
                check(lit != pivot) { "findAndGate: pivot in clause" }
                var tmp = value(lit)
                if (tmp < 0) continue
                if (tmp > 0) {
                    satisfied = lit
                    break
                }
                tmp = marked(lit)
                if (tmp < 0) {
                    arity++
                    continue
                }
                allLiteralsMarked = false
                break
            }

            if (!allLiteralsMarked) continue

            if (satisfied != 0) {
                markGarbage(c)
                continue
            }

            stats.elimands++
            stats.elimgates++

            check(!c.gate) { "findAndGate: c gate" }
            c.gate = true
            eliminator.gates.add(c)
            for (k in 0 until c.size) {
                val lit = c.literals[k]
                if (lit == -pivot) continue
                check(lit != pivot) { "findAndGate: pivot in clause" }
                val tmp = value(lit)
                if (tmp < 0) continue
                check(tmp == 0) { "findAndGate: assigned literal" }
                check(marked(lit) < 0) { "findAndGate: literal not marked negatively" }
                marks[vidx(lit)] = (marks[vidx(lit)] * 2).toByte()
            }

            var count = 0 // unsigned
            val ps = occs(pivot)
            val pend = ps.size
            for (m in 0 until pend) {
                val d = ps[m]
                if (d.garbage) continue
                val other = secondLiteralInBinaryClause(eliminator, d, pivot)
                if (other == 0) continue
                val tmp = marked(other)
                if (tmp != 2) continue
                check(!d.gate) { "findAndGate: d gate" }
                d.gate = true
                eliminator.gates.add(d)
                count++
            }
            check(count >= arity) { "findAndGate: count < arity" }

            break
        }
    }

    // DONE:
    unmarkBinaryLiterals(eliminator)
}

/*------------------------------------------------------------------------*/

// Find and extract ternary clauses.

internal fun Internal.getTernaryClause(d: Clause, a: IntRef, b: IntRef, c: IntRef): Boolean {
    if (d.garbage) return false
    if (d.size < 3) return false
    var found = 0
    a.value = 0
    b.value = 0
    c.value = 0
    for (k in 0 until d.size) {
        val lit = d.literals[k]
        if (value(lit) != 0) continue
        if (++found == 1) a.value = lit
        else if (found == 2) b.value = lit
        else if (found == 3) c.value = lit
        else return false
    }
    return found == 3
}

// This function checks whether 'd' exists as ternary clause.

internal fun Internal.matchTernaryClause(d: Clause, a: Int, b: Int, c: Int): Boolean {
    if (d.garbage) return false
    var found = 0
    for (k in 0 until d.size) {
        val lit = d.literals[k]
        if (value(lit) != 0) continue
        if (a != lit && b != lit && c != lit) return false
        found++
    }
    return found == 3
}

internal fun Internal.findTernaryClause(a: Int, b: Int, c: Int): Clause? {
    // 'a', 'b', 'c' are swapped (value parameters upstream).
    var x = a
    var y = b
    var z = c
    if (occs(y).size > occs(z).size) {
        val t = y
        y = z
        z = t
    }
    if (occs(x).size > occs(y).size) {
        val t = x
        x = y
        y = t
    }
    val os = occs(x)
    val end = os.size
    for (n in 0 until end) {
        val d = os[n]
        if (matchTernaryClause(d, x, y, z)) return d
    }
    return null
}

/*------------------------------------------------------------------------*/

// Find if-then-else gate.

internal fun Internal.findIfThenElse(eliminator: Eliminator, pivot: Int) {

    if (opts.elimites == 0) return

    check(opts.elimsubst != 0) { "findIfThenElse: elimsubst" }

    if (unsat) return
    if (value(pivot) != 0) return
    if (eliminator.gates.isNotEmpty()) return

    val os = occs(pivot)
    val end = os.size
    val ai = IntRef()
    val bi = IntRef()
    val ci = IntRef()
    val aj = IntRef()
    val bj = IntRef()
    val cj = IntRef()
    for (i in 0 until end) {
        val di = os[i]
        if (!getTernaryClause(di, ai, bi, ci)) continue
        if (bi.value == pivot) swapRefs(ai, bi)
        if (ci.value == pivot) swapRefs(ai, ci)
        check(ai.value == pivot) { "findIfThenElse: ai" }
        for (j in i + 1 until end) {
            val dj = os[j]
            if (!getTernaryClause(dj, aj, bj, cj)) continue
            if (bj.value == pivot) swapRefs(aj, bj)
            if (cj.value == pivot) swapRefs(aj, cj)
            check(aj.value == pivot) { "findIfThenElse: aj" }
            if (abs(bi.value) == abs(cj.value)) swapRefs(bj, cj)
            if (abs(ci.value) == abs(cj.value)) continue
            if (bi.value != -bj.value) continue
            val d1 = findTernaryClause(-pivot, bi.value, -ci.value) ?: continue
            val d2 = findTernaryClause(-pivot, bj.value, -cj.value) ?: continue
            check(!di.gate) { "findIfThenElse: di gate" }
            check(!dj.gate) { "findIfThenElse: dj gate" }
            check(!d1.gate) { "findIfThenElse: d1 gate" }
            check(!d2.gate) { "findIfThenElse: d2 gate" }
            di.gate = true
            dj.gate = true
            d1.gate = true
            d2.gate = true
            eliminator.gates.add(di)
            eliminator.gates.add(dj)
            eliminator.gates.add(d1)
            eliminator.gates.add(d2)
            stats.elimgates++
            stats.elimites++
            return
        }
    }
}

// 'swap (x, y)' of two int locals.
private fun swapRefs(x: IntRef, y: IntRef) {
    val t = x.value
    x.value = y.value
    y.value = t
}

/*------------------------------------------------------------------------*/

// Find and extract clause.

internal fun Internal.getClause(c: Clause, l: IntArrayList): Boolean {
    if (c.garbage) return false
    l.clear()
    for (k in 0 until c.size) {
        val lit = c.literals[k]
        if (value(lit) != 0) continue
        l.add(lit)
    }
    return true
}

// Check whether 'c' contains only the literals in 'l'.

internal fun Internal.isClause(c: Clause, lits: IntArrayList): Boolean {
    if (c.garbage) return false
    val size = lits.size
    if (c.size < size) return false
    var found = 0
    for (k in 0 until c.size) {
        val lit = c.literals[k]
        if (value(lit) != 0) continue
        if (!lits.contains(lit)) return false
        if (++found > size) return false
    }
    return found == size
}

internal fun Internal.findClause(lits: IntArrayList): Clause? {
    var best = 0
    var len = 0
    for (k in 0 until lits.size) {
        val lit = lits[k]
        val l = occs(lit).size
        if (best != 0 && l >= len) continue
        len = l
        best = lit
    }
    val os = occs(best)
    val end = os.size
    for (n in 0 until end) {
        val c = os[n]
        if (isClause(c, lits)) return c
    }
    return null
}

internal fun Internal.findXorGate(eliminator: Eliminator, pivot: Int) {

    if (opts.elimxors == 0) return

    check(opts.elimsubst != 0) { "findXorGate: elimsubst" }

    if (unsat) return
    if (value(pivot) != 0) return
    if (eliminator.gates.isNotEmpty()) return

    val lits = IntArrayList()

    val os = occs(pivot)
    val end = os.size
    for (n in 0 until end) {
        val d = os[n]

        if (!getClause(d, lits)) continue

        val size = lits.size // clause size
        val arity = size - 1 // arity of XOR

        if (size < 3) continue
        if (arity > opts.elimxorlim) continue

        check(eliminator.gates.isEmpty()) { "findXorGate: gates not empty" }

        var needed = (1 shl arity) - 1 // additional clauses (unsigned)
        var signs = 0 // literals to negate (unsigned)

        do {
            val prev = signs
            while (parity(++signs)) {
            }
            for (j in 0 until size) {
                val bit = 1 shl j
                val lit = lits[j]
                if ((prev and bit) != (signs and bit)) lits[j] = -lit
            }
            val e = findClause(lits) ?: break
            eliminator.gates.add(e)
        } while (--needed != 0)

        if (needed != 0) {
            eliminator.gates.clear()
            continue
        }

        eliminator.gates.add(d)
        check(eliminator.gates.size == (1 shl arity)) { "findXorGate: gates size" }

        stats.elimgates++
        stats.elimxors++
        val gates = eliminator.gates
        val gend = gates.size
        var j = 0
        for (i in 0 until gend) {
            val e = gates[i]
            if (e.gate) continue
            e.gate = true
            gates[j++] = e
        }
        gates.shrinkTo(j)

        break
    }
}

/*------------------------------------------------------------------------*/

// Find a gate for 'pivot'.  If such a gate is found, the gate clauses are
// marked and pushed on the stack of gates.  Further hyper unary resolution
// might detect units, which are propagated.  This might assign the pivot or
// even produce the empty clause.

internal fun Internal.findGateClauses(eliminator: Eliminator, pivot: Int) {
    if (opts.elimsubst == 0) return

    if (unsat) return
    if (value(pivot) != 0) return

    check(eliminator.gates.isEmpty()) { "findGateClauses: gates not empty" }

    findEquivalence(eliminator, pivot)
    findAndGate(eliminator, pivot)
    findAndGate(eliminator, -pivot)
    findIfThenElse(eliminator, pivot)
    findXorGate(eliminator, pivot)
}

internal fun Internal.unmarkGateClauses(eliminator: Eliminator) {
    for (k in 0 until eliminator.gates.size) {
        val c = eliminator.gates[k]
        check(c.gate) { "unmarkGateClauses: not a gate" }
        c.gate = false
    }
    eliminator.gates.clear()
}
