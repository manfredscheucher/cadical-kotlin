package org.bytefred.ksat.cadical.full

/*
 * flip.cpp: flipping the value of a literal in a satisfying assignment ('flip') and
 * checking whether that is possible without breaking the watch invariants ('flippable').
 */

internal fun Internal.flip(lit: Int): Boolean {
    var lit = lit

    // Do not try to flip inactive literals except for unused variables.

    if (!active(lit) && !flags(lit).unused())
        return false

    // TODO: Unused case is not handled yet.
    // if (flags (lit).unused ()) return false;

    // Need to reestablish proper watching invariants as if there are no
    // blocking literals as flipping in principle does not work with them.

    if (propergated < trail.size)
        propergate()

    run {
        val idx = vidx(lit)
        val originalValue = vals[vsize + idx].toInt()
        check(originalValue != 0) { "flip: unassigned literal" }
        lit = if (originalValue < 0) -idx else idx
        check(value(lit) > 0) { "flip: literal not true" }
    }

    // Here we go over all the clauses in which 'lit' is watched by 'lit' and
    // check whether assigning 'lit' to false would break watching invariants
    // or even make the clause false.  We also try to find replacement
    // watches in case this fixes the watching invariant.  This code is very
    // similar to propagation of a literal in 'Internal::propagate'.

    var res = true

    val ws = watches(lit)
    val eow = ws.size
    val bow = 0

    // We first go over binary watches/clauses first as this is cheaper and
    // has higher chance of failure and we can not use blocking literals.

    for (i in bow until eow) {
        val w = ws[i]
        if (!w.binary())
            continue
        val b = value(w.blit)
        if (b > 0)
            continue
        check(b < 0) { "flip: unassigned binary blit" }
        res = false
        break
    }

    if (res) {
        var i = bow
        var j = bow

        while (i != eow) {

            val w = ws[i++]
            ws[j++] = w

            if (w.binary())
                continue

            if (w.clause.garbage) {
                j--
                continue
            }

            val lits = w.clause.literals

            val other = lits[0] xor lits[1] xor lit
            val u = value(other)
            if (u > 0)
                continue

            val size = w.clause.size
            val middle = w.clause.pos
            val end = size
            var k = middle

            var r = 0
            var v = -1
            while (k != end && run { r = lits[k]; v = value(r); v } < 0)
                k++
            if (v < 0) {
                k = 2
                check(w.clause.pos <= size) { "flip: pos beyond size" }
                while (k != middle && run { r = lits[k]; v = value(r); v } < 0)
                    k++
            }

            if (v < 0) {
                res = false
                break
            }

            check(v > 0) { "flip: replacement not true" }
            check(2 <= k) { "flip: replacement before watches" }; check(k <= w.clause.size) { "flip: replacement out of range" }
            w.clause.pos = k
            lits[0] = other; lits[1] = r; lits[k] = lit
            watchLiteral(r, lit, w.clause)
            j--
        }

        if (j != i) {

            while (i != eow)
                ws[j++] = ws[i++]

            ws.shrinkTo(j)
        }
    }

    if (res) {

        val idx = vidx(lit)
        val originalValue = vals[vsize + idx].toInt()
        check(originalValue != 0) { "flip: unassigned literal" }
        lit = if (originalValue < 0) -idx else idx
        check(value(lit) > 0) { "flip: literal not true" }

        setVal(idx, -originalValue)
        check(value(-lit) > 0) { "flip: flipped literal not true" }
        check(value(lit) < 0) { "flip: old literal not false" }

        val v = variable(idx)
        check(trail[v.trail] == lit) { "flip: trail mismatch" }
        trail[v.trail] = -lit
        if (opts.ilb != 0) {
            if (taintedLiteral == 0)
                taintedLiteral = lit
            else {
                check(value(taintedLiteral) != 0) { "flip: tainted literal unassigned" }
                if (v.level < variable(taintedLiteral).level) {
                    taintedLiteral = lit
                }
            }
        }
    }
    // else: flipping value of lit failed

    return res
}

internal fun Internal.flippable(lit: Int): Boolean {
    var lit = lit

    // Can not check inactive literals except for unused variables.

    if (!active(lit) && !flags(lit).unused())
        return false

    // TODO: Unused case is not handled yet
    // if (flags (lit).unused ()) return false;

    // Need to reestablish proper watching invariants as if there are no
    // blocking literals as flipping in principle does not work with them.

    if (propergated < trail.size)
        propergate()

    val idx = vidx(lit)
    val originalValue = vals[vsize + idx].toInt()
    check(originalValue != 0) { "flippable: unassigned literal" }
    lit = if (originalValue < 0) -idx else idx
    check(value(lit) > 0) { "flippable: literal not true" }

    // Here we go over all the clauses in which 'lit' is watched by 'lit' and
    // check whether assigning 'lit' to false would break watching invariants
    // or even make the clause false.  In contrast to 'flip' we do not try to
    // find replacement literals but do use blocking literals'.  Therefore we
    // also do not split the traversal code into two parts.

    var res = true

    val ws = watches(lit)
    val eow = ws.size
    for (i in 0 until eow) {

        // 'const Watch w = *i': only 'i->blit' is written below, and 'w' is not read after.
        val w = ws[i]
        val b = value(w.blit)
        if (b > 0)
            continue
        check(b < 0) { "flippable: unassigned blit" }

        if (w.binary()) {
            res = false
            break
        }

        if (w.clause.garbage)
            continue

        val lits = w.clause.literals

        val other = lits[0] xor lits[1] xor lit
        val u = value(other)
        if (u > 0) {
            ws[i].blit = other
            continue
        }

        val size = w.clause.size
        val middle = w.clause.pos
        val end = size
        var k = middle

        var r = 0
        var v = -1
        while (k != end && run { r = lits[k]; v = value(r); v } < 0)
            k++
        if (v < 0) {
            k = 2
            check(w.clause.pos <= size) { "flippable: pos beyond size" }
            while (k != middle && run { r = lits[k]; v = value(r); v } < 0)
                k++
        }

        if (v < 0) {
            res = false
            break
        }

        check(v > 0) { "flippable: replacement not true" }
        check(2 <= k) { "flippable: replacement before watches" }
        check(k <= w.clause.size) { "flippable: replacement out of range" }
        w.clause.pos = k
        ws[i].blit = r
    }

    return res
}
