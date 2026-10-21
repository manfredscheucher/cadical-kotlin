package org.bytefred.ksat.cadical.full

/*
 * instantiate.cpp
 *
 * Mapping: watch iterators 'i', 'j' -> indices into 'ws' (see WatchHpp.kt for the aliasing of
 * 'const Watch w = *j++ = *i++' with the slot 'j[-1]'); clause literal iterators -> indices
 * into 'c.literals'. The '#ifndef QUIET' counters 'candidates' and 'tried' only feed messages
 * and are not ported.
 */

/*------------------------------------------------------------------------*/

// This provides an implementation of variable instantiation, a technique
// for removing literals with few occurrence (see also 'instantiate.hpp').

/*------------------------------------------------------------------------*/

// Triggered at the end of a variable elimination round ('elim_round').

internal fun Internal.collectInstantiationCandidates(instantiator: Instantiator) {
    check(occurring()) { "collect_instantiation_candidates: not occurring" }
    for (idx in 1..maxVar) {
        if (frozen(idx)) continue
        if (!active(idx)) continue
        if (flags(idx).elim) continue // BVE attempt pending
        var sign = -1
        while (sign <= 1) {
            val lit = sign * idx
            if (noccs(lit) > opts.instantiateocclim) {
                sign += 2
                continue
            }
            val os = occs(lit)
            for (c in os) {
                if (c.garbage) continue
                if (opts.instantiateonce != 0 && c.instantiated) continue
                if (c.size < opts.instantiateclslim) continue
                var satisfied = false
                var unassigned = 0
                for (k in 0 until c.size) {
                    val other = c.literals[k]
                    val tmp = value(other)
                    if (tmp > 0) satisfied = true
                    if (tmp == 0) unassigned++
                }
                if (satisfied) continue
                if (unassigned < 3) continue // avoid learning units
                val negoccs = occs(-lit).size.toLong()
                instantiator.candidate(lit, c, c.size, negoccs)
            }
            sign += 2
        }
    }
}

/*------------------------------------------------------------------------*/

// Specialized propagation and assignment routines for instantiation.

internal fun Internal.instAssign(lit: Int) {
    check(value(lit) == 0) { "inst_assign: assigned" }
    check(numAssigned < maxVar) { "inst_assign: num_assigned" }
    numAssigned++
    setVal(lit, 1)
    trail.add(lit)
}

// Conflict analysis is only needed to do valid resolution proofs.
// We remember propagated clauses in order of assignment (in inst_chain)
// which allows us to do a variant of conflict analysis if the instantiation
// attempt succeeds.
//
internal fun Internal.instPropagate(): Boolean { // Adapted from 'propagate'.
    val before = propagated.toLong()
    var ok = true
    while (ok && propagated != trail.size) {
        val lit = -trail[propagated++]
        val ws = watches(lit)
        val eow = ws.size
        var i = 0
        var j = 0
        while (i != eow) {
            val w = ws[i++]
            ws[j++] = w
            val b = value(w.blit)
            if (b > 0) continue
            if (w.binary()) {
                if (b < 0) {
                    ok = false
                    if (lrat) {
                        instChain.add(w.clause)
                    }
                    break
                } else {
                    if (lrat) {
                        instChain.add(w.clause)
                    }
                    instAssign(w.blit)
                }
            } else {
                val lits = w.clause.literals
                val other = lits[0] xor lits[1] xor lit
                lits[0] = other
                lits[1] = lit
                val u = value(other)
                if (u > 0) ws[j - 1].blit = other
                else {
                    val size = w.clause.size
                    val end = size
                    val middle = w.clause.pos
                    var k = middle
                    var v = -1
                    var r = 0
                    while (k != end) {
                        r = lits[k]
                        v = value(r)
                        if (v >= 0) break
                        k++
                    }
                    if (v < 0) {
                        k = 2
                        check(w.clause.pos <= size) { "inst_propagate: pos" }
                        while (k != middle) {
                            r = lits[k]
                            v = value(r)
                            if (v >= 0) break
                            k++
                        }
                    }
                    w.clause.pos = k
                    check(2 <= k) { "inst_propagate: k below 2" }
                    check(k <= w.clause.size) { "inst_propagate: k beyond end" }
                    if (v > 0) {
                        ws[j - 1].blit = r
                    } else if (v == 0) {
                        lits[1] = r
                        lits[k] = lit
                        watchLiteral(r, lit, w.clause)
                        j--
                    } else if (u == 0) {
                        check(v < 0) { "inst_propagate: v" }
                        if (lrat) {
                            instChain.add(w.clause)
                        }
                        instAssign(other)
                    } else {
                        check(u < 0) { "inst_propagate: u" }
                        check(v < 0) { "inst_propagate: v" }
                        if (lrat) {
                            instChain.add(w.clause)
                        }
                        ok = false
                        break
                    }
                }
            }
        }
        if (j != i) {
            while (i != eow) ws[j++] = ws[i++]
            ws.shrinkTo(j)
        }
    }
    val delta = propagated - before
    stats.propagations.instantiate += delta
    return ok
}

/*------------------------------------------------------------------------*/

// This is the instantiation attempt.

internal fun Internal.instantiateCandidate(lit: Int, c: Clause): Boolean {
    stats.instried++
    if (c.garbage) return false
    check(level == 0) { "instantiate_candidate: level" }
    var found = false
    var satisfied = false
    var inactive = false
    var unassigned = 0
    for (k in 0 until c.size) {
        val other = c.literals[k]
        if (other == lit) found = true
        val tmp = value(other)
        if (tmp > 0) {
            satisfied = true
            break
        }
        if (tmp == 0 && !active(other)) {
            inactive = true
            break
        }
        if (tmp == 0) unassigned++
    }
    if (!found) return false
    if (inactive) return false
    if (satisfied) return false
    if (unassigned < 3) return false
    val before = trail.size
    check(propagated == before) { "instantiate_candidate: propagated" }
    check(active(lit)) { "instantiate_candidate: inactive lit" }
    check(instChain.isEmpty()) { "instantiate_candidate: inst chain" }
    check(!c.garbage) { "instantiate_candidate: garbage" }
    c.instantiated = true
    check(lratChain.isEmpty()) { "instantiate_candidate: lrat chain" }
    level++
    instAssign(lit) // Assume 'lit' to true.
    for (k in 0 until c.size) {
        val other = c.literals[k]
        if (other == lit) continue
        val tmp = value(other)
        if (tmp != 0) {
            check(tmp < 0) { "instantiate_candidate: satisfied" }
            continue
        }
        instAssign(-other) // Assume other to false.
    }
    val ok = instPropagate() // Propagate.
    check(lratChain.isEmpty()) { "instantiate_candidate: lrat chain" } // chain will be built here
    if (ok) {
        instChain.clear()
    } else if (lrat) { // analyze conflict for lrat
        check(instChain.size != 0) { "instantiate_candidate: empty inst chain" }
        val reason = instChain.last()
        instChain.removeAt(instChain.size - 1)
        lratChain.add(reason.id)
        for (k in 0 until reason.size) {
            val other = reason.literals[k]
            val f = flags(other)
            check(!f.seen) { "instantiate_candidate: seen" }
            f.seen = true
            analyzed.add(other)
        }
    }
    while (trail.size > before) { // Backtrack.
        val other = trail.back()
        trail.removeLast()
        check(value(other) > 0) { "instantiate_candidate: unassign" }
        numAssigned--
        setVal(other, 0)
        // this is a variant of conflict analysis which is only needed for lrat
        if (!ok && instChain.size != 0 && lrat) {
            val f = flags(other)
            if (f.seen) {
                val reason = instChain.last()
                lratChain.add(reason.id)
                for (k in 0 until reason.size) {
                    val other2 = reason.literals[k]
                    val f2 = flags(other2)
                    if (f2.seen) continue
                    f2.seen = true
                    analyzed.add(other2)
                }
                f.seen = false
            }
            instChain.removeAt(instChain.size - 1)
        }
    }
    check(instChain.isEmpty()) { "instantiate_candidate: inst chain left" }
    // post processing step for lrat
    if (!ok && lrat) {
        if (flags(lit).seen) lratChain.add(c.id)
        for (k in 0 until c.size) {
            val other = c.literals[k]
            val f = flags(other)
            f.seen = false
        }
        for (k in 0 until analyzed.size) {
            val other = analyzed[k]
            val f = flags(other)
            if (!f.seen) {
                f.seen = true
                continue
            }
            val uidx = vlit(-other)
            val id = unitClauses(uidx)
            check(id != 0L) { "instantiate_candidate: unit id" }
            lratChain.add(id)
        }
        clearAnalyzedLiterals()
        lratChain.reverse()
    }
    check(analyzed.isEmpty()) { "instantiate_candidate: analyzed" }
    propagated = before
    check(level == 1) { "instantiate_candidate: level 1" }
    level = 0
    if (ok) {
        check(lratChain.isEmpty()) { "instantiate_candidate: lrat chain" }
        return false
    }
    unwatchClause(c)
    strengthenClause(c, lit)
    watchClause(c)
    lratChain.clear()
    check(c.size > 1) { "instantiate_candidate: size" }
    stats.instantiated++
    return true
}

/*------------------------------------------------------------------------*/

// Try to instantiate all candidates collected before through the
// 'collect_instantiation_candidates' routine.

internal fun Internal.instantiate(instantiator: Instantiator): Unit = tracePhase("instantiate") {
    check(opts.instantiate != 0) { "instantiate: option off" }
    stats.instrounds++
    // 'instantiated' only feeds messages and is not ported.
    initWatches()
    connectWatches()
    if (propagated < trail.size) {
        if (!propagate()) {
            learnEmptyClause()
            check(unsat) { "instantiate: not unsat" }
        }
    }
    while (!unsat && !terminatedAsynchronously() && instantiator.candidates.isNotEmpty()) {
        val cand = instantiator.candidates.last()
        instantiator.candidates.removeAt(instantiator.candidates.size - 1)
        if (!active(cand.lit)) continue
        if (!instantiateCandidate(cand.lit, cand.clause)) continue
    }
    // report ('I', !instantiated) dropped (message output).
    resetWatches()
}
