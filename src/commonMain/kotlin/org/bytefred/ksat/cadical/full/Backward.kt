package org.bytefred.ksat.cadical.full

/*
 * backward.cpp
 *
 * Mapping:
 *  - 'Eliminator::enqueue', 'Eliminator::dequeue' -> extension functions on [Eliminator];
 *    'queue<Clause *>' push / front / pop -> ArrayDeque addLast / first / removeFirst.
 *  - The destructor '~Eliminator' -> [destroy]; Kotlin has no destructors, so the owner of
 *    the eliminator ('elim_round') calls it where the C++ object goes out of scope.
 *  - 'size_t len = UINT_MAX' -> Long 4294967295 (size_t is 64 bit); 'unsigned size' -> Int
 *    bit pattern compared with toUInt () (it is set to UINT_MAX inside the loop).
 */

// Provide eager backward subsumption for resolved clauses.

// The eliminator maintains a queue of clauses that are new and have to be
// checked to subsume or strengthen other (longer or same size) clauses.

internal fun Eliminator.enqueue(c: Clause) {
    if (internal.opts.elimbackward == 0) return
    if (c.enqueued) return
    backward.addLast(c)
    c.enqueued = true
}

internal fun Eliminator.dequeue(): Clause? {
    if (backward.isEmpty()) return null
    val res = backward.first()
    backward.removeFirst()
    check(res.enqueued) { "dequeue: not enqueued" }
    res.enqueued = false
    return res
}

/** '~Eliminator ()'. */
internal fun Eliminator.destroy() {
    while (dequeue() != null) {
    }
}

/*------------------------------------------------------------------------*/

internal fun Internal.elimBackwardClause(eliminator: Eliminator, c: Clause) {
    check(opts.elimbackward != 0) { "elimBackwardClause: elimbackward" }
    check(!c.redundant) { "elimBackwardClause: redundant" }
    if (c.garbage) return
    var len = 4294967295L // UINT_MAX as size_t
    var size = 0 // unsigned
    var best = 0
    var satisfied = false
    check(miniChain.isEmpty()) { "elimBackwardClause: mini_chain" }
    for (k in 0 until c.size) {
        val lit = c.literals[k]
        val tmp = value(lit)
        if (tmp > 0) {
            satisfied = true
            break
        }
        if (tmp < 0) continue
        val l = occs(lit).size.toLong()
        if (l < len) {
            best = lit
            len = l
        }
        mark(lit)
        size++
    }
    if (satisfied) {
        elimUpdateRemovedClause(eliminator, c)
        markGarbage(c)
    } else if (len > opts.elimocclim.toLong()) {
        // skipping backward subsumption due to too many occurrences
    } else {
        check(len != 0L) { "elimBackwardClause: len" }
        val os = occs(best)
        val end = os.size
        for (n in 0 until end) {
            val d = os[n]
            if (d === c) continue
            if (d.garbage) continue
            if (d.size.toUInt() < size.toUInt()) continue
            var negated = 0
            var found = 0 // unsigned
            for (k in 0 until d.size) {
                val lit = d.literals[k]
                var tmp = value(lit)
                if (tmp > 0) {
                    satisfied = true
                    break
                }
                if (tmp < 0) continue
                tmp = marked(lit)
                if (tmp == 0) continue
                if (tmp < 0) {
                    if (negated != 0) {
                        size = -1 // UINT_MAX
                        break
                    } else {
                        negated = lit
                    }
                }
                if (++found == size) break
            }
            if (satisfied) {
                elimUpdateRemovedClause(eliminator, d)
                markGarbage(d)
            } else if (found == size) {
                if (negated == 0) {
                    elimUpdateRemovedClause(eliminator, d)
                    markGarbage(d)
                    stats.subsumed++
                    stats.elimbwsub++
                } else {
                    var unit = 0
                    check(minimizeChain.isEmpty()) { "elimBackwardClause: minimize_chain" }
                    check(analyzed.isEmpty()) { "elimBackwardClause: analyzed" }
                    check(lratChain.isEmpty()) { "elimBackwardClause: lrat_chain" }
                    for (k in 0 until d.size) { // find out if we get
                        val lit = d.literals[k]
                        val tmp = value(lit) // a new unit or just
                        if (tmp < 0) { // strengthen c
                            if (!lrat) continue
                            val f = flags(lit)
                            check(!f.seen) { "elimBackwardClause: seen" }
                            if (f.seen) continue
                            f.seen = true
                            analyzed.add(lit)
                            continue
                        }
                        if (tmp > 0) {
                            satisfied = true
                            break
                        }
                        if (lit == negated) continue
                        if (unit != 0) {
                            unit = Int.MIN_VALUE
                            break
                        } else {
                            unit = lit
                        }
                    }
                    if (lrat && !satisfied) {
                        // if we found a unit we need to add all unit ids from
                        // {c\d}U{d\c} otherwise just the unit ids from {c\d}
                        for (k in 0 until c.size) {
                            val lit = c.literals[k]
                            val tmp = value(lit)
                            check(tmp <= 0) { "elimBackwardClause: c satisfied" }
                            if (tmp >= 0) continue
                            val f = flags(lit)
                            if (f.seen && unit != 0 && unit == Int.MIN_VALUE) {
                                f.seen = false
                                continue
                            } else if (!f.seen) {
                                f.seen = true
                                analyzed.add(lit)
                            }
                        }
                        if (unit == Int.MIN_VALUE) { // we do not need units from {d\c}
                            for (k in 0 until d.size) {
                                val lit = d.literals[k]
                                flags(lit).seen = false
                            }
                        }
                        for (k in 0 until analyzed.size) {
                            val lit = analyzed[k]
                            val f = flags(lit)
                            if (!f.seen) {
                                f.seen = true
                                continue
                            }
                            val uidx = vlit(-lit)
                            val id = unitClauses(uidx)
                            check(id != 0L) { "elimBackwardClause: unit id" }
                            lratChain.add(id)
                        }
                        clearAnalyzedLiterals()
                        lratChain.add(d.id)
                        lratChain.add(c.id)
                    }
                    if (satisfied) {
                        check(lratChain.isEmpty()) { "elimBackwardClause: lrat_chain satisfied" }
                        markGarbage(d)
                        elimUpdateRemovedClause(eliminator, d)
                    } else if (unit != 0 && unit != Int.MIN_VALUE) {
                        check(unit != 0) { "elimBackwardClause: unit" }
                        assignUnit(unit)
                        elimPropagate(eliminator, unit)
                        lratChain.clear()
                        break
                    } else if (occs(negated).size.toLong() <= opts.elimocclim.toLong()) {
                        strengthenClause(d, negated)
                        removeOccs(occs(negated), d)
                        elimUpdateRemovedLit(eliminator, negated)
                        stats.elimbwstr++
                        check(negated != best) { "elimBackwardClause: negated == best" }
                        eliminator.enqueue(d)
                    }
                    lratChain.clear()
                }
            }
        }
    }
    miniChain.clear()
    unmark(c)
}

/*------------------------------------------------------------------------*/

internal fun Internal.elimBackwardClauses(eliminator: Eliminator) {
    if (opts.elimbackward == 0) {
        check(eliminator.backward.isEmpty()) { "elimBackwardClauses: backward not empty" }
        return
    }
    // 'while (!unsat && (c = eliminator.dequeue ()))'
    while (!unsat) {
        val c = eliminator.dequeue() ?: break
        elimBackwardClause(eliminator, c)
    }
}
