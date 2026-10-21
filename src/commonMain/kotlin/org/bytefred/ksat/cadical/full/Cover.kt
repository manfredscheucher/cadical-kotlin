package org.bytefred.ksat.cadical.full

import org.bytefred.ksat.cadical.IntArrayList

/*
 * cover.cpp: covered clause elimination (CCE, actually the asymmetric version ACCE).
 *
 * Mapping notes:
 *  - 'struct Coveror' -> class [Coveror] ('internal' because the cross-file signatures in
 *    SIGNATURES.md take it as a parameter); 'size_t' fields -> Int (indices) / Long (counts).
 *  - Watch / occurrence / literal iterators -> int indices (see PORTING.md).
 *  - 'int64_t *= double' ('delta *= 1e-3 * opts.coverreleff') -> convert to double,
 *    multiply, truncate with 'toLong ()'.
 *  - LOG / PHASE messages and 'report' are dropped; the '#ifndef QUIET' counters 'untried',
 *    'scheduled', 'remain', 'tried' only feed PHASE messages and are dropped too.
 */

/*------------------------------------------------------------------------*/

// Covered clause elimination (CCE) is described in our short LPAR-10 paper
// and later in more detail in our JAIR'15 article.  Actually implement
// the asymmetric version which adds asymmetric literals too but still call
// it 'CCE' in the following (and not 'ACCE').  This implementation provides
// a simplified and cleaner version of the one implemented before in
// Lingeling. We still follow quite closely the original description in the
// literature, which is based on asymmetric literal addition (ALA) and
// covered literal addition (CLA).  Both can be seen as kind of propagation,
// where the literals in the original and then extended clause are assigned
// to false, and the literals on the trail (actually we use our own 'added'
// stack for that) make up the extended clause.   The ALA steps can be
// implemented by simple propagation (copied from 'propagate.cpp') using
// watches, while the CLA steps need full occurrence lists to determine the
// resolution candidate clauses.  The CCE is successful if a conflict is
// found during ALA steps or if during a CLA step all resolution candidates
// of a literal on the trail are satisfied (the extended clause is blocked).

internal class Coveror {
    val added = IntArrayList() // acts as trail
    val extend = IntArrayList() // extension stack for witness
    val covered = IntArrayList() // clause literals or added through CLA
    val intersection = IntArrayList() // of literals in resolution candidates

    var alas = 0L // actual number of ALAs
    var clas = 0L // actual number of CLAs

    class Next {
        var added = 0
        var covered = 0
    }

    val next = Next() // propagate next ...
}

/*------------------------------------------------------------------------*/

// Push on the extension stack a clause made up of the given literal, the
// original clause (initially copied to 'covered') and all the added covered
// literals so far.  The given literal will act as blocking literal for that
// clause, if CCE is successful.  Only in this case, this private extension
// stack is copied to the actual extension stack of the solver.  Note, that
// even though all 'added' clauses correspond to the extended clause, we
// only need to save the original and added covered literals.

internal fun Internal.coverPushExtension(lit: Int, coveror: Coveror) {
    coveror.extend.add(0)
    coveror.extend.add(lit) // blocking literal comes first
    var found = false
    for (k in 0 until coveror.covered.size) {
        val other = coveror.covered[k]
        if (lit == other) {
            check(!found) { "cover: blocking literal twice in covered" }
            found = true
        } else {
            coveror.extend.add(other)
        }
    }
    check(found) { "cover: blocking literal not in covered" }
}

// Successful covered literal addition (CLA) step.

internal fun Internal.coveredLiteralAddition(lit: Int, coveror: Coveror) {
    requireMode(Internal.COVER)
    check(level == 1) { "cover: level not one" }
    coverPushExtension(lit, coveror)
    for (k in 0 until coveror.intersection.size) {
        val other = coveror.intersection[k]
        check(vals[vsize + other].toInt() == 0) { "cover: covered literal assigned" }
        check(vals[vsize - other].toInt() == 0) { "cover: covered literal negation assigned" }
        setVal(other, -1)
        coveror.covered.add(other)
        coveror.added.add(other)
        coveror.clas++
    }
    coveror.next.covered = 0
}

// Successful asymmetric literal addition (ALA) step.

internal fun Internal.asymmetricLiteralAddition(lit: Int, coveror: Coveror) {
    requireMode(Internal.COVER)
    check(level == 1) { "cover: level not one" }
    check(vals[vsize + lit].toInt() == 0) { "cover: asymmetric literal assigned" }
    check(vals[vsize - lit].toInt() == 0) { "cover: asymmetric literal negation assigned" }
    setVal(lit, -1)
    coveror.added.add(lit)
    coveror.alas++
    coveror.next.covered = 0
}

/*------------------------------------------------------------------------*/

// In essence copied and adapted from 'propagate' in 'propagate.cpp'. Since
// this function is also a hot-spot here in 'cover' we specialize it in the
// same spirit as 'probe_propagate' and 'vivify_propagate'.  Please refer to
// the detailed comments for 'propagate' in 'propagate.cpp' for details.

internal fun Internal.coverPropagateAsymmetric(lit: Int, ignore: Clause, coveror: Coveror): Boolean {
    requireMode(Internal.COVER)
    stats.propagations.cover++
    check(value(lit) < 0) { "cover: propagating non-false literal" }
    var subsumed = false
    val ws = watches(lit)
    val eow = ws.size
    var j = 0
    var i = j
    while (!subsumed && i != eow) {
        // 'const Watch w = *j++ = *i++': the slot 'j - 1' and 'w' are the same object here,
        // which is fine since 'w' is not read after a write to 'j[-1]'.
        val w = ws[i++]
        ws[j++] = w
        if (w.clause === ignore) continue // costly but necessary here ...
        val b = value(w.blit)
        if (b > 0) continue
        if (w.clause.garbage) {
            j--
        } else if (w.binary()) {
            if (b < 0) {
                subsumed = true
            } else {
                asymmetricLiteralAddition(-w.blit, coveror)
            }
        } else {
            val lits = w.clause.literals
            val other = lits[0] xor lits[1] xor lit
            lits[0] = other
            lits[1] = lit
            val u = value(other)
            if (u > 0) {
                ws[j - 1].blit = other
            } else {
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
                    check(w.clause.pos <= size) { "cover: watch position out of range" }
                    while (k != middle) {
                        r = lits[k]
                        v = value(r)
                        if (v >= 0) break
                        k++
                    }
                }
                w.clause.pos = k
                check(2 <= k) { "cover: watch position below two" }
                check(k <= w.clause.size) { "cover: watch position beyond end" }
                if (v > 0) {
                    ws[j - 1].blit = r
                } else if (v == 0) {
                    lits[1] = r
                    lits[k] = lit
                    watchLiteral(r, lit, w.clause)
                    j--
                } else if (u == 0) {
                    check(v < 0) { "cover: replacement not false" }
                    asymmetricLiteralAddition(-other, coveror)
                } else {
                    check(u < 0) { "cover: other watch not false" }
                    check(v < 0) { "cover: replacement not false" }
                    subsumed = true
                    break
                }
            }
        }
    }
    if (j != i) {
        while (i != eow) ws[j++] = ws[i++]
        ws.shrinkTo(j)
    }
    return subsumed
}

// Covered literal addition (which needs full occurrence lists).  The
// function returns 'true' if the extended clause is blocked on 'lit.'

internal fun Internal.coverPropagateCovered(lit: Int, coveror: Coveror): Boolean {
    requireMode(Internal.COVER)

    check(value(lit) < 0) { "cover: covered propagation of non-false literal" }
    if (frozen(lit)) {
        // no covered propagation on frozen literal
        return false
    }

    stats.propagations.cover++

    check(coveror.intersection.isEmpty()) { "cover: intersection not empty" }

    val os = occs(-lit)
    val end = os.size
    var first = true

    // Compute the intersection of the literals in all the clauses with
    // '-lit'.  If all these clauses are double satisfied then we know that
    // the extended clauses (in 'added') is blocked.  All literals in the
    // intersection can be added as covered literal. As soon the intersection
    // becomes empty (during traversal of clauses with '-lit') we abort.

    var i = 0
    while (i != end) {

        val c = os[i]
        if (c.garbage) {
            i++
            continue
        }

        // First check whether clause is 'blocked', i.e., is double satisfied.

        var blocked = false
        for (k in 0 until c.size) {
            val other = c.literals[k]
            if (other == -lit) continue
            val tmp = value(other)
            if (tmp < 0) continue
            if (tmp > 0) {
                blocked = true
                break
            }
        }
        if (blocked) { // ... if 'c' is double satisfied.
            i++
            continue // with next clause with '-lit'.
        }

        if (first) {

            // Copy and mark literals of first clause.

            for (k in 0 until c.size) {
                val other = c.literals[k]
                if (other == -lit) continue
                val tmp = value(other)
                if (tmp < 0) continue
                check(tmp == 0) { "cover: unexpected true literal" }
                coveror.intersection.add(other)
                mark(other)
            }

            first = false

        } else {

            // Unmark all literals in current clause.

            for (k in 0 until c.size) {
                val other = c.literals[k]
                if (other == -lit) continue
                var tmp = value(other)
                if (tmp < 0) continue
                check(tmp == 0) { "cover: unexpected true literal" }
                tmp = marked(other)
                if (tmp > 0) unmark(other)
            }

            // Then remove from intersection all marked literals.

            val iend = coveror.intersection.size
            var j = 0
            for (k in j until iend) {
                val other = coveror.intersection[k]
                coveror.intersection[j++] = other
                val tmp = marked(other)
                check(tmp >= 0) { "cover: negatively marked intersection literal" }
                if (tmp != 0) {
                    j--
                    unmark(other) // remove marked and unmark it
                } else {
                    mark(other) // keep unmarked and mark it
                }
            }
            val newSize = j
            coveror.intersection.resize(newSize)

            if (!coveror.intersection.isEmpty()) {
                i++
                continue
            }

            // No covered literal addition candidates in the intersection left!
            // Move this clause triggering early abort to the beginning.
            // This is a common move to front strategy to minimize effort.

            val begin = 0
            while (i != begin) {
                val prev = i - 1
                os[i] = os[prev]
                i = prev
            }
            os[begin] = c

            break // early abort ...
        }
        i++
    }

    var res = false
    if (first) {
        check(coveror.intersection.isEmpty()) { "cover: intersection not empty" }
        coverPushExtension(lit, coveror)
        res = true
    } else if (coveror.intersection.isEmpty()) {
        // empty intersection of resolution candidate literals
    } else {
        coveredLiteralAddition(lit, coveror)
        unmark(coveror.intersection)
        coveror.intersection.clear()
        coveror.next.covered = 0 // Restart covering.
    }

    unmark(coveror.intersection)
    coveror.intersection.clear()

    return res
}

/*------------------------------------------------------------------------*/

internal fun Internal.coverClause(c: Clause, coveror: Coveror): Boolean {

    requireMode(Internal.COVER)
    check(!c.garbage) { "cover: garbage clause" }

    var satisfied = false
    for (k in 0 until c.size) if (value(c.literals[k]) > 0) satisfied = true

    if (satisfied) {
        markGarbage(c)
        return false
    }

    check(coveror.added.isEmpty()) { "cover: added not empty" }
    check(coveror.extend.isEmpty()) { "cover: extend not empty" }
    check(coveror.covered.isEmpty()) { "cover: covered not empty" }

    check(level == 0) { "cover: not at root level" }
    level = 1
    for (k in 0 until c.size) {
        val lit = c.literals[k]
        if (value(lit) != 0) continue
        asymmetricLiteralAddition(lit, coveror)
        coveror.covered.add(lit)
    }

    var tautological = false

    coveror.next.covered = 0
    coveror.next.added = 0

    while (!tautological) {
        if (coveror.next.added < coveror.added.size) {
            val lit = coveror.added[coveror.next.added++]
            tautological = coverPropagateAsymmetric(lit, c, coveror)
        } else if (coveror.next.covered < coveror.covered.size) {
            val lit = coveror.covered[coveror.next.covered++]
            tautological = coverPropagateCovered(lit, coveror)
        } else {
            break
        }
    }

    if (tautological) {
        if (coveror.extend.isEmpty()) {
            stats.cover.asymmetric++
            stats.cover.total++
        } else {
            stats.cover.blocked++
            stats.cover.total++
            val ext = external!!
            // Only copy extension stack if successful.
            var prev = Int.MIN_VALUE
            var alreadyPushed = false
            var lastId = 0L
            check(clause.isEmpty()) { "cover: clause not empty" }
            for (e in 0 until coveror.extend.size) {
                val other = coveror.extend[e]
                if (prev == 0) {
                    // are we finishing a clause?
                    if (alreadyPushed) {
                        // add missing literals that are not needed for covering
                        // but avoid RAT proofs
                        var i = 0
                        var j = 0
                        while (i < c.size) {
                            val lit = c.literals[i]
                            if (j >= coveror.covered.size ||
                                c.literals[i] != coveror.covered[j]
                            ) {
                                --j
                                clause.add(lit)
                                ext.pushClauseLiteralOnExtensionStack(lit)
                            }
                            ++i
                            ++j
                        }
                    }
                    val p = proof
                    if (p != null && alreadyPushed) {
                        if (lrat) lratChain.add(c.id)
                        p.addDerivedClause(lastId, false, clause, lratChain)
                        p.weakenPlus(lastId, clause)
                        lratChain.clear()
                    }
                    lastId = ++clauseId
                    ext.pushZeroOnExtensionStack()
                    ext.pushWitnessLiteralOnExtensionStack(other)
                    ext.pushZeroOnExtensionStack()
                    ext.pushIdOnExtensionStack(lastId)
                    ext.pushZeroOnExtensionStack()
                    clause.clear()
                    alreadyPushed = true
                }
                if (other != 0) {
                    ext.pushClauseLiteralOnExtensionStack(other)
                    clause.add(other)
                }
                prev = other
            }

            val p = proof
            if (p != null) {
                // add missing literals that are not needed for covering
                // but avoid RAT proofs
                var i = 0
                var j = 0
                while (i < c.size) {
                    val lit = c.literals[i]
                    if (j >= coveror.covered.size ||
                        c.literals[i] != coveror.covered[j]
                    ) {
                        --j
                        clause.add(lit)
                        ext.pushClauseLiteralOnExtensionStack(lit)
                    }
                    ++i
                    ++j
                }
                if (lrat) lratChain.add(c.id)
                p.addDerivedClause(lastId, false, clause, lratChain)
                p.weakenPlus(lastId, clause)
                lratChain.clear()
            }
            clause.clear()

            markGarbage(c)
        }
    }

    // Backtrack and 'unassign' all literals.

    check(level == 1) { "cover: level not one after covering" }
    for (k in 0 until coveror.added.size) setVal(coveror.added[k], 0)
    level = 0

    coveror.covered.clear()
    coveror.extend.clear()
    coveror.added.clear()

    return tautological
}

/*------------------------------------------------------------------------*/

// Not yet tried and larger clauses are tried first.

private val clauseCoveredOrSmaller = Less<Clause> { a, b ->
    if (a.covered && !b.covered) true
    else if (!a.covered && b.covered) false
    else a.size < b.size
}

internal fun Internal.coverRound(): Long {

    if (unsat) return 0

    initWatches()
    connectWatches(true) // irredundant watches only is enough

    var delta = stats.propagations.search
    delta = (delta.toDouble() * (1e-3 * opts.coverreleff)).toLong()
    if (delta < opts.covermineff) delta = opts.covermineff.toLong()
    if (delta > opts.covermaxeff) delta = opts.covermaxeff.toLong()
    delta = maxOf(delta, 2L * active())

    val limit = stats.propagations.cover + delta

    initOccs()

    val schedule = ArrayList<Clause>()
    val coveror = Coveror()

    // First connect all clauses and find all not yet tried clauses.
    //
    for (c in clauses) {
        check(!c.frozen) { "cover: frozen clause" }
        if (c.garbage) continue
        if (c.redundant) continue
        var satisfied = false
        var allfrozen = true
        for (k in 0 until c.size) {
            val lit = c.literals[k]
            if (value(lit) > 0) {
                satisfied = true
                break
            } else if (allfrozen && !frozen(lit)) {
                allfrozen = false
            }
        }
        if (satisfied) {
            markGarbage(c)
            continue
        }
        if (allfrozen) {
            c.frozen = true
            continue
        }
        for (k in 0 until c.size) occs(c.literals[k]).add(c)
        if (c.size < opts.coverminclslim) continue
        if (c.size > opts.covermaxclslim) continue
        if (c.covered) continue
        schedule.add(c)
    }

    if (schedule.isEmpty()) {

        // no previously untried clause left

        for (c in clauses) {
            if (c.garbage) continue
            if (c.redundant) continue
            if (c.frozen) {
                c.frozen = false
                continue
            }
            if (c.size < opts.coverminclslim) continue
            if (c.size > opts.covermaxclslim) continue
            check(c.covered) { "cover: untried clause in second schedule" }
            c.covered = false
            schedule.add(c)
        }
    } else { // Mix of tried and not tried clauses ....

        for (c in clauses) {
            if (c.garbage) continue
            if (c.redundant) continue
            if (c.frozen) {
                c.frozen = false
                continue
            }
            if (c.size < opts.coverminclslim) continue
            if (c.size > opts.covermaxclslim) continue
            if (!c.covered) continue
            schedule.add(c)
        }
    }

    stableSort(schedule, clauseCoveredOrSmaller)

    // Heuristically it should be beneficial to intersect with smaller clauses
    // first, since then the chances are higher that the intersection of
    // resolution candidates becomes emptier earlier.

    for (lit in lits) {
        if (!active(lit)) continue
        val os = occs(lit)
        stableSort(os, clauseSmallerSize)
    }

    // This is the main loop of trying to do CCE of candidate clauses.
    //
    var covered = 0L
    //
    while (!terminatedAsynchronously() && schedule.isNotEmpty() &&
        stats.propagations.cover < limit
    ) {
        val c = schedule.last()
        schedule.removeAt(schedule.size - 1)
        c.covered = true
        if (coverClause(c, coveror)) covered++
    }

    resetOccs()
    resetWatches()

    return covered
}

/*------------------------------------------------------------------------*/

internal fun Internal.cover(): Boolean = tracePhase("cover") {

    if (opts.cover == 0) return false
    if (unsat) return false
    if (terminatedAsynchronously()) return false
    if (stats.current.irredundant == 0L) return false

    // TODO: Our current algorithm for producing the necessary clauses on the
    // reconstruction stack for extending the witness requires a covered
    // literal addition step which (empirically) conflicts with flushing
    // during restoring clauses (see 'regr00{48,51}.trace') even though
    // flushing during restore is disabled by default (as is covered clause
    // elimination).  The consequence of combining these two options
    // ('opts.cover' and 'opts.restoreflush') can thus produce incorrect
    // witness reconstruction and thus invalid witnesses.  This is quite
    // infrequent (one out of half billion mobical test cases) but as the two
    // regression traces show, does happen. Thus we disable the combination.
    //
    if (opts.restoreflush != 0) return false

    startSimplifier(Internal.COVER)

    stats.cover.count++

    // During variable elimination unit clauses can be generated which need to
    // be propagated properly over redundant clauses too.  Since variable
    // elimination avoids to have occurrence lists and watches at the same
    // time this propagation is delayed until the end of variable elimination.
    // Since we want to interleave CCE with it, we have to propagate here.
    // Otherwise this triggers inconsistencies.
    //
    if (propagated < trail.size) {
        initWatches()
        connectWatches() // need to propagated over all clauses!
        if (!propagate()) {
            learnEmptyClause()
            check(unsat) { "cover: not unsat after empty clause" }
        }
        resetWatches()
    }
    check(unsat || propagated == trail.size) { "cover: units not propagated" }

    val covered = coverRound()

    stopSimplifier(Internal.COVER)
    // report ('c', !opts.reportall && !covered) dropped (message output).

    covered != 0L
}
