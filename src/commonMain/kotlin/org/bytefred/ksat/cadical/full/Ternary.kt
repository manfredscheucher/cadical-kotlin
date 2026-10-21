package org.bytefred.ksat.cadical.full

/*
 * ternary.cpp
 *
 * Mapping:
 *  - Range-for over occurrence lists -> index loops with the end fixed at loop start (the
 *    cached end iterator). The lists iterated in 'ternary_lit' ('occs (pivot)',
 *    'occs (-pivot)') never receive the new resolvent (it contains neither 'pivot' nor
 *    '-pivot'), as upstream relies on.
 *  - 'steps_limit *= 1e-3 * opts.ternaryreleff' and 'htrs_limit *= opts.ternarymaxadd' are
 *    'int64_t *= double' / 'int64_t *= int' as upstream.
 *  - 'int old_htrs2 = stats.htrs2' truncates to int as upstream.
 *  - LOG / PHASE / report are dropped (PORTING.md); locals only feeding them are dropped.
 */

/*------------------------------------------------------------------------*/

// This procedure can be used to produce all possible hyper ternary
// resolvents from ternary clauses.  In contrast to hyper binary resolution
// we would only try to produce ternary clauses from ternary clauses, i.e.,
// do not consider quaternary clauses as antecedents.  Of course if a binary
// clause is generated we keep it too.  In any case we have to make sure
// though that we do not add clauses which are already in the formula or are
// subsumed by a binary clause in the formula.  This procedure simulates
// structural hashing for multiplexer (if-then-else) and binary XOR gates in
// combination with equivalent literal substitution ('decompose') if run
// until to completion (which in the current implementation is too costly
// though and would need to be interleaved more eagerly with equivalent
// literal substitution).  For more information see our CPAIOR'13 paper.

/*------------------------------------------------------------------------*/

// Check whether a binary clause consisting of the permutation of the given
// literals already exists.

internal fun Internal.ternaryFindBinaryClause(a: Int, b: Int): Boolean {
    check(occurring()) { "ternary_find_binary_clause: occurring" }
    check(active(a)) { "ternary_find_binary_clause: a" }
    check(active(b)) { "ternary_find_binary_clause: b" }
    val s = occs(a).size
    val t = occs(b).size
    val lit = if (s < t) a else b
    if (opts.ternaryocclim < occs(lit).size) return true
    val os = occs(lit)
    val end = os.size
    for (k in 0 until end) {
        val c = os[k]
        if (c.size != 2) continue
        val lits = c.literals
        if (lits[0] == a && lits[1] == b) return true
        if (lits[0] == b && lits[1] == a) return true
    }
    return false
}

/*------------------------------------------------------------------------*/

// Check whether a ternary clause consisting of the permutation of the given
// literals already exists or is subsumed by an existing binary clause.

internal fun Internal.ternaryFindTernaryClause(a: Int, b: Int, c: Int): Boolean {
    check(occurring()) { "ternary_find_ternary_clause: occurring" }
    check(active(a)) { "ternary_find_ternary_clause: a" }
    check(active(b)) { "ternary_find_ternary_clause: b" }
    check(active(c)) { "ternary_find_ternary_clause: c" }
    val r = occs(a).size
    val s = occs(b).size
    val t = occs(c).size
    val lit: Int
    if (r < s) lit = if (t < r) c else a
    else lit = if (t < s) c else b
    if (opts.ternaryocclim < occs(lit).size) return true
    val os = occs(lit)
    val end = os.size
    for (k in 0 until end) {
        val d = os[k]
        val lits = d.literals
        if (d.size == 2) {
            if (lits[0] == a && lits[1] == b) return true
            if (lits[0] == b && lits[1] == a) return true
            if (lits[0] == a && lits[1] == c) return true
            if (lits[0] == c && lits[1] == a) return true
            if (lits[0] == b && lits[1] == c) return true
            if (lits[0] == c && lits[1] == b) return true
        } else {
            check(d.size == 3) { "ternary_find_ternary_clause: size" }
            if (lits[0] == a && lits[1] == b && lits[2] == c) return true
            if (lits[0] == a && lits[1] == c && lits[2] == b) return true
            if (lits[0] == b && lits[1] == a && lits[2] == c) return true
            if (lits[0] == b && lits[1] == c && lits[2] == a) return true
            if (lits[0] == c && lits[1] == a && lits[2] == b) return true
            if (lits[0] == c && lits[1] == b && lits[2] == a) return true
        }
    }
    return false
}

/*------------------------------------------------------------------------*/

// Try to resolve the two ternary clauses on the given pivot (assumed to
// occur positively in the first clause, negatively in the second).  If the
// resolvent has four literals, is tautological, already exists or in the
// case of a ternary resolvent is subsumed by an existing binary clause then
// 'false' is returned.  The global 'clause' contains the resolvent and
// needs to be cleared in any case.

internal fun Internal.hyperTernaryResolve(c: Clause, pivot: Int, d: Clause): Boolean {
    stats.ternres++
    check(c.size == 3) { "hyper_ternary_resolve: c size" }
    check(d.size == 3) { "hyper_ternary_resolve: d size" }
    check(clause.isEmpty()) { "hyper_ternary_resolve: clause" }
    for (k in 0 until c.size) {
        val lit = c.literals[k]
        if (lit != pivot) clause.add(lit)
    }
    for (k in 0 until d.size) {
        val lit = d.literals[k]
        if (lit == -pivot) continue
        if (lit == clause[0]) continue
        if (lit == -clause[0]) return false
        if (lit == clause[1]) continue
        if (lit == -clause[1]) return false
        clause.add(lit)
    }
    val size = clause.size
    if (size > 3) return false
    if (size == 2 && ternaryFindBinaryClause(clause[0], clause[1])) return false
    if (size == 3 && ternaryFindTernaryClause(clause[0], clause[1], clause[2])) return false
    return true
}

/*------------------------------------------------------------------------*/

// Produce all ternary resolvents on literal 'pivot' and increment the
// 'steps' counter by the number of clauses containing 'pivot' which are
// used during this process.  The reason for choosing this metric to measure
// the effort spent in 'ternary' is that it should be similar to one
// propagation step during search.

internal fun Internal.ternaryLit(pivot: Int, steps: LongRef, htrs: LongRef) {
    val cs = occs(pivot)
    val cend = cs.size
    for (ci in 0 until cend) {
        val c = cs[ci]
        if (htrs.value < 0) break
        if (c.garbage) continue
        if (c.size != 3) {
            check(c.size == 2) { "ternary_lit: c size" }
            continue
        }
        if (--steps.value < 0) break
        var assigned = false
        for (k in 0 until c.size) {
            val lit = c.literals[k]
            if (value(lit) != 0) {
                assigned = true
                break
            }
        }
        if (assigned) continue
        // Note: 'assigned' is not reset per 'd', exactly as upstream.
        val ds = occs(-pivot)
        val dend = ds.size
        for (di in 0 until dend) {
            val d = ds[di]
            if (htrs.value < 0) break
            if (d.garbage) continue
            if (d.size != 3) {
                check(d.size == 2) { "ternary_lit: d size" }
                continue
            }
            for (k in 0 until d.size) {
                val lit = d.literals[k]
                if (value(lit) != 0) {
                    assigned = true
                    break
                }
            }
            if (assigned) continue
            check(clause.isEmpty()) { "ternary_lit: clause" }
            htrs.value--
            if (hyperTernaryResolve(c, pivot, d)) {
                val size = clause.size
                val red = (size == 3 || (c.redundant && d.redundant))
                if (lrat) {
                    check(lratChain.isEmpty()) { "ternary_lit: lrat_chain" }
                    lratChain.add(c.id)
                    lratChain.add(d.id)
                }
                val r = newHyperTernaryResolvedClause(red)
                if (red) r.hyper = true
                lratChain.clear()
                clause.clear()
                stats.htrs++
                for (k in 0 until r.size) {
                    val lit = r.literals[k]
                    occs(lit).add(r)
                }
                if (size == 2) {
                    markGarbage(c)
                    markGarbage(d)
                    stats.htrs2++
                    break
                } else {
                    check(r.size == 3) { "ternary_lit: r size" }
                    stats.htrs3++
                }
            } else {
                clause.clear()
            }
        }
    }
}

/*------------------------------------------------------------------------*/

// Same as 'ternary_lit' but pick the phase of the variable based on the
// number of positive and negative occurrence.

internal fun Internal.ternaryIdx(idx: Int, steps: LongRef, htrs: LongRef) {
    check(0 < idx) { "ternary_idx: idx" }
    check(idx <= maxVar) { "ternary_idx: idx max" }
    if (!active(idx)) return
    if (!flags(idx).ternary) return
    val pos = occs(idx).size
    val neg = occs(-idx).size
    if (pos <= opts.ternaryocclim && neg <= opts.ternaryocclim) {
        val pivot = (if (neg < pos) -idx else idx)
        ternaryLit(pivot, steps, htrs)
    }
    flags(idx).ternary = false
}

/*------------------------------------------------------------------------*/

// One round of ternary resolution over all variables.  As in 'block' and
// 'elim' we maintain a persistent global flag 'ternary' for each variable,
// which records, whether a ternary clause containing it was added.  Then we
// can focus on those variables for which we have not tried ternary
// resolution before and nothing changed for them since then.  This works
// across multiple calls to 'ternary' as well as 'ternary_round' since this
// 'ternary' variable flag is updated during adding (ternary) resolvents.
// This function goes over each variable just once.

internal fun Internal.ternaryRound(steps: LongRef, htrs: LongRef): Boolean {
    val stepsLimit = steps
    val htrsLimit = htrs

    check(!unsat) { "ternary_round: unsat" }

    initOccs()

    for (c in clauses) {
        if (c.garbage) continue
        if (c.size > 3) continue
        var assigned = false
        var marked = false
        for (k in 0 until c.size) {
            val lit = c.literals[k]
            if (value(lit) != 0) {
                assigned = true
                break
            }
            if (flags(lit).ternary) marked = true
        }
        if (assigned) continue
        if (c.size == 2) {
            // bincon++ (message only)
        } else {
            check(c.size == 3) { "ternary_round: size" }
            if (!marked) continue
            // terncon++ (message only)
        }

        for (k in 0 until c.size) {
            val lit = c.literals[k]
            occs(lit).add(c)
        }
    }

    // Try ternary resolution on all variables once.
    //
    for (idx in 1..maxVar) {
        if (terminatedAsynchronously()) break
        if (stepsLimit.value < 0) break
        if (htrsLimit.value < 0) break
        ternaryIdx(idx, stepsLimit, htrsLimit)
    }

    // Gather some statistics for the verbose messages below and also
    // determine whether new variables have been marked and it would make
    // sense to run another round of ternary resolution over those variables.
    //
    var remain = 0
    for (idx in 1..maxVar) {
        if (!active(idx)) continue
        if (!flags(idx).ternary) continue
        remain++
    }

    resetOccs()
    check(!unsat) { "ternary_round: unsat after" }

    return remain != 0 // Are there variables that should be tried again?
}

/*------------------------------------------------------------------------*/

internal fun Internal.ternary(): Boolean = tracePhase("ternary") {

    if (opts.ternary == 0) return false
    if (unsat) return false
    if (terminatedAsynchronously()) return false

    // No new ternary clauses added since last time?
    //
    if (last.ternary.marked == stats.mark.ternary) return false

    startSimplifier(Internal.TERNARY)
    stats.ternary++

    check(level == 0) { "ternary: level" }

    check(!unsat) { "ternary: unsat" }
    if (watching()) resetWatches()

    // The number of steps (see comment to 'ternary_lit' above) is global to
    // all rounds of producing ternary resolvents on all marked variables in
    // this call to the 'ternary' procedure.
    //
    var stepsLimit = stats.propagations.search
    stepsLimit = (stepsLimit * (1e-3 * opts.ternaryreleff)).toLong()
    if (stepsLimit < opts.ternarymineff) stepsLimit = opts.ternarymineff.toLong()
    if (stepsLimit > opts.ternarymaxeff) stepsLimit = opts.ternarymaxeff.toLong()

    // The number of clauses derived through ternary resolution can grow
    // substantially, particularly for random formulas.  Thus we limit the
    // number of added clauses too (actually the number of 'htrs').
    //
    var htrsLimit = stats.current.redundant + stats.current.irredundant
    htrsLimit *= opts.ternarymaxadd
    htrsLimit /= 100

    // With 'stats.ternary' we actually count the number of calls to
    // 'ternary_round' and not the number of calls to 'ternary'. But before
    // the first round we want to show the limit on the number of steps and
    // thus we increase counter for the first round here and skip increasing
    // it in the loop below.

    val steps = LongRef(stepsLimit)
    val htrs = LongRef(htrsLimit)

    var resolvedBinaryClause = false
    var completed = false

    var round = 0
    while (!terminatedAsynchronously() && round < opts.ternaryrounds) {
        if (htrs.value < 0) break
        if (steps.value < 0) break
        if (round != 0) stats.ternary++
        val oldHtrs2 = stats.htrs2.toInt()
        val oldHtrs3 = stats.htrs3.toInt()
        completed = ternaryRound(steps, htrs)
        val deltaHtrs2 = (stats.htrs2 - oldHtrs2).toInt()
        val deltaHtrs3 = (stats.htrs3 - oldHtrs3).toInt()
        // report ('3', ...) dropped.
        if (deltaHtrs2 != 0) resolvedBinaryClause = true
        if (deltaHtrs3 == 0) break
        round++
    }

    check(!occurring()) { "ternary: occurring" }
    check(!unsat) { "ternary: unsat after" }
    initWatches()
    connectWatches()
    if (!propagate()) {
        learnEmptyClause()
    }

    if (completed) last.ternary.marked = stats.mark.ternary

    stopSimplifier(Internal.TERNARY)

    resolvedBinaryClause
}
