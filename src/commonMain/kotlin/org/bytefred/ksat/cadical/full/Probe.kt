package org.bytefred.ksat.cadical.full

import org.bytefred.ksat.cadical.IntArrayList

/*
 * probe.cpp
 *
 * Mapping:
 *  - 'Var *u = &var (l)' with 'swap (u, v)' -> Var references swapped together with the
 *    literals.
 *  - Clause literal iterators ('lits', 'k', 'middle', 'end') -> indices into 'c.literals'.
 *  - Watch iterators in 'probe_propagate' are already indices upstream ('i', 'j'), and the
 *    loop bound 'ws.size ()' is re-read in every iteration as upstream (a hyper binary
 *    resolvent may add a watch to 'ws'). 'const Watch w = ws[j++] = ws[i++]' moves the
 *    reference (see WatchHpp.kt); after 'ws[j - 1].blit = ...' only 'w.clause' is used,
 *    which is not changed.
 *  - Range-for over watch lists in 'probe_propagate2' -> index loop with the end fixed at
 *    loop start (as the cached end iterator).
 *  - 'propfixed (lit) = stats.all.fixed' stores the int64 counter into the 'int' table
 *    (truncation as upstream); comparisons 'propfixed (lit) >= stats.all.fixed' promote the
 *    int to int64.
 *  - 'int old_failed = stats.failed' truncates to int as upstream.
 *  - LOG / PHASE / report are dropped (PORTING.md); locals only feeding them are dropped.
 */

/*------------------------------------------------------------------------*/

// Failed literal probing uses its own propagation and assignment
// functions.  It further provides on-the-fly generation of hyper binary
// resolvents but only probes on roots of the binary implication graph.  The
// search for failed literals is limited, but untried roots are kept until
// the next time 'probe' is called.  Left over probes from the last attempt
// and new probes are tried until the limit is hit or all are tried.

/*------------------------------------------------------------------------*/

internal fun Internal.probing(): Boolean {
    if (opts.probe == 0) return false
    if (!preprocessing && opts.inprocessing == 0) return false
    if (preprocessing) check(lim.preprocessing != 0L) { "probing: preprocessing limit" }
    if (stats.probingphases != 0L && last.probe.reductions == stats.reductions) return false
    return lim.probe <= stats.conflicts
}

/*------------------------------------------------------------------------*/

internal fun Internal.getParentReasonLiteral(lit: Int): Int {
    val idx = vidx(lit)
    var res = parents[idx]
    if (lit < 0) res = -res
    return res
}

internal fun Internal.setParentReasonLiteral(lit: Int, reason: Int) {
    var r = reason
    val idx = vidx(lit)
    if (lit < 0) r = -r
    parents[idx] = r
}

/*-----------------------------------------------------------------------*/

// for opts.probehbr=false we need to do a lot of extra work to remember the
// correct lrat_chains... This solution is also memory intensive I think
// all corresponding functions are guarded to only work with the right
// options so they can be called without checking for options
//
// call locally after failed_literal or backtracking
//
internal fun Internal.cleanProbehbrLrat() {
    if (!lrat || opts.probehbr != 0) return
    for (field in probehbrChains) {
        for (chain in field) {
            chain.clear()
        }
    }
}

// call globally before a probe round (or a lookahead round)
//
internal fun Internal.initProbehbrLrat() {
    if (!lrat || opts.probehbr != 0) return
    val size = 2 * (1 + maxVar)
    probehbrChains.resize(size) { ArrayList() }
    for (i in 0 until size) {
        probehbrChains[i].resize(size) { ArrayList() }
        // commented because not needed... should be empty already
    }
}

// sets lrat_chain to the stored chain in probehbr_chains.
// this leads to conflict with unit reason uip
//
internal fun Internal.getProbehbrLrat(lit: Int, uip: Int) {
    if (!lrat || opts.probehbr != 0) return
    check(lit != 0) { "get_probehbr_lrat: lit" }
    check(lratChain.isEmpty()) { "get_probehbr_lrat: lrat_chain" }
    check(value(uip) < 0) { "get_probehbr_lrat: uip" }
    lratChain.clear()
    lratChain.addAll(probehbrChains[vlit(lit)][vlit(uip)])
    lratChain.add(unitClauses(vlit(-uip)))
}

// sets the corresponding probehbr_chain to what is currently stored in
// lrat_chain. also clears lrat_chain.
//
internal fun Internal.setProbehbrLrat(lit: Int, uip: Int) {
    if (!lrat || opts.probehbr != 0) return
    check(lit != 0) { "set_probehbr_lrat: lit" }
    check(lratChain.size != 0) { "set_probehbr_lrat: lrat_chain" }
    check(probehbrChains[vlit(lit)][vlit(uip)].isEmpty()) { "set_probehbr_lrat: chain" }
    val dst = probehbrChains[vlit(lit)][vlit(uip)]
    dst.clear()
    dst.addAll(lratChain)
    lratChain.clear()
}

// compute lrat_chain for the part of the tree from lit to dom
// use mini_chain because it needs to be reversed
//
internal fun Internal.probeDominatorLrat(dom: Int, reason: Clause) {
    if (!lrat || dom == 0) return
    for (k in 0 until reason.size) {
        val lit = reason.literals[k]
        if (value(lit) >= 0) continue
        val other = -lit
        if (other == dom) continue
        val f = flags(other)
        if (f.seen) continue
        f.seen = true
        analyzed.add(other)
        // 'Var u = var (other)' is a copy upstream; it is only read here.
        val u = variable(other)
        if (u.level != 0) {
            val uReason = u.reason
            if (uReason == null) {
                continue
            }
            probeDominatorLrat(dom, uReason)
            continue
        }
        val uidx = vlit(other)
        val id = unitClauses(uidx)
        check(id != 0L) { "probe_dominator_lrat: unit id" }
        lratChain.add(id)
    }
    lratChain.add(reason.id)
}

/*------------------------------------------------------------------------*/

// On-the-fly (dynamic) hyper binary resolution on decision level one can
// make use of the fact that the implication graph is actually a tree.

// Compute a dominator of two literals in the binary implication tree.

internal fun Internal.probeDominator(a: Int, b: Int): Int {
    requireMode(Internal.PROBE)
    var l = a
    var k = b
    var u = variable(l)
    var v = variable(k)
    check(value(l) > 0) { "probe_dominator: l" }
    check(value(k) > 0) { "probe_dominator: k" }
    check(u.level == 1) { "probe_dominator: u level" }
    check(v.level == 1) { "probe_dominator: v level" }
    while (l != k) {
        if (u.trail > v.trail) {
            val tl = l
            l = k
            k = tl
            val tu = u
            u = v
            v = tu
        }
        if (getParentReasonLiteral(l) == 0) return l
        val parent = getParentReasonLiteral(k)
        check(parent != 0) { "probe_dominator: parent" }
        check(value(parent) > 0) { "probe_dominator: parent value" }
        k = parent
        v = variable(k)
        check(v.level == 1) { "probe_dominator: parent level" }
    }
    check(value(l) > 0) { "probe_dominator: result" }
    return l
}

// The idea of dynamic on-the-fly hyper-binary resolution came up in the
// PrecoSAT solver, where it originally was used on all decision levels.

// It turned out, that most of the hyper-binary resolvents were generated
// during probing on decision level one anyhow.  Thus this version is
// specialized to decision level one, where actually all long (non-binary)
// forcing clauses can be resolved to become binary.  So if we find a clause
// which would force a new assignment at decision level one during probing
// we resolve it (the 'reason' argument) to obtain a hyper binary resolvent.
// It consists of the still unassigned literal (the new unit) and the
// negation of the unique closest dominator of the negation of all (false)
// literals in the clause (which has to exist on decision level one).

// There are two special cases which should be mentioned:
//
//   (A) The reason is already a binary clause in a certain sense, since all
//   its unwatched literals are root level fixed to false.  In this
//   situation it would be better to shrink the clause immediately instead
//   of adding a new clause consisting only of the watched literals.
//   However, this would happen during the next garbage collection anyhow.
//
//   (B) The resolvent subsumes the original reason clause. This is
//   equivalent to the property that the negated dominator is contained in
//   the original reason.  Again one could in principle shrink the clause.
//
// Note that (A) is actually subsumed by (B).  The possible optimization to
// shrink the clause on-the-fly is difficult (need to update 'blit' and
// 'binary' of the other watch at least) and also not really that important.
// For (B) we simply add the new binary resolvent and mark the old subsumed
// clause as garbage instead.  And since in the situation of (A) the
// shrinking will be performed at the next  garbage collection anyhow, we
// do not change clauses in (A).

// The hyper binary resolvent clause is redundant unless it subsumes the
// original reason and that one is irredundant.

// If the option 'opts.probehbr' is 'false', we actually do not add the new
// hyper binary resolvent, but simply pretend we would have added it and
// still return the dominator as new reason / parent for the new unit.

// Finally note that adding clauses changes the watches of the propagated
// literal and thus we can not use standard iterators during probing but
// need to fall back to indices.  One watch for the hyper binary resolvent
// clause is added at the end of the currently propagated watches, but its
// watch is a binary watch and will be skipped during propagating long
// clauses anyhow.

internal fun Internal.hyperBinaryResolve(reason: Clause): Int {
    requireMode(Internal.PROBE)
    check(level == 1) { "hyper_binary_resolve: level" }
    check(reason.size > 2) { "hyper_binary_resolve: size" }
    val end = reason.size
    val lits = reason.literals
    var k: Int
    // '#ifndef NDEBUG' check (first literal unassigned, all others false): not in release.
    stats.hbrs++
    stats.hbrsizes += reason.size
    val lit = lits[1]
    var dom = -lit
    var nonRootLevelLiterals = 0
    k = 2
    while (k != end) {
        val other = -lits[k]
        check(value(other) > 0) { "hyper_binary_resolve: other" }
        if (variable(other).level == 0) {
            k++
            continue
        }
        dom = probeDominator(dom, other)
        nonRootLevelLiterals++
        k++
    }
    probeReason = reason
    if (nonRootLevelLiterals != 0 && opts.probehbr != 0) { // !(A)
        var contained = false
        k = 1
        while (!contained && k != end) {
            contained = (lits[k] == -dom)
            k++
        }
        val red = !contained || reason.redundant
        if (red) stats.hbreds++
        check(clause.isEmpty()) { "hyper_binary_resolve: clause" }
        clause.add(-dom)
        clause.add(lits[0])
        probeDominatorLrat(dom, reason)
        if (lrat) clearAnalyzedLiterals()
        val c = newHyperBinaryResolvedClause(red, 2)
        probeReason = c
        if (red) c.hyper = true
        clause.clear()
        lratChain.clear()
        if (contained) {
            stats.hbrsubs++
            markGarbage(reason)
        }
    } else if (nonRootLevelLiterals != 0 && lrat) {
        // still calculate LRAT and remember for later
        check(opts.probehbr == 0) { "hyper_binary_resolve: probehbr" }
        probeDominatorLrat(dom, reason)
        clearAnalyzedLiterals()
        setProbehbrLrat(dom, lits[0])
    }
    return dom
}

/*------------------------------------------------------------------------*/

// The following functions 'probe_assign' and 'probe_propagate' are used for
// propagating during failed literal probing in simplification mode, as
// replacement of the generic propagation routine 'propagate' and
// 'search_assign'.

// The code is mostly copied from 'propagate.cpp' and specialized.  We only
// comment on the differences.  More explanations are in 'propagate.cpp'.

internal fun Internal.probeAssign(lit: Int, parent: Int) {
    requireMode(Internal.PROBE)
    val idx = vidx(lit)
    check(value(idx) == 0) { "probe_assign: assigned" }
    check(!flags(idx).eliminated() || parent == 0) { "probe_assign: eliminated" }
    check(parent == 0 || value(parent) > 0) { "probe_assign: parent" }
    val v = variable(idx)
    v.level = level
    v.trail = trail.size
    check(numAssigned < maxVar) { "probe_assign: num_assigned" }
    numAssigned++
    v.reason = if (level != 0) probeReason else null
    probeReason = null
    setParentReasonLiteral(lit, parent)
    if (level == 0) learnUnitClause(lit)
    else check(level == 1) { "probe_assign: level" }
    val tmp = sign(lit)
    setVal(idx, tmp)
    check(value(lit) > 0) { "probe_assign: value" }
    check(value(-lit) < 0) { "probe_assign: negated value" }
    trail.add(lit)

    // Do not save the current phase during inprocessing but remember the
    // number of units on the trail of the last time this literal was
    // assigned.  This allows us to avoid some redundant failed literal
    // probing attempts.  Search for 'propfixed' in 'probe.cpp' for details.
    //
    if (level != 0) ptab[vlit(lit)] = stats.all.fixed.toInt()
}

internal fun Internal.probeAssignDecision(lit: Int) {
    requireMode(Internal.PROBE)
    check(level == 0) { "probe_assign_decision: level" }
    check(propagated == trail.size) { "probe_assign_decision: propagated" }
    level++
    control.add(Level(lit, trail.size))
    probeAssign(lit, 0)
}

internal fun Internal.probeAssignUnit(lit: Int) {
    requireMode(Internal.PROBE)
    check(level == 0) { "probe_assign_unit: level" }
    check(active(lit)) { "probe_assign_unit: inactive" }
    probeAssign(lit, 0)
}

/*------------------------------------------------------------------------*/

// same as in propagate but inlined here
//
internal fun Internal.probeLratForUnits(lit: Int) {
    if (!lrat) return
    if (level != 0) return // not decision level 0
    check(lratChain.isEmpty()) { "probe_lrat_for_units: lrat_chain" }
    val reason = probeReason
    check(reason != null) { "probe_lrat_for_units: probe_reason" }
    for (k in 0 until reason.size) {
        val reasonLit = reason.literals[k]
        if (lit == reasonLit) continue
        check(value(reasonLit) != 0) { "probe_lrat_for_units: unassigned" }
        if (value(reasonLit) == 0) continue
        val uidx = vlit(value(reasonLit) * reasonLit)
        val id = unitClauses(uidx)
        lratChain.add(id)
    }
    lratChain.add(reason.id)
}

/*------------------------------------------------------------------------*/

// This is essentially the same as 'propagate' except that we prioritize and
// always propagate binary clauses first (see our CPAIOR'13 paper on tree
// based look ahead), then immediately stop at a conflict and of course use
// 'probe_assign' instead of 'search_assign'.  The binary propagation part
// is factored out too.  If a new unit on decision level one is found we
// perform hyper binary resolution and thus actually build an implication
// tree instead of a DAG.  Statistics counters are also different.

internal fun Internal.probePropagate2() {
    requireMode(Internal.PROBE)
    while (propagated2 != trail.size) {
        val lit = -trail[propagated2++]
        val ws = watches(lit)
        val end = ws.size
        for (p in 0 until end) {
            val w = ws[p]
            if (!w.binary()) continue
            val b = value(w.blit)
            if (b > 0) continue
            if (b < 0) {
                conflict = w.clause // but continue
            } else {
                check(lratChain.isEmpty()) { "probe_propagate2: lrat_chain" }
                check(probeReason == null) { "probe_propagate2: probe_reason" }
                probeReason = w.clause
                probeLratForUnits(w.blit)
                probeAssign(w.blit, -lit)
                lratChain.clear()
            }
        }
    }
}

internal fun Internal.probePropagate(): Boolean {
    requireMode(Internal.PROBE)
    check(!unsat) { "probe_propagate: unsat" }
    propagated2 = propagated
    val before = propagated2.toLong()
    while (conflict == null) {
        if (propagated2 != trail.size) {
            probePropagate2()
        } else if (propagated != trail.size) {
            val lit = -trail[propagated++]
            val ws = watches(lit)
            var i = 0
            var j = 0
            while (i != ws.size) {
                val w = ws[i++]
                ws[j++] = w
                if (w.binary()) continue
                val b = value(w.blit)
                if (b > 0) continue
                val wc = w.clause
                if (wc.garbage) continue
                val lits = wc.literals
                val other = lits[0] xor lits[1] xor lit
                // lits[0] = other, lits[1] = lit;
                val u = value(other)
                if (u > 0) {
                    ws[j - 1].blit = other
                } else {
                    val size = wc.size
                    val end = size
                    val middle = wc.pos
                    var k = middle
                    var r = 0
                    var v = -1
                    while (k != end) {
                        r = lits[k]
                        v = value(r)
                        if (v >= 0) break
                        k++
                    }
                    if (v < 0) {
                        k = 2
                        check(wc.pos <= size) { "probe_propagate: pos" }
                        while (k != middle) {
                            r = lits[k]
                            v = value(r)
                            if (v >= 0) break
                            k++
                        }
                    }
                    wc.pos = k
                    check(2 <= k) { "probe_propagate: k low" }
                    check(k <= wc.size) { "probe_propagate: k high" }
                    if (v > 0) {
                        ws[j - 1].blit = r
                    } else if (v == 0) {
                        lits[k] = lit
                        lits[0] = other
                        lits[1] = r
                        watchLiteral(r, lit, wc)
                        j--
                    } else if (u == 0) {
                        if (level == 1) {
                            lits[0] = other
                            lits[1] = lit
                            check(lratChain.isEmpty()) { "probe_propagate: lrat_chain" }
                            check(probeReason == null) { "probe_propagate: probe_reason" }
                            val dom = hyperBinaryResolve(wc)
                            probeAssign(other, dom)
                        } else {
                            check(lratChain.isEmpty()) { "probe_propagate: lrat_chain" }
                            check(probeReason == null) { "probe_propagate: probe_reason" }
                            probeReason = wc
                            probeLratForUnits(other)
                            probeAssignUnit(other)
                            lratChain.clear()
                        }
                        probePropagate2()
                    } else {
                        conflict = wc
                    }
                }
            }
            if (j != i) {
                while (i != ws.size) ws[j++] = ws[i++]
                ws.shrinkTo(j)
            }
        } else {
            break
        }
    }
    val delta = propagated2 - before
    stats.propagations.probe += delta
    return conflict == null
}

/*------------------------------------------------------------------------*/

// This a specialized instance of 'analyze'.

internal fun Internal.failedLiteral(lit: Int) {
    val failed = lit

    stats.failed++
    stats.probefailed++

    check(!unsat) { "failed_literal: unsat" }
    val conflictClause = conflict
    check(conflictClause != null) { "failed_literal: no conflict" }
    check(level == 1) { "failed_literal: level" }
    check(analyzed.isEmpty()) { "failed_literal: analyzed" }
    check(lratChain.isEmpty()) { "failed_literal: lrat_chain" }

    var uip = 0
    for (k in 0 until conflictClause.size) {
        val other = -conflictClause.literals[k]
        if (variable(other).level == 0) {
            check(value(other) > 0) { "failed_literal: root literal" }
            continue
        }
        uip = if (uip != 0) probeDominator(uip, other) else other
    }
    probeDominatorLrat(uip, conflictClause)
    if (lrat) clearAnalyzedLiterals()

    check(uip != 0) { "failed_literal: uip" }

    val work = IntArrayList()

    var parent = uip
    while (parent != failed) {
        val next = getParentReasonLiteral(parent)
        parent = next
        check(parent != 0) { "failed_literal: parent" }
        work.add(parent)
    }

    backtrack()
    conflict = null

    check(value(uip) == 0) { "failed_literal: uip assigned" }
    probeAssignUnit(-uip)
    lratChain.clear()

    if (!probePropagate()) learnEmptyClause()

    var j = 0
    while (!unsat && j < work.size) {
        // assert (!opts.probehbr);        assertion fails ...
        val parent = work[j++]
        val tmp = value(parent)
        if (tmp > 0) {
            check(opts.probehbr == 0) { "failed_literal: probehbr (clash)" } // ... assertion should hold here
            getProbehbrLrat(parent, uip)
            learnEmptyClause()
        } else if (tmp == 0) {
            check(opts.probehbr == 0) { "failed_literal: probehbr (unassigned)" } // ... and here
            getProbehbrLrat(parent, uip) // this is computed during
            probeAssignUnit(-parent) // propagation and can include
            lratChain.clear() // multiple chains where only one
            if (!probePropagate()) learnEmptyClause() // is needed!
        }
        uip = parent
    }
    work.clear()

    check(unsat || value(failed) < 0) { "failed_literal: failed not false" }
}

/*------------------------------------------------------------------------*/

internal fun Internal.isBinaryClause(c: Clause, a: IntRef, b: IntRef): Boolean {
    check(level == 0) { "is_binary_clause: level" }
    if (c.garbage) return false
    var first = 0
    var second = 0
    for (k in 0 until c.size) {
        val lit = c.literals[k]
        val tmp = value(lit)
        if (tmp > 0) return false
        if (tmp < 0) continue
        if (second != 0) return false
        if (first != 0) second = lit
        else first = lit
    }
    if (second == 0) return false
    a.value = first
    b.value = second
    return true
}

// We probe on literals first, which occur more often negated and thus we
// sort the 'probes' stack in such a way that literals which occur negated
// less frequently come first.  Probes are taken from the back of the stack.

// 'Type' is 'size_t' (64 bits, the default of IntRank).
private class ProbeNegatedNoccsRank(private val internal: Internal) : IntRank {
    override fun rank(a: Int): Long = internal.noccs(-a)
}

// Fill the 'probes' schedule.

internal fun Internal.generateProbes() {

    check(probes.isEmpty()) { "generate_probes: probes" }

    // First determine all the literals which occur in binary clauses. It is
    // way faster to go over the clauses once, instead of walking the watch
    // lists for each literal.
    //
    initNoccs()
    val a = IntRef()
    val b = IntRef()
    for (c in clauses) {
        if (!isBinaryClause(c, a, b)) continue
        ntab[vlit(a.value)]++
        ntab[vlit(b.value)]++
    }

    for (idx in 1..maxVar) {

        // Then focus on roots of the binary implication graph, which are
        // literals occurring negatively in a binary clause, but not positively.
        // If neither 'idx' nor '-idx' is a root it makes less sense to probe
        // this variable.

        // This argument requires that equivalent literal substitution through
        // 'decompose' is performed, because otherwise there might be 'cyclic
        // roots' which are not tried, i.e., -1 2 0, 1 -2 0, 1 2 3 0, 1 2 -3 0.

        val havePosBinOccs = noccs(idx) > 0
        val haveNegBinOccs = noccs(-idx) > 0

        if (havePosBinOccs == haveNegBinOccs) continue

        val probe = if (haveNegBinOccs) idx else -idx

        // See the discussion where 'propfixed' is used below.
        //
        if (propfixed(probe).toLong() >= stats.all.fixed) continue

        probes.add(probe)
    }

    rsort(probes, ProbeNegatedNoccsRank(this))

    resetNoccs()
}

// Follow the ideas in 'generate_probes' but flush non root probes and
// reorder remaining probes.

internal fun Internal.flushProbes() {

    check(!probes.isEmpty()) { "flush_probes: probes" }

    initNoccs()
    val a = IntRef()
    val b = IntRef()
    for (c in clauses) {
        if (!isBinaryClause(c, a, b)) continue
        ntab[vlit(a.value)]++
        ntab[vlit(b.value)]++
    }

    val eop = probes.size
    var j = 0
    var i = j
    while (i != eop) {
        var lit = probes[i]
        i++
        if (!active(lit)) continue
        val havePosBinOccs = noccs(lit) > 0
        val haveNegBinOccs = noccs(-lit) > 0
        if (havePosBinOccs == haveNegBinOccs) continue
        if (havePosBinOccs) lit = -lit
        check(noccs(lit) == 0L) { "flush_probes: noccs (lit)" }
        check(noccs(-lit) > 0) { "flush_probes: noccs (-lit)" }
        if (propfixed(lit).toLong() >= stats.all.fixed) continue
        probes[j++] = lit
    }
    val remain = j
    probes.resize(remain)

    rsort(probes, ProbeNegatedNoccsRank(this))

    resetNoccs()
}

internal fun Internal.nextProbe(): Int {

    var generated = 0

    while (true) {

        if (probes.isEmpty()) {
            if (generated++ != 0) return 0
            generateProbes()
        }

        while (!probes.isEmpty()) {

            val probe = probes.back()
            probes.removeLast()

            // Eliminated or assigned.
            //
            if (!active(probe)) continue

            // There is now new unit since the last time we propagated this probe,
            // thus we propagated it before without obtaining a conflict and
            // nothing changed since then.  Thus there is no need to propagate it
            // again.  This observation was independently made by Partik Simons
            // et.al. in the context of implementing 'smodels' (see for instance
            // Alg. 4 in his JAIR article from 2002) and it has also been
            // contributed to the thesis work of Yacine Boufkhad.
            //
            if (propfixed(probe).toLong() >= stats.all.fixed) continue

            return probe
        }
    }
}

internal fun Internal.probeRound(): Boolean {

    if (unsat) return false
    if (terminatedAsynchronously()) return false

    startSimplifier(Internal.PROBE)
    stats.probingrounds++

    // Probing is limited in terms of non-probing propagations
    // 'stats.propagations'. We allow a certain percentage 'opts.probereleff'
    // (say %5) of probing propagations in each probing with a lower bound of
    // 'opts.probmineff'.
    //
    var delta = stats.propagations.search
    delta -= last.probe.propagations
    delta = (delta * (1e-3 * opts.probereleff)).toLong()
    if (delta < opts.probemineff) delta = opts.probemineff.toLong()
    if (delta > opts.probemaxeff) delta = opts.probemaxeff.toLong()
    delta += 2L * active()

    val limit = stats.propagations.probe + delta

    val oldFailed = stats.failed.toInt()
    // 'old_probed' and 'old_hbrs' only feed messages and 'report' (dropped).

    if (!probes.isEmpty()) flushProbes()

    // We reset 'propfixed' since there was at least another conflict thus
    // a new learned clause, which might produce new propagations (and hyper
    // binary resolvents).  During 'generate_probes' we keep the old value.
    //
    for (idx in 1..maxVar) {
        ptab[vlit(-idx)] = -1
        ptab[vlit(idx)] = -1
    }

    check(unsat || propagated == trail.size) { "probe_round: propagated" }
    propagated2 = trail.size
    propagated = propagated2

    initProbehbrLrat()
    while (true) {
        if (unsat) break
        if (terminatedAsynchronously()) break
        if (stats.propagations.probe >= limit) break
        val probe = nextProbe()
        if (probe == 0) break
        stats.probed++
        probeAssignDecision(probe)
        if (probePropagate()) backtrack()
        else failedLiteral(probe)
        cleanProbehbrLrat()
    }

    if (unsat) {
        // probing derived empty clause
    } else if (propagated < trail.size) {
        if (!propagate()) {
            learnEmptyClause()
        } else {
            sortWatches()
        }
    }

    val failed = (stats.failed - oldFailed).toInt()

    stopSimplifier(Internal.PROBE)

    // report ('p', ...) dropped.

    return !unsat && failed != 0
}

/*------------------------------------------------------------------------*/

internal fun Internal.probe(updateLimits: Boolean = true): Unit = tracePhase("probe") {

    if (unsat) return
    if (level != 0) backtrack()
    if (!propagate()) {
        learnEmptyClause()
        return
    }

    stats.probingphases++
    if (externalProp) {
        check(level == 0) { "probe: level" }
        privateSteps = true
    }
    val before = active()

    // We trigger equivalent literal substitution (ELS) before ...
    //
    decompose()

    if (ternary()) // If we derived a binary clause
        decompose() // then start another round of ELS.

    // Remove duplicated binary clauses and perform in essence hyper unary
    // resolution, i.e., derive the unit '2' from '1 2' and '-1 2'.
    //
    markDuplicatedBinaryClausesAsGarbage()

    for (round in 1..opts.proberounds) if (!probeRound()) break

    decompose() // ... and (ELS) afterwards.

    last.probe.propagations = stats.propagations.search

    if (externalProp) {
        check(level == 0) { "probe: level after" }
        privateSteps = false
    }

    if (!updateLimits) return

    val after = active()
    val removed = before - after
    check(removed >= 0) { "probe: removed" }

    if (removed != 0) {
        stats.probesuccess++
    }

    val delta = opts.probeint * (stats.probingphases + 1)
    lim.probe = stats.conflicts + delta

    last.probe.reductions = stats.reductions
}
