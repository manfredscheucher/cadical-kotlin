package org.bytefred.ksat.cadical.full

import kotlin.math.abs
import org.bytefred.ksat.cadical.IntArrayList

/*
 * decompose.cpp
 *
 * Mapping:
 *  - 'DFS *dfs' (a 'new DFS[size_dfs]' array) -> 'Array<DFS>'. SIGNATURES.md lists the
 *    parameter as 'dfs: DFS' (generated from the pointer type); upstream indexes it as an
 *    array ('dfs[vlit (from)]'), so the three helpers taking it use 'Array<DFS>'. They are
 *    only called from this file.
 *  - 'unsigned' DFS indices ('idx', 'min', 'dfs_idx', 'new_min') -> Int bit patterns;
 *    order comparisons use 'toUInt ()' since 'TRAVERSED' is UINT_MAX (-1).
 *  - 'int *reprs' (cleared with 'clear_n') -> IntArray; 'vector<uint64_t> decompose_ids'
 *    -> LongArray; 'vector<vector<Clause *>> dfs_chains' -> ArrayList<ArrayList<Clause>>.
 *  - DeferDeleteArray / erase_vector / delete [] -> nothing (garbage collected).
 *  - Clause iteration 'for (size_t i = 0; cond && i < clauses_size; i++)' keeps the bound
 *    'clauses_size' fixed at loop start as upstream (new clauses are appended behind it).
 *  - LOG / PHASE / report are dropped (PORTING.md); locals only feeding them are dropped.
 */

internal fun Internal.decomposeAnalyzeBinaryChain(dfs: Array<DFS>, from: Int) {
    if (!lrat) return
    val fromDfs = dfs[vlit(from)]
    val reason = fromDfs.parent ?: return
    check(reason.size == 2) { "decompose_analyze_binary_chain: size" }
    miniChain.add(reason.id)
    var other = reason.literals[0]
    other = if (other == from) -reason.literals[1] else -other
    val f = flags(other)
    if (f.seen) return
    f.seen = true
    analyzed.add(other)
    decomposeAnalyzeBinaryChain(dfs, other)
}

internal fun Internal.decomposeAnalyzeBinaryClauses(dfs: Array<DFS>, from: Int): ArrayList<Clause> {
    var fromLit = from
    val result = ArrayList<Clause>()
    val fromDfs = dfs[vlit(fromLit)]
    var reason = fromDfs.parent
    while (reason != null) {
        result.add(reason)
        check(reason.size == 2) { "decompose_analyze_binary_clauses: size" }
        var other = reason.literals[0]
        other = if (other == fromLit) -reason.literals[1] else -other
        val f = flags(other)
        if (f.seen) break
        f.seen = true
        analyzed.add(other)
        fromLit = other
        val nextDfs = dfs[vlit(fromLit)]
        reason = nextDfs.parent
    }
    return result
}

internal fun Internal.decomposeConflictingSccLrat(dfs: Array<DFS>, scc: IntArrayList) {
    if (!lrat) return
    check(lratChain.isEmpty()) { "decompose_conflicting_scc_lrat: lrat_chain" }
    check(miniChain.isEmpty()) { "decompose_conflicting_scc_lrat: mini_chain" }
    for (s in 0 until scc.size) {
        val lit = scc[s]
        val f = flags(lit)
        if (f.seen) return
        f.seen = true
        analyzed.add(lit)
        decomposeAnalyzeBinaryChain(dfs, lit)
        var p = miniChain.size - 1
        while (p != -1) {
            lratChain.add(miniChain[p])
            p--
        }
        miniChain.clear()
    }
    clearAnalyzedLiterals()
}

internal fun Internal.buildLratForClause(dfsChains: ArrayList<ArrayList<Clause>>, invert: Boolean = false) {
    check(lrat) { "build_lrat_for_clause: lrat" }
    check(lratChain.isEmpty()) { "build_lrat_for_clause: lrat_chain" }
    check(decomposed.isEmpty()) { "build_lrat_for_clause: decomposed" }
    for (ci in 0 until clause.size) { // build chain for each replaced literal
        val lit = clause[ci]
        var other = lit
        if (value(other) > 0) {
            if (markedDecompose(other)) continue
            markDecomposed(other)
            val uidx = vlit(other)
            val id = unitClauses(uidx)
            check(id != 0L) { "build_lrat_for_clause: unit id" }
            lratChain.add(id)
            continue
        }
        check(miniChain.isEmpty()) { "build_lrat_for_clause: mini_chain" }
        // The range 'dfs_chains[vlit (other)]' is evaluated once with the initial 'other'.
        val chain = dfsChains[vlit(other)]
        for (p in chain) {
            if (markedDecompose(other)) continue
            markDecomposed(other)
            var implied = p.literals[0]
            implied = if (implied == other) -p.literals[1] else -implied
            other = implied
            miniChain.add(p.id)
            if (value(implied) <= 0) continue
            if (markedDecompose(implied)) break
            markDecomposed(implied)
            val uidx = vlit(implied)
            val id = unitClauses(uidx)
            check(id != 0L) { "build_lrat_for_clause: implied unit id" }
            miniChain.add(id)
            break
        }
        if (invert) {
            var p = miniChain.size - 1
            while (p != -1) {
                lratChain.add(miniChain[p])
                p--
            }
        } else {
            for (p in 0 until miniChain.size) lratChain.add(miniChain[p])
        }
        miniChain.clear()
    }
    // clear_analyzed_literals ();
    clearDecomposedLiterals()
}

internal fun Internal.clearDecomposedLiterals() {
    for (k in 0 until decomposed.size) {
        val lit = decomposed[k]
        check(markedDecompose(lit)) { "clear_decomposed_literals: not marked" }
        unmarkDecompose(lit)
    }
    decomposed.clear()
}

// This performs one round of Tarjan's algorithm, e.g., equivalent literal
// detection and substitution, on the whole formula.  We might want to
// repeat it since its application might produce new binary clauses or
// units.  Such units might even result in an empty clause.

internal fun Internal.decomposeRound(): Boolean {

    if (opts.decompose == 0) return false
    if (unsat) return false
    if (terminatedAsynchronously()) return false

    check(level == 0) { "decompose_round: level" }

    startSimplifier(Internal.DECOMP)

    stats.decompositions++

    val sizeDfs = 2 * (1 + maxVar)
    val dfs = Array(sizeDfs) { DFS() }
    val reprs = IntArray(sizeDfs)
    val dfsChains = ArrayList<ArrayList<Clause>>(sizeDfs)
    dfsChains.resize(sizeDfs) { ArrayList() }
    if (lrat) {
        // Upstream loop 'for (size_t i = 0; i > size_dfs; i++)' never executes.
        var i = 0
        while (i > sizeDfs) {
            dfsChains[i] = ArrayList()
            i++
        }
    }

    var substituted = 0
    var dfsIdx = 0 // unsigned

    val work = IntArrayList() // depth first search working stack
    val scc = IntArrayList() // collects members of one SCC

    // The binary implication graph might have disconnected components and
    // thus we have in general to start several depth first searches.

    for (rootIdx in 1..maxVar) {
        if (unsat) break
        if (!active(rootIdx)) continue
        var rootSign = -1
        while (!unsat && rootSign <= 1) {
            val root = rootSign * rootIdx
            rootSign += 2
            if (dfs[vlit(root)].min == TRAVERSED) continue // skip traversed
            check(work.isEmpty()) { "decompose_round: work" }
            check(scc.isEmpty()) { "decompose_round: scc" }
            work.add(root)
            while (!unsat && !work.isEmpty()) {
                val parent = work.back()
                val parentDfs = dfs[vlit(parent)]
                if (parentDfs.min == TRAVERSED) { // skip traversed
                    check(reprs[vlit(parent)] != 0) { "decompose_round: traversed without repr" }
                    work.removeLast()
                } else {
                    check(reprs[vlit(parent)] == 0) { "decompose_round: repr" }

                    // Go over all implied literals, thus need to iterate over all
                    // binary watched clauses with the negation of 'parent'.

                    val ws = watches(-parent)

                    // Two cases: Either the node has never been visited before, i.e.,
                    // it's depth first search index is zero, then perform the
                    // 'pre-fix' work before visiting it's children.  Otherwise all
                    // it's children and nodes reachable from those children have been
                    // visited and their minimum reachable depth first search index
                    // has been computed.  This second case is the 'post-fix' work.

                    if (parentDfs.idx != 0) { // post-fix

                        work.removeLast() // 'parent' done

                        // Get the minimum reachable depth first search index reachable
                        // from the children of 'parent'.

                        var newMin = parentDfs.min

                        for (w in ws) {
                            if (!w.binary()) continue
                            val child = w.blit
                            if (!active(child)) continue
                            val childDfs = dfs[vlit(child)]
                            if (newMin.toUInt() > childDfs.min.toUInt()) newMin = childDfs.min
                        }

                        if (parentDfs.idx == newMin) { // entry to SCC

                            // All nodes on the 'scc' stack after and including 'parent'
                            // are in the same SCC.  Their representative is computed as
                            // the smallest literal (index-wise) in the SCC.  If the SCC
                            // contains both a literal and its negation, then the formula
                            // becomes unsatisfiable.

                            if (lrat) {
                                check(analyzed.isEmpty()) { "decompose_round: analyzed" }
                                var other: Int
                                var first = 0
                                var conflicting = false
                                var j = scc.size
                                do {
                                    check(j > 0) { "decompose_round: scc underflow (lrat)" }
                                    other = scc[--j]
                                    if (first == 0 || vlit(other) < vlit(first)) first = other
                                    val f = flags(other)
                                    if (other == -parent) {
                                        conflicting = true // conflicting scc
                                    }
                                    if (f.seen) {
                                        continue // also conflicting scc
                                    }
                                    f.seen = true
                                    analyzed.add(other)
                                } while (other != parent)

                                check(!conflicting || first > 0) { "decompose_round: conflicting first" }
                                val todo = IntArrayList()
                                if (conflicting) {
                                    todo.add(-parent)
                                } else {
                                    todo.add(first)
                                }
                                while (!todo.isEmpty()) {
                                    val next = todo.back()
                                    todo.removeLast()
                                    val nextWs = watches(-next)
                                    for (w in nextWs) {
                                        if (!w.binary()) continue
                                        val child = w.blit
                                        if (!active(child)) continue
                                        if (!flags(child).seen) continue
                                        val childDfs = dfs[vlit(child)]
                                        if (childDfs.parent != null) continue
                                        childDfs.parent = w.clause
                                        todo.add(child)
                                    }
                                }

                                clearAnalyzedLiterals()
                            }

                            var other: Int
                            var repr = parent
                            check(!scc.isEmpty()) { "decompose_round: scc empty" }
                            var j = scc.size
                            do {
                                check(j > 0) { "decompose_round: scc underflow" }
                                other = scc[--j]
                                if (other == -parent) {
                                    if (lrat) {
                                        val f = flags(-parent)
                                        f.seen = true
                                        analyzed.add(-parent)
                                        decomposeAnalyzeBinaryChain(dfs, parent)
                                        for (p in miniChain) lratChain.add(p)
                                        miniChain.clear()
                                    }
                                    assignUnit(parent)
                                    if (lrat) {
                                        propagate()
                                    }
                                    learnEmptyClause()
                                    lratChain.clear()
                                } else {
                                    if (abs(other) < abs(repr)) repr = other
                                }
                            } while (!unsat && other != parent)

                            if (unsat) break

                            do {
                                check(!scc.isEmpty()) { "decompose_round: scc empty (pop)" }
                                other = scc.back()
                                scc.removeLast()
                                dfs[vlit(other)].min = TRAVERSED
                                if (frozen(other)) {
                                    reprs[vlit(other)] = other
                                    continue
                                }
                                reprs[vlit(other)] = repr
                                if (other == repr) continue
                                substituted++
                                if (!lrat) continue
                                check(miniChain.isEmpty()) { "decompose_round: mini_chain" }
                                val f = flags(repr)
                                f.seen = true
                                analyzed.add(repr)
                                dfsChains[vlit(other)] = decomposeAnalyzeBinaryClauses(dfs, other)
                                // reverse (dfs_chains[vlit (other)].begin (),
                                // dfs_chains[vlit (other)].end ());
                                clearAnalyzedLiterals()
                            } while (other != parent)
                        } else {

                            // Current node 'parent' is in a non-trivial SCC but is not
                            // the entry point of the SCC in this depth first search, so
                            // keep it on the SCC stack until the entry point is reached.

                            parentDfs.min = newMin
                        }
                    } else { // pre-fix

                        dfsIdx++
                        check(dfsIdx.toUInt() < TRAVERSED.toUInt()) { "decompose_round: dfs_idx overflow" }
                        parentDfs.min = dfsIdx
                        parentDfs.idx = parentDfs.min
                        scc.add(parent)

                        // Now traverse all the children in the binary implication
                        // graph but keep 'parent' on the stack for 'post-fix' work.

                        for (w in ws) {
                            if (!w.binary()) continue
                            val child = w.blit
                            if (!active(child)) continue
                            val childDfs = dfs[vlit(child)]
                            if (childDfs.idx != 0) continue
                            work.add(child)
                        }
                    }
                }
            }
        }
    }

    work.clear()
    scc.clear()
    // delete [] dfs; need to postpone until after changing clauses...

    // Only keep the representatives 'repr' mapping.

    var newUnit = false
    var newBinaryClause = false

    // Finally, mark substituted literals as such and push the equivalences of
    // the substituted literals to their representative on the extension
    // stack to fix an assignment during 'extend'.
    //
    // TODO instead of adding the clauses to the extension stack one could
    // also just simply use the 'e2i' map as a union find data structure.
    // This would avoid the need to restore these clauses.

    val size = 2 * (1 + maxVar)
    val decomposeIds = LongArray(size)

    for (idx in 1..maxVar) {
        if (unsat) break
        if (!active(idx)) continue
        val other = reprs[vlit(idx)]
        if (other == idx) continue
        check(!flags(other).eliminated()) { "decompose_round: repr eliminated" }
        check(!flags(other).substituted()) { "decompose_round: repr substituted" }

        check(clause.isEmpty()) { "decompose_round: clause" }
        check(lratChain.isEmpty()) { "decompose_round: lrat_chain" }
        clause.add(other)
        clause.add(-idx)
        if (lrat) {
            buildLratForClause(dfsChains)
            check(!lratChain.isEmpty()) { "decompose_round: empty chain 1" }
        }

        val id1 = ++clauseId
        val p1 = proof
        if (p1 != null) {
            p1.addDerivedClause(id1, false, clause, lratChain)
            p1.weakenMinus(id1, clause)
        }
        external!!.pushBinaryClauseOnExtensionStack(id1, -idx, other)

        decomposeIds[vlit(-idx)] = id1

        lratChain.clear()
        clause.clear()

        check(clause.isEmpty()) { "decompose_round: clause 2" }
        check(lratChain.isEmpty()) { "decompose_round: lrat_chain 2" }
        clause.add(idx)
        clause.add(-other)
        if (lrat) {
            buildLratForClause(dfsChains)
            check(!lratChain.isEmpty()) { "decompose_round: empty chain 2" }
        }
        val id2 = ++clauseId
        val p2 = proof
        if (p2 != null) {
            p2.addDerivedClause(id2, false, clause, lratChain)
            p2.weakenMinus(id2, clause)
        }
        external!!.pushBinaryClauseOnExtensionStack(id2, idx, -other)
        decomposeIds[vlit(idx)] = id2

        clause.clear()
        lratChain.clear()
    }

    val postponedGarbage = ArrayList<Clause>()

    // Now go over all clauses and find clause which contain literals that
    // should be substituted by their representative.

    val clausesSize = clauses.size
    for (i in 0 until clausesSize) {
        if (!(substituted != 0 && !unsat)) break
        val c = clauses[i]
        if (c.garbage) continue
        var j: Int
        val csize = c.size
        j = 0
        while (j < csize) {
            val lit = c.literals[j]
            if (reprs[vlit(lit)] != lit) break
            j++
        }

        if (j == csize) continue

        // Now copy the result to 'clause'.  Substitute literals if they have a
        // different representative.  Skip duplicates and false literals.  If a
        // literal occurs in both phases or is assigned to true the clause is
        // satisfied and can be marked as garbage.

        check(clause.isEmpty()) { "decompose_round: clause (subst)" }
        check(lratChain.isEmpty()) { "decompose_round: lrat_chain (subst)" }
        check(analyzed.isEmpty()) { "decompose_round: analyzed (subst)" }
        var satisfied = false

        var k = 0
        while (!satisfied && k < csize) {
            val lit = c.literals[k]
            k++
            var tmp = value(lit)
            if (tmp > 0) {
                satisfied = true
            } else if (tmp < 0) {
                if (!lrat) continue
                val f = flags(lit)
                if (f.seen) continue
                f.seen = true
                analyzed.add(lit)
                val uidx = vlit(-lit)
                val id = unitClauses(uidx)
                check(id != 0L) { "decompose_round: unit id (false lit)" }
                lratChain.add(id)
                continue
            } else {
                val other = reprs[vlit(lit)]
                tmp = value(other)
                if (tmp < 0) {
                    if (!lrat) continue
                    val f = flags(other)
                    if (!f.seen) {
                        f.seen = true
                        analyzed.add(other)
                        val uidx = vlit(-other)
                        val id = unitClauses(uidx)
                        check(id != 0L) { "decompose_round: unit id (false repr)" }
                        lratChain.add(id)
                    }
                    if (other == lit) continue
                    val id = decomposeIds[vlit(-lit)]
                    check(id != 0L) { "decompose_round: decompose id (false repr)" }
                    lratChain.add(id)
                    continue
                } else if (tmp > 0) {
                    satisfied = true
                } else {
                    tmp = marked(other)
                    if (tmp < 0) {
                        satisfied = true
                    } else if (tmp == 0) {
                        mark(other)
                        clause.add(other)
                    }
                    if (other == lit) continue
                    if (!lrat) continue
                    val id = decomposeIds[vlit(-lit)]
                    check(id != 0L) { "decompose_round: decompose id" }
                    lratChain.add(id)
                }
            }
        }
        if (lrat) lratChain.add(c.id)
        clearAnalyzedLiterals()
        if (satisfied) {
            postponedGarbage.add(c)
        } else if (clause.size == 0) {
            learnEmptyClause()
        } else if (clause.size == 1) {
            assignUnit(clause[0])
            markGarbage(c)
            newUnit = true
        } else if (c.literals[0] != clause[0] || c.literals[1] != clause[1]) {
            if (clause.size == 2) newBinaryClause = true
            val dClauseIdx = clauses.size
            val d = newClauseAs(c)
            check(clauses[dClauseIdx] === d) { "decompose_round: new clause position" }
            clauses[dClauseIdx] = c
            clauses[i] = d
            markGarbage(c)
        } else {
            check(c.size > 2) { "decompose_round: shrink size" }
            if (!c.redundant) markRemoved(c)
            val p = proof
            if (p != null) {
                p.addDerivedClause(++clauseId, c.redundant, clause, lratChain)
                p.deleteClause(c)
                c.id = clauseId
            }
            var l = 2
            val literals = c.literals
            while (l < clause.size) {
                literals[l] = clause[l]
                l++
            }
            val flushed = c.size - l
            if (flushed != 0) {
                if (l == 2) newBinaryClause = true
                shrinkClause(c, l)
            } else if (likelyToBeKeptClause(c)) {
                markAdded(c)
            }
            // we have assert (c->size > 2)
            if (c.size == 2) { // cheaper to update only new binary clauses
                updateWatchSize(watches(c.literals[0]), c.literals[1], c)
                updateWatchSize(watches(c.literals[1]), c.literals[0], c)
            }
        }
        while (!clause.isEmpty()) {
            val lit = clause.back()
            clause.removeLast()
            check(marked(lit) > 0) { "decompose_round: unmark" }
            unmark(lit)
        }
        lratChain.clear()
    }

    val p = proof
    if (p != null) {
        for (idx in 1..maxVar) {
            if (!active(idx)) continue
            val id1 = decomposeIds[vlit(-idx)]
            if (id1 == 0L) continue
            val other = reprs[vlit(idx)]
            check(other != idx) { "decompose_round: proof repr" }
            check(!flags(other).eliminated()) { "decompose_round: proof repr eliminated" }
            check(!flags(other).substituted()) { "decompose_round: proof repr substituted" }

            clause.add(other)
            clause.add(-idx)
            p.deleteClause(id1, false, clause)
            clause.clear()

            clause.add(idx)
            clause.add(-other)
            val id2 = decomposeIds[vlit(idx)]
            p.deleteClause(id2, false, clause)
            clause.clear()
        }
    }

    if (!unsat && !postponedGarbage.isEmpty()) {
        for (c in postponedGarbage) markGarbage(c)
    }
    postponedGarbage.clear()

    scc.clear()

    // Propagate found units.

    if (!unsat && propagated < trail.size && !propagate()) {
        learnEmptyClause()
    }

    for (idx in 1..maxVar) {
        if (unsat) break
        if (!active(idx)) continue
        val other = reprs[vlit(idx)]
        if (other == idx) continue
        check(!flags(other).eliminated()) { "decompose_round: final repr eliminated" }
        check(!flags(other).substituted()) { "decompose_round: final repr substituted" }
        if (!flags(other).fixed()) markSubstituted(idx)
    }

    dfsChains.clear()

    flushAllOccsAndWatches() // particularly the 'blit's

    val success = unsat || (substituted > 0 && (newUnit || newBinaryClause))
    // report ('d', ...) dropped.

    stopSimplifier(Internal.DECOMP)

    return success
}

internal fun Internal.decompose(): Unit = tracePhase("decompose") {
    for (round in 1..opts.decomposerounds) if (!decomposeRound()) break
}
