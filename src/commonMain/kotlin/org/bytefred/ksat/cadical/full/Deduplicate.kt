package org.bytefred.ksat.cadical.full

import org.bytefred.ksat.cadical.IntArrayList

/*
 * deduplicate.cpp
 *
 * Mapping: watch iterators 'i', 'j', 'k' -> indices into 'ws'. 'Watch w = *j++ = *i' copies
 * the watch; here 'w' is the object at 'i', stored also at 'j'. The slot 'j - 1' is either
 * kept (then it is the same watch) or dropped by 'j--' and overwritten / cut off later, so
 * '*k = w' may store the same object in slot 'k'.
 */

// Equivalent literal substitution in 'decompose' and shrinking in 'subsume'
// or 'vivify' might produce duplicated binary clauses.  They can not be
// found in 'subsume' nor 'vivify' since we explicitly do not consider
// binary clauses as candidates to be shrunken or subsumed.  They are
// detected here by a simple scan of watch lists and then marked as garbage.
// This is actually also quite fast.

// Further it might also be possible that two binary clauses can be resolved
// to produce a unit (we call it 'hyper unary resolution').  For example
// resolving the binary clauses '1 -2' and '1 2' produces the unit '1'.
// This could be found by probing in 'probe' unless '-1' also occurs in a
// binary clause (add the clause '-1 2' to those two clauses) in which case
// '1' as well as '2' both occur positively as well as negatively and none
// of them nor their negation is considered as probe

internal fun Internal.markDuplicatedBinaryClausesAsGarbage(): Unit = tracePhase("deduplicate") {

    if (opts.deduplicate == 0) return
    if (unsat) return
    if (terminatedAsynchronously()) return

    startSimplifier(Internal.DEDUP)
    stats.deduplications++

    check(level == 0) { "deduplicate: level" }
    check(watching()) { "deduplicate: watching" }

    val stack = IntArrayList() // To save marked literals and unmark them later.

    // 'subsumed' and 'units' only feed 'report' and are not ported.

    for (idx in 1..maxVar) {

        if (unsat) break
        if (!active(idx)) continue
        var unit = 0

        var sign = -1
        while (unit == 0 && sign <= 1) {

            val lit = sign * idx // Consider all literals.

            check(stack.isEmpty()) { "deduplicate: stack not empty" }
            val ws = watches(lit)

            // We are removing references to garbage clause. Thus no 'auto'.

            val end = ws.size
            var j = 0
            var i = j

            while (unit == 0 && i != end) {
                val w = ws[i]
                ws[j++] = w
                if (!w.binary()) {
                    i++
                    continue
                }
                val other = w.blit
                val tmp = marked(other)
                var c = w.clause

                if (tmp > 0) { // Found duplicated binary clause.

                    if (c.garbage) {
                        j--
                        i++
                        continue
                    }

                    // The previous identical clause 'd' might be redundant and if the
                    // second clause 'c' is not (so irredundant), then we have to keep
                    // 'c' instead of 'd', thus we search for it and replace it.

                    if (!c.redundant) {
                        var k = 0
                        while (true) {
                            check(k != i) { "deduplicate: duplicate not found" }
                            if (!ws[k].binary()) {
                                k++
                                continue
                            }
                            if (ws[k].blit != other) {
                                k++
                                continue
                            }
                            val d = ws[k].clause
                            if (d.garbage) {
                                k++
                                continue
                            }
                            c = d
                            break
                        }
                        ws[k] = w
                    }

                    stats.subsumed++
                    stats.deduplicated++
                    markGarbage(c)
                    j--

                } else if (tmp < 0) { // Hyper unary resolution.

                    unit = lit
                    if (lrat) {
                        // taken from fradical
                        check(lratChain.isEmpty()) { "deduplicate: lrat chain" }
                        lratChain.add(c.id)
                        // We've forgotten where the other binary clause is, so go find
                        // it again
                        var k = 0
                        while (true) {
                            check(k != i) { "deduplicate: other binary not found" }
                            if (!ws[k].binary()) {
                                k++
                                continue
                            }
                            if (ws[k].blit != -other) {
                                k++
                                continue
                            }
                            lratChain.add(ws[k].clause.id)
                            break
                        }
                    }
                    j = 0 // Flush 'ws'.

                } else {
                    if (c.garbage) {
                        i++
                        continue
                    }
                    mark(other)
                    stack.add(other)
                }
                i++
            }

            if (j == 0) ws.clear()
            else if (j != end) ws.shrinkTo(j) // Shrink watchers.

            for (k in 0 until stack.size) unmark(stack[k])

            stack.clear()
            sign += 2
        }

        // Propagation potentially messes up the watches and thus we can not
        // propagate the unit immediately after finding it.  Instead we break
        // out of both loops and assign and propagate the unit here.

        if (unit != 0) {

            stats.failed++
            stats.hyperunary++
            assignUnit(unit)
            // lrat_chain.clear ();   done in search_assign

            if (!propagate()) {
                learnEmptyClause()
            }
        }
    }
    stopSimplifier(Internal.DEDUP)

    // report ('2', !opts.reportall && !(subsumed + units)) dropped (message output).
}
