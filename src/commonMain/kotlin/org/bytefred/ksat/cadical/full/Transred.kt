package org.bytefred.ksat.cadical.full

import org.bytefred.ksat.cadical.IntArrayList

/*
 * transred.cpp
 *
 * Mapping: clause iterator 'i' -> index into 'clauses'; watch iterator 'k' -> index.
 * 'limit *= 1e-3 * opts.transredreleff' is 'int64_t *= double', i.e. the product is computed
 * in double and truncated back to int64.
 */

// Implement transitive reduction in the binary implication graph.  This is
// important for hyper binary resolution, which has the risk to produce too
// many hyper binary resolvents otherwise.  This algorithm only works on
// binary clauses and is usually pretty fast.  It will also find some failed
// literals (in the binary implication graph).

internal fun Internal.transred(): Unit = tracePhase("transred") {

    if (unsat) return
    if (terminatedAsynchronously()) return
    if (stats.current.redundant == 0L && stats.current.irredundant == 0L) return

    check(opts.transred != 0) { "transred: option off" }
    check(level == 0) { "transred: level" }

    startSimplifier(Internal.TRANSRED)
    stats.transreds++

    // Transitive reduction can not be run to completion for larger formulas
    // with many binary clauses.  We bound it in the same way as 'probe_core'.
    //
    var limit = stats.propagations.search
    limit -= last.transred.propagations
    limit = (limit * (1e-3 * opts.transredreleff)).toLong()
    if (limit < opts.transredmineff) limit = opts.transredmineff.toLong()
    if (limit > opts.transredmaxeff) limit = opts.transredmaxeff.toLong()

    val end = clauses.size
    var i = 0

    // Find first clause not checked for being transitive yet.
    //
    while (i != end) {
        val c = clauses[i]
        if (c.garbage) {
            i++
            continue
        }
        if (c.size != 2) {
            i++
            continue
        }
        if (c.redundant && c.hyper) {
            i++
            continue
        }
        if (!c.transred) break
        i++
    }

    // If all candidate clauses have been checked reschedule all.
    //
    if (i == end) {

        i = 0
        while (i != end) {
            val c = clauses[i]
            if (c.transred) c.transred = false
            i++
        }
        i = 0
    }

    // Move watches of binary clauses to the front. Thus we can stop iterating
    // watches as soon a long clause is found during watch traversal.
    //
    sortWatches()

    // This working stack plays the same role as the 'trail' during standard
    // propagation.
    //
    val work = IntArrayList()

    var propagations = 0L // 'units' and 'removed' only feed messages

    while (!unsat && i != end && !terminatedAsynchronously() && propagations < limit) {
        val c = clauses[i++]

        // A clause is a candidate for being transitive if it is binary, and not
        // the result of hyper binary resolution.  The reason for excluding
        // those, is that they come in large numbers, most of them are reduced
        // away anyhow and further are non-transitive at the point they are
        // added (see the code in 'hyper_binary_resolve' in 'prope.cpp' and
        // also check out our CPAIOR paper on tree-based look ahead).
        //
        if (c.garbage) continue
        if (c.size != 2) continue
        if (c.redundant && c.hyper) continue
        if (c.transred) continue // checked before?
        c.transred = true // marked as checked

        // Find a different path from 'src' to 'dst' in the binary implication
        // graph, not using 'c'.  Since this is the same as checking whether
        // there is a path from '-dst' to '-src', we can do the reverse search
        // if the number of watches of '-dst' is larger than those of 'src'.
        //
        var src = -c.literals[0]
        var dst = c.literals[1]
        if (value(src) != 0 || value(dst) != 0) continue
        if (watches(-src).size < watches(dst).size) {
            val tmp = dst
            dst = -src
            src = -tmp
        }

        // If the candidate clause is irredundant then we can not use redundant
        // binary clauses in the implication graph.  See our inprocessing rules
        // paper, why this restriction is required.
        //
        val irredundant = !c.redundant

        check(work.isEmpty()) { "transred: work not empty" }
        mark(src)
        work.add(src)

        var transitive = false // found path from 'src' to 'dst'?
        var failed = false // 'src' failed literal?

        var j = 0 // 'propagated' in BFS

        check(lratChain.isEmpty()) { "transred: lrat chain" }
        check(miniChain.isEmpty()) { "transred: mini chain" }
        val parents = IntArrayList()

        while (!transitive && !failed && j < work.size) {
            val lit = work[j++]
            check(marked(lit) > 0) { "transred: unmarked work literal" }
            propagations++
            val ws = watches(-lit)
            val eow = ws.size
            var k = 0
            while (!transitive && !failed && k != eow) {
                val w = ws[k]
                if (!w.binary()) break // since we sorted watches above
                val d = w.clause
                if (d === c) {
                    k++
                    continue
                }
                if (irredundant && d.redundant) {
                    k++
                    continue
                }
                if (d.garbage) {
                    k++
                    continue
                }
                val other = w.blit
                if (other == dst) transitive = true // 'dst' reached
                else {
                    val tmp = marked(other)
                    if (tmp > 0) {
                        k++
                        continue
                    } else if (tmp < 0) {
                        if (lrat) {
                            parents.add(lit)
                            miniChain.add(d.id)
                            work.add(other)
                        }
                        failed = true
                    } else {
                        if (lrat) {
                            parents.add(lit)
                            miniChain.add(d.id)
                        }
                        mark(other)
                        work.add(other)
                    }
                }
                k++
            }
        }

        val failedLit = work.back()
        var nextPos = 0
        var nextNeg = 0

        // Unassign all assigned literals (same as '[bp]acktrack').
        //
        while (!work.isEmpty()) {
            val lit = work.back()
            work.removeLast()
            if (lrat && failed && !work.isEmpty()) {
                check(parents.size != 0 && miniChain.isNotEmpty()) { "transred: LRAT parents" }
                if (lit == failedLit || lit == nextPos) {
                    lratChain.add(miniChain.last())
                    nextPos = parents.back()
                } else if (lit == -failedLit || lit == nextNeg) {
                    lratChain.add(miniChain.last())
                    nextNeg = parents.back()
                }
                parents.removeLast()
                miniChain.removeAt(miniChain.size - 1)
            }
            unmark(lit)
        }
        miniChain.clear()
        check(miniChain.isEmpty()) { "transred: mini chain not empty" }
        if (lrat && failed) {
            lratChain.reverse()
        }

        if (transitive) {
            stats.transitive++
            markGarbage(c)
        } else if (failed) {
            stats.failed++
            stats.transredunits++
            assignUnit(-src)
            if (!propagate()) {
                learnEmptyClause()
            }
        }
        lratChain.clear()
    }

    last.transred.propagations = stats.propagations.search
    stats.propagations.transred += propagations
    work.clear()

    stopSimplifier(Internal.TRANSRED)
    // report ('t', !opts.reportall && !(removed + units)) dropped (message output).
}
