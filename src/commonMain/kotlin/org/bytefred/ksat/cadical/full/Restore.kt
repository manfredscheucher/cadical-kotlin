package org.bytefred.ksat.cadical.full

import kotlin.math.abs

/*
 * restore.cpp (CaDiCaL 2.1.3): restoring clauses from the extension stack in incremental
 * solving (see the long comment in upstream restore.cpp and our SAT'19 paper
 * [FazekasBiereScholl-SAT'19]).
 *
 * In short: clauses on the extension stack whose witness literal occurs negated as a
 * 'tainted' literal (newly internalized in 'add' / 'assume' since the last 'solve') are
 * restored as original clauses; root-level satisfied ones are flushed; then the witness
 * bits are recomputed.
 *
 * Iterators into 'extension' are Int indices ('begin' / 'end' of 'restore_clause' too).
 * Dropped as PORTING.md says: LOG, PHASE, START/STOP; the '#ifndef QUIET' tainted counts
 * only feed PHASE.
 */

internal fun External.restoreClause(begin: Int /* const_iterator */, end: Int /* const_iterator */, id: Long) {
    check(eclause.isEmpty()) { "eclause not empty" }
    check(id != 0L)
    for (p in begin until end) {
        eclause.add(extension[p])
        if (internal.proof != null && internal.lrat) {
            val elit = extension[p]
            val eidx = (if (elit > 0) 1 else 0) + 2 * abs(elit)
            check(eidx < extUnits.size)
            val unitId = extUnits[eidx] // shadows 'id' upstream
            val added = extFlags[abs(elit)]
            if (unitId != 0L && !added) {
                extFlags[abs(elit)] = true
                internal.lratChain.add(unitId)
            }
        }
        val ilit = internalize(extension[p])
        internal.addOriginalLit(ilit)
        internal.stats.restoredlits++
    }
    if (internal.proof != null && internal.lrat) {
        for (k in 0 until eclause.size) {
            extFlags[abs(eclause[k])] = false
        }
    }
    internal.finishAddedClauseWithId(id, true)
    eclause.clear()
    internal.stats.restored++
}

/*------------------------------------------------------------------------*/

private class RestoreClauses {
    var weakened = 0L
    var satisfied = 0L
    var restored = 0L
    var removed = 0L
}

internal fun External.restoreClauses() {

    check(internal.opts.restoreall == 2 || !tainted.isEmpty())

    internal.stats.restorations++

    val clauses = RestoreClauses() // zero initialized as with 'memset'

    val endOfExtension = extension.size
    var p = 0
    var q = p

    // Go over all witness labelled clauses on the extension stack, restore
    // those necessary, remove restored and flush satisfied clauses.
    //
    while (p != endOfExtension) {

        clauses.weakened++

        check(extension[p] == 0)
        val saved = q // Save old start.
        extension[q++] = extension[p++] // Copy zero '0'.

        // Copy witness part and try to find a tainted witness literal in it.
        //
        var tlit = 0 // Negation tainted.
        var elit: Int
        //
        check(p != endOfExtension)
        //
        while (true) {
            elit = extension[p++]
            extension[q++] = elit
            if (elit == 0) break

            if (marked(tainted, -elit)) {
                tlit = elit
            }

            check(p != endOfExtension)
        }

        // now copy the id of the clause
        val id: Long = (extension[p].toLong() shl 32) + extension[p + 1].toLong()
        extension[q++] = extension[p++]
        extension[q++] = extension[p++]
        check(id != 0L)
        check(extension[p] == 0)
        extension[q++] = extension[p++]

        // Now find 'end_of_clause' (clause starts at 'p') and at the same time
        // figure out whether the clause is actually root level satisfied.
        //
        var satisfied = 0
        var endOfClause = p
        while (endOfClause != endOfExtension) {
            elit = extension[endOfClause]
            if (elit == 0) break
            if (satisfied == 0 && fixed(elit) > 0) satisfied = elit
            endOfClause++
        }
        check(id != 0L)

        // Do not apply our 'FLUSH' rule to remove satisfied (implied) clauses
        // if the corresponding option is set simply by resetting 'satisfied'.
        //
        if (satisfied != 0 && internal.opts.restoreflush == 0) {
            satisfied = 0
        }

        if (satisfied != 0 || tlit != 0 || internal.opts.restoreall != 0) {

            if (satisfied != 0) {
                clauses.satisfied++
            } else {
                restoreClause(p, endOfClause, id) // Might taint literals.
                clauses.restored++
            }

            clauses.removed++
            p = endOfClause
            q = saved
        } else {

            while (p != endOfClause) // Copy clause too.
                extension[q++] = extension[p++]
        }
    }

    extension.resize(q)
    // shrink_vector (extension);  (no-op for IntArrayList)

    tainted.clear()

    // Finally recompute the witness bits.
    //
    witness.clear()
    val beginOfExtension = 0
    p = extension.size
    while (p != beginOfExtension) {
        while (extension[--p] != 0) check(p != beginOfExtension)
        var elit: Int
        check(p != beginOfExtension)
        --p
        check(p != beginOfExtension)
        check(extension[p] != 0 || extension[p - 1] != 0)
        --p
        check(p != beginOfExtension)
        check(extension[p] == 0)
        --p
        check(p != beginOfExtension)
        while (true) {
            elit = extension[--p]
            if (elit == 0) break
            mark(witness, elit)
            check(p != beginOfExtension)
        }
    }
}
