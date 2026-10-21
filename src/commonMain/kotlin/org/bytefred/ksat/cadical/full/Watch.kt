package org.bytefred.ksat.cadical.full

/*
 * watch.cpp: initializing, connecting, sorting and resetting watch lists.
 */

internal fun Internal.initWatches() {
    check(wtab.isEmpty())
    if (wtab.size < 2 * vsize) wtab.resize(2 * vsize) { Watches() }
    // LOG: initialized watcher tables
}

internal fun Internal.clearWatches() {
    for (lit in lits) watches(lit).clear()
}

internal fun Internal.resetWatches() {
    check(wtab.isNotEmpty())
    wtab.clear()
    // LOG: reset watcher tables
}

// This can be quite costly since lots of memory is accessed in a rather
// random fashion, and thus we optionally profile it.

internal fun Internal.connectWatches(irredundantOnly: Boolean = false) {
    check(watching())

    // LOG: watching all (irredundant) clauses

    // First connect binary clauses.
    //
    for (c in clauses) {
        if (irredundantOnly && c.redundant) continue
        if (c.garbage || c.size > 2) continue
        watchClause(c)
    }

    // Then connect non-binary clauses.
    //
    for (c in clauses) {
        if (irredundantOnly && c.redundant) continue
        if (c.garbage || c.size == 2) continue
        watchClause(c)
        if (level == 0) {
            val lit0 = c.literals[0]
            val lit1 = c.literals[1]
            val tmp0 = value(lit0)
            val tmp1 = value(lit1)
            if (tmp0 > 0) continue
            if (tmp1 > 0) continue
            if (tmp0 < 0) {
                val pos0 = variable(lit0).trail
                if (pos0 < propagated) {
                    propagated = pos0
                    // LOG: literal lit0 resets propagated to pos0
                }
            }
            if (tmp1 < 0) {
                val pos1 = variable(lit1).trail
                if (pos1 < propagated) {
                    propagated = pos1
                    // LOG: literal lit1 resets propagated to pos1
                }
            }
        }
    }
}

internal fun Internal.sortWatches() {
    check(watching())
    // LOG: sorting watches
    val saved = Watches()
    for (lit in lits) {
        val ws = watches(lit)

        val end = ws.size
        var j = 0

        check(saved.isEmpty())

        for (i in j until end) {
            val w = ws[i]
            if (w.binary()) ws[j++] = w
            else saved.add(w)
        }

        // std::copy (saved.cbegin (), saved.cend (), j)
        for (w in saved) ws[j++] = w

        saved.clear()
    }
}
