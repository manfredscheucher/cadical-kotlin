package org.bytefred.ksat.cadical.full

/*
 * watch.hpp: watch lists for CDCL search.
 *
 * Mapping:
 *  - 'struct Watch' -> class [Watch] (mutable as upstream). 'Watches' (vector<Watch>) ->
 *    'ArrayList<Watch>'; 'watch_iterator' -> int index.
 *  - Value semantics: upstream copies watches ('*j++ = *i++', 'const Watch w = *i'). In
 *    Kotlin the compaction idiom may move the reference ('ws[j++] = ws[i++]'), because every
 *    slot in '[j, i)' is overwritten or cut off by the final 'resize (j)'. But when upstream
 *    keeps a 'const Watch w' copy and then writes into a slot ('j[-1].blit = ...'), read the
 *    fields of 'w' into locals first (or use [copy]): the slot and 'w' are the same object.
 *
 * In fashion of Intel Sat 10.4230/LIPIcs.SAT.2022.8 we try to guarantee the following
 * invariant for both watches: if the watched literal is negatively assigned either it will be
 * propagated in the future or the corresponding blocking literal is positively assigned and
 * its level is smaller than the level of the watched literal.
 */
internal class Watch(
    var blit: Int,
    var clause: Clause,
    var size: Int = clause.size,
) {
    fun binary(): Boolean = size == 2

    fun copy(): Watch = Watch(blit, clause, size)
}

internal typealias Watches = ArrayList<Watch>

internal fun removeWatch(ws: Watches, clause: Clause) {
    val end = ws.size
    var i = 0
    for (j in 0 until end) {
        val w = ws[j]
        ws[i++] = w
        if (w.clause === clause) i--
    }
    check(i + 1 == end)
    ws.shrinkTo(i)
}

// search for the clause and updates the size marked in the watch lists
internal fun updateWatchSize(ws: Watches, blit: Int, conflict: Clause) {
    var found = false
    val size = conflict.size
    for (w in ws) {
        if (w.clause === conflict) {
            w.size = size
            w.blit = blit
            found = true
        }
        check(w.clause.garbage || w.size == 2 || w.clause.size != 2)
    }
    check(found)
}
