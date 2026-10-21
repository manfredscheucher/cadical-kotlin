package org.bytefred.ksat.cadical.full

import org.bytefred.ksat.cadical.IntArrayList

/*
 * score.cpp: initializing and shuffling the EVSIDS scores heap.
 */

// This initializes variables on the binary 'scores' heap also with
// smallest variable index first (thus picked first) and larger indices at
// the end.
//
internal fun Internal.initScores(oldMaxVar: Int, newMaxVar: Int) {
    for (i in oldMaxVar until newMaxVar) scores.pushBack(i + 1)
}

// Shuffle the EVSIDS heap.

internal fun Internal.shuffleScores() {
    if (opts.shuffle == 0) return
    if (opts.shufflescores == 0) return
    check(level == 0) { "shuffle_scores above root" }
    stats.shuffled++
    val shuffle = IntArrayList()
    if (opts.shufflerandom != 0) {
        scores.erase()
        var idx = maxVar
        while (idx != 0) {
            shuffle.add(idx)
            idx--
        }
        val random = Random(opts.seed.toULong()) // global seed
        random += stats.shuffled.toULong() // different every time
        for (i in 0..maxVar - 2) {
            val j = random.pickInt(i, maxVar - 1)
            val tmp = shuffle[i]
            shuffle[i] = shuffle[j]
            shuffle[j] = tmp
        }
    } else {
        while (!scores.empty()) {
            val idx = scores.front()
            scores.popFront()
            shuffle.add(idx)
        }
    }
    scoreInc = 0.0
    for (k in 0 until shuffle.size) {
        val idx = shuffle[k]
        stab[idx] = scoreInc++
        scores.pushBack(idx)
    }
}
