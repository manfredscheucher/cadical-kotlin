package org.bytefred.ksat.cadical.full

import org.bytefred.ksat.cadical.IntArrayList

/*
 * queue.cpp: initializing and shuffling the VMTF decision queue.
 */

// Slightly different than 'bump_variable' since the variable is not
// enqueued at all.
internal fun Internal.initEnqueue(idx: Int) {
    val l = links[idx]
    if (opts.reverse != 0) {
        l.prev = 0
        if (queue.first != 0) {
            check(links[queue.first].prev == 0)
            links[queue.first].prev = idx
            btab[idx] = btab[queue.first] - 1
        } else {
            check(queue.last == 0)
            queue.last = idx
            btab[idx] = 0
        }
        check(btab[idx] <= stats.bumped)
        l.next = queue.first
        queue.first = idx
        if (queue.unassigned == 0) updateQueueUnassigned(queue.last)
    } else {
        l.next = 0
        if (queue.last != 0) {
            check(links[queue.last].next == 0)
            links[queue.last].next = idx
        } else {
            check(queue.first == 0)
            queue.first = idx
        }
        btab[idx] = ++stats.bumped
        l.prev = queue.last
        queue.last = idx
        updateQueueUnassigned(queue.last)
    }
}

// Initialize VMTF queue from current 'old_max_var + 1' to 'new_max_var'.
// This incorporates an initial variable order.  We currently simply assume
// that variables with smaller index are more important.  This is the same
// as in MiniSAT (implicitly) and also matches the 'scores' initialization.
internal fun Internal.initQueue(oldMaxVar: Int, newMaxVar: Int) {
    check(oldMaxVar < newMaxVar)
    // New variables can be created that can invoke enlarge anytime (eg via
    // calls during ipasir-up call-backs), thus assuming (!level) is not
    // correct
    for (idx in oldMaxVar until newMaxVar) initEnqueue(idx + 1)
}

// Shuffle the VMTF queue.
internal fun Internal.shuffleQueue() {
    if (opts.shuffle == 0) return
    if (opts.shufflequeue == 0) return
    stats.shuffled++
    val shuffle = IntArrayList()
    if (opts.shufflerandom != 0) {
        var idx = maxVar
        while (idx != 0) shuffle.add(idx--)
        val random = Random(opts.seed.toULong()) // global seed
        random += stats.shuffled.toULong() // different every time
        for (i in 0..maxVar - 2) {
            val j = random.pickInt(i, maxVar - 1)
            val tmp = shuffle[i]
            shuffle[i] = shuffle[j]
            shuffle[j] = tmp
        }
    } else {
        var idx = queue.last
        while (idx != 0) {
            shuffle.add(idx)
            idx = links[idx].prev
        }
    }
    queue.first = 0
    queue.last = 0
    for (k in 0 until shuffle.size) queue.enqueue(links, shuffle[k])
    var bumped = queue.bumped
    var idx = queue.last
    while (idx != 0) {
        btab[idx] = bumped--
        idx = links[idx].prev
    }
    queue.unassigned = queue.last
}
