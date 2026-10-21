package org.bytefred.ksat.cadical.full

/*
 * occs.cpp: occurrence lists and one-sided occurrence counters.
 */

/*------------------------------------------------------------------------*/

// Occurrence lists.

internal fun Internal.initOccs() {
    if (otab.size < 2 * vsize) otab.resize(2 * vsize) { Occs() }
    // LOG: initialized occurrence lists
}

internal fun Internal.resetOccs() {
    check(occurring())
    otab.clear()
    // LOG: reset occurrence lists
}

/*------------------------------------------------------------------------*/

// One-sided occurrence counter (each literal has its own counter).

internal fun Internal.initNoccs() {
    check(ntab.isEmpty())
    if (ntab.size < 2 * vsize) ntab = ntab.resized(2 * vsize, 0L)
    // LOG: initialized two-sided occurrence counters
}

internal fun Internal.resetNoccs() {
    check(maxVar == 0 || ntab.isNotEmpty())
    ntab = LongArray(0)
    // LOG: reset two-sided occurrence counters
}
