package org.bytefred.ksat.cadical.full

/*
 * bins.cpp: binary implication graph lists.
 */

/*------------------------------------------------------------------------*/

// Binary implication graph lists.

internal fun Internal.initBins() {
    check(big.isEmpty())
    if (big.size < 2 * vsize) big.resize(2 * vsize) { Bins() }
    // LOG: initialized binary implication graph
}

internal fun Internal.resetBins() {
    check(big.isNotEmpty())
    big.clear()
    // LOG: reset binary implication graph
}
