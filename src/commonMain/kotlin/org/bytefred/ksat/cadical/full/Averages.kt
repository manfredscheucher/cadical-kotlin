package org.bytefred.ksat.cadical.full

/*
 * averages.cpp: initialize and swap the moving averages of the 'stable' and 'unstable' phase.
 *
 * Mapping: 'swap (averages.current, averages.saved)' swaps the two group references (do not
 * keep a reference to 'averages.current' across a swap).
 */

internal fun Internal.initAverages() {
    initEma(averages.current.jump, opts.emajump)
    initEma(averages.current.level, opts.emalevel)
    initEma(averages.current.size, opts.emasize)
    initEma(averages.current.glue.fast, opts.emagluefast)
    initEma(averages.current.glue.slow, opts.emaglueslow)
    initEma(averages.current.trail.fast, opts.ematrailfast)
    initEma(averages.current.trail.slow, opts.ematrailslow)
    check(averages.swapped == 0L)
}

internal fun Internal.swapAverages() {
    val tmp = averages.current
    averages.current = averages.saved
    averages.saved = tmp
    if (averages.swapped == 0L) initAverages()
    averages.swapped++
}
