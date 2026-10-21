package org.bytefred.ksat.cadical.full

/*
 * var.cpp: resetting the 'subsume' bits and checking the variable statistics.
 */

internal fun Internal.resetSubsumeBits() {
    // LOG: marking all variables as not subsume
    for (idx in vars) flags(idx).subsume = false
}

internal fun Internal.checkVarStats() {
    // '#ifndef NDEBUG'
    var fixed = 0L
    var eliminated = 0L
    var substituted = 0L
    var pure = 0L
    var unused = 0L
    for (idx in vars) {
        val f = flags(idx)
        if (f.active()) continue
        if (f.fixed()) fixed++
        if (f.eliminated()) eliminated++
        if (f.substituted()) substituted++
        if (f.unused()) unused++
        if (f.pure()) pure++
    }
    check(stats.now.fixed == fixed) { "fixed variable stats" }
    check(stats.now.eliminated == eliminated) { "eliminated variable stats" }
    check(stats.now.substituted == substituted) { "substituted variable stats" }
    check(stats.now.pure == pure) { "pure variable stats" }
    val inactive = unused + fixed + eliminated + substituted + pure
    check(stats.inactive == inactive) { "inactive variable stats" }
    check(maxVar.toLong() == stats.active + stats.inactive) { "active + inactive variable stats" }
}
