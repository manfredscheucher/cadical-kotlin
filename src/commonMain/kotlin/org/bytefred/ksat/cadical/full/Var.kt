package org.bytefred.ksat.cadical.full

/*
 * var.cpp: resetting the 'subsume' bits and checking the variable statistics.
 */

internal fun Internal.resetSubsumeBits() {
    // LOG: marking all variables as not subsume
    for (idx in vars) flags(idx).subsume = false
}

internal fun Internal.checkVarStats() {
    // The whole body is '#ifndef NDEBUG' upstream: empty in the release reference.
}
