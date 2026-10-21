package org.bytefred.ksat.cadical.full

/*
 * phases.cpp: copying / clearing phase tables and forcing phases ('phase', 'unphase').
 */

internal fun Internal.copyPhases(dst: ByteArray) {
    for (i in vars) dst[i] = phases.saved[i]
}

internal fun Internal.clearPhases(dst: ByteArray) {
    for (i in vars) dst[i] = 0
}

internal fun Internal.phase(lit: Int) {
    val idx = vidx(lit)
    val oldForcedPhase = phases.forced[idx].toInt()
    val newForcedPhase = sign(lit)
    if (oldForcedPhase == newForcedPhase) {
        // forced phase remains
        return
    }
    phases.forced[idx] = newForcedPhase.toByte()
}

internal fun Internal.unphase(lit: Int) {
    val idx = vidx(lit)
    val oldForcedPhase = phases.forced[idx].toInt()
    if (oldForcedPhase == 0) {
        // forced phase already reset
        return
    }
    phases.forced[idx] = 0
}
