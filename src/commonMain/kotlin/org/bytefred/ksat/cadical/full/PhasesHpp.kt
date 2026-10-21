package org.bytefred.ksat.cadical.full

/*
 * phases.hpp: saved, target and best phases. 'vector<signed char>' tables -> ByteArray,
 * grown in 'enlarge' (internal.cpp) with 'resized' and replaced on 'compact'.
 */
internal class Phases {
    var best = ByteArray(0) // The current largest trail phase.
    var forced = ByteArray(0) // Forced through 'phase'.
    var min = ByteArray(0) // The current minimum unsatisfied phase.
    var prev = ByteArray(0) // Previous during local search.
    var saved = ByteArray(0) // The actual saved phase.
    var target = ByteArray(0) // The current target phase.
}
