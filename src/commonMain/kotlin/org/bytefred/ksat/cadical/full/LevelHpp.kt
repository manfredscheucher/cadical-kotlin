package org.bytefred.ksat.cadical.full

/*
 * level.hpp: for each new decision we increase the decision level and push a 'Level' on the
 * 'control' stack. The information gathered here is used in 'reuse_trail' and for early
 * aborts in clause minimization.
 *
 * Mapping: the anonymous 'struct { int count, trail; } seen' -> [seenCount], [seenTrail].
 * The default constructor 'Level ()' is not ported: upstream only shrinks 'control' with
 * 'resize', it never grows it that way.
 */
internal class Level(
    var decision: Int, // decision literal of this level
    var trail: Int, // trail start of this level
) {
    var seenCount = 0 // how many variables seen during 'analyze'
    var seenTrail = 0 // smallest trail position seen on this level

    init {
        reset()
    }

    fun reset() {
        seenCount = 0
        seenTrail = Int.MAX_VALUE
    }
}
