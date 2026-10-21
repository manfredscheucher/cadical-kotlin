package org.bytefred.ksat.cadical.full

/*
 * averages.hpp: glue, size, jump moving averages local to the 'stable' and 'unstable' phase.
 *
 * Mapping: the anonymous struct of 'current' and 'saved' -> [Averages.Group]. 'swap (current,
 * saved)' in 'swap_averages' -> swap the two references ('current' and 'saved' are 'var').
 */
internal class Averages {
    var swapped = 0L

    class Glue {
        val fast = EMA() // average fast (small window) moving glucose level
        val slow = EMA() // average slow (large window) moving glucose level
    }

    class Trail {
        val fast = EMA() // average fast (small window) moving trail level
        val slow = EMA() // average slow (large window) moving trail level
    }

    class Group {
        val glue = Glue()
        val trail = Trail()
        val size = EMA() // average learned clause size
        val jump = EMA() // average (potential non-chronological) back-jump level
        val level = EMA() // average back track level after conflict
    }

    var current = Group()
    var saved = Group()
}
