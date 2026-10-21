package org.bytefred.ksat.cadical.full

import org.bytefred.ksat.cadical.IntArrayList

/*
 * vivify.hpp: vivification schedule and state.
 *
 * Mapping: 'std::tuple<int, Clause *, bool>' of 'vivify_build_lrat' ('lit, reason, finished')
 * -> [VivifyLratEntry].
 */
internal class VivifyLratEntry(
    val lit: Int,
    val reason: Clause?,
    val finished: Boolean,
)

internal class Vivifier(var redundantMode: Boolean) {
    val schedule = ArrayList<Clause>()
    val stack = ArrayList<Clause>()
    val sorted = IntArrayList()
    val lratStack = ArrayList<VivifyLratEntry>()

    fun erase() {
        schedule.clear()
        sorted.clear()
        stack.clear()
    }
}
