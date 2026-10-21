package org.bytefred.ksat.cadical.full

/*
 * block.hpp: blocked clause elimination schedule.
 *
 * Mapping: 'block_more_occs_size::operator ()' is defined in block.cpp; its Kotlin class
 * 'BlockMoreOccsSize (internal) : IntLess' goes to Block.kt and is passed in here.
 */
internal class Blocker(less: IntLess) {
    val candidates = ArrayList<Clause>()
    val reschedule = ArrayList<Clause>()
    val schedule = Heap(less) // BlockSchedule

    fun erase() {
        candidates.clear()
        reschedule.clear()
        schedule.erase()
    }
}
