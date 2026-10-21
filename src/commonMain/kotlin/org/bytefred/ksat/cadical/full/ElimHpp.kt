package org.bytefred.ksat.cadical.full

import org.bytefred.ksat.cadical.IntArrayList

/*
 * elim.hpp: bounded variable elimination schedule and state.
 *
 * Mapping:
 *  - 'elim_more::operator ()' is defined in elim.cpp; its Kotlin class
 *    'ElimMore (internal) : IntLess' goes to Elim.kt and is passed in here.
 *  - 'queue<Clause *> backward' -> ArrayDeque<Clause>. 'dequeue', 'enqueue' and the
 *    destructor '~Eliminator' are defined in backward.cpp (Backward.kt, as extension functions).
 */
internal class Eliminator(val internal: Internal, less: IntLess) {
    val schedule = Heap(less) // ElimSchedule
    val backward = ArrayDeque<Clause>()
    val gates = ArrayList<Clause>()
    val marked = IntArrayList()
}
