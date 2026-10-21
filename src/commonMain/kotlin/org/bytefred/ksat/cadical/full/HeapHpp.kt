package org.bytefred.ksat.cadical.full

import org.bytefred.ksat.cadical.IntArrayList

/*
 * heap.hpp: binary heap priority queue with updates for unsigned integer elements.
 *
 * Mapping:
 *  - 'template <class C> class heap' -> [Heap] taking the comparator as an [IntLess]
 *    ('C less' upstream). The elements are 'unsigned' upstream but always variable indices or
 *    unsigned literals well below 2^31, so they are Int here.
 *  - 'vector<unsigned> array, pos' -> IntArrayList; 'invalid_heap_position' (UINT_MAX) ->
 *    [INVALID_HEAP_POSITION] (-1, the same bit pattern).
 *  - 'unsigned &index (e)' returns a reference that callers assign to; here [index] reads and
 *    [setIndex] writes (both grow 'pos' as upstream).
 *  - The expensive 'check ()' is disabled upstream ('#if 0') and not ported.
 *  - Iteration 'for (auto e : heap)' -> 'for (k in 0 until heap.size ()) heap[k]' (the array
 *    order, as upstream iterates 'array').
 */
internal const val INVALID_HEAP_POSITION = -1

internal class Heap(private val less: IntLess) {
    private val array = IntArrayList() // actual binary heap
    private val pos = IntArrayList() // positions of elements in array

    // Map an element to its position entry in the 'pos' map.
    private fun index(e: Int): Int {
        if (e >= pos.size) pos.resize(1 + e, INVALID_HEAP_POSITION)
        val res = pos[e]
        check(res == INVALID_HEAP_POSITION || res < array.size)
        return res
    }

    private fun setIndex(e: Int, i: Int) {
        if (e >= pos.size) pos.resize(1 + e, INVALID_HEAP_POSITION)
        pos[e] = i
    }

    private fun hasParent(e: Int): Boolean = index(e) > 0

    private fun hasLeft(e: Int): Boolean = 2L * index(e) + 1 < size()

    private fun hasRight(e: Int): Boolean = 2L * index(e) + 2 < size()

    private fun parent(e: Int): Int {
        check(hasParent(e))
        return array[(index(e) - 1) / 2]
    }

    private fun left(e: Int): Int {
        check(hasLeft(e))
        return array[2 * index(e) + 1]
    }

    private fun right(e: Int): Int {
        check(hasRight(e))
        return array[2 * index(e) + 2]
    }

    // Exchange elements 'a' and 'b' in 'array' and fix their positions.
    private fun exchange(a: Int, b: Int) {
        val i = index(a)
        val j = index(b)
        val t = array[i]
        array[i] = array[j]
        array[j] = t
        setIndex(a, j)
        setIndex(b, i)
    }

    // Bubble up an element as far as necessary.
    private fun up(e: Int) {
        while (hasParent(e)) {
            val p = parent(e)
            if (!less.less(p, e)) break
            exchange(p, e)
        }
    }

    // Bubble down an element as far as necessary.
    private fun down(e: Int) {
        while (hasLeft(e)) {
            var c = left(e)
            if (hasRight(e)) {
                val r = right(e)
                if (less.less(c, r)) c = r
            }
            if (!less.less(e, c)) break
            exchange(e, c)
        }
    }

    // Number of elements in the heap.
    fun size(): Int = array.size

    // Check if no more elements are in the heap.
    fun empty(): Boolean = array.size == 0

    // Check whether 'e' is already in the heap.
    fun contains(e: Int): Boolean {
        if (e >= pos.size) return false
        return pos[e] != INVALID_HEAP_POSITION
    }

    // Add a new (not contained) element 'e' to the heap.
    fun pushBack(e: Int) {
        check(!contains(e))
        val i = array.size
        array.add(e)
        setIndex(e, i)
        up(e)
        down(e)
    }

    // Returns the maximum element in the heap.
    fun front(): Int {
        check(!empty())
        return array[0]
    }

    // Removes the maximum element in the heap.
    fun popFront(): Int {
        check(!empty())
        val res = array[0]
        val last = array[array.size - 1]
        if (size() > 1) exchange(res, last)
        setIndex(res, INVALID_HEAP_POSITION)
        array.removeLast()
        if (size() > 1) down(last)
        return res
    }

    // Notify the heap, that evaluation of 'less' has changed for 'e'.
    fun update(e: Int) {
        check(contains(e))
        up(e)
        down(e)
    }

    fun clear() {
        array.clear()
        pos.clear()
    }

    fun erase() {
        array.clear()
        pos.clear()
    }

    // 'shrink' only releases capacity upstream.
    fun shrink() {}

    /** Element at array position [k] (iteration over 'array' upstream). */
    operator fun get(k: Int): Int = array[k]
}
