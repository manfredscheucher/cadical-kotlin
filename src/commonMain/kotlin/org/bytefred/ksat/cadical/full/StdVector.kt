package org.bytefred.ksat.cadical.full

import org.bytefred.ksat.cadical.BooleanList
import org.bytefred.ksat.cadical.IntArrayList

/*
 * Kotlin counterparts of the std::vector operations used by CaDiCaL (no upstream file).
 *
 * Mapping (see PORTING.md for the full table):
 *   vector<int>, vector<unsigned>  -> IntArrayList (from the old port, reused as is)
 *   vector<bool>                   -> BooleanList  (from the old port, reused as is)
 *   vector<T> (objects)            -> ArrayList<T>
 *   vector<uint64_t>               -> ArrayList<Long> (only LRAT chains / ids, off by default)
 *   per-variable / per-literal tables that upstream only grows in 'enlarge' or rebuilds in
 *   'compact' (btab, stab, marks, phases, ...) -> primitive arrays, grown with 'resized'.
 *
 *   v.push_back (x)     -> v.add (x)
 *   v.pop_back ()       -> v.removeLast ()      (IntArrayList)  /  v.removeAt (v.size - 1)
 *   v.back ()           -> v.back ()            (IntArrayList)  /  v.last ()
 *   v.empty ()          -> v.isEmpty ()
 *   v.resize (n)        -> v.resize (n)  shrinks or grows (grown elements get the fill value)
 *   v.clear (), erase_vector (v)   -> v.clear ()   (capacity is not observable in Kotlin)
 *   shrink_vector (v)   -> nothing for IntArrayList/BooleanList, v.trimToSize () for ArrayList
 *
 * IntArrayList and BooleanList live in CaDiCaL.kt (the old port, which must stay unchanged),
 * so the missing operations are extension functions here. Their backing arrays are private,
 * thus growing goes through 'add'.
 */

internal fun IntArrayList.isEmpty(): Boolean = size == 0

internal fun IntArrayList.back(): Int {
    check(size > 0) { "back () of empty vector" }
    return this[size - 1]
}

/** std::vector<int>::resize: shrinks to [n] or grows to [n] filling with [fill]. */
internal fun IntArrayList.resize(n: Int, fill: Int = 0) {
    check(n >= 0) { "negative vector size $n" }
    if (n <= size) shrinkTo(n) else while (size < n) add(fill)
}

/** Copies [other] into this vector (C++ vector assignment 'this = other'). */
internal fun IntArrayList.assign(other: IntArrayList) {
    clear()
    for (k in 0 until other.size) add(other[k])
}

internal fun BooleanList.isEmpty(): Boolean = size == 0

/** std::vector<bool>::resize: shrinks to [n] or grows to [n] filling with [fill]. */
internal fun BooleanList.resize(n: Int, fill: Boolean = false) {
    check(n >= 0) { "negative vector size $n" }
    if (n <= size) shrinkTo(n) else while (size < n) add(fill)
}

/** std::vector<T>::resize for object vectors: shrinks or grows with fresh [init] elements. */
internal inline fun <T> MutableList<T>.resize(n: Int, init: () -> T) {
    check(n >= 0) { "negative vector size $n" }
    if (n < size) shrinkTo(n) else while (size < n) add(init())
}

/** Shrinking std::vector<T>::resize (the 'j = i' compaction idiom ends with 'v.resize (j)'). */
internal fun <T> MutableList<T>.shrinkTo(n: Int) {
    check(n in 0..size) { "shrinkTo $n out of range 0..$size" }
    if (n < size) subList(n, size).clear()
}

/** Resize of a primitive table: keeps the prefix, new elements get [fill]. */
internal fun IntArray.resized(n: Int, fill: Int = 0): IntArray {
    val res = copyOf(n)
    if (n > size && fill != 0) res.fill(fill, size, n)
    return res
}

internal fun LongArray.resized(n: Int, fill: Long = 0L): LongArray {
    val res = copyOf(n)
    if (n > size && fill != 0L) res.fill(fill, size, n)
    return res
}

internal fun DoubleArray.resized(n: Int, fill: Double = 0.0): DoubleArray {
    val res = copyOf(n)
    if (n > size && fill != 0.0) res.fill(fill, size, n)
    return res
}

internal fun ByteArray.resized(n: Int, fill: Byte = 0): ByteArray {
    val res = copyOf(n)
    if (n > size && fill != 0.toByte()) res.fill(fill, size, n)
    return res
}
