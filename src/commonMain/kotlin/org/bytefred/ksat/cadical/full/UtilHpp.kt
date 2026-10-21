package org.bytefred.ksat.cadical.full

/*
 * util.hpp: simple utility functions independent from 'Internal'.
 *
 * Mapping:
 *  - 'unsigned' results ('bign') are plain Int (values 1 or 2).
 *  - 'size_t' arguments of 'aligned' / 'align' are Long.
 *  - erase_vector / shrink_vector / DeferDeleteArray / DeferDeletePtr / clear_n are memory
 *    management only: see StdVector.kt ('clear ()', 'trimToSize ()', array 'fill').
 *  - is_color_option / is_no_color_option are command line helpers (cadical.cpp, mobical.cpp)
 *    and not ported.
 */

internal fun relative(a: Double, b: Double): Double = if (b != 0.0) a / b else 0.0

internal fun percent(a: Double, b: Double): Double = relative(100 * a, b)

internal fun sign(lit: Int): Int = (if (lit > 0) 1 else 0) - (if (lit < 0) 1 else 0)

internal fun bign(lit: Int): Int = 1 + (if (lit < 0) 1 else 0)

internal fun isPowerOfTwo(n: Int): Boolean = n != 0 && (n and (n - 1)) == 0

internal fun contained(c: Long, l: Long, u: Long): Boolean = l <= c && c <= u

internal fun aligned(n: Long, alignment: Long): Boolean {
    check(alignment != 0L && (alignment and (alignment - 1)) == 0L)
    val mask = alignment - 1
    return (n and mask) == 0L
}

internal fun align(n: Long, alignment: Long): Long {
    var res = n
    check(alignment != 0L && (alignment and (alignment - 1)) == 0L)
    val mask = alignment - 1
    if ((res and mask) != 0L) res = (res or mask) + 1
    check(aligned(res, alignment))
    return res
}

/** Parity of the 32 bits of [a] (an 'unsigned' upstream). */
internal fun parity(a: Int): Boolean {
    var tmp = a
    tmp = tmp xor (tmp ushr 16)
    tmp = tmp xor (tmp ushr 8)
    tmp = tmp xor (tmp ushr 4)
    tmp = tmp xor (tmp ushr 2)
    tmp = tmp xor (tmp ushr 1)
    return (tmp and 1) != 0
}
