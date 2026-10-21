package org.bytefred.ksat.cadical.full

import org.bytefred.ksat.cadical.IntArrayList

/*
 * radix.hpp: the generic radix sort 'rsort' and the 'MSORT' macro.
 *
 * Mapping:
 *  - 'Rank::Type' (the unsigned rank type) -> [Rank.bits]: 64 for 'uint64_t' / 'size_t'
 *    (the default), 32 for 'unsigned'. The rank value itself is returned as an unsigned bit
 *    pattern in a Long (a 32 bit rank must be zero extended: 'x.toLong () and 0xffffffffL').
 *    The loop runs over '8 * sizeof (rank)' bits as upstream.
 *  - The bucket array 'count' persists across the byte rounds exactly as the C stack array
 *    (only the range '[masked_lower, masked_upper]' is cleared at the start of each round).
 *  - The algorithm is written once for an IntArray; vectors of objects are sorted through an
 *    index permutation (isomorphic, since rsort only reads ranks and moves elements).
 *  - 'pointer_rank' (sorting clauses by address in 'collect.cpp') -> [clauseAddressRank], the
 *    virtual arena address of the clause (see ArenaHpp.kt).
 */

/** Rank function of an element (C++ functor with 'typedef ... Type' and 'operator ()'). */
internal fun interface Rank<T> {
    fun rank(a: T): Long

    /** '8 * sizeof (Rank::Type)'. */
    val bits: Int get() = 64
}

/** Rank function on int elements. */
internal fun interface IntRank {
    fun rank(a: Int): Long

    /** '8 * sizeof (Rank::Type)'. */
    val bits: Int get() = 64
}

/** pointer_rank: clauses are ranked by their (virtual) arena address. */
internal val clauseAddressRank = Rank<Clause> { c -> c.address }

/** rsort (first, last, rank) on 'a[first, last)'. */
internal fun rsort(a: IntArray, first: Int, last: Int, rank: IntRank) {
    check(first <= last) { "rsort range [$first,$last)" }
    val n = last - first
    if (n <= 1) return

    val l = 8 // Radix 8, thus byte-wise.
    val w = 1 shl l // So many buckets.
    val mask: ULong = (w - 1).toULong() // Fast mod 'w'.

    val count = IntArray(w)

    // 'a' is the input range, 'b' the temporary vector 'v'; 'cInA' tells whether the
    // current source 'c' is 'a' (true) or 'b' (false).
    var b = IntArray(0)
    var cInA = true
    var initialized = false
    var upper: ULong = 0u
    var lower: ULong = upper.inv()
    var shifted: ULong = mask
    var bounded = false
    var maskedLower: ULong = 0u
    var maskedUpper: ULong = mask

    val rankBits = rank.bits
    var i = 0
    while (i < rankBits) {
        if (!(bounded && (lower and shifted) == (upper and shifted))) {
            count.fill(0, maskedLower.toInt(), maskedUpper.toInt() + 1)
            val src = if (cInA) a else b
            val srcStart = if (cInA) first else 0
            var sorted = true
            var lastM: ULong = 0u
            for (p in srcStart until srcStart + n) {
                val r = rank.rank(src[p]).toULong()
                if (!bounded) {
                    lower = lower and r
                    upper = upper or r
                }
                val s = r shr i
                val m = s and mask
                if (sorted && lastM > m) sorted = false else lastM = m
                count[m.toInt()]++
            }
            maskedLower = (lower shr i) and mask
            maskedUpper = (upper shr i) and mask
            var skip = false
            if (!bounded) {
                bounded = true
                if ((lower and shifted) == (upper and shifted)) skip = true
            }
            if (!skip && !sorted) {
                var pos = 0
                var j = maskedLower
                while (j <= maskedUpper) {
                    val delta = count[j.toInt()]
                    count[j.toInt()] = pos
                    pos += delta
                    j++
                }
                if (!initialized) {
                    check(cInA)
                    b = IntArray(n)
                    initialized = true
                }
                val dst = if (cInA) b else a
                val dstStart = if (cInA) 0 else first
                for (p in srcStart until srcStart + n) {
                    val e = src[p]
                    val r = rank.rank(e).toULong()
                    val s = r shr i
                    val m = (s and mask).toInt()
                    dst[dstStart + count[m]++] = e
                }
                cInA = !cInA
            }
        }
        i += l
        shifted = shifted shl l
    }

    if (!cInA) {
        for (k in 0 until n) a[first + k] = b[k]
    }
}

/** rsort (v.begin (), v.end (), rank) on a vector<int>. */
internal fun rsort(v: IntArrayList, rank: IntRank) {
    if (v.size <= 1) return
    val a = v.toArray()
    rsort(a, 0, a.size, rank)
    for (k in a.indices) v[k] = a[k]
}

/** rsort (v.begin (), v.end (), rank) on a vector<T>. */
internal fun <T> rsort(v: MutableList<T>, rank: Rank<T>) {
    val n = v.size
    if (n <= 1) return
    val perm = IntArray(n) { it }
    rsort(perm, 0, n, object : IntRank {
        override fun rank(a: Int): Long = rank.rank(v[a])
        override val bits: Int get() = rank.bits
    })
    val sorted = ArrayList<T>(n)
    for (k in 0 until n) sorted.add(v[perm[k]])
    for (k in 0 until n) v[k] = sorted[k]
}

/** MSORT (limit, v.begin (), v.end (), rank, less): std::sort up to 'limit' elements. */
internal fun msort(limit: Int, v: IntArrayList, rank: IntRank, less: IntLess) {
    val n = v.size
    if (n <= limit) cxxSort(v, less) else rsort(v, rank)
}
