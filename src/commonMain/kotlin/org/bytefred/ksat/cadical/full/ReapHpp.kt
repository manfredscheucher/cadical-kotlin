package org.bytefred.ksat.cadical.full

import org.bytefred.ksat.cadical.IntArrayList

/*
 * reap.hpp plus reap.cpp: radix heap ('reap') used by 'shrink'.
 *
 * Mapping:
 *  - 'unsigned' elements -> Int holding the unsigned bit pattern; comparisons go through
 *    'toUInt ()'. 'size_t num_elements' -> Int.
 *  - 'std::vector<unsigned> buckets[33]' -> 33 IntArrayLists.
 *  - '__builtin_clz' -> 'countLeadingZeroBits' (32 for zero as the upstream helper).
 *  - 'init' assigns '{0}' to every bucket, i.e. a vector holding one zero element, exactly as
 *    upstream does.
 */
internal class Reap {
    private var numElements = 0
    private var lastDeleted = 0
    private var minBucket = 32
    private var maxBucket = 0
    private val buckets = Array(33) { IntArrayList() }

    fun init() {
        for (bucket in buckets) {
            bucket.clear()
            bucket.add(0)
        }
        check(numElements == 0)
        check(lastDeleted == 0)
        minBucket = 32
        check(maxBucket == 0)
    }

    fun release() {
        numElements = 0
        lastDeleted = 0
        minBucket = 32
        maxBucket = 0
    }

    fun empty(): Boolean = numElements == 0

    fun size(): Int = numElements

    fun push(e: Int) {
        check(lastDeleted.toUInt() <= e.toUInt())
        val diff = e xor lastDeleted
        val bucket = 32 - leadingZeroesOfUnsigned(diff)
        buckets[bucket].add(e)
        if (minBucket > bucket) minBucket = bucket
        if (maxBucket < bucket) maxBucket = bucket
        check(numElements != -1)
        numElements++
    }

    fun pop(): Int {
        check(numElements > 0)
        var i = minBucket
        while (true) {
            check(i < 33)
            check(i <= maxBucket)
            val s = buckets[i]
            if (s.isEmpty()) {
                minBucket = ++i
                continue
            }
            var res: Int
            if (i != 0) {
                res = -1 // UINT_MAX
                var q = 0
                check(s.size > 0)
                for (p in 0 until s.size) {
                    val tmp = s[p]
                    if (tmp.toUInt() >= res.toUInt()) continue
                    res = tmp
                    q = p
                }
                for (p in 0 until s.size) {
                    if (p == q) continue
                    val other = s[p]
                    val diff = other xor res
                    val j = 32 - leadingZeroesOfUnsigned(diff)
                    check(j < i)
                    buckets[j].add(other)
                    if (minBucket > j) minBucket = j
                }
                s.clear()
                if (i != 0 && maxBucket == i) {
                    if (s.isEmpty()) maxBucket = i - 1
                }
            } else {
                res = lastDeleted
                check(!buckets[0].isEmpty())
                check(buckets[0][0] == res)
                buckets[0].removeLast()
            }
            if (minBucket == i) {
                if (s.isEmpty()) minBucket = minOf(i + 1, 32)
            }
            --numElements
            check(lastDeleted.toUInt() <= res.toUInt())
            lastDeleted = res
            return res
        }
    }

    fun clear() {
        check(maxBucket <= 32)
        for (i in 0 until 33) buckets[i].clear()
        numElements = 0
        lastDeleted = 0
        minBucket = 32
        maxBucket = 0
    }

    private companion object {
        fun leadingZeroesOfUnsigned(x: Int): Int = if (x != 0) x.countLeadingZeroBits() else 32
    }
}
