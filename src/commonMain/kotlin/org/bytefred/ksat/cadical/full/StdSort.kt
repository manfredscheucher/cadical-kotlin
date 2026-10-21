package org.bytefred.ksat.cadical.full

import org.bytefred.ksat.cadical.IntArrayList

/*
 * Exact port of the C++ standard library sorting that CaDiCaL calls (no upstream file).
 *
 * std::sort is NOT stable: with ties (elements neither 'less' than the other) the result
 * depends on the library implementation. To reproduce the reference trace this is a 1:1 port
 * of libc++ 18.1 (LLVM 18, '_LIBCPP_VERSION 180100', the one of Apple clang 16 / the macOS 15
 * SDK the reference is built with), file '__algorithm/sort.h' plus the heap helpers it uses
 * for the introsort fallback ('partial_sort.h', 'make_heap.h', 'sift_down.h', 'sort_heap.h',
 * 'pop_heap.h', 'push_heap.h'). Only the path for user comparators is ported: libc++ takes the
 * branchless / bitset-partition path only for std::less / std::greater on arithmetic types,
 * where ties are identical values and any correct sort gives the same result. If the reference
 * were built against libstdc++ (g++), this file would have to become a port of that instead.
 *
 * The algorithm is written once for an IntArray. Sorting a list of objects goes through an
 * index permutation ([cxxSort] for MutableList): the algorithm only compares and moves
 * elements, so sorting indices with 'less (list[i], list[j])' and permuting afterwards gives
 * exactly the same order as sorting the objects in place.
 *
 * std::stable_sort is deterministic by definition for a strict weak ordering (unique result),
 * so [stableSort] uses Kotlin's stable 'sortWith'. Upstream comparators that are not strict
 * weak orderings would make both sides undefined; on the JVM TimSort then throws, which is the
 * wanted loud failure.
 */

/** Strict weak ordering on int elements (C++ comparator 'bool operator() (int a, int b)'). */
internal fun interface IntLess {
    fun less(a: Int, b: Int): Boolean
}

/** Strict weak ordering on objects (C++ comparator 'bool operator() (const T *a, const T *b)'). */
internal fun interface Less<T> {
    fun less(a: T, b: T): Boolean
}

/** std::sort (v.begin () + first, v.begin () + last, less) on an IntArray. */
internal fun cxxSort(a: IntArray, first: Int, last: Int, less: IntLess) {
    check(first in 0..last && last <= a.size) { "cxxSort range [$first,$last) of ${a.size}" }
    val depthLimit = 2 * log2i(last - first)
    CxxSorter(a, less).introsort(first, last, depthLimit, true)
}

/** std::sort (v.begin (), v.end (), less) on a vector<int>. */
internal fun cxxSort(v: IntArrayList, less: IntLess) {
    if (v.size <= 1) return
    val a = v.toArray()
    cxxSort(a, 0, a.size, less)
    for (k in a.indices) v[k] = a[k]
}

/** std::sort (v.begin () + first, v.begin () + last, less) on a vector<T>. */
internal fun <T> cxxSort(v: MutableList<T>, first: Int, last: Int, less: Less<T>) {
    check(first in 0..last && last <= v.size) { "cxxSort range [$first,$last) of ${v.size}" }
    val n = last - first
    if (n <= 1) return
    val perm = IntArray(n) { first + it }
    cxxSort(perm, 0, n) { i, j -> less.less(v[i], v[j]) }
    val sorted = ArrayList<T>(n)
    for (k in 0 until n) sorted.add(v[perm[k]])
    for (k in 0 until n) v[first + k] = sorted[k]
}

/** std::sort (v.begin (), v.end (), less) on a vector<T>. */
internal fun <T> cxxSort(v: MutableList<T>, less: Less<T>) = cxxSort(v, 0, v.size, less)

/** std::stable_sort (v.begin (), v.end (), less) on a vector<T>. */
internal fun <T> stableSort(v: MutableList<T>, less: Less<T>) {
    v.sortWith { a, b -> if (less.less(a, b)) -1 else if (less.less(b, a)) 1 else 0 }
}

/** std::stable_sort (v.begin (), v.end (), less) on a vector<int>. */
internal fun stableSort(v: IntArrayList, less: IntLess) {
    if (v.size <= 1) return
    val boxed = v.toArray().toMutableList()
    boxed.sortWith { a, b -> if (less.less(a, b)) -1 else if (less.less(b, a)) 1 else 0 }
    for (k in boxed.indices) v[k] = boxed[k]
}

// libc++ '__log2i' for 'ptrdiff_t' (64 bit 'long').
private fun log2i(n: Int): Int = if (n == 0) 0 else 63 - n.toLong().countLeadingZeroBits()

/** libc++ 18 '__introsort' and helpers for a user comparator, over 'a' with int indices. */
private class CxxSorter(private val a: IntArray, private val c: IntLess) {

    private fun iterSwap(x: Int, y: Int) {
        val t = a[x]
        a[x] = a[y]
        a[y] = t
    }

    private fun sort3(x: Int, y: Int, z: Int): Int {
        var r = 0
        if (!c.less(a[y], a[x])) { // if x <= y
            if (!c.less(a[z], a[y])) // if y <= z
                return r // x <= y && y <= z
            // x <= y && y > z
            iterSwap(y, z) // x <= z && y < z
            r = 1
            if (c.less(a[y], a[x])) { // if x > y
                iterSwap(x, y) // x < y && y <= z
                r = 2
            }
            return r // x <= y && y < z
        }
        if (c.less(a[z], a[y])) { // x > y, if y > z
            iterSwap(x, z) // x < y && y < z
            r = 1
            return r
        }
        iterSwap(x, y) // x > y && y <= z
        r = 1 // x < y && x <= z
        if (c.less(a[z], a[y])) { // if y > z
            iterSwap(y, z) // x <= y && y < z
            r = 2
        }
        return r
    }

    private fun sort4(x1: Int, x2: Int, x3: Int, x4: Int) {
        sort3(x1, x2, x3)
        if (c.less(a[x4], a[x3])) {
            iterSwap(x3, x4)
            if (c.less(a[x3], a[x2])) {
                iterSwap(x2, x3)
                if (c.less(a[x2], a[x1])) iterSwap(x1, x2)
            }
        }
    }

    private fun sort5(x1: Int, x2: Int, x3: Int, x4: Int, x5: Int) {
        sort4(x1, x2, x3, x4)
        if (c.less(a[x5], a[x4])) {
            iterSwap(x4, x5)
            if (c.less(a[x4], a[x3])) {
                iterSwap(x3, x4)
                if (c.less(a[x3], a[x2])) {
                    iterSwap(x2, x3)
                    if (c.less(a[x2], a[x1])) iterSwap(x1, x2)
                }
            }
        }
    }

    private fun insertionSort(first: Int, last: Int) {
        if (first == last) return
        var i = first + 1
        while (i != last) {
            var j = i - 1
            if (c.less(a[i], a[j])) {
                val t = a[i]
                var k = j
                j = i
                do {
                    a[j] = a[k]
                    j = k
                } while (j != first && c.less(t, a[--k]))
                a[j] = t
            }
            i++
        }
    }

    private fun insertionSortUnguarded(first: Int, last: Int) {
        if (first == last) return
        var i = first + 1
        while (i != last) {
            var j = i - 1
            if (c.less(a[i], a[j])) {
                val t = a[i]
                var k = j
                j = i
                do {
                    a[j] = a[k]
                    j = k
                } while (c.less(t, a[--k])) // no bounds check: not the leftmost range
                a[j] = t
            }
            i++
        }
    }

    private fun insertionSortIncomplete(first: Int, last: Int): Boolean {
        when (last - first) {
            0, 1 -> return true
            2 -> {
                if (c.less(a[last - 1], a[first])) iterSwap(first, last - 1)
                return true
            }
            3 -> {
                sort3(first, first + 1, last - 1)
                return true
            }
            4 -> {
                sort4(first, first + 1, first + 2, last - 1)
                return true
            }
            5 -> {
                sort5(first, first + 1, first + 2, first + 3, last - 1)
                return true
            }
        }
        var j = first + 2
        sort3(first, first + 1, j)
        val limit = 8
        var count = 0
        var i = j + 1
        while (i != last) {
            if (c.less(a[i], a[j])) {
                val t = a[i]
                var k = j
                j = i
                do {
                    a[j] = a[k]
                    j = k
                } while (j != first && c.less(t, a[--k]))
                a[j] = t
                if (++count == limit) return ++i == last
            }
            j = i
            i++
        }
        return true
    }

    // Returns the pivot position; 'alreadyPartitioned' is the second pair component upstream.
    private var alreadyPartitioned = false

    private fun partitionWithEqualsOnRight(begin: Int, end: Int): Int {
        var first = begin
        var last = end
        val pivot = a[first]
        // Find the first element greater or equal to the pivot (guarded by median-of-three).
        do {
            ++first
        } while (c.less(a[first], pivot))
        // Find the last element less than the pivot.
        if (begin == first - 1) {
            while (first < last && !c.less(a[--last], pivot)) {
                // empty body as upstream
            }
        } else {
            do {
                --last
            } while (!c.less(a[last], pivot))
        }
        alreadyPartitioned = first >= last
        while (first < last) {
            iterSwap(first, last)
            do {
                ++first
            } while (c.less(a[first], pivot))
            do {
                --last
            } while (!c.less(a[last], pivot))
        }
        val pivotPos = first - 1
        if (begin != pivotPos) a[begin] = a[pivotPos]
        a[pivotPos] = pivot
        return pivotPos
    }

    private fun partitionWithEqualsOnLeft(begin: Int, end: Int): Int {
        var first = begin
        var last = end
        val pivot = a[first]
        if (c.less(pivot, a[last - 1])) {
            do {
                ++first
            } while (!c.less(pivot, a[first]))
        } else {
            while (++first < last && !c.less(pivot, a[first])) {
                // empty body as upstream
            }
        }
        if (first < last) {
            do {
                --last
            } while (c.less(pivot, a[last]))
        }
        while (first < last) {
            iterSwap(first, last)
            do {
                ++first
            } while (!c.less(pivot, a[first]))
            do {
                --last
            } while (c.less(pivot, a[last]))
        }
        val pivotPos = first - 1
        if (begin != pivotPos) a[begin] = a[pivotPos]
        a[pivotPos] = pivot
        return first
    }

    fun introsort(first0: Int, last0: Int, depth0: Int, leftmost0: Boolean) {
        var first = first0
        var last = last0
        var depth = depth0
        var leftmost = leftmost0
        val limit = 24 // upper bound for using insertion sort
        val nintherThreshold = 128 // lower bound for Tukey's ninther
        while (true) {
            val len = last - first
            when (len) {
                0, 1 -> return
                2 -> {
                    if (c.less(a[last - 1], a[first])) iterSwap(first, last - 1)
                    return
                }
                3 -> {
                    sort3(first, first + 1, last - 1)
                    return
                }
                4 -> {
                    sort4(first, first + 1, first + 2, last - 1)
                    return
                }
                5 -> {
                    sort5(first, first + 1, first + 2, first + 3, last - 1)
                    return
                }
            }
            if (len < limit) {
                if (leftmost) insertionSort(first, last) else insertionSortUnguarded(first, last)
                return
            }
            if (depth == 0) {
                // Fallback to heap sort as Introsort suggests.
                partialSort(first, last, last)
                return
            }
            --depth
            val halfLen = len / 2
            if (len > nintherThreshold) {
                sort3(first, first + halfLen, last - 1)
                sort3(first + 1, first + (halfLen - 1), last - 2)
                sort3(first + 2, first + (halfLen + 1), last - 3)
                sort3(first + (halfLen - 1), first + halfLen, first + (halfLen + 1))
                iterSwap(first, first + halfLen)
            } else {
                sort3(first + halfLen, first, last - 1)
            }
            if (!leftmost && !c.less(a[first - 1], a[first])) {
                first = partitionWithEqualsOnLeft(first, last)
                continue
            }
            var i = partitionWithEqualsOnRight(first, last)
            if (alreadyPartitioned) {
                val fs = insertionSortIncomplete(first, i)
                if (insertionSortIncomplete(i + 1, last)) {
                    if (fs) return
                    last = i
                    continue
                } else if (fs) {
                    first = ++i
                    continue
                }
            }
            introsort(first, i, depth, leftmost)
            leftmost = false
            first = ++i
        }
    }

    // '__partial_sort_impl' (only called with middle == last from '__introsort').
    private fun partialSort(first: Int, middle: Int, last: Int) {
        if (first == middle) return
        makeHeap(first, middle)
        val len = middle - first
        var i = middle
        while (i != last) {
            if (c.less(a[i], a[first])) {
                iterSwap(i, first)
                siftDown(first, len, first)
            }
            i++
        }
        sortHeap(first, middle)
    }

    private fun makeHeap(first: Int, last: Int) {
        val n = last - first
        if (n > 1) {
            var start = (n - 2) / 2
            while (start >= 0) {
                siftDown(first, n, first + start)
                --start
            }
        }
    }

    private fun siftDown(first: Int, len: Int, start0: Int) {
        var start = start0
        var child = start - first
        if (len < 2 || (len - 2) / 2 < child) return
        child = 2 * child + 1
        var childI = first + child
        if ((child + 1) < len && c.less(a[childI], a[childI + 1])) {
            ++childI
            ++child
        }
        if (c.less(a[childI], a[start])) return
        val top = a[start]
        do {
            a[start] = a[childI]
            start = childI
            if ((len - 2) / 2 < child) break
            child = 2 * child + 1
            childI = first + child
            if ((child + 1) < len && c.less(a[childI], a[childI + 1])) {
                ++childI
                ++child
            }
        } while (!c.less(a[childI], top))
        a[start] = top
    }

    private fun floydSiftDown(first: Int, len: Int): Int {
        var hole = first
        var childI = first
        var child = 0
        while (true) {
            childI += child + 1
            child = 2 * child + 1
            if ((child + 1) < len && c.less(a[childI], a[childI + 1])) {
                ++childI
                ++child
            }
            a[hole] = a[childI]
            hole = childI
            if (child > (len - 2) / 2) return hole
        }
    }

    private fun siftUp(first: Int, last0: Int, len0: Int) {
        var last = last0
        var len = len0
        if (len > 1) {
            len = (len - 2) / 2
            var ptr = first + len
            if (c.less(a[ptr], a[--last])) {
                val t = a[last]
                do {
                    a[last] = a[ptr]
                    last = ptr
                    if (len == 0) break
                    len = (len - 1) / 2
                    ptr = first + len
                } while (c.less(a[ptr], t))
                a[last] = t
            }
        }
    }

    private fun popHeap(first: Int, last0: Int, len: Int) {
        var last = last0
        if (len > 1) {
            val top = a[first]
            var hole = floydSiftDown(first, len)
            --last
            if (hole == last) {
                a[hole] = top
            } else {
                a[hole] = a[last]
                ++hole
                a[last] = top
                siftUp(first, hole, hole - first)
            }
        }
    }

    private fun sortHeap(first: Int, last0: Int) {
        var last = last0
        var n = last - first
        while (n > 1) {
            popHeap(first, last, n)
            --last
            --n
        }
    }
}
