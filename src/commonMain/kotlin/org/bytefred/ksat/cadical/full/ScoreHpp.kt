package org.bytefred.ksat.cadical.full

/*
 * score.hpp plus 'score_smaller::operator ()' (defined at the end of internal.hpp):
 * the EVSIDS decision heap 'ScoreSchedule' ordered by 'stab' with ties broken towards the
 * smaller variable index (a > b means a is smaller in the heap order, so the smaller index
 * wins among equal scores).
 */
internal class ScoreSmaller(private val internal: Internal) : IntLess {
    override fun less(a: Int, b: Int): Boolean {
        // Avoid computing twice 'abs' in 'score ()'.
        check(1 <= a)
        check(a <= internal.maxVar)
        check(1 <= b)
        check(b <= internal.maxVar)
        val s = internal.stab[a]
        val t = internal.stab[b]

        if (s < t) return true
        if (s > t) return false

        return a > b
    }
}

internal typealias ScoreSchedule = Heap
