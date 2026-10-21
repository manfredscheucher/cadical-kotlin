package org.bytefred.ksat.cadical.full

/*
 * range.hpp: safe iteration over variables ('Range') and literals ('Sange').
 *
 * Mapping:
 *  - 'for (auto idx : vars)'  -> 'for (idx in 1..maxVar)' (Kotlin ranges do not overflow at
 *    Int.MAX_VALUE, which is all 'Range' is for). [Range] exists for code that passes the
 *    range object around.
 *  - 'for (auto lit : lits)'  -> 'for (lit in lits)' with [Sange]: '-1, 1, -2, 2, ...,
 *    -max_var, max_var', computed with the same unsigned increment as upstream.
 *  - Both keep a reference to the live maximum (a getter), read when the loop starts, as the
 *    'int &n' member upstream.
 */
internal class Range(private val n: () -> Int) {
    operator fun iterator(): IntIterator {
        val end = n()
        check(end >= 0)
        return (1..end).iterator()
    }
}

internal class Sange(private val n: () -> Int) {
    operator fun iterator(): IntIterator {
        val max = n()
        check(max >= 0)
        val end = inc(max)
        return object : IntIterator() {
            private var lit = inc(0)
            override fun hasNext(): Boolean = lit != end
            override fun nextInt(): Int {
                val res = lit
                lit = inc(lit)
                return res
            }
        }
    }

    private companion object {
        // 'static unsigned inc (unsigned u) { return ~u + (u >> 31); }'
        fun inc(u: Int): Int = u.inv() + (u ushr 31)
    }
}
