package org.bytefred.ksat.cadical.full

/*
 * occs.hpp: full occurrence lists used in a one-watch scheme for all clauses in subsumption
 * checking and for irredundant clauses in variable elimination.
 *
 * Mapping: 'Occs' (vector<Clause *>) -> 'ArrayList<Clause>'; shrink_occs -> 'trimToSize',
 * erase_occs -> 'clear' (capacity is not observable).
 */
internal typealias Occs = ArrayList<Clause>

internal fun shrinkOccs(os: Occs) = os.trimToSize()

internal fun eraseOccs(os: Occs) = os.clear()

internal fun removeOccs(os: Occs, c: Clause) {
    val end = os.size
    var i = 0
    for (j in 0 until end) {
        val d = os[j]
        os[i++] = d
        if (c === d) i--
    }
    check(i + 1 == end)
    os.shrinkTo(i)
}
