package org.bytefred.ksat.cadical.full

/*
 * instantiate.hpp: candidates for variable instantiation.
 *
 * We are trying to remove literals in clauses, which occur in few clauses and further
 * restrict this removal to variables for which variable elimination failed. The set of such
 * literal clause candidate pairs is collected at the end of a variable elimination round and
 * tried before returning [AnderssonBjesseCookHanna-DAC'02].
 *
 * Mapping: 'size_t negoccs' -> Long; 'operator bool ()' -> [nonEmpty].
 */
internal class Instantiator {
    class Candidate(
        val lit: Int,
        val clause: Clause,
        val size: Int,
        val negoccs: Long,
    )

    val candidates = ArrayList<Candidate>()

    fun candidate(l: Int, c: Clause, s: Int, n: Long) {
        candidates.add(Candidate(l, c, s, n))
    }

    fun nonEmpty(): Boolean = candidates.isNotEmpty()
}
