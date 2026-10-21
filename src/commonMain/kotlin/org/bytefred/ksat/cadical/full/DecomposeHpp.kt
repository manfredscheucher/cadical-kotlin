package org.bytefred.ksat.cadical.full

/*
 * decompose.hpp: Tarjan's algorithm for decomposing the binary implication graph into
 * strongly connected components (SCCs).
 *
 * Mapping: the 'unsigned' indices -> Int holding the unsigned bit pattern; 'TRAVERSED'
 * (UINT_MAX) -> [TRAVERSED] (-1). Compare with 'toUInt ()' where upstream relies on
 * unsigned order against TRAVERSED.
 */
internal const val TRAVERSED = -1 // mark completely traversed

internal class DFS {
    var idx = 0 // depth first search index
    var min = 0 // minimum reachable index
    var parent: Clause? = null // for lrat
}
