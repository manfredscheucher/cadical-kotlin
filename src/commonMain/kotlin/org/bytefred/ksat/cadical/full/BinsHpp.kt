package org.bytefred.ksat.cadical.full

/*
 * bins.hpp: binary implication graph entries. 'uint64_t id' -> Long.
 * 'Bins' (vector<Bin>) -> 'ArrayList<Bin>'; shrink_bins -> 'trimToSize', erase_bins -> 'clear'.
 */
internal class Bin(
    var lit: Int,
    var id: Long,
)

internal typealias Bins = ArrayList<Bin>

internal fun shrinkBins(bs: Bins) = bs.trimToSize()

internal fun eraseBins(bs: Bins) = bs.clear()
