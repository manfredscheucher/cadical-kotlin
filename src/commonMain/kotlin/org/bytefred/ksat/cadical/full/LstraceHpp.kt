package org.bytefred.ksat.cadical.full

import org.bytefred.ksat.cadical.IntArrayList

/*
 * lstrace.hpp of the shadow reference (ksat-extra/shadow/cadical-full/trace.patch, NOT
 * upstream): the trace output shared with the instrumented C++ reference.
 *
 * Mapping: 'LSTRACE (...)' printf to stdout gated by getenv ("LSTRACE") -> a line on the
 * sink 'Internal.trace' (null = tracing off, as with LSTRACE unset). 'lstrace_lits' ->
 * [traceLits] (' l1 ... lk 0' with external literals in stored order). 'LSTRACE_PHASE (x)'
 * (scope guard printing 'START x' at entry and 'END x' at every return) ->
 * [tracePhase] wrapped around the whole function body.
 */
internal fun interface TraceSink {
    fun line(s: String)
}

/** ' l1 l2 ... lk 0' of the first [size] internal literals of [lits], externalized. */
internal fun Internal.traceLits(lits: IntArray, size: Int): String {
    val sb = StringBuilder()
    for (k in 0 until size) sb.append(' ').append(externalize(lits[k]))
    sb.append(" 0")
    return sb.toString()
}

internal fun Internal.traceLits(c: Clause): String = traceLits(c.literals, c.size)

internal fun Internal.traceLits(lits: IntArrayList): String = traceLits(lits.toArray(), lits.size)

/** LSTRACE_PHASE (name): 'START name' before and 'END name' after [body] (any return). */
internal inline fun <T> Internal.tracePhase(name: String, body: () -> T): T {
    trace?.line("START $name")
    try {
        return body()
    } finally {
        trace?.line("END $name")
    }
}
