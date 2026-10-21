package org.bytefred.ksat.cadical.full

/*
 * tracer.hpp: proof tracer interfaces (DRAT/LRAT/FRAT/VeriPB/IDRUP tracers, checkers).
 *
 * The tracers themselves are a later wave (see PORTING.md). Mapping: virtual methods with an
 * empty body -> interface methods with an empty default; 'uint64_t' -> Long;
 * 'const std::vector<int> &' -> List<Int>, 'const std::vector<uint64_t> &' -> List<Long>.
 */

// 'enum ConclusionType'.
internal const val CONFLICT = 1
internal const val ASSUMPTIONS = 2
internal const val CONSTRAINT = 4

internal interface Tracer {
    // Basic Events

    fun addOriginalClause(id: Long, redundant: Boolean, clause: List<Int>, restored: Boolean = false) {}

    fun addDerivedClause(id: Long, redundant: Boolean, clause: List<Int>, antecedents: List<Long>) {}

    fun deleteClause(id: Long, redundant: Boolean, clause: List<Int>) {}

    fun weakenMinus(id: Long, clause: List<Int>) {}

    fun strengthen(id: Long) {}

    fun reportStatus(status: Int, id: Long) {}

    // Specifically non-incremental

    fun finalizeClause(id: Long, clause: List<Int>) {}

    fun beginProof(id: Long) {}

    // Specifically incremental

    fun solveQuery() {}

    fun addAssumption(lit: Int) {}

    fun addConstraint(clause: List<Int>) {}

    fun resetAssumptions() {}

    fun addAssumptionClause(id: Long, clause: List<Int>, antecedents: List<Long>) {}

    fun concludeUnsat(type: Int, ids: List<Long>) {}

    fun concludeSat(model: List<Int>) {}

    fun concludeUnknown(trail: List<Int>) {}
}

internal interface InternalTracer : Tracer {
    fun connectInternal(internal: Internal) {}
}

internal interface StatTracer : InternalTracer {
    fun printStats() {}
}

internal interface FileTracer : InternalTracer {
    fun closed(): Boolean
    fun close(print: Boolean = false)
    fun flush(print: Boolean = false)
}
