package org.bytefred.ksat.cadical.full

import org.bytefred.ksat.cadical.IntArrayList

/*
 * proof.hpp: the abstraction layer between solver and proof tracers.
 *
 * Proof tracing is a later wave (see PORTING.md). Until then the solver keeps every call to
 * 'proof' exactly where upstream has it, as 'proof?.addDerivedClause (...)', on the field
 * 'Internal.proof', which is null (no proof requested), as upstream with 'proof == 0'.
 * This interface lists the public members of upstream 'class Proof'; proof.cpp will
 * implement it.
 *
 * Mapping: 'uint64_t' -> Long, 'const vector<int> &' -> IntArrayList,
 * 'const vector<uint64_t> &' -> List<Long>, 'ConclusionType' -> Int (TracerHpp.kt).
 */
internal interface Proof {
    fun connect(tracer: Tracer)
    fun disconnect(tracer: Tracer)

    fun addOriginalClause(id: Long, redundant: Boolean, clause: IntArrayList)
    fun addAssumptionClause(id: Long, clause: IntArrayList, chain: List<Long>)
    fun addAssumptionClause(id: Long, lit: Int, chain: List<Long>)
    fun addAssumption(lit: Int)
    fun addConstraint(clause: IntArrayList)
    fun resetAssumptions()

    fun addExternalOriginalClause(id: Long, redundant: Boolean, clause: IntArrayList, restore: Boolean = false)
    fun deleteExternalOriginalClause(id: Long, redundant: Boolean, clause: IntArrayList)

    fun addDerivedEmptyClause(id: Long, chain: List<Long>)
    fun addDerivedUnitClause(id: Long, unit: Int, chain: List<Long>)
    fun addDerivedClause(c: Clause, chain: List<Long>)
    fun addDerivedClause(id: Long, redundant: Boolean, clause: IntArrayList, chain: List<Long>)

    fun deleteClause(id: Long, redundant: Boolean, clause: IntArrayList)
    fun weakenMinus(id: Long, clause: IntArrayList)
    fun weakenPlus(id: Long, clause: IntArrayList)
    fun deleteUnitClause(id: Long, lit: Int)
    fun deleteClause(c: Clause)
    fun weakenMinus(c: Clause)
    fun weakenPlus(c: Clause)
    fun strengthen(id: Long)

    fun finalizeUnit(id: Long, lit: Int)
    fun finalizeExternalUnit(id: Long, lit: Int)
    fun finalizeClause(id: Long, clause: IntArrayList)
    fun finalizeClause(c: Clause)

    fun reportStatus(status: Int, id: Long)
    fun beginProof(id: Long)
    fun concludeUnsat(type: Int, ids: List<Long>)
    fun concludeSat(model: IntArrayList)
    fun concludeUnknown(trail: IntArrayList)
    fun solveQuery()

    fun flushClause(c: Clause) // remove falsified literals
    fun strengthenClause(c: Clause, lit: Int, chain: List<Long>)
    fun otfsStrengthenClause(c: Clause, old: IntArrayList, chain: List<Long>)
    fun flush()
}

/** Forward declaration of upstream 'class LratBuilder' (lratbuilder.hpp, proof wave). */
internal interface LratBuilder
