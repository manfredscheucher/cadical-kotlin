package org.bytefred.ksat.cadical.full

import org.bytefred.ksat.cadical.IntArrayList

/*
 * proof.hpp + the members of 'class Proof' defined in proof.cpp (Kotlin cannot split a
 * class over files, see PORTING.md); the 'Internal::' functions of proof.cpp are in Proof.kt.
 *
 * The solver keeps every call to 'proof' exactly where upstream has it, as
 * 'proof?.addDerivedClause (...)' on the field 'Internal.proof', which is null unless a
 * tracer is connected (upstream 'proof == 0').
 *
 * Mapping: 'uint64_t' -> Long, 'const vector<int> &' arguments -> IntArrayList (the solver's
 * vectors), 'const vector<uint64_t> &' -> List<Long>, 'ConclusionType' -> Int (TracerHpp.kt).
 * The member vectors 'clause' (external literals) and 'proof_chain' are ArrayLists, since
 * they are handed to the tracers by reference ('const std::vector<int> &' -> List<Int>).
 */
internal class Proof(
    private val internal: Internal,
) {
    private val clause = ArrayList<Int>() // of external literals
    private val proofChain = ArrayList<Long>() // LRAT style proof chain of clause
    private var clauseId = 0L // id of added clause
    private var redundant = false

    // the 'tracers'
    private val tracers = ArrayList<Tracer>() // tracers (ie checker)
    // 'vector<FileTracer *> file_tracers' is declared in proof.hpp but never used upstream
    // (file tracers live in 'Internal::file_tracers'): not ported.
    private var lratbuilder: LratBuilder? = null // special tracer

    fun connect(lb: LratBuilder) {
        lratbuilder = lb
    }

    fun connect(t: Tracer) {
        tracers.add(t)
    }

    fun disconnect(t: Tracer) {
        tracers.removeAll { it === t }
    }

    /*------------------------------------------------------------------------*/

    private fun addLiteral(internalLit: Int) {
        val externalLit = internal.externalize(internalLit)
        clause.add(externalLit)
    }

    private fun addLiterals(c: Clause) {
        for (k in 0 until c.size) addLiteral(c.literals[k])
    }

    private fun addLiterals(c: IntArrayList) {
        for (k in 0 until c.size) addLiteral(c[k])
    }

    /*------------------------------------------------------------------------*/

    fun addOriginalClause(id: Long, r: Boolean, c: IntArrayList) {
        addLiterals(c)
        clauseId = id
        redundant = r
        addOriginalClause()
    }

    fun addExternalOriginalClause(id: Long, r: Boolean, c: IntArrayList, restore: Boolean = false) {
        // literals of c are already external
        check(clause.isEmpty()) { "proof clause not empty" }
        for (k in 0 until c.size) clause.add(c[k])
        clauseId = id
        redundant = r
        addOriginalClause(restore)
    }

    fun deleteExternalOriginalClause(id: Long, r: Boolean, c: IntArrayList) {
        // literals of c are already external
        check(clause.isEmpty()) { "proof clause not empty" }
        for (k in 0 until c.size) clause.add(c[k])
        clauseId = id
        redundant = r
        deleteClause()
    }

    fun addDerivedEmptyClause(id: Long, chain: List<Long>) {
        check(clause.isEmpty()) { "proof clause not empty" }
        check(proofChain.isEmpty()) { "proof chain not empty" }
        for (cid in chain) proofChain.add(cid)
        clauseId = id
        redundant = false
        addDerivedClause()
    }

    fun addDerivedUnitClause(id: Long, internalUnit: Int, chain: List<Long>) {
        check(proofChain.isEmpty()) { "proof chain not empty" }
        check(clause.isEmpty()) { "proof clause not empty" }
        addLiteral(internalUnit)
        for (cid in chain) proofChain.add(cid)
        clauseId = id
        redundant = false
        addDerivedClause()
    }

    /*------------------------------------------------------------------------*/

    fun addDerivedClause(c: Clause, chain: List<Long>) {
        check(clause.isEmpty()) { "proof clause not empty" }
        check(proofChain.isEmpty()) { "proof chain not empty" }
        addLiterals(c)
        for (cid in chain) proofChain.add(cid)
        clauseId = c.id
        redundant = c.redundant
        addDerivedClause()
    }

    fun addDerivedClause(id: Long, r: Boolean, c: IntArrayList, chain: List<Long>) {
        check(clause.isEmpty()) { "proof clause not empty" }
        check(proofChain.isEmpty()) { "proof chain not empty" }
        for (k in 0 until c.size) addLiteral(c[k])
        for (cid in chain) proofChain.add(cid)
        clauseId = id
        redundant = r
        addDerivedClause()
    }

    fun addAssumptionClause(id: Long, c: IntArrayList, chain: List<Long>) {
        // literals of c are already external
        check(clause.isEmpty()) { "proof clause not empty" }
        check(proofChain.isEmpty()) { "proof chain not empty" }
        for (k in 0 until c.size) clause.add(c[k])
        for (cid in chain) proofChain.add(cid)
        clauseId = id
        addAssumptionClause()
    }

    fun addAssumption(a: Int) {
        // a is already external
        check(clause.isEmpty()) { "proof clause not empty" }
        check(proofChain.isEmpty()) { "proof chain not empty" }
        clause.add(a)
        addAssumption()
    }

    fun addConstraint(c: IntArrayList) {
        // literals of c are already external
        check(clause.isEmpty()) { "proof clause not empty" }
        check(proofChain.isEmpty()) { "proof chain not empty" }
        for (k in 0 until c.size) clause.add(c[k])
        addConstraint()
    }

    fun addAssumptionClause(id: Long, lit: Int, chain: List<Long>) {
        check(clause.isEmpty()) { "proof clause not empty" }
        check(proofChain.isEmpty()) { "proof chain not empty" }
        clause.add(lit)
        for (cid in chain) proofChain.add(cid)
        clauseId = id
        addAssumptionClause()
    }

    fun deleteClause(c: Clause) {
        clause.clear() // Can be non-empty if an allocation fails during adding.
        addLiterals(c)
        clauseId = c.id
        redundant = c.redundant
        deleteClause() // Increments 'statistics.deleted'.
    }

    fun deleteClause(id: Long, r: Boolean, c: IntArrayList) {
        check(clause.isEmpty()) { "proof clause not empty" }
        addLiterals(c)
        clauseId = id
        redundant = r
        deleteClause() // Increments 'statistics.deleted'.
    }

    fun weakenMinus(c: Clause) {
        check(clause.isEmpty()) { "proof clause not empty" }
        addLiterals(c)
        clauseId = c.id
        weakenMinus()
    }

    fun weakenMinus(id: Long, c: IntArrayList) {
        check(clause.isEmpty()) { "proof clause not empty" }
        addLiterals(c)
        clauseId = id
        weakenMinus()
    }

    fun weakenPlus(c: Clause) {
        weakenMinus(c)
        deleteClause(c) // Increments 'statistics.deleted'.
    }

    fun weakenPlus(id: Long, c: IntArrayList) {
        weakenMinus(id, c)
        deleteClause(id, false, c) // Increments 'statistics.deleted'.
    }

    fun deleteUnitClause(id: Long, lit: Int) {
        check(clause.isEmpty()) { "proof clause not empty" }
        addLiteral(lit)
        clauseId = id
        redundant = false
        deleteClause()
    }

    fun finalizeClause(c: Clause) {
        check(clause.isEmpty()) { "proof clause not empty" }
        addLiterals(c)
        clauseId = c.id
        finalizeClause()
    }

    fun finalizeClause(id: Long, c: IntArrayList) {
        check(clause.isEmpty()) { "proof clause not empty" }
        for (k in 0 until c.size) addLiteral(c[k])
        clauseId = id
        finalizeClause()
    }

    fun finalizeUnit(id: Long, lit: Int) {
        check(clause.isEmpty()) { "proof clause not empty" }
        addLiteral(lit)
        clauseId = id
        finalizeClause()
    }

    fun finalizeExternalUnit(id: Long, lit: Int) {
        check(clause.isEmpty()) { "proof clause not empty" }
        clause.add(lit)
        clauseId = id
        finalizeClause()
    }

    /*------------------------------------------------------------------------*/

    // During garbage collection clauses are shrunken by removing falsified
    // literals. To avoid copying the clause, we provide a specialized tracing
    // function here, which traces the required 'add' and 'remove' operations.

    fun flushClause(c: Clause) {
        check(clause.isEmpty()) { "proof clause not empty" }
        val antecedents = (internal.lrat || internal.frat)
        for (i in 0 until c.size) {
            val internalLit = c.literals[i]
            if (internal.fixed(internalLit) < 0) {
                if (antecedents) {
                    val uidx = internal.vlit(-internalLit)
                    val id = internal.unitClauses(uidx)
                    check(id != 0L) { "missing unit clause id" }
                    proofChain.add(id)
                }
                continue
            }
            addLiteral(internalLit)
        }
        proofChain.add(c.id)
        redundant = c.redundant
        val id = ++internal.clauseId
        clauseId = id
        addDerivedClause()
        deleteClause(c)
        c.id = id
    }

    // While strengthening clauses, e.g., through self-subsuming resolutions,
    // during subsumption checking, we have a similar situation, except that we
    // have to remove exactly one literal.  Again the following function allows
    // to avoid copying the clause and instead provides tracing of the required
    // 'add' and 'remove' operations.

    fun strengthenClause(c: Clause, remove: Int, chain: List<Long>) {
        check(clause.isEmpty()) { "proof clause not empty" }
        for (i in 0 until c.size) {
            val internalLit = c.literals[i]
            if (internalLit == remove) continue
            addLiteral(internalLit)
        }
        val id = ++internal.clauseId
        clauseId = id
        redundant = c.redundant
        for (cid in chain) proofChain.add(cid)
        addDerivedClause()
        deleteClause(c)
        c.id = id
    }

    fun otfsStrengthenClause(c: Clause, old: IntArrayList, chain: List<Long>) {
        check(clause.isEmpty()) { "proof clause not empty" }
        for (i in 0 until c.size) {
            val internalLit = c.literals[i]
            addLiteral(internalLit)
        }
        val id = ++internal.clauseId
        clauseId = id
        redundant = c.redundant
        for (cid in chain) proofChain.add(cid)
        addDerivedClause()
        deleteClause(c.id, c.redundant, old)
        c.id = id
    }

    fun strengthen(id: Long) {
        clauseId = id
        strengthen()
    }

    /*------------------------------------------------------------------------*/

    private fun addOriginalClause(restore: Boolean = false) {
        check(clauseId != 0L) { "original clause without id" }

        lratbuilder?.addOriginalClause(clauseId, clause)
        for (tracer in tracers) {
            tracer.addOriginalClause(clauseId, false, clause, restore)
        }
        clause.clear()
        clauseId = 0
    }

    private fun addDerivedClause() {
        check(clauseId != 0L) { "derived clause without id" }
        val lb = lratbuilder
        if (lb != null) {
            val chain = lb.addClauseGetProof(clauseId, clause)
            proofChain.clear() // 'proof_chain = ...' (vector copy assignment)
            proofChain.addAll(chain)
        }
        for (tracer in tracers) {
            tracer.addDerivedClause(clauseId, redundant, clause, proofChain)
        }
        proofChain.clear()
        clause.clear()
        clauseId = 0
    }

    private fun deleteClause() {
        lratbuilder?.deleteClause(clauseId, clause)
        for (tracer in tracers) {
            tracer.deleteClause(clauseId, redundant, clause)
        }
        clause.clear()
        clauseId = 0
    }

    private fun weakenMinus() {
        for (tracer in tracers) {
            tracer.weakenMinus(clauseId, clause)
        }
        clause.clear()
        clauseId = 0
    }

    private fun strengthen() {
        for (tracer in tracers) {
            tracer.strengthen(clauseId)
        }
        clauseId = 0
    }

    private fun finalizeClause() {
        for (tracer in tracers) {
            tracer.finalizeClause(clauseId, clause)
        }
        clause.clear()
        clauseId = 0
    }

    private fun addAssumptionClause() {
        val lb = lratbuilder
        if (lb != null) {
            val chain = lb.addClauseGetProof(clauseId, clause)
            proofChain.clear() // 'proof_chain = ...' (vector copy assignment)
            proofChain.addAll(chain)
            lb.deleteClause(clauseId, clause)
        }
        for (tracer in tracers) {
            tracer.addAssumptionClause(clauseId, clause, proofChain)
        }
        proofChain.clear()
        clause.clear()
        clauseId = 0
    }

    private fun addAssumption() {
        check(clause.size == 1) { "assumption must be a single literal" }
        for (tracer in tracers) {
            tracer.addAssumption(clause.last())
        }
        clause.clear()
    }

    private fun addConstraint() {
        for (tracer in tracers) {
            tracer.addConstraint(clause)
        }
        clause.clear()
    }

    fun resetAssumptions() {
        for (tracer in tracers) {
            tracer.resetAssumptions()
        }
    }

    fun reportStatus(status: Int, id: Long) {
        for (tracer in tracers) {
            tracer.reportStatus(status, id)
        }
    }

    fun beginProof(id: Long) {
        for (tracer in tracers) {
            tracer.beginProof(id)
        }
    }

    fun solveQuery() {
        for (tracer in tracers) {
            tracer.solveQuery()
        }
    }

    fun concludeUnsat(con: Int, conclusion: List<Long>) {
        for (tracer in tracers) {
            tracer.concludeUnsat(con, conclusion)
        }
    }

    fun concludeSat(model: IntArrayList) {
        val m = model.toArray().asList() // 'const vector<int> &' handed on read-only
        for (tracer in tracers) {
            tracer.concludeSat(m)
        }
    }

    fun concludeUnknown(trail: IntArrayList) {
        val t = trail.toArray().asList() // 'const vector<int> &' handed on read-only
        for (tracer in tracers) {
            tracer.concludeUnknown(t)
        }
    }

    // 'void flush ()' is declared in proof.hpp but never defined or called upstream: not ported.
}
