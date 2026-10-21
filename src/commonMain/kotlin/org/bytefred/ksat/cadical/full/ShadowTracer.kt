package org.bytefred.ksat.cadical.full

/*
 * The proof tracer of the shadow reference driver (NOT upstream):
 * 'class LsTracer' in ksat-extra/shadow/cadical-full/driver.cpp. It prints every clause
 * addition / deletion reported to proof tracers as ADD / DEL / WEAKEN / STRENGTHEN lines,
 * with the external literals in the order the solver passes them, to [sink].
 *
 * The driver connects it with 'connect_proof_tracer (&tracer, false, false)' before
 * 'read_dimacs' (Kotlin: 'connectProofTracer (ShadowTracer (sink), false, false)').
 * RESULT / MODEL are printed by the driver itself, not by this tracer.
 */
internal class ShadowTracer(
    private val sink: TraceSink,
) : Tracer {
    private fun lits(c: List<Int>): String {
        val sb = StringBuilder()
        for (lit in c) sb.append(' ').append(lit)
        sb.append(" 0")
        return sb.toString()
    }

    private fun kind(redundant: Boolean): String = if (redundant) "red" else "irr"

    override fun addOriginalClause(id: Long, redundant: Boolean, clause: List<Int>, restored: Boolean) {
        sink.line("ADD ${if (restored) "R" else "O"} ${id.toULong()} ${kind(redundant)} :${lits(clause)}")
    }

    override fun addDerivedClause(id: Long, redundant: Boolean, clause: List<Int>, antecedents: List<Long>) {
        sink.line("ADD D ${id.toULong()} ${kind(redundant)} :${lits(clause)}")
    }

    override fun deleteClause(id: Long, redundant: Boolean, clause: List<Int>) {
        sink.line("DEL ${id.toULong()} ${kind(redundant)} :${lits(clause)}")
    }

    override fun weakenMinus(id: Long, clause: List<Int>) {
        sink.line("WEAKEN ${id.toULong()} :${lits(clause)}")
    }

    override fun strengthen(id: Long) {
        sink.line("STRENGTHEN ${id.toULong()}")
    }

    override fun addAssumptionClause(id: Long, clause: List<Int>, antecedents: List<Long>) {
        sink.line("ADD A ${id.toULong()} :${lits(clause)}")
    }
}
