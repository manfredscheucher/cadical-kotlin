package org.bytefred.ksat.cadical

import org.bytefred.ksat.ExternalPropagation
import org.bytefred.ksat.ExternalPropagator
import org.bytefred.ksat.FixedAssignmentListener
import org.bytefred.ksat.FixedListening
import org.bytefred.ksat.ForcedPhases
import org.bytefred.ksat.SatResult
import org.bytefred.ksat.SatSolver
import org.bytefred.ksat.Traceable
import org.bytefred.ksat.cadical.full.SATISFIABLE
import org.bytefred.ksat.cadical.full.SOLVING
import org.bytefred.ksat.cadical.full.Solver
import org.bytefred.ksat.cadical.full.TraceSink
import org.bytefred.ksat.cadical.full.UNSATISFIABLE

/**
 * The ksat-common interfaces on top of the full CaDiCaL 2.1.3 port ([Solver] in package
 * `full`, the upstream `CaDiCaL::Solver` API). Not part of the translation: it lives outside
 * the `full` package so that package stays a 1:1 image of upstream.
 *
 * Mapping (IPASIR / IPASIR-UP, as an IPASIR user would call upstream):
 *  - [addClause] -> `add (lit)` for each literal, then `add (0)`.
 *  - [solve] -> `assume (lit)` per assumption, then `solve ()`; 10 -> SAT, 20 -> UNSAT.
 *    Assumptions are reset by upstream at the next API call that leaves the result state.
 *  - [valueOf] -> `val (v)`. Upstream only allows `val` in the satisfied state; the
 *    [SatSolver] contract reads the model of the last SAT solve, so the model of all
 *    variables is read with `val` right at the SAT exit and kept until the next solve.
 *  - [failed] -> `failed (lit)` (upstream: only in the unsatisfied state, else it throws).
 *  - the IPASIR-UP block, fixed listener and `phase` / `unphase` map 1:1 to the Solver calls.
 *
 * Contract violations: the port's `REQUIRE` throws [IllegalStateException]. The facade's
 * convention (shared with the old core port [CaDiCaL]) is [IllegalArgumentException] for an
 * invalid literal (`REQUIRE_VALID_LIT`) and for a call made while solving, e.g. from a
 * propagator callback (`REQUIRE_VALID_STATE` / `REQUIRE_READY_STATE`); those two checks are
 * made here first, everything else is left to the port.
 *
 * Variables: [numVars] is upstream `vars ()` (the largest variable index used so far); the
 * constructor argument is a capacity hint only, as in the old port: variables are created
 * lazily when a literal references them (upstream `reserve` is not called, it would create them).
 *
 * [Traceable]: the sink gets the full port's trace lines (the format shared with the
 * instrumented upstream reference in ksat-extra/shadow/cadical-full), not the old core trace.
 */
class CaDiCaLFull(
    numVarsHint: Int = 0,
) : SatSolver, Traceable, ExternalPropagation, FixedListening, ForcedPhases {

    private val solver = Solver()

    // Model of the last SAT solve (index = variable), read with 'val' at the SAT exit.
    private var model = BooleanArray(1)

    override val numVars: Int get() = solver.vars()

    override fun setTraceSink(sink: ((String) -> Unit)?) {
        solver.internal.trace = sink?.let { s -> TraceSink { s(it) } }
    }

    // ---- facade argument / state checks (see class comment) ----

    private fun requireValidLit(function: String, lit: Int) {
        require(lit != 0 && lit != Int.MIN_VALUE) { "$function: invalid literal $lit" }
    }

    private fun requireNotSolving(function: String) {
        require(solver.state() != SOLVING) { "$function: not allowed during solving (e.g. from a propagator callback)" }
    }

    // ---- IPASIR ----

    override fun addClause(literals: IntArray) {
        requireNotSolving("addClause")
        for (lit in literals) requireValidLit("addClause", lit)
        for (lit in literals) solver.add(lit)
        solver.add(0)
    }

    override fun solve(): SatResult = solve(IntArray(0))

    override fun solve(assumptions: IntArray): SatResult {
        requireNotSolving("solve")
        for (lit in assumptions) requireValidLit("solve", lit)
        for (lit in assumptions) solver.assume(lit)
        return when (val res = solver.solve()) {
            SATISFIABLE -> {
                val n = solver.vars()
                val m = BooleanArray(n + 1)
                for (v in 1..n) m[v] = solver.value(v) > 0
                model = m
                SatResult.SAT
            }
            UNSATISFIABLE -> SatResult.UNSAT
            else -> throw IllegalStateException("solve returned $res (unknown) without a limit or terminator")
        }
    }

    override fun valueOf(v: Int): Boolean {
        // A variable that appeared in no clause was never created; report false (don't-care).
        if (v < 1 || v >= model.size) return false
        return model[v]
    }

    override fun failed(lit: Int): Boolean {
        requireNotSolving("failed")
        requireValidLit("failed", lit)
        return solver.failed(lit)
    }

    // ---- IPASIR-UP ----

    override fun connectExternalPropagator(propagator: ExternalPropagator) {
        requireNotSolving("connectExternalPropagator")
        solver.connectExternalPropagator(propagator)
    }

    override fun disconnectExternalPropagator() {
        requireNotSolving("disconnectExternalPropagator")
        solver.disconnectExternalPropagator()
    }

    override fun addObservedVar(v: Int) {
        requireValidLit("addObservedVar", v)
        solver.addObservedVar(v)
    }

    override fun removeObservedVar(v: Int) {
        requireNotSolving("removeObservedVar")
        requireValidLit("removeObservedVar", v)
        solver.removeObservedVar(v)
    }

    override fun resetObservedVars() = solver.resetObservedVars()

    override fun isDecision(lit: Int): Boolean {
        requireValidLit("isDecision", lit)
        return solver.isDecision(lit)
    }

    override fun forceBacktrack(newLevel: Int) {
        require(newLevel >= 0) { "forceBacktrack: negative level $newLevel" }
        solver.forceBacktrack(newLevel)
    }

    // ---- fixed-assignment listener ----

    override fun connectFixedListener(listener: FixedAssignmentListener) {
        requireNotSolving("connectFixedListener")
        solver.connectFixedListener(listener)
    }

    override fun disconnectFixedListener() {
        requireNotSolving("disconnectFixedListener")
        solver.disconnectFixedListener()
    }

    // ---- forced phases ----

    override fun phase(lit: Int) {
        requireValidLit("phase", lit)
        solver.phase(lit)
    }

    override fun unphase(lit: Int) {
        requireValidLit("unphase", lit)
        solver.unphase(lit)
    }
}
