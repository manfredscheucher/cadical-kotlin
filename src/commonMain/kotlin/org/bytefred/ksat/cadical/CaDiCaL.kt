package org.bytefred.ksat.cadical

import org.bytefred.ksat.Copying
import org.bytefred.ksat.ExternalPropagation
import org.bytefred.ksat.ExternalPropagator
import org.bytefred.ksat.FixedAssignmentListener
import org.bytefred.ksat.FixedListening
import org.bytefred.ksat.ForcedPhases
import org.bytefred.ksat.SatResult
import org.bytefred.ksat.SatSolver
import org.bytefred.ksat.Traceable
import org.bytefred.ksat.cadical.full.SATISFIABLE
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
 *  - [valueOf] -> `val (v) > 0`. As upstream, only allowed in the satisfied state, i.e.
 *    between a SAT [solve] and the next call that changes the formula (e.g. [addClause]).
 *  - [failed] -> `failed (lit)` (upstream: only in the unsatisfied state).
 *  - the IPASIR-UP block, fixed listener and `phase` / `unphase` map 1:1 to the Solver calls.
 *  - [copy] -> `copy (other)` into a fresh solver (irredundant clauses, units, options, flags;
 *    no learned clauses, no assumptions — upstream semantics).
 *
 * Contract violations: this adapter makes no checks of its own. Every API misuse (invalid
 * literal, call in the wrong state, e.g. from a propagator callback while solving) fails in
 * the port's `REQUIRE` exactly where upstream fails, with [IllegalStateException]
 * (contract.hpp `CONTRACT_VIOLATED` -> `contractRequire`).
 *
 * [forceBacktrack]: upstream takes `size_t new_level`; a negative Int is the port's image of
 * a huge `size_t`, so `new_level >= level` holds and upstream (and the port) return without
 * effect (external_propagate.cpp `Internal::force_backtrack`).
 *
 * Variables: [numVars] is upstream `vars ()` (the largest variable index used so far); the
 * constructor argument is a capacity hint only: variables are created
 * lazily when a literal references them (upstream `reserve` is not called, it would create them).
 *
 * [Traceable]: the sink gets the full port's trace lines (the format shared with the
 * instrumented upstream reference in ksat-extra/shadow/cadical-full).
 */
class CaDiCaL(
    numVarsHint: Int = 0,
) : SatSolver, Traceable, ExternalPropagation, FixedListening, ForcedPhases, Copying {

    private val solver = Solver()

    override val numVars: Int get() = solver.vars()

    override fun setTraceSink(sink: ((String) -> Unit)?) {
        solver.internal.trace = sink?.let { s -> TraceSink { s(it) } }
    }

    // ---- IPASIR ----

    override fun addClause(literals: IntArray) {
        for (lit in literals) solver.add(lit)
        solver.add(0)
    }

    override fun solve(): SatResult = solve(IntArray(0))

    override fun solve(assumptions: IntArray): SatResult {
        for (lit in assumptions) solver.assume(lit)
        return when (val res = solver.solve()) {
            SATISFIABLE -> SatResult.SAT
            UNSATISFIABLE -> SatResult.UNSAT
            else -> throw IllegalStateException("solve returned $res (unknown) without a limit or terminator")
        }
    }

    override fun valueOf(v: Int): Boolean = solver.value(v) > 0

    override fun failed(lit: Int): Boolean = solver.failed(lit)

    // ---- IPASIR-UP ----

    override fun connectExternalPropagator(propagator: ExternalPropagator) =
        solver.connectExternalPropagator(propagator)

    override fun disconnectExternalPropagator() = solver.disconnectExternalPropagator()

    override fun addObservedVar(v: Int) = solver.addObservedVar(v)

    override fun removeObservedVar(v: Int) = solver.removeObservedVar(v)

    override fun resetObservedVars() = solver.resetObservedVars()

    override fun isDecision(lit: Int): Boolean = solver.isDecision(lit)

    override fun forceBacktrack(newLevel: Int) = solver.forceBacktrack(newLevel)

    // ---- fixed-assignment listener ----

    override fun connectFixedListener(listener: FixedAssignmentListener) = solver.connectFixedListener(listener)

    override fun disconnectFixedListener() = solver.disconnectFixedListener()

    // ---- forced phases ----

    override fun phase(lit: Int) = solver.phase(lit)

    override fun unphase(lit: Int) = solver.unphase(lit)

    // ---- copy ----

    override fun copy(): CaDiCaL = CaDiCaL().also { solver.copy(it.solver) }
}
