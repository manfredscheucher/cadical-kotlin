package org.bytefred.ksat.cadical.full

import kotlin.math.abs
import kotlin.math.max
import org.bytefred.ksat.cadical.IntArrayList
import org.bytefred.ksat.cadical.full.isValidLimit as internalIsValidLimit

/*
 * solver.cpp (+ the 'Solver' class of cadical.hpp and the state shortcuts of contract.hpp):
 * the public API with its state machine and contract checks.
 *
 * Mapping:
 *  - 'REQUIRE (COND, ...)' -> [contractRequire] (throws). 'REQUIRE_INITIALIZED' and
 *    'REQUIRE_NON_ZERO_THIS' cannot fail (non-null 'internal' / 'external' / receiver) and
 *    are dropped; the state shortcuts are the private 'require*' functions below.
 *  - 'STATE (S)' -> [state] transition with the power-of-two check.
 *  - API call tracing ('TRACE', 'CADICAL_API_TRACE', 'trace_api_calls'), the environment
 *    variable LIDRUP tracing ('CADICAL_LIDRUP_TRACE', so 'tracing_nb_lidrup_env_var_method'
 *    is always false) and API logging ('LOG_API_CALL_*') are output only and not ported.
 *  - '~Solver' -> [delete] (state transition only).
 *  - Methods printing to the terminal ('build', 'options', 'usage', 'configurations',
 *    'resources') keep their state checks, the printing is dropped; 'section', 'message'
 *    and 'verbose' are dropped. 'statistics' calls 'Internal.printStatistics' as upstream. 'error' throws.
 *  - Reading and writing files by path or 'FILE *' (OS I/O) -> the same functions on an
 *    in-memory text ([readDimacs], [readSolution]) or an [Appendable] ([writeDimacs],
 *    [writeExtension], [traceProof]) or a byte [FileSink] ([traceProof]) through [File]. 'trace_proof (const char *path)'
 *    (opens the file by path) is not ported.
 *  - 'const char *' error results -> String? (null = success).
 *  - 'Solver::CubesWithStatus' -> [CubesWithStatus] (deep copy as the C++ struct copy).
 */
internal class Solver {

    // Kept for the parser ('Parser' accesses 'internal' and 'external').
    val internal: Internal
    val external: External

    private var addingClause = false
    private var addingConstraint = false

    private var _state = INITIALIZING // API states as discussed in 'cadical.hpp'.

    /*------------------------------------------------------------------------*/

    // Log state transitions.

    private fun state(s: Int) {
        check(isPowerOfTwo(s)) { "STATE: $s is not a single state" }
        if (_state == s) return
        _state = s
    }

    /*------------------------------------------------------------------------*/

    // These are common shortcuts for 'Solver' API contracts (requirements).

    private fun requireValidState(function: String) {
        contractRequire((state() and VALID) != 0, function) { "solver in invalid state" }
    }

    private fun requireReadyState(function: String) {
        requireValidState(function)
        contractRequire(state() != ADDING, function) { "clause incomplete (terminating zero not added)" }
    }

    private fun requireValidOrSolvingState(function: String) {
        contractRequire((state() and (VALID or SOLVING)) != 0, function) {
            "solver neither in valid nor solving state"
        }
    }

    private fun requireValidLit(function: String, lit: Int) {
        contractRequire(lit != 0 && lit != Int.MIN_VALUE, function) { "invalid literal '$lit'" }
    }

    private fun requireSteadyState(function: String) {
        contractRequire((state() and STEADY) != 0, function) { "solver is not in steady state" }
    }

    /*------------------------------------------------------------------------*/

    private fun transitionToSteadyState() {
        if (state() == CONFIGURING) {
            if (internal.opts.check != 0 && internal.opts.checkproof != 0) {
                internal.check()
            }
        } else if (state() == SATISFIED) {
            external.resetAssumptions()
            external.resetConcluded()
            external.resetConstraint()
        } else if (state() == UNSATISFIED) {
            external.resetAssumptions()
            external.resetConcluded()
            external.resetConstraint()
        }
        if (state() != STEADY)
            state(STEADY)
    }

    /*------------------------------------------------------------------------*/

    init {
        addingClause = false
        addingConstraint = false
        _state = INITIALIZING
        internal = Internal()
        external = External(internal)
        state(CONFIGURING)
    }

    // '~Solver ()'.
    fun delete() {
        requireValidOrSolvingState("Solver::~Solver")
        state(DELETING)
    }

    /*------------------------------------------------------------------------*/

    // Return the current state of the solver as defined above.
    //
    fun state(): Int = _state

    // Similar to 'state ()' but using the standard competition exit codes of
    // '10' for 'SATISFIABLE', '20' for 'UNSATISFIABLE' and '0' otherwise.
    //
    fun status(): Int {
        if (_state == SATISFIED)
            return 10
        else if (_state == UNSATISFIED)
            return 20
        else
            return 0
    }

    /*------------------------------------------------------------------------*/

    fun vars(): Int {
        requireValidOrSolvingState("Solver::vars")
        val res = external.maxVar
        return res
    }

    fun reserve(minMaxVar: Int) {
        requireValidState("Solver::reserve")
        transitionToSteadyState()
        external.resetExtended()
        external.init(minMaxVar)
    }

    /*------------------------------------------------------------------------*/

    fun get(arg: String): Int {
        requireValidOrSolvingState("Solver::get")
        return internal.opts.get(arg)
    }

    fun set(arg: String, v: Int): Boolean {
        requireValidState("Solver::set")
        if (arg != "log" && arg != "quiet" && arg != "report" && arg != "verbose") {
            contractRequire(state() == CONFIGURING, "Solver::set") {
                "can only set option 'set (\"$arg\", $v)' right after initialization"
            }
        }
        val res = internal.opts.set(arg, v)

        return res
    }

    fun setLongOption(arg: String): Boolean {
        requireValidState("Solver::set_long_option")
        contractRequire(state() == CONFIGURING, "Solver::set_long_option") {
            "can only set option '$arg' right after initialization"
        }
        val res: Boolean
        if (arg.length < 2 || arg[0] != '-' || arg[1] != '-')
            res = false
        else {
            val parsed = Options.parseLongOption(arg)
            res = parsed != null
            if (parsed != null)
                set(parsed.first, parsed.second)
        }
        return res
    }

    fun optimize(arg: Int) {
        requireValidState("Solver::optimize")
        internal.opts.optimize(arg)
    }

    fun limit(arg: String, v: Int): Boolean {
        requireValidState("Solver::limit")
        val res = internal.limit(arg, v)
        return res
    }

    fun prefix(str: String) {
        requireValidOrSolvingState("Solver::prefix")
        internal.prefix = str
    }

    fun configure(name: String): Boolean {
        requireValidState("Solver::configure")
        contractRequire(state() == CONFIGURING, "Solver::configure") {
            "can only set configuration '$name' right after initialization"
        }
        val res = Config.set(internal.opts, name)
        return res
    }

    /*===== IPASIR BEGIN =====================================================*/

    fun add(lit: Int) {
        requireValidState("Solver::add")
        if (lit != 0)
            requireValidLit("Solver::add", lit)
        transitionToSteadyState()
        external.add(lit)
        addingClause = lit != 0
        if (addingClause)
            state(ADDING)
        else if (!addingConstraint)
            state(STEADY)
    }

    fun clause(a: Int) {
        requireValidLit("Solver::clause", a)
        add(a); add(0)
    }

    fun clause(a: Int, b: Int) {
        requireValidLit("Solver::clause", a)
        requireValidLit("Solver::clause", b)
        add(a); add(b); add(0)
    }

    fun clause(a: Int, b: Int, c: Int) {
        requireValidLit("Solver::clause", a)
        requireValidLit("Solver::clause", b)
        requireValidLit("Solver::clause", c)
        add(a); add(b); add(c); add(0)
    }

    fun clause(a: Int, b: Int, c: Int, d: Int) {
        requireValidLit("Solver::clause", a)
        requireValidLit("Solver::clause", b)
        requireValidLit("Solver::clause", c)
        requireValidLit("Solver::clause", d)
        add(a); add(b); add(c); add(d); add(0)
    }

    fun clause(a: Int, b: Int, c: Int, d: Int, e: Int) {
        requireValidLit("Solver::clause", a)
        requireValidLit("Solver::clause", b)
        requireValidLit("Solver::clause", c)
        requireValidLit("Solver::clause", d)
        requireValidLit("Solver::clause", e)
        add(a); add(b); add(c); add(d); add(e); add(0)
    }

    // 'clause (const int *lits, size_t size)'.
    fun clause(lits: IntArray, size: Int) {
        for (p in 0 until size) {
            val lit = lits[p]
            requireValidLit("Solver::clause", lit)
            add(lit)
        }
        add(0)
    }

    // 'clause (const std::vector<int> &lits)'.
    fun clause(lits: List<Int>) {
        for (lit in lits) {
            requireValidLit("Solver::clause", lit)
            add(lit)
        }
        add(0)
    }

    fun inconsistent(): Boolean = internal.unsat

    fun constrain(lit: Int) {
        requireValidState("Solver::constrain")
        if (lit != 0)
            requireValidLit("Solver::constrain", lit)
        transitionToSteadyState()
        external.constrain(lit)
        addingConstraint = lit != 0
        if (addingConstraint)
            state(ADDING)
        else if (!addingClause)
            state(STEADY)
    }

    fun assume(lit: Int) {
        requireValidState("Solver::assume")
        requireValidLit("Solver::assume", lit)
        transitionToSteadyState()
        external.assume(lit)
    }

    fun lookahead(): Int {
        requireValidOrSolvingState("Solver::lookahead")
        val lit = external.lookahead()
        return lit
    }

    fun generateCubes(depth: Int, minDepth: Int = 0): CubesWithStatus {
        requireValidOrSolvingState("Solver::generate_cubes")
        val cubes = external.generateCubes(depth, minDepth)

        val cubes2 = CubesWithStatus()
        cubes2.status = cubes.status
        for (cube in cubes.cubes) {
            val copy = IntArrayList()
            copy.assign(cube)
            cubes2.cubes.add(copy)
        }
        return cubes2
    }

    fun resetAssumptions() {
        requireValidState("Solver::reset_assumptions")
        transitionToSteadyState()
        external.resetAssumptions()
        external.resetConcluded()
    }

    fun resetConstraint() {
        requireValidState("Solver::reset_constraint")
        transitionToSteadyState()
        external.resetConstraint()
        external.resetConcluded()
    }

    /*------------------------------------------------------------------------*/

    fun propagate(): Int {
        requireValidState("Solver::propagate")
        transitionToSteadyState()
        val res = external.propagateAssumptions()
        // 'tracing_nb_lidrup_env_var_method' is always false (not ported).
        if (res == 10)
            state(SATISFIED)
        else if (res == 20)
            state(UNSATISFIED)
        else
            state(STEADY)
        return res
    }

    fun getEntrailedLiterals(entrailed: IntArrayList) {
        requireSteadyState("Solver::get_entrailed_literals")
        external.concludeUnknown()
        external.getEntrailedLiterals(entrailed)
    }

    /*------------------------------------------------------------------------*/

    private fun callExternalSolveAndCheckResults(preprocessOnly: Boolean): Int {
        transitionToSteadyState()
        check((state() and READY) != 0) { "solve: not in ready state" }
        state(SOLVING)
        val res = external.solve(preprocessOnly)
        if (res == 10)
            state(SATISFIED)
        else if (res == 20)
            state(UNSATISFIED)
        else
            state(STEADY)
        if (res == 0) {
            external.resetAssumptions()
            external.resetConstraint()
            external.resetConcluded()
        }
        return res
    }

    fun solve(): Int {
        requireReadyState("Solver::solve")
        val res = callExternalSolveAndCheckResults(false)
        return res
    }

    fun simplify(rounds: Int = 3): Int {
        requireReadyState("Solver::simplify")
        contractRequire(rounds >= 0, "Solver::simplify") {
            "negative number of simplification rounds '$rounds'"
        }
        internal.limit("preprocessing", rounds)
        val res = callExternalSolveAndCheckResults(true)
        return res
    }

    /*------------------------------------------------------------------------*/

    fun value(lit: Int): Int {
        requireValidState("Solver::val")
        requireValidLit("Solver::val", lit)
        contractRequire(state() == SATISFIED, "Solver::val") { "can only get value in satisfied state" }
        if (!external.extended)
            external.extend()
        external.concludeSat()
        val res = external.ival(lit)
        check(state() == SATISFIED) { "val: left satisfied state" }
        check(res == lit || res == -lit) { "val: bad value $res for $lit" }
        return res
    }

    fun flip(lit: Int): Boolean {
        requireValidState("Solver::flip")
        requireValidLit("Solver::flip", lit)
        contractRequire(state() == SATISFIED, "Solver::flip") { "can only flip value in satisfied state" }
        contractRequire(external.propagator == null, "Solver::flip") {
            "can only flip when no external propagator is present"
        }
        val res = external.flip(lit)
        check(state() == SATISFIED) { "flip: left satisfied state" }
        return res
    }

    fun flippable(lit: Int): Boolean {
        requireValidState("Solver::flippable")
        requireValidLit("Solver::flippable", lit)
        contractRequire(state() == SATISFIED, "Solver::flippable") { "can only flip value in satisfied state" }
        contractRequire(external.propagator == null, "Solver::flippable") {
            "can only flip when no external propagator is present"
        }
        val res = external.flippable(lit)
        check(state() == SATISFIED) { "flippable: left satisfied state" }
        return res
    }

    fun failed(lit: Int): Boolean {
        requireValidState("Solver::failed")
        requireValidLit("Solver::failed", lit)
        contractRequire(state() == UNSATISFIED, "Solver::failed") {
            "can only get failed assumptions in unsatisfied state"
        }
        val res = external.failed(lit)
        check(state() == UNSATISFIED) { "failed: left unsatisfied state" }
        return res
    }

    fun constraintFailed(): Boolean {
        requireValidState("Solver::constraint_failed")
        contractRequire(state() == UNSATISFIED, "Solver::constraint_failed") {
            "can only determine if constraint failed in unsatisfied state"
        }
        val res = external.failedConstraint()
        check(state() == UNSATISFIED) { "constraint_failed: left unsatisfied state" }
        return res
    }

    fun fixed(lit: Int): Int {
        requireValidState("Solver::fixed")
        requireValidLit("Solver::fixed", lit)
        val res = external.fixed(lit)
        return res
    }

    fun phase(lit: Int) {
        requireValidOrSolvingState("Solver::phase")
        requireValidLit("Solver::phase", lit)
        external.phase(lit)
    }

    fun unphase(lit: Int) {
        requireValidOrSolvingState("Solver::unphase")
        requireValidLit("Solver::unphase", lit)
        external.unphase(lit)
    }

    /*------------------------------------------------------------------------*/

    fun terminate() {
        requireValidOrSolvingState("Solver::terminate")
        external.terminate()
    }

    fun connectTerminator(terminator: Terminator) {
        requireValidState("Solver::connect_terminator")
        external.terminator = terminator
    }

    fun disconnectTerminator() {
        requireValidState("Solver::disconnect_terminator")
        external.terminator = null
    }

    /*------------------------------------------------------------------------*/

    fun connectLearner(learner: Learner) {
        requireValidState("Solver::connect_learner")
        external.learner = learner
    }

    fun disconnectLearner() {
        requireValidState("Solver::disconnect_learner")
        external.learner = null
    }

    /*===== IPASIR END =======================================================*/

    fun connectFixedListener(fixedListener: FixedAssignmentListener) {
        requireValidState("Solver::connect_fixed_listener")
        if (external.fixedListener != null)
            disconnectFixedListener()
        external.fixedListener = fixedListener
        // Listeners are treated as real-time listeners, thus previously found
        // fixed assignments are not sent out (would be rather expensive to
        // recover it retrospect, see external_propagate.cpp/get_fixed_literals ()
        // function).
    }

    fun disconnectFixedListener() {
        requireValidState("Solver::disconnect_fixed_listener")
        external.fixedListener = null
    }

    /*===== IPASIR-UP BEGIN ==================================================*/

    fun connectExternalPropagator(propagator: ExternalPropagator) {
        requireValidState("Solver::connect_external_propagator")
        if (external.propagator != null)
            disconnectExternalPropagator()

        external.propagator = propagator
        internal.connectPropagator()
        internal.externalProp = true
        internal.externalPropIsLazy = propagator.isLazy
    }

    fun disconnectExternalPropagator() {
        requireValidState("Solver::disconnect_external_propagator")

        if (external.propagator != null)
            external.resetObservedVars()

        external.propagator = null
        internal.setTaintedLiteral()
        internal.externalProp = false
        internal.externalPropIsLazy = true
    }

    fun addObservedVar(idx: Int) {
        requireValidOrSolvingState("Solver::add_observed_var")
        requireValidLit("Solver::add_observed_var", idx)
        external.addObservedVar(idx)
    }

    fun removeObservedVar(idx: Int) {
        requireValidState("Solver::remove_observed_var")
        requireValidLit("Solver::remove_observed_var", idx)
        external.removeObservedVar(idx)
    }

    fun resetObservedVars() {
        requireValidOrSolvingState("Solver::reset_observed_vars")
        external.resetObservedVars()
    }

    /*===== IPASIR-UP END ====================================================*/

    fun active(): Int {
        requireValidState("Solver::active")
        val res = internal.active()
        return res
    }

    fun redundant(): Long {
        requireValidState("Solver::redundant")
        val res = internal.redundant()
        return res
    }

    fun irredundant(): Long {
        requireValidState("Solver::irredundant")
        val res = internal.irredundant()
        return res
    }

    /*------------------------------------------------------------------------*/

    fun freeze(lit: Int) {
        requireValidState("Solver::freeze")
        requireValidLit("Solver::freeze", lit)
        external.freeze(lit)
    }

    fun melt(lit: Int) {
        requireValidState("Solver::melt")
        requireValidLit("Solver::melt", lit)
        contractRequire(external.frozen(lit), "Solver::melt") {
            "can not melt completely melted literal '$lit'"
        }
        external.melt(lit)
    }

    fun frozen(lit: Int): Boolean {
        requireValidState("Solver::frozen")
        requireValidLit("Solver::frozen", lit)
        val res = external.frozen(lit)
        return res
    }

    /*------------------------------------------------------------------------*/

    // 'trace_proof (FILE *external_file, const char *name)' writing bytes to [out]
    // (binary proofs are byte-identical to upstream).
    fun traceProof(out: FileSink, name: String): Boolean {
        requireValidState("Solver::trace_proof")
        contractRequire(state() == CONFIGURING, "Solver::trace_proof") {
            "can only start proof tracing to '$name' right after initialization"
        }
        val internalFile = File.write(name, out)
        internal.trace(internalFile)
        return true
    }

    // 'trace_proof (FILE *external_file, const char *name)' writing to a text sink [out]
    // (each byte as the char with that code, see FileHpp.kt).
    fun traceProof(out: Appendable, name: String): Boolean {
        requireValidState("Solver::trace_proof")
        contractRequire(state() == CONFIGURING, "Solver::trace_proof") {
            "can only start proof tracing to '$name' right after initialization"
        }
        val internalFile = File.write(name, out)
        internal.trace(internalFile)
        return true
    }

    fun flushProofTrace(printStatisticsUnlessQuiet: Boolean = false) {
        requireValidState("Solver::flush_proof_trace")
        contractRequire(internal.fileTracers.isNotEmpty(), "Solver::flush_proof_trace") { "proof is not traced" }
        contractRequire(!internal.fileTracers.last().closed(), "Solver::flush_proof_trace") {
            "proof trace already closed"
        }
        internal.flushTrace(printStatisticsUnlessQuiet)
    }

    fun closeProofTrace(printStatisticsUnlessQuiet: Boolean = false) {
        requireValidState("Solver::close_proof_trace")
        contractRequire(internal.fileTracers.isNotEmpty(), "Solver::close_proof_trace") { "proof is not traced" }
        contractRequire(!internal.fileTracers.last().closed(), "Solver::close_proof_trace") {
            "proof trace already closed"
        }
        internal.closeTrace(printStatisticsUnlessQuiet)
    }

    /*------------------------------------------------------------------------*/

    fun connectProofTracer(tracer: Tracer, antecedents: Boolean, finalizeClauses: Boolean = false) {
        requireValidState("Solver::connect_proof_tracer")
        contractRequire(state() == CONFIGURING, "Solver::connect_proof_tracer") {
            "can only start proof tracing to right after initialization"
        }
        internal.connectProofTracer(tracer, antecedents, finalizeClauses)
    }

    fun connectProofTracer(tracer: InternalTracer, antecedents: Boolean, finalizeClauses: Boolean = false) {
        requireValidState("Solver::connect_proof_tracer")
        contractRequire(state() == CONFIGURING, "Solver::connect_proof_tracer") {
            "can only start proof tracing to right after initialization"
        }
        internal.connectProofTracer(tracer, antecedents, finalizeClauses)
    }

    fun connectProofTracer(tracer: StatTracer, antecedents: Boolean, finalizeClauses: Boolean = false) {
        requireValidState("Solver::connect_proof_tracer")
        contractRequire(state() == CONFIGURING, "Solver::connect_proof_tracer") {
            "can only start proof tracing to right after initialization"
        }
        internal.connectProofTracer(tracer, antecedents, finalizeClauses)
    }

    fun connectProofTracer(tracer: FileTracer, antecedents: Boolean, finalizeClauses: Boolean = false) {
        requireValidState("Solver::connect_proof_tracer")
        contractRequire(state() == CONFIGURING, "Solver::connect_proof_tracer") {
            "can only start proof tracing right after initialization"
        }
        internal.connectProofTracer(tracer, antecedents, finalizeClauses)
    }

    fun disconnectProofTracer(tracer: Tracer): Boolean {
        requireValidState("Solver::disconnect_proof_tracer")
        val res = internal.disconnectProofTracer(tracer)
        return res
    }

    fun disconnectProofTracer(tracer: StatTracer): Boolean {
        requireValidState("Solver::disconnect_proof_tracer")
        val res = internal.disconnectProofTracer(tracer)
        return res
    }

    fun disconnectProofTracer(tracer: FileTracer): Boolean {
        requireValidState("Solver::disconnect_proof_tracer")
        val res = internal.disconnectProofTracer(tracer)
        return res
    }

    /*------------------------------------------------------------------------*/

    fun conclude() {
        requireValidState("Solver::conclude")
        contractRequire(state() == UNSATISFIED || state() == SATISFIED || state() == STEADY, "Solver::conclude") {
            "can only conclude in satisfied, unsatisfied or STEADY state"
        }
        if (state() == UNSATISFIED)
            internal.concludeUnsat()
        else if (state() == SATISFIED)
            external.concludeSat()
        else if (state() == STEADY)
            external.concludeUnknown()
        check(state() == UNSATISFIED || state() == SATISFIED || state() == STEADY) {
            "conclude: unexpected state"
        }
    }

    /*------------------------------------------------------------------------*/

    // 'options ()' prints the option values (output only, not ported).
    fun options() {
        requireValidState("Solver::options")
    }

    fun statistics() {
        if (state() == DELETING)
            return
        requireValidOrSolvingState("Solver::statistics")
        internal.printStatistics()
    }

    // 'resources ()' prints the resource usage (output only, not ported).
    fun resources() {
        if (state() == DELETING)
            return
        requireValidOrSolvingState("Solver::resources")
    }

    /*------------------------------------------------------------------------*/

    // 'read_dimacs (File *, int &, int strict, bool *incremental, vector<int> *cubes)'.
    private fun readDimacs(
        file: File,
        vars: IntRef,
        strict: Int,
        incremental: BoolRef? = null,
        cubes: IntArrayList? = null,
    ): String? {
        requireValidState("Solver::read_dimacs")
        contractRequire(state() == CONFIGURING, "Solver::read_dimacs") {
            "can only read DIMACS file right after initialization"
        }
        val parser = Parser(this, file, incremental, cubes)
        val err = parser.parseDimacs(vars, strict)
        return err
    }

    // 'read_dimacs (FILE *external_file, const char *name, int &vars, int strict)'
    // on the content [text] of a file named [name].
    fun readDimacs(text: String, name: String, vars: IntRef, strict: Int = 1): String? {
        requireValidState("Solver::read_dimacs")
        contractRequire(state() == CONFIGURING, "Solver::read_dimacs") {
            "can only read DIMACS file right after initialization"
        }
        val file = File.read(name, text)
        val err = readDimacs(file, vars, strict)
        return err
    }

    // 'read_dimacs (FILE *external_file, const char *name, int &vars, int strict,
    // bool &incremental, vector<int> &cubes)' on the content [text].
    fun readDimacs(
        text: String,
        name: String,
        vars: IntRef,
        strict: Int,
        incremental: BoolRef,
        cubes: IntArrayList,
    ): String? {
        requireValidState("Solver::read_dimacs")
        contractRequire(state() == CONFIGURING, "Solver::read_dimacs") {
            "can only read DIMACS file right after initialization"
        }
        val file = File.read(name, text)
        val err = readDimacs(file, vars, strict, incremental, cubes)
        return err
    }

    // 'read_solution (const char *path)' on the content [text] of a file named [name].
    fun readSolution(text: String, name: String): String? {
        requireValidState("Solver::read_solution")
        val file = File.read(name, text)
        val parser = Parser(this, file, null, null)
        val err = parser.parseSolution()
        if (err == null)
            external.checkAssignment { external.sol(it) }
        return err
    }

    /*------------------------------------------------------------------------*/

    fun dumpCnf() {
        internal.dump()
    }

    /*------------------------------------------------------------------------*/

    fun getPropagator(): ExternalPropagator? = external.propagator

    fun observed(lit: Int): Boolean {
        requireValidOrSolvingState("Solver::observed")
        requireValidLit("Solver::observed", lit)
        val res = external.observed(lit)
        return res
    }

    fun isWitness(lit: Int): Boolean {
        requireValidOrSolvingState("Solver::is_witness")
        requireValidLit("Solver::is_witness", lit)
        val res = external.isWitness(lit)
        return res
    }

    fun isDecision(lit: Int): Boolean {
        requireValidOrSolvingState("Solver::is_decision")
        requireValidLit("Solver::is_decision", lit)
        val res = external.isDecision(lit)
        return res
    }

    fun forceBacktrack(newLevel: Int) {
        requireValidOrSolvingState("Solver::force_backtrack")
        external.forceBacktrack(newLevel)
    }

    /*------------------------------------------------------------------------*/

    fun traverseClauses(it: ClauseIterator): Boolean {
        requireValidState("Solver::traverse_clauses")
        val res = external.traverseAllFrozenUnitsAsClauses(it) &&
            internal.traverseClauses(it) &&
            internal.traverseConstraint(it)
        return res
    }

    fun traverseWitnessesBackward(it: WitnessIterator): Boolean {
        requireValidState("Solver::traverse_witnesses_backward")
        val res = external.traverseAllNonFrozenUnitsAsWitnesses(it) &&
            external.traverseWitnessesBackward(it)
        return res
    }

    fun traverseWitnessesForward(it: WitnessIterator): Boolean {
        requireValidState("Solver::traverse_witnesses_forward")
        val res = external.traverseWitnessesForward(it) &&
            external.traverseAllNonFrozenUnitsAsWitnesses(it)
        return res
    }

    /*------------------------------------------------------------------------*/

    private class ClauseCounter : ClauseIterator {
        var vars = 0
        var clauses = 0L
        override fun clause(clause: List<Int>): Boolean {
            for (lit in clause) {
                check(lit != Int.MIN_VALUE) { "ClauseCounter: INT_MIN literal" }
                val idx = abs(lit)
                if (idx > vars)
                    vars = idx
            }
            clauses++
            return true
        }
    }

    private class ClauseWriter(private val file: File) : ClauseIterator {
        override fun clause(clause: List<Int>): Boolean {
            for (lit in clause) {
                if (!file.put(lit))
                    return false
                if (!file.put(' '))
                    return false
            }
            return file.put("0\n")
        }
    }

    // 'write_dimacs (const char *path, int min_max_var)' to [out] (named [path] in messages).
    fun writeDimacs(out: Appendable, path: String, minMaxVar: Int = 0): String? {
        requireValidState("Solver::write_dimacs")
        internal.restoreClauses()
        val counter = ClauseCounter()
        traverseClauses(counter)
        val file = File.write(path, out)
        var res: String? = null
        val actualMaxVars = max(minMaxVar, counter.vars)
        file.put("p cnf ")
        file.put(actualMaxVars)
        file.put(' ')
        file.put(counter.clauses)
        file.put('\n')
        val writer = ClauseWriter(file)
        if (!traverseClauses(writer))
            res = "writing to DIMACS file '$path' failed"
        return res
    }

    /*------------------------------------------------------------------------*/

    private class WitnessWriter(private val file: File) : WitnessIterator {
        var witnesses = 0L
        fun write(a: List<Int>): Boolean {
            for (lit in a) {
                if (!file.put(lit))
                    return false
                if (!file.put(' '))
                    return false
            }
            return file.put('0')
        }

        override fun witness(clause: List<Int>, witness: List<Int>, id: Long): Boolean {
            if (!write(clause))
                return false
            if (!file.put(' '))
                return false
            if (!write(witness))
                return false
            if (!file.put('\n'))
                return false
            witnesses++
            return true
        }
    }

    // 'write_extension (const char *path)' to [out] (named [path] in messages).
    fun writeExtension(out: Appendable, path: String): String? {
        requireValidState("Solver::write_extension")
        var res: String? = null
        val file = File.write(path, out)
        val writer = WitnessWriter(file)
        if (!traverseWitnessesBackward(writer))
            res = "writing to DIMACS file '$path' failed"
        return res
    }

    /*------------------------------------------------------------------------*/

    private class ClauseCopier(private val dst: Solver) : ClauseIterator {
        override fun clause(clause: List<Int>): Boolean {
            for (lit in clause)
                dst.add(lit)
            dst.add(0)
            return true
        }
    }

    private class WitnessCopier(private val dst: External) : WitnessIterator {
        override fun witness(clause: List<Int>, witness: List<Int>, id: Long): Boolean {
            dst.pushExternalClauseAndWitnessOnExtensionStack(toIntArrayList(clause), toIntArrayList(witness), id)
            return true
        }

        private fun toIntArrayList(v: List<Int>): IntArrayList {
            val res = IntArrayList()
            for (lit in v) res.add(lit)
            return res
        }
    }

    fun copy(other: Solver) {
        requireReadyState("Solver::copy")
        contractRequire((other.state() and CONFIGURING) != 0, "Solver::copy") { "target solver already modified" }
        internal.opts.copy(other.internal.opts)
        val clauseCopier = ClauseCopier(other)
        traverseClauses(clauseCopier)
        val witnessCopier = WitnessCopier(other.external)
        traverseWitnessesForward(witnessCopier)
        external.copyFlags(other.external)
    }

    /*------------------------------------------------------------------------*/

    // 'section', 'message' and 'verbose' only print messages (not ported).

    // 'error' prints the message and exits upstream ('Internal::verror').
    fun error(msg: String) {
        if (state() == DELETING)
            return
        throw IllegalStateException(msg)
    }

    companion object {
        fun isValidOption(name: String): Boolean = Options.has(name) != null

        fun isPreprocessingOption(name: String): Boolean = Options.isPreprocessingOption(name)

        fun isValidLongOption(arg: String): Boolean = Options.parseLongOption(arg) != null

        fun isValidLimit(arg: String): Boolean = internalIsValidLimit(arg)

        fun isValidConfiguration(name: String): Boolean = Config.has(name)
    }
}
