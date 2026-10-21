package org.bytefred.ksat.cadical.full

/*
 * The shadow reference driver (NOT upstream): 'main' of
 * ksat-extra/shadow/cadical-full/driver.cpp, run with LSTRACE set and LSPROOF unset (the
 * configuration the golden traces are made with).
 *
 * Mapping:
 *  - LSTRACE set -> the solver's 'Internal.trace' and the proof tracer write to [sink]
 *    (lines without the trailing newline). 'LSPROOF' is not modelled: the proof tracer
 *    ([ShadowTracer]) is always connected, as for the goldens.
 *  - '--config=<name>' -> [config]; each '--name=value' argument -> one pair of [options],
 *    passed to 'set_long_option' as "--name=value" exactly as the C driver does.
 *  - The CNF file -> its content [cnfText], read with 'read_dimacs (..., strict = 1)'.
 *  - The assumptions file -> [assumptions] (zeros are skipped as in the driver).
 *  - The C driver prints 'error: ...' to stderr and exits with 1 on an invalid configuration,
 *    option or CNF; here these throw [IllegalArgumentException] with the same message.
 *  - 's SATISFIABLE' / 's UNSATISFIABLE' / 's UNKNOWN' are not part of the trace (the
 *    trace script drops them) and are not emitted. The result code (10 / 20 / 0) is returned.
 */
internal fun runShadow(
    cnfText: String,
    config: String?,
    options: List<Pair<String, Int>>,
    assumptions: IntArray?,
    sink: (String) -> Unit,
): Int {
    val traceSink = TraceSink { sink(it) }

    val solver = Solver()
    solver.internal.trace = traceSink
    if (config != null && !solver.configure(config))
        throw IllegalArgumentException("error: invalid configuration '$config'")
    for ((name, value) in options) {
        val opt = "--$name=$value"
        if (!solver.setLongOption(opt))
            throw IllegalArgumentException("error: invalid option '$opt'")
    }

    val tracer = ShadowTracer(traceSink)
    solver.connectProofTracer(tracer, false, false)

    val vars = IntRef(0)
    val err = solver.readDimacs(cnfText, "<cnf>", vars, 1)
    if (err != null)
        throw IllegalArgumentException("error: <cnf>: $err")

    if (assumptions != null) {
        for (lit in assumptions)
            if (lit != 0)
                solver.assume(lit)
    }

    val res = solver.solve()

    if (res == 10) {
        sink("RESULT SAT")
        val sb = StringBuilder("MODEL")
        val n = solver.vars()
        for (idx in 1..n)
            sb.append(' ').append(if (solver.value(idx) > 0) idx else -idx)
        sb.append(" 0")
        sink(sb.toString())
    } else if (res == 20)
        sink("RESULT UNSAT")
    else
        sink("RESULT UNKNOWN")
    solver.disconnectProofTracer(tracer)

    return res
}
