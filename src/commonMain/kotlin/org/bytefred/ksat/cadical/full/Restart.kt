package org.bytefred.ksat.cadical.full

import kotlin.math.abs

/*
 * restart.cpp: stabilization (mode switching), restart scheduling, trail reuse and restart.
 *
 * Mapping: 'return reluctant' (operator bool, which resets the trigger) -> 'reluctant.fire ()'.
 * 'report (...)', 'PHASE (...)', 'START' / 'STOP' -> dropped (messages / profiling).
 */

// As observed by Chanseok Oh and implemented in MapleSAT solvers too,
// various mostly satisfiable instances benefit from long quiet phases
// with less or almost no restarts.  We implement this idea by prohibiting
// the Glucose style restart scheme in a geometric fashion, which is very
// similar to how originally restarts were scheduled in MiniSAT and earlier
// solvers.  We start with say 1e3 = 1000 (opts.stabilizeinit) conflicts of
// Glucose restarts.  Then in a "stabilizing" phase we disable these
// until 1e4 = 2000 conflicts (if 'opts.stabilizefactor' is '200' percent)
// have passed. After that we switch back to regular Glucose style restarts
// until again 2 times more conflicts than the previous limit are reached.
// Actually, in the latest version we still restarts during stabilization
// but only in a reluctant doubling scheme with a rather high interval.

internal fun Internal.stabilizing(): Boolean {
    if (opts.stabilize == 0) return false
    if (stable && opts.stabilizeonly != 0) return true
    if (stats.conflicts >= lim.stabilize) {
        stable = !stable
        trace?.line("MODE ${if (stable) "stable" else "focused"}") // LSTRACE
        if (stable) stats.stabphases++
        // 'inc.stabilize *= opts.stabilizefactor * 1e-2' (int64_t *= double)
        inc.stabilize = (inc.stabilize.toDouble() * (opts.stabilizefactor * 1e-2)).toLong()
        if (inc.stabilize > opts.stabilizemaxint) inc.stabilize = opts.stabilizemaxint.toLong()
        lim.stabilize = stats.conflicts + inc.stabilize
        if (lim.stabilize <= stats.conflicts) lim.stabilize = stats.conflicts + 1
        swapAverages()
    }
    return stable
}

// Restarts are scheduled by a variant of the Glucose scheme as presented in
// our POS'15 paper using exponential moving averages.  There is a slow
// moving average of the average recent glucose level of learned clauses as
// well as a fast moving average of those glues.  If the end of a base
// restart conflict interval has passed and the fast moving average is above
// a certain margin over the slow moving average then we restart.

internal fun Internal.restarting(): Boolean {
    if (opts.restart == 0) return false
    if (level < assumptions.size + 2) return false
    if (stabilizing()) return reluctant.fire()
    if (stats.conflicts <= lim.restart) return false
    val f = averages.current.glue.fast.value
    val margin = (100.0 + opts.restartmargin) / 100.0
    val s = averages.current.glue.slow.value
    val l = margin * s
    return l <= f
}

// This is Marijn's reuse trail idea.  Instead of always backtracking to the
// top we figure out which decisions will be made again anyhow and only
// backtrack to the level of the last such decision or to the top if no such
// decision exists top (in which case we do not reuse any level).

internal fun Internal.reuseTrail(): Int {
    val trivialDecisions = assumptions.size +
        // Plus 1 if the constraint is satisfied via implications of
        // assumptions and a pseudo-decision level was introduced.
        (if (control[assumptions.size + 1].decision == 0) 1 else 0)
    if (opts.restartreusetrail == 0) return trivialDecisions
    val nextDecision = nextDecisionVariable()
    check(1 <= nextDecision) { "no next decision" }
    var res = trivialDecisions
    if (useScores()) {
        while (res < level) {
            val decision = control[res + 1].decision
            if (decision != 0 && ScoreSmaller(this).less(abs(decision), nextDecision)) break
            res++
        }
    } else {
        val limit = bumped(nextDecision)
        while (res < level) {
            val decision = control[res + 1].decision
            if (decision != 0 && bumped(decision) < limit) break
            res++
        }
    }
    val reused = res - trivialDecisions
    if (reused > 0) {
        stats.reused++
        stats.reusedlevels += reused
        if (stable) stats.reusedstable++
    }
    return res
}

internal fun Internal.restart() {
    trace?.line("RESTART") // LSTRACE
    stats.restarts++
    stats.restartlevels += level
    if (stable) stats.restartstable++
    backtrack(reuseTrail())

    lim.restart = stats.conflicts + opts.restartint

    // report ('R', 2): message output, not ported
}
