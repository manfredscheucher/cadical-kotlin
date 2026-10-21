package org.bytefred.ksat.cadical.full

import kotlin.math.ln

/*
 * limit.cpp: the 'Internal' member functions on limits ('scale', the explicit search limits
 * and 'reset_limits'). The constructors 'Limit ()', 'Last ()', 'Inc ()' are in LimitHpp.kt.
 *
 * Mapping: C 'log' -> kotlin.math.ln (see PORTING.md on transcendental functions).
 * 'static bool is_valid_limit (const char *)' -> top-level [isValidLimit].
 */

internal fun Internal.scale(v: Double): Double {
    val ratio = clauseVariableRatio()
    val factor = if (ratio <= 2) 1.0 else ln(ratio) / ln(2.0)
    var res = factor * v
    if (res < 1) res = 1.0
    return res
}

internal fun Internal.limitTerminate(l: Int) {
    if (l <= 0 && lim.terminate.forced == 0) {
        // keeping unbounded terminate limit
    } else if (l <= 0) {
        lim.terminate.forced = 0
    } else {
        lim.terminate.forced = l
    }
}

internal fun Internal.limitConflicts(l: Int) {
    if (l < 0 && inc.conflicts < 0) {
        // keeping unbounded conflict limit
    } else if (l < 0) {
        inc.conflicts = -1
    } else {
        inc.conflicts = l.toLong()
    }
}

internal fun Internal.limitDecisions(l: Int) {
    if (l < 0 && inc.decisions < 0) {
        // keeping unbounded decision limit
    } else if (l < 0) {
        inc.decisions = -1
    } else {
        inc.decisions = l.toLong()
    }
}

internal fun Internal.limitPreprocessing(l: Int) {
    if (l < 0) {
        // ignoring invalid preprocessing limit
    } else if (l == 0) {
        inc.preprocessing = 0
    } else {
        inc.preprocessing = l.toLong()
    }
}

internal fun Internal.limitLocalSearch(l: Int) {
    if (l < 0) {
        // ignoring invalid local search limit
    } else if (l == 0) {
        inc.localsearch = 0
    } else {
        inc.localsearch = l.toLong()
    }
}

internal fun isValidLimit(name: String): Boolean = when (name) {
    "terminate", "conflicts", "decisions", "preprocessing", "localsearch" -> true
    else -> false
}

// 'true' if 'name' valid
internal fun Internal.limit(name: String, l: Int): Boolean {
    var res = true
    when (name) {
        "terminate" -> limitTerminate(l)
        "conflicts" -> limitConflicts(l)
        "decisions" -> limitDecisions(l)
        "preprocessing" -> limitPreprocessing(l)
        "localsearch" -> limitLocalSearch(l)
        else -> res = false
    }
    return res
}

internal fun Internal.resetLimits() {
    limitTerminate(0)
    limitConflicts(-1)
    limitDecisions(-1)
    limitPreprocessing(0)
    limitLocalSearch(0)
}
