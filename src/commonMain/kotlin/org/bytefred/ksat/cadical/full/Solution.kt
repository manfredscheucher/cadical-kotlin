package org.bytefred.ksat.cadical.full

/*
 * solution.cpp (CaDiCaL 2.1.3): checking learned clauses against a given solution
 * (debugging only, 'External.solution' is null by default).
 *
 * Sam Buss suggested to debug the case where a solver incorrectly claims
 * the formula to be unsatisfiable by checking every learned clause to be
 * satisfied by a satisfying assignment.  Thus the first inconsistent
 * learned clause will be immediately flagged without the need to generate
 * proof traces and perform forward proof checking.
 *
 * 'fatal_message_start ... fatal_message_end' / 'FATAL' -> Kotlin 'error (...)' with the
 * same text (the literals as upstream prints them, internal ones).
 */

internal fun External.checkSolutionOnLearnedClause() {
    check(solution != null)
    val clause = internal.clause
    for (k in 0 until clause.size) {
        val lit = clause[k]
        if (sol(internal.externalize(lit)) == lit) return
    }
    val sb = StringBuilder("learned clause unsatisfied by solution:\n")
    for (k in 0 until clause.size) sb.append(clause[k]).append(' ')
    sb.append('0')
    error(sb.toString())
}

internal fun External.checkSolutionOnShrunkenClause(c: Clause) {
    check(solution != null)
    for (k in 0 until c.size) {
        val lit = c.literals[k]
        if (sol(internal.externalize(lit)) == lit) return
    }
    val sb = StringBuilder()
    for (k in 0 until c.size) sb.append(c.literals[k]).append(' ')
    sb.append('0')
    error(sb.toString())
}

internal fun External.checkNoSolutionAfterLearningEmptyClause() {
    check(solution != null)
    error("learned empty clause but got solution")
}

internal fun External.checkSolutionOnLearnedUnitClause(unit: Int) {
    check(solution != null)
    if (sol(internal.externalize(unit)) == unit) return
    error("learned unit $unit contradicts solution")
}
