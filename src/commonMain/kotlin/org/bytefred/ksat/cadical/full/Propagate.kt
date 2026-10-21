package org.bytefred.ksat.cadical.full

/*
 * propagate.cpp: search assignments and the main propagation loop.
 *
 * Mapping notes:
 *  - 'static Clause decision_reason_clause' / 'decision_reason' -> [decisionReasonClause] /
 *    [decisionReason], one object shared by all solvers as upstream (compared with '===').
 *  - Watch iterators 'i', 'j' -> int indices into the watch list. 'const Watch w = *j++ = *i++'
 *    moves the reference (see WatchHpp.kt): 'w' and 'ws[j - 1]' are the same object, which is
 *    safe because after a write to 'ws[j - 1].blit' the copy 'w' is not read again, and the
 *    slot 'i - 1' it came from is overwritten or cut off before it is read again.
 *  - Literal iterators 'lits', 'middle', 'end', 'k' -> indices into 'w.clause.literals'.
 *  - The '__builtin_prefetch' in 'search_assign' is a pure cache hint and dropped.
 */

/*------------------------------------------------------------------------*/

// We are using the address of 'decision_reason' as pseudo reason for
// decisions to distinguish assignment decisions from other assignments.
// Before we added chronological backtracking all learned units were
// assigned at decision level zero ('Solver.level == 0') and we just used a
// zero pointer as reason.  After allowing chronological backtracking units
// were also assigned at higher decision level (but with assignment level
// zero), and it was not possible anymore to just distinguish the case
// 'unit' versus 'decision' by just looking at the current level.  Both had
// a zero pointer as reason.  Now only units have a zero reason and
// decisions need to use the pseudo reason 'decision_reason'.

// External propagation steps use the pseudo reason 'external_reason'.
// The corresponding actual reason clauses are learned only when they are
// relevant in conflict analysis or in root-level fixing steps.

private val decisionReasonClause = Clause(0)
private val decisionReason: Clause = decisionReasonClause

// If chronological backtracking is used the actual assignment level might
// be lower than the current decision level. In this case the assignment
// level is defined as the maximum level of the literals in the reason
// clause except the literal for which the clause is a reason.  This
// function determines this assignment level. For non-chronological
// backtracking as in classical CDCL this function always returns the
// current decision level, the concept of assignment level does not make
// sense, and accordingly this function can be skipped.

// In case of external propagation, it is implicitly assumed that the
// assignment level is the level of the literal (since the reason clause,
// i.e., the set of other literals, is unknown).

internal fun Internal.assignmentLevel(lit: Int, reason: Clause?): Int {

    check(opts.chrono != 0 || externalProp) { "assignment_level without chrono" }
    if (reason == null || reason === externalReason) return level

    var res = 0

    for (k in 0 until reason.size) {
        val other = reason.literals[k]
        if (other == lit) continue
        check(value(other) != 0) { "unassigned literal in reason" }
        val tmp = variable(other).level
        if (tmp > res) res = tmp
    }

    return res
}

// calculate lrat_chain
//
internal fun Internal.buildChainForUnits(lit: Int, reason: Clause, forced: Boolean) {
    if (!lrat) return
    if (opts.chrono != 0 && assignmentLevel(lit, reason) != 0 && !forced) return
    else if (opts.chrono == 0 && level != 0 && !forced) return // not decision level 0
    check(lratChain.isEmpty()) { "non-empty lrat chain" }
    for (k in 0 until reason.size) {
        val reasonLit = reason.literals[k]
        if (lit == reasonLit) continue
        check(value(reasonLit) != 0) { "unassigned reason literal" }
        if (value(reasonLit) == 0) continue
        val uidx = vlit(value(reasonLit) * reasonLit)
        val id = unitClauses(uidx)
        lratChain.add(id)
    }
    lratChain.add(reason.id)
}

// same code as above but reason is assumed to be conflict and lit is not
// needed
//
internal fun Internal.buildChainForEmpty() {
    if (!lrat || lratChain.isNotEmpty()) return
    check(level == 0) { "empty clause chain above root" }
    check(lratChain.isEmpty()) { "non-empty lrat chain" }
    val conflict = checkNotNull(conflict) { "no conflict" }
    for (k in 0 until conflict.size) {
        val lit = conflict.literals[k]
        check(value(lit) < 0) { "conflict literal not falsified" }
        val uidx = vlit(-lit)
        val id = unitClauses(uidx)
        lratChain.add(id)
    }
    lratChain.add(conflict.id)
}

/*------------------------------------------------------------------------*/

internal fun Internal.searchAssign(lit: Int, reason: Clause?) {
    // 'reason' is a reassigned parameter upstream.
    var actualReason = reason

    if (level != 0) requireMode(Internal.SEARCH)

    val idx = vidx(lit)
    val fromExternal = actualReason === externalReason
    val lstraceReason = actualReason // LSTRACE
    check(value(idx) == 0) { "search_assign of assigned variable" }
    check(!flags(idx).eliminated() || actualReason === decisionReason || actualReason === externalReason) {
        "search_assign of eliminated variable"
    }
    val v = variable(idx)
    val litLevel: Int
    check(!lrat || level != 0 || actualReason === externalReason || actualReason === decisionReason ||
        lratChain.isNotEmpty()) { "missing lrat chain" }
    // The following cases are explained in the two comments above before
    // 'decision_reason' and 'assignment_level'.
    //
    // External decision reason means that the propagation was done by
    // an external propagation and the reason clause not known (yet).
    // In that case it is assumed that the propagation is NOT out of
    // order (i.e. lit_level = level), because due to lazy explanation,
    // we can not calculate the real assignment level.
    // The function assignment_level () will also assign the current level
    // to literals with external reason.
    if (actualReason == null) litLevel = 0 // unit
    else if (actualReason === decisionReason) {
        litLevel = level
        actualReason = null
    } else if (opts.chrono != 0) litLevel = assignmentLevel(lit, actualReason)
    else litLevel = level
    if (litLevel == 0) actualReason = null

    v.level = litLevel
    v.trail = trail.size
    v.reason = actualReason
    check(numAssigned < maxVar) { "too many assigned" }
    check(numAssigned == trail.size) { "num_assigned out of sync" }
    numAssigned++
    if (litLevel == 0 && !fromExternal) learnUnitClause(lit) // increases 'stats.fixed'
    check(litLevel != 0 || !fromExternal) { "external root-level assignment" }
    val tmp = sign(lit)
    setVal(idx, tmp)
    check(value(lit) > 0) // Just a bit paranoid but useful.
    check(value(-lit) < 0) // Ditto.
    if (!searchingLuckyPhases) phases.saved[idx] = tmp.toByte() // phase saving during search
    trail.add(lit)
    val tr = trace
    if (tr != null) { // LSTRACE
        val s = "ASSIGN ${externalize(lit)} level=$litLevel reason="
        if (lstraceReason === decisionReason) tr.line(s + "D")
        else if (litLevel == 0) tr.line(s + "U")
        else if (fromExternal) tr.line(s + "E")
        else {
            val r = actualReason!!
            tr.line(s + "C ${r.id} :" + traceLits(r))
        }
    }

    // (upstream prefetches the first watch of '-lit' here, a pure cache hint)
    lratChain.clear()
}

/*------------------------------------------------------------------------*/

// External versions of 'search_assign' which are not inlined.  They either
// are used to assign unit clauses on the root-level, in 'decide' to assign
// a decision or in 'analyze' to assign the literal 'driven' by a learned
// clause.  This happens far less frequently than the 'search_assign' above,
// which is called directly in 'propagate' below and thus is inlined.

internal fun Internal.assignUnit(lit: Int) {
    check(level == 0) { "assign_unit above root" }
    searchAssign(lit, null)
}

// Just assume the given literal as decision (increase decision level and
// assign it).  This is used below in 'decide'.

internal fun Internal.searchAssumeDecision(decision: Int) {
    val lit = decision
    requireMode(Internal.SEARCH)
    check(propagated == trail.size) { "decision before propagation completed" }
    newTrailLevel(lit)
    notifyDecision()
    trace?.line("DECIDE ${externalize(lit)}") // LSTRACE
    searchAssign(lit, decisionReason)
}

// Upstream passes a null 'c' from 'analyze' when the learned clause is a unit
// (driving clause of size 1), hence 'Clause?'.
internal fun Internal.searchAssignDriving(lit: Int, reason: Clause?) {
    requireMode(Internal.SEARCH)
    searchAssign(lit, reason)
    notifyAssignments()
}

internal fun Internal.searchAssignExternal(lit: Int) {
    requireMode(Internal.SEARCH)
    searchAssign(lit, externalReason)
    notifyAssignments()
}

/*------------------------------------------------------------------------*/

// The 'propagate' function is usually the hot-spot of a CDCL SAT solver.
// The 'trail' stack saves assigned variables and is used here as BFS queue
// for checking clauses with the negation of assigned variables for being in
// conflict or whether they produce additional assignments.

// This version of 'propagate' uses lazy watches and keeps two watched
// literals at the beginning of the clause.  We also use 'blocking literals'
// to reduce the number of times clauses have to be visited (2008 JSAT paper
// by Chu, Harwood and Stuckey).  The watches know if a watched clause is
// binary, in which case it never has to be visited.  If a binary clause is
// falsified we continue propagating.

// Finally, for long clauses we save the position of the last watch
// replacement in 'pos', which in turn reduces certain quadratic accumulated
// propagation costs (2013 JAIR article by Ian Gent) at the expense of four
// more bytes for each clause.

internal fun Internal.propagate(): Boolean {

    if (level != 0) requireMode(Internal.SEARCH)
    check(!unsat) { "propagate on unsat" }

    // Updating statistics counter in the propagation loops is costly so we
    // delay until propagation ran to completion.
    //
    val before = propagated.toLong()

    while (conflict == null && propagated != trail.size) {

        val lit = -trail[propagated++]
        val ws = watches(lit)

        val eow = ws.size
        var j = 0
        var i = j

        while (i != eow) {

            val w = ws[i++]
            ws[j++] = w
            val b = value(w.blit)

            if (b > 0) continue // blocking literal satisfied

            if (w.binary()) {

                // Binary clauses are treated separately since they do not require
                // to access the clause at all (only during conflict analysis, and
                // there also only to simplify the code).  Garbage binary clauses
                // are not skipped here (see the long upstream comment: deletion of
                // binary clauses is traced only when they are really deleted).

                if (b < 0) conflict = w.clause // but continue ...
                else {
                    buildChainForUnits(w.blit, w.clause, false)
                    searchAssign(w.blit, w.clause)
                    // lrat_chain.clear (); done in search_assign
                }

            } else {
                check(w.clause.size > 2) { "non-binary watch of binary clause" }

                if (conflict != null) break // Stop if there was a binary conflict already.

                // The cache line with the clause data is forced to be loaded here
                // and thus this first memory access below is the real hot-spot of
                // the solver.  Note, that this check is positive very rarely and
                // thus branch prediction should be almost perfect here.

                if (w.clause.garbage) {
                    j--
                    continue
                }

                val lits = w.clause.literals

                // Simplify code by forcing 'lit' to be the second literal in the
                // clause.  This goes back to MiniSAT.  We use a branch-less version
                // for conditionally swapping the first two literals.
                //
                val other = lits[0] xor lits[1] xor lit
                val u = value(other) // value of the other watch

                if (u > 0) ws[j - 1].blit = other // satisfied, just replace blit
                else {

                    // This follows Ian Gent's (JAIR'13) idea of saving the position
                    // of the last watch replacement.  In essence it needs two copies
                    // of the default search for a watch replacement (in essence the
                    // code in the 'if (v < 0) { ... }' block below), one starting at
                    // the saved position until the end of the clause and then if that
                    // one failed to find a replacement another one starting at the
                    // first non-watched literal until the saved position.

                    val size = w.clause.size
                    val middle = w.clause.pos
                    val end = size
                    var k = middle

                    // Find replacement watch 'r' at position 'k' with value 'v'.

                    var r = 0
                    var v = -1

                    while (k != end) {
                        r = lits[k]
                        v = value(r)
                        if (v >= 0) break
                        k++
                    }

                    if (v < 0) { // need second search starting at the head?

                        k = 2
                        check(w.clause.pos <= size) { "clause pos out of range" }
                        while (k != middle) {
                            r = lits[k]
                            v = value(r)
                            if (v >= 0) break
                            k++
                        }
                    }

                    w.clause.pos = k // always save position

                    check(2 <= k) { "replacement position below 2" }
                    check(k <= w.clause.size) { "replacement position beyond end" }

                    if (v > 0) {

                        // Replacement satisfied, so just replace 'blit'.

                        ws[j - 1].blit = r

                    } else if (v == 0) {

                        // Found new unassigned replacement literal to be watched.

                        lits[0] = other
                        lits[1] = r
                        lits[k] = lit

                        watchLiteral(r, lit, w.clause)

                        j-- // Drop this watch from the watch list of 'lit'.

                    } else if (u == 0) {

                        check(v < 0)

                        // The other watch is unassigned ('!u') and all other literals
                        // assigned to false (still 'v < 0'), thus we found a unit.
                        //
                        buildChainForUnits(other, w.clause, false)
                        searchAssign(other, w.clause)
                        // lrat_chain.clear (); done in search_assign

                        // Similar code is in the implementation of the SAT'18 paper on
                        // chronological backtracking but in our experience, this code
                        // first does not really seem to be necessary for correctness,
                        // and further does not improve running time either.
                        //
                        if (opts.chrono > 1) {

                            val otherLevel = variable(other).level

                            if (otherLevel > variable(lit).level) {

                                // The assignment level of the new unit 'other' is larger
                                // than the assignment level of 'lit'.  Thus we should find
                                // another literal in the clause at that higher assignment
                                // level and watch that instead of 'lit'.

                                check(size > 2)

                                var pos: Int
                                var s = 0

                                pos = 2
                                while (pos < size) {
                                    s = lits[pos]
                                    if (variable(s).level == otherLevel) break
                                    pos++
                                }

                                check(s != 0)
                                check(pos < size)

                                lits[pos] = lit
                                lits[0] = other
                                lits[1] = s
                                watchLiteral(s, other, w.clause)

                                j-- // Drop this watch from the watch list of 'lit'.
                            }
                        }
                    } else {

                        check(u < 0)
                        check(v < 0)

                        // The other watch is assigned false ('u < 0') and all other
                        // literals as well (still 'v < 0'), thus we found a conflict.

                        conflict = w.clause
                        break
                    }
                }
            }
        }

        if (j != i) {

            while (i != eow) ws[j++] = ws[i++]

            ws.shrinkTo(j)
        }
    }

    if (searchingLuckyPhases) {

        // ignoring lucky conflict

    } else {

        // Avoid updating stats eagerly in the hot-spot of the solver.
        //
        stats.propagations.search += propagated - before

        if (conflict == null) noConflictUntil = propagated
        else {

            if (stable) stats.stabconflicts++
            stats.conflicts++

            // The trail before the current decision level was conflict free.
            //
            noConflictUntil = control[level].trail
        }
    }

    return conflict == null
}

/*------------------------------------------------------------------------*/

internal fun Internal.propergate() {

    check(conflict == null) { "propergate with conflict" }
    check(propagated == trail.size) { "propergate before propagation completed" }

    while (propergated != trail.size) {

        val lit = -trail[propergated++]
        val ws = watches(lit)

        val eow = ws.size
        var j = 0
        var i = j

        while (i != eow) {

            val w = ws[i++]
            ws[j++] = w

            if (w.binary()) {
                check(value(w.blit) > 0) { "binary watch not satisfied in propergate" }
                continue
            }
            if (w.clause.garbage) {
                j--
                continue
            }

            val lits = w.clause.literals

            val other = lits[0] xor lits[1] xor lit
            val u = value(other)

            // TODO (upstream): check if u == 0 can happen.
            if (u > 0) continue
            check(u < 0)

            val size = w.clause.size
            val middle = w.clause.pos
            val end = size
            var k = middle

            var r = 0
            var v = -1

            while (k != end) {
                r = lits[k]
                v = value(r)
                if (v >= 0) break
                k++
            }

            if (v < 0) {
                k = 2
                check(w.clause.pos <= size) { "clause pos out of range" }
                while (k != middle) {
                    r = lits[k]
                    v = value(r)
                    if (v >= 0) break
                    k++
                }
            }

            check(2 <= k) { "replacement position below 2" }
            check(k <= w.clause.size) { "replacement position beyond end" }
            w.clause.pos = k

            check(v > 0)

            lits[0] = other
            lits[1] = r
            lits[k] = lit

            watchLiteral(r, lit, w.clause)

            j--
        }

        if (j != i) {

            while (i != eow) ws[j++] = ws[i++]

            ws.shrinkTo(j)
        }
    }
}
