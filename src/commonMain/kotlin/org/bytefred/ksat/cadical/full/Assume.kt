package org.bytefred.ksat.cadical.full

import kotlin.math.abs
import kotlin.math.max
import org.bytefred.ksat.cadical.IntArrayList

/*
 * assume.cpp: assumptions, failed assumption analysis ('failing'), concluding unsat for
 * proofs and the assumption reuse of incremental lazy backtracking.
 *
 * Mapping: 'goto DONE' in 'failing' jumps to 'STOP (analyze)' only, which is dropped, so it
 * is a 'return'. 'external->check_learned_clause ()' (inline wrapper in external.hpp) is
 * written out as its body: 'if (solution) check_solution_on_learned_clause ()'.
 */

// Failed literal handling as pioneered by MiniSAT.  This first function
// adds an assumption literal onto the assumption stack.

internal fun Internal.assume(lit: Int) {
    if (level != 0 && opts.ilbassumptions == 0)
        backtrack()
    else if (value(lit) < 0)
        backtrack(max(0, variable(lit).level - 1))
    val f = flags(lit)
    val bit = bign(lit)
    if ((f.assumed and bit) != 0) {
        // ignoring already assumed lit
        return
    }
    f.assumed = f.assumed or bit
    assumptions.add(lit)
    freeze(lit)
}

// for LRAT we actually need to implement recursive dfs
// I don't know how to do this non-recursively...
// for non-lrat use bfs
//
internal fun Internal.assumeAnalyzeLiteral(lit: Int) {
    check(lit != 0) { "assume_analyze_literal: zero literal" }
    val f = flags(lit)
    if (f.seen)
        return
    f.seen = true
    analyzed.add(lit)
    val v = variable(lit)
    check(value(lit) < 0) { "assume_analyze_literal: literal not false" }
    if (v.reason === externalReason) {
        v.reason = wrappedLearnExternalReasonClause(-lit)
        check(v.reason != null || v.level == 0) { "assume_analyze_literal: no external reason" }
    }
    check(v.reason !== externalReason) { "assume_analyze_literal: external reason left" }
    if (v.level == 0) {
        val uidx = vlit(-lit)
        val id = unitClauses(uidx)
        check(id != 0L) { "assume_analyze_literal: unit without id" }
        lratChain.add(id)
        return
    }
    val reason = v.reason
    if (reason != null) {
        check(v.level != 0) { "assume_analyze_literal: reason on root level" }
        for (k in 0 until reason.size) {
            val other = reason.literals[k]
            assumeAnalyzeLiteral(other)
        }
        lratChain.add(reason.id)
        return
    }
    check(assumed(-lit)) { "assume_analyze_literal: decision not an assumption" }
    clause.add(lit)
}

internal fun Internal.assumeAnalyzeReason(lit: Int, reason: Clause) {
    check(lratChain.isEmpty()) { "assume_analyze_reason: chain not empty" }
    check(reason !== externalReason) { "assume_analyze_reason: external reason" }
    check(lrat) { "assume_analyze_reason: without lrat" }
    for (k in 0 until reason.size) {
        val other = reason.literals[k]
        if (other != lit)
            assumeAnalyzeLiteral(other)
    }
    lratChain.add(reason.id)
}

// Find all failing assumptions starting from the one on the assumption
// stack with the lowest decision level.  This goes back to MiniSAT and is
// called 'analyze_final' there.

internal fun Internal.failing() {

    val external = external!!

    check(analyzed.isEmpty()) { "failing: analyzed not empty" }
    check(clause.isEmpty()) { "failing: clause not empty" }
    check(lratChain.isEmpty()) { "failing: chain not empty" }
    check(!markedFailed) { "failing: already marked failed" }
    check(conflictId == 0L) { "failing: with conflict id" }

    if (!unsatConstraint) {
        // Search for failing assumptions in the (internal) assumption stack.

        // There are in essence three cases: (1) An assumption is falsified on
        // the root-level and then 'failed_unit' is set to that assumption, (2)
        // two clashing assumptions are assumed and then 'failed_clashing' is
        // set to the second assumed one, or otherwise (3) there is a failing
        // assumption 'first_failed' with minimum (non-zero) decision level
        // 'failed_level'.

        var failedUnit = 0
        var failedClashing = 0
        var firstFailed = 0
        var failedLevel = Int.MAX_VALUE
        var efailed = 0

        for (ka in 0 until external.assumptions.size) {
            val elit = external.assumptions[ka]
            var lit = external.e2i[abs(elit)]
            if (elit < 0)
                lit = -lit
            if (value(lit) >= 0)
                continue
            val v = variable(lit)
            if (v.level == 0) {
                failedUnit = lit
                efailed = elit
                break
            }
            if (failedClashing != 0)
                continue
            if (v.reason === externalReason) {
                val ev = variable(lit)
                ev.reason = learnExternalReasonClause(-lit)
                val evReason = ev.reason
                if (evReason == null) {
                    ev.level = 0
                    failedUnit = lit
                    efailed = elit
                    break
                }
                ev.level = 0
                // Recalculate assignment level
                for (k in 0 until evReason.size) {
                    val other = evReason.literals[k]
                    if (other == -lit)
                        continue
                    check(value(other) != 0) { "failing: unassigned reason literal" }
                    val tmp = variable(other).level
                    if (tmp > ev.level)
                        ev.level = tmp
                }
                if (ev.level == 0) {
                    failedUnit = lit
                    efailed = elit
                    break
                }
            }
            check(v.reason !== externalReason) { "failing: external reason left" }
            if (v.reason == null) {
                failedClashing = lit
                efailed = elit
            } else if (firstFailed == 0 || v.level < failedLevel) {
                firstFailed = lit
                efailed = elit
                failedLevel = v.level
            }
        }

        check(clause.isEmpty()) { "failing: clause not empty" }

        // Get the 'failed' assumption from one of the three cases.
        val failed: Int
        if (failedUnit != 0)
            failed = failedUnit
        else if (failedClashing != 0)
            failed = failedClashing
        else
            failed = firstFailed
        check(failed != 0) { "failing: no failed assumption" }
        check(efailed != 0) { "failing: no external failed assumption" }

        // In any case mark literal 'failed' as failed assumption.
        run {
            val f = flags(failed)
            val bit = bign(failed)
            check((f.failed and bit) == 0) { "failing: already failed" }
            f.failed = f.failed or bit
        }

        // First case (1).
        if (failedUnit != 0) {
            check(failed == failedUnit)
            // root-level falsified assumption 'failed'
            if (proof != null) {
                if (lrat) {
                    val eidx = (if (efailed > 0) 1 else 0) + 2 * abs(efailed)
                    check(eidx < external.extUnits.size) { "failing: ext_units too small" }
                    val id = external.extUnits[eidx]
                    if (id != 0L) {
                        lratChain.add(id)
                    } else {
                        val uidx = vlit(-failedUnit)
                        val id2 = unitClauses(uidx)
                        check(id2 != 0L) { "failing: unit without id" }
                        lratChain.add(id2)
                    }
                }
                proof?.addAssumptionClause(++clauseId, -efailed, lratChain)
                conclusion.add(clauseId)
                lratChain.clear()
            }
            return // goto DONE
        }

        // Second case (2).
        if (failedClashing != 0) {
            check(failed == failedClashing)
            // clashing assumptions 'failed' and '-failed'
            val f = flags(-failed)
            val bit = bign(-failed)
            check((f.failed and bit) == 0) { "failing: clashing already failed" }
            f.failed = f.failed or bit
            if (proof != null) {
                val clash = IntArrayList()
                clash.add(externalize(failed))
                clash.add(externalize(-failed))
                proof?.addAssumptionClause(++clauseId, clash, lratChain)
                conclusion.add(clauseId)
            }
            return // goto DONE
        }

        // Fall through to third case (3).

        check(firstFailed != 0) { "failing: no first failed" }
        check(failedLevel > 0) { "failing: failed level zero" }

        // The 'analyzed' stack serves as working stack for a BFS through the
        // implication graph until decisions, which are all assumptions, or
        // units are reached.  This is simpler than corresponding code in
        // 'analyze'.
        run {
            val f = flags(firstFailed)
            check(!f.seen) { "failing: first failed already seen" }
            f.seen = true
            check((f.failed and bign(firstFailed)) != 0) { "failing: first failed not marked" }
            analyzed.add(-firstFailed)
            clause.add(-firstFailed)
        }
    } else {
        // unsat_constraint
        // The assumptions necessary to fail each literal in the constraint are
        // collected.
        for (k in 0 until constraint.size) {
            var lit = constraint[k]
            lit *= -1
            check(lit != Int.MIN_VALUE)
            flags(lit).seen = true
            analyzed.add(lit)
        }
    }

    run {
        // used for unsat_constraint lrat
        val constraintChains = ArrayList<ArrayList<Long>>()
        val constraintClauses = ArrayList<IntArrayList>()
        val sumConstraints = IntArrayList()
        val econstraints = IntArrayList()
        for (ke in 0 until external.constraint.size) {
            val elit = external.constraint[ke]
            var lit = external.e2i[abs(elit)]
            if (elit < 0)
                lit = -lit
            if (lit == 0)
                continue
            val f = flags(lit)
            if (f.seen)
                continue
            if (econstraints.contains(elit))
                continue
            econstraints.add(elit)
        }

        // no LRAT do bfs as it was before
        if (!lrat) {
            var next = 0
            while (next < analyzed.size) {
                val lit = analyzed[next++]
                check(value(lit) > 0) { "failing: analyzed literal not true" }
                val v = variable(lit)
                if (v.level == 0)
                    continue
                if (v.reason === externalReason) {
                    v.reason = wrappedLearnExternalReasonClause(lit)
                    if (v.reason == null) {
                        v.level = 0
                        continue
                    }
                }
                check(v.reason !== externalReason) { "failing: external reason left" }
                val reason = v.reason
                if (reason != null) {
                    check(v.level != 0)
                    for (k in 0 until reason.size) {
                        val other = reason.literals[k]
                        val f = flags(other)
                        if (f.seen)
                            continue
                        f.seen = true
                        check(value(other) < 0) { "failing: reason literal not false" }
                        analyzed.add(-other)
                    }
                } else {
                    check(assumed(lit)) { "failing: decision not an assumption" }
                    clause.add(-lit)
                    val f = flags(lit)
                    val bit = bign(lit)
                    check((f.failed and bit) == 0) { "failing: already failed" }
                    f.failed = f.failed or bit
                }
            }
            clearAnalyzedLiterals()
        } else if (!unsatConstraint) { // LRAT for case (3)
            check(clause.size == 1) { "failing: clause size not one" }
            val lit = clause[0]
            val v = variable(lit)
            check(v.reason != null) { "failing: no reason" }
            if (v.reason === externalReason) { // does this even happen?
                v.reason = wrappedLearnExternalReasonClause(lit)
            }
            check(v.reason !== externalReason) { "failing: external reason left" }
            val reason = v.reason
            if (reason != null)
                assumeAnalyzeReason(lit, reason)
            else {
                val uidx = vlit(lit)
                val id = unitClauses(uidx)
                check(id != 0L) { "failing: unit without id" }
                lratChain.add(id)
            }
            for (k in 0 until clause.size) {
                val lit2 = clause[k]
                val f = flags(lit2)
                val bit = bign(-lit2)
                if ((f.failed and bit) == 0)
                    f.failed = f.failed or bit
            }
            clearAnalyzedLiterals()
        } else { // LRAT for unsat_constraint
            check(clause.isEmpty()) { "failing: clause not empty" }
            clearAnalyzedLiterals()
            for (kc in 0 until constraint.size) {
                val lit = constraint[kc]
                // make sure nothing gets marked failed twice
                // also might shortcut the case where
                // lrat_chain is empty because clause is tautological
                check(lit != Int.MIN_VALUE)
                assumeAnalyzeLiteral(lit)
                val empty = ArrayList<Long>()
                val empty2 = IntArrayList()
                constraintChains.add(empty)
                constraintClauses.add(empty2)
                for (k in 0 until clause.size) {
                    val ign = clause[k]
                    constraintClauses.last().add(ign)
                    val f = flags(ign)
                    val bit = bign(-ign)
                    if ((f.failed and bit) == 0) {
                        sumConstraints.add(ign)
                        check((f.failed and bit) == 0)
                        f.failed = f.failed or bit
                    }
                }
                clause.clear()
                clearAnalyzedLiterals()
                for (p in lratChain) {
                    constraintChains.last().add(p)
                }
                lratChain.clear()
            }
            for (k in 0 until sumConstraints.size)
                clause.add(sumConstraints[k])
        }
        clearAnalyzedLiterals()

        // TODO: We can not do clause minimization here, right?

        // We do not actually need to learn this clause, since the conflict is
        // forced already by some other clauses.  There is also no bumping
        // of variables nor clauses necessary.  But we still want to check
        // correctness of the claim that the determined subset of failing
        // assumptions are a high-level core or equivalently their negations
        // form a unit-implied clause.
        //
        if (!unsatConstraint) {
            if (external.solution != null) external.checkSolutionOnLearnedClause()
            if (proof != null) {
                val eclause = IntArrayList()
                for (k in 0 until clause.size)
                    eclause.add(externalize(clause[k]))
                proof?.addAssumptionClause(++clauseId, eclause, lratChain)
                conclusion.add(clauseId)
            }
        } else {
            check(
                !lrat || (constraint.size == constraintClauses.size &&
                    constraint.size == constraintChains.size)
            ) { "failing: constraint chains mismatch" }
            for (kp in constraint.size - 1 downTo 0) {
                val lit = constraint[kp]
                if (lrat) {
                    clause.clear()
                    val back = constraintClauses.last()
                    for (k in 0 until back.size)
                        clause.add(back[k])
                    constraintClauses.removeAt(constraintClauses.size - 1)
                }
                clause.add(-lit)
                if (external.solution != null) external.checkSolutionOnLearnedClause()
                if (proof != null) {
                    if (lrat) {
                        for (p in constraintChains.last()) {
                            lratChain.add(p)
                        }
                        constraintChains.removeAt(constraintChains.size - 1)
                    }
                    val eclause = IntArrayList()
                    for (k in 0 until clause.size)
                        eclause.add(externalize(clause[k]))
                    proof?.addAssumptionClause(++clauseId, eclause, lratChain)
                    conclusion.add(clauseId)
                    lratChain.clear()
                }
                clause.removeLast()
            }
            if (proof != null) {
                for (ke in 0 until econstraints.size) {
                    val elit = econstraints[ke]
                    if (lrat) {
                        val eidx = (if (elit > 0) 1 else 0) + 2 * abs(elit)
                        check(eidx < external.extUnits.size) { "failing: ext_units too small" }
                        val id = external.extUnits[eidx]
                        if (id != 0L) {
                            lratChain.add(id)
                        } else {
                            var lit = external.e2i[abs(elit)]
                            if (elit < 0)
                                lit = -lit
                            val uidx = vlit(-lit)
                            val id2 = unitClauses(uidx)
                            check(id2 != 0L) { "failing: unit without id" }
                            lratChain.add(id2)
                        }
                    }
                    proof?.addAssumptionClause(++clauseId, -elit, lratChain)
                    conclusion.add(clauseId)
                    lratChain.clear()
                }
            }
        }
        lratChain.clear()
        clause.clear()
    }

    // DONE: STOP (analyze) dropped.
}

internal fun Internal.failed(lit: Int): Boolean {
    if (!markedFailed) {
        if (conflictId == 0L)
            failing()
        markedFailed = true
    }
    concludeUnsat()
    val f = flags(lit)
    val bit = bign(lit)
    return (f.failed and bit) != 0
}

internal fun Internal.concludeUnsat() {
    if (proof == null || concluded)
        return
    concluded = true
    if (!markedFailed) {
        check(conclusion.isEmpty()) { "conclude_unsat: conclusion not empty" }
        if (conflictId == 0L)
            failing()
        markedFailed = true
    }
    val con: Int
    if (conflictId != 0L)
        con = CONFLICT
    else if (unsatConstraint)
        con = CONSTRAINT
    else
        con = ASSUMPTIONS
    proof?.concludeUnsat(con, conclusion)
}

internal fun Internal.resetConcluded() {
    if (proof != null)
        proof?.resetAssumptions()
    if (concluded) {
        concluded = false
    }
    if (conflictId != 0L) {
        check(conclusion.size == 1) { "reset_concluded: conclusion size not one" }
        return
    }
    conclusion.clear()
}

// Add the start of each incremental phase (leaving the state
// 'UNSATISFIABLE' actually) we reset all assumptions.

internal fun Internal.resetAssumptions() {
    for (k in 0 until assumptions.size) {
        val lit = assumptions[k]
        val f = flags(lit)
        val bit = bign(lit)
        f.assumed = f.assumed and bit.inv()
        f.failed = f.failed and bit.inv()
        melt(lit)
    }
    assumptions.clear()
    markedFailed = true
}

// struct sort_assumptions_positive_rank
private class SortAssumptionsPositiveRank(private val internal: Internal) : IntRank {

    // Decision level could be 'INT_MAX' and thus 'level + 1' could overflow.
    // Therefore we carefully have to use 'unsigned' for levels below.

    private val maxLevel: UInt = internal.level.toUInt() + 1u

    // typedef uint64_t Type; (default 'bits = 64')

    // Set assumptions first, then sorted by position on the trail
    // unset literals are sorted by literal value.

    fun rankU(a: Int): ULong {
        val v0 = internal.value(a)
        val assigned = (v0 != 0)
        val v = internal.variable(a)
        var res: ULong = (if (assigned) v.level.toUInt() else maxLevel).toULong()
        res = res shl 32
        res = res or (if (assigned) v.trail else abs(a)).toLong().toULong()
        return res
    }

    override fun rank(a: Int): Long = rankU(a).toLong()
}

// struct sort_assumptions_smaller
private class SortAssumptionsSmaller(private val internal: Internal) : IntLess {
    override fun less(a: Int, b: Int): Boolean =
        SortAssumptionsPositiveRank(internal).rankU(a) <
            SortAssumptionsPositiveRank(internal).rankU(b)
}

// Sort the assumptions by the current position on the trail and backtrack
// to the first place where the assumptions and the current trail differ.

internal fun Internal.sortAndReuseAssumptions() {
    check(opts.ilbassumptions != 0) { "sort_and_reuse_assumptions: without ilbassumptions" }
    if (assumptions.isEmpty())
        return
    msort(
        opts.radixsortlim, assumptions,
        SortAssumptionsPositiveRank(this),
        SortAssumptionsSmaller(this),
    )

    var maxLevel: UInt = 0u
    // assumptions are sorted by level, with unset at the end
    for (k in 0 until assumptions.size) {
        val lit = assumptions[k]
        if (value(lit) != 0)
            maxLevel = variable(lit).level.toUInt()
        else
            break
    }

    val size: UInt = minOf(level.toUInt() + 1u, maxLevel + 1u)
    check(level == control.size - 1) { "sort_and_reuse_assumptions: level mismatch" }
    var target = 0
    var i = 1
    var j = 0
    while (i.toUInt() < size) {
        val l = control[i]
        val lit = l.decision
        val alit = assumptions[j]
        val lev = i
        target = lev
        if (value(alit) != 0 &&
            variable(alit).level < lev
        ) { // we can ignore propagated assumptions
            ++j
            continue
        }
        if (lit == 0) { // skip fake decisions
            target = lev - 1
            break
        }
        ++i; ++j
        check(variable(lit).level == lev) { "sort_and_reuse_assumptions: decision level" }
        if (l.decision == alit) {
            continue
        }
        target = lev - 1
        // first different literal on the trail and from the assumptions
        break
    }
    if (target < level)
        backtrack(target)
    //  COVER (target > 1);
    if (level > assumptions.size)
        stats.assumptionsreused += assumptions.size.toLong()
    else
        stats.assumptionsreused += level.toLong()
}
