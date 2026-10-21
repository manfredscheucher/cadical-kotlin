package org.bytefred.ksat.cadical.full

import org.bytefred.ksat.cadical.IntArrayList
import kotlin.math.abs
import kotlin.math.max

/*
 * elim.cpp
 *
 * Mapping:
 *  - 'elim_more::operator ()' -> [ElimMore] (an [IntLess] passed to the [Eliminator] heap).
 *  - 'Eliminator eliminator (this)' in 'elim_round' -> 'Eliminator (this, ElimMore (this))';
 *    its destructor ('~Eliminator', backward.cpp) runs when 'elim_round' returns, after
 *    'instantiate', and is called explicitly there ([destroy]).
 *  - 'swap (c, d)' / 'swap (pos, neg)' / 'pivot = -pivot' on parameters -> local vars.
 *  - 'int64_t delta; delta *= 1e-3 * opts.elimreleff' -> converted to double, multiplied and
 *    truncated back (C compound assignment). 'LONG_MAX' -> Long.MAX_VALUE (64-bit long).
 *  - 'mark_redundant_clauses_with_eliminated_variables_as_garbage' is defined here upstream
 *    (SIGNATURES.md lists it under "header / not defined").
 */

// Implements a variant of bounded variable elimination as originally
// described in our SAT'05 paper introducing 'SATeLite'.  This is an
// inprocessing version, i.e., it is interleaved with search and triggers
// subsumption and strengthening, blocked and covered clause elimination
// during elimination rounds.  It focuses only those variables which
// occurred in removed irredundant clauses since the last time an
// elimination round was run.  By bounding the maximum resolvent size we can
// run each elimination round until completion.  See the code of 'elim' for
// how elimination rounds are interleaved with blocked clause elimination
// and subsumption (which in turn also calls vivification and transitive
// reduction of the binary implication graph).

/*------------------------------------------------------------------------*/

internal fun Internal.computeElimScore(lit: Int): Double {
    check(1 <= lit) { "computeElimScore: lit < 1" }
    check(lit <= maxVar) { "computeElimScore: lit > max_var" }
    val uidx = 2 * lit
    val pos = ntab[uidx].toDouble()
    val neg = ntab[uidx + 1].toDouble()
    if (pos == 0.0) return -neg
    if (neg == 0.0) return -pos
    var sum = 0.0
    var prod = 0.0
    if (opts.elimsum != 0) sum = opts.elimsum * (pos + neg)
    if (opts.elimprod != 0) prod = opts.elimprod * (pos * neg)
    return prod + sum
}

/*------------------------------------------------------------------------*/

internal class ElimMore(private val internal: Internal) : IntLess {
    override fun less(a: Int, b: Int): Boolean {
        val s = internal.computeElimScore(a)
        val t = internal.computeElimScore(b)
        if (s > t) return true
        if (s < t) return false
        return a.toUInt() > b.toUInt()
    }
}

/*------------------------------------------------------------------------*/

// Note that the new fast subsumption algorithm implemented in 'subsume'
// does not distinguish between irredundant and redundant clauses and is
// also run during search to strengthen and remove 'sticky' redundant
// clauses but also irredundant ones.  So beside learned units during search
// or as consequence of other preprocessors, these subsumption rounds during
// search can remove (irredundant) clauses (and literals), which in turn
// might make new bounded variable elimination possible.  This is tested
// in the 'bool eliminating ()' guard.

internal fun Internal.eliminating(): Boolean {

    if (opts.elim == 0) return false
    if (!preprocessing && opts.inprocessing == 0) return false
    if (preprocessing) check(lim.preprocessing != 0L) { "eliminating: lim.preprocessing" }

    // Respect (increasing) conflict limit.
    //
    if (lim.elim >= stats.conflicts) return false

    // Wait until there are new units or new removed variables
    // (in removed or shrunken irredundant clauses and thus marked).
    //
    if (last.elim.fixed < stats.all.fixed) return true
    if (last.elim.marked < stats.mark.elim) return true

    return false
}

/*------------------------------------------------------------------------*/

// Update the global elimination schedule after adding or removing a clause.

internal fun Internal.elimUpdateAddedClause(eliminator: Eliminator, c: Clause) {
    check(!c.redundant) { "elimUpdateAddedClause: redundant" }
    val schedule = eliminator.schedule
    for (k in 0 until c.size) {
        val lit = c.literals[k]
        if (!active(lit)) continue
        occs(lit).add(c)
        if (frozen(lit)) continue
        ntab[vlit(lit)]++
        val idx = abs(lit)
        if (schedule.contains(idx)) schedule.update(idx)
    }
}

internal fun Internal.elimUpdateRemovedLit(eliminator: Eliminator, lit: Int) {
    if (!active(lit)) return
    if (frozen(lit)) return
    val u = vlit(lit)
    check(ntab[u] > 0) { "elimUpdateRemovedLit: score" }
    ntab[u]--
    val idx = abs(lit)
    val schedule = eliminator.schedule
    if (schedule.contains(idx)) schedule.update(idx)
    else {
        schedule.pushBack(idx)
    }
}

internal fun Internal.elimUpdateRemovedClause(eliminator: Eliminator, c: Clause, except: Int = 0) {
    check(!c.redundant) { "elimUpdateRemovedClause: redundant" }
    for (k in 0 until c.size) {
        val lit = c.literals[k]
        if (lit == except) continue
        check(lit != -except) { "elimUpdateRemovedClause: -except" }
        elimUpdateRemovedLit(eliminator, lit)
    }
}

/*------------------------------------------------------------------------*/

// Since we do not have watches we have to do our own unit propagation
// during elimination as soon we find a unit clause.  This finds new units
// and also marks clauses satisfied by those units as garbage immediately.

internal fun Internal.elimPropagate(eliminator: Eliminator, unit: Int) {
    val root = unit
    check(value(root) > 0) { "elimPropagate: root not true" }
    val work = IntArrayList()
    var i = 0
    work.add(root)
    while (i < work.size) {
        val lit = work[i++]
        check(value(lit) > 0) { "elimPropagate: lit not true" }
        val ns = occs(-lit)
        val nend = ns.size
        for (n in 0 until nend) {
            val c = ns[n]
            if (c.garbage) continue
            var unit = 0
            var satisfied = 0
            for (k in 0 until c.size) {
                val other = c.literals[k]
                val tmp = value(other)
                if (tmp < 0) continue
                if (tmp > 0) {
                    satisfied = other
                    break
                }
                if (unit != 0) unit = Int.MIN_VALUE
                else unit = other
            }
            if (satisfied != 0) {
                elimUpdateRemovedClause(eliminator, c, satisfied)
                markGarbage(c)
            } else if (unit == 0) {
                // need to set conflict = c for lrat
                conflict = c
                learnEmptyClause()
                conflict = null
                break
            } else if (unit != Int.MIN_VALUE) {
                buildChainForUnits(unit, c, false)
                assignUnit(unit)
                work.add(unit)
            }
        }
        if (unsat) break
        val ps = occs(lit)
        val pend = ps.size
        for (n in 0 until pend) {
            val c = ps[n]
            if (c.garbage) continue
            elimUpdateRemovedClause(eliminator, c, lit)
            markGarbage(c)
        }
    }
}

/*------------------------------------------------------------------------*/

// On-the-fly self-subsuming resolution during variable elimination is due
// to HyoJung Han, Fabio Somenzi, SAT'09.  Basically while resolving two
// clauses we test the resolvent to be smaller than one of the antecedents.
// If this is the case the pivot can be removed from the antecedent
// on-the-fly and the resolution can be skipped during elimination.

internal fun Internal.elimOnTheFlySelfSubsumption(eliminator: Eliminator, c: Clause, pivot: Int) {
    stats.elimotfstr++
    stats.strengthened++
    check(clause.isEmpty()) { "elimOnTheFlySelfSubsumption: clause not empty" }
    for (k in 0 until c.size) {
        val lit = c.literals[k]
        if (lit == pivot) continue
        val tmp = value(lit)
        check(tmp <= 0) { "elimOnTheFlySelfSubsumption: satisfied" }
        if (tmp < 0) continue
        clause.add(lit)
    }
    val r = newResolvedIrredundantClause()
    elimUpdateAddedClause(eliminator, r)
    clause.clear()
    lratChain.clear()
    elimUpdateRemovedClause(eliminator, c, pivot)
    markGarbage(c)
}

/*------------------------------------------------------------------------*/

// Resolve two clauses on the pivot literal 'pivot', which is assumed to
// occur in opposite phases in 'c' and 'd'.  The actual resolvent is stored
// in the temporary global 'clause' if it is not redundant.  It is
// considered redundant if one of the clauses is already marked as garbage
// it is root level satisfied, the resolvent is empty, a unit, or produces a
// self-subsuming resolution, which results in the pivot to be removed from
// at least one of the antecedents.

// Note that current root level assignments are taken into account, i.e., by
// removing root level falsified literals.  The function returns true if the
// resolvent is not redundant and for instance has to be taken into account
// during bounded variable elimination.

// Detected units are immediately assigned and in case the last argument is
// true also propagated eagerly in a elimination specific propagation
// routine, which not only finds units but also updates the schedule.

// When this function is called during computation of the number of
// non-trivial (or non-satisfied) resolvents we can eagerly propagate units.
// But during actually adding the resolvents this results in problems as we
// found one rare test case '../test/trace/reg0056.trace' (out of billions),
// where the pivot itself was assigned during such a propagation while
// adding resolvents and lead to pushing a clause to the reconstruction
// stack that later flipped the value of the pivot (while all other literals
// in that clause were unit implied too).  Not pushing the pivot clauses to
// the reconstruction stack produced a wrong model too.  Our fix is to only
// eagerly propagate during computation of the number of resolvents and
// otherwise delay propagation until the end of elimination (which is less
// precise regarding scheduling but very rarely happens).

internal fun Internal.resolveClauses(
    eliminator: Eliminator,
    c: Clause,
    pivot: Int,
    d: Clause,
    propagateEagerly: Boolean,
): Boolean {
    var c = c
    var d = d
    var pivot = pivot

    check(!c.redundant) { "resolveClauses: c redundant" }
    check(!d.redundant) { "resolveClauses: d redundant" }

    stats.elimres++

    if (c.garbage || d.garbage) return false
    if (c.size > d.size) {
        pivot = -pivot
        val tmp = c
        c = d
        d = tmp
    }

    check(level == 0) { "resolveClauses: level" }
    check(clause.isEmpty()) { "resolveClauses: clause not empty" }

    var satisfied = 0 // Contains this satisfying literal.
    var tautological = 0 // Clashing literal if tautological.

    var s = 0 // Actual literals from 'c'.
    var t = 0 // Actual literals from 'd'.

    // First determine whether the first antecedent is satisfied, add its
    // literals to 'clause' and mark them (except for 'pivot').
    //
    for (k in 0 until c.size) {
        val lit = c.literals[k]
        if (lit == pivot) {
            s++
            continue
        }
        check(lit != -pivot) { "resolveClauses: -pivot in c" }
        val tmp = value(lit)
        if (tmp > 0) {
            satisfied = lit
            break
        } else if (tmp < 0) {
            if (!lrat) continue
            val f = flags(lit)
            if (f.seen) continue
            analyzed.add(lit)
            f.seen = true
            val uidx = vlit(-lit)
            val id = unitClauses(uidx)
            check(id != 0L) { "resolveClauses: unit id" }
            lratChain.add(id)
            continue
        } else {
            mark(lit)
            clause.add(lit)
            s++
        }
    }
    if (satisfied != 0) {
        elimUpdateRemovedClause(eliminator, c, satisfied)
        markGarbage(c)
        clause.clear()
        lratChain.clear()
        clearAnalyzedLiterals()
        unmark(c)
        return false
    }

    // Then determine whether the second antecedent is satisfied, add its
    // literal to 'clause' and check whether a clashing literal is found, such
    // that the resolvent would be tautological.
    //
    for (k in 0 until d.size) {
        val lit = d.literals[k]
        if (lit == -pivot) {
            t++
            continue
        }
        check(lit != pivot) { "resolveClauses: pivot in d" }
        var tmp = value(lit)
        if (tmp > 0) {
            satisfied = lit
            break
        } else if (tmp < 0) {
            if (!lrat) continue
            val f = flags(lit)
            if (f.seen) continue
            analyzed.add(lit)
            f.seen = true
            val uidx = vlit(-lit)
            val id = unitClauses(uidx)
            check(id != 0L) { "resolveClauses: unit id" }
            lratChain.add(id)
            continue
        } else if (marked(lit).also { tmp = it } < 0) {
            tautological = lit
            break
        } else if (tmp == 0) {
            clause.add(lit)
            t++
        } else {
            check(tmp > 0) { "resolveClauses: marked" }
            t++
        }
    }

    clearAnalyzedLiterals()
    unmark(c)
    val size = clause.size.toLong()

    if (lrat) {
        lratChain.add(d.id)
        lratChain.add(c.id)
    }

    if (satisfied != 0) {
        elimUpdateRemovedClause(eliminator, d, satisfied)
        markGarbage(d)
        clause.clear()
        lratChain.clear()
        return false
    }

    if (tautological != 0) {
        clause.clear()
        lratChain.clear()
        return false
    }

    if (size == 0L) {
        clause.clear()
        // TODO: lrat?? c or d (or both) should be sufficient.
        // -> also need all unit ids (for negated lits in c and d)
        learnEmptyClause() // already clears lrat_chain.
        return false
    }

    if (size == 1L) {
        val unit = clause[0]
        clause.clear()
        // TODO: lrat, prob c + d
        // -> also need all unit ids (for negated lits in c and d)
        assignUnit(unit) // already clears lrat_chain.
        if (propagateEagerly) elimPropagate(eliminator, unit)
        return false
    }

    check(!lrat || lratChain.isNotEmpty()) { "resolveClauses: lrat_chain empty" }

    // Double self-subsuming resolution.  The clauses 'c' and 'd' are
    // identical except for the pivot which occurs in different phase.  The
    // resolvent subsumes both antecedents.

    if (s > size && t > size) {
        check(s.toLong() == size + 1) { "resolveClauses: s" }
        check(t.toLong() == size + 1) { "resolveClauses: t" }
        clause.clear()
        // TODO: LRAT is c + d (+ eventual units)
        elimOnTheFlySelfSubsumption(eliminator, c, pivot)
        stats.elimotfsub++
        stats.subsumed++
        elimUpdateRemovedClause(eliminator, d, -pivot)
        markGarbage(d)
        return false
    }

    // Single self-subsuming resolution:  The pivot can be removed from 'c',
    // which is implemented by adding a clause which is the same as 'c' but
    // with 'pivot' removed and then marking 'c' as garbage.

    if (s > size) {
        check(s.toLong() == size + 1) { "resolveClauses: s" }
        clause.clear()
        // TODO: LRAT is c + d (+ eventual units) -> not 100% sure.
        elimOnTheFlySelfSubsumption(eliminator, c, pivot)
        return false
    }

    // Same single self-subsuming resolution situation, but only for 'd'.

    if (t > size) {
        check(t.toLong() == size + 1) { "resolveClauses: t" }
        clause.clear()
        // TODO: LRAT is c + d (+ eventual units) -> same.
        elimOnTheFlySelfSubsumption(eliminator, d, -pivot)
        return false
    }

    // TODO: either clear lrat_chain or check what we do from here on out.
    // if propagate_eagerly is true we want to clear lrat_chain, else leave it
    if (propagateEagerly) lratChain.clear()
    return true
}

/*------------------------------------------------------------------------*/

// Check whether the number of non-tautological resolvents on 'pivot' is
// smaller or equal to the number of clauses with 'pivot' or '-pivot'.  This
// is the main criteria of bounded variable elimination.  As a side effect
// it flushes garbage clauses with that variable, sorts its occurrence lists
// (smallest clauses first) and also negates pivot if it has more positive
// than negative occurrences.

internal fun Internal.elimResolventsAreBounded(eliminator: Eliminator, pivot: Int): Boolean {
    val substitute = eliminator.gates.isNotEmpty()

    stats.elimtried++

    check(!unsat) { "elimResolventsAreBounded: unsat" }
    check(active(pivot)) { "elimResolventsAreBounded: inactive" }

    val ps = occs(pivot)
    val ns = occs(-pivot)
    val pos = ps.size.toLong()
    val neg = ns.size.toLong()
    if (pos == 0L || neg == 0L) return lim.elimbound >= 0
    val bound = pos + neg + lim.elimbound

    // Try all resolutions between a positive occurrence (outer loop) of
    // 'pivot' and a negative occurrence of 'pivot' (inner loop) as long the
    // bound on non-tautological resolvents is not hit and the size of the
    // generated resolvents does not exceed the resolvent clause size limit.

    var resolvents = 0L // Non-tautological resolvents.

    val pend = ps.size
    for (m in 0 until pend) {
        val c = ps[m]
        check(!c.redundant) { "elimResolventsAreBounded: c redundant" }
        if (c.garbage) continue
        val nend = ns.size
        for (n in 0 until nend) {
            val d = ns[n]
            check(!d.redundant) { "elimResolventsAreBounded: d redundant" }
            if (d.garbage) continue
            if (substitute && c.gate == d.gate) continue
            stats.elimrestried++
            if (resolveClauses(eliminator, c, pivot, d, true)) {
                resolvents++
                val size = clause.size
                clause.clear()
                if (size > opts.elimclslim) {
                    return false
                }
                if (resolvents > bound) {
                    return false
                }
            } else if (unsat) return false
            else if (value(pivot) != 0) return false
        }
    }

    return true
}

/*------------------------------------------------------------------------*/
// Add all resolvents on 'pivot' and connect them.

internal fun Internal.elimAddResolvents(eliminator: Eliminator, pivot: Int) {

    val substitute = eliminator.gates.isNotEmpty()
    if (substitute) {
        stats.elimsubst++
    }

    check(value(pivot) == 0) { "elimAddResolvents: assigned" }
    check(!flags(pivot).eliminated()) { "elimAddResolvents: eliminated" }

    val ps = occs(pivot)
    val ns = occs(-pivot)
    val pend = ps.size
    for (m in 0 until pend) {
        val c = ps[m]
        if (unsat) break
        if (c.garbage) continue
        val nend = ns.size
        for (n in 0 until nend) {
            val d = ns[n]
            if (unsat) break
            if (d.garbage) continue
            if (substitute && c.gate == d.gate) continue
            if (!resolveClauses(eliminator, c, pivot, d, false)) continue
            check(!lrat || lratChain.isNotEmpty()) { "elimAddResolvents: lrat_chain empty" }
            val r = newResolvedIrredundantClause()
            elimUpdateAddedClause(eliminator, r)
            eliminator.enqueue(r)
            lratChain.clear()
            clause.clear()
        }
    }
}

/*------------------------------------------------------------------------*/

// Remove clauses with 'pivot' and '-pivot' by marking them as garbage and
// push them on the extension stack.

internal fun Internal.markEliminatedClausesAsGarbage(
    eliminator: Eliminator,
    pivot: Int,
    deletedBinaryClause: BoolRef,
) {
    check(!unsat) { "markEliminatedClausesAsGarbage: unsat" }

    val substitute = eliminator.gates.size.toLong()
    var pushed = 0L // '#ifndef NDEBUG' counter, only checked
    val ps = occs(pivot)
    for (m in 0 until ps.size) {
        val c = ps[m]
        if (c.garbage) continue
        check(!c.redundant) { "markEliminatedClausesAsGarbage: c redundant" }
        if (substitute == 0L || c.gate) {
            proof?.weakenMinus(c)
            if (c.size == 2) deletedBinaryClause.value = true
            external!!.pushClauseOnExtensionStack(c, pivot)
            pushed++
        }
        markGarbage(c)
        elimUpdateRemovedClause(eliminator, c, pivot)
    }
    eraseOccs(ps)

    val ns = occs(-pivot)
    for (n in 0 until ns.size) {
        val d = ns[n]
        if (d.garbage) continue
        check(!d.redundant) { "markEliminatedClausesAsGarbage: d redundant" }
        if (substitute == 0L || d.gate) {
            proof?.weakenMinus(d)
            if (d.size == 2) deletedBinaryClause.value = true
            external!!.pushClauseOnExtensionStack(d, -pivot)
            pushed++
        }
        markGarbage(d)
        elimUpdateRemovedClause(eliminator, d, -pivot)
    }
    eraseOccs(ns)

    if (substitute != 0L) check(pushed <= substitute) { "markEliminatedClausesAsGarbage: pushed" }

    // Unfortunately, we can not use the trick by Niklas Soerensson anymore,
    // which avoids saving all clauses on the extension stack.  This would
    // break our new incremental 'restore' logic.
}

/*------------------------------------------------------------------------*/

// Try to eliminate 'pivot' by bounded variable elimination.

internal fun Internal.tryToEliminateVariable(
    eliminator: Eliminator,
    pivot: Int,
    deletedBinaryClause: BoolRef,
) {
    var pivot = pivot

    if (!active(pivot)) return
    check(!frozen(pivot)) { "tryToEliminateVariable: frozen" }

    // First flush garbage clauses.
    //
    var pos = flushOccs(pivot).toLong()
    var neg = flushOccs(-pivot).toLong()

    if (pos > neg) {
        pivot = -pivot
        val tmp = pos
        pos = neg
        neg = tmp
    }
    check(!eliminator.schedule.contains(abs(pivot))) { "tryToEliminateVariable: scheduled" }
    check(pos <= neg) { "tryToEliminateVariable: pos > neg" }

    if (pos != 0L && neg > opts.elimocclim) {
        check(!eliminator.schedule.contains(abs(pivot))) { "tryToEliminateVariable: scheduled" }
        return
    }

    check(!flags(pivot).eliminated()) { "tryToEliminateVariable: eliminated" }

    // Sort occurrence lists, such that shorter clauses come first.
    val ps = occs(pivot)
    stableSort(ps, clauseSmallerSize)
    val ns = occs(-pivot)
    stableSort(ns, clauseSmallerSize)

    if (pos != 0L) findGateClauses(eliminator, pivot)

    if (!unsat && value(pivot) == 0) {
        if (elimResolventsAreBounded(eliminator, pivot)) {
            elimAddResolvents(eliminator, pivot)
            if (!unsat) markEliminatedClausesAsGarbage(eliminator, pivot, deletedBinaryClause)
            if (active(pivot)) markEliminated(pivot)
        } else {
            // too many resolvents on 'pivot' so not eliminated
        }
    }

    unmarkGateClauses(eliminator)
    elimBackwardClauses(eliminator)
}

/*------------------------------------------------------------------------*/

internal fun Internal.markRedundantClausesWithEliminatedVariablesAsGarbage() {
    for (n in 0 until clauses.size) {
        val c = clauses[n]
        if (c.garbage || !c.redundant) continue
        var clean = true
        for (k in 0 until c.size) {
            val lit = c.literals[k]
            val f = flags(lit)
            if (f.eliminated()) {
                clean = false
                break
            }
            if (f.pure()) {
                clean = false
                break
            }
        }
        if (!clean) markGarbage(c)
    }
}

/*------------------------------------------------------------------------*/

// This function performs one round of bounded variable elimination and
// returns the number of eliminated variables. The additional result
// 'completed' is true if this elimination round ran to completion (all
// variables have been tried).  Otherwise it was asynchronously terminated
// or the resolution limit was hit.

internal fun Internal.elimRound(completed: BoolRef, deletedBinaryClause: BoolRef): Int {

    check(opts.elim != 0) { "elimRound: elim" }
    check(!unsat) { "elimRound: unsat" }

    startSimplifier(Internal.ELIM)
    stats.elimrounds++

    last.elim.marked = stats.mark.elim
    check(level == 0) { "elimRound: level" }

    val resolutionLimit: Long

    if (opts.elimlimited != 0) {
        var delta = stats.propagations.search
        delta = (delta * (1e-3 * opts.elimreleff)).toLong()
        if (delta < opts.elimineff) delta = opts.elimineff.toLong()
        if (delta > opts.elimaxeff) delta = opts.elimaxeff.toLong()
        delta = max(delta, 2L * active())

        resolutionLimit = stats.elimres + delta
    } else {
        resolutionLimit = Long.MAX_VALUE
    }

    initNoccs()

    // First compute the number of occurrences of each literal and at the same
    // time mark satisfied clauses and update 'elim' flags of variables in
    // clauses with root level assigned literals (both false and true).
    //
    for (n in 0 until clauses.size) {
        val c = clauses[n]
        if (c.garbage || c.redundant) continue
        var satisfied = false
        var falsified = false
        for (k in 0 until c.size) {
            val lit = c.literals[k]
            val tmp = value(lit)
            if (tmp > 0) satisfied = true
            else if (tmp < 0) falsified = true
            else check(active(lit)) { "elimRound: inactive" }
        }
        if (satisfied) markGarbage(c) // forces more precise counts
        else {
            for (k in 0 until c.size) {
                val lit = c.literals[k]
                if (!active(lit)) continue
                if (falsified) markElim(lit) // simulate unit propagation
                ntab[vlit(lit)]++
            }
        }
    }

    initOccs()

    val eliminator = Eliminator(this, ElimMore(this))
    val schedule = eliminator.schedule

    // Now find elimination candidates which occurred in clauses removed since
    // the last time we ran bounded variable elimination, which in turned
    // triggered their 'elim' bit to be set.
    //
    for (idx in vars) {
        if (!active(idx)) continue
        if (frozen(idx)) continue
        if (!flags(idx).elim) continue
        flags(idx).elim = false
        schedule.pushBack(idx)
    }

    schedule.shrink()

    // Connect irredundant clauses.
    //
    for (n in 0 until clauses.size) {
        val c = clauses[n]
        if (!c.garbage && !c.redundant) {
            for (k in 0 until c.size) {
                val lit = c.literals[k]
                if (active(lit)) occs(lit).add(c)
            }
        }
    }

    val oldEliminated = stats.all.eliminated.toInt()

    // Limit on garbage literals during variable elimination. If the limit is
    // hit a garbage collection is performed.
    //
    val garbageLimit = (2 * stats.irrlits / 3) + (1 shl 20)

    // Main loops tries to eliminate variables according to the schedule. The
    // schedule is updated dynamically and variables are potentially
    // rescheduled to be tried again if they occur in a removed clause.
    //
    while (!unsat && !terminatedAsynchronously() &&
        stats.elimres <= resolutionLimit && !schedule.empty()
    ) {
        val idx = schedule.front()
        schedule.popFront()
        flags(idx).elim = false
        tryToEliminateVariable(eliminator, idx, deletedBinaryClause)
        if (stats.garbage.literals <= garbageLimit) continue
        markRedundantClausesWithEliminatedVariablesAsGarbage()
        garbageCollection()
    }

    // If the schedule is empty all variables have been tried (even
    // rescheduled ones).  Otherwise asynchronous termination happened or we
    // ran into the resolution limit (or derived unsatisfiability).
    //
    completed.value = schedule.size() == 0

    schedule.erase()

    // Collect potential literal clause instantiation pairs, which needs full
    // occurrence lists and thus we have it here before resetting them.
    //
    val instantiator = Instantiator()
    if (!unsat && !terminatedAsynchronously() && opts.instantiate != 0) {
        collectInstantiationCandidates(instantiator)
    }

    resetOccs()
    resetNoccs()

    // Mark all redundant clauses with eliminated variables as garbage.
    //
    if (!unsat) markRedundantClausesWithEliminatedVariablesAsGarbage()

    val eliminated = (stats.all.eliminated - oldEliminated).toInt()

    last.elim.subsumephases = stats.subsumephases
    // 'units' (stats.all.fixed - old_fixed) only feeds 'report'.
    stopSimplifier(Internal.ELIM)

    if (!unsat && !terminatedAsynchronously() &&
        instantiator.nonEmpty()
    ) { // Do we have candidate pairs?
        instantiate(instantiator)
    }

    eliminator.destroy() // '~Eliminator' at scope exit

    return eliminated // non-zero if successful
}

/*------------------------------------------------------------------------*/

// Increase elimination bound (additional clauses allowed during variable
// elimination), which is triggered if elimination with last bound completed
// (including no new subsumptions).  This was pioneered by GlueMiniSAT in
// the SAT Race 2015 and then picked up Chanseok Oh in his COMinisatPS
// solver, which in turn is used in the Maple series of SAT solvers.
// The bound is no increased if the maximum bound is reached.

internal fun Internal.increaseEliminationBound() {

    if (lim.elimbound >= opts.elimboundmax) return

    if (lim.elimbound < 0) lim.elimbound = 0
    else if (lim.elimbound == 0L) lim.elimbound = 1
    else lim.elimbound *= 2

    if (lim.elimbound > opts.elimboundmax) lim.elimbound = opts.elimboundmax.toLong()

    // Now reschedule all active variables for elimination again.
    //
    for (idx in vars) {
        if (!active(idx)) continue
        if (flags(idx).elim) continue
        markElim(idx)
    }
}

/*------------------------------------------------------------------------*/

internal fun Internal.elim(updateLimits: Boolean = true): Unit = tracePhase("elim") {

    if (unsat) return
    if (level != 0) backtrack()
    if (!propagate()) {
        learnEmptyClause()
        return
    }

    stats.elimphases++

    if (externalProp) {
        check(level == 0) { "elim: level" }
        privateSteps = true
    }

    // Make sure there was a complete subsumption phase since last
    // elimination including vivification etc.
    //
    if (last.elim.subsumephases == stats.subsumephases) subsume(updateLimits)

    resetWatches() // saves lots of memory

    // Alternate one round of bounded variable elimination ('elim_round') and
    // subsumption ('subsume_round'), blocked ('block') and covered clause
    // elimination ('cover') until nothing changes, or the round limit is hit.
    // The loop also aborts early if no variable could be eliminated, the
    // empty clause is resolved, it is asynchronously terminated or a
    // resolution limit is hit.

    // This variable determines whether the whole loop of this bounded
    // variable elimination phase ('elim') ran until completion.  This
    // potentially triggers an incremental increase of the elimination bound.
    //
    var phaseComplete = false
    val deletedBinaryClause = BoolRef(false)

    var round = 1

    while (!unsat && !phaseComplete && !terminatedAsynchronously()) {

        val roundComplete = BoolRef()

        elimRound(roundComplete, deletedBinaryClause)

        if (!roundComplete.value) {
            check(!phaseComplete) { "elim: phase complete" }
            break
        }

        if (round++ >= opts.elimrounds) {
            check(!phaseComplete) { "elim: phase complete" }
            break
        }

        // Prioritize 'subsumption' over blocked and covered clause elimination.

        if (subsumeRound()) continue
        if (block()) continue
        if (cover()) continue

        // Was not able to generate new variable elimination candidates after
        // variable elimination round, neither through subsumption, nor blocked,
        // nor covered clause elimination.
        //
        check(roundComplete.value) { "elim: round not complete" }
        phaseComplete = true
    }

    if (phaseComplete) {
        stats.elimcompleted++
    }

    if (deletedBinaryClause.value) deleteGarbageClauses()
    initWatches()
    connectWatches()

    if (unsat) {
        // elimination derived empty clause
    } else if (propagated < trail.size) {
        if (!propagate()) {
            learnEmptyClause()
        }
    }

    // If we ran variable elimination until completion we increase the
    // variable elimination bound and reschedule elimination of all variables.
    //
    if (phaseComplete) increaseEliminationBound()

    if (externalProp) {
        check(level == 0) { "elim: level" }
        privateSteps = false
    }

    if (!updateLimits) return

    val delta = scale((opts.elimint * (stats.elimphases + 1)).toDouble()).toLong()
    lim.elim = stats.conflicts + delta

    last.elim.fixed = stats.all.fixed
}
