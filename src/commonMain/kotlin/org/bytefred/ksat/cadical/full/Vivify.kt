package org.bytefred.ksat.cadical.full

import kotlin.math.abs

/*
 * vivify.cpp
 *
 * Mapping:
 *  - Watch iterators and clause literal iterators -> indices (see WatchHpp.kt for the aliasing
 *    of 'const Watch w = *j++ = *i++' with the slot 'j[-1]').
 *  - The comparator structs 'vivify_more_noccs', 'vivify_clause_later', 'vivify_flush_smaller'
 *    and 'vivify_better_watch' -> private classes implementing IntLess / Less<Clause>.
 *    'std::sort' -> 'cxxSort', 'std::stable_sort' -> 'stableSort' (StdSort.kt).
 *  - 'std::tuple<int, Clause *, bool>' -> [VivifyLratEntry].
 *  - 'int64_t x *= double' -> product in double, truncated back to Long.
 *  - Values only used in 'PHASE' / 'report' messages are not ported.
 */

/*------------------------------------------------------------------------*/

// Vivification is a special case of asymmetric tautology elimination (ATE)
// and asymmetric literal elimination (ALE).  It strengthens and removes
// clauses proven redundant through unit propagation.
//
// The original algorithm is due to a paper by Piette, Hamadi and Sais
// published at ECAI'08.  We have an inprocessing version, e.g., it does not
// necessarily run-to-completion.  Our version also performs conflict
// analysis and uses a new heuristic for selecting clauses to vivify.
//
// (See upstream vivify.cpp for the full discussion.)

/*------------------------------------------------------------------------*/

// For vivification we have a separate dedicated propagation routine, which
// prefers to propagate binary clauses first.  It also uses its own
// assignment procedure 'vivify_assign', which does not mess with phase
// saving during search nor the conflict and other statistics and further
// can be inlined separately here.  The propagation routine needs to ignore
// (large) clauses which are currently vivified.

internal fun Internal.vivifyAssign(lit: Int, reason: Clause?) {
    requireMode(Internal.VIVIFY)
    val idx = vidx(lit)
    check(value(idx) == 0) { "vivify_assign: assigned" }
    check(!flags(idx).eliminated() || reason == null) { "vivify_assign: eliminated" }
    val v = variable(idx)
    v.level = level // required to reuse decisions
    v.trail = trail.size // used in 'vivify_better_watch'
    check(numAssigned < maxVar) { "vivify_assign: num_assigned" }
    numAssigned++
    v.reason = if (level != 0) reason else null // for conflict analysis
    if (level == 0) learnUnitClause(lit)
    val tmp = sign(lit)
    setVal(idx, tmp)
    trail.add(lit)
}

// Assume negated literals in candidate clause.

internal fun Internal.vivifyAssume(lit: Int) {
    requireMode(Internal.VIVIFY)
    level++
    control.add(Level(lit, trail.size))
    check(level > 0) { "vivify_assume: level" }
    check(propagated == trail.size) { "vivify_assume: propagated" }
    vivifyAssign(lit, null)
}

// Dedicated routine similar to 'propagate' in 'propagate.cpp' and
// 'probe_propagate' with 'probe_propagate2' in 'probe.cpp'.  Please refer
// to that code for more explanation on how propagation is implemented.

internal fun Internal.vivifyPropagate(): Boolean {
    requireMode(Internal.VIVIFY)
    check(!unsat) { "vivify_propagate: unsat" }
    propagated2 = propagated
    val before = propagated2.toLong()
    while (true) {
        if (propagated2 != trail.size) {
            val lit = -trail[propagated2++]
            val ws = watches(lit)
            val eow = ws.size
            for (k in 0 until eow) {
                val w = ws[k]
                if (!w.binary()) continue
                val b = value(w.blit)
                if (b > 0) continue
                if (b < 0) conflict = w.clause // but continue
                else {
                    buildChainForUnits(w.blit, w.clause, false)
                    vivifyAssign(w.blit, w.clause)
                    lratChain.clear()
                }
            }
        } else if (conflict == null && propagated != trail.size) {
            val lit = -trail[propagated++]
            val ws = watches(lit)
            val eow = ws.size
            var i = 0
            var j = 0
            while (i != eow) {
                val w = ws[i++]
                ws[j++] = w
                if (w.binary()) continue
                if (value(w.blit) > 0) continue
                if (w.clause.garbage) {
                    j--
                    continue
                }
                if (w.clause === ignore) continue
                val lits = w.clause.literals
                val other = lits[0] xor lits[1] xor lit
                val u = value(other)
                if (u > 0) ws[j - 1].blit = other
                else {
                    val size = w.clause.size
                    val end = size
                    val middle = w.clause.pos
                    var k = middle
                    var v = -1
                    var r = 0
                    while (k != end) {
                        r = lits[k]
                        v = value(r)
                        if (v >= 0) break
                        k++
                    }
                    if (v < 0) {
                        k = 2
                        check(w.clause.pos <= size) { "vivify_propagate: pos" }
                        while (k != middle) {
                            r = lits[k]
                            v = value(r)
                            if (v >= 0) break
                            k++
                        }
                    }
                    w.clause.pos = k
                    check(2 <= k) { "vivify_propagate: k below 2" }
                    check(k <= w.clause.size) { "vivify_propagate: k beyond end" }
                    if (v > 0) ws[j - 1].blit = r
                    else if (v == 0) {
                        lits[0] = other
                        lits[1] = r
                        lits[k] = lit
                        watchLiteral(r, lit, w.clause)
                        j--
                    } else if (u == 0) {
                        check(v < 0) { "vivify_propagate: v" }
                        vivifyChainForUnits(other, w.clause)
                        vivifyAssign(other, w.clause)
                        lratChain.clear()
                    } else {
                        check(u < 0) { "vivify_propagate: u" }
                        check(v < 0) { "vivify_propagate: v" }
                        conflict = w.clause
                        break
                    }
                }
            }
            if (j != i) {
                while (i != eow) ws[j++] = ws[i++]
                ws.shrinkTo(j)
            }
        } else break
    }
    val delta = propagated2 - before
    stats.propagations.vivify += delta
    return conflict == null
}

/*------------------------------------------------------------------------*/

// Check whether a literal occurs less often.  In the implementation below
// (search for 'int64_t score = ...' or '@4') we actually compute a
// weighted occurrence count similar to the Jeroslow Wang heuristic.

private class VivifyMoreNoccs(private val internal: Internal) : IntLess {
    override fun less(a: Int, b: Int): Boolean {
        val n = internal.noccs(a)
        val m = internal.noccs(b)
        if (n > m) return true // larger occurrences / score first
        if (n < m) return false // smaller occurrences / score last
        if (a == -b) return a > 0 // positive literal first
        return abs(a) < abs(b) // smaller index first
    }
}

private fun sameClause(a: Clause, b: Clause): Boolean {
    if (a.size != b.size) return false
    var i = 0
    var j = 0
    val end = a.size
    while (i != end) {
        if (a.literals[i] != b.literals[j]) return false
        i++
        j++
    }
    return true
}

// Sort candidate clauses by the number of occurrences (actually by their
// score) of their literals, with clauses to be vivified first last.   We
// assume that clauses are sorted w.r.t. more occurring (higher score)
// literals first (with respect to 'vivify_more_noccs').
//
// (See upstream vivify.cpp for the worked example '@1' to '@3'.)
//
// This order is defined by 'vivify_clause_later' which returns 'true' if
// the first clause should be vivified later than the second.

private class VivifyClauseLater(private val internal: Internal) : Less<Clause> {
    override fun less(a: Clause, b: Clause): Boolean {

        if (a === b) return false

        cover(sameClause(a, b))

        // First focus on clauses scheduled in the last vivify round but not
        // checked yet since then.
        //
        if (!a.vivify && b.vivify) return true
        if (a.vivify && !b.vivify) return false

        // Among redundant clauses (in redundant mode) prefer small glue.
        //
        if (a.redundant) {
            check(b.redundant) { "vivify_clause_later: mixed redundancy" }
            if (a.glue > b.glue) return true
            if (a.glue < b.glue) return false
        }

        // Then prefer shorter size.
        //
        if (a.size > b.size) return true
        if (a.size < b.size) return false

        // Now compare literals in the clauses lexicographically with respect to
        // the literal order 'vivify_more_noccs' assuming literals are sorted
        // decreasingly with respect to that order.
        //
        val eoa = a.size
        val eob = b.size
        var j = 0
        var i = 0
        while (i != eoa && j != eob) {
            if (a.literals[i] != b.literals[j])
                return VivifyMoreNoccs(internal).less(b.literals[j], a.literals[i])
            i++
            j++
        }

        cover(i == eoa && j == eob)

        return j == eob // Prefer shorter clauses to be vivified first.
    }
}

/*------------------------------------------------------------------------*/

// Attempting on-the-fly subsumption during sorting when the last line is
// reached in 'vivify_clause_later' above turned out to be trouble some for
// identical clauses.  This is the single point where 'vivify_clause_later'
// is not asymmetric and would require 'stable' sorting for determinism.  It
// can also not be made 'complete' on-the-fly.  Instead of on-the-fly
// subsumption we thus go over the sorted scheduled in a linear scan
// again and remove certain subsumed clauses (the subsuming clause is
// syntactically a prefix of the subsumed clause), which includes
// those troublesome syntactically identical clauses.

private class VivifyFlushSmaller : Less<Clause> {
    override fun less(a: Clause, b: Clause): Boolean {

        val eoa = a.size
        val eob = b.size
        var i = 0
        var j = 0
        while (i != eoa && j != eob) {
            if (a.literals[i] != b.literals[j]) return a.literals[i] < b.literals[j]
            i++
            j++
        }

        return j == eob && i != eoa
    }
}

internal fun Internal.flushVivificationSchedule(vivifier: Vivifier) {

    val schedule = vivifier.schedule

    stableSort(schedule, VivifyFlushSmaller())

    val end = schedule.size
    var j = 0
    var i = j

    var prev: Clause? = null
    var subsumed = 0L
    while (i != end) {
        val c = schedule[i]
        schedule[j++] = c
        if (prev == null || c.size < prev.size) {
            prev = c
            i++
            continue
        }
        val eop = prev.size
        var k = 0
        var l = 0
        while (k != eop) {
            if (prev.literals[k] != c.literals[l]) break
            k++
            l++
        }
        if (k == eop) {
            check(!c.garbage) { "flush_vivification_schedule: c garbage" }
            check(!prev.garbage) { "flush_vivification_schedule: prev garbage" }
            check(c.redundant || !prev.redundant) { "flush_vivification_schedule: redundancy" }
            markGarbage(c)
            subsumed++
            j--
        } else prev = c
        i++
    }

    stats.vivifysubs += subsumed

    if (subsumed != 0L) {
        schedule.shrinkTo(j)
        schedule.trimToSize()
    } else check(j == end) { "flush_vivification_schedule: j" }
}

/*------------------------------------------------------------------------*/

// Depending on whether we try to vivify redundant or irredundant clauses,
// we schedule a clause to be vivified.  For redundant clauses we only try
// to vivify them if they are likely to survive the next 'reduce' operation.

internal fun Internal.considerToVivifyClause(candidate: Clause, redundantMode: Boolean): Boolean {
    val c = candidate
    if (c.garbage) return false
    if (c.redundant != redundantMode) return false
    if (opts.vivifyonce >= 1 && c.redundant && c.vivified) return false
    if (opts.vivifyonce >= 2 && !c.redundant && c.vivified) return false
    if (c.redundant && !likelyToBeKeptClause(c)) return false
    return true
}

// Conflict analysis from 'start' which learns a decision only clause.
//
internal fun Internal.vivifyAnalyzeRedundant(vivifier: Vivifier, start: Clause, onlyBinaryReasons: BoolRef) {

    onlyBinaryReasons.value = true

    val stack = vivifier.stack
    stack.clear()

    stack.add(start)
    while (stack.isNotEmpty()) {
        val c = stack.last()
        if (c.size > 2) onlyBinaryReasons.value = false
        stack.removeAt(stack.size - 1)
        for (k in 0 until c.size) {
            val lit = c.literals[k]
            val v = variable(lit)
            if (v.level == 0) continue
            val f = flags(lit)
            if (f.seen) continue
            check(value(lit) < 0) { "vivify_analyze_redundant: not false" }
            f.seen = true
            analyzed.add(lit)
            val reason = v.reason
            if (reason != null) stack.add(reason)
        }
    }
}

// Check whether we assigned all literals to false and none is implied.

internal fun Internal.vivifyAllDecisions(candidate: Clause, subsume: Int): Boolean {
    val c = candidate

    // assert (redundant_mode);

    for (k in 0 until c.size) {
        val other = c.literals[k]
        if (other == subsume) continue
        if (value(other) >= 0) return false
        val v = variable(other)
        if (v.level == 0) continue
        if (v.reason != null) return false
        if (!flags(other).seen) return false
    }

    return true
}

// After conflict analysis (in redundant mode) we check whether all literals
// in the candidate clause 'c' are actually decisions.  If that is case we
// do not subsume the clause 'c'.  Otherwise we go over it and add literals
// to the global learned clause which should be kept.  Thus the result of
// this function is communicated through the global 'clause'.  If it becomes
// empty, we do not learn it and subsumption fails.   The 'subsume' literal
// is used to force keeping that literal (see case '@5' below, where we
// found this positively implied literal).

private const val ACTION_FLUSH = 0
private const val ACTION_IGNORE = 1
private const val ACTION_KEEP = 2

internal fun Internal.vivifyPostProcessAnalysis(candidate: Clause, subsume: Int) {
    val c = candidate

    // assert (redundant_mode);

    if (vivifyAllDecisions(c, subsume)) {

        clause.clear() // Do not subsume nor strengthen (case '@7').

    } else { // Otherwise prepare subsuming learned clause.

        for (k in 0 until c.size) {
            val other = c.literals[k]

            // enum { FLUSH, IGNORE, KEEP } action;
            val action: Int

            if (other == subsume) action = ACTION_KEEP
            else if (value(other) >= 0) action = ACTION_FLUSH
            else {
                val v = variable(other)
                action = if (v.level == 0) ACTION_IGNORE
                else if (v.reason != null) ACTION_FLUSH
                else if (flags(other).seen) ACTION_KEEP
                else ACTION_FLUSH
            }

            if (action == ACTION_KEEP) clause.add(other)
        }
    }
}

/*------------------------------------------------------------------------*/

// In a strengthened clause the idea is to move non-false literals to the
// front, followed by false literals.  Literals are further sorted by
// reverse assignment order.  The goal is to use watches which require to
// backtrack as few as possible decision levels.

private class VivifyBetterWatch(private val internal: Internal) : IntLess {
    override fun less(a: Int, b: Int): Boolean {

        val av = internal.value(a)
        val bv = internal.value(b)

        if (av >= 0 && bv < 0) return true
        if (av < 0 && bv >= 0) return false

        return internal.variable(a).trail > internal.variable(b).trail
    }
}

// Common code to actually strengthen a candidate clause.  The resulting
// strengthened clause is communicated through the global 'clause'.

internal fun Internal.vivifyStrengthen(candidate: Clause) {
    val c = candidate

    check(!clause.isEmpty()) { "vivify_strengthen: empty clause" }
    stats.vivifystrs++

    if (clause.size == 1) {

        backtrack()
        val unit = clause[0]
        check(value(unit) == 0) { "vivify_strengthen: unit assigned" }
        assignUnit(unit)
        // lrat_chain.clear ();   done in search_assign
        stats.vivifyunits++

        val ok = propagate()
        if (!ok) learnEmptyClause()

    } else {

        // See explanation before 'vivify_better_watch' above.
        //
        cxxSort(clause, VivifyBetterWatch(this))

        var newLevel = level

        val lit0 = clause[0]
        val val0 = value(lit0)
        if (val0 < 0) {
            val level0 = variable(lit0).level
            newLevel = level0 - 1
        }

        val lit1 = clause[1]
        val val1 = value(lit1)
        if (val1 < 0 && !(val0 > 0 && variable(lit0).level <= variable(lit1).level)) {
            val level1 = variable(lit1).level
            newLevel = level1 - 1
        }

        if (newLevel < level) backtrack(newLevel)

        check(value(lit0) >= 0) { "vivify_strengthen: lit0 false" }
        check(
            value(lit1) >= 0 ||
                (value(lit0) > 0 && value(lit1) < 0 && variable(lit0).level <= variable(lit1).level),
        ) { "vivify_strengthen: lit1 watch" }

        newClauseAs(c)
    }
    clause.clear()
    markGarbage(c)
    lratChain.clear()
}

/*------------------------------------------------------------------------*/

// Main function: try to vivify this candidate clause in the given mode.

internal fun Internal.vivifyClause(vivifier: Vivifier, candidate: Clause) {
    val c = candidate

    val redundantMode = vivifier.redundantMode

    check(redundantMode || !c.redundant) { "vivify_clause: redundant in irredundant mode" }
    check(c.size > 2) { "vivify_clause: binary" } // see (NO-BINARY) below

    c.vivify = false // mark as checked / tried
    c.vivified = true // and globally remember

    if (c.garbage) return

    val lratStack = vivifier.lratStack

    // First check whether the candidate clause is already satisfied and at
    // the same time copy its non fixed literals to 'sorted'.  The literals
    // in the candidate clause might not be sorted anymore due to replacing
    // watches during propagation, even though we sorted them initially
    // while pushing the clause onto the schedule and sorting the schedule.
    //
    var satisfied = 0
    val sorted = vivifier.sorted
    sorted.clear()

    for (k in 0 until c.size) {
        val lit = c.literals[k]
        val tmp = fixed(lit)
        if (tmp > 0) {
            satisfied = lit
            break
        } else if (tmp == 0) sorted.add(lit)
    }

    if (satisfied != 0) {
        markGarbage(c)
        return
    }

    cxxSort(sorted, VivifyMoreNoccs(this))

    // The actual vivification checking is performed here, by assuming the
    // negation of each of the remaining literals of the clause in turn and
    // propagating it.  If a conflict occurs or another literal in the
    // clause becomes assigned during propagation, we can stop.
    //
    stats.vivifychecks++

    // If the decision 'level' is non-zero, then we can reuse decisions for
    // the previous candidate, and avoid re-propagating them.  In preliminary
    // experiments this saved between 30%-50% decisions (and thus
    // propagations), which in turn lets us also vivify more clauses within
    // the same propagation bounds, or terminate earlier if vivify runs to
    // completion.
    //
    if (level != 0) {
        // First check whether this clause is actually a reason for forcing
        // one of its literals to true and then backtrack one level before
        // that happened.  Otherwise this clause might be incorrectly
        // considered to be redundant or if this situation is checked then
        // redundancy by other clauses using this forced literal becomes
        // impossible.
        //
        var forced = 0

        // This search could be avoided if we would eagerly set the 'reason'
        // boolean flag of clauses, which however we do not want to do for
        // binary clauses (during propagation) and thus would still require
        // a version of 'protect_reason' for binary clauses during 'reduce'
        // (well binary clauses are not collected during 'reduce', but again
        // this exception from the exception is pretty complex and thus a
        // simply search here is probably easier to understand).

        for (k in 0 until c.size) {
            val lit = c.literals[k]
            val tmp = value(lit)
            if (tmp < 0) continue
            if (tmp > 0 && variable(lit).reason === c) forced = lit
            break
        }
        if (forced != 0) {
            check(variable(forced).level != 0) { "vivify_clause: forced at root" }
            backtrack(variable(forced).level - 1)
        }

        // As long the (remaining) literals of the sorted clause match
        // decisions on the trail we just reuse them.
        //
        if (level != 0) {

            var l = 1 // This is the decision level we want to reuse.

            for (k in 0 until sorted.size) {
                val lit = sorted[k]
                if (fixed(lit) != 0) continue
                val decision = control[l].decision
                if (-lit == decision) {
                    stats.vivifyreused++
                    if (++l > level) break
                } else {
                    backtrack(l - 1)
                    break
                }
            }
        }
    }

    // Make sure to ignore this clause during propagation.  This is not that
    // easy for binary clauses (NO-BINARY), e.g., ignoring binary clauses,
    // without changing 'propagate'. Actually, we do not want to remove binary
    // clauses which are subsumed.  Those are hyper binary resolvents and
    // should be kept as learned clauses instead, unless they are transitive
    // in the binary implication graph, which in turn is detected during
    // transitive reduction in 'transred'.
    //
    ignore = c

    var subsume = 0 // determined to be redundant / subsumed
    var remove = 0 // at least literal 'remove' can be removed

    // If the candidate is redundant, i.e., we are in redundant mode, the
    // clause is subsumed (in one of the two cases below where 'subsume' is
    // assigned) and further all reasons involved are only binary clauses,
    // then this redundant clause is what we once called a hidden tautology,
    // and even for redundant clauses it makes sense to remove the candidate.
    // It does not add anything to propagation power of the formula.  This is
    // the same argument as removing transitive clauses in the binary
    // implication graph during transitive reduction.
    //
    val onlyBinaryReasons = BoolRef(false)

    // Go over the literals in the candidate clause in sorted order.
    //
    for (k in 0 until sorted.size) {
        val lit = sorted[k]

        // Exit loop as soon a literal is positively implied (case '@5' below)
        // or propagation of the negation of a literal fails ('@6').
        //
        if (subsume != 0) break

        // We keep on assigning literals, even though we know already that we
        // can remove one (was negatively implied), since we either might run
        // into the 'subsume' case above or more false literals become implied.
        // In any case this might result in stronger vivified clauses.  As a
        // consequence continue with this loop even if 'remove' is non-zero.

        val tmp = value(lit)

        if (tmp != 0) { // literal already assigned

            val v = variable(lit)

            if (v.level == 0) {
                continue
            }
            if (v.reason == null) {
                continue
            }

            if (tmp > 0) { // positively implied

                subsume = lit // will be able to subsume candidate '@5'

                // In redundant mode we want to strengthen clauses instead of
                // subsuming them (actually incorrect for irredundant candidates).
                // Thus we perform resolutions to find such a strengthening.
                //
                if (redundantMode) {

                    check(c.redundant) { "vivify_clause: not redundant" }
                    check(clause.isEmpty()) { "vivify_clause: clause not empty" }
                    check(analyzed.isEmpty()) { "vivify_clause: analyzed not empty" }

                    // We start the analysis by adding the negation of the implied
                    // literal to the global 'clause'.
                    //
                    flags(lit).seen = true
                    analyzed.add(-lit)
                    check(v.reason != null) { "vivify_clause: no reason" }

                    // Continue the analysis with the reason of the implied literal.
                    //
                    vivifyAnalyzeRedundant(vivifier, v.reason!!, onlyBinaryReasons)
                    if (!onlyBinaryReasons.value) {
                        vivifyPostProcessAnalysis(c, subsume)
                        if (!clause.isEmpty()) stats.vivifystred2++
                    }
                    clearAnalyzedLiterals()
                    if (lrat) {
                        check(lratChain.isEmpty()) { "vivify_clause: lrat chain" }
                        vivifyBuildLrat(lit, v.reason!!, lratStack)
                        clearAnalyzedLiterals()
                    }

                    backtrack(level - 1)
                    check(conflict == null) { "vivify_clause: conflict" }

                    break
                }

            } else { // negatively implied

                check(tmp < 0) { "vivify_clause: tmp" }

                remove = lit // will be able to remove this literal
            }

        } else { // still unassigned

            stats.vivifydecs++
            vivifyAssume(-lit)

            if (vivifyPropagate()) continue // hot-spot

            subsume = Int.MIN_VALUE // will be able to subsume candidate '@6'

            // Again try to strengthen instead of subsuming in redundant mode.
            //
            if (redundantMode) {

                check(c.redundant) { "vivify_clause: not redundant" }
                check(clause.isEmpty()) { "vivify_clause: clause not empty" }
                check(analyzed.isEmpty()) { "vivify_clause: analyzed not empty" }

                vivifyAnalyzeRedundant(vivifier, conflict!!, onlyBinaryReasons)
                if (!onlyBinaryReasons.value) {
                    vivifyPostProcessAnalysis(c, subsume)
                    if (!clause.isEmpty()) stats.vivifystred3++
                }
                clearAnalyzedLiterals()
                if (lrat) {
                    check(lratChain.isEmpty()) { "vivify_clause: lrat chain" }
                    vivifyBuildLrat(0, conflict!!, lratStack)
                    clearAnalyzedLiterals()
                }
            }

            backtrack(level - 1)
            conflict = null

            break
        }
    }

    // Now we go over the very last literal of the clause and attempt to
    // instantiate it refer to instantiate.hpp for more. As clauses as sorted
    // by number of occurrence, we attempt to remove literals with few
    // occurrences

    if (opts.vivifyinst != 0 && subsume == 0) {
        val lit = sorted.back()
        if (remove != lit) {
            backtrack(level - 1)
            check(value(lit) == 0) { "vivify_clause: instantiation literal assigned" }
            stats.vivifydecs++
            vivifyAssume(lit)
            val ok = vivifyPropagate()
            if (!ok) {
                stats.vivifyinst++
                // strengthen clause
                if (lrat) {
                    check(lratChain.isEmpty()) { "vivify_clause: lrat chain" }
                    vivifyBuildLrat(0, c, lratStack)
                    vivifyBuildLrat(0, conflict!!, lratStack)
                    clearAnalyzedLiterals()
                }
                remove = lit
                backtrack(level - 1)
                conflict = null
                check(conflict == null) { "vivify_clause: conflict" }
            }
        }
    }

    check(ignore === c) { "vivify_clause: ignore" }
    ignore = null

    if (subsume != 0) {

        if (redundantMode && !onlyBinaryReasons.value) {

            check(c.redundant) { "vivify_clause: not redundant" }

            if (!clause.isEmpty()) {

                check(!lrat || lratChain.isNotEmpty()) { "vivify_clause: lrat chain empty" }
                vivifyStrengthen(c)

            } else { // triggered by '@7'

                // In redundant mode, where candidates might be redundant and we
                // allow to propagate over redundant clauses too, we do not remove
                // unit implied clauses which we failed to strengthen.

                if (c.redundant) {

                    check(redundantMode) { "vivify_clause: redundant mode" }
                    check(!c.vivify) { "vivify_clause: vivify" }

                } else {

                    // For an irredundant clause the situation is different, since we
                    // might be able to remove it even if we only propagate over
                    // irredundant clauses.  Thus we schedule it again.

                    check(!c.vivify) { "vivify_clause: vivify" }

                    c.vivify = true
                }
            }

        } else {

            stats.vivifysubs++
            markGarbage(c)
        }

    } else if (remove != 0) {

        check(level != 0) { "vivify_clause: level" }
        check(clause.isEmpty()) { "vivify_clause: clause not empty" }

        // There might be other literals implied to false (or even root level
        // falsified).  Those should be removed in addition to 'remove'.
        //
        for (k in 0 until c.size) {
            val other = c.literals[k]
            check(value(other) != 0 || other == remove) { "vivify_clause: unassigned literal" }
            val v = variable(other)
            if (v.level == 0) { // Remove root-level fixed literals.
                continue
            }
            if (v.reason != null) { // Remove all negative implied literals.
                check(v.level != 0) { "vivify_clause: implied at root" }
                continue
            }
            if (other == remove) {
                continue
            }
            // Decision or unassigned.
            clause.add(other)
        }

        if (redundantMode) stats.vivifystred1++
        else stats.vivifystrirr++

        if (lrat && lratChain.isEmpty()) {
            check(lratChain.isEmpty()) { "vivify_clause: lrat chain" }
            vivifyBuildLrat(0, c, lratStack)
            clearAnalyzedLiterals()
        }
        vivifyStrengthen(c)

    } else {
        // vivification failed
    }
    lratChain.clear()
}

// when we can strengthen clause c we have to build lrat.
// uses f.seen so do not forget to clear flags afterwards.
// this can happen in three cases. (1), (2) are only sound in redundant mode
// (1) literal l in c is positively implied. in this case we call the
// function with (l, l.reason). This justifies the reduction because the new
// clause c' will include l and all decisions so l.reason is a conflict
// assuming -c' (2) conflict during vivify propagation. function is called
// with (0, conflict) similar to (1) but more direct. (3) some literals in c
// are negatively implied and can therefore be removed. in this case we call
// the function with (0, c). originally we justified each literal in c on
// its own but this is not actually necessary.
//
// Non-recursive version, as some bugs have been found.  DFS over the
// reasons with preordering (aka we explore the entire reason before
// exploring deeper)
internal fun Internal.vivifyBuildLrat(lit: Int, reason: Clause, stack: ArrayList<VivifyLratEntry>) {
    check(stack.isEmpty()) { "vivify_build_lrat: stack not empty" }
    stack.add(VivifyLratEntry(lit, reason, false))
    while (stack.isNotEmpty()) {
        val top = stack.last()
        val lit = top.lit
        val reason = top.reason!!
        val finished = top.finished
        stack.removeAt(stack.size - 1)
        if (lit != 0 && flags(lit).seen) {
            continue
        }
        if (finished) {
            lratChain.add(reason.id)
            if (lit != 0) {
                val f = flags(lit)
                f.seen = true
                analyzed.add(lit) // assert (val (other) < 0);
                check(flags(lit).seen) { "vivify_build_lrat: seen" }
            }
            continue
        } else stack.add(VivifyLratEntry(lit, reason, true))
        for (k in 0 until reason.size) {
            val other = reason.literals[k]
            if (other == lit) continue
            val v = variable(other)
            val f = flags(other)
            if (f.seen) continue // we would like to assert (val (other) < 0);
            // analyzed.push_back (other); // but we cannot because we have
            // f.seen = true;              // already backtracked (sometimes)
            if (v.level == 0) {
                val uidx = vlit(-other) // nevertheless we can use var (l)
                val id = unitClauses(uidx) // as if l was still assigned
                check(id != 0L) { "vivify_build_lrat: unit id" } // because var is updated lazily
                lratChain.add(id)
                f.seen = true
                analyzed.add(other)
                continue
            }
            val vReason = v.reason
            if (vReason != null) { // recursive justification
                stack.add(VivifyLratEntry(other, vReason, false))
            }
        }
    }
    stack.clear()
}

// calculate lrat_chain
//
internal fun Internal.vivifyChainForUnits(lit: Int, reason: Clause) {
    if (!lrat) return
    // LOG ("building chain for units");        bad line for debugging
    // equivalence if (opts.chrono && assignment_level (lit, reason)) return;
    if (level != 0) return // not decision level 0
    check(lratChain.isEmpty()) { "vivify_chain_for_units: lrat chain" }
    for (k in 0 until reason.size) {
        val reasonLit = reason.literals[k]
        if (lit == reasonLit) continue
        check(value(reasonLit) != 0) { "vivify_chain_for_units: unassigned" }
        val uidx = vlit(value(reasonLit) * reasonLit)
        val id = unitClauses(uidx)
        lratChain.add(id)
    }
    lratChain.add(reason.id)
}

/*------------------------------------------------------------------------*/

// There are two modes of vivification, one using all clauses and one
// focusing on irredundant clauses only.  The latter variant working on
// irredundant clauses only can also remove irredundant asymmetric
// tautologies (clauses subsumed through unit propagation), which in
// redundant mode is incorrect (due to propagating over redundant clauses).

internal fun Internal.vivifyRound(redundantMode: Boolean, delta: Long) {
    val propagationLimit = delta

    if (unsat) return
    if (terminatedAsynchronously()) return

    // Disconnect all watches since we sort literals within clauses.
    //
    if (watching()) clearWatches()

    // Count the number of occurrences of literals in all clauses,
    // particularly binary clauses, which are usually responsible
    // for most of the propagations.
    //
    initNoccs()

    for (c in clauses) {

        if (!considerToVivifyClause(c, redundantMode)) continue

        // This computes an approximation of the Jeroslow Wang heuristic score
        //
        //       nocc (L) =     sum       2^(12-|C|)
        //                   L in C in F
        //
        // but we cap the size at 12, that is all clauses of size 12 and larger
        // contribute '1' to the score, which allows us to use 'long' numbers.
        // See the example above (search for '@1').
        //
        val shift = 12 - c.size
        val score = if (shift < 1) 1L else (1L shl shift) // @4

        for (k in 0 until c.size) {
            ntab[vlit(c.literals[k])] += score
        }
    }

    // Refill the schedule every time.  Unchecked clauses are 'saved' by
    // setting their 'vivify' bit, such that they can be tried next time.
    //
    val vivifier = Vivifier(redundantMode)

    // In the first round of filling the schedule check whether there are
    // still clauses left, which were scheduled but have not been vivified
    // yet. The second round is only entered if no such clause was found in
    // the first round.  Then the second round selects all clauses.
    //
    for (c in clauses) {

        if (c.size == 2) continue // see also (NO-BINARY) above

        if (!considerToVivifyClause(c, redundantMode)) continue

        // Literals in scheduled clauses are sorted with their highest score
        // literals first (as explained above in the example at '@2').  This
        // is also needed in the prefix subsumption checking below.
        //
        cxxSort(c.literals, 0, c.size, VivifyMoreNoccs(this))

        vivifier.schedule.add(c)
    }
    vivifier.schedule.trimToSize()

    // Flush clauses subsumed by another clause with the same prefix, which
    // also includes flushing syntactically identical clauses.
    //
    flushVivificationSchedule(vivifier)

    // Sort candidates, with first to be tried candidate clause last, i.e.,
    // many occurrences and high score literals) as in the example explained
    // above (search for '@3').
    //
    stableSort(vivifier.schedule, VivifyClauseLater(this))

    // Remember old values of counters to summarize after each round with
    // verbose messages what happened in that round.
    //
    var subsumed = stats.vivifysubs
    var strengthened = stats.vivifystrs

    val scheduled = vivifier.schedule.size.toLong()
    stats.vivifysched += scheduled

    // Limit the number of propagations during vivification as in 'probe'.
    //
    val limit = stats.propagations.vivify + propagationLimit

    connectWatches(!redundantMode) // watch all relevant clauses

    // the clauses might still contain set literals, so propagation since the
    // beginning
    propagated = 0
    propagated2 = propagated

    if (!unsat && !propagate()) {
        learnEmptyClause()
    }

    while (!unsat && !terminatedAsynchronously() &&
        vivifier.schedule.isNotEmpty() && stats.propagations.vivify < limit
    ) {
        val c = vivifier.schedule.last() // Next candidate.
        vivifier.schedule.removeAt(vivifier.schedule.size - 1)
        vivifyClause(vivifier, c)
    }

    if (level != 0) backtrack()

    if (!unsat) {

        resetNoccs()

        var stillNeedToBeVivified = 0L
        for (c in vivifier.schedule)
            if (c.vivify) stillNeedToBeVivified++

        // Preference clauses scheduled but not vivified yet next time.
        //
        if (stillNeedToBeVivified == 0L) {
            for (c in vivifier.schedule) c.vivify = true
        }

        vivifier.erase() // Reclaim  memory early.
    }

    clearWatches()
    connectWatches()

    if (!unsat) {

        // Since redundant clause were disconnected during propagating vivified
        // units in redundant mode, and further irredundant clauses are
        // arbitrarily sorted, we have to propagate all literals again after
        // connecting the first two literals in the clauses, in order to
        // reestablish the watching invariant.
        //
        propagated = 0
        propagated2 = propagated

        if (!propagate()) {
            learnEmptyClause()
        }
    }

    subsumed = stats.vivifysubs - subsumed
    strengthened = stats.vivifystrs - strengthened

    stats.subsumed += subsumed
    stats.strengthened += strengthened

    last.vivify.propagations = stats.propagations.search

    // report (redundant_mode ? 'w' : 'v', unsuccessful) dropped (message output); the
    // 'checked' and 'units' deltas of upstream only feed messages and 'unsuccessful'.
}

/*------------------------------------------------------------------------*/

internal fun Internal.vivify(): Unit = tracePhase("vivify") {

    if (unsat) return
    if (terminatedAsynchronously()) return
    if (stats.current.irredundant == 0L) return

    check(opts.vivify != 0) { "vivify: option off" }
    check(level == 0) { "vivify: level" }

    startSimplifier(Internal.VIVIFY)
    stats.vivifications++

    var limit = stats.propagations.search
    limit -= last.vivify.propagations
    limit = (limit * (1e-3 * opts.vivifyreleff)).toLong()
    if (limit < opts.vivifymineff) limit = opts.vivifymineff.toLong()
    if (limit > opts.vivifymaxeff) limit = opts.vivifymaxeff.toLong()

    vivifyRound(false, limit) // Vivify only irredundant clauses.

    limit = (limit * (1e-3 * opts.vivifyredeff)).toLong()

    vivifyRound(true, limit) // Vivify all clauses.

    stopSimplifier(Internal.VIVIFY)

    last.vivify.propagations = stats.propagations.search
}
