package org.bytefred.ksat.cadical.full

import kotlin.math.abs
import org.bytefred.ksat.cadical.IntArrayList

/*
 * analyze.cpp: conflict analysis (1st UIP clause), bumping (VMTF queue and EVSIDS scores,
 * reason side bumping), glue recomputation, chronological backtracking, on-the-fly
 * strengthening / subsumption (OTFS), eager subsumption and learning empty / unit clauses.
 *
 * Mapping notes:
 *  - 'int &open, int &resolvent_size, ...' -> IntRef (see SIGNATURES.md).
 *  - Comparators / rank functors -> private classes; 'typedef uint64_t Type' ranks compare
 *    as unsigned ('toULong ()').
 *  - 'eagerly_subsume_recently_learned_clauses' is missing in SIGNATURES.md (generator gap);
 *    it is defined here as 'Internal.eagerlySubsumeRecentlyLearnedClauses (c: Clause)'.
 *  - 'learn_external_reason_clause' can return null upstream (a unit after explanation);
 *    its Kotlin result type in SIGNATURES.md is 'Clause', the null checks are kept as upstream.
 */

/*------------------------------------------------------------------------*/

// Code for conflict analysis, i.e., to generate the first UIP clause.  The
// main function is 'analyze' below.  It further uses 'minimize' to minimize
// the first UIP clause, which is in 'minimize.cpp'.  An important side
// effect of conflict analysis is to update the decision queue by bumping
// variables.  Similarly analyzed clauses are bumped to mark them as active.

/*------------------------------------------------------------------------*/

internal fun Internal.learnEmptyClause() {
    check(!unsat) { "learn_empty_clause on unsat" }
    buildChainForEmpty()
    external!!.checkLearnedEmptyClause()
    val id = ++clauseId
    val proof = proof
    if (proof != null) {
        proof.addDerivedEmptyClause(id, lratChain)
    }
    unsat = true
    conflictId = id
    markedFailed = true
    conclusion.add(id)
    lratChain.clear()
}

internal fun Internal.learnUnitClause(lit: Int) {
    check(!unsat) { "learn_unit_clause on unsat" }
    external!!.checkLearnedUnitClause(lit)
    val id = ++clauseId
    if (lrat || frat) {
        val uidx = vlit(lit)
        check(lrat || frat)
        unitClausesIdx[uidx] = id
    }
    val proof = proof
    if (proof != null) {
        proof.addDerivedUnitClause(id, lit, lratChain)
    }
    markFixed(lit)
}

/*------------------------------------------------------------------------*/

// Move bumped variables to the front of the (VMTF) decision queue.  The
// 'bumped' time stamp is updated accordingly.  It is used to determine
// whether the 'queue.assigned' pointer has to be moved in 'unassign'.

// SIGNATURES.md names the parameter 'idx' (header); the definition names it 'lit'.
internal fun Internal.bumpQueue(lit: Int) {
    check(opts.bump != 0)
    val idx = vidx(lit)
    if (links[idx].next == 0) return
    queue.dequeue(links, idx)
    queue.enqueue(links, idx)
    check(stats.bumped != Long.MAX_VALUE)
    btab[idx] = ++stats.bumped
    if (vals[vsize + idx].toInt() == 0) updateQueueUnassigned(idx)
}

/*------------------------------------------------------------------------*/

// It would be better to use 'isinf' but there are some historical issues
// with this function.  On some platforms it is a macro and even for C++ it
// changed the scope (in pre 5.0 gcc) from '::isinf' to 'std::isinf'.  I do
// not want to worry about these strange incompatibilities and thus use the
// same trick as in older solvers (since the MiniSAT team invented EVSIDS)
// and simply put a hard limit here.  It is less elegant but easy to port.

private fun evsidsLimitHit(score: Double): Boolean {
    return score > 1e150 // MAX_DOUBLE is around 1.8e308
}

/*------------------------------------------------------------------------*/

// Classical exponential VSIDS as pioneered by MiniSAT.

internal fun Internal.rescaleVariableScores() {
    stats.rescored++
    var divider = scoreInc
    for (idx in vars) {
        val tmp = stab[idx]
        if (tmp > divider) divider = tmp
    }
    check(divider > 0)
    val factor = 1.0 / divider
    for (idx in vars) stab[idx] *= factor
    scoreInc *= factor
}

internal fun Internal.bumpVariableScore(lit: Int) {
    check(opts.bump != 0)
    val idx = vidx(lit)
    var oldScore = score(idx)
    check(!evsidsLimitHit(oldScore))
    var newScore = oldScore + scoreInc
    if (evsidsLimitHit(newScore)) {
        rescaleVariableScores()
        oldScore = score(idx)
        check(!evsidsLimitHit(oldScore))
        newScore = oldScore + scoreInc
    }
    check(!evsidsLimitHit(newScore))
    stab[vidx(idx)] = newScore
    if (scores.contains(idx)) scores.update(idx)
}

// Important variables recently used in conflict analysis are 'bumped',

internal fun Internal.bumpVariable(lit: Int) {
    if (useScores()) bumpVariableScore(lit)
    else bumpQueue(lit)
}

// After every conflict the variable score increment is increased by a
// factor (if we are currently using scores).

internal fun Internal.bumpVariableScoreInc() {
    check(useScores())
    check(!evsidsLimitHit(scoreInc))
    val f = 1e3 / opts.scorefactor
    var newScoreInc = scoreInc * f
    if (evsidsLimitHit(newScoreInc)) {
        rescaleVariableScores()
        newScoreInc = scoreInc * f
    }
    check(!evsidsLimitHit(newScoreInc))
    scoreInc = newScoreInc
}

/*------------------------------------------------------------------------*/

private class AnalyzeBumpedRank(private val internal: Internal) : IntRank {
    // typedef uint64_t Type;
    override fun rank(a: Int): Long = internal.bumped(a)
}

private class AnalyzeBumpedSmaller(private val internal: Internal) : IntLess {
    override fun less(a: Int, b: Int): Boolean {
        val s = AnalyzeBumpedRank(internal).rank(a)
        val t = AnalyzeBumpedRank(internal).rank(b)
        return s.toULong() < t.toULong()
    }
}

/*------------------------------------------------------------------------*/

internal fun Internal.bumpVariables() {

    check(opts.bump != 0)

    if (opts.bumpreason != 0) bumpAlsoAllReasonLiterals()

    if (!useScores()) {

        // Variables are bumped in the order they are in the current decision
        // queue.  This maintains relative order between bumped variables in
        // the queue and seems to work best.  We also experimented with
        // focusing on variables of the last decision level, but results were
        // mixed.

        msort(opts.radixsortlim, analyzed, AnalyzeBumpedRank(this), AnalyzeBumpedSmaller(this))
    }

    for (k in 0 until analyzed.size) bumpVariable(analyzed[k])

    if (useScores()) bumpVariableScoreInc()
}

/*------------------------------------------------------------------------*/

// We use the glue time stamp table 'gtab' for fast glue computation.

internal fun Internal.recomputeGlue(c: Clause): Int {
    var res = 0
    val stamp = ++stats.recomputed
    for (k in 0 until c.size) {
        val lit = c.literals[k]
        val level = variable(lit).level
        check(gtab[level] <= stamp)
        if (gtab[level] == stamp) continue
        gtab[level] = stamp
        res++
    }
    return res
}

// Clauses resolved since the last reduction are marked as 'used', their
// glue is recomputed and they are promoted if the glue shrinks.  Note that
// promotion from 'tier3' to 'tier2' will set 'used' to '2'.

internal fun Internal.bumpClause(c: Clause) {
    val used = c.used
    c.used = 1
    if (c.keep) return
    if (c.hyper) return
    if (!c.redundant) return
    val newGlue = recomputeGlue(c)
    if (newGlue < c.glue) promoteClause(c, newGlue)
    else if (used != 0 && c.glue <= opts.reducetier2glue) c.used = 2
}

/*------------------------------------------------------------------------*/

// During conflict analysis literals not seen yet either become part of the
// first unique implication point (UIP) clause (if on lower decision level),
// are dropped (if fixed), or are resolved away (if on the current decision
// level and different from the first UIP).  At the same time we update the
// number of seen literals on a decision level.  This helps conflict clause
// minimization.  The number of seen levels is the glucose level (also
// called 'glue', or 'LBD').

internal fun Internal.analyzeLiteral(lit: Int, open: IntRef, resolventSize: IntRef, antecedentSize: IntRef) {
    check(lit != 0)
    val v = variable(lit)
    val f = flags(lit)

    if (v.level == 0) {
        if (f.seen || !lrat) return
        f.seen = true
        unitAnalyzed.add(lit)
        check(value(lit) < 0)
        val uidx = vlit(-lit)
        val id = unitClauses(uidx)
        check(id != 0L)
        unitChain.add(id)
        return
    }
    ++antecedentSize.value
    if (f.seen) return

    // before marking as seen, get reason and check for missed unit

    check(value(lit) < 0)
    check(v.level <= level)
    if (v.reason === externalReason) {
        check(opts.exteagerreasons == 0)
        v.reason = learnExternalReasonClause(-lit, 0, true)
        if (v.reason == null) { // actually a unit
            --antecedentSize.value
            if (f.seen || !lrat) return
            f.seen = true
            unitAnalyzed.add(lit)
            check(value(lit) < 0)
            val uidx = vlit(-lit)
            val id = unitClauses(uidx)
            check(id != 0L)
            unitChain.add(id)
            return
        }
    }

    f.seen = true
    analyzed.add(lit)

    check(v.reason !== externalReason)
    if (v.level < level) clause.add(lit)
    val l = control[v.level]
    if (l.seenCount++ == 0) {
        levels.add(v.level)
    }
    if (v.trail < l.seenTrail) l.seenTrail = v.trail
    ++resolventSize.value
    if (v.level == level) open.value++
}

internal fun Internal.analyzeReason(lit: Int, reason: Clause, open: IntRef, resolventSize: IntRef, antecedentSize: IntRef) {
    check(reason !== externalReason)
    bumpClause(reason)
    if (lrat) lratChain.add(reason.id)
    for (k in 0 until reason.size) {
        val other = reason.literals[k]
        if (other != lit) analyzeLiteral(other, open, resolventSize, antecedentSize)
    }
}

/*------------------------------------------------------------------------*/

// This is an idea which was implicit in MapleCOMSPS 2016 for 'limit = 1'.
// See also the paragraph on 'bumping reason side literals' in their SAT'16
// paper [LiangGaneshPoupartCzarnecki-SAT'16].  Reason side bumping was
// performed exactly when 'LRB' based decision heuristics was used, which in
// the original version was enabled after 10000 conflicts until a time limit
// of 2500 seconds was reached (half of the competition time limit).  The
// Maple / Glucose / MiniSAT evolution winning the SAT race in 2019 made
// the schedule of reason side bumping deterministic, i.e., avoiding a time
// limit, by switching between 'LRB' and 'VSIDS' in an interval of initially
// 30 million propagations, which then is increased geometrically by 10%.

internal fun Internal.bumpAlsoReasonLiteral(lit: Int): Boolean {
    check(lit != 0)
    check(value(lit) < 0)
    val f = flags(lit)
    if (f.seen) return false
    val v = variable(lit)
    if (v.level == 0) return false
    f.seen = true
    analyzed.add(lit)
    return true
}

// We experimented with deeper reason bumping without much success though.

internal fun Internal.bumpAlsoReasonLiterals(lit: Int, limit: Int) {
    check(lit != 0)
    check(limit > 0)
    val v = variable(lit)
    check(value(lit) != 0)
    if (v.level == 0) return
    val reason = v.reason
    if (reason == null || reason === externalReason) return
    for (k in 0 until reason.size) {
        val other = reason.literals[k]
        if (other == lit) continue
        if (!bumpAlsoReasonLiteral(other)) continue
        if (limit < 2) continue
        bumpAlsoReasonLiterals(-other, limit - 1)
    }
}

internal fun Internal.bumpAlsoAllReasonLiterals() {
    check(opts.bumpreason != 0)
    check(opts.bumpreasondepth > 0)
    for (k in 0 until clause.size) {
        val lit = clause[k]
        bumpAlsoReasonLiterals(-lit, opts.bumpreasondepth + (if (stable) 1 else 0))
    }
}

/*------------------------------------------------------------------------*/

internal fun Internal.clearUnitAnalyzedLiterals() {
    for (k in 0 until unitAnalyzed.size) {
        val lit = unitAnalyzed[k]
        val f = flags(lit)
        check(f.seen)
        check(variable(lit).level == 0)
        f.seen = false
        check(!f.keep)
        check(!f.poison)
        check(!f.removable)
    }
    unitAnalyzed.clear()
}

internal fun Internal.clearAnalyzedLiterals() {
    for (k in 0 until analyzed.size) {
        val lit = analyzed[k]
        val f = flags(lit)
        check(f.seen)
        f.seen = false
        check(!f.keep)
        check(!f.poison)
        check(!f.removable)
    }
    analyzed.clear()
}

internal fun Internal.clearAnalyzedLevels() {
    for (k in 0 until levels.size) {
        val l = levels[k]
        if (l < control.size) control[l].reset()
    }
    levels.clear()
}

/*------------------------------------------------------------------------*/

// Smaller level and trail.  Comparing literals on their level is necessary
// for chronological backtracking, since trail order might in this case not
// respect level order.

private class AnalyzeTrailNegativeRank(private val internal: Internal) : IntRank {
    // typedef uint64_t Type;
    override fun rank(a: Int): Long {
        val v = internal.variable(a)
        var res = v.level.toLong() and 0xffffffffL
        res = res shl 32
        res = res or (v.trail.toLong() and 0xffffffffL)
        return res.inv()
    }
}

private class AnalyzeTrailLarger(private val internal: Internal) : IntLess {
    override fun less(a: Int, b: Int): Boolean {
        return AnalyzeTrailNegativeRank(internal).rank(a).toULong() <
            AnalyzeTrailNegativeRank(internal).rank(b).toULong()
    }
}

/*------------------------------------------------------------------------*/

// Generate new driving clause and compute jump level.

internal fun Internal.newDrivingClause(glue: Int, jump: IntRef): Clause? {

    val size = clause.size
    val res: Clause?

    if (size == 0) {

        jump.value = 0
        res = null

    } else if (size == 1) {

        iterating = true
        jump.value = 0
        res = null

    } else {

        check(clause.size > 1)

        // We have to get the last assigned literals into the watch position.
        // Sorting all literals with respect to reverse assignment order is
        // overkill but seems to get slightly faster run-time.  For 'minimize'
        // we sort the literals too heuristically along the trail order (so in
        // the opposite order) with the hope to hit the recursion limit less
        // frequently.  Thus sorting effort is doubled here.
        //
        msort(opts.radixsortlim, clause, AnalyzeTrailNegativeRank(this), AnalyzeTrailLarger(this))

        jump.value = variable(clause[1]).level
        res = newLearnedRedundantClause(glue)
        res.used = 1 + (if (glue <= opts.reducetier2glue) 1 else 0)
    }

    val tr = trace
    if (tr != null) { // LSTRACE
        tr.line("LEARN id=${res?.id ?: 0L} glue=$glue jump=${jump.value} :" + traceLits(clause))
    }

    return res
}

/*------------------------------------------------------------------------*/

// determine the OTFS level for OTFS. Unlike the find_conflict_level, we do
// not have to fix the clause

internal fun Internal.otfsFindBacktrackLevel(forced: IntRef): Int {
    check(opts.otfs != 0)
    var res = 0

    val conflict = conflict!!
    for (k in 0 until conflict.size) {
        val lit = conflict.literals[k]
        val tmp = variable(lit).level
        if (tmp == level) {
            forced.value = lit
        } else if (tmp > res) {
            res = tmp
        }
    }
    return res
}

/*------------------------------------------------------------------------*/

// If chronological backtracking is enabled we need to find the actual
// conflict level and then potentially can also reuse the conflict clause
// as driving clause instead of deriving a redundant new driving clause
// (forcing 'forced') if the number 'count' of literals in conflict assigned
// at the conflict level is exactly one.

internal fun Internal.findConflictLevel(forced: IntRef): Int {

    val conflict = checkNotNull(conflict) { "find_conflict_level without conflict" }
    check(opts.chrono != 0 || opts.otfs != 0 || externalProp)

    var res = 0
    var count = 0

    forced.value = 0

    for (k in 0 until conflict.size) {
        val lit = conflict.literals[k]
        val tmp = variable(lit).level
        if (tmp > res) {
            res = tmp
            forced.value = lit
            count = 1
        } else if (tmp == res) {
            count++
            if (res == level && count > 1) break
        }
    }

    val size = conflict.size
    val lits = conflict.literals

    // Move the two highest level literals to the front.
    //
    for (i in 0 until 2) {

        val lit = lits[i]

        var highestPosition = i
        var highestLiteral = lit
        var highestLevel = variable(highestLiteral).level

        for (j in i + 1 until size) {
            val other = lits[j]
            val tmp = variable(other).level
            if (highestLevel >= tmp) continue
            highestLiteral = other
            highestPosition = j
            highestLevel = tmp
            if (highestLevel == res) break
        }

        // No unwatched higher assignment level literal.
        //
        if (highestPosition == i) continue

        if (highestPosition > 1) {
            removeWatch(watches(lit), conflict)
        }

        lits[highestPosition] = lit
        lits[i] = highestLiteral

        if (highestPosition > 1) watchLiteral(highestLiteral, lits[if (i == 0) 1 else 0], conflict)
    }

    // Only if the number of highest level literals in the conflict is one
    // then we can reuse the conflict clause as driving clause for 'forced'.
    //
    if (count != 1) forced.value = 0

    return res
}

/*------------------------------------------------------------------------*/

internal fun Internal.determineActualBacktrackLevel(jump: Int): Int {

    var res: Int

    check(level > jump)

    if (opts.chrono == 0) {
        res = jump
        // chronological backtracking disabled using jump level
    } else if (opts.chronoalways != 0) {
        stats.chrono++
        res = level - 1
        // forced chronological backtracking
    } else if (jump >= level - 1) {
        res = jump
        // jump level identical to chronological backtrack level
    } else if (jump < assumptions.size) {
        res = jump
        // using jump level since it is lower than assumption level
    } else if (level - jump > opts.chronolevelim) {
        stats.chrono++
        res = level - 1
        // back-jumping over too many levels prohibited thus backtracking chronologically
    } else if (opts.chronoreusetrail != 0) {
        var bestIdx = 0
        var bestPos = 0

        if (useScores()) {
            for (i in control[jump + 1].trail until trail.size) {
                val idx = abs(trail[i])
                if (bestIdx != 0 && !ScoreSmaller(this).less(bestIdx, idx)) continue
                bestIdx = idx
                bestPos = i
            }
        } else {
            for (i in control[jump + 1].trail until trail.size) {
                val idx = abs(trail[i])
                if (bestIdx != 0 && bumped(bestIdx) >= bumped(idx)) continue
                bestIdx = idx
                bestPos = i
            }
        }
        check(bestIdx != 0)

        // Now find the frame and decision level in the control stack of that
        // best variable index.  Note that, as in 'reuse_trail', the frame
        // 'control[i]' for decision level 'i' contains the trail before that
        // decision level, i.e., the decision 'control[i].decision' sits at
        // 'control[i].trail' in the trail and we thus have to check the level
        // of the control frame one higher than at the result level.
        //
        res = jump
        while (res < level - 1 && control[res + 1].trail <= bestPos) res++

        if (res == jump) {
            // default non-chronological back-jumping
        } else {
            stats.chrono++
            // chronological backtracking to reuse trail
        }

    } else {
        res = jump
        // non-chronological back-jumping
    }

    return res
}

/*------------------------------------------------------------------------*/

internal fun Internal.eagerlySubsumeRecentlyLearnedClauses(c: Clause) {
    check(opts.eagersubsume != 0)
    mark(c)
    val lim = stats.eagertried + opts.eagersubsumelim
    val begin = 0
    var it = clauses.size
    while (it != begin && stats.eagertried++ <= lim) {
        val d = clauses[--it]
        if (c === d) continue
        if (d.garbage) continue
        if (!d.redundant) continue
        var needed = c.size
        for (k in 0 until d.size) {
            val lit = d.literals[k]
            if (marked(lit) <= 0) continue
            if (--needed == 0) break
        }
        if (needed != 0) continue
        stats.eagersub++
        stats.subsumed++
        markGarbage(d)
    }
    unmark(c)
}

/*------------------------------------------------------------------------*/

internal fun Internal.onTheFlyStrengthen(conflict: Clause, lit: Int): Clause? {
    val newConflict = conflict
    val uip = lit
    check(newConflict.size > 2)
    val sorted = IntArrayList()
    check(sorted.isEmpty())
    ++stats.otfs.strengthened

    val lits = newConflict.literals

    check(lits[0] == uip || lits[1] == uip)
    val otherInit = lits[0] xor lits[1] xor uip

    check(miniChain.isEmpty())

    val oldSize = newConflict.size
    var newSize = 0
    for (i in 0 until oldSize) {
        val other = lits[i]
        sorted.add(other)
        if (variable(other).level != 0) lits[newSize++] = other
    }

    check(lits[0] == uip || lits[1] == uip)
    val other = lits[0] xor lits[1] xor uip
    lits[0] = other
    lits[1] = lits[--newSize]

    if (otherInit != other) removeWatch(watches(otherInit), newConflict)
    removeWatch(watches(uip), newConflict)

    check(!lrat || lratChain.last() == newConflict.id)
    if (lrat) {
        check(lratChain.isNotEmpty())
        for (id in unitChain) {
            miniChain.add(id)
        }
        val end = -1
        val begin = lratChain.size - 1
        var i = begin
        while (i != end) {
            val id = lratChain[i]
            miniChain.add(id)
            i--
        }
        lratChain.clear() // see if this is correct...
        clearUnitAnalyzedLiterals()
        unitChain.clear()
    }
    check(unitAnalyzed.isEmpty())
    // sort the clause
    run {
        var highestPos = 0
        var highestLevel = 0
        for (i in 1 until newSize) {
            val other = lits[i]
            check(value(other) < 0)
            val level = variable(other).level
            check(level != 0)
            if (level <= highestLevel) continue
            highestPos = i
            highestLevel = level
        }
        if (highestPos != 1) {
            val tmp = lits[1]
            lits[1] = lits[highestPos]
            lits[highestPos] = tmp
        }

        if (newSize == 1) {
            check(opts.exteagerreasons == 0)
            return null
        } else {
            otfsStrengthenClause(newConflict, uip, newSize, sorted)
            check(newSize == newConflict.size)
        }
    }

    if (otherInit != other) watchLiteral(other, lits[1], newConflict)
    else {
        updateWatchSize(watches(other), lits[1], newConflict)
    }
    watchLiteral(lits[1], other, newConflict)

    sorted.clear()

    return newConflict
}

/*------------------------------------------------------------------------*/
internal fun Internal.otfsSubsumeClause(subsuming: Clause, subsumed: Clause) {
    stats.subsumed++
    check(subsuming.size <= subsumed.size)
    if (subsumed.redundant) stats.subred++
    else stats.subirr++
    if (subsumed.redundant || !subsuming.redundant) {
        markGarbage(subsumed)
        return
    }
    // turning redundant subsuming clause into irredundant clause
    subsuming.redundant = false
    proof?.strengthen(subsuming.id)
    markGarbage(subsumed)
    stats.current.irredundant++
    stats.added.irredundant++
    stats.irrlits += subsuming.size
    check(stats.current.redundant > 0)
    stats.current.redundant--
    check(stats.added.redundant > 0)
    stats.added.redundant--
    // ... and keep 'stats.added.total'.
}

/*------------------------------------------------------------------------*/

// Candidate clause 'c' is strengthened by removing 'lit' and units.
//
internal fun Internal.otfsStrengthenClause(c: Clause, lit: Int, newSize: Int, old: IntArrayList) {
    stats.strengthened++
    check(c.size > 2)
    shrinkClause(c, newSize)
    val proof = proof
    if (proof != null) {
        proof.otfsStrengthenClause(c, old, miniChain)
    }
    if (!c.redundant) {
        markRemoved(lit)
    }
    miniChain.clear()
    c.used = 1
    external!!.checkShrunkenClause(c)
}

/*------------------------------------------------------------------------*/

// This is the main conflict analysis routine.  It assumes that a conflict
// was found.  Then we derive the 1st UIP clause, optionally minimize it,
// add it as learned clause, and then uses the clause for conflict directed
// back-jumping and flipping the 1st UIP literal.  In combination with
// chronological backtracking (see discussion above) the algorithm becomes
// slightly more involved.

internal fun Internal.analyze() {

    check(conflict != null) { "analyze without conflict" }
    val tr = trace
    if (tr != null) { // LSTRACE
        val c = conflict!!
        tr.line("CONFLICT level=$level ${c.id} :" + traceLits(c))
    }
    check(lratChain.isEmpty())
    check(unitChain.isEmpty())
    check(unitAnalyzed.isEmpty())
    check(clause.isEmpty())

    // First update moving averages of trail height at conflict.
    //
    averages.current.trail.fast.update(numAssigned.toDouble())
    averages.current.trail.slow.update(numAssigned.toDouble())

    /*----------------------------------------------------------------------*/

    if (externalProp && !externalPropIsLazy && opts.exteagerreasons != 0) {
        explainExternalPropagations()
    }

    if (opts.chrono != 0 || externalProp) {

        val forced = IntRef()

        val conflictLevel = findConflictLevel(forced)

        // In principle we can perform conflict analysis as in non-chronological
        // backtracking except if there is only one literal with the maximum
        // assignment level in the clause.  Then standard conflict analysis is
        // unnecessary and we can use the conflict as a driving clause.  In the
        // pseudo code of the SAT'18 paper on chronological backtracking this
        // corresponds to the situation handled in line 4-6 in Alg. 1, except
        // that the pseudo code in the paper only backtracks while we eagerly
        // assign the single literal on the highest decision level.

        if (forced.value != 0) {

            check(forced.value != 0)
            check(conflictLevel > 0)

            // The pseudo code in the SAT'18 paper actually backtracks to the
            // 'second highest decision' level, while their code backtracks
            // to 'conflict_level-1', which is more in the spirit of chronological
            // backtracking anyhow and thus we also do the latter.
            //
            backtrack(conflictLevel - 1)

            // if we are on decision level 0 search assign will learn unit
            // so we need a valid chain here (of course if we are not on decision
            // level 0 this will not result in a valid chain).
            // we can just use build_chain_for_units in propagate
            //
            buildChainForUnits(forced.value, conflict!!, false)

            searchAssignDriving(forced.value, conflict)

            conflict = null
            return
        }

        // Backtracking to the conflict level is in the pseudo code in the
        // SAT'18 chronological backtracking paper, but not in their actual
        // implementation.  In principle we do not need to backtrack here.
        // However, as a side effect of backtracking to the conflict level we
        // set 'level' to the conflict level which then allows us to reuse the
        // old 'analyze' code as is.  The alternative (which we also tried but
        // then abandoned) is to use 'conflict_level' instead of 'level' in the
        // analysis, which however requires to pass it to the 'analyze_reason'
        // and 'analyze_literal' functions.
        //
        backtrack(conflictLevel)
    }

    // Actual conflict on root level, thus formula unsatisfiable.
    //
    if (level == 0) {
        learnEmptyClause()
        if (external!!.learner != null) external!!.exportLearnedEmptyClause()
        // lrat_chain.clear (); done in learn_empty_clause
        return
    }

    /*----------------------------------------------------------------------*/

    // First derive the 1st UIP clause by going over literals assigned on the
    // current decision level.  Literals in the conflict are marked as 'seen'
    // as well as all literals in reason clauses of already 'seen' literals on
    // the current decision level.  Thus the outer loop starts with the
    // conflict clause as 'reason' and then uses the 'reason' of the next
    // seen literal on the trail assigned on the current decision level.
    // During this process maintain the number 'open' of seen literals on the
    // current decision level with not yet processed 'reason'.  As soon 'open'
    // drops to one, we have found the first unique implication point.  This
    // is sound because the topological order in which literals are processed
    // follows the assignment order and a more complex algorithm to find
    // articulation points is not necessary.
    //
    var reason: Clause? = conflict

    check(clause.isEmpty())
    check(lratChain.isEmpty())

    val t = trail
    var i = t.size // Start at end-of-trail.
    val open = IntRef(0) // Seen but not processed on this level.
    var uip = 0 // The first UIP literal.
    val resolventSize = IntRef(0) // without the uip
    val antecedentSize = IntRef(1) // with the uip and without unit literals
    var conflictSize = 0 // size of the conflict without the uip and without unit literals
    var resolved = 0 // number of resolution (0 = clause in CNF)
    val otfs = opts.otfs != 0

    while (true) {
        antecedentSize.value = 1 // for uip
        analyzeReason(uip, reason!!, open, resolventSize, antecedentSize)
        if (resolved == 0) conflictSize = antecedentSize.value - 1
        check(resolventSize.value == open.value + clause.size)

        if (otfs && resolved > 0 && antecedentSize.value > 2 &&
            resolventSize.value < antecedentSize.value
        ) {
            check(reason !== conflict)
            val other = reason.literals[0] xor reason.literals[1] xor uip
            check(other != uip)
            reason = onTheFlyStrengthen(reason, uip)
            if (tr != null) { // LSTRACE
                if (reason != null) {
                    tr.line("OTFS ${reason.id} :" + traceLits(reason))
                } else tr.line("OTFS 0 : 0")
            }
            if (opts.bump != 0) bumpVariables()

            check(conflictSize != 0)
            if (reason == null) {
                uip = -other
                check(open.value == 1)
                miniChain.reverse()
                for (id in miniChain) lratChain.add(id)
                miniChain.clear()
                clearAnalyzedLevels()
                check(opts.exteagerreasons == 0)
                clause.clear()
                break
            }
            check(conflictSize >= 2)

            if (resolved == 1 && resolventSize.value < conflictSize) {
                // in this case both clauses are part of the CNF, so one subsumes
                // the other
                otfsSubsumeClause(reason, conflict!!)
                --conflictSize
                check(conflictSize == reason.size)
                ++stats.otfs.subsumed
                ++stats.subsumed
                ++stats.conflicts
            }

            conflict = reason
            if (open.value == 1) {
                val forced = IntRef(0)
                val conflictLevel = otfsFindBacktrackLevel(forced)
                val newLevel = determineActualBacktrackLevel(conflictLevel)
                averages.current.level.update(newLevel.toDouble())
                backtrack(newLevel)

                searchAssignDriving(forced.value, conflict)

                conflict = null
                // Clean up.
                //
                clearAnalyzedLiterals()
                clearAnalyzedLevels()
                clause.clear()
                return
            }

            resolved = 0
            clearAnalyzedLiterals()
            // clear_analyzed_levels (); not needed because marking the exact same
            // again
            clause.clear()
            resolventSize.value = 0
            antecedentSize.value = 1
            open.value = 0
            analyzeReason(0, reason, open, resolventSize, antecedentSize)
            conflictSize = antecedentSize.value - 1
            check(open.value > 1)
        }

        ++resolved

        uip = 0
        while (uip == 0) {
            check(i > 0)
            val lit = t[--i]
            if (!flags(lit).seen) continue
            if (variable(lit).level == level) uip = lit
        }
        if (--open.value == 0) break
        reason = variable(uip).reason
        if (reason === externalReason) {
            check(opts.exteagerreasons == 0)
            reason = learnExternalReasonClause(-uip, 0, true)
            variable(uip).reason = reason
        }
        check(reason !== externalReason)
        check(resolventSize.value != 0)
        --resolventSize.value
    }
    clause.add(-uip)

    // Update glue and learned (1st UIP literals) statistics.
    //
    var size = clause.size
    val glue = levels.size - 1
    averages.current.glue.fast.update(glue.toDouble())
    averages.current.glue.slow.update(glue.toDouble())
    stats.learned.literals += size
    stats.learned.clauses++
    check(glue < size)

    // up to this point lrat_chain contains the proof for current clause in
    // reversed order. in minimize and shrink the clause is changed and
    // therefore lrat_chain has to be extended. Unfortunately we cannot create
    // the chain directly during minimization (or shrinking) but afterwards we
    // can calculate it pretty easily and even better the same algorithm works
    // for both shrinking and minimization.

    // Minimize the 1st UIP clause as pioneered by Niklas Soerensson in
    // MiniSAT and described in our joint SAT'09 paper.
    //
    if (size > 1) {
        if (opts.shrink != 0) shrinkAndMinimizeClause()
        else if (opts.minimize != 0) minimizeClause()

        size = clause.size

        // Update decision heuristics.
        //
        if (opts.bump != 0) bumpVariables()

        if (external!!.learner != null) external!!.exportLearnedLargeClause(clause)
    } else if (external!!.learner != null) external!!.exportLearnedUnitClause(-uip)

    // Update actual size statistics.
    //
    stats.units += (if (size == 1) 1 else 0)
    stats.binaries += (if (size == 2) 1 else 0)
    averages.current.size.update(size.toDouble())

    // reverse lrat_chain. We could probably work with reversed iterators
    // (views) to be more efficient but we would have to distinguish in proof
    //
    if (lrat) {
        for (id in unitChain) lratChain.add(id)
        unitChain.clear()
        lratChain.reverse()
    }

    // Determine back-jump level, learn driving clause, backtrack and assign
    // flipped 1st UIP literal.
    //
    val jump = IntRef()
    val drivingClause = newDrivingClause(glue, jump)
    averages.current.jump.update(jump.value.toDouble())

    val newLevel = determineActualBacktrackLevel(jump.value)
    averages.current.level.update(newLevel.toDouble())
    backtrack(newLevel)

    // It should hold that (!level <=> size == 1)
    //                 and (!uip   <=> size == 0)
    // this means either we have already learned a clause => size >= 2
    // in this case we will not learn empty clause or unit here
    // or we haven't actually learned a clause in new_driving_clause
    // then lrat_chain is still valid and we will learn a unit or empty clause
    //
    if (uip != 0) {
        searchAssignDriving(-uip, drivingClause)
    } else learnEmptyClause()

    if (stable) reluctant.tick() // Reluctant has its own 'conflict' counter.

    // Clean up.
    //
    clearAnalyzedLiterals()
    clearUnitAnalyzedLiterals()
    clearAnalyzedLevels()
    clause.clear()
    conflict = null

    lratChain.clear()

    if (drivingClause != null && opts.eagersubsume != 0) eagerlySubsumeRecentlyLearnedClauses(drivingClause)
}

// We wait reporting a learned unit until propagation of that unit is
// completed.  Otherwise the 'i' report gives the number of remaining
// variables before propagating the unit (and hides the actual remaining
// variables after propagating it).

internal fun Internal.iterate() {
    iterating = false
    // report ('i'): message output, not ported
}
