package org.bytefred.ksat.cadical.full

import kotlin.math.abs
import kotlin.math.min
import org.bytefred.ksat.cadical.IntArrayList

/*
 * external.cpp (CaDiCaL 2.1.3): the external variable layer (e2i / i2e mapping, freezing,
 * observed variables, assumptions and constraint at the external level, model checking,
 * unit traversal and learned clause export).
 *
 * Not here: the constructor (ExternalHpp.kt 'init' block). The destructor only frees
 * 'solution' (garbage collected).
 *
 * Dropped as PORTING.md says: LOG, VERBOSE, MSG. 'FATAL' / 'fatal_message_start ... end' ->
 * Kotlin 'error (...)' with the same text.
 */

internal fun External.enlarge(newMaxVar: Int) {

    check(!extended) { "enlarge while extended" }

    var newVsize = if (vsize != 0) 2 * vsize else 1 + newMaxVar
    while (newVsize <= newMaxVar) newVsize *= 2
    vsize = newVsize
}

internal fun External.init(newMaxVar: Int) {
    check(!extended) { "init while extended" }
    if (newMaxVar <= maxVar) return
    val newVars = newMaxVar - maxVar
    val oldInternalMaxVar = internal.maxVar
    val newInternalMaxVar = oldInternalMaxVar + newVars
    internal.initVars(newInternalMaxVar)
    if (newMaxVar >= vsize) enlarge(newMaxVar)
    if (maxVar == 0) {
        check(e2i.isEmpty()) { "e2i not empty" }
        e2i.add(0)
        extUnits.add(0L)
        extUnits.add(0L)
        extFlags.add(false)
        check(internal.i2e.isEmpty()) { "i2e not empty" }
        internal.i2e.add(0)
    } else {
        check(e2i.size == maxVar + 1) { "e2i size mismatch" }
        check(internal.i2e.size == oldInternalMaxVar + 1) { "i2e size mismatch" }
    }
    var iidx = oldInternalMaxVar + 1
    var eidx = maxVar + 1
    while (eidx <= newMaxVar) {
        check(e2i.size == eidx) { "e2i size mismatch" }
        e2i.add(iidx)
        extUnits.add(0L)
        extUnits.add(0L)
        extFlags.add(false)
        internal.i2e.add(eidx)
        check(internal.i2e[iidx] == eidx)
        check(e2i[eidx] == iidx)
        eidx++
        iidx++
    }
    if (newMaxVar.toLong() >= isObserved.size.toLong()) isObserved.resize(1 + newMaxVar, false)
    if (internal.opts.checkfrozen != 0)
        if (newMaxVar.toLong() >= moltentab.size.toLong()) moltentab.resize(1 + newMaxVar, false)
    check(iidx == newInternalMaxVar + 1)
    check(eidx == newMaxVar + 1)
    check(extUnits.size == newMaxVar * 2 + 2)
    maxVar = newMaxVar
}

/*------------------------------------------------------------------------*/

internal fun External.resetAssumptions() {
    assumptions.clear()
    internal.resetAssumptions()
}

internal fun External.resetConcluded() {
    concluded = false
    internal.resetConcluded()
}

internal fun External.resetConstraint() {
    constraint.clear()
    internal.resetConstraint()
}

internal fun External.resetExtended() {
    if (!extended) return
    extended = false
}

internal fun External.resetLimits() {
    internal.resetLimits()
}

/*------------------------------------------------------------------------*/

internal fun External.internalize(elit: Int): Int {
    var ilit: Int
    if (elit != 0) {
        check(elit != Int.MIN_VALUE)
        val eidx = abs(elit)
        if (eidx > maxVar) init(eidx)
        ilit = e2i[eidx]
        if (elit < 0) ilit = -ilit
        if (ilit == 0) {
            check(internal.maxVar < Int.MAX_VALUE)
            ilit = internal.maxVar + 1
            internal.initVars(ilit)
            e2i[eidx] = ilit
            e2i[eidx] = ilit
            internal.i2e.add(eidx)
            check(internal.i2e[ilit] == eidx)
            check(e2i[eidx] == ilit)
            if (elit < 0) ilit = -ilit
        }
        if (internal.opts.checkfrozen != 0) {
            check(eidx < moltentab.size)
            if (moltentab[eidx]) error("can not reuse molten literal $eidx")
        }
        val f = internal.flags(ilit)
        if (f.status == Flags.UNUSED) internal.markActive(ilit)
        else if (f.status != Flags.ACTIVE && f.status != Flags.FIXED) internal.reactivate(ilit)
        if (!marked(tainted, elit) && marked(witness, -elit)) {
            check(internal.opts.checkfrozen == 0)
            mark(tainted, elit)
        }
    } else
        ilit = 0
    return ilit
}

internal fun External.add(elit: Int) {
    check(elit != Int.MIN_VALUE)
    resetExtended()

    var forgettable = false

    if (internal.opts.check != 0 && (internal.opts.checkwitness != 0 || internal.opts.checkfailed != 0)) {

        forgettable = internal.fromPropagator && internal.extClauseForgettable

        // Forgettable clauses (coming from the external propagator) are not
        // saved into the external 'original' stack. They are stored separately
        // in external 'forgettable_original', from where they are deleted when
        // the corresponding clause is deleted (actually deleted, not just
        // marked as garbage).
        if (!forgettable) original.add(elit)
    }

    val ilit = internalize(elit)
    check((elit == 0) == (ilit == 0))

    // The external literals of the new clause must be saved for later
    // when the proof is printed during add_original_lit (0)
    if (elit != 0 && (internal.proof != null || forgettable)) {
        eclause.add(elit)
        if (internal.lrat) {
            // actually find unit of -elit (flips elit < 0)
            val eidx = (if (elit > 0) 1 else 0) + 2 * abs(elit)
            check(eidx < extUnits.size)
            val id = extUnits[eidx]
            val added = extFlags[abs(elit)]
            if (id != 0L && !added) {
                extFlags[abs(elit)] = true
                internal.lratChain.add(id)
            }
        }
    }

    if (elit == 0 && internal.proof != null && internal.lrat) {
        for (k in 0 until eclause.size) {
            extFlags[abs(eclause[k])] = false
        }
    }

    internal.addOriginalLit(ilit)

    // Clean-up saved external literals once proof line is printed
    if (elit == 0 && (internal.proof != null || forgettable)) eclause.clear()
}

internal fun External.assume(elit: Int) {
    check(elit != 0)
    resetExtended()
    internal.proof?.addAssumption(elit)
    assumptions.add(elit)
    val ilit = internalize(elit)
    check(ilit != 0)
    internal.assume(ilit)
}

internal fun External.flip(elit: Int): Boolean {
    check(elit != 0)
    check(elit != Int.MIN_VALUE)
    check(propagator == null)

    val eidx = abs(elit)
    if (eidx > maxVar) return false
    if (marked(witness, elit)) return false
    val ilit = e2i[eidx]
    if (ilit == 0) return false
    val res = internal.flip(ilit)
    if (res && extended) resetExtended()
    return res
}

internal fun External.flippable(elit: Int): Boolean {
    check(elit != 0)
    check(elit != Int.MIN_VALUE)
    check(propagator == null)

    val eidx = abs(elit)
    if (eidx > maxVar) return false
    if (marked(witness, elit)) return false
    val ilit = e2i[eidx]
    if (ilit == 0) return false
    return internal.flippable(ilit)
}

internal fun External.failed(elit: Int): Boolean {
    check(elit != 0)
    check(elit != Int.MIN_VALUE)
    val eidx = abs(elit)
    if (eidx > maxVar) return false
    var ilit = e2i[eidx]
    if (ilit == 0) return false
    if (elit < 0) ilit = -ilit
    return internal.failed(ilit)
}

internal fun External.constrain(elit: Int) {
    if (constraint.size != 0 && constraint.back() == 0) {
        resetConstraint()
    }
    check(elit != Int.MIN_VALUE)
    resetExtended()
    val ilit = internalize(elit)
    check((elit == 0) == (ilit == 0))
    if (elit == 0) internal.proof?.addConstraint(constraint) // (LOG for 'elit != 0' dropped)
    constraint.add(elit)
    internal.constrain(ilit)
}

internal fun External.failedConstraint(): Boolean = internal.failedConstraint()

internal fun External.phase(elit: Int) {
    check(elit != 0)
    check(elit != Int.MIN_VALUE)
    val ilit = internalize(elit)
    internal.phase(ilit)
}

internal fun External.unphase(elit: Int) {
    check(elit != 0)
    check(elit != Int.MIN_VALUE)
    val eidx = abs(elit)
    if (eidx > maxVar) {
        // UNUSED: resetting forced phase of unused external literal ignored
        return
    }
    var ilit = e2i[eidx]
    if (ilit == 0) return // goto UNUSED
    if (elit < 0) ilit = -ilit
    internal.unphase(ilit)
}

/*------------------------------------------------------------------------*/

// External propagation related functions
//
// Note that when an already assigned variable is added as observed, the
// solver will backtrack to undo this assignment.
//
internal fun External.addObservedVar(elit: Int) {
    val propagator = propagator ?: return // no connected propagator, observed flag not set

    check(elit != 0)
    check(elit != Int.MIN_VALUE)
    resetExtended() // tainting!

    val eidx = abs(elit)
    if (eidx <= maxVar && (marked(witness, elit) || marked(witness, -elit))) {
        // Error, only clean variables are allowed to become observed.
        check(false) { "only clean variables are allowed to become observed" }

        // TODO: here needs to come the taint and restore of the newly
        // observed variable. Restore_clauses must be called before continue.
        // LOG ("marking tainted %d", elit);
        // mark (tainted, elit);
        // mark (tainted, -elit);
        // restore_clauses ...
    }

    if (eidx.toLong() >= isObserved.size.toLong()) isObserved.resize(1 + eidx, false)

    if (isObserved[eidx]) return

    // Will do the necessary internalization
    freeze(elit)
    isObserved[eidx] = true

    val ilit = internalize(elit)
    // internal add-observed-var backtracks to a lower decision level to
    // unassign the variable in case it was already assigned previously (but
    // not on the current level)
    internal.addObservedVar(ilit)

    if (propagator.isLazy) return

    // In case this variable was already assigned (e.g. via unit clause) and
    // got compacted to map to another (not observed) variable, it can not be
    // unnasigned so it must be notified explicitly now. (-> Can lead to
    // repeated fixed assignment notifications, in case it was unobserved and
    // observed again. But a repeated notification is less error-prone than
    // never notifying an assignment.)
    val tmp = fixed(elit)
    if (tmp == 0) return
    val unit = if (tmp < 0) -elit else elit

    // internal add-observed-var had to backtrack to root-level already
    check(internal.level == 0)

    val assigned = intArrayOf(unit)
    propagator.notifyAssignment(assigned)
}

internal fun External.removeObservedVar(elit: Int) {
    if (propagator == null) {
        return // no connected propagator that could have watched the variable
    }
    val eidx = abs(elit)

    if (eidx > maxVar) return

    if (isObserved[eidx]) {
        // Follow opposite order of add_observed_var, first remove internal
        // is_observed
        val ilit = e2i[eidx] // internalize (elit);
        internal.removeObservedVar(ilit)

        isObserved[eidx] = false
        melt(elit)
    }
}

internal fun External.resetObservedVars() {
    // Shouldn't be called if there is no connected propagator
    check(propagator != null)
    resetExtended()

    internal.notified = 0

    if (isObserved.size == 0) return

    check(maxVar == 0 || maxVar + 1 == isObserved.size)

    for (elit in vars) {
        val eidx = abs(elit)
        check(eidx <= maxVar)
        if (isObserved[eidx]) {
            val ilit = internalize(elit)
            internal.removeObservedVar(ilit)
            isObserved[eidx] = false
            melt(elit)
        }
    }
}

internal fun External.observed(elit: Int): Boolean {
    check(elit != 0)
    check(elit != Int.MIN_VALUE)
    val eidx = abs(elit)
    if (eidx > maxVar) return false
    if (eidx >= isObserved.size) return false

    return isObserved[eidx]
}

internal fun External.isWitness(elit: Int): Boolean {
    check(elit != 0)
    check(elit != Int.MIN_VALUE)
    val eidx = abs(elit)
    if (eidx > maxVar) return false
    return marked(witness, elit) || marked(witness, -elit)
}

internal fun External.isDecision(elit: Int): Boolean {
    check(elit != 0)
    check(elit != Int.MIN_VALUE)
    val eidx = abs(elit)
    if (eidx > maxVar) return false

    val ilit = internalize(elit)
    return internal.isDecision(ilit)
}

internal fun External.forceBacktrack(newLevel: Int) {
    if (propagator == null) {
        return // no connected propagator that could force backtracking
    }
    internal.forceBacktrack(newLevel)
}

/*------------------------------------------------------------------------*/

internal fun External.propagateAssumptions(): Int {
    val res = internal.propagateAssumptions()
    if (res == 10 && !extended) extend() // Call solution reconstruction
    checkSolveResult(res)
    resetLimits()
    return res
}

internal fun External.getEntrailedLiterals(entrailed: IntArrayList) {
    val ilitImplicants = IntArrayList()
    internal.getEntrailedLiterals(ilitImplicants)

    // Those implied literals must be filtered out that are witnesses
    // on the reconstruction stack -> no inplace externalize is possible.
    // (Internal does not see these marks, so no earlier filter is
    // possible.)

    for (k in 0 until ilitImplicants.size) {
        val ilit = ilitImplicants[k]
        check(ilit != 0)
        val elit = internal.externalize(ilit)
        if (!marked(tainted, elit)) {
            entrailed.add(elit)
        }
    }
}

internal fun External.concludeUnknown() {
    val proof = internal.proof
    if (proof == null || concluded) return
    concluded = true

    val trail = IntArrayList()
    getEntrailedLiterals(trail)
    proof.concludeUnknown(trail)
}

/*------------------------------------------------------------------------*/

// Internal checker if 'solve' claims the formula to be satisfiable.

internal fun External.checkSatisfiable() {
    if (!extended) extend()
    if (internal.opts.checkwitness != 0) checkAssignment { ival(it) }
    if (internal.opts.checkassumptions != 0 && !assumptions.isEmpty()) checkAssumptionsSatisfied()
    if (internal.opts.checkconstraint != 0 && !constraint.isEmpty()) checkConstraintSatisfied()
}

// Internal checker if 'solve' claims formula to be unsatisfiable.

internal fun External.checkUnsatisfiable() {
    if (internal.opts.checkfailed == 0) return
    if (!assumptions.isEmpty() || !constraint.isEmpty()) checkFailing()
}

// Check result of 'solve' to be correct.

internal fun External.checkSolveResult(res: Int) {
    if (internal.opts.check == 0) return
    if (res == 10) checkSatisfiable()
    if (res == 20) checkUnsatisfiable()
}

// Prepare checking that completely molten literals are not used as argument
// of 'add' or 'assume', which is invalid under freezing semantics.  This
// case would be caught by our 'restore' implementation so is only needed
// for checking the deprecated 'freeze' semantics.

internal fun External.updateMoltenLiterals() {
    if (internal.opts.checkfrozen == 0) return
    check(maxVar + 1 == moltentab.size)
    for (lit in vars) {
        if (moltentab[lit]) {
            // skipping already molten literal
        } else if (frozen(lit)) {
            // skipping currently frozen literal
        } else {
            moltentab[lit] = true
        }
    }
}

internal fun External.solve(preprocessOnly: Boolean): Int {
    resetExtended()
    updateMoltenLiterals()
    val res = internal.solve(preprocessOnly)
    checkSolveResult(res)
    resetLimits()
    return res
}

internal fun External.terminate() {
    internal.terminate()
}

internal fun External.lookahead(): Int {
    resetExtended()
    updateMoltenLiterals()
    val ilit = internal.lookahead()
    val elit = if (ilit != 0 && ilit != Int.MIN_VALUE) internal.externalize(ilit) else 0
    return elit
}

internal fun External.generateCubes(depth: Int, minDepth: Int): CubesWithStatus {
    resetExtended()
    updateMoltenLiterals()
    resetLimits()
    val cubes = internal.generateCubes(depth, minDepth)
    // Upstream maps each literal with the 'externalize' lambda inside 'std::for_each' only
    // for 'MSG' output; the results are discarded, the cubes are returned unchanged.
    val externalize = { ilit: Int -> if (ilit != 0) internal.externalize(ilit) else 0 }
    val externalizeMap = { cube: IntArrayList ->
        for (k in 0 until cube.size) externalize(cube[k])
    }
    for (cube in cubes.cubes) externalizeMap(cube)

    return cubes
}

/*------------------------------------------------------------------------*/

internal fun External.freeze(elit: Int) {
    resetExtended()
    val ilit = internalize(elit)
    val eidx = vidx(elit)
    if (eidx >= frozentab.size) frozentab.resize(eidx + 1, 0)
    val ref = frozentab[eidx]
    if (ref.toUInt() < UInt.MAX_VALUE) {
        frozentab[eidx] = ref + 1
    } else {
        // external variable frozen but remains frozen forever
    }
    internal.freeze(ilit)
}

internal fun External.melt(elit: Int) {
    resetExtended()
    val ilit = internalize(elit)
    val eidx = vidx(elit)
    check(eidx < frozentab.size)
    var ref = frozentab[eidx]
    check(ref != 0)
    if (ref.toUInt() < UInt.MAX_VALUE) {
        if (--ref == 0) {
            if (observed(elit)) {
                ref++
                // external variable is observed, can not be completely molten
            } else {
                // external variable melted once and now completely melted
            }
        } else {
            // external variable melted once but remains frozen
        }
        frozentab[eidx] = ref
    } else {
        // external variable melted but remains frozen forever
    }
    internal.melt(ilit)
}

/*------------------------------------------------------------------------*/

internal fun External.checkAssignment(assignment: (Int) -> Int) {
    val a = assignment

    // First check all assigned and consistent.
    //
    for (idx in vars) {
        if (a(idx) == 0) error("unassigned variable: $idx")
        val valueIdx = a(idx)
        val valueNegIdx = a(-idx)
        if (valueIdx == idx) check(valueNegIdx == idx)
        else {
            check(valueIdx == -idx)
            check(valueNegIdx == -idx)
        }
        if (valueIdx != valueNegIdx) error("inconsistently assigned literals $idx and ${-idx}")
    }

    // Then check that all (saved) original clauses are satisfied.
    //
    var satisfied = false
    val end = original.size
    var start = 0
    var i = start
    while (i != end) {
        val lit = original[i]
        if (lit == 0) {
            if (!satisfied) {
                val sb = StringBuilder("unsatisfied clause:\n")
                for (j in start until i) sb.append(original[j]).append(' ')
                sb.append('0')
                error(sb.toString())
            }
            satisfied = false
            start = i + 1
        } else if (!satisfied && a(lit) == lit) satisfied = true
        i++
    }

    var presenceFlag: Boolean
    // Check those forgettable external clauses that are still present, but
    // only if the external propagator is still connected (otherwise solution
    // reconstruction is allowed to touch the previously observed variables so
    // there is no guarantee that the final model will satisfy these clauses.)
    // Iteration order of 'forgettable_original' (unordered_map) differs from upstream; it
    // only decides which unsatisfied clause is reported first.
    for (forgettables in forgettableOriginal) {
        if (propagator == null) break
        presenceFlag = true
        satisfied = false
        val second = forgettables.value
        for (k in 0 until second.size) {
            val lit = second[k]
            if (presenceFlag) {
                // First integer is a Boolean flag, not a literal
                if (lit == 0) {
                    // Deleted clauses can be ignored, they count as satisfied
                    satisfied = true
                    break
                }
                presenceFlag = false
                continue
            }

            if (a(lit) == lit) {
                satisfied = true
                break
            }
        }

        if (!satisfied) {
            val sb = StringBuilder("unsatisfied external forgettable clause:\n")
            for (j in 1 until second.size) sb.append(second[j]).append(' ')
            sb.append('0')
            error(sb.toString())
        }
    }
}

/*------------------------------------------------------------------------*/

internal fun External.checkAssumptionsSatisfied() {
    for (k in 0 until assumptions.size) {
        val lit = assumptions[k]
        // Not 'signed char' !!!!
        val tmp = ival(lit)
        if (tmp != lit) error("assumption $lit falsified")
        if (tmp == 0) error("assumption $lit unassigned")
    }
}

internal fun External.checkConstraintSatisfied() {
    for (k in 0 until constraint.size) {
        val lit = constraint[k]
        if (ival(lit) == lit) {
            return
        }
    }
    error("constraint not satisfied")
}

// 'DeferDeletePtr' / 'delete_checker.free ()' are dropped (garbage collected). The iteration
// order of 'forgettable_original' (unordered_map) differs from upstream; it does not matter
// here, all those clauses are added to the checker.
internal fun External.checkFailing() {
    val checker = Solver()
    checker.prefix("checker ")

    for (k in 0 until assumptions.size) {
        val lit = assumptions[k]
        if (!failed(lit))
            continue
        checker.add(lit)
        checker.add(0)
    }
    if (failedConstraint()) {
        for (k in 0 until constraint.size)
            checker.add(constraint[k])
    }

    // Add original clauses as last step, failing () and failed_constraint ()
    // might add more external clauses (due to lazy explanation)
    for (k in 0 until original.size)
        checker.add(original[k])

    // Add every forgettable external clauses
    for (forgettables in forgettableOriginal) {
        var presenceFlag = true
        val second = forgettables.value
        for (k in 0 until second.size) {
            val lit = second[k]
            if (presenceFlag) {
                // First integer is a Boolean flag, not a literal, ignore it here
                presenceFlag = false
                continue
            }
            checker.add(lit)
        }
        checker.add(0)
    }

    val res = checker.solve()
    if (res != 20)
        error("failed assumptions do not form a core")
}

/*------------------------------------------------------------------------*/

// Traversal of unit clauses is implemented here.
//
// Frozen units are treated as unit clauses while non-frozen units are treated
// as if they were already eliminated and put on the extension stack as
// witness clauses (see the long comment in upstream external.cpp).

internal fun External.traverseAllFrozenUnitsAsClauses(it: ClauseIterator): Boolean {
    if (internal.unsat) return true

    val clause = ArrayList<Int>()

    for (idx in vars) {
        if (!frozen(idx)) continue
        val tmp = fixed(idx)
        if (tmp == 0) continue
        val unit = if (tmp < 0) -idx else idx
        clause.add(unit)
        if (!it.clause(clause)) return false
        clause.clear()
    }

    return true
}

internal fun External.traverseAllNonFrozenUnitsAsWitnesses(it: WitnessIterator): Boolean {
    if (internal.unsat) return true

    val clauseAndWitness = ArrayList<Int>()
    for (idx in vars) {
        if (frozen(idx)) continue
        val tmp = fixed(idx)
        if (tmp == 0) continue
        val unit = if (tmp < 0) -idx else idx
        val ilit = e2i[idx] * (if (tmp < 0) -1 else 1)
        // heurstically add + max_var to the id to avoid reusing ids
        val id: Long = if (internal.opts.lrat != 0) internal.unitClauses(internal.vlit(ilit)) else 1L
        check(id != 0L)
        clauseAndWitness.add(unit)
        if (!it.witness(clauseAndWitness, clauseAndWitness, id + maxVar)) return false
        clauseAndWitness.clear()
    }

    return true
}

/*------------------------------------------------------------------------*/

internal fun External.copyFlags(other: External) {
    val thisFtab = internal.ftab
    val otherFtab = other.internal.ftab
    val limit = min(maxVar, other.maxVar)
    for (eidx in 1..limit) {
        val thisIlit = e2i[eidx]
        if (thisIlit == 0) continue
        val otherIlit = other.e2i[eidx]
        if (otherIlit == 0) continue
        if (!internal.active(thisIlit)) continue
        if (!other.internal.active(otherIlit)) continue
        check(thisIlit != Int.MIN_VALUE)
        check(otherIlit != Int.MIN_VALUE)
        val thisFlags = thisFtab[abs(thisIlit)]
        val otherFlags = otherFtab[abs(otherIlit)]
        thisFlags.copy(otherFlags)
    }
}

/*------------------------------------------------------------------------*/

internal fun External.exportLearnedEmptyClause() {
    val learner = checkNotNull(learner)
    if (learner.learning(0)) {
        learner.learn(0)
    } else {
        // not exporting learned empty clause
    }
}

internal fun External.exportLearnedUnitClause(ilit: Int) {
    val learner = checkNotNull(learner)
    if (learner.learning(1)) {
        val elit = internal.externalize(ilit)
        check(elit != 0)
        learner.learn(elit)
        learner.learn(0)
    } else {
        // not exporting learned unit clause
    }
}

internal fun External.exportLearnedLargeClause(clause: IntArrayList) {
    val learner = checkNotNull(learner)
    val size = clause.size
    if (learner.learning(size)) {
        for (k in 0 until clause.size) {
            val ilit = clause[k]
            val elit = internal.externalize(ilit)
            check(elit != 0)
            learner.learn(elit)
        }
        learner.learn(0)
    } else {
        // not exporting learned clause
    }
}
