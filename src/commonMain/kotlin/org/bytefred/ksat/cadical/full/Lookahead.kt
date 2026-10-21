package org.bytefred.ksat.cadical.full

import kotlin.math.abs
import org.bytefred.ksat.cadical.IntArrayList

/*
 * lookahead.cpp
 *
 * Mapping:
 *  - 'struct literal_occ' -> [LiteralOcc] (reference semantics are fine: 'std::sort' only
 *    permutes the elements, see StdSort.kt); its 'operator <' -> [literalOccLess].
 *  - 'std::vector<int>' cubes -> IntArrayList; C++ copies ('std::vector<int> cube1 {x}')
 *    -> fresh IntArrayList filled with 'assign'; 'std::move' -> the same object (the moved
 *    from vector is never read again).
 *  - 'probe_negated_noccs_rank' is a second, identical static struct in this file; it is
 *    [LookaheadProbeNegatedNoccsRank] here (Probe.kt has its own private copy).
 *  - MSG / PHASE / LOG / START / STOP are dropped (PORTING.md), except that the argument
 *    'terminating_asked ()' of one MSG has a side effect (it calls the terminator) and is
 *    kept: without QUIET upstream always evaluates MSG arguments.
 *  - 'int res' declared again inside the cube loop (shadowing the outer 'res') -> 'innerRes'.
 */

private class LiteralOcc {
    var lit = 0
    var count = 0
}

private val literalOccLess = Less<LiteralOcc> { a, b ->
    (a.count > b.count) || (a.count == b.count && a.lit < b.lit)
}

internal fun Internal.lookaheadPopulateLocc(): IntArrayList {
    val loccs = ArrayList<LiteralOcc>(maxVar + 1)
    loccs.resize(maxVar + 1) { LiteralOcc() }
    for (lit in 0 until loccs.size) {
        loccs[lit].lit = lit
    }
    for (c in clauses) {
        if (!c.redundant) {
            for (k in 0 until c.size) {
                val lit = c.literals[k]
                if (active(lit)) ++loccs[abs(lit)].count
            }
        }
    }
    cxxSort(loccs, literalOccLess)
    val loccMap = IntArrayList()
    for (locc in loccs) loccMap.add(locc.lit)
    return loccMap
}

internal fun Internal.lookaheadLocc(loccs: IntArrayList): Int {
    for (k in 0 until loccs.size) {
        val lit = loccs[k]
        if (active(abs(lit)) && !assumed(lit) && !assumed(-lit) && value(lit) == 0) return lit
    }
    return 0
}

// This calculates the literal that appears the most often reusing the
// available datastructures and iterating over the clause set. This is too
// slow to be called iteratively. A faster (but inexact) version is
// lookahead_populate_loc and lookahead_loc.
internal fun Internal.mostOccurringLiteral(): Int {
    initNoccs()
    for (c in clauses) {
        if (!c.redundant) {
            for (k in 0 until c.size) {
                val lit = c.literals[k]
                if (active(lit)) ntab[vlit(lit)]++
            }
        }
    }
    var maxNoccs = 0L
    var res = 0

    if (unsat) return Int.MIN_VALUE

    propagate()
    for (idx in 1..maxVar) {
        if (!active(idx) || assumed(idx) || assumed(-idx) || value(idx) != 0) continue
        var sign = -1
        while (sign <= 1) {
            val lit = sign * idx
            sign += 2
            if (!active(lit)) continue
            val tmp = noccs(lit)
            if (tmp <= maxNoccs) continue
            maxNoccs = tmp
            res = lit
        }
    }
    resetNoccs()
    return res
}

// We probe on literals first, which occur more often negated and thus we
// sort the 'probes' stack in such a way that literals which occur negated
// less frequently come first.  Probes are taken from the back of the stack.

// 'Type' is 'size_t' (64 bits, the default of IntRank).
private class LookaheadProbeNegatedNoccsRank(private val internal: Internal) : IntRank {
    override fun rank(a: Int): Long = internal.noccs(-a)
}

// Follow the ideas in 'generate_probes' but flush non root probes and
// reorder remaining probes.

internal fun Internal.lookaheadFlushProbes() {

    check(!probes.isEmpty()) { "lookahead_flush_probes: probes" }

    initNoccs()
    val a = IntRef()
    val b = IntRef()
    for (c in clauses) {
        if (!isBinaryClause(c, a, b)) continue
        ntab[vlit(a.value)]++
        ntab[vlit(b.value)]++
    }

    val eop = probes.size
    var j = 0
    var i = j
    while (i != eop) {
        var lit = probes[i]
        i++
        if (!active(lit)) continue
        val havePosBinOccs = noccs(lit) > 0
        val haveNegBinOccs = noccs(-lit) > 0
        if (havePosBinOccs == haveNegBinOccs) continue
        if (havePosBinOccs) lit = -lit
        check(noccs(lit) == 0L) { "lookahead_flush_probes: noccs (lit)" }
        check(noccs(-lit) > 0) { "lookahead_flush_probes: noccs (-lit)" }
        if (propfixed(lit).toLong() >= stats.all.fixed) continue
        probes[j++] = lit
    }
    val remain = j
    probes.resize(remain)

    rsort(probes, LookaheadProbeNegatedNoccsRank(this))

    resetNoccs()
}

internal fun Internal.lookaheadGenerateProbes() {

    check(probes.isEmpty()) { "lookahead_generate_probes: probes" }

    // First determine all the literals which occur in binary clauses. It is
    // way faster to go over the clauses once, instead of walking the watch
    // lists for each literal.
    //
    initNoccs()
    val a = IntRef()
    val b = IntRef()
    for (c in clauses) {
        if (!isBinaryClause(c, a, b)) continue
        ntab[vlit(a.value)]++
        ntab[vlit(b.value)]++
    }

    for (idx in 1..maxVar) {

        // Then focus on roots of the binary implication graph, which are
        // literals occurring negatively in a binary clause, but not positively.
        // If neither 'idx' nor '-idx' is a root it makes less sense to probe
        // this variable.

        // This argument requires that equivalent literal substitution through
        // 'decompose' is performed, because otherwise there might be 'cyclic
        // roots' which are not tried, i.e., -1 2 0, 1 -2 0, 1 2 3 0, 1 2 -3 0.

        val havePosBinOccs = noccs(idx) > 0
        val haveNegBinOccs = noccs(-idx) > 0

        // if (have_pos_bin_occs == have_neg_bin_occs) continue;

        if (havePosBinOccs) {
            val probe = -idx

            // See the discussion where 'propfixed' is used below.
            //
            if (propfixed(probe).toLong() >= stats.all.fixed) continue

            probes.add(probe)
        }

        if (haveNegBinOccs) {
            val probe = idx

            // See the discussion where 'propfixed' is used below.
            //
            if (propfixed(probe).toLong() >= stats.all.fixed) continue

            probes.add(probe)
        }
    }

    rsort(probes, LookaheadProbeNegatedNoccsRank(this))

    resetNoccs()
}

internal fun Internal.lookaheadNextProbe(): Int {

    var generated = 0

    while (true) {

        if (probes.isEmpty()) {
            if (generated++ != 0) return 0
            lookaheadGenerateProbes()
        }

        while (!probes.isEmpty()) {

            val probe = probes.back()
            probes.removeLast()

            // Eliminated or assigned.
            //
            if (!active(probe) || assumed(probe) || assumed(-probe)) continue

            // There is now new unit since the last time we propagated this probe,
            // thus we propagated it before without obtaining a conflict and
            // nothing changed since then.  Thus there is no need to propagate it
            // again.  This observation was independently made by Partik Simons
            // et.al. in the context of implementing 'smodels' (see for instance
            // Alg. 4 in his JAIR article from 2002) and it has also been
            // contributed to the thesis work of Yacine Boufkhad.
            //
            if (propfixed(probe).toLong() >= stats.all.fixed) continue

            return probe
        }
    }
}

// Non-static free function upstream ('bool non_tautological_cube (std::vector<int> cube)'),
// only used in this file; the argument is taken by value (sorted copy).
private fun nonTautologicalCube(cubeArg: IntArrayList): Boolean {
    val cube = IntArrayList()
    cube.assign(cubeArg)
    cxxSort(cube, clauseLitLessThan)

    var i = 0
    var j = 1
    while (j < cube.size) {
        if (cube[i] == cube[j]) return false
        else if (cube[i] == -cube[j]) return false
        else if (cube[i] == 0) return false
        ++i
        ++j
    }

    return true
}

internal fun Internal.terminatingAsked(): Boolean {

    val terminator = external!!.terminator
    if (terminator != null && terminator.terminate()) {
        return true
    }

    if (terminationForced) {
        return true
    }
    return false
}

// We run probing on all literals with some differences:
//
// * no limit on the number of propagations. We rely on terminating to
// stop()
// * we run only one round
//
// The run can be expensive, so we actually first run the cheaper
// occurrence version and only then run lookahead.
//
internal fun Internal.lookaheadProbing(): Int {

    if (active() == 0) return 0

    terminationForced = false

    // 'old_failed', 'old_probed' and 'old_hbrs' only feed messages (dropped).

    if (unsat) return Int.MIN_VALUE
    if (level != 0) backtrack()
    if (!propagate()) {
        learnEmptyClause()
        return Int.MIN_VALUE
    }

    if (terminatingAsked()) return mostOccurringLiteral()

    decompose()

    if (ternary()) // If we derived a binary clause
        decompose() // then start another round of ELS.

    // Remove duplicated binary clauses and perform in essence hyper unary
    // resolution, i.e., derive the unit '2' from '1 2' and '-1 2'.
    //
    markDuplicatedBinaryClausesAsGarbage()

    lim.conflicts = -1

    if (!probes.isEmpty()) lookaheadFlushProbes()

    // We reset 'propfixed' since there was at least another conflict thus
    // a new learned clause, which might produce new propagations (and hyper
    // binary resolvents).  During 'generate_probes' we keep the old value.
    //
    for (idx in 1..maxVar) {
        ptab[vlit(-idx)] = -1
        ptab[vlit(idx)] = -1
    }

    check(unsat || propagated == trail.size) { "lookahead_probing: propagated" }
    propagated2 = trail.size
    propagated = propagated2

    var res = mostOccurringLiteral()
    var maxHbrs = -1

    setMode(Internal.PROBE)

    // MSG ("unsat = %d, terminating_asked () = %d ", unsat, terminating_asked ()):
    // the message is dropped, its argument calls the terminator.
    terminatingAsked()
    initProbehbrLrat()
    while (true) {
        if (unsat) break
        if (terminatingAsked()) break
        val probe = lookaheadNextProbe()
        if (probe == 0) break
        stats.probed++
        val hbrs: Int

        probeAssignDecision(probe)
        if (probePropagate()) {
            hbrs = trail.size
            backtrack()
        } else {
            hbrs = 0
            failedLiteral(probe)
        }
        cleanProbehbrLrat()
        if (maxHbrs < hbrs || (maxHbrs == hbrs && bumped(probe) > bumped(res))) {
            res = probe
            maxHbrs = hbrs
        }
    }

    resetMode(Internal.PROBE)

    if (unsat) {
        res = Int.MIN_VALUE
    } else if (propagated < trail.size) {
        if (!propagate()) {
            learnEmptyClause()
            res = Int.MIN_VALUE
        } else {
            sortWatches()
        }
    }

    return res
}

internal fun Internal.generateCubes(depth: Int, minDepth: Int): CubesWithStatus {
    if (active() == 0 || depth == 0) {
        val cubes = CubesWithStatus()
        cubes.status = 0
        cubes.cubes.add(IntArrayList())
        return cubes
    }

    lookingahead = true

    // presimplify required due to assumptions

    terminationForced = false
    var res = alreadySolved()
    if (res == 0) res = restoreClauses()
    if (unsat) res = 10
    if (res != 0) res = solve(true)
    if (res != 0) {
        val cubes = CubesWithStatus()
        cubes.status = res
        lookingahead = false
        return cubes
    }

    resetLimits()

    check(ntab.isEmpty()) { "generate_cubes: ntab" }
    val currentAssumptions = IntArrayList()
    currentAssumptions.assign(assumptions)
    var cubes = ArrayList<IntArrayList>()
    val firstCube = IntArrayList()
    firstCube.assign(assumptions)
    cubes.add(firstCube)
    val loccs = lookaheadPopulateLocc()
    check(ntab.isEmpty()) { "generate_cubes: ntab after populate" }

    for (i in 0 until depth) {
        val cubes2 = cubes // std::move
        cubes = ArrayList()

        for (j in 0 until cubes2.size) {
            check(ntab.isEmpty()) { "generate_cubes: ntab in loop" }
            check(!unsat) { "generate_cubes: unsat" }
            resetAssumptions()
            val cube = cubes2[j]
            for (k in 0 until cube.size) assume(cube[k])
            restoreClauses()
            propagate()
            // preprocess_round(0); //uncomment maybe

            if (unsat) {
                unsat = false
                continue
            }

            val innerRes = if (terminatingAsked()) lookaheadLocc(loccs) else lookaheadProbing()
            if (unsat) {
                unsat = false
                continue
            }

            if (innerRes == 0) {
                cubes.add(cubes2[j])
                continue
            }

            check(innerRes != 0) { "generate_cubes: res" }
            val cube1 = IntArrayList()
            cube1.assign(cubes2[j])
            cube1.add(innerRes)
            val cube2 = cubes2[j] // std::move
            cube2.add(-innerRes)
            cubes.add(cube1)
            cubes.add(cube2)
        }

        if (terminatingAsked() && i >= minDepth) break
    }

    // 'assert (std::for_each (..., [] (cube) { return non_tautological_cube (cube); }))'
    // is vacuous upstream: 'for_each' returns the (captureless) lambda, which converts to a
    // non-null function pointer. The calls have no side effects.
    for (cube in cubes) nonTautologicalCube(cube)
    resetAssumptions()

    for (k in 0 until currentAssumptions.size) assume(currentAssumptions[k])

    lookingahead = false

    if (unsat) {
        val unsatCubes = CubesWithStatus()
        unsatCubes.status = 20
        return unsatCubes
    }

    val rcubes = CubesWithStatus()
    rcubes.status = 0
    rcubes.cubes.addAll(cubes)

    return rcubes
}
