package org.bytefred.ksat.cadical.full

/*
 * rephase.cpp: resetting the saved phases in arithmetically increasing conflict intervals.
 *
 * Mapping notes: PHASE messages and 'report' are dropped (see PORTING.md). 'size_t count =
 * lim.rephased[stable]++' -> Long. The shadow trace prints 'START/END rephase' around
 * [rephase] and 'REPHASE <type>' before the new limit is computed (trace.patch).
 */

/*------------------------------------------------------------------------*/

// We experimented with resetting and reinitializing the saved phase with
// many solvers. Actually RSAT had already such a scheme.  Our newest
// version seems to be quite beneficial for satisfiable instances.  In an
// arithmetic increasing interval in the number of conflicts we either use
// the original phase (set by the option 'phase'), its inverted value, flip
// the current phase, pick random phases, then pick the best since the last
// time a best phase was picked and finally also use local search to find
// phases which minimize the number of falsified clauses.  During
// stabilization (see 'stabilizing' in 'restart.cpp' when 'stable' is true)
// we execute a different rephasing schedule.  The same applies if local
// search is disabled.

/*------------------------------------------------------------------------*/

internal fun Internal.rephasing(): Boolean {
    if (opts.rephase == 0) return false
    if (opts.forcephase != 0) return false
    return stats.conflicts > lim.rephase
}

/*------------------------------------------------------------------------*/

// Pick the original default phase.

internal fun Internal.rephaseOriginal(): Char {
    stats.rephased.original++
    val v: Byte = if (opts.phase != 0) 1 else -1 // original = initial
    for (idx in 1..maxVar) phases.saved[idx] = v
    return 'O'
}

// Pick the inverted original default phase.

internal fun Internal.rephaseInverted(): Char {
    stats.rephased.inverted++
    val v: Byte = if (opts.phase != 0) -1 else 1 // original = -initial
    for (idx in 1..maxVar) phases.saved[idx] = v
    return 'I'
}

// Flip the current phase.

internal fun Internal.rephaseFlipping(): Char {
    stats.rephased.flipped++
    for (idx in 1..maxVar) phases.saved[idx] = (phases.saved[idx] * -1).toByte()
    return 'F'
}

// Complete random picking of phases.

internal fun Internal.rephaseRandom(): Char {
    stats.rephased.random++
    val random = Random(opts.seed.toULong()) // global seed
    random += stats.rephased.random.toULong() // different every time
    for (idx in 1..maxVar) phases.saved[idx] = if (random.generateBool()) -1 else 1
    return '#'
}

// Best phases are those saved at the largest trail height without conflict.
// See code and comments in 'update_target_and_best' in 'backtrack.cpp'

internal fun Internal.rephaseBest(): Char {
    stats.rephased.best++
    var v: Byte
    for (idx in 1..maxVar) {
        v = phases.best[idx]
        if (v.toInt() != 0) phases.saved[idx] = v
    }
    return 'B'
}

// Trigger local search 'walk' in 'walk.cpp'.

internal fun Internal.rephaseWalk(): Char {
    stats.rephased.walk++
    walk()
    return 'W'
}

/*------------------------------------------------------------------------*/

internal fun Internal.rephase(): Unit = tracePhase("rephase") {

    stats.rephased.total++

    // Report current 'target' and 'best' and then set 'rephased' below, which
    // will trigger reporting the new 'target' and 'best' after updating it in
    // the next 'update_target_and_best' called from the next 'backtrack'.
    //
    // report ('~', 1) dropped (message output).

    backtrack()
    clearPhases(phases.target)
    targetAssigned = 0

    val count = lim.rephased[if (stable) 1 else 0]++
    val single: Boolean
    val type: Char

    if (opts.stabilize != 0 && opts.stabilizeonly != 0) {
        single = true
    } else {
        single = opts.stabilize == 0
    }

    if (single && opts.walk == 0) {
        // (inverted,best,flipping,best,random,best,original,best)^\omega
        type = when (count % 8) {
            0L -> rephaseInverted()
            1L -> rephaseBest()
            2L -> rephaseFlipping()
            3L -> rephaseBest()
            4L -> rephaseRandom()
            5L -> rephaseBest()
            6L -> rephaseOriginal()
            7L -> rephaseBest()
            else -> '\u0000'
        }
    } else if (single && opts.walk != 0) {
        // (inverted,best,walk,
        //  flipping,best,walk,
        //    random,best,walk,
        //  original,best,walk)^\omega
        type = when (count % 12) {
            0L -> rephaseInverted()
            1L -> rephaseBest()
            2L -> rephaseWalk()
            3L -> rephaseFlipping()
            4L -> rephaseBest()
            5L -> rephaseWalk()
            6L -> rephaseRandom()
            7L -> rephaseBest()
            8L -> rephaseWalk()
            9L -> rephaseOriginal()
            10L -> rephaseBest()
            11L -> rephaseWalk()
            else -> '\u0000'
        }
    } else if (stable && opts.walk == 0) {
        // original,inverted,(best,original,best,inverted)^\omega
        if (count == 0L) {
            type = rephaseOriginal()
        } else if (count == 1L) {
            type = rephaseInverted()
        } else {
            type = when ((count - 2) % 4) {
                0L -> rephaseBest()
                1L -> rephaseOriginal()
                2L -> rephaseBest()
                3L -> rephaseInverted()
                else -> '\u0000'
            }
        }
    } else if (stable && opts.walk != 0) {
        // original,inverted,(best,walk,original,best,walk,inverted)^\omega
        if (count == 0L) {
            type = rephaseOriginal()
        } else if (count == 1L) {
            type = rephaseInverted()
        } else {
            type = when ((count - 2) % 6) {
                0L -> rephaseBest()
                1L -> rephaseWalk()
                2L -> rephaseOriginal()
                3L -> rephaseBest()
                4L -> rephaseWalk()
                5L -> rephaseInverted()
                else -> '\u0000'
            }
        }
    } else if (!stable && (opts.walk == 0 || opts.walknonstable == 0)) {
        // flipping,(random,best,flipping,best)^\omega
        if (count == 0L) {
            type = rephaseFlipping()
        } else {
            type = when ((count - 1) % 4) {
                0L -> rephaseRandom()
                1L -> rephaseBest()
                2L -> rephaseFlipping()
                3L -> rephaseBest()
                else -> '\u0000'
            }
        }
    } else {
        check(!stable && opts.walk != 0 && opts.walknonstable != 0) { "rephase: unexpected schedule" }
        // flipping,(random,best,walk,flipping,best,walk)^\omega
        if (count == 0L) {
            type = rephaseFlipping()
        } else {
            type = when ((count - 1) % 6) {
                0L -> rephaseRandom()
                1L -> rephaseBest()
                2L -> rephaseWalk()
                3L -> rephaseFlipping()
                4L -> rephaseBest()
                5L -> rephaseWalk()
                else -> '\u0000'
            }
        }
    }
    check(type != '\u0000') { "rephase: no rephase type" }

    trace?.line("REPHASE $type")
    val delta = opts.rephaseint.toLong() * (stats.rephased.total + 1)
    lim.rephase = stats.conflicts + delta

    // This will trigger to report the effect of this new set of phases at the
    // 'backtrack' (actually 'update_target_and_best') after the next
    // conflict, as well as resetting 'best_assigned' then to allow to compute
    // a new "best" assignment at that point.
    //
    last.rephase.conflicts = stats.conflicts
    rephased = type

    if (stable) shuffleScores()
    else shuffleQueue()
}
