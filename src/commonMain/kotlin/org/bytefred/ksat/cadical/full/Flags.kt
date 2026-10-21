package org.bytefred.ksat.cadical.full

/*
 * flags.cpp: variable status transitions (fixed, eliminated, pure, substituted, active,
 * reactivated) with their statistics.
 */

internal fun Internal.markFixed(lit: Int) {
    val fixedListener = external!!.fixedListener
    if (fixedListener != null) {
        val elit = externalize(lit)
        check(elit != 0)
        fixedListener.notifyFixedAssignment(elit)
    }
    val f = flags(lit)
    check(f.status == Flags.ACTIVE) { "mark_fixed of inactive variable" }
    f.status = Flags.FIXED
    stats.all.fixed++
    stats.now.fixed++
    stats.inactive++
    check(stats.active != 0L)
    stats.active--
    check(!active(lit))
    check(f.fixed())

    if (externalProp && privateSteps) {
        // If pre/inprocessing found a fixed assignment, we want the propagator
        // to know about it.
        // But at that point it is not guaranteed to be already on the trail, so
        // notification will happen only later.
        check(level == 0)
    }
}

internal fun Internal.markEliminated(lit: Int) {
    val f = flags(lit)
    check(f.status == Flags.ACTIVE) { "mark_eliminated of inactive variable" }
    f.status = Flags.ELIMINATED
    stats.all.eliminated++
    stats.now.eliminated++
    stats.inactive++
    check(stats.active != 0L)
    stats.active--
    check(!active(lit))
    check(f.eliminated())
}

internal fun Internal.markPure(lit: Int) {
    val f = flags(lit)
    check(f.status == Flags.ACTIVE) { "mark_pure of inactive variable" }
    f.status = Flags.PURE
    stats.all.pure++
    stats.now.pure++
    stats.inactive++
    check(stats.active != 0L)
    stats.active--
    check(!active(lit))
    check(f.pure())
}

internal fun Internal.markSubstituted(lit: Int) {
    val f = flags(lit)
    check(f.status == Flags.ACTIVE) { "mark_substituted of inactive variable" }
    f.status = Flags.SUBSTITUTED
    stats.all.substituted++
    stats.now.substituted++
    stats.inactive++
    check(stats.active != 0L)
    stats.active--
    check(!active(lit))
    check(f.substituted())
}

internal fun Internal.markActive(lit: Int) {
    val f = flags(lit)
    check(f.status == Flags.UNUSED) { "mark_active of used variable" }
    f.status = Flags.ACTIVE
    check(stats.inactive != 0L)
    stats.inactive--
    check(stats.unused != 0L)
    stats.unused--
    stats.active++
    check(active(lit))
}

internal fun Internal.reactivate(lit: Int) {
    check(!active(lit)) { "reactivate of active variable" }
    val f = flags(lit)
    check(f.status != Flags.FIXED)
    check(f.status != Flags.UNUSED)
    when (f.status) {
        Flags.SUBSTITUTED -> {
            check(stats.now.substituted > 0)
            stats.now.substituted--
        }
        Flags.PURE -> {
            check(stats.now.pure > 0)
            stats.now.pure--
        }
        else -> { // 'default:' falls into 'case Flags::ELIMINATED:'
            check(f.status == Flags.ELIMINATED)
            check(stats.now.eliminated > 0)
            stats.now.eliminated--
        }
    }
    f.status = Flags.ACTIVE
    check(active(lit))
    stats.reactivated++
    check(stats.inactive > 0)
    stats.inactive--
    stats.active++
}
