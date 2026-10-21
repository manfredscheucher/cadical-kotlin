package org.bytefred.ksat.cadical.full

/*
 * profile.hpp: built-in time profiling.
 *
 * Profiling does not influence the search, so it is not ported:
 *  - 'START (P)', 'STOP (P)', 'PROFILE_ACTIVE (P)' -> dropped (PROFILE_ACTIVE is false).
 *  - 'Profile' / 'Profiles' and profile.cpp are not ported.
 * The simplifier and walk macros also switch the solver 'mode', which is solver state, so
 * these are ported without their profiling part.
 */

/** START_SIMPLIFIER (S, M) without profiling. */
internal fun Internal.startSimplifier(m: Int) {
    if (!preprocessing && !lookingahead) resetMode(Internal.SEARCH)
    setMode(Internal.SIMPLIFY)
    setMode(m)
}

/** STOP_SIMPLIFIER (S, M) without profiling. */
internal fun Internal.stopSimplifier(m: Int) {
    resetMode(m)
    resetMode(Internal.SIMPLIFY)
    if (!preprocessing && !lookingahead) setMode(Internal.SEARCH)
}

/** START_INNER_WALK () without profiling. */
internal fun Internal.startInnerWalk() {
    requireMode(Internal.SEARCH)
    check(!preprocessing)
    setMode(Internal.WALK)
}

/** STOP_INNER_WALK () without profiling. */
internal fun Internal.stopInnerWalk() {
    requireMode(Internal.SEARCH)
    check(!preprocessing)
    resetMode(Internal.WALK)
}

/** START_OUTER_WALK () without profiling. */
internal fun Internal.startOuterWalk() {
    requireMode(Internal.SEARCH)
    check(!preprocessing)
    setMode(Internal.WALK)
}

/** STOP_OUTER_WALK () without profiling. */
internal fun Internal.stopOuterWalk() {
    requireMode(Internal.SEARCH)
    check(!preprocessing)
    resetMode(Internal.WALK)
}
