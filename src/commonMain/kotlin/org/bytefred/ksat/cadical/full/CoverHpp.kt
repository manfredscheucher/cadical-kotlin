package org.bytefred.ksat.cadical.full

/*
 * cover.hpp: only the 'COVER' macro, a coverage goal for testing (unrelated to cover.cpp).
 * Reaching a goal aborts upstream, also with NDEBUG, so it is loud here too.
 */
internal fun cover(cond: Boolean) {
    if (!cond) return
    error("Coverage goal reached.")
}
