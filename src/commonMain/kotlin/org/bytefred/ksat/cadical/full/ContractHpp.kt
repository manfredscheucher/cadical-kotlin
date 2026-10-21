package org.bytefred.ksat.cadical.full

/*
 * contract.hpp: API contract checks of the 'Solver' facade (solver.cpp).
 *
 * Mapping: 'CONTRACT_VIOLATED' prints and aborts upstream -> throws [IllegalStateException]
 * via 'error'. 'REQUIRE (COND, ...)' -> [contractRequire] (the message is built lazily).
 * 'REQUIRE_NON_ZERO_THIS' / 'REQUIRE_INITIALIZED' cannot fail in Kotlin (non-null receiver)
 * and are dropped. The state based shortcuts ('REQUIRE_VALID_STATE', ...) belong to the
 * 'Solver' class and are ported with solver.cpp.
 */
internal inline fun contractRequire(cond: Boolean, function: String, message: () -> String) {
    if (cond) return
    error("invalid API usage of '$function': ${message()}")
}
