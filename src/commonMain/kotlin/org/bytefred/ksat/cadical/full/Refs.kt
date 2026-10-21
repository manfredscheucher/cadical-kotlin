package org.bytefred.ksat.cadical.full

/*
 * Holders for C++ reference parameters of primitive types (no upstream file).
 *
 * 'void f (int &open)' -> 'fun Internal.f (open: IntRef)'; the caller passes a holder and
 * reads 'open.value' afterwards, the callee reads and writes 'open.value'. Used for exactly
 * the parameters SIGNATURES.md lists as IntRef / LongRef / BoolRef.
 */
internal class IntRef(var value: Int = 0)

internal class LongRef(var value: Long = 0)

internal class BoolRef(var value: Boolean = false)
