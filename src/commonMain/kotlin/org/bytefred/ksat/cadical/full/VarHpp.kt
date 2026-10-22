package org.bytefred.ksat.cadical.full

/*
 * var.hpp: data associated with an assigned variable.
 *
 * Mapping: 'Clause *reason' -> 'Clause?'. Upstream leaves the members uninitialized; vectors
 * value-initialize new elements ('resize (N, T ())'), which gives zero / null as here.
 * C++ struct assignment 'a = b' copies: never alias two table slots ('compact' moves the
 * references without aliasing, see Compact.kt).
 */
internal class Var {
    var level = 0 // decision level
    var trail = 0 // trail height at assignment
    var reason: Clause? = null // implication graph edge during search
}
