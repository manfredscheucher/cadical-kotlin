package org.bytefred.ksat.cadical.full

import org.bytefred.ksat.cadical.IntArrayList

// STUB generated from SIGNATURES.md; to be replaced by the 1:1 translation of gates.cpp.

internal fun Internal.secondLiteralInBinaryClauseLrat(c: Clause, first: Int): Int = TODO("gates.cpp: secondLiteralInBinaryClauseLrat")
internal fun Internal.secondLiteralInBinaryClause(eliminator: Eliminator, c: Clause, first: Int): Int = TODO("gates.cpp: secondLiteralInBinaryClause")
internal fun Internal.markBinaryLiterals(eliminator: Eliminator, pivot: Int): Unit = TODO("gates.cpp: markBinaryLiterals")
internal fun Internal.findAndGate(eliminator: Eliminator, pivot: Int): Unit = TODO("gates.cpp: findAndGate")
internal fun Internal.findEquivalence(eliminator: Eliminator, pivot: Int): Unit = TODO("gates.cpp: findEquivalence")
internal fun Internal.getTernaryClause(d: Clause, a: IntRef, b: IntRef, c: IntRef): Boolean = TODO("gates.cpp: getTernaryClause")
internal fun Internal.matchTernaryClause(d: Clause, a: Int, b: Int, c: Int): Boolean = TODO("gates.cpp: matchTernaryClause")
internal fun Internal.findTernaryClause(a: Int, b: Int, c: Int): Clause? = TODO("gates.cpp: findTernaryClause")
internal fun Internal.getClause(c: Clause, l: IntArrayList): Boolean = TODO("gates.cpp: getClause")
internal fun Internal.isClause(c: Clause, lits: IntArrayList): Boolean = TODO("gates.cpp: isClause")
internal fun Internal.findClause(lits: IntArrayList): Clause? = TODO("gates.cpp: findClause")
internal fun Internal.findXorGate(eliminator: Eliminator, pivot: Int): Unit = TODO("gates.cpp: findXorGate")
internal fun Internal.findIfThenElse(eliminator: Eliminator, pivot: Int): Unit = TODO("gates.cpp: findIfThenElse")
internal fun Internal.findBinaryClause(first: Int, second: Int): Clause? = TODO("gates.cpp: findBinaryClause")
internal fun Internal.findGateClauses(eliminator: Eliminator, pivot: Int): Unit = TODO("gates.cpp: findGateClauses")
internal fun Internal.unmarkGateClauses(eliminator: Eliminator): Unit = TODO("gates.cpp: unmarkGateClauses")
internal fun Internal.unmarkBinaryLiterals(eliminator: Eliminator): Unit = TODO("gates.cpp: unmarkBinaryLiterals")
