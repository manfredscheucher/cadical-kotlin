package org.bytefred.ksat.cadical.full

// STUB generated from SIGNATURES.md; to be replaced by the 1:1 translation of elim.cpp.

internal fun Internal.eliminating(): Boolean = TODO("elim.cpp: eliminating")
internal fun Internal.computeElimScore(lit: Int): Double = TODO("elim.cpp: computeElimScore")
internal fun Internal.resolveClauses(eliminator: Eliminator, c: Clause, pivot: Int, d: Clause, propagateEagerly: Boolean): Boolean = TODO("elim.cpp: resolveClauses")
internal fun Internal.markEliminatedClausesAsGarbage(eliminator: Eliminator, pivot: Int, deletedBinaryClause: BoolRef): Unit = TODO("elim.cpp: markEliminatedClausesAsGarbage")
internal fun Internal.elimResolventsAreBounded(eliminator: Eliminator, pivot: Int): Boolean = TODO("elim.cpp: elimResolventsAreBounded")
internal fun Internal.elimUpdateRemovedLit(eliminator: Eliminator, lit: Int): Unit = TODO("elim.cpp: elimUpdateRemovedLit")
internal fun Internal.elimUpdateRemovedClause(eliminator: Eliminator, c: Clause, except: Int = 0): Unit = TODO("elim.cpp: elimUpdateRemovedClause")
internal fun Internal.elimUpdateAddedClause(eliminator: Eliminator, c: Clause): Unit = TODO("elim.cpp: elimUpdateAddedClause")
internal fun Internal.elimAddResolvents(eliminator: Eliminator, pivot: Int): Unit = TODO("elim.cpp: elimAddResolvents")
internal fun Internal.elimPropagate(eliminator: Eliminator, unit: Int): Unit = TODO("elim.cpp: elimPropagate")
internal fun Internal.elimOnTheFlySelfSubsumption(eliminator: Eliminator, c: Clause, pivot: Int): Unit = TODO("elim.cpp: elimOnTheFlySelfSubsumption")
internal fun Internal.tryToEliminateVariable(eliminator: Eliminator, pivot: Int, deletedBinaryClause: BoolRef): Unit = TODO("elim.cpp: tryToEliminateVariable")
internal fun Internal.increaseEliminationBound(): Unit = TODO("elim.cpp: increaseEliminationBound")
internal fun Internal.elimRound(completed: BoolRef, deletedBinaryClause: BoolRef): Int = TODO("elim.cpp: elimRound")
internal fun Internal.elim(updateLimits: Boolean = true): Unit = TODO("elim.cpp: elim")
