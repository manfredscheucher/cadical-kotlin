package org.bytefred.ksat.cadical.full

import org.bytefred.ksat.cadical.IntArrayList

// STUB generated from SIGNATURES.md; to be replaced by the 1:1 translation of external_propagate.cpp.

internal fun Internal.externalPropagate(): Boolean = TODO("external_propagate.cpp: externalPropagate")
internal fun Internal.externalCheckSolution(): Boolean = TODO("external_propagate.cpp: externalCheckSolution")
internal fun Internal.addExternalClause(propagatedLit: Int = 0, noBacktrack: Boolean = false): Unit = TODO("external_propagate.cpp: addExternalClause")
internal fun Internal.learnExternalReasonClause(lit: Int, falsifiedElit: Int = 0, noBacktrack: Boolean = false): Clause = TODO("external_propagate.cpp: learnExternalReasonClause")
internal fun Internal.wrappedLearnExternalReasonClause(lit: Int): Clause = TODO("external_propagate.cpp: wrappedLearnExternalReasonClause")
internal fun Internal.explainExternalPropagations(): Unit = TODO("external_propagate.cpp: explainExternalPropagations")
internal fun Internal.explainReason(lit: Int, reason: Clause, open: IntRef): Unit = TODO("external_propagate.cpp: explainReason")
internal fun Internal.moveLiteralsToWatch(): Unit = TODO("external_propagate.cpp: moveLiteralsToWatch")
internal fun Internal.handleExternalClause(res: Clause?): Unit = TODO("external_propagate.cpp: handleExternalClause")
internal fun Internal.notifyAssignments(): Unit = TODO("external_propagate.cpp: notifyAssignments")
internal fun Internal.notifyDecision(): Unit = TODO("external_propagate.cpp: notifyDecision")
internal fun Internal.notifyBacktrack(newLevel: Int): Unit = TODO("external_propagate.cpp: notifyBacktrack")
internal fun Internal.forceBacktrack(newLevel: Int): Unit = TODO("external_propagate.cpp: forceBacktrack")
internal fun Internal.askDecision(): Int = TODO("external_propagate.cpp: askDecision")
internal fun Internal.askExternalClause(): Boolean = TODO("external_propagate.cpp: askExternalClause")
internal fun Internal.addObservedVar(ilit: Int): Unit = TODO("external_propagate.cpp: addObservedVar")
internal fun Internal.removeObservedVar(ilit: Int): Unit = TODO("external_propagate.cpp: removeObservedVar")
internal fun Internal.observed(ilit: Int): Boolean = TODO("external_propagate.cpp: observed")
internal fun Internal.isDecision(ilit: Int): Boolean = TODO("external_propagate.cpp: isDecision")
internal fun Internal.checkWatchedLiteralInvariants(): Unit = TODO("external_propagate.cpp: checkWatchedLiteralInvariants")
internal fun Internal.setTaintedLiteral(): Unit = TODO("external_propagate.cpp: setTaintedLiteral")
internal fun Internal.renotifyTrailAfterIlb(): Unit = TODO("external_propagate.cpp: renotifyTrailAfterIlb")
internal fun Internal.renotifyTrailAfterLocalSearch(): Unit = TODO("external_propagate.cpp: renotifyTrailAfterLocalSearch")
internal fun Internal.renotifyFullTrail(): Unit = TODO("external_propagate.cpp: renotifyFullTrail")
internal fun Internal.connectPropagator(): Unit = TODO("external_propagate.cpp: connectPropagator")
internal fun Internal.markGarbageExternalForgettable(id: Long): Unit = TODO("external_propagate.cpp: markGarbageExternalForgettable")
internal fun Internal.isExternalForgettable(id: Long): Boolean = TODO("external_propagate.cpp: isExternalForgettable")
internal fun Internal.getAllFixedLiterals(fixedLits: IntArrayList): Unit = TODO("external_propagate.cpp: getAllFixedLiterals")
