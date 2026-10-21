package org.bytefred.ksat.cadical.full

import org.bytefred.ksat.cadical.IntArrayList

// STUB generated from SIGNATURES.md; to be replaced by the 1:1 translation of analyze.cpp.

internal fun Internal.bumpVariableScore(lit: Int): Unit = TODO("analyze.cpp: bumpVariableScore")
internal fun Internal.bumpVariableScoreInc(): Unit = TODO("analyze.cpp: bumpVariableScoreInc")
internal fun Internal.rescaleVariableScores(): Unit = TODO("analyze.cpp: rescaleVariableScores")
internal fun Internal.bumpQueue(idx: Int): Unit = TODO("analyze.cpp: bumpQueue")
internal fun Internal.learnEmptyClause(): Unit = TODO("analyze.cpp: learnEmptyClause")
internal fun Internal.learnUnitClause(lit: Int): Unit = TODO("analyze.cpp: learnUnitClause")
internal fun Internal.bumpVariable(lit: Int): Unit = TODO("analyze.cpp: bumpVariable")
internal fun Internal.bumpVariables(): Unit = TODO("analyze.cpp: bumpVariables")
internal fun Internal.recomputeGlue(c: Clause): Int = TODO("analyze.cpp: recomputeGlue")
internal fun Internal.bumpClause(c: Clause): Unit = TODO("analyze.cpp: bumpClause")
internal fun Internal.clearUnitAnalyzedLiterals(): Unit = TODO("analyze.cpp: clearUnitAnalyzedLiterals")
internal fun Internal.clearAnalyzedLiterals(): Unit = TODO("analyze.cpp: clearAnalyzedLiterals")
internal fun Internal.clearAnalyzedLevels(): Unit = TODO("analyze.cpp: clearAnalyzedLevels")
internal fun Internal.bumpAlsoReasonLiteral(lit: Int): Boolean = TODO("analyze.cpp: bumpAlsoReasonLiteral")
internal fun Internal.bumpAlsoReasonLiterals(lit: Int, limit: Int): Unit = TODO("analyze.cpp: bumpAlsoReasonLiterals")
internal fun Internal.bumpAlsoAllReasonLiterals(): Unit = TODO("analyze.cpp: bumpAlsoAllReasonLiterals")
internal fun Internal.analyzeLiteral(lit: Int, open: IntRef, resolventSize: IntRef, antecedentSize: IntRef): Unit = TODO("analyze.cpp: analyzeLiteral")
internal fun Internal.analyzeReason(lit: Int, reason: Clause, open: IntRef, resolventSize: IntRef, antecedentSize: IntRef): Unit = TODO("analyze.cpp: analyzeReason")
internal fun Internal.newDrivingClause(glue: Int, jump: IntRef): Clause? = TODO("analyze.cpp: newDrivingClause")
internal fun Internal.findConflictLevel(forced: IntRef): Int = TODO("analyze.cpp: findConflictLevel")
internal fun Internal.determineActualBacktrackLevel(jump: Int): Int = TODO("analyze.cpp: determineActualBacktrackLevel")
internal fun Internal.otfsStrengthenClause(c: Clause, lit: Int, newSize: Int, old: IntArrayList): Unit = TODO("analyze.cpp: otfsStrengthenClause")
internal fun Internal.otfsSubsumeClause(subsuming: Clause, subsumed: Clause): Unit = TODO("analyze.cpp: otfsSubsumeClause")
internal fun Internal.otfsFindBacktrackLevel(forced: IntRef): Int = TODO("analyze.cpp: otfsFindBacktrackLevel")
internal fun Internal.onTheFlyStrengthen(conflict: Clause, lit: Int): Clause? = TODO("analyze.cpp: onTheFlyStrengthen")
internal fun Internal.analyze(): Unit = TODO("analyze.cpp: analyze")
internal fun Internal.iterate(): Unit = TODO("analyze.cpp: iterate")
