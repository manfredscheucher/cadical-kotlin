package org.bytefred.ksat.cadical.full

// STUB generated from SIGNATURES.md; to be replaced by the 1:1 translation of vivify.cpp.

internal fun Internal.flushVivificationSchedule(vivifier: Vivifier): Unit = TODO("vivify.cpp: flushVivificationSchedule")
internal fun Internal.considerToVivifyClause(candidate: Clause, redundantMode: Boolean): Boolean = TODO("vivify.cpp: considerToVivifyClause")
internal fun Internal.vivifyAnalyzeRedundant(vivifier: Vivifier, start: Clause, onlyBinaryReasons: BoolRef): Unit = TODO("vivify.cpp: vivifyAnalyzeRedundant")
internal fun Internal.vivifyBuildLrat(lit: Int, reason: Clause, stack: ArrayList<VivifyLratEntry>): Unit = TODO("vivify.cpp: vivifyBuildLrat")
internal fun Internal.vivifyChainForUnits(lit: Int, reason: Clause): Unit = TODO("vivify.cpp: vivifyChainForUnits")
internal fun Internal.vivifyAllDecisions(candidate: Clause, subsume: Int): Boolean = TODO("vivify.cpp: vivifyAllDecisions")
internal fun Internal.vivifyPostProcessAnalysis(candidate: Clause, subsume: Int): Unit = TODO("vivify.cpp: vivifyPostProcessAnalysis")
internal fun Internal.vivifyStrengthen(candidate: Clause): Unit = TODO("vivify.cpp: vivifyStrengthen")
internal fun Internal.vivifyAssign(lit: Int, reason: Clause?): Unit = TODO("vivify.cpp: vivifyAssign")
internal fun Internal.vivifyAssume(lit: Int): Unit = TODO("vivify.cpp: vivifyAssume")
internal fun Internal.vivifyPropagate(): Boolean = TODO("vivify.cpp: vivifyPropagate")
internal fun Internal.vivifyClause(vivifier: Vivifier, candidate: Clause): Unit = TODO("vivify.cpp: vivifyClause")
internal fun Internal.vivifyRound(redundantMode: Boolean, delta: Long): Unit = TODO("vivify.cpp: vivifyRound")
internal fun Internal.vivify(): Unit = TODO("vivify.cpp: vivify")
