package org.bytefred.ksat.cadical.full

import org.bytefred.ksat.cadical.IntArrayList

// STUB generated from SIGNATURES.md; to be replaced by the 1:1 translation of extend.cpp.

internal fun External.pushZeroOnExtensionStack(): Unit = TODO("extend.cpp: pushZeroOnExtensionStack")
internal fun External.pushClauseLiteralOnExtensionStack(ilit: Int): Unit = TODO("extend.cpp: pushClauseLiteralOnExtensionStack")
internal fun External.pushWitnessLiteralOnExtensionStack(ilit: Int): Unit = TODO("extend.cpp: pushWitnessLiteralOnExtensionStack")
internal fun External.pushClauseOnExtensionStack(c: Clause): Unit = TODO("extend.cpp: pushClauseOnExtensionStack")
internal fun External.pushClauseOnExtensionStack(c: Clause, witness: Int): Unit = TODO("extend.cpp: pushClauseOnExtensionStack")
internal fun External.pushBinaryClauseOnExtensionStack(id: Long, witness: Int, other: Int): Unit = TODO("extend.cpp: pushBinaryClauseOnExtensionStack")
internal fun External.extend(): Unit = TODO("extend.cpp: extend")
internal fun External.concludeSat(): Unit = TODO("extend.cpp: concludeSat")
internal fun External.pushExternalClauseAndWitnessOnExtensionStack(clause: IntArrayList, witness: IntArrayList, id: Long): Unit = TODO("extend.cpp: pushExternalClauseAndWitnessOnExtensionStack")
internal fun External.pushIdOnExtensionStack(id: Long): Unit = TODO("extend.cpp: pushIdOnExtensionStack")
internal fun External.traverseWitnessesBackward(it: WitnessIterator): Boolean = TODO("extend.cpp: traverseWitnessesBackward")
internal fun External.traverseWitnessesForward(it: WitnessIterator): Boolean = TODO("extend.cpp: traverseWitnessesForward")
