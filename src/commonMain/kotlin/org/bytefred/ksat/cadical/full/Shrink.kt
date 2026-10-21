package org.bytefred.ksat.cadical.full

// STUB generated from SIGNATURES.md; to be replaced by the 1:1 translation of shrink.cpp.

internal fun Internal.shrinkAndMinimizeClause(): Unit = TODO("shrink.cpp: shrinkAndMinimizeClause")
internal fun Internal.resetShrinkable(): Unit = TODO("shrink.cpp: resetShrinkable")
internal fun Internal.markShrinkableAsRemovable(blevel: Int, minimizedStart: Int): Unit = TODO("shrink.cpp: markShrinkableAsRemovable")
internal fun Internal.shrinkLiteral(lit: Int, blevel: Int, maxTrail: Int): Int = TODO("shrink.cpp: shrinkLiteral")
internal fun Internal.shrunkenBlockUip(uip: Int, blevel: Int, rbeginBlock: IntRef /* reverse_iterator */, rendBlock: IntRef /* reverse_iterator */, minimizedStart: Int, uip0: Int): Int = TODO("shrink.cpp: shrunkenBlockUip")
internal fun Internal.shrunkenBlockNoUip(rbeginBlock: Int /* reverse_iterator */, rendBlock: Int /* reverse_iterator */, blockMinimized: IntRef, uip0: Int): Unit = TODO("shrink.cpp: shrunkenBlockNoUip")
internal fun Internal.pushLiteralsOfBlock(rbeginBlock: Int /* reverse_iterator */, rendBlock: Int /* reverse_iterator */, blevel: Int, maxTrail: Int): Unit = TODO("shrink.cpp: pushLiteralsOfBlock")
internal fun Internal.shrinkNext(blevel: Int, open: IntRef, maxTrail: IntRef): Int = TODO("shrink.cpp: shrinkNext")
internal fun Internal.minimizeAndShrinkBlock(rbeginBlock: IntRef /* reverse_iterator */, totalShrunken: IntRef, totalMinimized: IntRef, uip0: Int): Int /* reverse_iterator */ = TODO("shrink.cpp: minimizeAndShrinkBlock")
internal fun Internal.shrinkBlock(rbeginLits: IntRef /* reverse_iterator */, rendBlock: IntRef /* reverse_iterator */, blevel: Int, open: IntRef, blockMinimized: IntRef, uip0: Int, maxTrail: Int): Int = TODO("shrink.cpp: shrinkBlock")
internal fun Internal.shrinkAlongReason(uip: Int, blevel: Int, resolveLargeClauses: Boolean, failedPtr: BoolRef, maxTrail: Int): Int = TODO("shrink.cpp: shrinkAlongReason")
