package org.bytefred.ksat.cadical.full

import org.bytefred.ksat.cadical.IntArrayList

/*
 * shrink.cpp: shrinking (and minimizing) the first UIP clause block by block.
 *
 * Mapping notes:
 *  - 'std::vector<int>::reverse_iterator' into 'clause' -> the index of the element it points
 *    to (PORTING.md): 'clause.rbegin ()' = 'clause.size - 1', 'clause.rend ()' = -1,
 *    'clause.rend () - 1' = 0, '++p' = 'p--', '*p' = 'clause[p]', 'p + 1' = 'p - 1',
 *    'a < b' on reverse iterators = 'a > b' on indices.
 *  - 'unsigned' counters ('open', 'max_trail', 'block_minimized', ...) -> Int (they are
 *    bounded by the clause / trail size).
 *  - 'Level::seen.trail' / 'seen.count' -> [Level.seenTrail] / [Level.seenCount].
 */

internal fun Internal.resetShrinkable() {
    for (k in 0 until shrinkable.size) {
        val lit = shrinkable[k]
        // LOG: resetting lit
        val f = flags(lit)
        check(f.shrinkable)
        f.shrinkable = false
    }
    // LOG: resetting shrinkable variables
}

internal fun Internal.markShrinkableAsRemovable(blevel: Int, minimizedStart: Int) {
    // '#ifndef NDEBUG'
    var minimizedStart = minimizedStart
    while (minimizedStart < minimized.size) {
        val lit = minimized[minimizedStart]
        val f = flags(lit)
        val v = variable(lit)
        if (v.level == blevel) {
            check(!f.poison)
        }
        ++minimizedStart
    }

    for (k in 0 until shrinkable.size) {
        val lit = shrinkable[k]
        val f = flags(lit)
        check(f.shrinkable)
        check(!f.poison)
        f.shrinkable = false
        if (f.removable) continue
        f.removable = true
        minimized.add(lit)
    }
    // LOG: resetting shrinkable variables, marked removable variables
}

internal fun Internal.shrinkLiteral(lit: Int, blevel: Int, maxTrail: Int): Int {
    check(value(lit) < 0)

    val f = flags(lit)
    val v = variable(lit)
    check(v.level <= blevel)

    if (v.level == 0) {
        // LOG: skipping root level assigned
        return 0
    }

    if (v.reason === externalReason) {
        check(opts.exteagerreasons == 0)
        v.reason = learnExternalReasonClause(-lit, 0, true)
        if (v.reason == null) {
            check(v.level == 0)
            return 0
        }
    }
    check(v.reason !== externalReason)
    if (f.shrinkable) {
        // LOG: skipping already shrinkable literal
        return 0
    }

    if (v.level < blevel) {
        if (f.removable) {
            // LOG: skipping removable thus shrinkable
            return 0
        }
        val alwaysMinimizeOnLowerBlevel = (opts.shrink > 2)
        if (alwaysMinimizeOnLowerBlevel && minimizeLiteral(-lit, 1)) {
            // LOG: minimized thus shrinkable
            return 0
        }
        // LOG: literal on lower blevel not removable/shrinkable
        return -1
    }

    // LOG: marking as shrinkable
    f.shrinkable = true
    f.poison = false
    shrinkable.add(lit)
    if (opts.shrinkreap != 0) {
        check(maxTrail < trail.size)
        val dist = maxTrail - v.trail
        reap.push(dist)
    }
    return 1
}

internal fun Internal.shrunkenBlockUip(
    uip: Int,
    blevel: Int,
    rbeginBlock: IntRef, /* reverse_iterator */
    rendBlock: IntRef, /* reverse_iterator */
    minimizedStart: Int,
    uip0: Int,
): Int {
    check(clause[0] == uip0)

    // LOG: UIP on level, uip (replacing by uip0)
    check(rendBlock.value < rbeginBlock.value) // 'rend_block > rbegin_block'
    check(rendBlock.value > -1) // 'rend_block < clause.rend ()'
    var blockShrunken = 0
    clause[rbeginBlock.value] = -uip
    val v = variable(-uip)
    val l = control[v.level]
    l.seenTrail = v.trail
    l.seenCount = 1

    val f = flags(-uip)
    if (!f.seen) {
        analyzed.add(-uip)
        f.seen = true
    }

    flags(-uip).keep = true
    var p = rbeginBlock.value - 1
    while (p != rendBlock.value) {
        val lit = clause[p]
        if (lit == -uip0) {
            --p
            continue
        }
        clause[p] = uip0
        // if (lit == -uip) continue;
        ++blockShrunken
        check(clause[0] == uip0)
        --p
    }
    markShrinkableAsRemovable(blevel, minimizedStart)
    check(clause[0] == uip0)
    return blockShrunken
}

internal fun Internal.shrunkenBlockNoUip(
    rbeginBlock: Int, /* reverse_iterator */
    rendBlock: Int, /* reverse_iterator */
    blockMinimized: IntRef,
    uip0: Int,
) {
    check(rendBlock < rbeginBlock) // 'rend_block > rbegin_block'
    // LOG: no UIP found, now minimizing
    var p = rbeginBlock
    while (p != rendBlock) {
        check(p != 0) // 'p != clause.rend () - 1'
        val lit = clause[p]
        if (opts.minimize != 0 && minimizeLiteral(-lit)) {
            check(!flags(lit).keep)
            ++blockMinimized.value
            clause[p] = uip0
        } else {
            flags(lit).keep = true
            check(flags(lit).keep)
        }
        --p
    }
}

internal fun Internal.pushLiteralsOfBlock(
    rbeginBlock: Int, /* reverse_iterator */
    rendBlock: Int, /* reverse_iterator */
    blevel: Int,
    maxTrail: Int,
) {
    check(rbeginBlock > rendBlock) // 'rbegin_block < rend_block'
    var p = rbeginBlock
    while (p != rendBlock) {
        check(p != 0) // 'p != clause.rend () - 1'
        check(!flags(clause[p]).keep)
        val lit = clause[p]
        // LOG: pushing lit of blevel
        val tmp = shrinkLiteral(lit, blevel, maxTrail)
        check(tmp > 0)
        --p
    }
}

internal fun Internal.shrinkNext(blevel: Int, open: IntRef, maxTrail: IntRef): Int {
    val t = trail
    if (opts.shrinkreap != 0) {
        check(!reap.empty())
        val dist = reap.pop()
        --open.value
        check(dist.toUInt() <= maxTrail.value.toUInt())
        val pos = maxTrail.value - dist
        check(pos < t.size)
        val uip = t[pos]
        check(value(uip) > 0)
        // LOG: trying to shrink literal at trail[pos] and level blevel
        return uip
    } else {
        var uip: Int
        val initMaxTrail = maxTrail.value
        do {
            check(maxTrail.value <= initMaxTrail)
            uip = t[maxTrail.value--]
        } while (!flags(uip).shrinkable)
        --open.value
        // LOG: open is now, uip, level
        return uip
    }
}

internal fun Internal.shrinkAlongReason(
    uip: Int,
    blevel: Int,
    resolveLargeClauses: Boolean,
    failedPtr: BoolRef,
    maxTrail: Int,
): Int {
    // LOG: shrinking along the reason of lit
    var open = 0
    val f = flags(uip)
    val v = variable(uip)

    check(f.shrinkable)
    check(v.level == blevel)
    check(v.reason != null)

    if (resolveLargeClauses || v.reason!!.size == 2) {
        val c = v.reason!!
        // LOG: resolving with reason
        for (k in 0 until c.size) {
            val lit = c.literals[k]
            if (lit == uip) continue
            check(value(lit) < 0)
            val tmp = shrinkLiteral(lit, blevel, maxTrail)
            if (tmp < 0) {
                failedPtr.value = true
                break
            }
            if (tmp > 0) {
                ++open
            }
        }
    } else {
        failedPtr.value = true
    }
    return open
}

internal fun Internal.shrinkBlock(
    rbeginLits: IntRef, /* reverse_iterator */
    rendBlock: IntRef, /* reverse_iterator */
    blevel: Int,
    open: IntRef,
    blockMinimized: IntRef,
    uip0: Int,
    maxTrail: Int,
): Int {
    check(shrinkable.isEmpty())
    check(blevel <= this.level)
    check(open.value < clause.size)
    check(rbeginLits.value <= clause.size - 1) // 'rbegin_lits >= clause.rbegin ()'
    check(rendBlock.value > -1) // 'rend_block < clause.rend ()'
    check(rbeginLits.value > rendBlock.value) // 'rbegin_lits < rend_block'
    check(opts.shrink != 0)

    // LOG: trying to shrink literals on level, maximum trail position

    val resolveLargeClauses = (opts.shrink > 1)
    val failed = BoolRef(false)
    var blockShrunken = 0
    val minimizedStart = minimized.size
    var uip = uip0
    val maxTrailRef = IntRef(maxTrail) // the by-value parameter 'max_trail'
    val maxTrail2 = maxTrail

    if (!failed.value) {
        pushLiteralsOfBlock(rbeginLits.value, rendBlock.value, blevel, maxTrailRef.value)
        check(opts.shrinkreap == 0 || reap.size() == open.value)

        check(open.value > 0)
        while (!failed.value) {
            check(opts.shrinkreap == 0 || reap.size() == open.value)
            uip = shrinkNext(blevel, open, maxTrailRef)
            if (open.value == 0) {
                break
            }
            open.value += shrinkAlongReason(uip, blevel, resolveLargeClauses, failed, maxTrail2)
            check(open.value >= 1)
        }

        // LOG: shrinking found UIP / shrinking failed
    }

    if (failed.value) {
        resetShrinkable()
        shrunkenBlockNoUip(rbeginLits.value, rendBlock.value, blockMinimized, uip0)
    } else {
        blockShrunken = shrunkenBlockUip(uip, blevel, rbeginLits, rendBlock, minimizedStart, uip0)
    }

    if (opts.shrinkreap != 0) reap.clear()
    shrinkable.clear()
    return blockShrunken
}

// Smaller level and trail.  Comparing literals on their level is necessary
// for chronological backtracking, since trail order might in this case not
// respect level order.

private class ShrinkTrailNegativeRank(private val internal: Internal) : IntRank {
    // typedef uint64_t Type;
    override fun rank(a: Int): Long {
        val v = internal.variable(a)
        var res = v.level.toLong()
        res = res shl 32
        res = res or v.trail.toLong()
        return res.inv()
    }
}

private class ShrinkTrailLarger(private val internal: Internal) : IntLess {
    override fun less(a: Int, b: Int): Boolean =
        ShrinkTrailNegativeRank(internal).rank(a).toULong() <
            ShrinkTrailNegativeRank(internal).rank(b).toULong()
}

// Finds the beginning of the block (rend_block, non-included) ending at
// rend_block (included). Then tries to shrinks and minimizes literals  the
// block
internal fun Internal.minimizeAndShrinkBlock(
    rbeginBlock: IntRef, /* reverse_iterator */
    totalShrunken: IntRef,
    totalMinimized: IntRef,
    uip0: Int,
): Int /* reverse_iterator */ {
    // LOG: shrinking block
    check(rbeginBlock.value > 0) // 'rbegin_block < clause.rend () - 1'
    val blevel: Int
    val open = IntRef(0)
    var maxTrail: Int

    // find begining of block;
    val rendBlock: IntRef
    run {
        check(rbeginBlock.value >= -1) // 'rbegin_block <= clause.rend ()'
        val lit = clause[rbeginBlock.value]
        val idx = vidx(lit)
        blevel = vtab[idx].level
        maxTrail = vtab[idx].trail
        // LOG: Block at level (first lit)

        rendBlock = IntRef(rbeginBlock.value)
        var finished: Boolean
        do {
            check(rendBlock.value > 0) // 'rend_block < clause.rend () - 1'
            val nextLit = clause[--rendBlock.value] // upstream shadows 'lit'
            val nextIdx = vidx(nextLit) // and 'idx'
            finished = (blevel != vtab[nextIdx].level)
            if (!finished && vtab[nextIdx].trail > maxTrail) maxTrail = vtab[nextIdx].trail
            ++open.value
            // LOG: testing if lit is on the same level
        } while (!finished)
    }
    check(open.value > 0)
    check(open.value < clause.size)
    check(rbeginBlock.value > -1) // 'rbegin_block < clause.rend ()'
    check(rendBlock.value > -1) // 'rend_block < clause.rend ()'

    var blockShrunken = 0
    val blockMinimized = IntRef(0)
    if (open.value < 2) {
        flags(clause[rbeginBlock.value]).keep = true
        minimized.add(clause[rbeginBlock.value])
    } else {
        blockShrunken = shrinkBlock(rbeginBlock, rendBlock, blevel, open, blockMinimized, uip0, maxTrail)
    }

    // LOG: shrunken literals on level (including minimized)

    totalShrunken.value += blockShrunken
    totalMinimized.value += blockMinimized.value

    return rendBlock.value
}

internal fun Internal.shrinkAndMinimizeClause() {
    check(opts.minimize != 0 || opts.shrink > 0)
    // LOG: shrink first UIP clause

    external!!.checkLearnedClause() // check 1st UIP learned clause first
    msort(opts.radixsortlim, clause, ShrinkTrailNegativeRank(this), ShrinkTrailLarger(this))
    val totalShrunken = IntRef(0)
    val totalMinimized = IntRef(0)

    // LOG: shrink first UIP clause (asserting lit)

    val rendLits = 0 // 'clause.rend () - 1'
    val rendBlock = IntRef(clause.size - 1) // 'clause.rbegin ()'
    val uip0 = clause[0]

    // for direct LRAT we remember how the clause used to look
    val oldClauseLrat = IntArrayList()
    check(minimizeChain.isEmpty())
    if (lrat) {
        for (k in 0 until clause.size) oldClauseLrat.add(clause[k])
    }

    while (rendBlock.value != rendLits) {
        rendBlock.value = minimizeAndShrinkBlock(rendBlock, totalShrunken, totalMinimized, uip0)
    }

    // LOG: post shrink pass (with uips, not removed) first UIP clause
    val oldSize = clause.size
    val stack = IntArrayList()
    run {
        var i = 1
        for (j in 1 until clause.size) {
            check(i <= j)
            clause[i] = clause[j]
            if (lrat) {
                check(j < oldClauseLrat.size)
                check(miniChain.isEmpty())
                if (clause[j] != oldClauseLrat[j]) {
                    calculateMinimizeChain(-oldClauseLrat[j], stack)
                    for (p in miniChain) {
                        minimizeChain.add(p)
                    }
                    miniChain.clear()
                }
            }
            if (clause[j] == uip0) {
                continue
            }
            check(flags(clause[i]).keep)
            ++i
            // LOG: keeping literal
        }
        clause.resize(i)
    }
    check(oldSize.toLong() == clause.size.toLong() + totalShrunken.value.toUInt().toLong() + totalMinimized.value.toUInt().toLong())
    // LOG: after shrinking first UIP clause, clause shrunken by literals

    stats.shrunken += totalShrunken.value.toUInt().toLong()
    stats.minishrunken += totalMinimized.value.toUInt().toLong()

    clearMinimizedLiterals()
    for (p in minimizeChain.size - 1 downTo 0) {
        lratChain.add(minimizeChain[p])
    }
    minimizeChain.clear()
}
