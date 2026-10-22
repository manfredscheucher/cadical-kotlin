package org.bytefred.ksat.cadical.full

import kotlin.math.min

/*
 * collect.cpp: garbage collection of clauses (non-moving and the moving arena collector).
 *
 * Mapping notes:
 *  - The moving collector copies clauses to the 'to' space of the Arena (ArenaHpp.kt), which
 *    gives each copy a virtual address in copy order; 'pointer_rank' -> [clauseAddressRank].
 *  - 'shrink_vector (clauses)' guarded by 'clauses.size () < clauses.capacity () / 2' ->
 *    'trimToSize ()' (the capacity is not observable, trimming has no visible effect).
 *  - 'LSTRACE_PHASE ("collect")' of the shadow trace -> [tracePhase] around
 *    'garbage_collection'.
 */

/*------------------------------------------------------------------------*/

// Returns the positive number '1' ( > 0) if the given clause is root level
// satisfied or the negative number '-1' ( < 0) if it is not root level
// satisfied but contains a root level falsified literal. Otherwise, if it
// contains neither a satisfied nor falsified literal, then '0' is returned.

internal fun Internal.clauseContainsFixedLiteral(c: Clause): Int {
    var satisfied = 0
    var falsified = 0
    for (k in 0 until c.size) {
        val lit = c.literals[k]
        val tmp = fixed(lit)
        if (tmp > 0) {
            // LOG: root level satisfied literal
            satisfied++
        }
        if (tmp < 0) {
            // LOG: root level falsified literal
            falsified++
        }
    }
    return if (satisfied != 0) 1
    else if (falsified != 0) -1
    else 0
}

// Assume that the clause is not root level satisfied but contains a literal
// set to false (root level falsified literal), so it can be shrunken.  The
// clause data is not actually reallocated at this point to avoid dealing
// with issues of special policies for watching binary clauses or whether a
// clause is extended or not. Only its size field is adjusted accordingly
// after flushing out root level falsified literals.

internal fun Internal.removeFalsifiedLiterals(c: Clause) {
    val end = c.size
    var i = 0
    var numNonFalse = 0
    while (numNonFalse < 2 && i != end) {
        if (fixed(c.literals[i]) >= 0) numNonFalse++
        i++
    }
    if (numNonFalse < 2) return
    proof?.flushClause(c)
    var j = 0
    for (k in j until end) {
        val lit = c.literals[k]
        c.literals[j++] = lit
        val tmp = fixed(lit)
        check(tmp <= 0)
        if (tmp >= 0) continue
        // LOG: flushing lit
        j--
    }
    stats.collected += shrinkClause(c, j)
}

// If there are new units (fixed variables) since the last garbage
// collection we go over all clauses, mark satisfied ones as garbage and
// flush falsified literals.  Otherwise if no new units have been generated
// since the last garbage collection just skip this step.

internal fun Internal.markSatisfiedClausesAsGarbage() {

    if (last.collect.fixed >= stats.all.fixed) return
    last.collect.fixed = stats.all.fixed

    // LOG: marking satisfied clauses and removing falsified literals

    for (c in clauses) {
        if (c.garbage) continue
        val tmp = clauseContainsFixedLiteral(c)
        if (tmp > 0) markGarbage(c)
        else if (tmp < 0) removeFalsifiedLiterals(c)
    }
}

/*------------------------------------------------------------------------*/

// Reason clauses can not be collected.
//
// We protect reasons before and release protection after garbage collection
// (actually within garbage collection).
//
// For 'reduce' we still need to make sure that all clauses which should not
// be removed are marked as such and thus we need to call it before marking
// clauses to be flushed.

internal fun Internal.protectReasons() {
    // LOG: protecting reason clauses of all assigned variables on trail
    check(!protectedReasons) { "reasons already protected" }
    for (k in 0 until trail.size) {
        val lit = trail[k]
        if (!active(lit)) continue
        check(value(lit) != 0)
        val v = variable(lit)
        check(v.level > 0)
        val reason = v.reason ?: continue
        if (reason === externalReason) continue
        check(!reason.reason)
        reason.reason = true
    }
    protectedReasons = true
}

/*------------------------------------------------------------------------*/

// After garbage collection we reset the 'reason' flag of the reasons
// of assigned literals on the trail.

internal fun Internal.unprotectReasons() {
    // LOG: unprotecting reasons clauses of all assigned variables on trail
    check(protectedReasons) { "reasons not protected" }
    for (k in 0 until trail.size) {
        val lit = trail[k]
        if (!active(lit)) continue
        check(value(lit) != 0)
        val v = variable(lit)
        check(v.level > 0)
        val reason = v.reason ?: continue
        if (reason === externalReason) continue
        check(reason.reason)
        reason.reason = false
    }
    protectedReasons = false
}

/*------------------------------------------------------------------------*/

// Update occurrence lists before deleting garbage clauses in the context of
// preprocessing, e.g., during bounded variable elimination 'elim'.  The
// result is the number of remaining clauses, which in this context means
// the number of non-garbage clauses.

internal fun Internal.flushOccs(lit: Int): Int {
    val os = occs(lit)
    val end = os.size
    var j = 0
    var i = j
    var res = 0
    var c: Clause
    while (i != end) {
        c = os[i]
        i++
        if (c.collect()) continue
        os[j++] = if (c.moved) c.copy!! else c
        check(!c.redundant)
        res++
    }
    os.shrinkTo(j)
    shrinkOccs(os)
    return res
}

// Update watch lists before deleting garbage clauses in the context of
// 'reduce' where we watch and no occurrence lists.  We have to protect
// reason clauses not be collected and thus we have this additional check
// hidden in 'Clause.collect', which for the root level context of
// preprocessing is actually redundant.

internal fun Internal.flushWatches(lit: Int, saved: Watches) {
    check(saved.isEmpty())
    val ws = watches(lit)
    val end = ws.size
    var j = 0
    var i = j
    while (i != end) {
        // 'Watch w = *i': the slot 'i' is never read again, so updating the
        // watch object in place is the same as updating the copy.
        val w = ws[i]
        i++
        var c = w.clause
        if (c.collect()) continue
        if (c.moved) {
            c = c.copy!!
            w.clause = c
        }
        w.size = c.size
        val newBlitPos = if (c.literals[0] == lit) 1 else 0
        // LOG: clause in flush_watch starting from lit
        check(c.literals[1 - newBlitPos] == lit) /*FW1*/
        w.blit = c.literals[newBlitPos]
        if (w.binary()) ws[j++] = w
        else saved.add(w)
    }
    ws.shrinkTo(j)
    for (w in saved) ws.add(w)
    saved.clear()
    ws.trimToSize()
}

internal fun Internal.flushAllOccsAndWatches() {
    if (occurring()) {
        for (idx in vars) {
            flushOccs(idx)
            flushOccs(-idx)
        }
    }

    if (watching()) {
        val tmp = Watches()
        for (idx in vars) {
            flushWatches(idx, tmp)
            flushWatches(-idx, tmp)
        }
    }
}

/*------------------------------------------------------------------------*/

internal fun Internal.updateReasonReferences() {
    // LOG: update assigned reason references
    for (k in 0 until trail.size) {
        val lit = trail[k]
        if (!active(lit)) continue
        val v = variable(lit)
        val c = v.reason ?: continue
        if (c === externalReason) continue
        check(c.reason)
        check(c.moved)
        val d = c.copy
        v.reason = d
    }
}

/*------------------------------------------------------------------------*/

// This is a simple garbage collector which does not move clauses.  It needs
// less space than the arena based clause allocator, but is not as cache
// efficient, since the copying garbage collector can put clauses together
// which are likely accessed after each other.

internal fun Internal.deleteGarbageClauses() {

    flushAllOccsAndWatches()

    // LOG: deleting garbage clauses
    val end = clauses.size
    var j = 0
    var i = j
    while (i != end) {
        val c = clauses[i++]
        clauses[j++] = c
        if (!c.collect()) continue
        deleteClause(c)
        j--
    }
    clauses.shrinkTo(j)
    clauses.trimToSize()

    // PHASE: collected bytes of garbage clauses
}

/*------------------------------------------------------------------------*/

// This is the start of the copying garbage collector using the arena.  At
// the core is the following function, which copies a clause to the 'to'
// space of the arena.  Be careful if this clause is a reason of an
// assignment.  In that case update the reason reference.
//
internal fun Internal.copyClause(c: Clause) {
    // LOG: moving
    check(!c.moved) { "copy_clause of moved clause" }
    val q = arena.copy(c)
    c.copy = q
    c.moved = true
}

// This is the moving garbage collector.

internal fun Internal.copyNonGarbageClauses() {

    var collectedClauses = 0L
    var collectedBytes = 0L
    var movedClauses = 0L
    var movedBytes = 0L

    // First determine 'moved_bytes' and 'collected_bytes'.
    //
    for (c in clauses) {
        if (!c.collect()) {
            movedBytes += c.bytes()
            movedClauses++
        } else {
            collectedBytes += c.bytes()
            collectedClauses++
        }
    }

    // PHASE: moving bytes of non garbage clauses
    // Prepare 'to' space of size 'moved_bytes'.
    //
    arena.prepare(movedBytes)

    // Keep clauses in arena in the same order.
    //
    if (opts.arenacompact != 0) {
        for (c in clauses) if (!c.collect() && arena.contains(c)) copyClause(c)
    }

    if (opts.arenatype == 1 || !watching()) {

        // Localize according to current clause order.

        // If the option 'opts.arenatype == 1' is set, then this means the
        // solver uses the original order of clauses.  If there are no watches,
        // we can not use the watched based copying policies below.  This
        // happens if garbage collection is triggered during bounded variable
        // elimination.

        // Copy clauses according to the order of calling 'copy_clause', which
        // in essence just gives a compacting garbage collector, since their
        // relative order is kept, and actually already gives the largest
        // benefit due to better cache locality.

        for (c in clauses) if (!c.moved && !c.collect()) copyClause(c)
    } else if (opts.arenatype == 2) {

        // Localize according to (original) variable order.

        // This is almost the version used by MiniSAT and descendants.
        // Our version uses saved phases too.

        var sign = -1
        while (sign <= 1) {
            for (idx in vars) {
                for (w in watches(sign * likelyPhase(idx))) {
                    if (!w.clause.moved && !w.clause.collect()) copyClause(w.clause)
                }
            }
            sign += 2
        }
    } else {

        // Localize according to decision queue order.

        // This is the default for search. It allocates clauses in the order of
        // the decision queue and also uses saved phases.  It seems faster than
        // the MiniSAT version and thus we keep 'opts.arenatype == 3'.

        check(opts.arenatype == 3)

        var sign = -1
        while (sign <= 1) {
            var idx = queue.last
            while (idx != 0) {
                for (w in watches(sign * likelyPhase(idx))) {
                    if (!w.clause.moved && !w.clause.collect()) copyClause(w.clause)
                }
                idx = link(idx).prev
            }
            sign += 2
        }
    }

    // Do not forget to move clauses which are not watched, which happened in
    // a rare situation, and now is only left as defensive code.
    //
    for (c in clauses) if (!c.collect() && !c.moved) copyClause(c)

    flushAllOccsAndWatches()
    updateReasonReferences()

    // Replace and flush clause references in 'clauses'.
    //
    val end = clauses.size
    var j = 0
    var i = j
    while (i != end) {
        val c = clauses[i]
        if (c.collect()) {
            deleteClause(c)
        } else {
            check(c.moved)
            clauses[j++] = c.copy!!
            deallocateClause(c)
        }
        i++
    }
    clauses.shrinkTo(j)
    clauses.trimToSize() // 'if (clauses.size () < clauses.capacity () / 2) shrink_vector'

    if (opts.arenasort != 0) rsort(clauses, clauseAddressRank)

    // Release 'from' space completely and then swap 'to' with 'from'.
    //
    arena.swap()

    // PHASE: collected bytes of garbage clauses
}

/*------------------------------------------------------------------------*/

// Maintaining clause statistics is complex and error prone but necessary
// for proper scheduling of garbage collection, particularly during bounded
// variable elimination.  With this function we can check whether these
// statistics are updated correctly.

internal fun Internal.checkClauseStats() {
    // The whole body is '#ifndef NDEBUG' upstream: empty in the release reference.
}

/*------------------------------------------------------------------------*/

// only delete binary clauses from watch list that are already mark as
// deleted.
internal fun Internal.removeGarbageBinaries() {
    if (unsat) return

    if (!protectedReasons) protectReasons()
    var backtrackLevel = level + 1
    val saved = Watches()
    for (v in vars) {
        for (lit in intArrayOf(-v, v)) {
            check(saved.isEmpty())
            val ws = watches(lit)
            val end = ws.size
            var j = 0
            var i = j
            while (i != end) {
                val w = ws[i]
                i++
                ws[j++] = w
                val c = w.clause
                cover(!w.binary() && c.size == 2)
                if (!w.binary()) continue
                if (c.reason && c.garbage) {
                    cover(true)
                    check(c.size == 2)
                    backtrackLevel = min(backtrackLevel, variable(c.literals[0]).level)
                    // LOG: need to backtrack to before level
                    --j
                    continue
                }
                if (!c.collect()) continue
                // LOG: removing from watch list
                --j
            }
            ws.shrinkTo(j)
            ws.trimToSize()
        }
    }
    deleteGarbageClauses()
    unprotectReasons()
    if (backtrackLevel - 1 < level) backtrack(backtrackLevel - 1)
}

/*------------------------------------------------------------------------*/

internal fun Internal.arenaing(): Boolean = opts.arena != 0 && (stats.collections > 1)

internal fun Internal.garbageCollection() {
    tracePhase("collect") {
        if (unsat) return
        // report ('G', 1)
        stats.collections++
        markSatisfiedClausesAsGarbage()
        if (!protectedReasons) protectReasons()
        if (arenaing()) copyNonGarbageClauses()
        else deleteGarbageClauses()
        checkClauseStats()
        checkVarStats()
        unprotectReasons()
        // report ('C', 1)
    }
}
