package org.bytefred.ksat.cadical.full

import kotlin.math.abs
import kotlin.math.min

/*
 * clause.cpp: allocating, marking, shrinking and deleting clauses.
 *
 * Mapping notes:
 *  - 'new char[bytes]' + field initialization -> 'Clause (size)' with the same field values;
 *    the clause is outside the arena (space 0), as upstream.
 *  - 'delete[] p' in 'deallocate_clause' -> nothing (garbage collected).
 *  - 'unordered_set<int> learned_levels' -> HashSet (only its size is used).
 */

/*------------------------------------------------------------------------*/

// Signed marking or unmarking of a clause or the global 'clause'.

internal fun Internal.mark(c: Clause) {
    for (k in 0 until c.size) mark(c.literals[k])
}

internal fun Internal.mark2(c: Clause) {
    for (k in 0 until c.size) mark2(c.literals[k])
}

internal fun Internal.unmark(c: Clause) {
    for (k in 0 until c.size) unmark(c.literals[k])
}

internal fun Internal.markClause() {
    for (k in 0 until clause.size) mark(clause[k])
}

internal fun Internal.unmarkClause() {
    for (k in 0 until clause.size) unmark(clause[k])
}

/*------------------------------------------------------------------------*/

// Mark the variables of an irredundant clause to 'have been removed', which
// will trigger these variables to be considered again in the next bounded
// variable elimination phase.  This is called from 'mark_garbage' below.
// Note that 'mark_removed (int lit)' will also mark the blocking flag of
// '-lit' to trigger reconsidering blocking clauses on '-lit'.

internal fun Internal.markRemoved(c: Clause, except: Int = 0) {
    check(!c.redundant) { "mark_removed on redundant clause" }
    for (k in 0 until c.size) {
        val lit = c.literals[k]
        if (lit != except) markRemoved(lit)
    }
}

// Mark the variables of a (redundant or irredundant) clause to 'have been
// added', which triggers clauses with such a variables, to be considered
// both as a subsumed or subsuming clause in the next subsumption phase.
// This function is called from 'new_clause' below as well as in situations
// where a clause is shrunken (and thus needs to be at least considered
// again to subsume a larger clause).  We also use this to tell
// 'ternary' preprocessing reconsider clauses on an added literal as well as
// trying to block clauses on it.

internal fun Internal.markAdded(lit: Int, size: Int, redundant: Boolean) {
    markSubsume(lit)
    if (size == 3) markTernary(lit)
    if (!redundant) markBlock(lit)
}

internal fun Internal.markAdded(c: Clause) {
    check(likelyToBeKeptClause(c)) { "mark_added on clause not likely to be kept" }
    for (k in 0 until c.size) markAdded(c.literals[k], c.size, c.redundant)
}

/*------------------------------------------------------------------------*/

internal fun Internal.newClause(red: Boolean, glue: Int = 0): Clause {
    var glue = glue

    check(clause.size <= Int.MAX_VALUE)
    val size = clause.size
    check(size >= 2) { "new_clause of size $size" }

    if (glue > size) glue = size

    // Determine whether this clauses should be kept all the time.
    //
    val keep: Boolean
    if (!red) keep = true
    else if (glue <= opts.reducetier1glue) keep = true
    else keep = false

    val bytes = Clause.bytes(size)
    val c = Clause(size)

    c.id = ++clauseId

    c.conditioned = false
    c.covered = false
    c.enqueued = false
    c.frozen = false
    c.garbage = false
    c.gate = false
    c.hyper = false
    c.instantiated = false
    c.keep = keep
    c.moved = false
    c.reason = false
    c.redundant = red
    c.transred = false
    c.subsume = false
    c.vivified = false
    c.vivify = false
    c.used = 0

    c.glue = glue
    c.size = size
    c.pos = 2

    for (i in 0 until size) c.literals[i] = clause[i]

    // Just checking that we did not mess up our sophisticated memory layout.
    // This might be compiler dependent though. Crucial for correctness.
    //
    check(c.bytes() == bytes)

    stats.current.total++
    stats.added.total++

    if (red) {
        stats.current.redundant++
        stats.added.redundant++
    } else {
        stats.irrlits += size
        stats.current.irredundant++
        stats.added.irredundant++
    }

    clauses.add(c)

    if (likelyToBeKeptClause(c)) markAdded(c)

    return c
}

/*------------------------------------------------------------------------*/

internal fun Internal.promoteClause(c: Clause, newGlue: Int) {
    check(c.redundant) { "promote_clause on irredundant clause" }
    if (c.keep) return
    if (c.hyper) return
    val oldGlue = c.glue
    if (newGlue >= oldGlue) return
    if (!c.keep && newGlue <= opts.reducetier1glue) {
        // LOG: promoting with new glue to tier1
        stats.promoted1++
        c.keep = true
    } else if (oldGlue > opts.reducetier2glue && newGlue <= opts.reducetier2glue) {
        // LOG: promoting with new glue to tier2
        stats.promoted2++
        c.used = 2
    } else if (c.keep) {
        // LOG: keeping with new glue in tier1
    } else if (oldGlue <= opts.reducetier2glue) {
        // LOG: keeping with new glue in tier2
    } else {
        // LOG: keeping with new glue in tier3
    }
    stats.improvedglue++
    c.glue = newGlue
}

/*------------------------------------------------------------------------*/

// Shrinking a clause, e.g., removing one or more literals, requires to fix
// the 'pos' field, if it exists and points after the new last literal. We
// also have adjust the global statistics counter of irredundant literals
// for irredundant clauses, and also adjust the glue value of redundant
// clauses if the size becomes smaller than the glue.  Also mark the
// literals in the resulting clause as 'added'.  The result is the number of
// (aligned) removed bytes, resulting from shrinking the clause.
//
internal fun Internal.shrinkClause(c: Clause, newSize: Int): Int {
    if (opts.check != 0 && isExternalForgettable(c.id)) markGarbageExternalForgettable(c.id)
    check(newSize >= 2) { "shrink_clause to size $newSize" }
    val oldSize = c.size
    check(newSize < oldSize) { "shrink_clause does not shrink" }
    // '#ifndef NDEBUG' loop from 'c->size' to 'new_size' (never iterates): not in release.

    if (c.pos >= newSize) c.pos = 2

    val oldBytes = c.bytes()
    c.size = newSize
    val newBytes = c.bytes()
    val res = oldBytes - newBytes

    if (c.redundant) {
        promoteClause(c, min(c.size - 1, c.glue))
    } else {
        val deltaSize = oldSize - newSize
        check(stats.irrlits >= deltaSize)
        stats.irrlits -= deltaSize
    }

    if (likelyToBeKeptClause(c)) markAdded(c)

    return res.toInt()
}

// This is the 'raw' deallocation of a clause.  If the clause is in the
// arena nothing happens.  If the clause is not in the arena its memory is
// reclaimed immediately.

internal fun Internal.deallocateClause(c: Clause) {
    if (arena.contains(c)) return
    // 'delete[] p': reclaimed by the garbage collector.
}

internal fun Internal.deleteClause(c: Clause) {
    val bytes = c.bytes()
    stats.collected += bytes
    if (c.garbage) {
        check(stats.garbage.bytes >= bytes)
        stats.garbage.bytes -= bytes
        check(stats.garbage.clauses > 0)
        stats.garbage.clauses--
        check(stats.garbage.literals >= c.size)
        stats.garbage.literals -= c.size

        // See the discussion in 'propagate' on avoiding to eagerly trace binary
        // clauses as deleted (produce 'd ...' lines) as soon they are marked
        // garbage.  We avoid this and only trace them as deleted when they are
        // actually deleted here.  This allows the solver to propagate binary
        // garbage clauses without producing incorrect 'd' lines.  The effect
        // from the proof perspective is that the deletion of these binary
        // clauses occurs later in the proof file.
        //
        val p = proof
        if (p != null && c.size == 2) {
            p.deleteClause(c)
        }
    }
    deallocateClause(c)
}

// We want to eagerly update statistics as soon clauses are marked garbage.
// Otherwise 'report' for instance gives wrong numbers after 'subsume'
// before the next 'reduce'.  Thus we factored out marking and accounting
// for garbage clauses.
//
// Eagerly deleting clauses instead is problematic, since references to
// these clauses need to be flushed, which is too costly to do eagerly.
//
// We also update garbage statistics at this point.  This helps to
// determine whether the garbage collector should be called during for
// instance bounded variable elimination, which usually generates lots of
// garbage clauses.
//
// In order not to miss any update to these clause statistics we call
// 'check_clause_stats' after garbage collection in debugging mode.
//
internal fun Internal.markGarbage(c: Clause) {

    check(!c.garbage) { "mark_garbage on garbage clause" }

    // Delay tracing deletion of binary clauses.  See the discussion above in
    // 'delete_clause' and also in 'propagate'.
    //
    val p = proof
    if (p != null && c.size != 2) {
        p.deleteClause(c)
    }

    // Because of the internal model checking, external forgettable clauses
    // must be marked as removed already upon mark_garbage, can not wait until
    // actual deletion.
    if (opts.check != 0 && isExternalForgettable(c.id)) markGarbageExternalForgettable(c.id)

    check(stats.current.total > 0)
    stats.current.total--

    val bytes = c.bytes()
    if (c.redundant) {
        check(stats.current.redundant > 0)
        stats.current.redundant--
    } else {
        check(stats.current.irredundant > 0)
        stats.current.irredundant--
        check(stats.irrlits >= c.size)
        stats.irrlits -= c.size
        markRemoved(c)
    }
    stats.garbage.bytes += bytes
    stats.garbage.clauses++
    stats.garbage.literals += c.size
    c.garbage = true
    c.used = 0
}

/*------------------------------------------------------------------------*/

// Almost the same function as 'search_assign' except that we do not pretend
// to learn a new unit clause (which was confusing in log files).

internal fun Internal.assignOriginalUnit(id: Long, lit: Int) {
    check(level == 0 || opts.chrono != 0)
    check(!unsat)
    val idx = vidx(lit)
    check(value(idx) == 0)
    check(!flags(idx).eliminated())
    val v = variable(idx)
    v.level = 0
    v.trail = trail.size
    v.reason = null
    val tmp = sign(lit)
    setVal(idx, tmp)
    trail.add(lit)
    numAssigned++
    val uidx = vlit(lit)
    if (lrat || frat) unitClausesIdx[uidx] = id
    check(numAssigned == trail.size || level != 0)
    markFixed(lit)
    if (level != 0) return
    if (propagate()) return
    check(conflict != null)
    // LOG: propagation of original unit results in conflict
    learnEmptyClause()
}

// New clause added through the API, e.g., while parsing a DIMACS file.
// Also used by external_propagate in various different modes.
// clause, original, lrat_chain and external->eclause are set.
// from_propagator and force_no_backtrack change the behaviour.
// sometimes the pointer to the new clause is needed, therefore it is
// made sure that newest_clause points to the new clause upon return.
//
// TODO: Find another name for 'tainted' in the context of ilb, tainted
// is reconstruction related already and they should not mix.
internal fun Internal.addNewOriginalClause(id: Long) {

    if (!fromPropagator && level != 0 && opts.ilb == 0) {
        backtrack()
    } else if (taintedLiteral != 0) {
        check(value(taintedLiteral) != 0)
        val newLevel = variable(taintedLiteral).level - 1
        check(newLevel >= 0)
        backtrack(newLevel)
    }
    check(taintedLiteral == 0)
    check(clause.isEmpty())
    var skip = false
    val learnedLevels = HashSet<Int>()
    var unassigned = 0
    newestClause = null
    if (unsat) {
        // LOG: skipping clause since formula is already inconsistent
        skip = true
    } else {
        check(clause.isEmpty())
        for (k in 0 until original.size) {
            val lit = original[k]
            var tmp = marked(lit)
            if (tmp > 0) {
                // LOG: removing duplicated literal
            } else if (tmp < 0) {
                // LOG: tautological since both -lit and lit occur
                skip = true
            } else {
                mark(lit)
                tmp = fixed(lit)
                if (tmp < 0) {
                    // LOG: removing falsified literal
                    if (lrat) {
                        val elit = externalize(lit)
                        val eidx = (if (elit > 0) 1 else 0) + 2 * abs(elit)
                        if (external!!.extUnits[eidx] == 0L) {
                            val uid = unitClauses(vlit(-lit))
                            check(uid != 0L)
                            lratChain.add(uid)
                        }
                    }
                } else if (tmp > 0) {
                    // LOG: satisfied since literal true
                    skip = true
                } else {
                    clause.add(lit)
                    check(flags(lit).status != Flags.UNUSED)
                    tmp = value(lit)
                    if (tmp != 0) learnedLevels.add(variable(lit).level)
                    else unassigned++
                }
            }
        }
        for (k in 0 until original.size) unmark(original[k])
    }
    if (skip) {
        if (fromPropagator) {
            stats.extProp.elearnConf++

            // In case it was a skipped external forgettable, we need to mark it
            // immediately as removed

            if (opts.check != 0 && isExternalForgettable(id)) markGarbageExternalForgettable(id)
        }
        val p = proof
        if (p != null) {
            p.deleteExternalOriginalClause(id, false, external!!.eclause)
        }
    } else {
        var newId = id
        val size = clause.size
        if (original.size > size) {
            newId = ++clauseId
            val p = proof
            if (p != null) {
                if (lrat) lratChain.add(id)
                p.addDerivedClause(newId, false, clause, lratChain)
                p.deleteExternalOriginalClause(id, false, external!!.eclause)
            }
            external!!.checkLearnedClause()

            if (fromPropagator) {
                // The original form of the added clause is immediately forgotten
                // TODO: shall we save and check the simplified form? (one with
                // new_id)
                if (opts.check != 0 && isExternalForgettable(id)) markGarbageExternalForgettable(id)
            }
        }
        external!!.eclause.clear()
        lratChain.clear()
        if (size == 0) {
            if (fromPropagator) stats.extProp.elearnConf++
            check(!unsat)
            // VERBOSE: found empty / falsified original clause
            unsat = true
            conflictId = newId
            markedFailed = true
            conclusion.add(newId)
        } else if (size == 1) {
            if (forceNoBacktrack) {
                check(level != 0)
                val idx = vidx(clause[0])
                check(value(clause[0]) >= 0)
                check(!flags(idx).eliminated())
                val v = variable(idx)
                check(value(clause[0]) != 0)
                v.level = 0
                v.reason = null
                val uidx = vlit(clause[0])
                if (lrat || frat) unitClausesIdx[uidx] = newId
                markFixed(clause[0])
            } else {
                val lit = clause[0]
                check(value(lit) == 0 || variable(lit).level != 0)
                if (value(lit) < 0) backtrack(variable(lit).level - 1)
                check(value(lit) >= 0)
                handleExternalClause(null)
                assignOriginalUnit(newId, lit)
            }
        } else {
            moveLiteralsToWatch()
            // '#ifndef NDEBUG' upstream: 'check_watched_literal_invariants ()', not in release.
            val glue = learnedLevels.size + unassigned
            check(glue <= clause.size)
            val clauseRedundancy = fromPropagator && extClauseForgettable
            val c = newClause(clauseRedundancy, glue)
            c.id = newId
            clauseId--
            watchClause(c)
            clause.clear()
            original.clear()
            handleExternalClause(c)
            newestClause = c
        }
    }
    clause.clear()
    lratChain.clear()
}

// Add learned new clause during conflict analysis and watch it. Requires
// that the clause is at least of size 2, and the first two literals
// are assigned at the highest decision level.
//
internal fun Internal.newLearnedRedundantClause(glue: Int): Clause {
    check(clause.size > 1)
    // '#ifndef NDEBUG' level order check of the learned clause: not in release.
    external!!.checkLearnedClause()
    val res = newClause(true, glue)
    val p = proof
    if (p != null) {
        p.addDerivedClause(res, lratChain)
    }
    check(watching())
    watchClause(res)
    return res
}

// Add hyper binary resolved clause during 'probing'.
//
internal fun Internal.newHyperBinaryResolvedClause(red: Boolean, glue: Int): Clause {
    external!!.checkLearnedClause()
    val res = newClause(red, glue)
    val p = proof
    if (p != null) {
        p.addDerivedClause(res, lratChain)
    }
    check(watching())
    watchClause(res)
    return res
}

// Add hyper ternary resolved clause during 'ternary'.
//
internal fun Internal.newHyperTernaryResolvedClause(red: Boolean): Clause {
    external!!.checkLearnedClause()
    val size = clause.size
    val res = newClause(red, size)
    val p = proof
    if (p != null) {
        p.addDerivedClause(res, lratChain)
    }
    check(!watching())
    return res
}

// Add a new clause with same glue and redundancy as 'orig' but literals are
// assumed to be in 'clause' in 'decompose' and 'vivify'.
//
internal fun Internal.newClauseAs(orig: Clause): Clause {
    external!!.checkLearnedClause()
    val newGlue = orig.glue
    val res = newClause(orig.redundant, newGlue)
    check(!orig.redundant || !orig.keep || res.keep)
    val p = proof
    if (p != null) {
        p.addDerivedClause(res, lratChain)
    }
    check(watching())
    watchClause(res)
    return res
}

// Add resolved clause during resolution, e.g., bounded variable
// elimination, but do not connect its occurrences here.
//
internal fun Internal.newResolvedIrredundantClause(): Clause {
    external!!.checkLearnedClause()
    val p = proof
    if (p != null) {
        p.addDerivedClause(clauseId + 1, false, clause, lratChain)
    }
    val res = newClause(false)
    check(!watching())
    return res
}
