package org.bytefred.ksat.cadical.full

import kotlin.math.abs

/*
 * clause.hpp: the 'Clause' data structure, 'clause_smaller_size', 'clause_lit_less_than'.
 *
 * Mapping:
 *  - 'Clause *' -> 'Clause' reference, 'nullptr' / '0' -> null.
 *  - The flexible array member 'int literals[]' -> [literals], an IntArray allocated with the
 *    size at creation. [size] is the actual size; shrinking a clause ('shrink_clause') only
 *    lowers [size], exactly as upstream keeps the allocated memory.
 *    'for (const auto &lit : *c)' -> 'for (k in 0 until c.size) { val lit = c.literals[k] ... }'.
 *    'literal_iterator' arithmetic ('c->begin () + i') -> int index into [literals].
 *  - 'union { uint64_t id; Clause *copy; }' -> two separate fields [id] and [copy]. Upstream
 *    writes 'copy' only in 'copy_clause' (collect.cpp) and never reads 'id' of a moved clause
 *    afterwards, so keeping both is equivalent. 'uint64_t id' -> Long (ids stay below 2^63).
 *  - Bit fields -> Boolean, 'unsigned used : 2' -> Int (0..2, never larger upstream).
 *  - Memory addresses: a clause has a virtual address used by the arena (see ArenaHpp.kt):
 *    [space] is the arena space id holding the clause (0 = allocated outside the arena with
 *    'new') and [address] its offset there. 'pointer_rank' sorts by [address].
 *  - 'Clause::bytes' mirrors the 64 bit layout: 'sizeof (Clause)' is 24 (measured with the
 *    upstream header, scripts/probe/probe_cadical_sizes.cpp), plus 4 bytes per literal,
 *    aligned to 8. Bytes only feed statistics and the arena addresses.
 */
internal class Clause(capacity: Int) {
    var id: Long = 0 // Used to create LRAT-style proofs
    var copy: Clause? = null // Only valid if 'moved', then that's where to.

    var conditioned = false // Tried for globally blocked clause elimination.
    var covered = false // Already considered for covered clause elimination.
    var enqueued = false // Enqueued on backward queue.
    var frozen = false // Temporarily frozen (in covered clause elimination).
    var garbage = false // can be garbage collected unless it is a 'reason'
    var gate = false // Clause part of a gate (function definition).
    var hyper = false // redundant hyper binary or ternary resolved
    var instantiated = false // tried to instantiate
    var keep = false // always keep this clause (if redundant)
    var moved = false // moved during garbage collector ('copy' valid)
    var reason = false // reason / antecedent clause can not be collected
    var redundant = false // aka 'learned' so not 'irredundant' (original)
    var transred = false // already checked for transitive reduction
    var subsume = false // not checked in last subsumption round
    var used = 0 // resolved in conflict analysis since last 'reduce' (2 bits)
    var vivified = false // clause already vivified
    var vivify = false // clause scheduled to be vivified

    // The glucose level ('LBD' or short 'glue') is a heuristic value for the
    // expected usefulness of a learned clause, where smaller glue is consider
    // more useful (see the long comment in upstream 'clause.hpp').
    var glue = 0
    var size = 0 // Actual size of 'literals' (at least 2).
    var pos = 0 // Position of last watch replacement [Gent'13].

    val literals = IntArray(capacity)

    var space = 0 // arena space id, 0 = not in the arena (see ArenaHpp.kt)
    var address = 0L // virtual address inside [space]

    fun bytes(): Long = bytes(size)

    // Check whether this clause is ready to be collected and deleted.  The
    // 'reason' flag is only there to protect reason clauses in 'reduce',
    // which does not backtrack to the root level.  If garbage collection is
    // triggered from a preprocessor, which backtracks to the root level, then
    // 'reason' is false for sure. We want to use the same garbage collection
    // code though for both situations and thus hide here this variance.
    fun collect(): Boolean = !reason && garbage

    /**
     * The 'memcpy' of 'Arena::copy': a new clause object with all fields and the first
     * [size] literals (the copy is not 'moved' and has no 'copy' yet, as the memcpy happens
     * before 'copy_clause' sets them on the original).
     */
    fun memcpy(): Clause {
        val res = Clause(size)
        res.id = id
        res.copy = copy
        res.conditioned = conditioned
        res.covered = covered
        res.enqueued = enqueued
        res.frozen = frozen
        res.garbage = garbage
        res.gate = gate
        res.hyper = hyper
        res.instantiated = instantiated
        res.keep = keep
        res.moved = moved
        res.reason = reason
        res.redundant = redundant
        res.transred = transred
        res.subsume = subsume
        res.used = used
        res.vivified = vivified
        res.vivify = vivify
        res.glue = glue
        res.size = size
        res.pos = pos
        literals.copyInto(res.literals, 0, 0, size)
        return res
    }

    companion object {
        /** sizeof (Clause) of the upstream 64 bit build. */
        const val HEADER_BYTES = 24L

        fun bytes(size: Int): Long {
            // Memory sanitizer insists that clauses put into consecutive memory in
            // the arena are still 8 byte aligned (see upstream comment).
            check(size > 1)
            val headerBytes = HEADER_BYTES
            val actualLiteralBytes = size * 4L
            val combinedBytes = headerBytes + actualLiteralBytes
            return align(combinedBytes, 8)
        }
    }
}

internal val clauseSmallerSize = Less<Clause> { a, b -> a.size < b.size }

// Place literals over the same variable close to each other.  This would
// allow eager removal of identical literals and detection of tautological
// clauses but is only currently used for better logging (see also
// 'opts.logsort' in 'logging.cpp').
internal val clauseLitLessThan = IntLess { a, b ->
    val s = abs(a)
    val t = abs(b)
    s < t || (s == t && a < b)
}
