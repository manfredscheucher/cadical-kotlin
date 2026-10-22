package org.bytefred.ksat.cadical.full

import kotlin.math.abs
import kotlin.math.max
import org.bytefred.ksat.cadical.IntArrayList

/*
 * checker.hpp + checker.cpp: the online forward DRUP proof checker ('opts.checkproof' 1 or 3,
 * requires 'opts.check').
 *
 * Mapping:
 *  - 'CheckerClause' with its flexible 'literals' array -> a class holding an IntArray;
 *    'CheckerWatch' -> a class. The watch copies '*j++ = *i' / '*j++ = w' of the compaction
 *    loops copy references: the source slot is never read again, so this is the same.
 *  - 'signed char *vals' valid in [-size_vars+1, size_vars-1] -> a ByteArray of length
 *    '2 * size_vars' indexed by 'size_vars + lit'. 'marks' -> ByteArray, 'watchers' ->
 *    ArrayList of watch lists, both indexed by 'l2u (lit)'.
 *  - The hash table -> an array of chain heads; 'CheckerClause **' slots -> [Slot] (bucket or
 *    previous chain element). 'uint64_t' hashes / nonces -> ULong, ids and counts -> Long.
 *  - 'fatal_message_start' ... 'fatal_message_end' -> 'error' with the same text.
 *  - 'Checker::check ()' -> [checkImplied] (Kotlin 'check' is the assertion).
 *  - 'START' / 'STOP' (profiling) and 'LOG' are dropped; 'print_stats' (stats.cpp) only
 *    prints; 'dump' (debugging output, never called) is not ported.
 */
internal class CheckerClause(
    var next: CheckerClause?, // collision chain link for hash table
    var hash: ULong, // previously computed full 64-bit hash
    var size: Int, // zero if this is a garbage clause
    val literals: IntArray, // otherwise 'literals' of length 'size'
)

internal class CheckerWatch(
    var blit: Int,
    var size: Int,
    var clause: CheckerClause,
) {
    constructor(b: Int, c: CheckerClause) : this(b, c.size, c)
}

// 'uint64_t nonces[]' -> ULongArray (the 'ExperimentalUnsignedTypes' API).
@OptIn(ExperimentalUnsignedTypes::class)
internal class Checker(
    private var internal: Internal,
) : StatTracer {
    // Capacity of variable values.
    //
    private var sizeVars = 0L

    // For the assignment we want to have an as fast access as possible and
    // thus we use an array which can also be indexed by negative literals and
    // is actually valid in the range [-size_vars+1, ..., size_vars-1].
    //
    private var vals = ByteArray(0)

    // The 'watchers' and 'marks' data structures are not that time critical
    // and thus we access them by first mapping a literal to 'unsigned'.
    //
    private val watchers = ArrayList<ArrayList<CheckerWatch>>() // watchers of literals
    private var marks = ByteArray(0) // mark bits of literals

    private var inconsistent = false // found or added empty clause

    private var numClauses = 0L // number of clauses in hash table
    private var numGarbage = 0L // number of garbage clauses
    private var sizeClauses = 0L // size of clause hash table
    private var clauses = arrayOfNulls<CheckerClause>(0) // hash table of clauses
    private var garbage: CheckerClause? = null // linked list of garbage clauses

    private val unsimplified = IntArrayList() // original clause for reporting
    private val simplified = IntArrayList() // clause for sorting

    private val trail = IntArrayList() // for propagation

    private var nextToPropagate = 0 // next to propagate on trail

    private val nonces = ULongArray(NUM_NONCES) // random numbers for hashing
    private var lastHash = 0uL // last computed hash value of clause
    private var lastId = 0L

    class Stats {
        var added = 0L // number of added clauses
        var original = 0L // number of added original clauses
        var derived = 0L // number of added derived clauses

        var deleted = 0L // number of deleted clauses

        var assumptions = 0L // number of assumed literals
        var propagations = 0L // number of propagated literals

        var insertions = 0L // number of clauses added to hash table
        var collisions = 0L // number of hash collisions in 'find'
        var searches = 0L // number of searched clauses in 'find'

        var checks = 0L // number of implication checks

        var collections = 0L // garbage collections
        var units = 0L
    }

    val stats = Stats()

    /*------------------------------------------------------------------------*/

    private fun l2u(lit: Int): Int {
        check(lit != 0)
        check(lit != Int.MIN_VALUE)
        var res = 2 * (abs(lit) - 1)
        if (lit < 0) res++
        return res
    }

    private fun value(lit: Int): Int {
        check(lit != 0)
        check(lit != Int.MIN_VALUE)
        check(abs(lit) < sizeVars)
        check(vals[(sizeVars + lit).toInt()] == (-vals[(sizeVars - lit).toInt()]).toByte())
        return vals[(sizeVars + lit).toInt()].toInt()
    }

    private fun setVal(lit: Int, v: Int) {
        vals[(sizeVars + lit).toInt()] = v.toByte()
    }

    private fun mark(lit: Int): Boolean {
        val u = l2u(lit)
        check(u < marks.size)
        return marks[u].toInt() != 0
    }

    private fun setMark(lit: Int, b: Boolean) {
        val u = l2u(lit)
        check(u < marks.size)
        marks[u] = if (b) 1 else 0
    }

    private fun watcher(lit: Int): ArrayList<CheckerWatch> {
        val u = l2u(lit)
        check(u < watchers.size)
        return watchers[u]
    }

    /*------------------------------------------------------------------------*/

    private fun newClause(): CheckerClause {
        val size = simplified.size
        check(size > 1)
        val literals = IntArray(size)
        val res = CheckerClause(null, lastHash, size, literals)
        var p = 0
        for (k in 0 until simplified.size) literals[p++] = simplified[k]
        numClauses++

        // First two literals are used as watches and should not be false.
        //
        for (i in 0 until 2) {
            val lit = literals[i]
            if (value(lit) == 0) continue
            for (j in i + 1 until size) {
                val other = literals[j]
                if (value(other) != 0) continue
                literals[i] = other
                literals[j] = lit
                break
            }
        }
        check(value(literals[0]) == 0)
        check(value(literals[1]) == 0)
        watcher(literals[0]).add(CheckerWatch(literals[1], res))
        watcher(literals[1]).add(CheckerWatch(literals[0], res))

        return res
    }

    private fun deleteClause(c: CheckerClause) {
        if (c.size != 0) {
            check(c.size > 1)
            check(numClauses > 0)
            numClauses--
        } else {
            check(numGarbage > 0)
            numGarbage--
        }
        c.next = null // 'delete[] (char *) c'
    }

    private fun enlargeClauses() {
        check(numClauses == sizeClauses)
        val newSizeClauses = if (sizeClauses != 0L) 2 * sizeClauses else 1L
        val newClauses = arrayOfNulls<CheckerClause>(newSizeClauses.toInt())
        for (i in 0 until sizeClauses.toInt()) {
            var c = clauses[i]
            while (c != null) {
                val next = c.next
                val h = reduceHash(c.hash, newSizeClauses).toInt()
                c.next = newClauses[h]
                newClauses[h] = c
                c = next
            }
        }
        clauses = newClauses
        sizeClauses = newSizeClauses
    }

    private fun clauseSatisfied(c: CheckerClause): Boolean {
        for (i in 0 until c.size)
            if (value(c.literals[i]) > 0) return true
        return false
    }

    // The main reason why we have an explicit garbage collection phase is that
    // removing clauses from watcher lists eagerly might lead to an accumulated
    // quadratic algorithm.  Thus we delay removing garbage clauses from watcher
    // lists until garbage collection (even though we remove garbage clauses on
    // the fly during propagation too).  We also remove satisfied clauses.
    //
    private fun collectGarbageClauses() {

        stats.collections++

        for (i in 0 until sizeClauses.toInt()) {
            var prev: CheckerClause? = null // 'p': null = '&clauses[i]', else '&prev->next'
            while (true) {
                val c = (if (prev == null) clauses[i] else prev.next) ?: break
                if (clauseSatisfied(c)) {
                    c.size = 0 // mark as garbage
                    if (prev == null) clauses[i] = c.next else prev.next = c.next
                    c.next = garbage
                    garbage = c
                    numGarbage++
                    check(numClauses > 0)
                    numClauses--
                } else prev = c
            }
        }

        var lit = (-sizeVars + 1).toInt()
        while (lit < sizeVars) {
            if (lit == 0) {
                lit++
                continue
            }
            val ws = watcher(lit)
            val end = ws.size
            var j = 0
            var i = j
            while (i != end) {
                val w = ws[i]
                if (w.clause.size != 0) ws[j++] = w
                i++
            }
            lit++
            if (j == ws.size) continue
            if (j == 0) ws.clear()
            else ws.shrinkTo(j)
        }

        var c = garbage
        while (c != null) {
            val next = c.next
            deleteClause(c)
            c = next
        }

        check(numGarbage == 0L)
        garbage = null
    }

    /*------------------------------------------------------------------------*/

    init {
        // Initialize random number table for hash function.
        //
        val random = Random(42uL)
        for (n in 0 until NUM_NONCES) {
            var nonce = random.next()
            if ((nonce and 1uL) == 0uL) nonce++
            check(nonce != 0uL)
            check((nonce and 1uL) != 0uL)
            nonces[n] = nonce
        }
    }

    override fun connectInternal(internal: Internal) {
        this.internal = internal
    }

    /*------------------------------------------------------------------------*/

    // The simplicity for accessing 'vals' and 'watchers' directly through a
    // signed integer literal, comes with the price of slightly more complex
    // code in deleting and enlarging the checker data structures.

    private fun enlargeVars(idx: Long) {

        check(0 < idx)
        check(idx <= Int.MAX_VALUE)

        var newSizeVars = if (sizeVars != 0L) 2 * sizeVars else 2L
        while (idx >= newSizeVars) newSizeVars *= 2

        val newVals = ByteArray((2 * newSizeVars).toInt())
        if (sizeVars != 0L) // To make sanitizer happy (without '-O').
            vals.copyInto(newVals, (newSizeVars - sizeVars).toInt(), 0, (2 * sizeVars).toInt())
        vals = newVals
        sizeVars = newSizeVars

        watchers.resize((2 * newSizeVars).toInt()) { ArrayList() }
        marks = marks.resized((2 * newSizeVars).toInt())

        check(idx < newSizeVars)
    }

    private fun importLiteral(lit: Int) {
        check(lit != 0)
        check(lit != Int.MIN_VALUE)
        val idx = abs(lit)
        if (idx >= sizeVars) enlargeVars(idx.toLong())
        simplified.add(lit)
        unsimplified.add(lit)
    }

    private fun importClause(c: List<Int>) {
        for (lit in c) importLiteral(lit)
    }

    private fun tautological(): Boolean {
        cxxSort(simplified, LitSmaller)
        val end = simplified.size
        var j = 0
        var prev = 0
        for (i in j until end) {
            val lit = simplified[i]
            if (lit == prev) continue // duplicated literal
            if (lit == -prev) return true // tautological clause
            val tmp = value(lit)
            if (tmp > 0) return true // satisfied literal and clause
            prev = lit
            simplified[j++] = prev
        }
        simplified.shrinkTo(j)
        return false
    }

    /*------------------------------------------------------------------------*/

    private fun computeHash(): ULong {
        val j = (lastId % NUM_NONCES).toInt()
        val tmp = nonces[j] * lastId.toULong()
        lastHash = tmp
        return lastHash
    }

    // 'CheckerClause **': the bucket head 'clauses[h]' (prev == null) or 'prev->next'.
    private inner class Slot(val h: Int, val prev: CheckerClause?) {
        fun get(): CheckerClause? = if (prev == null) clauses[h] else prev.next

        fun set(c: CheckerClause?) {
            if (prev == null) clauses[h] = c else prev.next = c
        }
    }

    private fun find(): Slot {
        stats.searches++
        val hash = computeHash()
        val size = simplified.size
        val h = reduceHash(hash, sizeClauses).toInt()
        for (k in 0 until simplified.size) setMark(simplified[k], true)
        var prev: CheckerClause? = null
        var c = clauses[h]
        while (c != null) {
            if (c.hash == hash && c.size == size) {
                var found = true
                val literals = c.literals
                var i = 0
                while (found && i != size) {
                    found = mark(literals[i])
                    i++
                }
                if (found) break
            }
            stats.collisions++
            prev = c
            c = c.next
        }
        for (k in 0 until simplified.size) setMark(simplified[k], false)
        return Slot(h, prev)
    }

    private fun insert() {
        stats.insertions++
        if (numClauses == sizeClauses) enlargeClauses()
        val h = reduceHash(computeHash(), sizeClauses).toInt()
        val c = newClause()
        c.next = clauses[h]
        clauses[h] = c
    }

    /*------------------------------------------------------------------------*/

    private fun assign(lit: Int) {
        check(value(lit) == 0)
        setVal(lit, 1)
        setVal(-lit, -1)
        trail.add(lit)
    }

    private fun assume(lit: Int) {
        val tmp = value(lit)
        if (tmp > 0) return
        check(tmp == 0)
        stats.assumptions++
        assign(lit)
    }

    private fun backtrack(previouslyPropagated: Int) {

        check(previouslyPropagated <= trail.size)

        while (trail.size > previouslyPropagated) {
            val lit = trail.back()
            check(value(lit) > 0)
            check(value(-lit) < 0)
            setVal(lit, 0)
            setVal(-lit, 0)
            trail.removeLast()
        }

        trail.resize(previouslyPropagated)
        nextToPropagate = previouslyPropagated
        check(trail.size == nextToPropagate)
    }

    /*------------------------------------------------------------------------*/

    // This is a standard propagation routine without using blocking literals
    // nor without saving the last replacement position.

    private fun propagate(): Boolean {
        var res = true
        while (res && nextToPropagate < trail.size) {
            val lit = trail[nextToPropagate++]
            stats.propagations++
            check(value(lit) > 0)
            check(abs(lit) < sizeVars)
            val ws = watcher(-lit)
            val end = ws.size
            var j = 0
            var i = j
            while (res && i != end) {
                val w = ws[i]
                ws[j++] = w
                i++ // 'i++' of the for loop, done here so 'continue' keeps it
                val blit = w.blit
                check(blit != -lit)
                val blitVal = value(blit)
                if (blitVal > 0) continue
                val size = w.size
                if (size == 2) { // not precise since
                    if (blitVal < 0) res = false // clause might be garbage
                    else assign(w.blit) // but still sound
                } else {
                    check(size > 2)
                    val c = w.clause
                    if (c.size == 0) {
                        j--
                        continue
                    } // skip garbage clauses
                    check(size == c.size)
                    val lits = c.literals
                    val other = lits[0] xor lits[1] xor (-lit)
                    check(other != -lit)
                    val otherVal = value(other)
                    if (otherVal > 0) {
                        ws[j - 1].blit = other
                        continue
                    }
                    lits[0] = other
                    lits[1] = -lit
                    var k = 2
                    var replacement: Int
                    var replacementVal = -1
                    while (k < size) {
                        replacement = lits[k]
                        replacementVal = value(replacement)
                        if (replacementVal >= 0) break
                        k++
                    }
                    if (replacementVal >= 0) {
                        val r = lits[k]
                        watcher(r).add(CheckerWatch(-lit, c))
                        lits[k] = lits[1]
                        lits[1] = r
                        j--
                    } else if (otherVal == 0) assign(other)
                    else res = false
                }
            }
            while (i != end) ws[j++] = ws[i++]
            ws.shrinkTo(j)
        }
        return res
    }

    // 'bool Checker::check ()'.
    private fun checkImplied(): Boolean {
        stats.checks++
        if (inconsistent) return true
        val previouslyPropagated = nextToPropagate
        for (k in 0 until simplified.size) assume(-simplified[k])
        val res = !propagate()
        backtrack(previouslyPropagated)
        return res
    }

    /*------------------------------------------------------------------------*/

    private fun addClause() {

        // If there are enough garbage clauses collect them first.
        if (numGarbage.toDouble() > 0.5 * max(sizeClauses, sizeVars).toDouble())
            collectGarbageClauses()

        var unit = 0
        for (k in 0 until simplified.size) {
            val lit = simplified[k]
            val tmp = value(lit)
            if (tmp < 0) continue
            check(tmp == 0)
            if (unit != 0) {
                unit = Int.MIN_VALUE
                break
            }
            unit = lit
        }

        if (simplified.isEmpty()) {
            inconsistent = true
        }
        if (unit == 0) {
            inconsistent = true
        } else if (unit != Int.MIN_VALUE) {
            assign(unit)
            stats.units++
            if (!propagate()) {
                inconsistent = true
            }
        } else insert()
    }

    override fun addOriginalClause(id: Long, redundant: Boolean, clause: List<Int>, restored: Boolean) {
        if (inconsistent) return
        stats.added++
        stats.original++
        importClause(clause)
        lastId = id
        if (tautological()) {
            // ignoring satisfied original clause
        } else addClause()
        simplified.clear()
        unsimplified.clear()
    }

    override fun addDerivedClause(id: Long, redundant: Boolean, clause: List<Int>, antecedents: List<Long>) {
        if (inconsistent) return
        stats.added++
        stats.derived++
        importClause(clause)
        lastId = id
        if (tautological()) {
            // ignoring satisfied derived clause
        } else if (!checkImplied()) {
            error("failed to check derived clause:\n${litsLine(unsimplified)}")
        } else addClause()
        simplified.clear()
        unsimplified.clear()
    }

    /*------------------------------------------------------------------------*/

    override fun deleteClause(id: Long, redundant: Boolean, clause: List<Int>) {
        if (inconsistent) return
        stats.deleted++
        simplified.clear() // Can be non-empty if clause allocation fails.
        unsimplified.clear() // Can be non-empty if clause allocation fails.
        importClause(clause)
        lastId = id
        if (!tautological()) {
            val p = find()
            val d = p.get()
            if (d != null) {
                check(d.size > 1)
                // Remove from hash table, mark as garbage, connect to garbage list.
                numGarbage++
                check(numClauses > 0)
                numClauses--
                p.set(d.next)
                d.next = garbage
                garbage = d
                d.size = 0
            } else {
                error("deleted clause not in proof:\n${litsLine(unsimplified)}")
            }
        }
        simplified.clear()
        unsimplified.clear()
    }

    override fun addAssumptionClause(id: Long, clause: List<Int>, antecedents: List<Long>) {
        addDerivedClause(id, true, clause, antecedents)
        deleteClause(id, true, clause)
    }

    override fun finalizeClause(id: Long, clause: List<Int>) {} // skip

    override fun reportStatus(status: Int, id: Long) {} // skip

    override fun beginProof(id: Long) {} // skip

    override fun printStats() {} // stats.cpp: messages only

    private companion object {
        const val NUM_NONCES = 4

        val LitSmaller = IntLess { a, b ->
            val c = abs(a)
            val d = abs(b)
            if (c < d) true
            else if (c > d) false
            else a < b
        }

        // Reduce hash value to the actual size.
        //
        fun reduceHash(hash: ULong, size: Long): ULong {
            check(size > 0)
            var shift = 32
            var res = hash
            while ((1uL shl shift) > size.toULong()) {
                res = res xor (res shr shift)
                shift = shift shr 1
            }
            res = res and (size.toULong() - 1uL)
            check(res < size.toULong())
            return res
        }

        // The 'fprintf (stderr, "%d ", lit)' loop plus 'fputc ('0', stderr)'.
        fun litsLine(lits: IntArrayList): String {
            val sb = StringBuilder()
            for (k in 0 until lits.size) sb.append(lits[k]).append(' ')
            sb.append('0')
            return sb.toString()
        }
    }
}
