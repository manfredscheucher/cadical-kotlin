package org.bytefred.ksat.cadical.full

import kotlin.math.abs
import kotlin.math.max
import org.bytefred.ksat.cadical.IntArrayList

/*
 * lratbuilder.hpp + lratbuilder.cpp: builds LRAT proof chains for derived clauses by
 * propagation ('opts.externallrat'), a special tracer connected with 'Proof::connect'.
 *
 * Mapping as in Checker.kt. 'LratBuilderClause' -> a class holding an IntArray;
 * 'LratBuilderWatch' -> a class (reference copies in the compaction loops, see Checker.kt);
 * 'reasons' / 'unit_reasons' -> ArrayLists of nullable clauses, 'vector<bool>' ->
 * BooleanArray, all indexed by 'l2a (lit)'. 'add_clause_get_proof' returns [chain] itself
 * (upstream returns a reference to it; 'Proof' copies it). The 'assumption' pseudo clause
 * is a clause object with size 0 and id 0. 'fatal_message_*' -> 'error'. 'print_stats' is
 * declared but never defined upstream and 'dump' only prints (debugging): not ported.
 */
internal class LratBuilderClause(
    var next: LratBuilderClause?, // collision chain link for hash table
    var hash: ULong, // previously computed full 64-bit hash
    var id: Long, // id of clause
    var garbage: Boolean, // for garbage clauses
    val size: Int,
    val literals: IntArray, // 'literals' of length 'size'
)

internal class LratBuilderWatch(
    var blit: Int,
    var size: Int,
    var clause: LratBuilderClause,
) {
    constructor(b: Int, c: LratBuilderClause) : this(b, c.size, c)
}

// 'uint64_t nonces[]' -> ULongArray (the 'ExperimentalUnsignedTypes' API).
@OptIn(ExperimentalUnsignedTypes::class)
internal class LratBuilder(
    private val internal: Internal,
) {
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
    private val watchers = ArrayList<ArrayList<LratBuilderWatch>>() // watchers of literals
    private var marks = ByteArray(0) // mark bits of literals

    private val reasons = ArrayList<LratBuilderClause?>() // reason for each assignment
    private val unitReasons = ArrayList<LratBuilderClause?>() // units get preferred
    private var justified = BooleanArray(0)
    private var todoJustify = BooleanArray(0)
    private var checkedLits = ByteArray(0) // this is implemented same as marks
    private var conflict: LratBuilderClause? = null
    private val chain = ArrayList<Long>() // LRAT style proof chain
    private val reverseChain = ArrayList<Long>()
    private val inconsistentChain = ArrayList<Long>() // store proof to reuse
    private var unjustified = 0 // number of lits to justify

    private var newClauseTaut = false
    private var inconsistent = false // found or added empty clause

    private var numClauses = 0L // number of clauses in hash table
    private var numGarbage = 0L // number of garbage clauses
    private var sizeClauses = 0L // size of clause hash table
    private var clauses = arrayOfNulls<LratBuilderClause>(0) // hash table of clauses
    private var garbage: LratBuilderClause? = null // linked list of garbage clauses

    private val unsimplified = IntArrayList() // original clause for reporting
    private val simplified = IntArrayList() // clause for sorting

    private val trail = IntArrayList() // for propagation

    private var nextToPropagate = 0 // next to propagate on trail

    private val assumption: LratBuilderClause
    private var inconsistentClause: LratBuilderClause? = null
    private val unitClauses = ArrayList<LratBuilderClause>() // we need this because propagate
    // cannot propagate unit clauses

    private val nonces = ULongArray(NUM_NONCES) // random numbers for hashing
    private var lastHash = 0uL // last computed hash value of clause
    private var lastId = 0L // id of the last added clause

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

    private fun l2a(lit: Int): Int {
        check(lit != 0)
        check(lit != Int.MIN_VALUE)
        val res = abs(lit)
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

    private fun watcher(lit: Int): ArrayList<LratBuilderWatch> {
        val u = l2u(lit)
        check(u < watchers.size)
        return watchers[u]
    }

    /*------------------------------------------------------------------------*/
    private fun newClause(): LratBuilderClause {
        val size = simplified.size
        val literals = IntArray(size)
        val res = LratBuilderClause(null, lastHash, lastId, false, size, literals)
        numClauses++
        var p = 0
        for (k in 0 until simplified.size) literals[p++] = simplified[k]

        if (size == 0) {
            return res
        }
        if (size == 1) {
            unitClauses.add(res)
            return res
        }

        // First two literals are used as watches and should not be false.
        // or at least one should be true. But we can have falsified clauses
        // then we cannot guarantee anything here.
        //
        for (i in 0 until 2) {
            val lit = literals[i]
            if (value(lit) >= 0) continue
            for (j in i + 1 until size) {
                val other = literals[j]
                if (value(other) < 0) continue
                literals[i] = other
                literals[j] = lit
                break
            }
        }

        // make sure the clause is not tautological
        if (!newClauseTaut) {
            watcher(literals[0]).add(LratBuilderWatch(literals[1], res))
            watcher(literals[1]).add(LratBuilderWatch(literals[0], res))
        }
        return res
    }

    private fun deleteClause(c: LratBuilderClause) {
        if (!c.garbage) {
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
        val newClauses = arrayOfNulls<LratBuilderClause>(newSizeClauses.toInt())
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

    private fun clauseSatisfied(c: LratBuilderClause): Boolean {
        for (i in 0 until c.size)
            if (value(c.literals[i]) > 0) return true
        return false
    }

    private fun clauseFalsified(c: LratBuilderClause): Boolean {
        for (i in 0 until c.size)
            if (value(c.literals[i]) >= 0) return false
        return true
    }

    // The main reason why we have an explicit garbage collection phase is that
    // removing clauses from watcher lists eagerly might lead to an accumulated
    // quadratic algorithm.  Thus we delay removing garbage clauses from watcher
    // lists until garbage collection (even though we remove garbage clauses on
    // the fly during propagation too).  We also remove satisfied clauses.
    //
    // Problem: this should only happen in DRAT not in lrat!! Done.
    //
    private fun collectGarbageClauses() {

        stats.collections++

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
                if (!w.clause.garbage) ws[j++] = w
                i++
            }
            lit++
            if (j == ws.size) continue
            if (j == 0) ws.clear()
            else ws.shrinkTo(j)
        }

        val end = unitClauses.size
        var j = 0
        for (i in j until end) {
            val c = unitClauses[i]
            if (c.garbage) continue // garbage clause
            unitClauses[j++] = c
        }
        unitClauses.shrinkTo(j)

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

        assumption = LratBuilderClause(null, 0uL, 0L, false, 0, IntArray(0)) // assumption clause
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

        reasons.resize(newSizeVars.toInt()) { null }
        unitReasons.resize(newSizeVars.toInt()) { null }
        justified = justified.copyOf(newSizeVars.toInt())
        todoJustify = todoJustify.copyOf(newSizeVars.toInt())
        // Upstream resets the new entries in a loop from 'size_vars', which
        // was already set to 'new_size_vars' (no iteration); 'resize' zeroes them anyway.

        watchers.resize((2 * newSizeVars).toInt()) { ArrayList() }
        marks = marks.resized((2 * newSizeVars).toInt())
        checkedLits = checkedLits.resized((2 * newSizeVars).toInt())

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

    private fun tautological() {
        cxxSort(simplified, LitSmaller)
        val end = simplified.size
        var j = 0
        var prev = 0
        for (i in j until end) {
            val lit = simplified[i]
            if (lit == prev) continue // duplicated literal
            if (lit == -prev) {
                newClauseTaut = true
                return
            } // tautological clause
            prev = lit
            simplified[j++] = prev // which means we don't care
        }
        simplified.shrinkTo(j)
    }

    /*------------------------------------------------------------------------*/

    private fun computeHash(id: Long): ULong {
        check(id > 0)
        val j = (id % NUM_NONCES).toInt() // Don't know if this is a good
        val tmp = nonces[j] * id.toULong() // hash function or even better
        lastHash = tmp // than just using id.
        return lastHash
    }

    // 'LratBuilderClause **': the bucket head 'clauses[h]' (prev == null) or 'prev->next'.
    private inner class Slot(val h: Int, val prev: LratBuilderClause?) {
        fun get(): LratBuilderClause? = if (prev == null) clauses[h] else prev.next

        fun set(c: LratBuilderClause?) {
            if (prev == null) clauses[h] = c else prev.next = c
        }
    }

    private fun find(id: Long): Slot {
        stats.searches++
        val hash = computeHash(id)
        val h = reduceHash(hash, sizeClauses).toInt()
        var prev: LratBuilderClause? = null
        var c = clauses[h]
        while (c != null) {
            if (c.hash == hash && c.id == id) {
                break
            }
            stats.collisions++
            prev = c
            c = c.next
        }
        return Slot(h, prev)
    }

    private fun insert(): LratBuilderClause {
        stats.insertions++
        if (numClauses == sizeClauses) enlargeClauses()
        val h = reduceHash(computeHash(lastId), sizeClauses).toInt()
        val c = newClause()
        c.next = clauses[h]
        clauses[h] = c
        return c
    }

    /*------------------------------------------------------------------------*/

    private fun assign(lit: Int) {
        check(value(lit) == 0) // cannot guarantee (!val (lit)) anymore :/ -> yes we can!
        setVal(lit, 1)
        setVal(-lit, -1)
        trail.add(lit)
    }

    private fun assume(lit: Int) {
        val tmp = value(lit)
        if (tmp > 0) return
        check(tmp == 0)
        reasons[l2a(lit)] = assumption
        stats.assumptions++
        assign(lit)
    }

    private fun assignReason(lit: Int, reasonClause: LratBuilderClause) {
        check(reasons[l2a(lit)] == null)
        reasons[l2a(lit)] = reasonClause
        assign(lit)
    }

    private fun unassignReason(lit: Int) {
        check(reasons[l2a(lit)] != null)
        reasons[l2a(lit)] = null
        check(value(lit) > 0)
        check(value(-lit) < 0)
        setVal(lit, 0)
        setVal(-lit, 0)
    }

    private fun backtrack(previouslyPropagated: Int) {

        check(previouslyPropagated <= trail.size)

        while (trail.size > previouslyPropagated) {
            val lit = trail.back()
            unassignReason(lit)
            trail.removeLast()
        }

        trail.resize(previouslyPropagated)
        nextToPropagate = previouslyPropagated
        check(trail.size == nextToPropagate)
    }

    /*------------------------------------------------------------------------*/

    private fun unitPropagate(): Boolean {
        val end = unitClauses.size
        var res = true
        var j = 0
        var i = j
        while (res && i != end) {
            val c = unitClauses[i]
            unitClauses[j++] = c
            i++ // 'i++' of the for loop, done here so 'continue' keeps it
            if (c.garbage) {
                j--
                continue
            } // skip garbage clauses
            check(c.size == 1)
            val lit = c.literals[0]
            val value = value(lit)
            if (value > 0) continue
            else if (value == 0) assignReason(c.literals[0], c)
            else {
                res = false
                conflict = c
            }
        }
        while (i != end) unitClauses[j++] = unitClauses[i++]
        unitClauses.shrinkTo(j)
        return res
    }

    // This is a standard propagation routine without using blocking literals
    // nor without saving the last replacement position.
    private fun propagate(): Boolean {
        var res = unitPropagate()
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
                if (w.clause.garbage) {
                    j--
                    continue
                } // skip garbage clauses
                check(w.size == w.clause.size)
                val blit = w.blit
                check(blit != -lit)
                val blitVal = value(blit)
                if (blitVal > 0) continue
                val size = w.size
                if (size == 1) { // should not happen
                    if (blitVal < 0) {
                        res = false
                        conflict = w.clause
                    } else assignReason(w.blit, w.clause)
                } else if (size == 2) {
                    if (blitVal < 0) {
                        res = false
                        conflict = w.clause
                    } else assignReason(w.blit, w.clause)
                } else {
                    check(size > 2)
                    val c = w.clause
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
                    var replacementVal = -1
                    while (k < size) {
                        replacementVal = value(lits[k])
                        if (replacementVal >= 0) break
                        k++
                    }
                    if (replacementVal >= 0) {
                        val replacement = lits[k]
                        watcher(replacement).add(LratBuilderWatch(-lit, c))
                        lits[k] = lits[1]
                        lits[1] = replacement
                        j--
                    } else if (otherVal == 0) assignReason(other, c)
                    else {
                        res = false
                        conflict = c
                    }
                }
            }
            while (i != end) ws[j++] = ws[i++]
            ws.shrinkTo(j)
        }
        return res
    }

    private fun constructChain() {
        for (p in trail.size - 1 downTo 0) {
            if (unjustified == 0) break
            val lit = trail[p]
            if (!todoJustify[l2a(lit)]) {
                continue
            }
            if (justified[l2a(lit)]) {
                unjustified-- // one of the todo_justify lits justified
                continue
            }
            justified[l2a(lit)] = true
            unjustified-- // one of the todo_justify lits justified
            var reasonClause = unitReasons[l2a(lit)]
            if (reasonClause == null) reasonClause = reasons[l2a(lit)]
            check(reasonClause != null)
            check(!reasonClause.garbage)
            reverseChain.add(reasonClause.id)
            val rp = reasonClause.literals
            for (i in 0 until reasonClause.size) {
                val reasonLit = rp[i]
                if (todoJustify[l2a(reasonLit)]) {
                    continue
                }
                if (justified[l2a(reasonLit)]) {
                    continue
                }
                unjustified++ // new todo_justify means unjustified increase
                todoJustify[l2a(reasonLit)] = true
            }
        }
        check(unjustified == 0)
        for (p in reverseChain.size - 1 downTo 0) {
            check(reverseChain[p] != 0L)
            chain.add(reverseChain[p])
        }
    }

    private fun proofTautologicalClause() {
        // tautological clause needs no proof
    }

    private fun proofSatisfiedLiteral(lit: Int) {
        unjustified = 1 // is always > 0 if we have work to do
        todoJustify[l2a(lit)] = true
        constructChain()
    }

    private fun proofInconsistentClause() {
        if (inconsistentChain.size != 0) {
            for (id in inconsistentChain) {
                chain.add(id)
            }
            return
        }

        val inconsistentClause = inconsistentClause!!
        unjustified = inconsistentClause.size // is always > 0 if we have work to do
        val end = inconsistentClause.size
        for (i in 0 until end) {
            val lit = inconsistentClause.literals[i]
            todoJustify[l2a(lit)] = true
        }
        reverseChain.add(inconsistentClause.id)
        constructChain()
        for (id in chain) {
            inconsistentChain.add(id)
        }
    }

    private fun proofClause() {
        // marking clause as justified
        for (k in 0 until simplified.size) {
            justified[l2a(simplified[k])] = true
        }
        val conflict = conflict!!
        unjustified = conflict.size // is always > 0 if we have work to do
        val end = conflict.size
        for (i in 0 until end) {
            val lit = conflict.literals[i]
            todoJustify[l2a(lit)] = true
        }
        reverseChain.add(conflict.id)
        constructChain()
    }

    private fun buildChainIfPossible(): Boolean {
        stats.checks++

        chain.clear()

        if (newClauseTaut) {
            proofTautologicalClause()
            return true
        }

        reverseChain.clear()
        for (i in justified.indices) justified[i] = false
        for (i in todoJustify.indices) todoJustify[i] = false

        if (inconsistent) {
            check(inconsistentClause != null)
            proofInconsistentClause()
            return true
        }
        val previouslyPropagated = nextToPropagate
        val previousTrailSize = trail.size

        for (k in 0 until simplified.size) {
            val lit = simplified[k]
            if (value(lit) > 0) {
                backtrack(previousTrailSize)
                nextToPropagate = previouslyPropagated
                proofSatisfiedLiteral(lit)
                return true
            } else if (value(lit) == 0) {
                assume(-lit)
            }
        }
        if (propagate()) {
            backtrack(previousTrailSize)
            nextToPropagate = previouslyPropagated
            return false
        }

        proofClause()

        backtrack(previousTrailSize)
        nextToPropagate = previouslyPropagated

        return true
    }

    /*------------------------------------------------------------------------*/

    private fun clean() {
        simplified.clear()
        unsimplified.clear()
        newClauseTaut = false
        conflict = null
    }

    private fun addClause() {

        // If there are enough garbage clauses collect them.
        if (numGarbage.toDouble() > 0.5 * max(sizeClauses, sizeVars).toDouble())
            collectGarbageClauses()

        val c = insert()
        if (inconsistent) {
            return
        }

        val size = c.size
        val sat = clauseSatisfied(c)
        var unit = 0
        if (!sat) {
            val p = c.literals
            for (i in 0 until size) {
                val lit = p[i]
                if (value(lit) == 0) {
                    if (unit != 0) {
                        unit = Int.MIN_VALUE
                        break
                    }
                    unit = lit
                }
            }
        }
        if (size == 1) {
            if (value(c.literals[0]) == 0) unitReasons[l2a(c.literals[0])] = c
        }
        if (size == 0) {
            inconsistent = true
            inconsistentClause = c
        } else if (sat) {
            // added and checked satisfied clause
        } else if (unit == 0) {
            inconsistent = true
            inconsistentClause = c
        } else if (unit == Int.MIN_VALUE) {
            // added and checked non unit clause
        } else {
            stats.units++
            assignReason(unit, c)
            if (!propagate()) {
                inconsistent = true
                inconsistentClause = conflict
                check(clauseFalsified(conflict!!))
            }
        }
    }

    /*------------------------------------------------------------------------*/

    fun addOriginalClause(id: Long, c: List<Int>) {
        stats.added++
        stats.original++
        importClause(c)
        lastId = id
        check(id != 0L)
        check(!newClauseTaut)
        tautological()
        addClause()
        clean()
    }

    fun addClauseGetProof(id: Long, c: List<Int>): List<Long> {
        stats.added++
        stats.derived++
        importClause(c)
        lastId = id
        check(id != 0L)
        check(!newClauseTaut)
        tautological()

        val res = buildChainIfPossible()
        if (!res) {
            error("failed to build chain for clause:\n${litsLine(unsimplified)}")
        } else addClause()
        clean()
        return chain
    }

    fun addDerivedClause(id: Long, c: List<Int>) {
        stats.added++
        importClause(c)
        lastId = id
        check(id != 0L)
        check(!newClauseTaut)
        tautological()
        addClause()
        clean()
    }

    fun deleteClause(id: Long, c: List<Int>) {
        stats.deleted++
        importClause(c)
        lastId = id
        tautological()
        val p = find(id)
        val d = p.get()
        if (d != null) {
            // TODO: marks should only be defined and used in debugging mode
            for (k in 0 until simplified.size) setMark(simplified[k], true)
            var unit = 0
            val dp = d.literals
            for (i in 0 until d.size) {
                val lit = dp[i]
                check(mark(lit))
                val reason = reasons[l2a(lit)]
                if (reason === d) {
                    check(value(lit) != 0)
                    check(unit == 0)
                    unit = lit
                }
            }
            for (k in 0 until simplified.size) setMark(simplified[k], false)

            // Remove from hash table, mark as garbage, connect to garbage list.
            numGarbage++
            check(numClauses > 0)
            numClauses--
            p.set(d.next)
            d.next = garbage
            garbage = d
            d.garbage = true

            if (d.size == 1) {
                val l = l2a(d.literals[0])
                if (unitReasons[l] === d) {
                    unitReasons[l] = null
                }
            }

            // we propagated unit with the deleted clause as reason. To ensure
            // topological order of the trail we have to backtrack (and repropagate)
            // usually unit should be implied by some other clause otherwise
            // deleting this clause does not really makes sense.
            //
            if (unit != 0) {
                while (trail.size != 0) {
                    val tlit = trail.back()
                    if (tlit == unit) break
                    unassignReason(tlit)
                    trail.removeLast()
                }
                check(trail.size != 0)
                unassignReason(unit)
                trail.removeLast()
            }
            if (unit != 0 || (inconsistent && inconsistentClause!!.id == d.id)) {
                inconsistentChain.clear()
                nextToPropagate = 0
                val res = propagate()
                check(res || inconsistent)
                if (!res) {
                    inconsistent = true
                    inconsistentClause = conflict
                } else if (inconsistent) {
                    inconsistent = false
                    inconsistentClause = null
                }
            }
        } else {
            error("deleted clause not in proof:\n${litsLine(unsimplified)}")
        }
        clean()
    }

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
