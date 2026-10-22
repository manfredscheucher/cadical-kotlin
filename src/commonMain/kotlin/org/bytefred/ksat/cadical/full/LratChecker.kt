package org.bytefred.ksat.cadical.full

import kotlin.math.abs
import kotlin.math.max

/*
 * lratchecker.hpp + lratchecker.cpp: the online LRUP checker ('opts.checkproof' 2 or 3,
 * requires 'opts.check'), checking the LRAT chains of derived clauses.
 *
 * Mapping as in Checker.kt. 'LratCheckerClause' -> a class holding an IntArray;
 * 'checked_lits' / 'marks' -> ByteArray indexed by 'l2u (lit)'; 'unordered_map<uint64_t,
 * vector<int>> clauses_to_reconstruct' -> HashMap (lookups only, never iterated);
 * 'check (vector<uint64_t>)' -> [checkChain]; 'std::find' on vectors -> 'contains'.
 * The by-value 'vector<uint64_t>' parameters of 'check' / 'check_resolution' are only read,
 * so the chain list is passed as is.
 */
internal class LratCheckerClause(
    var next: LratCheckerClause?, // collision chain link for hash table
    var hash: ULong, // previously computed full 64-bit hash
    var id: Long, // id of clause
    var garbage: Boolean, // for garbage clauses
    val size: Int,
    var used: Boolean,
    var tautological: Boolean,
    val literals: IntArray, // 'literals' of length 'size'
)

internal class LratChecker(
    private var internal: Internal?,
) : StatTracer {
    // Capacity of variable values.
    //
    private var sizeVars = 0L

    private var strictLrat = false

    private var checkedLits = ByteArray(0)
    private var marks = ByteArray(0) // mark bits of literals

    private val clausesToReconstruct = HashMap<Long, List<Int>>()
    private val assumptions = ArrayList<Int>()
    private val constraint = ArrayList<Int>()
    private var concluded = false

    private var numClauses = 0L // number of clauses in hash table
    private var numFinalized = 0L
    private var numGarbage = 0L // number of garbage clauses
    private var sizeClauses = 0L // size of clause hash table
    private var clauses = arrayOfNulls<LratCheckerClause>(0) // hash table of clauses
    private var garbage: LratCheckerClause? = null // linked list of garbage clauses

    private val importedClause = ArrayList<Int>() // original clause for reporting
    private val assumptionClauses = ArrayList<Long>()

    private val nonces = ULongArray(NUM_NONCES) // random numbers for hashing
    private var lastHash = 0uL // last computed hash value of clause
    private var lastId = 0L // id of the last added/deleted clause
    private var currentId = 0L // id of the last added clause

    class Stats {
        var added = 0L // number of added clauses
        var original = 0L // number of added original clauses
        var derived = 0L // number of added derived clauses

        var deleted = 0L // number of deleted clauses
        var finalized = 0L // number of finalized clauses

        var insertions = 0L // number of clauses added to hash table
        var collisions = 0L // number of hash collisions in 'find'
        var searches = 0L // number of searched clauses in 'find'

        var checks = 0L // number of implication checks

        var collections = 0L // garbage collections
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

    private fun checkedLit(lit: Int): Boolean {
        val u = l2u(lit)
        check(u < checkedLits.size)
        return checkedLits[u].toInt() != 0
    }

    private fun setCheckedLit(lit: Int, b: Boolean) {
        val u = l2u(lit)
        check(u < checkedLits.size)
        checkedLits[u] = if (b) 1 else 0
    }

    /*------------------------------------------------------------------------*/

    private fun newClause(): LratCheckerClause {
        val size = importedClause.size
        val literals = IntArray(size)
        val res = LratCheckerClause(null, lastHash, lastId, false, size, false, false, literals)
        var p = 0
        checkedLits.fill(0)
        for (lit in importedClause) {
            literals[p++] = lit
            setCheckedLit(-lit, true)
            if (checkedLit(lit)) {
                res.tautological = true
            }
        }
        for (lit in importedClause) setCheckedLit(-lit, false)
        numClauses++

        return res
    }

    private fun deleteClause(c: LratCheckerClause) {
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
        val newClauses = arrayOfNulls<LratCheckerClause>(newSizeClauses.toInt())
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

    // Probably not necessary since we have no watches.
    //
    private fun collectGarbageClauses() {

        stats.collections++

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

        strictLrat = internal?.lrat ?: false
    }

    override fun connectInternal(internal: Internal) {
        this.internal = internal
        strictLrat = internal.lrat
    }

    /*------------------------------------------------------------------------*/

    private fun enlargeVars(idx: Long) {

        check(0 < idx)
        check(idx <= Int.MAX_VALUE)

        var newSizeVars = if (sizeVars != 0L) 2 * sizeVars else 2L
        while (idx >= newSizeVars) newSizeVars *= 2

        marks = marks.resized((2 * newSizeVars).toInt())
        checkedLits = checkedLits.resized((2 * newSizeVars).toInt())

        check(idx < newSizeVars)
        sizeVars = newSizeVars
    }

    private fun importLiteral(lit: Int) {
        check(lit != 0)
        check(lit != Int.MIN_VALUE)
        val idx = abs(lit)
        if (idx >= sizeVars) enlargeVars(idx.toLong())
        importedClause.add(lit)
    }

    private fun importClause(c: List<Int>) {
        for (lit in c) importLiteral(lit)
    }

    /*------------------------------------------------------------------------*/

    private fun computeHash(id: Long): ULong {
        check(id > 0)
        val j = (id % NUM_NONCES).toInt() // Don't know if this is a good
        val tmp = nonces[j] * id.toULong() // hash function or even better
        lastHash = tmp // than just using id.
        return lastHash
    }

    // 'LratCheckerClause **': the bucket head 'clauses[h]' (prev == null) or 'prev->next'.
    private inner class Slot(val h: Int, val prev: LratCheckerClause?) {
        fun get(): LratCheckerClause? = if (prev == null) clauses[h] else prev.next

        fun set(c: LratCheckerClause?) {
            if (prev == null) clauses[h] = c else prev.next = c
        }
    }

    private fun find(id: Long): Slot {
        stats.searches++
        val hash = computeHash(id)
        val h = reduceHash(hash, sizeClauses).toInt()
        var prev: LratCheckerClause? = null
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

    private fun insert() {
        stats.insertions++
        if (numClauses == sizeClauses) enlargeClauses()
        val h = reduceHash(computeHash(lastId), sizeClauses).toInt()
        val c = newClause()
        c.next = clauses[h]
        clauses[h] = c
    }

    /*------------------------------------------------------------------------*/

    // TODO "strict" resolution check instead of rup check
    private fun checkResolution(proofChain: List<Long>): Boolean {
        if (proofChain.isEmpty()) { // ignore these case TODO chain.size == 1?
            return true
        }
        if (strictLrat) { // ignore this case
            return true
        }
        checkedLits.fill(0) // clearing checking bits
        var c = find(proofChain.last()).get()
        check(c != null)
        for (i in 0 until c.size) {
            val lit = c.literals[i]
            setCheckedLit(lit, true)
            check(!checkedLit(-lit))
        }
        for (p in proofChain.size - 2 downTo 0) {
            val id = proofChain[p]
            c = find(id).get()
            check(c != null) // since this is checked in check already
            for (i in 0 until c.size) {
                val lit = c.literals[i]
                if (!checkedLit(-lit)) setCheckedLit(lit, true)
                else setCheckedLit(-lit, false)
            }
        }
        for (lit in importedClause) {
            if (checkedLit(-lit)) {
                return false
            }
            if (!checkedLit(lit)) {
                // learned clause is subsumed by resolvents
                setCheckedLit(lit, true)
            }
            setCheckedLit(-lit, true)
        }
        var lit = 1L
        while (lit < sizeVars) {
            var ok = checkedLit(lit.toInt()) && checkedLit(-lit.toInt())
            ok = ok || (!checkedLit(lit.toInt()) && !checkedLit(-lit.toInt()))
            if (!ok) {
                return false
            }
            lit++
        }

        return true
    }

    /*------------------------------------------------------------------------*/

    // 'bool LratChecker::check (vector<uint64_t> proof_chain)'.
    private fun checkChain(proofChain: List<Long>): Boolean {
        stats.checks++
        // assert (proof_chain.size ());             // this might be attempting
        // to
        checkedLits.fill(0) // assert here but fails for
        for (lit in importedClause) { // tautological clauses
            setCheckedLit(-lit, true)
            if (checkedLit(lit)) {
                check(proofChain.isEmpty()) // would be unnecessary hence a bug
                return true
            }
        }
        check(proofChain.isNotEmpty()) // but we can assert it here :)

        val usedClauses = ArrayList<LratCheckerClause>()
        var checking = false
        for (id in proofChain) {
            val c = find(id).get() ?: break
            if (c.tautological) {
                break
            }
            usedClauses.add(c)
            if (c.used) {
                break // mostly fuzzed and debugged :)
            } else c.used = true
            var unit = 0
            for (i in 0 until c.size) {
                val lit = c.literals[i]
                if (checkedLit(-lit)) continue
                if (unit != 0 && unit != lit) {
                    unit = Int.MIN_VALUE // multiple unfalsified literals
                    break
                }
                unit = lit // potential unit
            }
            if (unit == Int.MIN_VALUE) {
                break
            }
            if (unit == 0) {
                checking = true
                break
            }
            setCheckedLit(unit, true)
        }
        for (lc in usedClauses) {
            lc.used = false
        }
        if (!checking) {
            return false // check failed because no empty clause was found
        }
        return true
    }

    /*------------------------------------------------------------------------*/

    override fun addOriginalClause(id: Long, redundant: Boolean, clause: List<Int>, restored: Boolean) {
        if (restored) restoreClause(id, clause)
        stats.added++
        stats.original++
        importClause(clause)
        lastId = id
        if (!restored && id == 1 + currentId) currentId = id

        if (sizeClauses != 0L && !restored) {
            val d = find(id).get()
            if (d != null) {
                error("different clause with id $id already present\n")
            }
        }
        check(id != 0L)
        insert()
        importedClause.clear()
    }

    override fun addDerivedClause(id: Long, redundant: Boolean, clause: List<Int>, antecedents: List<Long>) {
        stats.added++
        stats.derived++
        importClause(clause)
        lastId = id
        check(id == currentId + 1)
        currentId = id
        if (sizeClauses != 0L) {
            val d = find(id).get()
            if (d != null) {
                error("different clause with id $id already present\n")
            }
        }
        check(id != 0L)
        if (!checkChain(antecedents) || !checkResolution(antecedents)) {
            error("failed to check derived clause:\n${litsLine(importedClause)}")
        } else insert()
        importedClause.clear()
    }

    override fun addAssumptionClause(id: Long, clause: List<Int>, antecedents: List<Long>) {
        for (lit in clause) {
            if (assumptions.contains(-lit)) continue
            if (constraint.contains(-lit)) continue
            error("clause contains non assumptions or constraint literals\n")
        }
        addDerivedClause(id, true, clause, antecedents)
        deleteClause(id, true, clause)
        assumptionClauses.add(id)
    }

    override fun addAssumption(lit: Int) {
        assumptions.add(lit)
    }

    override fun addConstraint(clause: List<Int>) {
        constraint.clear()
        for (lit in clause) {
            check(lit != 0)
            if (constraint.contains(lit)) continue
            constraint.add(lit)
        }
    }

    override fun resetAssumptions() {
        assumptionClauses.clear()
        assumptions.clear()
        concluded = false
        // constraint.clear ();
    }

    override fun concludeUnsat(type: Int, ids: List<Long>) {
        if (concluded) {
            error("already concluded\n")
        }
        concluded = true
        if (type == CONFLICT) {
            val d = find(ids.last()).get()
            if (d == null || d.size != 0) {
                error("empty clause not in proof\n")
            }
            return
        } else if (type == ASSUMPTIONS) {
            if (ids.size != 1 || assumptionClauses.size != 1) {
                error("expected exactly one assumption clause\n")
            }
            if (ids.last() != assumptionClauses.last()) {
                error("conclusion is not an assumption clause\n")
            }
            return
        } else {
            check(type == CONSTRAINT)
            if (constraint.size != ids.size) {
                val sb = StringBuilder()
                sb.append("not complete conclusion given for constraint\n")
                sb.append("The constraint contains the literals: ")
                for (c in constraint) {
                    sb.append(c).append(' ')
                }

                sb.append("\nThe ids are: ")
                for (c in ids) {
                    sb.append(c).append(' ')
                }
                error(sb.toString())
            }
            for (id in ids) {
                if (assumptionClauses.contains(id)) continue
                error("assumption clause for constraint missing\n")
            }
        }
    }

    /*------------------------------------------------------------------------*/

    override fun deleteClause(id: Long, redundant: Boolean, clause: List<Int>) {
        stats.deleted++
        importClause(clause)
        lastId = id
        val p = find(id)
        val d = p.get()
        if (d != null) {
            for (lit in importedClause) setMark(lit, true)
            val dp = d.literals
            for (i in 0 until d.size) {
                val lit = dp[i]
                if (!mark(lit)) { // should never happen since ids
                    // are unique.
                    error("deleted clause not in proof:\n${litsLine(importedClause)}")
                }
            }
            for (lit in importedClause) setMark(lit, false)

            // Remove from hash table, mark as garbage, connect to garbage list.
            numGarbage++
            check(numClauses > 0)
            numClauses--
            p.set(d.next)
            d.next = garbage
            garbage = d
            d.garbage = true

            // If there are enough garbage clauses collect them.
            // TODO: probably can just delete clause directly without
            // specific garbage collection phase.
            if (numGarbage.toDouble() > 0.5 * max(sizeClauses, sizeVars).toDouble())
                collectGarbageClauses()
        } else {
            error("deleted clause not in proof:\n${litsLine(importedClause)}")
        }
        importedClause.clear()
    }

    /*------------------------------------------------------------------------*/

    override fun weakenMinus(id: Long, clause: List<Int>) {
        importClause(clause)

        check(id <= currentId)
        lastId = id
        val d = find(id).get()
        if (d != null) {
            for (lit in importedClause) setMark(lit, true)
            val dp = d.literals
            for (i in 0 until d.size) {
                val lit = dp[i]
                if (!mark(lit)) { // should never happen since ids
                    // are unique.
                    error("deleted clause not in proof:\n${litsLine(importedClause)}")
                }
            }
            for (lit in importedClause) setMark(lit, false)
        } else {
            error("weakened clause not in proof:\n${litsLine(importedClause)}")
        }
        importedClause.clear()

        val e = clause.toMutableList()
        e.sort()
        clausesToReconstruct[id] = e
    }

    fun restoreClause(id: Long, clause: List<Int>) {
        if (!strictLrat && !clausesToReconstruct.containsKey(id)) {
            return
        }
        if (!clausesToReconstruct.containsKey(id)) {
            error("restoring clauses not deleted previously:\n${litsLine(clause)}")
        }
        val e = clause.toMutableList()
        e.sort()
        val d = clausesToReconstruct[id]!!
        var eq = true
        if (clause.size != d.size) {
            eq = false
        }

        var i = 0
        while (i < e.size && eq) {
            eq = (e[i] == d[i])
            ++i
        }

        if (!eq) {
            error(
                "restoring clause that is different than the one imported:\n" +
                    litsLine(clause) + "vs:\n" + litsLine(d),
            )
        }

        clausesToReconstruct.remove(id)
    }

    override fun finalizeClause(id: Long, clause: List<Int>) {
        stats.finalized++
        numFinalized++
        importClause(clause)
        check(id <= currentId)
        lastId = id
        val d = find(id).get()
        if (d != null) {
            for (lit in importedClause) setMark(lit, true)
            val dp = d.literals
            for (i in 0 until d.size) {
                val lit = dp[i]
                if (!mark(lit)) { // should never happen since ids
                    // are unique.
                    error("deleted clause not in proof:\n${litsLine(importedClause)}")
                }
            }
            for (lit in importedClause) setMark(lit, false)
        } else {
            error("deleted clause not in proof:\n${litsLine(importedClause)}")
        }
        importedClause.clear()
    }

    // check if all clauses have been deleted
    override fun reportStatus(status: Int, id: Long) {
        if (numFinalized == numClauses) {
            numFinalized = 0
        } else {
            error("finalize check failed ${numClauses.toULong()} are not finalized")
        }
    }

    override fun printStats() {} // stats.cpp: messages only

    override fun beginProof(id: Long) {
        currentId = id
    }

    private companion object {
        const val NUM_NONCES = 4

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
        fun litsLine(lits: List<Int>): String {
            val sb = StringBuilder()
            for (lit in lits) sb.append(lit).append(' ')
            sb.append('0')
            return sb.toString()
        }
    }
}
