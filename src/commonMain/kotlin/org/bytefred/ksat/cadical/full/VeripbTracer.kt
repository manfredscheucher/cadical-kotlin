package org.bytefred.ksat.cadical.full

import kotlin.math.abs

/*
 * veripbtracer.hpp + veripbtracer.cpp: VeriPB proof output (always ASCII).
 *
 * Mapping as in DratTracer.kt. The hash table 'HashId **clauses' -> an array of chain heads;
 * the 'HashId **res' slot of 'find_and_delete' -> the bucket index plus the previous chain
 * element (null = the bucket head). 'uint64_t' hashes and nonces -> ULong (wrapping
 * multiplication as in C), ids and counts -> Long.
 * Not ported because upstream never uses them: the '#ifndef NDEBUG' member 'binary' and the
 * 'put_binary_zero' / 'put_binary_lit' / 'put_binary_id' helpers (VeriPB output is ASCII
 * only), 'delete_ids' and 'last_clause' (written, never read).
 */
internal class HashId(
    var next: HashId?, // collision chain link for hash table
    var hash: ULong, // previously computed full 64-bit hash
    var id: Long, // id of clause
)

internal class VeripbTracer(
    private var internal: Internal,
    private val file: File,
    b: Boolean, // 'binary': only stored under '#ifndef NDEBUG', never used
    private val withAntecedents: Boolean,
    private val checkedDeletions: Boolean,
) : FileTracer {
    // hash table for checked deletions
    //
    private var numClauses = 0L // number of clauses in hash table
    private var sizeClauses = 0L // size of clause hash table
    private var clauses = arrayOfNulls<HashId>(0) // hash table of clauses

    private val nonces = ULongArray(NUM_NONCES) // random numbers for hashing
    private var lastHash = 0uL // last computed hash value of clause
    private var lastId = 0L // id of the last added clause

    private var added = 0L
    private var deleted = 0L

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
        file.connectInternal(internal)
    }

    /*------------------------------------------------------------------------*/

    private fun enlargeClauses() {
        check(numClauses == sizeClauses)
        val newSizeClauses = if (sizeClauses != 0L) 2 * sizeClauses else 1L
        val newClauses = arrayOfNulls<HashId>(newSizeClauses.toInt())
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

    private fun newClause(): HashId {
        val res = HashId(null, lastHash, lastId)
        numClauses++
        return res
    }

    private fun deleteClause(c: HashId) {
        check(numClauses > 0)
        numClauses--
        c.next = null // 'delete c'
    }

    private fun computeHash(id: Long): ULong {
        check(id > 0)
        val j = (id % NUM_NONCES).toInt() // Dont know if this is a good
        val tmp = nonces[j] * id.toULong() // hash funktion or even better
        lastHash = tmp // than just using id.
        return lastHash
    }

    private fun findAndDelete(id: Long): Boolean {
        if (numClauses == 0L) return false
        val hash = computeHash(id)
        val h = reduceHash(hash, sizeClauses).toInt()
        var prev: HashId? = null // 'res': null = '&clauses[h]', else '&prev->next'
        var c = clauses[h]
        while (c != null) {
            if (c.hash == hash && c.id == id) {
                break
            }
            if (c.next == null) return false
            prev = c
            c = c.next
        }
        if (c == null) return false
        if (prev == null) clauses[h] = c.next else prev.next = c.next
        deleteClause(c)
        return true
    }

    private fun insert() {
        if (numClauses == sizeClauses) enlargeClauses()
        val h = reduceHash(computeHash(lastId), sizeClauses).toInt()
        val c = newClause()
        c.next = clauses[h]
        clauses[h] = c
    }

    /*------------------------------------------------------------------------*/

    private fun veripbAddDerivedClause(id: Long, redundant: Boolean, clause: List<Int>, chain: List<Long>) {
        file.put("pol ")
        var first = true
        for (p in chain.size - 1 downTo 0) {
            val cid = chain[p]
            if (first) {
                first = false
                file.put(cid)
            } else {
                file.put(' ')
                file.put(cid)
                file.put(" + s")
            }
        }
        file.put("\n")
        file.put("e ")
        file.put(id)
        file.put(" : ")
        for (externalLit in clause) {
            file.put("1 ")
            if (externalLit < 0) file.put('~')
            file.put('x')
            file.put(abs(externalLit))
            file.put(' ')
        }
        file.put(">= 1 ;\n")
        if (!redundant && checkedDeletions) {
            file.put("core id ")
            file.put(id)
            file.put("\n")
        }
    }

    private fun veripbAddDerivedClause(id: Long, redundant: Boolean, clause: List<Int>) {
        file.put("rup ")
        for (externalLit in clause) {
            file.put("1 ")
            if (externalLit < 0) file.put('~')
            file.put('x')
            file.put(abs(externalLit))
            file.put(' ')
        }
        file.put(">= 1 ;\n")
        if (!redundant && checkedDeletions) {
            file.put("core id ")
            file.put(id)
            file.put("\n")
        }
    }

    private fun veripbBeginProof(reservedIds: Long) {
        file.put("pseudo-Boolean proof version 2.0\n")
        file.put("f ")
        file.put(reservedIds)
        file.put("\n")
    }

    private fun veripbDeleteClause(id: Long, redundant: Boolean) {
        if (!redundant && checkedDeletions && findAndDelete(id)) return
        if (redundant || !checkedDeletions) file.put("del id ")
        else {
            file.put("delc ")
        }
        file.put(id)
        file.put("\n")
    }

    private fun veripbReportStatus(unsat: Boolean, conflictId: Long) {
        file.put("output NONE\n")
        if (unsat) {
            file.put("conclusion UNSAT : ")
            file.put(conflictId)
            file.put(" \n")
        } else file.put("conclusion NONE\n")
        file.put("end pseudo-Boolean proof\n")
    }

    private fun veripbStrengthen(id: Long) {
        if (!checkedDeletions) return
        file.put("core id ")
        file.put(id)
        file.put("\n")
    }

    /*------------------------------------------------------------------------*/

    override fun beginProof(id: Long) {
        if (file.closed()) return
        veripbBeginProof(id)
    }

    override fun addOriginalClause(id: Long, redundant: Boolean, clause: List<Int>, restored: Boolean) {} // skip

    override fun addDerivedClause(id: Long, redundant: Boolean, clause: List<Int>, antecedents: List<Long>) {
        if (file.closed()) return
        if (withAntecedents) veripbAddDerivedClause(id, redundant, clause, antecedents)
        else veripbAddDerivedClause(id, redundant, clause)
        added++
    }

    override fun deleteClause(id: Long, redundant: Boolean, clause: List<Int>) {
        if (file.closed()) return
        veripbDeleteClause(id, redundant)
        deleted++
    }

    override fun finalizeClause(id: Long, clause: List<Int>) {} // skip

    override fun reportStatus(status: Int, id: Long) {
        if (file.closed()) return
        veripbReportStatus(status == UNSATISFIABLE, id)
    }

    override fun weakenMinus(id: Long, clause: List<Int>) {
        if (!checkedDeletions) return
        if (file.closed()) return
        lastId = id
        insert()
    }

    override fun strengthen(id: Long) {
        if (file.closed()) return
        veripbStrengthen(id)
    }

    /*------------------------------------------------------------------------*/

    override fun closed(): Boolean = file.closed()

    override fun close(print: Boolean) {
        check(!closed())
        file.close()
    }

    override fun flush(print: Boolean) {
        check(!closed())
        file.flush()
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
    }
}
