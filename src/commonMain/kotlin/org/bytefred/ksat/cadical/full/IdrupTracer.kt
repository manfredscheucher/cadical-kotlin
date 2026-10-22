package org.bytefred.ksat.cadical.full

import kotlin.math.abs

/*
 * idruptracer.hpp + idruptracer.cpp: IDRUP (incremental DRUP) proof output (ASCII or binary).
 *
 * Mapping as in DratTracer.kt and VeripbTracer.kt (hash table of chain heads, the 'res' slot
 * as bucket plus previous element). 'IdrupClause' with its flexible 'literals' array -> a
 * class holding an IntArray of length 'size'. 'piping' is 'File::piping ()' (false here).
 * 'last_clause' is written but never read upstream: not ported.
 */
internal class IdrupClause(
    var next: IdrupClause?, // collision chain link for hash table
    var hash: ULong, // previously computed full 64-bit hash
    var id: Long, // id of clause
    val size: Int,
    val literals: IntArray,
)

internal class IdrupTracer(
    private var internal: Internal,
    private val file: File,
    private val binary: Boolean,
) : FileTracer {
    private val piping: Boolean // The 'file' is a pipe and needs eagerly flushing.

    // hash table for conclusion
    //
    private var numClauses = 0L // number of clauses in hash table
    private var sizeClauses = 0L // size of clause hash table
    private var clauses = arrayOfNulls<IdrupClause>(0) // hash table of clauses

    private val importedClause = ArrayList<Int>()
    private val assumptions = ArrayList<Int>()

    private val nonces = ULongArray(NUM_NONCES) // random numbers for hashing
    private var lastHash = 0uL // last computed hash value of clause
    private var lastId = 0L // id of the last added clause

    private var added = 0L
    private var deleted = 0L
    private var weakened = 0L
    private var restore = 0L
    private var original = 0L
    private var solved = 0L

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
        piping = file.piping()
    }

    override fun connectInternal(internal: Internal) {
        this.internal = internal
        file.connectInternal(internal)
    }

    /*------------------------------------------------------------------------*/

    private fun enlargeClauses() {
        check(numClauses == sizeClauses)
        val newSizeClauses = if (sizeClauses != 0L) 2 * sizeClauses else 1L
        val newClauses = arrayOfNulls<IdrupClause>(newSizeClauses.toInt())
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

    private fun newClause(): IdrupClause {
        val size = importedClause.size
        val literals = IntArray(size)
        var p = 0
        for (lit in importedClause) {
            literals[p++] = lit
        }
        val res = IdrupClause(null, lastHash, lastId, size, literals)
        numClauses++
        return res
    }

    private fun deleteClause(c: IdrupClause) {
        check(numClauses > 0)
        numClauses--
        c.next = null // 'delete[] (char *) c'
    }

    private fun computeHash(id: Long): ULong {
        check(id > 0)
        val j = (id % NUM_NONCES).toInt()
        val tmp = nonces[j] * id.toULong()
        lastHash = tmp
        return lastHash
    }

    private fun findAndDelete(id: Long): Boolean {
        if (numClauses == 0L) return false
        val hash = computeHash(id)
        val h = reduceHash(hash, sizeClauses).toInt()
        var prev: IdrupClause? = null // 'res': null = '&clauses[h]', else '&prev->next'
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
        val begin = c.literals
        for (i in 0 until c.size) {
            importedClause.add(begin[i])
        }
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

    private fun flushIfPiping() {
        if (piping) file.flush()
    }

    private fun putBinaryZero() {
        check(binary)
        file.put(0.toUByte())
    }

    private fun putBinaryLit(lit: Int) {
        check(binary)
        check(lit != Int.MIN_VALUE)
        var x = 2u * abs(lit).toUInt() + (if (lit < 0) 1u else 0u)
        var ch: UByte
        while ((x and 0x7fu.inv()) != 0u) {
            ch = ((x and 0x7fu) or 0x80u).toUByte()
            file.put(ch)
            x = x shr 7
        }
        ch = x.toUByte()
        file.put(ch)
    }

    private fun putBinaryId(id: ULong) {
        check(binary)
        var x = id
        var ch: UByte
        while ((x and 0x7fuL.inv()) != 0uL) {
            ch = ((x and 0x7fuL) or 0x80uL).toUByte()
            file.put(ch)
            x = x shr 7
        }
        ch = x.toUByte()
        file.put(ch)
    }

    /*------------------------------------------------------------------------*/

    private fun idrupAddRestoredClause(clause: List<Int>) {
        if (binary) file.put('r')
        else file.put("r ")
        for (externalLit in clause)
            if (binary) putBinaryLit(externalLit)
            else {
                file.put(externalLit)
                file.put(' ')
            }
        if (binary) putBinaryZero()
        else file.put("0\n")
        // flush_if_piping ();
    }

    private fun idrupAddDerivedClause(clause: List<Int>) {
        if (binary) file.put('l')
        else file.put("l ")
        for (externalLit in clause)
            if (binary) putBinaryLit(externalLit)
            else {
                file.put(externalLit)
                file.put(' ')
            }
        if (binary) putBinaryZero()
        else file.put("0\n")
        // flush_if_piping ();
    }

    private fun idrupAddOriginalClause(clause: List<Int>) {
        if (binary) file.put('i')
        else file.put("i ")
        for (externalLit in clause)
            if (binary) putBinaryLit(externalLit)
            else {
                file.put(externalLit)
                file.put(' ')
            }
        if (binary) putBinaryZero()
        else file.put("0\n")
        // flush_if_piping ();
    }

    private fun idrupDeleteClause(id: Long, clause: List<Int>) {
        if (findAndDelete(id)) {
            check(importedClause.isEmpty())
            if (binary) file.put('w')
            else file.put("w ")
            weakened++
        } else {
            if (binary) file.put('d')
            else file.put("d ")
            deleted++
        }
        for (externalLit in clause)
            if (binary) putBinaryLit(externalLit)
            else {
                file.put(externalLit)
                file.put(' ')
            }
        if (binary) putBinaryZero()
        else file.put("0\n")
        // flush_if_piping ();
    }

    private fun idrupConcludeAndDelete(conclusion: List<Long>) {
        val size = conclusion.size.toLong()
        if (size > 1) {
            if (binary) {
                file.put('U')
                putBinaryId(size.toULong()) // TODO: put_binary_id ok for size?
            } else {
                file.put("U ")
                file.put(size)
                file.put("\n")
            }
        }
        for (id in conclusion) {
            if (binary) file.put('u')
            else file.put("u ")
            findAndDelete(id)
            for (externalLit in importedClause) {
                // flip sign...
                val notElit = -externalLit
                if (binary) putBinaryLit(notElit)
                else {
                    file.put(notElit)
                    file.put(' ')
                }
            }
            if (binary) putBinaryZero()
            else file.put("0\n")
            importedClause.clear()
        }
        flushIfPiping()
    }

    private fun idrupReportStatus(status: Int) {
        if (binary) file.put('s')
        else file.put("s ")
        if (status == SATISFIABLE) file.put("SATISFIABLE")
        else if (status == UNSATISFIABLE) file.put("UNSATISFIABLE")
        else file.put("UNKNOWN")
        if (!binary) file.put("\n")
        flushIfPiping()
    }

    private fun idrupConcludeSat(model: List<Int>) {
        if (binary) file.put('m')
        else file.put("m ")
        for (lit in model) {
            if (binary) putBinaryLit(lit)
            else {
                file.put(lit)
                file.put(' ')
            }
        }
        if (binary) putBinaryZero()
        else file.put("0\n")
        flushIfPiping()
    }

    private fun idrupConcludeUnknown(trail: List<Int>) {
        if (binary) file.put('e')
        else file.put("e ")
        for (lit in trail) {
            if (binary) putBinaryLit(lit)
            else {
                file.put(lit)
                file.put(' ')
            }
        }
        if (binary) putBinaryZero()
        else file.put("0\n")
        flushIfPiping()
    }

    private fun idrupSolveQuery() {
        if (binary) file.put('q')
        else file.put("q ")
        for (lit in assumptions) {
            if (binary) putBinaryLit(lit)
            else {
                file.put(lit)
                file.put(' ')
            }
        }
        if (binary) putBinaryZero()
        else file.put("0\n")
        flushIfPiping()
    }

    /*------------------------------------------------------------------------*/

    override fun addDerivedClause(id: Long, redundant: Boolean, clause: List<Int>, antecedents: List<Long>) {
        if (file.closed()) return
        check(importedClause.isEmpty())
        idrupAddDerivedClause(clause)
        added++
    }

    override fun addAssumptionClause(id: Long, clause: List<Int>, antecedents: List<Long>) {
        if (file.closed()) return
        check(importedClause.isEmpty())
        for (lit in clause) importedClause.add(lit)
        lastId = id
        insert()
        importedClause.clear()
    }

    override fun deleteClause(id: Long, redundant: Boolean, clause: List<Int>) {
        if (file.closed()) return
        check(importedClause.isEmpty())
        idrupDeleteClause(id, clause)
    }

    override fun weakenMinus(id: Long, clause: List<Int>) {
        if (file.closed()) return
        check(importedClause.isEmpty())
        lastId = id
        insert()
        weakened++
    }

    override fun concludeUnsat(type: Int, ids: List<Long>) {
        if (file.closed()) return
        check(importedClause.isEmpty())
        idrupConcludeAndDelete(ids)
    }

    override fun addOriginalClause(id: Long, redundant: Boolean, clause: List<Int>, restored: Boolean) {
        if (file.closed()) return
        if (!restored) {
            original++
            return idrupAddOriginalClause(clause)
        }
        check(restored)
        if (findAndDelete(id)) {
            return
        }
        idrupAddRestoredClause(clause)
        restore++
    }

    override fun reportStatus(status: Int, id: Long) {
        if (file.closed()) return
        idrupReportStatus(status)
    }

    override fun concludeSat(model: List<Int>) {
        if (file.closed()) return
        idrupConcludeSat(model)
    }

    override fun concludeUnknown(trail: List<Int>) {
        if (file.closed()) return
        idrupConcludeUnknown(trail)
    }

    override fun solveQuery() {
        if (file.closed()) return
        idrupSolveQuery()
        solved++
    }

    override fun addAssumption(lit: Int) {
        assumptions.add(lit)
    }

    override fun resetAssumptions() {
        assumptions.clear()
    }

    // skip
    override fun beginProof(id: Long) {}

    override fun finalizeClause(id: Long, clause: List<Int>) {}

    override fun strengthen(id: Long) {}

    override fun addConstraint(clause: List<Int>) {}

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
