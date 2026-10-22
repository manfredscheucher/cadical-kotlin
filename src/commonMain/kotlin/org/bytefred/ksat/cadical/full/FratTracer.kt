package org.bytefred.ksat.cadical.full

import kotlin.math.abs

/*
 * frattracer.hpp + frattracer.cpp: FRAT proof output (ASCII or binary). Mapping as in
 * DratTracer.kt; 'put_binary_id (uint64_t)' on ULong.
 */
internal class FratTracer(
    private var internal: Internal,
    private val file: File,
    private val binary: Boolean,
    private val withAntecedents: Boolean,
) : FileTracer {
    private var added = 0L
    private var deleted = 0L
    private var finalized = 0L
    private var original = 0L

    // 'vector<uint64_t> delete_ids' is declared in frattracer.hpp but never used: not ported.

    override fun connectInternal(internal: Internal) {
        this.internal = internal
        file.connectInternal(internal)
    }

    /*------------------------------------------------------------------------*/

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

    private fun fratAddOriginalClause(id: Long, clause: List<Int>) {
        if (binary) file.put('o')
        else file.put("o ")
        if (binary) putBinaryId(id.toULong())
        else {
            file.put(id)
            file.put("  ")
        }
        for (externalLit in clause)
            if (binary) putBinaryLit(externalLit)
            else {
                file.put(externalLit)
                file.put(' ')
            }
        if (binary) putBinaryZero()
        else file.put("0\n")
    }

    private fun fratAddDerivedClause(id: Long, clause: List<Int>) {
        if (binary) file.put('a')
        else file.put("a ")
        if (binary) putBinaryId(id.toULong())
        else {
            file.put(id)
            file.put("  ")
        }
        for (externalLit in clause)
            if (binary) putBinaryLit(externalLit)
            else {
                file.put(externalLit)
                file.put(' ')
            }
        if (binary) putBinaryZero()
        else file.put("0\n")
    }

    private fun fratAddDerivedClause(id: Long, clause: List<Int>, chain: List<Long>) {
        if (binary) file.put('a')
        else file.put("a ")
        if (binary) putBinaryId(id.toULong())
        else {
            file.put(id)
            file.put("  ")
        }
        for (externalLit in clause)
            if (binary) putBinaryLit(externalLit)
            else {
                file.put(externalLit)
                file.put(' ')
            }
        if (binary) {
            putBinaryZero()
            file.put('l')
        } else file.put("0  l ")
        for (c in chain)
            if (binary) putBinaryId(2uL * c.toULong()) // LRAT can have negative ids
            else {
                file.put(c)
                file.put(' ') // in proof chain, so they get
            }
        if (binary) putBinaryZero() // since cadical has no rat-steps
        else file.put("0\n") // this is just 2c here
    }

    private fun fratDeleteClause(id: Long, clause: List<Int>) {
        if (binary) file.put('d')
        else file.put("d ")
        if (binary) putBinaryId(id.toULong())
        else {
            file.put(id)
            file.put("  ")
        }
        for (externalLit in clause)
            if (binary) putBinaryLit(externalLit)
            else {
                file.put(externalLit)
                file.put(' ')
            }
        if (binary) putBinaryZero()
        else file.put("0\n")
    }

    private fun fratFinalizeClause(id: Long, clause: List<Int>) {
        if (binary) file.put('f')
        else file.put("f ")
        if (binary) putBinaryId(id.toULong())
        else {
            file.put(id)
            file.put("  ")
        }
        for (externalLit in clause)
            if (binary) putBinaryLit(externalLit)
            else {
                file.put(externalLit)
                file.put(' ')
            }
        if (binary) putBinaryZero()
        else file.put("0\n")
    }

    /*------------------------------------------------------------------------*/

    override fun beginProof(id: Long) {} // skip

    override fun addOriginalClause(id: Long, redundant: Boolean, clause: List<Int>, restored: Boolean) {
        if (file.closed()) return
        fratAddOriginalClause(id, clause)
    }

    override fun addDerivedClause(id: Long, redundant: Boolean, clause: List<Int>, antecedents: List<Long>) {
        if (file.closed()) return
        if (withAntecedents) fratAddDerivedClause(id, clause, antecedents)
        else fratAddDerivedClause(id, clause)
        added++
    }

    override fun deleteClause(id: Long, redundant: Boolean, clause: List<Int>) {
        if (file.closed()) return
        fratDeleteClause(id, clause)
        deleted++
    }

    override fun finalizeClause(id: Long, clause: List<Int>) {
        if (file.closed()) return
        fratFinalizeClause(id, clause)
    }

    override fun reportStatus(status: Int, id: Long) {} // skip

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
}
