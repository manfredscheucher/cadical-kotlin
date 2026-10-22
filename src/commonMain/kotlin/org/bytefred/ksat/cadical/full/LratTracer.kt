package org.bytefred.ksat.cadical.full

import kotlin.math.abs

/*
 * lrattracer.hpp + lrattracer.cpp: LRAT proof output (ASCII or binary). Mapping as in
 * DratTracer.kt; 'uint64_t' ids -> Long (below 2^63), the varint of 'put_binary_id' on ULong.
 */
internal class LratTracer(
    private var internal: Internal,
    private val file: File,
    private val binary: Boolean,
) : FileTracer {
    private var added = 0L
    private var deleted = 0L
    private var latestId = 0L
    private val deleteIds = ArrayList<Long>()

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
        val idx = abs(lit).toUInt()
        check(idx < (1u shl 31))
        var x = 2u * idx + (if (lit < 0) 1u else 0u)
        var ch: UByte
        while ((x and 0x7fu.inv()) != 0u) {
            ch = ((x and 0x7fu) or 0x80u).toUByte()
            file.put(ch)
            x = x shr 7
        }
        ch = x.toUByte()
        file.put(ch)
    }

    private fun putBinaryId(id: Long) {
        check(binary)
        check(id.toULong() != (0uL.inv() shr 1))
        val u: ULong = if (id < 0) (-id).toULong() else id.toULong()
        check(u < (1uL shl 63))
        var x: ULong = 2uL * u + (if (id < 0) 1uL else 0uL)
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

    private fun lratAddClause(id: Long, clause: List<Int>, chain: List<Long>) {
        if (deleteIds.size != 0) {
            if (!binary) {
                file.put(latestId)
                file.put(" ")
            }
            if (binary) file.put('d')
            else file.put("d ")
            for (did in deleteIds) {
                if (binary) putBinaryId(did)
                else {
                    file.put(did)
                    file.put(" ")
                }
            }
            if (binary) putBinaryZero()
            else file.put("0\n")
            deleteIds.clear()
        }
        latestId = id

        if (binary) {
            file.put('a')
            putBinaryId(id)
        } else {
            file.put(id)
            file.put(" ")
        }
        for (externalLit in clause)
            if (binary) putBinaryLit(externalLit)
            else {
                file.put(externalLit)
                file.put(' ')
            }
        if (binary) putBinaryZero()
        else file.put("0 ")
        for (c in chain)
            if (binary) putBinaryId(c)
            else {
                file.put(c)
                file.put(' ') // in proof chain, so they get
            }
        if (binary) putBinaryZero() // since cadical has no rat-steps
        else file.put("0\n") // this is just 2c here
    }

    private fun lratDeleteClause(id: Long) {
        deleteIds.add(id) // pushing off deletion for later
    }

    /*------------------------------------------------------------------------*/

    override fun addOriginalClause(id: Long, redundant: Boolean, clause: List<Int>, restored: Boolean) {} // skip

    override fun addDerivedClause(id: Long, redundant: Boolean, clause: List<Int>, antecedents: List<Long>) {
        if (file.closed()) return
        lratAddClause(id, clause, antecedents)
        added++
    }

    override fun deleteClause(id: Long, redundant: Boolean, clause: List<Int>) {
        if (file.closed()) return
        lratDeleteClause(id)
        deleted++
    }

    override fun beginProof(id: Long) {
        if (file.closed()) return
        latestId = id
    }

    override fun finalizeClause(id: Long, clause: List<Int>) {} // skip

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
