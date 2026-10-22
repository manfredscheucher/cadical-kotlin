package org.bytefred.ksat.cadical.full

import kotlin.math.abs

/*
 * drattracer.hpp + drattracer.cpp: DRAT proof output (ASCII or binary).
 *
 * Mapping (as for all file tracers): 'File *file' owned by the tracer -> [file] (the
 * destructor 'delete file' is garbage collected); 'LOG' and 'MSG' / 'print_statistics' are
 * dropped (output only), the '#ifndef QUIET' counters are kept; 'unsigned char' -> UByte,
 * 'unsigned' -> UInt so the varint loop shifts and masks exactly as in C.
 */
internal class DratTracer(
    private var internal: Internal,
    private val file: File,
    private val binary: Boolean,
) : FileTracer {
    private var added = 0L
    private var deleted = 0L

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

    /*------------------------------------------------------------------------*/

    private fun dratAddClause(clause: List<Int>) {
        if (binary) file.put('a')
        for (externalLit in clause)
            if (binary) putBinaryLit(externalLit)
            else {
                file.put(externalLit)
                file.put(' ')
            }
        if (binary) putBinaryZero()
        else file.put("0\n")
    }

    private fun dratDeleteClause(clause: List<Int>) {
        if (binary) file.put('d')
        else file.put("d ")
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

    override fun addOriginalClause(id: Long, redundant: Boolean, clause: List<Int>, restored: Boolean) {} // skip

    override fun addDerivedClause(id: Long, redundant: Boolean, clause: List<Int>, antecedents: List<Long>) {
        if (file.closed()) return
        dratAddClause(clause)
        added++
    }

    override fun deleteClause(id: Long, redundant: Boolean, clause: List<Int>) {
        if (file.closed()) return
        dratDeleteClause(clause)
        deleted++
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
