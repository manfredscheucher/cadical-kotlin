package org.bytefred.ksat.cadical.full

/*
 * file.hpp: only the character level reading and writing members ('get', 'put', 'lineno',
 * 'bytes', 'name') that parse.cpp and solver.cpp use.
 *
 * Mapping: opening files, pipes and compressed files ('File::read', 'File::write',
 * 'open_pipe', ...) is OS level I/O and not ported (see PORTING.md). A [File] reads from an
 * in-memory text (its UTF-8 bytes, as 'getc' returns bytes) or writes to an [Appendable].
 * 'EOF' is [EOF] (-1) as in C.
 */
internal const val EOF = -1

internal class File private constructor(
    private val _name: String,
    private val input: ByteArray?,
    private val output: Appendable?,
) {
    private val writing: Boolean = output != null
    private var pos = 0

    private var _lineno = 0L
    private var _bytes = 0L

    companion object {
        // 'File::read (Internal *, FILE *, const char *name)' on the given text.
        fun read(name: String, text: String): File = File(name, text.encodeToByteArray(), null)

        // 'File::write (Internal *, FILE *, const char *name)' to the given sink.
        fun write(name: String, out: Appendable): File = File(name, null, out)
    }

    fun get(): Int {
        check(!writing) { "File.get on a writing file" }
        val input = input!!
        val res = if (pos < input.size) input[pos++].toInt() and 0xff else EOF
        if (res == '\n'.code) _lineno++
        if (res != EOF) _bytes++
        return res
    }

    fun put(ch: Char): Boolean {
        check(writing) { "File.put on a reading file" }
        output!!.append(ch)
        _bytes++
        return true
    }

    fun put(s: String): Boolean {
        for (ch in s) if (!put(ch)) return false
        return true
    }

    fun put(lit: Int): Boolean = put(lit.toString())

    fun put(l: Long): Boolean = put(l.toString())

    fun name(): String = _name

    fun lineno(): Long = _lineno

    fun bytes(): Long = _bytes
}
