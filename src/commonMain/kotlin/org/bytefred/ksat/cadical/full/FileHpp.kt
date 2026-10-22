package org.bytefred.ksat.cadical.full

/*
 * file.hpp: only the character level reading and writing members ('get', 'put', 'lineno',
 * 'bytes', 'name', 'closed', 'close', 'flush', 'piping', 'connect_internal') that parse.cpp,
 * solver.cpp and the proof tracers use.
 *
 * Mapping: opening files, pipes and compressed files ('File::read', 'File::write',
 * 'open_pipe', ...) is OS level I/O and not ported (see PORTING.md). A [File] reads from an
 * in-memory text (its UTF-8 bytes, as 'getc' returns bytes) or writes bytes to a [FileSink]
 * ('putc' on the 'FILE *'). An [Appendable] output is a sink taking each byte as the char
 * with that code (ISO-8859-1), so ASCII output (DIMACS, ASCII proofs) is unchanged.
 * 'EOF' is [EOF] (-1) as in C.
 *
 * 'File::close' maps the 'FILE *' closing ('fclose', 'pclose', 'waitpid') to
 * [FileSink.close] and drops its messages; 'File::flush' ('fflush') -> [FileSink.flush].
 * 'File::piping' ('fstat' + 'S_ISFIFO') is always false: a sink is not a pipe.
 */
internal const val EOF = -1

// The byte level output of a written 'FILE *'.
internal interface FileSink {
    // 'putc (ch, file)' with 'ch' in 0..255.
    fun put(b: Int)

    // 'fflush (file)'.
    fun flush() {}

    // 'fclose (file)'.
    fun close() {}
}

internal class File private constructor(
    private val _name: String,
    private val input: ByteArray?,
    private val output: FileSink?,
) {
    private var internal: Internal? = null
    private val writing: Boolean = output != null
    private var pos = 0
    private var open = true // 'file != 0'

    private var _lineno = 0L
    private var _bytes = 0L

    companion object {
        // 'File::read (Internal *, FILE *, const char *name)' on the given text.
        fun read(name: String, text: String): File = File(name, text.encodeToByteArray(), null)

        // 'File::write (Internal *, FILE *, const char *name)' to the given sink.
        fun write(name: String, out: FileSink): File = File(name, null, out)

        // 'File::write (Internal *, FILE *, const char *name)' to the given text sink.
        fun write(name: String, out: Appendable): File =
            File(name, null, object : FileSink {
                override fun put(b: Int) {
                    out.append(b.toChar())
                }
            })
    }

    fun piping(): Boolean = false

    fun get(): Int {
        check(!writing) { "File.get on a writing file" }
        val input = input!!
        val res = if (pos < input.size) input[pos++].toInt() and 0xff else EOF
        if (res == '\n'.code) _lineno++
        if (res != EOF) _bytes++
        return res
    }

    private fun putc(b: Int): Boolean {
        check(writing) { "File.put on a reading file" }
        check(open) { "File.put on a closed file" }
        output!!.put(b)
        _bytes++
        return true
    }

    // 'bool put (char ch)'.
    fun put(ch: Char): Boolean {
        check(ch.code <= 0xff) { "File.put of non 8 bit char ${ch.code}" }
        return putc(ch.code)
    }

    // 'bool put (unsigned char ch)'.
    fun put(ch: UByte): Boolean = putc(ch.toInt())

    fun endl(): Boolean = put('\n')

    // 'bool put (const char *s)'.
    fun put(s: String): Boolean {
        for (ch in s) if (!put(ch)) return false
        return true
    }

    // 'bool put (int lit)': decimal digits as upstream's buffer loop produces them.
    fun put(lit: Int): Boolean = put(lit.toString())

    // 'bool put (int64_t l)' and 'bool put (uint64_t l)' (ids stay below 2^63).
    fun put(l: Long): Boolean = put(l.toString())

    fun name(): String = _name

    fun lineno(): Long = _lineno

    fun bytes(): Long = _bytes

    fun connectInternal(i: Internal) {
        internal = i
    }

    fun closed(): Boolean = !open

    // 'void close (bool print = false)': 'print' only selects messages (dropped).
    fun close() {
        check(open) { "File.close on a closed file" }
        output?.close()
        open = false // mark as closed
    }

    fun flush() {
        check(open) { "File.flush on a closed file" }
        output?.flush()
    }
}
