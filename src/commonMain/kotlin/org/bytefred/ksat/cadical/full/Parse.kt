package org.bytefred.ksat.cadical.full

import kotlin.math.abs
import org.bytefred.ksat.cadical.IntArrayList

/*
 * parse.hpp + parse.cpp: parsing DIMACS CNF / INCCNF and solution files.
 *
 * Mapping:
 *  - 'PER (...)' (formats 'internal->error_message' as "<file>:<lineno>: parse error: ..."
 *    and returns it) -> 'return per ("...")'; 'error_message' is not ported, the parse
 *    functions return the message string directly (null = success, as upstream's 0).
 *  - 'int &ch', 'int &res', 'int &lit', 'int &vars' -> [IntRef].
 *  - 'bool *parse_inccnf_too' -> [BoolRef]? and 'vector<int> *cubes' -> IntArrayList?.
 *  - 'cube_token' is compared by pointer upstream -> by reference ('===').
 *  - 'isdigit' / 'isspace' of the C locale on 'int' characters (EOF is neither).
 *  - The 'enum { FORCED, RELAXED, STRICT }' -> constants in the companion object.
 *  - MSG / PHASE / LOG / START / STOP and the parse timing are dropped (messages only).
 */

private fun isdigit(ch: Int): Boolean = ch >= '0'.code && ch <= '9'.code

private fun isspace(ch: Int): Boolean =
    ch == ' '.code || ch == '\t'.code || ch == '\n'.code || ch == 0x0b || ch == 0x0c || ch == '\r'.code

private const val INT_MAX = Int.MAX_VALUE

private val cubeToken: String = "unexpected 'a' in CNF"

internal class Parser(
    private val solver: Solver,
    private val file: File,
    private val parseInccnfToo: BoolRef?,
    private val cubes: IntArrayList?,
) {
    private val internal: Internal = solver.internal
    private val external: External = solver.external

    companion object {
        const val FORCED = 0 // Force reading even if header is broken.
        const val RELAXED = 1 // Relaxed white space treatment in header.
        const val STRICT = 2 // Strict white space and header compliance.
    }

    /*------------------------------------------------------------------------*/

    // Parse error.

    private fun per(message: String): String =
        "${file.name()}:${file.lineno()}: parse error: $message"

    /*------------------------------------------------------------------------*/

    // Parsing utilities.

    private fun parseChar(): Int = file.get()

    // Return an non zero error string if a parse error occurred.

    private fun parseString(str: String, prev0: Char): String? {
        var prev = prev0
        for (p in str)
            if (parseChar() == p.code)
                prev = p
            else if (p == ' ')
                return per("expected space after '$prev'")
            else
                return per("expected '$p' after '$prev'")
        return null
    }

    private fun parsePositiveInt(ch: IntRef, res: IntRef, name: String): String? {
        check(isdigit(ch.value)) { "parsePositiveInt: no digit" }
        res.value = ch.value - '0'.code
        while (isdigit(parseChar().also { ch.value = it })) {
            val digit = ch.value - '0'.code
            if (INT_MAX / 10 < res.value || INT_MAX - digit < 10 * res.value)
                return per("too large '$name' in header")
            res.value = 10 * res.value + digit
        }
        return null
    }

    private fun parseLit(ch: IntRef, lit: IntRef, vars: IntRef, strict: Int): String? {
        if (ch.value == 'a'.code)
            return cubeToken
        var sign = 0
        if (ch.value == '-'.code) {
            if (!isdigit(parseChar().also { ch.value = it }))
                return per("expected digit after '-'")
            sign = -1
        } else if (!isdigit(ch.value))
            return per("expected digit or '-'")
        else
            sign = 1
        lit.value = ch.value - '0'.code
        while (isdigit(parseChar().also { ch.value = it })) {
            val digit = ch.value - '0'.code
            if (INT_MAX / 10 < lit.value || INT_MAX - digit < 10 * lit.value)
                return per("literal too large")
            lit.value = 10 * lit.value + digit
        }
        if (ch.value == '\r'.code)
            ch.value = parseChar()
        if (ch.value != 'c'.code && ch.value != ' '.code && ch.value != '\t'.code &&
            ch.value != '\n'.code && ch.value != EOF
        )
            return per("expected white space after '${sign * lit.value}'")
        if (lit.value > vars.value) {
            if (strict != FORCED)
                return per("literal ${sign * lit.value} exceeds maximum variable ${vars.value}")
            else
                vars.value = lit.value
        }
        lit.value *= sign
        return null
    }

    /*------------------------------------------------------------------------*/

    // Parsing CNF in DIMACS format.

    private fun parseDimacsNonProfiled(vars: IntRef, strict0: Int): String? {
        var strict = strict0

        var foundInccnfHeader = false
        val ch = IntRef()
        val clauses = IntRef(0)
        vars.value = 0

        // First read comments before header with possibly embedded options.
        //
        while (true) {
            ch.value = parseChar()
            if (strict != STRICT)
                if (ch.value == ' '.code || ch.value == '\n'.code || ch.value == '\t'.code ||
                    ch.value == '\r'.code
                )
                    continue
            if (ch.value != 'c'.code)
                break
            val buf = StringBuilder()
            while (parseChar().also { ch.value = it } != '\n'.code)
                if (ch.value == EOF)
                    return per("unexpected end-of-file in header comment")
                else if (ch.value != '\r'.code)
                    buf.append(ch.value.toChar())
            var o = 0
            while (o < buf.length && buf[o] != '-')
                o++
            if (o == buf.length)
                continue
            if (o < buf.length)
                solver.setLongOption(buf.substring(o))
        }

        if (ch.value != 'p'.code)
            return per("expected 'c' or 'p'")

        ch.value = parseChar()
        if (strict == STRICT) {
            if (ch.value != ' '.code)
                return per("expected space after 'p'")
            ch.value = parseChar()
        } else if (ch.value != ' '.code && ch.value != '\t'.code)
            return per("expected white space after 'p'")
        else {
            do
                ch.value = parseChar()
            while (ch.value == ' '.code || ch.value == '\t'.code)
        }

        // Now read 'p cnf <var> <clauses>' header of DIMACS file
        // or 'p inccnf' of incremental 'INCCNF' file.
        //
        if (ch.value == 'c'.code) {
            check(!foundInccnfHeader) { "parseDimacs: inccnf header already found" }
            if (strict == STRICT) {
                var err = parseString("nf ", 'c')
                if (err != null)
                    return err
                ch.value = parseChar()
                if (!isdigit(ch.value))
                    return per("expected digit after 'p cnf '")
                err = parsePositiveInt(ch, vars, "<max-var>")
                if (err != null)
                    return err
                if (ch.value != ' '.code)
                    return per("expected ' ' after 'p cnf ${vars.value}'")
                if (!isdigit(parseChar().also { ch.value = it }))
                    return per("expected digit after 'p cnf ${vars.value} '")
                err = parsePositiveInt(ch, clauses, "<num-clauses>")
                if (err != null)
                    return err
                if (ch.value != '\n'.code)
                    return per("expected new-line after 'p cnf ${vars.value} ${clauses.value}'")
            } else {
                if (parseChar() != 'n'.code)
                    return per("expected 'n' after 'p c'")
                if (parseChar() != 'f'.code)
                    return per("expected 'f' after 'p cn'")
                ch.value = parseChar()
                if (!isspace(ch.value))
                    return per("expected space after 'p cnf'")
                do
                    ch.value = parseChar()
                while (isspace(ch.value))
                if (!isdigit(ch.value))
                    return per("expected digit after 'p cnf '")
                var err = parsePositiveInt(ch, vars, "<max-var>")
                if (err != null)
                    return err
                if (!isspace(ch.value))
                    return per("expected space after 'p cnf ${vars.value}'")
                do
                    ch.value = parseChar()
                while (isspace(ch.value))
                if (!isdigit(ch.value))
                    return per("expected digit after 'p cnf ${vars.value} '")
                err = parsePositiveInt(ch, clauses, "<num-clauses>")
                if (err != null)
                    return err
                while (ch.value != '\n'.code) {
                    if (ch.value != '\r'.code && !isspace(ch.value))
                        return per("expected new-line after 'p cnf ${vars.value} ${clauses.value}'")
                    ch.value = parseChar()
                }
            }

            if (strict != FORCED)
                solver.reserve(vars.value)
            internal.reserveIds(clauses.value)
        } else if (parseInccnfToo == null)
            return per("expected 'c' after 'p '")
        else if (ch.value == 'i'.code) {
            foundInccnfHeader = true
            val err = parseString("nccnf", 'i')
            if (err != null)
                return err
            ch.value = parseChar()
            if (strict == STRICT) {
                if (ch.value != '\n'.code)
                    return per("expected new-line after 'p inccnf'")
            } else {
                while (ch.value != '\n'.code) {
                    if (ch.value != '\r'.code && !isspace(ch.value))
                        return per("expected new-line after 'p inccnf'")
                    ch.value = parseChar()
                }
            }

            strict = FORCED
        } else
            return per("expected 'c' or 'i' after 'p '")

        if (parseInccnfToo != null)
            parseInccnfToo.value = false

        // Now read body of DIMACS part.
        //
        val lit = IntRef(0)
        var parsed = 0
        while (parseChar().also { ch.value = it } != EOF) {
            if (ch.value == ' '.code || ch.value == '\n'.code || ch.value == '\t'.code ||
                ch.value == '\r'.code
            )
                continue
            if (ch.value == 'c'.code) {
                while (parseChar().also { ch.value = it } != '\n'.code && ch.value != EOF)
                    ;
                if (ch.value == EOF)
                    break
                continue
            }
            if (ch.value == 'a'.code && foundInccnfHeader)
                break
            val err = parseLit(ch, lit, vars, strict)
            if (err != null)
                return err
            if (ch.value == 'c'.code) {
                while (parseChar().also { ch.value = it } != '\n'.code)
                    if (ch.value == EOF)
                        return per("unexpected end-of-file in comment")
            }
            solver.add(lit.value)
            if (!foundInccnfHeader && lit.value == 0 && parsed++ >= clauses.value &&
                strict != FORCED
            )
                return per("too many clauses")
        }

        if (lit.value != 0)
            return per("last clause without terminating '0'")

        if (!foundInccnfHeader && parsed < clauses.value && strict != FORCED)
            return per("clause missing")

        if (ch.value == 'a'.code) {
            check(parseInccnfToo != null) { "parseDimacs: cube without inccnf" }
            check(foundInccnfHeader) { "parseDimacs: cube without inccnf header" }
            if (!parseInccnfToo.value)
                parseInccnfToo.value = true
            while (true) {
                ch.value = parseChar()
                if (ch.value == ' '.code || ch.value == '\n'.code || ch.value == '\t'.code ||
                    ch.value == '\r'.code
                )
                    continue
                if (ch.value == 'c'.code) {
                    while (parseChar().also { ch.value = it } != '\n'.code && ch.value != EOF)
                        ;
                    if (ch.value == EOF)
                        break
                    continue
                }
                val err = parseLit(ch, lit, vars, strict)
                if (err === cubeToken)
                    return per("two 'a' in a row")
                else if (err != null)
                    return err
                if (ch.value == 'c'.code) {
                    while (parseChar().also { ch.value = it } != '\n'.code)
                        if (ch.value == EOF)
                            return per("unexpected end-of-file in comment")
                }
                cubes?.add(lit.value)
                if (lit.value == 0) {
                    while (true) {
                        ch.value = parseChar()
                        if (ch.value == ' '.code || ch.value == '\n'.code ||
                            ch.value == '\t'.code || ch.value == '\r'.code
                        )
                            continue
                        if (ch.value == 'c'.code) {
                            while (parseChar().also { ch.value = it } != '\n'.code && ch.value != EOF)
                                ;
                            if (ch.value == EOF)
                                break
                        }
                        if (ch.value == EOF)
                            break
                        if (ch.value != 'a'.code)
                            return per("expected 'a' or end-of-file after zero")
                        lit.value = Int.MIN_VALUE
                        break
                    }
                    if (ch.value == EOF)
                        break
                }
            }
            if (lit.value != 0)
                return per("last cube without terminating '0'")
        }

        return null
    }

    /*------------------------------------------------------------------------*/

    // Parsing solution in competition output format.

    private fun parseSolutionNonProfiled(): String? {
        val solution = ByteArray(external.maxVar + 1)
        external.solution = solution
        val ch = IntRef()
        while (true) {
            ch.value = parseChar()
            if (ch.value == EOF)
                return per("missing 's' line")
            else if (ch.value == 'c'.code) {
                while (parseChar().also { ch.value = it } != '\n'.code)
                    if (ch.value == EOF)
                        return per("unexpected end-of-file in comment")
            } else if (ch.value == 's'.code)
                break
            else
                return per("expected 'c' or 's'")
        }
        var err = parseString(" SATISFIABLE", 's')
        if (err != null)
            return err
        if (parseChar().also { ch.value = it } == '\r'.code)
            ch.value = parseChar()
        if (ch.value != '\n'.code)
            return per("expected new-line after 's SATISFIABLE'")
        while (true) {
            ch.value = parseChar()
            if (ch.value != 'v'.code)
                return per("expected 'v' at start-of-line")
            if (parseChar().also { ch.value = it } != ' '.code)
                return per("expected ' ' after 'v'")
            val lit = IntRef(0)
            ch.value = parseChar()
            do {
                if (ch.value == ' '.code || ch.value == '\t'.code) {
                    ch.value = parseChar()
                    continue
                }
                // 'external->max_var' is passed by reference (and may grow with FORCED).
                val maxVar = IntRef(external.maxVar)
                err = parseLit(ch, lit, maxVar, FORCED)
                external.maxVar = maxVar.value
                if (err != null)
                    return err
                if (ch.value == 'c'.code)
                    return per("unexpected comment")
                if (lit.value == 0)
                    break
                if (solution[abs(lit.value)].toInt() != 0)
                    return per("variable ${abs(lit.value)} occurs twice")
                solution[abs(lit.value)] = (if (lit.value < 0) -1 else 1).toByte()
                if (ch.value == '\r'.code)
                    ch.value = parseChar()
            } while (ch.value != '\n'.code)
            if (lit.value == 0)
                break
        }
        return null
    }

    /*------------------------------------------------------------------------*/

    // Parse a DIMACS file.  Return null if successful. Otherwise a parse
    // error is return. The parsed clauses are added to the solver and the
    // maximum variable index found is returned in the 'vars' argument.
    // See upstream 'parse.hpp' for the meaning of 'strict'.

    fun parseDimacs(vars: IntRef, strict: Int): String? {
        check(strict == FORCED || strict == RELAXED || strict == STRICT) { "invalid strict mode $strict" }
        val err = parseDimacsNonProfiled(vars, strict)
        return err
    }

    // Parse a solution file as used in the SAT competition, e.g., with
    // comment lines 'c ...', a status line 's ...' and value lines 'v ...'.

    fun parseSolution(): String? {
        val err = parseSolutionNonProfiled()
        return err
    }
}
