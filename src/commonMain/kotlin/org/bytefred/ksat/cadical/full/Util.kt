package org.bytefred.ksat.cadical.full

/*
 * util.cpp: parse_int_str, has_suffix, has_prefix, hash_string.
 *
 * Mapping:
 *  - 'parse_int_str (const char *, int &)' returns the parsed value or null (false upstream).
 *  - C strings are Kotlin Strings; the terminating NUL of the C loops is the end of the
 *    String (the 'ch' after the last character is 0).
 *  - 'hash_string' uses 64 bit unsigned arithmetic (ULong) and hashes the bytes of the
 *    string; callers only pass ASCII (option names, numeric host names), where chars are
 *    bytes.
 *  - is_color_option / is_no_color_option are command line only and not ported.
 */

/** parse_int_str: 'true', 'false' or '[-]<mantissa>[e<exponent>]' within '[INT_MIN,INT_MAX]'. */
internal fun parseIntStr(valStr: String): Int? {
    if (valStr == "true") return 1
    if (valStr == "false") return 0
    var p = 0
    fun next(): Int {
        val ch = if (p < valStr.length) valStr[p].code else 0
        p++
        return ch
    }
    val sign: Int
    if (valStr.isNotEmpty() && valStr[0] == '-') {
        sign = -1
        p++
    } else {
        sign = 1
    }
    var ch = next()
    if (!isDigit(ch)) return null
    val bound = -Int.MIN_VALUE.toLong()
    var mantissa = (ch - '0'.code).toLong()
    while (isDigit(next().also { ch = it })) {
        mantissa = if (bound / 10 < mantissa) bound else mantissa * 10
        val digit = ch - '0'.code
        mantissa = if (bound - digit < mantissa) bound else mantissa + digit
    }
    var exponent = 0
    if (ch == 'e'.code) {
        while (isDigit(next().also { ch = it })) exponent = if (exponent != 0) 10 else ch - '0'.code
        if (ch != 0) return null
    } else if (ch != 0) {
        return null
    }
    check(exponent <= 10)
    var val64 = mantissa
    for (i in 0 until exponent) val64 *= 10
    if (sign < 0) {
        val64 = -val64
        if (val64 < Int.MIN_VALUE) val64 = Int.MIN_VALUE.toLong()
    } else {
        if (val64 > Int.MAX_VALUE) val64 = Int.MAX_VALUE.toLong()
    }
    return val64.toInt()
}

private fun isDigit(ch: Int): Boolean = ch >= '0'.code && ch <= '9'.code

internal fun hasSuffix(str: String, suffix: String): Boolean =
    str.length > suffix.length && str.endsWith(suffix)

internal fun hasPrefix(str: String, prefix: String): Boolean = str.startsWith(prefix)

private val primes = arrayOf(
    1111111111111111111uL, 2222222222222222249uL, 3333333333333333347uL,
    4444444444444444537uL, 5555555555555555621uL, 6666666666666666677uL,
    7777777777777777793uL, 8888888888888888923uL, 9999999999999999961uL,
)

internal fun hashString(str: String): ULong {
    val size = primes.size
    var res: ULong = 0u
    var i = 0
    for (c in str) {
        res += (c.code and 0xff).toULong()
        res *= primes[i++]
        if (i == size) i = 0
    }
    return res
}
