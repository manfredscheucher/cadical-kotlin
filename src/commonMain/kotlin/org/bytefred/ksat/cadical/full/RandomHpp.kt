package org.bytefred.ksat.cadical.full

/*
 * random.hpp: the 64 bit linear congruential random number generator.
 *
 * Mapping:
 *  - 'uint64_t state' -> ULong, so multiplication and addition wrap exactly as in C.
 *  - 'uint32_t generate ()' -> UInt; 'generate_int' reinterprets the bits as Int as the C cast.
 *  - 'unsigned' intermediates of 'pick_int' / 'pick_log' -> UInt, the C conversions
 *    'unsigned -> double' and 'double -> unsigned' (truncation) -> 'toDouble ()' / 'toUInt ()'
 *    (the value is always in range, so this matches the C conversion).
 *  - 'Random (const Random &)' -> [Random] (other); 'operator= (uint64_t)' -> [assign];
 *    'operator+= (uint64_t)' -> [plusAssign].
 *  - The default constructor 'Random ()' of random.cpp hashes machine id, network addresses,
 *    clock, pid and time. It is only used by the model based tester 'mobical' (the solver
 *    always seeds explicitly with 'opts.seed') and needs OS APIs, so it is not ported.
 */
internal class Random(private var state: ULong) {
    constructor(other: Random) : this(other.seed())

    private fun add(a: ULong) {
        state += a
        if (state == 0uL) state = 1u
        next()
    }

    fun assign(seed: ULong) {
        state = seed
    }

    operator fun plusAssign(a: ULong) = add(a)

    fun seed(): ULong = state

    fun next(): ULong {
        state *= 6364136223846793005uL
        state += 1442695040888963407uL
        check(state != 0uL)
        return state
    }

    fun generate(): UInt {
        next()
        return (state shr 32).toUInt()
    }

    fun generateInt(): Int = generate().toInt()

    fun generateBool(): Boolean = generate() < 2147483648u

    // Generate 'double' value in the range '[0,1]' excluding '1'.
    fun generateDouble(): Double = generate().toDouble() / 4294967295.0

    // Generate 'int' value in the range '[l,r]'.
    fun pickInt(l: Int, r: Int): Int {
        check(l <= r)
        val delta: UInt = 1u + r.toUInt() - l.toUInt()
        val tmp = generate()
        val scaled: UInt
        if (delta != 0u) {
            val fraction = tmp.toDouble() / 4294967296.0
            scaled = (delta.toDouble() * fraction).toUInt()
        } else {
            scaled = tmp
        }
        val res = (scaled + l.toUInt()).toInt()
        check(l <= res)
        check(res <= r)
        return res
    }

    fun pickLog(l: Int, r: Int): Int {
        check(l <= r)
        val delta: UInt = 1u + r.toUInt() - l.toUInt()
        var logDelta = if (delta != 0u) 0 else 32
        while (logDelta < 32 && (1u shl logDelta) < delta) logDelta++
        val logRes = pickInt(0, logDelta)
        var tmp = generate()
        if (logRes < 32) tmp = tmp and ((1u shl logRes) - 1u)
        if (delta != 0u) tmp %= delta
        val res = l + tmp.toInt()
        check(l <= res)
        check(res <= r)
        return res
    }

    // Generate 'double' value in the range '[l,r]'.
    fun pickDouble(l: Double, r: Double): Double {
        check(l <= r)
        var res = (r - l) * generateDouble()
        res += l
        check(l <= res)
        check(res <= r)
        return res
    }
}
