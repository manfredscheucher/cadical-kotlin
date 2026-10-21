package org.bytefred.ksat.cadical.full

/*
 * reluctant.hpp: Donald Knuth's version of the Luby restart sequence ('reluctant doubling').
 *
 * Mapping: the 'uint64_t' words -> ULong (the bit trick 'u & -u' needs unsigned wrap-around).
 * 'operator bool ()' (which also clears the trigger) -> [fire]. The uninitialized members of
 * the default constructor are zero here; they are only read after 'enable'.
 *
 * In our code we incorporate a base interval 'period' and only after period many calls to
 * 'tick' times the current sequence value we update the reluctant doubling sequence value.
 * The 'tick' call is decoupled from the activation signal of the sequence through 'trigger'.
 * It is also possible to set an upper limit to the length of an inactive sub-sequence. If
 * that limit is reached the whole reluctant doubling sequence starts over with the initial
 * values.
 */
internal class Reluctant {
    private var u: ULong = 0u
    private var v: ULong = 0u
    private var limit: ULong = 0u
    private var period: ULong = 0u
    private var countdown: ULong = 0u
    private var trigger = false
    private var limited = false

    fun enable(p: Int, l: Long) {
        check(p > 0)
        u = 1u
        v = 1u
        period = p.toULong()
        countdown = period
        trigger = false
        if (l <= 0) {
            limited = false
        } else {
            limited = true
            limit = l.toULong()
        }
    }

    fun disable() {
        period = 0u
        trigger = false
    }

    // Increments the count until the 'period' is hit.  Then it performs the
    // actual increment of reluctant doubling.  This gives the common 'Luby'
    // sequence with the specified base interval period.  As soon the limit is
    // reached (countdown goes to zero) we remember this event and then
    // disable updating the reluctant sequence until the signal is delivered.
    fun tick() {
        if (period == 0uL) return // disabled
        if (trigger) return // already triggered
        if (--countdown != 0uL) return // not there yet
        if ((u and (0uL - u)) == v) {
            u += 1u
            v = 1u
        } else {
            v *= 2u // (DK)
        }
        if (limited && v >= limit) {
            u = 1u
            v = 1u
        }
        countdown = v * period
        trigger = true
    }

    /** 'operator bool ()': true once per trigger. */
    fun fire(): Boolean {
        if (!trigger) return false
        trigger = false
        return true
    }
}
