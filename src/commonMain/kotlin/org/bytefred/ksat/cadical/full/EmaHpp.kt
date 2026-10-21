package org.bytefred.ksat.cadical.full

/*
 * ema.hpp plus 'EMA::update' of ema.cpp: exponential moving average with ADAM-style
 * initialization bias correction [KingmaBa-ICLR'15].
 *
 * Mapping:
 *  - 'EMA (double a)' with 'exp (!!beta)' -> exp = 1.0 if beta != 0 else 0.0.
 *  - 'operator double ()' -> [value] (read the field directly).
 *  - 'INIT_EMA (E, WINDOW)' -> [initEma]; 'UPDATE_AVERAGE (A, Y)' -> 'A.update (y)'.
 *  - The 'updated' counter only exists with LOGGING upstream and is not ported. The
 *    'Internal *' and 'name' arguments of 'update' are only used for logging and dropped.
 *  - C++ struct assignment 'E = EMA (ALPHA)' -> [initEma] overwrites all fields in place.
 *
 * The biased moving average is computed as usual ('biased += alpha * (y - biased)') and then
 * fixed with the correction term '1.0 / (1.0 - pow (beta, updated))' by multiplication to
 * obtain the unbiased moving average 'value'. To avoid computing 'pow' every time, 'exp' is
 * multiplied in every update with 'beta'.
 */
internal class EMA {
    var value = 0.0 // unbiased (corrected) moving average
    var biased = 0.0 // biased initialized moving average
    var alpha = 0.0 // input scaling with 'alpha = 1 - beta'
    var beta = 0.0 // decay of 'biased' with 'beta = 1 - alpha'
    var exp = 0.0 // 'exp = pow (beta, updated)'

    /** 'EMA (double a)' assigned to this EMA. */
    fun set(a: Double) {
        value = 0.0
        biased = 0.0
        alpha = a
        beta = 1 - a
        exp = if (beta != 0.0) 1.0 else 0.0
        check(beta >= 0)
    }

    fun update(y: Double) {
        val oldBiased = biased
        val delta = y - oldBiased
        val scaledDelta = alpha * delta
        val newBiased = oldBiased + scaledDelta
        biased = newBiased
        val oldExp = exp
        val newValue: Double
        if (oldExp != 0.0) {
            val newExp = oldExp * beta
            check(newExp < 1)
            exp = newExp
            val div = 1 - newExp
            check(div > 0)
            newValue = newBiased / div
        } else {
            newValue = newBiased
        }
        value = newValue
    }

    /** C++ struct assignment / 'swap' helper: copies all fields of [other]. */
    fun copyFrom(other: EMA) {
        value = other.value
        biased = other.biased
        alpha = other.alpha
        beta = other.beta
        exp = other.exp
    }
}

/** INIT_EMA (E, WINDOW). */
internal fun initEma(e: EMA, window: Int) {
    check(window >= 1)
    val alpha = 1.0 / window.toDouble()
    e.set(alpha)
}
