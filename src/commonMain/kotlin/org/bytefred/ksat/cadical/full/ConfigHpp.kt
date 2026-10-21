package org.bytefred.ksat.cadical.full

/*
 * config.hpp plus config.cpp: the pre-defined option configurations.
 *
 * 'default' resets the resettable options, 'plain' disables all preprocessing options, 'sat'
 * and 'unsat' set the option values below. 'usage' / 'begin' / 'end' (command line listing)
 * are replaced by [names].
 */
internal object Config {

    private val satConfig = listOf(
        "elimreleff" to 10,
        "stabilizeonly" to 1,
        "subsumereleff" to 60,
    )

    private val unsatConfig = listOf(
        "stabilize" to 0,
        "walk" to 0,
    )

    val names = listOf("default", "plain", "sat", "unsat")

    fun has(name: String): Boolean = name in names

    fun set(opts: Options, name: String): Boolean {
        if (name == "default") {
            opts.resetDefaultValues()
            return true
        }
        if (name == "plain") {
            opts.disablePreprocessing()
            return true
        }
        val config = when (name) {
            "sat" -> satConfig
            "unsat" -> unsatConfig
            else -> return false
        }
        for ((optionName, value) in config) {
            check(Options.has(optionName) != null)
            opts.set(optionName, value)
        }
        return true
    }
}
