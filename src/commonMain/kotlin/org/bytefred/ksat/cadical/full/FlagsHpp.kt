package org.bytefred.ksat.cadical.full

/*
 * flags.hpp: variable and literal flags.
 *
 * Mapping: 'bool x : 1' -> Boolean; 'unsigned char x : 2' / ': 3' -> Int. Upstream only stores
 * values that fit the bit width (block/skip/assumed/failed/decompose are sets of 'bign' bits
 * 1 and 2, status is one of the constants below), so no truncation is needed.
 * C++ struct assignment 'a = b' copies: never alias two table slots ('compact' moves the
 * references without aliasing, see Compact.kt).
 */
internal class Flags {
    // The first set of flags is related to 'analyze' and 'minimize'.
    var seen = false // seen in generating first UIP clause in 'analyze'
    var keep = false // keep in learned clause in 'minimize'
    var poison = false // can not be removed in 'minimize'
    var removable = false // can be removed in 'minimize'
    var shrinkable = false // can be removed in 'shrink'
    var added = false // has already been added to lrat_chain (in 'minimize')
    var ignorepos = false // decompose need to dif between pos/neg lit
    var ignoreneg = false // decompose

    // These three variable flags are used to schedule clauses in subsumption
    // ('subsume'), variables in bounded variable elimination ('elim') and in
    // hyper ternary resolution ('ternary').
    var elim = true // removed since last 'elim' round (*)
    var subsume = true // added since last 'subsume' round (*)
    var ternary = true // added in ternary clause since last 'ternary' (*)
    var decompose = 0 // generate correct LRAT chains in decompose (2 bits)

    // These literal flags are used by blocked clause elimination ('block').
    var block = 3 // removed since last 'block' round (*) (2 bits)
    var skip = 0 // skip this literal as blocking literal (2 bits)

    // Bits for handling assumptions.
    var assumed = 0 // 2 bits
    var failed = 0 // 0 if not part of failure, 1 if positive lit, 2 if negated lit (2 bits)

    var status = UNUSED // 3 bits

    fun unused(): Boolean = status == UNUSED
    fun active(): Boolean = status == ACTIVE
    fun fixed(): Boolean = status == FIXED
    fun eliminated(): Boolean = status == ELIMINATED
    fun substituted(): Boolean = status == SUBSTITUTED
    fun pure(): Boolean = status == PURE

    // The flags marked with '(*)' are copied during 'External::copy_flags',
    // which in essence means they are reset in the copy if they were clear.
    // This avoids the effort of fruitless preprocessing the copy.
    fun copy(dst: Flags) {
        dst.elim = elim
        dst.subsume = subsume
        dst.ternary = ternary
        dst.block = block
    }

    companion object {
        const val UNUSED = 0
        const val ACTIVE = 1
        const val FIXED = 2
        const val ELIMINATED = 3
        const val SUBSTITUTED = 4
        const val PURE = 5
    }
}
