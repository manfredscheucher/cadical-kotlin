package org.bytefred.ksat.cadical.full

import kotlin.math.abs
import org.bytefred.ksat.cadical.BooleanList
import org.bytefred.ksat.cadical.IntArrayList

/*
 * external.hpp: the 'External' layer mapping external variables to internal literals, plus
 * its constructor from external.cpp and the inline member functions of the header (and
 * 'External::fixed', which upstream defines at the end of internal.hpp).
 *
 * All other member functions are declared in external.hpp but defined in external.cpp,
 * extend.cpp, restore.cpp, solution.cpp, ...; they are Kotlin extension functions
 * 'internal fun External.foo (...)' in the matching '.kt' file (see PORTING.md).
 *
 * Mapping:
 *  - 'vector<bool>' -> BooleanList, 'vector<int>' / 'vector<unsigned>' -> IntArrayList
 *    ('frozentab' holds the unsigned bit pattern), 'vector<uint64_t>' -> ArrayList<Long>.
 *  - 'size_t vsize' -> Int.
 *  - 'unordered_map<uint64_t, vector<int>> forgettable_original' -> LinkedHashMap. Upstream
 *    iterates it only to check models and to feed the internal checker, where the order does
 *    not matter; the iteration order of the two maps differs.
 *  - 'signed char *solution' -> ByteArray? (debugging only, null by default).
 *  - The 'check_learned_*' / 'check_shrunken_clause' inline wrappers call checking functions
 *    of solution.cpp / external.cpp and are ported together with them.
 */
internal class External(val internal: Internal) {

    /*==== start of state ==================================================*/

    var maxVar = 0 // External maximum variable index.
    var vsize = 0 // Allocated external size.

    val vals = BooleanList() // Current external (extended) assignment.
    val e2i = IntArrayList() // External 'idx' to internal 'lit'.

    val assumptions = IntArrayList() // External assumptions.
    val constraint = IntArrayList() // External constraint. Terminated by zero.

    val extUnits = ArrayList<Long>() // External units. Needed to compute LRAT for eclause
    val extFlags = BooleanList() // to avoid duplicate units
    val eclause = IntArrayList() // External version of original input clause.

    // The extension stack for reconstructing complete satisfying assignments
    // (models) of the original external formula is kept in this external
    // solver object. It keeps track of blocked clauses and clauses containing
    // eliminated variable.  These irredundant clauses are stored in terms of
    // external literals on the 'extension' stack after mapping the
    // internal literals given as arguments with 'externalize'.
    var extended = false // Have been extended.
    var concluded = false
    val extension = IntArrayList() // Solution reconstruction extension stack.

    val witness = BooleanList() // Literal witness on extension stack.
    val tainted = BooleanList() // Literal tainted in adding literals.

    val frozentab = IntArrayList() // Reference counts for frozen variables (unsigned).

    // Regularly checked terminator if non-zero.  The terminator is set from
    // 'Solver::set (Terminator *)' and checked by 'Internal::terminating ()'.
    var terminator: Terminator? = null

    // If there is a learner export learned clauses.
    var learner: Learner? = null

    // If there is a listener for fixed assignments.
    var fixedListener: FixedAssignmentListener? = null

    // If there is an external propagator.
    var propagator: ExternalPropagator? = null

    val isObserved = BooleanList() // Quick flag for each external variable

    // Saved 'forgettable' original clauses coming from the external
    // propagator. The value of the map starts with a Boolean flag indicating
    // if the clause is still present or got already deleted, and then
    // followed by the literals of the clause.
    val forgettableOriginal = LinkedHashMap<Long, IntArrayList>()

    //----------------------------------------------------------------------//

    var solution: ByteArray? = null // Given solution checking for debugging.
    val original = IntArrayList() // Saved original formula for checking.

    // If 'opts.checkfrozen' is set make sure that only literals are added
    // which were never completely molten before.  These molten literals are
    // marked at the beginning of the 'solve' call.  Note that variables
    // larger than 'max_var' are not molten and can thus always be used in the
    // future.  Only needed to check and debug old style freeze semantics.
    val moltentab = BooleanList()

    //----------------------------------------------------------------------//

    val vars = Range { maxVar } // Provides safe variable iterations.

    /*==== end of state ====================================================*/

    init {
        check(internal.external == null)
        internal.external = this
    }

    // These two just factor out common sanity (assertion) checking code.

    fun vidx(elit: Int): Int {
        check(elit != 0)
        check(elit != Int.MIN_VALUE)
        val res = abs(elit)
        check(res <= maxVar)
        return res
    }

    fun vlit(elit: Int): Int {
        check(elit != 0)
        check(elit != Int.MIN_VALUE)
        check(abs(elit) <= maxVar)
        return elit
    }

    /*----------------------------------------------------------------------*/

    // Marking external literals.

    fun elit2ulit(elit: Int): Int {
        check(elit != 0)
        check(elit != Int.MIN_VALUE)
        val idx = abs(elit) - 1
        check(idx <= maxVar)
        return 2 * idx + (if (elit < 0) 1 else 0)
    }

    fun marked(map: BooleanList, elit: Int): Boolean {
        val ulit = elit2ulit(elit)
        return if (ulit < map.size) map[ulit] else false
    }

    fun mark(map: BooleanList, elit: Int) {
        val ulit = elit2ulit(elit)
        if (ulit >= map.size) map.resize(ulit + 1, false)
        map[ulit] = true
    }

    fun unmark(map: BooleanList, elit: Int) {
        val ulit = elit2ulit(elit)
        if (ulit < map.size) map[ulit] = false
    }

    /*----------------------------------------------------------------------*/

    fun frozen(elit: Int): Boolean {
        check(elit != 0)
        check(elit != Int.MIN_VALUE)
        val eidx = abs(elit)
        if (eidx > maxVar) return false
        if (eidx >= frozentab.size) return false
        return frozentab[eidx] != 0
    }

    // We call it 'ival' as abbreviation for 'val' with 'int' return type to
    // avoid bugs due to using 'signed char tmp = val (lit)', which might turn
    // a negative value into a positive one (happened in 'extend').
    fun ival(elit: Int): Int {
        check(elit != Int.MIN_VALUE)
        val eidx = abs(elit)
        var v = false
        if (eidx <= maxVar && eidx < vals.size) v = vals[eidx]
        if (elit < 0) v = !v
        return if (v) elit else -elit
    }

    // Implemented in 'internal.hpp' upstream.
    fun fixed(elit: Int): Int {
        check(elit != 0)
        check(elit != Int.MIN_VALUE)
        val eidx = abs(elit)
        if (eidx > maxVar) return 0
        var ilit = e2i[eidx]
        if (ilit == 0) return 0
        if (elit < 0) ilit = -ilit
        return internal.fixed(ilit)
    }

    /*----------------------------------------------------------------------*/

    // For debugging and testing only.  See 'solution.hpp' for more details.
    fun sol(elit: Int): Int {
        val solution = checkNotNull(solution)
        check(elit != Int.MIN_VALUE)
        val eidx = abs(elit)
        if (eidx > maxVar) return 0
        var value = solution[eidx].toInt()
        if (value == 0) return 0
        if (elit < 0) value = -value
        return if (value > 0) elit else -elit
    }
}
