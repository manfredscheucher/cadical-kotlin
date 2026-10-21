package org.bytefred.ksat.cadical.full

/*
 * cadical.hpp: the public API types the internal layers use (status codes, solver states and
 * the call back interfaces). The 'Solver' class itself is ported with solver.cpp.
 *
 * Mapping:
 *  - 'enum Status', 'enum State' -> Int constants (they are combined as bit sets).
 *  - Abstract classes with pure virtual methods -> interfaces; virtual methods with a
 *    default body keep that body as interface default.
 *  - 'const std::vector<int> &' arguments -> 'List<Int>' snapshots for the call backs.
 *  - 'size_t new_level' -> Int. 'bool &is_forgettable' (out parameter) -> [OutFlag].
 *  - 'uint64_t id' -> Long.
 */

// The SAT competition standardized the exit code of SAT solvers.
internal const val SATISFIABLE = 10
internal const val UNSATISFIABLE = 20
internal const val UNKNOWN = 0

// States are represented by a bit-set in order to combine them.
internal const val INITIALIZING = 1 // during initialization (invalid)
internal const val CONFIGURING = 2 // configure options (with 'set')
internal const val STEADY = 4 // ready to call 'solve'
internal const val ADDING = 8 // adding clause literals (zero missing)
internal const val SOLVING = 16 // while solving (within 'solve')
internal const val SATISFIED = 32 // satisfiable allows 'val'
internal const val UNSATISFIED = 64 // unsatisfiable allows 'failed'
internal const val DELETING = 128 // during and after deletion (invalid)

// These combined states are used to check contracts.
internal const val READY = CONFIGURING or STEADY or SATISFIED or UNSATISFIED
internal const val VALID = READY or ADDING
internal const val INVALID = INITIALIZING or DELETING

/** Out parameter 'bool &' of the call back API. */
internal class OutFlag(var value: Boolean = false)

// 'terminate' function of the terminator returns true the solver is
// terminated synchronously as soon it calls this function.
internal interface Terminator {
    fun terminate(): Boolean
}

// Connected learners which can be used to export learned clauses.
// The 'learning' can check the size of the learn clause and only if it
// returns true then the individual literals of the learned clause are given
// to the learn through 'learn' one by one terminated by a zero literal.
internal interface Learner {
    fun learning(size: Int): Boolean
    fun learn(lit: Int)
}

// Connected listener gets notified whenever the truth value of a variable
// is fixed (for example during inprocessing or due to some derived unit
// clauses).
internal interface FixedAssignmentListener {
    fun notifyFixedAssignment(lit: Int)
}

// Allows to connect an external propagator to propagate values to variables
// with an external clause as a reason or to learn new clauses during the
// CDCL loop (without restart). See upstream 'cadical.hpp' for the contract of
// each call back.
internal interface ExternalPropagator {
    val isLazy: Boolean get() = false // lazy propagator only checks complete assignments
    val areReasonsForgettable: Boolean get() = false // Reason external clauses can be deleted

    fun notifyAssignment(lits: List<Int>)
    fun notifyNewDecisionLevel()
    fun notifyBacktrack(newLevel: Int)

    fun cbCheckFoundModel(model: List<Int>): Boolean

    fun cbDecide(): Int = 0

    fun cbPropagate(): Int = 0

    fun cbAddReasonClauseLit(propagatedLit: Int): Int = 0

    fun cbHasExternalClause(isForgettable: OutFlag): Boolean

    fun cbAddExternalClauseLit(): Int
}

// Allows to traverse all remaining irredundant clauses.  Satisfied and
// eliminated clauses are not included, nor any derived units unless such
// a unit literal is frozen. Falsified literals are skipped.  If the solver
// is inconsistent only the empty clause is traversed.
//
// If 'clause' returns false traversal aborts early.
internal interface ClauseIterator {
    fun clause(clause: List<Int>): Boolean
}

// Allows to traverse all clauses on the extension stack together with their
// witness cubes.  If the solver is inconsistent, i.e., an empty clause is
// found and the formula is unsatisfiable, then nothing is traversed.
//
// If 'witness' returns false traversal aborts early.
internal interface WitnessIterator {
    fun witness(clause: List<Int>, witness: List<Int>, id: Long = 0): Boolean
}
