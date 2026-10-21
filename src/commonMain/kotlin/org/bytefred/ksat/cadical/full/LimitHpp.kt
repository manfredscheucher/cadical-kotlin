package org.bytefred.ksat.cadical.full

/*
 * limit.hpp plus the constructors 'Limit ()', 'Last ()', 'Inc ()' of limit.cpp.
 *
 * Mapping: the constructors 'memset (this, 0, ...)', which gives the zero initial values here.
 * Anonymous nested structs -> nested classes with the same member names ('lim.terminate.check',
 * 'last.elim.fixed', ...). 'int64_t rephased[2]' -> LongArray(2).
 */
internal class Limit {
    var initialized = false
    var conflicts = 0L // conflict limit if non-negative
    var decisions = 0L // decision limit if non-negative
    var preprocessing = 0L // limit on preprocessing rounds
    var localsearch = 0L // limit on local search rounds
    var compact = 0L // conflict limit for next 'compact'
    var condition = 0L // conflict limit for next 'condition'
    var elim = 0L // conflict limit for next 'elim'
    var flush = 0L // conflict limit for next 'flush'
    var probe = 0L // conflict limit for next 'probe'
    var reduce = 0L // conflict limit for next 'reduce'
    var rephase = 0L // conflict limit for next 'rephase'
    var report = 0L // report limit for header
    var restart = 0L // conflict limit for next 'restart'
    var stabilize = 0L // conflict limit for next 'stabilize'
    var subsume = 0L // conflict limit for next 'subsume'

    var keptsize = 0 // maximum kept size in 'reduce'
    var keptglue = 0 // maximum kept glue in 'reduce'

    // How often rephased during (1) or out (0) of stabilization.
    val rephased = LongArray(2)

    // Current elimination bound per eliminated variable.
    var elimbound = 0L

    class Terminate {
        var check = 0 // countdown to next terminator call
        var forced = 0 // forced termination for testing
    }

    val terminate = Terminate()
}

internal class Last {
    class Propagations {
        var propagations = 0L
    }

    class Elim {
        var fixed = 0L
        var subsumephases = 0L
        var marked = 0L
    }

    class Probe {
        var propagations = 0L
        var reductions = 0L
    }

    class Conflicts {
        var conflicts = 0L
    }

    class Marked {
        var marked = 0L
    }

    class Fixed {
        var fixed = 0L
    }

    val transred = Propagations()
    val vivify = Propagations()
    val elim = Elim()
    val probe = Probe()
    val reduce = Conflicts()
    val rephase = Conflicts()
    val ternary = Marked()
    val collect = Fixed()
}

internal class Inc {
    var flush = 0L // flushing interval in terms of conflicts
    var stabilize = 0L // stabilization interval increment
    var conflicts = -1L // next conflict limit if non-negative (-1 = unlimited)
    var decisions = -1L // next decision limit if non-negative (-1 = unlimited)
    var preprocessing = 0L // next preprocessing limit if non-negative
    var localsearch = 0L // next local search limit if non-negative
}
