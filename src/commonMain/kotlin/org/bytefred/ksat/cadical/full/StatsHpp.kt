package org.bytefred.ksat.cadical.full

/*
 * stats.hpp plus the constructor 'Stats ()' of stats.cpp: all statistics counters.
 *
 * Mapping:
 *  - 'int64_t' counters -> Long, initialized to zero as the 'memset' of 'Stats ()';
 *    'walk.minimum = LONG_MAX' -> Long.MAX_VALUE. The constructor also stores the absolute
 *    real and process start time in 'time'; times only feed messages and are left zero.
 *  - Anonymous nested structs -> nested classes with the same member names in camelCase
 *    ('stats.ext_prop.eprop_call' -> 'stats.extProp.epropCall', 'stats.now.fixed', ...).
 *    Structs declared once for several members ('current, added', 'all, now', the lucky
 *    'constant, forward, backward') share one class.
 *  - 'Stats::print' (stats.cpp) is message output and not ported.
 */
internal class Stats {
    var vars = 0L // internal initialized variables
    var conflicts = 0L // generated conflicts in 'propagate'
    var decisions = 0L // number of decisions in 'decide'
    class Propagations {
        var cover = 0L // propagated during covered clause elimination
        var instantiate = 0L // propagated during variable instantiation
        var probe = 0L // propagated during probing
        var search = 0L // propagated literals during search
        var transred = 0L // propagated during transitive reduction
        var vivify = 0L // propagated during vivification
        var walk = 0L // propagated during local search
    }
    val propagations = Propagations()
    class ExtProp {
        var extCb = 0L // number of times any external callback was called
        var epropCall = 0L // number of times external_propagate was called
        var epropProp = 0L // number of times external propagate propagated
        var epropConf = 0L // number of times ex-propagate was already falsified
        var epropExpl = 0L // number of times external propagate was explained
        var elearnCall = 0L // number of times external clause learning was tried
        var elearned = 0L // learned external clauses (incl. eprop explanations)
        var elearnProp = 0L // number of learned and propagating external clauses
        var elearnConf = 0L // number of learned and conflicting external clauses
        var echeckCall = 0L // number of checking found complete solutions
    }
    val extProp = ExtProp()
    var condassinit = 0L // initial assigned literals
    var condassirem = 0L // initial assigned literals for blocked
    var condassrem = 0L // remaining assigned literals for blocked
    var condassvars = 0L // sum of active variables at initial assignment
    var condautinit = 0L // initial literals in autarky part
    var condautrem = 0L // remaining literals in autarky part for blocked
    var condcands = 0L // globally blocked candidate clauses
    var condcondinit = 0L // initial literals in conditional part
    var condcondrem = 0L // remaining literals in conditional part for blocked
    var conditioned = 0L // globally blocked clauses eliminated
    var conditionings = 0L // globally blocked clause eliminations
    var condprops = 0L // propagated unassigned literals
    class Mark {
        var block = 0L // block marked literals
        var elim = 0L // elim marked variables
        var subsume = 0L // subsume marked variables
        var ternary = 0L // ternary marked variables
    }
    val mark = Mark()
    class Clauses {
        var total = 0L
        var redundant = 0L
        var irredundant = 0L
    }
    val current = Clauses()
    val added = Clauses()
    class Time {
        var process = 0.0
        var real = 0.0
    }
    val time = Time()
    class Cover {
        var count = 0L // number of covered clause elimination rounds
        var asymmetric = 0L // number of asymmetric tautologies in CCE
        var blocked = 0L // number of blocked covered tautologies
        var total = 0L // total number of eliminated clauses
    }
    val cover = Cover()
    class Lucky {
        var tried = 0L
        var succeeded = 0L
        class OneZero {
            var one = 0L
            var zero = 0L
        }
        val constant = OneZero()
        val forward = OneZero()
        val backward = OneZero()
        class Horn {
            var positive = 0L
            var negative = 0L
        }
        val horn = Horn()
    }
    val lucky = Lucky()
    class Rephased {
        var total = 0L // total number of happened rephases
        var best = 0L // how often reset to best phases
        var flipped = 0L // how often reset phases by flipping
        var inverted = 0L // how often reset to inverted phases
        var original = 0L // how often reset to original phases
        var random = 0L // how often randomly reset phases
        var walk = 0L // phases improved through random walked
    }
    val rephased = Rephased()
    class Walk {
        var count = 0L
        var broken = 0L
        var flips = 0L
        var minimum = Long.MAX_VALUE
    }
    val walk = Walk()
    class Flush {
        var count = 0L // flushings of learned clauses counter
        var learned = 0L // flushed learned clauses
        var hyper = 0L // flushed hyper binary/ternary clauses
    }
    val flush = Flush()
    var compacts = 0L // number of compactifications
    var shuffled = 0L // shuffled queues and scores
    var restarts = 0L // actual number of happened restarts
    var restartlevels = 0L // levels at restart
    var restartstable = 0L // actual number of happened restarts
    var stabphases = 0L // number of stabilization phases
    var stabconflicts = 0L // number of search conflicts during stabilizing
    var rescored = 0L // number of times scores were rescored
    var reused = 0L // number of reused trails
    var reusedlevels = 0L // reused levels at restart
    var reusedstable = 0L // number of reused trails during stabilizing
    var sections = 0L // 'section' counter
    var chrono = 0L // chronological backtracks
    var backtracks = 0L // number of backtracks
    var improvedglue = 0L // improved glue during bumping
    var promoted1 = 0L // promoted clauses to tier one
    var promoted2 = 0L // promoted clauses to tier two
    var bumped = 0L // seen and bumped variables in 'analyze'
    var recomputed = 0L // recomputed glues 'recompute_glue'
    var searched = 0L // searched decisions in 'decide'
    var reductions = 0L // 'reduce' counter
    var reduced = 0L // number of reduced clauses
    var collected = 0L // number of collected bytes
    var collections = 0L // number of garbage collections
    var hbrs = 0L // hyper binary resolvents
    var hbrsizes = 0L // sum of hyper resolved base clauses
    var hbreds = 0L // redundant hyper binary resolvents
    var hbrsubs = 0L // subsuming hyper binary resolvents
    var instried = 0L // number of tried instantiations
    var instantiated = 0L // number of successful instantiations
    var instrounds = 0L // number of instantiation rounds
    var subsumed = 0L // number of subsumed clauses
    var deduplicated = 0L // number of removed duplicated binary clauses
    var deduplications = 0L // number of deduplication phases
    var strengthened = 0L // number of strengthened clauses
    var elimotfstr = 0L // number of on-the-fly strengthened during elimination
    var subirr = 0L // number of subsumed irredundant clauses
    var subred = 0L // number of subsumed redundant clauses
    var subtried = 0L // number of tried subsumptions
    var subchecks = 0L // number of pair-wise subsumption checks
    var subchecks2 = 0L // same but restricted to binary clauses
    var elimotfsub = 0L // number of on-the-fly subsumed during elimination
    var subsumerounds = 0L // number of subsumption rounds
    var subsumephases = 0L // number of scheduled subsumption phases
    var eagertried = 0L // number of traversed eager subsumed candidates
    var eagersub = 0L // number of eagerly subsumed recently learned clauses
    var elimres = 0L // number of resolved clauses in BVE
    var elimrestried = 0L // number of tried resolved clauses in BVE
    var elimrounds = 0L // number of elimination rounds
    var elimphases = 0L // number of scheduled elimination phases
    var elimcompleted = 0L // number complete elimination procedures
    var elimtried = 0L // number of variable elimination attempts
    var elimsubst = 0L // number of eliminations through substitutions
    var elimgates = 0L // number of gates found during elimination
    var elimequivs = 0L // number of equivalences found during elimination
    var elimands = 0L // number of AND gates found during elimination
    var elimites = 0L // number of ITE gates found during elimination
    var elimxors = 0L // number of XOR gates found during elimination
    var elimbwsub = 0L // number of eager backward subsumed clauses
    var elimbwstr = 0L // number of eager backward strengthened clauses
    var ternary = 0L // number of ternary resolution phases
    var ternres = 0L // number of ternary resolutions
    var htrs = 0L // number of hyper ternary resolvents
    var htrs2 = 0L // number of binary hyper ternary resolvents
    var htrs3 = 0L // number of ternary hyper ternary resolvents
    var decompositions = 0L // number of SCC + ELS
    var vivifications = 0L // number of vivifications
    var vivifychecks = 0L // checked clauses during vivification
    var vivifydecs = 0L // vivification decisions
    var vivifyreused = 0L // reused vivification decisions
    var vivifysched = 0L // scheduled clauses for vivification
    var vivifysubs = 0L // subsumed clauses during vivification
    var vivifystrs = 0L // strengthened clauses during vivification
    var vivifystrirr = 0L // strengthened irredundant clause
    var vivifystred1 = 0L // strengthened redundant clause (1)
    var vivifystred2 = 0L // strengthened redundant clause (2)
    var vivifystred3 = 0L // strengthened redundant clause (3)
    var vivifyunits = 0L // units during vivification
    var vivifyinst = 0L // instantiation during vivification
    var transreds = 0L
    var transitive = 0L
    class Learned {
        var literals = 0L
        var clauses = 0L
    }
    val learned = Learned()
    var minimized = 0L // minimized literals
    var shrunken = 0L // shrunken literals
    var minishrunken = 0L // shrunken during minimization literals
    var irrlits = 0L // literals in irredundant clauses
    class Garbage {
        var bytes = 0L
        var clauses = 0L
        var literals = 0L
    }
    val garbage = Garbage()
    var units = 0L // learned unit clauses
    var binaries = 0L // learned binary clauses
    var probingphases = 0L // number of scheduled probing phases
    var probingrounds = 0L // number of probing rounds
    var probesuccess = 0L // number successful probing phases
    var probed = 0L // number of probed literals
    var failed = 0L // number of failed literals
    var hyperunary = 0L // hyper unary resolved unit clauses
    var probefailed = 0L // failed literals from probing
    var transredunits = 0L // units derived in transitive reduction
    var blockings = 0L // number of blocked clause eliminations
    var blocked = 0L // number of actually blocked clauses
    var blockres = 0L // number of resolutions during blocking
    var blockcands = 0L // number of clause / pivot pairs tried
    var blockpured = 0L // number of clauses blocked through pure literals
    var blockpurelits = 0L // number of pure literals
    var extensions = 0L // number of extended witnesses
    var extended = 0L // number of flipped literals during extension
    var weakened = 0L // number of clauses pushed to extension stack
    var weakenedlen = 0L // lengths of weakened clauses
    var restorations = 0L // number of restore calls
    var restored = 0L // number of restored clauses
    var reactivated = 0L // number of reactivated clauses
    var restoredlits = 0L // number of restored literals
    var preprocessings = 0L
    var ilbtriggers = 0L
    var ilbsuccess = 0L
    var levelsreused = 0L
    var literalsreused = 0L
    var assumptionsreused = 0L
    class Vars {
        var fixed = 0L // number of top level assigned variables
        var eliminated = 0L // number of eliminated variables
        var substituted = 0L // number of substituted variables
        var pure = 0L // number of pure literals
    }
    val all = Vars()
    val now = Vars()
    class Otfs {
        var strengthened = 0L // number of clauses strengthened during OTFS
        var subsumed = 0L // number of clauses subsumed by OTFS
    }
    val otfs = Otfs()
    var unused = 0L // number of unused variables
    var active = 0L // number of active variables
    var inactive = 0L // number of inactive variables
}
