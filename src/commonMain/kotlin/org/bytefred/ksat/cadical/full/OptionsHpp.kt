package org.bytefred.ksat.cadical.full

/*
 * options.hpp plus options.cpp: all run-time options with the upstream defaults and bounds.
 *
 * Mapping:
 *  - The 'OPTIONS' macro table -> [Options.table] (same order, which is sorted by name, as
 *    'has' needs for its binary search) and one typed Int property per option
 *    ('opts.reducetier1glue', ...). Upstream lays the 'int' members out directly after
 *    '__start_of_options__' and accesses them by index through 'val (idx)'; here the
 *    properties are views on [values], so 'val (idx)' is 'values[idx]'.
 *  - Defaults like '1e5' / '2e9' are the '(int) V' casts of upstream.
 *  - 'LOGOPT' options ('log', 'logsort') exist only with LOGGING and are left out as in the
 *    upstream release build. 'QUTOPT' options ('quiet', 'verbose') are present (QUIET is not
 *    defined upstream by default).
 *  - [Option.resettable] is the 'R' column, which upstream only uses inside the macro
 *    expansion of 'reset_default_values'; it is stored in the table here.
 *  - 'reportdefault' is 0 (library usage) as upstream; the stand alone app would set 1.
 *  - 'initialize_from_environment' ('CADICAL_<NAME>' environment variables) needs getenv,
 *    which is not available in Kotlin common code, and is not ported.
 *  - 'print' / 'usage' are message output and not ported.
 */
internal class Option(
    val name: String,
    val def: Int,
    val lo: Int,
    val hi: Int,
    val optimizable: Int,
    val preprocessing: Boolean,
    val resettable: Boolean,
    val description: String,
)

internal class Options {

    val values = IntArray(NUMBER_OF_OPTIONS)

    // Initialize all the options to their default value 'V'.
    init {
        // The table is rebuilt in every constructor as upstream (it reads 'reportdefault').
        table = buildTable()
        // '#ifndef NDEBUG' consistency asserts ('i == number_of_options', '!has (...)'): not in release.
        var prev = ""
        for (i in 0 until NUMBER_OF_OPTIONS) {
            val o = table[i]
            check(o.lo <= o.def) { "'${o.name}' default '${o.def}' lower minimum '${o.lo}' in 'options.hpp'" }
            check(o.hi >= o.def) { "'${o.name}' default '${o.def}' larger maximum '${o.hi}' in 'options.hpp'" }
            check(prev <= o.name) { "'$prev' ordered before '${o.name}' in 'options.hpp'" }
            values[i] = o.def
            prev = o.name
        }
    }

    // Force to [lo,hi] interval.
    fun set(o: Option, newValue: Int) {
        val idx = indexOf(o)
        val oldVal = values[idx]
        if (oldVal == newValue) return
        var newVal = newValue
        if (newVal < o.lo) newVal = o.lo
        if (newVal > o.hi) newVal = o.hi
        values[idx] = newVal
    }

    // Explicit version.
    fun set(name: String, v: Int): Boolean {
        val o = has(name) ?: return false
        set(o, v)
        return true
    }

    // Get current value.
    fun get(name: String): Int {
        val o = has(name) ?: return 0
        return values[indexOf(o)]
    }

    // increase some limits (val=0..31)
    fun optimize(v: Int) {
        if (v < 0) return
        val maxVal = 31
        val value = if (v > maxVal) maxVal else v
        var factor2 = 1L
        run {
            var i = 0
            while (i < value && factor2 <= Int.MAX_VALUE) {
                factor2 *= 2
                i++
            }
        }
        var factor10 = 1L
        run {
            var i = 0
            while (i < value && factor10 <= Int.MAX_VALUE) {
                factor10 *= 10
                i++
            }
        }
        for (i in 0 until NUMBER_OF_OPTIONS) {
            val o = table[i]
            if (o.optimizable == 0) continue
            val factor = if (o.optimizable == 1) factor2 else factor10
            var newVal = factor * o.def.toLong()
            if (newVal > o.hi) newVal = o.hi.toLong()
            if (newVal == o.def.toLong()) continue
            check(newVal <= Int.MAX_VALUE)
            values[i] = newVal.toInt()
        }
    }

    fun disablePreprocessing() {
        for (i in 0 until NUMBER_OF_OPTIONS) {
            val o = table[i]
            if (!o.preprocessing) continue
            if (values[i] == 0) continue
            check(o.lo == 0)
            check(o.hi == 1)
            values[i] = 0
        }
    }

    fun resetDefaultValues() {
        for (i in 0 until NUMBER_OF_OPTIONS) {
            val o = table[i]
            if (!o.resettable) continue
            if (values[i] == o.def) continue
            values[i] = o.def
        }
    }

    // Copy 'this' into 'other'.
    fun copy(other: Options) {
        for (i in 0 until NUMBER_OF_OPTIONS) {
            if (values[i] != table[i].def) other.values[i] = values[i]
        }
    }

    // Makes options directly accessible, e.g., 'opts.restart'.

    var arena: Int
        get() = values[0]
        set(v) { values[0] = v }

    var arenacompact: Int
        get() = values[1]
        set(v) { values[1] = v }

    var arenasort: Int
        get() = values[2]
        set(v) { values[2] = v }

    var arenatype: Int
        get() = values[3]
        set(v) { values[3] = v }

    var binary: Int
        get() = values[4]
        set(v) { values[4] = v }

    var block: Int
        get() = values[5]
        set(v) { values[5] = v }

    var blockmaxclslim: Int
        get() = values[6]
        set(v) { values[6] = v }

    var blockminclslim: Int
        get() = values[7]
        set(v) { values[7] = v }

    var blockocclim: Int
        get() = values[8]
        set(v) { values[8] = v }

    var bump: Int
        get() = values[9]
        set(v) { values[9] = v }

    var bumpreason: Int
        get() = values[10]
        set(v) { values[10] = v }

    var bumpreasondepth: Int
        get() = values[11]
        set(v) { values[11] = v }

    var check: Int
        get() = values[12]
        set(v) { values[12] = v }

    var checkassumptions: Int
        get() = values[13]
        set(v) { values[13] = v }

    var checkconstraint: Int
        get() = values[14]
        set(v) { values[14] = v }

    var checkfailed: Int
        get() = values[15]
        set(v) { values[15] = v }

    var checkfrozen: Int
        get() = values[16]
        set(v) { values[16] = v }

    var checkproof: Int
        get() = values[17]
        set(v) { values[17] = v }

    var checkwitness: Int
        get() = values[18]
        set(v) { values[18] = v }

    var chrono: Int
        get() = values[19]
        set(v) { values[19] = v }

    var chronoalways: Int
        get() = values[20]
        set(v) { values[20] = v }

    var chronolevelim: Int
        get() = values[21]
        set(v) { values[21] = v }

    var chronoreusetrail: Int
        get() = values[22]
        set(v) { values[22] = v }

    var compact: Int
        get() = values[23]
        set(v) { values[23] = v }

    var compactint: Int
        get() = values[24]
        set(v) { values[24] = v }

    var compactlim: Int
        get() = values[25]
        set(v) { values[25] = v }

    var compactmin: Int
        get() = values[26]
        set(v) { values[26] = v }

    var condition: Int
        get() = values[27]
        set(v) { values[27] = v }

    var conditionint: Int
        get() = values[28]
        set(v) { values[28] = v }

    var conditionmaxeff: Int
        get() = values[29]
        set(v) { values[29] = v }

    var conditionmaxrat: Int
        get() = values[30]
        set(v) { values[30] = v }

    var conditionmineff: Int
        get() = values[31]
        set(v) { values[31] = v }

    var conditionreleff: Int
        get() = values[32]
        set(v) { values[32] = v }

    var cover: Int
        get() = values[33]
        set(v) { values[33] = v }

    var covermaxclslim: Int
        get() = values[34]
        set(v) { values[34] = v }

    var covermaxeff: Int
        get() = values[35]
        set(v) { values[35] = v }

    var coverminclslim: Int
        get() = values[36]
        set(v) { values[36] = v }

    var covermineff: Int
        get() = values[37]
        set(v) { values[37] = v }

    var coverreleff: Int
        get() = values[38]
        set(v) { values[38] = v }

    var decompose: Int
        get() = values[39]
        set(v) { values[39] = v }

    var decomposerounds: Int
        get() = values[40]
        set(v) { values[40] = v }

    var deduplicate: Int
        get() = values[41]
        set(v) { values[41] = v }

    var eagersubsume: Int
        get() = values[42]
        set(v) { values[42] = v }

    var eagersubsumelim: Int
        get() = values[43]
        set(v) { values[43] = v }

    var elim: Int
        get() = values[44]
        set(v) { values[44] = v }

    var elimands: Int
        get() = values[45]
        set(v) { values[45] = v }

    var elimaxeff: Int
        get() = values[46]
        set(v) { values[46] = v }

    var elimbackward: Int
        get() = values[47]
        set(v) { values[47] = v }

    var elimboundmax: Int
        get() = values[48]
        set(v) { values[48] = v }

    var elimboundmin: Int
        get() = values[49]
        set(v) { values[49] = v }

    var elimclslim: Int
        get() = values[50]
        set(v) { values[50] = v }

    var elimequivs: Int
        get() = values[51]
        set(v) { values[51] = v }

    var elimineff: Int
        get() = values[52]
        set(v) { values[52] = v }

    var elimint: Int
        get() = values[53]
        set(v) { values[53] = v }

    var elimites: Int
        get() = values[54]
        set(v) { values[54] = v }

    var elimlimited: Int
        get() = values[55]
        set(v) { values[55] = v }

    var elimocclim: Int
        get() = values[56]
        set(v) { values[56] = v }

    var elimprod: Int
        get() = values[57]
        set(v) { values[57] = v }

    var elimreleff: Int
        get() = values[58]
        set(v) { values[58] = v }

    var elimrounds: Int
        get() = values[59]
        set(v) { values[59] = v }

    var elimsubst: Int
        get() = values[60]
        set(v) { values[60] = v }

    var elimsum: Int
        get() = values[61]
        set(v) { values[61] = v }

    var elimxorlim: Int
        get() = values[62]
        set(v) { values[62] = v }

    var elimxors: Int
        get() = values[63]
        set(v) { values[63] = v }

    var emagluefast: Int
        get() = values[64]
        set(v) { values[64] = v }

    var emaglueslow: Int
        get() = values[65]
        set(v) { values[65] = v }

    var emajump: Int
        get() = values[66]
        set(v) { values[66] = v }

    var emalevel: Int
        get() = values[67]
        set(v) { values[67] = v }

    var emasize: Int
        get() = values[68]
        set(v) { values[68] = v }

    var ematrailfast: Int
        get() = values[69]
        set(v) { values[69] = v }

    var ematrailslow: Int
        get() = values[70]
        set(v) { values[70] = v }

    var exteagerreasons: Int
        get() = values[71]
        set(v) { values[71] = v }

    var exteagerrecalc: Int
        get() = values[72]
        set(v) { values[72] = v }

    var externallrat: Int
        get() = values[73]
        set(v) { values[73] = v }

    var flush: Int
        get() = values[74]
        set(v) { values[74] = v }

    var flushfactor: Int
        get() = values[75]
        set(v) { values[75] = v }

    var flushint: Int
        get() = values[76]
        set(v) { values[76] = v }

    var forcephase: Int
        get() = values[77]
        set(v) { values[77] = v }

    var frat: Int
        get() = values[78]
        set(v) { values[78] = v }

    var idrup: Int
        get() = values[79]
        set(v) { values[79] = v }

    var ilb: Int
        get() = values[80]
        set(v) { values[80] = v }

    var ilbassumptions: Int
        get() = values[81]
        set(v) { values[81] = v }

    var inprocessing: Int
        get() = values[82]
        set(v) { values[82] = v }

    var instantiate: Int
        get() = values[83]
        set(v) { values[83] = v }

    var instantiateclslim: Int
        get() = values[84]
        set(v) { values[84] = v }

    var instantiateocclim: Int
        get() = values[85]
        set(v) { values[85] = v }

    var instantiateonce: Int
        get() = values[86]
        set(v) { values[86] = v }

    var lidrup: Int
        get() = values[87]
        set(v) { values[87] = v }

    var lrat: Int
        get() = values[88]
        set(v) { values[88] = v }

    var lucky: Int
        get() = values[89]
        set(v) { values[89] = v }

    var minimize: Int
        get() = values[90]
        set(v) { values[90] = v }

    var minimizedepth: Int
        get() = values[91]
        set(v) { values[91] = v }

    var otfs: Int
        get() = values[92]
        set(v) { values[92] = v }

    var phase: Int
        get() = values[93]
        set(v) { values[93] = v }

    var probe: Int
        get() = values[94]
        set(v) { values[94] = v }

    var probehbr: Int
        get() = values[95]
        set(v) { values[95] = v }

    var probeint: Int
        get() = values[96]
        set(v) { values[96] = v }

    var probemaxeff: Int
        get() = values[97]
        set(v) { values[97] = v }

    var probemineff: Int
        get() = values[98]
        set(v) { values[98] = v }

    var probereleff: Int
        get() = values[99]
        set(v) { values[99] = v }

    var proberounds: Int
        get() = values[100]
        set(v) { values[100] = v }

    var profile: Int
        get() = values[101]
        set(v) { values[101] = v }

    var quiet: Int
        get() = values[102]
        set(v) { values[102] = v }

    var radixsortlim: Int
        get() = values[103]
        set(v) { values[103] = v }

    var realtime: Int
        get() = values[104]
        set(v) { values[104] = v }

    var reduce: Int
        get() = values[105]
        set(v) { values[105] = v }

    var reduceint: Int
        get() = values[106]
        set(v) { values[106] = v }

    var reducetarget: Int
        get() = values[107]
        set(v) { values[107] = v }

    var reducetier1glue: Int
        get() = values[108]
        set(v) { values[108] = v }

    var reducetier2glue: Int
        get() = values[109]
        set(v) { values[109] = v }

    var reluctant: Int
        get() = values[110]
        set(v) { values[110] = v }

    var reluctantmax: Int
        get() = values[111]
        set(v) { values[111] = v }

    var rephase: Int
        get() = values[112]
        set(v) { values[112] = v }

    var rephaseint: Int
        get() = values[113]
        set(v) { values[113] = v }

    var report: Int
        get() = values[114]
        set(v) { values[114] = v }

    var reportall: Int
        get() = values[115]
        set(v) { values[115] = v }

    var reportsolve: Int
        get() = values[116]
        set(v) { values[116] = v }

    var restart: Int
        get() = values[117]
        set(v) { values[117] = v }

    var restartint: Int
        get() = values[118]
        set(v) { values[118] = v }

    var restartmargin: Int
        get() = values[119]
        set(v) { values[119] = v }

    var restartreusetrail: Int
        get() = values[120]
        set(v) { values[120] = v }

    var restoreall: Int
        get() = values[121]
        set(v) { values[121] = v }

    var restoreflush: Int
        get() = values[122]
        set(v) { values[122] = v }

    var reverse: Int
        get() = values[123]
        set(v) { values[123] = v }

    var score: Int
        get() = values[124]
        set(v) { values[124] = v }

    var scorefactor: Int
        get() = values[125]
        set(v) { values[125] = v }

    var seed: Int
        get() = values[126]
        set(v) { values[126] = v }

    var shrink: Int
        get() = values[127]
        set(v) { values[127] = v }

    var shrinkreap: Int
        get() = values[128]
        set(v) { values[128] = v }

    var shuffle: Int
        get() = values[129]
        set(v) { values[129] = v }

    var shufflequeue: Int
        get() = values[130]
        set(v) { values[130] = v }

    var shufflerandom: Int
        get() = values[131]
        set(v) { values[131] = v }

    var shufflescores: Int
        get() = values[132]
        set(v) { values[132] = v }

    var stabilize: Int
        get() = values[133]
        set(v) { values[133] = v }

    var stabilizefactor: Int
        get() = values[134]
        set(v) { values[134] = v }

    var stabilizeint: Int
        get() = values[135]
        set(v) { values[135] = v }

    var stabilizemaxint: Int
        get() = values[136]
        set(v) { values[136] = v }

    var stabilizeonly: Int
        get() = values[137]
        set(v) { values[137] = v }

    var stats: Int
        get() = values[138]
        set(v) { values[138] = v }

    var subsume: Int
        get() = values[139]
        set(v) { values[139] = v }

    var subsumebinlim: Int
        get() = values[140]
        set(v) { values[140] = v }

    var subsumeclslim: Int
        get() = values[141]
        set(v) { values[141] = v }

    var subsumeint: Int
        get() = values[142]
        set(v) { values[142] = v }

    var subsumelimited: Int
        get() = values[143]
        set(v) { values[143] = v }

    var subsumemaxeff: Int
        get() = values[144]
        set(v) { values[144] = v }

    var subsumemineff: Int
        get() = values[145]
        set(v) { values[145] = v }

    var subsumeocclim: Int
        get() = values[146]
        set(v) { values[146] = v }

    var subsumereleff: Int
        get() = values[147]
        set(v) { values[147] = v }

    var subsumestr: Int
        get() = values[148]
        set(v) { values[148] = v }

    var target: Int
        get() = values[149]
        set(v) { values[149] = v }

    var terminateint: Int
        get() = values[150]
        set(v) { values[150] = v }

    var ternary: Int
        get() = values[151]
        set(v) { values[151] = v }

    var ternarymaxadd: Int
        get() = values[152]
        set(v) { values[152] = v }

    var ternarymaxeff: Int
        get() = values[153]
        set(v) { values[153] = v }

    var ternarymineff: Int
        get() = values[154]
        set(v) { values[154] = v }

    var ternaryocclim: Int
        get() = values[155]
        set(v) { values[155] = v }

    var ternaryreleff: Int
        get() = values[156]
        set(v) { values[156] = v }

    var ternaryrounds: Int
        get() = values[157]
        set(v) { values[157] = v }

    var transred: Int
        get() = values[158]
        set(v) { values[158] = v }

    var transredmaxeff: Int
        get() = values[159]
        set(v) { values[159] = v }

    var transredmineff: Int
        get() = values[160]
        set(v) { values[160] = v }

    var transredreleff: Int
        get() = values[161]
        set(v) { values[161] = v }

    var verbose: Int
        get() = values[162]
        set(v) { values[162] = v }

    var veripb: Int
        get() = values[163]
        set(v) { values[163] = v }

    var vivify: Int
        get() = values[164]
        set(v) { values[164] = v }

    var vivifyinst: Int
        get() = values[165]
        set(v) { values[165] = v }

    var vivifymaxeff: Int
        get() = values[166]
        set(v) { values[166] = v }

    var vivifymineff: Int
        get() = values[167]
        set(v) { values[167] = v }

    var vivifyonce: Int
        get() = values[168]
        set(v) { values[168] = v }

    var vivifyredeff: Int
        get() = values[169]
        set(v) { values[169] = v }

    var vivifyreleff: Int
        get() = values[170]
        set(v) { values[170] = v }

    var walk: Int
        get() = values[171]
        set(v) { values[171] = v }

    var walkmaxeff: Int
        get() = values[172]
        set(v) { values[172] = v }

    var walkmineff: Int
        get() = values[173]
        set(v) { values[173] = v }

    var walknonstable: Int
        get() = values[174]
        set(v) { values[174] = v }

    var walkredundant: Int
        get() = values[175]
        set(v) { values[175] = v }

    var walkreleff: Int
        get() = values[176]
        set(v) { values[176] = v }

    companion object {
        const val NUMBER_OF_OPTIONS = 177

        // For library usage we disable reporting by default while for the stand
        // alone SAT solver we enable it by default.
        var reportdefault = 0

        var table: Array<Option> = buildTable()
            private set

        private fun buildTable(): Array<Option> = arrayOf(
            Option("arena", 1, 0, 1, 0, false, true, "allocate clauses in arena"),
            Option("arenacompact", 1, 0, 1, 0, false, true, "keep clauses compact"),
            Option("arenasort", 1, 0, 1, 0, false, true, "sort clauses in arena"),
            Option("arenatype", 3, 1, 3, 0, false, true, "1=clause, 2=var, 3=queue"),
            Option("binary", 1, 0, 1, 0, false, true, "use binary proof format"),
            Option("block", 0, 0, 1, 0, true, true, "blocked clause elimination"),
            Option("blockmaxclslim", 100000, 1, 2000000000, 2, false, true, "maximum clause size"),
            Option("blockminclslim", 2, 2, 2000000000, 0, false, true, "minimum clause size"),
            Option("blockocclim", 100, 1, 2000000000, 2, false, true, "occurrence limit"),
            Option("bump", 1, 0, 1, 0, false, true, "bump variables"),
            Option("bumpreason", 1, 0, 1, 0, false, true, "bump reason literals too"),
            Option("bumpreasondepth", 1, 1, 3, 0, false, true, "bump reason depth"),
            Option("check", 0, 0, 1, 0, false, false, "enable internal checking"),
            Option("checkassumptions", 1, 0, 1, 0, false, false, "check assumptions satisfied"),
            Option("checkconstraint", 1, 0, 1, 0, false, false, "check constraint satisfied"),
            Option("checkfailed", 1, 0, 1, 0, false, false, "check failed literals form core"),
            Option("checkfrozen", 0, 0, 1, 0, false, false, "check all frozen semantics"),
            Option("checkproof", 3, 0, 3, 0, false, false, "1=drat, 2=lrat, 3=both"),
            Option("checkwitness", 1, 0, 1, 0, false, false, "check witness internally"),
            Option("chrono", 1, 0, 2, 0, false, true, "chronological backtracking"),
            Option("chronoalways", 0, 0, 1, 0, false, true, "force always chronological"),
            Option("chronolevelim", 100, 0, 2000000000, 0, false, true, "chronological level limit"),
            Option("chronoreusetrail", 1, 0, 1, 0, false, true, "reuse trail chronologically"),
            Option("compact", 1, 0, 1, 0, true, true, "compact internal variables"),
            Option("compactint", 2000, 1, 2000000000, 0, false, true, "compacting interval"),
            Option("compactlim", 100, 0, 1000, 0, false, true, "inactive limit per mille"),
            Option("compactmin", 100, 1, 2000000000, 0, false, true, "minimum inactive limit"),
            Option("condition", 0, 0, 1, 0, false, true, "globally blocked clause elim"),
            Option("conditionint", 10000, 1, 2000000000, 0, false, true, "initial conflict interval"),
            Option("conditionmaxeff", 10000000, 0, 2000000000, 1, false, true, "maximum condition efficiency"),
            Option("conditionmaxrat", 100, 1, 2000000000, 1, false, true, "maximum clause variable ratio"),
            Option("conditionmineff", 1000000, 0, 2000000000, 1, false, true, "minimum condition efficiency"),
            Option("conditionreleff", 100, 1, 100000, 0, false, true, "relative efficiency per mille"),
            Option("cover", 0, 0, 1, 0, true, true, "covered clause elimination"),
            Option("covermaxclslim", 100000, 1, 2000000000, 2, false, true, "maximum clause size"),
            Option("covermaxeff", 100000000, 0, 2000000000, 1, false, true, "maximum cover efficiency"),
            Option("coverminclslim", 2, 2, 2000000000, 0, false, true, "minimum clause size"),
            Option("covermineff", 1000000, 0, 2000000000, 1, false, true, "minimum cover efficiency"),
            Option("coverreleff", 4, 1, 100000, 1, false, true, "relative efficiency per mille"),
            Option("decompose", 1, 0, 1, 0, true, true, "decompose BIG in SCCs and ELS"),
            Option("decomposerounds", 2, 1, 16, 1, false, true, "number of decompose rounds"),
            Option("deduplicate", 1, 0, 1, 0, true, true, "remove duplicated binaries"),
            Option("eagersubsume", 1, 0, 1, 0, false, true, "subsume recently learned"),
            Option("eagersubsumelim", 20, 1, 1000, 0, false, true, "limit on subsumed candidates"),
            Option("elim", 1, 0, 1, 0, true, true, "bounded variable elimination"),
            Option("elimands", 1, 0, 1, 0, false, true, "find AND gates"),
            Option("elimaxeff", 2000000000, 0, 2000000000, 1, false, true, "maximum elimination efficiency"),
            Option("elimbackward", 1, 0, 1, 0, false, true, "eager backward subsumption"),
            Option("elimboundmax", 16, -1, 2000000, 1, false, true, "maximum elimination bound"),
            Option("elimboundmin", 0, -1, 2000000, 0, false, true, "minimum elimination bound"),
            Option("elimclslim", 100, 2, 2000000000, 2, false, true, "resolvent size limit"),
            Option("elimequivs", 1, 0, 1, 0, false, true, "find equivalence gates"),
            Option("elimineff", 10000000, 0, 2000000000, 1, false, true, "minimum elimination efficiency"),
            Option("elimint", 2000, 1, 2000000000, 0, false, true, "elimination interval"),
            Option("elimites", 1, 0, 1, 0, false, true, "find if-then-else gates"),
            Option("elimlimited", 1, 0, 1, 0, false, true, "limit resolutions"),
            Option("elimocclim", 100, 0, 2000000000, 2, false, true, "occurrence limit"),
            Option("elimprod", 1, 0, 10000, 0, false, true, "elim score product weight"),
            Option("elimreleff", 1000, 1, 100000, 1, false, true, "relative efficiency per mille"),
            Option("elimrounds", 2, 1, 512, 1, false, true, "usual number of rounds"),
            Option("elimsubst", 1, 0, 1, 0, false, true, "elimination by substitution"),
            Option("elimsum", 1, 0, 10000, 0, false, true, "elimination score sum weight"),
            Option("elimxorlim", 5, 2, 27, 1, false, true, "maximum XOR size"),
            Option("elimxors", 1, 0, 1, 0, false, true, "find XOR gates"),
            Option("emagluefast", 33, 1, 2000000000, 0, false, true, "window fast glue"),
            Option("emaglueslow", 100000, 1, 2000000000, 0, false, true, "window slow glue"),
            Option("emajump", 100000, 1, 2000000000, 0, false, true, "window back-jump level"),
            Option("emalevel", 100000, 1, 2000000000, 0, false, true, "window back-track level"),
            Option("emasize", 100000, 1, 2000000000, 0, false, true, "window learned clause size"),
            Option("ematrailfast", 100, 1, 2000000000, 0, false, true, "window fast trail"),
            Option("ematrailslow", 100000, 1, 2000000000, 0, false, true, "window slow trail"),
            Option("exteagerreasons", 1, 0, 1, 0, false, true, "eagerly ask for all reasons (0: only when needed)"),
            Option("exteagerrecalc", 1, 0, 1, 0, false, true, "after eagerly asking for reasons recalculate all levels (0: trust the external tool)"),
            Option("externallrat", 0, 0, 1, 0, false, true, "external lrat"),
            Option("flush", 0, 0, 1, 0, false, true, "flush redundant clauses"),
            Option("flushfactor", 3, 1, 1000, 0, false, true, "interval increase"),
            Option("flushint", 100000, 1, 2000000000, 0, false, true, "initial limit"),
            Option("forcephase", 0, 0, 1, 0, false, true, "always use initial phase"),
            Option("frat", 0, 0, 2, 0, false, true, "1=frat(lrat), 2=frat(drat)"),
            Option("idrup", 0, 0, 1, 0, false, true, "incremental proof format"),
            Option("ilb", 0, 0, 1, 0, false, true, "ILB (incremental lazy backtrack)"),
            Option("ilbassumptions", 0, 0, 1, 0, false, true, "trail reuse for assumptions (ILB-like)"),
            Option("inprocessing", 1, 0, 1, 0, false, true, "enable inprocessing"),
            Option("instantiate", 0, 0, 1, 0, true, true, "variable instantiation"),
            Option("instantiateclslim", 3, 2, 2000000000, 0, false, true, "minimum clause size"),
            Option("instantiateocclim", 1, 1, 2000000000, 2, false, true, "maximum occurrence limit"),
            Option("instantiateonce", 1, 0, 1, 0, false, true, "instantiate each clause once"),
            Option("lidrup", 0, 0, 1, 0, false, true, "linear incremental proof format"),
            Option("lrat", 0, 0, 1, 0, false, true, "use LRAT proof format"),
            Option("lucky", 1, 0, 1, 0, false, true, "search for lucky phases"),
            Option("minimize", 1, 0, 1, 0, false, true, "minimize learned clauses"),
            Option("minimizedepth", 1000, 0, 1000, 0, false, true, "minimization depth"),
            Option("otfs", 1, 0, 1, 0, false, true, "on-the-fly self subsumption"),
            Option("phase", 1, 0, 1, 0, false, true, "initial phase"),
            Option("probe", 1, 0, 1, 0, true, true, "failed literal probing"),
            Option("probehbr", 1, 0, 1, 0, false, true, "learn hyper binary clauses"),
            Option("probeint", 5000, 1, 2000000000, 0, false, true, "probing interval"),
            Option("probemaxeff", 100000000, 0, 2000000000, 1, false, true, "maximum probing efficiency"),
            Option("probemineff", 1000000, 0, 2000000000, 1, false, true, "minimum probing efficiency"),
            Option("probereleff", 20, 1, 100000, 1, false, true, "relative efficiency per mille"),
            Option("proberounds", 1, 1, 16, 1, false, true, "probing rounds"),
            Option("profile", 2, 0, 4, 0, false, false, "profiling level"),
            Option("quiet", 0, 0, 1, 0, false, false, "disable all messages"),
            Option("radixsortlim", 32, 0, 2000000000, 0, false, true, "radix sort limit"),
            Option("realtime", 0, 0, 1, 0, false, false, "real instead of process time"),
            Option("reduce", 1, 0, 1, 0, false, true, "reduce useless clauses"),
            Option("reduceint", 300, 10, 1000000, 0, false, true, "reduce interval"),
            Option("reducetarget", 75, 10, 100, 0, false, true, "reduce fraction in percent"),
            Option("reducetier1glue", 2, 1, 2000000000, 0, false, true, "glue of kept learned clauses"),
            Option("reducetier2glue", 6, 1, 2000000000, 0, false, true, "glue of tier two clauses"),
            Option("reluctant", 1024, 0, 2000000000, 0, false, true, "reluctant doubling period"),
            Option("reluctantmax", 1048576, 0, 2000000000, 0, false, true, "reluctant doubling period"),
            Option("rephase", 1, 0, 1, 0, false, true, "enable resetting phase"),
            Option("rephaseint", 1000, 1, 2000000000, 0, false, true, "rephase interval"),
            Option("report", reportdefault, 0, 1, 0, false, true, "enable reporting"),
            Option("reportall", 0, 0, 1, 0, false, true, "report even if not successful"),
            Option("reportsolve", 0, 0, 1, 0, false, true, "use solving not process time"),
            Option("restart", 1, 0, 1, 0, false, true, "enable restarts"),
            Option("restartint", 2, 1, 2000000000, 0, false, true, "restart interval"),
            Option("restartmargin", 10, 0, 100, 0, false, true, "slow fast margin in percent"),
            Option("restartreusetrail", 1, 0, 1, 0, false, true, "enable trail reuse"),
            Option("restoreall", 0, 0, 2, 0, false, true, "restore all clauses (2=really)"),
            Option("restoreflush", 0, 0, 1, 0, false, true, "remove satisfied clauses"),
            Option("reverse", 0, 0, 1, 0, false, true, "reverse variable ordering"),
            Option("score", 1, 0, 1, 0, false, true, "use EVSIDS scores"),
            Option("scorefactor", 950, 500, 1000, 0, false, true, "score factor per mille"),
            Option("seed", 0, 0, 2000000000, 0, false, true, "random seed"),
            Option("shrink", 3, 0, 3, 0, false, true, "shrink conflict clause (1=only with binary, 2=minimize when pulling, 3=full)"),
            Option("shrinkreap", 1, 0, 1, 0, false, true, "use a reap for shrinking"),
            Option("shuffle", 0, 0, 1, 0, false, true, "shuffle variables"),
            Option("shufflequeue", 1, 0, 1, 0, false, true, "shuffle variable queue"),
            Option("shufflerandom", 0, 0, 1, 0, false, true, "not reverse but random"),
            Option("shufflescores", 1, 0, 1, 0, false, true, "shuffle variable scores"),
            Option("stabilize", 1, 0, 1, 0, false, true, "enable stabilizing phases"),
            Option("stabilizefactor", 200, 101, 2000000000, 0, false, true, "phase increase in percent"),
            Option("stabilizeint", 1000, 1, 2000000000, 0, false, true, "stabilizing interval"),
            Option("stabilizemaxint", 2000000000, 1, 2000000000, 0, false, true, "maximum stabilizing phase"),
            Option("stabilizeonly", 0, 0, 1, 0, false, true, "only stabilizing phases"),
            Option("stats", 0, 0, 1, 0, false, true, "print all statistics at the end of the run"),
            Option("subsume", 1, 0, 1, 0, true, true, "enable clause subsumption"),
            Option("subsumebinlim", 10000, 0, 2000000000, 1, false, true, "watch list length limit"),
            Option("subsumeclslim", 100, 0, 2000000000, 2, false, true, "clause length limit"),
            Option("subsumeint", 10000, 1, 2000000000, 0, false, true, "subsume interval"),
            Option("subsumelimited", 1, 0, 1, 0, false, true, "limit subsumption checks"),
            Option("subsumemaxeff", 100000000, 0, 2000000000, 1, false, true, "maximum subsuming efficiency"),
            Option("subsumemineff", 1000000, 0, 2000000000, 1, false, true, "minimum subsuming efficiency"),
            Option("subsumeocclim", 100, 0, 2000000000, 1, false, true, "watch list length limit"),
            Option("subsumereleff", 1000, 1, 100000, 1, false, true, "relative efficiency per mille"),
            Option("subsumestr", 1, 0, 1, 0, false, true, "strengthen during subsume"),
            Option("target", 1, 0, 2, 0, false, true, "target phases (1=stable only)"),
            Option("terminateint", 10, 0, 10000, 0, false, true, "termination check interval"),
            Option("ternary", 1, 0, 1, 0, true, true, "hyper ternary resolution"),
            Option("ternarymaxadd", 1000, 0, 10000, 1, false, true, "max clauses added in percent"),
            Option("ternarymaxeff", 100000000, 0, 2000000000, 1, false, true, "ternary maximum efficiency"),
            Option("ternarymineff", 1000000, 1, 2000000000, 1, false, true, "minimum ternary efficiency"),
            Option("ternaryocclim", 100, 1, 2000000000, 2, false, true, "ternary occurrence limit"),
            Option("ternaryreleff", 10, 1, 100000, 1, false, true, "relative efficiency per mille"),
            Option("ternaryrounds", 2, 1, 16, 1, false, true, "maximum ternary rounds"),
            Option("transred", 1, 0, 1, 0, true, true, "transitive reduction of BIG"),
            Option("transredmaxeff", 100000000, 0, 2000000000, 1, false, true, "maximum efficiency"),
            Option("transredmineff", 1000000, 0, 2000000000, 1, false, true, "minimum efficiency"),
            Option("transredreleff", 100, 1, 100000, 1, false, true, "relative efficiency per mille"),
            Option("verbose", 0, 0, 3, 0, false, false, "more verbose messages"),
            Option("veripb", 0, 0, 4, 0, false, true, "odd=checkdeletions, > 2=drat"),
            Option("vivify", 1, 0, 1, 0, true, true, "vivification"),
            Option("vivifyinst", 1, 0, 1, 0, false, true, "instantiate last literal when vivify"),
            Option("vivifymaxeff", 20000000, 0, 2000000000, 1, false, true, "maximum efficiency"),
            Option("vivifymineff", 20000, 0, 2000000000, 1, false, true, "minimum efficiency"),
            Option("vivifyonce", 0, 0, 2, 0, false, true, "vivify once: 1=red, 2=red+irr"),
            Option("vivifyredeff", 75, 0, 1000, 1, false, true, "redundant efficiency per mille"),
            Option("vivifyreleff", 20, 1, 100000, 1, false, true, "relative efficiency per mille"),
            Option("walk", 1, 0, 1, 0, false, true, "enable random walks"),
            Option("walkmaxeff", 10000000, 0, 2000000000, 1, false, true, "maximum efficiency"),
            Option("walkmineff", 100000, 0, 10000000, 1, false, true, "minimum efficiency"),
            Option("walknonstable", 1, 0, 1, 0, false, true, "walk in non-stabilizing phase"),
            Option("walkredundant", 0, 0, 1, 0, false, true, "walk redundant clauses too"),
            Option("walkreleff", 20, 1, 100000, 1, false, true, "relative efficiency per mille"),
        )

        private fun indexOf(o: Option): Int {
            val idx = table.indexOf(o)
            check(idx >= 0) { "option '${o.name}' not in table" }
            return idx
        }

        // Binary search in 'table', which requires option names to be sorted, which
        // in turned is checked at start-up in 'Options::Options'.
        fun has(name: String): Option? {
            var l = 0
            var r = NUMBER_OF_OPTIONS
            while (l < r) {
                val m = l + (r - l) / 2
                val res = table[m]
                val tmp = name.compareTo(res.name)
                if (tmp == 0) return res
                if (tmp < 0) r = m
                if (tmp > 0) l = m + 1
            }
            return null
        }

        fun isPreprocessingOption(name: String): Boolean = has(name)?.preprocessing ?: false

        /**
         * parse_long_option: '--<name>', '--<name>=<val>' or '--no-<name>'. Returns the option
         * name and value, or null if parsing fails.
         */
        fun parseLongOption(arg: String): Pair<String, Int>? {
            if (arg.length < 2 || arg[0] != '-' || arg[1] != '-') return null
            val hasNoPrefix = arg.startsWith("--no-")
            val offset = if (hasNoPrefix) 5 else 2
            val rest = arg.substring(offset)
            val pos = rest.indexOf('=')
            val name = if (pos >= 0) rest.substring(0, pos) else rest
            if (has(name) == null) return null
            val v = if (pos < 0) {
                if (hasNoPrefix) 0 else 1
            } else {
                parseIntStr(rest.substring(pos + 1)) ?: return null
            }
            return name to v
        }
    }
}
