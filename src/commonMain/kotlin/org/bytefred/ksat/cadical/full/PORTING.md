# Porting conventions for the full CaDiCaL 2.1.3 port

Package `org.bytefred.ksat.cadical.full`, Kotlin Multiplatform `commonMain` (no JVM-only
APIs). Upstream: CaDiCaL 2.1.3 `src/` (`f13d744`). Spec: `ksat-extra/doc/cadical-full-port.md`.
Rule zero: translate 1:1, line by line, in upstream order; never invent, never "improve".
If something cannot be mapped cleanly, stop and flag it instead of working around it.

## Files

- Header `foo.hpp` -> `FooHpp.kt` (data structures, inline header functions).
- Source `foo_bar.cpp` -> `FooBar.kt` (`analyze.cpp` -> `Analyze.kt`,
  `external_propagate.cpp` -> `ExternalPropagate.kt`).
- Where a `.cpp` only defines members of a class from its header (Reap, EMA::update, Options,
  Arena, Stats/Limit constructors), Kotlin cannot split the class, so those members are in
  `FooHpp.kt` and `Foo.kt` holds only the rest (or does not exist).
- No upstream file: `StdVector.kt` (vector helpers), `StdSort.kt` (libc++ std::sort),
  `Refs.kt` (reference parameters), `LstraceHpp.kt` (shadow trace sink, from the reference's
  `trace.patch`). `SIGNATURES.md`: the cross-file function contract.

## Functions and names

- `Internal::foo_bar` / `External::foo_bar` defined in `x.cpp` ->
  `internal fun Internal.fooBar (...)` / `internal fun External.fooBar (...)` in `X.kt`, with
  exactly the signature in `SIGNATURES.md`. Call functions of other files by that signature
  even if they are not written yet.
- `static` functions and structs local to one `.cpp` -> `private` in that file (comparators,
  `Walker`, `Coveror`, ...). Members of header helper structs defined in a `.cpp`
  (`Eliminator::enqueue`, `elim_more::operator ()`) -> extension functions / classes in
  that `.cpp`'s file.
- Fields keep the upstream name in camelCase (`opts.reducetier1glue`, `stats.extProp.epropCall`,
  `lim.terminate.check`). Kotlin keywords: `val (lit)` -> `value (lit)`, `var (lit)` ->
  `variable (lit)`.
- `internal->x` inside Internal code -> `x` (receiver); inside External code -> `internal.x`.
- Reference-returning accessors (`bumped (lit)`, `score (lit)`, `noccs (lit)`,
  `propfixed (lit)`, `unit_clauses (lit)`) are getters; write the table directly
  (`btab[vidx (lit)] = ...`, `ntab[vlit (lit)]++`).
- Reference parameters of primitive type: `IntRef` / `LongRef` / `BoolRef` (`x.value`).

## Types

| C++ | Kotlin |
|---|---|
| `int` | `Int` |
| `unsigned` | `Int` holding the bit pattern; use `toUInt ()` for comparisons, division, `%` and `>>` when the value can exceed `INT_MAX` (`UINT_MAX` = `-1`) |
| `int64_t`, `uint64_t` ids / counters | `Long` (ids stay below 2^63) |
| `uint64_t` with wrap-around / bit tricks | `ULong` (Random, Reluctant, hashes) |
| `size_t` index / size | `Int`; byte counts `Long` |
| `double` | `Double` |
| `signed char` | `Byte` in storage, `Int` in computations |
| `char` (phase types `'B'`, ...) | `Char` |
| `Clause *`, `0` / `nullptr` | `Clause` / `Clause?`, `null`; pointer `==` -> `===` |

- C truthiness: `if (x)` -> `x != 0` / `x != null`; `!x` likewise.
- Shifts: `>>` on signed -> `shr`, on unsigned -> `ushr`.
- `(int) d`, `(int64_t) d` -> `toInt ()` / `toLong ()` (truncation; C is undefined for NaN and
  out of range, Kotlin clamps: flag such a case if it can happen).
- `log`, `pow`, `exp` -> `kotlin.math.ln`, `pow`, `exp`. These are not guaranteed to be
  correctly rounded on either side (macOS libm vs JVM): if a trace diverges at a limit computed
  with them, check this first. `sqrt` is exact on both.

## Containers and iterators (StdVector.kt)

- `vector<int>` / `vector<unsigned>` -> `IntArrayList`, `vector<bool>` -> `BooleanList` (both
  reused from the old port `CaDiCaL.kt`), `vector<T>` -> `ArrayList<T>`, LRAT chains
  `vector<uint64_t>` -> `ArrayList<Long>`. Per-variable / per-literal tables grown in
  `enlarge` -> primitive arrays grown with `resized (n, fill)`.
- `push_back` -> `add`, `pop_back` -> `removeLast ()` / `removeAt (size - 1)`, `back` ->
  `back ()` / `last ()`, `resize (n)` -> `resize (n[, fill])` / `shrinkTo (n)`, `clear`,
  `erase_vector` -> `clear ()`, `shrink_vector` -> nothing (`trimToSize ()` for ArrayList).
- Iterators and pointers -> int indices. The compaction idiom
  `auto j = begin; for (i ...) *j++ = *i; v.resize (j - begin)` -> two indices and
  `shrinkTo (j)`. Clause literal pointers -> indices into `c.literals` (valid up to `c.size`).
- `reverse_iterator` -> index of the element it points to: `rbegin ()` = `size - 1`,
  `rend ()` = `-1`, `++rit` = `k--`, `*rit` = `v[k]`.
- `vals[lit]` -> `value (lit)` / `setVal`; raw access is `vals[vsize + lit]`.
- `for (auto idx : vars)` -> `for (idx in 1..maxVar)`; `for (auto lit : lits)` ->
  `for (lit in lits)` (Sange order).
- Struct value semantics: `Var`, `Flags`, `Link`, `Level`, `Watch`, `Bin`, `EMA` are classes.
  `Var &v = var (lit)` -> `val v = variable (lit)` (same object, as the reference). A C++ copy
  (`Flags f = flags (lit)`, `links[dst] = links[src]`, `const Watch w = *i` followed by a write
  to the slot) needs `copyFrom` / `copy ()` or reading the fields into locals first.
- `swap (v, w)` of vectors -> swap the references (make the fields `var`) or element-wise.
- `std::queue` -> `ArrayDeque`; `unordered_set` -> `HashSet` (membership only);
  `unordered_map` -> `LinkedHashMap`. Iterating an unordered container: flag it, the order
  differs from upstream.

## Sorting (StdSort.kt, RadixHpp.kt)

- `std::sort (b, e, less)` -> `cxxSort (v, less)`: an exact port of libc++ 18.1, so ties come
  out as in the reference. Never use Kotlin `sort` / `sortWith` for an upstream `std::sort`
  with a user comparator.
- `std::sort (b, e)` on plain ints (default `<`) -> Kotlin `sort ()` (ties are identical).
- `std::stable_sort` -> `stableSort` (unique result for a strict weak ordering).
- `rsort (b, e, rank)` -> `rsort (v, rank)`; the rank class implements `Rank<T>` / `IntRank`
  and overrides `bits = 32` when upstream's `Rank::Type` is `unsigned`.
- `MSORT (limit, b, e, rank, less)` -> `msort (limit, v, rank, less)`.
- Comparator structs -> classes implementing `IntLess` / `Less<T>` (port `operator ()`
  exactly, including its tie-breaks).

## Checks, messages, profiling

- `assert (c)` -> `check (c)` (always on, loud). `#ifndef NDEBUG` blocks that only check ->
  port them as checks; skip only ones that scan the whole database on hot paths, with a one
  line comment saying what was skipped. `#if 0` blocks are not ported.
- `LOG`, `PHASE`, `VERBOSE`, `MSG`, `section`, `report (...)`, `print_*`, `printf` to
  stdout -> dropped (keep argument expressions that have side effects).
  `opts.report` is 0 for library use, so `report` has no effect upstream either.
- `START (x)` / `STOP (x)` -> dropped. `START_SIMPLIFIER` / `STOP_SIMPLIFIER` /
  `START_INNER_WALK` / ... -> the functions in ProfileHpp.kt (they switch `mode`).
  `PROFILE_ACTIVE (x)` -> `false`. `time ()` / `process_time ()` only feed messages.
- `COVER (c)` -> `cover (c)`; `FATAL` / `fatal` / `error (...)` -> Kotlin `error (...)`.
- Statistics: update every `stats.*` counter exactly as upstream; many feed limits.

## Shadow trace (must match the reference byte for byte)

Reference: `ksat-extra/shadow/cadical-full/` (instrumented upstream; `README.md` there has the
full vocabulary, `trace.patch` the exact print sites). Every `+` line of `trace.patch` in
`foo.cpp` has a Kotlin counterpart at the same place in `Foo.kt`, and nowhere else:

- `LSTRACE ("BACKTRACK %d\n", new_level)` -> `trace?.line ("BACKTRACK $newLevel")`
  (`Internal.trace`, a `TraceSink`, null = off). Lines without the trailing newline.
- `lstrace_lits (this, clause)` -> `traceLits (clause)` / `traceLits (c)`: external literals
  in the current stored order, each with a leading space, ending with ` 0`.
- `LSTRACE_PHASE ("elim")` -> wrap the whole function body in `tracePhase ("elim") { ... }`
  (START at entry, END at every return).
- Events: `DECIDE`, `ASSIGN ... reason=D|U|E|C <id> :<lits>`, `CONFLICT level=<L> <id> :<lits>`,
  `OTFS`, `LEARN id= glue= jump=`, `BACKTRACK`, `RESTART`, `MODE stable|focused`,
  `REDUCE` / `FLUSH`, `REPHASE <c>`, `START` / `END <phase>`; formats exactly as in the patch.
- `ADD O|R|D|A`, `DEL`, `WEAKEN`, `STRENGTHEN`, `RESULT`, `MODEL` come from the driver's proof
  tracer, not from solver code: they are emitted by a `Tracer` connected through `proof`
  (proof wave / test driver). The golden traces are made WITH that tracer connected, so
  `proof` is non-null when tracing: clause-id allocation must be identical to upstream proof
  mode. Translate every `if (proof)` branch that allocates ids (`++clause_id`, e.g. in
  `Proof::otfs_strengthen_clause`, assumption clauses, decompose, cover) exactly; never
  allocate or skip an id depending on anything else.

## Proofs and LRAT

Proof tracing (proof.cpp, checker, LRAT builder/checker, DRAT/LRAT/FRAT/VeriPB/IDRUP tracers)
is ported (one file per upstream pair, output through `File` to a byte `FileSink`). Keep every call site: `if (proof) proof->add_derived_clause (...)` ->
`proof?.addDerivedClause (...)` against the `Proof` interface (ProofHpp.kt); `Internal.proof`
is null by default as upstream. Translate `if (lrat)` / `if (frat)` blocks and the chain
building (`lratChain`, `unitClausesIdx`, ...) fully: it is solver code and off by default.

## File status

| upstream | Kotlin | status |
|---|---|---|
| all headers listed in the spec | `*Hpp.kt` | done (foundation) |
| ema.cpp, random.cpp, reap.cpp, options.cpp, config.cpp, arena.cpp, stats.cpp (ctor), limit.cpp (ctors) | in `EmaHpp.kt`, `RandomHpp.kt`, `ReapHpp.kt`, `OptionsHpp.kt`, `ConfigHpp.kt`, `ArenaHpp.kt`, `StatsHpp.kt`, `LimitHpp.kt` | done |
| averages.cpp, limit.cpp, queue.cpp, util.cpp | `Averages.kt`, `Limit.kt`, `Queue.kt`, `Util.kt` | done |
| analyze, assume, backtrack, backward, bins, block, clause, collect, compact, condition, constrain, cover, decide, decompose, deduplicate, elim, extend, external, external_propagate, flags, flip, gates, instantiate, internal, lookahead, lucky, minimize, occs, phases, probe, propagate, reduce, rephase, restart, restore, score, shrink, solution, subsume, ternary, transred, var, vivify, walk, watch | `<Name>.kt` | next wave |
| solver.cpp (+ contract.cpp) | `Solver.kt` | after the next wave |
| proof, checker, lratbuilder, lratchecker, drattracer, lrattracer, frattracer, veripbtracer, idruptracer, lidruptracer | `<Name>.kt` (proof.cpp: `Proof.kt` + `ProofHpp.kt`) | done (proof wave); bytes checked by `FullProofTest` |
| message, report, profile, resources, format, terminal, signal, logging, version, stats (print), file, parse | none | not ported (output / OS); parse.cpp only if DIMACS parsing is needed |
| mobical, cadical, ccadical, ipasir | none | out of scope (not the solver) |
