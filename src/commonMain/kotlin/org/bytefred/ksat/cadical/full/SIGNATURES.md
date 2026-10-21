# Signatures of the Internal / External member functions

Generated from upstream `internal.hpp` / `external.hpp` (CaDiCaL 2.1.3) with
`scripts/probe/gen_cadical_signatures.py`, plus the nullability decisions below. This is the
contract between the parallel translators: implement each function with exactly this Kotlin
signature in the `.kt` file of its upstream `.cpp` (see PORTING.md), and call the functions of
other files with it, even before they exist.

Rules applied (see PORTING.md for the general type mapping):

- Names: camelCase of the upstream name; parameter names from the upstream `.cpp` definition.
- `Clause *` parameters are non-null `Clause`, except where upstream passes or tests null:
  `searchAssign.reason`, `searchAssignDriving.reason`, `assignmentLevel.reason`,
  `vivifyAssign.reason`, `handleExternalClause.res` are `Clause?`.
- `Clause *` results are `Clause?` where upstream can return null (`newDrivingClause`,
  `onTheFlyStrengthen`, `blockImpossible`, `findBinaryClause`, `findTernaryClause`,
  `findClause`, `learnExternalReasonClause`, `wrappedLearnExternalReasonClause`: they return
  `newest_clause`, null for satisfied / unit / empty external clauses), otherwise `Clause`.
- `int &` / `unsigned &` / `size_t &` -> `IntRef`, `int64_t &` -> `LongRef`, `bool &` ->
  `BoolRef` (Refs.kt). `std::vector<int>::reverse_iterator` -> element index (see PORTING.md).
- Upstream member functions of the helper structs (`Eliminator::enqueue`, ...) and the
  functions/structs local to one `.cpp` (`Walker`, `Coveror`, comparators, ...) are not listed;
  they belong to that `.cpp`'s translator.

## Solver functions

| upstream file | upstream declaration | Kotlin extension function |
|---|---|---|
| analyze.cpp | `void bump_variable_score (int lit)` | `Internal.bumpVariableScore(lit: Int): Unit` |
| analyze.cpp | `void bump_variable_score_inc ()` | `Internal.bumpVariableScoreInc(): Unit` |
| analyze.cpp | `void rescale_variable_scores ()` | `Internal.rescaleVariableScores(): Unit` |
| analyze.cpp | `void bump_queue (int idx)` | `Internal.bumpQueue(idx: Int): Unit` |
| analyze.cpp | `void learn_empty_clause ()` | `Internal.learnEmptyClause(): Unit` |
| analyze.cpp | `void learn_unit_clause (int lit)` | `Internal.learnUnitClause(lit: Int): Unit` |
| analyze.cpp | `void bump_variable (int lit)` | `Internal.bumpVariable(lit: Int): Unit` |
| analyze.cpp | `void bump_variables ()` | `Internal.bumpVariables(): Unit` |
| analyze.cpp | `int recompute_glue (Clause *)` | `Internal.recomputeGlue(c: Clause): Int` |
| analyze.cpp | `void bump_clause (Clause *)` | `Internal.bumpClause(c: Clause): Unit` |
| analyze.cpp | `void clear_unit_analyzed_literals ()` | `Internal.clearUnitAnalyzedLiterals(): Unit` |
| analyze.cpp | `void clear_analyzed_literals ()` | `Internal.clearAnalyzedLiterals(): Unit` |
| analyze.cpp | `void clear_analyzed_levels ()` | `Internal.clearAnalyzedLevels(): Unit` |
| analyze.cpp | `bool bump_also_reason_literal (int lit)` | `Internal.bumpAlsoReasonLiteral(lit: Int): Boolean` |
| analyze.cpp | `void bump_also_reason_literals (int lit, int limit)` | `Internal.bumpAlsoReasonLiterals(lit: Int, limit: Int): Unit` |
| analyze.cpp | `void bump_also_all_reason_literals ()` | `Internal.bumpAlsoAllReasonLiterals(): Unit` |
| analyze.cpp | `void analyze_literal (int lit, int &open, int &resolvent_size, int &antecedent_size)` | `Internal.analyzeLiteral(lit: Int, open: IntRef, resolventSize: IntRef, antecedentSize: IntRef): Unit` |
| analyze.cpp | `void analyze_reason (int lit, Clause *, int &open, int &resolvent_size, int &antecedent_size)` | `Internal.analyzeReason(lit: Int, reason: Clause, open: IntRef, resolventSize: IntRef, antecedentSize: IntRef): Unit` |
| analyze.cpp | `Clause * new_driving_clause (const int glue, int &jump)` | `Internal.newDrivingClause(glue: Int, jump: IntRef): Clause?` |
| analyze.cpp | `int find_conflict_level (int &forced)` | `Internal.findConflictLevel(forced: IntRef): Int` |
| analyze.cpp | `int determine_actual_backtrack_level (int jump)` | `Internal.determineActualBacktrackLevel(jump: Int): Int` |
| analyze.cpp | `void otfs_strengthen_clause (Clause *, int, int, const std::vector<int> &)` | `Internal.otfsStrengthenClause(c: Clause, lit: Int, newSize: Int, old: IntArrayList): Unit` |
| analyze.cpp | `void otfs_subsume_clause (Clause *subsuming, Clause *subsumed)` | `Internal.otfsSubsumeClause(subsuming: Clause, subsumed: Clause): Unit` |
| analyze.cpp | `int otfs_find_backtrack_level (int &forced)` | `Internal.otfsFindBacktrackLevel(forced: IntRef): Int` |
| analyze.cpp | `Clause * on_the_fly_strengthen (Clause *conflict, int lit)` | `Internal.onTheFlyStrengthen(conflict: Clause, lit: Int): Clause?` |
| analyze.cpp | `void analyze ()` | `Internal.analyze(): Unit` |
| analyze.cpp | `void iterate ()` | `Internal.iterate(): Unit` |
| assume.cpp | `void assume_analyze_literal (int lit)` | `Internal.assumeAnalyzeLiteral(lit: Int): Unit` |
| assume.cpp | `void assume_analyze_reason (int lit, Clause *reason)` | `Internal.assumeAnalyzeReason(lit: Int, reason: Clause): Unit` |
| assume.cpp | `void assume (int)` | `Internal.assume(lit: Int): Unit` |
| assume.cpp | `bool failed (int lit)` | `Internal.failed(lit: Int): Boolean` |
| assume.cpp | `void reset_assumptions ()` | `Internal.resetAssumptions(): Unit` |
| assume.cpp | `void sort_and_reuse_assumptions ()` | `Internal.sortAndReuseAssumptions(): Unit` |
| assume.cpp | `void failing ()` | `Internal.failing(): Unit` |
| assume.cpp | `void conclude_unsat ()` | `Internal.concludeUnsat(): Unit` |
| assume.cpp | `void reset_concluded ()` | `Internal.resetConcluded(): Unit` |
| averages.cpp | `void init_averages ()` | `Internal.initAverages(): Unit` |
| averages.cpp | `void swap_averages ()` | `Internal.swapAverages(): Unit` |
| backtrack.cpp | `void unassign (int lit)` | `Internal.unassign(lit: Int): Unit` |
| backtrack.cpp | `void update_target_and_best ()` | `Internal.updateTargetAndBest(): Unit` |
| backtrack.cpp | `void backtrack (int target_level = 0)` | `Internal.backtrack(targetLevel: Int = 0): Unit` |
| backward.cpp | `void elim_backward_clause (Eliminator &, Clause *)` | `Internal.elimBackwardClause(eliminator: Eliminator, c: Clause): Unit` |
| backward.cpp | `void elim_backward_clauses (Eliminator &)` | `Internal.elimBackwardClauses(eliminator: Eliminator): Unit` |
| bins.cpp | `void init_bins ()` | `Internal.initBins(): Unit` |
| bins.cpp | `void reset_bins ()` | `Internal.resetBins(): Unit` |
| block.cpp | `bool is_blocked_clause (Clause *c, int pivot)` | `Internal.isBlockedClause(c: Clause, pivot: Int): Boolean` |
| block.cpp | `void block_schedule (Blocker &)` | `Internal.blockSchedule(blocker: Blocker): Unit` |
| block.cpp | `size_t block_candidates (Blocker &, int lit)` | `Internal.blockCandidates(blocker: Blocker, lit: Int): Int` |
| block.cpp | `Clause * block_impossible (Blocker &, int lit)` | `Internal.blockImpossible(blocker: Blocker, lit: Int): Clause?` |
| block.cpp | `void block_literal_with_at_least_two_negative_occs (Blocker &, int lit)` | `Internal.blockLiteralWithAtLeastTwoNegativeOccs(blocker: Blocker, lit: Int): Unit` |
| block.cpp | `void block_literal_with_one_negative_occ (Blocker &, int lit)` | `Internal.blockLiteralWithOneNegativeOcc(blocker: Blocker, lit: Int): Unit` |
| block.cpp | `void block_pure_literal (Blocker &, int lit)` | `Internal.blockPureLiteral(blocker: Blocker, lit: Int): Unit` |
| block.cpp | `void block_reschedule_clause (Blocker &, int lit, Clause *)` | `Internal.blockRescheduleClause(blocker: Blocker, lit: Int, c: Clause): Unit` |
| block.cpp | `void block_reschedule (Blocker &, int lit)` | `Internal.blockReschedule(blocker: Blocker, lit: Int): Unit` |
| block.cpp | `void block_literal (Blocker &, int lit)` | `Internal.blockLiteral(blocker: Blocker, lit: Int): Unit` |
| block.cpp | `bool block ()` | `Internal.block(): Boolean` |
| clause.cpp | `void mark_clause ()` | `Internal.markClause(): Unit` |
| clause.cpp | `void mark (Clause *)` | `Internal.mark(c: Clause): Unit` |
| clause.cpp | `void mark2 (Clause *)` | `Internal.mark2(c: Clause): Unit` |
| clause.cpp | `void unmark_clause ()` | `Internal.unmarkClause(): Unit` |
| clause.cpp | `void unmark (Clause *)` | `Internal.unmark(c: Clause): Unit` |
| clause.cpp | `Clause * new_clause (bool red, int glue = 0)` | `Internal.newClause(red: Boolean, glue: Int = 0): Clause` |
| clause.cpp | `void promote_clause (Clause *, int new_glue)` | `Internal.promoteClause(c: Clause, newGlue: Int): Unit` |
| clause.cpp | `size_t shrink_clause (Clause *, int new_size)` | `Internal.shrinkClause(c: Clause, newSize: Int): Int` |
| clause.cpp | `void deallocate_clause (Clause *)` | `Internal.deallocateClause(c: Clause): Unit` |
| clause.cpp | `void delete_clause (Clause *)` | `Internal.deleteClause(c: Clause): Unit` |
| clause.cpp | `void mark_garbage (Clause *)` | `Internal.markGarbage(c: Clause): Unit` |
| clause.cpp | `void assign_original_unit (uint64_t, int)` | `Internal.assignOriginalUnit(id: Long, lit: Int): Unit` |
| clause.cpp | `void add_new_original_clause (uint64_t)` | `Internal.addNewOriginalClause(id: Long): Unit` |
| clause.cpp | `Clause * new_learned_redundant_clause (int glue)` | `Internal.newLearnedRedundantClause(glue: Int): Clause` |
| clause.cpp | `Clause * new_hyper_binary_resolved_clause (bool red, int glue)` | `Internal.newHyperBinaryResolvedClause(red: Boolean, glue: Int): Clause` |
| clause.cpp | `Clause * new_clause_as (const Clause *orig)` | `Internal.newClauseAs(orig: Clause): Clause` |
| clause.cpp | `Clause * new_resolved_irredundant_clause ()` | `Internal.newResolvedIrredundantClause(): Clause` |
| clause.cpp | `void mark_added (int lit, int size, bool redundant)` | `Internal.markAdded(lit: Int, size: Int, redundant: Boolean): Unit` |
| clause.cpp | `void mark_added (Clause *)` | `Internal.markAdded(c: Clause): Unit` |
| clause.cpp | `void mark_removed (Clause *, int except = 0)` | `Internal.markRemoved(c: Clause, except: Int = 0): Unit` |
| clause.cpp | `Clause * new_hyper_ternary_resolved_clause (bool red)` | `Internal.newHyperTernaryResolvedClause(red: Boolean): Clause` |
| collect.cpp | `void protect_reasons ()` | `Internal.protectReasons(): Unit` |
| collect.cpp | `void unprotect_reasons ()` | `Internal.unprotectReasons(): Unit` |
| collect.cpp | `int clause_contains_fixed_literal (Clause *)` | `Internal.clauseContainsFixedLiteral(c: Clause): Int` |
| collect.cpp | `void remove_falsified_literals (Clause *)` | `Internal.removeFalsifiedLiterals(c: Clause): Unit` |
| collect.cpp | `void mark_satisfied_clauses_as_garbage ()` | `Internal.markSatisfiedClausesAsGarbage(): Unit` |
| collect.cpp | `void copy_clause (Clause *)` | `Internal.copyClause(c: Clause): Unit` |
| collect.cpp | `void flush_watches (int lit, Watches &)` | `Internal.flushWatches(lit: Int, saved: Watches): Unit` |
| collect.cpp | `size_t flush_occs (int lit)` | `Internal.flushOccs(lit: Int): Int` |
| collect.cpp | `void flush_all_occs_and_watches ()` | `Internal.flushAllOccsAndWatches(): Unit` |
| collect.cpp | `void update_reason_references ()` | `Internal.updateReasonReferences(): Unit` |
| collect.cpp | `void copy_non_garbage_clauses ()` | `Internal.copyNonGarbageClauses(): Unit` |
| collect.cpp | `void delete_garbage_clauses ()` | `Internal.deleteGarbageClauses(): Unit` |
| collect.cpp | `void check_clause_stats ()` | `Internal.checkClauseStats(): Unit` |
| collect.cpp | `bool arenaing ()` | `Internal.arenaing(): Boolean` |
| collect.cpp | `void garbage_collection ()` | `Internal.garbageCollection(): Unit` |
| collect.cpp | `void remove_garbage_binaries ()` | `Internal.removeGarbageBinaries(): Unit` |
| compact.cpp | `bool compacting ()` | `Internal.compacting(): Boolean` |
| compact.cpp | `void compact ()` | `Internal.compact(): Unit` |
| condition.cpp | `bool is_autarky_literal (int lit)` | `Internal.isAutarkyLiteral(lit: Int): Boolean` |
| condition.cpp | `bool is_conditional_literal (int lit)` | `Internal.isConditionalLiteral(lit: Int): Boolean` |
| condition.cpp | `void mark_as_conditional_literal (int lit)` | `Internal.markAsConditionalLiteral(lit: Int): Unit` |
| condition.cpp | `void unmark_as_conditional_literal (int lit)` | `Internal.unmarkAsConditionalLiteral(lit: Int): Unit` |
| condition.cpp | `bool is_in_candidate_clause (int lit)` | `Internal.isInCandidateClause(lit: Int): Boolean` |
| condition.cpp | `void mark_in_candidate_clause (int lit)` | `Internal.markInCandidateClause(lit: Int): Unit` |
| condition.cpp | `void unmark_in_candidate_clause (int lit)` | `Internal.unmarkInCandidateClause(lit: Int): Unit` |
| condition.cpp | `void condition_assign (int lit)` | `Internal.conditionAssign(lit: Int): Unit` |
| condition.cpp | `void condition_unassign (int lit)` | `Internal.conditionUnassign(lit: Int): Unit` |
| condition.cpp | `bool conditioning ()` | `Internal.conditioning(): Boolean` |
| condition.cpp | `long condition_round (long unassigned_literal_propagation_limit)` | `Internal.conditionRound(unassignedLiteralPropagationLimit: Long): Long` |
| condition.cpp | `void condition (bool update_limits = true)` | `Internal.condition(updateLimits: Boolean = true): Unit` |
| constrain.cpp | `void constrain (int)` | `Internal.constrain(lit: Int): Unit` |
| constrain.cpp | `bool failed_constraint ()` | `Internal.failedConstraint(): Boolean` |
| constrain.cpp | `void reset_constraint ()` | `Internal.resetConstraint(): Unit` |
| cover.cpp | `void covered_literal_addition (int lit, Coveror &)` | `Internal.coveredLiteralAddition(lit: Int, coveror: Coveror): Unit` |
| cover.cpp | `void asymmetric_literal_addition (int lit, Coveror &)` | `Internal.asymmetricLiteralAddition(lit: Int, coveror: Coveror): Unit` |
| cover.cpp | `void cover_push_extension (int lit, Coveror &)` | `Internal.coverPushExtension(lit: Int, coveror: Coveror): Unit` |
| cover.cpp | `bool cover_propagate_asymmetric (int lit, Clause *ignore, Coveror &)` | `Internal.coverPropagateAsymmetric(lit: Int, ignore: Clause, coveror: Coveror): Boolean` |
| cover.cpp | `bool cover_propagate_covered (int lit, Coveror &)` | `Internal.coverPropagateCovered(lit: Int, coveror: Coveror): Boolean` |
| cover.cpp | `bool cover_clause (Clause *c, Coveror &)` | `Internal.coverClause(c: Clause, coveror: Coveror): Boolean` |
| cover.cpp | `int64_t cover_round ()` | `Internal.coverRound(): Long` |
| cover.cpp | `bool cover ()` | `Internal.cover(): Boolean` |
| decide.cpp | `void new_trail_level (int lit)` | `Internal.newTrailLevel(lit: Int): Unit` |
| decide.cpp | `bool satisfied ()` | `Internal.satisfied(): Boolean` |
| decide.cpp | `int next_decision_variable_on_queue ()` | `Internal.nextDecisionVariableOnQueue(): Int` |
| decide.cpp | `int next_decision_variable_with_best_score ()` | `Internal.nextDecisionVariableWithBestScore(): Int` |
| decide.cpp | `int next_decision_variable ()` | `Internal.nextDecisionVariable(): Int` |
| decide.cpp | `int decide_phase (int idx, bool target)` | `Internal.decidePhase(idx: Int, target: Boolean): Int` |
| decide.cpp | `int likely_phase (int idx)` | `Internal.likelyPhase(idx: Int): Int` |
| decide.cpp | `bool better_decision (int lit, int other)` | `Internal.betterDecision(lit: Int, other: Int): Boolean` |
| decide.cpp | `int decide ()` | `Internal.decide(): Int` |
| decompose.cpp | `void clear_decomposed_literals ()` | `Internal.clearDecomposedLiterals(): Unit` |
| decompose.cpp | `void decompose_conflicting_scc_lrat (DFS *dfs, vector<int> &)` | `Internal.decomposeConflictingSccLrat(dfs: DFS, scc: IntArrayList): Unit` |
| decompose.cpp | `void build_lrat_for_clause (const vector<vector<Clause *>> &dfs_chains, bool invert = false)` | `Internal.buildLratForClause(dfsChains: ArrayList<ArrayList<Clause>>, invert: Boolean = false): Unit` |
| decompose.cpp | `vector<Clause *> decompose_analyze_binary_clauses (DFS *dfs, int from)` | `Internal.decomposeAnalyzeBinaryClauses(dfs: DFS, from: Int): ArrayList<Clause>` |
| decompose.cpp | `void decompose_analyze_binary_chain (DFS *dfs, int)` | `Internal.decomposeAnalyzeBinaryChain(dfs: DFS, from: Int): Unit` |
| decompose.cpp | `bool decompose_round ()` | `Internal.decomposeRound(): Boolean` |
| decompose.cpp | `void decompose ()` | `Internal.decompose(): Unit` |
| deduplicate.cpp | `void mark_duplicated_binary_clauses_as_garbage ()` | `Internal.markDuplicatedBinaryClausesAsGarbage(): Unit` |
| elim.cpp | `bool eliminating ()` | `Internal.eliminating(): Boolean` |
| elim.cpp | `double compute_elim_score (unsigned lit)` | `Internal.computeElimScore(lit: Int): Double` |
| elim.cpp | `bool resolve_clauses (Eliminator &, Clause *, int pivot, Clause *, bool)` | `Internal.resolveClauses(eliminator: Eliminator, c: Clause, pivot: Int, d: Clause, propagateEagerly: Boolean): Boolean` |
| elim.cpp | `void mark_eliminated_clauses_as_garbage (Eliminator &, int pivot, bool &)` | `Internal.markEliminatedClausesAsGarbage(eliminator: Eliminator, pivot: Int, deletedBinaryClause: BoolRef): Unit` |
| elim.cpp | `bool elim_resolvents_are_bounded (Eliminator &, int pivot)` | `Internal.elimResolventsAreBounded(eliminator: Eliminator, pivot: Int): Boolean` |
| elim.cpp | `void elim_update_removed_lit (Eliminator &, int lit)` | `Internal.elimUpdateRemovedLit(eliminator: Eliminator, lit: Int): Unit` |
| elim.cpp | `void elim_update_removed_clause (Eliminator &, Clause *, int except = 0)` | `Internal.elimUpdateRemovedClause(eliminator: Eliminator, c: Clause, except: Int = 0): Unit` |
| elim.cpp | `void elim_update_added_clause (Eliminator &, Clause *)` | `Internal.elimUpdateAddedClause(eliminator: Eliminator, c: Clause): Unit` |
| elim.cpp | `void elim_add_resolvents (Eliminator &, int pivot)` | `Internal.elimAddResolvents(eliminator: Eliminator, pivot: Int): Unit` |
| elim.cpp | `void elim_propagate (Eliminator &, int unit)` | `Internal.elimPropagate(eliminator: Eliminator, unit: Int): Unit` |
| elim.cpp | `void elim_on_the_fly_self_subsumption (Eliminator &, Clause *, int)` | `Internal.elimOnTheFlySelfSubsumption(eliminator: Eliminator, c: Clause, pivot: Int): Unit` |
| elim.cpp | `void try_to_eliminate_variable (Eliminator &, int pivot, bool &)` | `Internal.tryToEliminateVariable(eliminator: Eliminator, pivot: Int, deletedBinaryClause: BoolRef): Unit` |
| elim.cpp | `void increase_elimination_bound ()` | `Internal.increaseEliminationBound(): Unit` |
| elim.cpp | `int elim_round (bool &completed, bool &)` | `Internal.elimRound(completed: BoolRef, deletedBinaryClause: BoolRef): Int` |
| elim.cpp | `void elim (bool update_limits = true)` | `Internal.elim(updateLimits: Boolean = true): Unit` |
| extend.cpp | `void push_zero_on_extension_stack ()` | `External.pushZeroOnExtensionStack(): Unit` |
| extend.cpp | `void push_clause_literal_on_extension_stack (int ilit)` | `External.pushClauseLiteralOnExtensionStack(ilit: Int): Unit` |
| extend.cpp | `void push_witness_literal_on_extension_stack (int ilit)` | `External.pushWitnessLiteralOnExtensionStack(ilit: Int): Unit` |
| extend.cpp | `void push_clause_on_extension_stack (Clause *)` | `External.pushClauseOnExtensionStack(c: Clause): Unit` |
| extend.cpp | `void push_clause_on_extension_stack (Clause *, int witness)` | `External.pushClauseOnExtensionStack(c: Clause, witness: Int): Unit` |
| extend.cpp | `void push_binary_clause_on_extension_stack (uint64_t id, int witness, int other)` | `External.pushBinaryClauseOnExtensionStack(id: Long, witness: Int, other: Int): Unit` |
| extend.cpp | `void extend ()` | `External.extend(): Unit` |
| extend.cpp | `void conclude_sat ()` | `External.concludeSat(): Unit` |
| extend.cpp | `void push_external_clause_and_witness_on_extension_stack ( const vector<int> &clause, const vector<int> &witness, uint64_t id)` | `External.pushExternalClauseAndWitnessOnExtensionStack(clause: IntArrayList, witness: IntArrayList, id: Long): Unit` |
| extend.cpp | `void push_id_on_extension_stack (uint64_t id)` | `External.pushIdOnExtensionStack(id: Long): Unit` |
| extend.cpp | `bool traverse_witnesses_backward (WitnessIterator &)` | `External.traverseWitnessesBackward(it: WitnessIterator): Boolean` |
| extend.cpp | `bool traverse_witnesses_forward (WitnessIterator &)` | `External.traverseWitnessesForward(it: WitnessIterator): Boolean` |
| external.cpp | `void export_learned_empty_clause ()` | `External.exportLearnedEmptyClause(): Unit` |
| external.cpp | `void export_learned_unit_clause (int ilit)` | `External.exportLearnedUnitClause(ilit: Int): Unit` |
| external.cpp | `void export_learned_large_clause (const vector<int> &)` | `External.exportLearnedLargeClause(clause: IntArrayList): Unit` |
| external.cpp | `void add_observed_var (int elit)` | `External.addObservedVar(elit: Int): Unit` |
| external.cpp | `void remove_observed_var (int elit)` | `External.removeObservedVar(elit: Int): Unit` |
| external.cpp | `void reset_observed_vars ()` | `External.resetObservedVars(): Unit` |
| external.cpp | `bool observed (int elit)` | `External.observed(elit: Int): Boolean` |
| external.cpp | `bool is_witness (int elit)` | `External.isWitness(elit: Int): Boolean` |
| external.cpp | `bool is_decision (int elit)` | `External.isDecision(elit: Int): Boolean` |
| external.cpp | `void force_backtrack (size_t new_level)` | `External.forceBacktrack(newLevel: Int): Unit` |
| external.cpp | `void freeze (int elit)` | `External.freeze(elit: Int): Unit` |
| external.cpp | `void melt (int elit)` | `External.melt(elit: Int): Unit` |
| external.cpp | `void enlarge (int new_max_var)` | `External.enlarge(newMaxVar: Int): Unit` |
| external.cpp | `void init (int new_max_var)` | `External.init(newMaxVar: Int): Unit` |
| external.cpp | `int internalize (int)` | `External.internalize(elit: Int): Int` |
| external.cpp | `void reset_assumptions ()` | `External.resetAssumptions(): Unit` |
| external.cpp | `void reset_concluded ()` | `External.resetConcluded(): Unit` |
| external.cpp | `void reset_extended ()` | `External.resetExtended(): Unit` |
| external.cpp | `void reset_limits ()` | `External.resetLimits(): Unit` |
| external.cpp | `void add (int elit)` | `External.add(elit: Int): Unit` |
| external.cpp | `void assume (int elit)` | `External.assume(elit: Int): Unit` |
| external.cpp | `int solve (bool preprocess_only)` | `External.solve(preprocessOnly: Boolean): Int` |
| external.cpp | `bool flip (int elit)` | `External.flip(elit: Int): Boolean` |
| external.cpp | `bool flippable (int elit)` | `External.flippable(elit: Int): Boolean` |
| external.cpp | `bool failed (int elit)` | `External.failed(elit: Int): Boolean` |
| external.cpp | `void terminate ()` | `External.terminate(): Unit` |
| external.cpp | `void constrain (int elit)` | `External.constrain(elit: Int): Unit` |
| external.cpp | `bool failed_constraint ()` | `External.failedConstraint(): Boolean` |
| external.cpp | `void reset_constraint ()` | `External.resetConstraint(): Unit` |
| external.cpp | `int propagate_assumptions ()` | `External.propagateAssumptions(): Int` |
| external.cpp | `void get_entrailed_literals (std::vector<int> &entrailed)` | `External.getEntrailedLiterals(entrailed: IntArrayList): Unit` |
| external.cpp | `void conclude_unknown ()` | `External.concludeUnknown(): Unit` |
| external.cpp | `int lookahead ()` | `External.lookahead(): Int` |
| external.cpp | `CaDiCaL::CubesWithStatus generate_cubes (int, int)` | `External.generateCubes(depth: Int, minDepth: Int): CubesWithStatus` |
| external.cpp | `void phase (int elit)` | `External.phase(elit: Int): Unit` |
| external.cpp | `void unphase (int elit)` | `External.unphase(elit: Int): Unit` |
| external.cpp | `bool traverse_all_frozen_units_as_clauses (ClauseIterator &)` | `External.traverseAllFrozenUnitsAsClauses(it: ClauseIterator): Boolean` |
| external.cpp | `bool traverse_all_non_frozen_units_as_witnesses (WitnessIterator &)` | `External.traverseAllNonFrozenUnitsAsWitnesses(it: WitnessIterator): Boolean` |
| external.cpp | `void copy_flags (External &other)` | `External.copyFlags(other: External): Unit` |
| external.cpp | `void check_assumptions_satisfied ()` | `External.checkAssumptionsSatisfied(): Unit` |
| external.cpp | `void check_constraint_satisfied ()` | `External.checkConstraintSatisfied(): Unit` |
| external.cpp | `void check_failing ()` | `External.checkFailing(): Unit` |
| external.cpp | `void check_assignment (int (External::*assignment) (int) const)` | `External.checkAssignment(assignment: (Int) -> Int): Unit` |
| external.cpp | `void check_satisfiable ()` | `External.checkSatisfiable(): Unit` |
| external.cpp | `void check_unsatisfiable ()` | `External.checkUnsatisfiable(): Unit` |
| external.cpp | `void check_solve_result (int res)` | `External.checkSolveResult(res: Int): Unit` |
| external.cpp | `void update_molten_literals ()` | `External.updateMoltenLiterals(): Unit` |
| external_propagate.cpp | `bool external_propagate ()` | `Internal.externalPropagate(): Boolean` |
| external_propagate.cpp | `bool external_check_solution ()` | `Internal.externalCheckSolution(): Boolean` |
| external_propagate.cpp | `void add_external_clause (int propagated_lit = 0, bool no_backtrack = false)` | `Internal.addExternalClause(propagatedLit: Int = 0, noBacktrack: Boolean = false): Unit` |
| external_propagate.cpp | `Clause * learn_external_reason_clause (int lit, int falsified_elit = 0, bool no_backtrack = false)` | `Internal.learnExternalReasonClause(lit: Int, falsifiedElit: Int = 0, noBacktrack: Boolean = false): Clause?` |
| external_propagate.cpp | `Clause * wrapped_learn_external_reason_clause (int lit)` | `Internal.wrappedLearnExternalReasonClause(lit: Int): Clause?` |
| external_propagate.cpp | `void explain_external_propagations ()` | `Internal.explainExternalPropagations(): Unit` |
| external_propagate.cpp | `void explain_reason (int lit, Clause *, int &open)` | `Internal.explainReason(lit: Int, reason: Clause, open: IntRef): Unit` |
| external_propagate.cpp | `void move_literals_to_watch ()` | `Internal.moveLiteralsToWatch(): Unit` |
| external_propagate.cpp | `void handle_external_clause (Clause *)` | `Internal.handleExternalClause(res: Clause?): Unit` |
| external_propagate.cpp | `void notify_assignments ()` | `Internal.notifyAssignments(): Unit` |
| external_propagate.cpp | `void notify_decision ()` | `Internal.notifyDecision(): Unit` |
| external_propagate.cpp | `void notify_backtrack (size_t new_level)` | `Internal.notifyBacktrack(newLevel: Int): Unit` |
| external_propagate.cpp | `void force_backtrack (size_t new_level)` | `Internal.forceBacktrack(newLevel: Int): Unit` |
| external_propagate.cpp | `int ask_decision ()` | `Internal.askDecision(): Int` |
| external_propagate.cpp | `bool ask_external_clause ()` | `Internal.askExternalClause(): Boolean` |
| external_propagate.cpp | `void add_observed_var (int ilit)` | `Internal.addObservedVar(ilit: Int): Unit` |
| external_propagate.cpp | `void remove_observed_var (int ilit)` | `Internal.removeObservedVar(ilit: Int): Unit` |
| external_propagate.cpp | `bool observed (int ilit)` | `Internal.observed(ilit: Int): Boolean` |
| external_propagate.cpp | `bool is_decision (int ilit)` | `Internal.isDecision(ilit: Int): Boolean` |
| external_propagate.cpp | `void check_watched_literal_invariants ()` | `Internal.checkWatchedLiteralInvariants(): Unit` |
| external_propagate.cpp | `void set_tainted_literal ()` | `Internal.setTaintedLiteral(): Unit` |
| external_propagate.cpp | `void renotify_trail_after_ilb ()` | `Internal.renotifyTrailAfterIlb(): Unit` |
| external_propagate.cpp | `void renotify_trail_after_local_search ()` | `Internal.renotifyTrailAfterLocalSearch(): Unit` |
| external_propagate.cpp | `void renotify_full_trail ()` | `Internal.renotifyFullTrail(): Unit` |
| external_propagate.cpp | `void connect_propagator ()` | `Internal.connectPropagator(): Unit` |
| external_propagate.cpp | `void mark_garbage_external_forgettable (int64_t id)` | `Internal.markGarbageExternalForgettable(id: Long): Unit` |
| external_propagate.cpp | `bool is_external_forgettable (int64_t id)` | `Internal.isExternalForgettable(id: Long): Boolean` |
| external_propagate.cpp | `void get_all_fixed_literals (std::vector<int> &)` | `Internal.getAllFixedLiterals(fixedLits: IntArrayList): Unit` |
| flags.cpp | `void reactivate (int lit)` | `Internal.reactivate(lit: Int): Unit` |
| flags.cpp | `void mark_eliminated (int)` | `Internal.markEliminated(lit: Int): Unit` |
| flags.cpp | `void mark_substituted (int)` | `Internal.markSubstituted(lit: Int): Unit` |
| flags.cpp | `void mark_active (int)` | `Internal.markActive(lit: Int): Unit` |
| flags.cpp | `void mark_fixed (int)` | `Internal.markFixed(lit: Int): Unit` |
| flags.cpp | `void mark_pure (int)` | `Internal.markPure(lit: Int): Unit` |
| flip.cpp | `bool flip (int lit)` | `Internal.flip(lit: Int): Boolean` |
| flip.cpp | `bool flippable (int lit)` | `Internal.flippable(lit: Int): Boolean` |
| gates.cpp | `int second_literal_in_binary_clause_lrat (Clause *, int first)` | `Internal.secondLiteralInBinaryClauseLrat(c: Clause, first: Int): Int` |
| gates.cpp | `int second_literal_in_binary_clause (Eliminator &, Clause *, int first)` | `Internal.secondLiteralInBinaryClause(eliminator: Eliminator, c: Clause, first: Int): Int` |
| gates.cpp | `void mark_binary_literals (Eliminator &, int pivot)` | `Internal.markBinaryLiterals(eliminator: Eliminator, pivot: Int): Unit` |
| gates.cpp | `void find_and_gate (Eliminator &, int pivot)` | `Internal.findAndGate(eliminator: Eliminator, pivot: Int): Unit` |
| gates.cpp | `void find_equivalence (Eliminator &, int pivot)` | `Internal.findEquivalence(eliminator: Eliminator, pivot: Int): Unit` |
| gates.cpp | `bool get_ternary_clause (Clause *, int &, int &, int &)` | `Internal.getTernaryClause(d: Clause, a: IntRef, b: IntRef, c: IntRef): Boolean` |
| gates.cpp | `bool match_ternary_clause (Clause *, int, int, int)` | `Internal.matchTernaryClause(d: Clause, a: Int, b: Int, c: Int): Boolean` |
| gates.cpp | `Clause * find_ternary_clause (int, int, int)` | `Internal.findTernaryClause(a: Int, b: Int, c: Int): Clause?` |
| gates.cpp | `bool get_clause (Clause *, vector<int> &)` | `Internal.getClause(c: Clause, l: IntArrayList): Boolean` |
| gates.cpp | `bool is_clause (Clause *, const vector<int> &)` | `Internal.isClause(c: Clause, lits: IntArrayList): Boolean` |
| gates.cpp | `Clause * find_clause (const vector<int> &)` | `Internal.findClause(lits: IntArrayList): Clause?` |
| gates.cpp | `void find_xor_gate (Eliminator &, int pivot)` | `Internal.findXorGate(eliminator: Eliminator, pivot: Int): Unit` |
| gates.cpp | `void find_if_then_else (Eliminator &, int pivot)` | `Internal.findIfThenElse(eliminator: Eliminator, pivot: Int): Unit` |
| gates.cpp | `Clause * find_binary_clause (int, int)` | `Internal.findBinaryClause(first: Int, second: Int): Clause?` |
| gates.cpp | `void find_gate_clauses (Eliminator &, int pivot)` | `Internal.findGateClauses(eliminator: Eliminator, pivot: Int): Unit` |
| gates.cpp | `void unmark_gate_clauses (Eliminator &)` | `Internal.unmarkGateClauses(eliminator: Eliminator): Unit` |
| gates.cpp | `void unmark_binary_literals (Eliminator &)` | `Internal.unmarkBinaryLiterals(eliminator: Eliminator): Unit` |
| instantiate.cpp | `void inst_assign (int lit)` | `Internal.instAssign(lit: Int): Unit` |
| instantiate.cpp | `bool inst_propagate ()` | `Internal.instPropagate(): Boolean` |
| instantiate.cpp | `void collect_instantiation_candidates (Instantiator &)` | `Internal.collectInstantiationCandidates(instantiator: Instantiator): Unit` |
| instantiate.cpp | `bool instantiate_candidate (int lit, Clause *)` | `Internal.instantiateCandidate(lit: Int, c: Clause): Boolean` |
| instantiate.cpp | `void instantiate (Instantiator &)` | `Internal.instantiate(instantiator: Instantiator): Unit` |
| internal.cpp | `void init_vars (int new_max_var)` | `Internal.initVars(newMaxVar: Int): Unit` |
| internal.cpp | `void add_original_lit (int lit)` | `Internal.addOriginalLit(lit: Int): Unit` |
| internal.cpp | `void finish_added_clause_with_id (uint64_t lit, bool restore = false)` | `Internal.finishAddedClauseWithId(lit: Long, restore: Boolean = false): Unit` |
| internal.cpp | `void reserve_ids (int number)` | `Internal.reserveIds(number: Int): Unit` |
| internal.cpp | `void enlarge_vals (size_t new_vsize)` | `Internal.enlargeVals(newVsize: Int): Unit` |
| internal.cpp | `void enlarge (int new_max_var)` | `Internal.enlarge(newMaxVar: Int): Unit` |
| internal.cpp | `int propagate_assumptions ()` | `Internal.propagateAssumptions(): Int` |
| internal.cpp | `void get_entrailed_literals (std::vector<int> &entrailed)` | `Internal.getEntrailedLiterals(entrailed: IntArrayList): Unit` |
| internal.cpp | `void init_report_limits ()` | `Internal.initReportLimits(): Unit` |
| internal.cpp | `void init_preprocessing_limits ()` | `Internal.initPreprocessingLimits(): Unit` |
| internal.cpp | `void init_search_limits ()` | `Internal.initSearchLimits(): Unit` |
| internal.cpp | `int try_to_satisfy_formula_by_saved_phases ()` | `Internal.tryToSatisfyFormulaBySavedPhases(): Int` |
| internal.cpp | `void produce_failed_assumptions ()` | `Internal.produceFailedAssumptions(): Unit` |
| internal.cpp | `int already_solved ()` | `Internal.alreadySolved(): Int` |
| internal.cpp | `int restore_clauses ()` | `Internal.restoreClauses(): Int` |
| internal.cpp | `bool preprocess_round (int round)` | `Internal.preprocessRound(round: Int): Boolean` |
| internal.cpp | `int preprocess ()` | `Internal.preprocess(): Int` |
| internal.cpp | `int local_search_round (int round)` | `Internal.localSearchRound(round: Int): Int` |
| internal.cpp | `int local_search ()` | `Internal.localSearch(): Int` |
| internal.cpp | `int cdcl_loop_with_inprocessing ()` | `Internal.cdclLoopWithInprocessing(): Int` |
| internal.cpp | `void reset_solving ()` | `Internal.resetSolving(): Unit` |
| internal.cpp | `int solve (bool preprocess_only = false)` | `Internal.solve(preprocessOnly: Boolean = false): Int` |
| internal.cpp | `void finalize (int)` | `Internal.finalize(res: Int): Unit` |
| internal.cpp | `int lookahead ()` | `Internal.lookahead(): Int` |
| internal.cpp | `void dump (Clause *)` | `Internal.dump(c: Clause): Unit` |
| internal.cpp | `void dump ()` | `Internal.dump(): Unit` |
| internal.cpp | `bool traverse_clauses (ClauseIterator &)` | `Internal.traverseClauses(it: ClauseIterator): Boolean` |
| internal.cpp | `bool traverse_constraint (ClauseIterator &)` | `Internal.traverseConstraint(it: ClauseIterator): Boolean` |
| internal.cpp | `void report_solving (int)` | `Internal.reportSolving(res: Int): Unit` |
| internal.cpp | `void print_statistics ()` | `Internal.printStatistics(): Unit` |
| limit.cpp | `double scale (double v)` | `Internal.scale(v: Double): Double` |
| limit.cpp | `void reset_limits ()` | `Internal.resetLimits(): Unit` |
| limit.cpp | `void limit_terminate (int)` | `Internal.limitTerminate(l: Int): Unit` |
| limit.cpp | `void limit_decisions (int)` | `Internal.limitDecisions(l: Int): Unit` |
| limit.cpp | `void limit_conflicts (int)` | `Internal.limitConflicts(l: Int): Unit` |
| limit.cpp | `void limit_preprocessing (int)` | `Internal.limitPreprocessing(l: Int): Unit` |
| limit.cpp | `void limit_local_search (int)` | `Internal.limitLocalSearch(l: Int): Unit` |
| limit.cpp | `bool limit (const char *name, int)` | `Internal.limit(name: String, l: Int): Boolean` |
| limit.cpp | `bool is_valid_limit (const char *name)` | `isValidLimit(name: String): Boolean  (static: top-level function)` |
| lookahead.cpp | `CubesWithStatus generate_cubes (int, int)` | `Internal.generateCubes(depth: Int, minDepth: Int): CubesWithStatus` |
| lookahead.cpp | `int most_occurring_literal ()` | `Internal.mostOccurringLiteral(): Int` |
| lookahead.cpp | `int lookahead_probing ()` | `Internal.lookaheadProbing(): Int` |
| lookahead.cpp | `int lookahead_next_probe ()` | `Internal.lookaheadNextProbe(): Int` |
| lookahead.cpp | `void lookahead_flush_probes ()` | `Internal.lookaheadFlushProbes(): Unit` |
| lookahead.cpp | `void lookahead_generate_probes ()` | `Internal.lookaheadGenerateProbes(): Unit` |
| lookahead.cpp | `std::vector<int> lookahead_populate_locc ()` | `Internal.lookaheadPopulateLocc(): IntArrayList` |
| lookahead.cpp | `int lookahead_locc (const std::vector<int> &)` | `Internal.lookaheadLocc(loccs: IntArrayList): Int` |
| lookahead.cpp | `bool terminating_asked ()` | `Internal.terminatingAsked(): Boolean` |
| lucky.cpp | `int unlucky (int res)` | `Internal.unlucky(res: Int): Int` |
| lucky.cpp | `int trivially_false_satisfiable ()` | `Internal.triviallyFalseSatisfiable(): Int` |
| lucky.cpp | `int trivially_true_satisfiable ()` | `Internal.triviallyTrueSatisfiable(): Int` |
| lucky.cpp | `int forward_false_satisfiable ()` | `Internal.forwardFalseSatisfiable(): Int` |
| lucky.cpp | `int forward_true_satisfiable ()` | `Internal.forwardTrueSatisfiable(): Int` |
| lucky.cpp | `int backward_false_satisfiable ()` | `Internal.backwardFalseSatisfiable(): Int` |
| lucky.cpp | `int backward_true_satisfiable ()` | `Internal.backwardTrueSatisfiable(): Int` |
| lucky.cpp | `int positive_horn_satisfiable ()` | `Internal.positiveHornSatisfiable(): Int` |
| lucky.cpp | `int negative_horn_satisfiable ()` | `Internal.negativeHornSatisfiable(): Int` |
| lucky.cpp | `int lucky_phases ()` | `Internal.luckyPhases(): Int` |
| minimize.cpp | `void minimize_sort_clause ()` | `Internal.minimizeSortClause(): Unit` |
| minimize.cpp | `bool minimize_literal (int lit, int depth = 0)` | `Internal.minimizeLiteral(lit: Int, depth: Int = 0): Boolean` |
| minimize.cpp | `void minimize_clause ()` | `Internal.minimizeClause(): Unit` |
| minimize.cpp | `void calculate_minimize_chain (int lit, std::vector<int> &stack)` | `Internal.calculateMinimizeChain(lit: Int, stack: IntArrayList): Unit` |
| minimize.cpp | `void clear_minimized_literals ()` | `Internal.clearMinimizedLiterals(): Unit` |
| occs.cpp | `void init_occs ()` | `Internal.initOccs(): Unit` |
| occs.cpp | `void init_noccs ()` | `Internal.initNoccs(): Unit` |
| occs.cpp | `void reset_occs ()` | `Internal.resetOccs(): Unit` |
| occs.cpp | `void reset_noccs ()` | `Internal.resetNoccs(): Unit` |
| phases.cpp | `void clear_phases (vector<signed char> &)` | `Internal.clearPhases(dst: ByteArray): Unit` |
| phases.cpp | `void copy_phases (vector<signed char> &)` | `Internal.copyPhases(dst: ByteArray): Unit` |
| phases.cpp | `void phase (int lit)` | `Internal.phase(lit: Int): Unit` |
| phases.cpp | `void unphase (int lit)` | `Internal.unphase(lit: Int): Unit` |
| probe.cpp | `bool probing ()` | `Internal.probing(): Boolean` |
| probe.cpp | `void failed_literal (int lit)` | `Internal.failedLiteral(lit: Int): Unit` |
| probe.cpp | `void probe_lrat_for_units (int lit)` | `Internal.probeLratForUnits(lit: Int): Unit` |
| probe.cpp | `void probe_assign_unit (int lit)` | `Internal.probeAssignUnit(lit: Int): Unit` |
| probe.cpp | `void probe_assign_decision (int lit)` | `Internal.probeAssignDecision(lit: Int): Unit` |
| probe.cpp | `void probe_assign (int lit, int parent)` | `Internal.probeAssign(lit: Int, parent: Int): Unit` |
| probe.cpp | `int get_parent_reason_literal (int lit)` | `Internal.getParentReasonLiteral(lit: Int): Int` |
| probe.cpp | `void set_parent_reason_literal (int lit, int reason)` | `Internal.setParentReasonLiteral(lit: Int, reason: Int): Unit` |
| probe.cpp | `void clean_probehbr_lrat ()` | `Internal.cleanProbehbrLrat(): Unit` |
| probe.cpp | `void init_probehbr_lrat ()` | `Internal.initProbehbrLrat(): Unit` |
| probe.cpp | `void get_probehbr_lrat (int lit, int uip)` | `Internal.getProbehbrLrat(lit: Int, uip: Int): Unit` |
| probe.cpp | `void set_probehbr_lrat (int lit, int uip)` | `Internal.setProbehbrLrat(lit: Int, uip: Int): Unit` |
| probe.cpp | `void probe_dominator_lrat (int dom, Clause *reason)` | `Internal.probeDominatorLrat(dom: Int, reason: Clause): Unit` |
| probe.cpp | `int probe_dominator (int a, int b)` | `Internal.probeDominator(a: Int, b: Int): Int` |
| probe.cpp | `int hyper_binary_resolve (Clause *)` | `Internal.hyperBinaryResolve(reason: Clause): Int` |
| probe.cpp | `void probe_propagate2 ()` | `Internal.probePropagate2(): Unit` |
| probe.cpp | `bool probe_propagate ()` | `Internal.probePropagate(): Boolean` |
| probe.cpp | `bool is_binary_clause (Clause *c, int &, int &)` | `Internal.isBinaryClause(c: Clause, a: IntRef, b: IntRef): Boolean` |
| probe.cpp | `void generate_probes ()` | `Internal.generateProbes(): Unit` |
| probe.cpp | `void flush_probes ()` | `Internal.flushProbes(): Unit` |
| probe.cpp | `int next_probe ()` | `Internal.nextProbe(): Int` |
| probe.cpp | `bool probe_round ()` | `Internal.probeRound(): Boolean` |
| probe.cpp | `void probe (bool update_limits = true)` | `Internal.probe(updateLimits: Boolean = true): Unit` |
| propagate.cpp | `int assignment_level (int lit, Clause *)` | `Internal.assignmentLevel(lit: Int, reason: Clause?): Int` |
| propagate.cpp | `void build_chain_for_units (int lit, Clause *reason, bool forced)` | `Internal.buildChainForUnits(lit: Int, reason: Clause, forced: Boolean): Unit` |
| propagate.cpp | `void build_chain_for_empty ()` | `Internal.buildChainForEmpty(): Unit` |
| propagate.cpp | `void search_assign (int lit, Clause *)` | `Internal.searchAssign(lit: Int, reason: Clause?): Unit` |
| propagate.cpp | `void search_assign_driving (int lit, Clause *reason)` | `Internal.searchAssignDriving(lit: Int, reason: Clause?): Unit` |
| propagate.cpp | `void search_assign_external (int lit)` | `Internal.searchAssignExternal(lit: Int): Unit` |
| propagate.cpp | `void search_assume_decision (int decision)` | `Internal.searchAssumeDecision(decision: Int): Unit` |
| propagate.cpp | `void assign_unit (int lit)` | `Internal.assignUnit(lit: Int): Unit` |
| propagate.cpp | `bool propagate ()` | `Internal.propagate(): Boolean` |
| propagate.cpp | `void propergate ()` | `Internal.propergate(): Unit` |
| queue.cpp | `void init_enqueue (int idx)` | `Internal.initEnqueue(idx: Int): Unit` |
| queue.cpp | `void init_queue (int old_max_var, int new_max_var)` | `Internal.initQueue(oldMaxVar: Int, newMaxVar: Int): Unit` |
| queue.cpp | `void shuffle_queue ()` | `Internal.shuffleQueue(): Unit` |
| reduce.cpp | `bool flushing ()` | `Internal.flushing(): Boolean` |
| reduce.cpp | `bool reducing ()` | `Internal.reducing(): Boolean` |
| reduce.cpp | `void mark_clauses_to_be_flushed ()` | `Internal.markClausesToBeFlushed(): Unit` |
| reduce.cpp | `void mark_useless_redundant_clauses_as_garbage ()` | `Internal.markUselessRedundantClausesAsGarbage(): Unit` |
| reduce.cpp | `bool propagate_out_of_order_units ()` | `Internal.propagateOutOfOrderUnits(): Boolean` |
| reduce.cpp | `void reduce ()` | `Internal.reduce(): Unit` |
| rephase.cpp | `bool rephasing ()` | `Internal.rephasing(): Boolean` |
| rephase.cpp | `char rephase_best ()` | `Internal.rephaseBest(): Char` |
| rephase.cpp | `char rephase_flipping ()` | `Internal.rephaseFlipping(): Char` |
| rephase.cpp | `char rephase_inverted ()` | `Internal.rephaseInverted(): Char` |
| rephase.cpp | `char rephase_original ()` | `Internal.rephaseOriginal(): Char` |
| rephase.cpp | `char rephase_random ()` | `Internal.rephaseRandom(): Char` |
| rephase.cpp | `char rephase_walk ()` | `Internal.rephaseWalk(): Char` |
| rephase.cpp | `void rephase ()` | `Internal.rephase(): Unit` |
| restart.cpp | `bool stabilizing ()` | `Internal.stabilizing(): Boolean` |
| restart.cpp | `bool restarting ()` | `Internal.restarting(): Boolean` |
| restart.cpp | `int reuse_trail ()` | `Internal.reuseTrail(): Int` |
| restart.cpp | `void restart ()` | `Internal.restart(): Unit` |
| restore.cpp | `void restore_clause (const vector<int>::const_iterator &begin, const vector<int>::const_iterator &end, const uint64_t id)` | `External.restoreClause(begin: Int /* const_iterator */, end: Int /* const_iterator */, id: Long): Unit` |
| restore.cpp | `void restore_clauses ()` | `External.restoreClauses(): Unit` |
| score.cpp | `void init_scores (int old_max_var, int new_max_var)` | `Internal.initScores(oldMaxVar: Int, newMaxVar: Int): Unit` |
| score.cpp | `void shuffle_scores ()` | `Internal.shuffleScores(): Unit` |
| shrink.cpp | `void shrink_and_minimize_clause ()` | `Internal.shrinkAndMinimizeClause(): Unit` |
| shrink.cpp | `void reset_shrinkable ()` | `Internal.resetShrinkable(): Unit` |
| shrink.cpp | `void mark_shrinkable_as_removable (int, std::vector<int>::size_type)` | `Internal.markShrinkableAsRemovable(blevel: Int, minimizedStart: Int): Unit` |
| shrink.cpp | `int shrink_literal (int, int, unsigned)` | `Internal.shrinkLiteral(lit: Int, blevel: Int, maxTrail: Int): Int` |
| shrink.cpp | `unsigned shrunken_block_uip (int, int, std::vector<int>::reverse_iterator &, std::vector<int>::reverse_iterator &, std::vector<int>::size_type, const int)` | `Internal.shrunkenBlockUip(uip: Int, blevel: Int, rbeginBlock: IntRef /* reverse_iterator */, rendBlock: IntRef /* reverse_iterator */, minimizedStart: Int, uip0: Int): Int` |
| shrink.cpp | `void shrunken_block_no_uip (const std::vector<int>::reverse_iterator &, const std::vector<int>::reverse_iterator &, unsigned &, const int)` | `Internal.shrunkenBlockNoUip(rbeginBlock: Int /* reverse_iterator */, rendBlock: Int /* reverse_iterator */, blockMinimized: IntRef, uip0: Int): Unit` |
| shrink.cpp | `void push_literals_of_block (const std::vector<int>::reverse_iterator &, const std::vector<int>::reverse_iterator &, int, unsigned)` | `Internal.pushLiteralsOfBlock(rbeginBlock: Int /* reverse_iterator */, rendBlock: Int /* reverse_iterator */, blevel: Int, maxTrail: Int): Unit` |
| shrink.cpp | `unsigned shrink_next (int, unsigned &, unsigned &)` | `Internal.shrinkNext(blevel: Int, open: IntRef, maxTrail: IntRef): Int` |
| shrink.cpp | `std::vector<int>::reverse_iterator minimize_and_shrink_block (std::vector<int>::reverse_iterator &, unsigned int &, unsigned int &, const int)` | `Internal.minimizeAndShrinkBlock(rbeginBlock: IntRef /* reverse_iterator */, totalShrunken: IntRef, totalMinimized: IntRef, uip0: Int): Int /* reverse_iterator */` |
| shrink.cpp | `unsigned shrink_block (std::vector<int>::reverse_iterator &, std::vector<int>::reverse_iterator &, int, unsigned &, unsigned &, const int, unsigned)` | `Internal.shrinkBlock(rbeginLits: IntRef /* reverse_iterator */, rendBlock: IntRef /* reverse_iterator */, blevel: Int, open: IntRef, blockMinimized: IntRef, uip0: Int, maxTrail: Int): Int` |
| shrink.cpp | `unsigned shrink_along_reason (int, int, bool, bool &, unsigned)` | `Internal.shrinkAlongReason(uip: Int, blevel: Int, resolveLargeClauses: Boolean, failedPtr: BoolRef, maxTrail: Int): Int` |
| solution.cpp | `void check_solution_on_learned_clause ()` | `External.checkSolutionOnLearnedClause(): Unit` |
| solution.cpp | `void check_solution_on_shrunken_clause (Clause *)` | `External.checkSolutionOnShrunkenClause(c: Clause): Unit` |
| solution.cpp | `void check_solution_on_learned_unit_clause (int unit)` | `External.checkSolutionOnLearnedUnitClause(unit: Int): Unit` |
| solution.cpp | `void check_no_solution_after_learning_empty_clause ()` | `External.checkNoSolutionAfterLearningEmptyClause(): Unit` |
| subsume.cpp | `bool subsuming ()` | `Internal.subsuming(): Boolean` |
| subsume.cpp | `void strengthen_clause (Clause *, int)` | `Internal.strengthenClause(c: Clause, lit: Int): Unit` |
| subsume.cpp | `void subsume_clause (Clause *subsuming, Clause *subsumed)` | `Internal.subsumeClause(subsuming: Clause, subsumed: Clause): Unit` |
| subsume.cpp | `int subsume_check (Clause *subsuming, Clause *subsumed)` | `Internal.subsumeCheck(subsuming: Clause, subsumed: Clause): Int` |
| subsume.cpp | `int try_to_subsume_clause (Clause *, vector<Clause *> &shrunken)` | `Internal.tryToSubsumeClause(c: Clause, shrunken: ArrayList<Clause>): Int` |
| subsume.cpp | `bool subsume_round ()` | `Internal.subsumeRound(): Boolean` |
| subsume.cpp | `void subsume (bool update_limits = true)` | `Internal.subsume(updateLimits: Boolean = true): Unit` |
| ternary.cpp | `bool ternary_find_binary_clause (int, int)` | `Internal.ternaryFindBinaryClause(a: Int, b: Int): Boolean` |
| ternary.cpp | `bool ternary_find_ternary_clause (int, int, int)` | `Internal.ternaryFindTernaryClause(a: Int, b: Int, c: Int): Boolean` |
| ternary.cpp | `bool hyper_ternary_resolve (Clause *, int, Clause *)` | `Internal.hyperTernaryResolve(c: Clause, pivot: Int, d: Clause): Boolean` |
| ternary.cpp | `void ternary_lit (int pivot, int64_t &steps, int64_t &htrs)` | `Internal.ternaryLit(pivot: Int, steps: LongRef, htrs: LongRef): Unit` |
| ternary.cpp | `void ternary_idx (int idx, int64_t &steps, int64_t &htrs)` | `Internal.ternaryIdx(idx: Int, steps: LongRef, htrs: LongRef): Unit` |
| ternary.cpp | `bool ternary_round (int64_t &steps, int64_t &htrs)` | `Internal.ternaryRound(steps: LongRef, htrs: LongRef): Boolean` |
| ternary.cpp | `bool ternary ()` | `Internal.ternary(): Boolean` |
| transred.cpp | `void transred ()` | `Internal.transred(): Unit` |
| var.cpp | `void check_var_stats ()` | `Internal.checkVarStats(): Unit` |
| var.cpp | `void reset_subsume_bits ()` | `Internal.resetSubsumeBits(): Unit` |
| vivify.cpp | `void flush_vivification_schedule (Vivifier &)` | `Internal.flushVivificationSchedule(vivifier: Vivifier): Unit` |
| vivify.cpp | `bool consider_to_vivify_clause (Clause *candidate, bool redundant_mode)` | `Internal.considerToVivifyClause(candidate: Clause, redundantMode: Boolean): Boolean` |
| vivify.cpp | `void vivify_analyze_redundant (Vivifier &, Clause *start, bool &)` | `Internal.vivifyAnalyzeRedundant(vivifier: Vivifier, start: Clause, onlyBinaryReasons: BoolRef): Unit` |
| vivify.cpp | `void vivify_build_lrat (int, Clause *, std::vector<std::tuple<int, Clause *, bool>> &)` | `Internal.vivifyBuildLrat(lit: Int, reason: Clause, stack: ArrayList<VivifyLratEntry>): Unit` |
| vivify.cpp | `void vivify_chain_for_units (int lit, Clause *reason)` | `Internal.vivifyChainForUnits(lit: Int, reason: Clause): Unit` |
| vivify.cpp | `bool vivify_all_decisions (Clause *candidate, int subsume)` | `Internal.vivifyAllDecisions(candidate: Clause, subsume: Int): Boolean` |
| vivify.cpp | `void vivify_post_process_analysis (Clause *candidate, int subsume)` | `Internal.vivifyPostProcessAnalysis(candidate: Clause, subsume: Int): Unit` |
| vivify.cpp | `void vivify_strengthen (Clause *candidate)` | `Internal.vivifyStrengthen(candidate: Clause): Unit` |
| vivify.cpp | `void vivify_assign (int lit, Clause *)` | `Internal.vivifyAssign(lit: Int, reason: Clause?): Unit` |
| vivify.cpp | `void vivify_assume (int lit)` | `Internal.vivifyAssume(lit: Int): Unit` |
| vivify.cpp | `bool vivify_propagate ()` | `Internal.vivifyPropagate(): Boolean` |
| vivify.cpp | `void vivify_clause (Vivifier &, Clause *candidate)` | `Internal.vivifyClause(vivifier: Vivifier, candidate: Clause): Unit` |
| vivify.cpp | `void vivify_round (bool redundant_mode, int64_t delta)` | `Internal.vivifyRound(redundantMode: Boolean, delta: Long): Unit` |
| vivify.cpp | `void vivify ()` | `Internal.vivify(): Unit` |
| walk.cpp | `void walk_save_minimum (Walker &)` | `Internal.walkSaveMinimum(walker: Walker): Unit` |
| walk.cpp | `Clause * walk_pick_clause (Walker &)` | `Internal.walkPickClause(walker: Walker): Clause` |
| walk.cpp | `unsigned walk_break_value (int lit)` | `Internal.walkBreakValue(lit: Int): Int` |
| walk.cpp | `int walk_pick_lit (Walker &, Clause *)` | `Internal.walkPickLit(walker: Walker, c: Clause): Int` |
| walk.cpp | `void walk_flip_lit (Walker &, int lit)` | `Internal.walkFlipLit(walker: Walker, lit: Int): Unit` |
| walk.cpp | `int walk_round (int64_t limit, bool prev)` | `Internal.walkRound(limit: Long, prev: Boolean): Int` |
| walk.cpp | `void walk ()` | `Internal.walk(): Unit` |
| watch.cpp | `void init_watches ()` | `Internal.initWatches(): Unit` |
| watch.cpp | `void connect_watches (bool irredundant_only = false)` | `Internal.connectWatches(irredundantOnly: Boolean = false): Unit` |
| watch.cpp | `void sort_watches ()` | `Internal.sortWatches(): Unit` |
| watch.cpp | `void clear_watches ()` | `Internal.clearWatches(): Unit` |
| watch.cpp | `void reset_watches ()` | `Internal.resetWatches(): Unit` |

## Proof functions (later wave)

| upstream file | upstream declaration | Kotlin extension function |
|---|---|---|
| proof.cpp | `void new_proof_on_demand ()` | `Internal.newProofOnDemand(): Unit` |
| proof.cpp | `void setup_lrat_builder ()` | `Internal.setupLratBuilder(): Unit` |
| proof.cpp | `void force_lrat ()` | `Internal.forceLrat(): Unit` |
| proof.cpp | `void resize_unit_clauses_idx ()` | `Internal.resizeUnitClausesIdx(): Unit` |
| proof.cpp | `void close_trace (bool stats = false)` | `Internal.closeTrace(stats: Boolean = false): Unit` |
| proof.cpp | `void flush_trace (bool stats = false)` | `Internal.flushTrace(stats: Boolean = false): Unit` |
| proof.cpp | `void trace (File *)` | `Internal.trace(file: File): Unit` |
| proof.cpp | `void check ()` | `Internal.check(): Unit` |
| proof.cpp | `void connect_proof_tracer (Tracer *tracer, bool antecedents, bool finalize_clauses = false)` | `Internal.connectProofTracer(tracer: Tracer, antecedents: Boolean, finalizeClauses: Boolean = false): Unit` |
| proof.cpp | `void connect_proof_tracer (InternalTracer *tracer, bool antecedents, bool finalize_clauses = false)` | `Internal.connectProofTracer(tracer: InternalTracer, antecedents: Boolean, finalizeClauses: Boolean = false): Unit` |
| proof.cpp | `void connect_proof_tracer (StatTracer *tracer, bool antecedents, bool finalize_clauses = false)` | `Internal.connectProofTracer(tracer: StatTracer, antecedents: Boolean, finalizeClauses: Boolean = false): Unit` |
| proof.cpp | `void connect_proof_tracer (FileTracer *tracer, bool antecedents, bool finalize_clauses = false)` | `Internal.connectProofTracer(tracer: FileTracer, antecedents: Boolean, finalizeClauses: Boolean = false): Unit` |
| proof.cpp | `bool disconnect_proof_tracer (Tracer *tracer)` | `Internal.disconnectProofTracer(tracer: Tracer): Boolean` |
| proof.cpp | `bool disconnect_proof_tracer (StatTracer *tracer)` | `Internal.disconnectProofTracer(tracer: StatTracer): Boolean` |
| proof.cpp | `bool disconnect_proof_tracer (FileTracer *tracer)` | `Internal.disconnectProofTracer(tracer: FileTracer): Boolean` |

## Not ported (messages, reports, profiling, resources)

| upstream file | upstream declaration | Kotlin extension function |
|---|---|---|
| message.cpp | `void vmessage (const char *, va_list &)` | `Internal.vmessage(fmt: String, ap: va_list): Unit` |
| message.cpp | `void message (const char *, ...)` | `Internal.message(fmt: String, : ?...): Unit` |
| message.cpp | `void message ()` | `Internal.message(): Unit` |
| message.cpp | `void vverbose (int level, const char *fmt, va_list &)` | `Internal.vverbose(level: Int, fmt: String, ap: va_list): Unit` |
| message.cpp | `void verbose (int level, const char *fmt, ...)` | `Internal.verbose(level: Int, fmt: String, : ?...): Unit` |
| message.cpp | `void verbose (int level)` | `Internal.verbose(level: Int): Unit` |
| message.cpp | `void section (const char *title)` | `Internal.section(title: String): Unit` |
| message.cpp | `void phase (const char *phase, const char *, ...)` | `Internal.phase(phase: String, fmt: String, : ?...): Unit` |
| message.cpp | `void phase (const char *phase, int64_t count, const char *, ...)` | `Internal.phase(phase: String, count: Long, fmt: String, : ?...): Unit` |
| message.cpp | `void verror (const char *, va_list &)` | `Internal.verror(fmt: String, ap: va_list): Unit` |
| message.cpp | `void error (const char *, ...)` | `Internal.error(fmt: String, : ?...): Unit` |
| message.cpp | `void error_message_start ()` | `Internal.errorMessageStart(): Unit` |
| message.cpp | `void warning (const char *, ...)` | `Internal.warning(fmt: String, : ?...): Unit` |
| profile.cpp | `void stop_profiling (Profile &p, double)` | `Internal.stopProfiling(p: Profile, s: Double): Unit` |
| profile.cpp | `double update_profiles ()` | `Internal.updateProfiles(): Double` |
| profile.cpp | `void print_profile ()` | `Internal.printProfile(): Unit` |
| profile.cpp | `double solve_time ()` | `Internal.solveTime(): Double` |
| report.cpp | `void report (char type, int verbose_level = 0)` | `Internal.report(type: Char, verboseLevel: Int = 0): Unit` |
| resources.cpp | `double process_time ()` | `Internal.processTime(): Double` |
| resources.cpp | `double real_time ()` | `Internal.realTime(): Double` |
| stats.cpp | `void print_resource_usage ()` | `Internal.printResourceUsage(): Unit` |

## Defined in the headers (already in InternalHpp.kt / ExternalHpp.kt) or never defined upstream (not ported)

| upstream file | upstream declaration | Kotlin extension function |
|---|---|---|
| (header / not defined) | `bool terminated_asynchronously (int factor = 1)` | `Internal.terminatedAsynchronously(factor: Int = 1): Boolean` |
| (header / not defined) | `bool search_limits_hit ()` | `Internal.searchLimitsHit(): Boolean` |
| (header / not defined) | `void mark_redundant_clauses_with_eliminated_variables_as_garbage ()` | `Internal.markRedundantClausesWithEliminatedVariablesAsGarbage(): Unit` |
| (header / not defined) | `void probe_post_dominator_lrat (vector<Clause *> &, int, int)` | `Internal.probePostDominatorLrat(p0: ArrayList<Clause>, p1: Int, p2: Int): Unit` |
| (header / not defined) | `const char * parse_dimacs (FILE *)` | `Internal.parseDimacs(p0: FILE): String` |
| (header / not defined) | `const char * parse_dimacs (const char *)` | `Internal.parseDimacs(p0: String): String` |
| (header / not defined) | `const char * parse_solution (const char *)` | `Internal.parseSolution(p0: String): String` |
| (header / not defined) | `int fixed (int elit)` | `External.fixed(elit: Int): Int` |
