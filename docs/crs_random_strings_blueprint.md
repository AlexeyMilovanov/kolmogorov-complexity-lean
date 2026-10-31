# Blueprint nodes and their Lean declarations

This page maps every node of the paper's blueprint for *Limit on the Computational Power of
C-Random Strings* to the Lean declarations in `KolmogorovMathlib/RandomStrings/Plain/` that
formalize it. The Lean docstrings carry the same references as "Blueprint node `label`", so

```
grep -rn "Blueprint node" KolmogorovMathlib/RandomStrings/Plain
```

lists them in the source.

**Conventions.**

* All declarations are in the namespace `Kolmogorov.Milovanov` (for example the first entry
  below is `Kolmogorov.Milovanov.exists_optimal_halting_not_poly_time_cumulative`), except
  where a different prefix is written out.
* `P/` abbreviates the directory `KolmogorovMathlib/RandomStrings/Plain/`.
* Only the principal declarations of a node are listed. A node whose proof needs many small
  lemmas (the encodings, the construction state machine, the referee tree) lists the
  definitions and statements that carry its content. The other declarations of the named
  module are supporting material and have their own docstrings.
* Nodes are grouped by blueprint section, in the order of the proof.

## 1. Final theorems

The main theorem: some optimal plain decompressor `U` has a cumulative complexity oracle that
does not compute the halting language in polynomial time. The theorems of this section only
assemble the pieces of the later sections.

* `thm:target` — the final theorem. `exists_optimal_halting_not_poly_time_cumulative`
  (`P/Target.lean`) gives an optimal conditional machine `U` with
  `HBin ∉ PolyTimeOracle (CumulativeOracle encF U)`.
* `cor:random-target` — the same for the random-string oracle.
  `exists_optimal_halting_not_poly_time_random` (`P/Target.lean`) states
  `HBin ∉ PolyTimeOracle (PlainRandomOracle U)`.
* `native:joint` — one machine witnesses both separations.
  `exists_optimal_native_halting_oracle_separation` (`P/Target.lean`) and its twin
  `native_halting_oracle_separation_joint` (`P/Main.lean`).
* `native:main` — the cumulative-oracle theorem for the concrete machine.
  `native_halting_not_poly_time_cumulative` (`P/Main.lean`), obtained from the flag-indexed
  `native_halting_not_poly_time`. The concrete data are `nativeSeparatingMachine`
  (equal to `fighterU nativeFighterParams nativePadding`), `nativeBase`, `nativeLiteral`,
  `nativeFighterParams`, `nativePadding`, `nativeFixedData`, `nativePriceData`,
  `nativeTailData` and the specification lemmas `native_separating_machine_spec`,
  `native_padding_spec`, `native_fixed_data_spec`, `native_price_data_spec`,
  `native_price_data_exists`, `native_tail_data_spec`, `native_fighter_price_hypotheses`
  (all `P/Main.lean`).
* `native:random` — the random-string-oracle theorem for the same machine.
  `native_halting_not_poly_time_random` (`P/Main.lean`).

## 2. Foundations

* `FoundationConditionalMachine` (also labeled `FoundationConditionalOptimality` and
  `FoundationOptimalPlain`) — the fixed optimal conditional machine. It is the structure
  `Base` with `nonempty_base` (`P/Basic.lean`).
* `FoundationConditionalComposition` — conditional prefix composition and removal of an
  auxiliary condition. `conditional_prefix_composition` and
  `conditional_prefix_composition_remove` (`P/PrefixInterface.lean`).
* `FoundationPrefixChainRule` — the exact conditional chain rule up to a constant.
  `conditional_prefix_chain_interface` and `conditional_prefix_chain_interface_lower`
  (`P/PrefixInterface.lean`).
* `FoundationPrefixCoding` — a priori mass of the optimal prefix machine and uniform
  conditional coding. `conditional_coding_interface` with the parts
  `conditional_coding_interface_mass`, `_approx`, `_mono`, `_limit` and `_uniform`
  (`P/PrefixInterface.lean`).
* `FoundationPlainPrefixBounds` — plain and prefix complexity agree at a supplied length up
  to a constant. `plain_prefix_supplied_length_interface` and its `_reverse`
  (`P/PrefixInterface.lean`).
* `FoundationPrefixRaw` — a prefix program followed by a raw suffix.
  `plain_prefix_program_raw_suffix` (`P/PrefixInterface.lean`).
* `FoundationPrefixSelfSufficiency` — `K(a, K(a | z) | z) = K(a | z) + O(1)`.
  `prefix_self_sufficiency_interface` and `_lower` (`P/PrefixInterface.lean`).
* `FoundationPrefixLiteralBound` (also labeled `FoundationIntegerPrefixCode` and
  `FoundationTupleEncoding`) — literal codes, integer codes, tuple encodings and the
  complexity bounds for them. All in `P/Encoding.lean`:
  `literalCode`, `literalCode_prefix_free`, `parseLiteral`, `integerCode`,
  `length_integerCode_le`, `integerLiteralBound`, `literalBound`, `triple`,
  `triple_injective`, `extensionCode`, `encF` (with `encF_injective`, `length_encF`,
  `target_length_le_encF`, `decodeQuery`), and the combined statement
  `literal_and_tuple_code_interface` with its parts `_integer`, `_pair`, `_triple`,
  `_plain_map` and `_prefix_map`.
* `FoundationOracleClockedMachines` — not a declaration of this development. It names the
  repository's existing clocked oracle-machine interface `Kolmogorov.RandomStrings.OTM` and
  its polynomial-time oracle classes (`PolyTimeOracle`), used throughout Section 7.

## 3. Counting, stages and markers

* `lem:counting` — a partial decompressor has fewer than `2^(k+1)` strings of complexity at
  most `k`. `simple_finite_card_lt` (`P/Basic.lean`).
* `lem:stage-api` — the finite stage histories `E_{k,s}` are computable and monotone.
  `canonical_enumeration_spec` (`P/Enumeration/Schedule.lean`) says the master state is
  computable. The remaining content is in the `canonical_enumeration_spec_*` lemmas
  (`_history`, `_mono`, `_outputs`, `_tables`, `_prefix_computable`, `_prefix_mono` in
  `Schedule.lean`; `_sound`, `_complete`, `_unique`, `_union`, `_candidate`, `_position`,
  `_prefix`, `_prefix_bound`, `_prefix_min`, `_queue`, `_search`, `_search_eq` in
  `P/Enumeration/CanonicalSpec.lean`). The data structures are `Candidate`,
  `PrefixObservation`, `ProgramEvent`, `TimedEvent`, `ScheduleState`, with `masterStep`,
  `masterState`, `eventAt`, `eventHistory`, `stageOutputs`, `stagePrefixComplexity` and
  `candidatePrefixComplexity` (`Schedule.lean`).
* `lem:marker-stabilization` — the marker (the last program of length at most `n`)
  stabilizes. `lastProgram`, `markerCandidate`, `markerPosition`, `markerTick`, `programTick`,
  `last_program_stabilizes_short_descriptions` with `_no_later` and `_position`
  (`P/Markers/LastProgram.lean`).
* `lem:marker-incompressible` — the marker is conditionally incompressible given `n`.
  `last_program_conditional_complexity` (`P/Markers/LastProgram.lean`) is the statement; the
  closing arithmetic is `last_program_conditional_complexity_deficit`
  (`P/Markers/StagePrefix.lean`).
* `lem:short-prefix-exact` — stage-bounded prefix complexity is exact for short objects.
  `marker_stage_prefix_complexity_exact` with `_candidate` and `_common`
  (`P/Markers/StagePrefix.lean`); the stage-bounded quantity is `candidatePrefixComplexity`
  (`P/Enumeration/Schedule.lean`).
* `lem:tail` — tail bound for the marker. `last_program_tail_bound` and
  `last_program_tail_bound_advice` (`P/Markers/StagePrefix.lean`).
* `cor:tail-budget` — the exponential-scale budget `Rest(n, 2^n) ≤ c₁ 2^(2^n - n)`.
  `exponential_tail_budget` (`P/Markers/StagePrefix.lean`).

## 4. The Key Lemma

* `key:main` — uniform integer-slack Key Lemma: a total price algorithm that is sound and
  complete up to `c_gap (δ+1)`. `extension_price_sound_complete`, with the parts
  `_sound` and `_strict`, and the specification `ExtensionPriceSpec`
  (`P/ExtensionPrice/SquareRoot.lean`).
* `key:sqrt` — the square-root formulation for even `d`.
  `extension_price_square_root_soundness` and `extension_price_square_root_slack`
  (`P/ExtensionPrice/SquareRoot.lean`).
* `key:algorithm` — the total price algorithm. `compute_extension_price` with
  `compute_extension_price_computable`, `_invalid`, `_small`; the data are
  `CandidatePriceInput`, `CandidatePrice`, `ExtensionPriceConstants`,
  `extensionPriceAlgorithm`, `extensionPriceDyadic` and `extension_price_dyadic_pos`
  (`P/ExtensionPrice/SquareRoot.lean`).
* `key:complete` — strict completeness. `extension_price_complete`
  (`P/ExtensionPrice/SquareRoot.lean`).
* `key:slack` — prefix-to-plain conversion with explicit slack.
  `plain_complexity_of_prefix_bound_with_slack` with `_bound` and `_linear`
  (`P/ExtensionPrice/SquareRoot.lean`).
* `key:volumes` — the single structural volume interface. `StructuralVolumeBounds` and
  `key_lemma_structural_volume_interface` with the parts `_decomposition`, `_future`,
  `_relaxed`, `_remaining` and `_simple` (`P/ExtensionPrice/SquareRoot.lean`).
* `key:density` — extension density with an explicit gap. `extension_density`
  (`P/ExtensionDensity/Density.lean`), `extension_density_relaxed` and
  `extension_density_common` (`P/ExtensionDensity/Relaxed.lean`); the objects are
  `extensionSet`, `extensionCount`, `strictExtensionCount`, `extensionScale`,
  `ExtensionDensityBounds`, `extension_set_finite` and `prefix_complexity_finite_value`
  (`P/ExtensionDensity/Bounds.lean`).
* `key:projection` — computable transformations preserve volume.
  `extension_volume_of_computable_projection` (`P/ExtensionDensity/Relaxed.lean`).
* `key:proxy` — the total computable structural proxy and the carrier identity.
  `compute_structural_proxy` with `_carrier`, `_common`, `_exact`, `_first`, `_length`
  (`P/StructuralProxy/Symmetry.lean`); the proxy itself is `computeStructuralProxy`,
  `structuralProxyAlpha`, `structuralProxyBeta`, `structuralProxyDelta`,
  `structuralProxyIndex`, `proxyCarrier`, `StructuralProxySpec`, together with the tower
  machinery `tower`, `IsTower`, `TowerRange`, `towerFloor`, `towerRangeBound`,
  `tower_floor_spec`, `tower_floor_computable`, `tower_range_separation`
  (`P/StructuralProxy/Towers.lean`).
* `key:crossing` — uniform adjacent differences and the finite crossing.
  `structural_proxy_crossing` with `_common` and `_finite`, `proxyCrossingIndex`,
  `proxyCrossingIndices`, `proxyPair`, `ExactProxyTable`, `zero_mem_proxy_crossing_indices`
  (`P/StructuralProxy/Towers.lean`).
* `key:symmetry` — constant-precision symmetry transfer.
  `structural_proxy_symmetry_transfer` (`P/StructuralProxy/Symmetry.lean`) and its basepoint
  `proxyBase` (`P/StructuralProxy/Towers.lean`).
* `key:gaps` — information-gap verification. `key_lemma_information_gaps` with `_lower`,
  `_marker`, `_plain`, `_upper`, and the records `KeyParameters`, `KeyInformationGaps`
  (`P/ExtensionPrice/PastFuture.lean`).
* `key:decompositions` — the two volume decompositions. `key_lemma_past_future_decompositions`
  with `_common` and `_lower` (`P/ExtensionPrice/Decompositions.lean`); the pieces are
  `LowerVolumeDecomposition`, `UpperVolumeDecomposition`, `extension_set_triple`,
  `lowerProxyBase`, `upperFutureBase`, `pastExtensionIndices`, `pastExtensionCount`,
  `mem_past_extension_indices`, `past_extension_count_eq` and
  `past_extension_count_computable` (`P/ExtensionPrice/PastFuture.lean`).

## 5. The construction

### State, actions, and the game

* `constr:game` — the finite counter game. `finite_counter_game`, `FiniteCounterGame`
  (with `LegalMove`, `objective`, `counterAnswer`), `CounterPosition`,
  `counter_answer_eq_true` (`P/FiniteGame/Rules.lean`).
* `constr:determinacy` — computable determinacy. `finite_counter_game_computable_winner`
  (`P/FiniteGame/RoleExchange.lean`), built from `FiniteCounterGame.solve` and
  `solveCounterGameCode` (`P/FiniteGame/Rules.lean`).
* `constr:flip` — symmetric control and one-unit target flipping. `symmetric_game_target_flip`,
  `fresh_dummy_target_flip`, `counter_game_role_exchange`, `FiniteCounterGame.exchangeRoles`,
  `FiniteCounterGame.controlWinningPlayer` (`P/FiniteGame/RoleExchange.lean`).
* `constr:tree` — referee preprocessing and finite coordinates.
  `finite_referee_coordinates` with `mem_finite_referee_coordinates`,
  `retainedCoordinateList`, `retained_coordinates_downward_closed`,
  `QueryTree.normalize`, `QueryTree.eval_normalize`, `normalizedAnswer`,
  `refereeOutput`, `refereeActualOutput`, `refereeSetOutput`,
  `referee_preprocessing_correct` and `referee_preprocessing_computable`
  (`P/Construction/Referees.lean`).
* `constr:admissible` — referee families and admissible occurrences. `RefereeFamily` and
  `admissible_clocked_occurrence` (`P/Construction/Referees.lean`).
* `constr:late` — every referee has arbitrarily late admissible occurrences.
  `clocked_machine_has_late_admissible_occurrence` and `polynomial_below_tower_range`
  (`P/Construction/Referees.lean`).
* `constr:range` — retained coordinates lie in the Key Lemma's domain.
  `retained_coordinates_within_key_lemma_range` (`P/Construction/Referees.lean`).
* `constr:conditional` — the conditional extension `U_d` of the constructed machine.
  `constructed_conditional_machine`, `constructed_machine_directive` and
  `constructed_machine_simulation` (`P/Construction/Conditional.lean`).
* `constr:optimal` — conditional optimality of the extension.
  `constructed_machine_optimal_conditional`, `constructed_machine_condK_le`,
  `constructed_machine_partrec`, `constructed_machine_literal_bound`, `PlainLiteral`,
  `nonempty_plainLiteral`, `constructedLiteralConstant` (`P/Construction/Conditional.lean`).
* `constr:algorithm` — construction state and phase initialization. `fighter_construction`
  (`P/Construction/State.lean`), over the records `FighterParams` (with `Admissible`),
  `FighterPhase` (with `J`, `game`, `live`, `official`, `indicesAt`, `fundRequests`,
  `predicateHolds`, `virtualAnswer`, `virtualOutput`), `FighterState` (with `activeAt`,
  `putPhase`), `PhaseEnd`, `EndedPhase`, `DirectiveKind`, `AllocatedDirective`,
  `FighterPhaseCode`, `initialFighterState`, `fighterOwner`, `fighterInitialIndices`,
  `fighterStageOutputs`, `fighterStageOutputList`, `fighterFreshString`, `halfPadding`
  (`State.lean`, with `equivProd`/`equivSum` encodings of the records), and the final
  virtual state `fighterFinalVirtualAnswer`, `fighterFinalVirtualOutput`,
  `fighterPhaseAt`, `fighterPhaseOracle` (`P/Construction/Effective/StateMachine.lean`).
* `constr:actions` — fuel, payoff and priority actions. `fighter_actions`
  (`P/Construction/Actions.lean`), assembled from `fighterAllocate`, `fighterCancel`,
  `fighterAbortAbove`, `fighterCloseLevel`, `fighterClosure`, `fighterClosureFuel`,
  `fighterDummy`, `fighterFlushBuffer`, `fighterFuelUnit`, `fighterFuelUnits`,
  `fighterFulfillReady`, `fighterLevelAction`, `fighterOpponent`, `fighterPayoff`,
  `fighterProcessLevel`, `fighterSafe`, `fighterStartPhase`, `fighterStrategyMove`,
  `FighterPhase.insertIndex`, `FighterPhase.unitVector`; the buffer invariants
  `FighterPhase.Backed` and `FighterPhase.BufferInvariant` are in
  `P/Construction/Effective/StateMachine.lean`.

### Accounting

* `constr:phasecount` — phase counts. `fighter_phase_count`
  (`P/Construction/Accounting/PhaseCountBounds.lean`), with `fighterPhaseCount`,
  `fighterDirectiveCount` and `fighterPhaseCount_lt_two_pow`
  (`P/Construction/Accounting/TargetRange.lean`).
* `constr:intervals` — disjoint target ranges. `fighter_directive_target_ranges`,
  `fighter_level_ranges_disjoint` and `fighter_target_types_disjoint`
  (`P/Construction/Accounting/LevelRanges.lean`), `FighterActivated` and `FighterTargetRange`
  (`.../TargetRange.lean`), `fighter_earlier_target_bound`
  (`.../EarlierTargets.lean`), and the numeric lemmas `fighter_dummy_below_range`,
  `fighter_previous_upper_bound`, `fighter_range_below_upper`, `fighter_log_padding_bound`
  and others in `.../PhaseCountBounds.lean`.
* `constr:capacity` — global payoff bound and fresh descriptions.
  `fighter_description_capacity` (`P/Construction/Accounting/OutputSet.lean`).
* `constr:smallset` — the small-output-set bound. `constructed_machine_exponential_output_bound`
  (`P/Construction/Accounting/UniformRank.lean`), `constructed_machine_output_set_finite`
  (`.../OutputSet.lean`) and `fighterSmallSet` (`P/Construction/Effective/StateMachine.lean`).
* `constr:rank` — uniform fixed-length rank description of the small set.
  `constructed_machine_uniform_rank_code` (`P/Construction/Accounting/UniformRank.lean`).

### Effectivity

* `constr:effective` — computable event transitions and the effective machine.
  `fighter_event_transition_computable`, `fighter_state_computable`,
  `fighter_directive_stream_partrec`, `fighter_allocations_injective`,
  `fighter_machine_optimal_conditional` (`P/Construction/Effective/Allocations.lean`);
  the state-machine objects `fighterState`, `fighterAllocationAt`, `fighterG`, `fighterOracle`,
  `fighterU` and `fighter_owner_spec` (`.../StateMachine.lean`); the stage-level
  computability lemmas in `.../ConstructionTransitions.lean`; the invariants
  `fighter_live_invariants` and `fighter_initial_base_counters` (`.../LiveInvariants.lean`);
  `fighter_event_actions_complete` (`.../EventActions.lean`);
  `fighter_closure_fixpoint` (`P/Construction/Actions.lean`).

### Stability of the true-marker phase

* `constr:dchoice` — one global choice of the padding constant. `choose_fighter_padding`,
  `fighter_good_padding_exists`, `fighter_fixed_constants_exist`, `GoodPadding`,
  `FighterFixedConstants`, `FighterPriceHypotheses`, `FighterRankHypothesis`,
  `FighterCapacityHypothesis`, `fighter_price_hypotheses_mono`
  (`P/Construction/Stability/Padding.lean`).
* `constr:lowerstable` — lower levels have settled at a late true marker.
  `lower_levels_settled_at_true_marker` (`P/Construction/Stability/SettledLowerLevels.lean`),
  `LateAdmissibleOccurrence`, `LowerLevelsSettled`, `TrueMarkerPhaseStarted`,
  `fighterLevelHistory` (`.../Padding.lean`).
* `constr:opponent` — opponent affordability and buffering.
  `true_marker_opponent_stream_legal` (`.../OpponentStream.lean`), `TrueMarkerLegalPlay`,
  `TrueMarkerClosureLegal`, `fighterBeforeClosure`, `fighterBeforeLevel`, `fighterClosureAt`
  (`.../LegalPlay.lean`), `TrueMarkerNeverEndsFor` (`.../Padding.lean`).
* `constr:realization` — every funded true-marker request is eventually realized.
  `true_marker_funded_request_realized` (`.../FundedRequest.lean`),
  `trueMarkerPhase`, `TrueMarkerPhaseAt`, `TrueMarkerPhaseSurvives`,
  `true_marker_indices_backed`, `true_marker_initial_table_on_tree`,
  `FighterPhase.initialAnswer` (`.../Padding.lean`).
* `constr:separation` — target and query separation. `true_marker_phase_separation`
  (`.../PhaseSeparation.lean`), `TrueMarkerSeparation`, `FighterLowerSources`,
  `FighterHigherLevelsIrrelevant`, `fighterStageAnswer` (`.../Padding.lean`).

### The diagonal

* `constr:agreement` — eventual agreement of the final virtual and the actual oracle on the
  query tree. `true_marker_virtual_actual_oracle_agreement`
  (`P/Construction/Diagonal/OracleAgreement.lean`), with `fighterVirtualOutputAt`,
  `fighterVirtualAnswerAt`, `fighterActualAnswer`, `fighter_actual_answer_eq`,
  `true_marker_virtual_output_eq` (`.../VirtualOutput.lean`),
  `true_marker_virtual_output_stabilizes` (`.../VirtualStabilization.lean`) and
  `true_marker_final_output_agrees` (`.../PolynomialCounting.lean`).
* `constr:diagonal` — diagonal failure of counting.
  `constructed_oracle_defeats_polynomial_counting` and `RefereeFamily.Contains`
  (`P/Construction/Diagonal/PolynomialCounting.lean`).

## 6. Native referees and the halting language

* `native:halting-language` — the binary halting language. `HBin`
  (`P/HaltingLanguage.lean`) with `haltWord`, `decodeHaltWord`, `sd`, `bits` and their
  correctness lemmas (`haltWord_injective`, `decodeHaltWord_haltWord`, `length_haltWord`,
  `haltWord_computable`) in `P/Encoding.lean`.
* `native:representation` — representation and undecidability.
  `native_halting_representation` and `haltWord_mem_HBin` (`P/Native/Instances.lean`).
* `native:literal` — literal length bound for threshold instances.
  `literal_threshold_instance_length`, `nativeLiteralFactor`, `nativeThresholdInstance`,
  `nativeThresholdData`, `nativeStringIndex` with `native_string_index_spec`,
  `_computable`, `_injective` (`P/Native/Instances.lean`).
* `native:search-index` — a fixed search index for each decompressor.
  `exists_threshold_search_index`, `decodeNativeThresholdData` and
  `native_threshold_data_spec` (`P/Native/Instances.lean`).
* `native:adapters` — cumulative and random raw answers. `NativeOracleFlag`,
  `nativeOracle`, `nativeRawAnswer`, `nativeCoordinateAnswer`, `NativeCoordinateTable`,
  `native_oracle_answer_adapters`, `native_oracle_adapters_computable`
  (`P/Native/Adapters.lean`).
* `native:adapter-correct` — adapter correctness and length control.
  `native_oracle_adapters_correct` (`P/Native/Adapters.lean`), with `nativeRawCoordinate`
  and `nativeInspectedCoordinate`.
* `native:finite-table-api` — bounded acceptance on explicit tables.
  `clocked_acceptance_finite_table_adapter`, `nativeClockedAcceptance`,
  `nativeClockedAcceptanceCode`, `native_clocked_acceptance_computable`, `NativeRawTable`,
  `nativeRawTableAnswer`, `nativeRawPositives`, `native_raw_words_spec`
  (`P/Native/Adapters.lean`).
* `native:referee` — the referee of a tuple. `native_counting_referee`, `NativeTuple`,
  `NativeTupleCode`, `nativeTupleBound`, `native_tuple_bound_eq`, `nativeRefereeLeaf`,
  `nativeRefereeRawTable`, `nativeRefereeTest`, `nativeTableTree`, `nativeBinarySearchState`
  (`P/Native/Referees/EffectiveInterface.lean`), and `nativeRawWords`, `nativeCoordinateList`,
  `nativeInspectedCoordinate`, `native_coordinate_list_spec` (`P/Native/Adapters.lean`).
* `native:referee-interface` — effective interface and query bounds.
  `native_referee_effective_interface`, `native_tuple_bound_polynomial`,
  `native_referee_test_clock_le`, `native_binary_search_terminates`
  (`P/Native/Referees/EffectiveInterface.lean`).
* `native:correct-referee` — correct clocked deciders force a correct referee.
  `native_referee_counts_of_clocked_decider` (`P/Native/Referees/ClockedDecider.lean`) and
  `native_binary_search_correct` (`.../EffectiveInterface.lean`).
* `native:family` — the infinitely repeated effective family. `native_referee_family`
  (`P/Native/Referees/ClockedDecider.lean`) with `nativeRefereeTree`, `nativeRefereeBound`,
  `nativeTupleAt`, `nativeTupleEnumeration` and its surjectivity and computability lemmas,
  `native_tuple_occurs_above`; the tuple encoding `encodeNativeTuple`, `decodeNativeTuple`,
  `decode_encode_native_tuple` (`.../EffectiveInterface.lean`); and the selected family
  `nativeFamily`, `native_family_spec`, `native_family_contains` (`P/Main.lean`).

## 7. Nodes realized differently or not formalized

* `lem:two-branch` has no declaration of its own; the two-branch optimality it describes is
  `constructed_machine_optimal_conditional` (`constr:optimal`).
* `native:halting-language` names a definition `native_halting_language`. The Lean
  development uses `HBin` together with the encoding functions of `P/Encoding.lean` instead.
* `FoundationConditionalOptimality`, `FoundationOptimalPlain`, `FoundationIntegerPrefixCode`
  and `FoundationTupleEncoding` are extra labels on the nodes in Section 2 and are realized
  by the declarations listed there.
* `FoundationOracleClockedMachines` refers to the existing `Kolmogorov.RandomStrings.OTM`
  interface and is not re-developed here.
* The remaining optional nodes are not part of the repository-native route and have no Lean
  counterpart: `FoundationPolynomialOracleComposition`, `lem:random-reduction`,
  `lem:threshold-compiler` and `thm:count-reduction`. The final theorem instead compares the
  referee's counting output with the constructed oracle directly (`native:referee`,
  `native:correct-referee`, `constr:diagonal`).
