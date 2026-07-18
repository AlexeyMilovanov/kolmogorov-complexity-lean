# Source → Lean coverage map

Maintenance rule: **every PR that formalizes, retires, or renames a
paper-facing result must update this file.** Agents: consult this map
*before* formalizing anything — if a row exists, build on the named
theorems instead of re-deriving them.

Sources:

- **SUV** — Shen, Uspensky, Vereshchagin, *Kolmogorov Complexity and
  Algorithmic Randomness* (scan + OCR + theorem index in
  `~/kolmogorov-complexity-literature/SUV-work/`).
- **VS40** — Vereshchagin, Shen, *Algorithmic statistics: forty years
  later* (arXiv:1607.08077, source in
  `~/kolmogorov-complexity-literature/algorithmic-statistics/`).
- **KR** — Kritchman, Raz, *The surprise examination paradox and the
  second incompleteness theorem* (arXiv:1011.4974).

Status legend: ✅ formalized · 🟡 partial · ❌ not started · ➖ out of scope for now.

## SUV book

| Chapter / § | Status | Lean home | Key theorems |
|---|---|---|---|
| 1.1 Plain complexity: definition, invariance | ✅ | `Core/Basic.lean`, `Core/UniversalDecompressor.lean`, `Core/Invariance.lean` | `condK`, `plainK`, `isOptimalConditional`, `existsIsOptimalConditional` |
| 1.1 Incompressibility / counting | ✅ | `Complexity/Incompressibility.lean` | `existsIncompressibleString`, `cardCompressibleWordsLt`, `existsComplexString` |
| 1.2 Algorithmic properties (non-computability, semicomputability) | ✅ | `Complexity/Uncomputability.lean`, `Complexity/Properties.lean` | `notComputablePlainKNat`, `noComputableUnboundedLowerBound`, `condKLeIsRe`, `plainKGtIsCore` |
| 2.1 Complexity of pairs (plain) | 🟡 | `Prefix/Properties.lean` (via prefix bridges) | `plainK_pair_le_KPPair`, `plainK_pair_le_KPPlain_add_KPPlain` — no standalone plain-pair theory |
| 2.2 Conditional complexity | ✅ | `Core/Basic.lean`, `Complexity/Properties.lean` | `condK`, `condKSelf`, `condKLePlainK`, `condKComp` |
| 2.3 **Symmetry of information, plain (Kolmogorov–Levin, O(log))** | ❌ | — | **known gap**; prefix-staged versions exist (see 4.7). Needed by ch. 7/10 |
| 3 Martin-Löf randomness | ➖ | — | infinite sequences; deferred |
| 4.1–4.2 Semimeasures on ℕ, maximal semimeasure | ✅ | `AlgorithmicProbability/Semimeasure.lean`, `UniversalSemimeasure.lean` | `IsSemimeasure`, `IsUniversalSemimeasure`, `exists_universalSemimeasure` |
| 4.3–4.4 Prefix machines | ✅ | `Prefix/Basic.lean`, `Prefix/Machine.lean`, `Prefix/Optimal.lean`, `Prefix/OptimalExistence.lean` | `IsPrefixMachine`, `KP`, `IsOptimalPrefixConditional`, `exists_isOptimalPrefixConditional` |
| 4.5 Coding theorem `K = −log m + O(1)` | ✅ | `AlgorithmicProbability/Coding.lean`, `ConditionalCoding.lean`, `KraftChaitin*.lean` | `universalSemimeasure_equiv_prefixComplexity`, `complexityWeight_KP_le_aprioriMeasure` |
| 4.5 Kraft inequality + converse | ✅ | `Prefix/Kraft.lean`, `Prefix/KraftConverse.lean`, `Prefix/CountableKraft.lean` | `finset_kraft_progWeight_le_one`, `exists_prefixFree_code_of_kraft_le_one` |
| 4.6 Properties of prefix complexity | ✅ | `Prefix/Properties.lean`, `Prefix/CountingBound.lean`, `Prefix/TotalCountingBound.lean` | assorted |
| 4.7 Conditional prefix complexity, pairs, SOI | ✅ | `Prefix/Symmetry.lean`, `Prefix/ConditionalSymmetry.lean`, `Prefix/CondTwoStage.lean`, `Prefix/KPPairSwap.lean` | `KPPair_symmetryOfInformation_staged`, `KPCondPair_symmetryOfInformation_staged` |
| 5 Monotone complexity | ➖ | — | deferred |
| 6 General scheme for complexities | ❌ | — | |
| 7 Shannon entropy ↔ complexity | ❌ | — | **recommended next** (SUV track) |
| 8 Applications | ❌ | — | |
| 9 Frequency/game randomness | ➖ | — | deferred |
| 10 Inequalities for entropy/complexity/size | ❌ | — | after ch. 7 |
| 11 Common information | ❌ | — | |
| 12 Multisource (Muchnik) | ❌ | — | |
| 14 / algorithmic statistics | — | see VS40 below | |

## VS40 survey

| Section | Status | Lean home | Key theorems |
|---|---|---|---|
| §1 Statistical models | ✅ | `AlgorithmicStatistics/Basic.lean`, `FiniteSetModel.lean`, `CodedFiniteDistribution.lean`, `NormalizedCodedFiniteDistribution.lean` | model/`codedUniformOn` infrastructure |
| §2.1 Prefix complexity, a priori probability, randomness deficiency | ✅ | `AlgorithmicStatistics/Deficiency.lean`, `DeficiencyTest.lean` | `DeficiencyLe` (multiplicative form) |
| §2.2 Definition of stochasticity | ✅ | `AlgorithmicStatistics/Stochasticity.lean` | `IsStochastic`, monotonicity lemmas |
| §2.3 Stochasticity conservation | ✅ | `AlgorithmicStatistics/Conservation.lean`, `Selector.lean` | |
| §2.4 Non-stochastic objects | ✅ | `AlgorithmicStatistics/NonStochastic.lean` | |
| §3.1 Optimality deficiency, two-part descriptions | ✅ | `TwoPart/Basic.lean`, `OptimalityDeficiency.lean`, `DescriptionShift.lean` | `InDescriptionProfile`, `OptimalityDeficiencyLe` |
| §3.2 Optimality vs randomness deficiencies (Thm 4/5 chain) | ✅ | `TwoPart/Deficiencies.lean`, `GapCounting.lean`, `DescriptionSnapshot.lean`, `PaperTheorems.lean` | `deficiencies_theorem_tight_thm`, `stochasticity_to_optimal_set_thm`, `optimal_stochasticity_imp_profile_thm` |
| §3.3 Complexity/size trade-off; profile realization (`stat-any-curve`) | ✅ | `TwoPart/Profile.lean`, `CurveRealization.lean`, `GreedyWindow.lean`, `ProfileRealization.lean` | `structureFunction_admissible`, `ProfileCurve`, `exists_string_with_profile`; improving descriptions: `improving_descriptions_complexity_thm`, `improving_descriptions_size_thm` |
| §4 Bounded complexity lists | ❌ | — | needs list-of-strings encoding API |
| §5 Computational/logical depth | ➖ | — | needs resource-bounded computability |
| §6 Descriptions of restricted type | 🟡 | `Foundation/EnumerationComplexity.lean`, `Restricted/Family.lean`, `Restricted/BasicProfile.lean`, `Restricted/GreedyCover.lean`, `Restricted/Selection.lean`, `Restricted/EffectiveSelection.lean`, `Restricted/Improving.lean`, `Restricted/DeficiencyEquiv.lean`, `Restricted/Examples/Cylinders.lean`, `Restricted/Examples/Masks.lean`, `Restricted/Examples/HammingBalls.lean`, `Restricted/HammingGap.lean`, `Restricted/FamilyCurve.lean`, `Restricted/FamilyCurve/Basic.lean`, `Restricted/FamilyCurve/Selector.lean`, `Restricted/FamilyCurve/EffectiveRebuild.lean`, `Restricted/FamilyCurve/BadStream.lean`, `Restricted/FamilyCurve/CoupledRun.lean`, `Restricted/FamilyCurve/RunCoding.lean`, `Restricted/FamilyCurve/EffectiveRun.lean`, `Restricted/FamilyCurve/EffectiveRunSemantics.lean`, `Restricted/FamilyCurve/AnchoredRun.lean`, `Restricted/FamilyCurve/RunBounds.lean` | `StagedEnumeration.KPPlain_le_log_index_of_enumeration`, `StagedEnumeration.KP_le_log_index_of_cond_enumeration`, `StagedEnumeration.KP_le_fixed_length_index_of_cond_enumeration`, `StagedEnumeration.setComplexity_le_log_index_of_enumeration`, `DescriptionFamily.HasPolynomialOverhead`, `DescriptionFamily.overhead_bits_le_logSlack`, `fullFamily_hasPolynomialOverhead`, `cylinderFamily_hasPolynomialOverhead`, `maskFamily_hasPolynomialOverhead`, `hammingFamily_hasPolynomialOverhead`, `inDescriptionProfileIn_fullFamily_iff`, `DescriptionFamily.singleton_mem`, `inDescriptionProfileIn_fullCube_of_optimal` (M2 a1), `inDescriptionProfileIn_singleton_of_optimal` (M2 a2), `exists_family_cover`, `exists_cover_codes_in_stage` (enumeration-stage refinement of the cover: a good cover whose codes all lie in a single `enum T`), `inDescriptionProfileIn_cover_shift` (M2 a3 — proved via `Restricted/CoverSearch.lean`), `greedy_cover`, `greedy_cover_indexed`, `selectionStrategy_length_bound`, `selectionStrategy_covers` (proved finite-stage indexed greedy selection), `familyStageModelCodesList_mono`, `familyMarkedCodeStream_computable`, `familyMarkedCodeStream_mono`, `familyMarkedCodeStream_sound`, `exists_markedStream_rank`, `ManyIJDescriptionsIn`, `manyIJDescriptionsIn_fullFamily_iff`, `inDescriptionProfileIn_improving_size`, `exists_familyComplexityRefinedSet`, `inDescriptionProfileIn_improving_complexity`, `restricted_improving_descriptions_conditional` (M5 draft), `restricted_stochasticity_to_optimal_set_thm` (M5 draft), `restricted_stochasticity_to_optimal_set_uniform` (M5 draft), `cylinderFamily` (M3 draft), `maskFamily` (M3 draft), `hammingFamily` (M3 draft), `prop_hamming_gap` (M6 draft), `restrictedCurveGrid_height_le_target_add_mesh`, `restrictedCurveGrid_mesh_le_sqrtSlack`, `restrictedCurveGrid_code_length_le_sqrt`, `KPPlain_restrictedCurveGridCode_le`, `exists_encoded_restricted_curve_grid`, `decode_restrictedCurveGridCode_sample_eq`, `restrictedSampledBadCodeStream_mono`, `restrictedSampledBadCodeStream_computable_uniform`, `restrictedSampledBadCodeStream_sound`, `restrictedSampledBadCodeStream_catches_violation`, `cover_argmax_intersection_bound`, `restrictedCoverValidBool_computable`, `restrictedMaxIntersectionCoverSelector_partrec`, `restrictedMaxIntersectionCoverSelector_spec`, `restrictedEffectiveRebuildStep_spec`, `restrictedEffectiveRebuildSuffix_partrec`, `restrictedEffectiveRebuildSuffix_decodes_density` (M7 effective suffix), `restrictedEffectiveSampledInitialState`, `restrictedEffectiveSampledRun`, `restrictedEffectiveSampledRun_partrec_uniform`, `restrictedSampledNewBadBatch_append`, `restrictedEffectiveLiveCodesAfterDelete_decode`, `restrictedEffectiveDensityFailsBool_iff`, `restrictedEffectiveFirstFailedScale_spec`, `restrictedEffectiveSampledRunStep_terminates`, `restrictedEffectiveSampledRun_step_spec`, `restrictedSampledBadBatchAt_decode_sound`, `restrictedEffectiveSampledRunProcess_spec`, `restrictedEffectiveSampledRun_processed_disjoint`, `restrictedEffectiveSampledRun_spec`, `restrictedAnchoredTarget`, `restrictedEffectiveAnchoredSizes`, `restrictedEffectiveAnchoredSampledRun`, `restrictedAnchoredRun_sample_getD`, `RestrictedSampledRunState.dropAnchor`, `restricted_rebuild_suffix`, `restrictedSampledRun_step_preserves`, `restrictedSampledRun_deleted_fresh`, `restrictedSampledRun_invariants`, `restricted_large_bad_appearances_le`, `restricted_small_bad_deleted_volume_le`, `restricted_rebuilds_charged_to_deleted_volume`, `restrictedSampledRun_rebuild_count_le`, `restrictedSampledRun_version_code_complexity`, `restrictedSampledRun_root_antitone`, `restrictedSampledRun_stabilizes`, `restrictedProfileBadSet_card_le`, `restrictedAnchoredProcessedBadUnion_card_le`, `restrictedCurveGrid_bad_volume_padding`, `exists_restricted_anchored_structural_output`, `RestrictedSampledOutputCore`, `RestrictedSampledOutput`, `restrictedCurveGridPredecessor_spec`, `RestrictedSampledOutput.toCoupledOutput`, `exists_restricted_sampled_output_core` (M7 version-coding leaf), `RestrictedCoupledOutput`, `exists_restricted_coupled_output`, `RestrictedScaleState` (M7 draft), `exists_restricted_scale_state` (M7 draft), `prop_family_curve` (M7 draft) |
| §7 Strong models | ❌ | — | needs total conditional complexity |

Internal M7 sampled-run combinatorics live in
`Restricted/FamilyCurve/SampledRun.lean`: `restricted_min_failed_scale_prefix_safe`
and `restricted_rebuild_suffix_terminal_nonempty` are proved.  Fresh deletion
blocks are now proved pairwise disjoint and feed
`restricted_self_rebuilds_charged_to_deleted_volume`.  The extensional
least-failed-scale transition and its finite-batch chronological recursion are
proved in `Restricted/FamilyCurve/CoupledRun.lean`, including fresh deletion and
the doubled post-rebuild density margin.  The effective decoder is now lifted
through finite batches and chronological time; connecting the anchored result
to final-state survival and bounded version ordinals remains open in
`exists_restricted_sampled_output_core`.  That leaf receives the exact encoded
grid together with its proved complexity budget; grid existence and the uniform
mesh estimate are no longer part of the obligation.
The static interpolation
from the `N + 1` sampled sets to every `i ≤ k` is now proved by
`RestrictedSampledOutput.toCoupledOutput`; in particular, the open construction
no longer ranges its version accounting over all `k + 1` coordinates.
`RunCoding.lean` now proves
the concrete finite charging bridge, binary version-code bound, root
antitonicity, eventual root stabilization, persistence of processed deletions
(`restrictedSampledRun_processed_bad_disjoint`), and survivor extraction from a
nonempty stabilized root (`restrictedSampledRun_exists_persistent_survivor`).
The extensional chronological run still makes no claim that all of its choices
form a computable version stream.  `EffectiveRebuild.lean` now supplies the
missing uniform partial-recursive suffix iterator and proves that its decoded
steps satisfy the same family-membership, size, live-intersection, and density
contract.  The computable maximum-intersection cover selector also has the proved coding leaf
`restrictedMaxIntersectionCoverSelector_KPPlain_le`, bounding the selected
cover-member code complexity by the selector-input complexity plus a uniform
constant.

`EffectiveRun.lean` keeps that partiality explicit: malformed inputs may
diverge instead of being assigned a noncomputable default.  Its coded update
deletes the new event, finds the least failed density edge, retains the safe
model prefix, and rebuilds only the strict suffix.  The false claim that every
new bad-code batch is empty has been replaced by the proved exact append
identity `restrictedSampledNewBadBatch_append`.  The former draft name
`restrictedEffectiveSampledRun_computable_uniform` is superseded by the honest
partial-recursive statement `restrictedEffectiveSampledRun_partrec_uniform`;
that statement and the decoded one-step correctness theorem
`restrictedEffectiveSampledRun_step_spec` are proved.

The sampled bad-event enumeration in `Restricted/FamilyCurve/BadStream.lean`
is prefix-stable and computable uniformly from the encoded grid.  Its catching
lemma now explicitly requires both `IsCodeFor c U` and strict decrease of the
target curve; these hypotheses are necessary to connect snapshot complexity to
`U` and to compare unsampled target heights with sampled grid heights.

`Restricted/FamilyCurve/RunBounds.lean` proves the concrete interval-wise
length bound for the sampled bad-code stream and its eventual stabilization
(`restrictedSampledBadCodeStream_length_le` and
`restrictedSampledBadCodeStream_stabilizes`).  It identifies the recursive
processed union with the chronological stream, proves the sound interval-wise
cardinality estimate `restrictedAnchoredProcessedBadUnion_card_le`, absorbs
that estimate into the balanced ambient cube with
`restrictedCurveGrid_bad_volume_padding`, and packages the complete nonempty
survivor/avoidance phase in `exists_restricted_anchored_structural_output`.
The stream's actual square-root subtraction is kept separate from the final
profile slack, avoiding a nested `sqrtSlack`.  `VersionDecoder.lean` now proves
partial recursiveness of the fixed-code event trace, actual-model change trace,
and version decoder, with all grid parameters recovered from the encoded grid.
The remaining core obligation is replay correctness for the terminal sampled
model, bounding its actual change ordinal by `RestrictedRunChain.rebuildSteps`,
and the final plain-complexity arithmetic for the self-delimiting decoder
bundle.
`EffectiveRun.lean` now also
proves the uniform partial-recursiveness of the chronological executor and the
decoded initial-state specification.  Its deletion trace now decodes exactly,
the executable density test is proved equivalent to the extensional predicate,
the first-failed-scale search has its least-index specification, and the
effective suffix search is proved to terminate.  Assembling the retained prefix
and rebuilt suffix into the decoded next-state invariants, and proving the
least-failed-edge transition contract, are now complete.

`EffectiveRunSemantics.lean` proves the finite-batch and chronological lifting.
Its public theorem is tied to an actual `RestrictedCurveGrid`; an earlier draft
incorrectly quantified an unrelated exponent function and omitted the initial
top-size bound.  `AnchoredRun.lean` starts the next M7 step by inserting the
fixed ambient cube at run level zero and shifting sampled level `s` to level
`s+1`.  Target/size alignment, monotonicity, code lookup, and sampled-state
projection, the effective initializer, and the exact finite-time root invariant
are proved.

## Other formalized results (outside the two sources)

| Result | Lean home | Key theorems |
|---|---|---|
| Chaitin incompleteness (abstract formal system) | `Complexity/Chaitin.lean`, `ChaitinCorollaries.lean` | `chaitinBound`, `chaitinIncompleteness` |
| Second incompleteness, Kritchman–Raz style (KR) | `Complexity/SecondIncompleteness.lean`, `SecondIncompletenessCorollaries.lean` | `secondIncompleteness` |
| Bundled paper-facing interface | `Interface/StandardMachine.lean` | `StandardMachine` + wrappers |
| List/tuple encoding API | `Encoding/Tuples.lean`, `Encoding/TuplesComplexity.lean` | `listCode`, `decodeListCode_listCode`, `listCode_injective`, `listCode_primrec`, `KPPlain_listCode_le`, `KP_component_listCode_le` |
| Primrec toolkit | `Foundation/PrimrecExtras.lean` | `Primrec.list_take/drop/takeWhile/replicate`, `Primrec.nat_iterate'`, `primrec_auto` — add new general `Primrec` lemmas HERE |

## Known gaps / debts

- **Plain symmetry of information** (SUV §2.3, `C(x,y) = C(x) + C(y|x) + O(log)`): not formalized; only prefix-staged versions and one-directional plain↔prefix bridges exist.
- ~~Chain-rule refactor~~ **done**: `KP_le_prefixComplexityContext_add_logSlack`
  is now a direct corollary of `KP_cond_remove_short_info`; the rest of
  `GapCounting`/`DescriptionShift` already sits on the pair/SOI primitives.
- `AdmissibleCurve` in `TwoPart/Profile.lean` is intentionally kept as a
  *documented false start* (`AdmissibleCurve_unsatisfiable`); do not build on it —
  use `structureFunction_admissible` / `ProfileCurve`.
