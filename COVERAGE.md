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
| §6 Descriptions of restricted type | ❌ | — | **recommended next** (survey track); reuses §3 machinery, Hamming-ball model class |
| §7 Strong models | ❌ | — | needs total conditional complexity |

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
