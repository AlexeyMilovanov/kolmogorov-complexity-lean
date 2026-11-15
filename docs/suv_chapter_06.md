# SUV Chapter 6 — General scheme for complexities: formalization notes

Shen, Uspensky, Vereshchagin, *Kolmogorov Complexity and Algorithmic Randomness* (AMS 2017),
Chapter 6: Sections 6.1 Decision complexity, 6.2 Comparing complexities, 6.3 Conditional
complexities, 6.4 Complexities and oracles. Page numbers in the tables below are the printed
page numbers of the book.

## Overview

Every numbered theorem and problem of the chapter is stated and proved in Lean except Problem 207; Problems 204 and 210 are formalized only in part, and Problems 197 (c) and 203 in a weaker form (see the deviations below). The modules are in
`KolmogorovMathlib/Complexity/GeneralScheme/`, the declarations are in the namespace
`Kolmogorov.GeneralScheme`, and the aggregator `KolmogorovMathlib.Complexity.GeneralScheme` is
imported by `KolmogorovMathlib.lean`. The larger modules (`DecisionMinimality`, `Comparing`,
`OracleDefs`, `Relativized`, `LargeConditionsPlain`, `Frequencies`) are themselves aggregators of
topical submodules; the "Module" columns below name the submodule that contains each
declaration. No `sorry` remains under `GeneralScheme`, and every theorem
depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`.

The chapter covers:

* decision complexity `KR` (Theorem 127, Problems 192–196);
* the unified α-β description modes and the comparison of `C`, `K`, `KM`, `KR` (Theorem 128,
  Problems 197–199);
* conditional modes, Schnorr numberings and complexity of functions (Theorems 129, 130,
  Problems 200–203);
* oracles, conditions given by sets, large conditions and lower frequencies (Problems 204–213,
  Theorems 131–136), together with the enumeration complexities `KE` and `m(S)`.

## Conventions

The library's conventions are followed throughout:

* `BitString = List Bool`, `Map = BitString × BitString →. BitString`.
* Complexities are `ℕ∞`-valued (`⊤` = no description). `KA` is the library's real-valued a
  priori complexity.
* There is no fixed optimal decompressor. Every statement takes an optimal machine as a
  hypothesis: `isOptimalConditional U` (plain `C`, `condK`), `IsOptimalPrefixConditional U`
  (prefix `K` = `KPPlain`, conditional `KP`), `IsOptimalMonotoneDecompressor D` (`KMOf`), and
  `R.IsOptimal` (`KROf`). Existence theorems `exists_isOptimal…` show that the hypotheses are not
  vacuous.
* `O(1)`: `∃ c : ℕ, ∀ x, a x ≤ b x + c`, with `∃ c` before `∀ x`. Two-sided `= + O(1)`
  statements use one constant for both directions.
* `O(log v)`: `((c * Nat.log 2 v + c : ℕ) : ℕ∞)`. When `v` is a complexity, it is `.toNat` of a
  finite value. Finiteness is stated separately: `KROf_ne_top`, `exists_const_setCondK_le_plainK`.
* Natural numbers as conditions or objects are coded by `Nat.bits n`, as in
  `computable_iff_condK_prefix_bounded`. Infinite sequences are `CantorSeq` with `cantorPrefix`.
* Oracles: `charOracle A`, `haltingOracle` (= `charOracle jumpSet`, the book's `0'`),
  `IsOptimalConditionalIn`, `PointToSet.IsOptimalOraclePrefix`, `PointToSet.IsREIn`,
  `PointToSet.IsLowerSemicomputableIn`.

## New definitions

| Definition | Module | Meaning |
|---|---|---|
| `StrRel`, `StrRel.Holds` | `Regular` | the relations `=` and `≍` (compatible) on strings |
| `IsRegular α β R`, `IsDescriptionMode`, `modeComplexity`, `IsOptimalDescriptionMode` | `Regular` | α-β description modes of §6.2 (`R p x`, description first) |
| `IsCondRegular`, `IsCondDescriptionMode`, `condModeComplexity`, `IsOptimalCondDescriptionMode` | `Regular` | `(α, β) \| γ` decompressors of §6.3 (`S p x y`) |
| `DecisionDecompressor`, `KROf`, `DecisionDecompressor.IsOptimal`, `KRSeq` | `Decision` | decision machines (`rel p x`: output on `p` starts with `x`), `KR` |
| `ContDecisionMap`, `ContDecisionMap.complexity` | `Decision` | computable continuous maps `ℕ⊥ → Σ` (Problem 193) |
| `bitwiseKR`, `IsOptimalBitwise` | `Decision` | Problem 194 |
| `PrintsPrefix`, `programKR`, `programKP` | `Decision` | Problems 195, 196 (programs = `Nat.Partrec.Code`) |
| `pairKROf`, `IsOptimalPairDecision`, `pairKMOf`, `IsOptimalPairMonotone`, `pairAPrioriOf`, `IsOptimalPairAPriori` | `Pairs` | Problem 198 (a), (b), (c) |
| `funComplexity`, `IsOptimalFunDecompressor` | `Numberings` | Problem 203 |
| `IsComputableNumbering`, `IsOptimalNumbering`, `numberingComplexity` | `Numberings` | Theorem 130 (Schnorr) |
| `jumpSet`, `charSeq` | `OracleDefs.MonotoneDecompressors` | `0'` as a set of naturals, characteristic sequence |
| `DecisionDecompressorIn`, `KRInOf`, `IsComputableStreamMapIn`, `IsOptimalMonotoneDecompressorIn`, `IsLSCContinuousSemimeasureIn`, `IsMaximalContinuousSemimeasureIn`, `KAOf` | `OracleDefs.MonotoneDecompressors` | relativized `KR`, `KM`, `KA` |
| `setCondK`, `IsOptimalSetCond`, `IsOptimalPrefixStableSetCond`, `IsOptimalPrefixFreeSetCond`, `setProgramComplexity`, `atLeast` | `SetConditions` | `C(x ‖ A)`, `K(x ‖ A)`, `K'(x ‖ A)`, `≥ n` |
| `EnumDecompressor`, `KEOf`, `ProbEnumerator`, `ProbEnumerator.output`, `.prob`, `.IsOptimal` | `Enumeration` | `KE(S)`, `m(S)` |
| `countOcc`, `lowerFreq`, `countOccPart`, `lowerFreqPart` | `Frequencies.LowerFrequency` | lower frequencies |

## Item map

Status: **existing** = a declaration of the library outside this chapter; **new** = a
declaration added by this chapter; **omitted** = deliberately not stated, with the reason.

### Section 6.1 Decision complexity

| Item | p. | Status | Lean name | Module | Deviations / choices |
|---|---|---|---|---|---|
| Problem 192 | 194 | new | `exists_optimal_decisionDecompressor` | `DecisionBasic` | |
| Problem 193 | 194 | new | `range_KROf_eq_range_contDecisionMap_complexity` | `DecisionMinimality.Minimality` | "not important for complexity" formalized as equality of the sets of complexity functions; close to definitional here (`⊥` is not a description) |
| Theorem 127 (a) | 194 | new | `theorem127a_KROf_mono` (from `KROf_mono_of_prefix`) | `DecisionBasic`; `Decision` | exact, for every decompressor |
| Theorem 127 (b), monotone | 194 | new | `KROf_cantorPrefix_monotone` | `DecisionBasic` | |
| Theorem 127 (b), bounded ⇔ computable | 194 | new | `computable_iff_KROf_prefixes_bounded` | `DecisionBasic` | |
| Theorem 127 (b), parenthetical remark | 194 | new | `KRSeq_ne_top_iff` | `DecisionBasic` | `KRSeq` = supremum of the prefix complexities |
| Theorem 127 (c) | 194 | new | `exists_const_KROf_le_plainK` | `DecisionBasic` | |
| Theorem 127 (d) | 194 | new | `exists_const_KROf_le_KMOf` | `DecisionBasic` | |
| Theorem 127 (e) | 194 | new | `exists_const_KMOf_le_KROf_add_log` | `DecisionBasic` | `O(log KR)` as `c·log₂ KR + c` |
| Theorem 127 (f) | 194 | new | `exists_const_condK_length_le_KROf` | `DecisionBasic` | condition `Nat.bits l(x)` |
| Theorem 127 (g) | 194 | new | `exists_const_KROf_comp_le` | `DecisionMinimality.MapsAndPrefixFreeSets` | stated for every finite prefix `y` of `f(x)` (`streamLowerGraph f x y`) |
| Theorem 127 (h) | 194 | new | `exists_const_plainK_comp_le_KROf` | `DecisionMinimality.MapsAndPrefixFreeSets` | `f : Σ → ℕ⊥` as a partial computable prefix-stable function |
| Theorem 127 (i) | 195 | new | `exists_const_KROf_comp_le_plainK` | `DecisionMinimality.MapsAndPrefixFreeSets` | `f : ℕ⊥ → Σ` as a decision decompressor (value at `⊥` irrelevant, see Problem 193) |
| Theorem 127 (j) | 195 | new | `encard_lt_two_pow_of_isPrefixFree_KROf_lt` | `DecisionMinimality.MapsAndPrefixFreeSets` | for every decompressor; `encard` covers infinite sets |
| Theorem 127 (k) | 195 | new | `isUpperSemicomputable_KROf` | `DecisionMinimality.MapsAndPrefixFreeSets` | for every decompressor |
| Theorem 127 (l) | 195 | new | `KROf_le_of_isUpperSemicomputable` | `DecisionMinimality.Minimality` | `O(2ⁿ)` as `≤ c·2ⁿ` |
| Theorem 127 (m) | 195 | new | `exists_const_KROf_le_KA` | `DecisionMinimality.Minimality` | real-valued, like `exists_const_KA_le_KMOf` |
| `KR ≤ l(x) + O(1)` (unnumbered) | 194 | new | `exists_const_KROf_le_length`, `KROf_ne_top` | `DecisionBasic` | |
| Problem 194 | 196 | new | `exists_isOptimalBitwise`, `exists_const_bitwiseKR_equiv` | `DecisionVariants` | |
| Problem 195 | 197 | new | `exists_const_programKR_equiv` | `DecisionVariants` | programs = `Nat.Partrec.Code`, bit `i` = value at `i` |
| Problem 196 | 197 | new | `exists_const_KMOf_le_programKP`, `not_exists_const_programKP_le_KMOf` | `DecisionVariants` | |

### Section 6.2 Comparing complexities

| Item | p. | Status | Lean name | Module | Deviations / choices |
|---|---|---|---|---|---|
| Figure 3: `KR ≤ C`, `KR ≤ KM` | 197 | new | Theorem 127 (c), (d) | `DecisionBasic` | |
| Figure 3: `C ≤ K`, `KM ≤ K` | 197 | existing | `condK_le_KPPlain`; `exists_const_KMOf_le_KP` | `Prefix.Properties.Part01`; `MonotoneComplexity.MonotoneFromPrefix` | |
| Problem 197 (a) | 197 | new | `exists_prefixStableFun_of_isRegular_compat_eq` | `Comparing.RegularRelations` | continuity part; computability is used inside Theorem 128 |
| Problem 197 (b) | 197 | existing + new bridge | `streamGapFill_isStreamLowerGraph`; `isStreamLowerGraph_streamGapFill_of_isRegular` | `MonotoneComplexity.StreamGapFill`; `Comparing.RegularRelations` | |
| Problem 197 (c) | 197 | new | `exists_decisionDecompressor_of_isDescriptionMode_eq_compat` | `Comparing.RegularRelations` | weaker than the book: only for enumerable relations, see the deviations |
| Theorem 128, existence | 198 | new | `exists_isOptimalDescriptionMode` | `Comparing.RegularRelations` | one theorem for all four `α, β`; the `≍`-`≍` case is also `exists_optimalConsistentRelation` (Problem 137, `MonotoneComplexity.ConsistentRelationComplexity`) |
| Theorem 128, `=`-`=` = `C` | 198 | new | `exists_const_modeComplexity_eq_eq_plainK` | `Comparing.RegularRelations` | |
| Theorem 128, `≍`-`=` = `K` | 198 | new | `exists_const_modeComplexity_compat_eq_KPPlain` | `Comparing.OptimalModes` | |
| Theorem 128, `≍`-`≍` = `KM` | 198 | new | `exists_const_modeComplexity_compat_compat_KMOf` (via `isOptimalDescriptionMode_compat_compat_iff`) | `Comparing.OptimalModes` | from Problem 137 |
| Theorem 128, `=`-`≍` = `KR` | 198 | new | `exists_const_modeComplexity_eq_compat_KROf` | `Comparing.OptimalModes` | |
| Problem 198 (a) | 198 | new | `exists_isOptimalPairMonotone` | `Pairs` | "define" = existence of an optimal pair of stream maps |
| Problem 198 (b) | 198 | new | `exists_isOptimalPairAPriori` | `Pairs` | a 2-tape probabilistic machine = a pair of computable stream maps on the same random sequence; "define" = existence of a machine maximal up to a constant factor |
| Problem 198 (c) | 198 | new | `exists_isOptimalPairDecision` | `Pairs` | |
| Problem 199 | 198 | new | `exists_const_pairKROf_le_length_add_length` | `Pairs` | |
| Triples / `k`-tuples, Karpovich's `KM` pair gap | 198 | omitted | — | — | cited results, no proof in the text |
| Classification by minimal upper semicomputable functions | 199 | existing | Theorem 8: `plainK_le_of_isUpperSemicomputable_of_card_lt_two_pow`; Theorem 62: `KPPlain_le_iff_tsum_two_pow_neg_ne_top`; Theorem 127 (l) (new); Theorem 80: `KA_isMinimal_upperSemicomputableComplexity` | `Complexity.EnumerableFamilies.CountingBounds`; `Prefix.UpperSemicomputableBound`; `DecisionMinimality.Minimality`; `MonotoneComplexity.APrioriMinimality` | summary of earlier results |
| Pentagon: `C ≤ KR + O(log n)` | 199 | new | `exists_const_plainK_le_KROf_add_log` | `Comparing.OptimalModes` | |
| Pentagon: `K ≤ KR + O(log n)` | 199 | new | `exists_const_KPPlain_le_KROf_add_log` | `Comparing.OptimalModes` | |
| `KA ≤ KR + O(log KR)` | 199 | omitted (corollary) | — | — | follows from 127 (e) and `exists_const_KA_le_KMOf` |
| North-west lines, Theorems 73, 86, 87 | 199–200 | existing | `solovay_plain_eq_prefix_sub_prefix_prefix`, `plainK_KMOf_log_gap_both_signs`, `gacsDay_separation` | `MonotoneComplexity.Omega.SolovayInverse.Core`; `MonotoneComplexity.PlainMonotoneSeparation`; `MonotoneComplexity.GacsDayTheorems` | remarks recalling earlier theorems |

### Section 6.3 Conditional complexities

| Item | p. | Status | Lean name | Module | Deviations / choices |
|---|---|---|---|---|---|
| Theorem 129 | 200 | new | `exists_isOptimalCondDescriptionMode` | `Conditional` | one theorem for all eight classes |
| Problem 200 | 201 | new (= Theorem 129) | `exists_isOptimalCondDescriptionMode` | `Conditional` | the problem asks for the detailed proof of Theorem 129 |
| Notation: `C(x\|y) = K(=,=)\|=` | 201 | new | `exists_const_condModeComplexity_eq_eq_eq_condK` | `Conditional` | |
| Notation: `K(x\|y) = K(≍,=)\|=` | 201 | new | `exists_const_condModeComplexity_compat_eq_eq_KP` | `Conditional` | `KP` with an optimal prefix-free conditional machine |
| Problem 201 | 201 | new | `exists_const_condModeComplexity_eq_le_compat` | `Conditional` | |
| Problem 202 | 201 | new | `exists_const_plainK_le_condModeComplexity_add_KROf` | `Conditional` | |
| Problem 203 | 201 | new | `exists_isOptimalFunDecompressor`, `exists_const_funComplexity_singleton_eq_condK` | `Numberings` | maps `ℕ⊥ → F` represented by functional enumerable triple sets; weaker than the book: optimality only on finite functions, not on every `f ∈ F` (see the deviations) |
| Function spaces `(Y → X)` for all 8 classes | 201 | omitted | — | — | informal remark (Scott domains), no statement |
| Theorem 130 | 202 | new | `exists_isOptimalNumbering` | `Numberings` | `h(n) = O(n)` as `h n ≤ c·(n+1)` |
| Schnorr: complexity of `x ↦ y` is `C(y\|x)` | 202 | new | `exists_const_numberingComplexity_eq_condK` | `Numberings` | |
| Schnorr's isomorphism of optimal numberings | 202 | omitted | — | — | cited result, proof not in the text |

### Section 6.4 Complexities and oracles

| Item | p. | Status | Lean name | Module | Deviations / choices |
|---|---|---|---|---|---|
| Relativized optimal decompressors exist | 202–203 | existing (prefix) / new | `exists_optimalOraclePrefix` (existing); `exists_isOptimalConditionalIn`, `exists_optimal_decisionDecompressorIn`, `exists_isOptimalMonotoneDecompressorIn`, `exists_isMaximalContinuousSemimeasureIn` | `Oracle.Universal.Optimal`; `OracleDefs.MonotoneDecompressors` (all but the last); `OracleDefs.MaximalSemimeasure` (the last) | needed so that the relativized hypotheses are not vacuous |
| Problem 204 | 203 | new | `exists_const_KP_oracle_eq_lim_condModeComplexity` | `Relativized.ProblemOracleLimit` | Partial: `lim` as `liminf ≥ K^A - c` and `limsup ≤ K^A + c` only; the book's first claim, a definition of `(A, x) ↦ K^A(x)` uniform in `A`, is not formalized (the constant may depend on `A`) |
| `C^A ≤ C + O(1)` | 203 | new | `exists_const_plainK_oracle_le_plainK` | `Relativized.ProblemOracleLimit` | |
| `C` is `0'`-computable | 203 | new | `computableIn_haltingOracle_cVal` | `Relativized.DecidableOracle` | |
| `0'`-complexity of lists, `B(n)`, `BB(n)` is `O(log n)`; most strings have `C^{0'} ≥ n - O(1)` | 203 | omitted | — | — | informal remarks |
| Problem 205 (`C`) | 203 | new | `isDecidableSet_of_plainK_eq_plainK_oracle` | `Relativized.DecidableOracle` | two-sided hypothesis, as printed |
| Problem 205 (`KM`) | 203 | new | `isDecidableSet_of_KMOf_eq_KMOf_oracle` | `Relativized.DecidableOracle` | |
| Problem 205 (`KR`) | 203 | new | `isDecidableSet_of_KROf_eq_KRInOf` | `Relativized.DecidableOracle` | |
| Problem 205 (`KA`) | 203 | new | `isDecidableSet_of_KA_eq_KAOf` | `Relativized.DecidableOracle` | `KA^A = -log₂ a` for a maximal `A`-semimeasure `a` |
| `K`-low sets exist | 203 | omitted | — | — | cited deep result |
| `α` computable iff `K(α↾n \| n) = O(1)` | 203–204 | omitted | — | — | remark; the plain version is Exercise 48 `computable_iff_condK_prefix_bounded` |
| Problem 206 | 204 | new | `exists_isOptimalSetCond`, `exists_const_setCondK_eq_setProgramComplexity` | `SetConditions` | |
| `C(x ‖ {a}) = C(x \| a)` | 204 | new | `exists_const_setCondK_singleton_eq_condK` | `SetConditions` | |
| `C(x ‖ A) ≤ C(x)`, monotone in `A`, `C(x ‖ ∅)` | 204 | new | `exists_const_setCondK_le_plainK`, `setCondK_mono`, `antitone_setCondK_atLeast`, `setCondK_empty` | `SetConditions` | `C(x ‖ ∅) = 0` exactly |
| Theorem 131 | 204 | new | `exists_const_iInf_setCondK_atLeast_eq_plainK_jump` | `LargeConditionsPlain.PlainJumpLimit` | `lim` = `⨅` (non-increasing) |
| `sup_{m≥n} C(x\|m) ≤ C(x ‖ ≥ n)` | 205 | new | `exists_const_iSup_condK_le_setCondK_atLeast` | `LargeConditionsPlain.PlainJumpLimit` | |
| Lemma in proof of Theorem 132 | 205 | new | `encard_eventually_condK_lt_lt_two_pow` | `LargeConditionsPlain.PlainJumpLimit` | for every decompressor; uses `exists_condK_ge_of_finset_card_pow` |
| Theorem 132 | 205 | new | `exists_const_limsup_condK_eq_plainK_jump` | `LargeConditionsPlain.LimsupJump` | `Filter.limsup` in `ℕ∞` |
| Lemma in proof of Theorem 133 (`liminf` of semimeasures) | 206–207 | new | `tsum_liminf_le_one` | `LargeConditionsPrefix` | Fatou for the counting measure |
| Theorem 133 | 206 | new | `exists_const_limsup_KP_eq_KP_jump` | `LargeConditionsPrefix` | |
| Problem 207 | 207 | omitted | — | — | with the triple representation, computable continuous maps `Σ → F` are exactly graphs of prefix-stable decompressors, so the statement would be definitional; domain theory for `F` is not formalized |
| Optimal `K(x ‖ A)`, `K'(x ‖ A)` exist | 207 | new | `exists_isOptimalPrefixStableSetCond`, `exists_isOptimalPrefixFreeSetCond` | `LargeConditionsPrefix` | |
| `m(x ‖ A)`, `-log m(k ‖ A) ≤ K(k ‖ A)` | 208 | omitted | — | — | needs probabilistic machines with input; not formalized |
| `K(k ‖ A) ≤ K'(k ‖ A) + O(1)` | 208 | new | `exists_const_prefixStableSetCond_le_prefixFreeSetCond` | `LargeConditionsPrefix` | |
| Kalinina: the second inequality is strict | 208 | omitted | — | — | cited result |
| `sup_{a∈A} K(k\|a) ≤ K(k ‖ A)` | 208 | new | `exists_const_iSup_KP_le_prefixStableSetCond` | `LargeConditionsPrefix` | |
| Theorem 134 | 208 | new | `exists_const_iInf_prefixSetCondK_atLeast_eq_KP_jump` | `LargeConditionsPrefix` | |
| Problem 208 | 208 | new | `exists_const_setCondK_le_prefixStableSetCond`, `problem208_prefixStable_le_prefixFree`, `exists_const_prefixFreeSetCond_le_setCondK_add_log` | `LargeConditionsPrefix` | three bounds `C ≤ K ≤ K' ≤ C + O(log C)` |
| Open: `C(x ‖ A)` vs `-log m(k ‖ A)` | 208 | omitted | — | — | open question in the book |
| `KE`: optimal exists, finite iff enumerable | 208 | new | `exists_optimal_enumDecompressor`, `KEOf_ne_top_iff` | `Enumeration` | |
| `m(S)`: optimal exists | 209 | new | `exists_optimal_probEnumerator` | `Enumeration` | |
| Problem 209 | 209 | new | `isEnumerableSet_of_prob_pos`, `prob_pos_iff_isEnumerableSet` | `Enumeration` | |
| `KE` vs `-log m` (Solovay, Vereshchagin) | 209 | omitted | — | — | cited / open, and the printed inequalities are garbled (`log m(S)` without sign) |
| `∑ pₖ ≤ 1` | 209 | new | `sum_lowerFreq_le_one`, `lowerFreq_nonneg` | `Frequencies.LowerFrequency` | finite partial sums |
| Theorem 135 | 209 | new | `isLowerSemicomputableIn_jumpSet_lowerFreq` | `Frequencies.LowerFrequency` | |
| Problem 210 | 210 | new | `isLowerSemicomputableIn_jumpSet_liminf` | `Frequencies.LowerFrequency` | Partial: only the `0'`-lower-semicomputability of the `liminf`; the effective passage from an algorithm for `rₙ` to the `0'`-algorithm is not formalized. No boundedness hypothesis on `r` (an infinite `liminf` gives Mathlib's junk value `0`, trivially lsc) |
| Problem 211 | 210 | new | `exists_computable_liminf_eq` | `Frequencies.MaximalFrequency` | the sequence produced is bounded |
| Theorem 136 | 210 | new | `exists_computable_le_lowerFreq` | `Frequencies.MaximalFrequency` | |
| Corollary: maximal `0'`-semimeasure as frequencies | 210 | new | `exists_computable_lowerFreq_maximal` | `Frequencies.MaximalFrequency` | |
| Corollary: `K^{0'}(k) = -log pₖ + O(1)` | 210 | new | `exists_computable_KP_jump_eq_neg_log_lowerFreq` | `Frequencies.MaximalFrequency` | includes `∀ k, 0 < pₖ`, which excludes `logb 2 0 = 0` |
| Problem 212 | 211 | new | `exists_computable_lowerFreq_eq` | `Frequencies.ExactFrequencies` | |
| Problem 213 | 211 | new | `exists_computable_lowerFreqPart_le` | `Frequencies.PartialSequences` | |

## Deviations from the printed statements

* **`KR` representation.** A decision machine is an enumerable, prefix-closed, `=`-`≍`-regular
  relation `rel p x` containing `(p, [])`, rather than a `BitStream`-valued function as for `KMOf`.
* **Uniform theorems.** Theorems 128 and 129 are stated once for all classes
  (`∀ α β`, `∀ α β γ`) instead of one theorem per class.
* **Relativized definitions.** The relativized decision, monotone and a priori complexities in
  `OracleDefs` duplicate the unrelativized definitions with `PointToSet.IsREIn` in place of
  `IsRE`. The relativized a priori complexity uses `PointToSet.IsLowerSemicomputableIn` (rational
  pairs), while the unrelativized `KA` uses `IsLSC` (dyadic approximations).
* **Limits.** Theorem 131 uses `⨅` (the sequence is non-increasing); Theorem 132 uses
  `Filter.limsup` in `ℕ∞`. Problems 210 and 211 use the real `Filter.liminf`: Problem 210 relies on
  the junk value `0` for infinite `liminf`s, and Problem 211 adds boundedness to its conclusion.
* **Problem 204 (missing part).** The book first asserts that `(A, x) ↦ K^A(x)` can be defined
  uniformly in `A`, up to `O(1)`, and then gives the limit formula. Lean states only the limit
  identity for a fixed oracle `A` and an arbitrary optimal `A`-decompressor, with a constant `c`
  chosen after `A`. The uniform definition is not formalized.
* **Problem 210 (missing part).** The book asserts that the `liminf` of a computable sequence of
  rationals is `0'`-lower-semicomputable and that the `0'`-algorithm is found effectively from an
  algorithm for the sequence. Lean states only the first claim; the effective passage from one
  algorithm to the other is not formalized.
* **Hypotheses of Problem 205.** The hypothesis is two-sided (`= + O(1)`), as printed.
* **Problem 203 (weaker).** The book asks for a decompressor that is optimal on every `f ∈ F`.
  `funComplexity` is defined on finite functions only, so `IsOptimalFunDecompressor` demands
  optimality only on finite functions; for infinite `f` nothing is stated.
* **Upper semicomputability.** Theorem 127 (k), (l) use the `ℕ∞`-valued `IsUpperSemicomputable` of
  `Foundation.EffectiveNotions`.
* **Problem 197 (c) (weaker).** The book states (c) for every `=`-`≍`-regular relation. Lean
  (`exists_decisionDecompressor_of_isDescriptionMode_eq_compat`) assumes the relation is
  enumerable, which is the case used in Theorem 128. The non-enumerable case, where the prefix
  closure is a chain defining a continuous map that is not computable, is not stated. Parts (a)
  and (b) are stated for arbitrary regular relations.
* **Problems 198 (a), 198 (b).** Stated for enumerable relations, and "define" is read as
  existence of an optimal machine (up to a constant factor for the a priori version).

## Modules

| Module | Contents |
|---|---|
| `GeneralScheme.Regular` | `StrRel`, α-β and `(α,β)\|γ` description modes, bridges to consistent relations |
| `GeneralScheme.Decision` | `DecisionDecompressor`, `KROf`, `KRSeq`, `ContDecisionMap`, `bitwiseKR`, `programKR`, `programKP`, `KROf_mono_of_prefix` |
| `GeneralScheme.DecisionBasic` | Problem 192, `KR ≤ l + O(1)`, Theorem 127 (a)–(f) |
| `GeneralScheme.DecisionMinimality` | aggregator of the two modules below |
| `GeneralScheme.DecisionMinimality.MapsAndPrefixFreeSets` | Theorem 127 (g)–(k) |
| `GeneralScheme.DecisionMinimality.Minimality` | Theorem 127 (l), (m), Problem 193 |
| `GeneralScheme.DecisionVariants` | Problems 194–196 |
| `GeneralScheme.Comparing` | aggregator of the two modules below |
| `GeneralScheme.Comparing.RegularRelations` | Problem 197 (a)–(c), Theorem 128 existence and `C` |
| `GeneralScheme.Comparing.OptimalModes` | Theorem 128 for `K`, `KM`, `KR`, pentagon bounds |
| `GeneralScheme.Pairs` | Problems 198 (a), (b), (c), 199 |
| `GeneralScheme.Conditional` | Theorem 129 / Problem 200, notation bridges, Problems 201, 202 |
| `GeneralScheme.Numberings` | Problem 203, Theorem 130, Schnorr complexity |
| `GeneralScheme.OracleDefs` | aggregator of the two modules below |
| `GeneralScheme.OracleDefs.MonotoneDecompressors` | `jumpSet`, `charSeq`, relativized `KR`, `KM`, `KA`, relativized existence of optimal conditional, decision and monotone decompressors |
| `GeneralScheme.OracleDefs.MaximalSemimeasure` | `exists_isMaximalContinuousSemimeasureIn` |
| `GeneralScheme.Relativized` | aggregator of the two modules below |
| `GeneralScheme.Relativized.ProblemOracleLimit` | Problem 204, `C^A ≤ C` |
| `GeneralScheme.Relativized.DecidableOracle` | `C` is `0'`-computable, Problem 205 (×4) |
| `GeneralScheme.SetConditions` | `C(x ‖ A)` and prefix variants, Problem 206, basic facts |
| `GeneralScheme.LargeConditionsPlain` | aggregator of the two modules below |
| `GeneralScheme.LargeConditionsPlain.PlainJumpLimit` | Theorem 131 and its lemmas, the lemma of Theorem 132 |
| `GeneralScheme.LargeConditionsPlain.LimsupJump` | Theorem 132 |
| `GeneralScheme.LargeConditionsPrefix` | Theorems 133, 134, `K(x ‖ A)` facts, Problem 208 |
| `GeneralScheme.Enumeration` | `KE`, `m(S)`, Problem 209 |
| `GeneralScheme.Frequencies` | aggregator of the four modules below |
| `GeneralScheme.Frequencies.LowerFrequency` | `lowerFreq` and its definitions, partial sums, Theorem 135, Problem 210 |
| `GeneralScheme.Frequencies.MaximalFrequency` | Theorem 136, Problem 211, the two corollaries |
| `GeneralScheme.Frequencies.ExactFrequencies` | Problem 212 |
| `GeneralScheme.Frequencies.PartialSequences` | Problem 213 |

Import graph inside the chapter:
`Regular → Decision → {DecisionBasic, OracleDefs.MonotoneDecompressors, Enumeration}`;
`DecisionBasic → {DecisionMinimality.*, DecisionVariants, Comparing.RegularRelations, Conditional,
Pairs}`; `Comparing.RegularRelations → Comparing.OptimalModes`;
`OracleDefs.MonotoneDecompressors → OracleDefs.MaximalSemimeasure`;
`OracleDefs → {Relativized.* (also ← Conditional), SetConditions, Frequencies.LowerFrequency}`;
`Frequencies.LowerFrequency → Frequencies.MaximalFrequency → {Frequencies.ExactFrequencies,
Frequencies.PartialSequences}`;
`SetConditions → {LargeConditionsPlain.PlainJumpLimit → LargeConditionsPlain.LimsupJump,
LargeConditionsPrefix}`; `Regular → Numberings`.
Notable external imports: `LargeConditionsPlain.PlainJumpLimit` imports
`AlgorithmicStatistics.StrongModels.LemmaOmpBlockCounting` (for `exists_condK_ge_of_finset_card_pow`),
and `LargeConditionsPrefix` imports `Mathlib.MeasureTheory.Integral.Lebesgue.{Add,Countable}`
(Fatou's lemma).

## Reuse map

| Library declaration | Used for |
|---|---|
| `condK`, `plainK`, `isOptimalConditional` (`Core.Basic`), `cVal` (`Foundation.EffectiveNotions`) | plain and conditional `C` |
| `KP`, `KPPlain`, `IsOptimalPrefixConditional`, `IsPrefixDecompressor`, `IsPrefixMachine` (`Prefix.*`) | prefix `K` |
| `IsPrefixStableFun`, `IsPrefixStableDecompressor` (`Prefix.StableDecompressors`, Theorem 48) | Theorem 127 (h), Problem 197 (a), `K(x ‖ A)` |
| `KMOf`, `IsOptimalMonotoneDecompressor`, `monotoneProduces`, `IsComputableStreamMap`, `streamLowerGraph`, `IsContinuousStreamMap`, `IsStreamLowerGraph` (`MonotoneComplexity.*`) | `KM`, Theorem 127 (d), (e), (g) |
| `IsConsistentStreamRelation`, `streamGapFill_isStreamLowerGraph`, `consistentRelationKMOf`, `IsOptimalConsistentRelation`, `exists_const_KMOf_consistentRelationKMOf_equiv` (Problem 137) | Problem 197 (b), Theorem 128 `≍`-`≍` |
| `KA`, `IsContinuousTreeSemimeasure` (`MonotoneComplexity.APrioriComplexity`, `TreeSemimeasure`) | Theorem 127 (m), Problem 205 (`KA`) |
| `IsRE`, `IsEnumerableSet`, `IsDecidableSet`, `IsUpperSemicomputable` (`Foundation.*`) | enumerability, Theorem 127 (k), (l), Problem 205 |
| `IsPrefixFree` (`Prefix.Basic`) | Theorem 127 (j), (l) |
| `CantorSeq`, `cantorPrefix`, `cantorPrefix_mono`, `uniformMeasure` (`AlgorithmicRandomness.*`) | sequences, Problem 209 |
| `IsDecompressorIn`, `IsOptimalConditionalIn`, `charOracle`, `haltingOracle` (`Foundation.EffectiveNotions`) | `C^A`, `C^{0'}` |
| `PointToSet.IsREIn`, `PointToSet.IsLowerSemicomputableIn`, `PointToSet.IsOptimalOraclePrefix`, `exists_optimalOraclePrefix` (`Oracle.*`) | relativized enumerability, `K^A`, `K^{0'}`, `0'`-lsc |
| `Nat.Partrec.Code`, `Denumerable.ofNat Code`, as in `programComplexity` (Exercise 28) | Problems 195, 196, 206 |
| Theorem 8, Theorem 62, Theorem 80 declarations | §6.2 classification (existing) |
