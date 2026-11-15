# Formalization notes: SUV Chapters 8 and 9

Shen, Uspensky, Vereshchagin, *Kolmogorov Complexity and Algorithmic Randomness* (AMS 2017):
Chapter 8 "Some applications" (printed pp. 233-260) and Chapter 9 "Frequency and game approaches to
randomness" (printed pp. 261-312).

## 1. Overview

Both chapters are formalized completely, including the numbered theorems, the problems, the local
lemmas of the proofs, and the results the book quotes from the literature without proof.  There is
no `sorry` under `KolmogorovMathlib/Complexity/Applications` or
`KolmogorovMathlib/AlgorithmicRandomness/FrequencyGames`, and every theorem there depends only on
the axioms `propext`, `Classical.choice` and `Quot.sound`.

* Chapter 8 lives in `KolmogorovMathlib/Complexity/Applications/` (namespace
  `Kolmogorov.Applications`), imported by the aggregator `KolmogorovMathlib/Complexity/Applications.lean`.
* Chapter 9 lives in `KolmogorovMathlib/AlgorithmicRandomness/FrequencyGames/` (namespace
  `Kolmogorov.FrequencyGames`), imported by the aggregator
  `KolmogorovMathlib/AlgorithmicRandomness/FrequencyGames.lean`.

Where the printed statement is false, ambiguous or implicitly restricted, the Lean statement is the
nearest true one; all such differences are listed in section 5.  The `LibraryAPI` file of each
directory only collects the imports of the library API the chapter builds on.

Most of the larger modules are aggregators: a file `X.lean` that only imports topical submodules
`X/*.lean` (for example `NonMonotone.lean` imports `NonMonotone/KLRules.lean`,
`NonMonotone/MuchnikTheorem.lean`, and so on).  The tables below name the submodule that contains
each declaration, written `X.Y` for `X/Y.lean`; a module without a dot is a single file.  The
declarations keep their namespaces (`Kolmogorov.Applications`, `Kolmogorov.FrequencyGames`).

## 2. Modules

Chapter 8:

| Module | Sections | Printed pp. |
| --- | --- | --- |
| `Primes` | 8.1 | 233 |
| `TapeMachine` | 8.2 (model, crossing sequences) | 233-235 |
| `CrossingSequences` (aggregator) | 8.2 (complexity bounds) | 234-235 |
| `CrossingSequences.CrossingSequenceBound` | 8.2 (the crossing-sequence inequality) | 234 |
| `CrossingSequences.DuplicationLowerBound` | 8.2 (Theorems 152, 153, Problem 242) | 234-235 |
| `MultiheadAutomata` (aggregator) | 8.3 | 236-238 |
| `MultiheadAutomata.AutomatonDefs` | 8.3 (model, `L_m`, recognizability) | 236-237 |
| `MultiheadAutomata.HeadHierarchy` | 8.3 (non-recognizability, Theorem 154) | 236-238 |
| `LawsOfLargeNumbers` (aggregator) | 8.4 | 238-241 |
| `LawsOfLargeNumbers.PrefixFrequency` | 8.4 (Theorem 155, entropy expansion, first estimate) | 238-240 |
| `LawsOfLargeNumbers.IteratedLogarithm` | 8.4 (Theorem 156) | 239-241 |
| `LawsOfLargeNumbers.KMUpperBound` | 8.4 (Problem 243) | 241 |
| `ForbiddenSubstrings` (aggregator) | 8.5.1 (combinatorics, Miller) | 241-244 |
| `ForbiddenSubstrings.BiinfiniteSequences` | 8.5.1 (budgets, compactness, Theorem 159, Problem 247) | 241-244 |
| `ForbiddenSubstrings.EmergencyLevel` | 8.5.1 (Miller's proof, Theorem 157) | 241-244 |
| `ForbiddenSubstrings.ComputableAvoidance` | 8.5.1 (Problem 248, Makarychev) | 244 |
| `ComplexSubstrings` (aggregator) | 8.5.1 (complexity) | 241-242 |
| `ComplexSubstrings.LevinLemma` | 8.5.1 (Theorem 158, Problems 244, 245) | 241-242 |
| `ComplexSubstrings.ComplexityProfile` | 8.5.1 (Problem 246) | 242 |
| `LovaszLocalLemma` | 8.5.2, 8.5.3 | 244-248 |
| `ForbiddenSubsequences` (aggregator) | 8.5.3, 8.5.4 | 248-250 |
| `ForbiddenSubsequences.ValidAssignments` | 8.5.3 (Problem 251), 8.5.4 (Muchnik-Semenov count) | 248-250 |
| `ForbiddenSubsequences.RestrictionBounds` | 8.5.4 (restrictions, Theorem 161) | 249 |
| `ComplexSubsequences` (aggregator) | 8.5.5 | 250-251 |
| `ComplexSubsequences.SetPairComplexity` | 8.5.5 (Theorem 162, corollaries) | 251 |
| `ComplexSubsequences.MartinLofRandomFailure` | 8.5.5 (random sequences fail it) | 251 |
| `MoserTardos` (aggregator) | 8.5.6 | 251-255 |
| `MoserTardos.Algorithm` | 8.5.6 (algorithm, correctness, reconstruction) | 252-253 |
| `MoserTardos.SuccessProbability` | 8.5.6 (counting, Theorem 163, satisfiability) | 253-255 |
| `LoomisWhitney` | 8.6 | 255-258 |
| `BesicovitchDistance` | 8.7 (definitions, the shift) | 258 |
| `LipschitzBesicovitch` | 8.7 | 258-260 |

Chapter 9:

| Module | Sections | Printed pp. |
| --- | --- | --- |
| `Selection` | 9.1, 9.2 | 261-264 |
| `MisesChurch` (aggregator) | 9.3 | 264-267 |
| `MisesChurch.Defs` | 9.3 (definitions, Theorem 167, not computable) | 264-266 |
| `MisesChurch.NormalSequences` | 9.3 (Theorem 168, Problem 254) | 264-265 |
| `MisesChurch.AlignedNormality` | 9.3 (Problem 255) | 265 |
| `MisesChurch.NormalInBase` | 9.3 (Problems 256-258, bases) | 265 |
| `MisesChurch.Champernowne` | 9.3 (Problem 259, rational multiples) | 265-266 |
| `MisesChurch.ComputableNormal` | 9.3 (Problem 260) | 266 |
| `MisesChurch.PredictionAndBets` | 9.3 (Theorems 169-171) | 266-267 |
| `VilleExample` (aggregator) | 9.4 | 267-270 |
| `VilleExample.CountableFamilies` | 9.4 (one rule, `m` rules, countably many) | 268-269 |
| `VilleExample.MisesChurchExample` | 9.4 (Theorem 172) | 269 |
| `VilleExample.LogarithmicComplexity` | 9.4 (Theorem 173) | 270 |
| `VilleExample.EffectivelyNullSet` | 9.4 (Problems 261, 262, Theorem 174) | 269-270 |
| `Martingale` (aggregator) | 9.5 | 270-275 |
| `Martingale.Martingales` | 9.5 (definitions, Theorems 175-178, stopped capital) | 270-274 |
| `Martingale.DoobTheorem` | 9.5 (Doob, Theorems 179, 180) | 273-275 |
| `MartingaleProbability` | 9.6 | 275-277 |
| `LowerSemicomputable` (aggregator) | 9.7 | 277-279 |
| `LowerSemicomputable.Theorem181` | 9.7 (definitions, Theorem 181) | 277-278 |
| `LowerSemicomputable.RandomnessTests` | 9.5 (Problem 264), 9.7 (ML-randomness, largest supermartingale) | 272, 278-279 |
| `LowerSemicomputable.ComputableMartingales` | 9.7 (Problem 265) | 278 |
| `ComputableMartingale` (aggregator) | 9.8 | 279-282 |
| `ComputableMartingale.RandomnessBasics` | 9.8 (definition, Problem 266, Theorem 182(a)) | 279-280 |
| `ComputableMartingale.LogComplexityConstruction` | 9.8 (Theorem 182(b), log complexity) | 279-280 |
| `ComputableMartingale.MartinLofSeparation` | 9.8 (Theorem 182(b) separation, (c)) | 279-280 |
| `ComputableMartingale.MisesChurchSeparation` | 9.8 (Theorem 182(d)) | 280 |
| `ComputableMartingale.ZerosDominateWin` | 9.8 (Problem 267) | 281 |
| `ComputableMartingale.BoundedConditionalComplexity` | 9.8 (Problem 268) | 282 |
| `ComputableMartingale.UniversalComplexityBound` | 9.8 (one `ω` for all `f`) | 282 |
| `ComputableMartingale.ConditionalMeasures` | 9.8 (Problem 269) | 282 |
| `SchnorrKurtz` (aggregator) | 9.9 | 282-284 |
| `SchnorrKurtz.Defs` | 9.9 (definitions) | 282-284 |
| `SchnorrKurtz.SchnorrSeries` | 9.9 (Problem 90 of Section 3.4) | 282 |
| `SchnorrKurtz.SchnorrMartingaleGrowth` | 9.9 (Theorem 183, Problem 270) | 282-283 |
| `SchnorrKurtz.SchnorrNotComputable` | 9.9 (Problem 271) | 284 |
| `SchnorrKurtz.KurtzMartingales` | 9.9 (Problem 272) | 284 |
| `SchnorrKurtz.GrowthMartingales` | 9.9 (Theorem 183, from non-randomness to a growth martingale) | 282-283 |
| `SchnorrKurtz.RandomnessHierarchy` | 9.9 (ML ⇒ Schnorr ⇒ Kurtz, Problem 92) | 282-284, 310 |
| `Gales` (aggregator) | 9.10 | 284-287 |
| `Gales.GalesAndNullSets` | 9.10 (definitions, Theorem 184) | 285 |
| `Gales.LowerSemicomputableGales` | 9.10 (Theorem 185, effective `α`-null not reached) | 286 |
| `Gales.EffectiveDimensionViaGales` | 9.10 (Theorems 186, 187, Theorem 120 through `KA`) | 286-287 |
| `PartialRules` (aggregator) | 9.11 | 287-290 |
| `PartialRules.MisesChurchDaley` | 9.11 (definition, Daley ⇒ Church, Problem 273) | 287 |
| `PartialRules.ComplexityLowerBound` | 9.11 (Theorem 188) | 287-289 |
| `PartialRules.PartialMartingales` | 9.11 (Theorems 189, 190, partial martingales) | 289-290 |
| `NonMonotone` (aggregator) | 9.12, 9.13 | 290-296, 309 |
| `NonMonotone.KLRules` | 9.12 (rules, Theorems 191, 192(a)) | 291-292 |
| `NonMonotone.MartinLofImpliesStochastic` | 9.12 (Theorem 192(b)) | 292 |
| `NonMonotone.BoundedBetStrategy` | 9.12 (Lemma of 9.12) | 294 |
| `NonMonotone.MuchnikCoding`, `NonMonotone.MuchnikStages`, `NonMonotone.MuchnikWitnesses` | 9.12 (auxiliary constructions of Theorem 193) | 293-295 |
| `NonMonotone.MuchnikTheorem` | 9.12 (Theorem 193) | 293 |
| `NonMonotone.ChurchDaleySeparation` | 9.12 (Theorems 194, 195), Problem 279 | 295-296, 309 |
| `NonMonotone.KLBetting` | 9.13 (KL randomness, definitions) | 309 |
| `NonMonotone.KLTotalMartingales` | 9.13 (KL randomness through total martingales, open question) | 309 |
| `ChangeOfMeasure` (aggregator) | 9.13 | 296-309 |
| `ChangeOfMeasure.IndependentTrials` | 9.13 (independent trials, Example 1, Problem 274) | 296-297 |
| `ChangeOfMeasure.SeparatedCriterion` | 9.13 (Problem 275, Theorem 196(a)) | 297 |
| `ChangeOfMeasure.VovkDichotomy` | 9.13 (Theorems 196(b), 197, Problems 276, 277) | 297-301 |
| `ChangeOfMeasure.BookmakerGame` | 9.13 (Problem 278, two bookmakers) | 301 |
| `ChangeOfMeasure.FrequencyDeviation` | 9.13 (Theorems 198-200) | 302-304 |
| `ChangeOfMeasure.VanLambalgen` | 9.13 (Theorem 201) | 305 |
| `ChangeOfMeasure.KLRandomness` | 9.13 (Theorem 202) | 305 |
| `ChangeOfMeasure.Separations` | 9.13 (Theorem 203, Problem 280) | 307-309 |
| `RandomnessRelations` | Figure 3 | 310 |

Import structure (an arrow means "imports"): `ForbiddenSubsequences → LovaszLocalLemma`;
`CrossingSequences → TapeMachine`; `ComplexSubstrings → ForbiddenSubstrings`;
`ComplexSubsequences → ForbiddenSubsequences`; `LipschitzBesicovitch → BesicovitchDistance`.  In
Chapter 9: `VilleExample → MisesChurch → Selection`; `{LowerSemicomputable, MartingaleProbability} →
Martingale`; `ComputableMartingale → {LowerSemicomputable, VilleExample}`;
`SchnorrKurtz → ComputableMartingale`; `Gales → LowerSemicomputable`;
`PartialRules → {VilleExample, ComputableMartingale}`;
`NonMonotone → PartialRules`; `ChangeOfMeasure → {NonMonotone, SchnorrKurtz}`;
`RandomnessRelations → ChangeOfMeasure`.  Between the chapters, `NonMonotone` imports
`LipschitzBesicovitch` and `Gales` imports `ComplexSubstrings`.  Inside an aggregator the
submodules form chains; for example `NonMonotone.MuchnikCoding →
NonMonotone.BoundedBetStrategy`, and `ForbiddenSubsequences.RestrictionBounds` imports
`LovaszLocalLemma`.

## 3. Status vocabulary

| Status | Meaning |
| --- | --- |
| proved | Proved in this development. |
| cited | Quoted by the book from the literature, without proof there; proved here. |
| existing | The content was already a library declaration, named in the notes. |
| definition | A definition (or structure) introduced for the chapter. |
| open | An open question of the book: only a `Prop` naming it, asserted by nothing. |
| omitted | No Lean statement; the reason is given. |

## 4. Item map

### 4.1 Chapter 8

Declarations are in `Kolmogorov.Applications`.

| Item | § | p. | Lean declaration | Module | Status | Notes |
| --- | --- | --- | --- | --- | --- | --- |
| Euclid's theorem | 8.1 | 233 | `infinite_setOf_prime'` | `Primes` | proved | Mathlib's `Nat.infinite_setOfPred_prime`. |
| Complexity core of 8.1 | 8.1 | 233 | `plainK_natBits_le_of_primeFactors` | `Primes` | proved | `C(x) = O(log log x)` for prime factors in a fixed finite set. |
| Footnote: `log p_n ≤ K(n) + O(1)` for infinitely many `n` | 8.1 | 233 | `frequently_logb_nth_prime_le` | `Primes` | cited | After Li-Vitányi. |
| Footnote: `∑ 1/p` diverges | 8.1 | 233 | `not_summable_inv_primes` | `Primes` | proved | Mathlib's `not_summable_one_div_on_primes`. |
| Model of Turing machines | 8.2 | 234 | `TuringMachine`, `TapeConfig`, `run`, `Duplicates`, `rightContents` | `TapeMachine` | definition | Two-way tape over `ℤ`, explicit blank, halting, stationary after halt. |
| Crossing sequences | 8.2 | 234 | `crossingSequence`, `crossingSteps` | `TapeMachine` | definition | |
| Sum of crossing counts `≤ t` | 8.2 | 235 | `sum_card_crossingSteps_le`, `exists_crossingSteps_short` | `TapeMachine` | proved | |
| Replay on the right of a border | 8.2 | 234 | `replayRight`, `run_right_eq_replayRight` | `TapeMachine` | proved | Core of Theorem 152. |
| Inequality `C(R) ≤ l(S) log m + 4 log t + c` | 8.2 | 234 | `rightComplexity_le_crossingSequence` | `CrossingSequences.CrossingSequenceBound` | proved | Quantified over the `b + 1` borders. |
| **Theorem 152** | 8.2 | 234 | `rightComplexity_le` | `CrossingSequences.DuplicationLowerBound` | proved | Head in the left zone, `b ≥ 1`; see section 5. |
| Problem 242 | 8.2 | 235 | `rightComplexity_le_two_mul` | `CrossingSequences.DuplicationLowerBound` | proved | Same adjustments. |
| **Theorem 153** | 8.2 | 235 | `exists_duplication_lower_bound` | `CrossingSequences.DuplicationLowerBound` | proved | `ε` depends on `M`, as in the book. `Duplicates` fixes the origin and trailing blanks of the output. |
| Model of `k`-head automata | 8.3 | 236 | `MultiheadAutomaton`, `Accepts`, `Recognizes` | `MultiheadAutomata.AutomatonDefs` | definition | End marker, one-way heads, at least one moves. |
| Termination of automata | 8.3 | 236 | `terminated_run` | `MultiheadAutomata.AutomatonDefs` | proved | |
| Languages `L_m` | 8.3 | 237 | `palindromeBlocks`, `blockWord` | `MultiheadAutomata.AutomatonDefs` | definition | |
| `L_m` recognizable for `m ≤ C(k, 2)` | 8.3 | 237 | `isRecognizedBy_palindromeBlocks` | `MultiheadAutomata.AutomatonDefs` | proved | `m ≥ 1`. |
| `L_m` not recognizable for `m > C(k, 2)` | 8.3 | 237 | `not_isRecognizedBy_palindromeBlocks` | `MultiheadAutomata.HeadHierarchy` | proved | |
| **Theorem 154** | 8.3 | 236 | `exists_language_isRecognizedBy_succ_not` | `MultiheadAutomata.HeadHierarchy` | proved | `k = 0` uses another language; see the docstring. |
| SLLN for ML-random sequences | 8.4 | 238 | `tendsto_freqOne_of_isMartinLofRandom_uniform` | library (Theorems 32-33) | existing | |
| **Theorem 155** | 8.4 | 239 | `tendsto_prefixFreq_of_plainK_isLittleO` | `LawsOfLargeNumbers.PrefixFrequency` | proved | `n + o(n)` through `IsLittleO`. |
| Taylor expansion of entropy (step of the proof of Theorem 156) | 8.4 | 239-240 | `binaryEntropy_half_add_isLittleO` | `LawsOfLargeNumbers.PrefixFrequency` | proved | Not part of Theorem 155; used by Theorem 156 and Problem 243. |
| Bound `O(√(log n / n))` (first estimate of the proof of Theorem 156) | 8.4 | 240 | `prefixFreq_sub_half_isBigO` | `LawsOfLargeNumbers.PrefixFrequency` | proved | |
| **Theorem 156** | 8.4 | 239 | `abs_prefixFreq_sub_half_le` | `LawsOfLargeNumbers.IteratedLogarithm` | proved | `ln ln n` as in the book. |
| Problem 243 | 8.4 | 241 | `abs_prefixFreq_sub_half_le_of_KM` | `LawsOfLargeNumbers.KMUpperBound` | proved | |
| **Theorem 157** | 8.5.1 | 241 | `exists_avoidsLong` | `ForbiddenSubstrings.EmergencyLevel` | proved | Exact budget `IsAtMostForbidden`; Miller's proof. |
| Compactness | 8.5.1 | 243, 247 | `exists_seq_avoiding_iff_arbitrarily_long` | `ForbiddenSubstrings.BiinfiniteSequences` | proved | |
| Budget in Theorem 158 | 8.5.1 | 241 | `ncard_plainK_lt_lt` | `ComplexSubstrings.LevinLemma` | proved | Count below `2^{αn+1}`, for optimal `V`; see section 5. |
| Block step, Theorem 71 | 8.5.1 | 242 | `exists_blockLength_KP_increase` | `ComplexSubstrings.LevinLemma` | proved | From the library's `exists_extension_KP_ge`. |
| **Theorem 158** | 8.5.1 | 241 | `exists_forall_substring_le_plainK` | `ComplexSubstrings.LevinLemma` | proved | |
| Problem 244 | 8.5.1 | 241 | `exists_lt_one_infinite_simple_substrings` | `ComplexSubstrings.LevinLemma` | proved | |
| Problem 245 | 8.5.1 | 242 | `exists_blockLength_plainK_increase` | `ComplexSubstrings.LevinLemma` | proved | Weaker than the book: only the first block step; see section 5. |
| Problem 246 | 8.5.1 | 242 | `exists_seq_KP_profile` | `ComplexSubstrings.ComplexityProfile` | proved | Uniformly large-increment repair of Problem 47; see section 5. |
| **Theorem 159** | 8.5.1 | 243 | `exists_decidable_counterexample` | `ForbiddenSubstrings.BiinfiniteSequences` | proved | Strict budget `IsLessForbidden`, as in the statement. |
| Problem 247 | 8.5.1 | 243 | `exists_biinfinite_avoiding` | `ForbiddenSubstrings.BiinfiniteSequences` | proved | |
| Miller's proof of Theorem 157: emergency level | 8.5.1 | 243 | `emergency` | `ForbiddenSubstrings.EmergencyLevel` | definition | Possible occurrences are explicit overlaps. |
| Miller's proof of Theorem 157: initial value | 8.5.1 | 244 | `emergency_nil` | `ForbiddenSubstrings.EmergencyLevel` | proved | |
| Miller's proof of Theorem 157: forbidden suffix | 8.5.1 | 244 | `one_le_emergency_of_suffix` | `ForbiddenSubstrings.EmergencyLevel` | proved | Suffix only; see section 5. |
| Miller's proof of Theorem 157: identity | 8.5.1 | 244 | `emergency_append_add` | `ForbiddenSubstrings.EmergencyLevel` | proved | In `ℝ≥0∞`, no subtraction. |
| Miller's proof of Theorem 157: invariant | 8.5.1 | 244 | `exists_bit_emergency_lt_one`, `exists_avoiding_of_tsum_lt` | `ForbiddenSubstrings.EmergencyLevel` | proved | |
| Problem 248 | 8.5.1 | 244 | `exists_computable_avoidsLong` | `ForbiddenSubstrings.ComputableAvoidance` | proved | "short" read as "long"; see section 5. |
| Makarychev's bi-infinite version (unnumbered, after Problem 248) | 8.5.1 | 244 | `exists_computable_biinfinite_avoidsLong` | `ForbiddenSubstrings.ComputableAvoidance` | cited | Only sketched in the book. |
| **Theorem 160 (LLL)** | 8.5.2 | 246 | `lovasz_local_lemma` | `LovaszLocalLemma` | proved | Independence from the tuple, through `ProbabilityTheory.Indep`. |
| LLL, statement (1) of the proof | 8.5.2 | 246 | `lovasz_conditional_bound` | `LovaszLocalLemma` | proved | Division-free. |
| Problem 249 | 8.5.2 | 247 | `exists_isValidFilling_of_four_div_twentySeven` | `LovaszLocalLemma` | proved | `0 < N` explicit. |
| Problem 250 | 8.5.2 | 247 | `exists_isValidFilling_of_lt_quarter` | `LovaszLocalLemma` | proved | `0 < N` explicit. |
| Inequality of the LLL proof of Theorem 157 (not part of Problem 251) | 8.5.3 | 248 | `exists_threshold_lll_forbidden` | `LovaszLocalLemma` | proved | Finite ranges of `k`. |
| Problem 251 | 8.5.3 | 248 | `exists_filling_avoiding_rectangles` | `ForbiddenSubsequences.ValidAssignments` | proved | Forbidden sets per rectangle. |
| Restrictions | 8.5.4 | 249 | `Restriction`, `restrictBits`, `Restriction.Forbids` | `ForbiddenSubsequences.RestrictionBounds` | definition | `\|X\| = \|F\|` is a field. |
| **Theorem 161** | 8.5.4 | 249 | `exists_not_forbidden` | `ForbiddenSubsequences.RestrictionBounds` | proved | Finiteness of the families explicit; see section 5. |
| Inequality of its proof | 8.5.4 | 249 | `exists_threshold_restrictions` | `ForbiddenSubsequences.RestrictionBounds` | proved | |
| Muchnik-Semenov | 8.5.4 | 250 | `validCount`, `exists_threshold_validCount` | `ForbiddenSubsequences.ValidAssignments` | proved | `c(∅) = 1` requires that no restriction is empty. |
| **Theorem 162** | 8.5.5 | 251 | `exists_max_setPairComplexity_ge` | `ComplexSubsequences.SetPairComplexity` | proved | Coding of `F` explicit. |
| First corollary | 8.5.5 | 251 | `exists_condK_restrictBits_ge` | `ComplexSubsequences.SetPairComplexity` | proved | |
| Second corollary | 8.5.5 | 251 | `condK_restrictBits_ge_of_forall_le` | `ComplexSubsequences.SetPairComplexity` | proved | For `\|F\| ≥ N`; see section 5. |
| Random sequences fail it | 8.5.5 | 251 | `not_exists_max_setPairComplexity_ge_of_isMartinLofRandom` | `ComplexSubsequences.MartinLofRandomFailure` | proved | |
| Random `K(F, ω(F)) ≥ \|F\| − c` (Problem 145) | 8.5.5 | 251 | none | n/a | omitted | An item of another chapter, cited for comparison only. |
| CNF, neighbours, algorithm | 8.5.6 | 252-253 | `UniformCNF`, `UniformCNF.step`, `UniformCNF.run`, `UniformCNF.State` | `MoserTardos.Algorithm` | definition | Explicit stack machine for `Fix`. |
| Correctness of `Fix` | 8.5.6 | 253 | `satisfies_of_isHalted` | `MoserTardos.Algorithm` | proved | `0 < m`. |
| Reconstruction of random bits | 8.5.6 | 253 | `random_bits_determined` | `MoserTardos.Algorithm` | proved | |
| Bound on the number of calls | 8.5.6 | 255 | `card_tapes_many_calls_le` | `MoserTardos.SuccessProbability` | proved | Exact count of tapes. |
| Time bound | 8.5.6 | 254 | `isHalted_run_of_calls_le` | `MoserTardos.SuccessProbability` | proved | `(N + 2)²` steps. |
| **Theorem 163** | 8.5.6 | 253 | `card_tapes_success` | `MoserTardos.SuccessProbability` | proved | Probability is a count over `n + (N + 1) m` bits; `0 < m` explicit. |
| Satisfiability | 8.5.6 | 252 | `exists_satisfies` | `MoserTardos.SuccessProbability` | proved | From `card_tapes_success`. |
| Amplification by repetition | 8.5.6 | 253 | none | n/a | omitted | Parenthetical; independent repetition is not modelled. |
| Triple inequality for `K` | 8.6 | 255 | `two_mul_KP_triple_le` | library (Problem 114) | existing | |
| **Theorem 164** | 8.6 | 256 | `sq_sum_mul_mul_le` | `LoomisWhitney` | proved | Cauchy-Schwarz proof. |
| Entropy proof of Theorem 164 | 8.6 | 257 | `two_mul_entropy_triple_le` | library | existing | The key inequality; the assembled proof is not repeated. |
| Problem 252, discrete | 8.6 | 257 | `sq_card_le_card_mul_card_mul_card` | `LoomisWhitney` | proved | Also the library's discrete Loomis-Whitney in `Entropy/Inequalities/Subtuples.lean`. |
| Problem 252, continuous | 8.6 | 257 | `sq_volume_le_volume_projections` | `LoomisWhitney` | proved | Compact bodies. |
| Distances, Lipschitz, transitive | 8.7 | 258 | `cantorDist`, `besicovitchDist`, `IsCantorLipschitz`, `IsTransitiveFor` | `BesicovitchDistance` | definition | |
| The shift is transitive | 8.7 | 258 | `isCantorTransitive_leftShift`, `isCantorLipschitz_leftShift` | `BesicovitchDistance` | proved | |
| **Theorem 165** | 8.7 | 259 | `not_isBesicovitchTransitive_of_isCantorLipschitz` | `LipschitzBesicovitch` | proved | |
| **Lemma 1** of 8.7 | 8.7 | 259 | `effectiveHausdorffDim_singleton_apply_le` | `LipschitzBesicovitch` | proved | |
| **Lemma 2** of 8.7 | 8.7 | 259 | `abs_effectiveHausdorffDim_sub_le` | `LipschitzBesicovitch` | proved | `ε ≤ 1/2`; see section 5. |
| Theorem 120 | 8.7 | 259 | `effectiveHausdorffDim_singleton_eq_liminf` | library | existing | |
| Relativized lemmas | 8.7 | 260 | `oraclePrefixDim`, `oraclePrefixDim_apply_le`, `abs_oraclePrefixDim_sub_le`, `oraclePrefixDim_extremes` | `LipschitzBesicovitch` | proved | Finite relative prefix complexity divided by length; no bridge to oracle-effective covers is formalized. |
| Lipschitz maps are oracle-computable | 8.7 | 260 | `exists_isComputableLipschitzIn_of_isCantorLipschitz` | `LipschitzBesicovitch` | proved | |

### 4.2 Chapter 9

Declarations are in `Kolmogorov.FrequencyGames`.

| Item | § | p. | Lean declaration | Module | Status | Notes |
| --- | --- | --- | --- | --- | --- | --- |
| Limit frequency, balanced | 9.1 | 261-262 | `HasLimitFreq`, `IsBalanced`, `FiniteOrFreq` | `Selection` | definition | The finite case is a separate branch. |
| Selection by a set | 9.2 | 262 | `selectedBits`, `selectStream`, `partialRuleSet` | `Selection` | definition | Output in the library's `BitStream`. |
| No Kollektiv for all `R` | 9.2 | 262 | `exists_rule_not_finiteOrFreq` | `Selection` | proved | |
| Countable family (Wald) | 9.2 | 262 | `ae_finiteOrFreq_of_countable` | `Selection` | proved | |
| **Theorem 166** | 9.2 | 263 | `measure_infinite_unbalanced_eq_zero` | `Selection` | proved | Outer measure; no measurability assumed. |
| **Lemma** of 9.2 | 9.2 | 263 | `measure_selectPreimage_eq_zero` | `Selection` | proved | |
| Preimage measure | 9.2 | 263 | `measure_selectPreimage_le`, `measure_selectPreimage_eq` | `Selection` | proved | |
| Problem 253 | 9.2 | 264 | `bernoulli_selectPreimage_eq` | `Selection` | proved | |
| Church-admissible, Mises-Church | 9.3 | 264 | `IsMisesChurchRandomAt`, `IsMisesChurchRandom` | `MisesChurch.Defs` | definition | Uses `IsDecidableSet`. |
| **Theorem 167** | 9.3 | 264 | `isMisesChurchRandom_of_isMartinLofRandom` | `MisesChurch.Defs` | proved | |
| Preimage of effective null | 9.3 | 264 | `isEffectivelyNull_selectPreimage` | `MisesChurch.Defs` | proved | |
| **Theorem 168** | 9.3 | 264 | `isNormal_of_isMisesChurchRandom` | `MisesChurch.NormalSequences` | proved | |
| Problem 254 | 9.3 | 264 | `isAlignedNormal_of_isMisesChurchRandom` | `MisesChurch.NormalSequences` | proved | |
| Problem 255 | 9.3 | 265 | `isNormal_iff_isAlignedNormal` | `MisesChurch.AlignedNormality` | proved | |
| Problem 256 | 9.3 | 265 | `isNormalInBase_iff_pow` | `MisesChurch.NormalInBase` | proved | `b ≥ 2`, `k ≥ 1`. |
| Problem 257 | 9.3 | 265 | `isNormal_iff_orbit_equidistributed` | `MisesChurch.NormalInBase` | proved | Half-open intervals. |
| Problem 258 | 9.3 | 265 | `isNormalInBase_mul`, `isNormalInBase_two_mul` | `MisesChurch.NormalInBase` | proved | Every base `b ≥ 2`, with `k ≠ 0`; the binary case is the specialization. |
| Division preserves normality (Wall) | 9.3 | 265 | `isNormalInBase_div_int`, `isNormalInBase_mul_rat` | `MisesChurch.NormalInBase`; `MisesChurch.Champernowne` | cited | Integer division and rational multiplication; nonzero factors. |
| Normality depends on the base | 9.3 | 265 | `exists_isNormalInBase_not_isNormalInBase` | `MisesChurch.NormalInBase` | cited | Some pair of bases, as asserted in the literature. |
| Problem 259 | 9.3 | 266 | `isNormal_champernowne` | `MisesChurch.Champernowne` | proved | |
| Problem 260 | 9.3 | 266 | `exists_computable_isAbsolutelyNormal` | `MisesChurch.ComputableNormal` | proved | |
| Mises-Church is not computable | 9.3 | 266 | `not_computable_of_isMisesChurchRandom` | `MisesChurch.Defs` | proved | |
| **Theorem 169** | 9.3 | 266 | `tendsto_correctPredictions_of_isMisesChurchRandom` | `MisesChurch.PredictionAndBets` | proved | |
| **Theorem 170** | 9.3 | 267 | `betGain_isLittleO_of_isMisesChurchRandom` | `MisesChurch.PredictionAndBets` | proved | Positive bet on `0`. |
| **Theorem 171** | 9.3 | 267 | `isMisesChurchRandom_of_selectStream` | `MisesChurch.PredictionAndBets` | proved | |
| One rule; `m` rules; countably many | 9.4 | 268-269 | `exists_alternating_selection`, `exists_finite_family_balanced`, `exists_countable_family_balanced` | `VilleExample.CountableFamilies` | proved | |
| **Theorem 172** | 9.4 | 269 | `exists_isMisesChurchRandom_zerosDominate` | `VilleExample.MisesChurchExample` | proved | |
| Strict version | 9.4 | 269 | `exists_isMisesChurchRandom_zerosStrictlyDominate` | `VilleExample.MisesChurchExample` | proved | First bit `0`; see section 5. |
| Problem 261 | 9.4 | 269 | `isEffectivelyNull_of_decidable_tree` | `VilleExample.EffectivelyNullSet` | proved | In the generality of its hint. |
| Problem 262 | 9.4 | 270 | `isEffectivelyNull_zerosDominate` | `VilleExample.EffectivelyNullSet` | proved | The `≥` version contains the `>` one. |
| **Theorem 173** | 9.4 | 270 | `exists_isMisesChurchRandom_plainK_log` | `VilleExample.LogarithmicComplexity` | proved | |
| **Theorem 174** | 9.4 | 270 | `exists_isMisesChurchRandom_not_isMartinLofRandom` | `VilleExample.EffectivelyNullSet` | proved | |
| Martingale, supermartingale | 9.5, 9.7 | 271, 274, 278 | `IsMartingale`, `IsFairCapital`, `IsSuperfairCapital` | `Martingale.Martingales` | definition | Product form; no ratio formed. |
| Wins, strongly wins, limit | 9.5 | 272-274 | `Wins`, `StronglyWins`, `HasFiniteLimit` | `Martingale.Martingales` | definition | |
| Uniform form of fairness | 9.5 | 271 | `isFairCapital_uniform_iff` | `Martingale.Martingales` | proved | From the library's `cantorMass_uniformMeasure`. |
| Measures as martingales | 9.5 | 271, 274 | `isMartingale_iff_exists_measure` | `Martingale.Martingales` | proved | |
| Problem 263 | 9.5 | 271 | `isMartingale_uniform_iff_exists_measure` | `Martingale.Martingales` | proved | |
| **Theorem 175** | 9.5 | 271 | `measure_exists_ge_le_of_isMartingale` | `Martingale.Martingales` | proved | |
| (1), p. 274, free capital | 9.5 | 274 | `measure_exists_ge_le`, `measure_exists_ge_le_of_superfair` | `Martingale.Martingales` | proved | Induction on the depth, general `π`. |
| Problem 264 | 9.5 | 272 | `isProbabilityBoundedRandomnessTest_sup` | `LowerSemicomputable.RandomnessTests` | proved | |
| **Theorem 176** | 9.5 | 272 | `exists_isMartingale_ge_of_isOpen` | `Martingale.Martingales` | proved | Hypothesis `≤ ε`; see section 5. |
| (2), p. 274 | 9.5 | 274 | `exists_isMartingale_ge_of_isOpen'` | `Martingale.Martingales` | proved | `π(U) > 0` explicit. |
| **Theorem 177(a)** | 9.5 | 273 | `measure_wins_eq_zero` | `Martingale.Martingales` | proved | General `π`. |
| **Theorem 177(b)** | 9.5 | 273 | `exists_isMartingale_stronglyWins_of_null` | `Martingale.Martingales` | proved | Strong form. |
| (3), p. 274 | 9.5 | 274 | `measure_eq_zero_iff_exists_wins` | `Martingale.Martingales` | proved | |
| **Theorem 178** | 9.5 | 273 | `exists_stronglyWins_of_wins` | `Martingale.Martingales` | proved | |
| Stopped capital | 9.5 | 273 | `stoppedCapital`, `IsFairCapital.stoppedCapital`, `le_stoppedCapital_of_prefix` | `Martingale.Martingales` | proved | Fairness for probability measures; see section 5. |
| Sharp integral criterion | 9.5 | 273 | `exists_martingale_of_integral_bound` | `Martingale.DoobTheorem` | cited | |
| Buy low, sell high | 9.5 | 274 | `exists_martingale_wins_of_oscillation` | `Martingale.DoobTheorem` | proved | |
| **Theorem 179 (Doob)** | 9.5 | 274 | `measure_not_hasFiniteLimit_eq_zero` | `Martingale.DoobTheorem` | proved | |
| Conditional probabilities | 9.5 | 275 | `condSecond`, `ae_exists_tendsto_condSecond` | `Martingale.DoobTheorem` | proved | |
| **Theorem 180** | 9.5 | 275 | `exists_forall_prefix_le_one` | `Martingale.DoobTheorem` | proved | For all `π`, through cylinders of positive mass. |
| SLLN through martingales | 9.6 | 276 | `isMartingale_bernoulliRatio`, `wins_bernoulliRatio_of_frequently_freq_gt`, `wins_bernoulliRatio_of_frequently_freq_lt` | `MartingaleProbability` | proved | |
| Market reading of randomness | 9.6 | 276-277 | none | n/a | omitted | No mathematical statement. |
| Lower semicomputable | 9.7 | 277 | `IsLowerSemicomputableOnStrings` | `LowerSemicomputable.Theorem181` | definition | Literally the book's, via `IsRE`. |
| Problem 265 | 9.7 | 278 | `isComputableOnStrings_of_isMartingale` | `LowerSemicomputable.ComputableMartingales` | proved | Positive cylinders; see section 5. |
| **Theorem 181(a)** | 9.7 | 278 | `isEffectivelyNull_wins` | `LowerSemicomputable.Theorem181` | proved | |
| **Theorem 181(b)** | 9.7 | 278 | `exists_lsc_stronglyWins_of_isEffectivelyNull` | `LowerSemicomputable.Theorem181` | proved | Strong form. |
| Strengthenings | 9.7 | 278 | `exists_lsc_stronglyWins_of_wins`, `isEffectivelyNull_wins_of_superfair` | `LowerSemicomputable.RandomnessTests`; `LowerSemicomputable.Theorem181` | proved | |
| ML-random through lsc martingales | 9.7 | 278 | `isMartinLofRandom_iff_forall_lsc_not_wins` | `LowerSemicomputable.RandomnessTests` | proved | |
| Largest supermartingale | 9.7 | 279 | `isLargest_universalRatio` | `LowerSemicomputable.RandomnessTests` | proved | Positive cylinders. |
| Levin-Schnorr, Theorem 91 | 9.7 | 279 | `isMartinLofRandom_iff_boundedAPrioriDeficiency` | library | existing | |
| Computably random | 9.8 | 279 | `IsComputablyRandom`, `IsComputableOnStrings` | `ComputableMartingale.RandomnessBasics`; `LowerSemicomputable.Theorem181` | definition | Hypotheses on `π` are in the theorems. |
| Problem 266(a), (b) | 9.8 | 279 | `isComputablyRandom_iff_ge_half`, `isComputablyRandom_iff_rational` | `ComputableMartingale.RandomnessBasics` | proved | |
| **Theorem 182(a)** | 9.8 | 279 | `isComputablyRandom_of_isMartinLofRandom` | `ComputableMartingale.RandomnessBasics` | proved | Null cylinders allowed. |
| **Theorem 182(b)** | 9.8 | 279 | `exists_isComputablyRandom_plainK_log`, `exists_isComputablyRandom_not_isMartinLofRandom` | `ComputableMartingale.LogComplexityConstruction`; `ComputableMartingale.MartinLofSeparation` | proved | General measure with positive cylinders. |
| Supporting facts of 182(b) | 9.8 | 280 | `exists_computable_seq_bounded`, `not_isComputablyRandom_of_computable`, `not_exists_largest_computable_capital` | `ComputableMartingale.RandomnessBasics` | proved | |
| **Theorem 182(c)** | 9.8 | 279 | `isMisesChurchRandom_of_isComputablyRandom` | `ComputableMartingale.MartinLofSeparation` | proved | |
| **Theorem 182(d)** | 9.8 | 280 | `exists_isMisesChurchRandom_not_isComputablyRandom` | `ComputableMartingale.MisesChurchSeparation` | proved | |
| Problem 267 | 9.8 | 281 | `exists_computable_wins_zerosDominate` | `ComputableMartingale.ZerosDominateWin` | proved | |
| Problem 268 | 9.8 | 282 | `exists_isComputablyRandom_condK_le` | `ComputableMartingale.BoundedConditionalComplexity` | proved | |
| One `ω` for all `f` | 9.8 | 282 | `exists_isComputablyRandom_condK_le_forall` | `ComputableMartingale.UniversalComplexityBound` | cited | |
| Problem 269 | 9.8 | 282 | `hasFiniteLimit_of_isComputablyRandom`, `exists_conditional_measure_of_isComputablyRandom` | `ComputableMartingale.ConditionalMeasures` | proved | Positive first projection. |
| Schnorr and Kurtz randomness | 9.9 (3.4) | 282-284 | `IsSchnorrNull`, `IsSchnorrRandom`, `IsKurtzNull`, `IsKurtzRandom` | `SchnorrKurtz.Defs` | definition | Kurtz uses the literal sum of finite cover masses; see section 5. |
| Problem 90 of Section 3.4 | 9.9 | 282 | `not_isSchnorrRandom_iff_exists_series` | `SchnorrKurtz.SchnorrSeries` | proved | |
| **Theorem 183** | 9.9 | 282 | `not_isSchnorrRandom_iff_exists_growth` | `SchnorrKurtz.SchnorrMartingaleGrowth` | proved | Positive cylinders, as in the book. |
| Computably random ⇒ Schnorr | 9.9 | 282 | `isSchnorrRandom_of_isComputablyRandom` | `SchnorrKurtz.SchnorrMartingaleGrowth` | proved | |
| Problem 270 | 9.9 | 283 | `isSchnorrRandom_iff_forall_computable_bound` | `SchnorrKurtz.SchnorrMartingaleGrowth` | proved | Positive cylinders added. |
| Problem 271 | 9.9 | 284 | `exists_isSchnorrRandom_not_isMisesChurchRandom`, `exists_isSchnorrRandom_not_isComputablyRandom` | `SchnorrKurtz.SchnorrNotComputable` | proved | |
| Problem 272 | 9.9 | 284 | `not_isKurtzRandom_iff_exists_growth` | `SchnorrKurtz.KurtzMartingales` | proved | |
| Schnorr ⇒ Kurtz, strict; Problem 92 | 9.9 | 284, 310 | `isKurtzRandom_of_isSchnorrRandom`, `exists_isKurtzRandom_not_isBalanced`, `isBalanced_of_isSchnorrRandom` | `SchnorrKurtz.RandomnessHierarchy` | proved | |
| ML ⇒ Schnorr | 9.9 | 282 | `isSchnorrRandom_of_isMartinLofRandom` | `SchnorrKurtz.RandomnessHierarchy` | proved | |
| Gales, supergales | 9.10 | 285 | `IsGale`, `IsSupergale` | `Gales.GalesAndNullSets` | definition | |
| Tax and measure readings | 9.10 | 285 | `isGale_taxed_iff`, `isGale_iff_exists_measure` | `Gales.GalesAndNullSets` | proved | |
| **Theorem 184** | 9.10 | 285 | `isAlphaNull_iff_exists_martingale`, `isAlphaNull_wins_of_isGale`, `exists_isGale_wins_of_isAlphaNull` | `Gales.GalesAndNullSets` | proved | Uses `IsAlphaNull`. |
| **Theorem 185** | 9.10 | 286 | `exists_lsc_isGale_wins_of_isEffectiveAlphaNull` | `Gales.LowerSemicomputableGales` | proved | `m(Λ) ≤ 1`. |
| **Theorem 186** | 9.10 | 286 | `isEffectiveAlphaNull_wins_of_lsc` | `Gales.EffectiveDimensionViaGales` | proved | Only `β > α`. |
| Effective `α`-null not reached | 9.10 | 286 | `exists_lsc_isGale_not_isEffectiveAlphaNull` | `Gales.LowerSemicomputableGales` | proved | Computable exponent in `(0,1)` and normalized capital. |
| **Theorem 187** | 9.10 | 286 | `effectiveHausdorffDim_eq_sInf_gale`, `effectiveHausdorffDim_eq_sInf_supergale` | `Gales.EffectiveDimensionViaGales` | proved | `α > 1` allowed; see section 5. |
| Theorem 120 through `KA` | 9.10 | 287 | `effectiveHausdorffDim_singleton_eq_liminf_KA` | `Gales.EffectiveDimensionViaGales` | proved | |
| Church-Daley rules | 9.11 | 287 | `IsMisesChurchDaleyRandomAt` (with `partialRuleSet` of `Selection`) | `PartialRules.MisesChurchDaley` | definition | Real partiality, hanging semantics. |
| Daley ⇒ Church | 9.11 | 287 | `IsMisesChurchDaleyRandomAt.isMisesChurchRandomAt` | `PartialRules.MisesChurchDaley` | proved | Given `IsDecidableSet`. |
| Problem 273 | 9.11 | 287 | `isMisesChurchDaleyRandom_of_selectStream` | `PartialRules.MisesChurchDaley` | proved | |
| **Theorem 188** | 9.11 | 287 | `not_exists_isMisesChurchDaleyRandom_plainK_log` | `PartialRules.ComplexityLowerBound` | proved | |
| **Theorem 189** | 9.11 | 289 | `exists_isMisesChurchDaleyRandom_plainK_le` | `PartialRules.PartialMartingales` | proved | |
| Partial martingales | 9.11 | 290 | `IsPartialMartingale`, `PartialWins`, `IsPartialComputablyRandom` | `PartialRules.PartialMartingales` | definition | |
| **Theorem 190(a), (b)** | 9.11 | 290 | `isMisesChurchDaleyRandom_of_isPartialComputablyRandom`, `exists_isPartialComputablyRandom_plainK_le` | `PartialRules.PartialMartingales` | proved | |
| Kolmogorov-Loveland rules | 9.12 | 291 | `KLRule`, `KLRule.revealed`, `KLRule.output`, `IsMisesKLRandomAt` | `NonMonotone.KLRules` | definition | No repeated query; choice before value. |
| Monotone rules are special | 9.12 | 292 | `KLRule.ofMonotone`, `KLRule.revealed_ofMonotone`, `KLRule.output_ofMonotone` | `NonMonotone.KLRules` | proved | |
| **Theorem 191** | 9.12 | 291 | `isMisesKLRandomAt_iff_total` | `NonMonotone.KLRules` | proved | |
| **Theorem 192(a)** | 9.12 | 292 | `IsMisesKLRandomAt.isMisesChurchDaleyRandomAt`, `IsMisesKLRandomAt.isMisesChurchRandomAt` | `NonMonotone.KLRules` | proved | All `p`. |
| **Theorem 192(b)** | 9.12 | 292 | `isMisesKLRandomAt_of_isMartinLofRandom_bernoulli`, `isMisesKLRandom_of_isMartinLofRandom` | `NonMonotone.MartinLofImpliesStochastic` | proved | |
| **Lemma** of 9.12 | 9.12 | 294 | `exists_bet_strategy_of_card_le` | `NonMonotone.BoundedBetStrategy` | proved | Positive bet on `1`. |
| Tangent-line remark on the Lemma | 9.12 | 294 | none | n/a | omitted | An alternative proof of a stated lemma. |
| **Theorem 193** | 9.12 | 293 | `not_isMisesKLRandom_of_plainK_lt` | `NonMonotone.MuchnikTheorem` | proved | |
| Infinitely many `n` (the strengthening in the remark after Theorem 193) | 9.12 | 293 | `not_isMisesKLRandom_of_frequently_plainK_lt` | `NonMonotone.MuchnikTheorem` | cited | A later strengthening. |
| **Theorem 194** | 9.12 | 295 | `not_isMisesChurchRandom_of_computable_bound` | `NonMonotone.ChurchDaleySeparation` | proved | Upper bound up to a constant. |
| **Theorem 195** | 9.12 | 296 | `exists_isMisesChurchDaleyRandom_not_isMisesKLRandom` | `NonMonotone.ChurchDaleySeparation` | proved | |
| Finite counterpart | 9.12 | 296 | none | n/a | omitted | Cited in the book; needs a notion of complexity of a rule. |
| Independent trials | 9.13 | 297 | `independentTrials`, `massR_independentTrials`, `isComputableMeasure_independentTrials`, `condOne_independentTrials` | `ChangeOfMeasure.IndependentTrials` | proved | |
| Example 1, Problem 274 | 9.13 | 296-297 | `firstTrialBiased`, `isMartinLofRandom_firstTrialBiased_iff` | `ChangeOfMeasure.IndependentTrials` | proved | |
| Problem 275 | 9.13 | 297 | `isComputablyRandom_firstTrialBiased_iff` | `ChangeOfMeasure.SeparatedCriterion` | proved | |
| **Theorem 196(a)** | 9.13 | 297 | `isMartinLofRandom_iff_of_summable` | `ChangeOfMeasure.SeparatedCriterion` | proved | |
| **Theorem 196(b)** | 9.13 | 297 | `not_isMartinLofRandom_and_of_not_summable` | `ChangeOfMeasure.VovkDichotomy` | proved | Derived from Theorem 197 without the separation hypothesis. |
| Problem 276(a), (b) | 9.13 | 299 | `kakutani_absolutelyContinuous`, `kakutani_mutuallySingular` | `ChangeOfMeasure.VovkDichotomy` | proved | |
| **Theorem 197** | 9.13 | 299 | `summable_sq_condOne_sub` | `ChangeOfMeasure.VovkDichotomy` | proved | From the library's `vovk_merging_summable`; separation not needed. |
| Problem 277 | 9.13 | 301 | `exists_measures_close_along_not_elsewhere` | `ChangeOfMeasure.VovkDichotomy` | proved | Weaker than the book: see section 5. |
| Problem 278 | 9.13 | 301 | `summable_sq_condOne_sub_of_isComputablyRandom` | `ChangeOfMeasure.BookmakerGame` | proved | Separation and positivity kept. |
| Two bookmakers | 9.13 | 301 | `bookmakerCapital`, `isMartingale_bookmakerCapital`, `wins_bookmaker_of_not_summable` | `ChangeOfMeasure.BookmakerGame` | proved | |
| **Theorem 198** | 9.13 | 302 | `measure_abs_ones_sub_condSum_gt_le` | `ChangeOfMeasure.FrequencyDeviation` | proved | `0 ≤ d`, `0 < n` explicit. |
| **Theorem 199** | 9.13 | 303 | `ae_tendsto_ones_sub_condSum` | `ChangeOfMeasure.FrequencyDeviation` | proved | |
| **Theorem 200** | 9.13 | 304 | `measure_selected_abs_sub_gt_le` | `ChangeOfMeasure.FrequencyDeviation` | proved | Indexing corrected; see section 5. |
| Example after Theorem 200 | 9.13 | 304 | none | n/a | omitted | An instance of Theorem 200. |
| **Theorem 201** | 9.13 | 305 | `isMisesChurchDaleyRandomAt_of_isMartinLofRandom` | `ChangeOfMeasure.VanLambalgen` | proved | |
| **Theorem 202** | 9.13 | 305 | `isMisesKLRandomAt_of_isMartinLofRandom` | `ChangeOfMeasure.KLRandomness` | proved | |
| Direct proof of Theorem 202 | 9.13 | 306-307 | none | n/a | omitted | An alternative proof of a stated theorem. |
| **Theorem 203(a)-(d)** | 9.13 | 307 | `exists_isMisesKLRandom_not_isMartinLofRandom`, `exists_isMisesKLRandom_zerosStrictlyDominate`, `exists_isMisesKLRandom_selectStream_not_isMisesKLRandom`, `exists_isMisesChurchDaleyRandom_permutation_not_isMisesChurchRandom` | `ChangeOfMeasure.Separations` | proved | |
| Problem 279 | 9.13 | 309 | `isMisesChurchDaleyRandom_of_output` | `NonMonotone.ChurchDaleySeparation` | proved | |
| Problem 280 | 9.13 | 309 | `exists_isMisesKLRandom_not_isKurtzRandom` | `ChangeOfMeasure.Separations` | proved | |
| KL randomness | 9.13 | 309 | `KLBetting`, `IsKLRandom`, `isKLRandom_of_isMartinLofRandom`, `isKLRandom_iff_total` | `NonMonotone.KLBetting`; `NonMonotone.KLTotalMartingales` (`isKLRandom_iff_total`) | proved | |
| **KL = ML?** | 9.13 | 309 | `KLRandomnessEqualsMartinLofQuestion` | `NonMonotone.KLTotalMartingales` | open | A `Prop`, asserted by nothing. |
| Figure 3 | 9.13 | 310 | `isPartialComputablyRandom_of_isKLRandom`, `isMisesKLRandom_of_isKLRandom`, `exists_isBalanced_not_isKurtzRandom`, `exists_isComputablyRandom_not_isMisesChurchDaleyRandom`, `exists_isPartialComputablyRandom_not_isMisesKLRandom` | `RandomnessRelations` | proved | The remaining arrows are the theorems listed in the module header. |
| Figure 3: partially computably random ⇒ computably random | 9.13 | 310 | `isComputablyRandom_of_isPartialComputablyRandom` | `PartialRules.PartialMartingales` | proved | Not part of Theorem 190. |

### 4.3 Deliberate omissions (no Lean statement)

| Item | § | p. | Reason |
| --- | --- | --- | --- |
| Random sequences satisfy `K(F, ω(F)) ≥ \|F\| − c` | 8.5.5 | 251 | Problem 145, another chapter, cited for comparison only. |
| Amplification by repeating the algorithm | 8.5.6 | 253 | Parenthetical; independent repetition is not modelled. |
| Market reading of randomness | 9.6 | 276-277 | No mathematical statement. |
| Finite counterpart of Theorem 193 | 9.12 | 296 | Needs a notion of complexity of a rule; cited only. |
| Example after Theorem 200 | 9.13 | 304 | An instance of Theorem 200. |
| Direct proof of Theorem 202 | 9.13 | 306-307 | An alternative proof of a stated theorem. |
| Tangent-line remark on the Lemma of 9.12 | 9.12 | 294 | An alternative proof of a stated lemma. |

### 4.4 Open question

`KLRandomnessEqualsMartinLofQuestion` (p. 309) only names the question; nothing asserts it or its
negation.  The other implications of Figure 3 are theorems.

## 5. Deviations from the printed statements

Some entries repair false or undefined wording, some make an implicit convention explicit, and
some are true strengthenings.

| Item | Printed | Here | Reason |
| --- | --- | --- | --- |
| Theorem 152 | Head position not stated | Head starts in the left zone | Used in the proof; false otherwise (a head starting far in `R` writes behind a long blank prefix, whose complexity is unrelated to `t`). |
| Theorem 152 | "for any `b`" | `b ≥ 1` | For `b = 0` a machine can copy `L` to `R`, and `t log m / b` has no meaning. |
| Theorem 153 | Output convention not fixed | `Duplicates` fixes the origin and trailing blanks | Crossings are counted left to right, as in both editions. |
| Theorem 154 | "for every `k`" | Kept, with a separate language for `k = 0` | The book's `L_m` with `m = (k+1)k/2` is empty of meaning for `k = 0`. |
| Proof of Theorem 154 | "all strings of length `m`" | Not used | Slip for length `N`. |
| Theorem 158 as instance of 157 | Count "at most `2^{αn}`" | `ncard_plainK_lt_lt` gives `< 2^{αn+1}`, for optimal `V` | The programs shorter than `αn` can number up to `2^{⌈αn⌉} − 1`.  Absorbed by changing `α`.  Optimality is needed in Lean because `toNat ⊤ = 0`. |
| Theorem 159 | "less than" in the statement, "at most" in the proof | "less than", also for the new set | |
| Problem 245 | The whole proof of Theorem 158 with plain instead of prefix complexity | Only the first block step: appending `N` bits raises plain complexity by `βN` (a consequence of Problem 46) | Weaker than the book.  The iteration over blocks, where the `O(log)` loss of plain subadditivity has to be absorbed, is not stated.  The conclusion of the problem is Theorem 158, which is proved by another route, through Theorem 157. |
| Problem 246 | Problem 47 as printed | Uniform `h ≥ H` | The literal statement is impossible at `h = 1` for integer `f`. |
| Problem 248 | "does not have short substrings" | Long substrings | Slip: the conclusion is that of Theorem 157. |
| Emergency level | "if `x` contains a forbidden string, `w_c(x) ≥ 1`" | Forbidden *suffix* | An occurrence strictly inside `x` is not counted by the definition.  The first forbidden substring of a growing string is a suffix, so the argument is not affected. |
| Theorem 161 | "at most `2^{αn}` restrictions" | Also finiteness | `Set.ncard` of an infinite set is `0`, and the book's count means a finite number. |
| Second corollary of Theorem 162 | "for every finite `F`" | `\|F\| ≥ N` | The derivation gives this; small `F` change the statement by a constant. |
| Theorem 163 | "clauses of size `m`" | `0 < m` | A clause with no variables is always false and has no neighbours. |
| Theorem 163 | Neighbour count | Includes the clause itself | By the book's definition two clauses are neighbours if they share a variable; the proof uses it. |
| Theorem 163 | "time polynomial" | `(N + 2)²` machine steps | Each step handles at most `m ≤ n` variables; the convention is stated in the module. |
| Problem 252, continuous | Bodies in space | Compact bodies | The continuous Loomis-Whitney inequality is stated for compact sets. |
| Lemma 2 of 8.7 | Any `ε` | `ε ≤ 1/2` | False otherwise: a random `ω₁` and `0^∞` have `ρ = 1/2 < 0.9`, dimensions differing by `1 > H(0.9)`. |
| Relative dimension (8.7) | Dimension relative to an oracle | Finite relative prefix complexity divided by length | The equality with an oracle-effective cover definition is not formalized; it is not needed for Theorem 165. |
| Problem 258 | "an integer factor" | `k ≠ 0`, every base `b ≥ 2` | `0` is not normal. |
| After Theorem 172 | "starting with first bit `1`" | First bit `0` | Slip: a first `1` puts the ones ahead. |
| Problem 262 | "more zeros than ones" | At least as many | Contains the set in the problem, and is the set Theorem 182(d) needs. |
| Theorem 175 | "exceeds `k`" | `≥ k` | The stronger form; the proof treats "`k` or more". |
| Stopped capital | Implicit | Probability measure | `massR` is a `toReal`, additive only for finite masses. |
| Theorem 176 | Different editions: "measure `ε`" and "at most `ε`" | `≤ ε` | Implies both. |
| Problem 265 | Any computable `π` in the section | Positive cylinders | False otherwise: a capital on a null cylinder is unconstrained. |
| `a(x) / π(x)` | No condition | Positive cylinders | The ratio is undefined otherwise. |
| Problem 270 | No condition | Positive cylinders; "upper bound" up to a constant | `−log μ` would be infinite. |
| Theorem 182 | One measure assumption | (b) general measure with positive cylinders; (a) also permits null cylinders | Both scopes are stated separately. |
| Theorems 185, 186 | Initial bound and exponent conventions | `m(Λ) ≤ 1`; only `β > α` | Source conventions made explicit. |
| Theorem 187 | Gales introduced for `α ∈ (0, 1]` | Infimum over computable `α > 0` | For `A = Ω` no `α ≤ 1` qualifies, by Theorem 180, while the dimension is `1`. |
| Theorems 191, 192(b) | Computable `p` | Arbitrary frequency and endpoint cases included | True extensions; computable `p` was already required. |
| Sections 9.3 and 9.12 | Opposite bet conventions | `betGain`, `betGainOnOne` | Kept separate rather than conflated. |
| Schnorr and Kurtz randomness (3.4) | Dyadic bounds, optional enumeration | Equivalent formulations | Kurtz uses the literal sum of finite cover masses, equivalent to a union budget by prefix pruning. |
| Theorem 196(b), Theorem 197 | Conditional probabilities in `(ε, 1 − ε)` | Not assumed | The library's `vovk_merging_summable` does not need it.  Stronger. |
| Problem 277 | Two measures and a sequence `ω` that is Martin-Löf random for both, in the setting of Theorem 197 along `ω` (conditional probabilities in `(ε, 1 − ε)` and close along `ω`), while the measures differ elsewhere | Two measures and an `ω` that is Martin-Löf random for both, and the measures differ elsewhere | Weaker than the book.  The statement has no `ε`-separation and no closeness of the conditional probabilities along `ω`.  The difference elsewhere is witnessed by a degenerate second measure (half of its mass is a point mass at `111…`), so the statement is true but does not show that the two measures stay close along `ω`. |
| Theorem 198 | `d` unrestricted | `0 ≤ d`, `0 < n` | For `d < 0` the event is certain and the bound can be below `1`. |
| Theorem 200 | Display ends with `i_n` | First `n` positions | Slip for `i_{n−1}`; the text says `n` terms. |

## 6. Library declarations reused

| Need | Library declaration |
| --- | --- |
| Finite or infinite sequences | `BitStream`, `BitStream.ofPrefixSet`, `IsStreamPrefixSet` |
| Cantor space, cylinders, masses | `CantorSeq`, `cantorPrefix`, `IsCantorPrefix`, `cantorCylinder`, `cantorMass`, `cantorMass_add`, `cantorPrefix_succ` |
| Measures | `uniformMeasure`, `bernoulliMeasure`, `cantorMass_uniformMeasure`, `IsComputableMeasure` |
| Martin-Löf randomness | `IsMartinLofRandom`, `IsEffectivelyNull`, `IsUniformlyEffectiveOpen` |
| Effectivity | `IsRE`, `IsDecidableSet`, `ComputableReals.IsComputableReal` |
| Complexity | `plainK`, `condK`, `isOptimalConditional`, `KP`, `KPPlain`, `IsOptimalPrefixConditional`, `KMOf`, `IsOptimalMonotoneDecompressor`, `KA`, `universalContinuousSemimeasure` |
| Coding | `natBits`, `pairCode`, `listCode`, `wordBits` |
| Frequencies | `freqOne`, `bitVal` |
| Fixed computable subsequences (a different notion from selection rules) | `AlgorithmicRandomness/Subsequence.lean`, Problem 82 |
| Dimension | `IsAlphaNull`, `IsEffectiveAlphaNull`, `effectiveHausdorffDim` |
| Entropy | `binaryEntropy` |
| Tests | `IsProbabilityBoundedRandomnessTest` |
| Conditional probabilities | `condProb`, `condProb_cantorMass_add_eq_one`, `MDLPrediction.random_prefix_mass_pos` |
| Theorem 197 | `MDLPrediction.vovk_merging_summable` |
| Oracle complexity | `charOracle`, `PartrecIn`, `PointToSet.optimalOraclePrefix` |
| Used by the proofs | `exists_extension_KP_ge` (Theorem 71), `two_mul_KP_triple_le`, `exists_plainK_word_le_entropy_freq` (Theorem 146), `isMartinLofRandom_iff_boundedMonotoneDeficiency` (Theorem 90), `isMartinLofRandom_iff_boundedAPrioriDeficiency` (Theorem 91), `isMartinLofRandom_uniform_iff_KA_KMOf_eq_length` (Theorem 94), `effectiveHausdorffDim_singleton_eq_liminf` (Theorem 120), `tendsto_freqOne_of_isMartinLofRandom_uniform` (Theorem 33), `strongLaw_bernoulli` (Theorem 27) |

New definitions were added only where the library has none: selection rules, martingales and
gales, Schnorr and Kurtz randomness, machine models, restrictions, and independent trials with
varying probabilities.
