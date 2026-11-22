# Muchnik–Romashchenko, "Stability of properties of Kolmogorov complexity under relativization"

Formalization notes for `KolmogorovMathlib/Relativization/`.

Source: An. A. Muchnik, A. E. Romashchenko, *Stability of properties of Kolmogorov complexity
under relativization*, Problems of Information Transmission 46(1), 2010. The paper text is not
part of the repository; these notes refer to its numbering of sections, definitions, lemmas and
theorems.

The paper asks whether the properties of the Kolmogorov complexity of a tuple `x̄` are preserved
when all complexities are relativized to a string `z` that has little mutual information with
`x̄`. Properties expressed by quantifier-free formulae are preserved (Proposition 1, Theorem 3).
For existential formulae one direction holds in general (Theorem 4); the other direction is
proved for stochastic tuples (Theorem 5) and is Conjecture 3 in general. Theorem 6 shows that
some pairs of strings are not equivalent to any stochastic pair, so the general case does not
reduce to Theorem 5. Theorem 2 shows that common information that can be extracted with an
oracle can be extracted without it, at the price of a sublinear increase of the thresholds; the
version with logarithmic thresholds is Conjecture 2. Conjectures 2 and 3 are open; they are
formalized as propositions and are not asserted.

All declarations are in the namespace `Kolmogorov.Relativization`. The main complexity theorems
assume a decompressor `D` with `isOptimalConditional D`; the open-conjecture predicates are
defined for arbitrary `D`.

## Modules

| module (under `KolmogorovMathlib/Relativization/`) | content |
|---|---|
| `Definitions.lean` | vocabulary of the paper: natural-valued complexities, subtuples, complexity profiles, typization, combinatorial entropy, stochasticity, equivalence, bunches, extractable common information, the propositions `Conjecture2` and `Conjecture3` |
| `QuantifierFree.lean` | Proposition 1, Theorem 3 |
| `Typization.lean` | aggregator for Lemmas 1–3 |
| `Typization/TypizationSize.lean` | Lemma 1: the size of the typization (enumeration of the tuples of smaller or equal profile, index description, lower bound) |
| `Typization/CloneMajority.lean` | Lemma 2: more than half of the typization consists of clones (partition chain rules, total-complexity bound) |
| `Typization/OracleStability.lean` | Lemma 3 in the form `lemma3_relativized` and its two printed parts `lemma3_part1`, `lemma3_part2` |
| `CombinatorialEntropy.lean` | Lemma 4: `K(x̄_V \| x̄_W, list(A)) ≤ ent_{V\|W}(A) + O(1)` |
| `Bunches.lean` | aggregator for Lemmas 5 and 6 |
| `Bunches/FiniteStageSelection.lean` | enumeration of the bunches of a given type and the effective greedy selection that keeps a set or discards it because of a large intersection with a kept set |
| `Bunches/BunchCovers.lean` | Lemma 5 and Lemma 6: standard covers of bunches and of semi-bunches, with the packing bounds that limit the number of kept sets |
| `CommonInformation.lean` | aggregator for Theorem 2 and the remarks of Sections 1, 2 and 6 |
| `CommonInformation/MutualInformationBounds.lean` | the bounds `K(y) ≤ I(x₁ : x₂) + …` and `K(v \| z) ≤ K(v \| x₁, z) + K(v \| x₂, z) + I(x₁ : x₂ \| z) + …`, and the cut and counting estimates of Section 6 |
| `CommonInformation/CloneCoordinateChains.lean` | typization of `⟨v, z⟩` given `x̄`: strong-typization count, clone coordinates, chain rules, `theorem2_typize`, `theorem2_semi_bunch_dichotomy` |
| `CommonInformation/ExtractionIndexBounds.lean` | extraction of a common string from a Lemma 6 cover of a semi-bunch (`theorem2_cover_semibunch`, `theorem2_select_pair`) |
| `CommonInformation/PairCloneBounds.lean` | bounds for pairs of clones and for the replacement oracles |
| `CommonInformation/PairPaddingBounds.lean` | pair extraction and oracle replacement; an iteration bound (`theorem2_typization_and_cover`) |
| `CommonInformation/SublinearDelta.lean` | choice of the number of rounds and of the budgets so that all error terms are `o(N)` |
| `CommonInformation/FiniteIteration.lean` | the iteration that replaces the oracle finitely many times (`theorem2_finite_iteration`) |
| `CommonInformation/CommonInformationTheorem.lean` | assembly of `theorem2`; the first part of the reduction of Conjecture 2 to Conjecture 3 |
| `CommonInformation/ConjectureReduction.lean` | `conjecture2_of_conjecture3` |
| `Existential.lean` | aggregator for Theorems 4 and 5 |
| `Existential/ProfileRelativization.lean` | `theorem4_extended`, `theorem4`, and auxiliary results for Theorem 5 through `theorem5_extended_aggregate_section` |
| `Existential/StochasticProfiles.lean` | `theorem5_extended`, `theorem5` |
| `Stochastic.lean` | aggregator for Section 2 examples and Theorem 6 |
| `Stochastic/StochasticExamples.lean` | `incompressible_isSetStochastic`, `exists_equiv_stochastic_string`, `remark2` |
| `Stochastic/NonstochasticPairs.lean` | Theorem 6 (`theorem6`): the random bounded-degree graph and the extraction argument |

## Conventions (`Definitions.lean`)

| paper | Lean |
|---|---|
| `K(x)`, `K(x \| y)` | `natK D x`, `natCondK D x y` (values in `ℕ` of `plainK`, `condK`; exact because every statement assumes `isOptimalConditional D`) |
| oracle `z`, `K(a \| b, z)` | `natCondK D a (pairCode b z)` |
| `n`-tuple `x̄`, `⟨x̄, ȳ⟩` | `x : Fin n → BitString`, `Fin.append x y` |
| `x̄_V`, `K(x̄_V)`, `K(x̄_V \| z)` | `subtupleCode x V`, `subK D x V`, `subKRel D x z V` |
| `K(x̄_V \| x̄_W)`, `K(x̄_V \| x̄_W, z)` | `subCondK D x V W`, `subCondKRel D x z V W` |
| `K(x̄)`, `K(x̄, z)` | `natK D (tupleCode x)`, `natK D (pairCode (tupleCode x) z)` |
| `O(log N)` | `logSlack c N = c * (Nat.bits N).length + c`, `c` existentially quantified |
| `I(x̄ : z) ≤ δ` | `MutualInfoLe D (tupleCode x) z δ`, that is `K(x̄) ≤ K(x̄ \| z) + δ` |
| profiles at distance `≤ d` | `ProfileWithin`, `ExtProfileWithin` (non-empty `V`; disjoint `V, W` with `V ≠ ∅`) |
| `T(x̄ \| ȳ)`, `ST_k(x̄ \| ȳ)` | `typization D x y`, `strongTypization D k x y` (sets of functions) |
| `ent_{V\|W}(A)`, `list(A)` | `combEnt A V W`, `tupleSetCode A` |
| `(α, β)`-stochastic | `IsSetStochastic D x α β`, `IsStochasticTuple D x α β` |
| `a ∼_C b` | `EquivWithin D C a b` |
| bunch, semi-bunch | `IsBunch D α β γ X`, `IsSemiBunch D α β γ X` |
| "an algorithm enumerates `U_0, …, U_q`" | `HasStandardCover` |
| `q` bits of common information, with and without the oracle | `CommonInfoExtractable D x₁ x₂ q k`, `CommonInfoExtractableRel D x₁ x₂ z q k` |

`subtupleCode x ∅ = []`, so `subCondK D x V ∅ = subK D x V` exactly, and
`subCondKRel D x z V ∅` differs from `subKRel D x z V` by a constant (`pairCode [] z` versus `z`).

## Statements

| paper | Lean | module |
|---|---|---|
| Proposition 1 | `proposition1` | `QuantifierFree.lean` |
| Theorem 2 | `theorem2` | `CommonInformation/CommonInformationTheorem.lean` |
| Theorem 3 | `theorem3` | `QuantifierFree.lean` |
| Theorem 4 | `theorem4`, `theorem4_extended` | `Existential/ProfileRelativization.lean` |
| Theorem 5 | `theorem5`, `theorem5_extended` | `Existential/StochasticProfiles.lean` |
| Theorem 6 | `theorem6` | `Stochastic/NonstochasticPairs.lean` |
| Lemma 1 | `lemma1` | `Typization/TypizationSize.lean` |
| Lemma 2 | `lemma2` | `Typization/CloneMajority.lean` |
| Lemma 3 | `lemma3_part1`, `lemma3_part2`, `lemma3_relativized` | `Typization/OracleStability.lean` |
| Lemma 4 | `lemma4` | `CombinatorialEntropy.lean` |
| Lemma 5, Lemma 6 | `lemma5`, `lemma6` | `Bunches/BunchCovers.lean` |
| Conjecture 2, Conjecture 3 (open) | `Conjecture2`, `Conjecture3` (propositions, not asserted) | `Definitions.lean` |
| "Conjecture 2 is a special case of Conjecture 3" | `conjecture2_of_conjecture3` | `CommonInformation/ConjectureReduction.lean` |
| `K(y) ≤ I(x₁ : x₂) + O(k + log K(x₁, x₂))` (Section 1) | `commonInfo_le_mutualInfo` | `CommonInformation/MutualInformationBounds.lean` |
| `K(v \| z) ≤ K(v \| x₁, z) + K(v \| x₂, z) + I(x₁ : x₂ \| z) + O(log N)` (Section 6) | `condK_le_add_condMutualInfo` | `CommonInformation/MutualInformationBounds.lean` |
| "every incompressible string is stochastic" (after Definition 1) | `incompressible_isSetStochastic` | `Stochastic/StochasticExamples.lean` |
| "for an individual `x` there exists an equivalent stochastic `x'`" (Section 2) | `exists_equiv_stochastic_string` | `Stochastic/StochasticExamples.lean` |
| Remark 2 | `remark2` | `Stochastic/StochasticExamples.lean` |

The headline statements, in the conventions above:

* **Theorem 2.** For every `f(N) = o(N)` there is `g(N) = o(N)` such that, for all `x₁, x₂, z`
  with `N = K(x₁, x₂, z)`: if `I(x̄ : z) ≤ f(N)` and `q` bits of common information can be extracted
  from `x₁, x₂` with the oracle `z` at threshold `f(N)`, then `q` bits can be extracted without
  the oracle at threshold `g(N)`. The thresholds are `o(N)`, not `O(log N)`; the logarithmic
  version is Conjecture 2.
* **Theorem 4.** If `I(x̄ : z) ≤ δ`, then for every `ȳ` there is `ȳ'` such that the profiles
  `K(x̄, ȳ)` and `K(x̄, ȳ' | z)` differ componentwise by at most `δ + O(log K(x̄, ȳ, z))`.
* **Theorem 5.** The same statement as Conjecture 3 (profile of `⟨x̄, ȳ⟩` given `z` against the
  profile of `⟨x̄, ȳ'⟩`) is proved when `x̄` is `(a log K(x̄), a log K(x̄))`-stochastic; the constant
  depends on `n`, `m` and `a`. For tuples that are not stochastic the statement is Conjecture 3
  and is not proved.
* **Theorem 6.** For positive reals `α, β` with `α, β < γ < α + β` and every `C`, for all large `n` there are strings
  `x₁, x₂` with `K(x₁) = αn + O(log n)`, `K(x₂) = βn + O(log n)`, `K(x₁, x₂) = γn + O(log n)`
  such that no `(C log n, C log n)`-stochastic pair is `C`-equivalent to `⟨x₁, x₂⟩`.

## What is not formalized

* **Conjecture 1** is an informal remark of the paper and has no Lean counterpart.
* **Conjectures 2 and 3** are open. `Conjecture2 D` and `Conjecture3 D` are propositions that
  state them; nothing asserts them. What is proved about them: `conjecture2_of_conjecture3`
  (Conjecture 3 implies Conjecture 2), Theorem 5 (Conjecture 3 for stochastic tuples) and
  Theorem 2 (Conjecture 2 with `o(N)` thresholds).
* **Theorem 1** (Kolmogorov–Levin symmetry of information) and the theorem on conditional
  descriptions, both quoted by the paper, are not restated here; they are results of the library
  (`KolmogorovMathlib/CommonInformation/PlainSymmetry.lean`,
  `KolmogorovMathlib/Multisource/Muchnik.lean`).
* **Lemma 7 and Remark 3** are steps of the proof of Theorem 5 about objects of that proof; they
  are part of the proof of `theorem5_extended` and are not stated as separate public results.

## Deviations from the printed text

1. **Lemma 3 needs `δ₁ ≥ 0`.** As printed, with integers `δ₁, δ₂`, the lemma is false for
   `δ₁ < 0`: take `n = 1`, `m = 0`, `x'` the empty string, `x` incompressible,
   `δ₁ = K(x') − K(x)`, `δ₂ = −δ₁`. The proof bounds the two auxiliary terms of the chain rule
   by `δ₁` each, which is only an upper bound for `2δ₁` terms when `δ₁ ≥ 0`. `δ₂` may be
   negative, and the proof of Theorem 5 uses a negative `δ₂`.
2. **Lemma 3 in the proof of Theorem 5.** The proof applies Lemma 3 with the
   oracle on the side of the *reference* tuple (`K'(x̄, ȳ | z)`), a case not covered by the two
   printed parts; `lemma3_relativized` has an oracle on either side and arbitrary tuples.
3. **Conjecture 2: `N = K(x̄, z)`.** The paper prints `N = K(x̄, y)`; no `y` occurs in the
   statement, and Theorem 2 has `N = K(x̄, z)`.
4. **`I(x̄ : z)`** is `K(x̄) − K(x̄ | z)` throughout (the form of Proposition 1 and of the proofs
   in Section 4); the paper's `I(x : y) = K(y) − K(y | x)` differs from it by `O(log K(x̄, z))`.
5. **Theorem 2: `K(w) ≥ q`.** The proof in Section 6 constructs `w` with `K(w) ≥ q − g(N)`; the
   statement asks for `K(w) ≥ q`, obtained by padding `w` with `g(N) + O(log N)` bits that are
   incompressible given `w` (this keeps `K(w | xᵢ) = o(N)`). For small `N` the hypotheses hold
   for finitely many `(x₁, x₂, z, q)` only, so `g` can be defined there separately.
6. **Lemmas 5 and 6: the list may be empty.** When no `(α, β, γ)`-(semi-)bunch exists, the
   printed "list `U_0, …, U_q`" cannot consist of (semi-)bunches; `HasStandardCover` uses a count
   `cnt α β γ` of the listed sets, and `|U ∩ Uᵢ| ≥ 2^(β − ε)` with `ε = 2(β − α) + O(1)` is
   written as `2 ^ (2α) ≤ |U ∩ Uᵢ| · 2 ^ (β + c)`. "An algorithm enumerates the list" is a
   partial computable `F` with `F (α, β, γ, i)` defined exactly for `i < cnt α β γ` (the greedy
   selection of the Appendix never produces an index `≥ cnt` and diverges there; `cnt` is the
   limit length of the selected list and is not computable).
7. **Complexity of a standard semi-bunch given its index.** The paper states `O(log γ)`; what
   the algorithm gives is `O(1)` given `(α, β, γ, i)`, hence `O(log (α + β + γ))` given `i`.
8. **Theorem 6: thresholds.** `C log n` and `C log K(a, b)` are `logSlack C n` and
   `logSlack C (K(a, b))`; for a fixed `C` this makes the non-existence claim slightly stronger.
9. **Extended profiles.** The proofs of Theorems 4 and 5 give closeness of the extended
   profiles with coefficient `1` at `δ` (`theorem4_extended`, `theorem5_extended`); closeness of
   the profiles alone would only give coefficient `2` for the conditional complexities.

## Remarks on the proofs

* **Lemma 1** asserts the finiteness of the typization explicitly, since `Set.ncard` of an
  infinite set is `0`.
* **Lemma 2** is a strict inequality, while the Appendix says "at least half": with
  `r = O(log N) + 1`, fewer than half of the elements of the typization have complexity below
  `K(x̄ | ȳ) − r` given `ȳ`.
* **Lemma 3, large `δ₁`.** The chain rule for the primed tuple has error `O(log K(u' | z'))`,
  which is `O(log N)` only when `K(u' | z') = O(N)`. When `2δ₁ + δ₂ ≥ N + O(1)` the conclusion is
  trivial, and otherwise the two hypotheses give `K(u' | z') < 2N + O(1)`.
* **Theorems 4 and 5** apply Lemma 3 to tuples `⟨x̄, ȳ'⟩` in which the second block varies, while
  the printed lemma varies the first block (`⟨x̄', ȳ⟩`); this is why `lemma3_relativized` is
  stated for arbitrary tuples.
* **Theorem 5, the role of `δ`.** The argument has to be run with
  `Δ = max(0, K(x̄) − K(x̄ | z)) ≤ δ`, not with `δ`: the number of selected correct sets is
  `2 ^ (Δ + O(log N))`, Remark 3 gives `δ₁ = Δ + O(log N)`, the choice of `ȳ'` gives
  `δ₂ = −Δ + O(log N)`, and Lemma 3 yields `2δ₁ + δ₂ = Δ + O(log N) ≤ δ + O(log N)`. With
  `δ₁ = δ` the bound would be `2δ − Δ`. In Remark 3 the index sets range over the subsets of
  `{1, …, n + m}` (the paper prints `{1, …, n}`).
* **`conjecture2_of_conjecture3`.** Conjecture 3 gives a string `w₀` with `K(w₀) ≥ q − O(log N)`
  only; `w₀` is padded with `O(log N)` bits that are incompressible given `w₀`.

## Library results used

* Symmetry of information with an external condition, in the convention
  `K(y | x, w) = condK V y (pairCode x w)`: `condK_pairCode_symmetryOfInformation_values`,
  `condK_pairCode_chain_lower_values`, `condK_pairCode_chain_upper_values`,
  `condK_pairCode_submodularity_values`
  (`KolmogorovMathlib/CommonInformation/ConditionalIndependence/Part01.lean`); without a
  condition: `pairPlainK_symmetryOfInformation_values`
  (`KolmogorovMathlib/CommonInformation/PlainSymmetry.lean`).
* Codes of lists: `listCode`, `decodeListCode` (`KolmogorovMathlib/Encoding/Tuples.lean`).
* Computable maps: `condK_comp`, `condK_map_le`, `plainK_le_length`, `condK_le_plainK`
  (`KolmogorovMathlib/Complexity/Properties.lean`).
* Counting: `compressibleWords`, `card_compressibleWordsLt`, `exists_incompressible_string`
  (`KolmogorovMathlib/Complexity/Incompressibility.lean`).
