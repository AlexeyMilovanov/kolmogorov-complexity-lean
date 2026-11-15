# SUV Chapter 13 "Information and logic": formalization notes

Shen, Uspensky, Vereshchagin, *Kolmogorov Complexity and Algorithmic Randomness* (AMS 2017),
Chapter 13, Sections 13.1-13.6 (printed pp. 401-423).

## Overview

The chapter is formalized in full: every numbered item (Theorems 238-247, Problems 333-344)
and the supporting statements of §13.1-13.6 have a Lean statement with a complete proof.
The declarations live in the namespace `Kolmogorov.InformationLogic`, in the modules
`KolmogorovMathlib/InformationLogic/*.lean`; the aggregator is
`KolmogorovMathlib/InformationLogic.lean`, imported by `KolmogorovMathlib.lean`. The modules
`SingletonFormulas`, `DiagonalLowerBounds` and `NonTupleLemmas` are aggregators of topical
submodules; the "Module" column of the item map names the submodule that contains each
declaration.

There is no `sorry` under `KolmogorovMathlib/InformationLogic`, and every theorem depends only
on the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Conventions

* **Problem** = `Set BitString`.  **Complexity of a problem**
  `problemK D X = ⨅ x ∈ X, plainK D x` (`ℕ∞`, `⊤` for the empty problem), `D` an arbitrary
  optimal decompressor (`isOptimalConditional D`), i.e. the book's plain complexity `C`.
  `C(x | y)` is `condK D x y`, `C(x, y)` is `cPair D x y = plainK D (pairCode x y)`, triples
  and quadruples are coded with `listCode`.
* **Operations** depend on a `ProblemCalculus` `P`: pairing `P.pair` with inverse `P.unpair`,
  tags `P.tag0`, `P.tag1`, and a programming language `P.lang : Map`, `[p](x) = P.lang (p, x)`.
  `P.Admissible`: computable pairing with computable inverse (injective; the book asks for a
  bijection, only injectivity and the computable inverse are used), distinct tags, and the
  Gödel property `IsGodelLang` (partial computable, and every partial computable language is
  translated into it by a total computable map).  `P.conj` = `∧` (`Set.image2 P.pair`),
  `P.disj` = `∨` (tagged), `P.pdisj` = pseudo-disjunction `∨~`, `P.imp` = `→`.
  **Every theorem is stated for an arbitrary admissible calculus** (the book fixes one choice
  and proves invariance, Problem 339).  The concrete calculus `std L` uses `pairCode`,
  tags `[false]`, `[true]`; `std_admissible` and `isGodelLang_universalDecompressor` show
  that admissible calculi exist (`exists_admissible`).
* **Precision.** `O(1)`: `∃ c, ∀ data, … ≤ … + c`.  `O(log n)` for strings of length at most `n`:
  `∃ k, ∀ n data, lengths ≤ n → … ≤ … + logSlack k n` (`logSlack k n = k * |bits n| + k`, the
  library's convention of Chapter 12).  `O(log C(…))`: `logSlack c (….toNat)`.  Linear
  bounds `εn` are written with `ε = 1/d`, `n ≤ d * C` in `ℕ∞`.  There is no truncated
  subtraction: differences are moved to the other side.
* **Formulas**: `PFormula ι` with `var`, `conj`, `disj`, `imp` (no `⊥`); `PFormula.eval P v`
  substitutes problems.  **IPC**: `PFormula.Provable`, the Hilbert system of positive
  intuitionistic logic (K, S, three `∧` and three `∨` axiom schemes, modus ponens); for the
  negation-free formulas of the chapter this is IPC-provability (conservativity, not
  formalized).  **Kripke**: `PFormula.Forces V w` over a preorder, `IsMonotoneValuation V`.
  **Critical implications**: `CriticalData k` (nonempty list of pairs of nonempty disjoint
  `Finset (Fin k)`), its `formula`; multiple `∧`/`∨` are nested to the right (`conjList`,
  `disjList`), as in the book's technical note (printed p. 410).

## Item map

| Book item | Sec. | p. | Lean name(s) | Module | Reading / deviation |
| --- | --- | --- | --- | --- | --- |
| def. `C(X)`, `C(∅) = ∞`, `C({x}) = C(x)` | 13.1 | 401 | `problemK`, `problemK_empty`, `problemK_singleton`, `problemK_mono`, `problemK_le_of_mem`, `exists_mem_plainK_eq_problemK` | Problems | — |
| defs `∧`, `∨`, `∨~`, `→`, Gödel property | 13.1 | 401-402 | `ProblemCalculus.conj/disj/pdisj/imp`, `IsGodelLang`, `ProblemCalculus.Admissible`, `std` | Problems | union-disjunction is just `X ∪ Y`, no claim |
| `C({x} ∧ {y}) = C(x, y)` | 13.1 | 401 | `problemK_conj_singleton_le_cPair`, `cPair_le_problemK_conj_singleton` | OperationsComplexity | `O(1)` (exact for `std`) |
| `C(X ∨ Y) = min(C(X), C(Y)) + O(1)` | 13.1 | 401 | `problemK_disj_le_min`, `min_le_problemK_disj` | OperationsComplexity | — |
| `C({x} → {y}) = C(y\|x) + O(1)` | 13.1 | 402 | `problemK_imp_singleton_le_condK`, `condK_le_problemK_imp_singleton` | OperationsComplexity | — |
| `C(x \|⩾ n) = C({m ⩾ n} → {x})` | 13.1 | 402 | — | — | not stated: notation of §6.4 (formalized in `KolmogorovMathlib/Complexity/GeneralScheme/`); the identity with `{m ⩾ n} → {x}` is only a remark and is not restated here |
| `(x → y) ∧ (y → x)`: `max(C(x\|y), C(y\|x)) + O(log C(x, y))` | 13.1 | 402 | `problemK_imp_conj_imp_le`, `max_condK_le_problemK_imp_conj_imp` | OperationsComplexity | both sides with the book's precision (the lower one holds with `O(1)`) |
| `(x → z) ∧ (y → z)`: `max(C(z\|x), C(z\|y)) + O(log C(x, y, z))` | 13.1 | 402 | `problemK_two_conditions_le`, `max_condK_le_problemK_two_conditions` | OperationsComplexity | idem |
| Problem 333 | 13.1 | 402 | `problemK_pdisj_le_disj`, `problemK_disj_le_pdisj` | OperationsProblems | — |
| Problem 334 | 13.1 | 402 | `problemK_imp_imp_singleton_le`, `condK_le_problemK_imp_imp_singleton` | OperationsProblems | "find": answer `C(c \| a, b) + O(1)` (our reading of the hint) |
| Problem 335 | 13.1 | 403 | `problemK_conj_imp_singleton_le`, `plainK_add_condK_le_problemK_conj_imp_singleton` | OperationsProblems | "logarithmic precision" = `O(log n)`, lengths ≤ n |
| Problem 336 | 13.1 | 403 | `problemK_imp_disj_pdisj_le`, `problemK_imp_pdisj_disj_le`, `problemK_disj_le_imp_pdisj_disj` | OperationsProblems | three clauses |
| Problem 337 | 13.1 | 403 | `problemK_imp_imp_pdisj_disj_pdisj_le_log` | OperationsProblems | — |
| remark: `(x ∨~ x) → x` has complexity close to `C(x)` | 13.1 | 403 | — | — | not stated: informal remark; the lower bound is Problem 336 with `y = x` |
| `C(X ∧ Y) ⩽ C(X) + C(X → Y) + O(log C(X))` (or `O(log C(X → Y))`), `C(Y) ⩽ …` | 13.2 | 403 | `problemK_conj_le_add_imp`, `problemK_conj_le_add_imp_log_imp`, `problemK_le_add_imp` | IntuitionisticBounds | — |
| Problem 338 | 13.2 | 403 | `exists_problemK_conj_add_le_add_imp` | IntuitionisticBounds | "significantly less" = gap `n − O(log n)` for nonempty `X`, `Y` whose solutions have length `O(n)` (without the length bound, singletons of huge complexity satisfy it trivially) |
| invariance of `Φ(X, …)` under the calculus | 13.2 | 404 | = Problem 339 | | |
| Problem 339 | 13.2 | 404 | `exists_partrec_eval_calculus_reduction` (one uniform reduction), `problemK_eval_calculus_le` (the claim, `O(1)`) | IntuitionisticBounds | pairing injective, not bijective |
| Problem 340 (Kleene) | 13.2 | 405 | `exists_uniform_solution_of_provable` | IntuitionisticBounds | — |
| provable `Φ` ⇒ `C(Φ(X, …)) = O(1)` | 13.2 | 404 | `problemK_eval_le_of_provable` | IntuitionisticBounds | — |
| provable `Φ → Ψ` ⇒ `C(Ψ(X…)) ⩽ C(Φ(X…)) + O(1)` (used for Thm 238) | 13.4 | 413 | `problemK_eval_le_of_provable_imp` | IntuitionisticBounds | — |
| **Theorem 238** | 13.2 (proof 13.4) | 405, 413 | `exists_finite_sets_le_mul_problemK_eval` | MedvedevReduction | `ε = 1/d`; sets given for every `n`, bound for `n ⩾ N` |
| **Theorem 239** | 13.3 | 405 | `problemK_peirce_singleton_le_log` | SingletonFormulas.PeirceLogBound | — |
| Problem 341 | 13.3 | 406 | `problemK_peirce_singleton_le_log_complexity` | SingletonFormulas.PeirceComplexity | `k = max(C(x), C(y))` via `toNat` |
| `C((x → y) → x) = C(x) + O(log n)` (unnumbered corollary printed after Problem 341, not part of Theorem 239) | 13.3 | 406 | `plainK_le_problemK_imp_imp_singleton`, `problemK_imp_imp_singleton_le_plainK` | SingletonFormulas.PeirceComplexity | the easy direction with `O(1)` |
| **Theorem 240** | 13.3 | 406 | `problemK_imp_imp_singleton_le_disj`, `problemK_disj_le_imp_imp_singleton` | SingletonFormulas.PeirceComplexity; SingletonFormulas.DisjunctionFormulas | — |
| **Theorem 241** | 13.3 | 407 | `problemK_imp_imp_le_disj_conj_imp`, `problemK_disj_conj_imp_le_imp_imp` | SingletonFormulas.DisjunctionFormulas | the remark `= min(C(z), C(x) + C(z\|x, y))` is not stated (it is Problem 335 plus disjunction) |
| **Theorem 242** | 13.4 | 408 | `problemK_imp_imp_imp_disj_le_min_condK`, `min_condK_le_problemK_imp_imp_imp_disj` | DiagonalLowerBounds.ImplicationUpperBound | "in particular … close to `n`": informal, not stated |
| key step of Thm 242 (uniform solution of `(…) → ((x → y) ∨~ (y → x))`) | 13.4 | 409 | `exists_uniform_solution_imp_imp_imp_disj_pdisj` | DiagonalLowerBounds.ImplicationUpperBound | — |
| computable diagonal function | 13.4 | 410 | `exists_partrec_diagonal` | DiagonalLowerBounds.ImplicationUpperBound | — |
| **Theorem 243** | 13.4 | 410 | `condK_others_le_problemK_criticalData_single` | DiagonalLowerBounds.CriticalImplications | stated as the case `N = 1` of Theorem 244 and derived from it |
| **Theorem 244** | 13.4 | 412 | `condK_others_le_problemK_criticalData` | DiagonalLowerBounds.CriticalImplications | — |
| critical implications are not provable | 13.4 | 412 | `not_provable_criticalData_formula` | Kripke | — |
| **Theorem 245** (Medvedev) | 13.4 | 413 | `exists_subst_provable_imp_criticalData` | MedvedevReduction | the book gives no proof (refers to the literature) |
| IPC soundness for Kripke models | 13.4-13.5 | — | `forces_mono`, `forces_of_provable` | Kripke | standard fact used by the book |
| finite Kripke completeness | 13.5 | 413-414 | `exists_finite_kripke_countermodel` | Kripke | standard fact used by the book, not proved there |
| stability of operations under algorithmic equivalence | 13.5 | 415 | `problemReduces_conj`, `problemReduces_disj`, `problemReduces_imp` | KripkeComplexity | stated for reductions (implies the equivalence version) |
| **Theorem 246** (Muchnik) | 13.5 | 413 | `exists_problems_problemK_eval_ge_of_countermodel` (the proof from a countermodel), `exists_problems_problemK_eval_ge` | KripkeComplexity | `∃ c N, ∀ n ⩾ N, ∃ X, …` (equivalent) |
| Problem 342 | 13.6 | 417 | `problemK_quad_le_condK_add_condK`, `problemK_quad_le_condK_add_plainK_left`, `problemK_quad_le_condK_add_plainK_right`, `condK_triple_le_problemK_quad_add_left`, `condK_triple_le_problemK_quad_add_right` | NonTupleComplexity | one theorem per inequality; lower bounds without subtraction |
| Problem 343 | 13.6 | 417 | `exists_quadruples_lowerBound342_add_le_upperBound342` | NonTupleComplexity | one existential (all 6 gaps for the same sequence), `O(1)` as printed |
| **Theorem 247** | 13.6 | 418 | `exists_quadruples_profileClose_problemK_quad_gap` | NonTupleLemmas.QuadrupleGap | `δ = 1/m`; gap required for `n ⩾ N` (equivalent); stated after the two lemmas because its proof uses them |
| incidence lemma (geometric proof) | 13.6 | 418 | `incidence_pairs_card_sq_le` | NonTupleLemmas.IncidenceLemma | `\|S\|² ⩽ C · 2^{11n}`, field of cardinality `2ⁿ` |
| second lemma of the probabilistic proof | 13.6 | 423 | `exists_computable_family_problemK_quad_ge` | NonTupleLemmas.ProbabilisticLemma | "complexity `log n + O(1)`" = member of a computable family (stronger than the literal statement, and what the proof gives); the first lemma (p. 421) is subsumed |
| counting for `ā = uvws`, … and `d = a ⊕ b ⊕ c` | 13.6 | 420-423 | — | — | not stated: proof-internal computations |
| Problem 344 | 13.6 | 423 | `exists_quadruples_profileClose_problemK_disjImp_gap` | NonTupleLemmas.DisjunctiveImplication | stated in the shape of Theorem 247 |

No numbered item of the chapter is omitted.  The two Chapter 12 restatements of §13.1 are new
problem-level statements whose proofs use Theorems 232 and 234.

## Deviations from the printed statements

* **Calculus.** Theorems hold for every admissible `ProblemCalculus` (some pairing, some Gödel
  language), not for one fixed choice.  The pairing is required injective with computable
  inverse, not bijective (`pairCode` is not surjective).
* **IPC.** `Provable` is positive intuitionistic logic; conservativity of IPC with `⊥` over it
  is not formalized.
* **Readings of informal wording.** Problem 334's answer with `O(1)`; Problem 335's
  "logarithmic precision" as `O(log n)` for strings of length at most `n`; Problem 338's
  "significantly" as a gap `n − O(log n)` for solutions of length `O(n)`; `ε = 1/d` and
  `δ = 1/m`; "for all sufficiently large `n`" as `∃ N, ∀ n ⩾ N`.
* **Probabilistic lemma.** "Complexity `log n + O(1)`" of the quadruple is stated as membership
  in a computable family, which is stronger than the literal statement.
* **Precision of lower bounds.** The Chapter 12 restatements of §13.1 and Theorems 240-242 are
  stated with the book's precision, although the lower bounds hold with `O(1)`.
* **Theorem 246.** The book assigns length `2n` to the top world; with the threshold
  `length/10` this only gives `≳ n/5`, so the construction uses a longer string (`20n`, still
  `O(n)`).

## Modules

| Module | Contents |
| --- | --- |
| `InformationLogic.Problems` | `problemK` and its basic API, `IsGodelLang`, `ProblemCalculus`, `Admissible`, operations, `std`, `ProblemReduces`, `ProblemEquiv` |
| `InformationLogic.Bridges` | reduction ⇒ `O(1)` bound, advice reduction ⇒ `O(log n)` bound, projections, Gödel property of `universalDecompressor`, `std_admissible`, `exists_admissible` |
| `InformationLogic.Formulas` | `PFormula`, `eval`, `subst`, `ImpFree`, `Provable`, `Forces`, `conjList`/`disjList`, `CriticalData`, `othersCode`, `eval_subst`, `eval_finite_of_impFree` |
| `InformationLogic.Kripke` | persistence and soundness, finite completeness, critical implications unprovable |
| `InformationLogic.OperationsComplexity` | §13.1 claims for `∧`, `∨`, `→` of singletons and the two Chapter 12 restatements |
| `InformationLogic.OperationsProblems` | Problems 333-337 |
| `InformationLogic.IntuitionisticBounds` | §13.2: modus-ponens inequality, Problems 338-340, corollaries |
| `InformationLogic.SingletonFormulas` | aggregator of the three modules below (§13.3) |
| `InformationLogic.SingletonFormulas.PeirceLogBound` | Theorem 239 |
| `InformationLogic.SingletonFormulas.PeirceComplexity` | Problem 341, the corollary `C((x → y) → x)`, Theorem 240 (upper bound) |
| `InformationLogic.SingletonFormulas.DisjunctionFormulas` | Theorem 240 (lower bound), Theorem 241 |
| `InformationLogic.DiagonalLowerBounds` | aggregator of the two modules below (§13.4) |
| `InformationLogic.DiagonalLowerBounds.ImplicationUpperBound` | computable diagonal function, Theorem 242, its key step |
| `InformationLogic.DiagonalLowerBounds.CriticalImplications` | Theorems 243, 244 |
| `InformationLogic.MedvedevReduction` | Theorems 245, 238 |
| `InformationLogic.KripkeComplexity` | §13.5: stability lemmas, Theorem 246 |
| `InformationLogic.NonTupleComplexity` | §13.6: Problems 342, 343 |
| `InformationLogic.NonTupleLemmas` | aggregator of the five modules below (§13.6) |
| `InformationLogic.NonTupleLemmas.IncidenceLemma` | incidence lemma (`AffLine`, `AffPlane`, `incidence_pairs_card_sq_le`) |
| `InformationLogic.NonTupleLemmas.ProbabilisticLemma` | second lemma of the probabilistic proof |
| `InformationLogic.NonTupleLemmas.QuadrupleConstruction` | counting and `u`-profile steps of the proof of Theorem 247 |
| `InformationLogic.NonTupleLemmas.QuadrupleGap` | `v`-profile step and Theorem 247 |
| `InformationLogic.NonTupleLemmas.DisjunctiveImplication` | Problem 344 |

Import graph: `Problems` ← `Bridges`, `Formulas`; `Formulas` ← `Kripke`;
`Bridges` ← `OperationsComplexity`, `OperationsProblems`; `OperationsComplexity` ←
`NonTupleComplexity` ← `NonTupleLemmas.{IncidenceLemma, ProbabilisticLemma,
QuadrupleConstruction}`; `NonTupleLemmas.{ProbabilisticLemma, QuadrupleConstruction}` ←
`NonTupleLemmas.QuadrupleGap` ← `NonTupleLemmas.DisjunctiveImplication`;
`Bridges` + `Formulas` ← `IntuitionisticBounds`;
`Bridges` + `IntuitionisticBounds` ← `SingletonFormulas.PeirceLogBound` ←
`SingletonFormulas.PeirceComplexity` (the corollary of Theorem 239 uses `problemK_le_add_imp`);
`Bridges` + `IntuitionisticBounds` ← `SingletonFormulas.DisjunctionFormulas`;
`Formulas` + `OperationsComplexity` + `OperationsProblems` ←
`DiagonalLowerBounds.ImplicationUpperBound` ← `DiagonalLowerBounds.CriticalImplications`;
`IntuitionisticBounds` + `DiagonalLowerBounds` + `Kripke` ← `MedvedevReduction`;
`Bridges` + `Kripke` ← `KripkeComplexity`.

## Reuse map

| Library declaration | Module | Used for |
| --- | --- | --- |
| `Map`, `plainK`, `condK`, `isOptimalConditional` | `Core.Basic` | complexity of problems, conditional complexity, languages as `Map`s |
| `universalDecompressor`, `universal_simulation`, `unaryPrefix` | `Core.UniversalDecompressor` | a concrete Gödel language |
| `plainK_map_le`, `plainK_le_length`, `condK_map_le` | `Complexity.Properties` | the reduction lemmas |
| `cPair`, `cPairVal`, `plainK_pair_le_add_two_log` | `Complexity.PairComplexity.Basic` | `C(x, y)`, self-delimiting pairs |
| `plainK_add_condK_le_plainK_pair_add_three_log` | `Complexity.ConditionalComplexity.Continuity` | symmetry of information (Problems 335, 342) |
| `pairCode`, `pairCode_injective`, `length_pairCode` | `Prefix.TwoStage` | the standard pairing (linear length, Theorem 238) |
| `decodeFirst`, `decodeSecond`, `decodeFirst_pairCode`, `decodeSecond_pairCode` | `AlgorithmicProbability.PairProjection` | inverse of the pairing (`pairUnpair`) |
| `pairCode_primrec`, `decodeFirst_primrec`, `decodeSecond_primrec` | `AlgorithmicStatistics.CodedComputability`, `AlgorithmicStatistics.NormalizedCodedFiniteDistribution` | `std_admissible` |
| `listCode` | `Encoding.Tuples` | triples, quadruples, "all other strings" |
| `logSlack`, `logSlack_add_constants` | `AlgorithmicStatistics.TwoPart.Basic` | `O(log n)` slack |
| `exists_informationDistanceCode` (SUV Thm 232) | `Multisource.InformationDistance.Part02` | `(x → y) ∧ (y → x)` |
| `exists_twoConditionCode` (SUV Thm 234) | `Multisource.TwoConditions` | `(x → z) ∧ (y → z)` |
| Mathlib `Nat.Partrec.Code` (`eval`, `exists_code`, `curry`) | Mathlib | Gödel property, diagonal function |
| Mathlib `AffineSubspace`, `Module.finrank`, `Set.ncard`, `Set.image2` | Mathlib | incidence lemma, conjunction |

Not used: prefix / monotone / a priori complexity and `StandardMachine` (the chapter uses plain
complexity), semimeasures, randomness notions, oracles, common information.
