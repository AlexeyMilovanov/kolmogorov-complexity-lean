import Mathlib.Computability.Partrec
import Mathlib.Order.Filter.AtTopBot.Defs
import KolmogorovMathlib.StrongMerging.Basic
import KolmogorovMathlib.StrongMerging.Upper.Minimality
import KolmogorovMathlib.StrongMerging.Lower.Q1

/-!
# Merging strong sufficient statistics: the headline statements

The frozen statements of the strong-merging note `sublinear-merging.tex`, over the shared
interface of `KolmogorovMathlib.StrongMerging.Basic`.

* `exists_sqrt_merger` and `exists_merger_tradeoff`: two `ε`-strong, `ε`-sufficient statistics
  of an `n`-bit string have a common model whose sufficiency error, total reduction costs from
  both statistics and mass loss are `O(√(n (ε + log n)))`, with point strength `O(ε + 1)`
  (Theorem `thm:main`, Proposition `prop:tradeoff`).
* `exists_strong_pair_without_common_model` and its real-tolerance form
  `exists_strong_pair_without_common_model_real`: the square-root order is sharp for
  `C log n ≤ ε ≤ n`, for an arbitrary finite candidate model (Theorem `thm:hamming-obstruction`,
  Corollary `cor:ham-sharp-range`).
* `exists_strongRobustMin_seq_unbounded_ratio` and `not_exists_strongRobustMin_total_bound`: the
  formal one-sided Question 1 of Vereshchagin–Shen §7.9 has a negative answer
  (Corollary `cor:q1-negative`).
* `setTotalC_le_of_strongRobustMin`: one-sided minimality does bound the total reduction cost
  once the minimality window is enlarged to `e + O(√(n H))` (blueprint Proposition
  `bp-upper-one-sided-minimality`).

Every statement is relative to an arbitrary optimal plain machine `V` for `C` and to the
canonical total interpreter `universalDecompressor` for `CT`.  Every constant is quantified
after `V` and before all instance data, as an explicit existential natural or real; "for all
sufficiently large `M`" is an explicit cutoff `M₀`.  The positive results are proved in
`StrongMerging.Upper`, the obstruction and Question 1 in `StrongMerging.Lower`; every theorem
here is axiom-clean.
-/

namespace Kolmogorov.StrongMerging

open Filter

/-! ### The positive merging results -/

/-- **Square-root merger.**  For an optimal plain machine `V` there is a constant `c` with the
following property.  Let `n ≥ 2`, `0 ≤ ε ≤ n`, and let `A, B` be `ε`-strong, `ε`-sufficient
statistics of a string `x` of length `n`; put `e = ⌈ε⌉`, `H = e + ⌈log₂ (n + 2)⌉` and
`S = √(n H)` (`rootScale n e`).  Then some finite model `D ∋ x` has point strength
`CT(D | x) ≤ c (e + 1)`, two-part length `C(D) + log₂ |D| ≤ C(x) + c S`, total reduction costs
`CT(D | A), CT(D | B) ≤ c S`, and mass `log₂ |D| ≥ log₂ |A| + log₂ |B| - log₂ |A ∩ B| - c S`.

`sublinear-merging.tex`, Theorem `thm:main` (blueprint target H07). -/
theorem exists_sqrt_merger (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ (n : ℕ) (ε : ℝ) (x : BitString) (A B : Finset BitString),
      IsMergingInstance V n ε x A B → ∃ D : Finset BitString, x ∈ D ∧
        pointTotalC D x ≤ c * (⌈ε⌉₊ + 1) ∧
        setC V D + Real.logb 2 D.card ≤ plainC V x + c * rootScale n ⌈ε⌉₊ ∧
        setTotalC D A ≤ c * rootScale n ⌈ε⌉₊ ∧ setTotalC D B ≤ c * rootScale n ⌈ε⌉₊ ∧
        Real.logb 2 A.card + Real.logb 2 B.card - Real.logb 2 (A ∩ B).card -
          c * rootScale n ⌈ε⌉₊ ≤ Real.logb 2 D.card :=
  Upper.exists_sqrt_merger' V hV

/-- **Quantitative merging tradeoff.**  For an optimal plain machine `V` there is a constant `c`
such that, under the hypotheses of `exists_sqrt_merger`, with `e = ⌈ε⌉` and
`H = e + ⌈log₂ (n + 2)⌉`:
* for every integer `1 ≤ R ≤ n` some finite model `D ∋ x` satisfies the tradeoff bounds
  `C(D) + log₂ |D| - C(x) ≤ c (R + H)`, `CT(D | A), CT(D | B) ≤ c (H + n H / R)` and
  `log₂ |D| ≥ log₂ |A| + log₂ |B| - log₂ |A ∩ B| - c (H + n H / R)` (`TradeoffBounds`), and
  `CT(D | x) ≤ c (e + log₂ (n + 2))`;
* for every fixed total computable rule `ρ(n, e)`, clipped to `R = min n (max 1 (ρ n e))`, some
  finite model `D ∋ x` satisfies the same tradeoff bounds, with the same `c`, together with the
  improved point bound `CT(D | x) ≤ c_ρ (e + 1)`; only `c_ρ` depends on the rule.

`sublinear-merging.tex`, Proposition `prop:tradeoff` (blueprint target H06). -/
theorem exists_merger_tradeoff (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ,
      (∀ (n : ℕ) (ε : ℝ) (x : BitString) (A B : Finset BitString),
        IsMergingInstance V n ε x A B → ∀ R : ℕ, 1 ≤ R → R ≤ n →
          ∃ D : Finset BitString, x ∈ D ∧ TradeoffBounds V n ⌈ε⌉₊ R c x A B D ∧
            pointTotalC D x ≤ c * (⌈ε⌉₊ + Real.logb 2 (n + 2))) ∧
      ∀ ρ : ℕ → ℕ → ℕ, Computable₂ ρ → ∃ cρ : ℕ,
        ∀ (n : ℕ) (ε : ℝ) (x : BitString) (A B : Finset BitString),
          IsMergingInstance V n ε x A B → ∃ D : Finset BitString, x ∈ D ∧
            TradeoffBounds V n ⌈ε⌉₊ (min n (max 1 (ρ n ⌈ε⌉₊))) c x A B D ∧
            pointTotalC D x ≤ cρ * (⌈ε⌉₊ + 1) :=
  Upper.exists_merger_tradeoff' V hV

/-- **Enlarged-window one-sided minimality.**  For an optimal plain machine `V` there are
constants `c_win, c_out > 0` with the following property.  Let `n ≥ 2`, let `0 ≤ e ≤ n` be an
integer, let `A, B` be `e`-strong, `e`-sufficient statistics of a string `x` of length `n`, and
put `S = √(n (e + ⌈log₂ (n + 2)⌉))`.  For every real `δ ≥ 0`, if `A` is strong-only robustly
minimal at tolerance `e + c_win S` with gap `δ` (`StrongRobustMin`: no `(e + c_win S)`-strong,
`(e + c_win S)`-sufficient model `F` of `x` has `C(F) ≤ C(A) - δ`), then
`CT(A | B) ≤ δ + c_out S`.  Since `A` is its own competitor, the strict cutoff of
`StrongRobustMin` can only hold when `δ > 0`.

`sublinear-merging.tex`, appendix Proposition `bp-upper-one-sided-minimality` (blueprint target
Q02). -/
theorem setTotalC_le_of_strongRobustMin (V : Map) (hV : isOptimalConditional V) :
    ∃ cwin cout : ℕ, 0 < cwin ∧ 0 < cout ∧
      ∀ (n e : ℕ) (x : BitString) (A B : Finset BitString), IsMergingInstance V n e x A B →
        ∀ δ : ℝ, 0 ≤ δ → StrongRobustMin V x A (e + cwin * rootScale n e) δ →
          setTotalC A B ≤ δ + cout * rootScale n e :=
  Upper.setTotalC_le_of_strongRobustMin' V hV

/-! ### The sharp lower bound -/

/-- **Sharp square-root obstruction to common models.**  For an optimal plain machine `V` there
are an integer `λ ≥ 1` (`lam`), a point-strength constant `c_pt` and a cutoff `M₀` such that for
every `M ≥ M₀` divisible by `2048` and every integer `E` with `λ ⌈log₂ (M + 2)⌉ ≤ E ≤ 2⁻¹⁰⁰ M`
there are a string `x` of length `n = 2M` and finite sets `A, B ∋ x` with point strengths
`CT(A | x), CT(B | x) ≤ c_pt`, two-part lengths `C(A) + log₂ |A|, C(B) + log₂ |B| ≤ C(x) + 32 E`
and `A ∩ B = {x}`, for which no finite set `D ∋ x` (with no strength or cardinality requirement)
satisfies all three of `C(D) + log₂ |D| ≤ C(x) + T`, `CT(D | A) ≤ T` and `CT(D | B) ≤ T`, where
`T = ⌊⌊√(M E)⌋ / 10⁶⌋` (`mergerBudget M E`).

`sublinear-merging.tex`, Theorem `thm:hamming-obstruction` (blueprint targets L00, L37). -/
theorem exists_strong_pair_without_common_model (V : Map) (hV : isOptimalConditional V) :
    ∃ lam cpt M₀ : ℕ, 1 ≤ lam ∧
      ∀ M : ℕ, M₀ ≤ M → 2048 ∣ M → ∀ E : ℕ, lam * headerLog M ≤ E → 2 ^ 100 * E ≤ M →
        ∃ (x : BitString) (A B : Finset BitString), x.length = 2 * M ∧
          pointTotalC A x ≤ cpt ∧ pointTotalC B x ≤ cpt ∧
          IsSufficientModel V x A (32 * E) ∧ IsSufficientModel V x B (32 * E) ∧ A ∩ B = {x} ∧
          ∀ D : Finset BitString, x ∈ D →
            ¬ (setC V D + Real.logb 2 D.card ≤ plainC V x + mergerBudget M E ∧
              setTotalC D A ≤ mergerBudget M E ∧ setTotalC D B ≤ mergerBudget M E) :=
  Lower.exists_strong_pair_without_common_model' V hV

/-- **The sharp obstruction over the full tolerance range.**  For an optimal plain machine `V`
there are constants `C, c > 0`, a point-strength constant `c_pt` and a cutoff `M₀` such that for
every `M ≥ M₀` divisible by `2048`, with `n = 2M`, and every real tolerance
`C log₂ (n + 2) ≤ ε ≤ n`, there are `ε`-strong, `ε`-sufficient models `A, B` of a string `x` of
length `n` with `A ∩ B = {x}` and point strengths `CT(A | x), CT(B | x) ≤ c_pt`, for which every
finite `D ∋ x` has `max (C(D) + log₂ |D| - C(x)) (max CT(D | A) CT(D | B)) > c √(n ε)`.

`sublinear-merging.tex`, Corollary `cor:ham-sharp-range` (blueprint target L38). -/
theorem exists_strong_pair_without_common_model_real (V : Map) (hV : isOptimalConditional V) :
    ∃ (C c : ℝ) (cpt M₀ : ℕ), 0 < C ∧ 0 < c ∧
      ∀ M : ℕ, M₀ ≤ M → 2048 ∣ M → ∀ ε : ℝ, C * Real.logb 2 (2 * M + 2) ≤ ε → ε ≤ 2 * M →
        ∃ (x : BitString) (A B : Finset BitString), x.length = 2 * M ∧
          IsStrongModel x A ε ∧ IsSufficientModel V x A ε ∧
          IsStrongModel x B ε ∧ IsSufficientModel V x B ε ∧ A ∩ B = {x} ∧
          pointTotalC A x ≤ cpt ∧ pointTotalC B x ≤ cpt ∧
          ∀ D : Finset BitString, x ∈ D →
            c * Real.sqrt (2 * M * ε) <
              max (modelScore V D x) (max (setTotalC D A) (setTotalC D B)) :=
  Lower.exists_strong_pair_without_common_model_real' V hV

/-! ### The formal Question 1 -/

/-- **Robustly minimal strong statistics need not be close: the sequence form.**  For an optimal
plain machine `V` and every fixed `c_min ≥ 0` there are a sequence `(x_j, A_j, B_j, ε_j, δ_j)`
and a constant `K` (depending on `c_min`) such that `n_j = |x_j| → ∞`, `A_j` and `B_j` are
`ε_j`-strong and `ε_j`-sufficient for `x_j`, `ε_j, δ_j ≤ K √(n_j log₂ n_j)`, `δ_j ≥ 1`, no
`(ε_j + c_min log₂ n_j)`-strong, `(ε_j + c_min log₂ n_j)`-sufficient model `A'` of `x_j` has
`C(A') ≤ C(A_j) - δ_j` (`StrongRobustMin`), and nevertheless
`CT(A_j | B_j) / (ε_j + δ_j + log₂ n_j) → ∞`.

`sublinear-merging.tex`, Corollary `cor:q1-negative` (blueprint target L42). -/
theorem exists_strongRobustMin_seq_unbounded_ratio (V : Map) (hV : isOptimalConditional V)
    (cmin : ℝ) (hcmin : 0 ≤ cmin) :
    ∃ (x : ℕ → BitString) (A B : ℕ → Finset BitString) (ε δ : ℕ → ℝ) (K : ℝ),
      Tendsto (fun j => (x j).length) atTop atTop ∧
      (∀ j, IsStrongModel (x j) (A j) (ε j) ∧ IsSufficientModel V (x j) (A j) (ε j) ∧
        IsStrongModel (x j) (B j) (ε j) ∧ IsSufficientModel V (x j) (B j) (ε j)) ∧
      (∀ j, ε j ≤ K * Real.sqrt ((x j).length * Real.logb 2 (x j).length) ∧
        δ j ≤ K * Real.sqrt ((x j).length * Real.logb 2 (x j).length) ∧ 1 ≤ δ j) ∧
      (∀ j, StrongRobustMin V (x j) (A j) (ε j + cmin * Real.logb 2 (x j).length) (δ j)) ∧
      Tendsto (fun j => setTotalC (A j) (B j) / (ε j + δ j + Real.logb 2 (x j).length))
        atTop atTop :=
  Lower.exists_strongRobustMin_seq_unbounded_ratio' V hV cmin hcmin

/-- **The formal Question 1 has a negative answer.**  For an optimal plain machine `V` there are
no constants `c_min ≥ 0`, `K_out ≥ 0` and `c₀` such that for all reals `ε ≥ 0` and `δ ≥ 1`, every
string `x` of length `n ≥ 2` and all `ε`-strong, `ε`-sufficient statistics `A, B` of `x`: if no
`(ε + c_min log₂ n)`-strong, `(ε + c_min log₂ n)`-sufficient model `A'` of `x` has
`C(A') ≤ C(A) - δ` (`StrongRobustMin`), then `CT(A | B) ≤ K_out (ε + δ + log₂ n) + c₀`.
The refuted implication is restricted to the source's parameter domain, so this negation cannot hold
merely because of a degenerate instance.

`sublinear-merging.tex`, Corollary `cor:q1-negative`, its concluding sentence; Vereshchagin–Shen,
*Algorithmic statistics: forty years later*, §7.9, Question 1. -/
theorem not_exists_strongRobustMin_total_bound (V : Map) (hV : isOptimalConditional V) :
    ¬ ∃ cmin Kout c₀ : ℝ, 0 ≤ cmin ∧ 0 ≤ Kout ∧
      ∀ (ε δ : ℝ) (x : BitString) (A B : Finset BitString), 0 ≤ ε → 1 ≤ δ → 2 ≤ x.length →
      IsStrongModel x A ε → IsSufficientModel V x A ε →
      IsStrongModel x B ε → IsSufficientModel V x B ε →
      StrongRobustMin V x A (ε + cmin * Real.logb 2 x.length) δ →
        setTotalC A B ≤ Kout * (ε + δ + Real.logb 2 x.length) + c₀ :=
  Lower.not_exists_strongRobustMin_total_bound' V hV

end Kolmogorov.StrongMerging
