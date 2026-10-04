/-
Copyright (c) 2026 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.StoppingComplexity.GeneralCriterion
import KolmogorovMathlib.StoppingComplexity.Divergence

/-!
# The main theorem: the stopping gap exceeds `log m + log log log m` infinitely often

Blueprint 01 F0 (Target MAIN, the T3c endpoint) and 04 §6 (Theorem E and its consequences).

The discount `F n = L(max 16 n) + L(L(L(max 16 n)))` of 04 Definition F (`discountF`,
`L = Nat.clog 2`) is admissible: computable and nondecreasing (module `CeilLog`), R1 from S2 and
F-double (`F(E_i) - F(E_{i-1}) ≤ 2 ≤ E_{i-1} - 1`), SHIFT with the explicit constant `D_a = 2a`
(F-shift), and DIV from the fully discrete triple-block divergence proof (module `Divergence`).
Theorem E′ for `F` together with the comparison `F(n) ≥ log₂ n + log₂ log₂ log₂ n` for `n ≥ 16`
gives Theorem E (`m(z) > T` for every `T ≥ 16`) and Target MAIN in the F0 form
(`m(z) ≥ max(16, T)`).

Consequences 1–3 of 04 §6 are stated as well: no constant `d` bounds `g(z) - log₂ m(z)`, nor
`g(z) - log₂ m(z) - log₂ log₂ log₂ m(z)`, on the domain `m(z) > 16`, and a sequence `z_q` with
`m(z_q) > q + 16` has excess greater than `q`. Consequence 4 (the proof does not identify the
optimal second-order term) is a remark about scope, not a theorem, and is not stated.

Every statement is about the fixed universal stopping machine and has no hypothesis.
-/

namespace Kolmogorov

/-- The discount `F n = L(max 16 n) + L(L(L(max 16 n)))` is admissible: total computable and
nondecreasing (04 §2), R1 (from S2 and F-double, `F(E_i) - F(E_{i-1}) ≤ 2 ≤ E_{i-1} - 1`), SHIFT
with the explicit constant `D_a = 2a` (F-shift) and DIV (Corollary F-diverges). A theorem, not a
hypothesis of the main theorem. Blueprint 04 Theorem E (proof: `F` satisfies MONO, R1, SHIFT,
DIV). -/
theorem discountF_isAdmissible : IsAdmissibleDiscount discountF := by
  refine ⟨discountF_computable, discountF_mono, fun i hi => ?_,
    fun a => ⟨2 * a, fun n => discountF_add_le n a⟩, discountF_hasDivergentSums⟩
  have h16 : 16 ≤ expSchedule (i - 1) := by
    have := expSchedule_ge (i - 1)
    omega
  have hle : expSchedule (i - 1) ≤ expSchedule i := expSchedule_strictMono.monotone (by omega)
  have h2 := discountF_le_of_le_two_mul h16 hle (expSchedule_le_two_mul_pred hi)
  omega

/-- For `x ≥ 16` the three iterated binary logarithms are at least `4`, `2` and `1`
(`log₂ 16 = 4`, `log₂ 4 = 2`, `log₂ 2 = 1`, and `log₂` is increasing); in particular every
logarithm below has a positive argument. Blueprint 04 Theorem E ("every logarithm has a positive
argument on this domain") and §6 Consequences ("`log log log m ≥ 1` when `m ≥ 16`"). -/
private theorem iteratedLogb_bounds {x : ℝ} (hx : 16 ≤ x) :
    4 ≤ Real.logb 2 x ∧ 2 ≤ Real.logb 2 (Real.logb 2 x) ∧
      1 ≤ Real.logb 2 (Real.logb 2 (Real.logb 2 x)) := by
  have h1 : 4 ≤ Real.logb 2 x := by
    calc (4 : ℝ) = Real.logb 2 (2 ^ 4) := by
          rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
          norm_num
      _ ≤ Real.logb 2 x := Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by linarith)
  have h2 : 2 ≤ Real.logb 2 (Real.logb 2 x) := by
    calc (2 : ℝ) = Real.logb 2 (2 ^ 2) := by
          rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
          norm_num
      _ ≤ Real.logb 2 (Real.logb 2 x) :=
          Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by linarith)
  refine ⟨h1, h2, ?_⟩
  calc (1 : ℝ) = Real.logb 2 2 := (Real.logb_self_eq_one (by norm_num)).symm
    _ ≤ Real.logb 2 (Real.logb 2 (Real.logb 2 x)) :=
        Real.logb_le_logb_of_le (by norm_num) (by norm_num) h2

/-- The comparison function `log₂ x + log₂ log₂ log₂ x` is nondecreasing on `x ≥ 16`: three
applications of the monotonicity of `log₂`, each with a positive argument. It carries the lower
bound `F(n) ≥ log₂ n + log₂ log₂ log₂ n` from `n = ⌈m⌉` down to `m`.
Blueprint 04 Theorem E (`F(n) ≥ log n + log log log n ≥ log m(z) + log log log m(z)`). -/
private theorem logb_add_logb_logb_logb_le_of_le {x y : ℝ} (hx : 16 ≤ x) (hxy : x ≤ y) :
    Real.logb 2 x + Real.logb 2 (Real.logb 2 (Real.logb 2 x)) ≤
      Real.logb 2 y + Real.logb 2 (Real.logb 2 (Real.logb 2 y)) := by
  obtain ⟨h1, h2, -⟩ := iteratedLogb_bounds hx
  have hl1 : Real.logb 2 x ≤ Real.logb 2 y :=
    Real.logb_le_logb_of_le (by norm_num) (by linarith) hxy
  have hl2 : Real.logb 2 (Real.logb 2 x) ≤ Real.logb 2 (Real.logb 2 y) :=
    Real.logb_le_logb_of_le (by norm_num) (by linarith) hl1
  have hl3 : Real.logb 2 (Real.logb 2 (Real.logb 2 x)) ≤
      Real.logb 2 (Real.logb 2 (Real.logb 2 y)) :=
    Real.logb_le_logb_of_le (by norm_num) (by linarith) hl2
  linarith

/-- **Theorem E** (strengthened logarithmic lower bound, strict cutoff): for every natural `q` and
every real `T ≥ 16` there is a string `z` with mass depth `m(z) > T` and stopping gap
`g(z) > log₂ m(z) + log₂ log₂ log₂ m(z) + q`. Theorem E′ for the admissible discount `F`, with
`F(⌈m⌉) ≥ log₂ m + log₂ log₂ log₂ m` on `m > 16`. Target MAIN is its F0 form.
Blueprint 04 Theorem E. -/
theorem stoppingGap_iteratedLog_lowerBound_strict (q : ℕ) {T : ℝ} (hT : 16 ≤ T) :
    ∃ z : BitString, T < massDepth z ∧
      Real.logb 2 (massDepth z) + Real.logb 2 (Real.logb 2 (Real.logb 2 (massDepth z))) + q <
        stoppingGap z := by
  obtain ⟨z, hm, hg⟩ := stoppingGap_exceeds_discount discountF discountF_isAdmissible q
    (by linarith : (0 : ℝ) ≤ T)
  have h16 : (16 : ℝ) ≤ massDepth z := by linarith
  have hceil : massDepth z ≤ ⌈massDepth z⌉₊ := Nat.le_ceil _
  have hn16 : 16 ≤ ⌈massDepth z⌉₊ := by exact_mod_cast h16.trans hceil
  have hF := logb_add_logb_logb_logb_le_discountF hn16
  have hmono := logb_add_logb_logb_logb_le_of_le h16 hceil
  exact ⟨z, hm, by linarith⟩

/-- **Target MAIN** (the T3c endpoint): for every natural `c` and every real `T` there is a string
`z` with mass depth `m(z) ≥ max(16, T)` and stopping gap
`g(z) > log₂ m(z) + log₂ log₂ log₂ m(z) + c`. Stated unconditionally about the fixed universal
machine; the domain `m(z) ≥ 16` keeps every logarithm's argument positive, and the arbitrary
cutoff `T` gives arbitrarily large mass depths, hence infinitely many strings. Theorem E at the
cutoff `max(16, T)`. Blueprint F0 Target MAIN. -/
theorem stoppingGap_iteratedLog_lowerBound (c : ℕ) (T : ℝ) :
    ∃ z : BitString, max 16 T ≤ massDepth z ∧
      Real.logb 2 (massDepth z) + Real.logb 2 (Real.logb 2 (Real.logb 2 (massDepth z))) + c <
        stoppingGap z := by
  have ⟨z, h1, h2⟩ := stoppingGap_iteratedLog_lowerBound_strict c (T := max 16 T) (le_max_left 16 T)
  exact ⟨z, le_of_lt h1, h2⟩

/-- Consequence 1 of Theorem E: there is no real constant `d` such that
`g(z) ≤ log₂ m(z) + d` for every string `z` with `m(z) > 16`.
Blueprint 04 §6, Consequences and exact scope (1). -/
theorem not_exists_const_log_bound :
    ¬ ∃ d : ℝ, ∀ z : BitString, 16 < massDepth z →
      stoppingGap z ≤ Real.logb 2 (massDepth z) + d := by
  rintro ⟨d, hd⟩
  obtain ⟨q, hq⟩ := exists_nat_gt d
  obtain ⟨z, hm, hg⟩ := stoppingGap_iteratedLog_lowerBound_strict q (le_refl (16 : ℝ))
  have h3 := (iteratedLogb_bounds hm.le).2.2
  have := hd z hm
  linarith

/-- Consequence 2 of Theorem E: there is no real constant `d` such that
`g(z) ≤ log₂ m(z) + log₂ log₂ log₂ m(z) + d` for every string `z` with `m(z) > 16`.
Blueprint 04 §6, Consequences and exact scope (2). -/
theorem not_exists_const_iteratedLog_bound :
    ¬ ∃ d : ℝ, ∀ z : BitString, 16 < massDepth z →
      stoppingGap z ≤
        Real.logb 2 (massDepth z) + Real.logb 2 (Real.logb 2 (Real.logb 2 (massDepth z))) + d := by
  rintro ⟨d, hd⟩
  obtain ⟨q, hq⟩ := exists_nat_gt d
  obtain ⟨z, hm, hg⟩ := stoppingGap_iteratedLog_lowerBound_strict q (le_refl (16 : ℝ))
  have := hd z hm
  linarith

/-- Consequence 3 of Theorem E: there is a sequence of strings `z_q` such that, for every natural
`q`, `m(z_q) > q + 16` and the excess of `g(z_q)` over `log₂ m(z_q) + log₂ log₂ log₂ m(z_q)` is
greater than `q` (an unbounded additive excess along a sequence). The sequence is obtained by
ordinary choice from Theorem E at the cutoffs `q + 16`; no algorithm finding it is claimed.
Blueprint 04 §6, Consequences and exact scope (3). -/
theorem exists_seq_massDepth_gt_excess :
    ∃ z : ℕ → BitString, ∀ q : ℕ, (q : ℝ) + 16 < massDepth (z q) ∧
      Real.logb 2 (massDepth (z q)) + Real.logb 2 (Real.logb 2 (Real.logb 2 (massDepth (z q)))) +
        q < stoppingGap (z q) := by
  choose z hz using fun q : ℕ => stoppingGap_iteratedLog_lowerBound_strict q (T := (q : ℝ) + 16)
    (by linarith [Nat.cast_nonneg q (α := ℝ)])
  exact ⟨z, hz⟩

end Kolmogorov
