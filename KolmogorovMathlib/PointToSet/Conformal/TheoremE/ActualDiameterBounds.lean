/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.Conformal.TheoremE.FactorialPackingGeometry

/-!
# Packing estimates for the factorial product

The factorial ultrametric product has vanishing actual-diameter packing premeasure at every
positive exponent. Disjoint balls are counted by their cylinder depths, and the resulting
factorial series is bounded by a geometric series. The module also constructs finite covers
used by `ActualDiameterCounterexample` to compare this vanishing dimension with specified-radius
packing dimension (`conf:packing-diameter-counterexample`).
-/

namespace Kolmogorov.PointToSet

open Filter
open scoped Topology ENNReal Computability

variable {X : Type*} [MetricSpace X]

/-- Each branching number of the factorial product is a power of two whose exponent is the
corresponding factorial (with exponent `1` at index `0`). -/
private lemma factorialBranching_eq_pow (j : ℕ) :
    (factorialBranching j : ℝ) = (2 : ℝ) ^ (if j = 0 then 1 else j.factorial : ℕ) := by
  dsimp [factorialBranching]
  split_ifs with h
  · norm_num
  · push_cast; rfl

/-- The partial sums $\sum_{j<m+2} e_j$ of the branching exponents are at most
$2\,(m+1)!$. -/
private lemma sum_factorial_le_twice_factorial (m : ℕ) :
    (∑ j ∈ Finset.range (m + 2), (if j = 0 then 1 else j.factorial : ℕ)) ≤
      2 * (m + 1).factorial := by
  induction m with | zero => ?_ | succ m ih => ?_
  · norm_num [Finset.sum_range_succ]
  · have h_range : m + 1 + 2 = m + 2 + 1 := by omega
    rw [h_range, Finset.sum_range_succ]
    have h_if : (if m + 2 = 0 then 1 else (m + 2).factorial : ℕ) = (m + 2).factorial := by
      simp
    have h_fact : (m + 2).factorial = (m + 2) * (m + 1).factorial := rfl
    rw [h_if, h_fact]
    have hm : 2 ≤ m + 2 := by omega
    nlinarith

/-- The exponent $L_n - s n!$ is eventually bounded by $-\frac{s}{2} n$. -/
private lemma factorial_mass_exponent_eventually_le
    (s : ℝ) (hs : 0 < s) :
    ∀ᶠ n : ℕ in Filter.atTop, ((∑ j ∈ Finset.range n, (if j = 0 then 1 else j.factorial : ℕ)) : ℝ) -
        s * (if n = 0 then 1 else n.factorial : ℝ) ≤ - (s / 2) * n := by
  have h1 := sum_factorial_le_twice_factorial
  rw [Filter.eventually_atTop]
  refine ⟨⌈4 / s⌉₊ + 2, fun n hn ↦ ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hm : 4 / s ≤ (m : ℝ) := by
    have h_ceil : ⌈4 / s⌉₊ ≤ m := by omega
    have hm1 := Nat.le_ceil (4 / s)
    exact_mod_cast le_trans hm1 (Nat.cast_le.mpr h_ceil)
  have hsm : 4 ≤ s * m := (div_le_iff₀' hs).mp hm
  have hF1 : 1 ≤ (m + 1).factorial := Nat.factorial_pos _
  have hF2 : (m + 2).factorial = (m + 2) * (m + 1).factorial := Nat.factorial_succ _
  have hn0 : m + 2 ≠ 0 := by omega
  have H_eq_goal : ((∑ j ∈ Finset.range (m + 2), (if j = 0 then 1 else j.factorial : ℕ)) : ℝ) - s *
      (if m + 2 = 0 then 1 else (m + 2).factorial : ℝ) = ((∑ j ∈ Finset.range (m + 2), (if j = 0
      then 1 else j.factorial : ℕ)) : ℝ) - s * (m + 2).factorial := by
    simp only [hn0, ite_false]
  rw [H_eq_goal]
  have hL := h1 m
  have hL2 : ((∑ j ∈ Finset.range (m + 2), (if j = 0 then 1 else j.factorial : ℕ)) : ℝ) ≤ 2 * ((m +
      1).factorial : ℝ) := by exact_mod_cast hL
  have H : ((∑ j ∈ Finset.range (m + 2), (if j = 0 then 1 else j.factorial : ℕ)) : ℝ) - s * (m +
      2).factorial ≤ 2 * ((m + 1).factorial : ℝ) - s * (m + 2) * ((m + 1).factorial : ℝ) := by
    calc
      _ ≤ 2 * ((m + 1).factorial : ℝ) - s * (m + 2).factorial := sub_le_sub_right hL2 _
      _ = 2 * ((m + 1).factorial : ℝ) - s * (m + 2) * ((m + 1).factorial : ℝ) := by
        push_cast [hF2]
        ring
  have H2 : 2 * ((m + 1).factorial : ℝ) - s * (m + 2) * ((m + 1).factorial : ℝ) = 2 - s * (m + 2) +
      (((m + 1).factorial : ℝ) - 1) * (2 - s * (m + 2)) := by ring
  have H3 : 2 - s * (m + 2) + (((m + 1).factorial : ℝ) - 1) * (2 - s * (m + 2)) ≤ 2 - s * (m + 2) :=
      by
    have hF1' : 0 ≤ ((m + 1).factorial : ℝ) - 1 := by
      have : (1 : ℝ) ≤ ((m + 1).factorial : ℝ) := by exact_mod_cast hF1
      linarith
    have ht2' : 2 - s * (m + 2) ≤ 0 := by linarith
    nlinarith
  have H4 : 2 - s * (m + 2) ≤ - (s / 2) * (m + 2) := by linarith
  have H5 : 2 * ((m + 1).factorial : ℝ) - s * (m + 2) * ((m + 1).factorial : ℝ) ≤ - (s / 2) * (m +
      2) := by
    calc
      _ = 2 - s * (m + 2) + (((m + 1).factorial : ℝ) - 1) * (2 - s * (m + 2)) := H2
      _ ≤ 2 - s * (m + 2) := H3
      _ ≤ - (s / 2) * (m + 2) := H4
  have H_final := H.trans H5
  push_cast
  exact_mod_cast H_final

/-- The product in $\mathbb{R}$ is bounded by $(2^{-s/2})^n$. -/
private lemma factorial_mass_eventually_le_geometric
    (s : ℝ) (hs : 0 < s) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (Finset.prod (Finset.range n) (fun j ↦ (factorialBranching j : ℝ))) *
        (factorialScale n) ^ s
      ≤ (2 ^ (-s / 2)) ^ n := by
  have h_exponent := factorial_mass_exponent_eventually_le s hs
  filter_upwards [h_exponent, Filter.eventually_ge_atTop 1] with n hn1 hn2
  have hn_ne_zero : n ≠ 0 := by linarith
  have Hprod : (Finset.prod (Finset.range n) (fun j ↦ (factorialBranching j : ℝ))) = (2:ℝ) ^ ((∑ j ∈
      Finset.range n, (if j = 0 then 1 else j.factorial : ℕ)) : ℝ) := by
    calc
      _ = Finset.prod (Finset.range n) (fun j ↦ (2 : ℝ) ^ (if j = 0 then 1 else j.factorial : ℕ)) :=
          by
        exact Finset.prod_congr rfl fun x _ ↦ factorialBranching_eq_pow x
      _ = (2 : ℝ) ^ (∑ j ∈ Finset.range n, (if j = 0 then 1 else j.factorial : ℕ) : ℕ) := by
        exact Finset.prod_pow_eq_pow_sum (Finset.range n) (fun j ↦ (if j = 0 then 1 else j.factorial
            : ℕ)) (2:ℝ)
      _ = (2 : ℝ) ^ ((∑ j ∈ Finset.range n, (if j = 0 then 1 else j.factorial : ℕ)) : ℝ) := by
        rw [← Real.rpow_natCast]
        congr 1
        push_cast
        rfl
  have Hrn : (factorialScale n) = (2:ℝ) ^ (-(n.factorial : ℝ)) := by
    simp only [factorialScale, hn_ne_zero, ↓reduceIte, one_div, inv_pow,
      Real.rpow_neg zero_le_two, Real.rpow_natCast]
  have Hrn_pow : (factorialScale n) ^ s = (2:ℝ) ^ (-s * (n.factorial : ℝ)) := by
    rw [Hrn]
    have h5 : ((2:ℝ) ^ (-(n.factorial : ℝ))) ^ s = (2:ℝ) ^ (-(n.factorial : ℝ) * s) := by
      exact (Real.rpow_mul zero_le_two (-(n.factorial : ℝ)) s).symm
    rw [h5]
    have h6 : -(n.factorial : ℝ) * s = - s * (n.factorial : ℝ) := by ring
    rw [h6]
  have Hrhs : ((2:ℝ) ^ (-s / 2)) ^ n = (2:ℝ) ^ (- (s / 2) * (n : ℝ)) := by
    have h6 : ((2:ℝ) ^ (-s / 2)) ^ n = ((2:ℝ) ^ (-s / 2)) ^ (n : ℝ) := by
      exact (Real.rpow_natCast ((2:ℝ) ^ (-s / 2)) n).symm
    rw [h6]
    have h7 : ((2:ℝ) ^ (-s / 2)) ^ (n : ℝ) = (2:ℝ) ^ (- (s / 2) * (n : ℝ)) := by
      have h8 : (-s / 2) * n = - (s / 2) * n := by ring
      rw [← h8]
      exact (Real.rpow_mul zero_le_two (-s / 2) (n : ℝ)).symm
    rw [h7]
  rw [Hprod, Hrn_pow, Hrhs, ← Real.rpow_add zero_lt_two]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have hn_fact_eq : (if n = 0 then 1 else n.factorial : ℝ) = (n.factorial : ℝ) := by
    simp [hn_ne_zero]
  rw [hn_fact_eq] at hn1
  linarith [hn1]

/-- Conversion from $\mathbb{R}$ to $\mathbb{R}_{\ge0}^\infty$. -/
private lemma ennreal_factorial_mass_le_of_real_bound
    {n : ℕ} (s : ℝ) (hs : 0 < s)
    (h_bound : (Finset.prod (Finset.range n) (fun j ↦ (factorialBranching j : ℝ))) *
        (factorialScale n) ^ s ≤ (2 ^ (-s / 2)) ^ n) :
    (Finset.prod (Finset.range n) (fun j ↦ (factorialBranching j : ENNReal))) *
      (ENNReal.ofReal (factorialScale n) ^ s) ≤ (ENNReal.ofReal (2 ^ (-s / 2))) ^ n := by
  have hr : 0 ≤ factorialScale n := by
    dsimp [factorialScale]
    split_ifs <;> positivity
  have h_prod : (Finset.prod (Finset.range n) (fun j ↦ (factorialBranching j : ENNReal))) =
      ENNReal.ofReal (Finset.prod (Finset.range n) (fun j ↦ (factorialBranching j : ℝ))) := by
    rw [ENNReal.ofReal_prod_of_nonneg]
    · apply Finset.prod_congr rfl
      intro j _
      rw [ENNReal.ofReal_natCast]
    · intro j _
      positivity
  have h_pow1 : ENNReal.ofReal (factorialScale n) ^ s = ENNReal.ofReal (factorialScale n ^ s) := by
    rw [ENNReal.ofReal_rpow_of_nonneg hr hs.le]
  have h_pow2 : ENNReal.ofReal (2 ^ (-s / 2)) ^ n = ENNReal.ofReal ((2 ^ (-s / 2)) ^ n) := by
    rw [← ENNReal.ofReal_pow (by positivity)]
  rw [h_prod, h_pow1, h_pow2]
  have h_mul : ENNReal.ofReal (Finset.prod (Finset.range n) (fun j ↦ (factorialBranching j : ℝ))) *
      ENNReal.ofReal (factorialScale n ^ s) = ENNReal.ofReal (Finset.prod (Finset.range n) (fun j ↦
      (factorialBranching j : ℝ)) * factorialScale n ^ s) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
  rw [h_mul]
  exact ENNReal.ofReal_le_ofReal h_bound

/-- The sequence $N_n r_n^s$ is eventually bounded by the geometric sequence $(2^{-s/2})^n$. -/
private lemma ennreal_factorial_mass_eventually_le_geometric
    (s : ℝ) (hs : 0 < s) :
    ∀ᶠ n in Filter.atTop, (Finset.prod (Finset.range n) (fun j ↦ (factorialBranching j : ENNReal)))
        *
      (ENNReal.ofReal (factorialScale n) ^ s) ≤ (ENNReal.ofReal (2 ^ (-s / 2))) ^ n := by
  have h3 := factorial_mass_eventually_le_geometric s hs
  filter_upwards [h3] with n hn
  exact ennreal_factorial_mass_le_of_real_bound s hs hn

/-- The geometric series $(2^{-s/2})^n$ has a finite sum in $\mathbb{R}_{\ge 0}^{\infty}$ since its
ratio is strictly less than 1. -/
private lemma tsum_rpow_geometric_ne_top
    (s : ℝ) (hs : 0 < s) :
    ∑' n : ℕ, (ENNReal.ofReal (2 ^ (-s / 2))) ^ n ≠ ⊤ := by
  have hr : ENNReal.ofReal ((2:ℝ) ^ (-s / 2)) < 1 :=
    ENNReal.ofReal_lt_one.2 (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))
  rw [ENNReal.tsum_geometric]
  exact ENNReal.inv_ne_top.2 (tsub_pos_of_lt hr).ne'

/-- The series $\sum N_n r_n^s$ has a finite sum since its terms are eventually bounded by a
summable geometric sequence. -/
private lemma tsum_factorial_mass_ne_top
    (s : ℝ) (hs : 0 < s) :
    ∑' n : ℕ, (Finset.prod (Finset.range n) (fun j ↦ (factorialBranching j : ENNReal))) *
      (ENNReal.ofReal (factorialScale n) ^ s) ≠ ⊤ := by
  have h_bound := ennreal_factorial_mass_eventually_le_geometric s hs
  have h_geom := tsum_rpow_geometric_ne_top s hs
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 h_bound
  let f : ℕ → ENNReal := fun n ↦
    (Finset.prod (Finset.range n) (fun j ↦ (factorialBranching j : ENNReal))) *
      (ENNReal.ofReal (factorialScale n) ^ s)
  let g : ℕ → ENNReal := fun n ↦ (ENNReal.ofReal (2 ^ (-s / 2))) ^ n
  have hfin : ∀ n, f n ≠ ⊤ := fun n ↦
    ENNReal.mul_ne_top
      (ENNReal.prod_ne_top (fun j _ ↦ ENNReal.natCast_ne_top _))
      (ENNReal.rpow_ne_top_of_nonneg hs.le ENNReal.ofReal_ne_top)
  have hsplit : ∑' n, f n = (∑ n ∈ Finset.range N, f n) + ∑' k, f (k + N) :=
    (Summable.sum_add_tsum_nat_add' (k := N) ENNReal.summable).symm
  have h1 : ∑ n ∈ Finset.range N, f n ≠ ⊤ :=
    (ENNReal.sum_lt_top.2 fun n _ ↦ (hfin n).lt_top).ne
  have h2 : ∑' k, f (k + N) ≤ ∑' k, g (k + N) :=
    ENNReal.tsum_le_tsum fun k ↦ hN _ (Nat.le_add_left N k)
  have h3 : ∑' k, g (k + N) ≤ ∑' n, g n :=
    ENNReal.tsum_comp_le_tsum_of_injective (add_left_injective N) g
  change ∑' n, f n ≠ ⊤
  rw [hsplit]
  exact ENNReal.add_ne_top.2 ⟨h1, (lt_of_le_of_lt (h2.trans h3) h_geom.lt_top).ne⟩

/-- The tail of a sequence can be rewritten as a shifted sum. -/
private lemma tsum_ite_le_eq_tsum_add
    (f : ℕ → ENNReal) (M : ℕ) :
    (∑' n : ℕ, if M ≤ n then f n else 0) = ∑' k : ℕ, f (k + M) := by
  have H : (fun n ↦ if M ≤ n then f n else 0) = fun n ↦ {n | M ≤ n}.indicator f n := by
    ext n
    simp [Set.indicator_apply]
  rw [H, ← tsum_subtype {n | M ≤ n} f]
  let e : ℕ ≃ {n // M ≤ n} :=
    { toFun := fun k ↦ ⟨k + M, Nat.le_add_left M k⟩,
      invFun := fun ⟨n, hn⟩ ↦ n - M,
      left_inv := fun k ↦ Nat.add_sub_cancel k M,
      right_inv := fun ⟨n, hn⟩ ↦ Subtype.ext (Nat.sub_add_cancel hn) }
  have H2 : (∑' (x : {n | M ≤ n}), f ↑x) = ∑' k : ℕ, f (e k).val := (Equiv.tsum_eq e (fun n ↦ f
      n.val)).symm
  rw [H2]
  rfl

/-- The tail series tends to zero. -/
private lemma factorial_mass_tail_tendsto_zero
    (s : ℝ) (hs : 0 < s) :
    Tendsto (fun M : ℕ ↦ ∑' n : ℕ, if M ≤ n then
      (Finset.prod (Finset.range n) (fun j ↦ (factorialBranching j : ENNReal))) *
        (ENNReal.ofReal (factorialScale n) ^ s)
      else 0) atTop (𝓝 0) := by
  have h_tail : ∀ M, (∑' n : ℕ, if M ≤ n then (Finset.prod (Finset.range n) (fun j ↦
      (factorialBranching j : ENNReal))) * (ENNReal.ofReal (factorialScale n) ^ s) else 0) = ∑' k :
      ℕ, (fun n ↦ (Finset.prod (Finset.range n) (fun j ↦ (factorialBranching j : ENNReal))) *
      (ENNReal.ofReal (factorialScale n) ^ s)) (k + M) := by
    intro M
    exact tsum_ite_le_eq_tsum_add (fun n ↦ (Finset.prod (Finset.range n) (fun j ↦
        (factorialBranching j : ENNReal))) * (ENNReal.ofReal (factorialScale n) ^ s)) M
  simp_rw [h_tail]
  exact ENNReal.tendsto_sum_nat_add _ (tsum_factorial_mass_ne_top s hs)

/-- A set of zero actual-diameter packing premeasure has zero packing outer measure. -/
private lemma actualDiameterPackingOuterMeasure_eq_zero_of_premeasure
    {X : Type} [MetricSpace X] {Z : Set X} {s : ℝ}
    (h : actualDiameterPackingPremeasure Z s = 0)
    (h_empty : actualDiameterPackingPremeasure (∅ : Set X) s = 0) :
    actualDiameterPackingOuterMeasure Z s = 0 := by
  rw [actualDiameterPackingOuterMeasure]
  apply nonpos_iff_eq_zero.mp
  have h_cov : Z ⊆ ⋃ (j : ℕ), if j = 0 then Z else ∅ := by
    intro x hx
    simp only [Set.mem_iUnion]
    use 0
    simp [hx]
  let Y : ℕ → Set X := fun j ↦ if j = 0 then Z else ∅
  have h1 : (⨅ (Y' : ℕ → Set X), ⨅ (_ : Z ⊆ ⋃ j, Y' j), ∑' j, actualDiameterPackingPremeasure (Y' j)
      s) ≤
         (⨅ (_ : Z ⊆ ⋃ j, Y j), ∑' j, actualDiameterPackingPremeasure (Y j) s) :=
    iInf_le (fun (Y' : ℕ → Set X) ↦ ⨅ (_ : Z ⊆ ⋃ j, Y' j), ∑' j, actualDiameterPackingPremeasure (Y'
        j) s) Y
  apply le_trans h1
  have h2 : (⨅ (_ : Z ⊆ ⋃ j, Y j), ∑' j, actualDiameterPackingPremeasure (Y j) s) ≤
            (∑' j, actualDiameterPackingPremeasure (Y j) s) :=
    iInf_le (fun (_ : Z ⊆ ⋃ j, Y j) ↦ ∑' j, actualDiameterPackingPremeasure (Y j) s) h_cov
  apply le_trans h2
  have heq : (fun (j : ℕ) ↦ actualDiameterPackingPremeasure (Y j) s) =
        (fun (j : ℕ) ↦ if j = 0 then (0 : ENNReal) else 0) := by
    ext j
    dsimp [Y]
    split_ifs with hj
    · exact h
    · exact h_empty
  rw [heq]
  have h_sum : (∑' (j : ℕ), (if j = 0 then (0 : ENNReal) else 0)) = 0 := by
    have : (fun (j : ℕ) ↦ (if j = 0 then (0 : ENNReal) else 0)) = (fun j ↦ 0) := by
      ext j
      split_ifs <;> rfl
    rw [this, tsum_zero]
  exact h_sum.le

/-- Premeasure of empty set is zero. -/
private lemma actualDiameterPackingPremeasure_empty (X : Type) [MetricSpace X] (s : ℝ) :
    actualDiameterPackingPremeasure (∅ : Set X) s = 0 := by
  rw [actualDiameterPackingPremeasure]
  apply nonpos_iff_eq_zero.mp
  have h1 : (⨅ δ : ℝ, ⨅ (_ : 0 < δ), actualDiameterPackingContent (∅ : Set X) s δ) ≤
             ⨅ (_ : 0 < (1:ℝ)), actualDiameterPackingContent (∅ : Set X) s 1 := iInf_le _ 1
  apply le_trans h1
  have h2 : (⨅ (_ : 0 < (1:ℝ)), actualDiameterPackingContent (∅ : Set X) s 1) ≤
             actualDiameterPackingContent (∅ : Set X) s 1 := iInf_le _ zero_lt_one
  apply le_trans h2
  rw [actualDiameterPackingContent]
  have h3 : ∀ F : Set (X × ℝ), IsDisjointMetricBallFamily ∅ F → F = ∅ := by
    intro F hF
    ext x
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hx
    have := hF.2.1 x hx
    exact this.1
  apply iSup_le
  intro F
  apply iSup_le
  intro hF
  have hF_empty := h3 F hF.1
  have : F = ∅ := hF_empty
  subst this
  have h_sum : (∑' (a : (∅ : Set (X × ℝ))), Metric.ediam (Metric.ball (a.val.1) (a.val.2)) ^ s) = 0
      := by apply tsum_empty
  exact h_sum.le

/-- A set whose actual-diameter packing premeasure vanishes at every exponent `s > 0` has
packing dimension zero. -/
private lemma actualDiameterPackingDimension_eq_zero_of_premeasure
    {X : Type} [MetricSpace X] {Z : Set X}
    (h : ∀ s > 0, actualDiameterPackingPremeasure Z s = 0) :
    actualDiameterPackingDimension Z = 0 := by
  rw [actualDiameterPackingDimension]
  apply nonpos_iff_eq_zero.mp
  have h_le : ∀ (ε : ℝ), 0 < ε → (⨅ s : ℝ, ⨅ (_ : 0 ≤ s), ⨅ (_ : actualDiameterPackingOuterMeasure Z
      s = 0), ENNReal.ofReal s) ≤ ENNReal.ofReal ε := by
    intro ε hε
    have h1 : (⨅ s : ℝ, ⨅ (_ : 0 ≤ s), ⨅ (_ : actualDiameterPackingOuterMeasure Z s = 0),
        ENNReal.ofReal s) ≤
              (⨅ (_ : 0 ≤ ε), ⨅ (_ : actualDiameterPackingOuterMeasure Z ε = 0), ENNReal.ofReal ε)
                  :=
      iInf_le _ ε
    apply le_trans h1
    have h2 : (⨅ (_ : 0 ≤ ε), ⨅ (_ : actualDiameterPackingOuterMeasure Z ε = 0), ENNReal.ofReal ε) ≤
              (⨅ (_ : actualDiameterPackingOuterMeasure Z ε = 0), ENNReal.ofReal ε) :=
      iInf_le _ hε.le
    apply le_trans h2
    have h3 : actualDiameterPackingOuterMeasure Z ε = 0 := by
      apply actualDiameterPackingOuterMeasure_eq_zero_of_premeasure
      · exact h ε hε
      · exact actualDiameterPackingPremeasure_empty X ε
    exact iInf_le _ h3
  have h_bound : (⨅ s : ℝ, ⨅ (_ : 0 ≤ s), ⨅ (_ : actualDiameterPackingOuterMeasure Z s = 0),
      ENNReal.ofReal s) ≤ ⨅ (ε : ℝ) (_ : 0 < ε), ENNReal.ofReal ε := by
    apply le_iInf
    intro ε
    apply le_iInf
    intro hε
    exact h_le ε hε
  apply le_trans h_bound
  have h_zero : (⨅ (ε : ℝ) (_ : 0 < ε), ENNReal.ofReal ε) = 0 := by
    apply nonpos_iff_eq_zero.mp
    have h_inf : ∀ n : ℕ, (⨅ (ε : ℝ) (_ : 0 < ε), ENNReal.ofReal ε) ≤ ENNReal.ofReal (1 / (n + 1 :
        ℝ)) := by
      intro n
      have hn : 0 < (1 / (n + 1 : ℝ)) := by positivity
      have h1 : (⨅ (ε : ℝ) (_ : 0 < ε), ENNReal.ofReal ε) ≤ ⨅ (_ : 0 < (1 / (n + 1 : ℝ))),
          ENNReal.ofReal (1 / (n + 1 : ℝ)) := iInf_le _ (1 / (n + 1 : ℝ))
      apply le_trans h1
      exact iInf_le _ hn
    have h_tendsto : Tendsto (fun n : ℕ ↦ ENNReal.ofReal (1 / (n + 1 : ℝ))) atTop (𝓝 0) := by
      have : Tendsto (fun n : ℕ ↦ (1 / (n + 1 : ℝ))) atTop (𝓝 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
      have h_real := ENNReal.tendsto_ofReal this
      simp only [ENNReal.ofReal_zero] at h_real
      exact h_real
    exact ge_of_tendsto h_tendsto (Filter.Eventually.of_forall h_inf)
  exact h_zero.le

/-- The actual-diameter packing premeasure of the whole factorial product vanishes at every
exponent `s > 0`. -/
private lemma factorialPackingPremeasure_eq_zero
    (m : MetricSpace FactorialProduct)
    (h_ultra : ∀ x y z : FactorialProduct, dist x z ≤ max (dist x y) (dist y z))
    (h_dist : ∀ x y : FactorialProduct, ∀ n : ℕ,
        (∀ k < n, x k = y k) → x n ≠ y n → dist x y = factorialScale n)
    (s : ℝ)
    (hs : 0 < s) :
    actualDiameterPackingPremeasure (Set.univ : Set FactorialProduct) s = 0 := by
  apply nonpos_iff_eq_zero.mp
  apply ge_of_tendsto (factorial_mass_tail_tendsto_zero s hs)
  apply Filter.Eventually.of_forall
  intro M
  exact (iInf_le_of_le (factorialScale M)
    (iInf_le_of_le (factorialScale_pos M) le_rfl)).trans
    (factorialPackingContent_le_tsum m h_ultra h_dist s M)

/-- The actual-diameter packing dimension of the factorial product is zero. -/
lemma factorialPackingDimension_eq_zero
    (m : MetricSpace FactorialProduct)
    (h_ultra : ∀ x y z : FactorialProduct, dist x z ≤ max (dist x y) (dist y z))
    (h_dist : ∀ x y : FactorialProduct, ∀ n : ℕ,
        (∀ k < n, x k = y k) → x n ≠ y n → dist x y = factorialScale n) :
    actualDiameterPackingDimension (Set.univ : Set FactorialProduct) = 0 := by
  exact actualDiameterPackingDimension_eq_zero_of_premeasure
    (fun s hs ↦ factorialPackingPremeasure_eq_zero m h_ultra h_dist s hs)

/-- The number of cylinders specified by the first `n` coordinates. -/
noncomputable def factorialCylinderCount (n : ℕ) : ℕ :=
  ∏ j ∈ Finset.range n, factorialBranching j

/-- The base-two logarithm of the number of depth-`n` cylinders. -/
noncomputable def factorialLogCylinderCount (n : ℕ) : ℝ :=
  Real.log (factorialCylinderCount n) / Real.log 2

/-- Factorial scales beyond depth `n` lie below the specified dyadic radius. -/
private lemma factorialScale_lt_dyadicRadius
    (n k j : ℕ) (hn : 2 ≤ n) (hj : n ≤ j) (hk2 : k < n.factorial) :
    factorialScale j < dyadicRadius k := by
  have hj0 : j ≠ 0 := by omega
  unfold factorialScale
  rw [ite_eq_right hj0]
  have h1 : (1 / 2 : ℝ) ^ j.factorial ≤ (1 / 2 : ℝ) ^ n.factorial :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.factorial_le hj)
  have h2 : (1 / 2 : ℝ) ^ n.factorial < (1 / 2 : ℝ) ^ k :=
    pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) hk2
  have h3 : (1 / 2 : ℝ) ^ k = dyadicRadius k := by
    unfold dyadicRadius
    rw [one_div]
  exact h1.trans_lt (h2.trans_eq h3)

/-- For $n \ge 2$ and $k < n!$, finitely many balls of radius $2^{-k}$, at most $N_n$ of them,
cover the factorial product. -/
private lemma exists_factorialProduct_ball_cover
    (m : MetricSpace FactorialProduct)
    (h_dist : ∀ x y : FactorialProduct, ∀ n : ℕ,
        (∀ k < n, x k = y k) → x n ≠ y n → dist x y = factorialScale n)
    (n k : ℕ) (hn : 2 ≤ n) (hk2 : k < n.factorial) :
    ∃ S : Finset FactorialProduct,
      S.card ≤ factorialCylinderCount n ∧
      Set.univ ⊆ ⋃ x ∈ (S : Set FactorialProduct), Metric.ball x (dyadicRadius k) := by
  have hbn : ∀ j, 0 < factorialBranching j := fun j ↦ by
    by_cases h : j = 0 <;> simp [factorialBranching, h]
  classical
  let center : (∀ j : Fin n, Fin (factorialBranching j)) → FactorialProduct :=
    fun p j ↦ if h : j < n then p ⟨j, h⟩ else ⟨0, hbn j⟩
  let S := Finset.univ.image center
  use S
  constructor
  · apply Finset.card_image_le.trans
    rw [Finset.card_univ, Fintype.card_pi]
    simp only [Fintype.card_fin]
    have H := Fin.prod_univ_eq_prod_range (fun j ↦ factorialBranching j) n
    unfold factorialCylinderCount
    exact H.le
  · rintro x _
    have hr : 0 < dyadicRadius k := by unfold dyadicRadius; positivity
    let p : (∀ j : Fin n, Fin (factorialBranching j)) := fun j ↦ x j.val
    have hp : p ∈ Finset.univ := Finset.mem_univ _
    have hcS : center p ∈ Finset.univ.image center := Finset.mem_image_of_mem center hp
    let c := center p
    rw [Set.mem_iUnion₂]
    refine ⟨c, Finset.mem_coe.mpr hcS, ?_⟩
    rw [Metric.mem_ball]
    by_cases hxc : x = c
    · simpa [hxc] using hr
    · have hex : ∃ j, x j ≠ c j := by
        by_contra hh
        push Not at hh
        exact hxc (funext hh)
      let j := Nat.find hex
      have hj : x j ≠ c j := Nat.find_spec hex
      have hmin : ∀ i < j, x i = c i := fun i hi ↦ not_not.mp (Nat.find_min hex hi)
      have hjn : n ≤ j := by
        by_contra hlt
        push Not at hlt
        have h_c : c j = x j := dite_eq_left hlt
        exact hj h_c.symm
      have hd : dist x c = factorialScale j := h_dist x c j hmin hj
      rw [hd]
      exact factorialScale_lt_dyadicRadius n k j hn hjn hk2

/-- For $n \ge 2$ and $(n-1)! \le k < n!$, the whole space can be covered by $N_n$ balls of radius
$2^{-k}$. -/
lemma factorialProduct_partitionSum_le
    (m : MetricSpace FactorialProduct)
    (h_dist : ∀ x y : FactorialProduct, ∀ n : ℕ,
        (∀ k < n, x k = y k) → x n ≠ y n → dist x y = factorialScale n)
    (n k : ℕ) (hn : 2 ≤ n) (hk2 : k < n.factorial) :
    partitionSum id (fun _ ↦ 0) .centered (Set.univ : Set FactorialProduct) 1 (dyadicRadius k) ≤
      (factorialCylinderCount n : ℝ≥0∞) := by
  let := m
  have hr : 0 < dyadicRadius k := by unfold dyadicRadius; positivity
  obtain ⟨S, hcard, hcov⟩ := exists_factorialProduct_ball_cover m h_dist n k hn hk2
  rw [packingEqModifiedUpperBox_open_covering _ _ hr]
  refine le_trans (iInf_le_of_le (S : Set FactorialProduct) (iInf_le_of_le hcov le_rfl)) ?_
  simpa using (Nat.cast_le.mpr hcard : (S.card : ℝ≥0∞) ≤ _)

/-- The number of depth-`n` cylinders is `2` to the sum of the branching exponents. -/
private lemma factorialCylinderCount_eq_pow (n : ℕ) :
    (factorialCylinderCount n : ℝ) =
      (2 : ℝ) ^ (∑ j ∈ Finset.range n, (if j = 0 then 1 else j.factorial : ℕ)) := by
  induction n with | zero => ?_ | succ n ih => ?_
  · simp [factorialCylinderCount]
  · have h1 : factorialCylinderCount (n + 1) = factorialCylinderCount n * factorialBranching n := by
      exact Finset.prod_range_succ _ n
    rw [h1, Nat.cast_mul, ih, factorialBranching_eq_pow]
    rw [Finset.sum_range_succ, pow_add]

/-- The logarithmic cylinder count is the sum of the factorial branching exponents. -/
lemma factorialLogCylinderCount_eq_sum (n : ℕ) : factorialLogCylinderCount n = ∑ j ∈ Finset.range n,
    (if j = 0 then (1:ℝ) else (j.factorial : ℝ)) := by
  dsimp [factorialLogCylinderCount]
  rw [factorialCylinderCount_eq_pow n]
  have h_pos : (0 : ℝ) < 2 := by norm_num
  have h_ne : (2 : ℝ) ≠ 1 := by norm_num
  have h2 : ((2:ℝ) ^ (∑ j ∈ Finset.range n, (if j = 0 then 1 else j.factorial : ℕ))) = (2:ℝ) ^ (∑ j
      ∈ Finset.range n, (if j = 0 then (1:ℝ) else (j.factorial : ℝ))) := by
    rw [← Real.rpow_natCast]
    congr 1
    push_cast
    apply Finset.sum_congr rfl
    intro x hx
    split_ifs <;> rfl
  rw [h2]
  rw [Real.log_rpow h_pos, mul_div_cancel_right₀ _ (Real.log_ne_zero_of_pos_of_ne_one h_pos h_ne)]

end Kolmogorov.PointToSet
