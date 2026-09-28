import KolmogorovMathlib.MonotoneComplexity.APrioriComplexity
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# A priori complexity is the least complexity with a semicomputable Kraft weight

Characterisation of `KA` by a minimality property. To a real-valued complexity function `k` one
attaches the weight `complexityRealWeight k x = 2 ^ (-k x)`; `complexityRealWeight_KA` identifies
the weight of `KA` with the universal continuous semimeasure. `KA_le_add_of_weight_le_mul` shows
that any complexity whose weight is dominated by that semimeasure is at least `KA` up to a
constant, and `prefixFree_tsum_le_one_iff_finset` reduces the Kraft condition to finite
prefix-free sets. The conclusions are
`KA_isMinimal_upperSemicomputableComplexity` and `problem_131_minimality`: `KA` itself has a
lower semicomputable weight obeying the Kraft inequality, and is minimal among such complexities.

Source: SUV, Problem 131.
-/

open ENNReal

namespace Kolmogorov

/-- The weight `2 ^ (-k x)` attached to a real-valued complexity function `k`. -/
noncomputable def complexityRealWeight (k : BitString → ℝ) (x : BitString) : ℝ≥0∞ :=
  ENNReal.ofReal (2 ^ (- k x))

/-- The weight attached to a real-valued complexity function is strictly positive. -/
lemma complexityRealWeight_pos (k : BitString → ℝ) (x : BitString) :
    0 < complexityRealWeight k x := by
  apply ENNReal.ofReal_pos.mpr
  apply Real.rpow_pos_of_pos (by norm_num)

/-- The weight attached to a real-valued complexity function is finite. -/
lemma complexityRealWeight_ne_top (k : BitString → ℝ) (x : BitString) :
    complexityRealWeight k x ≠ ⊤ := by
  exact ENNReal.ofReal_ne_top

/-- The universal continuous semimeasure takes finite values. -/
lemma universalContinuousSemimeasure_ne_top (x : BitString) :
    universalContinuousSemimeasure x ≠ ⊤ := by
  have ha := universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.1
  have h_pref : [] <+: x := List.nil_prefix
  have : universalContinuousSemimeasure x ≤ universalContinuousSemimeasure [] :=
    ha.antitone_of_prefix h_pref
  have h1 : universalContinuousSemimeasure [] = 1 := ha.1
  rw [h1] at this
  exact ne_of_lt (lt_of_le_of_lt this ENNReal.one_lt_top)

/-- A priori complexity is exactly the negative logarithm of the universal continuous semimeasure.
-/
lemma complexityRealWeight_KA (x : BitString) :
    complexityRealWeight KA x = universalContinuousSemimeasure x := by
  unfold complexityRealWeight KA
  rw [neg_neg, Real.rpow_logb (by norm_num) (by norm_num)]
  · exact ENNReal.ofReal_toReal (universalContinuousSemimeasure_ne_top x)
  · exact ENNReal.toReal_pos (universalContinuousSemimeasure_pos x).ne'
      (universalContinuousSemimeasure_ne_top x)

/-- It suffices to check the Kraft inequality on finite prefix-free sets: the finite and the
infinite
formulations agree. -/
lemma prefixFree_tsum_le_one_iff_finset (m : BitString → ℝ≥0∞) :
    (∀ S : Finset BitString, IsPrefixFree (S : Set BitString) → ∑ x ∈ S, m x ≤ 1) ↔
    (∀ S : Set BitString, IsPrefixFree S → ∑' x : S, m x ≤ 1) := by
  constructor
  · intro h S hS
    rw [ENNReal.tsum_eq_iSup_sum]
    apply iSup_le
    intro F
    have : (∑ x ∈ F, m (x : BitString)) = ∑ x ∈ F.image Subtype.val, m x := by
      exact (Finset.sum_image (fun x y _ _ hxy => Subtype.ext hxy)).symm
    rw [this]
    apply h
    intro x hx y hy hyz
    simp only [Finset.mem_coe, Finset.mem_image] at hx hy
    rcases hx with ⟨x', _, rfl⟩
    rcases hy with ⟨y', _, rfl⟩
    exact hS x'.property y'.property hyz
  · intro h S hS
    have := h S hS
    have H : (∑ x ∈ S, m x) = ∑' x : (S : Set BitString), m (x : BitString) := by
      have h_sum : (∑ x ∈ S, m x) = ∑ x ∈ Finset.univ (α := S), m x :=
        (Finset.sum_attach S m).symm
      rw [h_sum]
      exact (tsum_eq_sum (fun (x : S) hx => (hx (Finset.mem_univ x)).elim)).symm
    rw [H]
    exact this

/-- A complexity function whose weight is dominated by the universal continuous semimeasure up to a
finite factor is above `KA` up to an additive constant. -/
lemma KA_le_add_of_weight_le_mul {k : BitString → ℝ} {c : ℝ≥0∞} (hc_top : c ≠ ⊤)
    (h_le : ∀ x, complexityRealWeight k x ≤ c * universalContinuousSemimeasure x) :
    ∃ c' : ℝ, ∀ x, KA x ≤ k x + c' := by
  use Real.logb 2 c.toReal
  intro x
  have h1 := h_le x
  rw [← complexityRealWeight_KA x] at h1
  unfold complexityRealWeight at h1
  have hc_pos : 0 < c.toReal := by
    have h2 := complexityRealWeight_pos k x
    have h3 : 0 < c * ENNReal.ofReal (2 ^ (- KA x)) := lt_of_lt_of_le h2 h1
    have h4 : c ≠ 0 := by
      rintro rfl
      rw [zero_mul] at h3
      exact False.elim (lt_irrefl 0 h3)
    exact ENNReal.toReal_pos h4 hc_top
  have h_ne_top : c * ENNReal.ofReal (2 ^ (- KA x)) ≠ ⊤ := by
    apply ENNReal.mul_ne_top hc_top ENNReal.ofReal_ne_top
  have h_toReal : (ENNReal.ofReal (2 ^ (- k x))).toReal ≤
      (c * ENNReal.ofReal (2 ^ (- KA x))).toReal :=
    ENNReal.toReal_mono h_ne_top h1
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal (by positivity)] at h_toReal
  have h_log := (Real.logb_le_logb (b := 2) (x := 2 ^ (- k x))
    (y := c.toReal * 2 ^ (- KA x)) (by norm_num) (by positivity) (by positivity)).mpr h_toReal
  rw [Real.logb_mul hc_pos.ne' (by positivity)] at h_log
  rw [Real.logb_rpow (by norm_num) (by norm_num),
    Real.logb_rpow (by norm_num) (by norm_num)] at h_log
  linarith

/-- A priori complexity has lower semicomputable weight satisfying the Kraft inequality on
prefix-free sets, and is minimal among all such complexity functions up to an additive constant. -/
theorem KA_isMinimal_upperSemicomputableComplexity :
    IsLSC (fun (x _ctx : BitString) => complexityRealWeight KA x) ∧
    (∀ S : Set BitString, IsPrefixFree S → ∑' x : S, complexityRealWeight KA x ≤ 1) ∧
    (∀ k : BitString → ℝ,
      IsLSC (fun (x _ctx : BitString) => complexityRealWeight k x) →
      (∀ S : Set BitString, IsPrefixFree S → ∑' x : S, complexityRealWeight k x ≤ 1) →
      ∃ c' : ℝ, ∀ x, KA x ≤ k x + c') := by
  refine ⟨?_, ?_, ?_⟩
  · have h1 : (fun (x _ctx : BitString) => complexityRealWeight KA x) =
        (fun (x _ctx : BitString) => universalContinuousSemimeasure x) := by
      ext x _ctx
      exact complexityRealWeight_KA x
    rw [h1]
    exact universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.2
  · intro S hS
    have h1 : (fun x : S => complexityRealWeight KA x) =
        (fun x : S => universalContinuousSemimeasure (x : BitString)) := by
      ext x
      exact complexityRealWeight_KA x
    rw [h1]
    have h_meas := universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.1
    exact h_meas.tsum_antichain_le _ hS
  · intro k hk h_kraft
    have h_finset : ∀ S : Finset BitString, IsPrefixFree (S : Set BitString) →
        ∑ x ∈ S, complexityRealWeight k x ≤ 1 := by
      exact (prefixFree_tsum_le_one_iff_finset (complexityRealWeight k)).mpr h_kraft
    obtain ⟨c, hc_top, h_le⟩ := lsc_prefixFreeWeight_dominated_by_universal
      (complexityRealWeight k) hk h_finset
    exact KA_le_add_of_weight_le_mul hc_top h_le

/-- A complexity function with lower semicomputable weight that is majorised by some continuous tree
semimeasure is above `KA` up to an additive constant. -/
theorem problem_131_minimality
    (k : BitString → ℝ)
    (hlsc : IsLSC (fun (x _ctx : BitString) => complexityRealWeight k x))
    (h_majorant : ∃ a : BitString → ℝ≥0∞,
      IsContinuousTreeSemimeasure a ∧ ∀ x, complexityRealWeight k x ≤ a x) :
    ∃ c : ℝ, ∀ x, KA x ≤ k x + c := by
  have h_kraft : ∀ S : Set BitString, IsPrefixFree S → ∑' x : S, complexityRealWeight k x ≤ 1 := by
    intro S hS
    rcases h_majorant with ⟨a, ha, h_le⟩
    have h_le_tsum : ∑' x : S, complexityRealWeight k x ≤ ∑' x : S, a (x : BitString) :=
      ENNReal.tsum_le_tsum (fun x => h_le x)
    exact le_trans h_le_tsum (ha.tsum_antichain_le _ hS)
  exact KA_isMinimal_upperSemicomputableComplexity.2.2 k hlsc h_kraft

end Kolmogorov
