/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.MDLPrediction.Class.BlockCode
import Mathlib.Analysis.SpecialFunctions.CompareExp
import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Exclusion of full-block indices and polynomial ever-winner count

The score margin excludes every attaining index in a complete block. The single
mathematical final remainder contains the remaining indices; low layers use the
finite relative-complexity sublevel bound.
Blueprint nodes: `enum:block-exclusion`, `enum:dominate`, `enum:low-layers`.
-/

namespace Kolmogorov.MDLPrediction

open MeasureTheory Filter Topology
open scoped ENNReal

/-! ## Complete-block exclusion -/

/-- The chosen complete-block radius, rounded up after multiplying the logarithm.
Blueprint node `enum:block-exclusion`. -/
noncomputable def blockRadius (C0 a : ℕ) : ℕ :=
  Nat.ceil ((C0 : ℝ) * Real.logb 2 (a + 2 : ℝ))

/-- The logarithmic block radius eventually fits the layer and exceeds the score margin. -/
private lemma blockRadius_eventually_bounded (cA : ℕ) :
    ∃ C0 a0 : ℕ, ∀ a ≥ a0,
      let r := blockRadius C0 a
      r ≤ a ∧ 2 * r > 3 * cA * levelLog a + 3 * cA := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hev : ∀ᶠ n : ℕ in atTop, ((5 * cA + 1 : ℕ) : ℝ) * Real.logb 2 (n + 2) ≤ n := by
    let ε : ℝ := Real.log 2 / (2 * ((5 * cA + 1 : ℕ) : ℝ))
    have hε : 0 < ε := div_pos hlog2 (by positivity)
    have hlo := Real.isLittleO_log_id_atTop.def hε
    have hn : Tendsto (fun n : ℕ => (n + 2 : ℝ)) atTop atTop :=
      tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
    filter_upwards [hn.eventually hlo, eventually_ge_atTop 2] with n hn1 hn2
    have hnpos : (0 : ℝ) < n + 2 := by
      have : (2 : ℝ) ≤ n := by exact_mod_cast hn2
      linarith
    have hlog0 : 0 ≤ Real.log (n + 2) := Real.log_nonneg (by linarith)
    rw [Real.norm_of_nonneg hlog0, id, Real.norm_of_nonneg hnpos.le] at hn1
    rw [Real.logb, mul_div_assoc', div_le_iff₀ hlog2]
    calc ((5 * cA + 1 : ℕ) : ℝ) * Real.log (n + 2)
      _ ≤ ((5 * cA + 1 : ℕ) : ℝ) * (ε * (n + 2)) := mul_le_mul_of_nonneg_left hn1 (by positivity)
      _ = (Real.log 2 * (n + 2)) / 2 := by
        dsimp [ε]
        have h1 : ((5 * cA + 1 : ℕ) : ℝ) * (Real.log 2 / (2 * ((5 * cA + 1 : ℕ) : ℝ)) * (n +
          2)) = (Real.log 2 * (n + 2) * ((5 * cA + 1 : ℕ) : ℝ)) / (2 * ((5 * cA + 1 : ℕ) : ℝ))
            := by ring
        rw [h1, mul_div_mul_right _ _ (ne_of_gt (by positivity))]
      _ ≤ (n : ℝ) * Real.log 2 := by
        have : 2 ≤ (n : ℝ) := by exact_mod_cast hn2
        nlinarith
  obtain ⟨a0, ha0⟩ := Filter.eventually_atTop.mp hev
  refine ⟨5 * cA + 1, a0, fun a ha => ?_⟩
  dsimp only
  constructor
  · unfold blockRadius
    apply Nat.ceil_le.mpr
    exact ha0 a ha
  · let L := Real.logb 2 (a + 2 : ℝ)
    unfold blockRadius levelLog
    have h1 : ((5 * cA + 1 : ℕ) : ℝ) * L ≤ (Nat.ceil (((5 * cA + 1 : ℕ) : ℝ) * L) : ℝ) :=
      Nat.le_ceil _
    have hL1 : 1 ≤ L := by
      have h : (2 : ℝ) ^ (1 : ℝ) ≤ a + 2 := by
        have : (0 : ℝ) ≤ a := by positivity
        linarith
      have : (1 : ℝ) ≤ Real.logb 2 (a + 2 : ℝ) := by
        rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity)]
        exact h
      exact this
    have h2 : (Nat.ceil L : ℝ) < L + 1 := Nat.ceil_lt_add_one (by linarith)
    have key : 3 * (cA : ℝ) * (Nat.ceil L : ℝ) + 3 * (cA : ℝ) < 2 * (Nat.ceil (((5 * cA + 1 :
      ℕ) : ℝ) * L) : ℝ) := by
      calc 3 * (cA : ℝ) * (Nat.ceil L : ℝ) + 3 * (cA : ℝ)
        _ ≤ 3 * (cA : ℝ) * (L + 1) + 3 * (cA : ℝ) := by
          have h3 : 3 * (cA : ℝ) * (Nat.ceil L : ℝ) ≤ 3 * (cA : ℝ) * (L + 1) :=
            mul_le_mul_of_nonneg_left h2.le (by positivity)
          linarith
        _ = 3 * (cA : ℝ) * L + 6 * (cA : ℝ) := by ring
        _ < 2 * (((5 * cA + 1 : ℕ) : ℝ) * L) := by
          push_cast
          nlinarith
        _ ≤ 2 * (Nat.ceil (((5 * cA + 1 : ℕ) : ℝ) * L) : ℝ) := by nlinarith
    have h_nat : 3 * cA * Nat.ceil L + 3 * cA < 2 * Nat.ceil (((5 * cA + 1 : ℕ) : ℝ) * L) := by
      exact_mod_cast key
    exact h_nat

/-- A complete block mixture strictly beats a positive exact-layer member. -/
private lemma blockMixture_score_lt_member (U : Map) (hU : IsOptimalPrefixConditional U)
    (A : EffectiveMixtureClass U hU) (cA a r : ℕ)
    (hr1 : 2 * r > 3 * cA * levelLog a + 3 * cA)
    (hr_le : r ≤ a) (G : List ℕ) (i : ℕ) (x : BitString)
    (h_comp : classComplexity U hU A (A.model (A.mix G)) ≤ a - r + cA * levelLog a + cA)
    (h_mass : (2 : ℝ≥0∞)⁻¹ ^ r * cantorMass (A.model i) x ≤ cantorMass (A.model (A.mix G)) x)
    (h_i_comp : classComplexity U hU A (A.model i) = a)
    (h_i_pos : 0 < cantorMass (A.model i) x) :
    classScore U hU A (A.model (A.mix G)) x < classScore U hU A (A.model i) x := by
  have : IsProbabilityMeasure (A.model i) := (A.A i).probability
  have : IsProbabilityMeasure (A.model (A.mix G)) := (A.A (A.mix G)).probability
  have hQtop : cantorMass (A.model i) x ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top prob_le_one
  have hRtop : cantorMass (A.model (A.mix G)) x ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top
    prob_le_one
  have hpow : ((2 : ℝ≥0∞)⁻¹)^r ≠ 0 := by simp
  have hR_pos : 0 < cantorMass (A.model (A.mix G)) x :=
    lt_of_lt_of_le (ENNReal.mul_pos hpow h_i_pos.ne') h_mass
  let q := (cantorMass (A.model i) x).toReal
  let m := (cantorMass (A.model (A.mix G)) x).toReal
  have hq_pos : 0 < q := ENNReal.toReal_pos h_i_pos.ne' hQtop
  have hm_pos : 0 < m := ENNReal.toReal_pos hR_pos.ne' hRtop
  have h_mass_real : ((2 : ℝ)⁻¹)^r * q ≤ m := by
    have h := ENNReal.toReal_mono hRtop h_mass
    rwa [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_ofNat] at h
  have h1 : Real.logb 2 (((2 : ℝ)⁻¹)^r * q) ≤ Real.logb 2 m :=
    Real.logb_le_logb_of_le (by norm_num) (by positivity) h_mass_real
  rw [Real.logb_mul (by positivity) hq_pos.ne', Real.logb_pow, Real.logb_inv,
    Real.logb_self_eq_one (by norm_num)] at h1
  have h_comp_real : (classComplexity U hU A (A.model (A.mix G)) : ℝ) ≤ (a - r + cA * levelLog
    a + cA : ℝ) := by
    exact_mod_cast h_comp
  have hr1_real : (2 * r : ℝ) > (3 * cA * levelLog a + 3 * cA : ℝ) := by exact_mod_cast hr1
  simp only [classScore, hR_pos.ne', h_i_pos.ne', ↓reduceIte, EReal.coe_lt_coe_iff, h_i_comp]
  linarith

/-- At sufficiently high layers, a complete-block mixture strictly beats an
exact-layer member at every positive string. Blueprint node `enum:block-exclusion`. -/
theorem enum_block_exclusion (U : Map) (hU : IsOptimalPrefixConditional U)
    (A : EffectiveMixtureClass U hU) (cA : ℕ)
    (hcA : ∀ a r j G, 2 ≤ a → r ≤ a → IsCompleteBlock U hU a r j G →
      A.model (A.mix G) ∈ A.carrier ∧
      classComplexity U hU A (A.model (A.mix G)) ≤
        a - r + cA * levelLog a + cA ∧
      ∀ i ∈ G, ∀ x : BitString,
        (2 : ℝ≥0∞)⁻¹ ^ r * cantorMass (A.model i) x ≤
          cantorMass (A.model (A.mix G)) x) :
    ∃ C0 a0 : ℕ, ∀ a ≥ a0,
      let r := blockRadius C0 a
      r ≤ a ∧ 2 * r > 3 * cA * levelLog a + 3 * cA ∧
        ∀ j G i x, IsCompleteBlock U hU a r j G → i ∈ G →
          classComplexity U hU A (A.model i) = a →
          0 < cantorMass (A.model i) x →
          classScore U hU A (A.model (A.mix G)) x <
            classScore U hU A (A.model i) x := by
  obtain ⟨C0, a0, h_params⟩ := blockRadius_eventually_bounded cA
  use C0, max a0 2
  intro a ha
  have ha0 : a ≥ a0 := le_trans (le_max_left a0 2) ha
  have ha2 : a ≥ 2 := le_trans (le_max_right a0 2) ha
  obtain ⟨hr_le, hr_gt⟩ := h_params a ha0
  refine ⟨hr_le, hr_gt, ?_⟩
  intro j G i x h_comp_block hi_G hi_comp hi_pos
  obtain ⟨_, hmix_comp, hmix_mass⟩ := hcA a (blockRadius C0 a) j G ha2 hr_le h_comp_block
  exact blockMixture_score_lt_member U hU A cA a (blockRadius C0 a) hr_gt hr_le G i x
    hmix_comp (hmix_mass i hi_G x) hi_comp hi_pos

/-! ## Counting class winners -/

/-- Finitely many class measures lie below any fixed relative-complexity threshold.
Blueprint node `enum:low-layers`. -/
theorem enum_low_layers (U : Map) (hU : IsOptimalPrefixConditional U)
    (A : EffectiveMixtureClass U hU) (a0 : ℕ) :
    (Set.Finite {Q : Measure CantorSeq | Q ∈ A.carrier ∧
      classComplexity U hU A Q < a0}) ∧
      Set.ncard {Q : Measure CantorSeq | Q ∈ A.carrier ∧
        classComplexity U hU A Q < a0} ≤ 2 ^ (a0 + 1) := by
  obtain ⟨hfin, hcard⟩ := enum_relative_finite U hU A a0
  have hsub : {Q : Measure CantorSeq | Q ∈ A.carrier ∧ classComplexity U hU A Q < a0} ⊆
      {Q : Measure CantorSeq | Q ∈ A.carrier ∧ classComplexity U hU A Q ≤ a0} :=
    fun Q hQ => ⟨hQ.1, hQ.2.le⟩
  exact ⟨hfin.subset hsub, (Set.ncard_le_ncard hsub hfin).trans hcard⟩

/-- Every exact-layer winner comes from the final incomplete block. -/
private lemma everWinners_subset_remainder (U : Map)
    (hU : IsOptimalPrefixConditional U)
    (A : EffectiveMixtureClass U hU) (C0 a : ℕ)
    (h_win : ∀ j G i x, IsCompleteBlock U hU a (blockRadius C0 a) j G → i ∈ G →
          classComplexity U hU A (A.model i) = a →
          0 < cantorMass (A.model i) x →
          classScore U hU A (A.model (A.mix G)) x <
            classScore U hU A (A.model i) x) :
    ∃ rem : List ℕ,
      {Q | Q ∈ A.carrier ∧
        classComplexity U hU A Q = a ∧ ∃ x,
        IsClassWinner U hU A Q x} ⊆ A.model '' {x | x ∈ rem} ∧
      rem.length < 2 ^ (blockRadius C0 a) := by
  obtain ⟨L, rem, _, _, hmem, _, hsplit, _, hremlen, hcomplete⟩ := enum_blocks U hU a
    (blockRadius C0 a)
  refine ⟨rem, ?_, hremlen⟩
  rintro Q ⟨hQ, hk, x, hQx⟩
  obtain ⟨hne, i, hi, hKi⟩ := enum_relative_attained U hU A Q hQ
  refine ⟨i, ?_, hi⟩
  have hKa : KPNat U i <= a := by
    have h1 : ((classComplexity U hU A Q : Nat) : ENat) = classComplexityENat U hU A Q :=
      ENat.natCast_toNat hne
    rw [hKi, <- h1, hk]
  have hiL : i ∈ L := (hmem i).mpr hKa
  rw [hsplit, List.mem_append] at hiL
  rcases hiL with hblk | hrem
  · exfalso
    obtain ⟨j, hj, hiG⟩ := List.mem_flatMap.mp hblk
    have hlt := h_win j (ordinalBlock L (blockRadius C0 a) j) i x (hcomplete j
      (List.mem_range.mp hj)) hiG (by rw [hi]; exact hk) (by rw [hi]; exact hQx.2.1)
    rw [hi] at hlt
    have hRpos : 0 < cantorMass (A.model (A.mix (ordinalBlock L (blockRadius C0 a) j))) x := by
      refine pos_iff_ne_zero.mpr fun h0 => ?_
      simp [classScore, h0] at hlt
    exact absurd (hQx.2.2 _ ⟨_, rfl⟩ hRpos) (not_le.mpr hlt)
  · exact hrem

/-- The final remainder bounds the number of exact-layer winners. -/
private lemma everWinners_remainder_card (U : Map)
    (hU : IsOptimalPrefixConditional U)
    (A : EffectiveMixtureClass U hU) (C0 a : ℕ)
    (rem : List ℕ)
    (h_sub : {Q | Q ∈ A.carrier ∧
        classComplexity U hU A Q = a ∧ ∃ x,
        IsClassWinner U hU A Q x} ⊆ A.model '' {x | x ∈ rem})
    (h_len : rem.length < 2 ^ (blockRadius C0 a)) :
    (Set.Finite {Q | Q ∈ A.carrier ∧
        classComplexity U hU A Q = a ∧ ∃ x,
        IsClassWinner U hU A Q x}) ∧
      Set.ncard {Q | Q ∈ A.carrier ∧
        classComplexity U hU A Q = a ∧ ∃ x,
        IsClassWinner U hU A Q x} ≤
        2 ^ (blockRadius C0 a) := by
  have hfin : ({i | i ∈ rem} : Set Nat).Finite := rem.finite_toSet
  refine ⟨(hfin.image _).subset h_sub, ?_⟩
  calc
    _ ≤ (A.model '' {i | i ∈ rem}).ncard := Set.ncard_le_ncard h_sub (hfin.image _)
    _ ≤ ({i | i ∈ rem} : Set Nat).ncard := Set.ncard_image_le hfin
    _ ≤ rem.length := by rw [← List.coe_toFinset, Set.ncard_coe_finset]; exact
      List.toFinset_card_le rem
    _ ≤ 2 ^ (blockRadius C0 a) := h_len.le

/-- Large layers have at most exponentially many winners in their block radius. -/
private lemma everWinners_large_layer_bound (U : Map)
    (hU : IsOptimalPrefixConditional U)
    (A : EffectiveMixtureClass U hU) :
    ∃ C0 a0 : ℕ, ∀ a ≥ a0,
      (Set.Finite {Q | Q ∈ A.carrier ∧
        classComplexity U hU A Q = a ∧ ∃ x,
        IsClassWinner U hU A Q x}) ∧
      Set.ncard {Q | Q ∈ A.carrier ∧
        classComplexity U hU A Q = a ∧ ∃ x,
        IsClassWinner U hU A Q x} ≤
        2 ^ (blockRadius C0 a) := by
  obtain ⟨C0, a0, h_params⟩ := enum_block_exclusion U hU A _
    (Classical.choose_spec (blockMixture_complexity_le U hU A))
  use C0, a0
  intro a ha
  obtain ⟨hr_le, hr_gt, h_win⟩ := h_params a ha
  have ⟨rem, h_sub, h_len⟩ := everWinners_subset_remainder U hU A C0 a h_win
  exact everWinners_remainder_card U hU A C0 a rem h_sub h_len

/-- The exponential block-radius bound is polynomial in the layer. -/
private lemma blockRadius_pow_le_polynomial (C0 a : ℕ) :
    2 ^ (blockRadius C0 a) ≤ 2 * (a + 2) ^ C0 := by
  unfold blockRadius
  let t := (C0 : ℝ) * Real.logb 2 (a + 2 : ℝ)
  have hx0 : 0 ≤ (C0 : ℝ) * Real.logb 2 (a + 2 : ℝ) := by
    apply mul_nonneg (by positivity)
    apply Real.logb_nonneg (by norm_num)
    have : (0 : ℝ) ≤ a := by positivity
    linarith
  have key : (2 : ℝ) ^ ((Nat.ceil ((C0 : ℝ) * Real.logb 2 (a + 2 : ℝ))) : ℝ) ≤ (2 : ℝ) ^ (((C0
    : ℝ) * Real.logb 2 (a + 2 : ℝ)) + 1) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.ceil_lt_add_one hx0).le
  have hb : 0 < (a + 2 : ℝ) := by positivity
  have h2x : (2 : ℝ) ^ ((C0 : ℝ) * Real.logb 2 (a + 2 : ℝ)) = ((a + 2) ^ C0 : ℝ) := by
    rw [mul_comm, Real.rpow_mul (by norm_num)]
    have hlog : (2 : ℝ) ^ Real.logb 2 (a + 2 : ℝ) = (a + 2 : ℝ) := by
      apply Real.rpow_logb (by norm_num) (by norm_num) hb
    rw [hlog]
    rw [Real.rpow_natCast]
  rw [Real.rpow_add (by norm_num), Real.rpow_one, h2x] at key
  have h3 : ((2 ^ Nat.ceil ((C0 : ℝ) * Real.logb 2 (a + 2 : ℝ)) : ℕ) : ℝ) ≤ ((2 * (a + 2) ^ C0
    : ℕ) : ℝ) := by
    push_cast
    have key_comm : ((a + 2) ^ C0 : ℝ) * 2 = 2 * ((a + 2) ^ C0 : ℝ) := by rw [mul_comm]
    rw [key_comm] at key
    rw [Real.rpow_natCast] at key
    exact key
  exact_mod_cast h3

/-- Low-layer winners lie in a finite relative-complexity sublevel. -/
private lemma everWinners_small_layer_bound (U : Map)
    (hU : IsOptimalPrefixConditional U)
    (A : EffectiveMixtureClass U hU)
    (a0 a : ℕ) (ha : a < a0) :
    Set.Finite {Q | Q ∈ A.carrier ∧
      classComplexity U hU A Q = a ∧ ∃ x,
      IsClassWinner U hU A Q x} ∧
    Set.ncard {Q | Q ∈ A.carrier ∧
      classComplexity U hU A Q = a ∧ ∃ x,
      IsClassWinner U hU A Q x} ≤
        2 ^ (a0 + 1) := by
  have H := enum_low_layers U hU A a0
  rcases H with ⟨Hfin, Hcard⟩
  have hsub : {Q | Q ∈ A.carrier ∧
      classComplexity U hU A Q = a ∧ ∃ x,
      IsClassWinner U hU A Q x} ⊆
        {Q | Q ∈ A.carrier ∧ classComplexity U hU A Q < a0} := by
    intro Q hQ
    rcases hQ with ⟨h1, h2, h3⟩
    exact ⟨h1, by linarith⟩
  constructor
  · exact Set.Finite.subset Hfin hsub
  · exact (Set.ncard_le_ncard hsub Hfin).trans Hcard

/-- At every complexity layer, only polynomially many distinct class measures
can win at any positive string. Blueprint node `enum:dominate`. -/
theorem everWinners_layer_polynomial (U : Map) (hU : IsOptimalPrefixConditional U)
    (A : EffectiveMixtureClass U hU) :
    ∃ C e : ℕ, ∀ a : ℕ,
      (Set.Finite {Q : Measure CantorSeq | Q ∈ A.carrier ∧
        classComplexity U hU A Q = a ∧
          ∃ x : BitString, IsClassWinner U hU A Q x}) ∧
      Set.ncard {Q : Measure CantorSeq | Q ∈ A.carrier ∧
        classComplexity U hU A Q = a ∧
          ∃ x : BitString, IsClassWinner U hU A Q x} ≤ C * (a + 2) ^ e := by
  rcases everWinners_large_layer_bound U hU A with ⟨C0, a0, h_large⟩
  use max (2 ^ (a0 + 1)) 2, C0
  intro a
  by_cases ha : a < a0
  · rcases everWinners_small_layer_bound U hU A a0 a ha with ⟨hfin, hcard⟩
    exact ⟨hfin, hcard.trans (by
      have h1 : 2 ^ (a0 + 1) ≤ max (2 ^ (a0 + 1)) 2 := le_max_left _ _
      have h2 : max (2 ^ (a0 + 1)) 2 ≤ max (2 ^ (a0 + 1)) 2 * (a + 2) ^ C0 := by
        have : 1 ≤ (a + 2) ^ C0 := by
          apply Nat.one_le_pow
          omega
        nlinarith
      exact h1.trans h2)⟩
  · rw [not_lt] at ha
    rcases h_large a ha with ⟨hfin, hcard⟩
    refine ⟨hfin, hcard.trans ?_⟩
    have h1 := blockRadius_pow_le_polynomial C0 a
    have h2 : 2 * (a + 2) ^ C0 ≤ max (2 ^ (a0 + 1)) 2 * (a + 2) ^ C0 := by
      have : 2 ≤ max (2 ^ (a0 + 1)) 2 := le_max_right _ _
      nlinarith
    exact h1.trans h2
end Kolmogorov.MDLPrediction
