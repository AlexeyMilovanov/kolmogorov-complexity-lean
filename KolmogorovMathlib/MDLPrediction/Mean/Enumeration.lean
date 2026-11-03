/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.MDLPrediction.Mean.Tree
import KolmogorovMathlib.AlgorithmicRandomness.LSCCharacterizations.DyadicEnumeration

/-!
# Lower requests for the first-exit mean tree

Each factor waits for positive lower certificates from both parents. The finite product
therefore includes a first one-zero child and kills descendants. Rounding uses the
repository's dyadic denominator convention.
Blueprint nodes: `exp:mean-lsc`.
-/

namespace Kolmogorov.MDLPrediction

open MeasureTheory
open scoped ENNReal

/-! ## Stage conditionals and products -/

/-- The jointly gated lower mean conditional. Blueprint node `exp:mean-lsc`. -/
noncomputable def meanStageFactor (eP eQ s : ℕ) (y : BitString) (b : Bool) : ℝ :=
  if 0 < massLower eP s y ∧ 0 < massLower eQ s y then
    (conditionalLower eP s y b + conditionalLower eQ s y b) / 2
  else 0

/-- The stage product of certified mean conditionals. Blueprint node `exp:mean-lsc`. -/
noncomputable def meanStageProduct (eP eQ s : ℕ) (x : BitString) : ℝ≥0∞ :=
  ∏ i : Fin x.length,
    ENNReal.ofReal (meanStageFactor eP eQ s (x.take i.val) (x[i.val]'i.isLt))

/-- Rounding a stage product down to the stage dyadic scale.
Blueprint node `exp:mean-lsc`. -/
noncomputable def meanStageRounded (eP eQ s : ℕ) (x : BitString) : ℝ≥0∞ :=
  dyadicValue (⌊(2 ^ s : ℝ) * (meanStageProduct eP eQ s x).toReal⌋₊) s

/-- A conditional lower approximation is nonnegative. -/
private lemma conditionalLower_nonneg (e s : ℕ) (y : BitString) (b : Bool) :
    0 ≤ conditionalLower e s y b := by
  unfold conditionalLower
  split_ifs
  · apply div_nonneg
    · exact ENNReal.toReal_nonneg
    · exact ENNReal.toReal_nonneg
  · exact le_refl 0

/-- The stage mean conditional increases for valid measure indices. -/
private lemma meanStageFactor_mono (P Q : Measure CantorSeq) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (eP eQ s : ℕ)
    (heP : IsComputableMeasureIndex P eP)
    (heQ : IsComputableMeasureIndex Q eQ) (y : BitString) (b : Bool) :
    meanStageFactor eP eQ s y b ≤ meanStageFactor eP eQ (s + 1) y b := by
  unfold meanStageFactor
  split_ifs with h_s h_succ
  · have hP : 0 < cantorMass P y := lt_of_lt_of_le h_s.1 ((exp_dyadic_bracket P eP heP y).2.2.1 s).1
    have hQ : 0 < cantorMass Q y := lt_of_lt_of_le h_s.2 ((exp_dyadic_bracket Q eQ heQ y).2.2.1 s).1
    have h1 := (exp_quotient_lower P eP heP y b hP).2.1 s
    have h2 := (exp_quotient_lower Q eQ heQ y b hQ).2.1 s
    linarith
  · have h_le_P := (exp_dyadic_bracket P eP heP y).1 s
    have h_le_Q := (exp_dyadic_bracket Q eQ heQ y).1 s
    have h_P_succ : 0 < massLower eP (s + 1) y := lt_of_lt_of_le h_s.1 h_le_P
    have h_Q_succ : 0 < massLower eQ (s + 1) y := lt_of_lt_of_le h_s.2 h_le_Q
    exact False.elim (h_succ ⟨h_P_succ, h_Q_succ⟩)
  · have h1 := conditionalLower_nonneg eP (s + 1) y b
    have h2 := conditionalLower_nonneg eQ (s + 1) y b
    linarith
  · exact le_refl 0

/-- The finite product of stage mean conditionals increases. -/
private lemma meanStageProduct_mono (P Q : Measure CantorSeq) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (eP eQ : ℕ)
    (heP : IsComputableMeasureIndex P eP)
    (heQ : IsComputableMeasureIndex Q eQ) (x : BitString) :
    ∀ s, meanStageProduct eP eQ s x ≤ meanStageProduct eP eQ (s + 1) x := by
  intro s
  unfold meanStageProduct
  gcongr with i
  exact meanStageFactor_mono P Q eP eQ s heP heQ (x.take i.val) (x[i.val]'i.isLt)

/-- A stage mean conditional converges to the first-exit factor. -/
private lemma meanStageFactor_tendsto (P Q : Measure CantorSeq) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (eP eQ : ℕ)
    (heP : IsComputableMeasureIndex P eP)
    (heQ : IsComputableMeasureIndex Q eQ) (y : BitString) (b : Bool) :
    Filter.Tendsto (fun s => ENNReal.ofReal (meanStageFactor eP eQ s y b)) Filter.atTop
      (nhds (meanFactor P Q y b)) := by
  unfold meanFactor meanStageFactor
  by_cases hP : cantorMass P y = 0
  · have hy : ¬(0 < cantorMass P y) := by simp [hP]
    have hy2 : ¬(0 < cantorMass P y ∧ 0 < cantorMass Q y) := by simp [hy]
    simp only [hy2, ite_false]
    have h1 := (exp_dyadic_bracket P eP heP y).2.2.1
    have h_zero : ∀ s, massLower eP s y = 0 := by
      intro s
      have h1s := (h1 s).1
      rw [hP] at h1s
      exact le_antisymm h1s zero_le
    have h_not : ∀ s, ¬(0 < massLower eP s y ∧ 0 < massLower eQ s y) := by
      intro s
      rw [h_zero s]
      simp
    simp only [h_not, ite_false, ENNReal.ofReal_zero, tendsto_const_nhds]
  · by_cases hQ : cantorMass Q y = 0
    · have hy : ¬(0 < cantorMass Q y) := by simp [hQ]
      have hy2 : ¬(0 < cantorMass P y ∧ 0 < cantorMass Q y) := by simp [hy]
      simp only [hy2, ite_false]
      have h1 := (exp_dyadic_bracket Q eQ heQ y).2.2.1
      have h_zero : ∀ s, massLower eQ s y = 0 := by
        intro s
        have h1s := (h1 s).1
        rw [hQ] at h1s
        exact le_antisymm h1s zero_le
      have h_not : ∀ s, ¬(0 < massLower eP s y ∧ 0 < massLower eQ s y) := by
        intro s
        rw [h_zero s]
        simp
      simp only [h_not, ite_false, ENNReal.ofReal_zero, tendsto_const_nhds]
    · have hP_pos : 0 < cantorMass P y := lt_of_le_of_ne zero_le (Ne.symm hP)
      have hQ_pos : 0 < cantorMass Q y := lt_of_le_of_ne zero_le (Ne.symm hQ)
      have h_common : 0 < cantorMass P y ∧ 0 < cantorMass Q y := ⟨hP_pos, hQ_pos⟩
      simp only [h_common, and_self, ite_true]
      have hP_sup := (exp_dyadic_bracket P eP heP y).2.2.2.1
      have hQ_sup := (exp_dyadic_bracket Q eQ heQ y).2.2.2.1
      have ⟨sP, hsP⟩ : ∃ sP, 0 < massLower eP sP y := by
        rw [← hP_sup] at hP_pos
        exact lt_iSup_iff.mp hP_pos
      have ⟨sQ, hsQ⟩ : ∃ sQ, 0 < massLower eQ sQ y := by
        rw [← hQ_sup] at hQ_pos
        exact lt_iSup_iff.mp hQ_pos
      have h_eventually_P : ∀ s ≥ sP, 0 < massLower eP s y := by
        intro s hs
        have h_mono := monotone_nat_of_le_succ (exp_dyadic_bracket P eP heP y).1
        exact lt_of_lt_of_le hsP (h_mono hs)
      have h_eventually_Q : ∀ s ≥ sQ, 0 < massLower eQ s y := by
        intro s hs
        have h_mono := monotone_nat_of_le_succ (exp_dyadic_bracket Q eQ heQ y).1
        exact lt_of_lt_of_le hsQ (h_mono hs)
      have h_eventually_both : ∀ s ≥ max sP sQ, 0 < massLower eP s y ∧ 0 < massLower eQ s y := by
        intro s hs
        exact ⟨h_eventually_P s (le_trans (le_max_left sP sQ) hs),
               h_eventually_Q s (le_trans (le_max_right sP sQ) hs)⟩
      have h_eventually : ∀ᶠ s in Filter.atTop, 0 < massLower eP s y ∧ 0 < massLower eQ s y := by
        apply Filter.eventually_atTop.mpr
        exact ⟨max sP sQ, h_eventually_both⟩
      have h_tendsto_P := (exp_quotient_lower P eP heP y b hP_pos).2.2.2
      have h_tendsto_Q := (exp_quotient_lower Q eQ heQ y b hQ_pos).2.2.2
      have h_tendsto_add := Filter.Tendsto.add h_tendsto_P h_tendsto_Q
      have h_tendsto_div := Filter.Tendsto.div_const h_tendsto_add 2
      have h_tendsto_ofReal := ENNReal.tendsto_ofReal h_tendsto_div
      have H_eq : (fun a => ENNReal.ofReal ((conditionalLower eP a y b + conditionalLower
          eQ a y b) / 2)) =ᶠ[Filter.atTop] (fun s => ENNReal.ofReal (meanStageFactor eP eQ
          s y b)) := by
        apply Filter.Eventually.mono h_eventually
        intro s hs
        dsimp only
        unfold meanStageFactor
        have hs_true : (0 < massLower eP s y ∧ 0 < massLower eQ s y) = True := eq_true hs
        simp only [hs_true, ite_true]
      exact Filter.Tendsto.congr' H_eq h_tendsto_ofReal

/-- The supremum of stage products is the mean tree. -/
private lemma iSup_meanStageProduct_eq (P Q : Measure CantorSeq) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (eP eQ : ℕ)
    (heP : IsComputableMeasureIndex P eP)
    (heQ : IsComputableMeasureIndex Q eQ) (x : BitString) :
    (⨆ s, meanStageProduct eP eQ s x) = meanTree P Q x := by
  have h_mono := meanStageProduct_mono P Q eP eQ heP heQ x
  have h_tendsto : Filter.Tendsto (fun s => meanStageProduct eP eQ s x) Filter.atTop (nhds
      (meanTree P Q x)) := by
    unfold meanStageProduct meanTree
    apply ENNReal.tendsto_finsetProd_of_ne_top Finset.univ
    · intro i _
      exact meanStageFactor_tendsto P Q eP eQ heP heQ (x.take i.val) (x[i.val]'i.isLt)
    · intro i _
      unfold meanFactor
      split_ifs with h
      · exact ENNReal.ofReal_ne_top
      · exact ENNReal.zero_ne_top
  have h_mono_f : Monotone (fun s => meanStageProduct eP eQ s x) := monotone_nat_of_le_succ h_mono
  have h_tendsto2 := tendsto_atTop_ciSup h_mono_f (OrderTop.bddAbove _)
  exact tendsto_nhds_unique h_tendsto2 h_tendsto

/-! ## Dyadic rounding -/

/-- The rounded stage product increases with the stage. -/
private lemma meanStageRounded_mono (P Q : Measure CantorSeq) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (eP eQ : ℕ)
    (heP : IsComputableMeasureIndex P eP)
    (heQ : IsComputableMeasureIndex Q eQ) (x : BitString) :
    ∀ s, meanStageRounded eP eQ s x ≤ meanStageRounded eP eQ (s + 1) x := by
  intro s
  unfold meanStageRounded
  rw [← dyadicValue_two_mul_succ]
  apply dyadicValue_mono_num
  set a := (meanStageProduct eP eQ s x).toReal
  set b := (meanStageProduct eP eQ (s + 1) x).toReal
  have ha_nonneg : 0 ≤ a := ENNReal.toReal_nonneg
  have h_mono : meanStageProduct eP eQ s x ≤ meanStageProduct eP eQ (s + 1) x :=
    meanStageProduct_mono P Q eP eQ heP heQ x s
  have h_b_ne_top : meanStageProduct eP eQ (s + 1) x ≠ ⊤ := by
    unfold meanStageProduct
    exact ENNReal.prod_ne_top (fun _ _ => ENNReal.ofReal_ne_top)
  have hab : a ≤ b :=
    (ENNReal.toReal_le_toReal (ne_top_of_le_ne_top h_b_ne_top h_mono) h_b_ne_top).mpr h_mono
  apply Nat.le_floor
  push_cast
  have h1 : (2 : ℝ) * ⌊(2 ^ s : ℝ) * a⌋₊ ≤ 2 * ((2 ^ s : ℝ) * a) := by
    gcongr
    exact Nat.floor_le (mul_nonneg (by positivity) ha_nonneg)
  have h2 : 2 * ((2 ^ s : ℝ) * a) ≤ (2 ^ (s + 1) : ℝ) * b := by
    rw [pow_succ, mul_assoc]
    have hs : (0 : ℝ) ≤ 2 ^ s := by positivity
    nlinarith
  exact h1.trans h2

/-- Rounding preserves the supremum of stage products. -/
private lemma iSup_meanStageRounded_eq (P Q : Measure CantorSeq) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (eP eQ : ℕ)
    (heP : IsComputableMeasureIndex P eP)
    (heQ : IsComputableMeasureIndex Q eQ) (x : BitString) :
    (⨆ s, meanStageRounded eP eQ s x) = meanTree P Q x := by
  let r_fn := meanStageProduct eP eQ (x := x)
  let d_fn := meanStageRounded eP eQ (x := x)
  have hl : (⨆ s, r_fn s) = meanTree P Q x := iSup_meanStageProduct_eq P Q eP eQ heP heQ x
  have hmono : ∀ s, r_fn s ≤ r_fn (s + 1) := meanStageProduct_mono P Q eP eQ heP heQ x
  have hmono_general : ∀ s₁ s₂, s₁ ≤ s₂ → r_fn s₁ ≤ r_fn s₂ :=
    fun s1 s2 hle => monotone_nat_of_le_succ hmono hle
  have hb : ∀ s, d_fn s ≤ r_fn s ∧ r_fn s ≤ d_fn s + dyadicValue 1 s := by
    intro s
    let r : ℝ≥0∞ := r_fn s
    let a : ℝ := r.toReal
    have ha0 : 0 ≤ a := by
      simp only [a, r]
      exact ENNReal.toReal_nonneg
    have hround : d_fn s = dyadicValue ⌊(2 ^ s : ℝ) * a⌋₊ s := by
      dsimp [d_fn, meanStageRounded, a, r, r_fn]
    have hr_ne_top : r ≠ ∞ := ENNReal.prod_ne_top (fun i _ => ENNReal.ofReal_ne_top)
    have hr_eq_ofReal : r = ENNReal.ofReal a := (ENNReal.ofReal_toReal hr_ne_top).symm
    rw [hround]
    rw [Kolmogorov.dyadicValue_eq_ofReal]
    change ENNReal.ofReal (↑⌊2 ^ s * a⌋₊ / ↑(2 ^ s : ℕ)) ≤ r ∧
      r ≤ ENNReal.ofReal (↑⌊2 ^ s * a⌋₊ / ↑(2 ^ s : ℕ)) + dyadicValue 1 s
    have h2 : r = ENNReal.ofReal a := hr_eq_ofReal
    rw [h2]
    have h1 : dyadicValue 1 s = ENNReal.ofReal (1 / (2 ^ s : ℝ)) := by
      rw [Kolmogorov.dyadicValue_eq_ofReal]
      push_cast
      rfl
    rw [h1]
    rw [← ENNReal.ofReal_add]
    · constructor
      · rw [ENNReal.ofReal_le_iff_le_toReal ENNReal.ofReal_ne_top]
        rw [ENNReal.toReal_ofReal ha0]
        have hp : (0:ℝ) < (2 ^ s : ℝ) := by positivity
        have hp2 : (0:ℝ) < ((2 ^ s : ℕ) : ℝ) := by positivity
        have h_floor : (⌊(2 ^ s : ℝ) * a⌋₊ : ℝ) ≤ (2 ^ s : ℝ) * a := Nat.floor_le (by positivity)
        have h_mul : (⌊(2 ^ s : ℝ) * a⌋₊ : ℝ) ≤ a * ((2 ^ s : ℕ) : ℝ) := by
          push_cast
          linarith
        have hdiv : (⌊(2 ^ s : ℝ) * a⌋₊ : ℝ) / ((2 ^ s : ℕ) : ℝ) ≤ a ↔
          (⌊(2 ^ s : ℝ) * a⌋₊ : ℝ) ≤ a * ((2 ^ s : ℕ) : ℝ) := div_le_iff₀ hp2
        exact hdiv.mpr h_mul
      · rw [ENNReal.ofReal_le_iff_le_toReal ENNReal.ofReal_ne_top]
        have hpos_rhs : (0 : ℝ) ≤ (⌊(2 ^ s : ℝ) * a⌋₊ : ℝ) / ((2 ^ s : ℕ) : ℝ) + 1 / (2 ^ s : ℝ) :=
          by positivity
        have heq_rhs : (ENNReal.ofReal (↑⌊2 ^ s * a⌋₊ / ↑(2 ^ s : ℕ) + 1 / (2 ^ s : ℝ))).toReal =
            ↑⌊2 ^ s * a⌋₊ / ↑(2 ^ s : ℕ) + 1 / (2 ^ s : ℝ) := by
          exact ENNReal.toReal_ofReal hpos_rhs
        rw [heq_rhs]
        have heq : (ENNReal.ofReal a).toReal = a := ENNReal.toReal_ofReal ha0
        have h_goal : a ≤ ↑⌊2 ^ s * a⌋₊ / ↑(2 ^ s : ℕ) + 1 / (2 ^ s : ℝ) := by
          have hp : (0:ℝ) < (2 ^ s : ℝ) := by positivity
          have hp2 : (0:ℝ) < ((2 ^ s : ℕ) : ℝ) := by positivity
          have hdiv : a ≤ (⌊(2 ^ s : ℝ) * a⌋₊ : ℝ) / ((2 ^ s : ℕ) : ℝ) + 1 / ((2 ^ s : ℕ) : ℝ) ↔
              a * ((2 ^ s : ℕ) : ℝ) ≤ (⌊(2 ^ s : ℝ) * a⌋₊ : ℝ) + 1 := by
            have h_add : (⌊(2 ^ s : ℝ) * a⌋₊ : ℝ) / ((2 ^ s : ℕ) : ℝ) + 1 / ((2 ^ s : ℕ) : ℝ) =
                ((⌊(2 ^ s : ℝ) * a⌋₊ : ℝ) + 1) / ((2 ^ s : ℕ) : ℝ) := by
              exact (add_div (↑⌊2 ^ s * a⌋₊) 1 ((2 ^ s : ℕ) : ℝ)).symm
            rw [h_add]
            exact le_div_iff₀ hp2
          have hlto := Nat.lt_floor_add_one ((2 ^ s : ℝ) * a)
          have hmulo : a * ((2 ^ s : ℕ) : ℝ) ≤ ((⌊(2 ^ s : ℝ) * a⌋₊ : ℝ) + 1) := by
            push_cast
            linarith
          have heq2 : (2 ^ s : ℝ) = ↑(2 ^ s : ℕ) := by push_cast; rfl
          have hsubst : a ≤ ↑⌊2 ^ s * a⌋₊ / ↑(2 ^ s : ℕ) + 1 / (2 ^ s : ℝ) ↔
              a ≤ ↑⌊2 ^ s * a⌋₊ / ↑(2 ^ s : ℕ) + 1 / ↑(2 ^ s : ℕ) := by
            calc a ≤ ↑⌊2 ^ s * a⌋₊ / ↑(2 ^ s : ℕ) + 1 / (2 ^ s : ℝ)
              _ ↔ a ≤ ↑⌊2 ^ s * a⌋₊ / ↑(2 ^ s : ℕ) + 1 / ↑(2 ^ s : ℕ) := by rw [heq2]
          rw [hsubst]
          exact hdiv.mpr hmulo
        have h_final : (ENNReal.ofReal a).toReal ≤ ↑⌊2 ^ s * a⌋₊ / ↑(2 ^ s : ℕ) + 1 / (2 ^ s : ℝ) :=
          by
          rw [heq]
          exact h_goal
        have hl_sub : a ≤ ↑⌊2 ^ s * a⌋₊ / ↑(2 ^ s : ℕ) + 1 / (2 ^ s : ℝ) ↔
            (ENNReal.ofReal a).toReal ≤ ↑⌊2 ^ s * a⌋₊ / ↑(2 ^ s : ℕ) + 1 / (2 ^ s : ℝ) := by
          rw [heq]
        rw [hl_sub]
        exact h_final
    · positivity
    · positivity
  rw [← hl]
  apply le_antisymm
  · apply iSup_le
    intro s
    have hbs := (hb s).1
    exact le_trans hbs (le_iSup r_fn s)
  · apply ENNReal.le_of_forall_pos_le_add
    intro ε hε htop
    have htop_real : (ε:ℝ≥0∞) ≠ ∞ := by
      exact ENNReal.coe_ne_top
    rcases ENNReal.exists_inv_two_pow_lt (show (ε:ℝ≥0∞) ≠ 0 by
      exact (ENNReal.coe_pos.mpr hε).ne') with ⟨t, ht⟩
    have hle_sup : ∀ s', d_fn s' ≤ ⨆ s, d_fn s := le_iSup d_fn
    apply iSup_le
    intro s
    have hs1 : r_fn s ≤ r_fn (max s t) := hmono_general s (max s t) (le_max_left s t)
    have hs2 : r_fn (max s t) ≤ d_fn (max s t) + dyadicValue 1 (max s t) := (hb (max s t)).2
    have h_pow_le : dyadicValue 1 (max s t) ≤ dyadicValue 1 t := by
      rw [Kolmogorov.dyadicValue_one_eq_inv_two_pow', Kolmogorov.dyadicValue_one_eq_inv_two_pow']
      apply pow_le_pow_of_le_one (by positivity) (by norm_num) (le_max_right s t)
    calc r_fn s
      _ ≤ r_fn (max s t) := hs1
      _ ≤ d_fn (max s t) + dyadicValue 1 (max s t) := hs2
      _ ≤ (⨆ s, d_fn s) + dyadicValue 1 (max s t) := add_le_add (hle_sup (max s t)) (le_refl _)
      _ ≤ (⨆ s, d_fn s) + dyadicValue 1 t := add_le_add (le_refl _) h_pow_le
      _ ≤ (⨆ s, d_fn s) + ε := by
        have heq_dv : dyadicValue 1 t = 2⁻¹ ^ t :=
          Kolmogorov.dyadicValue_one_eq_inv_two_pow' t
        rw [heq_dv]
        exact add_le_add (le_refl _) (le_of_lt ht)

/-- Valid pair requests grow to the first-exit mean tree, also after dyadic rounding.
Blueprint node `exp:mean-lsc`. -/
theorem exp_mean_lsc (P Q : Measure CantorSeq) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (eP eQ : ℕ)
    (heP : IsComputableMeasureIndex P eP)
    (heQ : IsComputableMeasureIndex Q eQ) (x : BitString) :
    (∀ s, meanStageProduct eP eQ s x ≤ meanStageProduct eP eQ (s + 1) x) ∧
    (⨆ s, meanStageProduct eP eQ s x) = meanTree P Q x ∧
    (∀ s, meanStageRounded eP eQ s x ≤ meanStageRounded eP eQ (s + 1) x) ∧
    (⨆ s, meanStageRounded eP eQ s x) = meanTree P Q x := by
  exact ⟨meanStageProduct_mono P Q eP eQ heP heQ x,
         iSup_meanStageProduct_eq P Q eP eQ heP heQ x,
         meanStageRounded_mono P Q eP eQ heP heQ x,
         iSup_meanStageRounded_eq P Q eP eQ heP heQ x⟩

end Kolmogorov.MDLPrediction
