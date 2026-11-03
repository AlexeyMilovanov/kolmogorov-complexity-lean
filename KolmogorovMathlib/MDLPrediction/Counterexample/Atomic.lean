/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.MDLPrediction.Core.Model
import KolmogorovMathlib.MonotoneComplexity.APrioriComplexity
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitinCore.LSCApproximation
import KolmogorovMathlib.AlgorithmicRandomness.ComputableMeasure
import KolmogorovMathlib.Foundation.EnumerationComplexity

/-!
# Incompressible branch words and an atomic rational witness

The atom at `1z0^∞` has weight `2^(-2k)`; the remaining mass is at `0^∞`.
Both cylinders `1` and `1z` therefore have the same positive mass.

Blueprint nodes: `audit:atomic`, `audit:incompressible`.
-/

namespace Kolmogorov.MDLPrediction

open MeasureTheory
open scoped ENNReal


/-- A branch word has
small a priori mass. -/
private theorem exists_branch_small_mass (k : ℕ) :
    ∃ z : BitString, z.length = k ∧
      universalContinuousSemimeasure (true :: z) ≤ (2 : ℝ≥0∞)⁻¹ ^ k := by
  have ha := universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.1
  induction k with
  | zero =>
    use []
    refine ⟨rfl, ?_⟩
    simpa using ha.le_one [true]
  | succ k ih =>
    rcases ih with ⟨z, hz, hm⟩
    by_cases hf : universalContinuousSemimeasure (true :: (z ++ [false])) ≤ (2 : ℝ≥0∞)⁻¹ ^ (k + 1)
    · use z ++ [false]
      refine ⟨by simp [hz], ?_⟩
      exact hf
    · use z ++ [true]
      refine ⟨by simp [hz], ?_⟩
      by_contra ht
      have hlt := ENNReal.add_lt_add (not_le.mp hf) (not_le.mp ht)
      have hhalf : (2 : ℝ≥0∞)⁻¹ ^ (k + 1) + (2 : ℝ≥0∞)⁻¹ ^ (k + 1) = (2 : ℝ≥0∞)⁻¹ ^ k := by
        rw [pow_succ, ← mul_add, ENNReal.inv_two_add_inv_two, mul_one]
      rw [hhalf] at hlt
      exact absurd ((ha.2 (true :: z)).trans hm) (not_le.mpr hlt)

/-- Small a priori mass gives a
complexity lower bound. -/
private theorem ka_lower_of_small_mass
    (x : BitString) (k : ℕ)
    (h : universalContinuousSemimeasure x ≤ (2 : ℝ≥0∞)⁻¹ ^ k) :
    (k : ℝ) ≤ KA x := by
  unfold KA
  have h_ne_top : (2 : ℝ≥0∞)⁻¹ ^ k ≠ ⊤ := by
    exact ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr (by norm_num))
  have h_real_le : (universalContinuousSemimeasure x).toReal ≤
      ((2 : ℝ≥0∞)⁻¹ ^ k).toReal := by
    apply (ENNReal.toReal_le_toReal _ h_ne_top).mpr h
    exact universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.1.ne_top x
  
  have h_val : ((2 : ℝ≥0∞)⁻¹ ^ k).toReal = (2 : ℝ)⁻¹ ^ k := by
    rw [ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_ofNat]
  rw [h_val] at h_real_le
  
  have pos_mass : 0 < (universalContinuousSemimeasure x).toReal := by
    apply ENNReal.toReal_pos
    · exact (universalContinuousSemimeasure_pos x).ne'
    · exact universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.1.ne_top x
  
  have log_le : Real.logb 2 ((universalContinuousSemimeasure x).toReal) ≤
      Real.logb 2 ((2 : ℝ)⁻¹ ^ k) := by
    unfold Real.logb
    have h_log_le : Real.log ((universalContinuousSemimeasure x).toReal) ≤
        Real.log ((2 : ℝ)⁻¹ ^ k) := by
      exact Real.log_le_log pos_mass h_real_le
    have hlog_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    exact div_le_div_of_nonneg_right h_log_le (le_of_lt hlog_pos)
  
  have log_two_pow : Real.logb 2 ((2 : ℝ)⁻¹ ^ k) = - (k : ℝ) := by
    unfold Real.logb
    rw [Real.log_pow, Real.log_inv]
    have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
    field_simp
  rw [log_two_pow] at log_le
  linarith

/-- The length bound is
uniform on branch words. -/
private theorem exists_uniform_ka_upper :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ k : ℕ, ∀ z : BitString, z.length = k →
      KA (true :: z) ≤ (k : ℝ) + c + 1 := by
  obtain ⟨c, hc⟩ := KA_le_length
  use max 0 c
  refine ⟨le_max_left 0 c, fun k z hz => ?_⟩
  have h_bound := hc (true :: z)
  simp only [List.length_cons, hz, Nat.cast_add, Nat.cast_one] at h_bound
  have h_c_le : c ≤ max 0 c := le_max_right 0 c
  linarith

/-- One absolute constant supplies a length-`k` branch word with a priori
complexity at least `k-c`; the upper bound is uniform.
Blueprint node `audit:incompressible`. -/
theorem audit_incompressible :
    ∃ c : ℝ, (∀ k : ℕ, 1 ≤ k → ∃ z : BitString,
      z.length = k ∧ (k : ℝ) - c ≤ KA (true :: z) ∧
        KA (true :: z) ≤ (k : ℝ) + c + 1) ∧
      ∀ k : ℕ, 1 ≤ k → ∀ z : BitString, z.length = k →
        KA (true :: z) ≤ (k : ℝ) + c + 1 := by
  obtain ⟨c, hc_pos, hc⟩ := exists_uniform_ka_upper
  use c
  refine ⟨fun k hk => ?_, fun k hk z hz => hc k z hz⟩
  obtain ⟨z, hz_len, hz_mass⟩ := exists_branch_small_mass k
  use z
  refine ⟨hz_len, ?_, hc k z hz_len⟩
  have hk_le : (k : ℝ) ≤ KA (true :: z) :=
    ka_lower_of_small_mass (true :: z) k hz_mass
  linarith

/-- The explicit two-atom rational witness measure.
Blueprint node `audit:atomic`. -/
noncomputable def atomicWitness (k : ℕ) (z : BitString) : Measure CantorSeq :=
  let weight : ℝ≥0∞ := (2 : ℝ≥0∞)⁻¹ ^ (2 * k)
  weight • Measure.dirac (prependCantor (true :: z) (fun _ => false)) +
    (1 - weight) • Measure.dirac (fun _ => false)

/-- Primitive recursiveness of prefixes of a primitive recursive path. -/
private lemma primrec_cantorPrefix (w : ℕ → Bool) (hw : Primrec w) :
  Primrec (fun (x : BitString) => cantorPrefix w x.length) := by
  have h1 : (fun (x : BitString) => cantorPrefix w x.length) = fun x => (List.range
      x.length).map w := by
    ext1 x
    apply List.ext_getElem
    · simp [cantorPrefix]
    · intro i _ _
      simp [cantorPrefix]
  rw [h1]
  apply Primrec.list_map
  · apply Primrec.list_range.comp Primrec.list_length
  · exact hw.comp Primrec.snd |>.to₂

/-- The branch path obtained by prepending a finite word is primitive recursive. -/
private lemma primrec_prependCantor (z : BitString) :
  Primrec (prependCantor (true :: z) (fun _ => false)) := by
  have h1 : prependCantor (true :: z) (fun _ => false) = fun i => ((true :: z).getD i false) := by
    ext i
    dsimp [prependCantor]
    split_ifs
    · symm; apply List.getD_eq_getElem
    · symm; apply List.getD_eq_default; simp only [List.length_cons] at *; omega
  rw [h1]
  apply Primrec.list_getD false |>.comp (Primrec.const (true :: z)) (Primrec.id (α := ℕ))

/-- The dyadic approximation to the atomic witness is primitive recursive. -/
private lemma primrec_atomic_approx (k : ℕ) (z : BitString) :
  Primrec₂ (fun (x : BitString) (s : ℕ) =>
    (((if cantorPrefix (prependCantor (true :: z) (fun _ => false)) x.length = x then 1 else 0) +
    (if cantorPrefix (fun _ => false) x.length = x then 2 ^ (2 * k) - 1 else 0)) * 2 ^ s
        / 2 ^ (2 * k))) := by
  have h_w1 : Primrec (prependCantor (true :: z) (fun _ => false)) := primrec_prependCantor z
  have h_w2 : Primrec (fun (_ : ℕ) => false) := Primrec.const false
  have hp1 : PrimrecPred (fun x => cantorPrefix (prependCantor (true :: z) (fun _ =>
      false)) x.length = x) := by
    exact PrimrecRel.comp (@Primrec.eq BitString _) (primrec_cantorPrefix _ h_w1)
        (Primrec.id (α := BitString))
  have hp2 : PrimrecPred (fun x => cantorPrefix (fun _ => false) x.length = x) := by
    exact PrimrecRel.comp (@Primrec.eq BitString _) (primrec_cantorPrefix _ h_w2)
        (Primrec.id (α := BitString))
  have hc1 : Primrec (fun x => if cantorPrefix (prependCantor (true :: z) (fun _ =>
      false)) x.length = x then 1 else 0) := by
    apply Primrec.ite hp1
    · exact Primrec.const 1
    · exact Primrec.const 0
  have hc2 : Primrec (fun x => if cantorPrefix (fun _ => false) x.length = x then 2 ^ (2
      * k) - 1 else 0) := by
    apply Primrec.ite hp2
    · exact Primrec.const (2 ^ (2 * k) - 1)
    · exact Primrec.const 0
  have hc3 : Primrec (fun x => (if cantorPrefix (prependCantor (true :: z) (fun _ =>
      false)) x.length = x then 1 else 0) + (if cantorPrefix (fun _ => false) x.length =
      x then 2 ^ (2 * k) - 1 else 0)) := by
    exact Primrec.nat_add.comp hc1 hc2
  have hc4 : Primrec₂ (fun x s => ((if cantorPrefix (prependCantor (true :: z) (fun _ =>
      false)) x.length = x then 1 else 0) + (if cantorPrefix (fun _ => false) x.length =
      x then 2 ^ (2 * k) - 1 else 0)) * 2 ^ s) := by
    have hc4' : Primrec₂ (fun (x : BitString) (s : ℕ) => (fun x => (if cantorPrefix
        (prependCantor (true :: z) (fun _ => false)) x.length = x then 1 else 0) + (if
        cantorPrefix (fun _ => false) x.length = x then 2 ^ (2 * k) - 1 else 0)) x * 2 ^ s) := by
      exact Primrec.nat_mul.comp (hc3.comp Primrec.fst) (primrec_two_pow_aux.comp Primrec.snd)
    exact hc4'
  exact Primrec.nat_div.comp hc4 (Primrec.const (2 ^ (2 * k)))

/-- Cylinder mass of the two-atom witness in dyadic form. -/
private lemma atomicWitness_mass (k : ℕ) (z : BitString) (x : BitString) :
  cantorMass (atomicWitness k z) x =
    dyadicValue ((if cantorPrefix (prependCantor (true :: z) (fun _ => false)) x.length
        = x then 1 else 0) +
                (if cantorPrefix (fun _ => false) x.length = x then 2 ^ (2 * k) - 1 else
                    0)) (2 * k) := by
  rw [Kolmogorov.dyadicValue_add]
  simp only [cantorMass, atomicWitness, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  rw [Measure.dirac_apply' _ (measurableSet_cantorCylinder x)]
  rw [Measure.dirac_apply' _ (measurableSet_cantorCylinder x)]
  congr 1
  · classical
    have h_eq : (if cantorPrefix (prependCantor (true :: z) (fun _ => false)) x.length =
        x then 1 else 0) =
                (if prependCantor (true :: z) (fun _ => false) ∈ cantorCylinder x then 1
                    else 0) := by
      apply if_congr _ rfl rfl
      exact isCantorPrefix_iff_cantorPrefix_eq x (prependCantor (true :: z) (fun _ =>
          false)) |>.symm
    rw [h_eq]
    split_ifs with h
    · simp [Set.indicator_of_mem h, ← Kolmogorov.dyadicValue_one_eq_inv_two_pow']
    · simp [Set.indicator_of_notMem h]
      dsimp [dyadicValue]
      simp
  · classical
    have h_eq : (if cantorPrefix (fun _ => false) x.length = x then 2 ^ (2 * k) - 1 else 0) =
                (if (fun _ => false) ∈ cantorCylinder x then 2 ^ (2 * k) - 1 else 0) := by
      apply if_congr _ rfl rfl
      exact isCantorPrefix_iff_cantorPrefix_eq x (fun _ => false) |>.symm
    rw [h_eq]
    split_ifs with h
    · simp only [Set.indicator_of_mem h, Pi.one_apply, mul_one]
      have h1 : dyadicValue (2 ^ (2 * k) - 1) (2 * k) = 1 - (2 : ℝ≥0∞)⁻¹ ^ (2 * k) := by
        apply ENNReal.eq_sub_of_add_eq (ENNReal.pow_ne_top (by simp))
        rw [← Kolmogorov.dyadicValue_one_eq_inv_two_pow', ← Kolmogorov.dyadicValue_add]
        have h2 : 2 ^ (2 * k) - 1 + 1 = 2 ^ (2 * k) := Nat.sub_add_cancel Nat.one_le_two_pow
        rw [h2]
        dsimp [dyadicValue]
        have : ((2 ^ (2 * k) : ℕ) : ℝ≥0∞) = 2 ^ (2 * k) := by simp
        rw [this]
        apply ENNReal.div_self <;> simp
      exact h1.symm
    · simp [Set.indicator_of_notMem h]
      dsimp [dyadicValue]
      simp

/-- Rounding a dyadic value down loses less than one unit at the target scale. -/
private lemma atomicWitness_floor (n t s : ℕ) :
  dyadicValue (n * 2 ^ s / 2 ^ t) s ≤ dyadicValue n t ∧
  dyadicValue n t ≤ dyadicValue (n * 2 ^ s / 2 ^ t) s + dyadicValue 1 s := by
  have h1 : dyadicValue n t = dyadicValue (n * 2 ^ s) (s + t) := by
    have eq : n * 2 ^ s = 2 ^ s * n := mul_comm _ _
    rw [eq]
    have eq2 : s + t = t + s := add_comm _ _
    rw [eq2]
    exact (dyadicValue_two_pow_mul_add n t s).symm
  constructor
  · rw [h1]
    have h2 : dyadicValue (n * 2 ^ s / 2 ^ t) s = dyadicValue (n * 2 ^ s / 2 ^ t * 2 ^
        t) (s + t) := by
      have h_comm : n * 2 ^ s / 2 ^ t * 2 ^ t = 2 ^ t * (n * 2 ^ s / 2 ^ t) := mul_comm _ _
      rw [h_comm]
      exact (dyadicValue_two_pow_mul_add (n * 2 ^ s / 2 ^ t) s t).symm
    rw [h2]
    apply dyadicValue_mono_num
    apply Nat.div_mul_le_self
  · rw [h1]
    have h3 : dyadicValue (n * 2 ^ s / 2 ^ t) s + dyadicValue 1 s = dyadicValue (n * 2 ^
        s / 2 ^ t + 1) s :=
      (Kolmogorov.dyadicValue_add _ _ _).symm
    rw [h3]
    have h4 : dyadicValue (n * 2 ^ s / 2 ^ t + 1) s = dyadicValue ((n * 2 ^ s / 2 ^ t +
        1) * 2 ^ t) (s + t) := by
      have h_comm : (n * 2 ^ s / 2 ^ t + 1) * 2 ^ t = 2 ^ t * (n * 2 ^ s / 2 ^ t + 1) :=
          mul_comm _ _
      rw [h_comm]
      exact (dyadicValue_two_pow_mul_add (n * 2 ^ s / 2 ^ t + 1) s t).symm
    rw [h4]
    apply dyadicValue_mono_num
    have h5 : n * 2 ^ s < (n * 2 ^ s / 2 ^ t + 1) * 2 ^ t := by
      rw [add_mul, one_mul]
      apply Nat.lt_div_mul_add
      apply Nat.two_pow_pos
    exact h5.le

/-- The atomic witness is a computable proper measure whose two branch
cylinders have mass `2^(-2k)`. Blueprint node `audit:atomic`. -/
theorem audit_atomic (k : ℕ) (z : BitString) :
    IsProbabilityMeasure (atomicWitness k z) ∧
      IsComputableMeasure (atomicWitness k z) ∧
      cantorMass (atomicWitness k z) [true] =
        (2 : ℝ≥0∞)⁻¹ ^ (2 * k) ∧
      cantorMass (atomicWitness k z) (true :: z) =
        (2 : ℝ≥0∞)⁻¹ ^ (2 * k) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp [atomicWitness]
    constructor
    simp only [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    apply add_tsub_cancel_of_le
    exact pow_le_one₀ zero_le (ENNReal.inv_le_one.mpr one_le_two)
  · let num (x : BitString) :=
      (if cantorPrefix (prependCantor (true :: z) (fun _ => false)) x.length = x then 1 else 0) +
      (if cantorPrefix (fun _ => false) x.length = x then 2 ^ (2 * k) - 1 else 0)
    let a (x : BitString) (s : ℕ) := num x * 2 ^ s / 2 ^ (2 * k)
    apply isComputableMeasure_of_dyadicFloorApprox (a := a)
    · exact (primrec_atomic_approx k z).to_comp
    · intro x s
      have h := atomicWitness_floor (num x) (2 * k) s
      rw [← atomicWitness_mass k z x] at h
      exact h
  · simp only [cantorMass, atomicWitness, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
    rw [Measure.dirac_apply' (prependCantor (true :: z) (fun _ => false))
        (measurableSet_cantorCylinder _)]
    rw [Measure.dirac_apply' (fun _ => false) (measurableSet_cantorCylinder _)]
    have h1 : prependCantor (true :: z) (fun _ => false) ∈ cantorCylinder [true] := by
      dsimp [cantorCylinder]
      intro i hi
      simp at hi
      have heq : i = 0 := by omega
      subst heq
      rfl
    have h2 : (fun _ => false) ∉ cantorCylinder [true] := by
      dsimp [cantorCylinder]
      intro h
      have h' := h 0 (by simp)
      simp at h'
    simp [Set.indicator, h1, h2]
  · simp only [cantorMass, atomicWitness, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
    rw [Measure.dirac_apply' (prependCantor (true :: z) (fun _ => false))
        (measurableSet_cantorCylinder _)]
    rw [Measure.dirac_apply' (fun _ => false) (measurableSet_cantorCylinder _)]
    have h1 : prependCantor (true :: z) (fun _ => false) ∈ cantorCylinder (true :: z) := by
      dsimp [cantorCylinder]
      intro i hi
      have h : prependCantor (true :: z) (fun _ => false) i = (true :: z)[i] := by
        exact isCantorPrefix_prepend (true :: z) (fun _ => false) i hi
      exact h
    have h2 : (fun _ => false) ∉ cantorCylinder (true :: z) := by
      dsimp [cantorCylinder]
      intro h
      have h' := h 0 (by simp)
      simp at h'
    simp [Set.indicator, h1, h2]

end Kolmogorov.MDLPrediction
