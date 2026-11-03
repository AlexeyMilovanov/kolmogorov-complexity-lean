/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.MDLPrediction.Class.Relative
import KolmogorovMathlib.MDLPrediction.Core.TwoPart

/-!
# Uniform class-to-measure index compiler

The computational field `toIndex` is one fixed total program for the presentation.
Its coding overhead is quantified before the varying class index and model.
Blueprint nodes: `enum:bridge`, `enum:compiler`.
-/

namespace Kolmogorov.MDLPrediction

open MeasureTheory

/-- A fixed class presentation compiles its indices into dyadic measure indices
with one additive prefix-code overhead. Blueprint node `enum:compiler`. -/
theorem enum_compiler (U : Map) (hU : IsOptimalPrefixConditional U)
    (A : EffectiveMixtureClass U hU) :
    ∃ cA : ℕ, ∀ i : ℕ, KPNat U (A.toIndex i) ≤ KPNat U i + cA := by
  have he₁ : Computable (fun i => natToBitString (A.toIndex i)) :=
    computable_natToBitString.comp A.toIndex_computable
  have hd : Computable bitStringToNat := computable_bitStringToNat
  have hde : ∀ n, bitStringToNat (natToBitString n) = n := bitStringToNat_natToBitString
  obtain ⟨c, hc⟩ := exists_const_KPPlain_comp_le U hU he₁ hd hde
  use c
  intro i
  have h := hc i
  rwa [KPNat_def, KPNat_def]
open scoped ENNReal

/-- Transfer an extended-natural upper bound with a finite right side to naturals. -/
private lemma ENat.toNat_le_add_of_le (x y : ENat)
    (c : ℕ) (h_top : y ≠ ⊤) (h : x ≤ y + c) :
    x.toNat ≤ y.toNat + c := by
  have hyc : y + c ≠ ⊤ := by
    intro h_c_top
    apply h_top
    exact WithTop.add_eq_top.mp h_c_top |>.resolve_right (WithTop.coe_ne_top)
  have h_le := ENat.toNat_le_toNat h hyc
  have h_add : (y + (c : ENat)).toNat = y.toNat + c := by
    calc (y + (c : ENat)).toNat = y.toNat + (c : ENat).toNat :=
        ENat.toNat_add h_top (WithTop.coe_ne_top : (c : ENat) ≠ ⊤)
      _ = y.toNat + c := by rw [ENat.toNat_natCast]
  rw [h_add] at h_le
  exact h_le

/-- Relative complexity controls absolute computable-measure complexity and the
two-part a priori bound. Blueprint node `enum:bridge`. -/
theorem measureComplexity_le_classComplexity (U : Map)
    (hU : IsOptimalPrefixConditional U) (A : EffectiveMixtureClass U hU) :
    ∃ cU cA : ℕ,
      (∀ P : Measure CantorSeq, IsProbabilityMeasure P →
        IsComputableMeasure P → ∀ x : BitString, 0 < cantorMass P x →
          KA x ≤ (computableMeasureComplexity U P).toNat -
            Real.logb 2 (cantorMass P x).toReal + cU) ∧
      ∀ Q ∈ A.carrier,
        (computableMeasureComplexity U Q).toNat ≤
          classComplexity U hU A Q + cA ∧
        ∀ x : BitString, 0 < cantorMass Q x →
          KA x ≤ (classComplexity U hU A Q : ℝ) -
            Real.logb 2 (cantorMass Q x).toReal + cU + cA := by
  obtain ⟨cU, hcU⟩ := KA_le_measure_code U hU
  obtain ⟨cA, hcA⟩ := enum_compiler U hU A
  use cU, cA
  refine ⟨hcU, fun Q hQ => ?_⟩
  obtain ⟨h_fin, i, hi_eq, hi_k⟩ := enum_relative_attained U hU A Q hQ
  have hi_spec := A.toIndex_spec i
  have heq : (A.A i).measure = Q := hi_eq
  have hi_spec' : IsComputableMeasureIndex Q (A.toIndex i) := by
    rw [← heq]
    exact hi_spec
  have h1 : computableMeasureComplexity U Q ≤ KPNat U (A.toIndex i) :=
    computableMeasureComplexity_le U hi_spec'
  have h2 : KPNat U (A.toIndex i) ≤ KPNat U i + cA := hcA i
  have h3 : computableMeasureComplexity U Q ≤ classComplexityENat U hU A Q + cA := by
    calc
      computableMeasureComplexity U Q ≤ KPNat U (A.toIndex i) := h1
      _ ≤ KPNat U i + (cA : ENat) := h2
      _ = classComplexityENat U hU A Q + cA := by rw [hi_k]
  have h_bound : (computableMeasureComplexity U Q).toNat ≤ classComplexity U hU A Q + cA := by
    apply ENat.toNat_le_add_of_le _ _ _ h_fin h3
  refine ⟨h_bound, fun x hx => ?_⟩
  have hP_prob : IsProbabilityMeasure Q := by
    rw [← heq]
    exact (A.A i).probability
  have hP_comp : IsComputableMeasure Q := by
    rw [← heq]
    exact (A.A i).computable
  have h_ka := hcU Q hP_prob hP_comp x hx
  have h_bound_r : ((computableMeasureComplexity U Q).toNat : ℝ) ≤
      (classComplexity U hU A Q : ℝ) + (cA : ℝ) := by
    have h_cast := (Nat.cast_le (α := ℝ)).mpr h_bound
    push_cast at h_cast
    exact h_cast
  calc KA x ≤ ((computableMeasureComplexity U Q).toNat : ℝ) -
        Real.logb 2 (cantorMass Q x).toReal + (cU : ℝ) := h_ka
    _ ≤ ((classComplexity U hU A Q : ℝ) + (cA : ℝ)) -
        Real.logb 2 (cantorMass Q x).toReal + (cU : ℝ) := by linarith
    _ = (classComplexity U hU A Q : ℝ) - Real.logb 2 (cantorMass Q x).toReal + cU + cA := by ring
end Kolmogorov.MDLPrediction
