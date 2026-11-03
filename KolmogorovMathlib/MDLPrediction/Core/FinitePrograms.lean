/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.MDLPrediction.Core.Index
import KolmogorovMathlib.MonotoneComplexity.Omega.SolovayFunctions.ExistenceFlatten
import KolmogorovMathlib.Prefix.TotalCountingBound
import KolmogorovMathlib.AlgorithmicStatistics.Selector

/-!
# Finite prefix-complexity sublevels

Complexity sublevels of numeric indices and extensional computable measures are finite.
The measure count uses attained indices and the fact that one index determines one measure.

Blueprint nodes: `base:finite`, `base:program-count`.
-/

namespace Kolmogorov.MDLPrediction

open MeasureTheory

/-- Fewer than `2^(a+1)` outputs have prefix complexity at most `a`.
Blueprint node `base:program-count`. -/
theorem base_program_count (U : Map) (a : ℕ) :
    (Set.Finite {i : ℕ | KPNat U i ≤ a}) ∧
      Set.ncard {i : ℕ | KPNat U i ≤ a} < 2 ^ (a + 1) := by
  have h1 : Set.Finite {i : ℕ | KPNat U i ≤ a} := kpNatSublevel_finite U a
  have h2 : Set.ncard {i : ℕ | KPNat U i ≤ a} ≤ (boundedPrograms a).length := by
    let A : Finset ℕ := h1.toFinset
    have hA : ∀ x ∈ A, KPNat U x ≤ (a : ENat) := fun x hx => by
      exact (Set.Finite.mem_toFinset h1).mp hx
    let B : Finset BitString := A.image natToBitString
    have hB : ∀ x ∈ B, KPPlain U x ≤ (a : ENat) := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
      exact hA y hy
    have hcard : B.card ≤ (boundedPrograms a).length :=
      card_KPPlain_le_boundedPrograms_length U a B hB
    have heq : B.card = A.card := Finset.card_image_of_injective A natToBitString_injective
    have h_ncard_eq : Set.ncard {i : ℕ | KPNat U i ≤ a} = A.card := by
      exact Set.ncard_eq_toFinset_card _ h1
    linarith
  have h3 : (boundedPrograms a).length < 2 ^ (a + 1) := by
    exact length_boundedPrograms_lt a
  exact ⟨h1, lt_of_le_of_lt h2 h3⟩

/-- The extensional computable-probability-measure complexity sublevel is finite.
Blueprint node `base:finite`. -/
theorem finite_models_complexity_le (U : Map) (hU : IsOptimalPrefixConditional U)
    (a : ℕ) :
    (Set.Finite {P : Measure CantorSeq | IsProbabilityMeasure P ∧
      IsComputableMeasure P ∧ (computableMeasureComplexity U P).toNat ≤ a}) ∧
    Set.ncard {P : Measure CantorSeq | IsProbabilityMeasure P ∧
      IsComputableMeasure P ∧ (computableMeasureComplexity U P).toNat ≤ a} <
        2 ^ (a + 1) := by
  let S := {P : Measure CantorSeq | IsProbabilityMeasure P ∧
      IsComputableMeasure P ∧ (computableMeasureComplexity U P).toNat ≤ a}
  let T := {e : ℕ | KPNat U e ≤ a}
  have hT_fin : T.Finite := (base_program_count U a).1
  have hT_card : T.ncard < 2 ^ (a + 1) := (base_program_count U a).2
  have h_ex : ∀ P ∈ S, ∃ e : ℕ, IsComputableMeasureIndex P e ∧
      KPNat U e = computableMeasureComplexity U P := by
    intro P hP
    have _inst : IsProbabilityMeasure P := hP.1
    have hcomp : IsComputableMeasure P := hP.2.1
    exact (base_complexity_attained U hU P hcomp).2
  let f (P : Measure CantorSeq) : ℕ := open Classical in
    if hP : P ∈ S then choose (h_ex P hP) else 0
  have hf_maps : ∀ P ∈ S, f P ∈ T := by
    intro P hP
    simp only [f, hP, dite_eq_left]
    change KPNat U (Classical.choose (h_ex P hP)) ≤ (a : ENat)
    have h_spec := Classical.choose_spec (h_ex P hP)
    have hPbound : (computableMeasureComplexity U P).toNat ≤ a := hP.2.2
    have H2 : KPNat U (Classical.choose (h_ex P hP)) = computableMeasureComplexity U P :=
      h_spec.2
    have _inst : IsProbabilityMeasure P := hP.1
    have h_ne_top : computableMeasureComplexity U P ≠ ⊤ :=
      (base_complexity_attained U hU P hP.2.1).1
    have h_complexity_le : computableMeasureComplexity U P ≤ (a : ENat) := by
      rw [← ENat.natCast_toNat h_ne_top]
      exact_mod_cast hPbound
    rw [H2]
    exact h_complexity_le
  have h_inj : Set.InjOn f S := by
    intro P hP Q hQ h_eq
    simp only [f, hP, hQ, dite_eq_left] at h_eq
    have _inst : IsProbabilityMeasure P := hP.1
    have _inst2 : IsProbabilityMeasure Q := hQ.1
    have h1 := (Classical.choose_spec (h_ex P hP)).1
    have h2 := h_eq ▸ (Classical.choose_spec (h_ex Q hQ)).1
    exact IsComputableMeasureIndex.measure_eq h1 h2
  have hf_img : f '' S ⊆ T := Set.image_subset_iff.mpr hf_maps
  have hS_fin : S.Finite := Set.Finite.of_finite_image (hT_fin.subset hf_img) h_inj
  have h_ncard := Set.ncard_le_ncard_of_injOn f hf_maps h_inj hT_fin
  exact ⟨hS_fin, lt_of_le_of_lt h_ncard hT_card⟩

/-- The corresponding sublevel of numeric measure indices has the same bound.
Blueprint node `base:finite`. -/
theorem finite_model_indices_complexity_le (U : Map) (a : ℕ) :
    (Set.Finite {e : ℕ | KPNat U e ≤ a}) ∧
      Set.ncard {e : ℕ | KPNat U e ≤ a} < 2 ^ (a + 1) := by
  exact base_program_count U a

end Kolmogorov.MDLPrediction
