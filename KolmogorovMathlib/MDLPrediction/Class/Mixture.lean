/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.MDLPrediction.Class.Presentation

/-!
# Cylinder mass of a finite class mixture

The presentation's mixture equation counts repeated indices separately.
Blueprint nodes: `enum:mix-mass`.
-/

namespace Kolmogorov.MDLPrediction

open MeasureTheory
open scoped ENNReal

/-- Every occurrence in a nonempty mixture contributes its share of cylinder mass.
Blueprint node `enum:mix-mass`. -/
theorem enum_mix_mass (U : Map) (hU : IsOptimalPrefixConditional U)
    (A : EffectiveMixtureClass U hU) (G : List ℕ) (hne : G ≠ [])
    (i : ℕ) (hi : i ∈ G) (x : BitString) :
    (G.length : ℝ≥0∞)⁻¹ * cantorMass (A.model i) x ≤
      cantorMass (A.model (A.mix G)) x := by
  have h_mix_eq := A.mix_eq G hne
  unfold cantorMass EffectiveMixtureClass.model
  rw [h_mix_eq]
  rw [Measure.smul_apply, smul_eq_mul]
  gcongr
  apply List.single_le_sum
  · intro j _
    exact OrderBot.bot_le j
  · simp only [List.mem_map]
    exact ⟨i, hi, rfl⟩
end Kolmogorov.MDLPrediction
