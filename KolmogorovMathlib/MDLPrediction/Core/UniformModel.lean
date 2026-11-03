/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.MDLPrediction.Core.Model
import KolmogorovMathlib.MonotoneComplexity.CylinderMass
import KolmogorovMathlib.AlgorithmicRandomness.ComputableMeasure

/-!
# Uniform computable competitor

The uniform measure gives a positive-mass eligible model at every finite string.

Blueprint nodes: `base:uniform-positive`.
-/

namespace Kolmogorov.MDLPrediction

open MeasureTheory
open scoped ENNReal

/-- The uniform measure is proper, computable, and positive on every cylinder.
Blueprint node `base:uniform-positive`. -/
theorem base_uniform_positive (x : BitString) :
    IsProbabilityMeasure uniformMeasure ∧ IsComputableMeasure uniformMeasure ∧
      cantorMass uniformMeasure x = (2 : ℝ≥0∞)⁻¹ ^ x.length ∧
        0 < cantorMass uniformMeasure x := by
  refine ⟨inferInstance, isComputableMeasure_uniform, cantorMass_uniformMeasure x, ?_⟩
  rw [cantorMass_uniformMeasure]
  have hpos : (0 : ℝ≥0∞) < (2 : ℝ≥0∞)⁻¹ := by norm_num
  exact ENNReal.pow_pos hpos x.length

end Kolmogorov.MDLPrediction
