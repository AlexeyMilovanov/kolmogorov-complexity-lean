/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.MDLPrediction.Core.Model

/-!
# Indices and attained complexity of computable models

The existing computable-measure index interface gives both directions of the index bridge.
For an optimal prefix machine, the model's index complexity is finite and attained.

Blueprint nodes: `base:complexity-attained`, `base:index-bridge`.
-/

namespace Kolmogorov.MDLPrediction

open MeasureTheory

/-- Computability of a measure is equivalent to existence of a numeric index.
Blueprint node `base:index-bridge`. -/
theorem base_index_bridge (P : Measure CantorSeq) :
    IsComputableMeasure P ↔ ∃ e : ℕ, IsComputableMeasureIndex P e := by
  exact isComputableMeasure_iff_exists_index P

/-- A computable proper measure has an index attaining its finite model complexity.
Blueprint node `base:complexity-attained`. -/
theorem base_complexity_attained (U : Map) (hU : IsOptimalPrefixConditional U)
    (P : Measure CantorSeq) [IsProbabilityMeasure P] (hP : IsComputableMeasure P) :
    computableMeasureComplexity U P ≠ ⊤ ∧
      ∃ e : ℕ, IsComputableMeasureIndex P e ∧
        KPNat U e = computableMeasureComplexity U P := by
  constructor
  · exact computableMeasureComplexity_ne_top U hU hP
  · exact exists_index_KPNat_eq_computableMeasureComplexity U hP

end Kolmogorov.MDLPrediction
