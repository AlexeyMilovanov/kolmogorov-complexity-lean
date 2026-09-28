import KolmogorovMathlib.MonotoneComplexity.TreeSemimeasure
import KolmogorovMathlib.MonotoneComplexity.TreeMixture
import KolmogorovMathlib.MonotoneComplexity.TreeSemimeasureEnumeration

/-!
# Existence of a maximal lower semicomputable continuous semimeasure

The mixture of the standard enumeration of lower semicomputable continuous tree semimeasures is
again one (`treeMixture_isLowerSemicomputableContinuousSemimeasure`), and it dominates every
member of the enumeration up to a multiplicative constant, giving
`exists_maximal_lowerSemicomputableContinuousSemimeasure`. This is the existence statement behind
the a priori probability on the tree.
-/

open scoped ENNReal

namespace Kolmogorov

/-- The mixture of the standard enumeration is itself a lower semicomputable continuous semimeasure.
-/
theorem treeMixture_isLowerSemicomputableContinuousSemimeasure :
    IsLowerSemicomputableContinuousSemimeasure (continuousTreeMixture treeLSCEnum) := by
  apply continuousTreeMixture_dyadicWeight_isLowerSemicomputableContinuousSemimeasure
    (a := fun i s out _ => treeSanitize (fun s out _ => makeMono (approxEnum i) s out []) s out)
  · intro i s out ctx
    exact treeSanitize_stage_mono _ (fun s out _ => makeMono_mono _ s out []) s out
  · intro i out ctx
    rfl
  · intro i
    exact (treeLSCEnum_isLowerSemicomputableContinuousSemimeasure i).1
  · exact treeLSCEnumApprox_uniform_computable

-- Theorem 78
/-- There is a lower semicomputable continuous semimeasure dominating every other one up to a
multiplicative constant. -/
theorem exists_maximal_lowerSemicomputableContinuousSemimeasure :
    ∃ a : BitString → ℝ≥0∞, IsLowerSemicomputableContinuousSemimeasure a ∧
    ∀ a', IsLowerSemicomputableContinuousSemimeasure a' →
      ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ ∀ x, a' x ≤ c * a x := by
  use continuousTreeMixture treeLSCEnum
  constructor
  · exact treeMixture_isLowerSemicomputableContinuousSemimeasure
  · intro a' ha'
    obtain ⟨i, hi⟩ := treeLSCEnum_complete ha'
    use (dyadicWeight i)⁻¹
    constructor
    · exact ENNReal.inv_ne_top.mpr (dyadicWeight_pos i).ne'
    · intro x
      have h1 := continuousTreeMixture_dominates_component treeLSCEnum i x
      rw [hi] at h1
      calc
        a' x = (dyadicWeight i)⁻¹ * (dyadicWeight i * a' x) := by
          rw [← mul_assoc]
          rw [ENNReal.inv_mul_cancel (dyadicWeight_pos i).ne' (dyadicWeight_ne_top i)]
          rw [one_mul]
        _ ≤ (dyadicWeight i)⁻¹ * continuousTreeMixture treeLSCEnum x := by
          gcongr

end Kolmogorov
