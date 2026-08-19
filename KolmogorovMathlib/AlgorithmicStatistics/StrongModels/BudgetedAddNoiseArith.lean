import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Basic

/-!
# Arithmetic for charged add-noise strata

The budget-scale heavy-truncation route assigns a stratum charge to both the
description-complexity coordinate and the multiplicity exponent.  This file
records the exact truncated-subtraction cancellation used after applying the
many-descriptions complexity-drop theorem.
-/

namespace Kolmogorov

/-- A charge added to both the starting complexity and the multiplicity gain
cancels completely, even with natural-number truncated subtraction. -/
theorem addNoise_charge_cancels (complexity charge gain loss : Nat) :
    complexity + charge - (gain + charge - loss) ≤
      complexity - gain + loss := by
  omega

end Kolmogorov
