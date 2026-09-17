import KolmogorovMathlib.MonotoneComplexity.GacsDayGrayArea
import KolmogorovMathlib.MonotoneComplexity.GacsDayMass

/-!
# Bridge between Gray Area calculus and Gács-Day Game Allocation
-/

namespace Kolmogorov
open MeasureTheory ENNReal

/-- The new gray area of an allocation against an unavailable allocation, read as finite sets. -/
def grayCellsOfAlloc (epsDepth deltaDepth : ℕ) (A U : Allocation) : Finset BitString :=
  newGrayCells epsDepth deltaDepth A.toFinset U.toFinset

/-- The uniform mass of the gray cells is at most `1` (from the probability measure bound).
The earlier statement `≤ allocationMass A` was false when `A` contains strings longer than
`epsDepth`: e.g. `A = [[0,0]]`, `eps = delta = 1` gives gray mass `1/2 > 1/4 = allocationMass A`. -/
theorem grayCellMass_le_one {epsDepth deltaDepth : ℕ} (A U : Allocation) :
    ((grayCellsOfAlloc epsDepth deltaDepth A U).card : ℝ≥0∞) * (2⁻¹ : ℝ≥0∞) ^ deltaDepth ≤ 1 := by
  rw [grayCellsOfAlloc, ← uniformMeasure_newGrayCells]
  exact prob_le_one

/-- The accounting inequality behind the charged bookkeeping: for `kappa ≥ 1` and
`gamma ≤ m * eps`, amplifying by `kappa + 1/2` after adding the slack
`m * eps / (6 * kappa)` stays below `kappa * gamma + (3/4) * (m * eps)`. -/
theorem gray_accounting_inequality
    {gamma m eps kappa : ℚ} (hk : 1 ≤ kappa) (hm : 0 ≤ m * eps)
    (hle : gamma ≤ m * eps) :
    (kappa + 1/2) * (gamma + m * eps / (6 * kappa))
      ≤ kappa * gamma + (3/4) * (m * eps) := by
  set me := m * eps with hme_def
  have hk0 : (0 : ℚ) < kappa := lt_of_lt_of_le one_pos hk
  have hk_ne : (kappa : ℚ) ≠ 0 := ne_of_gt hk0
  have key : (kappa + 1/2) * (gamma + me / (6 * kappa)) =
    kappa * gamma + me / 6 + gamma / 2 + me / (12 * kappa) := by
    field_simp
    ring
  rw [key]
  have h12 : (12 : ℚ) ≤ 12 * kappa := by linarith
  have hme12k : me / (12 * kappa) ≤ me / 12 := by
    apply div_le_div_of_nonneg_left hm (by norm_num : (0:ℚ) < 12) h12
  linarith [mul_le_mul_of_nonneg_right hle (show (0:ℚ) ≤ 1/2 by norm_num)]


end Kolmogorov
