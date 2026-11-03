/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.MDLPrediction.Mean.Quotients
import KolmogorovMathlib.MDLPrediction.Mean.Support
import KolmogorovMathlib.MonotoneComplexity.TreeSemimeasure

/-!
# The first-exit mean tree

The product tests the two parent masses at each position. A first one-zero child is
included; all strict descendants have a zero factor. The tree has a child-sum
inequality, with exact additivity only at common-positive parents.
Blueprint nodes: `exp:mean-tree`.
-/

namespace Kolmogorov.MDLPrediction

open MeasureTheory
open scoped ENNReal

/-- The mean of the two bit conditionals at a common-positive parent, or zero.
Blueprint node `exp:mean-tree`. -/
noncomputable def meanFactor (P Q : Measure CantorSeq) (y : BitString) (b : Bool) : ℝ≥0∞ :=
  if 0 < cantorMass P y ∧ 0 < cantorMass Q y then
    ENNReal.ofReal ((condProb (cantorMass P) y b + condProb (cantorMass Q) y b) / 2)
  else 0

/-- The first-exit mean-product mass of a finite word. Blueprint node `exp:mean-tree`. -/
noncomputable def meanTree (P Q : Measure CantorSeq) (x : BitString) : ℝ≥0∞ :=
  ∏ i : Fin x.length, meanFactor P Q (x.take i.val) (x[i.val]'i.isLt)

/-- The mean product has root mass one and satisfies the continuous-tree
semimeasure inequality. Blueprint node `exp:mean-tree`. -/
theorem exp_mean_tree (P Q : Measure CantorSeq) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] : IsContinuousTreeSemimeasure (meanTree P Q) := by
  refine ⟨by simp [meanTree], fun y => ?_⟩
  have hstep : ∀ b : Bool, meanTree P Q (y ++ [b]) = meanTree P Q y * meanFactor P Q y b := by
    intro b
    unfold meanTree
    rw [← Fin.prod_congr' _ (by simp : y.length + 1 = (y ++ [b]).length),
      Fin.prod_univ_castSucc]
    congr 1
    · refine Finset.prod_congr rfl fun i _ => ?_
      simp [List.take_append_of_le_length (Nat.le_of_lt i.isLt),
        List.getElem_append_left i.isLt]
    · simp
  have hsum : meanFactor P Q y false + meanFactor P Q y true ≤ 1 := by
    unfold meanFactor
    split_ifs with h
    · have hP := condProb_cantorMass_add_eq_one P h.1.ne'
      have hQ := condProb_cantorMass_add_eq_one Q h.2.ne'
      have h0 := condProb_nonneg (cantorMass P) y false
      have h1 := condProb_nonneg (cantorMass P) y true
      have h2 := condProb_nonneg (cantorMass Q) y false
      have h3 := condProb_nonneg (cantorMass Q) y true
      rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
      apply ENNReal.ofReal_le_one.mpr
      linarith
    · simp
  rw [hstep false, hstep true, ← mul_add]
  exact mul_le_of_le_one_right' hsum

/-- On common-positive strict prefixes, the tree is exactly the mean product,
including a first one-zero child. Blueprint node `exp:mean-tree`. -/
theorem meanTree_product (P Q : Measure CantorSeq) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (x : BitString)
    (hcommon : CommonPositivePrefixes P Q x) :
    meanTree P Q x = ∏ i : Fin x.length,
      ENNReal.ofReal ((condProb (cantorMass P) (x.take i.val) (x[i.val]'i.isLt) +
        condProb (cantorMass Q) (x.take i.val) (x[i.val]'i.isLt)) / 2) := by
  unfold meanTree
  apply Finset.prod_congr rfl
  intro i _
  unfold meanFactor
  have h := hcommon i.val i.isLt
  simp only [h, and_self, ite_true]

/-- The mean tree vanishes on strict descendants of a first zero-mass exit.
Blueprint node `exp:mean-tree`. -/
theorem meanTree_killed (P Q : Measure CantorSeq) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (x y : BitString)
    (hzero : cantorMass P x = 0 ∨ cantorMass Q x = 0)
    (hprefix : x <+: y) (hlen : x.length < y.length) :
    meanTree P Q y = 0 := by
  unfold meanTree
  have h_in : (⟨x.length, hlen⟩ : Fin y.length) ∈ Finset.univ := Finset.mem_univ _
  apply Finset.prod_eq_zero h_in
  dsimp
  have hy_take : y.take x.length = x := by
    cases hprefix with | intro c hc =>
      rw [←hc, List.take_left]
  rw [hy_take]
  unfold meanFactor
  split_ifs with h
  · cases hzero with
    | inl hzeroP => rw [hzeroP] at h; exact False.elim (lt_irrefl _ h.1)
    | inr hzeroQ => rw [hzeroQ] at h; exact False.elim (lt_irrefl _ h.2)
  · rfl

end Kolmogorov.MDLPrediction
