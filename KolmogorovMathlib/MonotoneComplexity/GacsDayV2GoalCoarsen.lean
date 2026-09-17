import KolmogorovMathlib.MonotoneComplexity.GacsDayGrayCharge
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailConstruction
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2ReserveSupport

/-!
# Coarsening the anchor depth of the charged gray goal

The executable gray goal `familyGrayGoalAtB` and the designated-gray
certificate `familyGrayChargeAtB` mention the anchor depth `epsDepth` only
through the new-gray cell test `newGrayCellsList epsDepth deltaDepth S U`,
and that test is antitone in `epsDepth`: if the `epsDepth`-prefix of a cell
is comparable with an allocated cylinder, so is every shorter prefix.  Hence
a goal certified at a fine anchor `e1` is also certified at every coarser
anchor `e0 ≤ e1`, with the very same designated-gray certificate.
-/

namespace Kolmogorov

/-- The new-gray count is antitone in the anchor depth: the fine list is a
duplicate-free sublist (up to permutation) of the coarse one. -/
lemma newGrayCount_coarsen_le {e0 e1 delta : Nat} (h01 : e0 <= e1) (S U : List BitString) :
    newGrayCount e1 delta S U <= newGrayCount e0 delta S U := by
  unfold newGrayCount
  exact List.Subperm.length_le
    (List.subperm_of_subset (newGrayCellsList_nodup e1 delta S U)
      fun _ hx => grayChargedV2_newGrayCell_coarsen h01 hx)

/-- The gray mass of the count is antitone in the anchor depth. -/
lemma grayMassOfCount_newGrayCount_coarsen_le {e0 e1 delta : Nat} (h01 : e0 <= e1)
    (S U : List BitString) :
    grayMassOfCount delta (newGrayCount e1 delta S U) <=
      grayMassOfCount delta (newGrayCount e0 delta S U) := by
  unfold grayMassOfCount
  exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (newGrayCount_coarsen_le h01 S U))
    (by positivity)

/-- The executable gray goal survives coarsening of the anchor depth. -/
lemma familyGrayGoalAtB_coarsen {kappa beta : Rat} {e0 e1 delta n : Nat} {A : Allocation}
    {c : FamilyClientMove} {sList : List BitString} (h01 : e0 <= e1)
    (h : familyGrayGoalAtB kappa beta e1 delta n A c sList = true) :
    familyGrayGoalAtB kappa beta e0 delta n A c sList = true := by
  have hmass := grayMassOfCount_newGrayCount_coarsen_le h01 sList A (delta := delta)
  simp only [familyGrayGoalAtB, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact ⟨⟨h1.trans hmass, h2.trans hmass⟩, h3⟩

/-- A designated-gray certificate at the fine anchor `e1` is a certificate at
every coarser anchor `e0 ≤ e1`: only the new-gray membership of the charged
cells mentions the anchor, and it coarsens cell by cell. -/
lemma familyGrayChargeAtB_coarsen {eta kappa alpha beta : Rat} {e0 e1 delta n : Nat}
    {A : Allocation} {c : FamilyClientMove} {s : FamilyServerMove} {G : FamilyGrayCharge}
    (h01 : e0 <= e1)
    (h : familyGrayChargeAtB eta kappa alpha beta e1 delta n A c s G = true) :
    familyGrayChargeAtB eta kappa alpha beta e0 delta n A c s G = true := by
  simp only [familyGrayChargeAtB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
    at h ⊢
  obtain ⟨⟨⟨⟨⟨hU, hcells⟩, hwin⟩, hbeta⟩, hkappa⟩, hsub⟩ := h
  refine ⟨⟨⟨⟨⟨hU, ?_⟩, hwin⟩, hbeta⟩, hkappa⟩, hsub⟩
  intro z hz
  obtain ⟨hzn, hzcell⟩ := hcells z hz
  exact ⟨hzn, grayChargedV2_newGrayCell_coarsen h01 hzcell⟩

/-- The executable charged gray goal survives coarsening of the anchor depth;
the certificate universe depends only on the final depth, so the same
certificate is reused. -/
theorem familyChargedGrayGoalAtB_coarsen {eta kappa alpha beta : Rat} {e0 e1 delta n : Nat}
    {A : Allocation} {c : FamilyClientMove} {s : FamilyServerMove} (h01 : e0 <= e1)
    (h : familyChargedGrayGoalAtB eta kappa alpha beta e1 delta n A c s = true) :
    familyChargedGrayGoalAtB eta kappa alpha beta e0 delta n A c s = true := by
  unfold familyChargedGrayGoalAtB at h ⊢
  rw [Bool.and_eq_true, List.any_eq_true] at h ⊢
  obtain ⟨hgoal, G, hG, hcharge⟩ := h
  exact ⟨familyGrayGoalAtB_coarsen h01 hgoal, G, hG, familyGrayChargeAtB_coarsen h01 hcharge⟩

end Kolmogorov
