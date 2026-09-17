import KolmogorovMathlib.MonotoneComplexity.GacsDayV2RequestWindow
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2L5Leaves
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2SubfamilyBridge
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2CornerReduced

/-!
# D5: packaging the geometry's charge as the V2 charged gray goal

Given the geometry's final charge `F` (nodup, valid at the call's anchor `a`,
H2, H3, H5, H4), the charge Boolean `familyGrayChargeAtB` holds at the frozen
constants with `epsDepth = a` (proof document v15.1, A2′: the certificate is
validity at the call's outer anchor), hence so does the executable charged
goal `familyChargedGrayGoalAtB` at `a`.  No root-allocation prefix (the
retired ANCHOR conjunct of v14) is involved.
-/

namespace Kolmogorov

/-- **The charge Boolean at the frozen constants**, at the call's anchor `a`,
from the geometry's conjuncts. -/
theorem grayChargedV2_charge_valid_of_validity
    {q L a e n T U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hpin : e = a + 8 * L + 3) (hae : a <= e)
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    (hmove : grayChargedRunMoveV2 q L a e n sigma A sm U =
      grayChargedRunMoveV2 q L a e n sigma A sm T)
    (F : FamilyGrayCharge)
    (hFnodup : (F.map Prod.snd).Nodup)
    (hFvalid : ∀ z, z ∈ F -> z.1 < n ∧
      z.2 ∈ newGrayCellsList a (e + grayTailNewLoss q L)
        (getFamilyAlloc (sm U) z.1 []) A)
    (hbeta : (n : Rat) * ((3 / 4 : Rat) * dyadicScale a) <=
      grayChargeMass (e + grayTailNewLoss q L) F)
    (hreq : halfAmplification (q + 1) *
        totalRootRequest n (grayChargedRunMoveV2 q L a e n sigma A sm U) <=
      grayChargeMass (e + grayTailNewLoss q L) F)
    (hcap : ∀ i : Fin n,
      grayChargeMass (e + grayTailNewLoss q L) (grayChargeAtRoot i.val F) <=
        4 * halfAmplification (q + 1) *
          getFamilyReq (grayChargedRunMoveV2 q L a e n sigma A sm U) i.val [])
    (hH4 : GrayChargedL5SubfamilyV2 q L e n
      (grayChargedRunMoveV2 q L a e n sigma A sm U) F) :
    familyGrayChargeAtB 4 (halfAmplification (q + 1)) (dyadicScale a)
      ((3 / 4 : Rat) * dyadicScale a) a (e + grayTailNewLoss q L) n A
      (grayChargedRunMoveV2 q L a e n sigma A sm U) (sm U) F = true := by
  classical
  have hwindow := grayChargedV2_final_request_window hpin hae replay.final
  unfold familyGrayChargeAtB
  simp only [Bool.and_eq_true, grayChargeCellsUniqueB_eq_true_iff,
    decide_eq_true_eq, List.all_eq_true]
  refine ⟨⟨⟨⟨⟨hFnodup, ?_⟩, ?_⟩, hbeta⟩, hreq⟩, ?_⟩
  · intro z hz
    exact hFvalid z hz
  · intro i hi
    have hi' := List.mem_range.mp hi
    have hw := hwindow ⟨i, hi'⟩
    rw [← hmove] at hw
    exact ⟨⟨hw.1, hw.2⟩, hcap ⟨i, hi'⟩⟩
  · intro I hI
    exact hH4 I hI

/-- **The weak gray goal at the anchor `a`** from the charge: the new gray
cells over the family allocation carry at least the charge's mass. -/
theorem grayChargedV2_weak_goal_of_charge
    {q L a e n T U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hpin : e = a + 8 * L + 3) (hae : a <= e)
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    (hmove : grayChargedRunMoveV2 q L a e n sigma A sm U =
      grayChargedRunMoveV2 q L a e n sigma A sm T)
    (F : FamilyGrayCharge)
    (hFnodup : (F.map Prod.snd).Nodup)
    (hFvalid : ∀ z, z ∈ F -> z.1 < n ∧
      z.2 ∈ newGrayCellsList a (e + grayTailNewLoss q L)
        (getFamilyAlloc (sm U) z.1 []) A)
    (hbeta : (n : Rat) * ((3 / 4 : Rat) * dyadicScale a) <=
      grayChargeMass (e + grayTailNewLoss q L) F)
    (hreq : halfAmplification (q + 1) *
        totalRootRequest n (grayChargedRunMoveV2 q L a e n sigma A sm U) <=
      grayChargeMass (e + grayTailNewLoss q L) F) :
    familyGrayGoalAtB (halfAmplification (q + 1))
      ((3 / 4 : Rat) * dyadicScale a) a (e + grayTailNewLoss q L) n A
      (grayChargedRunMoveV2 q L a e n sigma A sm U)
      (familyAllocatedOnList (List.range n) (sm U)) = true := by
  classical
  have hwindow := grayChargedV2_final_request_window hpin hae replay.final
  -- the charge's cells sit among the new gray cells over the family allocation
  have hsub_set : (F.map Prod.snd).toFinset ⊆
      (newGrayCellsList a (e + grayTailNewLoss q L)
        (familyAllocatedOnList (List.range n) (sm U)) A).toFinset := by
    intro p hp
    rw [List.mem_toFinset, List.mem_map] at hp
    obtain ⟨z, hz, rfl⟩ := hp
    have hv := hFvalid z hz
    obtain ⟨hlen, h1, h2⟩ := mem_newGrayCellsList.mp hv.2
    rw [List.mem_toFinset, mem_newGrayCellsList]
    refine ⟨hlen, ?_, h2⟩
    obtain ⟨c, hc, hcp⟩ := h1
    refine ⟨c, ?_, hcp⟩
    rw [familyAllocatedOnList, List.mem_flatMap]
    exact ⟨z.1, List.mem_range.mpr hv.1, hc⟩
  have hnodup2 := newGrayCellsList_nodup a (e + grayTailNewLoss q L)
    (familyAllocatedOnList (List.range n) (sm U)) A
  have hcard : (F.map Prod.snd).length <=
      (newGrayCellsList a (e + grayTailNewLoss q L)
        (familyAllocatedOnList (List.range n) (sm U)) A).length := by
    rw [← List.toFinset_card_of_nodup hFnodup,
      ← List.toFinset_card_of_nodup hnodup2]
    exact Finset.card_le_card hsub_set
  have hmass_le : grayChargeMass (e + grayTailNewLoss q L) F <=
      grayMassOfCount (e + grayTailNewLoss q L)
        (newGrayCount a (e + grayTailNewLoss q L)
          (familyAllocatedOnList (List.range n) (sm U)) A) := by
    have hlenF : F.length = (F.map Prod.snd).length := by simp
    rw [grayChargeMass, grayMassOfCount, grayMassOfCount, newGrayCount, hlenF]
    have hpos : (0 : Rat) <= (1 / 2 : Rat) ^ (e + grayTailNewLoss q L) := by
      positivity
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hpos
  -- the request lower bound from the H1 window
  have hsum : (n : Rat) * (dyadicScale a / 2) <=
      totalRootRequest n (grayChargedRunMoveV2 q L a e n sigma A sm U) := by
    unfold totalRootRequest
    have hsum_le : ∑ i : Fin n, (dyadicScale a / 2) <=
        ∑ i : Fin n, getFamilyReq
          (grayChargedRunMoveV2 q L a e n sigma A sm U) i.val [] := by
      refine Finset.sum_le_sum ?_
      intro i _
      have hw := (hwindow i).1
      rw [← hmove] at hw
      exact hw
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at hsum_le
    exact hsum_le
  have h1 : (1 : Rat) <= halfAmplification q := by
    unfold halfAmplification
    have hq : (0 : Rat) <= (q : Rat) / 2 :=
      div_nonneg (Nat.cast_nonneg q) (by norm_num)
    linarith
  have hk2 : (3 / 4 : Rat) <= halfAmplification (q + 1) / 2 := by
    rw [halfAmplification_succ]
    linarith
  have hhalf0 : (0 : Rat) <= halfAmplification (q + 1) := by
    rw [halfAmplification_succ]
    linarith
  have hnd : (0 : Rat) <= (n : Rat) * dyadicScale a :=
    mul_nonneg (Nat.cast_nonneg n) (dyadicScale_pos a).le
  have h3 : (n : Rat) * ((3 / 4 : Rat) * dyadicScale a) <=
      halfAmplification (q + 1) *
        totalRootRequest n (grayChargedRunMoveV2 q L a e n sigma A sm U) := by
    generalize hR : totalRootRequest n
      (grayChargedRunMoveV2 q L a e n sigma A sm U) = R at hsum ⊢
    calc (n : Rat) * ((3 / 4 : Rat) * dyadicScale a)
        = (3 / 4 : Rat) * ((n : Rat) * dyadicScale a) := by ring
      _ <= (halfAmplification (q + 1) / 2) * ((n : Rat) * dyadicScale a) :=
          mul_le_mul_of_nonneg_right hk2 hnd
      _ = halfAmplification (q + 1) * ((n : Rat) * (dyadicScale a / 2)) := by
          ring
      _ <= halfAmplification (q + 1) * R :=
          mul_le_mul_of_nonneg_left hsum hhalf0
  unfold familyGrayGoalAtB
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨le_trans hbeta hmass_le, le_trans hreq hmass_le⟩, h3⟩

/-- **The V2 charged gray goal at the anchor `a`** from the geometry's charge
(validity at `a`). -/
theorem grayChargedV2_chargedGoal_of_validity
    {q L a e n T U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hpin : e = a + 8 * L + 3) (hae : a <= e)
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    (hmove : grayChargedRunMoveV2 q L a e n sigma A sm U =
      grayChargedRunMoveV2 q L a e n sigma A sm T)
    (F : FamilyGrayCharge)
    (hFsub : F ∈ (familyGrayChargeUniverse n (e + grayTailNewLoss q L)).sublists)
    (hFnodup : (F.map Prod.snd).Nodup)
    (hFvalid : ∀ z, z ∈ F -> z.1 < n ∧
      z.2 ∈ newGrayCellsList a (e + grayTailNewLoss q L)
        (getFamilyAlloc (sm U) z.1 []) A)
    (hbeta : (n : Rat) * ((3 / 4 : Rat) * dyadicScale a) <=
      grayChargeMass (e + grayTailNewLoss q L) F)
    (hreq : halfAmplification (q + 1) *
        totalRootRequest n (grayChargedRunMoveV2 q L a e n sigma A sm U) <=
      grayChargeMass (e + grayTailNewLoss q L) F)
    (hcap : ∀ i : Fin n,
      grayChargeMass (e + grayTailNewLoss q L) (grayChargeAtRoot i.val F) <=
        4 * halfAmplification (q + 1) *
          getFamilyReq (grayChargedRunMoveV2 q L a e n sigma A sm U) i.val [])
    (hH4 : GrayChargedL5SubfamilyV2 q L e n
      (grayChargedRunMoveV2 q L a e n sigma A sm U) F) :
    familyChargedGrayGoalAtB 4 (halfAmplification (q + 1)) (dyadicScale a)
      ((3 / 4 : Rat) * dyadicScale a) a (e + grayTailNewLoss q L) n A
      (grayChargedRunMoveV2 q L a e n sigma A sm U) (sm U) = true := by
  unfold familyChargedGrayGoalAtB
  simp only [Bool.and_eq_true, List.any_eq_true]
  exact ⟨grayChargedV2_weak_goal_of_charge hpin hae replay hmove F hFnodup
      hFvalid hbeta hreq,
    F, hFsub,
    grayChargedV2_charge_valid_of_validity hpin hae replay hmove F hFnodup
      hFvalid hbeta hreq hcap hH4⟩

end Kolmogorov
