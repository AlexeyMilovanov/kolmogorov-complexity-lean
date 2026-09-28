import KolmogorovMathlib.MonotoneComplexity.GacsDayV2ReserveSupport

/-!
# The V2 source ledger flatten (Stage D5, part i)

All accepted rounds' anchored charge sources — advantage and spend — in one
list; the flattened physical charge; its global cell uniqueness (within-round
cylinder uniqueness plus the certificate-driven cross-round chase); and its
exact mass.
-/

namespace Kolmogorov

open Classical in
/-- All rounds' anchored source records, in frozen order. -/
noncomputable def grayChargedFrozenSourcesV2
    {q L a e n T U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    (hU : T + 1 <= U) (hae : a <= e) :
    List (GrayChargedChargeSourceV2 q L a e n A
      (grayChargedRunMoveV2 q L a e n sigma A sm U) (sm U)) :=
  (List.finRange (grayChargedRunStateV2 (n := n)
      (b := grayTailBranch q L a e)
      q L a e sigma A sm (T + 1)).core.frozen.length).flatMap fun i =>
    if hfine : grayCallDepth q e <=
        ((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm (T + 1)).core.frozen[i.val]).blockAnchor then
      grayChargedRoundSourcesAdvV2 hsm replay hU
        (List.getElem_mem i.isLt) hae hfine
    else
      grayChargedRoundSourcesSpendV2 hsm replay hU
        (List.getElem_mem i.isLt) hae hfine

/-- Flatten the V2 source records to the physical charge. -/
def grayChargedSourceChargeV2
    {q L a e n : Nat} {A : Allocation}
    {c : FamilyClientMove} {s : FamilyServerMove}
    (sources : List (GrayChargedChargeSourceV2 q L a e n A c s)) :
    FamilyGrayCharge :=
  sources.flatMap GrayChargedChargeSourceV2.transported

/-- The charge of a flattened family of V2 sources is the flattening of their charges. -/
lemma grayChargedSourceChargeV2_flatMap {alpha : Type _}
    {q L a e n : Nat} {A : Allocation}
    {c : FamilyClientMove} {s : FamilyServerMove}
    (l : List alpha)
    (f : alpha -> List (GrayChargedChargeSourceV2 q L a e n A c s)) :
    grayChargedSourceChargeV2 (l.flatMap f) =
      l.flatMap fun x => grayChargedSourceChargeV2 (f x) := by
  simp [grayChargedSourceChargeV2, List.flatMap_assoc]

/-- The advantage builder's flattened charge is the round transport. -/
lemma grayChargedRoundSourcesAdvV2_charge_eq
    {q L a e n T U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    (hU : T + 1 <= U)
    {p : GrayTailRoundV2 n (grayTailBranch q L a e)}
    (hp : p ∈ (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm (T + 1)).core.frozen)
    (hae : a <= e)
    (hfine : grayCallDepth q e <= p.blockAnchor) :
    grayChargedSourceChargeV2
        (grayChargedRoundSourcesAdvV2 hsm replay hU hp hae hfine) =
      grayChargedTransportRound (e + grayTailNewLoss q L) p.slots
        (grayChargedLocalChargeOfBlockGoal
          (grayChargedRunStateV2_frozen_adv_goal q L a e sigma A sm (T + 1)
            hp hae hfine)) := by
  rw [grayChargedSourceChargeV2, grayChargedRoundSourcesAdvV2,
    grayChargedTransportRound,
    grayChargedList_flatMap_eq_flatMap_id, List.map_ofFn]
  rfl

/-- The spend builder's flattened charge is the round transport. -/
lemma grayChargedRoundSourcesSpendV2_charge_eq
    {q L a e n T U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    (hU : T + 1 <= U)
    {p : GrayTailRoundV2 n (grayTailBranch q L a e)}
    (hp : p ∈ (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm (T + 1)).core.frozen)
    (hae : a <= e)
    (hcoarse : ¬ grayCallDepth q e <= p.blockAnchor) :
    grayChargedSourceChargeV2
        (grayChargedRoundSourcesSpendV2 hsm replay hU hp hae hcoarse) =
      grayChargedTransportRound (e + grayTailNewLoss q L) p.slots
        (grayChargedLocalChargeOfBlockSpendGoal
          (grayChargedRunStateV2_frozen_spend_goal q L a e sigma A sm (T + 1)
            hp hcoarse).choose_spec.2.2.2) := by
  rw [grayChargedSourceChargeV2, grayChargedRoundSourcesSpendV2,
    grayChargedTransportRound,
    grayChargedList_flatMap_eq_flatMap_id, List.map_ofFn]
  rfl

/-- The per-round flattened charge, uniformly. -/
lemma grayChargedFrozenSourcesV2_round_charge
    {q L a e n T U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    (hU : T + 1 <= U) (hae : a <= e)
    (i : Fin (grayChargedRunStateV2 (n := n)
      (b := grayTailBranch q L a e)
      q L a e sigma A sm (T + 1)).core.frozen.length) :
    grayChargedSourceChargeV2
        (open Classical in
        if hfine : grayCallDepth q e <=
            ((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
              q L a e sigma A sm (T + 1)).core.frozen[i.val]).blockAnchor then
          grayChargedRoundSourcesAdvV2 hsm replay hU
            (List.getElem_mem i.isLt) hae hfine
        else
          grayChargedRoundSourcesSpendV2 hsm replay hU
            (List.getElem_mem i.isLt) hae hfine) =
      grayChargedTransportRound (e + grayTailNewLoss q L)
        ((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm (T + 1)).core.frozen[i.val]).slots
        (grayChargedRoundLocalChargeV2 hae _ (List.getElem_mem i.isLt)) := by
  by_cases hfine : grayCallDepth q e <=
      ((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm (T + 1)).core.frozen[i.val]).blockAnchor
  · rw [dif_pos hfine,
      grayChargedRoundSourcesAdvV2_charge_eq hsm replay hU _ hae hfine]
    congr 1
    rw [grayChargedRoundLocalChargeV2, dif_pos hfine]
  · rw [dif_neg hfine,
      grayChargedRoundSourcesSpendV2_charge_eq hsm replay hU _ hae hfine]
    congr 1
    rw [grayChargedRoundLocalChargeV2, dif_neg hfine]

/-- The full flattened charge in transport form. -/
lemma grayChargedFrozenSourcesV2_charge_eq
    {q L a e n T U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    (hU : T + 1 <= U) (hae : a <= e) :
    grayChargedSourceChargeV2
        (grayChargedFrozenSourcesV2 hsm replay hU hae) =
      (List.finRange (grayChargedRunStateV2 (n := n)
          (b := grayTailBranch q L a e)
          q L a e sigma A sm (T + 1)).core.frozen.length).flatMap fun i =>
        grayChargedTransportRound (e + grayTailNewLoss q L)
          ((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm (T + 1)).core.frozen[i.val]).slots
          (grayChargedRoundLocalChargeV2 hae _ (List.getElem_mem i.isLt)) := by
  rw [grayChargedFrozenSourcesV2, grayChargedSourceChargeV2_flatMap]
  refine List.flatMap_congr ?_
  intro i _
  exact grayChargedFrozenSourcesV2_round_charge hsm replay hU hae i

/-- Within-round cell uniqueness of the uniform round charge transport. -/
lemma grayChargedRoundLocalChargeV2_transport_nodup
    {q L a e n t : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hae : a <= e)
    (p : GrayTailRoundV2 n (grayTailBranch q L a e))
    (hp : p ∈ (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).core.frozen) :
    ((grayChargedTransportRound (e + grayTailNewLoss q L) p.slots
      (grayChargedRoundLocalChargeV2 hae p hp)).map Prod.snd).Nodup := by
  unfold grayChargedRoundLocalChargeV2
  split
  next hfine =>
    exact grayChargedTransportRound_nodup_of_charge
      (grayChargedLocalChargeOfBlockGoal_valid
        (grayChargedRunStateV2_frozen_adv_goal q L a e sigma A sm t hp
          hae hfine))
  next hfine =>
    exact grayChargedTransportRound_nodup_of_charge
      (grayChargedLocalChargeOfBlockSpendGoal_valid
        (grayChargedRunStateV2_frozen_spend_goal q L a e sigma A sm t hp
          hfine).choose_spec.2.2.2)

/-- **Global cell uniqueness of the V2 source ledger** (pinned gap). -/
theorem grayChargedFrozenSourcesV2_cells_nodup
    {q L a e n T U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    (hU : T + 1 <= U) (hae : a <= e) (hpin : e = a + 8 * L + 3) :
    ((grayChargedSourceChargeV2
      (grayChargedFrozenSourcesV2 hsm replay hU hae)).map Prod.snd).Nodup := by
  rw [grayChargedFrozenSourcesV2_charge_eq hsm replay hU hae,
    List.map_flatMap]
  refine List.nodup_flatMap.2 ⟨?_, ?_⟩
  · intro i _
    exact grayChargedRoundLocalChargeV2_transport_nodup hae _ _
  · refine List.Pairwise.imp ?_ (List.pairwise_lt_finRange _)
    intro i j hij
    simp only [Function.onFun]
    have hidx :
        ((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm (T + 1)).core.frozen[i.val]).roundIndex <
        ((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm (T + 1)).core.frozen[j.val]).roundIndex := by
      have h1 := (grayChargedRunStateV2_coreCertified (n := n)
        q L a e sigma A sm (T + 1)).frozen_index i.val i.isLt
      have h2 := (grayChargedRunStateV2_coreCertified (n := n)
        q L a e sigma A sm (T + 1)).frozen_index j.val j.isLt
      omega
    exact grayChargedRunV2_transport_disjoint hsm hpin hae
      (List.getElem_mem i.isLt) (List.getElem_mem j.isLt) hidx

/-- The mass of the V2 source ledger is the sum of the rounds' local
masses (transport is lossless). -/
lemma grayChargedFrozenSourcesV2_mass
    {q L a e n T U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    (hU : T + 1 <= U) (hae : a <= e) :
    grayChargeMass (e + grayTailNewLoss q L)
        (grayChargedSourceChargeV2
          (grayChargedFrozenSourcesV2 hsm replay hU hae)) =
      ∑ i : Fin (grayChargedRunStateV2 (n := n)
          (b := grayTailBranch q L a e)
          q L a e sigma A sm (T + 1)).core.frozen.length,
        grayChargeMass
          (((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm (T + 1)).core.frozen[i.val]).blockAnchor + L)
          (grayChargedRoundLocalChargeV2 hae _ (List.getElem_mem i.isLt)) := by
  rw [grayChargedFrozenSourcesV2_charge_eq hsm replay hU hae,
    grayChargeMass_flatMap, ← List.ofFn_eq_map, List.sum_ofFn]
  refine Finset.sum_congr rfl ?_
  intro i _
  -- transport preserves the local mass at each round
  set p := (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
    q L a e sigma A sm (T + 1)).core.frozen[i.val] with hpdef
  have hp : p ∈ (grayChargedRunStateV2 (n := n)
      (b := grayTailBranch q L a e)
      q L a e sigma A sm (T + 1)).core.frozen := List.getElem_mem i.isLt
  have hub := grayChargedRunStateV2_frozen_depth_ub hp hae
  unfold grayChargedRoundLocalChargeV2
  split
  next hfine =>
    have hsplit := grayChargedRunStateV2_frozen_phase_split
      q L a e sigma A sm (T + 1) hp hae hfine
    have hvalid := grayChargedLocalChargeOfBlockGoal_valid
      (grayChargedRunStateV2_frozen_adv_goal q L a e sigma A sm (T + 1) hp
        hae hfine)
    have hdeltaLe : grayTailRoundDelta q L e p.roundIndex <=
        e + grayTailNewLoss q L := by
      have hfineEq : p.fineEnd = p.blockAnchor + L := by
        rw [hsplit.2.1, hsplit.1, grayTailRoundDelta]
      rw [← hsplit.2.1, hfineEq]
      exact hub
    rw [grayChargedTransportRound_mass hdeltaLe hvalid]
    congr 1
    rw [hsplit.1, grayTailRoundDelta]
  next hfine =>
    have hSp := grayChargedRunStateV2_frozen_spend_goal
      q L a e sigma A sm (T + 1) hp hfine
    have hvalid := grayChargedLocalChargeOfBlockSpendGoal_valid
      hSp.choose_spec.2.2.2
    have hanchor := hSp.choose_spec.2.1
    have hfineEq2 := hSp.choose_spec.2.2.1
    have hd : grayChargedSpendDelta a L e hSp.choose =
        grayChargedSpendEps a L e hSp.choose + L := rfl
    have hfineEq3 : p.fineEnd = p.blockAnchor + L :=
      grayChargedRunStateV2_frozen_fineEnd q L a e sigma A sm (T + 1) hp
    have hdeltaLe : grayChargedSpendDelta a L e hSp.choose <=
        e + grayTailNewLoss q L := by omega
    rw [grayChargedTransportRound_mass hdeltaLe hvalid]
    have heq : p.blockAnchor + L = grayChargedSpendDelta a L e hSp.choose := by
      omega
    rw [heq]

end Kolmogorov
