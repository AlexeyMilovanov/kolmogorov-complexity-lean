import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Export
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2AdvSource
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2SpendPhase

/-!
# The V2 source records (Stage D1): per-round transport at the `a` anchor

The V2 charge-source record and its per-round builders.  Unlike the V1
ledger (fine rounds only — the R1/R2 residuals), the anchored export lets
BOTH phases transport: every accepted round's designated local cells extend
to `(a, e+newLoss]`-valid cells of the outer owner.
-/

namespace Kolmogorov

/-- The V2 spend-goal charge extractor (the all-at-anchor spend goal). -/
noncomputable def grayChargedLocalChargeOfBlockSpendGoal
    {q L a e pass m : Nat} {A : Allocation}
    {c : FamilyClientMove} {s : FamilyServerMove}
    (h : grayChargedBlockSpendGoalAtB q L a e pass m A c s = true) :
    FamilyGrayCharge :=
  (familyChargedGrayGoalAtB.exists_charge h).choose

/-- The local charge extracted from a satisfied block spend goal is a valid gray charge at the
spend scale of that pass. -/
lemma grayChargedLocalChargeOfBlockSpendGoal_valid
    {q L a e pass m : Nat} {A : Allocation}
    {c : FamilyClientMove} {s : FamilyServerMove}
    (h : grayChargedBlockSpendGoalAtB q L a e pass m A c s = true) :
    familyGrayChargeAtB 4 (halfAmplification q)
        (dyadicScale (grayChargedSpendEps a L e pass))
        ((3 / 4 : Rat) * dyadicScale (grayChargedSpendEps a L e pass))
        (grayChargedSpendEps a L e pass) (grayChargedSpendDelta a L e pass)
        m A c s
        (grayChargedLocalChargeOfBlockSpendGoal h) = true :=
  (familyChargedGrayGoalAtB.exists_charge h).choose_spec.2

/-- One V2 recursive contribution after transport to the final common depth,
valid at the `a` anchor. -/
structure GrayChargedChargeSourceV2
    (q L a e n : Nat) (A : Allocation)
    (c : FamilyClientMove) (s : FamilyServerMove) : Type where
  phase : GrayChargedSourcePhase
  round : GrayTailRoundV2 n (grayTailBranch q L a e)
  recursiveRoot : Nat
  recursiveRoot_lt : recursiveRoot < round.slots.length
  outerRoot : Fin n
  owner_eq : outerRoot =
    (round.slots.get ⟨recursiveRoot, recursiveRoot_lt⟩).1
  localCharge : FamilyGrayCharge
  transported : FamilyGrayCharge
  transported_owner : forall z, z ∈ transported -> z.1 = outerRoot.val
  transported_valid : forall z, z ∈ transported ->
    z.1 < n ∧
      z.2 ∈ newGrayCellsList a (e + grayTailNewLoss q L)
        (getFamilyAlloc s z.1 []) A
  transported_cells_nodup : (transported.map Prod.snd).Nodup
  requestContribution : Rat
  request_nonneg : 0 <= requestContribution
  recursive_lower :
    halfAmplification q * requestContribution <=
      grayChargeMass (e + grayTailNewLoss q L) transported
  recursive_root_cap :
    grayChargeMass (e + grayTailNewLoss q L) transported <=
      4 * halfAmplification q * getFamilyReq c outerRoot.val []

/-- The frozen V2 rounds' fine-end depth stays inside the final window. -/
lemma grayChargedRunStateV2_frozen_depth_ub {n : Nat}
    {q L a e t : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    {p : GrayTailRoundV2 n (grayTailBranch q L a e)}
    (hp : p ∈ (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).core.frozen)
    (hae : a <= e) :
    p.blockAnchor + L <= e + grayTailNewLoss q L := by
  have hLle : L <= grayTailNewLoss q L := by
    rw [grayTailNewLoss_eq]
    calc
      L = 1 * L := (one_mul L).symm
      _ <= 256 * (q + 1) ^ 2 * L := by
        have hpos : 0 < 256 * (q + 1) ^ 2 := by positivity
        exact Nat.mul_le_mul_right L hpos
      _ <= 256 * (q + 1) ^ 2 * L + 256 * (q + 1) := Nat.le_add_right _ _
  have hvalid := (grayChargedRunStateV2_coreCertified (n := n)
    q L a e sigma A sm t).round_valid p hp
  rcases hvalid.2.2.2.2.2 with ⟨hanchor, -⟩ | ⟨pass, -, hanchor, -⟩
  · rw [hanchor]
    have hdelta_eq : grayTailRoundEps q L e p.roundIndex + L =
        grayTailRoundDelta q L e p.roundIndex := rfl
    rw [hdelta_eq, grayTailNewLoss_eq]
    have hdelta_ub := grayTailRoundDelta_upper q L e p.roundIndex
    linarith
  · have hle : p.blockAnchor <= e + 3 := by
      rw [hanchor]
      exact grayChargedSpendEps_le_add_three L pass hae
    have hq1 : 256 <= 256 * (q + 1) := by
      have := Nat.succ_le_succ (Nat.zero_le q)
      calc
        256 = 256 * 1 := (mul_one 256).symm
        _ <= 256 * (q + 1) := Nat.mul_le_mul_left 256 this
    have hq2 : L <= 256 * (q + 1) ^ 2 * L := by
      have hpos : 0 < 256 * (q + 1) ^ 2 := by positivity
      calc
        L = 1 * L := (one_mul L).symm
        _ <= 256 * (q + 1) ^ 2 * L := Nat.mul_le_mul_right L hpos
    rw [grayTailNewLoss_eq]
    omega

/-- Every frozen V2 round's anchor is at least `a` (both phases). -/
lemma grayChargedRunStateV2_frozen_anchor_ge_a {n : Nat}
    {q L a e t : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    {p : GrayTailRoundV2 n (grayTailBranch q L a e)}
    (hp : p ∈ (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).core.frozen)
    (hae : a <= e) :
    a <= p.blockAnchor := by
  have hvalid := (grayChargedRunStateV2_coreCertified (n := n)
    q L a e sigma A sm t).round_valid p hp
  rcases hvalid.2.2.2.2.2 with ⟨hanchor, -⟩ | ⟨pass, -, hanchor, -⟩
  · rw [hanchor]
    unfold grayTailRoundEps
    have h1 := grayCallDepth_ge q e
    omega
  · rw [hanchor]
    unfold grayChargedSpendEps grayChargedSpendAlphaDepth
    exact le_trans (by omega) (le_max_left _ _)

/-- The stored-scale local charge of an advantage round, with its cells
rewritten to the round's stored anchors. -/
lemma grayChargedBlockRound_localCharge_cells {n : Nat}
    {q L a e t : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    {p : GrayTailRoundV2 n (grayTailBranch q L a e)}
    (hp : p ∈ (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).core.frozen)
    (hae : a <= e)
    (hfine : grayCallDepth q e <= p.blockAnchor)
    (z : Nat × BitString)
    (hz : z ∈ grayChargedLocalChargeOfBlockGoal
      (grayChargedRunStateV2_frozen_adv_goal q L a e sigma A sm t hp
        hae hfine)) :
    z.1 < p.slots.length ∧
      z.2 ∈ newGrayCellsList p.blockAnchor (p.blockAnchor + L)
        (getFamilyAlloc (grayTailLocalServerMove p.fineEnd p.slots
          (sm p.serverTime)) z.1 []) p.unavailable := by
  have hsplit := grayChargedRunStateV2_frozen_phase_split
    q L a e sigma A sm t hp hae hfine
  have hcells := grayChargedLocalChargeOfBlockGoal_cells
    (grayChargedRunStateV2_frozen_adv_goal q L a e sigma A sm t hp
      hae hfine) z hz
  refine ⟨hcells.1, ?_⟩
  have hfineEq : p.fineEnd = p.blockAnchor + L := by
    rw [hsplit.2.1, hsplit.1, grayTailRoundDelta]
  have := hcells.2
  rw [← hsplit.1, ← hsplit.2.1, hfineEq] at this
  rw [hfineEq]
  exact this

open Classical in
/-- The V2 advantage per-round transport: one anchored charge source per recursive root of an
accepted fine block round. -/
noncomputable def grayChargedRoundSourcesAdvV2
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
    List (GrayChargedChargeSourceV2 q L a e n A
      (grayChargedRunMoveV2 q L a e n sigma A sm U) (sm U)) :=
  List.ofFn fun j : Fin p.slots.length =>
    { phase := GrayChargedSourcePhase.advantage
      round := p
      recursiveRoot := j.val
      recursiveRoot_lt := j.isLt
      outerRoot := (p.slots.get j).1
      owner_eq := rfl
      localCharge := grayChargedLocalChargeOfBlockGoal
        (grayChargedRunStateV2_frozen_adv_goal q L a e sigma A sm (T + 1)
          hp hae hfine)
      transported := grayChargedTransportRoot (e + grayTailNewLoss q L)
        (p.slots.get j).1.val j.val
        (grayChargedLocalChargeOfBlockGoal
          (grayChargedRunStateV2_frozen_adv_goal q L a e sigma A sm (T + 1)
            hp hae hfine))
      transported_owner := fun _ hz => grayChargedTransportRoot_owner hz
      transported_valid := by
        intro z hz
        obtain ⟨source, hsource, hzc⟩ := mem_grayChargedTransportRoot.mp hz
        obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hzc
        have hcellmem := (mem_grayChargeAtRoot.mp hsource).1
        have hroot := (mem_grayChargeAtRoot.mp hsource).2
        have hcell := grayChargedBlockRound_localCharge_cells hp hae hfine
          source hcellmem
        have hcellLen : source.2.length = p.blockAnchor + L :=
          (mem_newGrayCellsList.mp hcell.2).1
        have hwLen : w.length =
            (e + grayTailNewLoss q L) - source.2.length :=
          (mem_allStrings _ _).mp hw
        refine ⟨(p.slots.get j).1.isLt, ?_⟩
        have hub := grayChargedRunStateV2_frozen_depth_ub hp hae
        have hcell' : source.2 ∈ newGrayCellsList p.blockAnchor
            (p.blockAnchor + L)
            (getFamilyAlloc (grayTailLocalServerMove (p.blockAnchor + L)
              p.slots (sm p.serverTime)) j.val []) p.unavailable := by
          have hfineEq : p.fineEnd = p.blockAnchor + L := by
            have hsplit := grayChargedRunStateV2_frozen_phase_split
              q L a e sigma A sm (T + 1) hp hae hfine
            rw [hsplit.2.1, hsplit.1, grayTailRoundDelta]
          rw [hfineEq, hroot] at hcell
          exact hcell.2
        exact grayChargedRunV2_cell_transport_valid hsm hp
          (grayChargedRunStateV2_frozen_anchor_ge_a hp hae)
          (le_trans (replay.frozen_serverTime_le p hp) (by omega))
          j hcell' (by rw [hcellLen, hwLen, hcellLen]; omega)
      transported_cells_nodup := by
        have hvalid := grayChargedLocalChargeOfBlockGoal_valid
          (grayChargedRunStateV2_frozen_adv_goal q L a e sigma A sm (T + 1)
            hp hae hfine)
        refine grayChargedTransportRoot_nodup (d := p.blockAnchor + L)
          (List.Nodup.sublist (List.filter_sublist.map Prod.snd)
            (familyGrayChargeAtB.cells_nodup hvalid)) ?_
        intro z hz
        exact (mem_newGrayCellsList.mp
          (grayChargedBlockRound_localCharge_cells hp hae hfine z
            (mem_grayChargeAtRoot.mp hz).1).2).1
      requestContribution :=
        grayChargeMass (e + grayTailNewLoss q L)
          (grayChargedTransportRoot (e + grayTailNewLoss q L)
            (p.slots.get j).1.val j.val
            (grayChargedLocalChargeOfBlockGoal
              (grayChargedRunStateV2_frozen_adv_goal q L a e sigma A sm
                (T + 1) hp hae hfine)))
          / halfAmplification q
      request_nonneg :=
        div_nonneg (grayChargedChargeMass_nonneg _ _)
          (halfAmplification_pos q).le
      recursive_lower := by
        rw [mul_div_cancel₀ _ (ne_of_gt (halfAmplification_pos q))]
      recursive_root_cap := by
        have hgoal := grayChargedRunStateV2_frozen_adv_goal
          q L a e sigma A sm (T + 1) hp hae hfine
        have hvalid := grayChargedLocalChargeOfBlockGoal_valid hgoal
        have hsplit := grayChargedRunStateV2_frozen_phase_split
          q L a e sigma A sm (T + 1) hp hae hfine
        have hub := grayChargedRunStateV2_frozen_depth_ub hp hae
        have hdeltaLe : grayTailRoundDelta q L e p.roundIndex <=
            e + grayTailNewLoss q L := by
          rw [← hsplit.2.1]
          have hfineEq : p.fineEnd = p.blockAnchor + L := by
            rw [hsplit.2.1, hsplit.1, grayTailRoundDelta]
          rw [hfineEq]
          exact hub
        rw [grayChargedTransportRoot_mass_of_charge hdeltaLe hvalid]
        refine le_trans (familyGrayChargeAtB.root hvalid j.isLt).2.2 ?_
        refine mul_le_mul_of_nonneg_left ?_
          (mul_nonneg (by norm_num) (halfAmplification_pos q).le)
        exact grayChargedV2_frozen_slot_req_le_final_root replay hU hae hp j }

/-- Cell membership of the V2 spend-goal charge. -/
lemma grayChargedLocalChargeOfBlockSpendGoal_cells
    {q L a e pass m : Nat} {A : Allocation}
    {c : FamilyClientMove} {s : FamilyServerMove}
    (h : grayChargedBlockSpendGoalAtB q L a e pass m A c s = true)
    (z : Nat × BitString)
    (hz : z ∈ grayChargedLocalChargeOfBlockSpendGoal h) :
    z.1 < m ∧
      z.2 ∈ newGrayCellsList (grayChargedSpendEps a L e pass)
        (grayChargedSpendDelta a L e pass) (getFamilyAlloc s z.1 []) A := by
  have hvalid := grayChargedLocalChargeOfBlockSpendGoal_valid h
  unfold familyGrayChargeAtB at hvalid
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    Bool.and_eq_true] at hvalid
  have hB := hvalid.1.1.1.1.2
  rw [List.all_eq_true] at hB
  have hz2 := hB z hz
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hz2
  exact hz2

open Classical in
/-- The V2 spend per-round transport: one anchored charge source per recursive root of an accepted
spend block round. -/
noncomputable def grayChargedRoundSourcesSpendV2
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
    List (GrayChargedChargeSourceV2 q L a e n A
      (grayChargedRunMoveV2 q L a e n sigma A sm U) (sm U)) :=
  let hSp := grayChargedRunStateV2_frozen_spend_goal
    q L a e sigma A sm (T + 1) hp hcoarse
  List.ofFn fun j : Fin p.slots.length =>
    { phase := GrayChargedSourcePhase.spend hSp.choose
      round := p
      recursiveRoot := j.val
      recursiveRoot_lt := j.isLt
      outerRoot := (p.slots.get j).1
      owner_eq := rfl
      localCharge := grayChargedLocalChargeOfBlockSpendGoal
        hSp.choose_spec.2.2.2
      transported := grayChargedTransportRoot (e + grayTailNewLoss q L)
        (p.slots.get j).1.val j.val
        (grayChargedLocalChargeOfBlockSpendGoal hSp.choose_spec.2.2.2)
      transported_owner := fun _ hz => grayChargedTransportRoot_owner hz
      transported_valid := by
        intro z hz
        obtain ⟨source, hsource, hzc⟩ := mem_grayChargedTransportRoot.mp hz
        obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hzc
        have hcellmem := (mem_grayChargeAtRoot.mp hsource).1
        have hroot := (mem_grayChargeAtRoot.mp hsource).2
        have hcell := grayChargedLocalChargeOfBlockSpendGoal_cells
          hSp.choose_spec.2.2.2 source hcellmem
        have hanchor := hSp.choose_spec.2.1
        have hfineEq2 := hSp.choose_spec.2.2.1
        have hd : grayChargedSpendDelta a L e hSp.choose =
            grayChargedSpendEps a L e hSp.choose + L := rfl
        have hfineEq3 : p.fineEnd = p.blockAnchor + L := by omega
        have hcellLen : source.2.length = p.blockAnchor + L := by
          have hlen0 := (mem_newGrayCellsList.mp hcell.2).1
          omega
        have hwLen : w.length =
            (e + grayTailNewLoss q L) - source.2.length :=
          (mem_allStrings _ _).mp hw
        refine ⟨(p.slots.get j).1.isLt, ?_⟩
        have hub := grayChargedRunStateV2_frozen_depth_ub hp hae
        have hcell' : source.2 ∈ newGrayCellsList p.blockAnchor
            (p.blockAnchor + L)
            (getFamilyAlloc (grayTailLocalServerMove (p.blockAnchor + L)
              p.slots (sm p.serverTime)) j.val []) p.unavailable := by
          have hcell2 := hcell.2
          rw [hroot] at hcell2
          rw [← hanchor, ← hfineEq2, hfineEq3] at hcell2
          exact hcell2
        exact grayChargedRunV2_cell_transport_valid hsm hp
          (grayChargedRunStateV2_frozen_anchor_ge_a hp hae)
          (le_trans (replay.frozen_serverTime_le p hp) (by omega))
          j hcell' (by rw [hcellLen, hwLen, hcellLen]; omega)
      transported_cells_nodup := by
        have hvalid := grayChargedLocalChargeOfBlockSpendGoal_valid
          hSp.choose_spec.2.2.2
        refine grayChargedTransportRoot_nodup (d := p.blockAnchor + L)
          (List.Nodup.sublist (List.filter_sublist.map Prod.snd)
            (familyGrayChargeAtB.cells_nodup hvalid)) ?_
        intro z hz
        have hcz := grayChargedLocalChargeOfBlockSpendGoal_cells
          hSp.choose_spec.2.2.2 z (mem_grayChargeAtRoot.mp hz).1
        have hlen0 := (mem_newGrayCellsList.mp hcz.2).1
        have hanchor := hSp.choose_spec.2.1
        have hfineEq2 := hSp.choose_spec.2.2.1
        have hd : grayChargedSpendDelta a L e hSp.choose =
            grayChargedSpendEps a L e hSp.choose + L := rfl
        omega
      requestContribution :=
        grayChargeMass (e + grayTailNewLoss q L)
          (grayChargedTransportRoot (e + grayTailNewLoss q L)
            (p.slots.get j).1.val j.val
            (grayChargedLocalChargeOfBlockSpendGoal
              hSp.choose_spec.2.2.2))
          / halfAmplification q
      request_nonneg :=
        div_nonneg (grayChargedChargeMass_nonneg _ _)
          (halfAmplification_pos q).le
      recursive_lower := by
        rw [mul_div_cancel₀ _ (ne_of_gt (halfAmplification_pos q))]
      recursive_root_cap := by
        have hvalid := grayChargedLocalChargeOfBlockSpendGoal_valid
          hSp.choose_spec.2.2.2
        have hub := grayChargedRunStateV2_frozen_depth_ub hp hae
        have hanchor := hSp.choose_spec.2.1
        have hfineEq2 := hSp.choose_spec.2.2.1
        have hd : grayChargedSpendDelta a L e hSp.choose =
            grayChargedSpendEps a L e hSp.choose + L := rfl
        have hdeltaLe : grayChargedSpendDelta a L e hSp.choose <=
            e + grayTailNewLoss q L := by omega
        rw [grayChargedTransportRoot_mass_of_charge hdeltaLe hvalid]
        refine le_trans (familyGrayChargeAtB.root hvalid j.isLt).2.2 ?_
        refine mul_le_mul_of_nonneg_left ?_
          (mul_nonneg (by norm_num) (halfAmplification_pos q).le)
        exact grayChargedV2_frozen_slot_req_le_final_root replay hU hae hp j }

/-- The uniform local charge of one frozen run round (phase-split). -/
noncomputable def grayChargedRoundLocalChargeV2
    {q L a e n t : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hae : a <= e)
    (p : GrayTailRoundV2 n (grayTailBranch q L a e))
    (hp : p ∈ (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).core.frozen) : FamilyGrayCharge :=
  open Classical in
  if hfine : grayCallDepth q e <= p.blockAnchor then
    grayChargedLocalChargeOfBlockGoal
      (grayChargedRunStateV2_frozen_adv_goal q L a e sigma A sm t hp
        hae hfine)
  else
    grayChargedLocalChargeOfBlockSpendGoal
      (grayChargedRunStateV2_frozen_spend_goal q L a e sigma A sm t hp
        hfine).choose_spec.2.2.2

/-- The uniform stored-scale cell membership of the round charge. -/
lemma grayChargedRoundLocalChargeV2_cells
    {q L a e n t : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hae : a <= e)
    (p : GrayTailRoundV2 n (grayTailBranch q L a e))
    (hp : p ∈ (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).core.frozen)
    (z : Nat × BitString)
    (hz : z ∈ grayChargedRoundLocalChargeV2 hae p hp) :
    z.1 < p.slots.length ∧
      z.2 ∈ newGrayCellsList p.blockAnchor (p.blockAnchor + L)
        (getFamilyAlloc (grayTailLocalServerMove (p.blockAnchor + L) p.slots
          (sm p.serverTime)) z.1 []) p.unavailable := by
  unfold grayChargedRoundLocalChargeV2 at hz
  split at hz
  next hfine =>
    have h := grayChargedBlockRound_localCharge_cells hp hae hfine z hz
    refine ⟨h.1, ?_⟩
    have hfineEq : p.fineEnd = p.blockAnchor + L :=
      grayChargedRunStateV2_frozen_fineEnd q L a e sigma A sm t hp
    have h2 := h.2
    rw [hfineEq] at h2
    exact h2
  next hfine =>
    have hSp := grayChargedRunStateV2_frozen_spend_goal
      q L a e sigma A sm t hp hfine
    have h := grayChargedLocalChargeOfBlockSpendGoal_cells
      hSp.choose_spec.2.2.2 z hz
    refine ⟨h.1, ?_⟩
    have hanchor := hSp.choose_spec.2.1
    have hfineEq2 := hSp.choose_spec.2.2.1
    have hfineEq3 : p.fineEnd = p.blockAnchor + L :=
      grayChargedRunStateV2_frozen_fineEnd q L a e sigma A sm t hp
    have h2 := h.2
    rw [← hanchor, ← hfineEq2, hfineEq3] at h2
    exact h2

/-- The round charge's cells all have the round's fine length. -/
lemma grayChargedRoundLocalChargeV2_cell_length
    {q L a e n t : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hae : a <= e)
    (p : GrayTailRoundV2 n (grayTailBranch q L a e))
    (hp : p ∈ (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).core.frozen)
    (z : Nat × BitString)
    (hz : z ∈ grayChargedRoundLocalChargeV2 hae p hp) :
    z.2.length = p.blockAnchor + L :=
  (mem_newGrayCellsList.mp
    (grayChargedRoundLocalChargeV2_cells hae p hp z hz).2).1

end Kolmogorov
