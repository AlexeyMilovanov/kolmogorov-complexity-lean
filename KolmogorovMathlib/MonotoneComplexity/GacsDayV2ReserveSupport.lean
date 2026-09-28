import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Reserves

/-!
# Reserve support for the V2 ledger (Stage D2b)

The run-level facts feeding the late-reserve family: frozen-prefix and
source-son-base monotonicity along the V2 run, the terminal frozen equality,
the done-phase son display, the raised-source display, the non-positive
branch's reserve existence, and the common-late-horizon reserve selection.
-/

namespace Kolmogorov

/-- The V2 charged play wins outright by an unserved positive request:
`familyClientWinsUnservedPositive` at height `2 * (q + 1)` on the branch `grayTailBranch q L a
e` for the play of `grayChargedStrategyV2` against `sm`. -/
def GrayChargedPositiveV2
    (q L a e n : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) : Prop :=
  familyClientWinsUnservedPositive n (2 * (q + 1))
    (grayTailBranch q L a e)
    (playClientFamily A n (grayChargedStrategyV2 q L a e sigma) sm) sm

/-- If the charged V2 run never leaves a request unserved, then every positive request at an
admissible node of client `i` is eventually served by some server move. -/
lemma grayChargedV2_exists_serves_of_not_positive
    {q L a e n : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hnotpos : ¬ GrayChargedPositiveV2 q L a e n sigma A sm)
    {i : Nat} (hi : i < n) (t : Nat) (x : GacsDayNode)
    (hlen : x.length <= 2 * (q + 1))
    (hx : forall d, d ∈ x -> d < grayTailBranch q L a e)
    (hpos : 0 < getFamilyReq (grayChargedRunMoveV2 q L a e n sigma A sm t)
      i x) :
    exists u, Serves (getFamilyAlloc (sm u) i x)
      (getFamilyReq (grayChargedRunMoveV2 q L a e n sigma A sm t) i x) := by
  by_contra hcon
  push_neg at hcon
  exact hnotpos ⟨i, hi, t, x, hlen, hx, fun u => hcon u, hpos⟩

/-- If the charged V2 run never leaves a request unserved, then a request of size at least
`dyadicScale e` at an admissible node yields a tail reserve string for that node. -/
lemma grayChargedV2_exists_reserve_of_not_positive
    {q L a e n : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hnotpos : ¬ GrayChargedPositiveV2 q L a e n sigma A sm)
    {i : Nat} (hi : i < n) (t : Nat) (x : GacsDayNode)
    (hlen : x.length <= 2 * (q + 1))
    (hx : forall d, d ∈ x -> d < grayTailBranch q L a e)
    (hreq : dyadicScale e <=
      getFamilyReq (grayChargedRunMoveV2 q L a e n sigma A sm t) i x) :
    exists u R, IsTailFamilyReserve e (grayTailBranch q L a e) A n i
      (sm u) x R := by
  have hpos : 0 < getFamilyReq
      (grayChargedRunMoveV2 q L a e n sigma A sm t) i x :=
    lt_of_lt_of_le (dyadicScale_pos e) hreq
  obtain ⟨u, hu⟩ :=
    grayChargedV2_exists_serves_of_not_positive hnotpos hi t x hlen hx hpos
  obtain ⟨c, hc, hcle⟩ := hu
  have hserve : Serves (getFamilyAlloc (sm u) i x) (dyadicScale e) := by
    refine ⟨c, hc, le_trans ?_ hcle⟩
    exact_mod_cast hreq
  exact ⟨u, exists_tailFamilyReserve_of_serves hsm hi hx hserve⟩

/-- The frozen ledger of the V2 run only grows (as a prefix). -/
lemma grayChargedRunStateV2_frozen_prefix_le {n : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) {t u : Nat} (htu : t <= u) :
    (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).core.frozen <+:
    (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm u).core.frozen := by
  induction u, htu using Nat.le_induction with
  | base => exact List.prefix_rfl
  | succ m hm ih =>
      exact ih.trans
        (grayChargedRunStateV2_frozen_prefix_succ q L a e sigma A sm m)

/-- Source son bases only grow along the V2 run (projected entries). -/
lemma grayChargedRunStateV2_frozenSonBase_mono {n : Nat}
    {q L a e : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat -> FamilyServerMove} {t u : Nat} (htu : t <= u)
    (i : Fin n) (c : Fin (grayTailBranch q L a e)) :
    grayTailFrozenSonBase
        ((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).core.frozen.map GrayTailRoundV2.toV1) i c <=
      grayTailFrozenSonBase
        ((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm u).core.frozen.map GrayTailRoundV2.toV1) i c := by
  obtain ⟨rest, hrest⟩ :=
    grayChargedRunStateV2_frozen_prefix_le q L a e sigma A sm htu
  have hmap : (grayChargedRunStateV2 (n := n)
      (b := grayTailBranch q L a e)
      q L a e sigma A sm u).core.frozen.map GrayTailRoundV2.toV1 =
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t).core.frozen.map GrayTailRoundV2.toV1 ++
      rest.map GrayTailRoundV2.toV1 := by
    rw [← List.map_append, hrest]
  have hsplit := grayTailFrozenSonBase_append_list
    ((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).core.frozen.map GrayTailRoundV2.toV1)
    (rest.map GrayTailRoundV2.toV1) i c
  have hnonneg : 0 <= grayTailFrozenSonBase
      (rest.map GrayTailRoundV2.toV1) i c := by
    apply grayTailSonBase_nonneg_global
    intro z hz
    refine grayChargedRunStateV2_frozenEntries_req_nonneg (t := u) (q := q)
      (L := L) (a := a) (e := e) (sigma := sigma) (A := A) (sm := sm) z ?_
    rw [hmap, grayTailFrozenEntries, List.flatMap_append]
    exact List.mem_append_right _ hz
  rw [hmap, hsplit]
  linarith

/-- The V2 exit snapshot carries the frozen list of the successor state. -/
lemma grayChargedReplayV2_advantageTerminal_frozen_eq
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T) :
    (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm (replay.advantageExitTime + 1)).core.frozen =
      replay.advantageTerminal.frozen := by
  rw [replay.advantageTerminal_eq, grayChargedRunStateV2_succ]
  by_cases hdone : (grayChargedBlockTailStepV2 q L a e sigma A
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm replay.advantageExitTime).core
      (sm replay.advantageExitTime)).done = true
  · by_cases hserved : grayChargedWaitServedB q a e
        (grayChargedBlockTailStepV2 q L a e sigma A
          (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm replay.advantageExitTime).core
          (sm replay.advantageExitTime)) (sm replay.advantageExitTime) = true
    · rw [grayChargedStepV2_advantage_exit q L a e sigma A _
        (sm replay.advantageExitTime) replay.advantage_before hdone hserved]
      exact grayChargedStartSpendV2_frozen q L a e A _ _
    · have hserved' : grayChargedWaitServedB q a e
          (grayChargedBlockTailStepV2 q L a e sigma A
            (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
              q L a e sigma A sm replay.advantageExitTime).core
            (sm replay.advantageExitTime)) (sm replay.advantageExitTime) =
            false := by
        simpa using hserved
      rw [grayChargedStepV2_advantage_wait q L a e sigma A _
        (sm replay.advantageExitTime) replay.advantage_before hdone hserved']
  · have hnext : (grayChargedBlockTailStepV2 q L a e sigma A
        (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm replay.advantageExitTime).core
        (sm replay.advantageExitTime)).done = false := by
      simpa using hdone
    rw [grayChargedStepV2_advantage_continue q L a e sigma A _
      (sm replay.advantageExitTime) replay.advantage_before hnext]

/-- After the V2 controller is done, the displayed son request equals the
charged son request over the projected frozen entries. -/
lemma grayChargedRunMoveV2_son_eq_of_done
    {q L a e n U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hdone : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm U).phase = .done)
    (i : Fin n) (c : Fin (grayTailBranch q L a e)) :
    getFamilyReq (grayChargedRunMoveV2 q L a e n sigma A sm U) i.val
        [c.val] =
      grayChargedSonRequest (grayChargedSourceCount a e)
        (grayChargedThreshold q e) (dyadicScale e)
        (grayTailFrozenEntries
          ((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm U).core.frozen.map GrayTailRoundV2.toV1))
        i c := by
  have hslots := grayChargedRunStateV2_slots_eq_nil_of_done
    q L a e sigma A sm U hdone
  rw [show grayChargedRunMoveV2 q L a e n sigma A sm U =
      playClientFamily A n (grayChargedStrategyV2 q L a e sigma) sm U from
      rfl,
    playClientFamily_grayChargedStrategyV2]
  simp only [grayChargedDisplayedMoveV2, hdone, hslots, ite_self]
  rw [show getFamilyReq
      (grayChargedTailFamilyMove (grayChargedSourceCount a e)
        (grayChargedThreshold q e) (dyadicScale e)
        ((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm U).core.frozen.map GrayTailRoundV2.toV1) [] [])
      i.val [c.val] = _ from
    getFamilyReq_grayChargedTailFamilyMove_son _ _ _ _ _ _ i c]
  simp [grayTailEntries, grayTailSlotEntries]

/-- A threshold-raised source displays one coarse unit at every late time. -/
theorem grayChargedReplayV2_raised_display_eq
    {q L a e n T U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    (hU : T + 1 <= U)
    {z : Fin n × Fin (grayTailBranch q L a e)}
    (hz : z ∈ grayChargedReplayV2RaisedSources replay) :
    getFamilyReq (grayChargedRunMoveV2 q L a e n sigma A sm U) z.1.val
        [z.2.val] =
      dyadicScale e := by
  classical
  have hmem := Finset.mem_filter.mp hz
  have hsrc : z.2.val < grayChargedSourceCount a e := hmem.2.1
  have hraise : grayChargedThreshold q e <
      grayTailFrozenSonBase (frozenV1OfV2 replay.advantageTerminal)
        z.1 z.2 := hmem.2.2
  have hdone := (replay.done_stable U hU).1
  have hstep : replay.advantageExitTime + 1 <= U :=
    le_trans (Nat.succ_le_succ replay.advantageExit_le) hU
  have hmono := grayChargedRunStateV2_frozenSonBase_mono
    (q := q) (L := L) (a := a) (e := e) (sigma := sigma) (A := A) (sm := sm)
    hstep z.1 z.2
  rw [grayChargedReplayV2_advantageTerminal_frozen_eq replay] at hmono
  have hfinal : grayChargedThreshold q e <
      grayTailSonBase (grayTailFrozenEntries
        ((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm U).core.frozen.map GrayTailRoundV2.toV1))
        z.1 z.2 := by
    refine lt_of_lt_of_le ?_ hmono
    simpa [frozenV1OfV2] using hraise
  rw [grayChargedRunMoveV2_son_eq_of_done hdone z.1 z.2]
  simp only [grayChargedSonRequest, hsrc, if_pos, grayTailSonRequest]
  rw [if_pos hfinal]

/-- **The V2 late reserve selection** (Stage D2b): on the non-positive
branch, every resolved source carries a genuine tail family reserve at a
common late horizon that preserves the terminal display. -/
theorem grayChargedReplayV2_resolved_late_reserves
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hnotpos : ¬ GrayChargedPositiveV2 q L a e n sigma A sm)
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T) :
    exists (U : Nat) (tau : Fin n × Fin (grayTailBranch q L a e) -> Nat)
      (res : Fin n × Fin (grayTailBranch q L a e) -> BitString),
      T + 1 <= U ∧
      grayChargedRunMoveV2 q L a e n sigma A sm U =
        grayChargedRunMoveV2 q L a e n sigma A sm T ∧
      ∀ z ∈ grayChargedReplayV2RaisedSources replay ∪
          grayChargedReplayV2ServerResolvedSources replay,
        tau z <= U ∧ z.2.val < grayChargedSourceCount a e ∧
        IsTailFamilyReserve e (grayTailBranch q L a e) A n z.1.val
          (sm (tau z)) [z.2.val] (res z) := by
  classical
  have hex : ∀ z : Fin n × Fin (grayTailBranch q L a e),
      z ∈ grayChargedReplayV2RaisedSources replay ∪
        grayChargedReplayV2ServerResolvedSources replay ->
      exists p : Nat × BitString,
        IsTailFamilyReserve e (grayTailBranch q L a e) A n z.1.val
          (sm p.1) [z.2.val] p.2 := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · have hreq : dyadicScale e <=
          getFamilyReq (grayChargedRunMoveV2 q L a e n sigma A sm (T + 1))
            z.1.val [z.2.val] :=
        le_of_eq (grayChargedReplayV2_raised_display_eq replay le_rfl hz).symm
      obtain ⟨u, R, hR⟩ := grayChargedV2_exists_reserve_of_not_positive
        hsm hnotpos z.1.isLt (T + 1) [z.2.val] (by simp; omega)
        (by
          intro d hd
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
          subst hd
          exact z.2.isLt) hreq
      exact ⟨(u, R), hR⟩
    · have hsome := (Finset.mem_filter.mp hz).2.2.2
      obtain ⟨R, hR⟩ :=
        (getTailFamilyReserve_isSome_iff _ _ _ _ _ _ _).mp hsome
      exact ⟨(replay.advantageDoneTime, R), hR⟩
  choose! f hf using hex
  refine ⟨max (T + 1) ((grayChargedReplayV2RaisedSources replay ∪
      grayChargedReplayV2ServerResolvedSources replay).sup
      (fun z => (f z).1)), fun z => (f z).1, fun z => (f z).2,
    le_max_left _ _, replay.move_stable _ (le_max_left _ _), ?_⟩
  intro z hz
  refine ⟨le_trans (Finset.le_sup (f := fun z => (f z).1) hz)
    (le_max_right _ _), ?_, hf z hz⟩
  rcases Finset.mem_union.mp hz with hz | hz
  · exact grayChargedRaisedSources_source_lt hz
  · exact grayChargedServerResolvedSources_source_lt hz

/-- One V2 reserve-complement contribution, valid at the `a` anchor. -/
structure GrayChargedReserveSourceV2
    (q L a e n U : Nat) (A : Allocation)
    (sm : Nat -> FamilyServerMove) : Type where
  kind : GrayChargedReserveKind
  coordinate : Fin n × Fin (grayTailBranch q L a e)
  source_lt : coordinate.2.val < grayChargedSourceCount a e
  serviceTime : Nat
  service_le : serviceTime <= U
  reserve : BitString
  reserve_witness : IsTailFamilyReserve e (grayTailBranch q L a e) A n
    coordinate.1.val (sm serviceTime) [coordinate.2.val] reserve
  cells : FamilyGrayCharge
  cells_owner : forall z, z ∈ cells -> z.1 = coordinate.1.val
  cells_valid : forall z, z ∈ cells ->
    z.1 < n ∧
      z.2 ∈ newGrayCellsList a (e + grayTailNewLoss q L)
        (getFamilyAlloc (sm U) z.1 []) A
  cells_nodup : (cells.map Prod.snd).Nodup
  massContribution : Rat
  mass_lower : massContribution <=
    grayChargeMass (e + grayTailNewLoss q L) cells
  root_upper :
    grayChargeMass (e + grayTailNewLoss q L) cells <= dyadicScale a

/-- Coarsen a bin-anchored new-gray membership to the `a` anchor. -/
lemma grayChargedV2_newGrayCell_coarsen {a e delta : Nat}
    {S U : List BitString} {cell : BitString}
    (hae : a <= e)
    (h : cell ∈ newGrayCellsList e delta S U) :
    cell ∈ newGrayCellsList a delta S U := by
  obtain ⟨hlen, ⟨c, hc, hcomp⟩, hfresh⟩ := mem_newGrayCellsList.mp h
  rw [mem_newGrayCellsList]
  refine ⟨hlen, ⟨c, hc, ?_⟩, hfresh⟩
  have htake : cell.take a <+: cell.take e := by
    have h1 : (cell.take e).take a = cell.take a := by
      rw [List.take_take, min_eq_left hae]
    rw [← h1]
    exact List.take_prefix _ _
  exact prefixComparable_of_prefix_of_prefixComparable htake hcomp

/-- The V2 late reserve source at one resolved coordinate. -/
noncomputable def grayChargedLateReserveSourceOfV2
    {q L a e n U : Nat} {A : Allocation} {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hae : a <= e)
    (kind : GrayChargedReserveKind)
    (z : Fin n × Fin (grayTailBranch q L a e))
    (hsrc : z.2.val < grayChargedSourceCount a e)
    (tau : Nat) (htau : tau <= U) (R : BitString)
    (hres : IsTailFamilyReserve e (grayTailBranch q L a e) A n z.1.val
      (sm tau) [z.2.val] R) :
    GrayChargedReserveSourceV2 q L a e n U A sm where
  kind := kind
  coordinate := z
  source_lt := hsrc
  serviceTime := tau
  service_le := htau
  reserve := R
  reserve_witness := hres
  cells := grayChargedReserveCylinder z.1.val (e + grayTailNewLoss q L) R
  cells_owner := fun _ hz => grayChargedReserveCylinder_owner hz
  cells_valid := by
    intro w hw
    have hbase := (grayChargedLateReserveSourceOf hsm hae kind z hsrc
      tau htau R hres).cells_valid w hw
    exact ⟨hbase.1, grayChargedV2_newGrayCell_coarsen hae hbase.2⟩
  cells_nodup := grayChargedReserveCylinder_nodup _ _ _
  massContribution := dyadicScale e
  mass_lower := by
    rw [grayChargedReserveCylinder_mass
      (by rw [hres.1.1]; exact Nat.le_add_right _ _), hres.1.1]
  root_upper := by
    rw [grayChargedReserveCylinder_mass
      (by rw [hres.1.1]; exact Nat.le_add_right _ _), hres.1.1]
    exact dyadicScale_antitone hae

/-- The late reserve source built for a coordinate `z` records `z` as its coordinate. -/
@[simp] lemma grayChargedLateReserveSourceOfV2_coordinate
    {q L a e n U : Nat} {A : Allocation} {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hae : a <= e) (kind : GrayChargedReserveKind)
    (z : Fin n × Fin (grayTailBranch q L a e))
    (hsrc : z.2.val < grayChargedSourceCount a e)
    (tau : Nat) (htau : tau <= U) (R : BitString)
    (hres : IsTailFamilyReserve e (grayTailBranch q L a e) A n z.1.val
      (sm tau) [z.2.val] R) :
    (grayChargedLateReserveSourceOfV2 hsm hae kind z hsrc tau htau R
      hres).coordinate = z := rfl

/-- The cells of the late reserve source are the reserve cylinder above `R` at depth
`e + grayTailNewLoss q L`. -/
@[simp] lemma grayChargedLateReserveSourceOfV2_cells
    {q L a e n U : Nat} {A : Allocation} {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hae : a <= e) (kind : GrayChargedReserveKind)
    (z : Fin n × Fin (grayTailBranch q L a e))
    (hsrc : z.2.val < grayChargedSourceCount a e)
    (tau : Nat) (htau : tau <= U) (R : BitString)
    (hres : IsTailFamilyReserve e (grayTailBranch q L a e) A n z.1.val
      (sm tau) [z.2.val] R) :
    (grayChargedLateReserveSourceOfV2 hsm hae kind z hsrc tau htau R
      hres).cells
      = grayChargedReserveCylinder z.1.val (e + grayTailNewLoss q L) R := rfl

/-- Flatten the V2 reserve contributions. -/
def grayChargedReserveChargeV2
    {q L a e n U : Nat} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (reserves : List (GrayChargedReserveSourceV2 q L a e n U A sm)) :
    FamilyGrayCharge :=
  reserves.flatMap GrayChargedReserveSourceV2.cells

/-- **The V2 late reserve family** (Stage D2c): a unit-mass reserve source
per resolved coordinate, with globally distinct cells, at one common late
horizon preserving the terminal display. -/
theorem grayChargedV2_late_reserve_family
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hae : a <= e)
    (hnotpos : ¬ GrayChargedPositiveV2 q L a e n sigma A sm)
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T) :
    exists (U : Nat)
      (reserves : List (GrayChargedReserveSourceV2 q L a e n U A sm)),
      T + 1 <= U ∧
      grayChargedRunMoveV2 q L a e n sigma A sm U =
        grayChargedRunMoveV2 q L a e n sigma A sm T ∧
      (forall z, z ∈ grayChargedReplayV2RaisedSources replay ∪
          grayChargedReplayV2ServerResolvedSources replay ->
        exists r, r ∈ reserves ∧ r.coordinate = z) ∧
      (forall r, r ∈ reserves -> r.coordinate ∈
        grayChargedReplayV2RaisedSources replay ∪
          grayChargedReplayV2ServerResolvedSources replay) ∧
      ((grayChargedReserveChargeV2 reserves).map Prod.snd).Nodup ∧
      grayChargeMass (e + grayTailNewLoss q L)
          (grayChargedReserveChargeV2 reserves) =
        ((grayChargedReplayV2RaisedSources replay ∪
          grayChargedReplayV2ServerResolvedSources replay).card : Rat) *
          dyadicScale e ∧
      (reserves.map fun r => r.coordinate).Nodup ∧
      (forall r, r ∈ reserves ->
        grayChargeMass (e + grayTailNewLoss q L) r.cells = dyadicScale e) ∧
      (forall r, r ∈ reserves -> r.cells =
        grayChargedReserveCylinder r.coordinate.1.val
          (e + grayTailNewLoss q L) r.reserve) := by
  classical
  obtain ⟨U, tau, res, hU, hmove, hall⟩ :=
    grayChargedReplayV2_resolved_late_reserves hsm hnotpos replay
  set S := grayChargedReplayV2RaisedSources replay ∪
    grayChargedReplayV2ServerResolvedSources replay with hSdef
  refine ⟨U, S.toList.attach.map fun zz =>
    grayChargedLateReserveSourceOfV2 hsm hae
      (if zz.1 ∈ grayChargedReplayV2RaisedSources replay then
        GrayChargedReserveKind.thresholdRaised
      else GrayChargedReserveKind.serverResolved)
      zz.1 (hall zz.1 (Finset.mem_toList.mp zz.2)).2.1
      (tau zz.1) (hall zz.1 (Finset.mem_toList.mp zz.2)).1
      (res zz.1) (hall zz.1 (Finset.mem_toList.mp zz.2)).2.2,
    hU, hmove, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact ⟨_, List.mem_map.mpr
      ⟨⟨z, Finset.mem_toList.mpr hz⟩, List.mem_attach _ _, rfl⟩, rfl⟩
  · intro r hr
    obtain ⟨zz, -, rfl⟩ := List.mem_map.mp hr
    simpa using Finset.mem_toList.mp zz.2
  · rw [grayChargedReserveChargeV2, List.map_flatMap, List.flatMap_map]
    refine List.nodup_flatMap.2 ⟨?_, ?_⟩
    · intro zz _
      exact grayChargedReserveCylinder_nodup _ _ _
    · refine List.Pairwise.imp ?_
        (List.nodup_attach.mpr (Finset.nodup_toList S))
      intro zz zz' hne
      have hcoord : zz.1 ≠ zz'.1 := fun h => hne (Subtype.ext h)
      have hpair : ¬ (zz.1.1.val = zz'.1.1.val ∧
          zz.1.2.val = zz'.1.2.val) := by
        rintro ⟨h1, h2⟩
        exact hcoord (Prod.ext (Fin.ext h1) (Fin.ext h2))
      have hR := (hall zz.1 (Finset.mem_toList.mp zz.2)).2.2
      have hR' := (hall zz'.1 (Finset.mem_toList.mp zz'.2)).2.2
      have hne' : res zz.1 ≠ res zz'.1 :=
        isTailFamilyReserve_ne_of_ne_coordinate hsm zz.1.1.isLt zz'.1.1.isLt
          zz.1.2.isLt zz'.1.2.isLt hR hR' hpair
      exact grayChargedReserveCylinder_disjoint hR.1.1 hR'.1.1 hne'
  · rw [grayChargedReserveChargeV2, grayChargeMass_flatMap]
    refine (List.sum_eq_card_nsmul _ (dyadicScale e) ?_).trans ?_
    · intro x hx
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
      obtain ⟨zz, -, rfl⟩ := List.mem_map.mp hr
      have hR := (hall zz.1 (Finset.mem_toList.mp zz.2)).2.2
      simp only [grayChargedLateReserveSourceOfV2_cells]
      rw [grayChargedReserveCylinder_mass
        (by rw [hR.1.1]; exact Nat.le_add_right _ _), hR.1.1]
    · simp [nsmul_eq_mul]
  · rw [List.map_map]
    refine List.Nodup.map ?_ (List.nodup_attach.mpr (Finset.nodup_toList S))
    intro zz zz' h
    exact Subtype.ext h
  · intro r hr
    obtain ⟨zz, -, rfl⟩ := List.mem_map.mp hr
    have hR := (hall zz.1 (Finset.mem_toList.mp zz.2)).2.2
    simp only [grayChargedLateReserveSourceOfV2_cells]
    rw [grayChargedReserveCylinder_mass
      (by rw [hR.1.1]; exact Nat.le_add_right _ _), hR.1.1]
  · intro r hr
    obtain ⟨zz, -, rfl⟩ := List.mem_map.mp hr
    rfl

end Kolmogorov
