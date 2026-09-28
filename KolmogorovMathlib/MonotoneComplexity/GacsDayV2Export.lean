import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Closure
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2SourceLedger

/-!
# The V2 export: anchored transport validity for the whole charged run

Stage D1's export (proof doc v14 §9.3): the run-level harvest-chain bridge
(both phases store `fineEnd = blockAnchor + L`, so the projected frozen list
is a V1 `GrayTailHarvestChain`), and the ANCHORED transport validity — a
designated local cell of ANY frozen round (advantage block or spend block)
extends to a new gray cell of the outer owner at the common final depth,
anchored at any `aa ≤ blockAnchor`.  With `aa = a` this is the `(a, D]`
export both phases enter (the blueprint's D1 coarsening), the point the
de-scoped architecture could not reach (XII.8(a)).
-/

namespace Kolmogorov

/-- Both phases of a frozen V2 charged round satisfy
`fineEnd = blockAnchor + L`. -/
lemma grayChargedRunStateV2_frozen_fineEnd {n : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (t : Nat)
    {p : GrayTailRoundV2 n (grayTailBranch q L a e)}
    (hp : p ∈ (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).core.frozen) :
    p.fineEnd = p.blockAnchor + L := by
  have hvalid := (grayChargedRunStateV2_coreCertified
    q L a e sigma A sm t).round_valid p hp
  rcases hvalid.2.2.2.2.2 with ⟨hanchor, hfine, -⟩ |
    ⟨pass, -, hanchor, hfine, -⟩
  · rw [hfine, hanchor, grayTailRoundDelta]
  · rw [hfine, hanchor, grayChargedSpendDelta]

/-- Every frozen round of the V2 charged run keeps the ambient list `A` in
its `unavailable` list (the harvest chain with admissible snapshots, both
phases). -/
lemma grayChargedRunStateV2_frozen_mem_unavailable_of_A {n : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (t : Nat)
    {p : GrayTailRoundV2 n (grayTailBranch q L a e)}
    (hp : p ∈ (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).core.frozen) :
    forall z, z ∈ A -> z ∈ p.unavailable := by
  intro z hz
  obtain ⟨k, hk, hpk⟩ := List.mem_iff_getElem.mp hp
  obtain ⟨s, -, hsnap⟩ := (grayChargedRunStateV2_coreCertified (n := n)
    q L a e sigma A sm t).frozen_chain k hk
  rw [← hpk, hsnap]
  exact List.mem_append_left _ hz

/-- **The anchored V2 transport validity** (v14 §9.3, both phases): a
designated local gray cell of any frozen charged round extends to a new gray
cell of the round's outer owner at the common final depth, anchored at any
`aa ≤ blockAnchor`. -/
theorem grayChargedRunV2_cell_transport_valid
    {n q L a e t U aa : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    {p : GrayTailRoundV2 n (grayTailBranch q L a e)}
    (hp : p ∈ (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).core.frozen)
    (hlow : aa <= p.blockAnchor)
    (hTU : p.serverTime <= U)
    (j : Fin p.slots.length) {cell w : BitString}
    (hcell : cell ∈ newGrayCellsList p.blockAnchor (p.blockAnchor + L)
      (getFamilyAlloc (grayTailLocalServerMove (p.blockAnchor + L) p.slots
        (sm p.serverTime)) j.val []) p.unavailable)
    (hw : cell.length + w.length = e + grayTailNewLoss q L) :
    (cell ++ w) ∈ newGrayCellsList aa (e + grayTailNewLoss q L)
      (getFamilyAlloc (sm U) (p.slots.get j).1.val []) A := by
  obtain ⟨hcellLen, hnear, hfresh⟩ := mem_newGrayCellsList.mp hcell
  rw [mem_newGrayCellsList]
  refine ⟨by simp [hw], ?_, ?_⟩
  · obtain ⟨z, hz, hzcomp⟩ := hnear
    have hzFamily := grayCharged_mem_localAlloc_imp_mem_family p.toV1
      ⟨j.val, j.isLt⟩ hz
    obtain ⟨root, hroot, hrootz⟩ :=
      exists_root_prefix_of_family_alloc hsm (p.slots.get j).1.isLt hTU
        (by
          intro c hc
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl
          · exact (p.slots.get j).2.1.isLt
          · exact (p.slots.get j).2.2.isLt) hzFamily
    refine ⟨root, hroot, ?_⟩
    have hcoarse : cell.take p.blockAnchor <+: root ∨
        root <+: cell.take p.blockAnchor :=
      prefixComparable_of_common_extension hzcomp hrootz
    have htakePrefix : (cell ++ w).take aa <+: cell.take p.blockAnchor := by
      have htake : cell.take aa <+: cell.take p.blockAnchor := by
        simpa [List.take_take, min_eq_left hlow] using
          (List.take_prefix aa (cell.take p.blockAnchor))
      have hacell : aa <= cell.length := by rw [hcellLen]; omega
      simpa [List.take_append_of_le_length hacell] using htake
    exact prefixComparable_of_prefix_of_prefixComparable htakePrefix hcoarse
  · rintro ⟨c, hc, hcomp⟩
    refine hfresh ⟨c, ?_, ?_⟩
    · exact grayChargedRunStateV2_frozen_mem_unavailable_of_A q L a e sigma A sm t
        hp c hc
    · exact prefixComparable_of_prefix_of_prefixComparable
        (List.prefix_append cell w) hcomp

/-- Phase discrimination for a frozen V2 charged round: the call depth
separates advantage anchors (`≥ callDepth`) from spend anchors (`≤ e+3`). -/
lemma grayChargedRunStateV2_frozen_phase_split {n : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (t : Nat)
    {p : GrayTailRoundV2 n (grayTailBranch q L a e)}
    (hp : p ∈ (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).core.frozen)
    (hae : a <= e)
    (hfine : grayCallDepth q e <= p.blockAnchor) :
    p.blockAnchor = grayTailRoundEps q L e p.roundIndex ∧
      p.fineEnd = grayTailRoundDelta q L e p.roundIndex ∧
      grayChargedBlockGoalAtB q L e p.roundIndex
        p.slots.length p.unavailable p.move
          (grayTailLocalServerMove p.fineEnd p.slots
            (sm p.serverTime)) = true ∧
      (forall s, s ∈ p.slots -> grayInAdvBlock q L p.roundIndex s.2.2.val) ∧
      p.roundIndex < grayChargedAdvantageRoundCount q := by
  have hvalid := (grayChargedRunStateV2_coreCertified (n := n)
    q L a e sigma A sm t).round_valid p hp
  rcases hvalid.2.2.2.2.2 with ⟨h1, h2, h3, h4, h5, -⟩ |
    ⟨pass, -, hdepth, -, -, -⟩
  · exact ⟨h1, h2, h3, h4, h5⟩
  · exfalso
    have hcall5 : e + 5 <= grayCallDepth q e := by
      have h4sz : 2 ^ 2 <= 3 * q + 5 := by omega
      have := Nat.lt_size.mpr h4sz
      unfold grayCallDepth
      omega
    have hsp : grayChargedSpendEps a L e pass <= e + 3 := by
      unfold grayChargedSpendEps grayChargedSpendAlphaDepth
      exact max_le (by omega) (by omega)
    rw [hdepth] at hfine
    omega

/-- The advantage goal of a fine frozen round of the V2 charged run. -/
lemma grayChargedRunStateV2_frozen_adv_goal {n : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (t : Nat)
    {p : GrayTailRoundV2 n (grayTailBranch q L a e)}
    (hp : p ∈ (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).core.frozen)
    (hae : a <= e)
    (hfine : grayCallDepth q e <= p.blockAnchor) :
    grayChargedBlockGoalAtB q L e p.roundIndex
      p.slots.length p.unavailable p.move
        (grayTailLocalServerMove p.fineEnd p.slots (sm p.serverTime)) = true :=
  (grayChargedRunStateV2_frozen_phase_split q L a e sigma A sm t hp
    hae hfine).2.2.1

/-- The spend goal of a coarse frozen round of the V2 charged run. -/
lemma grayChargedRunStateV2_frozen_spend_goal {n : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (t : Nat)
    {p : GrayTailRoundV2 n (grayTailBranch q L a e)}
    (hp : p ∈ (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).core.frozen)
    (hcoarse : ¬ grayCallDepth q e <= p.blockAnchor) :
    ∃ pass, pass < 8 ∧
      p.blockAnchor = grayChargedSpendEps a L e pass ∧
      p.fineEnd = grayChargedSpendDelta a L e pass ∧
      grayChargedBlockSpendGoalAtB q L a e pass
        p.slots.length p.unavailable p.move
          (grayTailLocalServerMove p.fineEnd p.slots
            (sm p.serverTime)) = true := by
  have hvalid := (grayChargedRunStateV2_coreCertified (n := n)
    q L a e sigma A sm t).round_valid p hp
  rcases hvalid.2.2.2.2.2 with ⟨h1, -, -, -, -, -⟩ |
    ⟨pass, hpass, hdepth, hfineEq, hgoal, -, -⟩
  · exfalso
    apply hcoarse
    rw [h1]
    unfold grayTailRoundEps
    exact Nat.le_add_right _ _
  · exact ⟨pass, hpass, hdepth, hfineEq, hgoal⟩

/-- All displayed frozen requests of the V2 run are nonnegative. -/
lemma grayChargedRunStateV2_frozenEntries_req_nonneg {n : Nat}
    {q L a e t : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    (z : GrayTailSlot n (grayTailBranch q L a e) × ClientMove)
    (hz : z ∈ grayTailFrozenEntries
      ((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t).core.frozen.map GrayTailRoundV2.toV1)) :
    0 <= getReq z.2 [] := by
  rw [grayTailFrozenEntries, List.mem_flatMap] at hz
  obtain ⟨pV1, hpV1, hzp⟩ := hz
  rw [List.mem_map] at hpV1
  obtain ⟨p, hp, rfl⟩ := hpV1
  have hshape := ((grayChargedRunStateV2_coreCertified (n := n)
    q L a e sigma A sm t).round_valid p hp).2.2.2.2.2
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hzp
  rcases hshape with ⟨hanchor, -, hgoal, -, -, -⟩ |
    ⟨pass, -, hanchor, -, hgoal, -, -⟩
  · have hj := (grayChargedBlockGoalAtB_root_bounds hgoal
      (⟨j.val, by simp [GrayTailRoundV2.toV1]⟩ : Fin _)).1
    have hpos : (0 : Rat) <=
        dyadicScale (grayTailRoundEps q L e p.roundIndex) / 2 :=
      div_nonneg (dyadicScale_pos _).le (by norm_num)
    have hnn : (0 : Rat) <= getFamilyReq p.move j.val [] := le_trans hpos hj
    simpa [getFamilyReq, GrayTailRoundV2.toV1] using hnn
  · have hj := (grayChargedBlockSpendGoalAtB_root_bounds hgoal
      (⟨j.val, by simp [GrayTailRoundV2.toV1]⟩ : Fin _)).1
    have hpos : (0 : Rat) <=
        dyadicScale (grayChargedSpendEps a L e pass) / 2 :=
      div_nonneg (dyadicScale_pos _).le (by norm_num)
    have hnn : (0 : Rat) <= getFamilyReq p.move j.val [] := le_trans hpos hj
    simpa [getFamilyReq, GrayTailRoundV2.toV1] using hnn

/-- After the V2 controller is done, the displayed root request equals the
charged root request over the projected frozen entries. -/
lemma grayChargedRunMoveV2_root_eq_of_done
    {q L a e n U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hdone : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm U).phase = .done)
    (i : Fin n) :
    getFamilyReq (grayChargedRunMoveV2 q L a e n sigma A sm U) i.val [] =
      grayChargedRootRequest (grayChargedSourceCount a e)
        (grayChargedThreshold q e) (dyadicScale e)
        (grayTailFrozenEntries
          ((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm U).core.frozen.map GrayTailRoundV2.toV1)) i := by
  have hslots := grayChargedRunStateV2_slots_eq_nil_of_done
    q L a e sigma A sm U hdone
  rw [show grayChargedRunMoveV2 q L a e n sigma A sm U =
      playClientFamily A n (grayChargedStrategyV2 q L a e sigma) sm U from rfl,
    playClientFamily_grayChargedStrategyV2]
  simp only [grayChargedDisplayedMoveV2, hdone, hslots]
  simp [getFamilyReq, familyClientMoveAt, grayChargedTailFamilyMove,
    List.getD_eq_getElem?_getD, i.isLt, grayTailEntries, grayTailSlotEntries]

/-- **The request window (L4, V2)**: one frozen recursive slot's displayed
request never exceeds the final displayed request of its outer root. -/
theorem grayChargedV2_frozen_slot_req_le_final_root
    {q L a e n T U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    (hU : T + 1 <= U) (_hae : a <= e)
    {p : GrayTailRoundV2 n (grayTailBranch q L a e)}
    (hp : p ∈ (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm (T + 1)).core.frozen)
    (j : Fin p.slots.length) :
    getFamilyReq p.move j.val [] <=
      getFamilyReq (grayChargedRunMoveV2 q L a e n sigma A sm U)
        (p.slots.get j).1.val [] := by
  classical
  set frozenV1 := (grayChargedRunStateV2 (n := n)
    (b := grayTailBranch q L a e)
    q L a e sigma A sm (T + 1)).core.frozen.map GrayTailRoundV2.toV1
    with hfrozen
  set entries := grayTailFrozenEntries frozenV1 with hentries
  set i : Fin n := (p.slots.get j).1 with hi
  set c : Fin (grayTailBranch q L a e) := (p.slots.get j).2.1 with hc
  have hreq : forall z, z ∈ entries -> 0 <= getReq z.2 [] := by
    intro z hz
    exact grayChargedRunStateV2_frozenEntries_req_nonneg
      (q := q) (L := L) (a := a) (e := e)
      (t := T + 1) (sigma := sigma) (A := A) (sm := sm) z hz
  have hmemEntry : (p.slots.get j, familyClientMoveAt p.move j.val) ∈
      entries := by
    rw [hentries, grayTailFrozenEntries, List.mem_flatMap]
    refine ⟨p.toV1, List.mem_map_of_mem hp, ?_⟩
    rw [grayTailSlotEntries]
    exact List.mem_ofFn.mpr ⟨⟨j.val, by
      simp [GrayTailRoundV2.toV1]⟩, by
      simp [GrayTailRoundV2.toV1]⟩
  have hterm : getFamilyReq p.move j.val [] <= grayTailSonBase entries i c := by
    have := grayTailSonBase_single_le hmemEntry rfl rfl hreq
    simpa [getFamilyReq, familyClientMoveAt] using this
  have hshape := ((grayChargedRunStateV2_coreCertified (n := n)
    q L a e sigma A sm (T + 1)).round_valid p hp).2.2.2.2.2
  have hson : getFamilyReq p.move j.val [] <=
      grayChargedSonRequest (grayChargedSourceCount a e)
        (grayChargedThreshold q e) (dyadicScale e) entries i c := by
    by_cases hcs : c.val < grayChargedSourceCount a e
    · rw [grayChargedSonRequest_source i c hcs, grayTailSonRequest]
      by_cases hraise : grayChargedThreshold q e < grayTailSonBase entries i c
      · simp only [hraise, if_true]
        rcases hshape with ⟨hanchor, -, hgoal, -, -, -⟩ |
          ⟨pass, -, -, -, -, hpSlots, -⟩
        · have hub := (grayChargedBlockGoalAtB_root_bounds hgoal
            (⟨j.val, j.isLt⟩ : Fin p.slots.length)).2
          refine le_trans hub ?_
          refine le_trans (dyadicScale_antitone ?_)
            (dyadicScale_antitone (le_grayCallDepth q e))
          unfold grayTailRoundEps
          exact Nat.le_add_right _ _
        · exfalso
          have hpair := hpSlots _ (List.get_mem p.slots j)
          have hge : grayChargedSourceCount a e <=
              (p.slots.get j).2.1.val :=
            grayBlockSpendPairs_first_ge hpair
          rw [hc] at hcs
          omega
      · simp only [hraise, if_false]
        exact hterm
    · rw [grayChargedSonRequest_spare i c (Nat.not_lt.mp hcs)]
      exact hterm
  have hnonneg : forall d : Fin (grayTailBranch q L a e),
      0 <= grayChargedSonRequest (grayChargedSourceCount a e)
        (grayChargedThreshold q e) (dyadicScale e) entries i d := by
    intro d
    by_cases hds : d.val < grayChargedSourceCount a e
    · rw [grayChargedSonRequest_source i d hds, grayTailSonRequest]
      by_cases hraise : grayChargedThreshold q e < grayTailSonBase entries i d
      · simp only [hraise, if_true]
        exact (dyadicScale_pos e).le
      · simp only [hraise, if_false]
        exact grayTailSonBase_nonneg_global hreq
    · rw [grayChargedSonRequest_spare i d (Nat.not_lt.mp hds)]
      exact grayTailSonBase_nonneg_global hreq
  have hroot : grayChargedSonRequest (grayChargedSourceCount a e)
      (grayChargedThreshold q e) (dyadicScale e) entries i c <=
      grayChargedRootRequest (grayChargedSourceCount a e)
        (grayChargedThreshold q e) (dyadicScale e) entries i := by
    rw [grayChargedRootRequest]
    exact Finset.single_le_sum (f := fun d =>
      grayChargedSonRequest (grayChargedSourceCount a e)
        (grayChargedThreshold q e) (dyadicScale e) entries i d)
      (fun d _ => hnonneg d) (Finset.mem_univ c)
  have hdisplay : getFamilyReq (grayChargedRunMoveV2 q L a e n sigma A sm U)
      i.val [] =
      grayChargedRootRequest (grayChargedSourceCount a e)
        (grayChargedThreshold q e) (dyadicScale e) entries i := by
    rw [grayChargedRunMoveV2_root_eq_of_done (replay.done_stable U hU).1 i]
    rw [hentries, hfrozen]
    congr 2
    rw [(replay.done_stable U hU).2]
  rw [hdisplay]
  exact le_trans hson hroot

end Kolmogorov
