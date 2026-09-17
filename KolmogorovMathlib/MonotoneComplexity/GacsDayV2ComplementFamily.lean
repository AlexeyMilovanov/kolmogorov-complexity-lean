import KolmogorovMathlib.MonotoneComplexity.GacsDayV2L5Disjoint
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailLeafB

/-!
# The complement reserve family (blueprint D2, assembled)

One owner-aligned complement record per resolved source: the reserve comes
from the Phase 2A datum, the removed window is the owner fibre component,
and each record certifies `5ε/6` of reserve mass.  The records inherit the
cylinder geometry, so their cells stay globally distinct.
-/

namespace Kolmogorov

/-- The datum's owner position indexes the advantage terminal. -/
lemma grayChargedSonReserveDataV2_owner_lt
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    {replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T}
    {z : Fin n × Fin (grayTailBranch q L a e)} {t : Nat} {R : BitString}
    {k : Nat}
    (hdata : GrayChargedSonReserveDataV2 replay z t R k) :
    k < replay.advantageTerminal.frozen.length := by
  obtain ⟨pre, p, post, hsplit, hlen, -, -⟩ := hdata.2.2.1
  have h2 : (frozenV1OfV2 replay.advantageTerminal).length =
      replay.advantageTerminal.frozen.length := by
    rw [frozenV1OfV2, List.length_map]
  have h3 : (frozenV1OfV2 replay.advantageTerminal).length =
      pre.length + (post.length + 1) := by
    rw [hsplit]
    simp
  omega

/-- The advantage terminal's frozen ledger is the run's frozen ledger right
after the advantage done time (v15.1 A7′). -/
lemma grayChargedReplayV2_terminal_frozen_eq_done
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T) :
    replay.advantageTerminal.frozen =
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm (replay.advantageDoneTime + 1)).core.frozen := by
  rw [replay.advantageTerminal_frozen_eq, grayChargedRunStateV2_succ]
  have hphase := replay.advantageDone_before
  have hdone := replay.advantageDone_step
  by_cases hserved : grayChargedWaitServedB q a e
      (grayChargedBlockTailStepV2 q L a e sigma A
        (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm replay.advantageDoneTime).core
        (sm replay.advantageDoneTime)) (sm replay.advantageDoneTime) = true
  · rw [grayChargedStepV2_advantage_exit q L a e sigma A _
      (sm replay.advantageDoneTime) hphase hdone hserved,
      grayChargedStartSpendV2_frozen]
  · have hserved' : grayChargedWaitServedB q a e
        (grayChargedBlockTailStepV2 q L a e sigma A
          (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm replay.advantageDoneTime).core
          (sm replay.advantageDoneTime)) (sm replay.advantageDoneTime) = false := by
      simpa using hserved
    rw [grayChargedStepV2_advantage_wait q L a e sigma A _
      (sm replay.advantageDoneTime) hphase hdone hserved']

/-- Every advantage-terminal round was frozen by the advantage done time. -/
lemma grayChargedReplayV2_terminal_frozen_serverTime_le_done
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    {r : GrayTailRoundV2 n (grayTailBranch q L a e)}
    (hr : r ∈ replay.advantageTerminal.frozen) :
    r.serverTime <= replay.advantageDoneTime := by
  rw [grayChargedReplayV2_terminal_frozen_eq_done] at hr
  exact Nat.lt_succ_iff.mp
    (grayChargedRunStateV2_frozen_serverTime_lt q L a e sigma A sm _ r hr)

/-- Advantage-terminal rounds stay frozen at every late time. -/
lemma grayChargedReplayV2_terminal_round_mem_late
    {q L a e n T U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    (hU : replay.advantageDoneTime + 1 <= U)
    {p : GrayTailRoundV2 n (grayTailBranch q L a e)}
    (hp : p ∈ replay.advantageTerminal.frozen) :
    p ∈ (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm U).core.frozen := by
  have hpre : replay.advantageTerminal.frozen <+:
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm U).core.frozen := by
    rw [grayChargedReplayV2_terminal_frozen_eq_done replay]
    exact grayChargedRunStateV2_frozen_prefix_le q L a e sigma A sm hU
  exact hpre.sublist.mem hp

/-- **The exit-time datum for server-resolved sons**: the recorded reserve
observed at the advantage exit already dominates every advantage round, so
the full freshness datum holds at `tau = advantageDoneTime` — a time that
also precedes every spend round's snapshot, closing the spend side for
this class through the early-reserve harvest theorem. -/
theorem grayChargedReplayV2_serverResolved_exit_datum
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    (z : Fin n × Fin (grayTailBranch q L a e))
    (hz : z ∈ grayChargedReplayV2ServerResolvedSources replay) :
    exists R k, GrayChargedSonReserveDataV2 replay z
      replay.advantageDoneTime R k := by
  classical
  have hz2 : z ∈ grayChargedServerResolvedSources e
      (grayChargedSourceCount a e) (grayChargedThreshold q e) A
      (frozenV1OfV2 replay.advantageTerminal)
      (sm replay.advantageDoneTime) := hz
  have hmem := Finset.mem_filter.mp hz2
  obtain ⟨R, hR⟩ := (getTailFamilyReserve_isSome_iff e
    (grayTailBranch q L a e) A n z.1.val
    (sm replay.advantageDoneTime) [z.2.val]).mp hmem.2.2.2
  obtain ⟨chron⟩ := grayChargedReplayV2_resolved_source_chronology replay z
    (Finset.mem_union_right _ hz)
  have hexit : GrayTailThresholdExit e A sm
      (frozenV1OfV2 replay.advantageTerminal) z.1 z.2 := by
    rcases chron.resolution with h | h
    · exact h.2
    · exact h.1.toThresholdExit
  obtain ⟨pre, p, post, hsplit, hson, hcheck, hpost⟩ := hexit
  rw [frozenV1OfV2] at hsplit
  obtain ⟨pre2, p2, post2, hsplit2, hpreM, hpM, hpostM⟩ :=
    grayChargedV2_map_split hsplit
  have hdom : forall r, r ∈ replay.advantageTerminal.frozen ->
      r.serverTime <= replay.advantageDoneTime :=
    fun r hr =>
      grayChargedReplayV2_terminal_frozen_serverTime_le_done replay hr
  have hp2mem : p2 ∈ replay.advantageTerminal.frozen := by
    rw [hsplit2]
    exact List.mem_append_right _ List.mem_cons_self
  have hcheck2 : pre2 = [] ∨ exists S,
      (forall r, r ∈ pre2 -> r.serverTime <= S) ∧
      S <= replay.advantageDoneTime ∧
      (getTailFamilyReserve e (grayTailBranch q L a e) A n z.1.val
        (sm S) [z.2.val]).isNone := by
    rcases hcheck with hempty | ⟨S, hboundS, hSp, hnone⟩
    · left
      cases pre2 with
      | nil => rfl
      | cons y ys =>
          rw [hempty] at hpreM
          simp at hpreM
    · refine Or.inr ⟨S, ?_, ?_, hnone⟩
      · intro r hr
        have hmemPre : r.toV1 ∈ pre := by
          rw [← hpreM]
          exact List.mem_map_of_mem hr
        exact hboundS r.toV1 hmemPre
      · have hpT : p.serverTime <= replay.advantageDoneTime := by
          rw [← hpM]
          exact hdom p2 hp2mem
        omega
  have hpost2 : forall r, r ∈ post2 ->
      ¬ GrayTailRoundHasSon r.toV1 z.1 z.2 := by
    intro r hr
    refine hpost _ ?_
    rw [← hpostM]
    exact List.mem_map_of_mem hr
  exact ⟨R, pre2.length,
    grayChargedSonReserveDataV2_of_split hsm replay hsplit2
      (by rw [hpM]; exact hson) hR hdom hcheck2 hpost2⟩

/-- **The anchored datum for raised sons** (amendment G1.3, threshold
side): the served raised display yields an ANCHORED reserve at the pushed
time, alongside the full freshness datum. -/
theorem grayChargedReplayV2_raised_anchored_datum
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hnotpos : ¬ GrayChargedPositiveV2 q L a e n sigma A sm)
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    (z : Fin n × Fin (grayTailBranch q L a e))
    (hz : z ∈ grayChargedReplayV2RaisedSources replay) :
    exists t R k,
      GrayChargedSonReserveDataV2 replay z t R k ∧
      IsAnchoredTailFamilyReserve e (grayTailBranch q L a e) A n z.1.val
        (sm t) [z.2.val] R := by
  classical
  obtain ⟨chron⟩ := grayChargedReplayV2_resolved_source_chronology replay z
    (Finset.mem_union_left _ hz)
  have hexit : GrayTailThresholdExit e A sm
      (frozenV1OfV2 replay.advantageTerminal) z.1 z.2 := by
    rcases chron.resolution with h | h
    · exact h.2
    · exact h.1.toThresholdExit
  obtain ⟨pre, p, post, hsplit, hson, hcheck, hpost⟩ := hexit
  rw [frozenV1OfV2] at hsplit
  obtain ⟨pre2, p2, post2, hsplit2, hpreM, hpM, hpostM⟩ :=
    grayChargedV2_map_split hsplit
  have hreq := grayChargedReplayV2_raised_display_eq replay le_rfl hz
  have hnode : forall d, d ∈ ([z.2.val] : GacsDayNode) ->
      d < grayTailBranch q L a e := by
    intro d hd
    simp only [List.mem_singleton] at hd
    subst d
    exact z.2.isLt
  have hpos : 0 < getFamilyReq
      (grayChargedRunMoveV2 q L a e n sigma A sm (T + 1)) z.1.val
      [z.2.val] := by
    rw [hreq]
    exact dyadicScale_pos e
  obtain ⟨u, hu⟩ := grayChargedV2_exists_serves_of_not_positive hnotpos
    z.1.isLt (T + 1) [z.2.val] (by simp; omega) hnode hpos
  rw [hreq] at hu
  have hserveLate : Serves
      (getFamilyAlloc (sm (max u replay.advantageDoneTime)) z.1.val
        [z.2.val]) (dyadicScale e) :=
    serves_mono_time (hsm.1 z.1.val z.1.isLt)
      (le_max_left u replay.advantageDoneTime) hu
  obtain ⟨R, hR⟩ := exists_anchoredTailFamilyReserve_of_serves hsm
    z.1.isLt hnode hserveLate
  have hdom : forall r, r ∈ replay.advantageTerminal.frozen ->
      r.serverTime <= max u replay.advantageDoneTime :=
    fun r hr => le_trans
      (grayChargedReplayV2_terminal_frozen_serverTime_le_done replay hr)
      (le_max_right u replay.advantageDoneTime)
  have hp2mem : p2 ∈ replay.advantageTerminal.frozen := by
    rw [hsplit2]
    exact List.mem_append_right _ List.mem_cons_self
  have hcheck2 : pre2 = [] ∨ exists S,
      (forall r, r ∈ pre2 -> r.serverTime <= S) ∧
      S <= max u replay.advantageDoneTime ∧
      (getTailFamilyReserve e (grayTailBranch q L a e) A n z.1.val
        (sm S) [z.2.val]).isNone := by
    rcases hcheck with hempty | ⟨S, hboundS, hSp, hnone⟩
    · left
      cases pre2 with
      | nil => rfl
      | cons y ys =>
          rw [hempty] at hpreM
          simp at hpreM
    · refine Or.inr ⟨S, ?_, ?_, hnone⟩
      · intro r hr
        have hmem : r.toV1 ∈ pre := by
          rw [← hpreM]
          exact List.mem_map_of_mem hr
        exact hboundS r.toV1 hmem
      · have hpT : p.serverTime <= max u replay.advantageDoneTime := by
          rw [← hpM]
          exact hdom p2 hp2mem
        omega
  have hpost2 : forall r, r ∈ post2 ->
      ¬ GrayTailRoundHasSon r.toV1 z.1 z.2 := by
    intro r hr
    refine hpost _ ?_
    rw [← hpostM]
    exact List.mem_map_of_mem hr
  exact ⟨max u replay.advantageDoneTime, R, pre2.length,
    grayChargedSonReserveDataV2_of_split hsm replay hsplit2
      (by rw [hpM]; exact hson) hR.1 hdom hcheck2 hpost2, hR⟩

/-- Cell projection disjointness for pairwise distinct resolved coordinates. -/
private lemma grayChargedReserveComplementV2_disjoint_of_ne
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    {replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T}
    {zz zz' : Fin n × Fin (grayTailBranch q L a e)}
    {t t' : Nat} {R R' : BitString} {k k' : Nat} {f f'}
    (hd1 : GrayChargedSonReserveDataV2 replay zz t R k)
    (hd2 : GrayChargedSonReserveDataV2 replay zz' t' R' k')
    (hne : zz ≠ zz') :
    List.Disjoint
      ((grayChargedReserveComplementV2 zz.1.val
        (e + grayTailNewLoss q L) R f).map Prod.snd)
      ((grayChargedReserveComplementV2 zz'.1.val
        (e + grayTailNewLoss q L) R' f').map Prod.snd) := by
  have hpair : ¬ (zz.1.val = zz'.1.val ∧ zz.2.val = zz'.2.val) := by
    rintro ⟨h1, h2⟩
    exact hne (Prod.ext (Fin.ext h1) (Fin.ext h2))
  have hne' : R ≠ R' :=
    isTailFamilyReserve_ne_of_ne_coordinate hsm zz.1.isLt zz'.1.isLt
      zz.2.isLt zz'.2.isLt hd1.1 hd2.1 hpair
  have hcyl := grayChargedReserveCylinder_disjoint
    (i := zz.1.val) (j := zz'.1.val) (delta := e + grayTailNewLoss q L)
    hd1.1.1.1 hd2.1.1.1 hne'
  intro s hs hs'
  have hsC : s ∈ (grayChargedReserveCylinder zz.1.val
      (e + grayTailNewLoss q L) R).map Prod.snd := by
    rw [List.mem_map] at hs ⊢
    obtain ⟨y, hy, rfl⟩ := hs
    exact ⟨y, (grayChargedReserveComplementV2_sublist _ _ _ _).mem hy, rfl⟩
  have hsC' : s ∈ (grayChargedReserveCylinder zz'.1.val
      (e + grayTailNewLoss q L) R').map Prod.snd := by
    rw [List.mem_map] at hs' ⊢
    obtain ⟨y, hy, rfl⟩ := hs'
    exact ⟨y, (grayChargedReserveComplementV2_sublist _ _ _ _).mem hy, rfl⟩
  exact hcyl hsC hsC'

/-- Construction of the complement reserve source list and proof of its core
properties for any valid per-source datum package. -/
private theorem grayChargedV2_complement_reserve_sources_build
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hae : a <= e)
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    {P : Nat → Fin n × Fin (grayTailBranch q L a e) → BitString → Prop}
    (hson : ∀ z : Fin n × Fin (grayTailBranch q L a e),
      z ∈ grayChargedReplayV2RaisedSources replay ∪
        grayChargedReplayV2ServerResolvedSources replay →
      ∃ t R, (∃ k, GrayChargedSonReserveDataV2 replay z t R k) ∧
        (z ∈ grayChargedReplayV2ServerResolvedSources replay →
          t = replay.advantageDoneTime) ∧
        P t z R) :
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
      (reserves.map fun r => r.coordinate).Nodup ∧
      ((grayChargedReserveChargeV2 reserves).map Prod.snd).Nodup ∧
      (forall r, r ∈ reserves ->
        r.massContribution = dyadicScale e - dyadicScale e / 6 ∧
        dyadicScale e - dyadicScale e / 6 <=
          grayChargeMass (e + grayTailNewLoss q L) r.cells) ∧
      (forall r, r ∈ reserves ->
        exists (k : Nat)
          (hk : k < replay.advantageTerminal.frozen.length)
          (hp' : replay.advantageTerminal.frozen[k] ∈
            (grayChargedRunStateV2 (n := n)
              (b := grayTailBranch q L a e)
              q L a e sigma A sm (T + 1)).core.frozen),
          GrayChargedSonReserveDataV2 replay r.coordinate r.serviceTime
            r.reserve k ∧
          r.cells = grayChargedReserveComplementV2 r.coordinate.1.val
            (e + grayTailNewLoss q L) r.reserve
            (grayChargedOwnerFibreV2 hae
              (replay.advantageTerminal.frozen[k]) hp' r.coordinate)) ∧
      (forall r, r ∈ reserves ->
        r.coordinate ∈ grayChargedReplayV2ServerResolvedSources replay ->
        r.serviceTime = replay.advantageDoneTime) ∧
      (forall r, r ∈ reserves -> P r.serviceTime r.coordinate r.reserve) := by
  classical
  set S := grayChargedReplayV2RaisedSources replay ∪
    grayChargedReplayV2ServerResolvedSources replay
  obtain ⟨U0, time, wit, hU0⟩ := grayTail_exists_common_horizon
    (fun z => z ∈ S)
    (fun z t R =>
      (exists k, GrayChargedSonReserveDataV2 replay z t R k) ∧
      (z ∈ grayChargedReplayV2ServerResolvedSources replay ->
        t = replay.advantageDoneTime) ∧
      P t z R)
    hson
  have hTU : T + 1 <= max (T + 1) U0 := le_max_left _ _
  have hexitU : replay.advantageDoneTime + 1 <= T + 1 := by
    have h1 := replay.advantageDone_le
    have h2 := replay.advantageExit_le
    omega
  have hbuild : forall zz : {z // z ∈ S.toList},
      exists (k : Nat)
        (hk : k < replay.advantageTerminal.frozen.length)
        (hp' : replay.advantageTerminal.frozen[k] ∈
          (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm (T + 1)).core.frozen),
        GrayChargedSonReserveDataV2 replay zz.1 (time zz.1)
          (wit zz.1) k := by
    intro zz
    obtain ⟨-, ⟨k, hdata⟩, -, -⟩ := hU0 zz.1 (Finset.mem_toList.mp zz.2)
    have hk := grayChargedSonReserveDataV2_owner_lt hdata
    refine ⟨k, hk, ?_, hdata⟩
    exact grayChargedReplayV2_terminal_round_mem_late replay hexitU
      (List.getElem_mem hk)
  choose kOf hkOf hpOf hdataOf using hbuild
  let mk : {z // z ∈ S.toList} ->
      GrayChargedReserveSourceV2 q L a e n (max (T + 1) U0) A sm :=
    fun zz =>
      grayChargedComplementReserveSourceOfV2 hsm hae
        (if zz.1 ∈ grayChargedReplayV2RaisedSources replay then
          GrayChargedReserveKind.thresholdRaised
        else GrayChargedReserveKind.serverResolved)
        zz.1
        ((mem_grayChargedResolvedSources_union zz.1).mp
          (Finset.mem_toList.mp zz.2)).1
        (time zz.1)
        (le_trans (hU0 zz.1 (Finset.mem_toList.mp zz.2)).1
          (le_max_right _ _))
        (wit zz.1) (hdataOf zz).1
        (grayChargedOwnerFibreV2 hae
          (replay.advantageTerminal.frozen[kOf zz]'(hkOf zz)) (hpOf zz)
          zz.1)
        (fun u hu => grayChargedOwnerFibreV2_cell_length hae _ (hpOf zz)
          zz.1 hu)
        (grayChargedOwnerFibreV2_mass_le hae _ (hpOf zz)
          (grayChargedReplayV2_terminal_round_adv replay
            (List.getElem_mem (hkOf zz))) zz.1)
  refine ⟨max (T + 1) U0, S.toList.attach.map mk,
    hTU, replay.move_stable _ hTU, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact ⟨_, List.mem_map.mpr
      ⟨⟨z, Finset.mem_toList.mpr hz⟩, List.mem_attach _ _, rfl⟩, rfl⟩
  · intro r hr
    obtain ⟨zz, -, rfl⟩ := List.mem_map.mp hr
    simpa [mk] using Finset.mem_toList.mp zz.2
  · rw [List.map_map]
    refine List.Nodup.map ?_ (List.nodup_attach.mpr (Finset.nodup_toList S))
    intro zz zz' h
    exact Subtype.ext h
  · rw [grayChargedReserveChargeV2, List.map_flatMap, List.flatMap_map]
    refine List.nodup_flatMap.2 ⟨?_, ?_⟩
    · intro zz _
      exact grayChargedReserveComplementV2_nodup _ _ _ _
    · refine List.Pairwise.imp ?_
        (List.nodup_attach.mpr (Finset.nodup_toList S))
      intro zz zz' hne
      exact grayChargedReserveComplementV2_disjoint_of_ne hsm
        (hdataOf zz) (hdataOf zz') (fun h => hne (Subtype.ext h))
  · intro r hr
    obtain ⟨zz, -, rfl⟩ := List.mem_map.mp hr
    exact ⟨rfl, (mk zz).mass_lower⟩
  · intro r hr
    obtain ⟨zz, -, rfl⟩ := List.mem_map.mp hr
    exact ⟨kOf zz, hkOf zz, hpOf zz, hdataOf zz, rfl⟩
  · intro r hr hsr
    obtain ⟨zz, -, rfl⟩ := List.mem_map.mp hr
    exact (hU0 zz.1 (Finset.mem_toList.mp zz.2)).2.2.1 hsr
  · intro r hr
    obtain ⟨zz, -, rfl⟩ := List.mem_map.mp hr
    exact (hU0 zz.1 (Finset.mem_toList.mp zz.2)).2.2.2

/-- Per-source reserve datum for resolved sources in the anchored complement family. -/
private lemma grayChargedV2_complement_reserve_family_son_datum
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hnotpos : ¬ GrayChargedPositiveV2 q L a e n sigma A sm)
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    (hSRanch : ∀ z, z ∈ grayChargedReplayV2ServerResolvedSources replay ->
      ∃ R k, GrayChargedSonReserveDataV2 replay z replay.advantageDoneTime R k ∧
        ∃ v ∈ getFamilyAlloc (sm replay.advantageDoneTime) z.1.val [z.2.val],
          v <+: R)
    (z : Fin n × Fin (grayTailBranch q L a e))
    (hz : z ∈ grayChargedReplayV2RaisedSources replay ∪
      grayChargedReplayV2ServerResolvedSources replay) :
    ∃ t R, (∃ k, GrayChargedSonReserveDataV2 replay z t R k) ∧
      (z ∈ grayChargedReplayV2ServerResolvedSources replay ->
        t = replay.advantageDoneTime) ∧
      ∃ v ∈ getFamilyAlloc (sm t) z.1.val [z.2.val], v <+: R := by
  by_cases hsr : z ∈ grayChargedReplayV2ServerResolvedSources replay
  · obtain ⟨R, k, hd, hanch⟩ := hSRanch z hsr
    exact ⟨replay.advantageDoneTime, R, ⟨k, hd⟩, fun _ => rfl, hanch⟩
  · have hraised : z ∈ grayChargedReplayV2RaisedSources replay := by
      rw [Finset.mem_union] at hz
      exact hz.resolve_right hsr
    obtain ⟨t, R, k, hd, hanch⟩ :=
      grayChargedReplayV2_raised_anchored_datum hsm hnotpos replay z hraised
    exact ⟨t, R, ⟨k, hd⟩, fun h => absurd h hsr, hanch.2⟩

/-- **The V2 complement reserve family** (blueprint D2): one owner-aligned
`K(z)` record per resolved coordinate, at one common late horizon, each
certifying five sixths of a coarse unit, with the datum exposed for the
disjointness assembly. -/
theorem grayChargedV2_complement_reserve_family
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hae : a <= e)
    (hnotpos : ¬ GrayChargedPositiveV2 q L a e n sigma A sm)
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    (hSRanch : ∀ z, z ∈ grayChargedReplayV2ServerResolvedSources replay ->
      ∃ R k, GrayChargedSonReserveDataV2 replay z replay.advantageDoneTime R k ∧
        ∃ v ∈ getFamilyAlloc (sm replay.advantageDoneTime) z.1.val [z.2.val],
          v <+: R)
    :
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
      (reserves.map fun r => r.coordinate).Nodup ∧
      ((grayChargedReserveChargeV2 reserves).map Prod.snd).Nodup ∧
      (forall r, r ∈ reserves ->
        r.massContribution = dyadicScale e - dyadicScale e / 6 ∧
        dyadicScale e - dyadicScale e / 6 <=
          grayChargeMass (e + grayTailNewLoss q L) r.cells) ∧
      (forall r, r ∈ reserves ->
        exists (k : Nat)
          (hk : k < replay.advantageTerminal.frozen.length)
          (hp' : replay.advantageTerminal.frozen[k] ∈
            (grayChargedRunStateV2 (n := n)
              (b := grayTailBranch q L a e)
              q L a e sigma A sm (T + 1)).core.frozen),
          GrayChargedSonReserveDataV2 replay r.coordinate r.serviceTime
            r.reserve k ∧
          r.cells = grayChargedReserveComplementV2 r.coordinate.1.val
            (e + grayTailNewLoss q L) r.reserve
            (grayChargedOwnerFibreV2 hae
              (replay.advantageTerminal.frozen[k]) hp' r.coordinate)) ∧
      (forall r, r ∈ reserves ->
        r.coordinate ∈ grayChargedReplayV2ServerResolvedSources replay ->
        r.serviceTime = replay.advantageDoneTime) ∧
      (forall r, r ∈ reserves ->
        ∃ v ∈ getFamilyAlloc (sm r.serviceTime) r.coordinate.1.val
          [r.coordinate.2.val], v <+: r.reserve) :=
  grayChargedV2_complement_reserve_sources_build hsm hae replay
    (grayChargedV2_complement_reserve_family_son_datum hsm hnotpos replay hSRanch)


/-! ### The wait exit serves every raised son -/

/-- At the wait exit the raised-service test of the advantage terminal is
true: the exit step is not a wait step. -/
lemma grayChargedReplayV2_exit_served
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T) :
    grayChargedRaisedServedB e (grayChargedSourceCount a e) (grayChargedThreshold q e)
      (frozenV1OfV2 replay.advantageTerminal) (sm replay.advantageExitTime) = true := by
  have hdone := grayChargedV2_advantage_exit_terminal_done
    replay.advantage_before replay.advantage_after
  by_contra hbad
  have hserved' : grayChargedWaitServedB q a e
      (grayChargedBlockTailStepV2 q L a e sigma A
        (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm replay.advantageExitTime).core
        (sm replay.advantageExitTime)) (sm replay.advantageExitTime) = false := by
    rw [← replay.advantageTerminal_eq]
    unfold grayChargedWaitServedB
    simpa using hbad
  apply replay.advantage_after
  rw [grayChargedRunStateV2_succ,
    grayChargedStepV2_advantage_wait q L a e sigma A _ (sm replay.advantageExitTime)
      replay.advantage_before hdone hserved']

/-- Every threshold-raised source son is served at scale `2^-e` at the wait
exit. -/
lemma grayChargedReplayV2_raised_served_at_exit
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    {z : Fin n × Fin (grayTailBranch q L a e)}
    (hz : z ∈ grayChargedReplayV2RaisedSources replay) :
    Serves (getFamilyAlloc (sm replay.advantageExitTime) z.1.val [z.2.val])
      (dyadicScale e) :=
  (grayChargedRaisedServedB_eq_true_iff.mp (grayChargedReplayV2_exit_served replay)) z hz

/-- **The exit-time datum for raised sons** (v15.1 A7′): the reserve served at
the wait exit, anchored by the served bin, with the owner split and the
freshness datum of the son's last consideration. -/
theorem grayChargedReplayV2_raised_anchored_datum_exit
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    (z : Fin n × Fin (grayTailBranch q L a e))
    (hz : z ∈ grayChargedReplayV2RaisedSources replay) :
    exists R k,
      GrayChargedSonReserveDataV2 replay z replay.advantageExitTime R k ∧
      IsAnchoredTailFamilyReserve e (grayTailBranch q L a e) A n z.1.val
        (sm replay.advantageExitTime) [z.2.val] R := by
  classical
  obtain ⟨chron⟩ := grayChargedReplayV2_resolved_source_chronology replay z
    (Finset.mem_union_left _ hz)
  have hexit : GrayTailThresholdExit e A sm
      (frozenV1OfV2 replay.advantageTerminal) z.1 z.2 := by
    rcases chron.resolution with h | h
    · exact h.2
    · exact h.1.toThresholdExit
  obtain ⟨pre, p, post, hsplit, hson, hcheck, hpost⟩ := hexit
  rw [frozenV1OfV2] at hsplit
  obtain ⟨pre2, p2, post2, hsplit2, hpreM, hpM, hpostM⟩ :=
    grayChargedV2_map_split hsplit
  have hnode : forall d, d ∈ ([z.2.val] : GacsDayNode) ->
      d < grayTailBranch q L a e := by
    intro d hd
    simp only [List.mem_singleton] at hd
    subst d
    exact z.2.isLt
  have hserveExit := grayChargedReplayV2_raised_served_at_exit replay hz
  obtain ⟨R, hR⟩ := exists_anchoredTailFamilyReserve_of_serves hsm
    z.1.isLt hnode hserveExit
  have hdom : forall r, r ∈ replay.advantageTerminal.frozen ->
      r.serverTime <= replay.advantageExitTime :=
    fun r hr => le_trans
      (grayChargedReplayV2_terminal_frozen_serverTime_le_done replay hr)
      replay.advantageDone_le
  have hp2mem : p2 ∈ replay.advantageTerminal.frozen := by
    rw [hsplit2]
    exact List.mem_append_right _ List.mem_cons_self
  have hcheck2 : pre2 = [] ∨ exists S,
      (forall r, r ∈ pre2 -> r.serverTime <= S) ∧
      S <= replay.advantageExitTime ∧
      (getTailFamilyReserve e (grayTailBranch q L a e) A n z.1.val
        (sm S) [z.2.val]).isNone := by
    rcases hcheck with hempty | ⟨S, hboundS, hSp, hnone⟩
    · left
      cases pre2 with
      | nil => rfl
      | cons y ys =>
          rw [hempty] at hpreM
          simp at hpreM
    · refine Or.inr ⟨S, ?_, ?_, hnone⟩
      · intro r hr
        have hmem : r.toV1 ∈ pre := by
          rw [← hpreM]
          exact List.mem_map_of_mem hr
        exact hboundS r.toV1 hmem
      · have hpT : p.serverTime <= replay.advantageExitTime := by
          rw [← hpM]
          exact hdom p2 hp2mem
        omega
  have hpost2 : forall r, r ∈ post2 ->
      ¬ GrayTailRoundHasSon r.toV1 z.1 z.2 := by
    intro r hr
    refine hpost _ ?_
    rw [← hpostM]
    exact List.mem_map_of_mem hr
  exact ⟨R, pre2.length,
    grayChargedSonReserveDataV2_of_split hsm replay hsplit2
      (by rw [hpM]; exact hson) hR.1 hdom hcheck2 hpost2, hR⟩

/-- Per-source reserve datum for resolved sources in the plain complement family. -/
private lemma grayChargedV2_complement_reserve_family_plain_son_datum
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    (z : Fin n × Fin (grayTailBranch q L a e))
    (hz : z ∈ grayChargedReplayV2RaisedSources replay ∪
      grayChargedReplayV2ServerResolvedSources replay) :
    ∃ t R, (∃ k, GrayChargedSonReserveDataV2 replay z t R k) ∧
      (z ∈ grayChargedReplayV2ServerResolvedSources replay ->
        t = replay.advantageDoneTime) ∧
      t <= replay.advantageExitTime := by
  by_cases hsr : z ∈ grayChargedReplayV2ServerResolvedSources replay
  · obtain ⟨R, k, hd⟩ := grayChargedReplayV2_serverResolved_exit_datum hsm replay z hsr
    exact ⟨replay.advantageDoneTime, R, ⟨k, hd⟩, fun _ => rfl, replay.advantageDone_le⟩
  · have hraised : z ∈ grayChargedReplayV2RaisedSources replay := by
      rw [Finset.mem_union] at hz
      exact hz.resolve_right hsr
    obtain ⟨R, k, hd, -⟩ :=
      grayChargedReplayV2_raised_anchored_datum_exit hsm replay z hraised
    exact ⟨replay.advantageExitTime, R, ⟨k, hd⟩, fun h => absurd h hsr, le_rfl⟩

/-- **The V2 complement reserve family** (blueprint D2): one owner-aligned
`K(z)` record per resolved coordinate, at one common late horizon, each
certifying five sixths of a coarse unit, with the datum exposed for the
disjointness assembly. -/
theorem grayChargedV2_complement_reserve_family_plain
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hae : a <= e)
    (_hnotpos : ¬ GrayChargedPositiveV2 q L a e n sigma A sm)
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
      (reserves.map fun r => r.coordinate).Nodup ∧
      ((grayChargedReserveChargeV2 reserves).map Prod.snd).Nodup ∧
      (forall r, r ∈ reserves ->
        r.massContribution = dyadicScale e - dyadicScale e / 6 ∧
        dyadicScale e - dyadicScale e / 6 <=
          grayChargeMass (e + grayTailNewLoss q L) r.cells) ∧
      (forall r, r ∈ reserves ->
        exists (k : Nat)
          (hk : k < replay.advantageTerminal.frozen.length)
          (hp' : replay.advantageTerminal.frozen[k] ∈
            (grayChargedRunStateV2 (n := n)
              (b := grayTailBranch q L a e)
              q L a e sigma A sm (T + 1)).core.frozen),
          GrayChargedSonReserveDataV2 replay r.coordinate r.serviceTime
            r.reserve k ∧
          r.cells = grayChargedReserveComplementV2 r.coordinate.1.val
            (e + grayTailNewLoss q L) r.reserve
            (grayChargedOwnerFibreV2 hae
              (replay.advantageTerminal.frozen[k]) hp' r.coordinate)) ∧
      (forall r, r ∈ reserves ->
        r.coordinate ∈ grayChargedReplayV2ServerResolvedSources replay ->
        r.serviceTime = replay.advantageDoneTime) ∧
      (forall r, r ∈ reserves -> r.serviceTime <= replay.advantageExitTime) :=
  grayChargedV2_complement_reserve_sources_build hsm hae replay
    (grayChargedV2_complement_reserve_family_plain_son_datum hsm replay)

end Kolmogorov
