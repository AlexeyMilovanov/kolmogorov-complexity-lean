import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailFresh
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailLeafBGeom
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailOwnerIndex
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Sources
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2ResolutionExact
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Reserves
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2ReserveSupport

/-!
# Terminal reserve chronology for the block controller (Phase 2A)

The blueprint's §3.4 bridge on the V2 path: an advantage round's designated
cell is comparable, at the block anchor, with one of the round's own slot
allocations; a reserve that is prefix-incomparable with every allocation of
that slot is therefore prefix-incomparable with the cell itself, because the
cell is strictly deeper than the reserve.  Combined with the V1 checkpoint
freshness theorem, transported through `toV1`, this excludes every own-fibre
round strictly before the exit's last owner round.
-/

namespace Kolmogorov

/-- The internal call depth exceeds the outer scale. -/
lemma grayChargedV2_lt_callDepth (q e : Nat) : e < grayCallDepth q e := by
  unfold grayCallDepth
  omega

/-- **The §3.4 trace bridge**: a designated cell whose anchor trace is
comparable with a slot allocation is prefix-incomparable with any reserve
that is prefix-incomparable with every allocation of the slot and strictly
coarser than the anchor. -/
lemma grayChargedV2_trace_incomparable_of_alloc_fresh
    {aa d : Nat} {S U : List BitString} {cell R : BitString}
    (hcell : cell ∈ newGrayCellsList aa d S U)
    (hfreshR : forall w, w ∈ S -> ¬ (R <+: w ∨ w <+: R))
    (hlen : R.length < aa) (had : aa <= d) :
    ¬ (cell <+: R ∨ R <+: cell) := by
  obtain ⟨hclen, ⟨w, hw, hcomp⟩, -⟩ := mem_newGrayCellsList.mp hcell
  intro hcmp
  rcases hcmp with h | h
  · have := h.length_le
    omega
  · have htR : R <+: cell.take aa := by
      have h1 : (cell.take aa).take R.length = cell.take R.length := by
        rw [List.take_take, min_eq_left (by omega)]
      have h2 : cell.take R.length = R := by
        obtain ⟨tl, htl⟩ := h
        rw [← htl, List.take_left]
      rw [← h2, ← h1]
      exact List.take_prefix _ _
    rcases hcomp with h3 | h3
    · exact hfreshR w hw (Or.inl (htR.trans h3))
    · rcases List.prefix_or_prefix_of_prefix h3 htR with h4 | h4
      · exact hfreshR w hw (Or.inr h4)
      · exact hfreshR w hw (Or.inl h4)

/-- Split a mapped list along a mapped decomposition. -/
lemma grayChargedV2_map_split {alpha beta : Type _} {f : alpha -> beta}
    {l : List alpha} {pre : List beta} {p : beta} {post : List beta}
    (h : l.map f = pre ++ p :: post) :
    exists pre2 p2 post2, l = pre2 ++ p2 :: post2 ∧
      pre2.map f = pre ∧ f p2 = p ∧ post2.map f = post := by
  induction l generalizing pre with
  | nil => cases pre <;> simp at h
  | cons x xs ih =>
      cases pre with
      | nil =>
          rw [List.map_cons, List.nil_append] at h
          obtain ⟨h1, h2⟩ := List.cons_eq_cons.mp h
          exact ⟨[], x, xs, rfl, rfl, h1, h2⟩
      | cons y ys =>
          rw [List.map_cons, List.cons_append] at h
          obtain ⟨h1, h2⟩ := List.cons_eq_cons.mp h
          obtain ⟨pre2, p2, post2, hsplit, hpre, hp, hpost⟩ := ih h2
          refine ⟨x :: pre2, p2, post2, ?_, ?_, hp, hpost⟩
          · rw [hsplit]
            rfl
          · rw [List.map_cons, hpre, h1]

/-- **Checkpoint freshness on V2 rounds** (§4.2, transported through `toV1`):
a threshold exit of the projected frozen list, together with a reserve whose
service time dominates every owner round, splits the V2 frozen list at a last
owner round so that the reserve is prefix-incomparable with every own-fibre
slot allocation of every earlier round, and no later round carries the son. -/
theorem grayChargedV2_thresholdExit_pre_allocations_fresh
    {n b e L T : Nat} {A : Allocation} {sm : Nat -> FamilyServerMove}
    (hleg : familyServerPlayLegal n b A sm)
    {frozen2 : List (GrayTailRoundV2 n b)} {i : Fin n} {c : Fin b}
    (h : GrayTailThresholdExit e A sm
      (frozen2.map GrayTailRoundV2.toV1) i c)
    {R : BitString}
    (hR : IsTailFamilyReserve e b A n i.val (sm T) [c.val] R)
    (hafter : forall p, p ∈ frozen2.map GrayTailRoundV2.toV1 ->
      GrayTailRoundHasSon p i c -> p.serverTime <= T) :
    exists pre2 p2 post2, frozen2 = pre2 ++ p2 :: post2 ∧
      GrayTailRoundHasSon p2.toV1 i c ∧
      (forall r2, r2 ∈ post2 -> ¬ GrayTailRoundHasSon r2.toV1 i c) ∧
      forall q2, q2 ∈ pre2 ->
        forall j : Fin q2.slots.length,
          (q2.slots.get j).1 = i ->
          (q2.slots.get j).2.1 = c ->
          forall d, d ∈ getFamilyAlloc
            (grayTailLocalServerMove (q2.blockAnchor + L)
              q2.slots (sm q2.serverTime)) j.val [] ->
            ¬ (R <+: d ∨ d <+: R) := by
  obtain ⟨pre, p, post, hsplit, hp, hfresh, hpost⟩ := h
  obtain ⟨pre2, p2, post2, rfl, hpreM, hpM, hpostM⟩ :=
    grayChargedV2_map_split hsplit
  refine ⟨pre2, p2, post2, rfl, by rw [hpM]; exact hp, ?_, ?_⟩
  · intro r2 hr2 hson
    refine hpost _ ?_ hson
    rw [← hpostM]
    exact List.mem_map_of_mem hr2
  · intro q2 hq2 j hji hjc d hd
    rcases hfresh with hempty | ⟨checkpoint, hmax, hcheckpoint, hnone⟩
    · cases pre2 with
      | nil => simp at hq2
      | cons y ys =>
          rw [hempty] at hpreM
          simp at hpreM
    · have hqCheckpoint : q2.serverTime <= checkpoint := by
        have := hmax q2.toV1 (by rw [← hpreM]; exact List.mem_map_of_mem hq2)
        exact this
      have hpT : p2.toV1.serverTime <= T := by
        refine hafter p2.toV1 ?_ (by rw [hpM]; exact hp)
        exact List.mem_map_of_mem
          (List.mem_append_right _ List.mem_cons_self)
      have hcheckpointT : checkpoint <= T := by
        have hpc : checkpoint <= p.serverTime := hcheckpoint
        rw [hpM] at hpT
        omega
      have hmono := allocationSubset_mono_time
        (hleg.1 i.val i.isLt) hqCheckpoint
        [c.val, (q2.slots.get j).2.2.val]
      have hdRaw : d ∈ getFamilyAlloc (sm q2.serverTime) i.val
          [c.val, (q2.slots.get j).2.2.val] := by
        rw [getFamilyAlloc_grayTailLocalServerMove
          q2.slots (sm q2.serverTime) j.val j.isLt [] (by simp)] at hd
        have hd' := (mem_truncAlloc.mp hd).1
        have hd'' : d ∈ getFamilyAlloc (sm q2.serverTime)
            (q2.slots.get j).1.val
            [(q2.slots.get j).2.1.val, (q2.slots.get j).2.2.val] := by
          simpa [getFamilyAlloc, getAlloc_extractSubtreeServerMove] using hd'
        simpa only [hji, hjc] using hd''
      obtain ⟨d', hd', hd'd⟩ := hmono d hdRaw
      have hnot := IsTailFamilyReserve.not_tail_of_search_none
        hleg hcheckpointT hR hnone
      have hfreshR := IsTailReserve.fresh_of_not_before
        (hleg.1 i.val i.isLt) hcheckpointT
        (x := [c.val]) (by simp)
        hR.1 hnot
        (y := [c.val, (q2.slots.get j).2.2.val]) (by simp)
        (by
          intro z hz
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
          rcases hz with rfl | rfl
          · exact c.isLt
          · exact (q2.slots.get j).2.2.isLt)
        hd'
      intro hcomp
      exact hfreshR
        (prefixComparable_of_common_extension hcomp hd'd)

/-- The per-son reserve freshness datum: a reserve at a time dominating every advantage round, the
owner split position in the V1 projection of the frozen list, and prefix-incomparability with
every slot allocation displayed outside the owner round's own slot. -/
def GrayChargedSonReserveDataV2
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    (z : Fin n × Fin (grayTailBranch q L a e))
    (t : Nat) (R : BitString) (k : Nat) : Prop :=
  IsTailFamilyReserve e (grayTailBranch q L a e) A n z.1.val
      (sm t) [z.2.val] R ∧
    (forall r, r ∈ replay.advantageTerminal.frozen -> r.serverTime <= t) ∧
    GrayTailOwnerSplitAt (frozenV1OfV2 replay.advantageTerminal) z.1 z.2 k ∧
    forall kk : Fin replay.advantageTerminal.frozen.length,
      forall j : Fin (replay.advantageTerminal.frozen[kk.val]).slots.length,
        (kk.val ≠ k ∨
          ((replay.advantageTerminal.frozen[kk.val]).slots.get j).1 ≠ z.1 ∨
          ((replay.advantageTerminal.frozen[kk.val]).slots.get j).2.1 ≠
            z.2) ->
        forall d, d ∈ getFamilyAlloc
            (grayTailLocalServerMove
              ((replay.advantageTerminal.frozen[kk.val]).blockAnchor + L)
              (replay.advantageTerminal.frozen[kk.val]).slots
              (sm (replay.advantageTerminal.frozen[kk.val]).serverTime))
            j.val [] ->
          ¬ (R <+: d ∨ d <+: R)

/-- The shared assembly (V2): an exit split of the advantage terminal,
a reserve dominating every advantage round, and the split's no-reserve
checkpoint yield the complete per-son freshness datum at the split
position. -/
lemma grayChargedSonReserveDataV2_of_split
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    {z : Fin n × Fin (grayTailBranch q L a e)} {t : Nat} {R : BitString}
    {pre post : List (GrayTailRoundV2 n (grayTailBranch q L a e))}
    {p : GrayTailRoundV2 n (grayTailBranch q L a e)}
    (hsplit : replay.advantageTerminal.frozen = pre ++ p :: post)
    (hson : GrayTailRoundHasSon p.toV1 z.1 z.2)
    (hR : IsTailFamilyReserve e (grayTailBranch q L a e) A n z.1.val
      (sm t) [z.2.val] R)
    (hdom : forall r, r ∈ replay.advantageTerminal.frozen ->
      r.serverTime <= t)
    (hcheck : pre = [] ∨ exists S,
      (forall r, r ∈ pre -> r.serverTime <= S) ∧ S <= t ∧
      (getTailFamilyReserve e (grayTailBranch q L a e) A n z.1.val
        (sm S) [z.2.val]).isNone)
    (hpost : forall r, r ∈ post -> ¬ GrayTailRoundHasSon r.toV1 z.1 z.2) :
    GrayChargedSonReserveDataV2 replay z t R pre.length := by
  classical
  have hprojSplit : frozenV1OfV2 replay.advantageTerminal =
      pre.map GrayTailRoundV2.toV1 ++ p.toV1 ::
        post.map GrayTailRoundV2.toV1 := by
    rw [frozenV1OfV2, hsplit]
    simp
  have hpostProj : forall r, r ∈ post.map GrayTailRoundV2.toV1 ->
      ¬ GrayTailRoundHasSon r z.1 z.2 := by
    intro r hr
    obtain ⟨r2, hr2, rfl⟩ := List.mem_map.mp hr
    exact hpost r2 hr2
  have hcheckProj : pre.map GrayTailRoundV2.toV1 = [] ∨ exists S,
      (forall r, r ∈ pre.map GrayTailRoundV2.toV1 -> r.serverTime <= S) ∧
      S <= t ∧
      (getTailFamilyReserve e (grayTailBranch q L a e) A n z.1.val
        (sm S) [z.2.val]).isNone := by
    rcases hcheck with hempty | ⟨S, hbound, hSt, hnone⟩
    · left
      rw [hempty]
      rfl
    · refine Or.inr ⟨S, ?_, hSt, hnone⟩
      intro r hr
      obtain ⟨r2, hr2, rfl⟩ := List.mem_map.mp hr
      exact hbound r2 hr2
  refine ⟨hR, hdom, ⟨pre.map GrayTailRoundV2.toV1, p.toV1,
    post.map GrayTailRoundV2.toV1, hprojSplit, by simp, hson,
    hpostProj⟩, ?_⟩
  intro kk j hcond d hd
  by_cases hslot :
      ((replay.advantageTerminal.frozen[kk.val]).slots.get j).1 = z.1 ∧
        ((replay.advantageTerminal.frozen[kk.val]).slots.get j).2.1 = z.2
  · -- the cell sits at the son's own slot: the round is not the owner
    have hkk : kk.val ≠ pre.length := by
      rcases hcond with h | h | h
      · exact h
      · exact absurd hslot.1 h
      · exact absurd hslot.2 h
    have hlenEq : replay.advantageTerminal.frozen.length =
        pre.length + (post.length + 1) := by
      rw [hsplit]
      simp [List.length_append]
    have hlen : kk.val < pre.length + (post.length + 1) :=
      hlenEq ▸ kk.isLt
    rcases Nat.lt_or_ge kk.val pre.length with hlt | hge
    · -- an earlier own-slot round: fresh by the checkpoint
      have hget : replay.advantageTerminal.frozen[kk.val] = pre[kk.val] :=
        (List.getElem_of_eq hsplit kk.isLt).trans
          (List.getElem_append_left hlt)
      have hmem : replay.advantageTerminal.frozen[kk.val] ∈ pre := by
        rw [hget]
        exact List.getElem_mem hlt
      exact grayTail_prefix_alloc_fresh_of_checkpoint (L := L) hsm hR
        hcheckProj _ (List.mem_map_of_mem hmem) j hslot.1 hslot.2 d hd
    · -- a later own-slot round would contradict the exit's post clause
      have hgt : pre.length < kk.val := lt_of_le_of_ne hge (Ne.symm hkk)
      obtain ⟨m, hm, hmlt⟩ :
          exists m, kk.val = pre.length + (m + 1) ∧ m < post.length :=
        ⟨kk.val - pre.length - 1, by omega, by omega⟩
      have hget : replay.advantageTerminal.frozen[kk.val] = post[m] := by
        refine (List.getElem_of_eq hsplit kk.isLt).trans ?_
        rw [List.getElem_append_right (by omega)]
        simp only [hm, Nat.add_sub_cancel_left, List.getElem_cons_succ]
      have hmem : replay.advantageTerminal.frozen[kk.val] ∈ post := by
        rw [hget]
        exact List.getElem_mem hmlt
      exact absurd
        ⟨(replay.advantageTerminal.frozen[kk.val]).slots.get j,
          List.get_mem _ j, hslot.1, hslot.2⟩
        (hpost _ hmem)
  · -- a foreign slot: spatial separation transported to the reserve time
    have hne :
        ((replay.advantageTerminal.frozen[kk.val]).slots.get j).1 ≠ z.1 ∨
        ((replay.advantageTerminal.frozen[kk.val]).slots.get j).2.1 ≠
          z.2 := by
      by_cases h1 :
          ((replay.advantageTerminal.frozen[kk.val]).slots.get j).1 = z.1
      · exact Or.inr fun h2 => hslot ⟨h1, h2⟩
      · exact Or.inl h1
    exact grayTail_reserve_fresh_of_slot_ne_before (L := L) hsm hR
      (replay.advantageTerminal.frozen[kk.val]).toV1 j
      (hdom _ (List.getElem_mem kk.isLt)) hne hd

/-- The advantage terminal is the block tail state one past the exit. -/
lemma grayChargedReplayV2_advantageTerminal_eq_stateAt
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T) :
    replay.advantageTerminal =
      grayChargedBlockTailStateAtV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm (replay.advantageExitTime + 1) := by
  rw [replay.advantageTerminal_eq,
    grayChargedRunStateV2_core_eq_tailStateAt q L a e sigma A sm
      replay.advantageExitTime replay.advantage_before,
    ← grayChargedBlockTailStateAtV2_succ]

/-- **Exact V2 chronology at the replayed advantage exit**: every inactive
source coordinate leaves through a raised threshold or a persistent
reserve. -/
theorem grayChargedReplayV2_terminal_detailed_resolution
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    (i : Fin n) (c : Fin (grayTailBranch q L a e))
    (hused : c.val < grayChargedSourceCount a e)
    (hinactive : ¬ GrayTailHasSon replay.advantageTerminal.slots i c) :
    ((grayChargedThreshold q e <
          grayTailFrozenSonBase
            (frozenV1OfV2 replay.advantageTerminal) i c) ∧
        GrayTailThresholdExit e A sm
          (frozenV1OfV2 replay.advantageTerminal) i c) ∨
      (GrayTailPersistentReserveExit e A sm
          (frozenV1OfV2 replay.advantageTerminal) i c ∧
        grayTailFrozenSonBase
            (frozenV1OfV2 replay.advantageTerminal) i c <=
          grayChargedThreshold q e) := by
  have heq := grayChargedReplayV2_advantageTerminal_eq_stateAt replay
  have hres := grayChargedBlockTail_terminal_detailed_resolution
    (q := q) (L := L) (a := a) (e := e) (n := n)
    (t := replay.advantageExitTime + 1) (sigma := sigma) (A := A)
    (sm := sm) i c hused
    (by rw [← heq]; exact hinactive)
  rw [← heq] at hres
  simpa [grayChargedThreshold] using hres

/-- The chronology of one resolved source `z` of the replay: its son index is a source index, it
holds no slot at the advantage terminal, it is resolved either by crossing `grayChargedThreshold
q e` with a threshold exit or by a persistent reserve exit below that threshold, and it has an
owner index at which its owner split occurs. -/
structure GrayChargedResolvedSourceChronologyV2
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    (z : Fin n × Fin (grayTailBranch q L a e)) : Type where
  source_lt : z.2.val < grayChargedSourceCount a e
  inactive : ¬ GrayTailHasSon replay.advantageTerminal.slots z.1 z.2
  resolution :
    ((grayChargedThreshold q e <
          grayTailFrozenSonBase
            (frozenV1OfV2 replay.advantageTerminal) z.1 z.2) ∧
        GrayTailThresholdExit e A sm
          (frozenV1OfV2 replay.advantageTerminal) z.1 z.2) ∨
      (GrayTailPersistentReserveExit e A sm
          (frozenV1OfV2 replay.advantageTerminal) z.1 z.2 ∧
        grayTailFrozenSonBase
            (frozenV1OfV2 replay.advantageTerminal) z.1 z.2 <=
          grayChargedThreshold q e)
  ownerIndex : Nat
  ownerSplit : GrayTailOwnerSplitAt
    (frozenV1OfV2 replay.advantageTerminal) z.1 z.2 ownerIndex

/-- **Every resolved source of the V2 replay carries an exact chronology.** -/
theorem grayChargedReplayV2_resolved_source_chronology
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    (z : Fin n × Fin (grayTailBranch q L a e))
    (hz : z ∈ grayChargedReplayV2RaisedSources replay ∪
      grayChargedReplayV2ServerResolvedSources replay) :
    Nonempty (GrayChargedResolvedSourceChronologyV2 replay z) := by
  classical
  have hz' : z ∈ grayChargedRaisedSources
      (n := n) (b := grayTailBranch q L a e)
      (grayChargedSourceCount a e) (grayChargedThreshold q e)
      (frozenV1OfV2 replay.advantageTerminal) ∪
      grayChargedServerResolvedSources e (grayChargedSourceCount a e)
        (grayChargedThreshold q e) A
        (frozenV1OfV2 replay.advantageTerminal)
        (sm replay.advantageDoneTime) := hz
  have hsource := (mem_grayChargedResolvedSources_union z).mp hz'
  have hterm := grayChargedReplayV2_advantageTerminal_eq_stateAt replay
  have hbound := (grayChargedBlockTailCertifiedV2_stateAt (n := n)
    (b := grayTailBranch q L a e)
    q L a e sigma A sm (replay.advantageExitTime + 1)).frozen_bound.1
  have hround_lt : replay.advantageTerminal.frozen.length <
      grayTailBranch q L a e := by
    rw [hterm]
    have := grayChargedAdvantageRoundCount_lt_branch q L a e
    omega
  have hlen_le : replay.advantageTerminal.frozen.length <=
      grayChargedAdvantageRoundCount q := by
    rw [hterm]
    exact hbound
  have hG := grayAdvBlockGrandsons_ne_nil_of_le
    (q := q) (L := L) (a := a) (e := e) hlen_le
  have hslots := grayChargedReplayV2_terminal_accept replay
  have hinactive :
      ¬ GrayTailHasSon replay.advantageTerminal.slots z.1 z.2 := by
    intro hson
    rw [hslots] at hson
    have hson2 := (grayBlockHasSon_iff hround_lt hG z.1 z.2).mp hson
    have hunresolved :=
      (grayTailHasSon_next_iff hround_lt z.1 z.2).mp hson2
    exact hsource.2 ⟨hunresolved.2.1, hunresolved.2.2⟩
  have hresolution := grayChargedReplayV2_terminal_detailed_resolution
    replay z.1 z.2 hsource.1 hinactive
  have hexit : GrayTailThresholdExit e A sm
      (frozenV1OfV2 replay.advantageTerminal) z.1 z.2 := by
    rcases hresolution with h | h
    · exact h.2
    · exact h.1.toThresholdExit
  obtain ⟨k, hk⟩ := hexit.ownerSplitAt
  exact ⟨{
    source_lt := hsource.1
    inactive := hinactive
    resolution := hresolution
    ownerIndex := k
    ownerSplit := hk }⟩

/-- Every advantage-terminal round precedes the exit time. -/
lemma grayChargedReplayV2_terminal_frozen_serverTime_le
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    {r : GrayTailRoundV2 n (grayTailBranch q L a e)}
    (hr : r ∈ replay.advantageTerminal.frozen) :
    r.serverTime <= replay.advantageExitTime := by
  have hr' : r ∈ (grayChargedRunStateV2 (n := n)
      (b := grayTailBranch q L a e)
      q L a e sigma A sm (replay.advantageExitTime + 1)).core.frozen := by
    rw [grayChargedReplayV2_advantageTerminal_frozen_eq replay]
    exact hr
  have hvalid := (grayChargedRunStateV2_coreCertified q L a e sigma A sm
    (replay.advantageExitTime + 1)).round_valid r hr'
  omega

/-- **Day's Lemma 9 for the V2 replay** (blueprint D2): every resolved
source son carries a complete reserve freshness datum — a reserve at a time
dominating every advantage round, its owner position, and incomparability
with everything displayed outside the owner round's own slot. -/
theorem grayChargedReplayV2_son_reserve_data
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hnotpos : ¬ GrayChargedPositiveV2 q L a e n sigma A sm)
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    (z : Fin n × Fin (grayTailBranch q L a e))
    (hz : z ∈ grayChargedReplayV2RaisedSources replay ∪
      grayChargedReplayV2ServerResolvedSources replay) :
    exists t R k, GrayChargedSonReserveDataV2 replay z t R k := by
  classical
  obtain ⟨chron⟩ := grayChargedReplayV2_resolved_source_chronology replay z hz
  rcases chron.resolution with ⟨hbase, hexit⟩ | ⟨hexit, -⟩
  · -- threshold exit: the raised display must be served; the served
    -- cylinder yields a reserve at a pushed-late time
    obtain ⟨pre, p, post, hsplit, hson, hcheck, hpost⟩ := hexit
    rw [frozenV1OfV2] at hsplit
    obtain ⟨pre2, p2, post2, hsplit2, hpreM, hpM, hpostM⟩ :=
      grayChargedV2_map_split hsplit
    have hzr : z ∈ grayChargedReplayV2RaisedSources replay :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ z, chron.source_lt, hbase⟩
    have hreq := grayChargedReplayV2_raised_display_eq replay le_rfl hzr
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
        (getFamilyAlloc (sm (max u replay.advantageExitTime)) z.1.val
          [z.2.val]) (dyadicScale e) :=
      serves_mono_time (hsm.1 z.1.val z.1.isLt)
        (le_max_left u replay.advantageExitTime) hu
    obtain ⟨R, hR⟩ := exists_tailFamilyReserve_of_serves hsm z.1.isLt
      hnode hserveLate
    have hdom : forall r, r ∈ replay.advantageTerminal.frozen ->
        r.serverTime <= max u replay.advantageExitTime :=
      fun r hr => le_trans
        (grayChargedReplayV2_terminal_frozen_serverTime_le replay hr)
        (le_max_right u replay.advantageExitTime)
    have hp2mem : p2 ∈ replay.advantageTerminal.frozen := by
      rw [hsplit2]
      exact List.mem_append_right _ List.mem_cons_self
    have hcheck2 : pre2 = [] ∨ exists S,
        (forall r, r ∈ pre2 -> r.serverTime <= S) ∧
        S <= max u replay.advantageExitTime ∧
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
        · have hpT : p.serverTime <= max u replay.advantageExitTime := by
            rw [← hpM]
            exact hdom p2 hp2mem
          omega
    have hpost2 : forall r, r ∈ post2 ->
        ¬ GrayTailRoundHasSon r.toV1 z.1 z.2 := by
      intro r hr
      refine hpost _ ?_
      rw [← hpostM]
      exact List.mem_map_of_mem hr
    exact ⟨max u replay.advantageExitTime, R, pre2.length,
      grayChargedSonReserveDataV2_of_split hsm replay hsplit2
        (by rw [hpM]; exact hson) hR hdom hcheck2 hpost2⟩
  · -- persistent reserve exit: the recorded reserve already dominates
    -- every advantage round
    obtain ⟨pre, p, post, reserveTime, R, hsplit, hson, hR, hmax, hcheck,
      hpost⟩ := hexit
    rw [frozenV1OfV2] at hsplit
    obtain ⟨pre2, p2, post2, hsplit2, hpreM, hpM, hpostM⟩ :=
      grayChargedV2_map_split hsplit
    have hdom : forall r, r ∈ replay.advantageTerminal.frozen ->
        r.serverTime <= reserveTime := by
      intro r hr
      have := hmax r.toV1 (by
        rw [frozenV1OfV2]
        exact List.mem_map_of_mem hr)
      exact this
    have hp2mem : p2 ∈ replay.advantageTerminal.frozen := by
      rw [hsplit2]
      exact List.mem_append_right _ List.mem_cons_self
    have hcheck2 : pre2 = [] ∨ exists S,
        (forall r, r ∈ pre2 -> r.serverTime <= S) ∧ S <= reserveTime ∧
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
        · have hpT : p.serverTime <= reserveTime := by
            rw [← hpM]
            exact hdom p2 hp2mem
          omega
    have hpost2 : forall r, r ∈ post2 ->
        ¬ GrayTailRoundHasSon r.toV1 z.1 z.2 := by
      intro r hr
      refine hpost _ ?_
      rw [← hpostM]
      exact List.mem_map_of_mem hr
    exact ⟨reserveTime, R, pre2.length,
      grayChargedSonReserveDataV2_of_split hsm replay hsplit2
        (by rw [hpM]; exact hson) hR hdom hcheck2 hpost2⟩

/-- **Cell-level pre-owner freshness**: a designated cell of a frozen
advantage round is prefix-incomparable with a reserve that is incomparable
with every allocation of the cell's slot. -/
theorem grayChargedV2_cell_reserve_incomparable_of_slot_fresh
    {q L a e n t : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hae : a <= e)
    (p : GrayTailRoundV2 n (grayTailBranch q L a e))
    (hp : p ∈ (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).core.frozen)
    {z : Nat × BitString}
    (hz : z ∈ grayChargedRoundLocalChargeV2 hae p hp)
    {R : BitString} (hRe : R.length = e)
    (hadv : grayCallDepth q e <= p.blockAnchor)
    (hfreshS : forall d, d ∈ getFamilyAlloc
        (grayTailLocalServerMove (p.blockAnchor + L) p.slots
          (sm p.serverTime)) z.1 [] ->
      ¬ (R <+: d ∨ d <+: R)) :
    ¬ (z.2 <+: R ∨ R <+: z.2) := by
  have hcells := grayChargedRoundLocalChargeV2_cells hae p hp z hz
  refine grayChargedV2_trace_incomparable_of_alloc_fresh hcells.2 hfreshS
    ?_ (Nat.le_add_right _ _)
  have := grayChargedV2_lt_callDepth q e
  omega

end Kolmogorov
