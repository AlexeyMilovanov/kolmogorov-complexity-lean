/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.ArchiveMonotonicity
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.CommonGameInvariantBase

/-!
# Preservation of the true-marker game during a tick

This module proves that a true-marker phase keeps its candidate, counter game, and buffer
invariant through the next tick's preprocessing and internal closure. Cancellation archives
are monotone, so the capacity bound and opponent-exhaustion bound rule out loss of the phase
before closure. During closure, legal play and the absence of allocation failure ensure survival,
while each internal action preserves the candidate and game code of every surviving phase.

`CommonGame` combines these results with preservation under higher-level services to show that
all true-marker phases play the same game (blueprint node `constr:opponent`).
`EventuallyBounded` also uses the action-level preservation of candidate and game code
to track strategy moves.
-/

namespace Kolmogorov.Milovanov

/-- Immediate payoff processing either preserves the phase's candidate and game code
or records that same phase's saturation in the permanent cancellation archive. -/
private lemma activeAt_or_saturated_fighterFulfillReady
    (P : FighterParams) (d l : ℕ) (state : FighterState) (phase : FighterPhase)
    (hphase : state.activeAt d l = some phase) :
    (∃ live, (fighterFulfillReady P d l state).activeAt d l = some live ∧
      live.candidate = phase.candidate ∧ live.gameCode = phase.gameCode) ∨
    ∃ e ∈ (fighterFulfillReady P d l state).ended,
      e.1.level = l ∧ e.1.candidate = phase.candidate ∧ e.2.2.1 = .saturated := by
  let Good (s : FighterState) : Prop :=
    (∃ live, s.activeAt d l = some live ∧
      live.candidate = phase.candidate ∧ live.gameCode = phase.gameCode) ∨
    ∃ e ∈ s.ended,
      e.1.level = l ∧ e.1.candidate = phase.candidate ∧ e.2.2.1 = .saturated
  have hpay (q : Coordinate) (s : FighterState) (hs : Good s) :
      Good (fighterPayoff P d l q s) := by
    rcases hs with ⟨old, hold, hc, hg⟩ | ⟨e, he, hl, hc, hr⟩
    · have hrefl : Good s := Or.inl ⟨old, hold, hc, hg⟩
      have hlevel : old.level = l := beq_iff_eq.mp
        (List.find?_some (p := fun p : FighterPhase ↦ p.level == l) hold)
      simp only [fighterPayoff, hold]
      split
      · cases ha : fighterAllocate d l .payoff q.2 q.1 s with
        | mk next success =>
          simp only
          cases success with
          | false =>
            simp only [Bool.false_eq_true, ite_false]
            have halloc := ha
            simp only [fighterAllocate, hold] at halloc
            cases hf : (if q.2 = 0 then (none : Option BitString) else
                (fighterInputs d (q.2 - 1)).find? (fun p ↦
                  !s.allocated.any (fun a ↦ a.input == p))) with
            | none =>
              rw [hf] at halloc
              have hn := congrArg Prod.fst halloc
              change fighterCancel d l .saturated l { s with failed := true } = next at hn
              rw [← hn]
              right
              refine ⟨({ old with pending := [] }, s.tick, .saturated, l), ?_, hlevel, hc, rfl⟩
              simp only [fighterCancel, show
                ({ s with failed := true }).activeAt d l = some old from hold]
              exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
            | some input =>
              rw [hf] at halloc
              have hb := congrArg Prod.snd halloc
              change true = false at hb
              cases hb
          | true =>
            simp only [ite_true]
            have hn := activeAt_fighterAllocate_eq_of_success
              d l q.2 .payoff q.1 s next old hold ha
            left
            refine ⟨{ old with pending := old.pending.filter (fun r ↦ r != q) }, ?_, hc, hg⟩
            simp only [FighterState.activeAt, List.find?_map]
            change (next.activeAt d l).map (fun p ↦
              { p with pending := p.pending.filter (fun r ↦ r != q) }) = _
            rw [hn]
            rfl
      · exact hrefl
    · right
      refine ⟨e, ?_, hl, hc, hr⟩
      exact ended_subset_fighterPayoff P d l q s he
  have hfold (requests : List Coordinate) (s : FighterState) (hs : Good s) :
      Good (requests.foldl (fun s q ↦ fighterPayoff P d l q s) s) := by
    induction requests generalizing s with
    | nil => exact hs
    | cons q requests ih => exact ih _ (hpay q s hs)
  unfold fighterFulfillReady
  rw [hphase]
  exact hfold phase.pending state (Or.inl ⟨phase, hphase, rfl, rfl⟩)

/-- One opponent event either preserves the issuing candidate and game code or archives
that phase for saturation or opponent exhaustion. This is a local transition statement. -/
private lemma activeAt_or_ended_fighterOpponent
    (P : FighterParams) (d l : ℕ) (state : FighterState) (phase : FighterPhase)
    (hphase : state.activeAt d l = some phase) (event : ProgramEvent) :
    (∃ live, (fighterOpponent P d l event state).activeAt d l = some live ∧
      live.candidate = phase.candidate ∧ live.gameCode = phase.gameCode) ∨
    ∃ e ∈ (fighterOpponent P d l event state).ended,
      e.1.level = l ∧ e.1.candidate = phase.candidate ∧
        (e.2.2.1 = .saturated ∨ e.2.2.1 = .opponentExhausted) := by
  have hrefl : (∃ live, state.activeAt d l = some live ∧
      live.candidate = phase.candidate ∧ live.gameCode = phase.gameCode) ∨
      ∃ e ∈ state.ended, e.1.level = l ∧ e.1.candidate = phase.candidate ∧
        (e.2.2.1 = .saturated ∨ e.2.2.1 = .opponentExhausted) :=
    Or.inl ⟨phase, hphase, rfl, rfl⟩
  have hlevel : phase.level = l := beq_iff_eq.mp
    (List.find?_some (p := fun p : FighterPhase ↦ p.level == l) hphase)
  simp only [fighterOpponent, hphase]
  cases ht : fighterOpponentTuple d phase event with
  | none => exact hrefl
  | some qi =>
    rcases qi with ⟨q, index⟩
    dsimp only
    split
    · exact hrefl
    · split
      · right
        refine ⟨({ phase with pending := [] }, state.tick, .opponentExhausted, l),
          ?_, hlevel, rfl, Or.inr rfl⟩
        simp only [fighterCancel, hphase]
        exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
      · let inserted := phase.insertIndex d q index
        let next := { inserted with
          opponentRemaining := phase.opponentRemaining - 1
          buffer := (phase.game d).addCounters phase.buffer (phase.unitVector d q) }
        let funded := next.fundRequests d state.fulfilled
        have hput : (state.putPhase d funded).activeAt d l = some funded := by
          simp [FighterState.putPhase, FighterState.activeAt, funded, next, inserted,
            FighterPhase.fundRequests, FighterPhase.insertIndex, hlevel]
        rcases activeAt_or_saturated_fighterFulfillReady
            P d l (state.putPhase d funded) funded hput with
          ⟨live, hlive, hc, hg⟩ | ⟨e, he, hl, hc, hr⟩
        · exact Or.inl ⟨live, hlive, hc, hg⟩
        · exact Or.inr ⟨e, he, hl, hc, Or.inl hr⟩

/-- Splitting the actual sorted traversal at an already active level places its closure
before a finite suffix of services. In particular its pre-closure archive persists to the
completed tick. -/
private lemma ended_fighterBeforeClosure_subset_succ
    (P : FighterParams) (d l tick : ℕ) (hd : 1 ≤ d)
    (phase : FighterPhase) (hphase : (fighterState P d tick).activeAt d l = some phase) :
    (fighterBeforeClosure P d (tick + 1) l).ended ⊆
      (fighterState P d (tick + 1)).ended := by
  let current : FighterState :=
    { fighterState P d tick with tick := tick + 1, schedule := masterState P.B (tick + 1) }
  let event := eventAt P.B (tick + 1)
  let owner := event.bind (fun e ↦ fighterOwner d e.2.2.1.length)
  let levels := (current.active.map FighterPhase.level ++ owner.toList).eraseDups
  let traversal := levels.mergeSort (· ≤ ·)
  have hlevel : phase.level = l := beq_iff_eq.mp
    (List.find?_some (p := fun p : FighterPhase ↦ p.level == l) hphase)
  have hmem : l ∈ traversal := by
    simp only [traversal, List.mem_mergeSort, levels, List.mem_eraseDups, List.mem_append]
    left
    exact List.mem_map.mpr ⟨phase, List.mem_of_find?_eq_some hphase, hlevel⟩
  have hsorted : traversal.Pairwise (· < ·) := by
    have hle := List.pairwise_mergeSort' (· ≤ ·) levels
    have hne : traversal.Nodup := by
      rw [List.nodup_mergeSort]
      exact Kolmogorov.nodup_eraseDups_list _
    exact (hle.and hne).imp (fun h ↦ lt_of_le_of_ne h.1 h.2)
  have hsplit (xs : List ℕ) (hs : xs.Pairwise (· < ·)) (hm : l ∈ xs) :
      ∃ tail, xs = xs.takeWhile (· < l) ++ l :: tail := by
    induction xs with
    | nil => simp at hm
    | cons j xs ih =>
      by_cases hj : j = l
      · subst j
        exact ⟨xs, by simp⟩
      · have hm' : l ∈ xs := (List.mem_cons.mp hm).resolve_left (Ne.symm hj)
        have hlt : j < l := (List.pairwise_cons.mp hs).1 l hm'
        obtain ⟨tail, ht⟩ := ih (List.pairwise_cons.mp hs).2 hm'
        exact ⟨tail, by simpa [List.takeWhile_cons, hlt] using congrArg (List.cons j) ht⟩
  obtain ⟨tail, ht⟩ := hsplit traversal hsorted hmem
  have hfull : fighterState P d (tick + 1) =
      tail.foldl (fun s j ↦ fighterProcessLevel P d j event s)
        (fighterCloseLevel P d l (fighterBeforeClosure P d (tick + 1) l)) := by
    change fighter_actions P d (tick + 1) (fighterState P d tick) = _
    simp only [fighter_actions, Nat.ne_of_gt hd, ite_false]
    change traversal.foldl (fun s j ↦ fighterProcessLevel P d j event s) current = _
    rw [ht, List.foldl_append, List.foldl_cons]
    rfl
  have hfold (xs : List ℕ) (s : FighterState) :
      s.ended ⊆ (xs.foldl (fun s j ↦ fighterProcessLevel P d j event s) s).ended := by
    induction xs generalizing s with
    | nil => exact fun _ h ↦ h
    | cons j xs ih => exact fun _ h ↦ ih _ (ended_subset_fighterProcessLevel P d j event s h)
  intro e he
  rw [hfull]
  exact hfold tail _ (ended_subset_fighterClosure P d l _ _ he)

/-- After the marker tick, preprocessing at its level preserves the true-marker candidate
and game and leaves a phase satisfying the buffer invariant. -/
lemma true_marker_before_closure_invariant
    (P : FighterParams) (C cGap cRank d₀ d l : ℕ)
    (hfixed : FighterFixedConstants P C cGap cRank d₀)
    (hgood : GoodPadding P d₀ cRank cGap d) (hlate : LateAdmissibleOccurrence P d l)
    (hclosure : TrueMarkerClosureLegal P d l)
    (game : FiniteCounterGame)
    (tick : ℕ) (htick : markerTick P.B (levelScale l) ≤ tick)
    (phase : FighterPhase)
    (hphase : TrueMarkerPhaseAt P d l tick phase)
    (hphase_game : phase.game d = game) :
    ∃ next, (fighterBeforeClosure P d (tick + 1) l).activeAt d l = some next ∧
      next.candidate = markerCandidate P.B (levelScale l) ∧
      next.game d = game ∧ next.BufferInvariant d := by
  let start := fighterBeforeLevel P d (tick + 1) l
  let before := fighterBeforeClosure P d (tick + 1) l
  have hlong : ∀ e, eventAt P.B (tick + 1) = some e →
      levelScale l < e.2.2.1.length := by
    intro ⟨t, i, p, x⟩ he
    have ht : t = tick + 1 := (canonical_enumeration_spec_sound P.B he).1
    subst t
    exact length_gt_of_eventAt_of_markerTick_lt P.B (levelScale l)
      (tick + 1) (by omega) i p x he
  have hstart : start.activeAt d l = some phase := by
    dsimp only [start]
    have hprefix : fighterBeforeLevel P d (tick + 1) l =
        { fighterState P d tick with
          tick := tick + 1, schedule := masterState P.B (tick + 1) } := by
      let before := fighterState P d tick
      let current := { before with tick := tick + 1, schedule := masterState P.B (tick + 1) }
      have hcut : levelLower l ≤ levelScale l :=
        tower_le_tower (by omega)
      have hrange := fighterState_tick_and_requestRanges P d tick hgood.positive
      have hquiet : ∀ j < l, fighterLevelAction P d j current = none := by
        intro j hj
        refine fighterLevelAction_eq_none_of_advance P d j before (tick + 1) _ ?_
          (fighterLevelAction_fighterState_eq_none P d tick j)
        intro phase hphase q hq
        have hlevel : phase.level = j := beq_iff_eq.mp
          (List.find?_some (p := fun p : FighterPhase ↦ p.level == j) hphase)
        have hbound := (hrange.2 phase (List.mem_of_find?_eq_some hphase)).2 q hq
        have hupper := levelUpper_le_levelLower j l hj
        rw [hlevel] at hbound
        rw [show before.tick = tick from hrange.1]
        simpa only [Nat.add_sub_cancel] using
          fighterSafe_eq_pred_of_long_event P d (tick + 1)
            (levelScale l) hlong q (by omega)
      have hservice : ∀ j < l,
          fighterProcessLevel P d j (eventAt P.B (tick + 1)) current = current := by
        intro j hj
        apply fighterProcessLevel_eq_self_of_levelAction_eq_none P d j _ current
          (hquiet j hj)
        intro e he
        exact fighterOwner_ne_and_fighterOpponentTuple_eq_none_of_levelLower_lt d l j hj e
          (hcut.trans_lt (hlong e he))
      have hfold (levels : List ℕ) (hlevels : ∀ j ∈ levels, j < l) :
          levels.foldl (fun s j ↦ fighterProcessLevel P d j (eventAt P.B (tick + 1)) s)
            current = current := by
        induction levels with
        | nil => rfl
        | cons j levels ih =>
          rw [List.foldl_cons, hservice j (hlevels j (by simp))]
          exact ih (fun k hk ↦ hlevels k (List.mem_cons_of_mem j hk))
      unfold fighterBeforeLevel
      simp only [Nat.add_sub_cancel]
      apply hfold
      intro j hj
      have hdecide := List.mem_takeWhile_imp hj
      exact of_decide_eq_true hdecide
    rw [hprefix]
    exact hphase.2.2.2
  have hnostart (e : TimedEvent) (he : eventAt P.B (tick + 1) = some e) :
      ¬ (fighterOwner d e.2.2.1.length = some l ∧
        e.2.2.1.length ≤ levelScale l ∧ P.Admissible d l) := by
    have hlen := hlong e he
    omega
  have htrace :
      (∃ next, before.activeAt d l = some next ∧
        next.candidate = phase.candidate ∧ next.gameCode = phase.gameCode) ∨
      ∃ e ∈ before.ended, e.1.level = l ∧ e.1.candidate = phase.candidate ∧
        (e.2.2.1 = .saturated ∨ e.2.2.1 = .opponentExhausted) := by
    have hready := activeAt_or_saturated_fighterFulfillReady P d l start phase hstart
    cases he : eventAt P.B (tick + 1) with
    | none =>
      have hbefore : before = fighterFulfillReady P d l start := by
        simp only [before, fighterBeforeClosure, he]
        rfl
      rw [hbefore]
      rcases hready with hactive | ⟨e, he, hl, hc, hr⟩
      · exact Or.inl hactive
      · exact Or.inr ⟨e, he, hl, hc, Or.inl hr⟩
    | some event =>
      have hbefore : before = fighterOpponent P d l event.2.2
          (fighterFulfillReady P d l start) := by
        simp only [before, fighterBeforeClosure, he, hnostart event he, ite_false]
        rfl
      rw [hbefore]
      rcases hready with ⟨checked, hchecked, hc, hg⟩ | ⟨e, hemem, hl, hc, hr⟩
      · rcases activeAt_or_ended_fighterOpponent P d l
          (fighterFulfillReady P d l start) checked hchecked event.2.2 with
            ⟨next, hnext, hc', hg'⟩ | ⟨e, hemem, hl, hc', hr⟩
        · exact Or.inl ⟨next, hnext, hc'.trans hc, hg'.trans hg⟩
        · exact Or.inr ⟨e, hemem, hl, hc'.trans hc, hr⟩
      · exact Or.inr ⟨e, ended_subset_fighterOpponent P d l event.2.2 _ hemem,
          hl, hc, Or.inl hr⟩
  rcases htrace with ⟨next, hnext, hc, hg⟩ | ⟨e, he, hl, hc, hr⟩
  · have hcand : next.candidate = markerCandidate P.B (levelScale l) :=
      hc.trans hphase.2.2.1
    refine ⟨next, hnext, hcand, ?_, ?_⟩
    · change decodeCounterGame next.gameCode = game
      rw [hg]
      exact hphase_game
    · exact (hclosure (tick + 1) (by omega) 0 (Nat.zero_le _) next hnext hcand).1
  · have hemem := ended_fighterBeforeClosure_subset_succ P d l tick hgood.positive phase
      hphase.2.2.2 he
    rcases hr with hsat | hexhausted
    · exact (fighterState_ended_reason_ne_saturated P d (tick + 1)
        (hfixed.capacity d hgood.capacity_threshold hgood.even (tick + 1)) e hemem hsat).elim
    · have hnever := (trueMarker_started_and_neverEndsFor_opponentExhausted
        P C cGap cRank d₀ d l hfixed hgood hlate).2
      exact (hnever (tick + 1) e hemem hl (hc.trans hphase.2.2.1) hexhausted).elim

/-- A fuel allocation and its resulting payoff processing preserve the candidate and
game code of every surviving phase at the serviced level. -/
private lemma candidate_gameCode_of_activeAt_fighterFuelUnit
    (P : FighterParams) (d l : ℕ) (q : Coordinate) (s : FighterState) :
    ∀ live, (fighterFuelUnit P d l q s).activeAt d l = some live →
      ∃ old, s.activeAt d l = some old ∧
        live.candidate = old.candidate ∧ live.gameCode = old.gameCode := by
  let Keep (s t : FighterState) : Prop :=
    ∀ live, t.activeAt d l = some live →
      ∃ old, s.activeAt d l = some old ∧
        live.candidate = old.candidate ∧ live.gameCode = old.gameCode
  have hrefl (s : FighterState) : Keep s s :=
    fun live hlive ↦ ⟨live, hlive, rfl, rfl⟩
  have hfulfill (s : FighterState) : Keep s (fighterFulfillReady P d l s) := by
    intro live hlive
    obtain ⟨old, hold, pending, rfl⟩ :=
      pending_update_of_activeAt_fighterFulfillReady
        P d l s live hlive
    exact ⟨old, hold, rfl, rfl⟩
  change Keep s (fighterFuelUnit P d l q s)
  unfold fighterFuelUnit
  split
  · exact hrefl s
  · rename_i p hp
    split
    · have hlevel : p.level = l :=
        beq_iff_eq.mp (List.find?_some (p := fun p : FighterPhase ↦ p.level == l) hp)
      let charged := { p with controlledRemaining := p.controlledRemaining - 1 }
      let index := fighterFreshString d
        (p.indices[(p.game d).coordinates.idxOf q]?.getD [])
      let output := pairCode (triple q.1 (q.2 - d) p.candidate.1) index
      have ha :=
        activeAt_fighterAllocate
          d l (s.putPhase d charged) .fuel (levelUpper l + d) output
      change Keep s
        (match fighterAllocate d l .fuel (levelUpper l + d) output (s.putPhase d charged) with
        | (next, success) => if success then
            fighterFulfillReady P d l (next.putPhase d
              ((charged.insertIndex d q index).fundRequests d next.fulfilled)) else next)
      cases he : fighterAllocate d l .fuel (levelUpper l + d) output (s.putPhase d charged) with
      | mk next success =>
        rw [he] at ha
        cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true] at ha ⊢
        · intro live hlive
          rw [ha] at hlive
          contradiction
        · intro live hlive
          obtain ⟨old, hold, hc, hg⟩ := hfulfill _ live hlive
          have hput : (next.putPhase d
              ((charged.insertIndex d q index).fundRequests d next.fulfilled)).activeAt d l =
              some ((charged.insertIndex d q index).fundRequests d next.fulfilled) := by
            simp [FighterState.putPhase, FighterState.activeAt, FighterPhase.fundRequests,
              FighterPhase.insertIndex, charged, hlevel]
          rw [hput] at hold
          cases hold
          exact ⟨p, hp, hc, hg⟩
    · exact hrefl s

private lemma candidate_gameCode_of_activeAt_fighterDummy
    (d l : ℕ) (s : FighterState) :
    ∀ live, (fighterDummy d l s).activeAt d l = some live →
      ∃ old, s.activeAt d l = some old ∧
        live.candidate = old.candidate ∧ live.gameCode = old.gameCode := by
  let Keep (s t : FighterState) : Prop :=
    ∀ live, t.activeAt d l = some live →
      ∃ old, s.activeAt d l = some old ∧
        live.candidate = old.candidate ∧ live.gameCode = old.gameCode
  have hrefl (s : FighterState) : Keep s s :=
    fun live hlive ↦ ⟨live, hlive, rfl, rfl⟩
  change Keep s (fighterDummy d l s)
  unfold fighterDummy
  split
  · exact hrefl s
  · rename_i p hp
    have hlevel : p.level = l :=
      beq_iff_eq.mp (List.find?_some (p := fun p : FighterPhase ↦ p.level == l) hp)
    split
    · exact hrefl s
    · rename_i output hout
      split
      · exact hrefl s
      · have ha :=
          activeAt_fighterAllocate
            d l s .dummy (levelInput d l) output
        cases he : fighterAllocate d l .dummy (levelInput d l) output s with
        | mk next success =>
          rw [he] at ha
          cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true] at ha ⊢
          · intro live hlive
            rw [ha] at hlive
            contradiction
          · intro live hlive
            have hput : (next.putPhase d
                { p with dummyIssued := true }).activeAt d l =
                some { p with dummyIssued := true } := by
              simp [FighterState.putPhase, FighterState.activeAt, hlevel]
            rw [hput] at hlive
            cases hlive
            exact ⟨p, hp, rfl, rfl⟩

/-- Every phase surviving an internal action has the same candidate and game code as
an active phase at that level before the action. -/
lemma candidate_gameCode_of_activeAt_fighterLevelAction
    (P : FighterParams) (d l : ℕ) (state next : FighterState)
    (haction : fighterLevelAction P d l state = some next) :
    ∀ live, next.activeAt d l = some live →
      ∃ old, state.activeAt d l = some old ∧
        live.candidate = old.candidate ∧ live.gameCode = old.gameCode := by
  let Keep (s t : FighterState) : Prop :=
    ∀ live, t.activeAt d l = some live →
      ∃ old, s.activeAt d l = some old ∧
        live.candidate = old.candidate ∧ live.gameCode = old.gameCode
  have hrefl (s : FighterState) : Keep s s :=
    fun live hlive ↦ ⟨live, hlive, rfl, rfl⟩
  have htrans {s t u : FighterState} (hst : Keep s t) (htu : Keep t u) : Keep s u := by
    intro live hlive
    obtain ⟨mid, hmid, hc, hg⟩ := htu live hlive
    obtain ⟨old, hold, hc', hg'⟩ := hst mid hmid
    exact ⟨old, hold, hc.trans hc', hg.trans hg'⟩
  have hfold {α : Type} (f : α → FighterState → FighterState)
      (hf : ∀ a s, Keep s (f a s)) (xs : List α) (s : FighterState) :
      Keep s (xs.foldl (fun s a ↦ f a s) s) := by
    induction xs generalizing s with
    | nil => exact hrefl s
    | cons a xs ih => exact htrans (hf a s) (ih _)
  have hpay (q : Coordinate) (s : FighterState) : Keep s (fighterPayoff P d l q s) := by
    intro live hlive
    obtain ⟨old, hold, pending, rfl⟩ :=
      pending_update_of_activeAt_fighterPayoff
        P d l q s live hlive
    exact ⟨old, hold, rfl, rfl⟩
  have hunits (q : Coordinate) (count : ℕ) (s : FighterState) :
      Keep s (fighterFuelUnits P d l q count s) := by
    induction count generalizing s with
    | zero => exact hrefl s
    | succ count ih =>
      exact htrans (candidate_gameCode_of_activeAt_fighterFuelUnit P d l q s) (ih _)
  have hflush (s next : FighterState) (h : fighterFlushBuffer d l s = some next) :
      Keep s next := by
    cases hp : s.activeAt d l with
    | none => simp [fighterFlushBuffer, hp] at h
    | some p =>
      simp only [fighterFlushBuffer, hp, bind, Option.bind_some] at h
      split at h
      · cases h
        intro live hlive
        have hlevel : p.level = l :=
          beq_iff_eq.mp (List.find?_some (p := fun p : FighterPhase ↦ p.level == l) hp)
        have hput : (s.putPhase d { p with
            officialCode := ((p.game d).afterMove (p.official d) p.buffer).encode
            buffer := List.replicate (p.game d).coordinates.length 0 }).activeAt d l =
            some { p with
              officialCode := ((p.game d).afterMove (p.official d) p.buffer).encode
              buffer := List.replicate (p.game d).coordinates.length 0 } := by
          simp [FighterState.putPhase, FighterState.activeAt, hlevel]
        rw [hput] at hlive
        cases hlive
        exact ⟨p, hp, rfl, rfl⟩
      · contradiction
  have hstrategy (s next : FighterState) (h : fighterStrategyMove P d l s = some next) :
      Keep s next := by
    cases hp : s.activeAt d l with
    | none => simp [fighterStrategyMove, hp] at h
    | some p =>
      simp only [fighterStrategyMove, hp, bind, Option.bind_some] at h
      split at h
      · cases hm : (p.game d).strategy (p.official d) with
        | none => simp [hm] at h
        | some move =>
          simp only [hm, Option.bind_some] at h
          split at h
          · let middle := (p.game d).coordinates.zipIdx.foldl (fun s (q, i) ↦
              fighterFuelUnits P d l q (move[i]?.getD 0) s) s
            have hmiddle : Keep s middle :=
              hfold (fun (qi : Coordinate × ℕ) s ↦
                  fighterFuelUnits P d l qi.1 (move[qi.2]?.getD 0) s)
                (fun qi s ↦ hunits qi.1 (move[qi.2]?.getD 0) s) _ s
            change (match middle.activeAt d l with
              | none => some middle
              | some live => some (middle.putPhase d
                  { live with officialCode :=
                      ((p.game d).afterMove (p.official d) move).encode })) =
                some next at h
            cases hlive : middle.activeAt d l with
            | none =>
              simp only [hlive, Option.some.injEq] at h
              subst next
              exact hmiddle
            | some live =>
              simp only [hlive, Option.some.injEq] at h
              subst next
              intro final hfinal
              have hlevel : live.level = l :=
                beq_iff_eq.mp (List.find?_some (p := fun p : FighterPhase ↦ p.level == l) hlive)
              have hput : (middle.putPhase d
                  { live with officialCode :=
                      ((p.game d).afterMove (p.official d) move).encode }).activeAt d l =
                  some { live with officialCode :=
                    ((p.game d).afterMove (p.official d) move).encode } := by
                simp [FighterState.putPhase, FighterState.activeAt, hlevel]
              rw [hput] at hfinal
              cases hfinal
              exact hmiddle live hlive
          · contradiction
      · contradiction
  change Keep state next
  unfold fighterLevelAction at haction
  cases hp : state.activeAt d l with
  | none => simp [hp] at haction
  | some p =>
    simp only [hp, bind, Option.bind_some] at haction
    split at haction
    · cases haction
      exact candidate_gameCode_of_activeAt_fighterDummy d l state
    · split at haction
      · cases haction
        exact hpay _ state
      · cases hf : fighterFlushBuffer d l state with
        | some flushed =>
          simp only [hf, Option.some.injEq] at haction
          subst next
          exact hflush state flushed hf
        | none =>
          simp only [hf] at haction
          exact hstrategy state next haction

/-- A dummy or payoff allocation preserves an active phase at its level whenever the
resulting state has not failed. -/
private lemma activeAt_allocations_of_not_failed
    (P : FighterParams) (d l : ℕ) (state : FighterState) (phase : FighterPhase)
    (hphase : state.activeAt d l = some phase) :
    ((fighterDummy d l state).failed = false →
      ∃ live, (fighterDummy d l state).activeAt d l = some live) ∧
    (∀ q, (fighterPayoff P d l q state).failed = false →
      ∃ live, (fighterPayoff P d l q state).activeAt d l = some live) := by
  have halloc (kind : DirectiveKind) (target : ℕ) (output : BitString)
      (next : FighterState) (success : Bool)
      (he : fighterAllocate d l kind target output state = (next, success))
      (hfailed : next.failed = false) : next.activeAt d l = some phase := by
    have hs : success = true := by
      simp only [fighterAllocate, hphase] at he
      split at he
      · have hf : (fighterCancel d l .saturated l { state with failed := true }).failed = true := by
          unfold fighterCancel
          split <;> rfl
        have hn := congrArg (fun r : FighterState × Bool ↦ r.1.failed) he
        simp only at hn
        rw [hf, hfailed] at hn
        contradiction
      · exact (congrArg Prod.snd he).symm
    subst success
    exact activeAt_fighterAllocate_eq_of_success
      d l target kind output state next phase hphase he
  constructor
  · simp only [fighterDummy, hphase]
    split
    · exact fun _ ↦ ⟨phase, hphase⟩
    · rename_i output hout
      split
      · exact fun _ ↦ ⟨phase, hphase⟩
      · cases he : fighterAllocate d l .dummy (levelInput d l) output state with
        | mk next success =>
          cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
          · intro hf
            exact ⟨phase, halloc .dummy _ output next false he hf⟩
          · intro hf
            have hlevel : phase.level = l :=
              beq_iff_eq.mp (List.find?_some (p := fun p : FighterPhase ↦ p.level == l) hphase)
            exact ⟨{ phase with dummyIssued := true },
              by simp [FighterState.putPhase, FighterState.activeAt, hlevel]⟩
  · intro q
    simp only [fighterPayoff, hphase]
    split
    · cases he : fighterAllocate d l .payoff q.2 q.1 state with
      | mk next success =>
        cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
        · intro hf
          exact ⟨phase, halloc .payoff _ q.1 next false he hf⟩
        · intro hf
          have hn := halloc .payoff _ q.1 next true he hf
          refine ⟨{ phase with pending := phase.pending.filter (fun r ↦ r != q) }, ?_⟩
          simp only [FighterState.activeAt, List.find?_map]
          change (next.activeAt d l).map (fun p ↦
            { p with pending := p.pending.filter (fun r ↦ r != q) }) = _
          rw [hn]
          rfl
    · exact fun _ ↦ ⟨phase, hphase⟩

/-- A closure with one more unit of fuel performs an action after its preceding prefix,
or leaves the state unchanged if that prefix has finished. -/
lemma fighterClosure_succ_eq_levelAction
    (P : FighterParams) (d l step : ℕ) (state : FighterState) :
    fighterClosure P d l (step + 1) state =
      (fighterLevelAction P d l (fighterClosure P d l step state)).getD
        (fighterClosure P d l step state) := by
  induction step generalizing state with
  | zero =>
    cases ha : fighterLevelAction P d l state <;> simp [fighterClosure, ha]
  | succ step ih =>
    cases ha : fighterLevelAction P d l state with
    | none => simp [fighterClosure, ha]
    | some next => simpa only [fighterClosure, ha] using ih next

/-- Internal closure preserves the true-marker candidate and game and leaves a phase
satisfying the buffer invariant. -/
lemma true_marker_close_level_invariant
    (P : FighterParams) (C cGap cRank d₀ d l : ℕ)
    (hfixed : FighterFixedConstants P C cGap cRank d₀)
    (hgood : GoodPadding P d₀ cRank cGap d)
    (hclosure : TrueMarkerClosureLegal P d l)
    (game : FiniteCounterGame)
    (tick : ℕ) (htick : markerTick P.B (levelScale l) ≤ tick)
    (beforePhase : FighterPhase)
    (hbefore : (fighterBeforeClosure P d (tick + 1) l).activeAt d l = some beforePhase)
    (hcand : beforePhase.candidate = markerCandidate P.B (levelScale l))
    (hgame : beforePhase.game d = game) :
    ∃ next,
      (fighterCloseLevel P d l (fighterBeforeClosure P d (tick + 1) l)).activeAt d l = some next ∧
      next.candidate = markerCandidate P.B (levelScale l) ∧
      next.game d = game ∧ next.BufferInvariant d := by
  let fuel := fighterClosureFuel d l (fighterBeforeClosure P d (tick + 1) l)
  have hinvariant : ∀ step, step ≤ fuel →
      ∃ next, (fighterClosureAt P d (tick + 1) l step).activeAt d l = some next ∧
        next.candidate = markerCandidate P.B (levelScale l) ∧ next.game d = game := by
    intro step
    induction step with
    | zero => exact fun _ ↦ ⟨beforePhase, hbefore, hcand, hgame⟩
    | succ step ih =>
      intro hstep
      obtain ⟨phase, hphase, hcand', hgame'⟩ := ih (by omega)
      have heq : fighterClosureAt P d (tick + 1) l (step + 1) =
          (fighterLevelAction P d l (fighterClosureAt P d (tick + 1) l step)).getD
            (fighterClosureAt P d (tick + 1) l step) :=
        fighterClosure_succ_eq_levelAction
          P d l step _
      rw [heq]
      cases ha : fighterLevelAction P d l (fighterClosureAt P d (tick + 1) l step) with
      | none => exact ⟨phase, hphase, hcand', hgame'⟩
      | some next =>
        let state := fighterClosureAt P d (tick + 1) l step
        change fighterLevelAction P d l state = some next at ha
        change state.activeAt d l = some phase at hphase
        have hservice : (fighterCloseLevel P d l state).failed = false :=
          fighterCloseLevel_closureAt_failed_eq_false
            P d l (tick + 1) step (Nat.ne_of_gt hgood.positive) (Nat.zero_lt_succ tick)
            (hfixed.capacity d hgood.capacity_threshold hgood.even (tick + 1)) phase hphase
        have hfailed : next.failed = false := by
          have hpos : 0 < fighterClosureFuel d l state := by
            simp [fighterClosureFuel, hphase]
          obtain ⟨fuel, hfuel⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
          have heq : fighterCloseLevel P d l state = fighterClosure P d l fuel next := by
            simp only [fighterCloseLevel, hfuel, fighterClosure, ha]
          by_contra h
          have hf :=
            fighter_failed_persists P d
              |>.2.1 l fuel next (Bool.eq_true_of_ne_false h)
          rw [← heq, hservice] at hf
          contradiction
        have hlegal := hclosure (tick + 1) (by omega) step
          (Nat.le_of_succ_le hstep) phase hphase hcand'
        have hsurvives : ∃ live, next.activeAt d l = some live := by
          simp only [fighterLevelAction, hphase, bind, Option.bind_some] at ha
          split at ha
          · cases ha
            exact (activeAt_allocations_of_not_failed
              P d l state phase hphase).1 hfailed
          · split at ha
            · cases ha
              exact (activeAt_allocations_of_not_failed
                P d l state phase hphase).2 _ hfailed
            · cases hf : fighterFlushBuffer d l state with
              | some flushed =>
                simp only [hf, Option.some.injEq] at ha
                subst next
                obtain ⟨live, hlive, _, _⟩ := (hlegal.2.1 flushed hf).2.2
                exact ⟨live, hlive⟩
              | none =>
                simp only [hf] at ha
                obtain ⟨move, _, _, _, live, hlive, _⟩ := hlegal.2.2 next ha
                exact ⟨live, hlive⟩
        obtain ⟨live, hlive⟩ := hsurvives
        obtain ⟨old, hold, hc, hg⟩ :=
          candidate_gameCode_of_activeAt_fighterLevelAction
            P d l state next ha live hlive
        rw [hphase] at hold
        cases hold
        exact ⟨live, hlive, hc.trans hcand', (congrArg decodeCounterGame hg).trans hgame'⟩
  obtain ⟨next, hnext, hcand', hgame'⟩ := hinvariant fuel le_rfl
  exact ⟨next, hnext, hcand', hgame',
    (hclosure (tick + 1) (by omega) fuel le_rfl next hnext hcand').1⟩

end Kolmogorov.Milovanov
