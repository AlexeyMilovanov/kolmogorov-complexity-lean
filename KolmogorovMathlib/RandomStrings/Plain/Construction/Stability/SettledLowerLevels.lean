/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.CandidateChronology

/-!
# Lower levels have settled by a late true marker

This module proves blueprint node `constr:lowerstable`
(`lower_levels_settled_at_true_marker`): for every sufficiently late admissible level `l`, the
event of the true marker starts a phase at level `l`, and no level below `l` can change its
history or abort a phase of level `l` at any later tick.

The argument has three parts.

* *Quiescence.* A level is quiescent when it has no enabled action
  (`fighterLevelAction_eq_none_iff`, from `Effective.EventActions`). Servicing a quiescent level
  with an event that neither belongs to it nor is an opponent tuple for it changes nothing
  (`fighterProcessLevel_eq_self_of_levelAction_eq_none`), and quiescence survives a clock
  update that leaves the safety tests of the pending requests unchanged
  (`fighterLevelAction_eq_none_of_advance`). Every completed state is quiescent at every level
  (`fighterLevelAction_fighterState_eq_none`).
* *Freezing.* If all events from a tick `τ` on are longer than the cutoff of level `l`, then one
  tick after `τ - 1` leaves the histories of the levels below `l` and the archive of their
  abortions unchanged, and induction extends this to all later ticks
  (`fighterState_lower_frozen_of_long_events`).
* *The marker.* The true marker is recorded in the start log at its own tick
  (`mem_started_fighterState_of_eventAt`), and no archived phase can have a candidate stamped
  after the current tick (`fighterState_candidates_le_tick`), so no phase with the marker
  candidate was aborted before the freeze began.

The quiescence and freezing lemmas are also used by the common-game, opponent-stream and
phase-separation modules.
-/

namespace Kolmogorov.Milovanov

/-- A quiescent level has no safe unfulfilled pending request, so the preliminary payoff fold
is already the identity. Unsafe requests remain pending and do not delay controlled work. -/
lemma fighterFulfillReady_eq_self_of_levelAction_eq_none
    (P : FighterParams) (d j : ℕ) (state : FighterState)
    (hquiet : fighterLevelAction P d j state = none) :
    fighterFulfillReady P d j state = state := by
  cases hs : state.activeAt d j with
  | none => simp [fighterFulfillReady, hs]
  | some phase =>
    have hpending := ((fighterLevelAction_eq_none_iff P d j state phase hs).mp hquiet).2.1
    have hpay : ∀ q ∈ phase.pending, fighterPayoff P d j q state = state := by
      intro q hq
      have hnot := List.find?_eq_none.mp hpending q hq
      have hguard : ¬ (q ∈ phase.pending ∧ q ∉ state.fulfilled ∧
          fighterSafe P d state.tick q = true) := by
        intro h
        apply hnot
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact h.2
      simp only [fighterPayoff, hs, hguard, ite_false]
    have hfold : ∀ qs : List Coordinate,
        (∀ q ∈ qs, fighterPayoff P d j q state = state) →
        qs.foldl (fun s q => fighterPayoff P d j q s) state = state := by
      intro qs
      induction qs with
      | nil => intro _; rfl
      | cons q qs ih =>
        intro h
        rw [List.foldl_cons, h q (by simp)]
        exact ih (fun r hr => h r (List.mem_cons_of_mem q hr))
    simpa only [fighterFulfillReady, hs] using hfold phase.pending hpay

/-- Closing a quiescent level under its enabled actions stutters at the existing fixpoint. -/
lemma fighterCloseLevel_eq_self_of_levelAction_eq_none
    (P : FighterParams) (d j : ℕ) (state : FighterState)
    (hquiet : fighterLevelAction P d j state = none) :
    fighterCloseLevel P d j state = state := by
  unfold fighterCloseLevel
  cases fighterClosureFuel d j state <;> simp only [fighterClosure, hquiet]

/-- Without a candidate event or a recognized opponent tuple, the complete service of a
quiescent level is the identity. The tuple condition restricts the phase's actual level. -/
lemma fighterProcessLevel_eq_self_of_levelAction_eq_none
    (P : FighterParams) (d j : ℕ) (event : Option TimedEvent) (state : FighterState)
    (hquiet : fighterLevelAction P d j state = none)
    (hevent : ∀ e, event = some e →
      fighterOwner d e.2.2.1.length ≠ some j ∧
      ∀ phase : FighterPhase, phase.level = j → fighterOpponentTuple d phase e.2.2 = none) :
    fighterProcessLevel P d j event state = state := by
  unfold fighterProcessLevel
  rw [fighterFulfillReady_eq_self_of_levelAction_eq_none P d j state hquiet]
  cases event with
  | none => exact fighterCloseLevel_eq_self_of_levelAction_eq_none P d j state hquiet
  | some e =>
    obtain ⟨howner, htuple⟩ := hevent e rfl
    have hopponent : fighterOpponent P d j e.2.2 state = state := by
      cases hs : state.activeAt d j with
      | none => simp [fighterOpponent, hs]
      | some phase =>
        simp only [fighterOpponent, hs,
          htuple phase (FighterState.level_eq_of_activeAt_eq_some hs)]
    simp only [howner, false_and, ite_false, hopponent]
    exact fighterCloseLevel_eq_self_of_levelAction_eq_none P d j state hquiet

/-- Advancing the clock and the schedule of a state keeps a level quiescent when the safety
tests of its pending requests at the new tick agree with those at the old tick. -/
lemma fighterLevelAction_eq_none_of_advance
    (P : FighterParams) (d j : ℕ) (before : FighterState) (tick : ℕ) (schedule : ScheduleState)
    (hsafe : ∀ phase, before.activeAt d j = some phase → ∀ q ∈ phase.pending,
      fighterSafe P d tick q = fighterSafe P d before.tick q)
    (hquiet : fighterLevelAction P d j before = none) :
    fighterLevelAction P d j { before with tick := tick, schedule := schedule } = none := by
  cases hs : before.activeAt d j with
  | none =>
    have ht : ({ before with tick := tick, schedule := schedule } : FighterState).activeAt d j =
        none := hs
    simp [fighterLevelAction, ht]
  | some phase =>
    have ht : ({ before with tick := tick, schedule := schedule } : FighterState).activeAt d j =
        some phase := hs
    obtain ⟨hdummy, hpending, hflush, hstrategy⟩ :=
      (fighterLevelAction_eq_none_iff P d j before phase hs).mp hquiet
    refine (fighterLevelAction_eq_none_iff P d j _ phase ht).mpr ⟨hdummy, ?_, ?_, ?_⟩
    · apply List.find?_eq_none.mpr
      intro q hq htest
      apply List.find?_eq_none.mp hpending q hq
      simp only [Bool.and_eq_true, decide_eq_true_eq] at htest ⊢
      exact ⟨htest.1, (hsafe phase hs q hq) ▸ htest.2⟩
    · simpa [fighterFlushBuffer, ht, hs] using hflush
    · exact (fighterStrategyMove_eq_none_iff P d j _ phase ht).mpr
        ((fighterStrategyMove_eq_none_iff P d j before phase hs).mp hstrategy)

/-- A finite traversal of services preserves the bounded request ranges and the current clock. -/
private lemma foldl_fighterProcessLevel_tick_and_requestRanges
    (P : FighterParams) (d : ℕ) (hd : 1 ≤ d) (event : Option TimedEvent)
    (levels : List ℕ) (state : FighterState)
    (hranges : FighterRequestRanges d state) :
    (levels.foldl (fun s k => fighterProcessLevel P d k event s) state).tick = state.tick ∧
      FighterRequestRanges d
        (levels.foldl (fun s k => fighterProcessLevel P d k event s) state) := by
  induction levels generalizing state with
  | nil => exact ⟨rfl, hranges⟩
  | cons k levels ih =>
    have hk := fighterProcessLevel_tick_and_requestRanges P d k hd event state hranges
    have htail := ih _ hk.2
    exact ⟨htail.1.trans hk.1, htail.2⟩

/-- Reachable completed states have the bounded request ranges and their true numerical tick. -/
lemma fighterState_tick_and_requestRanges (P : FighterParams) (d tick : ℕ) (hd : 1 ≤ d) :
    (fighterState P d tick).tick = tick ∧
      FighterRequestRanges d (fighterState P d tick) := by
  induction tick with
  | zero => exact ⟨rfl, by simp [FighterRequestRanges, fighterState, initialFighterState]⟩
  | succ tick ih =>
    change (fighter_actions P d (tick + 1) (fighterState P d tick)).tick = tick + 1 ∧
      FighterRequestRanges d (fighter_actions P d (tick + 1) (fighterState P d tick))
    unfold fighter_actions
    have hdne : d ≠ 0 := by omega
    simp only [hdne, ite_false]
    exact foldl_fighterProcessLevel_tick_and_requestRanges P d hd _ _
      { fighterState P d tick with tick := tick + 1, schedule := masterState P.B (tick + 1) }
      ih.2

/-- Completed states are quiescent at every level: the exported completed-tick closure theorem
also covers the waiting levels. -/
lemma fighterLevelAction_fighterState_eq_none (P : FighterParams) (d tick j : ℕ) :
    fighterLevelAction P d j (fighterState P d tick) = none := by
  cases hs : (fighterState P d tick).activeAt d j with
  | none => simp [fighterLevelAction, hs]
  | some phase =>
    have h := fighter_event_actions_complete P d tick phase (List.mem_of_find?_eq_some hs)
    rwa [FighterState.level_eq_of_activeAt_eq_some hs] at h

/-- Events longer than the cutoff of a level `l` have neither a lower owner nor a lower opponent
tuple. The latter statement ranges over phases with the specified lower level, rather than
arbitrary phase records. -/
lemma fighterOwner_ne_and_fighterOpponentTuple_eq_none_of_levelLower_lt
    (d l j : ℕ) (hj : j < l) (e : TimedEvent)
    (hlen : levelLower l < e.2.2.1.length) :
    fighterOwner d e.2.2.1.length ≠ some j ∧
      ∀ phase : FighterPhase, phase.level = j → fighterOpponentTuple d phase e.2.2 = none := by
  have hupper := levelUpper_le_levelLower j l hj
  refine ⟨?_, ?_⟩
  · intro howner
    have h := ((fighter_owner_spec d e.2.2.1.length).2 j).mp howner
    omega
  · intro phase hphase
    have hlong : levelUpper phase.level < e.2.2.1.length := by
      rw [hphase]
      omega
    simp [fighterOpponentTuple, hlong]

/-- A finite list of services at or above the cutoff preserves the protected histories and the
archive of abortions caused below the cutoff. -/
private lemma foldl_fighterProcessLevel_lower_frame_of_le
    (P : FighterParams) (d l : ℕ) (hd : 1 ≤ d) (event : Option TimedEvent)
    (levels : List ℕ) (hlevels : ∀ k ∈ levels, l ≤ k) (state : FighterState)
    (hranges : FighterRequestRanges d state) :
    (∀ j < l,
      fighterLevelHistory (levels.foldl (fun s k => fighterProcessLevel P d k event s) state)
          d j = fighterLevelHistory state d j) ∧
    (levels.foldl (fun s k => fighterProcessLevel P d k event s) state).ended.filter
        (fun e => decide (e.2.2.1 = .aborted ∧ e.2.2.2 < l)) =
      state.ended.filter (fun e => decide (e.2.2.1 = .aborted ∧ e.2.2.2 < l)) := by
  induction levels generalizing state with
  | nil => exact ⟨fun _ _ => rfl, rfl⟩
  | cons k levels ih =>
    have hk := fighterProcessLevel_lower_history_eq_of_le P d l k hd
      (hlevels k (by simp)) event state hranges
    have hr := (fighterProcessLevel_tick_and_requestRanges P d k hd event state hranges).2
    have htail := ih (fun k hk => hlevels k (List.mem_cons_of_mem _ hk)) _ hr
    exact ⟨fun j hj => (htail.1 j hj).trans (hk.1 j hj), htail.2.trans hk.2⟩

/-- In an increasing service traversal, lower services stutter at their existing fixpoints;
after the cutoff all remaining services obey the higher-level frame rule. -/
private lemma foldl_fighterProcessLevel_lower_frame_of_sorted
    (P : FighterParams) (d l : ℕ) (hd : 1 ≤ d) (event : Option TimedEvent)
    (levels : List ℕ) (hsorted : levels.Pairwise (· ≤ ·)) (state : FighterState)
    (hranges : FighterRequestRanges d state)
    (hquiet : ∀ j < l, fighterLevelAction P d j state = none)
    (hevent : ∀ j < l, ∀ e, event = some e →
      fighterOwner d e.2.2.1.length ≠ some j ∧
      ∀ phase : FighterPhase, phase.level = j → fighterOpponentTuple d phase e.2.2 = none) :
    (∀ j < l,
      fighterLevelHistory (levels.foldl (fun s k => fighterProcessLevel P d k event s) state)
          d j = fighterLevelHistory state d j) ∧
    (levels.foldl (fun s k => fighterProcessLevel P d k event s) state).ended.filter
        (fun e => decide (e.2.2.1 = .aborted ∧ e.2.2.2 < l)) =
      state.ended.filter (fun e => decide (e.2.2.1 = .aborted ∧ e.2.2.2 < l)) := by
  induction levels with
  | nil => exact ⟨fun _ _ => rfl, rfl⟩
  | cons k levels ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hsorted
    by_cases hk : k < l
    · rw [List.foldl_cons, fighterProcessLevel_eq_self_of_levelAction_eq_none P d k event state
        (hquiet k hk) (hevent k hk)]
      exact ih htail
    · apply foldl_fighterProcessLevel_lower_frame_of_le P d l hd event (k :: levels) _ state
        hranges
      intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · omega
      · have := hhead j hj
        omega

/-- One actual tick preserves the lower histories and introduces no lower-caused abortion when
its event is beyond their budgets and their bounded safety tests have not changed. The previous
completed state supplies finite closure, and `FighterRequestRanges` supplies the precise
bounded domain of pending payoffs. -/
private lemma fighterState_lower_frame_succ
    (P : FighterParams) (d l t : ℕ) (hd : 1 ≤ d)
    (hevent : ∀ e, eventAt P.B (t + 1) = some e → levelLower l < e.2.2.1.length)
    (hsafe : ∀ q : Coordinate, q.2 ≤ levelLower l →
      fighterSafe P d (t + 1) q = fighterSafe P d t q) :
    (∀ j < l,
      fighterLevelHistory (fighterState P d (t + 1)) d j =
        fighterLevelHistory (fighterState P d t) d j) ∧
    (fighterState P d (t + 1)).ended.filter
        (fun e => decide (e.2.2.1 = .aborted ∧ e.2.2.2 < l)) =
      (fighterState P d t).ended.filter
        (fun e => decide (e.2.2.1 = .aborted ∧ e.2.2.2 < l)) := by
  let current := { fighterState P d t with tick := t + 1, schedule := masterState P.B (t + 1) }
  have hb := fighterState_tick_and_requestRanges P d t hd
  have hquiet : ∀ j < l, fighterLevelAction P d j current = none := by
    intro j hj
    refine fighterLevelAction_eq_none_of_advance P d j _ (t + 1) _ ?_
      (fighterLevelAction_fighterState_eq_none P d t j)
    intro phase hphase q hq
    have hbound := (hb.2 phase (List.mem_of_find?_eq_some hphase)).2 q hq
    have hupper := levelUpper_le_levelLower j l hj
    rw [hb.1]
    apply hsafe
    rw [FighterState.level_eq_of_activeAt_eq_some hphase] at hbound
    omega
  have hdne : d ≠ 0 := by omega
  have hnext : fighterState P d (t + 1) = fighter_actions P d (t + 1) (fighterState P d t) := rfl
  rw [hnext]
  unfold fighter_actions
  simp only [hdne, ite_false]
  exact foldl_fighterProcessLevel_lower_frame_of_sorted P d l hd (eventAt P.B (t + 1)) _
    (List.pairwise_mergeSort' (· ≤ ·) _) current hb.2 hquiet
    (fun j hj e he ↦ fighterOwner_ne_and_fighterOpponentTuple_eq_none_of_levelLower_lt d l j hj e
      (hevent e he))

/-- Induct the one-tick preservation result from the state immediately before the marker.
Thus no future quiet interval or restart with the same marker is assumed. -/
lemma fighterState_lower_frozen_of_long_events
    (P : FighterParams) (d l τ : ℕ) (hd : 1 ≤ d) (hτ : 0 < τ)
    (hevents : ∀ t ≥ τ, ∀ e, eventAt P.B t = some e → levelLower l < e.2.2.1.length) :
    ∀ t ≥ τ - 1,
      (∀ j < l, fighterLevelHistory (fighterState P d t) d j =
        fighterLevelHistory (fighterState P d (τ - 1)) d j) ∧
      (fighterState P d t).ended.filter
          (fun e => decide (e.2.2.1 = .aborted ∧ e.2.2.2 < l)) =
        (fighterState P d (τ - 1)).ended.filter
          (fun e => decide (e.2.2.1 = .aborted ∧ e.2.2.2 < l)) := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => exact ⟨fun _ _ => rfl, rfl⟩
  | succ t ht ih =>
    have hτt : τ ≤ t + 1 := by omega
    have hsafe (q : Coordinate) (hq : q.2 ≤ levelLower l) :
        fighterSafe P d (t + 1) q = fighterSafe P d t q := by
      simpa only [Nat.add_sub_cancel] using fighterSafe_eq_pred_of_long_event P d (t + 1)
        (levelLower l) (hevents (t + 1) hτt) q ((Nat.sub_le _ _).trans hq)
    have hs := fighterState_lower_frame_succ P d l t hd (hevents (t + 1) hτt) hsafe
    exact ⟨fun j hj => (hs.1 j hj).trans (ih.1 j hj), hs.2.trans ih.2⟩

/-- Sufficiently late admissible levels start at their own true marker after all lower work ends.
Blueprint node `constr:lowerstable`. The conclusion excludes every later abortion by a lower
level, and does not assume a restart with the same marker or a future quiet interval. The
hypothesis `hfixed` is not needed by the argument. -/
theorem lower_levels_settled_at_true_marker (P : FighterParams) (C cGap cRank d₀ d : ℕ)
    (hfixed : FighterFixedConstants P C cGap cRank d₀)
    (hgood : GoodPadding P d₀ cRank cGap d) :
    ∃ l₀ : ℕ, ∀ l ≥ l₀, P.Admissible d l →
      (levelLower l < (lastProgram P.B (levelScale l)).length ∧
        (lastProgram P.B (levelScale l)).length ≤ levelScale l) ∧
      TrueMarkerPhaseStarted P d l ∧
      LowerLevelsSettled P d l (markerTick P.B (levelScale l)) ∧
      ∀ tick ≥ markerTick P.B (levelScale l), ∀ e ∈ (fighterState P d tick).ended,
        e.1.level = l → e.1.candidate = markerCandidate P.B (levelScale l) →
          e.2.2.1 = .aborted → e.2.2.2 < l → False := by
  have _ := hfixed
  obtain ⟨l₀, hl₀⟩ := exists_level_threshold_marker_window P.B
  refine ⟨l₀, ?_⟩
  intro l hl hadm
  obtain ⟨hbounds, hvalid, hlater⟩ := hl₀ l hl
  obtain ⟨hτ, hevents⟩ := markerTick_pos_and_lt_length_of_ge P.B
    (levelScale l) (levelLower l) hvalid hbounds.1 hlater
  obtain ⟨_, i, x, hev⟩ :=
    (canonical_enumeration_spec_candidate P.B (levelScale l) _).mp hvalid
  have howner : fighterOwner d (lastProgram P.B (levelScale l)).length = some l := by
    apply ((fighter_owner_spec _ _).2 l).mpr
    have hscale : levelScale l ≤ levelUpper l :=
      tower_le_tower (by omega)
    exact ⟨hadm.1, hbounds.1, hbounds.2.trans hscale⟩
  have hstart : TrueMarkerPhaseStarted P d l :=
    mem_started_fighterState_of_eventAt P d l _ i _ x hgood.positive hev howner hbounds.2 hadm
  have hfrozen := fighterState_lower_frozen_of_long_events P d l
    (markerTick P.B (levelScale l)) hgood.positive hτ hevents
  refine ⟨hbounds, hstart, ?_, ?_⟩
  · intro j hj t ht
    exact (hfrozen t ((Nat.sub_le _ _).trans ht)).1 j hj
  · intro tick ht e he hlevel hcandidate habort hcause
    have hmem : e ∈ (fighterState P d tick).ended.filter
        (fun e => decide (e.2.2.1 = .aborted ∧ e.2.2.2 < l)) := by
      simp only [List.mem_filter, decide_eq_true_eq]
      exact ⟨he, habort, hcause⟩
    rw [(hfrozen tick ((Nat.sub_le _ _).trans ht)).2] at hmem
    have hbefore := (fighterState_candidates_le_tick P d
      (markerTick P.B (levelScale l) - 1)).2 e (List.mem_filter.mp hmem).1
    rw [hcandidate] at hbefore
    change markerTick P.B (levelScale l) ≤ markerTick P.B (levelScale l) - 1 at hbefore
    omega

end Kolmogorov.Milovanov
