/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.CommonGameInitial

/-!
# The true-marker phase at its initial tick

This module establishes the base case of the common-game invariant for blueprint node
`constr:opponent`. The marker event installs a phase with the true candidate; legal internal
closure and the remaining higher-level services preserve that phase. The live-state invariant
then supplies its buffer invariant. We also show that lower-level services are inert after the
marker tick, using the exhaustion of their program budgets and the stability of their safety
checks. `CommonGame` uses the base case, while it and `CommonGameInvariantTick` use the inertness
result to propagate the common game through subsequent ticks.
-/

namespace Kolmogorov.Milovanov

/-- An internal action in a true-marker closure preserves the candidate and level
of the active phase. -/
private lemma exists_true_marker_phase_after_action
    (P : FighterParams) (C cGap cRank d₀ d l : ℕ)
    (hfixed : FighterFixedConstants P C cGap cRank d₀)
    (hgood : GoodPadding P d₀ cRank cGap d) (hlate : LateAdmissibleOccurrence P d l)
    (hclosure : TrueMarkerClosureLegal P d l)
    (tick : ℕ) (htick : markerTick P.B (levelScale l) ≤ tick)
    (step : ℕ) (hstep : step < fighterClosureFuel d l (fighterBeforeClosure P d tick l))
    (state : FighterState) (hstate : state = fighterClosureAt P d tick l step)
    (phase : FighterPhase) (hphase : state.activeAt d l = some phase)
    (hcandidate : phase.candidate = markerCandidate P.B (levelScale l))
    (next : FighterState) (hnext : fighterLevelAction P d l state = some next) :
    ∃ p', next.activeAt d l = some p' ∧
      p'.candidate = phase.candidate ∧ p'.level = phase.level := by
  have hfinish (p : FighterPhase)
      (hp : next.activeAt d l = some p) :
      ∃ p', next.activeAt d l = some p' ∧
        p'.candidate = phase.candidate ∧ p'.level = phase.level := by
    obtain ⟨old, hold, hc⟩ :=
      candidate_eq_of_activeAt_fighterLevelAction
        P d l state next hnext p hp
    have he : old = phase := Option.some.inj (hold.symm.trans hphase)
    subst old
    have hlp : p.level = l := FighterState.level_eq_of_activeAt_eq_some hp
    have hlphase : phase.level = l := FighterState.level_eq_of_activeAt_eq_some hphase
    exact ⟨p, hp, hc.symm, hlp.trans hlphase.symm⟩
  unfold fighterLevelAction at hnext
  rw [hphase] at hnext
  change (do
    if phase.dummy.isSome && !phase.dummyIssued then some (fighterDummy d l state) else
      match phase.pending.find? (fun q ↦
          decide (q ∉ state.fulfilled) && fighterSafe P d state.tick q) with
      | some q => some (fighterPayoff P d l q state)
      | none =>
        match fighterFlushBuffer d l state with
        | some next => some next
        | none => fighterStrategyMove P d l state) = some next at hnext
  split at hnext
  · rename_i dummy_true
    injection hnext with hnext_eq
    rw [← hnext_eq]
    exact exists_activeAt_fighterDummy_of_closureAt P C cGap cRank d₀ d l hfixed hgood hlate
      tick htick step state hstate phase hphase
  · rename_i dummy_false
    split at hnext
    · rename_i q hq
      injection hnext with hnext_eq
      rw [← hnext_eq]
      exact exists_activeAt_fighterPayoff_of_closureAt P C cGap cRank d₀ d l hfixed hgood hlate
        tick htick step state hstate phase hphase q
    · rename_i pending_none
      subst state
      have h1 : step ≤ fighterClosureFuel d l
          (fighterBeforeClosure P d tick l) := Nat.le_of_lt hstep
      have hlegal := hclosure tick htick step h1 phase hphase hcandidate
      cases hf : fighterFlushBuffer d l
          (fighterClosureAt P d tick l step) with
      | some flushed =>
          simp only [hf] at hnext
          have he : flushed = next := Option.some.inj hnext
          subst next
          obtain ⟨_, _, afterPhase, hafter, _, _⟩ :=
            hlegal.2.1 flushed hf
          exact hfinish afterPhase hafter
      | none =>
          simp only [hf] at hnext
          obtain ⟨move, _, _, _, afterPhase, hafter, _⟩ :=
            hlegal.2.2 next hnext
          exact hfinish afterPhase hafter

/-- Legal internal closure at or after the marker tick preserves an installed
true-marker phase. -/
lemma exists_marker_phase_after_closure
    (P : FighterParams) (C cGap cRank d₀ d l : ℕ)
    (hfixed : FighterFixedConstants P C cGap cRank d₀)
    (hgood : GoodPadding P d₀ cRank cGap d) (hlate : LateAdmissibleOccurrence P d l)
    (hclosure : TrueMarkerClosureLegal P d l)
    (tick : ℕ) (htick : markerTick P.B (levelScale l) ≤ tick)
    (hbefore : ∃ phase, (fighterBeforeClosure P d tick l).activeAt d l = some phase ∧
      phase.level = l ∧ phase.candidate = markerCandidate P.B (levelScale l)) :
    ∃ p, (fighterCloseLevel P d l (fighterBeforeClosure P d tick l)).activeAt d l = some p ∧
      p.level = l ∧ p.candidate = markerCandidate P.B (levelScale l) := by
  let fuel := fighterClosureFuel d l (fighterBeforeClosure P d tick l)
  have hrec (k : ℕ) (s : FighterState) :
      fighterClosure P d l (k + 1) s =
        match fighterLevelAction P d l (fighterClosure P d l k s) with
        | none => fighterClosure P d l k s
        | some next => next := by
    induction k generalizing s with
    | zero => rfl
    | succ k ih =>
      cases ha : fighterLevelAction P d l s with
      | none => simp only [fighterClosure, ha]
      | some next => simpa only [fighterClosure, ha] using ih next
  -- Continue the closure from any prefix, tracking the remaining fuel.
  have hcontinue : ∀ remaining step (state : FighterState), step + remaining ≤ fuel →
      state = fighterClosureAt P d tick l step →
      ∀ phase, state.activeAt d l = some phase →
        phase.candidate = markerCandidate P.B (levelScale l) →
        ∃ live, (fighterClosure P d l remaining state).activeAt d l = some live ∧
          live.candidate = markerCandidate P.B (levelScale l) ∧ live.level = phase.level := by
    intro remaining
    induction remaining with
    | zero =>
      intro step state _ _ phase hphase hcand
      exact ⟨phase, hphase, hcand, rfl⟩
    | succ remaining ih =>
      intro step state hbound hstate phase hphase hcand
      simp only [fighterClosure]
      cases ha : fighterLevelAction P d l state with
      | none => exact ⟨phase, hphase, hcand, rfl⟩
      | some next =>
        obtain ⟨live, hlive, hc, hl⟩ := exists_true_marker_phase_after_action
          P C cGap cRank d₀ d l hfixed hgood hlate hclosure tick htick
          step ((Nat.lt_add_of_pos_right (Nat.succ_pos remaining)).trans_le hbound)
          state hstate phase hphase hcand next ha
        have hnext : next = fighterClosureAt P d tick l (step + 1) := by
          change next = fighterClosure P d l (step + 1) (fighterBeforeClosure P d tick l)
          rw [hrec]
          change next = match fighterLevelAction P d l
              (fighterClosureAt P d tick l step) with
            | none => fighterClosureAt P d tick l step
            | some next => next
          rw [← hstate, ha]
        obtain ⟨last, hlast, hcand', hlevel⟩ := ih (step + 1) next (by omega)
          hnext live hlive (hc.trans hcand)
        exact ⟨last, hlast, hcand', hlevel.trans hl⟩
  obtain ⟨phase, hphase, hlevel, hcand⟩ := hbefore
  obtain ⟨live, hlive, hcand', hlevel'⟩ :=
    hcontinue fuel 0 (fighterBeforeClosure P d tick l) (by omega) rfl phase hphase hcand
  exact ⟨live, hlive, hlevel'.trans hlevel, hcand'⟩

/-- At the marker tick there is a true-marker phase carrying the common game and satisfying
the buffer invariant. -/
lemma exists_trueMarkerPhaseAt_markerTick_with_invariants
    (P : FighterParams) (C cGap cRank d₀ d l : ℕ)
    (hfixed : FighterFixedConstants P C cGap cRank d₀)
    (hgood : GoodPadding P d₀ cRank cGap d) (hlate : LateAdmissibleOccurrence P d l)
    (hclosure : TrueMarkerClosureLegal P d l)
    (game : FiniteCounterGame)
    (hgame : ∀ phase, TrueMarkerPhaseAt P d l (markerTick P.B (levelScale l)) phase →
      phase.game d = game) :
    ∃ phase, TrueMarkerPhaseAt P d l (markerTick P.B (levelScale l)) phase ∧
      phase.game d = game ∧ phase.BufferInvariant d := by
  obtain ⟨phase, hphase⟩ := exists_trueMarkerPhaseAt
    P C cGap cRank d₀ d l hfixed hgood hlate hclosure
  exact ⟨phase, hphase, hgame phase hphase, (fighter_live_invariants P d _ hgood.positive phase
      (List.mem_of_find?_eq_some hphase.2.2.2)).1⟩

/-- Lower-level services after the marker tick are inert: their program budgets are exhausted
and their bounded safety tables cannot change. -/
lemma fighterBeforeLevel_succ_eq_of_markerTick_le
    (P : FighterParams) (d l tick : ℕ) (hd : 1 ≤ d)
    (htick : markerTick P.B (levelScale l) ≤ tick) :
    fighterBeforeLevel P d (tick + 1) l =
      { fighterState P d tick with
        tick := tick + 1, schedule := masterState P.B (tick + 1) } := by
  let before := fighterState P d tick
  let current := { before with tick := tick + 1, schedule := masterState P.B (tick + 1) }
  have hlong : ∀ e, eventAt P.B (tick + 1) = some e →
      levelScale l < e.2.2.1.length := by
    intro ⟨t, i, p, x⟩ he
    have ht : t = tick + 1 := (canonical_enumeration_spec_sound P.B he).1
    subst t
    exact length_gt_of_eventAt_of_markerTick_lt P.B (levelScale l)
      (tick + 1) (by omega) i p x he
  have hcut : levelLower l ≤ levelScale l :=
    tower_le_tower (by omega)
  have hrange := fighterState_tick_and_requestRanges P d tick hd
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

end Kolmogorov.Milovanov
