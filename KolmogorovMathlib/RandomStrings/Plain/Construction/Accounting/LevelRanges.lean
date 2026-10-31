/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Construction.Accounting.PhaseCountBounds

/-!
# Disjoint directive target ranges

This module proves the target-range assertions of blueprint node `constr:intervals`.
The invariant `fighterTargetRangesValid` records admissibility and the prescribed ranges
for allocated directives, game coordinates, and pending requests. Construction establishes
the invariant, and each fighter operation preserves it, so every issued directive lies in
its designated range. Tower inequalities then separate directive kinds within a level and
separate the ranges of distinct levels. These bounds support the capacity estimates and
the bounds on earlier targets in the subsequent accounting modules.
-/

namespace Kolmogorov.Milovanov

/-- A newly constructed phase has the requested level, and its game coordinates and pending
requests lie in that level's payoff range. -/
lemma construction_payoff_target_ranges
    (P : FighterParams) (d l : ℕ) (hd : 1 ≤ d)
    (ha : P.Admissible d l) (candidate : Candidate)
    (state : FighterState) :
    let phase := fighter_construction P d l candidate state
    phase.level = l ∧
    (∀ q ∈ (phase.game d).coordinates,
      FighterTargetRange d l .payoff q.2) ∧
    (∀ q ∈ phase.pending,
      FighterTargetRange d l .payoff q.2) := by
  intro phase
  have hdecode (original : FiniteCounterGame) :
      (decodeCounterGame original.controlWinningPlayer.encode).coordinates =
        original.coordinates := by
    rw [decode_encode_counter_game]
    unfold FiniteCounterGame.controlWinningPlayer
    split_ifs <;> rfl
  have hgame : (phase.game d).coordinates =
      (retainedCoordinateList (constructedLiteralConstant P.literal d) (levelInput d l)
        (P.family.tree d l (levelInput d l))).eraseDups := by
    dsimp [phase, fighter_construction, FighterPhase.game, FighterPhase.fundRequests]
    rw [hdecode]
    rfl
  have hrange : ∀ q ∈ (phase.game d).coordinates, FighterTargetRange d l .payoff q.2 := by
    intro q hq
    rw [hgame] at hq
    have hretained : q ∈ finite_referee_coordinates (constructedLiteralConstant P.literal d)
        (levelInput d l) (P.family.tree d l (levelInput d l)) :=
      List.mem_toFinset.mpr (List.mem_eraseDups.mp hq)
    have hconstant : constructedLiteralConstant P.literal d = d + P.literal.cV := by
      unfold constructedLiteralConstant
      omega
    rw [hconstant] at hretained
    have hbounds := retained_coordinates_within_key_lemma_range
      P.family P.literal.cV P.n₀ d l P.threshold hd ha q.1 q.2 hretained
    obtain ⟨k, _, _, hlower, _⟩ :=
      (mem_finite_referee_coordinates _ _ _ q.1 q.2).mp hretained
    exact ⟨hlower, hbounds.2.2.1⟩
  refine ⟨rfl, hrange, ?_⟩
  intro q hq
  apply hrange q
  dsimp [phase, fighter_construction, FighterPhase.fundRequests] at hq
  change q ∈ (([] ++ List.filter _ (phase.game d).coordinates).filter _).eraseDups at hq
  simp only [List.mem_eraseDups, List.mem_filter, List.nil_append] at hq
  exact hq.1.1

/-- Allocations and active phases belong to admissible levels; allocations have the range
prescribed by their kind, and game coordinates and pending requests have payoff targets. -/
def fighterTargetRangesValid (P : FighterParams) (d : ℕ) (state : FighterState) : Prop :=
  (∀ a ∈ state.allocated,
    P.Admissible d a.level ∧
    FighterTargetRange d a.level a.kind a.target) ∧
  (∀ phase ∈ state.active,
    P.Admissible d phase.level ∧
    (∀ q ∈ (phase.game d).coordinates,
      FighterTargetRange d phase.level .payoff q.2) ∧
    (∀ q ∈ phase.pending,
      FighterTargetRange d phase.level .payoff q.2))

/-- Replacing an active phase preserves valid target ranges if the new phase has them. -/
private lemma target_ranges_valid_put_phase
    (P : FighterParams) (d : ℕ) (state : FighterState) (phase : FighterPhase)
    (hs : fighterTargetRangesValid P d state)
    (hp : P.Admissible d phase.level ∧
      (∀ q ∈ (phase.game d).coordinates, FighterTargetRange d phase.level .payoff q.2) ∧
      (∀ q ∈ phase.pending, FighterTargetRange d phase.level .payoff q.2)) :
    fighterTargetRangesValid P d (state.putPhase d phase) := by
  refine ⟨hs.1, ?_⟩
  intro p hp_mem
  simp only [FighterState.putPhase, List.mem_cons, List.mem_filter] at hp_mem
  rcases hp_mem with rfl | ⟨hp_mem, _⟩
  · exact hp
  · exact hs.2 p hp_mem

private lemma target_ranges_valid_cancel
    (P : FighterParams) (d l : ℕ) (reason : PhaseEnd) (cause : ℕ) (state : FighterState)
    (h_good : fighterTargetRangesValid P d state) :
    fighterTargetRangesValid P d (fighterCancel d l reason cause state) := by
  unfold fighterCancel
  cases state.activeAt d l
  · exact h_good
  · dsimp [fighterTargetRangesValid] at h_good ⊢
    rcases h_good with ⟨h_alloc, h_active⟩
    constructor
    · exact h_alloc
    · intro phase h_phase
      simp only [List.mem_filter] at h_phase
      exact h_active phase h_phase.1

private lemma target_ranges_valid_abort_above
    (P : FighterParams) (d l : ℕ) (state : FighterState)
    (h_good : fighterTargetRangesValid P d state) :
    fighterTargetRangesValid P d (fighterAbortAbove d l state) := by
  unfold fighterAbortAbove
  apply List.foldlRecOn _ _ h_good
  intro s hs phase _
  split_ifs
  · exact target_ranges_valid_cancel P d phase.level .aborted l s hs
  · exact hs

private lemma target_ranges_valid_allocate
    (P : FighterParams) (d l : ℕ) (kind : DirectiveKind) (target : ℕ)
    (output : BitString) (s : FighterState)
    (hs : fighterTargetRangesValid P d s)
    (ha : P.Admissible d l)
    (hr : FighterTargetRange d l kind target) :
    fighterTargetRangesValid P d (fighterAllocate d l kind target output s).1 := by
  unfold fighterAllocate
  cases h_active : s.activeAt d l with
  | none =>
    exact hs
  | some phase =>
    cases h_fresh : (if target = 0 then none else
      (fighterInputs d (target - 1)).find? (fun p ↦ !s.allocated.any (fun a ↦ a.input == p))) with
    | none =>
      apply target_ranges_valid_cancel
      dsimp [fighterTargetRangesValid] at hs ⊢
      exact hs
    | some p =>
      apply target_ranges_valid_abort_above
      dsimp [fighterTargetRangesValid] at hs ⊢
      constructor
      · intro a ha_alloc
        simp only [List.mem_append, List.mem_singleton] at ha_alloc
        cases ha_alloc with
        | inl h_in_s => exact hs.1 a h_in_s
        | inr h_eq =>
          subst h_eq
          exact ⟨ha, hr⟩
      · exact hs.2

private lemma target_ranges_valid_payoff
    (P : FighterParams) (d l : ℕ) (q : Coordinate) (s : FighterState)
    (hs : fighterTargetRangesValid P d s) :
    fighterTargetRangesValid P d (fighterPayoff P d l q s) := by
  unfold fighterPayoff
  cases hactive : s.activeAt d l with
  | none => exact hs
  | some phase =>
    dsimp only
    split
    · rename_i hready
      have hmem : phase ∈ s.active := List.mem_of_find?_eq_some hactive
      have hlevel : phase.level = l := eq_of_beq
        (List.find?_some (p := fun p : FighterPhase ↦ p.level == l) hactive)
      have hadm : P.Admissible d l := hlevel ▸ (hs.2 phase hmem).1
      have hrange : FighterTargetRange d l .payoff q.2 :=
        hlevel ▸ (hs.2 phase hmem).2.2 q hready.1
      have halloc := target_ranges_valid_allocate P d l .payoff q.2 q.1 s hs hadm hrange
      split
      · refine ⟨halloc.1, ?_⟩
        intro p hp
        obtain ⟨p', hp', rfl⟩ := List.mem_map.mp hp
        have hphase := halloc.2 p' hp'
        exact ⟨hphase.1, hphase.2.1, fun r hr ↦
          hphase.2.2 r (List.mem_filter.mp hr).1⟩
      · exact halloc
    · exact hs

private lemma target_ranges_valid_fulfill_ready
    (P : FighterParams) (d l : ℕ) (state : FighterState)
    (h_good : fighterTargetRangesValid P d state) :
    fighterTargetRangesValid P d (fighterFulfillReady P d l state) := by
  unfold fighterFulfillReady
  cases state.activeAt d l with
  | none => exact h_good
  | some phase =>
    exact List.foldlRecOn phase.pending _ h_good
      (fun s hs q _ ↦ target_ranges_valid_payoff P d l q s hs)

private lemma target_ranges_valid_fuel_unit
    (P : FighterParams) (d l : ℕ) (q : Coordinate) (state : FighterState)
    (h_good : fighterTargetRangesValid P d state) :
    fighterTargetRangesValid P d (fighterFuelUnit P d l q state) := by
  unfold fighterFuelUnit
  cases h_active : state.activeAt d l with
  | none => exact h_good
  | some phase =>
    dsimp only
    split
    · have h_find : state.active.find? (fun p : FighterPhase ↦ p.level == l) =
          some phase := h_active
      have hp := h_good.2 phase (List.mem_of_find?_eq_some h_find)
      have hlevel : phase.level = l := beq_iff_eq.mp
        (List.find?_some (p := fun p : FighterPhase ↦ p.level == l) h_find)
      let charged := { phase with controlledRemaining := phase.controlledRemaining - 1 }
      let index := fighterFreshString d
        (phase.indices[(phase.game d).coordinates.idxOf q]?.getD [])
      let output := pairCode (triple q.1 (q.2 - d) phase.candidate.1) index
      have hc := target_ranges_valid_put_phase P d state charged h_good hp
      have ha := target_ranges_valid_allocate
        P d l .fuel (levelUpper l + d) output (state.putPhase d charged) hc
        (hlevel ▸ hp.1) rfl
      change fighterTargetRangesValid P d
        (match fighterAllocate d l .fuel (levelUpper l + d) output
            (state.putPhase d charged) with
        | (next, success) =>
          if success then
            fighterFulfillReady P d l
              (next.putPhase d
                ((charged.insertIndex d q index).fundRequests d next.fulfilled))
          else next)
      cases he : fighterAllocate d l .fuel (levelUpper l + d) output
          (state.putPhase d charged) with
      | mk next success =>
        rw [he] at ha
        cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
        · exact ha
        · apply target_ranges_valid_fulfill_ready
          apply target_ranges_valid_put_phase P d next _ ha
          refine ⟨hp.1, hp.2.1, ?_⟩
          intro r hr
          dsimp only [FighterPhase.fundRequests, FighterPhase.insertIndex] at hr
          change r ∈ (List.filter _ (_ ++ _)).eraseDups at hr
          simp only [List.mem_eraseDups, List.mem_filter, List.mem_append] at hr
          rcases hr.1 with hr_old | hr_funded
          · exact hp.2.2 r hr_old
          · exact hp.2.1 r hr_funded.1
    · exact h_good

private lemma target_ranges_valid_fuel_units
    (P : FighterParams) (d l : ℕ) (q : Coordinate) (count : ℕ) (state : FighterState)
    (h_good : fighterTargetRangesValid P d state) :
    fighterTargetRangesValid P d (fighterFuelUnits P d l q count state) := by
  induction count generalizing state with
  | zero => exact h_good
  | succ c ih =>
    unfold fighterFuelUnits
    exact ih (fighterFuelUnit P d l q state) (target_ranges_valid_fuel_unit P d l q state h_good)

private lemma target_ranges_valid_opponent
    (P : FighterParams) (d l : ℕ) (event : ProgramEvent) (state : FighterState)
    (h_good : fighterTargetRangesValid P d state) :
    fighterTargetRangesValid P d (fighterOpponent P d l event state) := by
  classical
  cases h_active : state.activeAt d l with
  | none =>
    simpa [fighterOpponent, h_active] using h_good
  | some phase =>
    cases h_tuple : fighterOpponentTuple d phase event with
    | none =>
        simpa [fighterOpponent, h_active, h_tuple] using h_good
    | some result =>
        rcases result with ⟨q, index⟩
        by_cases h_index : index ∈ phase.indicesAt d q
        · simpa [fighterOpponent, h_active, h_tuple, h_index] using h_good
        · by_cases h_rem : phase.opponentRemaining = 0
          · simpa [fighterOpponent, h_active, h_tuple, h_index, h_rem] using
              (target_ranges_valid_cancel
                P d l .opponentExhausted l state h_good)
          · dsimp only [fighterOpponent]
            simp only [h_active, h_tuple, h_index, h_rem, ite_false]
            apply target_ranges_valid_fulfill_ready
            apply target_ranges_valid_put_phase P d _ _ h_good
            have ⟨ha, hg, hpending⟩ :=
              h_good.2 phase (List.mem_of_find?_eq_some h_active)
            refine ⟨ha, hg, ?_⟩
            intro r hr
            dsimp only [FighterPhase.fundRequests, FighterPhase.insertIndex] at hr
            change r ∈ (List.filter _ (_ ++ _)).eraseDups at hr
            simp only [List.mem_eraseDups, List.mem_filter, List.mem_append] at hr
            rcases hr.1 with hold | hfunded
            · exact hpending r hold
            · exact hg r hfunded.1

private lemma target_ranges_valid_start_phase
    (P : FighterParams) (d l : ℕ) (candidate : Candidate) (s : FighterState)
    (hd : 1 ≤ d)
    (ha : P.Admissible d l)
    (hs : fighterTargetRangesValid P d s) :
    fighterTargetRangesValid P d (fighterStartPhase P d l candidate s) := by
  let waiting := fighterAbortAbove d l (fighterCancel d l .replaced l s)
  have hc := target_ranges_valid_cancel P d l .replaced l s hs
  have hwaiting := target_ranges_valid_abort_above P d l _ hc
  have hcons := construction_payoff_target_ranges P d l hd ha candidate waiting
  apply target_ranges_valid_put_phase P d waiting _ hwaiting
  exact ⟨hcons.1.symm ▸ ha, hcons.1.symm ▸ hcons.2⟩

private lemma target_ranges_valid_dummy
    (P : FighterParams) (d l : ℕ) (state : FighterState)
    (h_good : fighterTargetRangesValid P d state) :
    fighterTargetRangesValid P d (fighterDummy d l state) := by
  unfold fighterDummy
  cases hactive : state.activeAt d l with
  | none => exact h_good
  | some phase =>
    dsimp only
    cases hdummy : phase.dummy with
    | none => exact h_good
    | some output =>
      dsimp only
      split
      · exact h_good
      · have hmem : phase ∈ state.active := List.mem_of_find?_eq_some hactive
        have hlevel : phase.level = l := eq_of_beq
          (List.find?_some (p := fun p : FighterPhase ↦ p.level == l) hactive)
        have hp := h_good.2 phase hmem
        have halloc := target_ranges_valid_allocate P d l .dummy (levelInput d l)
          output state h_good (hlevel ▸ hp.1) rfl
        split
        · exact target_ranges_valid_put_phase P d _ _ halloc hp
        · exact halloc

private lemma target_ranges_valid_flush_buffer
    (P : FighterParams) (d l : ℕ) (s next : FighterState)
    (hs : fighterTargetRangesValid P d s)
    (hnext : fighterFlushBuffer d l s = some next) :
    fighterTargetRangesValid P d next := by
  dsimp [fighterTargetRangesValid] at hs ⊢
  unfold fighterFlushBuffer at hnext
  cases hphase : s.activeAt d l
  · simp [hphase] at hnext
  · rename_i phase
    simp only [hphase, bind, Option.bind_some] at hnext
    split_ifs at hnext with hcond
    · injection hnext with hnext
      subst hnext
      constructor
      · intro a ha
        exact hs.1 a ha
      · intro p hp
        dsimp [FighterState.putPhase] at hp
        simp only [List.mem_cons, List.mem_filter] at hp
        rcases hp with rfl | ⟨hp, _⟩
        · have h_find : s.active.find? (fun p ↦ p.level == l) = some phase := by
            simpa only [FighterState.activeAt] using hphase
          have h_mem : phase ∈ s.active := List.mem_of_find?_eq_some h_find
          exact hs.2 phase h_mem
        · exact hs.2 p hp

private lemma target_ranges_valid_strategy_move
    (P : FighterParams) (d l : ℕ) (s next : FighterState)
    (hs : fighterTargetRangesValid P d s)
    (hnext : fighterStrategyMove P d l s = some next) :
    fighterTargetRangesValid P d next := by
  unfold fighterStrategyMove at hnext
  cases hphase : s.activeAt d l
  · rw [hphase] at hnext
    dsimp at hnext
    contradiction
  · rename_i phase
    rw [hphase] at hnext
    dsimp at hnext
    split_ifs at hnext with h1
    · cases hm : (phase.game d).strategy (phase.official d)
      · rw [hm] at hnext
        dsimp at hnext
        contradiction
      · rename_i move
        rw [hm] at hnext
        dsimp at hnext
        split_ifs at hnext with h2
        · let f := fun (s : FighterState) (x : Coordinate × ℕ) ↦
            fighterFuelUnits P d l x.1 (move[x.2]?.getD 0) s
          generalize hfold : (List.foldl f s (phase.game d).coordinates.zipIdx) = next_fold
          rw [hfold] at hnext
          have hnext_fold : fighterTargetRangesValid P d next_fold := by
            rw [← hfold]
            exact List.foldlRecOn _ f hs (fun st hst x _ ↦
              target_ranges_valid_fuel_units P d l x.1 (move[x.2]?.getD 0) st hst)
          change (match next_fold.activeAt d l with
            | none => some next_fold
            | some live => some (next_fold.putPhase d
                { live with officialCode :=
                  ((phase.game d).afterMove (phase.official d) move).encode })) = some next at hnext
          cases hlive : next_fold.activeAt d l
          · rw [hlive] at hnext
            injection hnext with hnext
            rw [← hnext]
            exact hnext_fold
          · rw [hlive] at hnext
            injection hnext with hnext
            rw [← hnext]
            rename_i live
            have h_mem : live ∈ next_fold.active := by
              unfold FighterState.activeAt at hlive
              exact List.mem_of_find?_eq_some hlive
            exact target_ranges_valid_put_phase P d _ _ hnext_fold
              (hnext_fold.2 live h_mem)

private lemma target_ranges_valid_level_action
    (P : FighterParams) (d l : ℕ) (s next : FighterState)
    (hs : fighterTargetRangesValid P d s)
    (hnext : fighterLevelAction P d l s = some next) :
    fighterTargetRangesValid P d next := by
  unfold fighterLevelAction at hnext
  dsimp at hnext
  rcases eq_or_ne (s.activeAt d l) none with h | h
  · simp [h] at hnext
  · obtain ⟨phase, hphase⟩ := Option.ne_none_iff_exists'.mp h
    simp only [hphase, Option.bind_some] at hnext
    split_ifs at hnext with hdummy
    · injection hnext with hnext
      subst hnext
      exact target_ranges_valid_dummy P d l s hs
    · revert hnext
      cases hq : (List.find? (fun q ↦
        decide (q ∉ s.fulfilled) && fighterSafe P d s.tick q) phase.pending)
      · cases hflush : fighterFlushBuffer d l s
        · intro hnext
          exact target_ranges_valid_strategy_move P d l s next hs hnext
        · rename_i next'
          intro hnext
          injection hnext with hnext
          subst hnext
          exact target_ranges_valid_flush_buffer P d l s next' hs hflush
      · rename_i q
        intro hnext
        injection hnext with hnext
        subst hnext
        exact target_ranges_valid_payoff P d l q s hs

private lemma target_ranges_valid_closure
    (P : FighterParams) (d l : ℕ) (fuel : ℕ) (state : FighterState)
    (h_good : fighterTargetRangesValid P d state) :
    fighterTargetRangesValid P d (fighterClosure P d l fuel state) := by
  induction fuel generalizing state with
  | zero => exact h_good
  | succ f ih =>
    unfold fighterClosure
    cases haction : fighterLevelAction P d l state with
    | none => exact h_good
    | some next =>
      exact ih next (target_ranges_valid_level_action P d l state next h_good haction)

private lemma target_ranges_valid_close_level
    (P : FighterParams) (d l : ℕ) (state : FighterState)
    (h_good : fighterTargetRangesValid P d state) :
    fighterTargetRangesValid P d (fighterCloseLevel P d l state) := by
  unfold fighterCloseLevel
  exact target_ranges_valid_closure P d l (fighterClosureFuel d l state) state h_good

private lemma target_ranges_valid_process_level
    (P : FighterParams) (d l : ℕ) (hd : 1 ≤ d) (event : Option TimedEvent) (state : FighterState)
    (h_good : fighterTargetRangesValid P d state) :
    fighterTargetRangesValid P d (fighterProcessLevel P d l event state) := by
  unfold fighterProcessLevel
  have h_checked : fighterTargetRangesValid P d (fighterFulfillReady P d l state) :=
    target_ranges_valid_fulfill_ready P d l state h_good
  have h_next : fighterTargetRangesValid P d (match event with
    | none => fighterFulfillReady P d l state
    | some e =>
      if fighterOwner d e.2.2.1.length = some l ∧ e.2.2.1.length ≤ levelScale l ∧
          P.Admissible d l then
        fighterStartPhase P d l (e.2.2.1, e.1) (fighterFulfillReady P d l state)
      else fighterOpponent P d l e.2.2 (fighterFulfillReady P d l state)) := by
    cases event with
    | none => exact h_checked
    | some e =>
      dsimp
      split_ifs with h
      · rcases h with ⟨h1, h2, h3⟩
        exact target_ranges_valid_start_phase P d l (e.2.2.1, e.1)
          (fighterFulfillReady P d l state) hd h3 h_checked
      · exact target_ranges_valid_opponent P d l e.2.2 (fighterFulfillReady P d l state) h_checked
  exact target_ranges_valid_close_level P d l _ h_next

private lemma target_ranges_valid_actions
    (P : FighterParams) (d tick : ℕ) (state : FighterState)
    (hs : fighterTargetRangesValid P d state) :
    fighterTargetRangesValid P d (fighter_actions P d tick state) := by
  unfold fighter_actions
  split_ifs with hd
  · subst hd
    simp [fighterTargetRangesValid, initialFighterState]
  · let current := { state with tick := tick, schedule := masterState P.B tick }
    have hc : fighterTargetRangesValid P d current := hs
    apply List.foldlRecOn _ _ hc
    intro s hs l _
    exact target_ranges_valid_process_level P d l (by omega) _ s hs

/-- Every actually issued directive belongs to an admissible level and its stated target range.
Blueprint node `constr:intervals`. The issuing phase and kind are read from the permanent graph. -/
theorem fighter_directive_target_ranges (P : FighterParams) (d tick : ℕ)
    (a : AllocatedDirective) (ha : a ∈ (fighterState P d tick).allocated) :
    P.Admissible d a.level ∧ FighterTargetRange d a.level a.kind a.target := by
  have hstate (t : ℕ) : fighterTargetRangesValid P d (fighterState P d t) := by
    induction t with
    | zero => simp [fighterState, fighterTargetRangesValid, initialFighterState]
    | succ t ih =>
      exact target_ranges_valid_actions P d (t + 1) (fighterState P d t) ih
  exact (hstate tick).1 a ha

/-- The input scale of a level is below its fuel scale. -/
lemma levelScale_lt_levelUpper (l : ℕ) : levelScale l < levelUpper l := by
  dsimp [levelScale, levelUpper]
  exact tower_lt_tower_add_one (2 * l)

/-- The exclusive upper bound for payoff targets does not exceed the fuel scale. -/
lemma levelRangeBound_le_upper (l : ℕ) : levelRangeBound l ≤ levelUpper l := by
  rcases l with _ | _ | l'
  · dsimp [levelRangeBound, levelUpper, towerRangeBound, levelScale, tower]
    decide
  · dsimp [levelRangeBound, levelUpper, towerRangeBound, levelScale, tower]
    decide
  · have hscale : tower 4 ≤ levelScale (l' + 2) := by
      have h := tower_le_tower (n := 4) (m := 2 * (l' + 2)) (by omega)
      simpa [levelScale] using h
    have h32 : 32 ≤ levelScale (l' + 2) := (by decide : 32 ≤ tower 4).trans hscale
    have ht : IsTower (levelScale (l' + 2)) := ⟨2 * (l' + 2), rfl⟩
    have hlt := fighter_range_below_upper (levelScale (l' + 2)) h32 ht
    simpa [levelRangeBound, level_upper_eq] using hlt.le

/-- The dummy, fuel, and payoff target ranges at an activated level are pairwise disjoint.
Blueprint node `constr:intervals`. -/
theorem fighter_target_types_disjoint (P : FighterParams) (d l tick : ℕ)
    (ha : FighterActivated P d l tick) (first second : DirectiveKind) (hne : first ≠ second) :
    Disjoint {r | FighterTargetRange d l first r} {r | FighterTargetRange d l second r} := by
  rcases ha with ⟨_, _⟩
  have hscale := levelScale_lt_levelUpper l
  have hrange := levelRangeBound_le_upper l
  rw [Set.disjoint_left]
  intro r hr₁ hr₂
  cases first <;> cases second <;>
    simp only [Set.mem_ofPred_eq, FighterTargetRange] at hr₁ hr₂ <;>
    first | exact (hne rfl).elim | omega

/-- No target belongs to the ranges of two different activated levels.
Blueprint node `constr:intervals`. -/
theorem fighter_level_ranges_disjoint (P : FighterParams) (d j l tick : ℕ)
    (hj : FighterActivated P d j tick) (hl : FighterActivated P d l tick) (hne : j ≠ l)
    (first second : DirectiveKind) :
    Disjoint {r | FighterTargetRange d j first r} {r | FighterTargetRange d l second r} := by
  rcases hj with ⟨_, _⟩
  rcases hl with ⟨_, _⟩
  have bounds (k : ℕ) (kind : DirectiveKind) {r : ℕ}
      (hr : FighterTargetRange d k kind r) :
      levelScale k + d ≤ r ∧ r ≤ levelUpper k + d := by
    have hscale := levelScale_lt_levelUpper k
    have hrange := levelRangeBound_le_upper k
    cases kind <;> simp only [FighterTargetRange] at hr <;> omega
  have gap {a b : ℕ} (hab : a < b) : levelUpper a < levelScale b := by
    change tower (2 * a + 1) < tower (2 * b)
    exact (tower_lt_tower_add_one (2 * a + 1)).trans_le (tower_le_tower (by omega))
  rw [Set.disjoint_left]
  intro r hrj hrl
  have hbj := bounds j first hrj
  have hbl := bounds l second hrl
  rcases lt_or_gt_of_ne hne with hjl | hlj
  · have hgap := gap hjl
    omega
  · have hgap := gap hlj
    omega

end Kolmogorov.Milovanov
