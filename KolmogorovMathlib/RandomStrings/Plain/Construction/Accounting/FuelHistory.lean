/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Construction.Accounting.DummyIdentities
import KolmogorovMathlib.RandomStrings.Plain.Construction.Accounting.LevelFrames

/-!
# Dummy counts and fuel allocation history

This module proves the history facts behind the phase-count bounds of the fighter
construction (blueprint node `constr:phasecount`).

* `fighterDirectiveCount_dummy_le_fighterPhaseCount`: the dummy-identity invariant is
  propagated through every tick of `fighterState`, so the dummy allocations at a level have
  pairwise distinct phase identities, and each of them is recorded among the phase starts;
  hence there are at most as many dummy allocations at a level as phase starts there.
* `fighterState_allocated_fuel_mem_started`: a second invariant (every allocation and every
  active phase is recorded in `started`) is preserved by every construction operation, which
  shows that each fuel allocation originates from a recorded phase start.
* `FighterState.invariant_foldl`: a predicate preserved by single updates is preserved by
  folding a list of updates over a state.

`PhaseCountBounds` uses these results to charge dummy and fuel directives to their phases.
-/

namespace Kolmogorov.Milovanov

/-- The reachable state's clock equals its numerical master tick. -/
private lemma fighterState_tick
    (P : FighterParams) (d tick : ℕ) :
    (fighterState P d tick).tick = tick := by
  have hfold (event : Option TimedEvent) (levels : List ℕ) (s : FighterState) :
      (levels.foldl (fun s l ↦ fighterProcessLevel P d l event s) s).tick = s.tick := by
    induction levels generalizing s with
    | nil => rfl
    | cons l levels ih =>
      exact (ih _).trans
        (processLevel_tick_allocated
          P d l event s).1
  cases tick with
  | zero => rfl
  | succ tick =>
    change (fighter_actions P d (tick + 1) (fighterState P d tick)).tick = tick + 1
    unfold fighter_actions
    split
    · rfl
    · exact hfold _ _ _

/-- Advancing the clock and replacing the schedule preserves the identity invariants. -/
private lemma dummy_identity_invariant_advance
    (d tick : ℕ) (schedule : ScheduleState) (state : FighterState)
    (h_good : DummyIdentityInvariant d state)
    (h_tick : state.tick ≤ tick) :
    DummyIdentityInvariant d { state with tick := tick, schedule := schedule } := by
  refine ⟨h_good.1, h_good.2.1, ?_, ?_⟩
  · intro a ha
    exact (h_good.2.2.1 a ha).trans h_tick
  · intro l p hp
    exact (h_good.2.2.2 l p hp).trans h_tick

/-- Fold over distinct levels, retaining old candidate timestamps at every unprocessed
level. This supplies event freshness for each single-level preservation step. -/
private lemma dummy_identity_invariant_level_fold
    (P : FighterParams) (d : ℕ) (event : Option TimedEvent) (levels : List ℕ)
    (h_nodup : levels.Nodup)
    (state : FighterState)
    (h_event : match event with | some e => e.1 = state.tick | none => True)
    (h_good : DummyIdentityInvariant d state)
    (h_unprocessed : ∀ a ∈ state.allocated, a.level ∈ levels → a.candidate.2 < state.tick) :
    DummyIdentityInvariant d
      (levels.foldl (fun s l ↦ fighterProcessLevel P d l event s) state) := by
  induction levels generalizing state with
  | nil => exact h_good
  | cons l levels ih =>
    obtain ⟨hl, hlevels⟩ := List.nodup_cons.mp h_nodup
    have hnext : DummyIdentityInvariant d (fighterProcessLevel P d l event state) := by
      refine dummy_identity_invariant_processLevel
        P d l event h_good h_event ?_
      cases event with
      | none => trivial
      | some e =>
        intro a ha hal
        have hle := h_unprocessed a ha (hal ▸ List.mem_cons_self)
        dsimp only at h_event
        omega
    have hframe :=
      processLevel_tick_allocated
        P d l event state
    refine ih hlevels _ ?_ hnext ?_
    · simpa only [hframe.1] using h_event
    intro a ha hlevel
    rw [hframe.1]
    rcases hframe.2 a ha with ha | hal
    · exact h_unprocessed a ha (List.mem_cons_of_mem l hlevel)
    · exact (hl (hal ▸ hlevel)).elim

/-- The transition function `fighter_actions` preserves the identity invariants across a single
  tick. -/
private lemma dummy_identity_invariant_actions
    (P : FighterParams) (d tick : ℕ)
    (h_good : DummyIdentityInvariant d (fighterState P d tick)) :
    DummyIdentityInvariant d (fighter_actions P d (tick + 1) (fighterState P d tick)) := by
  have hclock :=
    fighterState_tick
      P d tick
  unfold fighter_actions
  split
  · simp [DummyIdentityInvariant,
      initialFighterState, FighterState.activeAt]
  · let current := { fighterState P d tick with
        tick := tick + 1, schedule := masterState P.B (tick + 1) }
    let event := eventAt P.B (tick + 1)
    let owner := event.bind (fun e ↦ fighterOwner d e.2.2.1.length)
    let levels := (current.active.map FighterPhase.level ++ owner.toList).eraseDups
    have hnodup : (levels.mergeSort (· ≤ ·)).Nodup := by
      rw [List.nodup_mergeSort]
      exact nodup_eraseDups_list _
    have hevent : match event with | some e => e.1 = tick + 1 | none => True := by
      dsimp only [event]
      cases he : eventAt P.B (tick + 1) with
      | none => trivial
      | some e => exact (canonical_enumeration_spec_sound P.B he).1
    have hcurrent :
        DummyIdentityInvariant d current :=
      dummy_identity_invariant_advance
        d (tick + 1) (masterState P.B (tick + 1)) (fighterState P d tick)
        h_good (by omega)
    apply dummy_identity_invariant_level_fold
      P d event (levels.mergeSort (· ≤ ·)) hnodup current hevent hcurrent
    intro a ha _
    have hle := h_good.2.2.1 a ha
    change a.candidate.2 < tick + 1
    omega

/-- Induction over all ticks establishes the identity invariants for the reachable states. -/
private lemma dummy_identity_invariant_state
    (P : FighterParams) (d tick : ℕ) :
    DummyIdentityInvariant d (fighterState P d tick) := by
  induction tick with
  | zero => exact dummy_identity_invariant_initial d
  | succ t ih => exact dummy_identity_invariant_actions P d t ih

/-- No two dummy allocations share the same phase identity. -/
private lemma dummy_identities_nodup
    (P : FighterParams) (d tick : ℕ) :
    (((fighterState P d tick).allocated.filter
      (fun a ↦ decide (a.kind = .dummy))).map
        (fun a ↦ (a.level, a.candidate))).Nodup := by
  exact (dummy_identity_invariant_state P d tick).1

/-- Distinct dummy identities inject into the recorded starts at their level. -/
private lemma dummy_count_le_started
    (started : List (ℕ × Candidate))
    (allocated : List AllocatedDirective) (l : ℕ)
    (hhistory : ∀ a ∈ allocated, a.kind = .dummy →
      (a.level, a.candidate) ∈ started)
    (hnodup : ((allocated.filter
      (fun a ↦ decide (a.kind = .dummy))).map
        (fun a ↦ (a.level, a.candidate))).Nodup) :
    (allocated.filter
      (fun a ↦ decide (a.level = l ∧ a.kind = .dummy))).length ≤
      (started.filter (fun entry ↦ entry.1 == l)).length := by
  let ids := (allocated.filter
    (fun a ↦ decide (a.kind = .dummy))).map
      (fun a ↦ (a.level, a.candidate))
  have hsub : ids.filter (fun e ↦ e.1 == l) ⊆
      started.filter (fun e ↦ e.1 == l) := by
    intro e he
    obtain ⟨hem, hel⟩ := List.mem_filter.mp he
    change e ∈ (allocated.filter
      (fun a ↦ decide (a.kind = .dummy))).map
        (fun a ↦ (a.level, a.candidate)) at hem
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hem
    obtain ⟨ham, hak⟩ := List.mem_filter.mp ha
    exact List.mem_filter.mpr
      ⟨hhistory a ham (by simpa using hak), hel⟩
  have hc := (List.Nodup.filter
    (fun e : ℕ × Candidate ↦ e.1 == l) hnodup).length_le_of_subset hsub
  simpa only [ids, List.filter_map, Function.comp_def,
    List.filter_filter, List.length_map,
    Bool.beq_eq_decide_eq, ← Bool.decide_and, and_comm] using hc

/-- The number of dummy allocations at a level is bounded by its recorded phase starts. -/
lemma fighterDirectiveCount_dummy_le_fighterPhaseCount
    (P : FighterParams) (d l tick : ℕ) :
    fighterDirectiveCount P d l tick .dummy ≤ fighterPhaseCount P d l tick := by
  unfold fighterDirectiveCount fighterPhaseCount
  exact dummy_count_le_started _ _ l
    (dummy_identity_mem_started P d tick)
    (dummy_identities_nodup P d tick)

/-- Every allocation and every active phase of `s` is recorded in the list of phase starts. -/
private def fuelHistoryInvariant (s : FighterState) : Prop :=
  (∀ a ∈ s.allocated, (a.level, a.candidate) ∈ s.started) ∧
  (∀ p ∈ s.active, (p.level, p.candidate) ∈ s.started)

/-- The empty initial state satisfies the allocation and active-phase history invariant. -/
private lemma fuel_history_initial
    (d : ℕ) : fuelHistoryInvariant (initialFighterState d) := by
  dsimp [fuelHistoryInvariant, initialFighterState]
  exact ⟨fun a ha ↦ by simp at ha, fun p hp ↦ by simp at hp⟩

/-- Cancelling a phase preserves membership of allocation and active identities
in the start history. -/
private lemma fuel_history_cancel
    (d l : ℕ) (reason : PhaseEnd) (owner : ℕ) (s : FighterState)
    (hs : fuelHistoryInvariant s) :
    fuelHistoryInvariant (fighterCancel d l reason owner s) := by
  unfold fighterCancel
  split
  · exact hs
  · refine ⟨?_, ?_⟩
    · intro a ha
      exact hs.1 a ha
    · intro p hp
      have hp2 := List.mem_filter.mp hp
      exact hs.2 p hp2.1

/-- A list fold preserves every predicate preserved by its individual updates. -/
lemma FighterState.invariant_foldl
    {α : Type} (I : FighterState → Prop)
    (f : FighterState → α → FighterState)
    (hf : ∀ s x, I s → I (f s x))
    (xs : List α) (s : FighterState) (hs : I s) :
    I (xs.foldl f s) := by
  induction xs generalizing s with
  | nil => exact hs
  | cons x xs ih => exact ih (f s x) (hf s x hs)

/-- Aborting higher levels preserves the allocation and active-phase history invariant. -/
private lemma fuel_history_abortAbove
    (d l : ℕ) (s : FighterState)
    (hs : fuelHistoryInvariant s) :
    fuelHistoryInvariant (fighterAbortAbove d l s) := by
  dsimp [fighterAbortAbove]
  apply FighterState.invariant_foldl
  · intro st p hst
    split
    · exact fuel_history_cancel _ _ _ _ _ hst
    · exact hst
  · exact hs

/-- Installing a phase whose identity has been recorded preserves the history invariant. -/
private lemma fuel_history_putPhase
    (d : ℕ) (s : FighterState) (p : FighterPhase)
    (hs : fuelHistoryInvariant s)
    (hp : (p.level, p.candidate) ∈ s.started) :
    fuelHistoryInvariant (s.putPhase d p) := by
  dsimp [fuelHistoryInvariant, FighterState.putPhase] at hs ⊢
  constructor
  · exact hs.1
  · intro q hq
    simp only [List.mem_cons, List.mem_filter] at hq
    cases hq with
    | inl hq =>
      subst hq
      exact hp
    | inr hq =>
      exact hs.2 q hq.1

/-- Installing a phase and recording its identity preserves the history invariant. -/
private lemma fuel_history_putPhase_started
    (d : ℕ) (s : FighterState) (p : FighterPhase)
    (hs : fuelHistoryInvariant s) :
    fuelHistoryInvariant { s.putPhase d p with
      started := s.started ++ [(p.level, p.candidate)] } := by
  dsimp [fuelHistoryInvariant] at hs ⊢
  constructor
  · intro a ha
    dsimp [FighterState.putPhase] at ha
    have ha' : (a.level, a.candidate) ∈ s.started := hs.1 a ha
    exact List.mem_append_left [(p.level, p.candidate)] ha'
  · intro q hq
    dsimp [FighterState.putPhase] at hq
    cases List.mem_cons.mp hq with
    | inl h_eq =>
      subst h_eq
      exact List.mem_append_right s.started (List.mem_singleton_self _)
    | inr h_mem =>
      have h_mem2 : q ∈ s.active := List.mem_of_mem_filter h_mem
      have ha' : (q.level, q.candidate) ∈ s.started := hs.2 q h_mem2
      exact List.mem_append_left [(p.level, p.candidate)] ha'

/-- `fighterStartPhase` preserves the allocation and active-phase history invariant. -/
private lemma fuel_history_startPhase
    (P : FighterParams) (d l : ℕ) (c : Candidate) (s : FighterState)
    (hs : fuelHistoryInvariant s) :
    fuelHistoryInvariant (fighterStartPhase P d l c s) := by
  unfold fighterStartPhase
  have h1 := fuel_history_cancel d l .replaced l s hs
  have h2 := fuel_history_abortAbove d l _ h1
  exact fuel_history_putPhase_started d _ _ h2

/-- Allocation preserves the history invariant without changing the list of phase starts. -/
private lemma fuel_history_allocate
    (d l : ℕ) (kind : DirectiveKind) (target : ℕ) (output : BitString) (s : FighterState)
    (hs : fuelHistoryInvariant s) :
    fuelHistoryInvariant (fighterAllocate d l kind target output s).1 ∧
    (fighterAllocate d l kind target output s).1.started = s.started := by
  dsimp only [fighterAllocate]
  cases h_act : s.activeAt d l with
  | none =>
    dsimp only
    exact ⟨hs, rfl⟩
  | some phase =>
    dsimp only
    have hp_mem : phase ∈ s.active := List.mem_of_find?_eq_some h_act
    have hp_level : phase.level = l := by
      have h_some := List.find?_some h_act
      exact beq_iff_eq.mp h_some
    cases h_fresh : if target = 0 then none else (fighterInputs d (target - 1)).find? (fun p ↦
      !s.allocated.any (fun a ↦ a.input == p)) with
    | none =>
      dsimp only
      have h_failed : fuelHistoryInvariant { s with failed := true } := hs
      constructor
      · exact fuel_history_cancel d l .saturated l _ h_failed
      · dsimp [fighterCancel, FighterState.activeAt]
        have h_eq : s.active.find? (fun phase ↦ phase.level == l) = some phase := h_act
        rw [h_eq]
    | some p =>
      dsimp only
      have h_alloc : fuelHistoryInvariant { s with allocated := s.allocated ++
          [{ level := l, candidate := phase.candidate, tick := s.tick,
             kind := kind, target := target, input := p, output := output }] } := by
        dsimp [fuelHistoryInvariant] at hs ⊢
        constructor
        · intro a ha
          cases List.mem_append.mp ha with
          | inl h => exact hs.1 a h
          | inr h =>
            obtain rfl := List.mem_singleton.mp h
            dsimp only
            have h_started : (phase.level, phase.candidate) ∈ s.started := hs.2 phase hp_mem
            rw [hp_level] at h_started
            exact h_started
        · exact hs.2
      constructor
      · exact fuel_history_abortAbove d l _ h_alloc
      · exact fighterAbortAbove_started d l _

/-- `fighterPayoff` preserves the allocation and active-phase history invariant. -/
private lemma fuel_history_payoff
    (P : FighterParams) (d l : ℕ) (q : Coordinate) (s : FighterState)
    (hs : fuelHistoryInvariant s) :
    fuelHistoryInvariant (fighterPayoff P d l q s) := by
  unfold fighterPayoff
  split
  · exact hs
  · rename_i phase hphase
    split_ifs with h
    · have h_alloc := fuel_history_allocate d l .payoff q.2 q.1 s hs
      cases he : fighterAllocate d l .payoff q.2 q.1 s with
      | mk next success =>
        rw [he] at h_alloc
        cases success
        · exact h_alloc.1
        · have hn : fuelHistoryInvariant next := h_alloc.1
          unfold fuelHistoryInvariant
          refine ⟨?_, ?_⟩
          · intro a ha
            dsimp
            exact h_alloc.2 ▸ (hn.1 a ha)
          · intro p hp
            dsimp at hp ⊢
            obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hp
            exact h_alloc.2 ▸ (hn.2 old hold)
    · exact hs

/-- `fighterFulfillReady` preserves the allocation and active-phase history invariant. -/
private lemma fuel_history_fulfillReady
    (P : FighterParams) (d l : ℕ) (s : FighterState)
    (hs : fuelHistoryInvariant s) :
    fuelHistoryInvariant (fighterFulfillReady P d l s) := by
  unfold fighterFulfillReady
  cases h : s.activeAt d l with
  | none => simpa [h] using hs
  | some phase =>
      exact FighterState.invariant_foldl fuelHistoryInvariant
        (fun st q ↦ fighterPayoff P d l q st)
        (fun st q hst ↦ fuel_history_payoff P d l q st hst) phase.pending s hs

/-- `fighterFuelUnit` preserves the allocation and active-phase history invariant. -/
private lemma fuel_history_fuelUnit
    (P : FighterParams) (d l : ℕ) (q : Coordinate) (s : FighterState)
    (hs : fuelHistoryInvariant s) :
    fuelHistoryInvariant (fighterFuelUnit P d l q s) := by
  unfold fighterFuelUnit
  cases h_active : s.activeAt d l with
  | none => exact hs
  | some phase =>
    dsimp only
    split
    · let charged : FighterPhase := { phase with controlledRemaining := phase.controlledRemaining
        - 1 }
      have h_phase_mem : phase ∈ s.active := by
        exact List.mem_of_find?_eq_some h_active
      have h_phase_started : (phase.level, phase.candidate) ∈ s.started := hs.2 _ h_phase_mem
      have h_charged_started : (charged.level, charged.candidate) ∈ s.started := h_phase_started
      have hs_put := fuel_history_putPhase d s charged hs h_charged_started
      let index := fighterFreshString d (phase.indices[(phase.game d).coordinates.idxOf q]?.getD [])
      let output := pairCode (triple q.1 (q.2 - d) phase.candidate.1) index
      have h_alloc_res := fuel_history_allocate d l .fuel (levelUpper l + d) output (s.putPhase d
        charged) hs_put
      cases he : fighterAllocate d l .fuel (levelUpper l + d) output (s.putPhase d charged) with
      | mk next success =>
        have h_alloc_1 : fuelHistoryInvariant next := by
          have h_tmp := h_alloc_res.1
          rw [he] at h_tmp
          exact h_tmp
        have h_alloc_2 : next.started = (s.putPhase d charged).started := by
          have h_tmp := h_alloc_res.2
          rw [he] at h_tmp
          exact h_tmp
        cases success
        · exact h_alloc_1
        · dsimp only
          let inserted : FighterPhase := (charged.insertIndex d q index).fundRequests d
            next.fulfilled
          have h_inserted_started : (inserted.level, inserted.candidate) ∈ next.started := by
            change (charged.level, charged.candidate) ∈ next.started
            rw [h_alloc_2]
            exact h_charged_started
          have h_next_put := fuel_history_putPhase d next inserted h_alloc_1 h_inserted_started
          exact fuel_history_fulfillReady P d l (next.putPhase d inserted) h_next_put
    · exact hs

/-- `fighterFuelUnits` preserves the allocation and active-phase history invariant. -/
private lemma fuel_history_fuelUnits
    (P : FighterParams) (d l : ℕ) (q : Coordinate) (count : ℕ) (s : FighterState)
    (hs : fuelHistoryInvariant s) :
    fuelHistoryInvariant (fighterFuelUnits P d l q count s) := by
  induction count generalizing s with
  | zero => exact hs
  | succ count ih => exact ih _ (fuel_history_fuelUnit P d l q s hs)

/-- `fighterOpponent` preserves the allocation and active-phase history invariant. -/
private lemma fuel_history_opponent
    (P : FighterParams) (d l : ℕ) (event : ProgramEvent) (s : FighterState)
    (hs : fuelHistoryInvariant s) :
    fuelHistoryInvariant (fighterOpponent P d l event s) := by
  unfold fighterOpponent
  cases h_phase : s.activeAt d l with
  | none => exact hs
  | some phase =>
    dsimp only
    cases h_tuple : fighterOpponentTuple d phase event with
    | none => exact hs
    | some pair =>
      dsimp only
      split
      · exact hs
      · split
        · exact fuel_history_cancel _ _ _ _ _ hs
        · have h_phase_mem : phase ∈ s.active := List.mem_of_find?_eq_some h_phase
          have h_started : (phase.level, phase.candidate) ∈ s.started := hs.2 phase h_phase_mem
          let inserted := phase.insertIndex d pair.fst pair.snd
          let next := { inserted with
            opponentRemaining := phase.opponentRemaining - 1
            buffer := (phase.game d).addCounters phase.buffer (phase.unitVector d pair.fst) }
          have h_inserted_started :
              ((next.fundRequests d s.fulfilled).level,
                (next.fundRequests d s.fulfilled).candidate) ∈ s.started := by
            change (phase.level, phase.candidate) ∈ s.started
            exact h_started
          exact fuel_history_fulfillReady
            P d l (s.putPhase d (next.fundRequests d s.fulfilled))
            (fuel_history_putPhase
              d s (next.fundRequests d s.fulfilled) hs h_inserted_started)

/-- Issuing a dummy directive preserves membership of allocation and active-phase
identities in the start history. -/
private lemma fuel_history_dummy
    (d l : ℕ) (s : FighterState)
    (hs : fuelHistoryInvariant s) :
    fuelHistoryInvariant (fighterDummy d l s) := by
  unfold fighterDummy
  cases hactive : s.activeAt d l with
  | none => exact hs
  | some phase =>
    dsimp only
    cases hdummy : phase.dummy with
    | none => exact hs
    | some output =>
      dsimp only
      split
      · exact hs
      · have halloc :=
          fuel_history_allocate
            d l .dummy (levelInput d l) output s hs
        cases he : fighterAllocate d l .dummy (levelInput d l) output s with
        | mk next success =>
          rw [he] at halloc
          cases success with
          | false => exact halloc.1
          | true =>
            apply fuel_history_putPhase
              d next _ halloc.1
            change (phase.level, phase.candidate) ∈ next.started
            rw [halloc.2]
            exact hs.2 phase (List.mem_of_find?_eq_some hactive)

/-- `fighterFlushBuffer` preserves the allocation and active-phase history invariant. -/
private lemma fuel_history_flushBuffer
    (d l : ℕ) (s next : FighterState)
    (hs : fuelHistoryInvariant s)
    (hn : fighterFlushBuffer d l s = some next) :
    fuelHistoryInvariant next := by
  dsimp [fighterFlushBuffer] at hn
  cases h_active : s.activeAt d l with
  | none =>
    rw [h_active] at hn
    dsimp [bind] at hn
    contradiction
  | some phase =>
    rw [h_active] at hn
    dsimp [bind] at hn
    split at hn
    · next h_if =>
      injection hn with h_eq
      rw [← h_eq]
      apply fuel_history_putPhase d s _ hs
      have h_phase_active : phase ∈ s.active := by
        exact List.mem_of_find?_eq_some h_active
      exact hs.2 phase h_phase_active
    · contradiction

/-- `fighterStrategyMove` preserves the allocation and active-phase history invariant. -/
private lemma fuel_history_strategyMove
    (P : FighterParams) (d l : ℕ) (s next : FighterState)
    (hs : fuelHistoryInvariant s)
    (hn : fighterStrategyMove P d l s = some next) :
    fuelHistoryInvariant next := by
  cases hphase : s.activeAt d l with
  | none =>
    simp [fighterStrategyMove, hphase] at hn
  | some phase =>
    simp only [fighterStrategyMove, hphase, bind, Option.bind_some] at hn
    split at hn
    · cases hm : (phase.game d).strategy (phase.official d) with
      | none =>
        simp [hm] at hn
      | some move =>
        simp only [hm, Option.bind_some] at hn
        split at hn
        · let mid := (phase.game d).coordinates.zipIdx.foldl
            (fun s (q, i) ↦ fighterFuelUnits P d l q (move[i]?.getD 0) s) s
          change (match mid.activeAt d l with
          | none => some mid
          | some live => some (mid.putPhase d { live with
              officialCode := ((phase.game d).afterMove (phase.official d) move).encode })) = some
                next at hn
          have h_mid : fuelHistoryInvariant mid := by
            have hfold : ∀ (xs : List (Coordinate × ℕ)) (s' : FighterState),
              fuelHistoryInvariant s' →
              fuelHistoryInvariant
                (xs.foldl (fun s (q, i) ↦ fighterFuelUnits P d l q (move[i]?.getD 0) s) s') := by
              intro xs s' hs'
              induction xs generalizing s' with
              | nil => exact hs'
              | cons x xs ih => exact ih _ (fuel_history_fuelUnits P d l x.1 (move[x.2]?.getD 0)
                s' hs')
            exact hfold _ _ hs
          cases hlive : mid.activeAt d l with
          | none =>
            simp only [hlive, Option.some.injEq] at hn
            rw [← hn]
            exact h_mid
          | some live =>
            simp only [hlive, Option.some.injEq] at hn
            rw [← hn]
            apply fuel_history_putPhase
            · exact h_mid
            · have h_find : mid.active.find? (fun p : FighterPhase ↦ p.level == l) = some live := by
                simpa only [FighterState.activeAt] using hlive
              have h_mem : live ∈ mid.active := List.mem_of_find?_eq_some h_find
              have h_eq : ({ live with officialCode := ((phase.game d).afterMove (phase.official
                d) move).encode } : FighterPhase).candidate = live.candidate := rfl
              have h_eq_l : ({ live with officialCode := ((phase.game d).afterMove (phase.official
                d) move).encode } : FighterPhase).level = live.level := rfl
              rw [h_eq, h_eq_l]
              exact h_mid.2 live h_mem
        · simp at hn
    · simp at hn

/-- `fighterLevelAction` preserves the allocation and active-phase history invariant. -/
private lemma fuel_history_levelAction
    (P : FighterParams) (d l : ℕ) (s next : FighterState)
    (hs : fuelHistoryInvariant s)
    (hn : fighterLevelAction P d l s = some next) :
    fuelHistoryInvariant next := by
  unfold fighterLevelAction at hn
  cases h_phase : s.activeAt d l with
  | none =>
    rw [h_phase] at hn
    dsimp [bind, Option.bind] at hn
    contradiction
  | some phase =>
    rw [h_phase] at hn
    dsimp [bind, Option.bind] at hn
    split at hn
    · injection hn with hn_eq
      rw [← hn_eq]
      exact fuel_history_dummy d l s hs
    · split at hn
      · injection hn with hn_eq
        rw [← hn_eq]
        exact fuel_history_payoff P d l _ s hs
      · cases h_flush : fighterFlushBuffer d l s with
        | none =>
          rw [h_flush] at hn
          dsimp [bind, Option.bind] at hn
          exact fuel_history_strategyMove P d l s next hs hn
        | some next_flush =>
          rw [h_flush] at hn
          dsimp [bind, Option.bind] at hn
          injection hn with hn_eq
          rw [← hn_eq]
          exact fuel_history_flushBuffer d l s next_flush hs h_flush

/-- `fighterClosure` preserves the allocation and active-phase history invariant. -/
private lemma fuel_history_closure
    (P : FighterParams) (d l fuel : ℕ) (s : FighterState)
    (hs : fuelHistoryInvariant s) :
    fuelHistoryInvariant (fighterClosure P d l fuel s) := by
  induction fuel generalizing s with
  | zero => exact hs
  | succ f ih =>
    simp only [fighterClosure]
    cases ha : fighterLevelAction P d l s
    · exact hs
    · exact ih _ (fuel_history_levelAction P d l s _ hs ha)

/-- `fighterProcessLevel` preserves the allocation and active-phase history invariant. -/
private lemma fuel_history_processLevel
    (P : FighterParams) (d l : ℕ) (event : Option TimedEvent) (s : FighterState)
    (hs : fuelHistoryInvariant s) :
    fuelHistoryInvariant (fighterProcessLevel P d l event s) := by
  dsimp [fighterProcessLevel, fighterCloseLevel]
  have hchecked := fuel_history_fulfillReady P d l s hs
  cases event with
  | none =>
    exact fuel_history_closure P d l _ _ hchecked
  | some e =>
    dsimp
    split
    · have hstart := fuel_history_startPhase P d l (e.2.2.1, e.1) _ hchecked
      exact fuel_history_closure P d l _ _ hstart
    · have hopp := fuel_history_opponent P d l e.2.2 _ hchecked
      exact fuel_history_closure P d l _ _ hopp

/-- `fighter_actions` preserves the allocation and active-phase history invariant. -/
private lemma fuel_history_actions
    (P : FighterParams) (d tick : ℕ) (s : FighterState)
    (hs : fuelHistoryInvariant s) :
    fuelHistoryInvariant (fighter_actions P d tick s) := by
  dsimp [fighter_actions]
  split_ifs with hd
  · exact fuel_history_initial d
  · generalize h_curr : { s with tick := tick, schedule := masterState P.B tick } = current
    have hs_curr : fuelHistoryInvariant current := by
      subst h_curr
      rcases hs with ⟨hs1, hs2⟩
      exact ⟨hs1, hs2⟩
    apply FighterState.invariant_foldl
      fuelHistoryInvariant
      (fun s l ↦ fighterProcessLevel P d l (eventAt P.B tick) s)
    · intro s l hsl
      exact fuel_history_processLevel P d l (eventAt P.B tick) s hsl
    · exact hs_curr

/-- Every fuel allocation originates from a recorded phase start. -/
lemma fighterState_allocated_fuel_mem_started
    (P : FighterParams) (d tick : ℕ) :
    ∀ a ∈ (fighterState P d tick).allocated, a.kind = .fuel →
      (a.level, a.candidate) ∈ (fighterState P d tick).started := by
  have h_ind : fuelHistoryInvariant (fighterState P d tick) := by
    induction tick with
    | zero =>
      dsimp [fighterState]
      exact fuel_history_initial d
    | succ t ih =>
      exact fuel_history_actions P d (t + 1) _ ih
  intro a ha _
  exact h_ind.1 a ha

end Kolmogorov.Milovanov
