/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Construction.Accounting.TargetRange

/-!
# Provenance and uniqueness of dummy allocations

The phase-count bound charges each dummy allocation to the phase that issued it.
This module proves that every such identity occurs in the phase-start log and defines
`DummyIdentityInvariant`, which combines uniqueness of dummy identities with freshness
of unissued dummies and bounds on candidate timestamps. The invariant is preserved by
cancellation, allocation, payoff, fulfillment, and dummy issuance. `DummyIdentities`
extends these preservation results to the remaining actions, and `FuelHistory` uses
them to bound dummy allocations by recorded starts in the phase-count argument
(blueprint node `constr:phasecount`).
-/

namespace Kolmogorov.Milovanov

private lemma start_log_covers_cancel
    (d l : ℕ) (reason : PhaseEnd) (cause : ℕ) (state : FighterState)
    (hs : FighterStartLogCovers state) :
    FighterStartLogCovers (fighterCancel d l reason cause state) := by
  dsimp only [fighterCancel]
  cases h : state.activeAt d l
  · exact hs
  · rcases hs with ⟨hactive, halloc⟩
    constructor
    · intro p hp
      have hp' := List.mem_of_mem_filter hp
      exact hactive p hp'
    · exact halloc

private lemma start_log_covers_abort_fold
    (d l : ℕ) (state : FighterState) (hs : FighterStartLogCovers state) (L : List FighterPhase) :
    FighterStartLogCovers
      (L.foldl (fun s phase ↦
        if l < phase.level then fighterCancel d phase.level .aborted l s else s) state) := by
  induction L generalizing state with
  | nil => exact hs
  | cons phase L ih =>
    apply ih
    dsimp only
    split
    · exact start_log_covers_cancel _ _ _ _ _ hs
    · exact hs

private lemma start_log_covers_abort
    (d l : ℕ) (state : FighterState) (hs : FighterStartLogCovers state) :
    FighterStartLogCovers (fighterAbortAbove d l state) := by
  exact start_log_covers_abort_fold d l state hs state.active

private lemma start_log_covers_allocate_payoff
    (d l target : ℕ) (output : BitString) (state : FighterState)
    (hs : FighterStartLogCovers state) :
    FighterStartLogCovers (fighterAllocate d l .payoff target output state).1 := by
  dsimp only [fighterAllocate]
  cases h : state.activeAt d l
  · exact hs
  · dsimp only
    split
    · exact start_log_covers_cancel _ _ _ _ _ hs
    · apply start_log_covers_abort
      rcases hs with ⟨hactive, halloc⟩
      constructor
      · exact hactive
      · intro a ha hkind
        have h_mem_append : a ∈ state.allocated ∨ a ∈ [_] := List.mem_append.mp ha
        cases h_mem_append with
        | inl ha => exact halloc a ha hkind
        | inr ha =>
          have ha' : a = _ := List.mem_singleton.mp ha
          subst ha'
          contradiction

private lemma start_log_covers_payoff
    (P : FighterParams) (d l : ℕ) (q : Coordinate) (state : FighterState)
    (hs : FighterStartLogCovers state) :
    FighterStartLogCovers (fighterPayoff P d l q state) := by
  dsimp only [fighterPayoff]
  cases h : state.activeAt d l
  · exact hs
  · dsimp only
    split
    · have h1 := start_log_covers_allocate_payoff d l q.2 q.1 state hs
      cases h2 : fighterAllocate d l .payoff q.2 q.1 state
      rename_i next success
      rw [h2] at h1
      dsimp only
      split
      · rcases h1 with ⟨hactive, halloc⟩
        constructor
        · intro p hp
          dsimp only at hp
          obtain ⟨p', hp', rfl⟩ := List.mem_map.mp hp
          dsimp only
          exact hactive p' hp'
        · intro a ha
          exact halloc a ha
      · exact h1
    · exact hs

private lemma start_log_covers_fulfill_fold
    (P : FighterParams) (d l : ℕ) (state : FighterState)
    (hs : FighterStartLogCovers state) (L : List Coordinate) :
    FighterStartLogCovers (L.foldl (fun s q ↦ fighterPayoff P d l q s) state) := by
  induction L generalizing state with
  | nil => exact hs
  | cons q L ih =>
    apply ih
    exact start_log_covers_payoff P d l q state hs

/-- Fulfilling pending requests preserves the provenance of active phases and dummies. -/
private lemma start_log_covers_fulfill_ready
    (P : FighterParams) (d l : ℕ) (s : FighterState)
    (hs : FighterStartLogCovers s) :
    FighterStartLogCovers
      (fighterFulfillReady P d l s) := by
  dsimp only [fighterFulfillReady]
  cases h : s.activeAt d l
  · exact hs
  · exact start_log_covers_fulfill_fold P d l s hs _

/-- Processing an opponent event preserves the start-log invariant. -/
private lemma start_log_covers_opponent
    (P : FighterParams) (d l : ℕ) (e : ProgramEvent) (s : FighterState)
    (hs : FighterStartLogCovers s) :
    FighterStartLogCovers
      (fighterOpponent P d l e s) := by
  unfold fighterOpponent
  cases hactive : s.activeAt d l with
  | none => exact hs
  | some phase =>
    dsimp only
    cases htuple : fighterOpponentTuple d phase e with
    | none => exact hs
    | some q_index =>
      rcases q_index with ⟨q, index⟩
      dsimp only
      split
      · exact hs
      · split
        · exact start_log_covers_cancel _ _ _ _ _ hs
        · apply start_log_covers_fulfill_ready
          refine ⟨?_, hs.2⟩
          intro p hp
          rcases List.mem_cons.mp hp with rfl | hp
          · exact hs.1 phase (List.mem_of_find?_eq_some hactive)
          · exact hs.1 p (List.mem_of_mem_filter hp)

/-- Starting a phase records its identity and preserves all surviving provenance. -/
private lemma start_log_covers_start_phase
    (P : FighterParams) (d l : ℕ) (candidate : Candidate) (s : FighterState)
    (hs : FighterStartLogCovers s) :
    FighterStartLogCovers
      (fighterStartPhase P d l candidate s) := by
  dsimp only [fighterStartPhase, FighterState.putPhase, FighterStartLogCovers] at hs ⊢
  have hcancel (j cause : ℕ) (reason : PhaseEnd) (t : FighterState) :
      (fighterCancel d j reason cause t).allocated = t.allocated ∧
      (fighterCancel d j reason cause t).started = t.started ∧
      (∀ p ∈ (fighterCancel d j reason cause t).active, p ∈ t.active) := by
    unfold fighterCancel
    split
    · exact ⟨rfl, rfl, fun _ h ↦ h⟩
    · exact ⟨rfl, rfl, fun _ hp ↦ List.mem_of_mem_filter hp⟩
  have habort (t : FighterState) :
      (fighterAbortAbove d l t).allocated = t.allocated ∧
      (fighterAbortAbove d l t).started = t.started ∧
      (∀ p ∈ (fighterAbortAbove d l t).active, p ∈ t.active) := by
    have hfold (ps : List FighterPhase) (t : FighterState) :
        (ps.foldl (fun s p ↦ if l < p.level then
          fighterCancel d p.level .aborted l s else s) t).allocated = t.allocated ∧
        (ps.foldl (fun s p ↦ if l < p.level then
          fighterCancel d p.level .aborted l s else s) t).started = t.started ∧
        (∀ p ∈ (ps.foldl (fun s p ↦ if l < p.level then
          fighterCancel d p.level .aborted l s else s) t).active, p ∈ t.active) := by
      induction ps generalizing t with
      | nil => exact ⟨rfl, rfl, fun _ h ↦ h⟩
      | cons p ps ih =>
        rw [List.foldl_cons]
        have ih' := ih (if l < p.level then fighterCancel d p.level .aborted l t else t)
        have hallocated : (if l < p.level then
            fighterCancel d p.level .aborted l t else t).allocated = t.allocated := by
          split_ifs
          · exact (hcancel _ _ _ _).1
          · rfl
        have hstarted : (if l < p.level then
            fighterCancel d p.level .aborted l t else t).started = t.started := by
          split_ifs
          · exact (hcancel _ _ _ _).2.1
          · rfl
        have hmem (x) (hx : x ∈ (if l < p.level then
            fighterCancel d p.level .aborted l t else t).active) : x ∈ t.active := by
          split_ifs at hx
          · exact (hcancel _ _ _ _).2.2 _ hx
          · exact hx
        exact ⟨ih'.1.trans hallocated, ih'.2.1.trans hstarted, fun _ h ↦ hmem _ (ih'.2.2 _ h)⟩
    exact hfold _ _
  let waiting := fighterAbortAbove d l (fighterCancel d l .replaced l s)
  let phase := fighter_construction P d l candidate waiting
  let next := { waiting with
    active := phase :: waiting.active.filter (fun p ↦ p.level != phase.level) }
  have hactive (p : FighterPhase) : p ∈ next.active ↔
      p = phase ∨ p ∈ waiting.active ∧ (p.level != phase.level) = true := by
    dsimp only [next]
    rw [List.mem_cons, List.mem_filter]
  have h_waiting_allocated : waiting.allocated = s.allocated := by
    dsimp only [waiting]
    rw [(habort _).1, (hcancel _ _ _ _).1]
  have h_waiting_started : waiting.started = s.started := by
    dsimp only [waiting]
    rw [(habort _).2.1, (hcancel _ _ _ _).2.1]
  have h_waiting_active (p : FighterPhase) (hp : p ∈ waiting.active) : p ∈ s.active := by
    dsimp only [waiting] at hp
    exact (hcancel _ _ _ _).2.2 _ ((habort _).2.2 _ hp)
  refine ⟨fun p hp ↦ ?_, fun a ha h_dummy ↦ ?_⟩
  · have hp_next : p ∈ next.active := hp
    rw [hactive] at hp_next
    cases hp_next with
    | inl h_eq =>
      subst h_eq
      have h_phase : phase.level = l ∧ phase.candidate = candidate := by
        dsimp only [phase, fighter_construction]
        exact ⟨rfl, rfl⟩
      rw [h_phase.1, h_phase.2]
      apply List.mem_append_right
      exact List.mem_singleton_self _
    | inr h_in =>
      have hp_s := h_waiting_active _ h_in.1
      have hp_started := hs.1 _ hp_s
      apply List.mem_append_left
      rw [h_waiting_started]
      exact hp_started
  · have ha_next : a ∈ next.allocated := ha
    dsimp only [next] at ha_next
    rw [h_waiting_allocated] at ha_next
    have ha_s := hs.2 _ ha_next h_dummy
    apply List.mem_append_left
    rw [h_waiting_started]
    exact ha_s

/-- Preparing a level preserves provenance, including when an event starts a new phase. -/
private lemma start_log_covers_prepare
    (P : FighterParams) (d l : ℕ) (event : Option TimedEvent)
    (s : FighterState)
    (hs : FighterStartLogCovers s) :
    FighterStartLogCovers
      (let checked := fighterFulfillReady P d l s
       match event with
       | none => checked
       | some e =>
         if fighterOwner d e.2.2.1.length = some l ∧
             e.2.2.1.length ≤ levelScale l ∧ P.Admissible d l then
           fighterStartPhase P d l (e.2.2.1, e.1) checked
         else fighterOpponent P d l e.2.2 checked) := by
  have hchecked : FighterStartLogCovers (fighterFulfillReady P d l s) :=
    start_log_covers_fulfill_ready P d l s hs
  cases event with
  | none => exact hchecked
  | some e =>
    dsimp only
    split
    · exact start_log_covers_start_phase P d l _ _ hchecked
    · exact start_log_covers_opponent P d l _ _ hchecked

/-- Installing a phase whose identity is logged preserves provenance. -/
private lemma start_log_covers_put_phase
    (d : ℕ) (s : FighterState) (phase : FighterPhase)
    (hs : FighterStartLogCovers s)
    (hphase : (phase.level, phase.candidate) ∈ s.started) :
    FighterStartLogCovers (s.putPhase d phase) := by
  refine ⟨?_, hs.2⟩
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact hphase
  · exact hs.1 p (List.mem_of_mem_filter hp)

/-- Allocation preserves provenance and leaves the start log unchanged. -/
private lemma start_log_covers_allocate
    (d l : ℕ) (kind : DirectiveKind) (target : ℕ) (output : BitString)
    (s : FighterState)
    (hs : FighterStartLogCovers s) :
    FighterStartLogCovers
        (fighterAllocate d l kind target output s).1 ∧
      (fighterAllocate d l kind target output s).1.started = s.started := by
  have hcancel (j : ℕ) (reason : PhaseEnd) (cause : ℕ) (t : FighterState) :
      (fighterCancel d j reason cause t).started = t.started := by
    unfold fighterCancel
    split <;> rfl
  have habort (t : FighterState) :
      (fighterAbortAbove d l t).started = t.started := by
    have hfold (xs : List FighterPhase) (t : FighterState) :
        (xs.foldl (fun u p ↦
          if l < p.level then fighterCancel d p.level .aborted l u else u) t).started =
            t.started := by
      induction xs generalizing t with
      | nil => rfl
      | cons p xs ih =>
        rw [List.foldl_cons, ih]
        split
        · exact hcancel _ _ _ _
        · rfl
    exact hfold t.active t
  dsimp only [fighterAllocate]
  cases hactive : s.activeAt d l with
  | none => exact ⟨hs, rfl⟩
  | some phase =>
    have hmem : phase ∈ s.active := List.mem_of_find?_eq_some hactive
    have hlevel : phase.level = l := beq_iff_eq.mp
      (List.find?_some (p := fun p : FighterPhase ↦ p.level == l) hactive)
    have hlogged : (l, phase.candidate) ∈ s.started := by
      simpa only [hlevel] using hs.1 phase hmem
    dsimp only
    cases hfresh : (if target = 0 then none else
        (fighterInputs d (target - 1)).find? (fun p ↦
          !s.allocated.any (fun a ↦ a.input == p))) with
    | none =>
      exact ⟨start_log_covers_cancel
        _ _ _ _ _ hs, hcancel _ _ _ _⟩
    | some p =>
      refine ⟨start_log_covers_abort
        _ _ _ ?_, habort _⟩
      refine ⟨hs.1, ?_⟩
      intro a ha hkind
      rcases List.mem_append.mp ha with hold | hnew
      · exact hs.2 a hold hkind
      · obtain rfl := List.mem_singleton.mp hnew
        exact hlogged

/-- Issuing a dummy preserves the logged identity of its phase. -/
private lemma start_log_covers_dummy
    (d l : ℕ) (s : FighterState)
    (hs : FighterStartLogCovers s) :
    FighterStartLogCovers (fighterDummy d l s) := by
  unfold fighterDummy
  cases hactive : s.activeAt d l with
  | none => exact hs
  | some phase =>
    have hlogged := hs.1 phase (List.mem_of_find?_eq_some hactive)
    dsimp only
    cases hdummy : phase.dummy with
    | none => exact hs
    | some output =>
      dsimp only
      split
      · exact hs
      · have ha :=
          start_log_covers_allocate
            d l .dummy (levelInput d l) output s hs
        cases he : fighterAllocate d l .dummy (levelInput d l) output s with
        | mk next success =>
          rw [he] at ha
          dsimp only at ha ⊢
          split
          · apply start_log_covers_put_phase
              d next _ ha.1
            rw [ha.2]
            exact hlogged
          · exact ha.1

/-- Issuing one fuel unit preserves the start-log invariant. -/
private lemma start_log_covers_fuel_unit
    (P : FighterParams) (d l : ℕ) (q : Coordinate) (s : FighterState)
    (hs : FighterStartLogCovers s) :
    FighterStartLogCovers (fighterFuelUnit P d l q s) := by
  unfold fighterFuelUnit
  cases hactive : s.activeAt d l with
  | none => exact hs
  | some phase =>
    have hlogged := hs.1 phase (List.mem_of_find?_eq_some hactive)
    dsimp only
    split
    · let index := fighterFreshString d
        (phase.indices[(phase.game d).coordinates.idxOf q]?.getD [])
      let output := pairCode (triple q.1 (q.2 - d) phase.candidate.1) index
      let charged := { phase with controlledRemaining := phase.controlledRemaining - 1 }
      have hcharged : FighterStartLogCovers
          (s.putPhase d charged) :=
        start_log_covers_put_phase
          d s charged hs hlogged
      have ha :=
        start_log_covers_allocate
          d l .fuel (levelUpper l + d) output (s.putPhase d charged) hcharged
      change FighterStartLogCovers
        (let (next, success) := fighterAllocate d l .fuel (levelUpper l + d) output
            (s.putPhase d charged)
         if success then
           fighterFulfillReady P d l
             (next.putPhase d ((charged.insertIndex d q index).fundRequests d next.fulfilled))
         else next)
      cases he : fighterAllocate d l .fuel (levelUpper l + d) output (s.putPhase d charged) with
      | mk next success =>
        rw [he] at ha
        dsimp only at ha ⊢
        split
        · apply start_log_covers_fulfill_ready
          apply start_log_covers_put_phase
            d next _ ha.1
          rw [ha.2]
          exact hlogged
        · exact ha.1
    · exact hs

/-- A strategy move preserves provenance through fuel issuance and phase updates. -/
private lemma start_log_covers_strategy_move
    (P : FighterParams) (d l : ℕ) (s : FighterState)
    (hs : FighterStartLogCovers s) :
    FighterStartLogCovers
      ((fighterStrategyMove P d l s).getD s) := by
  have hunits (q : Coordinate) (count : ℕ) (t : FighterState)
      (ht : FighterStartLogCovers t) :
      FighterStartLogCovers
        (fighterFuelUnits P d l q count t) := by
    induction count generalizing t with
    | zero => exact ht
    | succ count ih =>
      exact ih _
        (start_log_covers_fuel_unit
          P d l q t ht)
  have hfold (move : CounterMove) (xs : List (Coordinate × ℕ)) (t : FighterState)
      (ht : FighterStartLogCovers t) :
      FighterStartLogCovers
        (xs.foldl (fun u qi ↦ fighterFuelUnits P d l qi.1 (move[qi.2]?.getD 0) u) t) := by
    induction xs generalizing t with
    | nil => exact ht
    | cons qi xs ih => exact ih _ (hunits qi.1 _ t ht)
  cases hactive : s.activeAt d l with
  | none => simpa [fighterStrategyMove, hactive] using hs
  | some phase =>
    simp only [fighterStrategyMove, hactive, bind, Option.bind_some]
    split
    · cases hm : (phase.game d).strategy (phase.official d) with
      | none => exact hs
      | some move =>
        simp only [Option.bind_some]
        split
        · let next := (phase.game d).coordinates.zipIdx.foldl
            (fun t qi ↦ fighterFuelUnits P d l qi.1 (move[qi.2]?.getD 0) t) s
          have hn : FighterStartLogCovers next :=
            hfold move _ s hs
          change FighterStartLogCovers
            ((match next.activeAt d l with
              | none => some next
              | some live => some (next.putPhase d
                  { live with officialCode :=
                    ((phase.game d).afterMove (phase.official d) move).encode })).getD s)
          cases hlive : next.activeAt d l with
          | none => exact hn
          | some live =>
            exact start_log_covers_put_phase
              d next _ hn (hn.1 live (List.mem_of_find?_eq_some hlive))
        · exact hs
    · exact hs

/-- Flushing a buffer preserves phase identities and allocation provenance. -/
private lemma start_log_covers_flush_buffer
    (d l : ℕ) (s : FighterState)
    (hs : FighterStartLogCovers s) :
    FighterStartLogCovers
      ((fighterFlushBuffer d l s).getD s) := by
  cases hactive : s.activeAt d l with
  | none => simpa [fighterFlushBuffer, hactive] using hs
  | some phase =>
    simp only [fighterFlushBuffer, hactive, bind, Option.bind_some]
    split
    · exact start_log_covers_put_phase
        d s _ hs (hs.1 phase (List.mem_of_find?_eq_some hactive))
    · exact hs

/-- Every enabled level action preserves the start-log invariant. -/
private lemma start_log_covers_level_action
    (P : FighterParams) (d l : ℕ) (s : FighterState)
    (hs : FighterStartLogCovers s) :
    FighterStartLogCovers
      ((fighterLevelAction P d l s).getD s) := by
  cases hactive : s.activeAt d l with
  | none => simpa [fighterLevelAction, hactive] using hs
  | some phase =>
    simp only [fighterLevelAction, hactive, bind, Option.bind_some]
    split
    · exact start_log_covers_dummy
        d l s hs
    · split
      · exact start_log_covers_payoff P d l _ s hs
      · cases hflush : fighterFlushBuffer d l s with
        | none =>
          exact start_log_covers_strategy_move
            P d l s hs
        | some next =>
          have h :=
            start_log_covers_flush_buffer d l s hs
          simpa only [hflush] using h

/-- Iterating enabled actions preserves logged phase identities and dummy provenance. -/
private lemma start_log_covers_closure
    (P : FighterParams) (d l fuel : ℕ) (s : FighterState)
    (hs : FighterStartLogCovers s) :
    FighterStartLogCovers
      (fighterClosure P d l fuel s) := by
  induction fuel generalizing s with
  | zero => exact hs
  | succ fuel ih =>
    simp only [fighterClosure]
    cases haction : fighterLevelAction P d l s with
    | none => exact hs
    | some next =>
      have hnext :=
        start_log_covers_level_action P d l s hs
      simp only [haction, Option.getD_some] at hnext
      exact ih next hnext

/-- Every dummy allocation in the fighter state has an identity recorded in the start log. -/
lemma dummy_identity_mem_started
    (P : FighterParams) (d tick : ℕ) :
    ∀ a ∈ (fighterState P d tick).allocated, a.kind = .dummy →
      (a.level, a.candidate) ∈ (fighterState P d tick).started := by
  let I := FighterStartLogCovers
  have hprocess (l : ℕ) (event : Option TimedEvent)
      (s : FighterState) (hs : I s) :
      I (fighterProcessLevel P d l event s) := by
    unfold fighterProcessLevel fighterCloseLevel
    apply start_log_covers_closure
    exact start_log_covers_prepare
      P d l event s hs
  have hfold (event : Option TimedEvent) (xs : List ℕ)
      (s : FighterState) (hs : I s) :
      I (xs.foldl (fun t l ↦ fighterProcessLevel P d l event t) s) := by
    induction xs generalizing s with
    | nil => exact hs
    | cons l xs ih => exact ih _ (hprocess l event s hs)
  have hall : ∀ t, I (fighterState P d t) := by
    intro t
    induction t with
    | zero =>
      simp [I, FighterStartLogCovers,
        fighterState, initialFighterState]
    | succ t ih =>
      change I (fighter_actions P d (t + 1) (fighterState P d t))
      by_cases hd : d = 0
      · simp [fighter_actions, hd, I,
          FighterStartLogCovers,
          initialFighterState]
      · unfold fighter_actions
        rw [ite_eq_right hd]
        exact hfold (eventAt P.B (t + 1)) _ _ ih
  exact (hall tick).2

/-- Dummy identities are unique, unissued active phases have no dummy allocation, and all
allocated and active candidates have timestamps at most the state's clock. -/
def DummyIdentityInvariant (d : ℕ) (state : FighterState) : Prop :=
  (((state.allocated.filter
      (fun a ↦ decide (a.kind = .dummy))).map
        (fun a ↦ (a.level, a.candidate))).Nodup) ∧
  (∀ l p, state.activeAt d l = some p → p.dummyIssued = false →
    ∀ a ∈ state.allocated, a.kind = .dummy → (a.level, a.candidate) ≠ (l, p.candidate)) ∧
  (∀ a ∈ state.allocated, a.candidate.2 ≤ state.tick) ∧
  (∀ l p, state.activeAt d l = some p → p.candidate.2 ≤ state.tick)

/-- The empty initial state satisfies dummy uniqueness, freshness, and timestamp bounds. -/
lemma dummy_identity_invariant_initial
    (d : ℕ) :
    DummyIdentityInvariant d (initialFighterState d) := by
  dsimp only [DummyIdentityInvariant, initialFighterState]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp
  · intro l p h
    simp only [FighterState.activeAt, List.find?_nil] at h
    contradiction
  · intro a h
    contradiction
  · intro l p h
    simp only [FighterState.activeAt, List.find?_nil] at h
    contradiction

/-- Filtering by a predicate implied by the search predicate does not change a lookup. -/
private lemma find?_filter_of_imp {α : Type} (p q : α → Bool) (L : List α)
    (hpq : ∀ x, p x = true → q x = true) :
    List.find? p (List.filter q L) = List.find? p L := by
  rw [List.find?_filter]
  apply List.find?_congr
  intro x _
  by_cases hx : p x = true <;> simp_all

private lemma find_level_eq_some_of_filter_ne (ps : List FighterPhase) (l j : ℕ)
    (p : FighterPhase)
    (hp : (ps.filter (fun q ↦ q.level != l)).find? (fun q ↦ q.level == j) = some p) :
    ps.find? (fun q ↦ q.level == j) = some p := by
  have hmem := List.mem_filter.mp (List.mem_of_find?_eq_some hp)
  have hlevel : p.level = j := beq_iff_eq.mp
    (List.find?_some (p := fun q : FighterPhase ↦ q.level == j) hp)
  have hne : j ≠ l := by simpa only [hlevel, bne_iff_ne] using hmem.2
  rw [find?_filter_of_imp (fun q ↦ q.level == j) (fun q ↦ q.level != l) ps
    (fun q hq ↦ bne_iff_ne.mpr (by simpa only [beq_iff_eq.mp hq] using hne))] at hp
  exact hp

/-- Cancelling a phase preserves dummy uniqueness, freshness, and timestamp bounds. -/
lemma dummy_identity_invariant_cancel
    (d l : ℕ) (reason : PhaseEnd) (cause : ℕ) (state : FighterState)
    (h_good : DummyIdentityInvariant d state) :
    DummyIdentityInvariant d (fighterCancel d l reason cause state) := by
  unfold fighterCancel
  rcases h_good with ⟨h1, h2, h3, h4⟩
  split
  · exact ⟨h1, h2, h3, h4⟩
  · refine ⟨h1, ?_, h3, ?_⟩
    · intro j p hp
      exact h2 j p (find_level_eq_some_of_filter_ne state.active l j p hp)
    · intro j p hp
      exact h4 j p (find_level_eq_some_of_filter_ne state.active l j p hp)

/-- Aborting higher-level phases preserves the dummy invariant. -/
lemma dummy_identity_invariant_abortAbove
    (d l : ℕ) (state : FighterState)
    (h_good : DummyIdentityInvariant d state) :
    DummyIdentityInvariant d (fighterAbortAbove d l state) := by
  unfold fighterAbortAbove
  have h_fold : ∀ (L : List FighterPhase) (s : FighterState),
      DummyIdentityInvariant d s →
      DummyIdentityInvariant d (L.foldl (fun s phase ↦
        if l < phase.level then fighterCancel d phase.level .aborted l s else s) s) := by
    intro L
    induction L with
    | nil =>
      intro s hs
      exact hs
    | cons phase L ih =>
      intro s hs
      apply ih
      dsimp only
      split_ifs
      · exact dummy_identity_invariant_cancel d phase.level .aborted l s hs
      · exact hs
  exact h_fold state.active state h_good

/-- Appending a non-dummy allocation with a valid timestamp preserves the dummy invariant. -/
private lemma dummy_identity_invariant_append_of_ne_dummy
    (d : ℕ) (state : FighterState) (a : AllocatedDirective)
    (hgood : DummyIdentityInvariant d state) (hkind : a.kind ≠ .dummy)
    (htime : a.candidate.2 ≤ state.tick) :
    DummyIdentityInvariant d { state with allocated := state.allocated ++ [a] } := by
  rcases hgood with ⟨h_nodup, h_identities, h_tick_alloc, h_tick_act⟩
  refine ⟨?_, ?_, ?_, h_tick_act⟩
  · simpa [List.filter_append, hkind] using h_nodup
  · intro l p h_act h_dummy b hb hb_dummy
    rcases List.mem_append.mp hb with hb | hb
    · exact h_identities l p h_act h_dummy b hb hb_dummy
    · obtain rfl := List.mem_singleton.mp hb
      exact (hkind hb_dummy).elim
  · intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact h_tick_alloc b hb
    · obtain rfl := List.mem_singleton.mp hb
      exact htime

/-- Allocating fuel or payoff preserves dummy uniqueness, freshness, and timestamp bounds. -/
lemma dummy_identity_invariant_allocate_of_ne_dummy
    (d l : ℕ) (kind : DirectiveKind) (target : ℕ) (output : BitString) (state : FighterState)
    (h_good : DummyIdentityInvariant d state)
    (h_not_dummy : kind ≠ .dummy) :
    DummyIdentityInvariant d (fighterAllocate d l kind target output state).1 := by
  dsimp only [fighterAllocate]
  cases h_act : state.activeAt d l with
  | none =>
    exact h_good
  | some phase =>
    dsimp only
    cases h_fresh : (if target = 0 then none else
        (fighterInputs d (target - 1)).find? (fun p ↦
          !state.allocated.any (fun a ↦ a.input == p))) with
    | none =>
      dsimp only
      exact dummy_identity_invariant_cancel d l .saturated l _ h_good
    | some p =>
      dsimp only
      apply dummy_identity_invariant_abortAbove
      exact dummy_identity_invariant_append_of_ne_dummy d state _ h_good h_not_dummy
        (h_good.2.2.2 l phase h_act)

/-- Paying off a request preserves the dummy invariant. -/
lemma dummy_identity_invariant_payoff
    (P : FighterParams) (d l : ℕ) (q : Coordinate) (state : FighterState)
    (h_good : DummyIdentityInvariant d state) :
    DummyIdentityInvariant d (fighterPayoff P d l q state) := by
  dsimp only [fighterPayoff]
  cases h_act : state.activeAt d l with
  | none => exact h_good
  | some phase =>
    dsimp only
    have hdummy_cond : DirectiveKind.payoff ≠ .dummy := by decide
    by_cases h_cond : q ∈ phase.pending ∧ q ∉ state.fulfilled ∧ fighterSafe P d state.tick q = true
    · rw [ite_eq_left h_cond]
      have hnext := dummy_identity_invariant_allocate_of_ne_dummy
        d l .payoff q.2 q.1 state h_good hdummy_cond
      cases h_alloc : fighterAllocate d l .payoff q.2 q.1 state with
      | mk next success =>
        rw [h_alloc] at hnext
        cases success with
        | false => exact hnext
        | true =>
          rcases hnext with ⟨h1, h2, h3, h4⟩
          let f := fun (p : FighterPhase) ↦
            { p with pending := p.pending.filter (fun r ↦ r != q) }
          have hlookup (j : ℕ) :
              (next.active.map f).find? (fun p ↦ p.level == j) =
                (next.active.find? (fun p ↦ p.level == j)).map f := by
            simpa only [Function.comp, f] using
              (List.find?_map (p := fun p : FighterPhase ↦ p.level == j)
                (f := f) (l := next.active))
          refine ⟨h1, ?_, h3, ?_⟩
          · intro l' p' h_act' h_dummy' a h_a h_kind
            change (next.active.map f).find? (fun p ↦ p.level == l') = some p' at h_act'
            rw [hlookup] at h_act'
            cases hfind : next.active.find? (fun p ↦ p.level == l') with
            | none => simp [hfind] at h_act'
            | some p_next =>
              have hp : f p_next = p' := by
                simpa [hfind] using h_act'
              subst p'
              exact h2 l' p_next hfind h_dummy' a h_a h_kind
          · intro l' p' h_act'
            change (next.active.map f).find? (fun p ↦ p.level == l') = some p' at h_act'
            rw [hlookup] at h_act'
            cases hfind : next.active.find? (fun p ↦ p.level == l') with
            | none => simp [hfind] at h_act'
            | some p_next =>
              have hp : f p_next = p' := by
                simpa [hfind] using h_act'
              subst p'
              exact h4 l' p_next hfind
    · rw [ite_eq_right h_cond]
      exact h_good

/-- Fulfilling ready requests preserves the dummy invariant. -/
lemma dummy_identity_invariant_fulfillReady
    (P : FighterParams) (d l : ℕ) (state : FighterState)
    (h_good : DummyIdentityInvariant d state) :
    DummyIdentityInvariant d (fighterFulfillReady P d l state) := by
  unfold fighterFulfillReady
  cases h : state.activeAt d l
  · exact h_good
  · rename_i phase
    have h_fold : ∀ (pending : List Coordinate) s, DummyIdentityInvariant d s →
        DummyIdentityInvariant d (pending.foldl (fun s q ↦ fighterPayoff P d l q s) s) := by
      intro pending
      induction pending with
      | nil => intro s hs; exact hs
      | cons q qs ih =>
        intro s hs
        exact ih (fighterPayoff P d l q s) (dummy_identity_invariant_payoff P d l q s hs)
    exact h_fold phase.pending state h_good

/-- Aborting higher levels preserves allocations and the clock; surviving lookups are unchanged. -/
private lemma abort_above_allocation_clock_and_lookup
    (d l : ℕ) (state : FighterState) :
    (fighterAbortAbove d l state).allocated = state.allocated ∧
    (fighterAbortAbove d l state).tick = state.tick ∧
    (∀ j p, (fighterAbortAbove d l state).activeAt d j = some p →
      state.activeAt d j = some p) := by
  have hcancel (j : ℕ) (s : FighterState) :
      (fighterCancel d j .aborted l s).allocated = s.allocated ∧
      (fighterCancel d j .aborted l s).tick = s.tick ∧
      (∀ k p, (fighterCancel d j .aborted l s).activeAt d k = some p →
        s.activeAt d k = some p) := by
    unfold fighterCancel
    split
    · exact ⟨rfl, rfl, fun _ _ hp ↦ hp⟩
    · refine ⟨rfl, rfl, ?_⟩
      intro k p hp
      change (s.active.filter (fun q ↦ q.level != j)).find?
        (fun q ↦ q.level == k) = some p at hp
      exact find_level_eq_some_of_filter_ne s.active j k p hp
  have hfold (ps : List FighterPhase) (s : FighterState) :
      (ps.foldl (fun s p ↦ if l < p.level then
        fighterCancel d p.level .aborted l s else s) s).allocated = s.allocated ∧
      (ps.foldl (fun s p ↦ if l < p.level then
        fighterCancel d p.level .aborted l s else s) s).tick = s.tick ∧
      (∀ j p, (ps.foldl (fun s p ↦ if l < p.level then
        fighterCancel d p.level .aborted l s else s) s).activeAt d j = some p →
        s.activeAt d j = some p) := by
    induction ps generalizing s with
    | nil => exact ⟨rfl, rfl, fun _ _ hp ↦ hp⟩
    | cons p ps ih =>
      rw [List.foldl_cons]
      by_cases h : l < p.level
      · simp only [ite_eq_left h]
        obtain ⟨ha, ht, hp⟩ := ih (fighterCancel d p.level .aborted l s)
        obtain ⟨ha', ht', hp'⟩ := hcancel p.level s
        exact ⟨ha.trans ha', ht.trans ht', fun j q hq ↦ hp' j q (hp j q hq)⟩
      · simpa only [ite_eq_right h] using ih s
  exact hfold state.active state

/-- Installing a phase changes only the active lookup at its own level. -/
lemma activeAt_putPhase_eq (d : ℕ) (state : FighterState) (phase : FighterPhase) (l : ℕ) :
    (state.putPhase d phase).activeAt d l =
      if phase.level = l then some phase else state.activeAt d l := by
  simp only [FighterState.putPhase, FighterState.activeAt, List.find?_cons]
  by_cases hl : phase.level = l
  · simp only [hl, beq_self_eq_true, ↓reduceIte]
  · simp only [beq_eq_false_iff_ne.mpr hl, hl, ↓reduceIte, List.find?_filter]
    apply List.find?_congr
    intro p _
    by_cases hp : p.level = l <;> simp [hp, Ne.symm hl]

/-- Issuing a dummy preserves uniqueness by excluding identities of unissued active phases. -/
lemma dummy_identity_invariant_dummy
    (d l : ℕ) (state : FighterState)
    (h_good : DummyIdentityInvariant d state) :
    DummyIdentityInvariant d (fighterDummy d l state) := by
  cases hactive : state.activeAt d l with
  | none => simpa [fighterDummy, hactive] using h_good
  | some phase =>
    cases hdummy : phase.dummy with
    | none => simpa [fighterDummy, hactive, hdummy] using h_good
    | some output =>
      cases hissued : phase.dummyIssued with
      | true => simpa [fighterDummy, hactive, hdummy, hissued] using h_good
      | false =>
        simp only [fighterDummy, hactive, hdummy, hissued, Bool.false_eq_true, ↓reduceIte,
          fighterAllocate]
        cases hfresh : (if levelInput d l = 0 then (none : Option BitString) else
            (fighterInputs d (levelInput d l - 1)).find? (fun p ↦
              !state.allocated.any (fun a ↦ a.input == p))) with
        | none =>
          exact dummy_identity_invariant_cancel
            d l .saturated l _ h_good
        | some input =>
          let entry := AllocatedDirective.mk l phase.candidate state.tick .dummy
            (levelInput d l) input output
          let appended := { state with allocated := state.allocated ++ [entry] }
          let next := fighterAbortAbove d l appended
          change DummyIdentityInvariant d
            (next.putPhase d { phase with dummy := some output, dummyIssued := true })
          have hframe :=
            abort_above_allocation_clock_and_lookup
              d l appended
          have hlookup :=
            activeAt_putPhase_eq
              d next { phase with dummy := some output, dummyIssued := true }
          have hlevel : phase.level = l := beq_iff_eq.mp
            (List.find?_some (p := fun p : FighterPhase ↦ p.level == l) hactive)
          rcases h_good with ⟨hnd, hexclude, hatime, hptime⟩
          refine ⟨?_, ?_, ?_, ?_⟩
          · change ((next.allocated.filter (fun a ↦ decide (a.kind = .dummy))).map
              (fun a ↦ (a.level, a.candidate))).Nodup
            rw [hframe.1]
            simp only [appended, List.filter_append, List.filter_cons, entry,
              decide_true, ↓reduceIte, List.filter_nil, List.map_append, List.map_cons,
              List.map_nil]
            rw [List.nodup_append_comm]
            refine List.nodup_cons.mpr ⟨?_, hnd⟩
            intro hmem
            obtain ⟨a, ha, hid⟩ := List.mem_map.mp hmem
            obtain ⟨ha, hk⟩ := List.mem_filter.mp ha
            exact hexclude l phase hactive hissued a ha (of_decide_eq_true hk) hid
          · intro j p hp hflag a ha hk
            rw [hlookup j] at hp
            split at hp
            · cases hp
              contradiction
            · rename_i hj
              have hold : state.activeAt d j = some p := hframe.2.2 j p hp
              change a ∈ next.allocated at ha
              rw [hframe.1] at ha
              rcases List.mem_append.mp ha with ha | ha
              · exact hexclude j p hold hflag a ha hk
              · obtain rfl := List.mem_singleton.mp ha
                intro hid
                have hidlevel : l = j := congrArg Prod.fst hid
                exact hj (hlevel.trans hidlevel)
          · intro a ha
            change a ∈ next.allocated at ha
            change a.candidate.2 ≤ next.tick
            rw [hframe.1] at ha
            rw [hframe.2.1]
            rcases List.mem_append.mp ha with ha | ha
            · exact hatime a ha
            · obtain rfl := List.mem_singleton.mp ha
              exact hptime l phase hactive
          · intro j p hp
            change p.candidate.2 ≤ next.tick
            rw [hframe.2.1]
            rw [hlookup j] at hp
            split at hp
            · cases hp
              exact hptime l phase hactive
            · exact hptime j p (hframe.2.2 j p hp)

end Kolmogorov.Milovanov
