/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Construction.Accounting.DummyHistory

/-!
# Preservation of dummy identities

The phase-count argument bounds dummy allocations by showing that each phase identity
issues at most one dummy directive. This module proves that the identity invariant
(uniqueness of issued identities, freshness of unissued identities, and candidate timestamp
bounds) survives fuel moves, opponent events, and the creation and closure of phases.
`FuelHistory` uses the single-level preservation theorem to propagate the invariant through
all levels serviced at a clock tick, yielding the dummy part of the phase-count bound
(blueprint node `constr:phasecount`).
-/

namespace Kolmogorov.Milovanov

/-- Replacing a live phase with the same identity and dummy flag preserves the invariant. -/
private lemma dummy_identity_invariant_putPhase
    (d : ℕ) (state : FighterState) (phase phase' : FighterPhase)
    (hgood : DummyIdentityInvariant d state)
    (hactive : state.activeAt d phase.level = some phase)
    (hidentity : (phase'.level, phase'.candidate, phase'.dummyIssued) =
      (phase.level, phase.candidate, phase.dummyIssued)) :
    DummyIdentityInvariant d (state.putPhase d phase') := by
  simp only [Prod.mk.injEq] at hidentity
  obtain ⟨hlevel, hcandidate, hdummyIssued⟩ := hidentity
  rcases hgood with ⟨h1, h2, h3, h4⟩
  refine ⟨h1, ?_, h3, ?_⟩
  · intro l p hp hdummy a ha hkind
    rw [activeAt_putPhase_eq] at hp
    split at hp
    · rename_i hl
      cases hp
      rw [hlevel] at hl
      rw [hcandidate, ← hl]
      rw [hdummyIssued] at hdummy
      exact h2 phase.level phase hactive hdummy a ha hkind
    · exact h2 l p hp hdummy a ha hkind
  · intro l p hp
    rw [activeAt_putPhase_eq] at hp
    split at hp
    · cases hp
      rw [hcandidate]
      exact h4 phase.level phase hactive
    · exact h4 l p hp

/-- Flushing buffered counters preserves dummy identities and candidate timestamps. -/
private lemma dummy_identity_invariant_flushBuffer
    (d l : ℕ) (s next : FighterState)
    (hs : DummyIdentityInvariant d s)
    (hnext : fighterFlushBuffer d l s = some next) :
    DummyIdentityInvariant d next := by
  cases hphase : s.activeAt d l with
  | none => simp [fighterFlushBuffer, hphase] at hnext
  | some phase =>
    have hlevel : phase.level = l :=
      beq_iff_eq.mp (List.find?_some (p := fun p : FighterPhase ↦ p.level == l) hphase)
    have hactive : s.activeAt d phase.level = some phase := by
      rw [hlevel]
      exact hphase
    simp only [fighterFlushBuffer, hphase, bind, Option.bind_some] at hnext
    split at hnext
    · cases hnext
      exact dummy_identity_invariant_putPhase
        d s phase _ hs hactive rfl
    · contradiction

/-- Issuing one fuel directive preserves dummy identities and candidate timestamps. -/
private lemma dummy_identity_invariant_fuelUnit
    (P : FighterParams) (d l : ℕ) (q : Coordinate) (state : FighterState)
    (hgood : DummyIdentityInvariant d state) :
    DummyIdentityInvariant d (fighterFuelUnit P d l q state) := by
  unfold fighterFuelUnit
  cases hactive : state.activeAt d l with
  | none => exact hgood
  | some phase =>
    have hlevel : phase.level = l := beq_iff_eq.mp
      (List.find?_some (p := fun p : FighterPhase ↦ p.level == l) hactive)
    have hlookup : state.activeAt d phase.level = some phase := by
      simpa only [hlevel] using hactive
    dsimp only
    split
    · let index := fighterFreshString d
        (phase.indices[(phase.game d).coordinates.idxOf q]?.getD [])
      let output := pairCode (triple q.1 (q.2 - d) phase.candidate.1) index
      let charged := { phase with controlledRemaining := phase.controlledRemaining - 1 }
      have hcharged : DummyIdentityInvariant d (state.putPhase d charged) :=
        dummy_identity_invariant_putPhase
          d state phase charged hgood hlookup rfl
      have hchargedLookup : (state.putPhase d charged).activeAt d l = some charged := by
        simp [FighterState.putPhase, FighterState.activeAt, charged, hlevel]
      have ha :=
        dummy_identity_invariant_allocate_of_ne_dummy
          d l .fuel (levelUpper l + d) output (state.putPhase d charged) hcharged (by decide)
      change DummyIdentityInvariant d
        (let (next, success) := fighterAllocate d l .fuel (levelUpper l + d) output
            (state.putPhase d charged)
         if success then
           fighterFulfillReady P d l
             (next.putPhase d ((charged.insertIndex d q index).fundRequests d next.fulfilled))
         else next)
      cases he : fighterAllocate d l .fuel (levelUpper l + d) output
          (state.putPhase d charged) with
      | mk next success =>
        rw [he] at ha
        cases success with
        | false => exact ha
        | true =>
          have hnext :=
            activeAt_fighterAllocate_eq_of_success
              d l (levelUpper l + d) .fuel output (state.putPhase d charged) next charged
              hchargedLookup he
          have hnextLookup : next.activeAt d charged.level = some charged := by
            simpa only [charged, hlevel] using hnext
          apply
            dummy_identity_invariant_fulfillReady
          exact dummy_identity_invariant_putPhase
            d next charged _ ha hnextLookup rfl
    · exact hgood

/-- Issuing a finite batch of fuel directives preserves the identity invariant. -/
private lemma dummy_identity_invariant_fuelUnits
    (P : FighterParams) (d l : ℕ) (q : Coordinate) (count : ℕ) (state : FighterState)
    (hgood : DummyIdentityInvariant d state) :
    DummyIdentityInvariant d (fighterFuelUnits P d l q count state) := by
  induction count generalizing state with
  | zero => exact hgood
  | succ count ih =>
    exact ih _ (dummy_identity_invariant_fuelUnit P d l q state hgood)

/-- Distributing fuel over indexed coordinates preserves the identity invariant. -/
private lemma dummy_identity_invariant_fuel_fold
    (P : FighterParams) (d l : ℕ) (move : List ℕ) (pairs : List (Coordinate × ℕ))
    (state : FighterState)
    (hgood : DummyIdentityInvariant d state) :
    DummyIdentityInvariant d (pairs.foldl (fun st (q, i) ↦
        fighterFuelUnits P d l q (move[i]?.getD 0) st) state) := by
  induction pairs generalizing state with
  | nil =>
    exact hgood
  | cons head tail ih =>
    simp only [List.foldl_cons]
    apply ih
    apply dummy_identity_invariant_fuelUnits
    exact hgood

/-- A successful strategy move preserves the identity invariant. -/
private lemma dummy_identity_invariant_strategyMove
    (P : FighterParams) (d l : ℕ) (s next : FighterState)
    (hs : DummyIdentityInvariant d s)
    (hnext : fighterStrategyMove P d l s = some next) :
    DummyIdentityInvariant d next := by
  have htotal : DummyIdentityInvariant d ((fighterStrategyMove P d l s).getD s) := by
    cases hphase : s.activeAt d l with
    | none =>
      simpa only [fighterStrategyMove, hphase, bind, Option.bind_none, Option.getD_none] using hs
    | some phase =>
      simp only [fighterStrategyMove, hphase, bind, Option.bind_some]
      split
      · cases hm : (phase.game d).strategy (phase.official d) with
        | none =>
          exact hs
        | some move =>
          simp only [Option.bind_some]
          split
          · let next_fold := (phase.game d).coordinates.zipIdx.foldl
              (fun t (q, i) ↦
                fighterFuelUnits P d l q (move[i]?.getD 0) t) s
            have hnext_fold : DummyIdentityInvariant d next_fold :=
              dummy_identity_invariant_fuel_fold
                P d l move _ s hs
            change DummyIdentityInvariant d ((match next_fold.activeAt d l with
              | none => some next_fold
              | some live => some (next_fold.putPhase d
                  { live with officialCode :=
                    ((phase.game d).afterMove
                      (phase.official d) move).encode })).getD s)
            cases hlive : next_fold.activeAt d l with
            | none =>
              exact hnext_fold
            | some live =>
              have hfind : next_fold.active.find?
                  (fun p : FighterPhase ↦ p.level == l) =
                    some live := hlive
              have hlevel : live.level = l :=
                beq_iff_eq.mp (List.find?_some (p := fun p : FighterPhase ↦ p.level == l) hfind)
              have hlookup :
                  next_fold.activeAt d live.level = some live := by
                simpa only [hlevel] using hlive
              exact dummy_identity_invariant_putPhase
                d next_fold live _ hnext_fold hlookup rfl
          · exact hs
      · exact hs
  simpa only [hnext, Option.getD_some] using htotal

/-- Every successful action at a level preserves the identity invariant. -/
private lemma dummy_identity_invariant_levelAction
    (P : FighterParams) (d l : ℕ) (s next : FighterState)
    (hs : DummyIdentityInvariant d s)
    (hnext : fighterLevelAction P d l s = some next) :
    DummyIdentityInvariant d next := by
  unfold fighterLevelAction at hnext
  simp only [bind, Option.bind] at hnext
  cases h_act : s.activeAt d l with
  | none =>
    rw [h_act] at hnext
    simp at hnext
  | some phase =>
    rw [h_act] at hnext
    by_cases h_dum : phase.dummy.isSome && !phase.dummyIssued
    · simp only [h_dum, ite_true] at hnext
      injection hnext with heq
      subst next
      exact dummy_identity_invariant_dummy d l s hs
    · simp only [h_dum, Bool.false_eq_true, ↓reduceIte] at hnext
      cases h_find : phase.pending.find? (fun x ↦ decide (x ∉ s.fulfilled) && fighterSafe P d
        s.tick x) with
      | some q =>
        rw [h_find] at hnext
        injection hnext with heq
        subst next
        exact dummy_identity_invariant_payoff P d
          l q s hs
      | none =>
        rw [h_find] at hnext
        cases h_flush : fighterFlushBuffer d l s with
        | some next' =>
          rw [h_flush] at hnext
          injection hnext with heq
          subst next
          exact dummy_identity_invariant_flushBuffer d l s next' hs h_flush
        | none =>
          rw [h_flush] at hnext
          exact dummy_identity_invariant_strategyMove P d l s next hs hnext

/-- Iterating level actions preserves the identity invariant. -/
private lemma dummy_identity_invariant_closure
    (P : FighterParams) (d l : ℕ) (fuel : ℕ) (state : FighterState)
    (h_good : DummyIdentityInvariant d state) :
    DummyIdentityInvariant d (fighterClosure P d l fuel state) := by
  induction fuel generalizing state with
  | zero => exact h_good
  | succ fuel ih =>
    unfold fighterClosure
    cases h_action : fighterLevelAction P d l state
    · exact h_good
    · rename_i next
      apply ih
      exact dummy_identity_invariant_levelAction P d l state next h_good h_action

/-- Closing a level preserves the identity invariant. -/
private lemma dummy_identity_invariant_closeLevel
    (P : FighterParams) (d l : ℕ) (state : FighterState)
    (h_good : DummyIdentityInvariant d state) :
    DummyIdentityInvariant d (fighterCloseLevel P d l state) := by
  exact dummy_identity_invariant_closure P d l (fighterClosureFuel d l state) state h_good

/-- Responding to an opponent event preserves the identity invariant. -/
private lemma dummy_identity_invariant_opponent
    (P : FighterParams) (d l : ℕ) (event : ProgramEvent) (state : FighterState)
    (h_good : DummyIdentityInvariant d state) :
    DummyIdentityInvariant d (fighterOpponent P d l event state) := by
  dsimp [fighterOpponent]
  cases h_active : state.activeAt d l
  · exact h_good
  · rename_i phase
    dsimp only
    cases h_tuple : fighterOpponentTuple d phase event
    · exact h_good
    · rename_i tuple
      cases tuple with
      | mk q index =>
        dsimp only
        split
        · exact h_good
        · split
          · exact dummy_identity_invariant_cancel
              d l .opponentExhausted l state h_good
          · have hlevel : phase.level = l :=
              beq_iff_eq.mp
                (List.find?_some
                  (p := fun p : FighterPhase ↦ p.level == l)
                  h_active)
            apply
              dummy_identity_invariant_fulfillReady
            have hlookup : state.activeAt d phase.level = some phase := by
              simpa only [hlevel] using h_active
            exact dummy_identity_invariant_putPhase
              d state phase _ h_good hlookup rfl

/-- Cancelling a phase changes neither allocations nor the clock. -/
private lemma cancel_allocated_tick
    (d l : ℕ) (reason : PhaseEnd) (cause : ℕ) (state : FighterState) :
    (fighterCancel d l reason cause state).allocated = state.allocated ∧
    (fighterCancel d l reason cause state).tick = state.tick := by
  unfold fighterCancel
  split <;> exact ⟨rfl, rfl⟩

/-- Aborting higher levels changes neither allocations nor the clock. -/
private lemma abortAbove_allocated_tick
    (d l : ℕ) (state : FighterState) :
    (fighterAbortAbove d l state).allocated = state.allocated ∧
    (fighterAbortAbove d l state).tick = state.tick := by
  unfold fighterAbortAbove
  suffices h : ∀ (ps : List FighterPhase) (s : FighterState),
      (ps.foldl (fun s phase ↦
          if l < phase.level then fighterCancel d phase.level .aborted l s else s) s).allocated =
          s.allocated ∧
        (ps.foldl (fun s phase ↦
          if l < phase.level then fighterCancel d phase.level .aborted l s else s) s).tick =
          s.tick from h _ _
  intro ps
  induction ps with
  | nil => intro s; exact ⟨rfl, rfl⟩
  | cons p ps ih =>
    intro s
    dsimp [List.foldl]
    split_ifs with h_if
    · have ih' := ih (fighterCancel d p.level .aborted l s)
      have h_cancel := cancel_allocated_tick d p.level .aborted l s
      exact ⟨ih'.1.trans h_cancel.1, ih'.2.trans h_cancel.2⟩
    · exact ih s

/-- Preparing a level for a new phase preserves allocations and the clock. -/
private lemma waiting_allocated_tick
    (d l : ℕ) (state : FighterState) :
    (fighterAbortAbove d l (fighterCancel d l .replaced l state)).allocated = state.allocated ∧
    (fighterAbortAbove d l (fighterCancel d l .replaced l state)).tick = state.tick := by
  have h_cancel := cancel_allocated_tick d l .replaced l state
  have h_abort := abortAbove_allocated_tick d l (fighterCancel d l .replaced l state)
  exact ⟨h_abort.1.trans h_cancel.1, h_abort.2.trans h_cancel.2⟩

/-- Allocating a directive preserves the clock, including on failure. -/
private lemma allocate_tick (d l : ℕ) (kind : DirectiveKind) (target : ℕ) (output : BitString)
    (state : FighterState) :
    (fighterAllocate d l kind target output state).1.tick = state.tick := by
  unfold fighterAllocate
  cases state.activeAt d l
  · rfl
  · dsimp
    cases h : (if target = 0 then none else (fighterInputs d (target - 1)).find? fun p ↦
      !(state.allocated.any fun a ↦ a.input == p))
    · exact (cancel_allocated_tick _ _ _ _ _).2
    · exact (abortAbove_allocated_tick _ _ _).2

/-- Paying off a request preserves the clock. -/
private lemma payoff_tick (P : FighterParams) (d l : ℕ) (q : Coordinate) (state : FighterState) :
    (fighterPayoff P d l q state).tick = state.tick := by
  unfold fighterPayoff
  split
  · rfl
  · split
    · have h := allocate_tick d l .payoff q.2 q.1 state
      cases he : fighterAllocate d l .payoff q.2 q.1 state with
      | mk next success =>
        rw [he] at h
        cases success <;> exact h
    · rfl

/-- Fulfilling ready requests preserves the clock. -/
private lemma fulfillReady_tick
    (P : FighterParams) (d l : ℕ) (state : FighterState) :
    (fighterFulfillReady P d l state).tick = state.tick := by
  unfold fighterFulfillReady
  cases h : state.activeAt d l
  · rfl
  · rename_i phase
    have : ∀ (s : FighterState), s.tick = state.tick → (phase.pending.foldl (fun s q ↦
      fighterPayoff P d l q s) s).tick = state.tick := by
      intro s hs
      induction phase.pending generalizing s
      · exact hs
      · rename_i hd tl ih
        apply ih
        have h_payoff := payoff_tick P d l hd s
        rw [h_payoff]
        exact hs
    apply this state rfl

/-- Fulfilling ready requests creates no dummy allocations. -/
private lemma dummy_mem_of_mem_fulfillReady
    (P : FighterParams) (d l : ℕ) (state : FighterState)
    (a : AllocatedDirective) (ha : a ∈ (fighterFulfillReady P d l state).allocated)
    (hk : a.kind = .dummy) :
    a ∈ state.allocated := by
  let E (s t : FighterState) : Prop := ∀ a ∈ t.allocated, a.kind = .dummy → a ∈ s.allocated
  have hrefl (s : FighterState) : E s s := fun _ h _ ↦ h
  have htrans {s t u : FighterState} (hst : E s t) (htu : E t u) : E s u :=
    fun a ha hk ↦ hst a (htu a ha hk) hk
  have hsame (s t : FighterState) (h : t.allocated = s.allocated) : E s t := by
    intro a ha hk
    rw [h] at ha
    exact ha
  have hfold {α : Type} (f : α → FighterState → FighterState)
      (hf : ∀ a s, E s (f a s)) (xs : List α) (s : FighterState) :
      E s (xs.foldl (fun acc x ↦ f x acc) s) := by
    induction xs generalizing s with
    | nil => exact hrefl s
    | cons x xs ih => exact htrans (hf x s) (ih _)
  have hcancel (j : ℕ) (reason : PhaseEnd) (cause : ℕ) (s : FighterState) :
      E s (fighterCancel d j reason cause s) := by
    apply hsame
    unfold fighterCancel
    split <;> rfl
  have habort (j : ℕ) (s : FighterState) : E s (fighterAbortAbove d j s) := by
    unfold fighterAbortAbove
    apply hfold
    intro p t
    split
    · exact hcancel _ _ _ _
    · exact hrefl t
  have halloc (j : ℕ) (kind : DirectiveKind) (target : ℕ) (out : BitString) (s : FighterState)
    (hkind : kind ≠ .dummy) :
      E s (fighterAllocate d j kind target out s).1 := by
    unfold fighterAllocate
    cases hs : s.activeAt d j with
    | none => exact hrefl s
    | some phase =>
      dsimp only
      by_cases ht : target = 0
      · simp only [ht, ↓reduceIte]
        exact htrans (hsame _ _ rfl) (hcancel _ _ _ _)
      · simp only [ht, ↓reduceIte]
        cases hf : (fighterInputs d (target - 1)).find?
            (fun p ↦ !s.allocated.any (fun a ↦ a.input == p)) with
        | none =>
          exact htrans (hsame _ _ rfl) (hcancel _ _ _ _)
        | some p =>
          apply htrans (t := { s with allocated := s.allocated ++
            [AllocatedDirective.mk j phase.candidate s.tick kind target p out] })
          · intro b hb hk
            rcases List.mem_append.mp hb with hb | hb
            · exact hb
            · have heq := List.mem_singleton.mp hb
              subst b
              dsimp at hk
              contradiction
          · exact habort _ _
  have hpay (j : ℕ) (q : Coordinate) (s : FighterState) : E s (fighterPayoff P d j q s) := by
    unfold fighterPayoff
    cases hs : s.activeAt d j with
    | none => exact hrefl s
    | some phase =>
      dsimp only
      split
      · cases he : fighterAllocate d j .payoff q.2 q.1 s with
        | mk next success =>
          have h := halloc j .payoff q.2 q.1 s (by decide)
          rw [he] at h
          cases success
          · exact htrans h (hsame _ _ rfl)
          · exact h
      · exact hrefl s
  have hfulfill (j : ℕ) (s : FighterState) : E s (fighterFulfillReady P d j s) := by
    unfold fighterFulfillReady
    cases hs : s.activeAt d j with
    | none => exact hrefl s
    | some phase =>
      exact hfold (fun q acc ↦ fighterPayoff P d j q acc) (fun q s ↦ hpay j q s) _ _
  exact hfulfill l state a ha hk

/-- Installing a phase with a fresh dummy identity preserves the invariant. -/
private lemma dummy_identity_invariant_started
    (d : ℕ) (state : FighterState) (phase : FighterPhase)
    (h_good : DummyIdentityInvariant d state)
    (h_fresh : ∀ a ∈ state.allocated, a.kind = .dummy →
      (a.level, a.candidate) ≠ (phase.level, phase.candidate))
    (h_tick : phase.candidate.2 ≤ state.tick) :
    let next : FighterState := { state.putPhase d phase with
      started := state.started ++ [(phase.level, phase.candidate)] }
    DummyIdentityInvariant d next := by
  intro next
  have h_next_alloc : next.allocated = state.allocated := by rfl
  have h_next_tick : next.tick = state.tick := by rfl
  dsimp [DummyIdentityInvariant] at h_good ⊢
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h_next_alloc]
    exact h_good.1
  · intro l' p' h_act h_dum a ha h_a_dum
    rw [h_next_alloc] at ha
    change (state.putPhase d phase).activeAt d l' = some p' at h_act
    rw [activeAt_putPhase_eq] at h_act
    split_ifs at h_act with hl
    · cases h_act
      rw [← hl]
      exact h_fresh a ha h_a_dum
    · exact h_good.2.1 l' p' h_act h_dum a ha h_a_dum
  · intro a ha
    rw [h_next_alloc] at ha
    rw [h_next_tick]
    exact h_good.2.2.1 a ha
  · intro l' p' h_act
    rw [h_next_tick]
    change (state.putPhase d phase).activeAt d l' = some p' at h_act
    rw [activeAt_putPhase_eq] at h_act
    split_ifs at h_act with hl
    · cases h_act
      exact h_tick
    · exact h_good.2.2.2 l' p' h_act

/-- Starting a phase at the current tick preserves the invariant if its dummy identity is fresh. -/
private lemma dummy_identity_invariant_startPhase
    (P : FighterParams) (d l : ℕ) (candidate : Candidate) (state : FighterState)
    (h_good : DummyIdentityInvariant d state)
    (h_tick : candidate.2 = state.tick)
    (h_dummy_fresh : ∀ a ∈ state.allocated, a.kind = .dummy →
      (a.level, a.candidate) ≠ (l, candidate)) :
    DummyIdentityInvariant d (fighterStartPhase P d l candidate state) := by
  unfold fighterStartPhase
  let waiting := fighterAbortAbove d l (fighterCancel d l .replaced l state)
  have h_waiting_good : DummyIdentityInvariant d waiting :=
    dummy_identity_invariant_abortAbove d l _
      (dummy_identity_invariant_cancel
        d l .replaced l state h_good)
  have h_eq : waiting.allocated = state.allocated ∧ waiting.tick = state.tick :=
    waiting_allocated_tick d l state
  let phase := fighter_construction P d l candidate waiting
  have h_tick_le : candidate.2 ≤ waiting.tick := by
    rw [h_eq.2]
    exact le_of_eq h_tick
  have h_dummy_fresh' : ∀ a ∈ waiting.allocated, a.kind = .dummy →
      (a.level, a.candidate) ≠ (l, candidate) := by
    rw [h_eq.1]
    exact h_dummy_fresh
  exact dummy_identity_invariant_started d waiting phase h_waiting_good h_dummy_fresh' h_tick_le

/-- Processing a level preserves uniqueness of dummy identities and the timestamp bounds,
provided the event occurs at the current tick and its timestamp is fresh at that level.
This is the preservation lemma used by the distinct-level fold in `FuelHistory`. -/
lemma dummy_identity_invariant_processLevel
    (P : FighterParams) (d l : ℕ) (event : Option TimedEvent) {state : FighterState}
    (h_good : DummyIdentityInvariant d state)
    (hevent : match event with | some e => e.1 = state.tick | none => True)
    (hfresh : match event with
      | some e => ∀ a ∈ state.allocated, a.level = l → a.candidate.2 ≠ e.1
      | none => True) :
    DummyIdentityInvariant d (fighterProcessLevel P d l event state) := by
  dsimp [fighterProcessLevel]
  have h_checked_good :=
    dummy_identity_invariant_fulfillReady P d l
      state h_good
  refine dummy_identity_invariant_closeLevel P d l _ ?_
  cases event with
  | none => exact h_checked_good
  | some e =>
    dsimp
    split_ifs
    · have h_tick : (e.2.2.1, e.1).2 =
          (fighterFulfillReady P d l state).tick := by
        rw [fulfillReady_tick P d l state]
        exact hevent
      have h_dummy_fresh : ∀ a ∈ (fighterFulfillReady P d l state).allocated,
          a.kind = .dummy → (a.level, a.candidate) ≠ (l, (e.2.2.1, e.1)) := by
        intro a ha hk heq
        have ha_orig := dummy_mem_of_mem_fulfillReady P d l state a ha hk
        have hlevel : a.level = l := congrArg Prod.fst heq
        have hcand : a.candidate = (e.2.2.1, e.1) := congrArg Prod.snd heq
        have hneq := hfresh a ha_orig hlevel
        apply hneq
        simp [hcand]
      exact dummy_identity_invariant_startPhase P d l (e.2.2.1, e.1)
        (fighterFulfillReady P d l state) h_checked_good h_tick h_dummy_fresh
    · exact dummy_identity_invariant_opponent P d l e.2.2
        (fighterFulfillReady P d l state) h_checked_good

end Kolmogorov.Milovanov
