/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Construction.Effective.StateMachine

/-!
# Completeness of the event actions of the fighter construction

This module proves that the event transition of the fighter construction leaves no enabled
internal action behind: after a completed tick, `fighterLevelAction` is `none` at every active
level (`fighter_event_actions_complete`, blueprint node `constr:effective`).

A tick services the active levels together with the owner level of the current halting event,
in strictly increasing order. The proof tracks a relation `levelEffect d l` describing what
servicing level `l` can do to a state: it fixes the clock, only enlarges the fulfilled table,
and at smaller levels it merely filters pending requests. Hence an already quiescent smaller
level stays quiescent, and every level of the sorted service list is quiescent at the end of
the fold, since a level is closed under its own enabled actions when it is serviced.

The result is consumed by the stability modules, which use it to read off the invariants of the
state at the end of each tick.
-/

namespace Kolmogorov.Milovanov

/-- Servicing level `l` fixes the clock, enlarges the fulfilled table, and introduces
no other active level. At smaller levels it only filters pending requests; every
other phase field and the order used by `activeAt` stay fixed. -/
private def levelEffect (d l : ℕ) (before after : FighterState) : Prop :=
  after.tick = before.tick ∧ before.fulfilled ⊆ after.fulfilled ∧
    (∀ j < l, ∃ keep : Coordinate → Bool,
      after.activeAt d j = (before.activeAt d j).map
        (fun phase ↦ { phase with pending := phase.pending.filter keep })) ∧
    ∀ phase ∈ after.active,
      phase.level = l ∨ phase.level ∈ before.active.map FighterPhase.level

private lemma levelEffect_refl (d l : ℕ) (s : FighterState) : levelEffect d l s s := by
  refine ⟨rfl, fun _ h ↦ h, ?_, ?_⟩
  · intro j hj
    exact ⟨fun _ ↦ true, by simp⟩
  · intro phase hp
    exact Or.inr (List.mem_map_of_mem hp)

private lemma levelEffect_trans (d l : ℕ) {s t u : FighterState}
    (hst : levelEffect d l s t) (htu : levelEffect d l t u) : levelEffect d l s u := by
  refine ⟨htu.1.trans hst.1, fun _ h ↦ htu.2.1 (hst.2.1 h), ?_, ?_⟩
  · intro j hj
    obtain ⟨f, hf⟩ := hst.2.2.1 j hj
    obtain ⟨g, hg⟩ := htu.2.2.1 j hj
    refine ⟨fun q ↦ g q && f q, ?_⟩
    rw [hg, hf, Option.map_map]
    congr 1
    funext p
    simp [List.filter_filter]
  · intro phase hp
    rcases htu.2.2.2 phase hp with h | h
    · exact Or.inl h
    · rcases List.mem_map.mp h with ⟨old, hold, heq⟩
      exact heq ▸ hst.2.2.2 old hold

private lemma levelEffect_of_active_eq (d l : ℕ) (s t : FighterState)
    (htick : t.tick = s.tick) (hfulfilled : s.fulfilled ⊆ t.fulfilled)
    (hactive : t.active = s.active) : levelEffect d l s t := by
  refine ⟨htick, hfulfilled, ?_, ?_⟩
  · intro j hj
    refine ⟨fun _ ↦ true, ?_⟩
    simp [FighterState.activeAt, hactive]
  · intro phase hp
    exact Or.inr (List.mem_map_of_mem (hactive ▸ hp))

private lemma pending_filter_true (p : FighterPhase) :
    { p with pending := p.pending.filter (fun _ ↦ true) } = p := by
  cases p
  simp

private lemma levelEffect_putPhase (d l : ℕ) (s : FighterState) (p : FighterPhase)
    (hp : p.level = l) : levelEffect d l s (s.putPhase d p) := by
  refine ⟨rfl, fun _ h ↦ h, ?_, ?_⟩
  · intro j hj
    refine ⟨fun _ ↦ true, ?_⟩
    simp only [pending_filter_true, Option.map_id']
    exact FighterState.activeAt_putPhase_of_ne d j s p (by omega)
  · intro phase hphase
    rcases List.mem_cons.mp hphase with rfl | hphase
    · exact Or.inl hp
    · exact Or.inr (List.mem_map_of_mem (List.mem_filter.mp hphase).1)

private lemma levelEffect_cancel (d l k : ℕ) (hk : l ≤ k) (reason : PhaseEnd) (cause : ℕ)
    (s : FighterState) : levelEffect d l s (fighterCancel d k reason cause s) := by
  unfold fighterCancel
  split
  · exact levelEffect_refl d l s
  · refine ⟨rfl, fun _ h ↦ h, ?_, ?_⟩
    · intro j hj
      refine ⟨fun _ ↦ true, ?_⟩
      simp only [pending_filter_true, Option.map_id']
      change (s.active.filter (fun p ↦ p.level != k)).find? (fun p ↦ p.level == j) =
        s.active.find? (fun p ↦ p.level == j)
      exact FighterState.find?_level_filter_ne s.active j k (by omega)
    · intro phase hp
      exact Or.inr (List.mem_map_of_mem (List.mem_filter.mp hp).1)

private lemma levelEffect_foldl {α : Type} (d l : ℕ) (f : α → FighterState → FighterState)
    (hf : ∀ a s, levelEffect d l s (f a s)) (xs : List α) (s : FighterState) :
    levelEffect d l s (xs.foldl (fun s a ↦ f a s) s) := by
  induction xs generalizing s with
  | nil => exact levelEffect_refl d l s
  | cons a xs ih => exact levelEffect_trans d l (hf a s) (ih _)

private lemma levelEffect_abortAbove (d l : ℕ) (s : FighterState) :
    levelEffect d l s (fighterAbortAbove d l s) := by
  unfold fighterAbortAbove
  apply levelEffect_foldl
  intro p t
  split
  · apply levelEffect_cancel
    omega
  · exact levelEffect_refl d l t

private lemma levelEffect_allocate (d l : ℕ) (kind : DirectiveKind) (target : ℕ)
    (out : BitString) (s : FighterState) :
    levelEffect d l s (fighterAllocate d l kind target out s).1 := by
  unfold fighterAllocate
  split
  · exact levelEffect_refl d l s
  · cases hf : (if target = 0 then (none : Option BitString) else
        (fighterInputs d (target - 1)).find? (fun p ↦
          !s.allocated.any (fun a ↦ a.input == p))) with
    | none =>
      dsimp only
      apply levelEffect_trans d l
        (levelEffect_of_active_eq d l s { s with failed := true } rfl (fun _ h ↦ h) rfl)
      exact levelEffect_cancel d l l le_rfl .saturated l _
    | some p =>
      dsimp only
      apply levelEffect_trans d l (levelEffect_of_active_eq d l s _ rfl (fun _ h ↦ h) rfl)
      exact levelEffect_abortAbove d l _

private lemma levelEffect_recordPayoff (d l : ℕ) (q : Coordinate) (s : FighterState) :
    levelEffect d l s
      { s with
        fulfilled := s.fulfilled ++ [q]
        active := s.active.map (fun p ↦ { p with pending := p.pending.filter (· != q) }) } := by
  refine ⟨rfl, fun _ h ↦ List.mem_append_left _ h, ?_, ?_⟩
  · intro j hj
    refine ⟨fun r ↦ r != q, ?_⟩
    simp [FighterState.activeAt, List.find?_map]
  · intro phase hp
    obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hp
    exact Or.inr (List.mem_map.mpr ⟨old, hold, rfl⟩)

private lemma levelEffect_payoff (P : FighterParams) (d l : ℕ) (q : Coordinate)
    (s : FighterState) : levelEffect d l s (fighterPayoff P d l q s) := by
  unfold fighterPayoff
  split
  · exact levelEffect_refl d l s
  · split
    · have ha := levelEffect_allocate d l .payoff q.2 q.1 s
      cases he : fighterAllocate d l .payoff q.2 q.1 s with
      | mk next success =>
        simp only [he] at ha ⊢
        cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
        · exact ha
        · exact levelEffect_trans d l ha (levelEffect_recordPayoff d l q next)
    · exact levelEffect_refl d l s

private lemma levelEffect_fulfillReady (P : FighterParams) (d l : ℕ) (s : FighterState) :
    levelEffect d l s (fighterFulfillReady P d l s) := by
  unfold fighterFulfillReady
  split
  · exact levelEffect_refl d l s
  · apply levelEffect_foldl
    intro q t
    exact levelEffect_payoff P d l q t

private lemma levelEffect_fuelUnit (P : FighterParams) (d l : ℕ) (q : Coordinate)
    (s : FighterState) : levelEffect d l s (fighterFuelUnit P d l q s) := by
  unfold fighterFuelUnit
  split
  · exact levelEffect_refl d l s
  · rename_i phase hphase
    have hlevel := FighterState.level_eq_of_activeAt_eq_some (p := phase) hphase
    split
    · let charged := { phase with controlledRemaining := phase.controlledRemaining - 1 }
      let out := pairCode (triple q.1 (q.2 - d) phase.candidate.1)
        (fighterFreshString d (phase.indices[(phase.game d).coordinates.idxOf q]?.getD []))
      have hc := levelEffect_putPhase d l s charged hlevel
      have ha := levelEffect_allocate d l .fuel (levelUpper l + d) out (s.putPhase d charged)
      have hbefore := levelEffect_trans d l hc ha
      change levelEffect d l s
        (match fighterAllocate d l .fuel (levelUpper l + d) out (s.putPhase d charged) with
          | (next, success) => if success then
              fighterFulfillReady P d l (next.putPhase d
                ((charged.insertIndex d q (fighterFreshString d
                  (phase.indices[(phase.game d).coordinates.idxOf q]?.getD []))).fundRequests d
                    next.fulfilled)) else next)
      cases he : fighterAllocate d l .fuel (levelUpper l + d) out (s.putPhase d charged) with
      | mk next success =>
        rw [he] at hbefore
        cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
        · exact hbefore
        · apply levelEffect_trans d l hbefore
          apply levelEffect_trans d l
            (levelEffect_putPhase d l next
              ((charged.insertIndex d q (fighterFreshString d
                (phase.indices[(phase.game d).coordinates.idxOf q]?.getD []))).fundRequests d
                  next.fulfilled)
              (by simpa [FighterPhase.fundRequests, FighterPhase.insertIndex, charged]
                using hlevel))
          exact levelEffect_fulfillReady P d l _
    · exact levelEffect_refl d l s

private lemma levelEffect_fuelUnits (P : FighterParams) (d l : ℕ) (q : Coordinate)
    (count : ℕ) (s : FighterState) : levelEffect d l s (fighterFuelUnits P d l q count s) := by
  induction count generalizing s with
  | zero => exact levelEffect_refl d l s
  | succ count ih => exact levelEffect_trans d l (levelEffect_fuelUnit P d l q s) (ih _)

private lemma levelEffect_dummy (d l : ℕ) (s : FighterState) :
    levelEffect d l s (fighterDummy d l s) := by
  unfold fighterDummy
  split
  · exact levelEffect_refl d l s
  · rename_i phase hphase
    have hlevel := FighterState.level_eq_of_activeAt_eq_some (p := phase) hphase
    split
    · exact levelEffect_refl d l s
    · rename_i out hout
      split
      · exact levelEffect_refl d l s
      · have ha := levelEffect_allocate d l .dummy (levelInput d l) out s
        cases he : fighterAllocate d l .dummy (levelInput d l) out s with
        | mk next success =>
          simp only [he] at ha ⊢
          cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
          · exact ha
          · exact levelEffect_trans d l ha
              (levelEffect_putPhase d l next { phase with dummyIssued := true } hlevel)

private lemma levelEffect_opponent (P : FighterParams) (d l : ℕ) (event : ProgramEvent)
    (s : FighterState) : levelEffect d l s (fighterOpponent P d l event s) := by
  unfold fighterOpponent
  split
  · exact levelEffect_refl d l s
  · rename_i phase hphase
    have hlevel := FighterState.level_eq_of_activeAt_eq_some (p := phase) hphase
    split
    · exact levelEffect_refl d l s
    · rename_i q index htuple
      split
      · exact levelEffect_refl d l s
      · split
        · exact levelEffect_cancel d l l le_rfl .opponentExhausted l s
        · let inserted := phase.insertIndex d q index
          let next := { inserted with
            opponentRemaining := phase.opponentRemaining - 1
            buffer := (phase.game d).addCounters phase.buffer (phase.unitVector d q) }
          exact levelEffect_trans d l
            (levelEffect_putPhase d l s (next.fundRequests d s.fulfilled)
              (by simpa [next, inserted, FighterPhase.fundRequests, FighterPhase.insertIndex]
                using hlevel))
            (levelEffect_fulfillReady P d l _)

private lemma levelEffect_startPhase (P : FighterParams) (d l : ℕ) (candidate : Candidate)
    (s : FighterState) : levelEffect d l s (fighterStartPhase P d l candidate s) := by
  let waiting := fighterAbortAbove d l (fighterCancel d l .replaced l s)
  have hw : levelEffect d l s waiting :=
    levelEffect_trans d l (levelEffect_cancel d l l le_rfl .replaced l s)
      (levelEffect_abortAbove d l _)
  have hp := levelEffect_putPhase d l waiting (fighter_construction P d l candidate waiting)
    (by simp [fighter_construction, FighterPhase.fundRequests])
  apply levelEffect_trans d l hw
  apply levelEffect_trans d l hp
  exact levelEffect_of_active_eq d l _ _ rfl (fun _ h ↦ h) rfl

private lemma levelEffect_flushBuffer (d l : ℕ) (s : FighterState) :
    levelEffect d l s ((fighterFlushBuffer d l s).getD s) := by
  cases hs : s.activeAt d l with
  | none => simpa [fighterFlushBuffer, hs] using levelEffect_refl d l s
  | some phase =>
    have hlevel := FighterState.level_eq_of_activeAt_eq_some (p := phase) hs
    simp only [fighterFlushBuffer, hs, bind, Option.bind_some]
    split
    · exact levelEffect_putPhase d l s
        { phase with
          officialCode := ((phase.game d).afterMove (phase.official d) phase.buffer).encode
          buffer := List.replicate (phase.game d).coordinates.length 0 } hlevel
    · exact levelEffect_refl d l s

private lemma levelEffect_strategyMove (P : FighterParams) (d l : ℕ) (s : FighterState) :
    levelEffect d l s ((fighterStrategyMove P d l s).getD s) := by
  cases hs : s.activeAt d l with
  | none => simpa [fighterStrategyMove, hs] using levelEffect_refl d l s
  | some phase =>
    simp only [fighterStrategyMove, hs, bind, Option.bind_some]
    split
    · cases hm : (phase.game d).strategy (phase.official d) with
      | none =>
        simp only [Option.bind_none, Option.getD_none]
        exact levelEffect_refl d l s
      | some move =>
        simp only [Option.bind_some]
        split
        · let next := ((phase.game d).coordinates.zipIdx).foldl (fun s (q, i) ↦
            fighterFuelUnits P d l q (move[i]?.getD 0) s) s
          have hn : levelEffect d l s next := by
            apply levelEffect_foldl
            intro qi t
            exact levelEffect_fuelUnits P d l qi.1 (move[qi.2]?.getD 0) t
          change levelEffect d l s
            ((match next.activeAt d l with
              | none => some next
              | some live => some (next.putPhase d
                  { live with officialCode :=
                      ((phase.game d).afterMove (phase.official d) move).encode })).getD s)
          cases hlive : next.activeAt d l with
          | none => exact hn
          | some live =>
            exact levelEffect_trans d l hn
              (levelEffect_putPhase d l next _
                (FighterState.level_eq_of_activeAt_eq_some (p := live) hlive))
        · exact levelEffect_refl d l s
    · exact levelEffect_refl d l s

private lemma levelEffect_levelAction (P : FighterParams) (d l : ℕ) (s : FighterState) :
    levelEffect d l s ((fighterLevelAction P d l s).getD s) := by
  cases hs : s.activeAt d l with
  | none => simpa [fighterLevelAction, hs] using levelEffect_refl d l s
  | some phase =>
    simp only [fighterLevelAction, hs, bind, Option.bind_some]
    split
    · exact levelEffect_dummy d l s
    · split
      · exact levelEffect_payoff P d l _ s
      · cases hf : fighterFlushBuffer d l s with
        | none => exact levelEffect_strategyMove P d l s
        | some next =>
          have h := levelEffect_flushBuffer d l s
          simpa only [hf] using h

private lemma levelEffect_closure (P : FighterParams) (d l fuel : ℕ) (s : FighterState) :
    levelEffect d l s (fighterClosure P d l fuel s) := by
  induction fuel generalizing s with
  | zero => exact levelEffect_refl d l s
  | succ fuel ih =>
    simp only [fighterClosure]
    cases ha : fighterLevelAction P d l s with
    | none => exact levelEffect_refl d l s
    | some next =>
      have hn := levelEffect_levelAction P d l s
      simp only [ha, Option.getD_some] at hn
      exact levelEffect_trans d l hn (ih next)

private lemma levelEffect_processLevel (P : FighterParams) (d l : ℕ) (event : Option TimedEvent)
    (s : FighterState) : levelEffect d l s (fighterProcessLevel P d l event s) := by
  unfold fighterProcessLevel
  apply levelEffect_trans d l (levelEffect_fulfillReady P d l s)
  cases event with
  | none => exact levelEffect_closure P d l _ _
  | some e =>
    dsimp only
    split
    · exact levelEffect_trans d l (levelEffect_startPhase P d l _ _)
        (levelEffect_closure P d l _ _)
    · exact levelEffect_trans d l (levelEffect_opponent P d l _ _)
        (levelEffect_closure P d l _ _)

private lemma fighterFlushBuffer_eq_none_iff (d l : ℕ) (s : FighterState) (phase : FighterPhase)
    (hs : s.activeAt d l = some phase) :
    fighterFlushBuffer d l s = none ↔
      ¬ (phase.predicateHolds d = false ∧
        (phase.game d).activePlayer (phase.official d) ≠ phase.controlledPlayer ∧
        (phase.game d).LegalMove (phase.official d) phase.buffer) := by
  simp [fighterFlushBuffer, hs]

/-- The controlled strategy move of an active level is disabled exactly when no legal move that
the strategy proposes fits in the remaining controlled budget at a position where the strategy
has to move. -/
theorem fighterStrategyMove_eq_none_iff (P : FighterParams) (d l : ℕ) (s : FighterState)
    (phase : FighterPhase) (hs : s.activeAt d l = some phase) :
    fighterStrategyMove P d l s = none ↔
      (phase.predicateHolds d = false ∧ phase.buffer.sum = 0 ∧
        (phase.game d).activePlayer (phase.official d) = phase.controlledPlayer →
        ∀ move, (phase.game d).strategy (phase.official d) = some move →
          ¬ ((phase.game d).LegalMove (phase.official d) move ∧
            move.sum ≤ phase.controlledRemaining)) := by
  simp only [fighterStrategyMove, hs, bind, Option.bind_some]
  by_cases hg : phase.predicateHolds d = false ∧ phase.buffer.sum = 0 ∧
      (phase.game d).activePlayer (phase.official d) = phase.controlledPlayer
  · simp only [hg, and_self, ite_true, true_implies]
    cases hm : (phase.game d).strategy (phase.official d) with
    | none => simp
    | some move =>
      simp only [Option.bind_some, Option.some.injEq, forall_eq']
      by_cases hmove : (phase.game d).LegalMove (phase.official d) move ∧
          move.sum ≤ phase.controlledRemaining
      · simp only [hmove, and_self, ite_true, not_true_eq_false, iff_false]
        split <;> simp
      · simp only [hmove, ite_false, not_false_eq_true]
  · simp [hg]

/-- An active level has no enabled internal action exactly when its dummy is not due, no safe
pending request is ready, its buffer cannot be flushed and its strategy has no move. -/
theorem fighterLevelAction_eq_none_iff (P : FighterParams) (d l : ℕ) (s : FighterState)
    (phase : FighterPhase) (hs : s.activeAt d l = some phase) :
    fighterLevelAction P d l s = none ↔
      (phase.dummy.isSome && !phase.dummyIssued) = false ∧
      phase.pending.find? (fun q ↦
        decide (q ∉ s.fulfilled) && fighterSafe P d s.tick q) = none ∧
      fighterFlushBuffer d l s = none ∧ fighterStrategyMove P d l s = none := by
  cases hd : phase.dummy.isSome && !phase.dummyIssued <;>
    cases hp : phase.pending.find? (fun q ↦
      decide (q ∉ s.fulfilled) && fighterSafe P d s.tick q) <;>
    cases hf : fighterFlushBuffer d l s <;>
    simp only [fighterLevelAction, hs, bind, Option.bind_some, hd, hp, hf] <;> simp

/-- A level that has no enabled action stays without one when a larger level is serviced
with an effect `levelEffect d l`. -/
private lemma fighterLevelAction_eq_none_of_levelEffect (P : FighterParams) (d l j : ℕ)
    (s t : FighterState) (heffect : levelEffect d l s t) (hj : j < l)
    (hnone : fighterLevelAction P d j s = none) : fighterLevelAction P d j t = none := by
  obtain ⟨keep, hactive⟩ := heffect.2.2.1 j hj
  cases hs : s.activeAt d j with
  | none => simp [fighterLevelAction, hactive, hs]
  | some phase =>
    have ht : t.activeAt d j = some { phase with pending := phase.pending.filter keep } := by
      simpa only [hs, Option.map_some] using hactive
    obtain ⟨hdummy, hpending, hflush, hstrategy⟩ :=
      (fighterLevelAction_eq_none_iff P d j s phase hs).mp hnone
    apply (fighterLevelAction_eq_none_iff P d j t _ ht).mpr
    refine ⟨hdummy, ?_, ?_, ?_⟩
    · apply List.find?_eq_none.mpr
      intro q hq htest
      have hold := List.find?_eq_none.mp hpending q (List.mem_filter.mp hq).1
      simp only [Bool.and_eq_true, decide_eq_true_eq] at htest
      apply hold
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨fun h ↦ htest.1 (heffect.2.1 h), heffect.1 ▸ htest.2⟩
    · apply (fighterFlushBuffer_eq_none_iff d j t _ ht).mpr
      exact (fighterFlushBuffer_eq_none_iff d j s phase hs).mp hflush
    · apply (fighterStrategyMove_eq_none_iff P d j t _ ht).mpr
      exact (fighterStrategyMove_eq_none_iff P d j s phase hs).mp hstrategy

/-- Processing a strictly larger level preserves the absence of enabled actions at a smaller
level. Successful payoffs may remove requests from the smaller phase, but cannot enable work. -/
private theorem fighterLevelAction_processLevel_eq_none_of_lt (P : FighterParams)
    (d l₁ l₂ : ℕ) (event : Option TimedEvent) (state : FighterState)
    (hlt : l₁ < l₂) (h : fighterLevelAction P d l₁ state = none) :
    fighterLevelAction P d l₁ (fighterProcessLevel P d l₂ event state) = none :=
  fighterLevelAction_eq_none_of_levelEffect P d l₂ l₁ state _
    (levelEffect_processLevel P d l₂ event state) hlt h

/-- The fold over larger levels preserves a previously completed smaller level. -/
private lemma fighterLevelAction_foldl_processLevel_eq_none_of_lt (P : FighterParams)
    (d l : ℕ) (event : Option TimedEvent) (levels : List ℕ) (state : FighterState)
    (hlt : ∀ j ∈ levels, l < j) (h : fighterLevelAction P d l state = none) :
    fighterLevelAction P d l
      (levels.foldl (fun s j ↦ fighterProcessLevel P d j event s) state) = none := by
  induction levels generalizing state with
  | nil => exact h
  | cons j levels ih =>
    exact ih _ (fun k hk ↦ hlt k (List.mem_cons_of_mem j hk))
      (fighterLevelAction_processLevel_eq_none_of_lt P d l j event state (hlt j (by simp)) h)

/-- Each level in a strictly increasing service list is completed by the fold that services
the list, and later levels preserve it. -/
private lemma fighterLevelAction_foldl_processLevel_eq_none (P : FighterParams) (d : ℕ)
    (event : Option TimedEvent) (levels : List ℕ) (state : FighterState)
    (hsorted : levels.Pairwise (· < ·)) (l : ℕ) (hl : l ∈ levels) :
    fighterLevelAction P d l
      (levels.foldl (fun s j ↦ fighterProcessLevel P d j event s) state) = none := by
  induction levels generalizing state with
  | nil => simp at hl
  | cons j levels ih =>
    rcases List.pairwise_cons.mp hsorted with ⟨hj, ht⟩
    rcases List.mem_cons.mp hl with rfl | hl
    · apply fighterLevelAction_foldl_processLevel_eq_none_of_lt P d l event levels _ hj
      unfold fighterProcessLevel
      exact fighter_closure_fixpoint P d l _
    · exact ih _ ht hl

/-- Sorting a deduplicated list of levels yields a strictly increasing list. -/
private lemma pairwise_lt_mergeSort_eraseDups (levels : List ℕ) :
    (levels.eraseDups.mergeSort (· ≤ ·)).Pairwise (· < ·) := by
  have hle := List.pairwise_mergeSort' (· ≤ ·) levels.eraseDups
  have hne : (levels.eraseDups.mergeSort (· ≤ ·)).Nodup := by
    rw [List.nodup_mergeSort]
    exact Kolmogorov.nodup_eraseDups_list _
  exact (hle.and hne).imp (fun h ↦ lt_of_le_of_ne h.1 h.2)

/-- Servicing one level can only retain existing active levels or introduce that particular
level. This concerns level membership; payoff fulfillment can change surviving phase records. -/
private theorem level_mem_active_processLevel (P : FighterParams) (d l : ℕ)
    (event : Option TimedEvent) (state : FighterState) :
    ∀ phase ∈ (fighterProcessLevel P d l event state).active,
      phase.level = l ∨ phase.level ∈ state.active.map FighterPhase.level :=
  (levelEffect_processLevel P d l event state).2.2.2

/-- Every phase surviving a finite service fold has an initial level or a level in the
service list. -/
private lemma level_mem_active_foldl_processLevel (P : FighterParams) (d : ℕ)
    (event : Option TimedEvent) (levels : List ℕ) (state : FighterState) :
    ∀ phase ∈ (levels.foldl (fun s l ↦ fighterProcessLevel P d l event s) state).active,
      phase.level ∈ levels ∨ phase.level ∈ state.active.map FighterPhase.level := by
  induction levels generalizing state with
  | nil =>
    intro phase hp
    exact Or.inr (List.mem_map_of_mem hp)
  | cons l levels ih =>
    intro phase hp
    rcases ih _ phase hp with h | h
    · exact Or.inl (List.mem_cons_of_mem l h)
    · rcases List.mem_map.mp h with ⟨old, hold, heq⟩
      rcases level_mem_active_processLevel P d l event state old hold with h | h
      · exact Or.inl (List.mem_cons.mpr (Or.inl (heq ▸ h)))
      · exact Or.inr (heq ▸ h)

/-- A completed tick leaves no enabled internal action at any active level.
Blueprint node `constr:effective`. Pending requests without an observed witness remain. -/
theorem fighter_event_actions_complete (P : FighterParams) (d tick : ℕ) :
    ∀ phase ∈ (fighterState P d tick).active,
      fighterLevelAction P d phase.level (fighterState P d tick) = none := by
  cases tick with
  | zero => simp [fighterState, initialFighterState]
  | succ tick =>
    intro phase hp
    change phase ∈ (fighter_actions P d (tick + 1) (fighterState P d tick)).active at hp
    change fighterLevelAction P d phase.level
      (fighter_actions P d (tick + 1) (fighterState P d tick)) = none
    unfold fighter_actions at hp ⊢
    by_cases hd : d = 0
    · simp [hd, initialFighterState] at hp
    · simp only [hd, ite_false] at hp ⊢
      let current := { fighterState P d tick with
          tick := tick + 1, schedule := masterState P.B (tick + 1) }
      let event := eventAt P.B (tick + 1)
      let owner := event.bind (fun e ↦ fighterOwner d e.2.2.1.length)
      let levels := current.active.map FighterPhase.level ++ owner.toList
      apply fighterLevelAction_foldl_processLevel_eq_none P d event _ current
        (pairwise_lt_mergeSort_eraseDups levels)
      rcases level_mem_active_foldl_processLevel P d event _ current phase hp with h | h
      · exact h
      · exact List.mem_mergeSort.mpr (List.mem_eraseDups.mpr (List.mem_append_left _ h))

end Kolmogorov.Milovanov
