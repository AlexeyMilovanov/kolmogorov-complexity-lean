/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Construction.Accounting
import KolmogorovMathlib.RandomStrings.Plain.Construction.Actions
import KolmogorovMathlib.RandomStrings.Plain.Construction.Effective
import KolmogorovMathlib.RandomStrings.Plain.Construction.State

/-!
# Properties of active phases are inherited from their construction

The fighter construction keeps a list of active phases in its state.  A phase is created only by
`fighter_construction`; every later action (counters, requests, payoffs, cancellations, moves of
the controlled strategy) rewrites other fields of the phase or removes it from the list, but never
changes its level, candidate, initial allocation snapshot or game code.

This module makes that precise.  `fighterProcessLevel_preserves_active` says that processing one
level at one tick keeps the clock unchanged and keeps any property `Q` of the four frozen fields
true of every active phase, provided `Q` holds of every freshly constructed phase.
`active_phase_of_construction` iterates this along the whole run `fighterState P d`, and
`fighterState_forall_active_of_init` restates it for a property of the fields in the order
level, candidate, game code, initial allocations.  They are
used by the true-marker invariants of the later modules of the stability argument, for instance
to show that the initial table of a phase is the one computed at its initialization.
-/

namespace Kolmogorov.Milovanov

/-- Every active phase of `s` satisfies `Q`, a property of the fields that are frozen when a
phase is constructed: level, candidate, initial allocations and game code. -/
abbrev ActivePhasesSatisfy
    (Q : ℕ → Candidate → List AllocatedDirective → CounterGameCode → Prop)
    (s : FighterState) : Prop :=
  ∀ p ∈ s.active, Q p.level p.candidate p.initialAllocations p.gameCode

/-- A transition from `s` to `t` that keeps the clock and leaves every active phase of `t`
satisfying the frozen-field property `Q`. -/
structure PhaseInvariantStep
    (Q : ℕ → Candidate → List AllocatedDirective → CounterGameCode → Prop)
    (s t : FighterState) : Prop where
  /-- The clock is unchanged. -/
  tick_eq : t.tick = s.tick
  /-- Every active phase satisfies `Q`. -/
  active : ActivePhasesSatisfy Q t

section Steps

variable {P : FighterParams} {d : ℕ}
  {Q : ℕ → Candidate → List AllocatedDirective → CounterGameCode → Prop}

private lemma PhaseInvariantStep.trans {s t u : FighterState} (h₁ : PhaseInvariantStep Q s t)
    (h₂ : PhaseInvariantStep Q t u) : PhaseInvariantStep Q s u :=
  ⟨h₂.1.trans h₁.1, h₂.2⟩

private lemma PhaseInvariantStep.foldl {α : Type} (f : α → FighterState → FighterState)
    (hf : ∀ a s, ActivePhasesSatisfy Q s → PhaseInvariantStep Q s (f a s))
    (xs : List α) (s : FighterState) (hs : ActivePhasesSatisfy Q s) :
    PhaseInvariantStep Q s (xs.foldl (fun s a ↦ f a s) s) := by
  induction xs generalizing s with
  | nil => exact ⟨rfl, hs⟩
  | cons a xs ih => exact (hf a s hs).trans (ih _ (hf a s hs).2)

private lemma satisfies_of_activeAt {s : FighterState} {j : ℕ} {phase : FighterPhase}
    (hs : ActivePhasesSatisfy Q s) (hp : s.activeAt d j = some phase) :
    Q phase.level phase.candidate phase.initialAllocations phase.gameCode :=
  hs phase (List.mem_of_find?_eq_some hp)

private lemma putPhase_invariantStep (s : FighterState) (phase : FighterPhase)
    (hs : ActivePhasesSatisfy Q s)
    (hp : Q phase.level phase.candidate phase.initialAllocations phase.gameCode) :
    PhaseInvariantStep Q s (s.putPhase d phase) := by
  refine ⟨rfl, ?_⟩
  intro p hmem
  rcases List.mem_cons.mp hmem with rfl | hmem
  · exact hp
  · exact hs p (List.mem_filter.mp hmem).1

private lemma fighterCancel_invariantStep (s : FighterState) (j : ℕ) (reason : PhaseEnd)
    (cause : ℕ) (hs : ActivePhasesSatisfy Q s) :
    PhaseInvariantStep Q s (fighterCancel d j reason cause s) := by
  unfold fighterCancel
  split
  · exact ⟨rfl, hs⟩
  · exact ⟨rfl, fun p hp ↦ hs p (List.mem_filter.mp hp).1⟩

private lemma fighterAbortAbove_invariantStep (s : FighterState) (j : ℕ)
    (hs : ActivePhasesSatisfy Q s) : PhaseInvariantStep Q s (fighterAbortAbove d j s) := by
  unfold fighterAbortAbove
  refine PhaseInvariantStep.foldl _ (fun p t ht ↦ ?_) _ s hs
  split
  · exact fighterCancel_invariantStep t p.level .aborted j ht
  · exact ⟨rfl, ht⟩

private lemma fighterAllocate_invariantStep (s : FighterState) (j : ℕ) (kind : DirectiveKind)
    (target : ℕ) (output : BitString) (hs : ActivePhasesSatisfy Q s) :
    PhaseInvariantStep Q s (fighterAllocate d j kind target output s).1 := by
  unfold fighterAllocate
  split
  · exact ⟨rfl, hs⟩
  · cases hf : (if target = 0 then (none : Option BitString) else
        (fighterInputs d (target - 1)).find? (fun p =>
          !s.allocated.any (fun a => a.input == p))) with
    | none =>
      have h := fighterCancel_invariantStep (d := d) { s with failed := true } j .saturated j hs
      exact ⟨h.1, h.2⟩
    | some p =>
      refine ⟨(fighterAbortAbove_invariantStep (d := d) (Q := Q) _ j ?_).1,
        (fighterAbortAbove_invariantStep (d := d) (Q := Q) _ j ?_).2⟩ <;> exact hs

private lemma fighterPayoff_invariantStep (s : FighterState) (j : ℕ) (q : Coordinate)
    (hs : ActivePhasesSatisfy Q s) : PhaseInvariantStep Q s (fighterPayoff P d j q s) := by
  unfold fighterPayoff
  split
  · exact ⟨rfl, hs⟩
  · split
    · have ha := fighterAllocate_invariantStep (d := d) s j .payoff q.2 q.1 hs
      cases he : fighterAllocate d j .payoff q.2 q.1 s with
      | mk next success =>
        simp only [he] at ha ⊢
        cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
        · exact ha
        · refine ⟨ha.1, ?_⟩
          intro p hp
          obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hp
          exact ha.2 old hold
    · exact ⟨rfl, hs⟩

private lemma fighterFulfillReady_invariantStep (s : FighterState) (j : ℕ)
    (hs : ActivePhasesSatisfy Q s) :
    PhaseInvariantStep Q s (fighterFulfillReady P d j s) := by
  unfold fighterFulfillReady
  split
  · exact ⟨rfl, hs⟩
  · exact PhaseInvariantStep.foldl (fun q t ↦ fighterPayoff P d j q t)
      (fun q t ht ↦ fighterPayoff_invariantStep t j q ht) _ s hs

private lemma fighterFuelUnit_invariantStep (s : FighterState) (j : ℕ) (q : Coordinate)
    (hs : ActivePhasesSatisfy Q s) : PhaseInvariantStep Q s (fighterFuelUnit P d j q s) := by
  unfold fighterFuelUnit
  split
  · exact ⟨rfl, hs⟩
  · rename_i phase hphase
    have hp := satisfies_of_activeAt hs hphase
    split
    · let charged := { phase with controlledRemaining := phase.controlledRemaining - 1 }
      let index := fighterFreshString d
        (phase.indices[(phase.game d).coordinates.idxOf q]?.getD [])
      let output := pairCode (triple q.1 (q.2 - d) phase.candidate.1) index
      have hc := putPhase_invariantStep (d := d) s charged hs hp
      have ha := fighterAllocate_invariantStep (d := d) (s.putPhase d charged) j .fuel
        (levelUpper j + d) output hc.2
      have hbefore := hc.trans ha
      change PhaseInvariantStep Q s
        (match fighterAllocate d j .fuel (levelUpper j + d) output (s.putPhase d charged) with
          | (next, success) => if success then fighterFulfillReady P d j
              (next.putPhase d ((charged.insertIndex d q index).fundRequests d next.fulfilled))
            else next)
      cases he : fighterAllocate d j .fuel (levelUpper j + d) output
          (s.putPhase d charged) with
      | mk next success =>
        rw [he] at hbefore
        cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
        · exact hbefore
        · have hput := putPhase_invariantStep (d := d) next
            ((charged.insertIndex d q index).fundRequests d next.fulfilled) hbefore.2 hp
          exact hbefore.trans (hput.trans (fighterFulfillReady_invariantStep _ j hput.2))
    · exact ⟨rfl, hs⟩

private lemma fighterFuelUnits_invariantStep (s : FighterState) (j : ℕ) (q : Coordinate)
    (count : ℕ) (hs : ActivePhasesSatisfy Q s) :
    PhaseInvariantStep Q s (fighterFuelUnits P d j q count s) := by
  induction count generalizing s with
  | zero => exact ⟨rfl, hs⟩
  | succ count ih =>
    exact (fighterFuelUnit_invariantStep s j q hs).trans
      (ih _ (fighterFuelUnit_invariantStep s j q hs).2)

private lemma fighterOpponent_invariantStep (s : FighterState) (j : ℕ) (e : ProgramEvent)
    (hs : ActivePhasesSatisfy Q s) :
    PhaseInvariantStep Q s (fighterOpponent P d j e s) := by
  unfold fighterOpponent
  split
  · exact ⟨rfl, hs⟩
  · rename_i phase hphase
    have hp := satisfies_of_activeAt hs hphase
    split
    · exact ⟨rfl, hs⟩
    · rename_i q index htuple
      split
      · exact ⟨rfl, hs⟩
      · split
        · exact fighterCancel_invariantStep s j .opponentExhausted j hs
        · let inserted := phase.insertIndex d q index
          let next := { inserted with
            opponentRemaining := phase.opponentRemaining - 1
            buffer := (phase.game d).addCounters phase.buffer (phase.unitVector d q) }
          have hput := putPhase_invariantStep (d := d) s (next.fundRequests d s.fulfilled) hs hp
          exact hput.trans (fighterFulfillReady_invariantStep _ j hput.2)

private lemma fighterDummy_invariantStep (s : FighterState) (j : ℕ)
    (hs : ActivePhasesSatisfy Q s) : PhaseInvariantStep Q s (fighterDummy d j s) := by
  unfold fighterDummy
  split
  · exact ⟨rfl, hs⟩
  · rename_i phase hphase
    have hp := satisfies_of_activeAt hs hphase
    split
    · exact ⟨rfl, hs⟩
    · rename_i output hout
      split
      · exact ⟨rfl, hs⟩
      · have ha := fighterAllocate_invariantStep (d := d) s j .dummy (levelInput d j) output hs
        cases he : fighterAllocate d j .dummy (levelInput d j) output s with
        | mk next success =>
          simp only [he] at ha ⊢
          cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
          · exact ha
          · exact ha.trans (putPhase_invariantStep (d := d) next _ ha.2 hp)

private lemma fighterFlushBuffer_invariantStep (s : FighterState) (j : ℕ)
    (hs : ActivePhasesSatisfy Q s) :
    PhaseInvariantStep Q s ((fighterFlushBuffer d j s).getD s) := by
  cases hphase : s.activeAt d j with
  | none =>
    have h : (fighterFlushBuffer d j s).getD s = s := by simp [fighterFlushBuffer, hphase]
    rw [h]
    exact ⟨rfl, hs⟩
  | some phase =>
    have hp := satisfies_of_activeAt hs hphase
    simp only [fighterFlushBuffer, hphase, bind, Option.bind_some]
    split
    · exact putPhase_invariantStep (d := d) s _ hs hp
    · exact ⟨rfl, hs⟩

private lemma fighterStrategyMove_invariantStep (s : FighterState) (j : ℕ)
    (hs : ActivePhasesSatisfy Q s) :
    PhaseInvariantStep Q s ((fighterStrategyMove P d j s).getD s) := by
  cases hphase : s.activeAt d j with
  | none =>
    have h : (fighterStrategyMove P d j s).getD s = s := by simp [fighterStrategyMove, hphase]
    rw [h]
    exact ⟨rfl, hs⟩
  | some phase =>
    simp only [fighterStrategyMove, hphase, bind, Option.bind_some]
    split
    · cases hm : (phase.game d).strategy (phase.official d) with
      | none => exact ⟨rfl, hs⟩
      | some move =>
        simp only [Option.bind_some]
        split
        · let next := (phase.game d).coordinates.zipIdx.foldl (fun s qi ↦
            fighterFuelUnits P d j qi.1 (move[qi.2]?.getD 0) s) s
          have hn : PhaseInvariantStep Q s next :=
            PhaseInvariantStep.foldl
              (fun (qi : Coordinate × ℕ) t ↦ fighterFuelUnits P d j qi.1 (move[qi.2]?.getD 0) t)
              (fun qi t ht ↦ fighterFuelUnits_invariantStep t j qi.1 _ ht) _ s hs
          change PhaseInvariantStep Q s ((match next.activeAt d j with
            | none => some next
            | some live => some (next.putPhase d { live with officialCode :=
                ((phase.game d).afterMove (phase.official d) move).encode })).getD s)
          cases hlive : next.activeAt d j with
          | none => exact hn
          | some live =>
            have hq := satisfies_of_activeAt hn.2 hlive
            exact hn.trans (putPhase_invariantStep (d := d) next _ hn.2 hq)
        · exact ⟨rfl, hs⟩
    · exact ⟨rfl, hs⟩

private lemma fighterLevelAction_invariantStep (s : FighterState) (j : ℕ)
    (hs : ActivePhasesSatisfy Q s) :
    PhaseInvariantStep Q s ((fighterLevelAction P d j s).getD s) := by
  cases hphase : s.activeAt d j with
  | none =>
    have h : (fighterLevelAction P d j s).getD s = s := by simp [fighterLevelAction, hphase]
    rw [h]
    exact ⟨rfl, hs⟩
  | some phase =>
    simp only [fighterLevelAction, hphase, bind, Option.bind_some]
    split
    · exact fighterDummy_invariantStep s j hs
    · split
      · exact fighterPayoff_invariantStep s j _ hs
      · cases hf : fighterFlushBuffer d j s with
        | none => exact fighterStrategyMove_invariantStep s j hs
        | some next =>
          simpa only [hf, Option.getD_some] using
            fighterFlushBuffer_invariantStep (d := d) s j hs

private lemma fighterClosure_invariantStep (fuel : ℕ) (s : FighterState) (j : ℕ)
    (hs : ActivePhasesSatisfy Q s) :
    PhaseInvariantStep Q s (fighterClosure P d j fuel s) := by
  induction fuel generalizing s with
  | zero => exact ⟨rfl, hs⟩
  | succ fuel ih =>
    simp only [fighterClosure]
    cases ha : fighterLevelAction P d j s with
    | none => exact ⟨rfl, hs⟩
    | some next =>
      have hn := fighterLevelAction_invariantStep (P := P) (d := d) s j hs
      simp only [ha, Option.getD_some] at hn
      exact hn.trans (ih next hn.2)

end Steps

/-- Processing one level at one tick keeps the clock and the property `Q` of the frozen fields of
all active phases, provided `Q` holds of every phase the level may construct at this event.
Blueprint node `constr:realization` (supporting lemma). -/
theorem fighterProcessLevel_preserves_active (P : FighterParams) (d l : ℕ)
    (ev : Option TimedEvent) (s : FighterState)
    (Q : ℕ → Candidate → List AllocatedDirective → CounterGameCode → Prop)
    (he : ∀ e, ev = some e → e.1 = s.tick)
    (hnew : ∀ (c : Candidate) (b : FighterState), c.2 = b.tick →
      Q l c (fighter_construction P d l c b).initialAllocations
        (fighter_construction P d l c b).gameCode)
    (hs : ActivePhasesSatisfy Q s) :
    PhaseInvariantStep Q s (fighterProcessLevel P d l ev s) := by
  have start (t : FighterState) (candidate : Candidate)
      (ht : candidate.2 = t.tick) (hs : ActivePhasesSatisfy Q t) :
      PhaseInvariantStep Q t (fighterStartPhase P d l candidate t) := by
    let waiting := fighterAbortAbove d l (fighterCancel d l .replaced l t)
    have hc := fighterCancel_invariantStep (d := d) t l .replaced l hs
    have hw := hc.trans (fighterAbortAbove_invariantStep (d := d) _ l hc.2)
    have hp := putPhase_invariantStep (d := d) waiting
      (fighter_construction P d l candidate waiting) hw.2
      (hnew candidate waiting (ht.trans hw.1.symm))
    exact ⟨hp.1.trans hw.1, hp.2⟩
  unfold fighterProcessLevel
  have hc := fighterFulfillReady_invariantStep (P := P) (d := d) s l hs
  refine hc.trans ?_
  cases ev with
  | none => exact fighterClosure_invariantStep _ _ l hc.2
  | some e =>
    dsimp only
    split
    · have hn := start _ (e.2.2.1, e.1) ((he e rfl).trans hc.1.symm) hc.2
      exact hn.trans (fighterClosure_invariantStep _ _ l hn.2)
    · have hn := fighterOpponent_invariantStep (P := P) (d := d) _ l e.2.2 hc.2
      exact hn.trans (fighterClosure_invariantStep _ _ l hn.2)

/-- A property of the frozen fields (level, candidate, initial allocations, game code) that holds
of every phase at its construction holds of every active phase at every tick.
Blueprint node `constr:realization` (supporting lemma). -/
theorem active_phase_of_construction (P : FighterParams) (d : ℕ)
    (Q : ℕ → Candidate → List AllocatedDirective → CounterGameCode → Prop)
    (hnew : ∀ (l : ℕ) (c : Candidate) (s : FighterState), c.2 = s.tick →
      Q l c (fighter_construction P d l c s).initialAllocations
        (fighter_construction P d l c s).gameCode) :
    ∀ tick, ActivePhasesSatisfy Q (fighterState P d tick) := by
  intro tick
  induction tick with
  | zero =>
    intro p hp
    simp [fighterState, initialFighterState] at hp
  | succ tick ih =>
    let event := eventAt P.B (tick + 1)
    have hevent : ∀ e, event = some e → e.1 = tick + 1 := by
      intro e he
      dsimp [event, eventAt] at he
      rw [Option.filter_eq_some_iff] at he
      exact of_decide_eq_true he.2
    have hfold (ls : List ℕ) (s : FighterState) (ht : s.tick = tick + 1)
        (hs : ActivePhasesSatisfy Q s) :
        PhaseInvariantStep Q s (ls.foldl (fun s l ↦ fighterProcessLevel P d l event s) s) := by
      induction ls generalizing s with
      | nil => exact ⟨rfl, hs⟩
      | cons j ls ihls =>
        have hstep := fighterProcessLevel_preserves_active P d j event s Q
          (fun e he ↦ (hevent e he).trans ht.symm) (hnew j) hs
        exact hstep.trans (ihls _ (hstep.1.trans ht) hstep.2)
    dsimp [fighterState, fighter_actions]
    split
    · intro p hp
      simp [initialFighterState] at hp
    · let current : FighterState :=
        { fighterState P d tick with tick := tick + 1, schedule := masterState P.B (tick + 1) }
      exact (hfold _ current rfl ih).2

/-- Every active phase satisfies any initialization property of its frozen fields, with the
fields in the order level, candidate, game code, initial allocations: the form of
`active_phase_of_construction` used by the diagonal argument, whose property need not use the
clock of the construction. -/
theorem fighterState_forall_active_of_init
    (P : FighterParams) (d tick : ℕ)
    (Q : ℕ → Candidate → CounterGameCode → List AllocatedDirective → Prop)
    (hinit : ∀ l c s, Q l c (fighter_construction P d l c s).gameCode
      (fighter_construction P d l c s).initialAllocations) :
    ∀ phase ∈ (fighterState P d tick).active,
      Q phase.level phase.candidate phase.gameCode phase.initialAllocations :=
  active_phase_of_construction P d (fun l c a g ↦ Q l c g a) (fun l c s _ ↦ hinit l c s) tick

end Kolmogorov.Milovanov
