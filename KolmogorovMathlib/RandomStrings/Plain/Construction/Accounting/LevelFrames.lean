/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Construction.Actions

/-!
# Clock and allocation frames for level processing

Each operation servicing a level keeps the clock fixed and can allocate new directives
only at that level. These frame properties compose along lists of operations and through
closure. `FuelHistory` uses them to retain timestamp freshness at levels that have not yet
been processed, as required by the dummy part of the phase-count argument
(blueprint node `constr:phasecount`).
-/

namespace Kolmogorov.Milovanov

private def levelFrame (l : ℕ) (s t : FighterState) : Prop :=
  t.tick = s.tick ∧ ∀ a ∈ t.allocated, a ∈ s.allocated ∨ a.level = l

variable {P : FighterParams} {d l : ℕ}

private lemma levelFrame_refl (s : FighterState) : levelFrame l s s := ⟨rfl, fun _ h ↦ Or.inl h⟩

private lemma levelFrame_trans {s t u : FighterState}
    (hst : levelFrame l s t) (htu : levelFrame l t u) :
    levelFrame l s u := by
  refine ⟨htu.1.trans hst.1, ?_⟩
  intro a ha
  rcases htu.2 a ha with ha | ha
  · exact hst.2 a ha
  · exact Or.inr ha

private lemma levelFrame_fold {α : Type} (f : α → FighterState → FighterState)
    (hf : ∀ a s, levelFrame l s (f a s)) (xs : List α) (s : FighterState) :
    levelFrame l s (xs.foldl (fun s a ↦ f a s) s) := by
  induction xs generalizing s with
  | nil => exact levelFrame_refl s
  | cons a xs ih => exact levelFrame_trans (hf a s) (ih _)

private lemma levelFrame_cancel (j : ℕ) (reason : PhaseEnd) (cause : ℕ) (s : FighterState) :
    levelFrame l s (fighterCancel d j reason cause s) := by
  unfold fighterCancel
  split <;> exact levelFrame_refl s

private lemma levelFrame_abortAbove (j : ℕ) (s : FighterState) :
    levelFrame l s (fighterAbortAbove d j s) := by
  unfold fighterAbortAbove
  apply levelFrame_fold
  intro p t
  split
  · exact levelFrame_cancel _ _ _ _
  · exact levelFrame_refl t

private lemma levelFrame_putPhase (s : FighterState) (phase : FighterPhase) :
    levelFrame l s (s.putPhase d phase) :=
  ⟨rfl, fun _ h ↦ Or.inl h⟩

private lemma levelFrame_allocate (kind : DirectiveKind) (target : ℕ) (out : BitString)
    (s : FighterState) :
    levelFrame l s (fighterAllocate d l kind target out s).1 := by
  unfold fighterAllocate
  split
  · exact levelFrame_refl s
  · cases hf : (if target = 0 then (none : Option BitString) else
        (fighterInputs d (target - 1)).find? (fun p ↦
          !s.allocated.any (fun a ↦ a.input == p))) with
    | none => exact levelFrame_cancel l .saturated l { s with failed := true }
    | some p =>
      apply levelFrame_trans (t := { s with allocated := s.allocated ++ [_] }) ?_
        (levelFrame_abortAbove l _)
      refine ⟨rfl, ?_⟩
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact Or.inl ha
      · obtain rfl := List.mem_singleton.mp ha
        exact Or.inr rfl

private lemma levelFrame_payoff (q : Coordinate) (s : FighterState) :
    levelFrame l s (fighterPayoff P d l q s) := by
  unfold fighterPayoff
  split
  · exact levelFrame_refl s
  · split
    · have h := levelFrame_allocate (d := d) (l := l) .payoff q.2 q.1 s
      cases he : fighterAllocate d l .payoff q.2 q.1 s with
      | mk next success =>
        rw [he] at h
        cases success <;> exact h
    · exact levelFrame_refl s

private lemma levelFrame_fulfillReady (s : FighterState) :
    levelFrame l s (fighterFulfillReady P d l s) := by
  unfold fighterFulfillReady
  split
  · exact levelFrame_refl s
  · exact levelFrame_fold (fun q s ↦ fighterPayoff P d l q s) levelFrame_payoff _ _

private lemma levelFrame_fuelUnit (q : Coordinate) (s : FighterState) :
    levelFrame l s (fighterFuelUnit P d l q s) := by
  unfold fighterFuelUnit
  split
  · exact levelFrame_refl s
  · rename_i phase hs
    split
    · have h := levelFrame_trans
        (levelFrame_putPhase (d := d) (l := l) s { phase with
          controlledRemaining := phase.controlledRemaining - 1 })
        (levelFrame_allocate (d := d) .fuel (levelUpper l + d)
          (pairCode (triple q.1 (q.2 - d) phase.candidate.1)
            (fighterFreshString d
              (phase.indices[(phase.game d).coordinates.idxOf q]?.getD []))) _)
      dsimp only
      split
      · exact levelFrame_trans h
          (levelFrame_trans (levelFrame_putPhase (d := d) _ _) (levelFrame_fulfillReady _))
      · exact h
    · exact levelFrame_refl s

private lemma levelFrame_fuelUnits (q : Coordinate) (count : ℕ) (s : FighterState) :
    levelFrame l s (fighterFuelUnits P d l q count s) := by
  induction count generalizing s with
  | zero => exact levelFrame_refl s
  | succ count ih => exact levelFrame_trans (levelFrame_fuelUnit q s) (ih _)

private lemma levelFrame_dummy (s : FighterState) :
    levelFrame l s (fighterDummy d l s) := by
  unfold fighterDummy
  split
  · exact levelFrame_refl s
  · split
    · exact levelFrame_refl s
    · rename_i output hout
      split
      · exact levelFrame_refl s
      · have h := levelFrame_allocate (d := d) (l := l) .dummy (levelInput d l) output s
        dsimp only
        split
        · exact levelFrame_trans h (levelFrame_putPhase (d := d) _ _)
        · exact h

private lemma levelFrame_flushBuffer (s : FighterState) :
    levelFrame l s ((fighterFlushBuffer d l s).getD s) := by
  cases hs : s.activeAt d l with
  | none => simpa [fighterFlushBuffer, hs] using levelFrame_refl s
  | some phase =>
    simp only [fighterFlushBuffer, hs, bind, Option.bind_some]
    split
    · exact levelFrame_putPhase (d := d) _ _
    · exact levelFrame_refl s

private lemma levelFrame_strategyMove (s : FighterState) :
    levelFrame l s ((fighterStrategyMove P d l s).getD s) := by
  cases hs : s.activeAt d l with
  | none => simpa [fighterStrategyMove, hs] using levelFrame_refl s
  | some phase =>
    simp only [fighterStrategyMove, hs, bind, Option.bind_some]
    split
    · cases hm : (phase.game d).strategy (phase.official d) with
      | none => exact levelFrame_refl s
      | some move =>
        simp only [Option.bind_some]
        split
        · let next := ((phase.game d).coordinates.zipIdx).foldl (fun s (q, i) ↦
            fighterFuelUnits P d l q (move[i]?.getD 0) s) s
          have hn : levelFrame l s next := levelFrame_fold _
            (fun (qi : Coordinate × ℕ) t ↦ levelFrame_fuelUnits qi.1 _ t) _ _
          change levelFrame l s ((match next.activeAt d l with
            | none => some next
            | some live => some (next.putPhase d
                { live with officialCode :=
                  ((phase.game d).afterMove (phase.official d) move).encode })).getD s)
          cases hlive : next.activeAt d l with
          | none => exact hn
          | some live => exact levelFrame_trans hn (levelFrame_putPhase (d := d) _ _)
        · exact levelFrame_refl s
    · exact levelFrame_refl s

private lemma levelFrame_levelAction (s : FighterState) :
    levelFrame l s ((fighterLevelAction P d l s).getD s) := by
  cases hs : s.activeAt d l with
  | none => simpa [fighterLevelAction, hs] using levelFrame_refl s
  | some phase =>
    simp only [fighterLevelAction, hs, bind, Option.bind_some]
    split
    · exact levelFrame_dummy s
    · split
      · exact levelFrame_payoff _ s
      · cases hf : fighterFlushBuffer d l s with
        | none => exact levelFrame_strategyMove s
        | some next => simpa only [hf] using levelFrame_flushBuffer (d := d) (l := l) s

private lemma levelFrame_closure (fuel : ℕ) (s : FighterState) :
    levelFrame l s (fighterClosure P d l fuel s) := by
  induction fuel generalizing s with
  | zero => exact levelFrame_refl s
  | succ fuel ih =>
    simp only [fighterClosure]
    cases ha : fighterLevelAction P d l s with
    | none => exact levelFrame_refl s
    | some next =>
      have h := levelFrame_levelAction (P := P) (d := d) (l := l) s
      simp only [ha, Option.getD_some] at h
      exact levelFrame_trans h (ih next)

private lemma levelFrame_startPhase (candidate : Candidate) (s : FighterState) :
    levelFrame l s (fighterStartPhase P d l candidate s) := by
  unfold fighterStartPhase
  exact levelFrame_trans (levelFrame_cancel l .replaced l s) (levelFrame_abortAbove l _)

private lemma levelFrame_opponent (e : ProgramEvent) (s : FighterState) :
    levelFrame l s (fighterOpponent P d l e s) := by
  unfold fighterOpponent
  split
  · exact levelFrame_refl s
  · split
    · exact levelFrame_refl s
    · split
      · exact levelFrame_refl s
      · split
        · exact levelFrame_cancel _ _ _ s
        · exact levelFrame_trans (levelFrame_putPhase (d := d) _ _) (levelFrame_fulfillReady _)

/-- Servicing a level fixes the clock and introduces allocations only at that level. -/
lemma processLevel_tick_allocated
    (P : FighterParams) (d l : ℕ) (event : Option TimedEvent) (state : FighterState) :
    (fighterProcessLevel P d l event state).tick = state.tick ∧
      ∀ a ∈ (fighterProcessLevel P d l event state).allocated,
        a ∈ state.allocated ∨ a.level = l := by
  unfold fighterProcessLevel fighterCloseLevel
  apply levelFrame_trans (levelFrame_fulfillReady state)
  cases event with
  | none => exact levelFrame_closure _ _
  | some e =>
    dsimp only
    split
    · exact levelFrame_trans (levelFrame_startPhase _ _) (levelFrame_closure _ _)
    · exact levelFrame_trans (levelFrame_opponent _ _) (levelFrame_closure _ _)

end Kolmogorov.Milovanov
