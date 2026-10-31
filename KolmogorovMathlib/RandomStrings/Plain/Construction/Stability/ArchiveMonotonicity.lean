/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Construction.Actions

/-!
# Monotonicity of the fighter cancellation archive

Every fighter transition retains all previously archived cancellations. We prove this first
for allocation and payoff processing, then for opponent events, internal closure, and a complete
level service. `CommonGameInvariantTick` uses these facts to transport a cancellation before
closure to the completed tick, where the capacity and opponent-exhaustion bounds exclude it.
These are supporting facts for blueprint node `constr:opponent`.
-/

namespace Kolmogorov.Milovanov

private lemma ended_subset_foldl {α : Type} (f : α → FighterState → FighterState)
    (hf : ∀ a s, s.ended ⊆ (f a s).ended) (xs : List α) (s : FighterState) :
    s.ended ⊆ (xs.foldl (fun s a ↦ f a s) s).ended := by
  induction xs generalizing s with
  | nil => exact List.Subset.refl _
  | cons a xs ih => exact List.Subset.trans (hf a s) (ih _)

private lemma ended_subset_fighterCancel
    (d l cause : ℕ) (reason : PhaseEnd) (s : FighterState) :
    s.ended ⊆ (fighterCancel d l reason cause s).ended := by
  unfold fighterCancel
  split
  · exact List.Subset.refl _
  · exact fun _ h ↦ List.mem_append_left _ h

private lemma ended_subset_fighterAbortAbove
    (d l : ℕ) (s : FighterState) :
    s.ended ⊆ (fighterAbortAbove d l s).ended := by
  unfold fighterAbortAbove
  apply ended_subset_foldl
  intro p t
  split
  · exact ended_subset_fighterCancel d _ _ _ _
  · exact List.Subset.refl _

private lemma ended_subset_fighterAllocate
    (d l : ℕ) (kind : DirectiveKind) (target : ℕ) (out : BitString)
    (s : FighterState) :
    s.ended ⊆ (fighterAllocate d l kind target out s).1.ended := by
  unfold fighterAllocate
  split
  · exact List.Subset.refl _
  · rename_i phase hp
    cases hf : (if target = 0 then (none : Option BitString) else
        (fighterInputs d (target - 1)).find? (fun p ↦
          !s.allocated.any (fun a ↦ a.input == p))) with
    | none => exact ended_subset_fighterCancel d l l .saturated { s with failed := true }
    | some input =>
      exact ended_subset_fighterAbortAbove d l { s with allocated := s.allocated ++
        [⟨l, phase.candidate, s.tick, kind, target, input, out⟩] }

/-- Processing a payoff retains every archived cancellation. -/
lemma ended_subset_fighterPayoff
    (P : FighterParams) (d l : ℕ) (q : Coordinate) (s : FighterState) :
    s.ended ⊆ (fighterPayoff P d l q s).ended := by
  unfold fighterPayoff
  split
  · exact List.Subset.refl _
  · split
    · have ha := ended_subset_fighterAllocate d l .payoff q.2 q.1 s
      cases he : fighterAllocate d l .payoff q.2 q.1 s with
      | mk next success =>
        simp only [he] at ha ⊢
        cases success <;> exact ha
    · exact List.Subset.refl _

/-- Fulfilling ready payoff requests retains every archived cancellation. -/
lemma ended_subset_fighterFulfillReady
    (P : FighterParams) (d l : ℕ) (s : FighterState) :
    s.ended ⊆ (fighterFulfillReady P d l s).ended := by
  unfold fighterFulfillReady
  split
  · exact List.Subset.refl _
  · exact ended_subset_foldl _ (ended_subset_fighterPayoff P d l) _ _

private lemma ended_subset_fighterFuelUnit
    (P : FighterParams) (d l : ℕ) (q : Coordinate) (s : FighterState) :
    s.ended ⊆ (fighterFuelUnit P d l q s).ended := by
  unfold fighterFuelUnit
  split
  · exact List.Subset.refl _
  · rename_i phase hp
    split
    · let charged := { phase with controlledRemaining := phase.controlledRemaining - 1 }
      let index := fighterFreshString d
        (phase.indices[(phase.game d).coordinates.idxOf q]?.getD [])
      let out := pairCode (triple q.1 (q.2 - d) phase.candidate.1) index
      have ha := ended_subset_fighterAllocate
        d l .fuel (levelUpper l + d) out (s.putPhase d charged)
      change s.ended ⊆
        (match fighterAllocate d l .fuel (levelUpper l + d) out (s.putPhase d charged) with
          | (next, success) => if success then
            fighterFulfillReady P d l
              (next.putPhase d ((charged.insertIndex d q index).fundRequests d next.fulfilled))
            else next).ended
      cases he : fighterAllocate d l .fuel (levelUpper l + d) out (s.putPhase d charged) with
      | mk next success =>
        rw [he] at ha
        cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
        · exact ha
        · exact List.Subset.trans ha (ended_subset_fighterFulfillReady P d l
            (next.putPhase d ((charged.insertIndex d q index).fundRequests d next.fulfilled)))
    · exact List.Subset.refl _

private lemma ended_subset_fighterFuelUnits
    (P : FighterParams) (d l : ℕ) (q : Coordinate) (count : ℕ) (s : FighterState) :
    s.ended ⊆ (fighterFuelUnits P d l q count s).ended := by
  induction count generalizing s with
  | zero => exact List.Subset.refl _
  | succ count ih => exact List.Subset.trans (ended_subset_fighterFuelUnit P d l q s) (ih _)

/-- Handling an opponent event retains every archived cancellation. -/
lemma ended_subset_fighterOpponent
    (P : FighterParams) (d l : ℕ) (event : ProgramEvent) (s : FighterState) :
    s.ended ⊆ (fighterOpponent P d l event s).ended := by
  unfold fighterOpponent
  split
  · exact List.Subset.refl _
  · rename_i phase hp
    split
    · exact List.Subset.refl _
    · rename_i q index ht
      split
      · exact List.Subset.refl _
      · split
        · exact ended_subset_fighterCancel d _ _ _ _
        · let inserted := phase.insertIndex d q index
          let next := { inserted with
            opponentRemaining := phase.opponentRemaining - 1
            buffer := (phase.game d).addCounters phase.buffer (phase.unitVector d q) }
          exact ended_subset_fighterFulfillReady
            P d l (s.putPhase d (next.fundRequests d s.fulfilled))

private lemma ended_subset_fighterDummy
    (d l : ℕ) (s : FighterState) :
    s.ended ⊆ (fighterDummy d l s).ended := by
  unfold fighterDummy
  split
  · exact List.Subset.refl _
  · split
    · exact List.Subset.refl _
    · rename_i output hout
      split
      · exact List.Subset.refl _
      · have ha := ended_subset_fighterAllocate d l .dummy (levelInput d l) output s
        cases he : fighterAllocate d l .dummy (levelInput d l) output s with
        | mk next success =>
          simp only [he] at ha ⊢
          cases success <;> exact ha

private lemma ended_subset_fighterFlushBuffer
    (d l : ℕ) (s : FighterState) :
    s.ended ⊆ ((fighterFlushBuffer d l s).getD s).ended := by
  unfold fighterFlushBuffer
  cases hp : s.activeAt d l with
  | none => exact List.Subset.refl _
  | some phase =>
    simp only [bind, Option.bind_some]
    split <;> exact List.Subset.refl _

private lemma ended_subset_fighterStrategyMove
    (P : FighterParams) (d l : ℕ) (s : FighterState) :
    s.ended ⊆ ((fighterStrategyMove P d l s).getD s).ended := by
  unfold fighterStrategyMove
  cases hp : s.activeAt d l with
  | none => exact List.Subset.refl _
  | some phase =>
    simp only [bind, Option.bind_some]
    split
    · cases hm : (phase.game d).strategy (phase.official d) with
      | none => exact List.Subset.refl _
      | some move =>
        simp only [Option.bind_some]
        split
        · let next := (phase.game d).coordinates.zipIdx.foldl (fun s (q, i) ↦
            fighterFuelUnits P d l q (move[i]?.getD 0) s) s
          have hn : s.ended ⊆ next.ended := ended_subset_foldl _
            (fun (qi : Coordinate × ℕ) t ↦
              ended_subset_fighterFuelUnits P d l qi.1 (move[qi.2]?.getD 0) t) _ s
          change s.ended ⊆ ((match next.activeAt d l with
            | none => some next
            | some live => some (next.putPhase d
              { live with officialCode :=
                  ((phase.game d).afterMove (phase.official d) move).encode })).getD s).ended
          split <;> exact hn
        · exact List.Subset.refl _
    · exact List.Subset.refl _

private lemma ended_subset_fighterLevelAction
    (P : FighterParams) (d l : ℕ) (s : FighterState) :
    s.ended ⊆ ((fighterLevelAction P d l s).getD s).ended := by
  unfold fighterLevelAction
  cases hp : s.activeAt d l with
  | none => exact List.Subset.refl _
  | some phase =>
    simp only [bind, Option.bind_some]
    split
    · exact ended_subset_fighterDummy d l s
    · split
      · exact ended_subset_fighterPayoff P d l _ s
      · cases hf : fighterFlushBuffer d l s with
        | none => exact ended_subset_fighterStrategyMove P d l s
        | some next =>
          have h := ended_subset_fighterFlushBuffer d l s
          simpa only [hf, Option.getD_some] using h

/-- Internal closure retains every archived cancellation, for any fuel budget. -/
lemma ended_subset_fighterClosure
    (P : FighterParams) (d l fuel : ℕ) (s : FighterState) :
    s.ended ⊆ (fighterClosure P d l fuel s).ended := by
  induction fuel generalizing s with
  | zero => exact List.Subset.refl _
  | succ fuel ih =>
    simp only [fighterClosure]
    cases ha : fighterLevelAction P d l s with
    | none => exact List.Subset.refl _
    | some next =>
      have hn := ended_subset_fighterLevelAction P d l s
      simp only [ha, Option.getD_some] at hn
      exact List.Subset.trans hn (ih next)

private lemma ended_subset_fighterStartPhase
    (P : FighterParams) (d l : ℕ) (c : Candidate) (s : FighterState) :
    s.ended ⊆ (fighterStartPhase P d l c s).ended := by
  unfold fighterStartPhase
  exact List.Subset.trans (ended_subset_fighterCancel d l l .replaced s)
    (ended_subset_fighterAbortAbove d l _)

/-- A complete service at any level retains every archived cancellation. -/
lemma ended_subset_fighterProcessLevel
    (P : FighterParams) (d l : ℕ) (event : Option TimedEvent) (s : FighterState) :
    s.ended ⊆ (fighterProcessLevel P d l event s).ended := by
  unfold fighterProcessLevel fighterCloseLevel
  apply List.Subset.trans _ (ended_subset_fighterClosure P d l _ _)
  cases event with
  | none => exact ended_subset_fighterFulfillReady P d l s
  | some e =>
    dsimp only
    split
    · exact List.Subset.trans (ended_subset_fighterFulfillReady P d l s)
        (ended_subset_fighterStartPhase P d l _ _)
    · exact List.Subset.trans (ended_subset_fighterFulfillReady P d l s)
        (ended_subset_fighterOpponent P d l _ _)

end Kolmogorov.Milovanov
