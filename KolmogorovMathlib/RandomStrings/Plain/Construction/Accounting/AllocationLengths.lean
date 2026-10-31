/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Construction.Effective

/-!
# Input lengths in the permanent allocation table

Every successful directive allocates an input exactly one bit shorter than its target.
This module follows that property through the fighter's state operations, while also
tracking inclusion of permanent allocation tables. No assumption on the initial state
or on the availability of descriptions is needed: failed attempts add no entries.

The tick-level result is shared by `CapacityFailure`, which counts occupied inputs
for blueprint node `constr:capacity`, and `UniformRank`, which bounds outputs at a given
input length for blueprint node `constr:smallset`.
-/

namespace Kolmogorov.Milovanov

/-- The table grows, and each new entry has the required input length. -/
private def allocationLengthExtension (s t : FighterState) : Prop :=
  s.allocated ⊆ t.allocated ∧
    ∀ a ∈ t.allocated, a ∈ s.allocated ∨ a.input.length + 1 = a.target

private lemma length_extension_refl
    (s : FighterState) : allocationLengthExtension s s := ⟨fun _ h ↦ h, fun _ h ↦ Or.inl h⟩

private lemma length_extension_trans {s t u : FighterState}
    (hst : allocationLengthExtension s t) (htu : allocationLengthExtension t u) :
    allocationLengthExtension s u := by
  refine ⟨fun _ h ↦ htu.1 (hst.1 h), ?_⟩
  intro a ha
  rcases htu.2 a ha with ha | ha
  · exact hst.2 a ha
  · exact Or.inr ha

private lemma length_extension_of_allocated_eq
    (s t : FighterState) (h : t.allocated = s.allocated) : allocationLengthExtension s t := by
  change s.allocated ⊆ t.allocated ∧ _
  rw [h]
  exact ⟨fun _ h ↦ h, fun _ h ↦ Or.inl h⟩

private lemma length_extension_foldl {α : Type} (f : α → FighterState → FighterState)
    (hf : ∀ a s, allocationLengthExtension s (f a s)) (xs : List α) (s : FighterState) :
    allocationLengthExtension s (xs.foldl (fun s a ↦ f a s) s) := by
  induction xs generalizing s with
  | nil => exact length_extension_refl s
  | cons a xs ih => exact length_extension_trans (hf a s) (ih _)

private lemma length_extension_cancel (d l : ℕ) (reason : PhaseEnd) (cause : ℕ) (s : FighterState) :
    allocationLengthExtension s (fighterCancel d l reason cause s) := by
  apply length_extension_of_allocated_eq
  unfold fighterCancel
  split <;> rfl

private lemma length_extension_abort_above
    (d l : ℕ) (s : FighterState) : allocationLengthExtension s (fighterAbortAbove d l s) := by
  unfold fighterAbortAbove
  apply length_extension_foldl
  intro p t
  split
  · exact length_extension_cancel d _ _ _ _
  · exact length_extension_refl t

private lemma length_extension_put_phase
    (d : ℕ) (s : FighterState) (phase : FighterPhase) :
    allocationLengthExtension s (s.putPhase d phase) :=
  length_extension_of_allocated_eq _ _ rfl

private lemma length_extension_allocate
    (d l : ℕ) (kind : DirectiveKind) (target : ℕ) (out : BitString)
    (s : FighterState) : allocationLengthExtension s (fighterAllocate d l kind target out s).1 := by
  unfold fighterAllocate
  cases hs : s.activeAt d l with
  | none => exact length_extension_refl s
  | some phase =>
    dsimp only
    by_cases ht : target = 0
    · simp only [ht, ↓reduceIte]
      exact length_extension_trans (t := { s with failed := true })
        (length_extension_of_allocated_eq _ _ rfl) (length_extension_cancel d _ _ _ _)
    · simp only [ht, ↓reduceIte]
      cases hf : (fighterInputs d (target - 1)).find?
          (fun p ↦ !s.allocated.any (fun a ↦ a.input == p)) with
      | none =>
        exact length_extension_trans (t := { s with failed := true })
          (length_extension_of_allocated_eq _ _ rfl) (length_extension_cancel d _ _ _ _)
      | some p =>
        have hp : p ∈ fighterInputs d (target - 1) := List.mem_of_find?_eq_some hf
        have hlen := length_eq_of_mem_fighterInputs d (target - 1) p hp
        apply length_extension_trans (t := { s with allocated := s.allocated ++
          [⟨l, phase.candidate, s.tick, kind, target, p, out⟩] })
        · refine ⟨fun _ h ↦ List.mem_append_left _ h, ?_⟩
          intro a ha
          rcases List.mem_append.mp ha with ha | ha
          · exact Or.inl ha
          · have heq := List.mem_singleton.mp ha
            subst a
            exact Or.inr (by dsimp; omega)
        · exact length_extension_abort_above d _ _

private lemma length_extension_payoff
    (P : FighterParams) (d l : ℕ) (q : Coordinate) (s : FighterState) :
    allocationLengthExtension s (fighterPayoff P d l q s) := by
  unfold fighterPayoff
  split
  · exact length_extension_refl s
  · split
    · have h := length_extension_allocate d l .payoff q.2 q.1 s
      cases he : fighterAllocate d l .payoff q.2 q.1 s with
      | mk next success =>
        rw [he] at h
        cases success
        · exact h
        · exact length_extension_trans h (length_extension_of_allocated_eq _ _ rfl)
    · exact length_extension_refl s

private lemma length_extension_fulfill_ready
    (P : FighterParams) (d l : ℕ) (s : FighterState) :
    allocationLengthExtension s (fighterFulfillReady P d l s) := by
  unfold fighterFulfillReady
  split
  · exact length_extension_refl s
  · exact length_extension_foldl (fun q s ↦ fighterPayoff P d l q s)
      (length_extension_payoff P d l) _ _

private lemma length_extension_fuel_unit
    (P : FighterParams) (d l : ℕ) (q : Coordinate) (s : FighterState) :
    allocationLengthExtension s (fighterFuelUnit P d l q s) := by
  unfold fighterFuelUnit
  split
  · exact length_extension_refl s
  · rename_i phase hs
    split
    · have h := length_extension_trans (length_extension_put_phase d s { phase with
          controlledRemaining := phase.controlledRemaining - 1 })
        (length_extension_allocate d l .fuel (levelUpper l + d)
          (pairCode (triple q.1 (q.2 - d) phase.candidate.1)
            (fighterFreshString d
              (phase.indices[(phase.game d).coordinates.idxOf q]?.getD []))) _)
      dsimp only
      split
      · exact length_extension_trans h
          (length_extension_trans (length_extension_put_phase d _ _)
            (length_extension_fulfill_ready P d _ _))
      · exact h
    · exact length_extension_refl s

private lemma length_extension_fuel_units
    (P : FighterParams) (d l : ℕ) (q : Coordinate) (count : ℕ) (s : FighterState) :
    allocationLengthExtension s (fighterFuelUnits P d l q count s) := by
  induction count generalizing s with
  | zero => exact length_extension_refl s
  | succ count ih => exact length_extension_trans (length_extension_fuel_unit P d l q s) (ih _)

private lemma length_extension_dummy
    (d l : ℕ) (s : FighterState) : allocationLengthExtension s (fighterDummy d l s) := by
  unfold fighterDummy
  split
  · exact length_extension_refl s
  · split
    · exact length_extension_refl s
    · rename_i output hout
      split
      · exact length_extension_refl s
      · have h := length_extension_allocate d l .dummy (levelInput d l) output s
        dsimp only
        split
        · exact length_extension_trans h (length_extension_put_phase d _ _)
        · exact h

private lemma length_extension_flush_buffer (d l : ℕ) (s : FighterState) :
    allocationLengthExtension s ((fighterFlushBuffer d l s).getD s) := by
  cases hs : s.activeAt d l with
  | none => simpa [fighterFlushBuffer, hs] using length_extension_refl s
  | some phase =>
    simp only [fighterFlushBuffer, hs, bind, Option.bind_some]
    split
    · exact length_extension_put_phase d _ _
    · exact length_extension_refl s

private lemma length_extension_strategy_move (P : FighterParams) (d l : ℕ) (s : FighterState) :
    allocationLengthExtension s ((fighterStrategyMove P d l s).getD s) := by
  cases hs : s.activeAt d l with
  | none => simpa [fighterStrategyMove, hs] using length_extension_refl s
  | some phase =>
    simp only [fighterStrategyMove, hs, bind, Option.bind_some]
    split
    · cases hm : (phase.game d).strategy (phase.official d) with
      | none => exact length_extension_refl s
      | some move =>
        simp only [Option.bind_some]
        split
        · let next := ((phase.game d).coordinates.zipIdx).foldl (fun s (q, i) ↦
            fighterFuelUnits P d l q (move[i]?.getD 0) s) s
          have hn : allocationLengthExtension s next :=
            length_extension_foldl _
              (fun (qi : Coordinate × ℕ) t ↦ length_extension_fuel_units P d l qi.1 _ t) _ _
          change allocationLengthExtension s ((match next.activeAt d l with
            | none => some next
            | some live => some (next.putPhase d
                { live with officialCode :=
                  ((phase.game d).afterMove (phase.official d) move).encode })).getD s)
          cases hlive : next.activeAt d l with
          | none => exact hn
          | some live => exact length_extension_trans hn (length_extension_put_phase d _ _)
        · exact length_extension_refl s
    · exact length_extension_refl s

private lemma length_extension_level_action (P : FighterParams) (d l : ℕ) (s : FighterState) :
    allocationLengthExtension s ((fighterLevelAction P d l s).getD s) := by
  cases hs : s.activeAt d l with
  | none => simpa [fighterLevelAction, hs] using length_extension_refl s
  | some phase =>
    simp only [fighterLevelAction, hs, bind, Option.bind_some]
    split
    · exact length_extension_dummy d l s
    · split
      · exact length_extension_payoff P d l _ s
      · cases hf : fighterFlushBuffer d l s with
        | none => exact length_extension_strategy_move P d l s
        | some next => simpa only [hf] using length_extension_flush_buffer d l s

private lemma length_extension_closure (P : FighterParams) (d : ℕ) (l fuel : ℕ) (s : FighterState) :
    allocationLengthExtension s (fighterClosure P d l fuel s) := by
  induction fuel generalizing s with
  | zero => exact length_extension_refl s
  | succ fuel ih =>
    simp only [fighterClosure]
    cases ha : fighterLevelAction P d l s with
    | none => exact length_extension_refl s
    | some next =>
      have h := length_extension_level_action P d l s
      simp only [ha, Option.getD_some] at h
      exact length_extension_trans h (ih next)

private lemma length_extension_start_phase
    (P : FighterParams) (d l : ℕ) (candidate : Candidate) (s : FighterState) :
    allocationLengthExtension s (fighterStartPhase P d l candidate s) := by
  exact length_extension_trans (length_extension_cancel d _ _ _ s)
    (length_extension_trans (length_extension_abort_above d _ _)
      (length_extension_of_allocated_eq _ _ rfl))

private lemma length_extension_opponent
    (P : FighterParams) (d l : ℕ) (event : ProgramEvent) (s : FighterState) :
    allocationLengthExtension s (fighterOpponent P d l event s) := by
  unfold fighterOpponent
  split
  · exact length_extension_refl s
  · split
    · exact length_extension_refl s
    · split
      · exact length_extension_refl s
      · split
        · exact length_extension_cancel d _ _ _ s
        · exact length_extension_trans (length_extension_put_phase d _ _)
            (length_extension_fulfill_ready P d _ _)

private lemma length_extension_process_level
    (P : FighterParams) (d l : ℕ) (event : Option TimedEvent) (s : FighterState) :
    allocationLengthExtension s (fighterProcessLevel P d l event s) := by
  unfold fighterProcessLevel fighterCloseLevel
  apply length_extension_trans (length_extension_fulfill_ready P d l s)
  cases event with
  | none => exact length_extension_closure P d _ _ _
  | some e =>
    dsimp only
    split
    · exact length_extension_trans (length_extension_start_phase P d _ _ _)
        (length_extension_closure P d _ _ _)
    · exact length_extension_trans (length_extension_opponent P d _ _ _)
        (length_extension_closure P d _ _ _)

/-- A positive-padding tick retains every allocation and adds only directives whose inputs
are exactly one bit shorter than their targets. This holds even when an allocation fails. -/
theorem fighter_actions_allocation_lengths
    (P : FighterParams) (d tick : ℕ) (state : FighterState) (hd : 1 ≤ d) :
    state.allocated ⊆ (fighter_actions P d tick state).allocated ∧
      ∀ a ∈ (fighter_actions P d tick state).allocated,
        a ∈ state.allocated ∨ a.input.length + 1 = a.target := by
  change allocationLengthExtension state (fighter_actions P d tick state)
  unfold fighter_actions
  rw [ite_eq_right (by omega : d ≠ 0)]
  exact length_extension_trans
    (t := { state with tick := tick, schedule := masterState P.B tick })
    (length_extension_of_allocated_eq _ _ rfl)
    (length_extension_foldl _
      (fun l s ↦ length_extension_process_level P d l (eventAt P.B tick) s) _ _)

end Kolmogorov.Milovanov
