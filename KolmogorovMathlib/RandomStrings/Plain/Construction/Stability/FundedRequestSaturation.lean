/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.Padding

/-!
# Saturation records and the failure flag

The fighter construction archives a phase with the reason `PhaseEnd.saturated` only when an
allocation runs out of fresh inputs, and at that moment it also raises the persistent flag
`FighterState.failed`.  This module proves the resulting invariant of the fighter run
`fighterState`: as long as no allocation has failed, no archived phase ended by saturation
(`fighterState_ended_reason_ne_saturated`).

The proof follows the control flow of `fighter_actions`: every atomic action
(`fighterCancel`, `fighterAllocate`, `fighterPayoff`, `fighterFuelUnit`, `fighterOpponent`, ...)
preserves the invariant `SaturationFlagged`, and so do their compositions up to
`fighterProcessLevel`.  The compositions use the generic fold principle
`foldl_preserves_invariant` of `ListLemmas`.  The result is used by the funded
request argument for the true marker (`FundedRequest`) and by the common-game invariant.
-/

namespace Kolmogorov.Milovanov

/-- Every saturation end record of a fighter state is justified by the raised failure flag. -/
private def SaturationFlagged (s : FighterState) : Prop :=
  ∀ e ∈ s.ended, e.2.2.1 = .saturated → s.failed = true

namespace SaturationFlagged

/-- Cancelling a phase preserves the invariant, provided that a saturated cancellation happens
only with the failure flag raised. -/
private theorem cancel (d j cause : ℕ) (reason : PhaseEnd) {s : FighterState}
    (hs : SaturationFlagged s) (hsat : reason = .saturated → s.failed = true) :
    SaturationFlagged (fighterCancel d j reason cause s) := by
  unfold fighterCancel
  split
  · exact hs
  · intro e he hr
    rcases List.mem_append.mp he with hold | hnew
    · exact hs e hold hr
    · have heq := List.mem_singleton.mp hnew
      subst e
      exact hsat hr

/-- Aborting the larger levels preserves the invariant. -/
private theorem abortAbove (d l : ℕ) {s : FighterState} (hs : SaturationFlagged s) :
    SaturationFlagged (fighterAbortAbove d l s) := by
  unfold fighterAbortAbove
  refine foldl_preserves_invariant SaturationFlagged _ _ (fun t p ht ↦ ?_) hs
  split
  · exact cancel d _ _ _ ht (by intro h; cases h)
  · exact ht

/-- A guarded allocation preserves the invariant; on failure it raises the flag together with
the saturation record. -/
private theorem allocate (d l : ℕ) (kind : DirectiveKind) (target : ℕ) (out : BitString)
    {s : FighterState} (hs : SaturationFlagged s) :
    SaturationFlagged (fighterAllocate d l kind target out s).1 := by
  unfold fighterAllocate
  split
  · exact hs
  · cases hf : (if target = 0 then (none : Option BitString) else
        (fighterInputs d (target - 1)).find? (fun p =>
          !s.allocated.any (fun a => a.input == p))) with
    | none =>
      exact cancel d l l .saturated (s := { s with failed := true })
        (fun _ _ _ ↦ rfl) (fun _ ↦ rfl)
    | some input => exact abortAbove d l hs

/-- Paying a coordinate off preserves the invariant. -/
private theorem payoff (P : FighterParams) (d l : ℕ) (q : Coordinate) {s : FighterState}
    (hs : SaturationFlagged s) : SaturationFlagged (fighterPayoff P d l q s) := by
  unfold fighterPayoff
  split
  · exact hs
  · split
    · have ha := allocate d l .payoff q.2 q.1 hs
      cases he : fighterAllocate d l .payoff q.2 q.1 s with
      | mk next success =>
        simp only [he] at ha ⊢
        cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> exact ha
    · exact hs

/-- Fulfilling all ready requests of a level preserves the invariant. -/
private theorem fulfillReady (P : FighterParams) (d l : ℕ) {s : FighterState}
    (hs : SaturationFlagged s) : SaturationFlagged (fighterFulfillReady P d l s) := by
  unfold fighterFulfillReady
  split
  · exact hs
  · exact foldl_preserves_invariant SaturationFlagged _ _ (fun t q ht ↦ payoff P d l q ht) hs

/-- Spending one unit of the fuel budget on a coordinate preserves the invariant. -/
private theorem fuelUnit (P : FighterParams) (d l : ℕ) (q : Coordinate) {s : FighterState}
    (hs : SaturationFlagged s) : SaturationFlagged (fighterFuelUnit P d l q s) := by
  unfold fighterFuelUnit
  split
  · exact hs
  · rename_i phase hp
    split
    · let charged := { phase with controlledRemaining := phase.controlledRemaining - 1 }
      let index := fighterFreshString d
        (phase.indices[(phase.game d).coordinates.idxOf q]?.getD [])
      let out := pairCode (triple q.1 (q.2 - d) phase.candidate.1) index
      have ha := allocate d l .fuel (levelUpper l + d) out (s := s.putPhase d charged) hs
      change SaturationFlagged
        (match fighterAllocate d l .fuel (levelUpper l + d) out (s.putPhase d charged) with
          | (next, success) => if success then
            fighterFulfillReady P d l
              (next.putPhase d ((charged.insertIndex d q index).fundRequests d next.fulfilled))
            else next)
      cases he : fighterAllocate d l .fuel (levelUpper l + d) out (s.putPhase d charged) with
      | mk next success =>
        rw [he] at ha
        cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
        · exact ha
        · exact fulfillReady P d l ha
    · exact hs

/-- Spending several units of the fuel budget on a coordinate preserves the invariant. -/
private theorem fuelUnits (P : FighterParams) (d l : ℕ) (q : Coordinate) (count : ℕ)
    {s : FighterState} (hs : SaturationFlagged s) :
    SaturationFlagged (fighterFuelUnits P d l q count s) := by
  induction count generalizing s with
  | zero => exact hs
  | succ count ih => exact ih (fuelUnit P d l q hs)

/-- The dummy allocation of a level preserves the invariant. -/
private theorem dummy (d l : ℕ) {s : FighterState} (hs : SaturationFlagged s) :
    SaturationFlagged (fighterDummy d l s) := by
  unfold fighterDummy
  split
  · exact hs
  · split
    · exact hs
    · rename_i output _
      split
      · exact hs
      · have ha := allocate d l .dummy (levelInput d l) output hs
        cases he : fighterAllocate d l .dummy (levelInput d l) output s with
        | mk next success =>
          simp only [he] at ha ⊢
          cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> exact ha

/-- Processing an opponent program event at a level preserves the invariant. -/
private theorem opponent (P : FighterParams) (d l : ℕ) (e : ProgramEvent) {s : FighterState}
    (hs : SaturationFlagged s) : SaturationFlagged (fighterOpponent P d l e s) := by
  unfold fighterOpponent
  split
  · exact hs
  · split
    · exact hs
    · split
      · exact hs
      · split
        · exact cancel d _ _ _ hs (by intro h; cases h)
        · exact fulfillReady P d l hs

/-- Starting a phase for a candidate at a level preserves the invariant. -/
private theorem startPhase (P : FighterParams) (d l : ℕ) (c : Candidate) {s : FighterState}
    (hs : SaturationFlagged s) : SaturationFlagged (fighterStartPhase P d l c s) := by
  unfold fighterStartPhase
  exact abortAbove d l (cancel d l l .replaced hs (by intro h; cases h))

/-- Flushing the buffer of a level preserves the invariant. -/
private theorem flushBuffer (d l : ℕ) {s : FighterState} (hs : SaturationFlagged s) :
    SaturationFlagged ((fighterFlushBuffer d l s).getD s) := by
  unfold fighterFlushBuffer
  cases hp : s.activeAt d l with
  | none => exact hs
  | some phase =>
    simp only [bind, Option.bind_some]
    split <;> exact hs

/-- A strategy move at a level preserves the invariant. -/
private theorem strategyMove (P : FighterParams) (d l : ℕ) {s : FighterState}
    (hs : SaturationFlagged s) : SaturationFlagged ((fighterStrategyMove P d l s).getD s) := by
  unfold fighterStrategyMove
  cases hp : s.activeAt d l with
  | none => exact hs
  | some phase =>
    simp only [bind, Option.bind_some]
    split
    · cases hm : (phase.game d).strategy (phase.official d) with
      | none => exact hs
      | some move =>
        simp only [Option.bind_some]
        split
        · let next := (phase.game d).coordinates.zipIdx.foldl (fun s (q, i) =>
            fighterFuelUnits P d l q (move[i]?.getD 0) s) s
          have hn : SaturationFlagged next :=
            foldl_preserves_invariant SaturationFlagged _ _
              (fun t qi ht ↦ fuelUnits P d l qi.1 (move[qi.2]?.getD 0) ht) hs
          change SaturationFlagged ((match next.activeAt d l with
            | none => some next
            | some live => some (next.putPhase d
              { live with officialCode :=
                  ((phase.game d).afterMove (phase.official d) move).encode })).getD s)
          split <;> exact hn
        · exact hs
    · exact hs

/-- The single action of a level preserves the invariant. -/
private theorem levelAction (P : FighterParams) (d l : ℕ) {s : FighterState}
    (hs : SaturationFlagged s) : SaturationFlagged ((fighterLevelAction P d l s).getD s) := by
  unfold fighterLevelAction
  cases hp : s.activeAt d l with
  | none => exact hs
  | some phase =>
    simp only [bind, Option.bind_some]
    split
    · exact dummy d l hs
    · split
      · exact payoff P d l _ hs
      · cases hf : fighterFlushBuffer d l s with
        | none => exact strategyMove P d l hs
        | some next =>
          have h := flushBuffer d l hs
          simpa only [hf, Option.getD_some] using h

/-- Closing a level, i.e. iterating its action with bounded fuel, preserves the invariant. -/
private theorem closure (P : FighterParams) (d l fuel : ℕ) {s : FighterState}
    (hs : SaturationFlagged s) : SaturationFlagged (fighterClosure P d l fuel s) := by
  induction fuel generalizing s with
  | zero => exact hs
  | succ fuel ih =>
    simp only [fighterClosure]
    cases ha : fighterLevelAction P d l s with
    | none => exact hs
    | some next =>
      have hn := levelAction P d l hs
      simp only [ha, Option.getD_some] at hn
      exact ih hn

/-- Processing one level for one (optional) event preserves the invariant. -/
private theorem processLevel (P : FighterParams) (d l : ℕ) (e : Option TimedEvent)
    {s : FighterState} (hs : SaturationFlagged s) :
    SaturationFlagged (fighterProcessLevel P d l e s) := by
  unfold fighterProcessLevel fighterCloseLevel
  apply closure
  cases e with
  | none => exact fulfillReady P d l hs
  | some e =>
    dsimp only
    split
    · exact startPhase P d l _ (fulfillReady P d l hs)
    · exact opponent P d l _ (fulfillReady P d l hs)

/-- Every reachable fighter state satisfies the invariant. -/
private theorem reachable (P : FighterParams) (d t : ℕ) :
    SaturationFlagged (fighterState P d t) := by
  induction t with
  | zero => simp [SaturationFlagged, fighterState, initialFighterState]
  | succ t ih =>
    change SaturationFlagged (fighter_actions P d (t + 1) (fighterState P d t))
    unfold fighter_actions
    split
    · simp [SaturationFlagged, initialFighterState]
    · exact foldl_preserves_invariant SaturationFlagged _ _
        (fun s l hs ↦ processLevel P d l (eventAt P.B (t + 1)) hs)
        (s := { fighterState P d t with
          tick := t + 1
          schedule := masterState P.B (t + 1) }) ih

end SaturationFlagged

/-- Every archived saturation sets the persistent failure flag.  Hence a completed state with
no allocation failure contains no saturation end record.  Blueprint node
`true_marker_funded_request_realized`. -/
theorem fighterState_ended_reason_ne_saturated (P : FighterParams) (d tick : ℕ)
    (hfailed : (fighterState P d tick).failed = false) :
    ∀ e ∈ (fighterState P d tick).ended, e.2.2.1 ≠ .saturated := by
  intro e he hr
  have hf := SaturationFlagged.reachable P d tick e he hr
  rw [hfailed] at hf
  cases hf

end Kolmogorov.Milovanov
