/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.StrategyClosure

/-!
# Higher-level services do not disturb a lower phase

At one tick the fighter state machine serves the active levels in increasing order.  This module
shows that the service of a level `j` strictly above `l` (a payoff, a dummy allocation, a strategy
move, an opponent move, a closure, or the start of a new phase) never changes the level and the
candidate of the phase found at level `l`: the only effects on lower levels are cancellations and
aborts of strictly higher ones.

The main results are `phaseKeyAt_fighterProcessLevel`, the statement for one service, and
`exists_activeAt_foldl_fighterProcessLevel`, the statement for any list of higher-level services.
They are used in `CommonGameInitial.lean` to show that the true marker phase survives the services
following the closure of its own level at the marker tick.
-/

namespace Kolmogorov.Milovanov

/-- The level and the candidate of the phase found at level `l`, if there is one. -/
def phaseKeyAt (d l : ℕ) (s : FighterState) : Option (ℕ × Candidate) :=
  (s.activeAt d l).map fun p ↦ (p.level, p.candidate)

/-- Folding a list of state transformations which each preserve `phaseKeyAt` preserves it. -/
private lemma phaseKeyAt_foldl {α : Type} (d l : ℕ) (f : α → FighterState → FighterState)
    (hf : ∀ a s, phaseKeyAt d l (f a s) = phaseKeyAt d l s) (xs : List α) (s : FighterState) :
    phaseKeyAt d l (xs.foldl (fun s a ↦ f a s) s) = phaseKeyAt d l s := by
  induction xs generalizing s with
  | nil => rfl
  | cons a xs ih => exact (ih _).trans (hf a s)

/-- Installing a phase of a level above `l` does not change the phase of level `l`. -/
private lemma phaseKeyAt_putPhase (d l : ℕ) (s : FighterState) (p : FighterPhase)
    (hp : l < p.level) : phaseKeyAt d l (s.putPhase d p) = phaseKeyAt d l s := by
  have heq : (s.putPhase d p).activeAt d l = s.activeAt d l := by
    simp only [FighterState.putPhase, FighterState.activeAt, List.find?_cons,
      beq_eq_false_iff_ne.mpr (by omega : p.level ≠ l)]
    exact FighterState.find?_level_filter_ne s.active l p.level (by omega)
  unfold phaseKeyAt
  rw [heq]

/-- Cancelling the phase of a level above `l` does not change the phase of level `l`. -/
private lemma phaseKeyAt_fighterCancel (d l k : ℕ) (reason : PhaseEnd) (cause : ℕ)
    (s : FighterState) (hk : l < k) :
    phaseKeyAt d l (fighterCancel d k reason cause s) = phaseKeyAt d l s := by
  unfold phaseKeyAt
  rw [activeAt_fighterCancel_eq_of_ne d k l reason cause s hk.ne']

/-- Aborting the phases above level `k` does not change the phase of a level `l < k`. -/
private lemma phaseKeyAt_fighterAbortAbove (d l k : ℕ) (s : FighterState) (hk : l < k) :
    phaseKeyAt d l (fighterAbortAbove d k s) = phaseKeyAt d l s := by
  unfold fighterAbortAbove
  apply phaseKeyAt_foldl
  intro p t
  split
  · exact phaseKeyAt_fighterCancel d l p.level .aborted k t (by omega)
  · rfl

/-- An allocation at a level `k > l` does not change the phase of level `l`. -/
private lemma phaseKeyAt_fighterAllocate (d l k : ℕ) (kind : DirectiveKind) (target : ℕ)
    (output : BitString) (s : FighterState) (hk : l < k) :
    phaseKeyAt d l (fighterAllocate d k kind target output s).1 = phaseKeyAt d l s := by
  unfold fighterAllocate
  split
  · rfl
  · cases hf : (if target = 0 then (none : Option BitString) else
        (fighterInputs d (target - 1)).find? (fun p ↦ !s.allocated.any (fun a ↦ a.input == p)))
        with
    | none => exact phaseKeyAt_fighterCancel d l k .saturated k { s with failed := true } hk
    | some p => exact phaseKeyAt_fighterAbortAbove d l k _ hk

/-- A payoff at a level `k > l` does not change the level and the candidate of the phase of
level `l`. -/
private lemma phaseKeyAt_fighterPayoff (P : FighterParams) (d l k : ℕ) (q : Coordinate)
    (s : FighterState) (hk : l < k) :
    phaseKeyAt d l (fighterPayoff P d k q s) = phaseKeyAt d l s := by
  unfold fighterPayoff
  split
  · rfl
  · split
    · have ha := phaseKeyAt_fighterAllocate d l k .payoff q.2 q.1 s hk
      cases he : fighterAllocate d k .payoff q.2 q.1 s with
      | mk next success =>
        simp only [he] at ha ⊢
        cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
        · exact ha
        · simpa only [phaseKeyAt, FighterState.activeAt, List.find?_map, Option.map_map,
            Function.comp_def] using ha
    · rfl

/-- Fulfilling the ready requests at a level `k > l` does not change the level and the candidate of
the phase of level `l`. -/
private lemma phaseKeyAt_fighterFulfillReady (P : FighterParams) (d l k : ℕ) (s : FighterState)
    (hk : l < k) : phaseKeyAt d l (fighterFulfillReady P d k s) = phaseKeyAt d l s := by
  unfold fighterFulfillReady
  split
  · rfl
  · exact phaseKeyAt_foldl d l (fun q t ↦ fighterPayoff P d k q t)
      (fun q t ↦ phaseKeyAt_fighterPayoff P d l k q t hk) _ s

/-- A unit of fuel at a level `k > l` does not change the level and the candidate of the phase of
level `l`. -/
private lemma phaseKeyAt_fighterFuelUnit (P : FighterParams) (d l k : ℕ) (q : Coordinate)
    (s : FighterState) (hk : l < k) :
    phaseKeyAt d l (fighterFuelUnit P d k q s) = phaseKeyAt d l s := by
  unfold fighterFuelUnit
  split
  · rfl
  · rename_i phase hphase
    have hp : l < phase.level := hk.trans_eq (FighterState.level_eq_of_activeAt_eq_some hphase).symm
    split
    · let charged := { phase with controlledRemaining := phase.controlledRemaining - 1 }
      let index := fighterFreshString d (phase.indices[(phase.game d).coordinates.idxOf q]?.getD [])
      let output := pairCode (triple q.1 (q.2 - d) phase.candidate.1) index
      have hc := phaseKeyAt_putPhase d l s charged hp
      have ha := phaseKeyAt_fighterAllocate d l k .fuel (levelUpper k + d) output
        (s.putPhase d charged) hk
      change phaseKeyAt d l (match fighterAllocate d k .fuel (levelUpper k + d) output
        (s.putPhase d charged) with
        | (next, success) => if success then fighterFulfillReady P d k
            (next.putPhase d ((charged.insertIndex d q index).fundRequests d next.fulfilled))
          else next) = _
      cases he : fighterAllocate d k .fuel (levelUpper k + d) output (s.putPhase d charged) with
      | mk next success =>
        rw [he] at ha
        cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
        · exact ha.trans hc
        · refine ((phaseKeyAt_fighterFulfillReady P d l k _ hk).trans
            (phaseKeyAt_putPhase d l next _ ?_)).trans (ha.trans hc)
          exact hp
    · rfl

/-- Repeated units of fuel at a level `k > l` do not change the level and the candidate of the
phase of level `l`. -/
private lemma phaseKeyAt_fighterFuelUnits (P : FighterParams) (d l k : ℕ) (q : Coordinate)
    (count : ℕ) (s : FighterState) (hk : l < k) :
    phaseKeyAt d l (fighterFuelUnits P d k q count s) = phaseKeyAt d l s := by
  induction count generalizing s with
  | zero => rfl
  | succ count ih => exact (ih _).trans (phaseKeyAt_fighterFuelUnit P d l k q s hk)

/-- An opponent move at a level `k > l` does not change the level and the candidate of the phase
of level `l`. -/
private lemma phaseKeyAt_fighterOpponent (P : FighterParams) (d l k : ℕ) (e : ProgramEvent)
    (s : FighterState) (hk : l < k) :
    phaseKeyAt d l (fighterOpponent P d k e s) = phaseKeyAt d l s := by
  unfold fighterOpponent
  split
  · rfl
  · rename_i phase hphase
    have hp : l < phase.level := hk.trans_eq (FighterState.level_eq_of_activeAt_eq_some hphase).symm
    split
    · rfl
    · split
      · rfl
      · split
        · exact phaseKeyAt_fighterCancel d l k .opponentExhausted k s hk
        · exact (phaseKeyAt_fighterFulfillReady P d l k _ hk).trans (phaseKeyAt_putPhase d l s _ hp)

/-- A dummy allocation at a level `k > l` does not change the level and the candidate of the phase
of level `l`. -/
private lemma phaseKeyAt_fighterDummy (d l k : ℕ) (s : FighterState) (hk : l < k) :
    phaseKeyAt d l (fighterDummy d k s) = phaseKeyAt d l s := by
  unfold fighterDummy
  split
  · rfl
  · rename_i phase hphase
    have hp : l < phase.level := hk.trans_eq (FighterState.level_eq_of_activeAt_eq_some hphase).symm
    split
    · rfl
    · rename_i output hout
      split
      · rfl
      · have ha := phaseKeyAt_fighterAllocate d l k .dummy (levelInput d k) output s hk
        cases he : fighterAllocate d k .dummy (levelInput d k) output s with
        | mk next success =>
          simp only [he] at ha ⊢
          cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
          · exact ha
          · refine (phaseKeyAt_putPhase d l next _ ?_).trans ha
            exact hp

/-- Flushing the buffer at a level `k > l` does not change the level and the candidate of the phase
of level `l`. -/
private lemma phaseKeyAt_fighterFlushBuffer (d l k : ℕ) (s : FighterState) (hk : l < k) :
    phaseKeyAt d l ((fighterFlushBuffer d k s).getD s) = phaseKeyAt d l s := by
  cases hphase : s.activeAt d k with
  | none => simp [fighterFlushBuffer, hphase]
  | some phase =>
    have hp : l < phase.level := hk.trans_eq (FighterState.level_eq_of_activeAt_eq_some hphase).symm
    simp only [fighterFlushBuffer, hphase, bind, Option.bind_some]
    split
    · exact phaseKeyAt_putPhase d l s _ hp
    · rfl

/-- A strategy move at a level `k > l` does not change the level and the candidate of the phase of
level `l`. -/
private lemma phaseKeyAt_fighterStrategyMove (P : FighterParams) (d l k : ℕ) (s : FighterState)
    (hk : l < k) : phaseKeyAt d l ((fighterStrategyMove P d k s).getD s) = phaseKeyAt d l s := by
  cases hphase : s.activeAt d k with
  | none => simp [fighterStrategyMove, hphase]
  | some phase =>
    simp only [fighterStrategyMove, hphase, bind, Option.bind_some]
    split
    · cases hm : (phase.game d).strategy (phase.official d) with
      | none => rfl
      | some move =>
        simp only [Option.bind_some]
        split
        · let next := (phase.game d).coordinates.zipIdx.foldl (fun s qi ↦
            fighterFuelUnits P d k qi.1 (move[qi.2]?.getD 0) s) s
          have hn : phaseKeyAt d l next = phaseKeyAt d l s :=
            phaseKeyAt_foldl d l (fun (qi : Coordinate × ℕ) t ↦
              fighterFuelUnits P d k qi.1 (move[qi.2]?.getD 0) t)
              (fun qi t ↦ phaseKeyAt_fighterFuelUnits P d l k qi.1 _ t hk) _ s
          change phaseKeyAt d l ((match next.activeAt d k with
            | none => some next
            | some live => some (next.putPhase d { live with
                officialCode := ((phase.game d).afterMove (phase.official d) move).encode })).getD
              s) = _
          cases hlive : next.activeAt d k with
          | none => exact hn
          | some live =>
            refine (phaseKeyAt_putPhase d l next _ ?_).trans hn
            exact hk.trans_eq (FighterState.level_eq_of_activeAt_eq_some hlive).symm
        · rfl
    · rfl

/-- One action of the closure of a level `k > l` does not change the level and the candidate of the
phase of level `l`. -/
private lemma phaseKeyAt_fighterLevelAction (P : FighterParams) (d l k : ℕ) (s : FighterState)
    (hk : l < k) : phaseKeyAt d l ((fighterLevelAction P d k s).getD s) = phaseKeyAt d l s := by
  cases hphase : s.activeAt d k with
  | none => simp [fighterLevelAction, hphase]
  | some phase =>
    simp only [fighterLevelAction, hphase, bind, Option.bind_some]
    split
    · exact phaseKeyAt_fighterDummy d l k s hk
    · split
      · exact phaseKeyAt_fighterPayoff P d l k _ s hk
      · cases hf : fighterFlushBuffer d k s with
        | none => exact phaseKeyAt_fighterStrategyMove P d l k s hk
        | some next =>
          simpa only [hf, Option.getD_some] using phaseKeyAt_fighterFlushBuffer d l k s hk

/-- The closure of a level `k > l` does not change the level and the candidate of the phase of
level `l`. -/
private lemma phaseKeyAt_fighterClosure (P : FighterParams) (d l k : ℕ) (fuel : ℕ)
    (s : FighterState) (hk : l < k) :
    phaseKeyAt d l (fighterClosure P d k fuel s) = phaseKeyAt d l s := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
    simp only [fighterClosure]
    cases ha : fighterLevelAction P d k s with
    | none => rfl
    | some next =>
      have hn := phaseKeyAt_fighterLevelAction P d l k s hk
      simp only [ha, Option.getD_some] at hn
      exact (ih next).trans hn

/-- Starting a phase at a level `k > l` does not change the level and the candidate of the phase of
level `l`. -/
private lemma phaseKeyAt_fighterStartPhase (P : FighterParams) (d l k : ℕ) (candidate : Candidate)
    (s : FighterState) (hk : l < k) :
    phaseKeyAt d l (fighterStartPhase P d k candidate s) = phaseKeyAt d l s :=
  (phaseKeyAt_putPhase d l _ (fighter_construction P d k candidate _) hk).trans
    ((phaseKeyAt_fighterAbortAbove d l k _ hk).trans
      (phaseKeyAt_fighterCancel d l k .replaced k s hk))

/-- The service of a level `j > l` at a tick does not change the level and the candidate of the
phase of level `l`. -/
lemma phaseKeyAt_fighterProcessLevel (P : FighterParams) (d l j : ℕ)
    (event : Option TimedEvent) (state : FighterState) (hjl : l < j) :
    phaseKeyAt d l (fighterProcessLevel P d j event state) = phaseKeyAt d l state := by
  unfold fighterProcessLevel fighterCloseLevel
  have hc := phaseKeyAt_fighterFulfillReady P d l j state hjl
  cases event with
  | none => exact (phaseKeyAt_fighterClosure P d l j _ _ hjl).trans hc
  | some e =>
    dsimp only
    split
    · exact (phaseKeyAt_fighterClosure P d l j _ _ hjl).trans
        ((phaseKeyAt_fighterStartPhase P d l j (e.2.2.1, e.1) _ hjl).trans hc)
    · exact (phaseKeyAt_fighterClosure P d l j _ _ hjl).trans
        ((phaseKeyAt_fighterOpponent P d l j e.2.2 _ hjl).trans hc)

/-- The services of strictly higher levels, run in any order at one tick, preserve the level and
the candidate of an existing phase of level `l`. -/
lemma exists_activeAt_foldl_fighterProcessLevel (P : FighterParams) (d l : ℕ)
    (event : Option TimedEvent) (state : FighterState) (levels : List ℕ)
    (hlevels : ∀ j ∈ levels, l < j) :
    ∀ old, state.activeAt d l = some old →
      ∃ next,
        (levels.foldl (fun s j ↦ fighterProcessLevel P d j event s) state).activeAt d l =
          some next ∧
        next.level = old.level ∧ next.candidate = old.candidate := by
  have hfold : phaseKeyAt d l (levels.foldl (fun s j ↦ fighterProcessLevel P d j event s) state) =
      phaseKeyAt d l state := by
    induction levels generalizing state with
    | nil => rfl
    | cons j levels ih =>
      exact (ih (fighterProcessLevel P d j event state)
        fun k hk ↦ hlevels k (List.mem_cons_of_mem j hk)).trans
        (phaseKeyAt_fighterProcessLevel P d l j event state (hlevels j (by simp)))
  intro old hold
  simp only [phaseKeyAt, hold, Option.map_some] at hfold
  obtain ⟨next, hnext, hmeta⟩ := Option.map_eq_some_iff.mp hfold
  exact ⟨next, hnext, congrArg Prod.fst hmeta, congrArg Prod.snd hmeta⟩

end Kolmogorov.Milovanov

