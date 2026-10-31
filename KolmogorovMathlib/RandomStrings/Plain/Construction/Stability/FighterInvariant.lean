/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.Padding

/-!
# Invariants of the fighter scheduler

A `FighterInvariant` bundles a property of active phases and a property of archived phases
which are stable under every elementary operation of the fighter construction except the
opponent insertion: cancelling, aborting, allocating, paying off, spending fuel, issuing the
dummy, flushing the buffer, making a strategy move and starting a phase.
`FighterInvariant.holds_fighterState` shows that such an invariant holds at every tick of the
construction as soon as it is preserved by the opponent insertion.

The ledger of the opponent budget in `FundedRequestOpponent` is one instance; it is used there to
show that a true-marker phase is never cancelled for exhausting its opponent budget.
-/

namespace Kolmogorov.Milovanov

/-- A property of the active phases and of the archived phases of the fighter scheduler.
The active property depends only on the frozen fields of a phase (level, candidate, initial
allocations, game code, indices, remaining opponent budget) and is preserved by controlled
insertions and by phase construction at valid candidates; archiving keeps it. -/
structure FighterInvariant (P : FighterParams) (d : ℕ) where
  /-- The property of an active phase. -/
  Active : FighterPhase → Prop
  /-- The property of an archived phase together with its end tick, reason and cause. -/
  Archived : EndedPhase → Prop
  /-- `Active` depends only on the level, candidate, initial allocations, game code, indices
  and remaining opponent budget. -/
  active_congr : ∀ p p' : FighterPhase,
    (p.level, p.candidate, p.initialAllocations, p.gameCode, p.indices, p.opponentRemaining) =
      (p'.level, p'.candidate, p'.initialAllocations, p'.gameCode, p'.indices,
        p'.opponentRemaining) → Active p → Active p'
  /-- A phase constructed at a valid candidate is active. -/
  active_construction : ∀ l c s, validCandidate P.B (levelScale l) c = true →
    Active (fighter_construction P d l c s)
  /-- A controlled insertion keeps a phase active. -/
  active_insertIndex : ∀ p q index, Active p → Active (p.insertIndex d q index)
  /-- Cancelling an active phase for any reason other than opponent exhaustion archives it. -/
  archived_cancel : ∀ p tick reason cause, reason ≠ .opponentExhausted → Active p →
    Archived ({ p with pending := [] }, tick, reason, cause)

namespace FighterInvariant

variable {P : FighterParams} {d : ℕ} (I : FighterInvariant P d)

/-- A fighter state satisfies the invariant when all its active phases and all its archived
phases satisfy the respective properties. -/
abbrev Holds (s : FighterState) : Prop :=
  (∀ p ∈ s.active, I.Active p) ∧ ∀ e ∈ s.ended, I.Archived e

variable {I}

/-- The active phase of a level in a state satisfying the invariant satisfies the active
property. -/
theorem Holds.active_of_activeAt {s : FighterState} {l : ℕ} {p : FighterPhase}
    (hs : I.Holds s) (hp : s.activeAt d l = some p) : I.Active p :=
  hs.1 p (List.mem_of_find?_eq_some hp)

/-- Replacing the active phase of a level by a phase with the active property keeps the
invariant. -/
theorem Holds.putPhase {s : FighterState} {p : FighterPhase} (hs : I.Holds s)
    (hp : I.Active p) : I.Holds (s.putPhase d p) := by
  refine ⟨?_, hs.2⟩
  intro next hn
  rcases List.mem_cons.mp hn with rfl | hn
  · exact hp
  · exact hs.1 next (List.mem_filter.mp hn).1

/-- Cancelling a level keeps the invariant provided the archived record of the cancelled phase
satisfies the archive property. -/
theorem Holds.cancel {s : FighterState} (hs : I.Holds s) (l cause : ℕ) (reason : PhaseEnd)
    (hended : ∀ p, s.activeAt d l = some p →
      I.Archived ({ p with pending := [] }, s.tick, reason, cause)) :
    I.Holds (fighterCancel d l reason cause s) := by
  unfold fighterCancel
  split
  · exact hs
  · rename_i p hp
    refine ⟨fun q hq ↦ hs.1 q (List.mem_filter.mp hq).1, ?_⟩
    intro e he
    rcases List.mem_append.mp he with hold | hnew
    · exact hs.2 e hold
    · rw [List.mem_singleton.mp hnew]
      exact hended p hp

private theorem Holds.foldl {α : Type} {f : α → FighterState → FighterState}
    (hf : ∀ a s, I.Holds s → I.Holds (f a s)) (xs : List α) {s : FighterState}
    (hs : I.Holds s) : I.Holds (xs.foldl (fun s a ↦ f a s) s) := by
  induction xs generalizing s with
  | nil => exact hs
  | cons a xs ih => exact ih (hf a s hs)

private theorem Holds.cancel_of_ne {s : FighterState} (hs : I.Holds s) (l cause : ℕ)
    {reason : PhaseEnd} (hreason : reason ≠ .opponentExhausted) :
    I.Holds (fighterCancel d l reason cause s) :=
  hs.cancel l cause reason fun _ hp ↦ I.archived_cancel _ _ _ _ hreason (hs.active_of_activeAt hp)

private theorem Holds.abortAbove {s : FighterState} (hs : I.Holds s) (l : ℕ) :
    I.Holds (fighterAbortAbove d l s) := by
  unfold fighterAbortAbove
  refine Holds.foldl (f := fun (phase : FighterPhase) s ↦
    if l < phase.level then fighterCancel d phase.level .aborted l s else s) ?_ _ hs
  intro p t ht
  split
  · exact ht.cancel_of_ne _ _ (reason := .aborted) (by simp)
  · exact ht

private theorem Holds.allocate {s : FighterState} (hs : I.Holds s) (l : ℕ)
    (kind : DirectiveKind) (target : ℕ) (output : BitString) :
    I.Holds (fighterAllocate d l kind target output s).1 := by
  unfold fighterAllocate
  split
  · exact hs
  · cases hf : (if target = 0 then (none : Option BitString) else
        (fighterInputs d (target - 1)).find? (fun p ↦
          !s.allocated.any (fun a ↦ a.input == p))) with
    | none =>
      exact Holds.cancel_of_ne (s := { s with failed := true }) hs l l (reason := .saturated)
        (by simp)
    | some p =>
      dsimp only
      refine Holds.abortAbove ?_ l
      exact hs

private theorem Holds.payoff {s : FighterState} (hs : I.Holds s) (l : ℕ) (q : Coordinate) :
    I.Holds (fighterPayoff P d l q s) := by
  unfold fighterPayoff
  split
  · exact hs
  · split
    · have ha := hs.allocate l .payoff q.2 q.1
      cases he : fighterAllocate d l .payoff q.2 q.1 s with
      | mk next success =>
        simp only [he] at ha ⊢
        cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
        · exact ha
        · refine ⟨?_, ha.2⟩
          intro p hp
          obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hp
          exact I.active_congr old _ rfl (ha.1 old hold)
    · exact hs

/-- Servicing the pending requests of a level keeps the invariant. -/
theorem Holds.fulfillReady {s : FighterState} (hs : I.Holds s) (l : ℕ) :
    I.Holds (fighterFulfillReady P d l s) := by
  unfold fighterFulfillReady
  split
  · exact hs
  · exact Holds.foldl (f := fun q s ↦ fighterPayoff P d l q s) (fun q t ht ↦ ht.payoff l q) _ hs

private theorem Holds.fuelUnit {s : FighterState} (hs : I.Holds s) (l : ℕ) (q : Coordinate) :
    I.Holds (fighterFuelUnit P d l q s) := by
  unfold fighterFuelUnit
  split
  · exact hs
  · rename_i phase hp
    have hq := hs.active_of_activeAt hp
    split
    · let charged := { phase with controlledRemaining := phase.controlledRemaining - 1 }
      let index := fighterFreshString d
        (phase.indices[(phase.game d).coordinates.idxOf q]?.getD [])
      let out := pairCode (triple q.1 (q.2 - d) phase.candidate.1) index
      have hc : I.Active charged := I.active_congr phase _ rfl hq
      have ha := (hs.putPhase hc).allocate l .fuel (levelUpper l + d) out
      change I.Holds
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
        · refine Holds.fulfillReady (ha.putPhase ?_) l
          exact I.active_congr (charged.insertIndex d q index) _ rfl
            (I.active_insertIndex _ _ _ hc)
    · exact hs

private theorem Holds.fuelUnits {s : FighterState} (hs : I.Holds s) (l : ℕ) (q : Coordinate)
    (count : ℕ) : I.Holds (fighterFuelUnits P d l q count s) := by
  induction count generalizing s with
  | zero => exact hs
  | succ count ih => exact ih (hs.fuelUnit l q)

private theorem Holds.dummy {s : FighterState} (hs : I.Holds s) (l : ℕ) :
    I.Holds (fighterDummy d l s) := by
  unfold fighterDummy
  split
  · exact hs
  · rename_i phase hp
    have hq := hs.active_of_activeAt hp
    split
    · exact hs
    · rename_i output hout
      split
      · exact hs
      · have ha := hs.allocate l .dummy (levelInput d l) output
        cases he : fighterAllocate d l .dummy (levelInput d l) output s with
        | mk next success =>
          simp only [he] at ha ⊢
          cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
          · exact ha
          · exact ha.putPhase (I.active_congr phase _ rfl hq)

private theorem Holds.startPhase {s : FighterState} (hs : I.Holds s) (l : ℕ) (c : Candidate)
    (hc : validCandidate P.B (levelScale l) c = true) :
    I.Holds (fighterStartPhase P d l c s) := by
  unfold fighterStartPhase
  exact ((hs.cancel_of_ne l l (by simp)).abortAbove l).putPhase (I.active_construction l c _ hc)

private theorem Holds.flushBuffer {s : FighterState} (hs : I.Holds s) (l : ℕ) :
    I.Holds ((fighterFlushBuffer d l s).getD s) := by
  unfold fighterFlushBuffer
  cases hp : s.activeAt d l with
  | none => exact hs
  | some phase =>
    have hq := hs.active_of_activeAt hp
    simp only [bind, Option.bind_some]
    split
    · exact hs.putPhase (I.active_congr phase _ rfl hq)
    · exact hs

private theorem Holds.strategyMove {s : FighterState} (hs : I.Holds s) (l : ℕ) :
    I.Holds ((fighterStrategyMove P d l s).getD s) := by
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
        · let next := (phase.game d).coordinates.zipIdx.foldl (fun s (q, i) ↦
            fighterFuelUnits P d l q (move[i]?.getD 0) s) s
          have hn : I.Holds next :=
            Holds.foldl (f := fun (qi : Coordinate × ℕ) t ↦
              fighterFuelUnits P d l qi.1 (move[qi.2]?.getD 0) t)
              (fun qi t ht ↦ ht.fuelUnits l qi.1 _) _ hs
          change I.Holds ((match next.activeAt d l with
            | none => some next
            | some live => some (next.putPhase d
              { live with officialCode :=
                  ((phase.game d).afterMove (phase.official d) move).encode })).getD s)
          split
          · exact hn
          · rename_i live hlive
            exact hn.putPhase (I.active_congr live _ rfl (hn.active_of_activeAt hlive))
        · exact hs
    · exact hs

private theorem Holds.levelAction {s : FighterState} (hs : I.Holds s) (l : ℕ) :
    I.Holds ((fighterLevelAction P d l s).getD s) := by
  unfold fighterLevelAction
  cases hp : s.activeAt d l with
  | none => exact hs
  | some phase =>
    simp only [bind, Option.bind_some]
    split
    · exact hs.dummy l
    · split
      · exact hs.payoff l _
      · cases hf : fighterFlushBuffer d l s with
        | none => exact hs.strategyMove l
        | some next => simpa only [hf, Option.getD_some] using hs.flushBuffer l

private theorem Holds.closure {s : FighterState} (hs : I.Holds s) (l fuel : ℕ) :
    I.Holds (fighterClosure P d l fuel s) := by
  induction fuel generalizing s with
  | zero => exact hs
  | succ fuel ih =>
    simp only [fighterClosure]
    cases ha : fighterLevelAction P d l s with
    | none => exact hs
    | some next =>
      have hn := hs.levelAction l
      simp only [ha, Option.getD_some] at hn
      exact ih hn

private theorem Holds.processLevel {s : FighterState}
    (hopponent : ∀ l (e : ProgramEvent), produces P.B.V e.1 [] e.2 →
      ∀ s, I.Holds s → I.Holds (fighterOpponent P d l e s))
    (hs : I.Holds s) (l : ℕ) (ev : Option TimedEvent)
    (hev : ∀ e, ev = some e → eventAt P.B e.1 = some e) :
    I.Holds (fighterProcessLevel P d l ev s) := by
  unfold fighterProcessLevel fighterCloseLevel
  apply Holds.closure
  cases ev with
  | none => exact hs.fulfillReady l
  | some e =>
    dsimp only
    have he := hev e rfl
    split
    · rename_i henabled
      apply Holds.startPhase (hs.fulfillReady l)
      simp only [validCandidate, he, Option.any_some, decide_true, Bool.and_true]
      exact decide_eq_true henabled.2.1
    · exact hopponent l _ (canonical_enumeration_spec_sound P.B he).2 _ (hs.fulfillReady l)

/-- An invariant of the fighter scheduler holds at every tick of the construction provided it is
preserved by opponent insertions. -/
theorem holds_fighterState
    (hopponent : ∀ l (e : ProgramEvent), produces P.B.V e.1 [] e.2 →
      ∀ s, I.Holds s → I.Holds (fighterOpponent P d l e s)) (tick : ℕ) :
    I.Holds (fighterState P d tick) := by
  induction tick with
  | zero => exact ⟨by simp [fighterState, initialFighterState],
      by simp [fighterState, initialFighterState]⟩
  | succ tick ih =>
    change I.Holds (fighter_actions P d (tick + 1) (fighterState P d tick))
    unfold fighter_actions
    split
    · exact ⟨by simp [initialFighterState], by simp [initialFighterState]⟩
    · let current := { fighterState P d tick with
          tick := tick + 1, schedule := masterState P.B (tick + 1) }
      refine Holds.foldl (f := fun l s ↦ fighterProcessLevel P d l (eventAt P.B (tick + 1)) s)
        (fun l s hs ↦ hs.processLevel hopponent l _ ?_) _ (s := current) ih
      intro e he
      have ht := (canonical_enumeration_spec_sound P.B he).1
      simpa only [ht] using he

end FighterInvariant

end Kolmogorov.Milovanov
