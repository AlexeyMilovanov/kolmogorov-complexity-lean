/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Construction.Actions

/-!
# Invariants preserved by one level service

The fighter construction services one level `k` at a time (`fighterProcessLevel`): it first
fulfills ready requests, then starts a phase or reacts to an opponent event, and finally closes
the level under its enabled actions. Several stability proofs show that some property of the
global state survives such a service.

`ServiceInvariant P d k` packages such a property together with the finitely many facts about
the primitive state operations that the service is built from (installing a phase, canceling a
level, logging an allocation, ...). The main result `ServiceInvariant.inv_processLevel` then
shows once and for all that the property is preserved by `fighterProcessLevel P d k`. It is
used in `SettledLowerFrames` for the clock, the request ranges and the protected history of
lower levels.
-/

namespace Kolmogorov.Milovanov

/-- A property of the global state, with a companion property of active phase records, that
is preserved by every primitive operation used while servicing the level `k`.
The fields are exactly the closure properties needed by `ServiceInvariant.inv_processLevel`;
the operations on other levels are the cancellations of larger levels caused by level `k`. -/
structure ServiceInvariant (P : FighterParams) (d k : ℕ) where
  /-- The property of global states. -/
  Inv : FighterState → Prop
  /-- The property of active phase records. -/
  PhaseInv : FighterPhase → Prop
  /-- The phase active at level `k` has the phase property. -/
  phaseInv_of_activeAt : ∀ {s phase}, Inv s → s.activeAt d k = some phase → PhaseInv phase
  /-- The phase property depends only on the game, the level and the pending requests. -/
  phaseInv_congr : ∀ {phase phase'}, PhaseInv phase → phase'.gameCode = phase.gameCode →
    phase'.pending = phase.pending → phase'.level = phase.level → PhaseInv phase'
  /-- Funding requests preserves the phase property. -/
  phaseInv_fundRequests : ∀ {phase fulfilled},
    PhaseInv phase → PhaseInv (phase.fundRequests d fulfilled)
  /-- A phase freshly constructed at level `k` has the phase property. -/
  phaseInv_construction : ∀ (s : FighterState) (candidate : Candidate),
    P.Admissible d k → PhaseInv (fighter_construction P d k candidate s)
  /-- Installing a phase with the phase property preserves the state property. -/
  inv_putPhase : ∀ {s phase}, Inv s → PhaseInv phase → Inv (s.putPhase d phase)
  /-- Canceling a level at least `k` on behalf of level `k` preserves the state property. -/
  inv_cancel : ∀ {s j reason}, k ≤ j → Inv s → Inv (fighterCancel d j reason k s)
  /-- Recording saturation preserves the state property. -/
  inv_failed : ∀ {s}, Inv s → Inv { s with failed := true }
  /-- Logging an allocation of level `k` preserves the state property. -/
  inv_allocated : ∀ {s a}, a.level = k → Inv s →
    Inv { s with allocated := s.allocated ++ [a] }
  /-- Logging a started phase of level `k` preserves the state property. -/
  inv_started : ∀ {s candidate}, Inv s →
    Inv { s with started := s.started ++ [(k, candidate)] }
  /-- Recording a payoff of a pending request of the phase at level `k`, and removing the
  request from all pending lists, preserves the state property. -/
  inv_record : ∀ {s phase q}, Inv s → PhaseInv phase → phase.level = k → q ∈ phase.pending →
    Inv { s with
      fulfilled := s.fulfilled ++ [q]
      active := s.active.map
        (fun p ↦ { p with pending := p.pending.filter (fun r ↦ r != q) }) }

namespace ServiceInvariant

variable {P : FighterParams} {d k : ℕ} (I : ServiceInvariant P d k)

/-- Aborting the larger levels preserves the state property. -/
lemma inv_abortAbove {s : FighterState} (hs : I.Inv s) : I.Inv (fighterAbortAbove d k s) := by
  unfold fighterAbortAbove
  refine foldl_preserves_invariant _ _ _ (fun t phase ht ↦ ?_) hs
  split
  · rename_i hlt
    exact I.inv_cancel hlt.le ht
  · exact ht

/-- Allocation at level `k`, successful or not, preserves the state property. -/
lemma inv_allocate {kind : DirectiveKind} {target : ℕ} {output : BitString}
    {s : FighterState} (hs : I.Inv s) : I.Inv (fighterAllocate d k kind target output s).1 := by
  unfold fighterAllocate
  split
  · exact hs
  · cases hf : (if target = 0 then (none : Option BitString) else
        (fighterInputs d (target - 1)).find? (fun p ↦
          !s.allocated.any (fun a ↦ a.input == p))) with
    | none => exact I.inv_cancel le_rfl (I.inv_failed hs)
    | some p => exact I.inv_abortAbove (I.inv_allocated rfl hs)

/-- `inv_allocate`, stated for a named result of the allocation. -/
lemma inv_of_allocate_eq {kind : DirectiveKind} {target : ℕ} {output : BitString}
    {s next : FighterState} {success : Bool}
    (h : fighterAllocate d k kind target output s = (next, success)) (hs : I.Inv s) :
    I.Inv next := by
  simpa only [h] using I.inv_allocate (kind := kind) (target := target) (output := output) hs

/-- Paying off a request at level `k` preserves the state property. -/
lemma inv_payoff (q : Coordinate) {s : FighterState} (hs : I.Inv s) :
    I.Inv (fighterPayoff P d k q s) := by
  unfold fighterPayoff
  split
  · exact hs
  · rename_i phase hphase
    split
    · rename_i hguard
      split
      rename_i next success he
      have hnext := I.inv_of_allocate_eq he hs
      split
      · exact I.inv_record hnext (I.phaseInv_of_activeAt hs hphase)
          (FighterState.level_eq_of_activeAt_eq_some hphase) hguard.1
      · exact hnext
    · exact hs

/-- Fulfilling all ready requests of level `k` preserves the state property. -/
lemma inv_fulfillReady {s : FighterState} (hs : I.Inv s) :
    I.Inv (fighterFulfillReady P d k s) := by
  unfold fighterFulfillReady
  split
  · exact hs
  · exact foldl_preserves_invariant _ _ _ (fun t q ht ↦ I.inv_payoff q ht) hs

/-- One fuel unit at level `k` preserves the state property. -/
lemma inv_fuelUnit (q : Coordinate) {s : FighterState} (hs : I.Inv s) :
    I.Inv (fighterFuelUnit P d k q s) := by
  unfold fighterFuelUnit
  split
  · exact hs
  · rename_i phase hphase
    have hp := I.phaseInv_of_activeAt hs hphase
    split
    · dsimp only
      have hcharged : I.PhaseInv
          { phase with controlledRemaining := phase.controlledRemaining - 1 } :=
        I.phaseInv_congr hp rfl rfl rfl
      split
      · exact I.inv_fulfillReady (I.inv_putPhase (I.inv_allocate (I.inv_putPhase hs hcharged))
          (I.phaseInv_fundRequests (I.phaseInv_congr hcharged rfl rfl rfl)))
      · exact I.inv_allocate (I.inv_putPhase hs hcharged)
    · exact hs

/-- Several consecutive fuel units at level `k` preserve the state property. -/
lemma inv_fuelUnits (q : Coordinate) (count : ℕ) {s : FighterState} (hs : I.Inv s) :
    I.Inv (fighterFuelUnits P d k q count s) := by
  induction count generalizing s with
  | zero => exact hs
  | succ count ih => exact ih (I.inv_fuelUnit q hs)

/-- Reacting to an opponent event at level `k` preserves the state property. -/
lemma inv_opponent (event : ProgramEvent) {s : FighterState} (hs : I.Inv s) :
    I.Inv (fighterOpponent P d k event s) := by
  unfold fighterOpponent
  split
  · exact hs
  · rename_i phase hphase
    have hp := I.phaseInv_of_activeAt hs hphase
    split
    · exact hs
    · split
      · exact hs
      · split
        · exact I.inv_cancel le_rfl hs
        · exact I.inv_fulfillReady (I.inv_putPhase hs
            (I.phaseInv_fundRequests (I.phaseInv_congr hp rfl rfl rfl)))

/-- Allocating the dummy of level `k` preserves the state property. -/
lemma inv_dummy {s : FighterState} (hs : I.Inv s) : I.Inv (fighterDummy d k s) := by
  unfold fighterDummy
  split
  · exact hs
  · rename_i phase hphase
    have hp := I.phaseInv_of_activeAt hs hphase
    split
    · exact hs
    · split
      · exact hs
      · split
        rename_i next success he
        have hnext := I.inv_of_allocate_eq he hs
        split
        · exact I.inv_putPhase hnext (I.phaseInv_congr hp rfl rfl rfl)
        · exact hnext

/-- Flushing the buffer of level `k`, when enabled, preserves the state property. -/
lemma inv_flushBuffer {s : FighterState} (hs : I.Inv s) :
    I.Inv ((fighterFlushBuffer d k s).getD s) := by
  cases hphase : s.activeAt d k with
  | none => simpa [fighterFlushBuffer, hphase] using hs
  | some phase =>
    have hp := I.phaseInv_of_activeAt hs hphase
    simp only [fighterFlushBuffer, hphase, bind, Option.bind_some]
    split
    · exact I.inv_putPhase hs (I.phaseInv_congr hp rfl rfl rfl)
    · exact hs

/-- The controlled strategy move of level `k`, when enabled, preserves the state property. -/
lemma inv_strategyMove {s : FighterState} (hs : I.Inv s) :
    I.Inv ((fighterStrategyMove P d k s).getD s) := by
  cases hphase : s.activeAt d k with
  | none => simpa [fighterStrategyMove, hphase] using hs
  | some phase =>
    simp only [fighterStrategyMove, hphase, bind, Option.bind_some]
    split
    · cases hm : (phase.game d).strategy (phase.official d) with
      | none => exact hs
      | some move =>
        simp only [Option.bind_some]
        split
        · have hn := foldl_preserves_invariant (Good := I.Inv)
            (f := fun s (qi : Coordinate × ℕ) ↦ fighterFuelUnits P d k qi.1 (move[qi.2]?.getD 0) s)
            (phase.game d).coordinates.zipIdx (fun t qi ht ↦ I.inv_fuelUnits qi.1 _ ht) hs
          cases hlive : (List.foldl _ s (phase.game d).coordinates.zipIdx).activeAt d k with
          | none => exact hn
          | some live => exact I.inv_putPhase hn (I.phaseInv_congr
              (I.phaseInv_of_activeAt hn hlive) rfl rfl rfl)
        · exact hs
    · exact hs

/-- One enabled action of level `k` preserves the state property. -/
lemma inv_levelAction {s : FighterState} (hs : I.Inv s) :
    I.Inv ((fighterLevelAction P d k s).getD s) := by
  cases hphase : s.activeAt d k with
  | none => simpa [fighterLevelAction, hphase] using hs
  | some phase =>
    simp only [fighterLevelAction, hphase, bind, Option.bind_some]
    split
    · exact I.inv_dummy hs
    · split
      · exact I.inv_payoff _ hs
      · cases hf : fighterFlushBuffer d k s with
        | none => exact I.inv_strategyMove hs
        | some next => simpa only [hf, Option.getD_some] using I.inv_flushBuffer hs

/-- The closure of level `k` under enabled actions preserves the state property. -/
lemma inv_closure (fuel : ℕ) {s : FighterState} (hs : I.Inv s) :
    I.Inv (fighterClosure P d k fuel s) := by
  induction fuel generalizing s with
  | zero => exact hs
  | succ fuel ih =>
    simp only [fighterClosure]
    cases ha : fighterLevelAction P d k s with
    | none => exact hs
    | some next =>
      have hn := I.inv_levelAction hs
      simp only [ha, Option.getD_some] at hn
      exact ih hn

/-- Starting a phase at level `k` preserves the state property. -/
lemma inv_startPhase (candidate : Candidate) (hadm : P.Admissible d k) {s : FighterState}
    (hs : I.Inv s) : I.Inv (fighterStartPhase P d k candidate s) := by
  unfold fighterStartPhase
  exact I.inv_started (I.inv_putPhase (I.inv_abortAbove (I.inv_cancel le_rfl hs))
    (I.phaseInv_construction _ candidate hadm))

/-- A complete service of level `k` preserves the state property. -/
lemma inv_processLevel (event : Option TimedEvent) {s : FighterState} (hs : I.Inv s) :
    I.Inv (fighterProcessLevel P d k event s) := by
  unfold fighterProcessLevel
  refine I.inv_closure _ ?_
  have hc := I.inv_fulfillReady hs
  cases event with
  | none => exact hc
  | some e =>
    dsimp only
    split
    · rename_i hstart
      exact I.inv_startPhase _ hstart.2.2 hc
    · exact I.inv_opponent _ hc

end ServiceInvariant

end Kolmogorov.Milovanov
