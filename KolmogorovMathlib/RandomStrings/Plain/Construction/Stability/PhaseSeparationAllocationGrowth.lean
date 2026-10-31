/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.FundedRequest
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.SettledLowerLevels

/-!
# Growth of the permanent allocation table

This module proves that, at a positive padding `d`, each active phase's saved allocation
snapshot stays inside the permanent allocation table
(`fighterState_initialAllocations_subset_allocated`).

It is obtained from a transition invariant. The relation `AllocGrowth` between two states says
that the allocation table only grows and that the snapshot invariant is preserved. It is closed
under composition, and it is shown for each action of `fighter_actions` in turn, bottom-up from
cancelling and allocating to the level closure. The invariant then follows by induction on the
tick.

`PhaseSeparationSources` and `Diagonal.VirtualStabilization` rely on this fact for blueprint
node `constr:separation`.
-/

namespace Kolmogorov.Milovanov

/-- Every active phase of the state has its saved allocation snapshot inside the permanent
allocation table. -/
private def SnapshotsSaved (s : FighterState) : Prop :=
  ∀ p ∈ s.active, p.initialAllocations ⊆ s.allocated

/-- The allocation table of `t` extends that of `s`, and snapshots stay saved. -/
private structure AllocGrowth (s t : FighterState) : Prop where
  subset : s.allocated ⊆ t.allocated
  saved : SnapshotsSaved s → SnapshotsSaved t

namespace AllocGrowth

private lemma refl (s : FighterState) : AllocGrowth s s :=
  ⟨fun _ h ↦ h, id⟩

private lemma trans {s t u : FighterState} (hst : AllocGrowth s t) (htu : AllocGrowth t u) :
    AllocGrowth s u :=
  ⟨fun _ h ↦ htu.subset (hst.subset h), fun h ↦ htu.saved (hst.saved h)⟩

private lemma of_eq {s t : FighterState} (hallocated : t.allocated = s.allocated)
    (hactive : t.active = s.active) : AllocGrowth s t := by
  refine ⟨by rw [hallocated], fun hs p hp ↦ ?_⟩
  rw [hallocated]
  exact hs p (hactive ▸ hp)

private lemma foldl {α : Type} (f : α → FighterState → FighterState)
    (hf : ∀ a s, AllocGrowth s (f a s)) (xs : List α) (s : FighterState) :
    AllocGrowth s (xs.foldl (fun s a ↦ f a s) s) := by
  induction xs generalizing s with
  | nil => exact refl s
  | cons a xs ih => exact trans (hf a s) (ih _)

/-- Storing a phase whose snapshot is already in the table keeps the snapshots saved. -/
private lemma putPhase {s t : FighterState} (d : ℕ) (hst : AllocGrowth s t) (p : FighterPhase)
    (hp : SnapshotsSaved s → p.initialAllocations ⊆ t.allocated) :
    AllocGrowth s (t.putPhase d p) := by
  refine ⟨hst.subset, fun hs next hn ↦ ?_⟩
  rcases List.mem_cons.mp hn with rfl | hn
  · exact hp hs
  · exact hst.saved hs next (List.mem_filter.mp hn).1

private lemma snapshot_subset_of_activeAt {s : FighterState} {d l : ℕ} {p : FighterPhase}
    (hs : SnapshotsSaved s) (hp : s.activeAt d l = some p) : p.initialAllocations ⊆ s.allocated :=
  hs p (List.mem_of_find?_eq_some hp)

private lemma cancel (d l : ℕ) (reason : PhaseEnd) (cause : ℕ) (s : FighterState) :
    AllocGrowth s (fighterCancel d l reason cause s) := by
  unfold fighterCancel
  split
  · exact refl s
  · exact ⟨fun _ h ↦ h, fun hs p hp ↦ hs p (List.mem_filter.mp hp).1⟩

private lemma abortAbove (d l : ℕ) (s : FighterState) :
    AllocGrowth s (fighterAbortAbove d l s) := by
  unfold fighterAbortAbove
  apply foldl
  intro p t
  split
  · exact cancel _ _ _ _ _
  · exact refl t

private lemma allocate (d l : ℕ) (kind : DirectiveKind) (target : ℕ) (out : BitString)
    (s : FighterState) : AllocGrowth s (fighterAllocate d l kind target out s).1 := by
  unfold fighterAllocate
  cases hactive : s.activeAt d l with
  | none => exact refl s
  | some phase =>
    dsimp only
    by_cases ht : target = 0
    · simp only [ht, ↓reduceIte]
      exact trans (t := { s with failed := true }) (of_eq rfl rfl) (cancel _ _ _ _ _)
    · simp only [ht, ↓reduceIte]
      cases hf : (fighterInputs d (target - 1)).find?
          (fun p ↦ !s.allocated.any (fun a ↦ a.input == p)) with
      | none => exact trans (t := { s with failed := true }) (of_eq rfl rfl) (cancel _ _ _ _ _)
      | some p =>
        refine trans (t := { s with allocated := s.allocated ++
          [⟨l, phase.candidate, s.tick, kind, target, p, out⟩] }) ⟨?_, ?_⟩ (abortAbove _ _ _)
        · exact fun _ h ↦ List.mem_append_left _ h
        · exact fun hs q hq _ ha ↦ List.mem_append_left _ (hs q hq ha)

private lemma payoff (P : FighterParams) (d l : ℕ) (q : Coordinate) (s : FighterState) :
    AllocGrowth s (fighterPayoff P d l q s) := by
  unfold fighterPayoff
  split
  · exact refl s
  · split
    · have ha := allocate d l .payoff q.2 q.1 s
      cases he : fighterAllocate d l .payoff q.2 q.1 s with
      | mk next success =>
        simp only [he] at ha ⊢
        cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
        · exact ha
        · refine trans ha ⟨fun _ h ↦ h, ?_⟩
          intro hs p hp
          obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hp
          exact hs old hold
    · exact refl s

private lemma fulfillReady (P : FighterParams) (d l : ℕ) (s : FighterState) :
    AllocGrowth s (fighterFulfillReady P d l s) := by
  unfold fighterFulfillReady
  split
  · exact refl s
  · exact foldl _ (fun q t ↦ payoff P d l q t) _ _

private lemma fuelUnit (P : FighterParams) (d l : ℕ) (q : Coordinate) (s : FighterState) :
    AllocGrowth s (fighterFuelUnit P d l q s) := by
  unfold fighterFuelUnit
  split
  · exact refl s
  · rename_i phase hp
    split
    · let charged := { phase with controlledRemaining := phase.controlledRemaining - 1 }
      let index := fighterFreshString d
        (phase.indices[(phase.game d).coordinates.idxOf q]?.getD [])
      let out := pairCode (triple q.1 (q.2 - d) phase.candidate.1) index
      have h1 : AllocGrowth s (s.putPhase d charged) :=
        putPhase d (refl s) charged (fun hs ↦ snapshot_subset_of_activeAt (p := phase) hs hp)
      have ha := allocate d l .fuel (levelUpper l + d) out (s.putPhase d charged)
      change AllocGrowth s
        (match fighterAllocate d l .fuel (levelUpper l + d) out (s.putPhase d charged) with
          | (next, success) => if success then
            fighterFulfillReady P d l
              (next.putPhase d ((charged.insertIndex d q index).fundRequests d next.fulfilled))
            else next)
      cases he : fighterAllocate d l .fuel (levelUpper l + d) out (s.putPhase d charged) with
      | mk next success =>
        rw [he] at ha
        cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
        · exact trans h1 ha
        · refine trans (putPhase d (trans h1 ha) _ fun hs ↦ ?_) (fulfillReady P d l _)
          exact fun _ h ↦ (trans h1 ha).subset (snapshot_subset_of_activeAt (p := phase) hs hp h)
    · exact refl s

private lemma fuelUnits (P : FighterParams) (d l : ℕ) (q : Coordinate) (count : ℕ)
    (s : FighterState) : AllocGrowth s (fighterFuelUnits P d l q count s) := by
  induction count generalizing s with
  | zero => exact refl s
  | succ count ih => exact trans (fuelUnit P d l q s) (ih _)

private lemma dummy (d l : ℕ) (s : FighterState) : AllocGrowth s (fighterDummy d l s) := by
  unfold fighterDummy
  split
  · exact refl s
  · rename_i phase hp
    split
    · exact refl s
    · rename_i output hout
      split
      · exact refl s
      · have ha := allocate d l .dummy (levelInput d l) output s
        cases he : fighterAllocate d l .dummy (levelInput d l) output s with
        | mk next success =>
          simp only [he] at ha ⊢
          cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
          · exact ha
          · exact putPhase d ha _ fun hs _ h ↦
              ha.subset (snapshot_subset_of_activeAt (p := phase) hs hp h)

private lemma opponent (P : FighterParams) (d l : ℕ) (e : ProgramEvent) (s : FighterState) :
    AllocGrowth s (fighterOpponent P d l e s) := by
  unfold fighterOpponent
  split
  · exact refl s
  · rename_i phase hp
    split
    · exact refl s
    · split
      · exact refl s
      · split
        · exact cancel _ _ _ _ _
        · refine trans (putPhase d (refl s) _ ?_) (fulfillReady P d l _)
          exact fun hs ↦ snapshot_subset_of_activeAt (p := phase) hs hp

private lemma startPhase (P : FighterParams) (d l : ℕ) (c : Candidate) (s : FighterState) :
    AllocGrowth s (fighterStartPhase P d l c s) := by
  unfold fighterStartPhase
  let waiting := fighterAbortAbove d l (fighterCancel d l .replaced l s)
  have hw : AllocGrowth s waiting := trans (cancel d l .replaced l s) (abortAbove d l _)
  have hp : AllocGrowth waiting (waiting.putPhase d (fighter_construction P d l c waiting)) :=
    putPhase d (refl waiting) _ fun _ _ h ↦ h
  exact trans (trans hw hp) (of_eq rfl rfl)

private lemma flushBuffer (d l : ℕ) (s : FighterState) :
    AllocGrowth s ((fighterFlushBuffer d l s).getD s) := by
  unfold fighterFlushBuffer
  cases hp : s.activeAt d l with
  | none => exact refl s
  | some phase =>
    simp only [bind, Option.bind_some]
    split
    · refine putPhase d (refl s) _ ?_
      exact fun hs ↦ snapshot_subset_of_activeAt (p := phase) hs hp
    · exact refl s

private lemma strategyMove (P : FighterParams) (d l : ℕ) (s : FighterState) :
    AllocGrowth s ((fighterStrategyMove P d l s).getD s) := by
  unfold fighterStrategyMove
  cases hp : s.activeAt d l with
  | none => exact refl s
  | some phase =>
    simp only [bind, Option.bind_some]
    split
    · cases hm : (phase.game d).strategy (phase.official d) with
      | none => exact refl s
      | some move =>
        simp only [Option.bind_some]
        split
        · let next := (phase.game d).coordinates.zipIdx.foldl (fun s (q, i) ↦
            fighterFuelUnits P d l q (move[i]?.getD 0) s) s
          have hn : AllocGrowth s next :=
            foldl _ (fun (qi : Coordinate × ℕ) t ↦ fuelUnits P d l qi.1 (move[qi.2]?.getD 0) t) _ _
          change AllocGrowth s ((match next.activeAt d l with
            | none => some next
            | some live => some (next.putPhase d
              { live with officialCode :=
                ((phase.game d).afterMove (phase.official d) move).encode })).getD s)
          split
          · exact hn
          · rename_i live hlive
            refine trans hn (putPhase d (refl next) _ ?_)
            exact fun hs ↦ snapshot_subset_of_activeAt (p := live) hs hlive
        · exact refl s
    · exact refl s

private lemma levelAction (P : FighterParams) (d l : ℕ) (s : FighterState) :
    AllocGrowth s ((fighterLevelAction P d l s).getD s) := by
  unfold fighterLevelAction
  cases hp : s.activeAt d l with
  | none => exact refl s
  | some phase =>
    simp only [bind, Option.bind_some]
    split
    · exact dummy d l s
    · split
      · exact payoff P d l _ s
      · cases hf : fighterFlushBuffer d l s with
        | none => exact strategyMove P d l s
        | some next => simpa only [hf, Option.getD_some] using flushBuffer d l s

private lemma closure (P : FighterParams) (d l fuel : ℕ) (s : FighterState) :
    AllocGrowth s (fighterClosure P d l fuel s) := by
  induction fuel generalizing s with
  | zero => exact refl s
  | succ fuel ih =>
    simp only [fighterClosure]
    cases ha : fighterLevelAction P d l s with
    | none => exact refl s
    | some next =>
      have hn := levelAction P d l s
      simp only [ha, Option.getD_some] at hn
      exact trans hn (ih next)

private lemma processLevel (P : FighterParams) (d l : ℕ) (e : Option TimedEvent)
    (s : FighterState) : AllocGrowth s (fighterProcessLevel P d l e s) := by
  unfold fighterProcessLevel fighterCloseLevel
  refine trans ?_ (closure P d l _ _)
  cases e with
  | none => exact fulfillReady P d l s
  | some e =>
    dsimp only
    split
    · exact trans (fulfillReady P d l s) (startPhase P d l _ _)
    · exact trans (fulfillReady P d l s) (opponent P d l _ _)

private lemma fighterActions (P : FighterParams) (d tick : ℕ) (hd : 1 ≤ d)
    (s : FighterState) : AllocGrowth s (fighter_actions P d tick s) := by
  unfold fighter_actions
  rw [ite_eq_right (by omega : d ≠ 0)]
  refine trans (t := { s with tick := tick, schedule := masterState P.B tick })
    (of_eq rfl rfl) ?_
  exact foldl _ (fun l t ↦ processLevel P d l _ t) _ _

end AllocGrowth

/-- At every completed tick with positive padding, each active phase's saved allocation
snapshot consists of permanent allocations of that tick. -/
theorem fighterState_initialAllocations_subset_allocated (P : FighterParams) (d tick : ℕ)
    (hd : 1 ≤ d) :
    ∀ p ∈ (fighterState P d tick).active,
      p.initialAllocations ⊆ (fighterState P d tick).allocated := by
  induction tick with
  | zero => simp [fighterState, initialFighterState]
  | succ tick ih => exact (AllocGrowth.fighterActions P d (tick + 1) hd _).saved ih

end Kolmogorov.Milovanov
