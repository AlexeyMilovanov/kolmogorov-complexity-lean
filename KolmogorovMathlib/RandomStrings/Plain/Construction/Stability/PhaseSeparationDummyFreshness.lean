/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.PhaseSeparationClasses

/-!
# Freshness and issuance of dummy strings in reachable states

For blueprint node `constr:separation`, the dummy string of a true-marker phase must lie
outside the referee's query tree and outside the saved table of short outputs, and an issued
dummy must have a matching permanent allocation of exactly the right length.

The construction chooses a phase's dummy by `fighterFreshString`, which is absent from any
list it is given, and it records the allocation whenever it issues the dummy. This module shows
that every operation of the fighter construction (cancelling, allocating, paying off, fuelling,
the opponent's and the strategy's moves, the level actions and the processing of one tick)
keeps this invariant of the active phases, hence that it holds in every reachable state
`fighterState P d tick`. `PhaseSeparation` specialises the result to the true-marker phase.
-/

namespace Kolmogorov.Milovanov

/-- The construction chooses its dummy outside the full query tree and the saved bounded
outputs, using the constructor state's clock as the candidate timestamp. -/
private lemma fighter_construction_dummy_fresh
    (P : FighterParams) (d l : ℕ) (c : Candidate)
    (s : FighterState) (ht : c.2 = s.tick) :
    ∀ z, (fighter_construction P d l c s).dummy = some z →
      z ∉ fighterStageOutputs P d (levelInput d l) c.2 s.allocated ∧
      ∀ q ∈ (P.family.tree d l (levelInput d l)).queries, q.1 ≠ z := by
  intro z hz
  dsimp only [fighter_construction, FighterPhase.fundRequests] at hz
  split at hz
  · have heq := Option.some.inj hz
    subst z
    have hfresh := fighterFreshString_notMem d
      ((P.family.tree d l (levelInput d l)).queries.map Prod.fst ++
        fighterStageOutputList P d (levelInput d l) s.tick s.allocated)
    constructor
    · intro hmem
      apply hfresh
      apply List.mem_append_right
      simpa only [fighterStageOutputs, List.mem_toFinset, ht] using hmem
    · intro q hq heq
      apply hfresh
      apply List.mem_append_left
      rw [← heq]
      exact List.mem_map.mpr ⟨q, hq, rfl⟩
  · contradiction

section Invariant

variable {P : FighterParams} {d : ℕ}

/-- The dummy of the phase `p`, if any, avoids the saved output table of its candidate and
the whole query tree of its level. -/
private abbrev DummyFresh (P : FighterParams) (d : ℕ) (p : FighterPhase) : Prop :=
  ∀ z, p.dummy = some z →
    z ∉ fighterStageOutputs P d (levelInput d p.level) p.candidate.2 p.initialAllocations ∧
    ∀ q ∈ (P.family.tree d p.level (levelInput d p.level)).queries, q.1 ≠ z

/-- If the phase `p` has issued its dummy, some allocation in `allocated` outputs the dummy
and has input of exactly the length that the level's dummy target demands. -/
private abbrev DummyRecorded (d : ℕ) (allocated : List AllocatedDirective)
    (p : FighterPhase) : Prop :=
  p.dummyIssued = true → ∃ z a, p.dummy = some z ∧
    a ∈ allocated ∧ a.output = z ∧ a.input.length + 1 = levelInput d p.level

/-- A phase is *sound* with respect to a list of allocations if its dummy is fresh and, once
issued, recorded in that list. -/
private abbrev PhaseSound (P : FighterParams) (d : ℕ) (allocated : List AllocatedDirective)
    (p : FighterPhase) : Prop :=
  DummyFresh P d p ∧ DummyRecorded d allocated p

/-- Every active phase of the state `s` is sound with respect to its allocations. -/
private abbrev ActiveSound (P : FighterParams) (d : ℕ) (s : FighterState) : Prop :=
  ∀ p ∈ s.active, PhaseSound P d s.allocated p

/-- A transition from `s` to `t` keeps the clock, only grows the allocation list, and ends in
a state whose active phases are sound. -/
private abbrev SoundStep (P : FighterParams) (d : ℕ) (s t : FighterState) : Prop :=
  t.tick = s.tick ∧ s.allocated ⊆ t.allocated ∧ ActiveSound P d t

private lemma PhaseSound.mono {as bs : List AllocatedDirective} (h : as ⊆ bs)
    {p : FighterPhase} (hp : PhaseSound P d as p) : PhaseSound P d bs p := by
  refine ⟨hp.1, fun hi ↦ ?_⟩
  obtain ⟨z, a, hz, ha, ho, hn⟩ := hp.2 hi
  exact ⟨z, a, hz, h ha, ho, hn⟩

private lemma SoundStep.refl {s : FighterState} (hs : ActiveSound P d s) : SoundStep P d s s :=
  ⟨rfl, fun _ h ↦ h, hs⟩

private lemma SoundStep.trans {s t u : FighterState} (h₁ : SoundStep P d s t)
    (h₂ : SoundStep P d t u) : SoundStep P d s u :=
  ⟨h₂.1.trans h₁.1, fun _ h ↦ h₂.2.1 (h₁.2.1 h), h₂.2.2⟩

private lemma soundStep_foldl {α : Type} (f : α → FighterState → FighterState)
    (hf : ∀ a s, ActiveSound P d s → SoundStep P d s (f a s))
    (xs : List α) (s : FighterState) (hs : ActiveSound P d s) :
    SoundStep P d s (xs.foldl (fun s a ↦ f a s) s) := by
  induction xs generalizing s with
  | nil => exact .refl hs
  | cons a xs ih => exact (hf a s hs).trans (ih _ (hf a s hs).2.2)

private lemma phaseSound_of_activeAt {s : FighterState} {j : ℕ} {p : FighterPhase}
    (hs : ActiveSound P d s) (hp : s.activeAt d j = some p) : PhaseSound P d s.allocated p :=
  hs p (List.mem_of_find?_eq_some hp)

private lemma soundStep_putPhase (s : FighterState) (p : FighterPhase)
    (hs : ActiveSound P d s) (hp : PhaseSound P d s.allocated p) :
    SoundStep P d s (s.putPhase d p) := by
  refine ⟨rfl, fun _ h ↦ h, ?_⟩
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq
  · exact hp
  · exact hs q (List.mem_filter.mp hq).1

private lemma soundStep_cancel (s : FighterState) (j : ℕ) (reason : PhaseEnd) (cause : ℕ)
    (hs : ActiveSound P d s) : SoundStep P d s (fighterCancel d j reason cause s) := by
  unfold fighterCancel
  split
  · exact .refl hs
  · exact ⟨rfl, fun _ h ↦ h, fun p hp ↦ hs p (List.mem_filter.mp hp).1⟩

private lemma soundStep_abortAbove (s : FighterState) (j : ℕ) (hs : ActiveSound P d s) :
    SoundStep P d s (fighterAbortAbove d j s) := by
  unfold fighterAbortAbove
  apply soundStep_foldl _ _ _ s hs
  intro p t ht
  split
  · exact soundStep_cancel t p.level .aborted j ht
  · exact .refl ht

private lemma soundStep_allocate (s : FighterState) (j : ℕ) (kind : DirectiveKind)
    (target : ℕ) (output : BitString) (hs : ActiveSound P d s) :
    SoundStep P d s (fighterAllocate d j kind target output s).1 := by
  unfold fighterAllocate
  split
  · exact .refl hs
  · rename_i phase hphase
    cases hf : (if target = 0 then (none : Option BitString) else
        (fighterInputs d (target - 1)).find? (fun p ↦
          !s.allocated.any (fun a ↦ a.input == p))) with
    | none => exact soundStep_cancel { s with failed := true } j .saturated j hs
    | some input =>
      let entry : AllocatedDirective := ⟨j, phase.candidate, s.tick, kind, target, input, output⟩
      let grown := { s with allocated := s.allocated ++ [entry] }
      have hg : SoundStep P d s grown :=
        ⟨rfl, List.subset_append_left _ _, fun p hp ↦
          (hs p hp).mono (List.subset_append_left _ _)⟩
      exact hg.trans (soundStep_abortAbove grown j hg.2.2)

private lemma soundStep_payoff (s : FighterState) (j : ℕ) (q : Coordinate)
    (hs : ActiveSound P d s) : SoundStep P d s (fighterPayoff P d j q s) := by
  unfold fighterPayoff
  split
  · exact .refl hs
  · split
    · have ha := soundStep_allocate s j .payoff q.2 q.1 hs
      cases he : fighterAllocate d j .payoff q.2 q.1 s with
      | mk next success =>
        simp only [he] at ha ⊢
        cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
        · exact ha
        · refine ⟨ha.1, ha.2.1, ?_⟩
          intro p hp
          obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hp
          exact ha.2.2 old hold
    · exact .refl hs

private lemma soundStep_fulfillReady (s : FighterState) (j : ℕ) (hs : ActiveSound P d s) :
    SoundStep P d s (fighterFulfillReady P d j s) := by
  unfold fighterFulfillReady
  split
  · exact .refl hs
  · exact soundStep_foldl (fun q t ↦ fighterPayoff P d j q t)
      (fun q t ht ↦ soundStep_payoff t j q ht) _ s hs

private lemma soundStep_fuelUnit (s : FighterState) (j : ℕ) (q : Coordinate)
    (hs : ActiveSound P d s) : SoundStep P d s (fighterFuelUnit P d j q s) := by
  unfold fighterFuelUnit
  split
  · exact .refl hs
  · rename_i phase hphase
    have hp := phaseSound_of_activeAt hs hphase
    split
    · let charged := { phase with controlledRemaining := phase.controlledRemaining - 1 }
      let index := fighterFreshString d
        (phase.indices[(phase.game d).coordinates.idxOf q]?.getD [])
      let output := pairCode (triple q.1 (q.2 - d) phase.candidate.1) index
      have hc := soundStep_putPhase s charged hs hp
      have ha := soundStep_allocate (s.putPhase d charged) j .fuel (levelUpper j + d) output
        hc.2.2
      have hbefore := hc.trans ha
      change SoundStep P d s (match fighterAllocate d j .fuel (levelUpper j + d) output
        (s.putPhase d charged) with
        | (next, success) => if success then fighterFulfillReady P d j
            (next.putPhase d ((charged.insertIndex d q index).fundRequests d next.fulfilled))
          else next)
      cases he : fighterAllocate d j .fuel (levelUpper j + d) output (s.putPhase d charged) with
      | mk next success =>
        rw [he] at hbefore
        cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
        · exact hbefore
        · have hp' : PhaseSound P d next.allocated
              ((charged.insertIndex d q index).fundRequests d next.fulfilled) :=
            hp.mono hbefore.2.1
          have hput := soundStep_putPhase next _ hbefore.2.2 hp'
          exact hbefore.trans (hput.trans (soundStep_fulfillReady _ j hput.2.2))
    · exact .refl hs

private lemma soundStep_fuelUnits (s : FighterState) (j : ℕ) (q : Coordinate) (count : ℕ)
    (hs : ActiveSound P d s) : SoundStep P d s (fighterFuelUnits P d j q count s) := by
  induction count generalizing s with
  | zero => exact .refl hs
  | succ count ih =>
    exact (soundStep_fuelUnit s j q hs).trans (ih _ (soundStep_fuelUnit s j q hs).2.2)

private lemma soundStep_opponent (s : FighterState) (j : ℕ) (e : ProgramEvent)
    (hs : ActiveSound P d s) : SoundStep P d s (fighterOpponent P d j e s) := by
  unfold fighterOpponent
  split
  · exact .refl hs
  · rename_i phase hphase
    have hp := phaseSound_of_activeAt hs hphase
    split
    · exact .refl hs
    · rename_i q index htuple
      split
      · exact .refl hs
      · split
        · exact soundStep_cancel s j .opponentExhausted j hs
        · let inserted := phase.insertIndex d q index
          let next := { inserted with
            opponentRemaining := phase.opponentRemaining - 1
            buffer := (phase.game d).addCounters phase.buffer (phase.unitVector d q) }
          have hp' : PhaseSound P d s.allocated (next.fundRequests d s.fulfilled) := hp
          have hput := soundStep_putPhase s _ hs hp'
          exact hput.trans (soundStep_fulfillReady _ j hput.2.2)

private lemma soundStep_dummy (s : FighterState) (j : ℕ) (hs : ActiveSound P d s) :
    SoundStep P d s (fighterDummy d j s) := by
  unfold fighterDummy
  split
  · exact .refl hs
  · rename_i phase hphase
    have hp := phaseSound_of_activeAt hs hphase
    have hlevel : phase.level = j := beq_iff_eq.mp
      (List.find?_some (p := fun p : FighterPhase ↦ p.level == j) hphase)
    split
    · exact .refl hs
    · rename_i output hout
      split
      · exact .refl hs
      · have ha := soundStep_allocate s j .dummy (levelInput d j) output hs
        cases he : fighterAllocate d j .dummy (levelInput d j) output s with
        | mk next success =>
          simp only [he] at ha ⊢
          cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
          · exact ha
          · obtain ⟨a, hamem, hlen, ho⟩ :=
              exists_allocation_of_fighterAllocate_success
                d j (levelInput d j) .dummy output s next he
            have hp' : PhaseSound P d next.allocated { phase with dummyIssued := true } := by
              refine ⟨hp.1, fun _ ↦ ⟨output, a, hout, hamem, ho, ?_⟩⟩
              simpa only [hlevel] using hlen
            exact ha.trans (soundStep_putPhase next _ ha.2.2 hp')

private lemma soundStep_flushBuffer (s : FighterState) (j : ℕ) (hs : ActiveSound P d s) :
    SoundStep P d s ((fighterFlushBuffer d j s).getD s) := by
  cases hphase : s.activeAt d j with
  | none => simpa [fighterFlushBuffer, hphase] using SoundStep.refl hs
  | some phase =>
    have hp := phaseSound_of_activeAt hs hphase
    simp only [fighterFlushBuffer, hphase, bind, Option.bind_some]
    split
    · exact soundStep_putPhase s _ hs hp
    · exact .refl hs

private lemma soundStep_strategyMove (s : FighterState) (j : ℕ) (hs : ActiveSound P d s) :
    SoundStep P d s ((fighterStrategyMove P d j s).getD s) := by
  cases hphase : s.activeAt d j with
  | none => simpa [fighterStrategyMove, hphase] using SoundStep.refl hs
  | some phase =>
    simp only [fighterStrategyMove, hphase, bind, Option.bind_some]
    split
    · cases hm : (phase.game d).strategy (phase.official d) with
      | none => exact .refl hs
      | some move =>
        simp only [Option.bind_some]
        split
        · let next := (phase.game d).coordinates.zipIdx.foldl (fun s qi ↦
            fighterFuelUnits P d j qi.1 (move[qi.2]?.getD 0) s) s
          have hn : SoundStep P d s next :=
            soundStep_foldl (fun (qi : Coordinate × ℕ) t ↦
              fighterFuelUnits P d j qi.1 (move[qi.2]?.getD 0) t)
              (fun qi t ht ↦ soundStep_fuelUnits t j qi.1 _ ht) _ s hs
          change SoundStep P d s ((match next.activeAt d j with
            | none => some next
            | some live => some (next.putPhase d { live with
                officialCode := ((phase.game d).afterMove (phase.official d) move).encode })).getD
                  s)
          cases hlive : next.activeAt d j with
          | none => exact hn
          | some live =>
            have hl := phaseSound_of_activeAt hn.2.2 hlive
            exact hn.trans (soundStep_putPhase next _ hn.2.2 hl)
        · exact .refl hs
    · exact .refl hs

private lemma soundStep_levelAction (s : FighterState) (j : ℕ) (hs : ActiveSound P d s) :
    SoundStep P d s ((fighterLevelAction P d j s).getD s) := by
  cases hphase : s.activeAt d j with
  | none => simpa [fighterLevelAction, hphase] using SoundStep.refl hs
  | some phase =>
    simp only [fighterLevelAction, hphase, bind, Option.bind_some]
    split
    · exact soundStep_dummy s j hs
    · split
      · exact soundStep_payoff s j _ hs
      · cases hf : fighterFlushBuffer d j s with
        | none => exact soundStep_strategyMove s j hs
        | some next => simpa only [hf, Option.getD_some] using soundStep_flushBuffer s j hs

private lemma soundStep_closure (fuel : ℕ) (s : FighterState) (j : ℕ) (hs : ActiveSound P d s) :
    SoundStep P d s (fighterClosure P d j fuel s) := by
  induction fuel generalizing s with
  | zero => exact .refl hs
  | succ fuel ih =>
    simp only [fighterClosure]
    cases ha : fighterLevelAction P d j s with
    | none => exact .refl hs
    | some next =>
      have hn := soundStep_levelAction s j hs
      simp only [ha, Option.getD_some] at hn
      exact hn.trans (ih next hn.2.2)

private lemma soundStep_startPhase (s : FighterState) (j : ℕ) (candidate : Candidate)
    (ht : candidate.2 = s.tick) (hs : ActiveSound P d s) :
    SoundStep P d s (fighterStartPhase P d j candidate s) := by
  let waiting := fighterAbortAbove d j (fighterCancel d j .replaced j s)
  have hw : SoundStep P d s waiting :=
    (soundStep_cancel s j .replaced j hs).trans
      (soundStep_abortAbove _ j (soundStep_cancel s j .replaced j hs).2.2)
  have hp : PhaseSound P d waiting.allocated (fighter_construction P d j candidate waiting) := by
    constructor
    · exact fighter_construction_dummy_fresh P d j candidate waiting (ht.trans hw.1.symm)
    · simp [fighter_construction, FighterPhase.fundRequests]
  exact hw.trans (soundStep_putPhase waiting _ hw.2.2 hp)

private lemma soundStep_processLevel (s : FighterState) (j : ℕ) (ev : Option TimedEvent)
    (he : ∀ e, ev = some e → e.1 = s.tick) (hs : ActiveSound P d s) :
    SoundStep P d s (fighterProcessLevel P d j ev s) := by
  unfold fighterProcessLevel fighterCloseLevel
  have hc := soundStep_fulfillReady s j hs
  apply hc.trans
  cases ev with
  | none => exact soundStep_closure _ _ j hc.2.2
  | some e =>
    dsimp only
    split
    · have hn := soundStep_startPhase _ j (e.2.2.1, e.1) ((he e rfl).trans hc.1.symm) hc.2.2
      exact hn.trans (soundStep_closure _ _ j hn.2.2)
    · have hn := soundStep_opponent _ j e.2.2 hc.2.2
      exact hn.trans (soundStep_closure _ _ j hn.2.2)

end Invariant

/-- In every reachable state, each active phase has a dummy outside the saved output table of
its candidate and outside the query tree of its level, and an issued dummy has an allocation
with matching output and exact-length input in the permanent allocation list. -/
lemma active_phase_dummy_fresh_and_recorded (P : FighterParams) (d tick : ℕ) :
    ∀ p ∈ (fighterState P d tick).active,
      (∀ z, p.dummy = some z →
        z ∉ fighterStageOutputs P d (levelInput d p.level) p.candidate.2 p.initialAllocations ∧
        ∀ q ∈ (P.family.tree d p.level (levelInput d p.level)).queries, q.1 ≠ z) ∧
      (p.dummyIssued = true → ∃ z a, p.dummy = some z ∧
        a ∈ (fighterState P d tick).allocated ∧ a.output = z ∧
        a.input.length + 1 = levelInput d p.level) := by
  change ActiveSound P d (fighterState P d tick)
  induction tick with
  | zero => simp [ActiveSound, fighterState, initialFighterState]
  | succ tick ih =>
    have hevent : ∀ e, eventAt P.B (tick + 1) = some e → e.1 = tick + 1 := by
      intro e he
      rw [eventAt, Option.filter_eq_some_iff] at he
      exact of_decide_eq_true he.2
    have services (ls : List ℕ) (s : FighterState)
        (ht : s.tick = tick + 1) (hs : ActiveSound P d s) :
        SoundStep P d s
          (ls.foldl (fun s j ↦ fighterProcessLevel P d j (eventAt P.B (tick + 1)) s) s) := by
      induction ls generalizing s with
      | nil => exact .refl hs
      | cons j ls ih =>
        have hn := soundStep_processLevel s j (eventAt P.B (tick + 1))
          (fun e he ↦ (hevent e he).trans ht.symm) hs
        exact hn.trans (ih _ (hn.1.trans ht) hn.2.2)
    change ActiveSound P d (fighter_actions P d (tick + 1) (fighterState P d tick))
    unfold fighter_actions
    split
    · simp [ActiveSound, initialFighterState]
    · let current := { fighterState P d tick with
          tick := tick + 1, schedule := masterState P.B (tick + 1) }
      exact (services _ current rfl ih).2.2

end Kolmogorov.Milovanov
