/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Construction.Diagonal.AllocationGraph
import KolmogorovMathlib.RandomStrings.Plain.Construction.Diagonal.FundedFrames
import KolmogorovMathlib.RandomStrings.Plain.Construction.Diagonal.LiveCounters
import KolmogorovMathlib.RandomStrings.Plain.Construction.Diagonal.SimulationEvents

/-!
# Provenance of the allocated directives

Every directive in the permanent allocation graph of the fighter simulation was issued by some
phase.  This module proves two facts about where a directive comes from, valid at every tick
(`fighterState_allocated_provenance`):

* an allocated directive has its target equal to the length of its input plus one, and a dummy
  directive outputs a string that is not queried anywhere in the query tree of its level;
* relative to an active phase, every allocation of a level at most the phase's level is either
  saved in the phase's initial allocations, or is an allocation of the same level and candidate
  as the phase.  Allocations of lower levels are always saved, because a new one would abort
  the phase.

Both are proved by induction over the ticks with a single invariant, which every primitive
action of the simulation (cancellation, allocation, payoff, fuel, dummy, opponent move, phase
start, strategy move and closure of a level) preserves.

The facts are used in `Diagonal.OracleAgreement` to identify an allocated directive with a
payoff of the true-marker phase.
-/

namespace Kolmogorov.Milovanov

/-- The string `out` is not a query of the query tree of level `l`. -/
private abbrev OutputFresh (P : FighterParams) (d l : ℕ) (out : BitString) : Prop :=
  ∀ q ∈ (P.family.tree d l (levelInput d l)).queries, q.1 ≠ out

/-- An allocated directive has the target dictated by its input, and a dummy directive outputs
a string fresh for its level. -/
private abbrev DirectiveSound (P : FighterParams) (d : ℕ) (a : AllocatedDirective) : Prop :=
  a.target = a.input.length + 1 ∧ (a.kind = .dummy → OutputFresh P d a.level a.output)

/-- Every allocation of level at most the level of `p` is saved by `p` or belongs to `p`. -/
private abbrev AllocationsSaved (allocated : List AllocatedDirective) (p : FighterPhase) :
    Prop :=
  ∀ a ∈ allocated, a.level ≤ p.level →
    a ∈ p.initialAllocations ∨ (a.level = p.level ∧ a.candidate = p.candidate)

/-- The provenance invariant of a single phase. -/
private abbrev PhaseProvenance (P : FighterParams) (d : ℕ) (allocated : List AllocatedDirective)
    (p : FighterPhase) : Prop :=
  AllocationsSaved allocated p ∧ ∀ out, p.dummy = some out → OutputFresh P d p.level out

/-- The provenance invariant of a simulation state. -/
private abbrev ProvenanceInv (P : FighterParams) (d : ℕ) (s : FighterState) : Prop :=
  (s.active.map FighterPhase.level).Nodup ∧ (∀ a ∈ s.allocated, DirectiveSound P d a) ∧
    ∀ p ∈ s.active, PhaseProvenance P d s.allocated p

section

variable {P : FighterParams} {d : ℕ}

private lemma ProvenanceInv.phase {s : FighterState} {l : ℕ} {p : FighterPhase}
    (hs : ProvenanceInv P d s) (hp : s.activeAt d l = some p) :
    PhaseProvenance P d s.allocated p :=
  hs.2.2 p (List.mem_of_find?_eq_some hp)

private lemma nodup_levels_filter (ps : List FighterPhase) (test : FighterPhase → Bool)
    (hu : (ps.map FighterPhase.level).Nodup) :
    ((ps.filter test).map FighterPhase.level).Nodup :=
  (List.filter_sublist.map FighterPhase.level).nodup hu

private lemma ProvenanceInv.of_eq {s t : FighterState} (hs : ProvenanceInv P d s)
    (ha : t.allocated = s.allocated) (hp : t.active = s.active) : ProvenanceInv P d t := by
  simpa only [ProvenanceInv, ha, hp] using hs

private lemma ProvenanceInv.putPhase {s : FighterState} {p : FighterPhase}
    (hs : ProvenanceInv P d s) (hp : PhaseProvenance P d s.allocated p) :
    ProvenanceInv P d (s.putPhase d p) := by
  refine ⟨?_, hs.2.1, ?_⟩
  · simp only [FighterState.putPhase, List.map_cons, List.nodup_cons]
    refine ⟨?_, nodup_levels_filter _ _ hs.1⟩
    intro hm
    obtain ⟨old, hold, heq⟩ := List.mem_map.mp hm
    have hne := (List.mem_filter.mp hold).2
    simp only [bne_iff_ne] at hne
    exact hne heq
  · intro next hn
    rcases List.mem_cons.mp hn with rfl | hn
    · exact hp
    · exact hs.2.2 next (List.mem_filter.mp hn).1

private lemma ProvenanceInv.cancel (l cause : ℕ) (reason : PhaseEnd) {s : FighterState}
    (hs : ProvenanceInv P d s) : ProvenanceInv P d (fighterCancel d l reason cause s) := by
  unfold fighterCancel
  split
  · exact hs
  · exact ⟨nodup_levels_filter _ _ hs.1, hs.2.1,
      fun p hp ↦ hs.2.2 p (List.mem_filter.mp hp).1⟩

private lemma ProvenanceInv.abortAbove (l : ℕ) {s : FighterState} (hs : ProvenanceInv P d s) :
    ProvenanceInv P d (fighterAbortAbove d l s) := by
  unfold fighterAbortAbove
  refine List.foldlRecOn (motive := ProvenanceInv P d) _ _ hs fun t ht p _ ↦ ?_
  split
  · exact ht.cancel _ _ _
  · exact ht

/-- A successful allocation of a directive keeps the provenance invariant: the new directive
is sound, and it belongs to the phase of its own level. -/
private lemma ProvenanceInv.allocate (l : ℕ) (kind : DirectiveKind) (target : ℕ) (out : BitString)
    {s : FighterState} (hs : ProvenanceInv P d s) (hfresh : kind = .dummy → OutputFresh P d l out) :
    ProvenanceInv P d (fighterAllocate d l kind target out s).1 := by
  unfold fighterAllocate
  split
  · exact hs
  · rename_i phase hphase
    by_cases ht : target = 0
    · simp only [ht, ite_true]
      exact ProvenanceInv.cancel l l .saturated (hs.of_eq rfl rfl)
    · simp only [ht, ite_false]
      cases hf : (fighterInputs d (target - 1)).find? (fun p ↦
          !s.allocated.any (fun a ↦ a.input == p)) with
      | none => exact ProvenanceInv.cancel l l .saturated (hs.of_eq rfl rfl)
      | some input =>
        let entry : AllocatedDirective := ⟨l, phase.candidate, s.tick, kind, target, input, out⟩
        let extended := { s with allocated := s.allocated ++ [entry] }
        obtain ⟨hgraph, hsub, hbound⟩ := fighterAbortAbove_allocated_eq_active_sublist d l extended
        change ProvenanceInv P d (fighterAbortAbove d l extended)
        refine ⟨(hsub.map FighterPhase.level).nodup hs.1, ?_, ?_⟩
        · intro a ha
          rw [hgraph] at ha
          rcases List.mem_append.mp ha with ha | ha
          · exact hs.2.1 a ha
          · obtain rfl := List.mem_singleton.mp ha
            have hlen := length_eq_of_mem_fighterInputs d (target - 1) input
              (List.mem_of_find?_eq_some hf)
            exact ⟨by dsimp [entry]; omega, hfresh⟩
        · intro p hp
          have hpm : p ∈ s.active := hsub.subset hp
          refine ⟨?_, (hs.2.2 p hpm).2⟩
          intro a ha hle
          rw [hgraph] at ha
          rcases List.mem_append.mp ha with ha | ha
          · exact (hs.2.2 p hpm).1 a ha hle
          · obtain rfl := List.mem_singleton.mp ha
            have hlevel : p.level = l := by
              have hb := hbound p hp
              change l ≤ p.level at hle
              omega
            have hphaselevel : phase.level = l :=
              FighterState.level_eq_of_activeAt_eq_some (p := phase) hphase
            have heq : p = phase := List.inj_on_of_nodup_map hs.1 hpm
              (List.mem_of_find?_eq_some hphase) (hlevel.trans hphaselevel.symm)
            exact Or.inr ⟨hlevel.symm, by dsimp [entry]; rw [heq]⟩

private lemma ProvenanceInv.recordFulfilled (q : Coordinate) {s : FighterState}
    (hs : ProvenanceInv P d s) :
    ProvenanceInv P d { s with
      fulfilled := s.fulfilled ++ [q]
      active := s.active.map (fun p ↦ { p with pending := p.pending.filter (· != q) }) } := by
  refine ⟨?_, hs.2.1, ?_⟩
  · simpa only [List.map_map, Function.comp_def] using hs.1
  · intro p hp
    obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hp
    exact hs.2.2 old hold

private lemma ProvenanceInv.payoff (l : ℕ) (q : Coordinate) {s : FighterState}
    (hs : ProvenanceInv P d s) : ProvenanceInv P d (fighterPayoff P d l q s) := by
  unfold fighterPayoff
  split
  · exact hs
  · split
    · have ha := hs.allocate l .payoff q.2 q.1 (by intro h; cases h)
      cases he : fighterAllocate d l .payoff q.2 q.1 s with
      | mk next success =>
        simp only [he] at ha ⊢
        cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
        · exact ha
        · exact ha.recordFulfilled q
    · exact hs

private lemma ProvenanceInv.fulfillReady (l : ℕ) {s : FighterState} (hs : ProvenanceInv P d s) :
    ProvenanceInv P d (fighterFulfillReady P d l s) := by
  unfold fighterFulfillReady
  split
  · exact hs
  · exact List.foldlRecOn (motive := ProvenanceInv P d) _ _ hs fun t ht _ _ ↦ ht.payoff l _

/-- One unit of fuel spent on a coordinate keeps the provenance invariant. -/
private lemma ProvenanceInv.fuelUnit (l : ℕ) (q : Coordinate) {s : FighterState}
    (hs : ProvenanceInv P d s) : ProvenanceInv P d (fighterFuelUnit P d l q s) := by
  unfold fighterFuelUnit
  split
  · exact hs
  · rename_i phase hphase
    have hp := hs.phase hphase
    have hl := FighterState.level_eq_of_activeAt_eq_some (p := phase) hphase
    split
    · let charged := { phase with controlledRemaining := phase.controlledRemaining - 1 }
      let index := fighterFreshString d (phase.indices[(phase.game d).coordinates.idxOf q]?.getD [])
      let out := pairCode (triple q.1 (q.2 - d) phase.candidate.1) index
      have ha := (hs.putPhase (p := charged) hp).allocate l .fuel (levelUpper l + d) out
        (by intro h; cases h)
      change ProvenanceInv P d
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
        · have hstay : next.activeAt d l = some charged := by
            have h := FighterState.activeAt_fighterAllocate_of_success d l .fuel
              (levelUpper l + d) out (s.putPhase d charged) (by rw [he])
            rw [he] at h
            exact h.trans (by simp [FighterState.putPhase, FighterState.activeAt, charged, hl])
          have hpn := ha.phase hstay
          exact ProvenanceInv.fulfillReady l (ha.putPhase hpn)
    · exact hs

private lemma ProvenanceInv.fuelUnits (l : ℕ) (q : Coordinate) (count : ℕ) {s : FighterState}
    (hs : ProvenanceInv P d s) : ProvenanceInv P d (fighterFuelUnits P d l q count s) := by
  induction count generalizing s with
  | zero => exact hs
  | succ count ih => exact ih (hs.fuelUnit l q)

private lemma ProvenanceInv.dummy (l : ℕ) {s : FighterState} (hs : ProvenanceInv P d s) :
    ProvenanceInv P d (fighterDummy d l s) := by
  unfold fighterDummy
  split
  · exact hs
  · rename_i phase hphase
    have hp := hs.phase hphase
    have hl := FighterState.level_eq_of_activeAt_eq_some (p := phase) hphase
    split
    · exact hs
    · rename_i out hout
      split
      · exact hs
      · have hfresh : OutputFresh P d l out := by
          simpa only [hl] using hp.2 out hout
        have ha := hs.allocate l .dummy (levelInput d l) out (fun _ ↦ hfresh)
        cases he : fighterAllocate d l .dummy (levelInput d l) out s with
        | mk next success =>
          simp only [he] at ha ⊢
          cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
          · exact ha
          · have hstay : next.activeAt d l = some phase := by
              have h := FighterState.activeAt_fighterAllocate_of_success d l .dummy
                (levelInput d l) out s (by rw [he])
              rw [he] at h
              exact h.trans hphase
            have hpn := ha.phase hstay
            exact ha.putPhase hpn

private lemma ProvenanceInv.opponent (l : ℕ) (e : ProgramEvent) {s : FighterState}
    (hs : ProvenanceInv P d s) : ProvenanceInv P d (fighterOpponent P d l e s) := by
  unfold fighterOpponent
  split
  · exact hs
  · rename_i phase hphase
    have hp := hs.phase hphase
    split
    · exact hs
    · split
      · exact hs
      · split
        · exact hs.cancel _ _ _
        · exact ProvenanceInv.fulfillReady l (hs.putPhase hp)

private lemma ProvenanceInv.startPhase (l : ℕ) (candidate : Candidate) {s : FighterState}
    (hs : ProvenanceInv P d s) : ProvenanceInv P d (fighterStartPhase P d l candidate s) := by
  unfold fighterStartPhase
  let waiting := fighterAbortAbove d l (fighterCancel d l .replaced l s)
  have hw : ProvenanceInv P d waiting := (hs.cancel l l .replaced).abortAbove l
  have hp : PhaseProvenance P d waiting.allocated
      (fighter_construction P d l candidate waiting) := by
    refine ⟨fun a ha _ ↦ Or.inl ha, ?_⟩
    intro out hout
    dsimp only [fighter_construction, FighterPhase.fundRequests] at hout
    split at hout
    · obtain rfl := Option.some.inj hout
      intro q hq heq
      apply fighterFreshString_notMem
        d ((P.family.tree d l (levelInput d l)).queries.map Prod.fst ++
          fighterStageOutputList P d (levelInput d l) waiting.tick waiting.allocated)
      apply List.mem_append_left
      rw [← heq]
      exact List.mem_map.mpr ⟨q, hq, rfl⟩
    · contradiction
  exact (hw.putPhase hp).of_eq rfl rfl

private lemma ProvenanceInv.flushBuffer (l : ℕ) {s : FighterState} (hs : ProvenanceInv P d s) :
    ProvenanceInv P d ((fighterFlushBuffer d l s).getD s) := by
  unfold fighterFlushBuffer
  cases hp : s.activeAt d l with
  | none => exact hs
  | some phase =>
    simp only [bind, Option.bind_some]
    split
    · have hphase := hs.phase hp
      exact hs.putPhase hphase
    · exact hs

private lemma ProvenanceInv.strategyMove (l : ℕ) {s : FighterState} (hs : ProvenanceInv P d s) :
    ProvenanceInv P d ((fighterStrategyMove P d l s).getD s) := by
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
          have hn : ProvenanceInv P d next :=
            List.foldlRecOn (motive := ProvenanceInv P d) _ _ hs fun t ht qi _ ↦
              ht.fuelUnits l qi.1 (move[qi.2]?.getD 0)
          change ProvenanceInv P d ((match next.activeAt d l with
            | none => some next
            | some live => some (next.putPhase d
              { live with officialCode :=
                ((phase.game d).afterMove (phase.official d) move).encode })).getD s)
          split
          · exact hn
          · rename_i live hlive
            have hphase := hn.phase hlive
            exact hn.putPhase hphase
        · exact hs
    · exact hs

private lemma ProvenanceInv.levelAction (l : ℕ) {s : FighterState} (hs : ProvenanceInv P d s) :
    ProvenanceInv P d ((fighterLevelAction P d l s).getD s) := by
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
        | some next =>
          simpa only [hf, Option.getD_some] using hs.flushBuffer l

private lemma ProvenanceInv.closure (l fuel : ℕ) {s : FighterState} (hs : ProvenanceInv P d s) :
    ProvenanceInv P d (fighterClosure P d l fuel s) := by
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

private lemma ProvenanceInv.processLevel (l : ℕ) (e : Option TimedEvent) {s : FighterState}
    (hs : ProvenanceInv P d s) : ProvenanceInv P d (fighterProcessLevel P d l e s) := by
  unfold fighterProcessLevel fighterCloseLevel
  apply ProvenanceInv.closure
  cases e with
  | none => exact hs.fulfillReady l
  | some e =>
    dsimp only
    split
    · exact (hs.fulfillReady l).startPhase l _
    · exact (hs.fulfillReady l).opponent l _

private lemma provenanceInv_fighterState (P : FighterParams) (d tick : ℕ) :
    ProvenanceInv P d (fighterState P d tick) := by
  induction tick with
  | zero => simp [ProvenanceInv, fighterState, initialFighterState]
  | succ tick ih =>
    change ProvenanceInv P d (fighter_actions P d (tick + 1) (fighterState P d tick))
    unfold fighter_actions
    split
    · simp [ProvenanceInv, initialFighterState]
    · exact List.foldlRecOn (motive := ProvenanceInv P d) _ _ (ih.of_eq rfl rfl)
        fun t ht l _ ↦ ht.processLevel l _

end

/-- Allocation provenance at every tick.  Every allocated directive has target one more than the
length of its input, and a dummy directive outputs a string that is no query of its level's
tree.  Relative to an active phase, the allocations of a level at most the phase's level are
saved in the phase's initial allocations, or have the level and candidate of the phase. -/
theorem fighterState_allocated_provenance (P : FighterParams) (d tick : ℕ) :
    (∀ a ∈ (fighterState P d tick).allocated,
      a.target = a.input.length + 1 ∧
        (a.kind = .dummy →
          ∀ q ∈ (P.family.tree d a.level (levelInput d a.level)).queries,
            q.1 ≠ a.output)) ∧
    ∀ p ∈ (fighterState P d tick).active,
      ∀ a ∈ (fighterState P d tick).allocated, a.level ≤ p.level →
        a ∈ p.initialAllocations ∨
          (a.level = p.level ∧ a.candidate = p.candidate) :=
  have hinv := provenanceInv_fighterState P d tick
  ⟨hinv.2.1, fun p hp ↦ (hinv.2.2 p hp).1⟩

end Kolmogorov.Milovanov
