/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.FundedRequestReceipts
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.FundedRequestTrace
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.SettledLowerLevels

/-!
# Candidate provenance and allocation snapshots

For blueprint node `constr:separation`, this module relates permanent allocations to the
candidates that created them. Every allocated candidate is valid and occurs no later than the
true marker. An active phase's initial table contains all same-level allocations from earlier
candidates, even if the allocation is observed at a later tick.

Candidate-history invariants prevent new allocations for superseded candidates; snapshot
invariants record older allocations when a phase starts. `PhaseSeparationClasses` uses these
facts to classify same-level allocations outside a true-marker phase's initial table.
-/

namespace Kolmogorov.Milovanov

/-- All live candidates satisfy `valid`; every allocation either belongs to `past` or
has a candidate satisfying `valid`. -/
private abbrev CandidateHistory (valid : ℕ → Candidate → Prop)
    (past : List AllocatedDirective) (s : FighterState) : Prop :=
  (∀ p ∈ s.active, valid p.level p.candidate) ∧
    ∀ a ∈ s.allocated, a ∈ past ∨ valid a.level a.candidate

namespace CandidateHistory

variable {P : FighterParams} {d : ℕ} {valid : ℕ → Candidate → Prop}
  {past : List AllocatedDirective}

private lemma of_activeAt {s : FighterState} {l : ℕ} {p : FighterPhase}
    (hs : CandidateHistory valid past s) (hp : s.activeAt d l = some p) :
    valid p.level p.candidate :=
  hs.1 p (List.mem_of_find?_eq_some hp)

private lemma putPhase
    (s : FighterState) (p : FighterPhase) (hs : CandidateHistory valid past s)
    (hp : valid p.level p.candidate) : CandidateHistory valid past (s.putPhase d p) := by
  refine ⟨?_, hs.2⟩
  intro next hn
  rcases List.mem_cons.mp hn with rfl | hn
  · exact hp
  · exact hs.1 next (List.mem_filter.mp hn).1

private lemma cancel (l cause : ℕ) (reason : PhaseEnd)
    (s : FighterState) (hs : CandidateHistory valid past s) :
    CandidateHistory valid past (fighterCancel d l reason cause s) := by
  unfold fighterCancel
  split
  · exact hs
  · exact ⟨fun p hp ↦ hs.1 p (List.mem_filter.mp hp).1, hs.2⟩

private lemma abortAbove (l : ℕ) (s : FighterState) (hs : CandidateHistory valid past s) :
    CandidateHistory valid past (fighterAbortAbove d l s) := by
  unfold fighterAbortAbove
  apply List.foldlRecOn _ _ hs
  intro t ht p _
  split
  · exact cancel (d := d) _ _ _ _ ht
  · exact ht

private lemma allocate (l : ℕ) (kind : DirectiveKind) (target : ℕ) (out : BitString)
    (s : FighterState) (hs : CandidateHistory valid past s) :
    CandidateHistory valid past (fighterAllocate d l kind target out s).1 := by
  unfold fighterAllocate
  split
  · exact hs
  · rename_i phase hp
    have hvalid := of_activeAt (d := d) hs hp
    have hlevel : phase.level = l := beq_iff_eq.mp
      (List.find?_some (p := fun p : FighterPhase ↦ p.level == l) hp)
    cases hf : (if target = 0 then (none : Option BitString) else
        (fighterInputs d (target - 1)).find? (fun p ↦
          !s.allocated.any (fun a ↦ a.input == p))) with
    | none => exact cancel (d := d) _ _ _ _ hs
    | some p =>
      apply abortAbove (d := d)
      refine ⟨hs.1, ?_⟩
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact hs.2 a ha
      · obtain rfl := List.mem_singleton.mp ha
        exact Or.inr (by simpa only [hlevel] using hvalid)

private lemma payoff (l : ℕ) (q : Coordinate)
    (s : FighterState) (hs : CandidateHistory valid past s) :
    CandidateHistory valid past (fighterPayoff P d l q s) := by
  unfold fighterPayoff
  split
  · exact hs
  · split
    · have ha := allocate (d := d) l .payoff q.2 q.1 s hs
      cases he : fighterAllocate d l .payoff q.2 q.1 s with
      | mk next success =>
        simp only [he] at ha ⊢
        cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
        · exact ha
        · refine ⟨?_, ha.2⟩
          intro p hp
          obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hp
          exact ha.1 old hold
    · exact hs

private lemma fulfillReady (l : ℕ) (s : FighterState) (hs : CandidateHistory valid past s) :
    CandidateHistory valid past (fighterFulfillReady P d l s) := by
  unfold fighterFulfillReady
  split
  · exact hs
  · exact List.foldlRecOn _ _ hs (fun t ht q _ ↦ payoff (P := P) (d := d) l q t ht)

private lemma fuelUnit (l : ℕ) (q : Coordinate)
    (s : FighterState) (hs : CandidateHistory valid past s) :
    CandidateHistory valid past (fighterFuelUnit P d l q s) := by
  unfold fighterFuelUnit
  split
  · exact hs
  · rename_i phase hp
    have hq := of_activeAt (d := d) hs hp
    split
    · let charged := { phase with controlledRemaining := phase.controlledRemaining - 1 }
      let index := fighterFreshString d
        (phase.indices[(phase.game d).coordinates.idxOf q]?.getD [])
      let out := pairCode (triple q.1 (q.2 - d) phase.candidate.1) index
      have ha := allocate (d := d) l .fuel (levelUpper l + d) out (s.putPhase d charged)
        (putPhase (d := d) s charged hs hq)
      change CandidateHistory valid past
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
        · exact fulfillReady (P := P) (d := d) l _ (putPhase (d := d) next _ ha hq)
    · exact hs

private lemma fuelUnits (l : ℕ) (q : Coordinate) (count : ℕ)
    (s : FighterState) (hs : CandidateHistory valid past s) :
    CandidateHistory valid past (fighterFuelUnits P d l q count s) := by
  induction count generalizing s with
  | zero => exact hs
  | succ count ih => exact ih _ (fuelUnit (P := P) (d := d) l q s hs)

private lemma dummy (l : ℕ) (s : FighterState) (hs : CandidateHistory valid past s) :
    CandidateHistory valid past (fighterDummy d l s) := by
  unfold fighterDummy
  split
  · exact hs
  · rename_i phase hp
    have hq := of_activeAt (d := d) hs hp
    split
    · exact hs
    · rename_i output hout
      split
      · exact hs
      · have ha := allocate (d := d) l .dummy (levelInput d l) output s hs
        cases he : fighterAllocate d l .dummy (levelInput d l) output s with
        | mk next success =>
          simp only [he] at ha ⊢
          cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
          · exact ha
          · exact putPhase (d := d) next _ ha hq

private lemma opponent (l : ℕ) (e : ProgramEvent)
    (s : FighterState) (hs : CandidateHistory valid past s) :
    CandidateHistory valid past (fighterOpponent P d l e s) := by
  unfold fighterOpponent
  split
  · exact hs
  · rename_i phase hp
    have hq := of_activeAt (d := d) hs hp
    split
    · exact hs
    · split
      · exact hs
      · split
        · exact cancel (d := d) _ _ _ _ hs
        · exact fulfillReady (P := P) (d := d) l _ (putPhase (d := d) s _ hs hq)

private lemma startPhase (l : ℕ) (c : Candidate)
    (s : FighterState) (hs : CandidateHistory valid past s)
    (hc : valid l c) : CandidateHistory valid past (fighterStartPhase P d l c s) := by
  unfold fighterStartPhase
  exact putPhase (d := d) _ _ (abortAbove (d := d) l _ (cancel (d := d) _ _ _ s hs)) hc

private lemma flushBuffer (l : ℕ) (s : FighterState) (hs : CandidateHistory valid past s) :
    CandidateHistory valid past ((fighterFlushBuffer d l s).getD s) := by
  unfold fighterFlushBuffer
  cases hp : s.activeAt d l with
  | none => exact hs
  | some phase =>
    have hq := of_activeAt (d := d) hs hp
    simp only [bind, Option.bind_some]
    split
    · exact putPhase (d := d) s _ hs hq
    · exact hs

private lemma strategyMove (l : ℕ) (s : FighterState) (hs : CandidateHistory valid past s) :
    CandidateHistory valid past ((fighterStrategyMove P d l s).getD s) := by
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
          have hn : CandidateHistory valid past next := by
            apply List.foldlRecOn _ _ hs
            intro t ht qi _
            exact fuelUnits (P := P) (d := d) l qi.1 (move[qi.2]?.getD 0) t ht
          change CandidateHistory valid past ((match next.activeAt d l with
            | none => some next
            | some live => some (next.putPhase d
              { live with officialCode :=
                  ((phase.game d).afterMove (phase.official d) move).encode })).getD s)
          split
          · exact hn
          · rename_i live hlive
            have hq := of_activeAt (d := d) (p := live) hn hlive
            exact putPhase (d := d) next _ hn hq
        · exact hs
    · exact hs

private lemma levelAction (l : ℕ) (s : FighterState) (hs : CandidateHistory valid past s) :
    CandidateHistory valid past ((fighterLevelAction P d l s).getD s) := by
  unfold fighterLevelAction
  cases hp : s.activeAt d l with
  | none => exact hs
  | some phase =>
    simp only [bind, Option.bind_some]
    split
    · exact dummy (d := d) l s hs
    · split
      · exact payoff (P := P) (d := d) l _ s hs
      · cases hf : fighterFlushBuffer d l s with
        | none => exact strategyMove (P := P) (d := d) l s hs
        | some next =>
          have h := flushBuffer (d := d) l s hs
          simpa only [hf, Option.getD_some] using h

private lemma closure (l fuel : ℕ) (s : FighterState) (hs : CandidateHistory valid past s) :
    CandidateHistory valid past (fighterClosure P d l fuel s) := by
  induction fuel generalizing s with
  | zero => exact hs
  | succ fuel ih =>
    simp only [fighterClosure]
    cases ha : fighterLevelAction P d l s with
    | none => exact hs
    | some next =>
      have hn := levelAction (P := P) (d := d) l s hs
      simp only [ha, Option.getD_some] at hn
      exact ih next hn

private lemma processLevel (l : ℕ) (e : Option TimedEvent)
    (hevent : ∀ ev, e = some ev →
      ev.2.2.1.length ≤ levelScale l →
      valid l (ev.2.2.1, ev.1))
    (s : FighterState) (hs : CandidateHistory valid past s) :
    CandidateHistory valid past (fighterProcessLevel P d l e s) := by
  unfold fighterProcessLevel fighterCloseLevel
  apply closure (P := P) (d := d)
  cases e with
  | none => exact fulfillReady (P := P) (d := d) l s hs
  | some e =>
    dsimp only
    split
    · rename_i hguard
      apply startPhase (P := P) (d := d) l _ _ (fulfillReady (P := P) (d := d) l s hs)
      exact hevent e rfl hguard.2.1
    · exact opponent (P := P) (d := d) l _ _ (fulfillReady (P := P) (d := d) l s hs)

end CandidateHistory

/-- Every permanent allocation originates from a candidate satisfying its level's length
bound in the canonical enumeration. -/
lemma validCandidate_of_mem_allocated
    (P : FighterParams) (d tick : ℕ) (a : AllocatedDirective)
    (ha : a ∈ (fighterState P d tick).allocated) :
    validCandidate P.B (levelScale a.level) a.candidate = true := by
  let valid := fun l c ↦ validCandidate P.B (levelScale l) c = true
  have hall : ∀ t, CandidateHistory valid [] (fighterState P d t) := by
    intro t
    induction t with
    | zero => simp [CandidateHistory, fighterState, initialFighterState]
    | succ t ih =>
      change CandidateHistory valid [] (fighter_actions P d (t + 1) (fighterState P d t))
      unfold fighter_actions
      split
      · simp [CandidateHistory, initialFighterState]
      · let current := { fighterState P d t with
          tick := t + 1, schedule := masterState P.B (t + 1) }
        have hc : CandidateHistory valid [] current := ih
        apply List.foldlRecOn _ _ hc
        intro s hs l _
        apply CandidateHistory.processLevel l _ ?_ s hs
        intro e he hvalid
        apply (canonical_enumeration_spec_candidate P.B (levelScale l) _).mpr
        have ht := (canonical_enumeration_spec_sound P.B he).1
        refine ⟨hvalid, e.2.1, e.2.2.2, ?_⟩
        change eventAt P.B e.1 = some e
        rw [ht]
        exact he
  exact ((hall tick).2 a ha).resolve_left List.not_mem_nil

/-- Every valid candidate occurs no later than the marker; a candidate at the marker's
timestamp is the marker candidate itself. -/
lemma candidate_tick_le_markerTick
    (B : Base) (n : ℕ) (c : Candidate) (hc : validCandidate B n c = true) :
    c.2 ≤ markerTick B n ∧ (c.2 = markerTick B n → c = markerCandidate B n) := by
  obtain ⟨hlen, i, x, hevent⟩ := (canonical_enumeration_spec_candidate B n c).mp hc
  constructor
  · by_contra h
    have hlong := length_gt_of_eventAt_of_markerTick_lt B n
      c.2 (by omega) i c.1 x hevent
    omega
  · intro ht
    have hprogram : lastProgram B n = c.1 := by
      unfold lastProgram
      rw [← ht, hevent]
      rfl
    exact Prod.ext hprogram.symm ht

/-- A phase's snapshot contains all same-level allocations from older candidates. -/
private abbrev SavesOlderAllocations (allocated : List AllocatedDirective)
    (p : FighterPhase) : Prop :=
  ∀ a ∈ allocated, a.level = p.level → a.candidate.2 < p.candidate.2 →
    a ∈ p.initialAllocations

/-- Active levels are distinct and each active phase saves the allocations from older
candidates at its level. -/
private abbrev AllocationSnapshots (s : FighterState) : Prop :=
  (s.active.map FighterPhase.level).Nodup ∧
    ∀ p ∈ s.active, SavesOlderAllocations s.allocated p

namespace AllocationSnapshots

variable {P : FighterParams} {d : ℕ}

private lemma of_activeAt {s : FighterState} {l : ℕ} {p : FighterPhase}
    (hs : AllocationSnapshots s) (hp : s.activeAt d l = some p) :
    SavesOlderAllocations s.allocated p :=
  hs.2 p (List.mem_of_find?_eq_some hp)

private lemma putPhase (s : FighterState) (p : FighterPhase) (hs : AllocationSnapshots s)
    (hp : SavesOlderAllocations s.allocated p) : AllocationSnapshots (s.putPhase d p) := by
  refine ⟨?_, ?_⟩
  · simp only [FighterState.putPhase, List.map_cons, List.nodup_cons]
    refine ⟨?_, List.pairwise_map.mpr ((List.pairwise_map.mp hs.1).filter _)⟩
    intro hm
    obtain ⟨old, hold, heq⟩ := List.mem_map.mp hm
    have hne := (List.mem_filter.mp hold).2
    simp [heq] at hne
  · intro next hn
    rcases List.mem_cons.mp hn with rfl | hn
    · exact hp
    · exact hs.2 next (List.mem_filter.mp hn).1

private lemma cancel (l cause : ℕ) (reason : PhaseEnd)
    (s : FighterState) (hs : AllocationSnapshots s) :
    AllocationSnapshots (fighterCancel d l reason cause s) := by
  unfold fighterCancel
  split
  · exact hs
  · exact ⟨List.pairwise_map.mpr ((List.pairwise_map.mp hs.1).filter _),
      fun p hp ↦ hs.2 p (List.mem_filter.mp hp).1⟩

private lemma abortAbove (l : ℕ) (s : FighterState) (hs : AllocationSnapshots s) :
    AllocationSnapshots (fighterAbortAbove d l s) := by
  unfold fighterAbortAbove
  apply List.foldlRecOn _ _ hs
  intro t ht p _
  split
  · exact cancel (d := d) _ _ _ _ ht
  · exact ht

private lemma allocate (l : ℕ) (kind : DirectiveKind) (target : ℕ) (out : BitString)
    (s : FighterState) (hs : AllocationSnapshots s) :
    AllocationSnapshots (fighterAllocate d l kind target out s).1 := by
  unfold fighterAllocate
  split
  · exact hs
  · rename_i phase hp
    have hlevel : phase.level = l := beq_iff_eq.mp
      (List.find?_some (p := fun p : FighterPhase ↦ p.level == l) hp)
    cases hf : (if target = 0 then (none : Option BitString) else
        (fighterInputs d (target - 1)).find? (fun p ↦
          !s.allocated.any (fun a ↦ a.input == p))) with
    | none => exact cancel (d := d) _ _ _ _ hs
    | some input =>
      apply abortAbove (d := d)
      refine ⟨hs.1, ?_⟩
      intro p hp_mem a ha hsame holder
      rcases List.mem_append.mp ha with ha | ha
      · exact hs.2 p hp_mem a ha hsame holder
      · obtain rfl := List.mem_singleton.mp ha
        have heq : p = phase := List.inj_on_of_nodup_map hs.1 hp_mem
          (List.mem_of_find?_eq_some hp) (hsame.symm.trans hlevel.symm)
        subst p
        exact (Nat.lt_irrefl _ holder).elim

private lemma payoff (l : ℕ) (q : Coordinate) (s : FighterState) (hs : AllocationSnapshots s) :
    AllocationSnapshots (fighterPayoff P d l q s) := by
  unfold fighterPayoff
  split
  · exact hs
  · split
    · have ha := allocate (d := d) l .payoff q.2 q.1 s hs
      cases he : fighterAllocate d l .payoff q.2 q.1 s with
      | mk next success =>
        simp only [he] at ha ⊢
        cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
        · exact ha
        · refine ⟨?_, ?_⟩
          · simpa only [List.map_map, Function.comp_def] using ha.1
          · intro p hp
            obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hp
            exact ha.2 old hold
    · exact hs

private lemma fulfillReady (l : ℕ) (s : FighterState) (hs : AllocationSnapshots s) :
    AllocationSnapshots (fighterFulfillReady P d l s) := by
  unfold fighterFulfillReady
  split
  · exact hs
  · exact List.foldlRecOn _ _ hs (fun t ht q _ ↦ payoff (P := P) (d := d) l q t ht)

private lemma fuelUnit (l : ℕ) (q : Coordinate)
    (s : FighterState) (hs : AllocationSnapshots s) :
    AllocationSnapshots (fighterFuelUnit P d l q s) := by
  unfold fighterFuelUnit
  split
  · exact hs
  · rename_i phase hp
    have hq := of_activeAt (d := d) hs hp
    split
    · let charged := { phase with controlledRemaining := phase.controlledRemaining - 1 }
      let index := fighterFreshString d
        (phase.indices[(phase.game d).coordinates.idxOf q]?.getD [])
      let out := pairCode (triple q.1 (q.2 - d) phase.candidate.1) index
      have hlevel : phase.level = l := beq_iff_eq.mp
        (List.find?_some (p := fun p : FighterPhase ↦ p.level == l) hp)
      have hcharged : (s.putPhase d charged).activeAt d l = some charged := by
        simp [FighterState.putPhase, FighterState.activeAt, charged, hlevel]
      have ha := allocate (d := d) l .fuel (levelUpper l + d) out (s.putPhase d charged)
        (putPhase (d := d) s charged hs hq)
      change AllocationSnapshots
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
        · have hpnext := activeAt_fighterAllocate_eq_of_success
            d l (levelUpper l + d) .fuel out (s.putPhase d charged) next charged
            hcharged he
          exact fulfillReady (P := P) (d := d) l _
            (putPhase (d := d) next _ ha (of_activeAt (d := d) (p := charged) ha hpnext))
    · exact hs

private lemma fuelUnits (l : ℕ) (q : Coordinate) (count : ℕ)
    (s : FighterState) (hs : AllocationSnapshots s) :
    AllocationSnapshots (fighterFuelUnits P d l q count s) := by
  induction count generalizing s with
  | zero => exact hs
  | succ count ih => exact ih _ (fuelUnit (P := P) (d := d) l q s hs)

private lemma dummy (l : ℕ) (s : FighterState) (hs : AllocationSnapshots s) :
    AllocationSnapshots (fighterDummy d l s) := by
  unfold fighterDummy
  split
  · exact hs
  · rename_i phase hp
    have hq := of_activeAt (d := d) hs hp
    split
    · exact hs
    · rename_i output hout
      split
      · exact hs
      · have ha := allocate (d := d) l .dummy (levelInput d l) output s hs
        cases he : fighterAllocate d l .dummy (levelInput d l) output s with
        | mk next success =>
          simp only [he] at ha ⊢
          cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
          · exact ha
          · have hpnext := activeAt_fighterAllocate_eq_of_success
              d l (levelInput d l) .dummy output s next phase hp he
            exact putPhase (d := d) next _ ha (of_activeAt (d := d) (p := phase) ha hpnext)

private lemma opponent (l : ℕ) (e : ProgramEvent)
    (s : FighterState) (hs : AllocationSnapshots s) :
    AllocationSnapshots (fighterOpponent P d l e s) := by
  unfold fighterOpponent
  split
  · exact hs
  · rename_i phase hp
    have hq := of_activeAt (d := d) hs hp
    split
    · exact hs
    · split
      · exact hs
      · split
        · exact cancel (d := d) _ _ _ _ hs
        · exact fulfillReady (P := P) (d := d) l _ (putPhase (d := d) s _ hs hq)

private lemma startPhase (l : ℕ) (c : Candidate)
    (s : FighterState) (hs : AllocationSnapshots s) :
    AllocationSnapshots (fighterStartPhase P d l c s) := by
  unfold fighterStartPhase
  apply putPhase (d := d) _ _ (abortAbove (d := d) l _ (cancel (d := d) _ _ _ s hs))
  intro a ha _ _
  exact ha

private lemma flushBuffer (l : ℕ) (s : FighterState) (hs : AllocationSnapshots s) :
    AllocationSnapshots ((fighterFlushBuffer d l s).getD s) := by
  unfold fighterFlushBuffer
  cases hp : s.activeAt d l with
  | none => exact hs
  | some phase =>
    have hq := of_activeAt (d := d) hs hp
    simp only [bind, Option.bind_some]
    split
    · exact putPhase (d := d) s _ hs hq
    · exact hs

private lemma strategyMove (l : ℕ) (s : FighterState) (hs : AllocationSnapshots s) :
    AllocationSnapshots ((fighterStrategyMove P d l s).getD s) := by
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
          have hn : AllocationSnapshots next := by
            apply List.foldlRecOn _ _ hs
            intro t ht qi _
            exact fuelUnits (P := P) (d := d) l qi.1 (move[qi.2]?.getD 0) t ht
          change AllocationSnapshots ((match next.activeAt d l with
            | none => some next
            | some live => some (next.putPhase d
              { live with officialCode :=
                  ((phase.game d).afterMove (phase.official d) move).encode })).getD s)
          split
          · exact hn
          · rename_i live hlive
            have hq := of_activeAt (d := d) (p := live) hn hlive
            exact putPhase (d := d) next _ hn hq
        · exact hs
    · exact hs

private lemma levelAction (l : ℕ) (s : FighterState) (hs : AllocationSnapshots s) :
    AllocationSnapshots ((fighterLevelAction P d l s).getD s) := by
  unfold fighterLevelAction
  cases hp : s.activeAt d l with
  | none => exact hs
  | some phase =>
    simp only [bind, Option.bind_some]
    split
    · exact dummy (d := d) l s hs
    · split
      · exact payoff (P := P) (d := d) l _ s hs
      · cases hf : fighterFlushBuffer d l s with
        | none => exact strategyMove (P := P) (d := d) l s hs
        | some next =>
          have h := flushBuffer (d := d) l s hs
          simpa only [hf, Option.getD_some] using h

private lemma closure (l fuel : ℕ) (s : FighterState) (hs : AllocationSnapshots s) :
    AllocationSnapshots (fighterClosure P d l fuel s) := by
  induction fuel generalizing s with
  | zero => exact hs
  | succ fuel ih =>
    simp only [fighterClosure]
    cases ha : fighterLevelAction P d l s with
    | none => exact hs
    | some next =>
      have hn := levelAction (P := P) (d := d) l s hs
      simp only [ha, Option.getD_some] at hn
      exact ih next hn

private lemma processLevel (l : ℕ) (e : Option TimedEvent)
    (s : FighterState) (hs : AllocationSnapshots s) :
    AllocationSnapshots (fighterProcessLevel P d l e s) := by
  unfold fighterProcessLevel fighterCloseLevel
  apply closure (P := P) (d := d)
  cases e with
  | none => exact fulfillReady (P := P) (d := d) l s hs
  | some e =>
    dsimp only
    split
    · exact startPhase (P := P) (d := d) l _ _ (fulfillReady (P := P) (d := d) l s hs)
    · exact opponent (P := P) (d := d) l _ _ (fulfillReady (P := P) (d := d) l s hs)

private lemma holds (P : FighterParams) (d tick : ℕ) :
    AllocationSnapshots (fighterState P d tick) := by
  induction tick with
  | zero => simp [AllocationSnapshots, fighterState, initialFighterState]
  | succ t ih =>
    change AllocationSnapshots (fighter_actions P d (t + 1) (fighterState P d t))
    unfold fighter_actions
    split
    · simp [AllocationSnapshots, initialFighterState]
    · let current := { fighterState P d t with
        tick := t + 1, schedule := masterState P.B (t + 1) }
      have hc : AllocationSnapshots current := ih
      apply List.foldlRecOn _ _ hc
      intro s hs l _
      exact processLevel (P := P) (d := d) l _ s hs

end AllocationSnapshots

/-- Once active candidates at a level have timestamps at least `r`, allocations for
older candidates at that level must already be in the permanent table. -/
private lemma allocation_mem_of_candidate_tick_lt
    {P : FighterParams} {d baseTick laterTick l r : ℕ} (hr : r ≤ baseTick)
    (hlater : baseTick ≤ laterTick)
    (hbound : ∀ p ∈ (fighterState P d baseTick).active, p.level = l → r ≤ p.candidate.2)
    {a : AllocatedDirective} (ha : a ∈ (fighterState P d laterTick).allocated)
    (hsame : a.level = l) (holder : a.candidate.2 < r) :
    a ∈ (fighterState P d baseTick).allocated := by
  let valid := fun j (c : Candidate) ↦ j = l → r ≤ c.2
  let past := (fighterState P d baseTick).allocated
  have hall : ∀ t ≥ baseTick, CandidateHistory valid past (fighterState P d t) := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => exact ⟨hbound, fun _ ha ↦ Or.inl ha⟩
    | succ t ht ih =>
      change CandidateHistory valid past (fighter_actions P d (t + 1) (fighterState P d t))
      unfold fighter_actions
      split
      · simp [CandidateHistory, initialFighterState]
      · let current := { fighterState P d t with
          tick := t + 1, schedule := masterState P.B (t + 1) }
        have hc : CandidateHistory valid past current := ih
        apply List.foldlRecOn _ _ hc
        intro s hs j _
        apply CandidateHistory.processLevel j _ ?_ s hs
        intro e he _ _
        have htime := (canonical_enumeration_spec_sound P.B he).1
        dsimp only
        omega
  exact ((hall laterTick hlater).2 a ha).resolve_right
    (fun h ↦ (Nat.not_lt_of_ge (h hsame)) holder)

/-- An active phase's initial table contains every same-level allocation from an older
candidate, regardless of the tick at which that allocation is observed. -/
lemma allocation_mem_initialAllocations_of_candidate_lt
    {P : FighterParams} {d phaseTick allocationTick : ℕ} {phase : FighterPhase}
    (hphase : phase ∈ (fighterState P d phaseTick).active)
    {a : AllocatedDirective} (ha : a ∈ (fighterState P d allocationTick).allocated)
    (hsame : a.level = phase.level) (holder : a.candidate.2 < phase.candidate.2) :
    a ∈ phase.initialAllocations := by
  by_cases hd : d = 0
  · subst d
    have hempty : (fighterState P 0 phaseTick).active = [] := by
      cases phaseTick <;> simp [fighterState, fighter_actions, initialFighterState]
    simp only [hempty, List.not_mem_nil] at hphase
  · have hpos : 1 ≤ d := by omega
    have hmem : a ∈ (fighterState P d phaseTick).allocated := by
      by_cases ht : allocationTick ≤ phaseTick
      · exact (fighterState_tables_mono
          P d allocationTick phaseTick hpos ht).1 ha
      · have hbound : ∀ p ∈ (fighterState P d phaseTick).active,
            p.level = phase.level → phase.candidate.2 ≤ p.candidate.2 := by
          intro p hp hl
          have heq := List.inj_on_of_nodup_map
            (fighterState_active_levels_nodup P d phaseTick hpos)
            hp hphase hl
          rw [heq]
        exact allocation_mem_of_candidate_tick_lt
          ((fighterState_candidates_le_tick P d phaseTick).1 phase hphase) (by omega) hbound
          ha hsame holder
    exact (AllocationSnapshots.holds P d phaseTick).2 phase hphase
      a hmem hsame holder

end Kolmogorov.Milovanov
