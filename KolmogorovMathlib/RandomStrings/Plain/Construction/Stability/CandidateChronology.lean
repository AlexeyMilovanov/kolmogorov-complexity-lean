/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.SettledLowerFrames

/-!
# Candidate timestamps and the start log

Every phase of the fighter construction is built for a candidate `(program, timestamp)` that was
emitted by the master schedule, so no active or archived phase can carry a timestamp from the
future. This module proves that chronology invariant together with the exact bookkeeping of the
start log `FighterState.started` that it needs:

* `fighterProcessLevel_started_and_candidates_le` shows that one service of a level appends to
  the start log exactly the candidate started by the event, and keeps the timestamp bound of the
  active and archived phases. The proof follows the primitive operations of the service one by
  one (canceling, aborting, allocating, paying off, fueling, flushing, strategy moves and
  closure), each of which leaves the start log alone.
* `fighterState_candidates_le_tick` is the resulting chronology of all reachable states.
* `mem_started_fighterState_of_eventAt` states that a witnessed admissible candidate event is
  recorded in the start log at its own tick.

These facts are used by `SettledLowerLevels` to prove that the true marker starts its phase and
that no abortion can predate it, and by the legal-play and phase-separation modules.
-/

namespace Kolmogorov.Milovanov

/-- Every active and every archived phase of `s` has a candidate whose timestamp is at most
`bound`. -/
private def CandidatesBoundedBy (bound : ℕ) (s : FighterState) : Prop :=
  (∀ phase ∈ s.active, phase.candidate.2 ≤ bound) ∧ ∀ e ∈ s.ended, e.1.candidate.2 ≤ bound

/-- The state `t` has the start log of `s` and still satisfies the timestamp bound. -/
private def StartLogKept (bound : ℕ) (s t : FighterState) : Prop :=
  t.started = s.started ∧ CandidatesBoundedBy bound t

private lemma StartLogKept.refl {bound : ℕ} {s : FighterState} (hs : CandidatesBoundedBy bound s) :
    StartLogKept bound s s :=
  ⟨rfl, hs⟩

private lemma StartLogKept.trans {bound : ℕ} {s t u : FighterState}
    (h₁ : StartLogKept bound s t) (h₂ : StartLogKept bound t u) : StartLogKept bound s u :=
  ⟨h₂.1.trans h₁.1, h₂.2⟩

private lemma StartLogKept.foldl {α : Type} {bound : ℕ} (f : α → FighterState → FighterState)
    (hf : ∀ a s, CandidatesBoundedBy bound s → StartLogKept bound s (f a s))
    (xs : List α) {s : FighterState} (hs : CandidatesBoundedBy bound s) :
    StartLogKept bound s (xs.foldl (fun s a ↦ f a s) s) := by
  induction xs generalizing s with
  | nil => exact .refl hs
  | cons a xs ih => exact (hf a s hs).trans (ih (hf a s hs).2)

private lemma candidate_le_of_activeAt {bound d j : ℕ} {s : FighterState} {phase : FighterPhase}
    (hs : CandidatesBoundedBy bound s) (hp : s.activeAt d j = some phase) :
    phase.candidate.2 ≤ bound :=
  hs.1 phase (List.mem_of_find?_eq_some hp)

private lemma startLogKept_putPhase {bound : ℕ} (d : ℕ) {s : FighterState} {phase : FighterPhase}
    (hs : CandidatesBoundedBy bound s) (hp : phase.candidate.2 ≤ bound) :
    StartLogKept bound s (s.putPhase d phase) := by
  refine ⟨rfl, ?_, hs.2⟩
  intro p hmem
  rcases List.mem_cons.mp hmem with rfl | hmem
  · exact hp
  · exact hs.1 p (List.mem_filter.mp hmem).1

private lemma startLogKept_fighterCancel {bound : ℕ} (d j : ℕ) (reason : PhaseEnd) (cause : ℕ)
    {s : FighterState} (hs : CandidatesBoundedBy bound s) :
    StartLogKept bound s (fighterCancel d j reason cause s) := by
  unfold fighterCancel
  split
  · exact .refl hs
  · rename_i phase hphase
    refine ⟨rfl, fun p hp ↦ hs.1 p (List.mem_filter.mp hp).1, fun e he ↦ ?_⟩
    rcases List.mem_append.mp he with he | he
    · exact hs.2 e he
    · obtain rfl := List.mem_singleton.mp he
      have hp : phase.candidate.2 ≤ bound := candidate_le_of_activeAt hs hphase
      exact hp

private lemma startLogKept_fighterAbortAbove {bound : ℕ} (d j : ℕ) {s : FighterState}
    (hs : CandidatesBoundedBy bound s) :
    StartLogKept bound s (fighterAbortAbove d j s) := by
  unfold fighterAbortAbove
  refine StartLogKept.foldl _ (fun p t ht ↦ ?_) _ hs
  split
  · exact startLogKept_fighterCancel d p.level .aborted j ht
  · exact .refl ht

private lemma startLogKept_fighterAllocate {bound : ℕ} (d j : ℕ) {kind : DirectiveKind}
    {target : ℕ} {output : BitString} {s : FighterState} (hs : CandidatesBoundedBy bound s) :
    StartLogKept bound s (fighterAllocate d j kind target output s).1 := by
  unfold fighterAllocate
  split
  · exact .refl hs
  · cases hf : (if target = 0 then (none : Option BitString) else
        (fighterInputs d (target - 1)).find? (fun p ↦
          !s.allocated.any (fun a ↦ a.input == p))) with
    | none => exact startLogKept_fighterCancel d j .saturated j hs
    | some p => exact startLogKept_fighterAbortAbove d j hs

private lemma startLogKept_of_fighterAllocate_eq {bound : ℕ} {d j : ℕ} {kind : DirectiveKind}
    {target : ℕ} {output : BitString} {s next : FighterState} {success : Bool}
    (h : fighterAllocate d j kind target output s = (next, success))
    (hs : CandidatesBoundedBy bound s) : StartLogKept bound s next := by
  simpa only [h] using startLogKept_fighterAllocate (kind := kind) (target := target)
    (output := output) d j hs

private lemma startLogKept_fighterPayoff {bound : ℕ} (P : FighterParams) (d j : ℕ)
    (q : Coordinate) {s : FighterState} (hs : CandidatesBoundedBy bound s) :
    StartLogKept bound s (fighterPayoff P d j q s) := by
  unfold fighterPayoff
  split
  · exact .refl hs
  · split
    · split
      rename_i next success he
      have ha := startLogKept_of_fighterAllocate_eq he hs
      split
      · refine ⟨ha.1, ?_, ha.2.2⟩
        intro p hp
        obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hp
        exact ha.2.1 old hold
      · exact ha
    · exact .refl hs

private lemma startLogKept_fighterFulfillReady {bound : ℕ} (P : FighterParams) (d j : ℕ)
    {s : FighterState} (hs : CandidatesBoundedBy bound s) :
    StartLogKept bound s (fighterFulfillReady P d j s) := by
  unfold fighterFulfillReady
  split
  · exact .refl hs
  · exact StartLogKept.foldl (fun q t ↦ fighterPayoff P d j q t)
      (fun q t ht ↦ startLogKept_fighterPayoff P d j q ht) _ hs

private lemma startLogKept_fulfillReady_putPhase {bound : ℕ} (P : FighterParams) (d j : ℕ)
    {s : FighterState} {phase : FighterPhase} (hs : CandidatesBoundedBy bound s)
    (hp : phase.candidate.2 ≤ bound) :
    StartLogKept bound s (fighterFulfillReady P d j (s.putPhase d phase)) :=
  (startLogKept_putPhase d hs hp).trans
    (startLogKept_fighterFulfillReady P d j (startLogKept_putPhase d hs hp).2)

private lemma startLogKept_fighterFuelUnit {bound : ℕ} (P : FighterParams) (d j : ℕ)
    (q : Coordinate) {s : FighterState} (hs : CandidatesBoundedBy bound s) :
    StartLogKept bound s (fighterFuelUnit P d j q s) := by
  unfold fighterFuelUnit
  split
  · exact .refl hs
  · rename_i phase hphase
    have hp : phase.candidate.2 ≤ bound := candidate_le_of_activeAt hs hphase
    split
    · dsimp only
      have hcharged := startLogKept_putPhase d (phase := { phase with
        controlledRemaining := phase.controlledRemaining - 1 }) hs hp
      split
      · exact hcharged.trans ((startLogKept_fighterAllocate d j hcharged.2).trans
          (startLogKept_fulfillReady_putPhase P d j
            (startLogKept_fighterAllocate d j hcharged.2).2 hp))
      · exact hcharged.trans (startLogKept_fighterAllocate d j hcharged.2)
    · exact .refl hs

private lemma startLogKept_fighterFuelUnits {bound : ℕ} (P : FighterParams) (d j : ℕ)
    (q : Coordinate) (count : ℕ) {s : FighterState} (hs : CandidatesBoundedBy bound s) :
    StartLogKept bound s (fighterFuelUnits P d j q count s) := by
  induction count generalizing s with
  | zero => exact .refl hs
  | succ count ih =>
    exact (startLogKept_fighterFuelUnit P d j q hs).trans
      (ih (startLogKept_fighterFuelUnit P d j q hs).2)

private lemma startLogKept_fighterOpponent {bound : ℕ} (P : FighterParams) (d j : ℕ)
    (event : ProgramEvent) {s : FighterState} (hs : CandidatesBoundedBy bound s) :
    StartLogKept bound s (fighterOpponent P d j event s) := by
  unfold fighterOpponent
  split
  · exact .refl hs
  · rename_i phase hphase
    have hp : phase.candidate.2 ≤ bound := candidate_le_of_activeAt hs hphase
    split
    · exact .refl hs
    · split
      · exact .refl hs
      · split
        · exact startLogKept_fighterCancel d j .opponentExhausted j hs
        · exact startLogKept_fulfillReady_putPhase P d j hs hp

private lemma startLogKept_fighterDummy {bound : ℕ} (d j : ℕ) {s : FighterState}
    (hs : CandidatesBoundedBy bound s) : StartLogKept bound s (fighterDummy d j s) := by
  unfold fighterDummy
  split
  · exact .refl hs
  · rename_i phase hphase
    have hp : phase.candidate.2 ≤ bound := candidate_le_of_activeAt hs hphase
    split
    · exact .refl hs
    · split
      · exact .refl hs
      · split
        rename_i next success he
        have ha := startLogKept_of_fighterAllocate_eq he hs
        split
        · exact ha.trans (startLogKept_putPhase d ha.2 hp)
        · exact ha

private lemma startLogKept_fighterFlushBuffer {bound : ℕ} (d j : ℕ) {s : FighterState}
    (hs : CandidatesBoundedBy bound s) :
    StartLogKept bound s ((fighterFlushBuffer d j s).getD s) := by
  cases hphase : s.activeAt d j with
  | none => simpa [fighterFlushBuffer, hphase] using StartLogKept.refl hs
  | some phase =>
    have hp : phase.candidate.2 ≤ bound := candidate_le_of_activeAt hs hphase
    simp only [fighterFlushBuffer, hphase, bind, Option.bind_some]
    split
    · exact startLogKept_putPhase d hs hp
    · exact .refl hs

private lemma startLogKept_fighterStrategyMove {bound : ℕ} (P : FighterParams) (d j : ℕ)
    {s : FighterState} (hs : CandidatesBoundedBy bound s) :
    StartLogKept bound s ((fighterStrategyMove P d j s).getD s) := by
  cases hphase : s.activeAt d j with
  | none => simpa [fighterStrategyMove, hphase] using StartLogKept.refl hs
  | some phase =>
    simp only [fighterStrategyMove, hphase, bind, Option.bind_some]
    split
    · cases hm : (phase.game d).strategy (phase.official d) with
      | none => exact .refl hs
      | some move =>
        simp only [Option.bind_some]
        split
        · have hn := StartLogKept.foldl (bound := bound)
            (fun (qi : Coordinate × ℕ) s ↦
              fighterFuelUnits P d j qi.1 (move[qi.2]?.getD 0) s)
            (fun qi t ht ↦ startLogKept_fighterFuelUnits P d j qi.1 _ ht)
            (phase.game d).coordinates.zipIdx hs
          cases hlive : (List.foldl _ s (phase.game d).coordinates.zipIdx).activeAt d j with
          | none => exact hn
          | some live =>
            have hl : live.candidate.2 ≤ bound := candidate_le_of_activeAt hn.2 hlive
            exact hn.trans (startLogKept_putPhase d hn.2 hl)
        · exact .refl hs
    · exact .refl hs

private lemma startLogKept_fighterLevelAction {bound : ℕ} (P : FighterParams) (d j : ℕ)
    {s : FighterState} (hs : CandidatesBoundedBy bound s) :
    StartLogKept bound s ((fighterLevelAction P d j s).getD s) := by
  cases hphase : s.activeAt d j with
  | none => simpa [fighterLevelAction, hphase] using StartLogKept.refl hs
  | some phase =>
    simp only [fighterLevelAction, hphase, bind, Option.bind_some]
    split
    · exact startLogKept_fighterDummy d j hs
    · split
      · exact startLogKept_fighterPayoff P d j _ hs
      · cases hf : fighterFlushBuffer d j s with
        | none => exact startLogKept_fighterStrategyMove P d j hs
        | some next =>
          simpa only [hf, Option.getD_some] using startLogKept_fighterFlushBuffer d j hs

private lemma startLogKept_fighterClosure {bound : ℕ} (P : FighterParams) (d j : ℕ) (fuel : ℕ)
    {s : FighterState} (hs : CandidatesBoundedBy bound s) :
    StartLogKept bound s (fighterClosure P d j fuel s) := by
  induction fuel generalizing s with
  | zero => exact .refl hs
  | succ fuel ih =>
    simp only [fighterClosure]
    cases ha : fighterLevelAction P d j s with
    | none => exact .refl hs
    | some next =>
      have hn := startLogKept_fighterLevelAction P d j hs
      simp only [ha, Option.getD_some] at hn
      exact hn.trans (ih hn.2)

/-- Starting a phase appends exactly the started candidate to the start log, and the phase
built for a candidate with a small timestamp respects the timestamp bound. -/
private lemma fighterStartPhase_started_and_candidates_le {bound : ℕ} (P : FighterParams)
    (d j : ℕ) (candidate : Candidate) (hcandidate : candidate.2 ≤ bound) {s : FighterState}
    (hs : CandidatesBoundedBy bound s) :
    (fighterStartPhase P d j candidate s).started = s.started ++ [(j, candidate)] ∧
      CandidatesBoundedBy bound (fighterStartPhase P d j candidate s) := by
  let waiting := fighterAbortAbove d j (fighterCancel d j .replaced j s)
  have hw : StartLogKept bound s waiting := (startLogKept_fighterCancel d j .replaced j hs).trans
    (startLogKept_fighterAbortAbove d j (startLogKept_fighterCancel d j .replaced j hs).2)
  have hp := startLogKept_putPhase d hw.2
    (phase := fighter_construction P d j candidate waiting) hcandidate
  exact ⟨congrArg (fun log ↦ log ++ [(j, candidate)]) (hp.1.trans hw.1), hp.2⟩

/-- One service of a level appends to the start log exactly the candidate started by the event
(if any) and keeps the timestamp bound of the active and archived phases, provided the event
itself respects the bound. -/
private lemma fighterProcessLevel_started_and_candidates_le {bound : ℕ} (P : FighterParams)
    (d k : ℕ) (event : Option TimedEvent) (hevent : ∀ e, event = some e → e.1 ≤ bound)
    {state : FighterState} (hstate : CandidatesBoundedBy bound state) :
    (fighterProcessLevel P d k event state).started = state.started ++
      (match event with
      | none => []
      | some e => if fighterOwner d e.2.2.1.length = some k ∧
          e.2.2.1.length ≤ levelScale k ∧ P.Admissible d k
        then [(k, (e.2.2.1, e.1))] else []) ∧
    CandidatesBoundedBy bound (fighterProcessLevel P d k event state) := by
  unfold fighterProcessLevel fighterCloseLevel
  have hc := startLogKept_fighterFulfillReady P d k hstate
  cases event with
  | none =>
    simp only [List.append_nil]
    exact hc.trans (startLogKept_fighterClosure P d k _ hc.2)
  | some e =>
    dsimp only
    split
    · have hn := fighterStartPhase_started_and_candidates_le P d k (e.2.2.1, e.1)
        (hevent e rfl) hc.2
      obtain ⟨hlog, hbound⟩ := startLogKept_fighterClosure P d k
        (fighterClosureFuel d k (fighterStartPhase P d k (e.2.2.1, e.1)
          (fighterFulfillReady P d k state))) hn.2
      rw [hn.1, hc.1] at hlog
      exact ⟨hlog, hbound⟩
    · have hn := startLogKept_fighterOpponent P d k e.2.2 hc.2
      simp only [List.append_nil]
      exact hc.trans (hn.trans (startLogKept_fighterClosure P d k _ hn.2))

/-- A finite traversal of levels keeps the timestamp bound of the active and archived phases. -/
private lemma foldl_fighterProcessLevel_candidates_le {bound : ℕ} (P : FighterParams) (d : ℕ)
    (event : Option TimedEvent) (hevent : ∀ e, event = some e → e.1 ≤ bound)
    (levels : List ℕ) {state : FighterState} (hstate : CandidatesBoundedBy bound state) :
    CandidatesBoundedBy bound
      (levels.foldl (fun s k ↦ fighterProcessLevel P d k event s) state) := by
  induction levels generalizing state with
  | nil => exact hstate
  | cons k levels ih =>
    exact ih (fighterProcessLevel_started_and_candidates_le P d k event hevent hstate).2

/-- Every active or archived phase of a reachable state has a candidate timestamp at most the
current tick. Updating the master clock weakens the bound, and servicing the event of the new
tick preserves it. -/
lemma fighterState_candidates_le_tick (P : FighterParams) (d tick : ℕ) :
    (∀ phase ∈ (fighterState P d tick).active, phase.candidate.2 ≤ tick) ∧
    ∀ e ∈ (fighterState P d tick).ended, e.1.candidate.2 ≤ tick := by
  induction tick with
  | zero => simp [fighterState, initialFighterState]
  | succ tick ih =>
    change CandidatesBoundedBy (tick + 1) (fighter_actions P d (tick + 1) (fighterState P d tick))
    unfold fighter_actions
    split
    · simp [CandidatesBoundedBy, initialFighterState]
    · refine foldl_fighterProcessLevel_candidates_le P d _ (fun e he ↦ ?_) _ ?_
      · exact ((canonical_enumeration_spec_sound P.B he).1).le
      · exact ⟨fun phase hp ↦ (ih.1 phase hp).trans (Nat.le_succ _),
          fun e he ↦ (ih.2 e he).trans (Nat.le_succ _)⟩

/-- A witnessed admissible candidate event is recorded in the start log at its own tick.
The owner is included in the service list even if it was waiting; closure and larger services
retain the start log, including a phase canceled during that same tick. -/
lemma mem_started_fighterState_of_eventAt
    (P : FighterParams) (d l t i : ℕ) (p x : BitString) (hd : 1 ≤ d)
    (hevent : eventAt P.B t = some (t, i, p, x))
    (howner : fighterOwner d p.length = some l) (hlen : p.length ≤ levelScale l)
    (hadm : P.Admissible d l) :
    (l, (p, t)) ∈ (fighterState P d t).started := by
  have ht : 0 < t := (canonical_enumeration_spec_position P.B hevent).1
  let before := fighterState P d (t - 1)
  let current := { before with tick := t, schedule := masterState P.B t }
  have hb := fighterState_candidates_le_tick P d (t - 1)
  have hc : CandidatesBoundedBy t current :=
    ⟨fun phase hp ↦ (hb.1 phase hp).trans (Nat.sub_le _ _),
      fun e he ↦ (hb.2 e he).trans (Nat.sub_le _ _)⟩
  have hfold : ∀ (levels : List ℕ) (state : FighterState), CandidatesBoundedBy t state →
      ((l, (p, t)) ∈ state.started ∨ l ∈ levels) →
      (l, (p, t)) ∈ (levels.foldl (fun s k ↦
        fighterProcessLevel P d k (some (t, i, p, x)) s) state).started := by
    intro levels
    induction levels with
    | nil =>
      intro state _ hmem
      exact hmem.resolve_right (by simp)
    | cons k levels ih =>
      intro state hstate hmem
      have hk := fighterProcessLevel_started_and_candidates_le P d k (some (t, i, p, x))
        (by intro e he; cases he; exact le_rfl) hstate
      apply ih _ hk.2
      rcases hmem with hmem | hmem
      · left
        rw [hk.1]
        exact List.mem_append_left _ hmem
      · rcases List.mem_cons.mp hmem with rfl | hmem
        · left
          rw [hk.1]
          simp [howner, hlen, hadm]
        · exact Or.inr hmem
  have hnext : fighterState P d t = fighter_actions P d t before := by
    cases t with
    | zero => omega
    | succ t => rfl
  rw [hnext]
  unfold fighter_actions
  have hdne : d ≠ 0 := by omega
  simp only [hdne, ite_false, hevent, Option.bind_some, howner]
  apply hfold _ current hc
  right
  simp only [List.mem_mergeSort, List.mem_eraseDups, List.mem_append]
  exact Or.inr (by simp)

end Kolmogorov.Milovanov
