/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Construction.Diagonal.AllocationGraph
import KolmogorovMathlib.RandomStrings.Plain.Construction.Diagonal.LiveCounters
import KolmogorovMathlib.RandomStrings.Plain.Construction.Diagonal.VirtualStabilization

/-!
# Funded positives of the true-marker phase are actual positives

The virtual oracle of the true-marker phase can answer positively because a retained request of
the phase is *funded*: its price is covered by the live counters.  This module shows, for the
blueprint node `constr:agreement`, that every such answer is already positive for the actual
oracle `fighterActualAnswer`, which gives the inequality "virtual ≤ actual" of the oracle
agreement.

The proof tracks how the event transition `fighter_actions` changes the state, through a relation
`R s t` on `FighterState` that is reflexive, transitive and preserved by every primitive action
(`FrameRel`; the hypotheses of the generic lemmas are discharged once for the relation):

* the *identity step* `IdentityStep d l` says that no new phase identity (candidate) appears at
  level `l` except by updating the active record.  It proves
  `fighterState_ended_candidate_ne_marker`: if the true-marker phase is active at every tick of
  the marker tail, no end log of the phase exists, because the phase is started only once;
* a fulfilled request has an allocation receipt (`exists_allocation_of_mem_fulfilled`, from
  `Stability.FundedRequestReceipts`), hence it is a simple pair of the constructed machine
  (`simple_of_mem_fighterState_fulfilled`).

The main result `fighterActualAnswer_of_fighterFinalVirtualAnswer` combines these with the case
analysis of `Diagonal.VirtualStabilization` and the realization of funded requests of
`Diagonal.LiveCounters`; it is used in `Diagonal.OracleAgreement`, which also uses the
absence of end logs.
-/

namespace Kolmogorov.Milovanov

/-! ### Generic transport of a relation along the primitive actions -/

section FrameRel

variable {R : FighterState → FighterState → Prop} [Std.Refl R] [IsTrans FighterState R]

private theorem foldl_rel {α : Type} (f : α → FighterState → FighterState)
    (hf : ∀ a s, R s (f a s)) (xs : List α) (s : FighterState) :
    R s (xs.foldl (fun s a ↦ f a s) s) := by
  induction xs generalizing s with
  | nil => exact refl s
  | cons a xs ih => exact _root_.trans (hf a s) (ih _)

private theorem abortAbove_rel (d : ℕ)
    (hcancel : ∀ j reason cause s, R s (fighterCancel d j reason cause s)) (j : ℕ)
    (s : FighterState) : R s (fighterAbortAbove d j s) := by
  unfold fighterAbortAbove
  refine foldl_rel _ (fun p t ↦ ?_) _ s
  split
  · exact hcancel _ _ _ t
  · exact refl t

variable (R) in
/-- A reflexive and transitive relation between fighter states is *frame-compatible* when it is
preserved by the primitive actions of the event transition at every level `j`: updating the
active record without changing its identity, cancelling, allocating, and fulfilling a request.
All composite actions then preserve it (`FrameRel.closure`). -/
private structure FrameRel (P : FighterParams) (d : ℕ) : Prop where
  /-- Replacing the active record of level `j` by one with the same identity. -/
  putPhase : ∀ j s old p, s.activeAt d j = some old → p.level = j →
    p.candidate = old.candidate → R s (s.putPhase d p)
  /-- Cancelling level `j`. -/
  cancel : ∀ j reason cause s, R s (fighterCancel d j reason cause s)
  /-- Allocating at level `j`, whether or not the allocation succeeds. -/
  allocate : ∀ j kind target out s, R s (fighterAllocate d j kind target out s).1
  /-- Checking one request at level `j`. -/
  payoff : ∀ j q s, R s (fighterPayoff P d j q s)

namespace FrameRel

variable {P : FighterParams} {d : ℕ} (hR : FrameRel R P d)
include hR

private theorem fulfillReady (j : ℕ) (s : FighterState) : R s (fighterFulfillReady P d j s) := by
  unfold fighterFulfillReady
  split
  · exact refl s
  · exact foldl_rel _ (fun q t ↦ hR.payoff j q t) _ s

private theorem fuelUnit (j : ℕ) (q : Coordinate) (s : FighterState) :
    R s (fighterFuelUnit P d j q s) := by
  unfold fighterFuelUnit
  split
  · exact refl s
  · rename_i phase hp
    have hl := FighterState.level_eq_of_activeAt_eq_some (p := phase) hp
    split
    · let charged := { phase with controlledRemaining := phase.controlledRemaining - 1 }
      let index := fighterFreshString d
        (phase.indices[(phase.game d).coordinates.idxOf q]?.getD [])
      let out := pairCode (triple q.1 (q.2 - d) phase.candidate.1) index
      have hc := hR.putPhase j s phase charged hp hl rfl
      have ha := hR.allocate j .fuel (levelUpper j + d) out (s.putPhase d charged)
      change R s
        (match fighterAllocate d j .fuel (levelUpper j + d) out (s.putPhase d charged) with
        | (next, success) => if success then
            fighterFulfillReady P d j (next.putPhase d
              ((charged.insertIndex d q index).fundRequests d next.fulfilled)) else next)
      cases he : fighterAllocate d j .fuel (levelUpper j + d) out (s.putPhase d charged) with
      | mk next success =>
        rw [he] at ha
        cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
        · exact _root_.trans hc ha
        · have hstay : next.activeAt d j = some charged := by
            have hh := FighterState.activeAt_fighterAllocate_of_success d j
              .fuel (levelUpper j + d) out (s.putPhase d charged) (by rw [he])
            rw [he] at hh
            exact hh.trans (by simp [FighterState.putPhase, FighterState.activeAt, charged, hl])
          refine _root_.trans (_root_.trans hc ha) (_root_.trans ?_ (hR.fulfillReady j _))
          exact hR.putPhase j next charged _ hstay hl rfl
    · exact refl s

private theorem fuelUnits (j : ℕ) (q : Coordinate) (count : ℕ) (s : FighterState) :
    R s (fighterFuelUnits P d j q count s) := by
  induction count generalizing s with
  | zero => exact refl s
  | succ count ih => exact _root_.trans (hR.fuelUnit j q s) (ih _)

private theorem opponent (j : ℕ) (event : ProgramEvent) (s : FighterState) :
    R s (fighterOpponent P d j event s) := by
  unfold fighterOpponent
  split
  · exact refl s
  · rename_i phase hp
    have hl := FighterState.level_eq_of_activeAt_eq_some (p := phase) hp
    split
    · exact refl s
    · split
      · exact refl s
      · split
        · exact hR.cancel j _ _ s
        · refine _root_.trans ?_ (hR.fulfillReady j _)
          exact hR.putPhase j s phase _ hp hl rfl

private theorem dummy (j : ℕ) (s : FighterState) : R s (fighterDummy d j s) := by
  unfold fighterDummy
  split
  · exact refl s
  · rename_i phase hp
    have hl := FighterState.level_eq_of_activeAt_eq_some (p := phase) hp
    split
    · exact refl s
    · rename_i out hout
      split
      · exact refl s
      · have ha := hR.allocate j .dummy (levelInput d j) out s
        cases he : fighterAllocate d j .dummy (levelInput d j) out s with
        | mk next success =>
          simp only [he] at ha ⊢
          cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
          · exact ha
          · have hstay : next.activeAt d j = some phase := by
              have hh := FighterState.activeAt_fighterAllocate_of_success d j
                .dummy (levelInput d j) out s (by rw [he])
              rw [he] at hh
              exact hh.trans hp
            exact _root_.trans ha (hR.putPhase j next phase _ hstay hl rfl)

omit [IsTrans FighterState R] in
private theorem flushBuffer (j : ℕ) (s : FighterState) :
    R s ((fighterFlushBuffer d j s).getD s) := by
  unfold fighterFlushBuffer
  cases hp : s.activeAt d j with
  | none => exact refl s
  | some phase =>
    have hl := FighterState.level_eq_of_activeAt_eq_some (p := phase) hp
    simp only [bind, Option.bind_some]
    split
    · exact hR.putPhase j s phase _ hp hl rfl
    · exact refl s

private theorem strategyMove (j : ℕ) (s : FighterState) :
    R s ((fighterStrategyMove P d j s).getD s) := by
  unfold fighterStrategyMove
  cases hp : s.activeAt d j with
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
            fighterFuelUnits P d j q (move[i]?.getD 0) s) s
          have hn : R s next :=
            foldl_rel (fun (qi : Coordinate × ℕ) t ↦
              fighterFuelUnits P d j qi.1 (move[qi.2]?.getD 0) t)
              (fun qi t ↦ hR.fuelUnits j qi.1 _ t) _ s
          change R s ((match next.activeAt d j with
            | none => some next
            | some live => some (next.putPhase d
              { live with officialCode :=
                  ((phase.game d).afterMove (phase.official d) move).encode })).getD s)
          split
          · exact hn
          · rename_i live hlive
            have hl := FighterState.level_eq_of_activeAt_eq_some (p := live) hlive
            exact _root_.trans hn (hR.putPhase j next live _ hlive hl rfl)
        · exact refl s
    · exact refl s

private theorem levelAction (j : ℕ) (s : FighterState) :
    R s ((fighterLevelAction P d j s).getD s) := by
  unfold fighterLevelAction
  cases hp : s.activeAt d j with
  | none => exact refl s
  | some phase =>
    simp only [bind, Option.bind_some]
    split
    · exact hR.dummy j s
    · split
      · exact hR.payoff j _ s
      · cases hf : fighterFlushBuffer d j s with
        | none => exact hR.strategyMove j s
        | some next =>
          simpa only [hf, Option.getD_some] using hR.flushBuffer j s

/-- All composite level actions preserve a frame-compatible relation, so does the closure of
a level under its actions. -/
private theorem closure (j fuel : ℕ) (s : FighterState) :
    R s (fighterClosure P d j fuel s) := by
  induction fuel generalizing s with
  | zero => exact refl s
  | succ fuel ih =>
    simp only [fighterClosure]
    cases ha : fighterLevelAction P d j s with
    | none => exact refl s
    | some next =>
      have hn := hR.levelAction j s
      simp only [ha, Option.getD_some] at hn
      exact _root_.trans hn (ih next)

end FrameRel

end FrameRel

/-! ### Phase identities: a service of level `l` starts at most one phase -/

/-- A transition without a start at the tracked level preserves the identity of every
surviving record. Any new end record comes from the old active record and leaves the
tracked level empty. This also applies to malformed input states with repeated levels. -/
private def IdentityStep (d l : ℕ) (s t : FighterState) : Prop :=
  (∀ p, t.activeAt d l = some p →
    ∃ old, s.activeAt d l = some old ∧ p.candidate = old.candidate) ∧
  ∀ e ∈ t.ended, e.1.level = l →
    e ∈ s.ended ∨ (t.activeAt d l = none ∧
      ∃ old, s.activeAt d l = some old ∧ e.1.candidate = old.candidate)

/-- The active identity of a level is absent from its cancellation archive. -/
private def ActiveNotEnded (d l : ℕ) (s : FighterState) : Prop :=
  ∀ p, s.activeAt d l = some p → ∀ e ∈ s.ended,
    e.1.level = l → e.1.candidate ≠ p.candidate

/-- All identities already observed at the tracked level predate the next event. -/
private def EndedBefore (d l born : ℕ) (s : FighterState) : Prop :=
  (∀ p, s.activeAt d l = some p → p.candidate.2 < born) ∧
  ∀ e ∈ s.ended, e.1.level = l → e.1.candidate.2 < born

private instance (d l : ℕ) : Std.Refl (IdentityStep d l) :=
  ⟨fun _ ↦ ⟨fun p hp ↦ ⟨p, hp, rfl⟩, fun _ he _ ↦ Or.inl he⟩⟩

private instance (d l : ℕ) : IsTrans FighterState (IdentityStep d l) := by
  refine ⟨fun s t u hst htu ↦ ⟨fun p hp ↦ ?_, fun e he hl ↦ ?_⟩⟩
  · obtain ⟨mid, hm, hpm⟩ := htu.1 p hp
    obtain ⟨old, ho, hmo⟩ := hst.1 mid hm
    exact ⟨old, ho, hpm.trans hmo⟩
  · rcases htu.2 e he hl with he | ⟨hnone, mid, hm, hcm⟩
    · rcases hst.2 e he hl with he | ⟨hnone, old, ho, hco⟩
      · exact Or.inl he
      · refine Or.inr ⟨?_, old, ho, hco⟩
        cases hu : u.activeAt d l with
        | none => rfl
        | some p =>
          obtain ⟨mid, hm, _⟩ := htu.1 p hu
          rw [hnone] at hm
          contradiction
    · obtain ⟨old, ho, hmo⟩ := hst.1 mid hm
      exact Or.inr ⟨hnone, old, ho, hcm.trans hmo⟩

namespace IdentityStep

variable {d l : ℕ}

private theorem of_eq {s t : FighterState} (ha : t.activeAt d l = s.activeAt d l)
    (he : t.ended = s.ended) : IdentityStep d l s t :=
  ⟨fun p hp ↦ ⟨p, ha ▸ hp, rfl⟩, fun _ h _ ↦ Or.inl (he ▸ h)⟩

private theorem activeNotEnded {s t : FighterState} (hframe : IdentityStep d l s t)
    (hs : ActiveNotEnded d l s) : ActiveNotEnded d l t := by
  intro p hp e he hl hc
  obtain ⟨old, ho, hco⟩ := hframe.1 p hp
  rcases hframe.2 e he hl with he | ⟨hnone, _⟩
  · exact hs old ho e he hl (hc.trans hco)
  · rw [hnone] at hp
    contradiction

private theorem endedBefore (born : ℕ) {s t : FighterState} (hframe : IdentityStep d l s t)
    (hs : EndedBefore d l born s) : EndedBefore d l born t := by
  refine ⟨fun p hp ↦ ?_, fun e he hl ↦ ?_⟩
  · obtain ⟨old, ho, hc⟩ := hframe.1 p hp
    rw [hc]
    exact hs.1 old ho
  · rcases hframe.2 e he hl with he | ⟨_, old, ho, hc⟩
    · exact hs.2 e he hl
    · rw [hc]
      exact hs.1 old ho

/-- Updating the current record does not create a new phase identity. -/
private theorem putPhase (s : FighterState) (p : FighterPhase)
    (hupdate : p.level = l →
      ∃ old, s.activeAt d l = some old ∧ p.candidate = old.candidate) :
    IdentityStep d l s (s.putPhase d p) := by
  refine ⟨fun next hn ↦ ?_, fun _ he _ ↦ Or.inl he⟩
  by_cases hl : p.level = l
  · have heq : p = next := by
      simpa [FighterState.putPhase, FighterState.activeAt, hl] using hn
    subst next
    exact hupdate hl
  · rw [FighterState.activeAt_putPhase_of_ne d l s p (Ne.symm hl)] at hn
    exact ⟨next, hn, rfl⟩

/-- Cancellation is the only primitive operation that adds an end record, and it
simultaneously removes every active record of that level. -/
private theorem cancel (j : ℕ) (reason : PhaseEnd) (cause : ℕ) (s : FighterState) :
    IdentityStep d l s (fighterCancel d j reason cause s) := by
  unfold fighterCancel
  split
  · exact refl s
  · rename_i phase hphase
    have hj := FighterState.level_eq_of_activeAt_eq_some (p := phase) hphase
    by_cases hl : l = j
    · cases hl
      have hnone :
          ({ s with active := s.active.filter (fun p ↦ p.level != l)
                    ended := s.ended ++ [({ phase with pending := [] }, s.tick, reason, cause)] }
            : FighterState).activeAt d l = none := by
        simp [FighterState.activeAt, List.find?_filter]
      refine ⟨fun p hp ↦ ?_, fun e he _ ↦ ?_⟩
      · rw [hnone] at hp
        contradiction
      · rcases List.mem_append.mp he with he | he
        · exact Or.inl he
        · obtain rfl := List.mem_singleton.mp he
          exact Or.inr ⟨hnone, phase, hphase, rfl⟩
    · refine ⟨fun p hp ↦ ?_, fun e he helevel ↦ ?_⟩
      · change (s.active.filter (fun p ↦ p.level != j)).find?
          (fun p ↦ p.level == l) = some p at hp
        rw [FighterState.find?_level_filter_ne _ _ _ hl] at hp
        exact ⟨p, hp, rfl⟩
      · rcases List.mem_append.mp he with he | he
        · exact Or.inl he
        · obtain rfl := List.mem_singleton.mp he
          exact False.elim (hl (helevel.symm.trans hj))

/-- Allocation, successful or not, never starts a phase: it either cancels the issuing level
or aborts the larger ones. -/
private theorem allocate (j : ℕ) (kind : DirectiveKind) (target : ℕ) (out : BitString)
    (s : FighterState) : IdentityStep d l s (fighterAllocate d j kind target out s).1 := by
  unfold fighterAllocate
  split
  · exact refl s
  · cases hf : (if target = 0 then (none : Option BitString) else
        (fighterInputs d (target - 1)).find? (fun p ↦
          !s.allocated.any (fun a ↦ a.input == p))) with
    | none => exact _root_.trans (of_eq rfl rfl) (cancel j .saturated j _)
    | some input => exact _root_.trans (of_eq rfl rfl) (abortAbove_rel d cancel j _)

/-- Fulfilling a request never starts a phase: the pair is only removed from the pending lists
of the active records. -/
private theorem payoff (P : FighterParams) (j : ℕ) (q : Coordinate) (s : FighterState) :
    IdentityStep d l s (fighterPayoff P d j q s) := by
  have hrecord (next : FighterState) : IdentityStep d l next
      { next with fulfilled := next.fulfilled ++ [q]
                  active := next.active.map (fun p ↦
                    { p with pending := p.pending.filter (· != q) }) } := by
    refine ⟨fun p hp ↦ ?_, fun _ he _ ↦ Or.inl he⟩
    have hm : (next.activeAt d l).map
        (fun p ↦ { p with pending := p.pending.filter (· != q) }) = some p := by
      simpa only [FighterState.activeAt, List.find?_map, Function.comp_def] using hp
    obtain ⟨old, ho, rfl⟩ := Option.map_eq_some_iff.mp hm
    exact ⟨old, ho, rfl⟩
  unfold fighterPayoff
  split
  · exact refl s
  · split
    · have ha : IdentityStep d l s (fighterAllocate d j .payoff q.2 q.1 s).1 :=
        allocate j .payoff q.2 q.1 s
      cases he : fighterAllocate d j .payoff q.2 q.1 s with
      | mk next success =>
        simp only [he] at ha ⊢
        cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
        · exact ha
        · exact _root_.trans ha (hrecord next)
    · exact refl s

private theorem frameRel (P : FighterParams) : FrameRel (IdentityStep d l) P d where
  putPhase j s old p hp hl hc := putPhase s p fun heq ↦
    ⟨old, by simpa only [← hl, heq] using hp, hc⟩
  cancel := cancel
  allocate := allocate
  payoff := payoff P

/-- Starting a candidate at another level can cancel the tracked level, but cannot create a
record there. The start's insertion changes only its own level. -/
private theorem startPhase_of_ne (P : FighterParams) (j : ℕ) (candidate : Candidate)
    (s : FighterState) (hne : j ≠ l) :
    IdentityStep d l s (fighterStartPhase P d j candidate s) := by
  let waiting := fighterAbortAbove d j (fighterCancel d j .replaced j s)
  have hw : IdentityStep d l s waiting :=
    _root_.trans (cancel j .replaced j s) (abortAbove_rel d cancel j _)
  have hp : IdentityStep d l waiting
      (waiting.putPhase d (fighter_construction P d j candidate waiting)) :=
    putPhase _ _ fun hlevel ↦ False.elim (hne hlevel)
  exact _root_.trans hw (_root_.trans hp (of_eq rfl rfl))

/-- A complete service at another level has no start at the tracked level. -/
private theorem processLevel_of_ne (P : FighterParams) (j : ℕ) (event : Option TimedEvent)
    (s : FighterState) (hne : j ≠ l) : IdentityStep d l s (fighterProcessLevel P d j event s) := by
  have hR := frameRel (d := d) (l := l) P
  unfold fighterProcessLevel fighterCloseLevel
  refine _root_.trans (hR.fulfillReady j s) ?_
  cases event with
  | none => exact hR.closure j _ _
  | some e =>
    dsimp only
    split
    · exact _root_.trans (startPhase_of_ne P j _ _ hne) (hR.closure j _ _)
    · exact _root_.trans (hR.opponent j _ _) (hR.closure j _ _)

end IdentityStep

/-- If every old identity at a level predates the new candidate's timestamp, starting that
candidate installs an identity absent from the archive. Cancellation of the previous phase and
priority abortion only archive old identities. -/
private theorem activeNotEnded_startPhase (P : FighterParams) (d l born : ℕ)
    (candidate : Candidate) (s : FighterState) (hcandidate : candidate.2 = born)
    (hbefore : EndedBefore d l born s) :
    ActiveNotEnded d l (fighterStartPhase P d l candidate s) := by
  let waiting := fighterAbortAbove d l (fighterCancel d l .replaced l s)
  let phase := fighter_construction P d l candidate waiting
  have hw : IdentityStep d l s waiting :=
    _root_.trans (IdentityStep.cancel l .replaced l s)
      (abortAbove_rel d IdentityStep.cancel l _)
  have hb := hw.endedBefore born hbefore
  intro p hp e he hl hc
  change (waiting.putPhase d phase).activeAt d l = some p at hp
  have hlevel : phase.level = l := rfl
  have heq : phase = p := by
    simpa only [FighterState.putPhase, FighterState.activeAt, hlevel,
      List.find?_cons, beq_self_eq_true, Option.some.injEq] using hp
  subst p
  change e ∈ waiting.ended at he
  have htime := hb.2 e he hl
  have hcand : phase.candidate = candidate := rfl
  rw [hc, hcand, hcandidate] at htime
  exact (Nat.lt_irrefl born) htime

/-- One service of the tracked level preserves disjoint active and ended identities when all
input identities are older than the current event. A start uses the fresh event timestamp; every
other part of the service has no starts. -/
private theorem activeNotEnded_processLevel (P : FighterParams) (d l born : ℕ)
    (event : Option TimedEvent) (s : FighterState)
    (hevent : ∀ e, event = some e → e.1 = born)
    (hdisjoint : ActiveNotEnded d l s) (hbefore : EndedBefore d l born s) :
    ActiveNotEnded d l (fighterProcessLevel P d l event s) := by
  have hR := IdentityStep.frameRel (d := d) (l := l) P
  have hchecked := (hR.fulfillReady l s).activeNotEnded hdisjoint
  have hcheckedBefore := (hR.fulfillReady l s).endedBefore born hbefore
  unfold fighterProcessLevel fighterCloseLevel
  refine (hR.closure l _ _).activeNotEnded ?_
  cases event with
  | none => exact hchecked
  | some e =>
    dsimp only
    split
    · exact activeNotEnded_startPhase P d l born _ _ (hevent e rfl) hcheckedBefore
    · exact (hR.opponent l _ _).activeNotEnded hchecked

/-- In a list of distinct service levels, the tracked level is visited at most once. The prefix
preserves the old timestamp bound, its own service can introduce one fresh identity, and the
suffix cannot restart that identity after cancellation. -/
private theorem activeNotEnded_foldl_processLevel (P : FighterParams) (d l born : ℕ)
    (event : Option TimedEvent) (levels : List ℕ) (s : FighterState)
    (hnodup : levels.Nodup) (hevent : ∀ e, event = some e → e.1 = born)
    (hdisjoint : ActiveNotEnded d l s) (hbefore : EndedBefore d l born s) :
    ActiveNotEnded d l (levels.foldl (fun s j ↦ fighterProcessLevel P d j event s) s) := by
  have hothers (xs : List ℕ) (hnot : l ∉ xs) (s : FighterState) :
      IdentityStep d l s (xs.foldl (fun s j ↦ fighterProcessLevel P d j event s) s) := by
    induction xs generalizing s with
    | nil => exact refl s
    | cons j xs ih =>
      have hne : j ≠ l := fun h ↦ hnot (List.mem_cons.mpr (Or.inl h.symm))
      exact _root_.trans (IdentityStep.processLevel_of_ne P j event s hne)
        (ih (fun h ↦ hnot (List.mem_cons.mpr (Or.inr h))) _)
  induction levels generalizing s with
  | nil => exact hdisjoint
  | cons j levels ih =>
    obtain ⟨hnot, hnodup⟩ := List.nodup_cons.mp hnodup
    by_cases hj : j = l
    · subst j
      exact (hothers levels hnot _).activeNotEnded
        (activeNotEnded_processLevel P d l born event s hevent hdisjoint hbefore)
    · have hf : IdentityStep d l s _ := IdentityStep.processLevel_of_ne P j event s hj
      exact ih _ hnodup (hf.activeNotEnded hdisjoint) (hf.endedBefore born hbefore)

/-- At each completed tick the active identity is absent from the end log. Previous records have
timestamps at most the previous tick, while any new start is stamped by the current tick and the
service list has no duplicate levels. -/
private theorem activeNotEnded_fighterState (P : FighterParams) (d l tick : ℕ) :
    ActiveNotEnded d l (fighterState P d tick) := by
  induction tick with
  | zero => simp [ActiveNotEnded, fighterState, initialFighterState, FighterState.activeAt]
  | succ tick ih =>
    change ActiveNotEnded d l (fighter_actions P d (tick + 1) (fighterState P d tick))
    unfold fighter_actions
    split
    · simp [ActiveNotEnded, initialFighterState, FighterState.activeAt]
    · refine activeNotEnded_foldl_processLevel P d l (tick + 1) _ _ _
        (nodup_eraseDups_list _).mergeSort
        (fun e he ↦ (canonical_enumeration_spec_sound P.B he).1) ih ?_
      have hhistory := fighterState_candidate_time_le P d tick
      exact ⟨fun p hp ↦ Nat.lt_succ_of_le (hhistory.1 l p hp),
        fun e he _ ↦ Nat.lt_succ_of_le (hhistory.2 e he)⟩

/-- If the true-marker phase has an active record at every completed tick from the marker tick
through `tick`, then no end log of this phase (same level and candidate) exists at `tick`.
An end log is written only by cancelling the active record; a phase born at the marker tick
is started at most once (one service of level `l` per tick) and never restarted later, so a
cancellation at a tick `t` in the interval would leave no active record at the end of `t`.
Before the marker tick no record with this candidate exists. -/
lemma fighterState_ended_candidate_ne_marker
    (P : FighterParams) (d l tick : ℕ)
    (htick : markerTick P.B (levelScale l) ≤ tick)
    (hactive : ∀ t, markerTick P.B (levelScale l) ≤ t → t ≤ tick →
      ∃ phase, TrueMarkerPhaseAt P d l t phase) :
    ∀ e ∈ (fighterState P d tick).ended,
      e.1.level = l → e.1.candidate = markerCandidate P.B (levelScale l) → False := by
  obtain ⟨phase, hphase⟩ := hactive tick htick le_rfl
  intro e he hl hc
  exact activeNotEnded_fighterState P d l tick phase hphase.2.2.2 e he hl
    (hc.trans hphase.2.2.1.symm)

/-! ### Allocation receipts: a fulfilled request is a simple pair -/

/-- A globally fulfilled pair `(x, r)` has a permanent successful payoff allocation with an input
of length `r - 1` and output `x`; the directive branch of the constructed machine turns it
into a description of `x` of length `r`. -/
private theorem simple_of_mem_fighterState_fulfilled (P : FighterParams) (d tick : ℕ)
    (hd : 1 ≤ d) (x : BitString) (r : ℕ)
    (hfulfilled : (x, r) ∈ (fighterState P d tick).fulfilled) :
    Simple (fighterU P d) x r := by
  obtain ⟨a, ha, hlen, hout⟩ := exists_allocation_of_mem_fulfilled P d tick (x, r) hfulfilled
  simpa [hout, hlen] using simple_of_mem_fighterState_allocated P d tick hd a ha

/-- Realization makes every funded pair globally fulfilled, making it an actual positive. -/
private theorem fighterActualAnswer_of_funded
    (P : FighterParams) (C cGap cRank d₀ d l : ℕ) (hfixed : FighterFixedConstants P C cGap cRank d₀)
    (hgood : GoodPadding P d₀ cRank cGap d) (hlate : LateAdmissibleOccurrence P d l)
    (q : Coordinate)
    (hfunded : ∃ tick ≥ markerTick P.B (levelScale l), ∃ phase,
        TrueMarkerPhaseAt P d l tick phase ∧
        ∃ retained ∈ phase.J d, retained.1 = q.1 ∧ retained.2 ≤ q.2 ∧
        (phase.game d).price retained ≤
          (phase.game d).coordinateValue phase.liveCounters retained) :
    fighterActualAnswer P d q = true := by
  obtain ⟨tick, htick, phase, hphase, ⟨x, r⟩, hret, hx, hk, hprice⟩ := hfunded
  obtain ⟨hstarted, _, hlegal, _⟩ :=
    true_marker_opponent_stream_legal P C cGap cRank d₀ d l hfixed hgood hlate
  obtain ⟨_, _, _, hrecords, _⟩ := hlegal
  have hactive : ∀ t, markerTick P.B (levelScale l) ≤ t → t ≤ tick →
      ∃ phase, TrueMarkerPhaseAt P d l t phase := by
    intro t ht _
    obtain ⟨p, hp, _⟩ := hrecords t ht
    exact ⟨p, hp⟩
  have hsurvives : TrueMarkerPhaseSurvives P d l tick :=
    ⟨hstarted, htick, hactive, fighterState_ended_candidate_ne_marker P d l tick htick hactive⟩
  have hcard :=
    fighterState_counter_eq_card_indicesAt
      P d tick phase (List.mem_of_find?_eq_some hphase.2.2.2) (x, r) hret
  rw [hcard] at hprice
  obtain ⟨_, ⟨later, _, hful⟩, _⟩ :=
    true_marker_funded_request_realized P C cGap cRank d₀ d l tick hfixed hgood hlate
      hsurvives phase hphase x r hret hprice
  have hsimple := simple_of_mem_fighterState_fulfilled P d later hgood.positive x r hful
  have hq : Simple (fighterU P d) q.1 q.2 := by
    have h := simple_mono (fighterU P d) x hk
    simp only at hx
    rw [← hx]
    exact h hsimple
  rw [fighter_actual_answer_eq P d hgood.positive]
  simp [coordinateOracleAnswer, fighterOracle, actualCoordinateOracle, hq]

/-- If the limiting virtual answer is yes, the query is either universally trivial,
true initially, or funded and eventually realized, making it an actual positive. -/
lemma fighterActualAnswer_of_fighterFinalVirtualAnswer (P : FighterParams)
    (C cGap cRank d₀ d l : ℕ) (hfixed : FighterFixedConstants P C cGap cRank d₀)
    (hgood : GoodPadding P d₀ cRank cGap d) (hlate : LateAdmissibleOccurrence P d l) :
    ∀ q ∈ (P.family.tree d l (levelInput d l)).queries,
      fighterFinalVirtualAnswer P d l (markerCandidate P.B (levelScale l)) q = true →
      fighterActualAnswer P d q = true := by
  intro q _ hq_virt
  rcases fighterFinalVirtualAnswer_cases
    P C cGap cRank d₀ d l hfixed hgood hlate q hq_virt with hliteral | hinitial | hfunded
  · exact fighterActualAnswer_of_literal P d q hliteral
  · exact fighterActualAnswer_of_initialAnswer P d l hgood.positive q hinitial
  · exact fighterActualAnswer_of_funded P C cGap cRank d₀ d l hfixed hgood hlate q hfunded

end Kolmogorov.Milovanov
