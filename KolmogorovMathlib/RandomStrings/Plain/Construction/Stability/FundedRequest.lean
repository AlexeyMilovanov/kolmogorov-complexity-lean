/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.FundedRequestReceipts
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.FundedRequestTrace
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.FundedRequestPriority
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.FundedRequestOpponent

/-!
# Every funded true-marker request is realized

This module proves the realization lemma of the construction (blueprint node
`constr:realization`): for the fixed good even `d`, a retained pair `(x, r)` of a surviving
true-marker phase whose price is covered by the phase's index budget is *safe*
(`plainK P.B.V x ≤ r - d / 2`), is eventually fulfilled in the global table, and, if it was
already fulfilled before the phase began, is positively answered by the phase's initial
allocation snapshot.

The proof combines the priority and opponent-budget exclusions of the sibling modules
`FundedRequestPriority` and `FundedRequestOpponent` with the capacity certificate to show that
the phase record survives all later ticks, and with the receipt lemmas of `FundedRequestReceipts`
and `FundedRequestTrace` to turn a safety witness into a payoff.  Two auxiliary facts are proved
here:

* `fighterState_allocated_subset_initialAllocations_of_lt`: a live phase's saved allocation
  snapshot contains every allocation made before its candidate timestamp, proved by an invariant
  preserved by each action of the fighter's tick;
* a saved successful allocation yields a positive initial answer.

The result is used by `PhaseSeparationSources` to separate the phases of one level.
-/

namespace Kolmogorov.Milovanov

/-- A true-marker phase that survives until `tick` keeps surviving at every later tick: combine
the separate priority and opponent-budget exclusions with the capacity certificate.
The phase trace then supplies every future active record and rules out all end logs. -/
private theorem trueMarkerPhaseSurvives_of_le
    (P : FighterParams) (d l tick : ℕ) (hd : 1 ≤ d)
    (hlate : LateAdmissibleOccurrence P d l)
    (hnoalloc : ∀ t, (fighterState P d t).failed = false)
    (hsurvives : TrueMarkerPhaseSurvives P d l tick) :
    ∀ later ≥ tick, TrueMarkerPhaseSurvives P d l later := by
  have hpriority := ended_reason_ne_replaced_and_aborted_of_trueMarkerPhaseSurvives
    P d l tick hd hsurvives
      (length_gt_of_eventAt_of_markerTick_lt P.B (levelScale l))
  have hn : P.n₀ ≤ levelScale l := (le_max_right _ _).trans hlate.1.2.1
  have htail : rest P.B (levelScale l) (levelUpper l) ≤
      P.c₁ * 2 ^ (levelUpper l - levelScale l) := by
    simpa only [level_upper_eq] using P.tail_bound (levelScale l) hn
  have hopponent := trueMarkerNeverEndsFor_opponentExhausted P d l htail
  have hnoend : ∀ time ≥ tick, ∀ e ∈ (fighterState P d time).ended,
      e.1.level = l → e.1.candidate = markerCandidate P.B (levelScale l) → False := by
    intro time htime e he hl hc
    obtain ⟨hr, ha⟩ := hpriority time htime e he hl hc
    have ho := hopponent time e he hl hc
    have hs := fighterState_ended_reason_ne_saturated
      P d time (hnoalloc time) e he
    cases hreason : e.2.2.1 with
    | replaced => exact hr hreason
    | aborted => exact ha hreason
    | opponentExhausted => exact ho hreason
    | saturated => exact hs hreason
  obtain ⟨phase, hphase⟩ := hsurvives.2.2.1 tick hsurvives.2.1 le_rfl
  intro later hle
  refine ⟨hsurvives.1, hsurvives.2.1.trans hle, ?_, hnoend later hle⟩
  intro time hmarker htime
  by_cases hpast : time ≤ tick
  · exact hsurvives.2.2.1 time hmarker hpast
  · have hfuture : tick ≤ time := by omega
    rcases fighterState_active_or_ended_of_le
        P d tick time hd hfuture phase (List.mem_of_find?_eq_some hphase.2.2.2) with
      ⟨next, hn, hl, hc⟩ | ⟨e, he, hl, hc⟩
    · have hlevel := hl.trans hphase.2.1
      have hcand := hc.trans hphase.2.2.1
      refine ⟨next, hmarker, hlevel, hcand, ?_⟩
      exact FighterState.activeAt_eq_some_of_mem d l _ next
        (fighterState_active_levels_nodup P d time hd) hn hlevel
    · exact (hnoend time hfuture e he (hl.trans hphase.2.1)
        (hc.trans hphase.2.2.1)).elim

section AllocationSnapshots

/-- A phase record's saved allocation snapshot contains every allocation of the ticks strictly
preceding its candidate timestamp. -/
private def PhaseSnapshotCovers (P : FighterParams) (d : ℕ) (p : FighterPhase) : Prop :=
  ∀ before < p.candidate.2, (fighterState P d before).allocated ⊆ p.initialAllocations

/-- The invariant maintained by the actions of the tick `bound - 1`: the working allocation list
contains all allocations of the ticks before `bound`, and every active phase is covered. -/
private def SnapshotsCover (P : FighterParams) (d bound : ℕ) (s : FighterState) : Prop :=
  (∀ before < bound, (fighterState P d before).allocated ⊆ s.allocated) ∧
    ∀ p ∈ s.active, PhaseSnapshotCovers P d p

variable {P : FighterParams} {d bound : ℕ}

private theorem snapshotsCover_foldl {α : Type} (f : α → FighterState → FighterState)
    (hf : ∀ a s, SnapshotsCover P d bound s → SnapshotsCover P d bound (f a s))
    (xs : List α) (s : FighterState) (hs : SnapshotsCover P d bound s) :
    SnapshotsCover P d bound (xs.foldl (fun s a => f a s) s) := by
  induction xs generalizing s with
  | nil => exact hs
  | cons a xs ih => exact ih _ (hf a s hs)

private theorem snapshotsCover_putPhase (s : FighterState) (p : FighterPhase)
    (hs : SnapshotsCover P d bound s) (hp : PhaseSnapshotCovers P d p) :
    SnapshotsCover P d bound (s.putPhase d p) := by
  refine ⟨hs.1, ?_⟩
  intro next hn
  rcases List.mem_cons.mp hn with rfl | hn
  · exact hp
  · exact hs.2 next (List.mem_filter.mp hn).1

private theorem snapshotsCover_cancel (l cause : ℕ) (reason : PhaseEnd) (s : FighterState)
    (hs : SnapshotsCover P d bound s) :
    SnapshotsCover P d bound (fighterCancel d l reason cause s) := by
  unfold fighterCancel
  split
  · exact hs
  · refine ⟨hs.1, ?_⟩
    intro p hp
    exact hs.2 p (List.mem_filter.mp hp).1

private theorem snapshotsCover_abortAbove (l : ℕ) (s : FighterState)
    (hs : SnapshotsCover P d bound s) :
    SnapshotsCover P d bound (fighterAbortAbove d l s) := by
  unfold fighterAbortAbove
  apply snapshotsCover_foldl _ _ _ _ hs
  intro p t ht
  split
  · exact snapshotsCover_cancel _ _ _ _ ht
  · exact ht

private theorem snapshotsCover_allocate (l : ℕ) (kind : DirectiveKind) (target : ℕ)
    (out : BitString) (s : FighterState) (hs : SnapshotsCover P d bound s) :
    SnapshotsCover P d bound (fighterAllocate d l kind target out s).1 := by
  unfold fighterAllocate
  split
  · exact hs
  · cases hf : (if target = 0 then (none : Option BitString) else
        (fighterInputs d (target - 1)).find? (fun p =>
          !s.allocated.any (fun a => a.input == p))) with
    | none => exact snapshotsCover_cancel _ _ _ _ hs
    | some input =>
      apply snapshotsCover_abortAbove l _
      exact ⟨fun b hb a ha => List.mem_append_left _ (hs.1 b hb ha), hs.2⟩

private theorem snapshotsCover_payoff (l : ℕ) (q : Coordinate) (s : FighterState)
    (hs : SnapshotsCover P d bound s) :
    SnapshotsCover P d bound (fighterPayoff P d l q s) := by
  unfold fighterPayoff
  split
  · exact hs
  · split
    · have ha := snapshotsCover_allocate l .payoff q.2 q.1 s hs
      cases he : fighterAllocate d l .payoff q.2 q.1 s with
      | mk next success =>
        simp only [he] at ha ⊢
        cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
        · exact ha
        · refine ⟨ha.1, ?_⟩
          intro p hp
          obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hp
          exact ha.2 old hold
    · exact hs

private theorem snapshotsCover_fulfillReady (l : ℕ) (s : FighterState)
    (hs : SnapshotsCover P d bound s) :
    SnapshotsCover P d bound (fighterFulfillReady P d l s) := by
  unfold fighterFulfillReady
  split
  · exact hs
  · exact snapshotsCover_foldl _ (snapshotsCover_payoff l) _ _ hs

private theorem snapshotsCover_fuelUnit (l : ℕ) (q : Coordinate) (s : FighterState)
    (hs : SnapshotsCover P d bound s) :
    SnapshotsCover P d bound (fighterFuelUnit P d l q s) := by
  unfold fighterFuelUnit
  split
  · exact hs
  · rename_i phase hp
    have hq := hs.2 phase (List.mem_of_find?_eq_some hp)
    split
    · let charged := { phase with controlledRemaining := phase.controlledRemaining - 1 }
      let index := fighterFreshString d
        (phase.indices[(phase.game d).coordinates.idxOf q]?.getD [])
      let out := pairCode (triple q.1 (q.2 - d) phase.candidate.1) index
      have ha := snapshotsCover_allocate l .fuel (levelUpper l + d) out (s.putPhase d charged)
        (snapshotsCover_putPhase s charged hs hq)
      change SnapshotsCover P d bound
        (match fighterAllocate d l .fuel (levelUpper l + d) out (s.putPhase d charged) with
          | (next, success) => if success then
            fighterFulfillReady P d l
              (next.putPhase d ((charged.insertIndex d q index).fundRequests d
                next.fulfilled))
            else next)
      cases he : fighterAllocate d l .fuel (levelUpper l + d) out (s.putPhase d charged) with
      | mk next success =>
        rw [he] at ha
        cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
        · exact ha
        · exact snapshotsCover_fulfillReady l _ (snapshotsCover_putPhase next _ ha hq)
    · exact hs

private theorem snapshotsCover_fuelUnits (l : ℕ) (q : Coordinate) (count : ℕ)
    (s : FighterState) (hs : SnapshotsCover P d bound s) :
    SnapshotsCover P d bound (fighterFuelUnits P d l q count s) := by
  induction count generalizing s with
  | zero => exact hs
  | succ count ih => exact ih _ (snapshotsCover_fuelUnit l q s hs)

private theorem snapshotsCover_dummy (l : ℕ) (s : FighterState)
    (hs : SnapshotsCover P d bound s) : SnapshotsCover P d bound (fighterDummy d l s) := by
  unfold fighterDummy
  split
  · exact hs
  · rename_i phase hp
    have hq := hs.2 phase (List.mem_of_find?_eq_some hp)
    split
    · exact hs
    · rename_i output hout
      split
      · exact hs
      · have ha := snapshotsCover_allocate l .dummy (levelInput d l) output s hs
        cases he : fighterAllocate d l .dummy (levelInput d l) output s with
        | mk next success =>
          simp only [he] at ha ⊢
          cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
          · exact ha
          · exact snapshotsCover_putPhase next _ ha hq

private theorem snapshotsCover_opponent (l : ℕ) (e : ProgramEvent) (s : FighterState)
    (hs : SnapshotsCover P d bound s) :
    SnapshotsCover P d bound (fighterOpponent P d l e s) := by
  unfold fighterOpponent
  split
  · exact hs
  · rename_i phase hp
    have hq := hs.2 phase (List.mem_of_find?_eq_some hp)
    split
    · exact hs
    · split
      · exact hs
      · split
        · exact snapshotsCover_cancel _ _ _ _ hs
        · exact snapshotsCover_fulfillReady l _ (snapshotsCover_putPhase s _ hs hq)

/-- Starting a phase at the candidate timestamp `bound` saves the working allocation list, which
by the invariant contains all allocations of the earlier ticks. -/
private theorem snapshotsCover_startPhase (l : ℕ) (c : Candidate) (s : FighterState)
    (hctime : c.2 = bound) (hs : SnapshotsCover P d bound s) :
    SnapshotsCover P d bound (fighterStartPhase P d l c s) := by
  unfold fighterStartPhase
  let waiting := fighterAbortAbove d l (fighterCancel d l .replaced l s)
  have hw : SnapshotsCover P d bound waiting :=
    snapshotsCover_abortAbove l _ (snapshotsCover_cancel l l .replaced s hs)
  apply snapshotsCover_putPhase waiting (fighter_construction P d l c waiting) hw
  intro before hb
  change (fighterState P d before).allocated ⊆ waiting.allocated
  apply hw.1 before
  change before < c.2 at hb
  rwa [hctime] at hb

private theorem snapshotsCover_flushBuffer (l : ℕ) (s : FighterState)
    (hs : SnapshotsCover P d bound s) :
    SnapshotsCover P d bound ((fighterFlushBuffer d l s).getD s) := by
  unfold fighterFlushBuffer
  cases hp : s.activeAt d l with
  | none => exact hs
  | some phase =>
    have hq := hs.2 phase (List.mem_of_find?_eq_some hp)
    simp only [bind, Option.bind_some]
    split
    · exact snapshotsCover_putPhase s _ hs hq
    · exact hs

private theorem snapshotsCover_strategyMove (l : ℕ) (s : FighterState)
    (hs : SnapshotsCover P d bound s) :
    SnapshotsCover P d bound ((fighterStrategyMove P d l s).getD s) := by
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
          have hn : SnapshotsCover P d bound next := by
            apply snapshotsCover_foldl _ _ _ _ hs
            intro qi t ht
            exact snapshotsCover_fuelUnits l qi.1 (move[qi.2]?.getD 0) t ht
          change SnapshotsCover P d bound ((match next.activeAt d l with
            | none => some next
            | some live => some (next.putPhase d
              { live with officialCode :=
                  ((phase.game d).afterMove (phase.official d) move).encode })).getD s)
          split
          · exact hn
          · rename_i live hlive
            have hq := hn.2 live (List.mem_of_find?_eq_some hlive)
            exact snapshotsCover_putPhase next _ hn hq
        · exact hs
    · exact hs

private theorem snapshotsCover_levelAction (l : ℕ) (s : FighterState)
    (hs : SnapshotsCover P d bound s) :
    SnapshotsCover P d bound ((fighterLevelAction P d l s).getD s) := by
  unfold fighterLevelAction
  cases hp : s.activeAt d l with
  | none => exact hs
  | some phase =>
    simp only [bind, Option.bind_some]
    split
    · exact snapshotsCover_dummy l s hs
    · split
      · exact snapshotsCover_payoff l _ s hs
      · cases hf : fighterFlushBuffer d l s with
        | none => exact snapshotsCover_strategyMove l s hs
        | some next =>
          have h := snapshotsCover_flushBuffer l s hs
          simpa only [hf, Option.getD_some] using h

private theorem snapshotsCover_closure (l fuel : ℕ) (s : FighterState)
    (hs : SnapshotsCover P d bound s) :
    SnapshotsCover P d bound (fighterClosure P d l fuel s) := by
  induction fuel generalizing s with
  | zero => exact hs
  | succ fuel ih =>
    simp only [fighterClosure]
    cases ha : fighterLevelAction P d l s with
    | none => exact hs
    | some next =>
      have hn := snapshotsCover_levelAction l s hs
      simp only [ha, Option.getD_some] at hn
      exact ih next hn

private theorem snapshotsCover_processLevel (l : ℕ) (s : FighterState)
    (hs : SnapshotsCover P d bound s) :
    SnapshotsCover P d bound (fighterProcessLevel P d l (eventAt P.B bound) s) := by
  unfold fighterProcessLevel fighterCloseLevel
  apply snapshotsCover_closure
  cases he : eventAt P.B bound with
  | none => exact snapshotsCover_fulfillReady l s hs
  | some e =>
    dsimp only
    split
    · exact snapshotsCover_startPhase l (e.2.2.1, e.1) _
        (canonical_enumeration_spec_sound P.B he).1 (snapshotsCover_fulfillReady l s hs)
    · exact snapshotsCover_opponent l _ _ (snapshotsCover_fulfillReady l s hs)

end AllocationSnapshots

/-- A live phase's saved allocation snapshot contains every allocation from completed ticks
strictly preceding that phase's candidate timestamp. Starts save the current graph,
and subsequent actions preserve this snapshot while the permanent graph grows. -/
theorem fighterState_allocated_subset_initialAllocations_of_lt
    (P : FighterParams) (d tick : ℕ) (hd : 1 ≤ d) (phase : FighterPhase)
    (hphase : phase ∈ (fighterState P d tick).active) :
    ∀ before < phase.candidate.2,
      (fighterState P d before).allocated ⊆ phase.initialAllocations := by
  have hall : ∀ t, ∀ p ∈ (fighterState P d t).active, PhaseSnapshotCovers P d p := by
    intro time
    induction time with
    | zero => simp [fighterState, initialFighterState]
    | succ stage ih =>
      change ∀ p ∈ (fighter_actions P d (stage + 1) (fighterState P d stage)).active,
        PhaseSnapshotCovers P d p
      unfold fighter_actions
      simp only [show ¬ d = 0 by omega, ↓reduceIte]
      let current := { fighterState P d stage with
        tick := stage + 1
        schedule := masterState P.B (stage + 1) }
      have hc : SnapshotsCover P d (stage + 1) current := by
        refine ⟨?_, ih⟩
        intro before hb
        exact (fighterState_tables_mono P d before stage hd (by omega)).1
      exact (snapshotsCover_foldl
        (fun l s => fighterProcessLevel P d l (eventAt P.B (stage + 1)) s)
        (fun l s => snapshotsCover_processLevel l s) _ current hc).2
  exact hall tick phase hphase

/-- Reading a saved successful allocation gives a positive initial answer at every threshold
large enough for its directive description, including coordinates outside the referee tree. -/
private theorem initialAnswer_eq_true_of_mem_initialAllocations
    (P : FighterParams) (d : ℕ) (hd : 1 ≤ d) (phase : FighterPhase)
    (q : Coordinate) (a : AllocatedDirective) (ha : a ∈ phase.initialAllocations)
    (hlen : a.input.length + 1 ≤ q.2) (hout : a.output = q.1) :
    phase.initialAnswer P d q = true := by
  have hpos : 1 ≤ q.2 := by omega
  have hm : a ∈ phase.initialAllocations.filter
      (fun a => decide (a.input.length ≤ q.2 - 1)) :=
    List.mem_filter.mpr ⟨ha, decide_eq_true (by omega)⟩
  have hx : q.1 ∈ fighterStageOutputs P d q.2 phase.candidate.2
      phase.initialAllocations := by
    simp only [fighterStageOutputs, fighterStageOutputList, List.mem_toFinset,
      List.mem_eraseDups, List.mem_append]
    right
    simp only [hpos, hd, and_self, ↓reduceIte]
    exact List.mem_map.mpr ⟨a, hm, hout⟩
  simp [FighterPhase.initialAnswer, normalizedAnswer, hx]

/-- A funded retained pair is safe, eventually fulfilled globally, and visible initially if old.
Blueprint node `constr:realization`. Survival is assumed only through the funding tick;
true-marker stability and affordability ensure that the later request is not discarded. -/
theorem true_marker_funded_request_realized
    (P : FighterParams) (C cGap cRank d₀ d l tick : ℕ)
    (hfixed : FighterFixedConstants P C cGap cRank d₀)
    (hgood : GoodPadding P d₀ cRank cGap d) (hlate : LateAdmissibleOccurrence P d l)
    (hsurvives : TrueMarkerPhaseSurvives P d l tick)
    (phase : FighterPhase) (hphase : TrueMarkerPhaseAt P d l tick phase)
    (x : BitString) (r : ℕ) (hq : (x, r) ∈ phase.J d)
    (hfunded : (phase.game d).price (x, r) ≤ (phase.indicesAt d (x, r)).card) :
    plainK P.B.V x ≤ (r - d / 2 : ℕ) ∧
    (∃ later ≥ tick, (x, r) ∈ (fighterState P d later).fulfilled) ∧
    (∀ before < markerTick P.B (levelScale l),
      (x, r) ∈ (fighterState P d before).fulfilled → phase.initialAnswer P d (x, r) = true) := by
  have hactive : phase ∈ (fighterState P d tick).active :=
    List.mem_of_find?_eq_some hphase.2.2.2
  obtain ⟨hJ, hprices⟩ :=
    active_phase_game_tables P d tick phase hactive
  rw [hphase.2.1] at hJ
  have hret := hJ ▸ hq
  have hcount := indicesAt_card_le_extensionCount
    P cRank d l tick (Nat.sqrt d) hgood.positive hlate.1 hfixed.rank
      hgood.rank_slack phase hphase x r hq
  have hprice := hprices (x, r) hq
  rw [hphase.2.1, hphase.2.2.1] at hprice
  have hpriced : compute_extension_price P.B P.lam P.n₀ (levelScale l)
      (markerCandidate P.B (levelScale l)) x (r - d) ≤
      extensionCount P.B (levelScale l) (Nat.sqrt d)
        (triple x (r - d) (lastProgram P.B (levelScale l))) := by
    rw [← hprice]
    exact hfunded.trans hcount
  have hsafe := plainK_le_of_extension_price_le_count
    P cGap d l hgood.positive hgood.even hlate.1 hfixed.price.1
      hgood.price_slack x r hret hpriced
  refine ⟨hsafe, ?_, ?_⟩
  · rcases mem_fulfilled_or_pending_of_funded
        P d tick phase hactive (x, r) hq hfunded with hdone | hpend
    · exact ⟨tick, le_rfl, hdone⟩
    · have hr : d / 2 ≤ r := by
        obtain ⟨k, hk, hnontrivial, hlow, hhigh⟩ :=
          (mem_finite_referee_coordinates _ _ _ x r).mp hret
        dsimp only [levelInput] at hlow
        omega
      obtain ⟨later, hle, htest⟩ := exists_tick_fighterSafe_of_plainK_le
        P d tick x r hr hsafe
      have hsurvlater := trueMarkerPhaseSurvives_of_le
        P d l tick hgood.positive hlate
          (hfixed.capacity d hgood.capacity_threshold hgood.even) hsurvives later hle
      rcases pending_mem_fulfilled_or_pending_of_le
          P d l tick later hgood.positive hle hsurvlater phase hphase (x, r) hpend with
        hdone | ⟨next, hnext, hpend⟩
      · exact ⟨later, hle, hdone⟩
      · refine ⟨later, hle, mem_fulfilled_of_pending_safe
          P d later l next hnext.2.2.2 (x, r) hpend ?_⟩
        rw [fighterState_tick P d later hgood.positive]
        exact htest
  · intro before hbefore hdone
    obtain ⟨a, ha, hlen, hout⟩ :=
      exists_allocation_of_mem_fulfilled P d before (x, r) hdone
    have htime : before < phase.candidate.2 := by
      rw [hphase.2.2.1]
      exact hbefore
    have hinitial := fighterState_allocated_subset_initialAllocations_of_lt
      P d tick hgood.positive phase hactive before htime ha
    exact initialAnswer_eq_true_of_mem_initialAllocations P d hgood.positive
      phase (x, r) a hinitial hlen.le hout

end Kolmogorov.Milovanov
