/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Construction.Effective
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Sqrt

/-!
# Phase counts and target ranges of the fighter construction

This module introduces the bookkeeping notions for the accounting of the fighter
construction: `fighterPhaseCount` (phases started at a level), `fighterDirectiveCount`
(successful directives of a given kind issued by a level), `FighterActivated` (a level has
started a phase) and `FighterTargetRange` (the exact target ranges of the dummy, payoff and
fuel directives of a level, blueprint node `constr:intervals`).

It then proves the candidate-count half of the phase-count lemma (blueprint node
`constr:phasecount`): the candidates started at one level are pairwise distinct programs of
length at most `levelScale l`, so `fighterPhaseCount P d l tick < 2 ^ (levelScale l + 1)`.
The proof tracks the `started` log of the fighter state: every operation of the state machine
leaves the log untouched, except that the processing of an event appends the event's program
at its owner level.  The same description of the log shows that every logged entry is an
actual event of the canonical enumeration.

The result and the log invariant are used by `PhaseCountBounds` for the fuel accounting, and
`FighterStartLogCovers` is the history invariant used by `DummyHistory`.
-/

namespace Kolmogorov.Milovanov

/-- Number of phases started at a level, including subsequently canceled phases.
Blueprint node `constr:phasecount` (supporting definition). -/
def fighterPhaseCount (P : FighterParams) (d l tick : ℕ) : ℕ :=
  ((fighterState P d tick).started.filter (fun entry => entry.1 == l)).length

/-- Number of successful directives of a given kind issued by a given level so far.
Blueprint node `constr:phasecount` (supporting definition). -/
def fighterDirectiveCount (P : FighterParams) (d l tick : ℕ) (kind : DirectiveKind) : ℕ :=
  ((fighterState P d tick).allocated.filter (fun a =>
    decide (a.level = l ∧ a.kind = kind))).length

/-- A level is activated if a candidate has started a phase there by this tick.
Blueprint node `constr:intervals` (supporting definition).
Cancellation preserves this history. -/
def FighterActivated (P : FighterParams) (d l tick : ℕ) : Prop :=
  ∃ candidate, (l, candidate) ∈ (fighterState P d tick).started

/-- Exact dummy, payoff, and fuel target ranges, with the strict payoff upper endpoint.
Blueprint node `constr:intervals` (supporting definition). -/
def FighterTargetRange (d l : ℕ) (kind : DirectiveKind) (r : ℕ) : Prop :=
  match kind with
  | .dummy => r = levelScale l + d
  | .payoff => levelScale l + d + 1 ≤ r ∧ r < levelRangeBound l
  | .fuel => r = levelUpper l + d

/-- History invariant of a fighter state: every active phase and every phase that was granted a
dummy directive is recorded in the `started` log by its level and candidate. -/
def FighterStartLogCovers (s : FighterState) : Prop :=
  (∀ p ∈ s.active, (p.level, p.candidate) ∈ s.started) ∧
  (∀ a ∈ s.allocated, a.kind = .dummy →
    (a.level, a.candidate) ∈ s.started)

/-! ### Effect of the state operations on the `started` log -/

private lemma started_foldl_eq {α : Type} (f : α → FighterState → FighterState)
    (hf : ∀ a s, (f a s).started = s.started) (xs : List α) (s : FighterState) :
    (xs.foldl (fun s a => f a s) s).started = s.started := by
  induction xs generalizing s with
  | nil => rfl
  | cons a xs ih => exact (ih _).trans (hf a s)

private lemma putPhase_started (d : ℕ) (s : FighterState) (phase : FighterPhase) :
    (s.putPhase d phase).started = s.started := rfl

private lemma fighterCancel_started (d j : ℕ) (reason : PhaseEnd) (cause : ℕ)
    (s : FighterState) : (fighterCancel d j reason cause s).started = s.started := by
  unfold fighterCancel
  split <;> rfl

private lemma fighterAllocate_started (d j : ℕ) (kind : DirectiveKind) (target : ℕ)
    (out : BitString) (s : FighterState) :
    (fighterAllocate d j kind target out s).1.started = s.started := by
  unfold fighterAllocate
  split
  · rfl
  · cases hf : (if target = 0 then (none : Option BitString) else
        (fighterInputs d (target - 1)).find? (fun p =>
          !s.allocated.any (fun a => a.input == p))) with
    | none => exact fighterCancel_started _ _ _ _ _
    | some p => exact fighterAbortAbove_started _ _ _

private lemma fighterPayoff_started (P : FighterParams) (d j : ℕ) (q : Coordinate)
    (s : FighterState) : (fighterPayoff P d j q s).started = s.started := by
  unfold fighterPayoff
  split
  · rfl
  · split
    · have h := fighterAllocate_started d j .payoff q.2 q.1 s
      cases he : fighterAllocate d j .payoff q.2 q.1 s with
      | mk next success =>
        rw [he] at h
        cases success <;> exact h
    · rfl

private lemma fighterFulfillReady_started (P : FighterParams) (d j : ℕ) (s : FighterState) :
    (fighterFulfillReady P d j s).started = s.started := by
  unfold fighterFulfillReady
  split
  · rfl
  · exact started_foldl_eq (fun q s => fighterPayoff P d j q s) (fighterPayoff_started P d j) _ _

private lemma fighterFuelUnit_started (P : FighterParams) (d j : ℕ) (q : Coordinate)
    (s : FighterState) : (fighterFuelUnit P d j q s).started = s.started := by
  unfold fighterFuelUnit
  split
  · rfl
  · rename_i phase hs
    split
    · have h := (fighterAllocate_started d j .fuel (levelUpper j + d)
          (pairCode (triple q.1 (q.2 - d) phase.candidate.1)
            (fighterFreshString d (phase.indices[(phase.game d).coordinates.idxOf q]?.getD [])))
          _).trans (putPhase_started d s
            { phase with controlledRemaining := phase.controlledRemaining - 1 })
      dsimp only
      split
      · exact ((fighterFulfillReady_started _ _ _ _).trans (putPhase_started d _ _)).trans h
      · exact h
    · rfl

private lemma fighterFuelUnits_started (P : FighterParams) (d j : ℕ) (q : Coordinate)
    (count : ℕ) (s : FighterState) :
    (fighterFuelUnits P d j q count s).started = s.started := by
  induction count generalizing s with
  | zero => rfl
  | succ count ih => exact (ih _).trans (fighterFuelUnit_started P d j q s)

private lemma fighterDummy_started (d j : ℕ) (s : FighterState) :
    (fighterDummy d j s).started = s.started := by
  unfold fighterDummy
  split
  · rfl
  · split
    · rfl
    · rename_i output hout
      split
      · rfl
      · have h := fighterAllocate_started d j .dummy (levelInput d j) output s
        dsimp only
        split
        · exact (putPhase_started d _ _).trans h
        · exact h

private lemma fighterFlushBuffer_started (d j : ℕ) (s : FighterState) :
    ((fighterFlushBuffer d j s).getD s).started = s.started := by
  cases hs : s.activeAt d j with
  | none => simp [fighterFlushBuffer, hs]
  | some phase =>
    simp only [fighterFlushBuffer, hs, bind, Option.bind_some]
    split
    · exact putPhase_started d _ _
    · rfl

private lemma fighterStrategyMove_started (P : FighterParams) (d j : ℕ) (s : FighterState) :
    ((fighterStrategyMove P d j s).getD s).started = s.started := by
  cases hs : s.activeAt d j with
  | none => simp [fighterStrategyMove, hs]
  | some phase =>
    simp only [fighterStrategyMove, hs, bind, Option.bind_some]
    split
    · cases hm : (phase.game d).strategy (phase.official d) with
      | none => rfl
      | some move =>
        simp only [Option.bind_some]
        split
        · let next := ((phase.game d).coordinates.zipIdx).foldl (fun s (q, i) =>
            fighterFuelUnits P d j q (move[i]?.getD 0) s) s
          have hn : next.started = s.started := started_foldl_eq _
            (fun (qi : Coordinate × ℕ) t => fighterFuelUnits_started P d j qi.1 _ t) _ _
          change ((match next.activeAt d j with
            | none => some next
            | some live => some (next.putPhase d
                { live with officialCode :=
                  ((phase.game d).afterMove (phase.official d) move).encode })).getD s).started =
            s.started
          cases hlive : next.activeAt d j with
          | none => exact hn
          | some live => exact (putPhase_started d _ _).trans hn
        · rfl
    · rfl

private lemma fighterLevelAction_started (P : FighterParams) (d j : ℕ) (s : FighterState) :
    ((fighterLevelAction P d j s).getD s).started = s.started := by
  cases hs : s.activeAt d j with
  | none => simp [fighterLevelAction, hs]
  | some phase =>
    simp only [fighterLevelAction, hs, bind, Option.bind_some]
    split
    · exact fighterDummy_started d j s
    · split
      · exact fighterPayoff_started P d j _ s
      · cases hf : fighterFlushBuffer d j s with
        | none => exact fighterStrategyMove_started P d j s
        | some next => simpa only [hf] using fighterFlushBuffer_started d j s

private lemma fighterClosure_started (P : FighterParams) (d j fuel : ℕ) (s : FighterState) :
    (fighterClosure P d j fuel s).started = s.started := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
    simp only [fighterClosure]
    cases ha : fighterLevelAction P d j s with
    | none => rfl
    | some next =>
      have h := fighterLevelAction_started P d j s
      simp only [ha, Option.getD_some] at h
      exact (ih next).trans h

private lemma fighterStartPhase_started (P : FighterParams) (d j : ℕ) (candidate : Candidate)
    (s : FighterState) :
    (fighterStartPhase P d j candidate s).started = s.started ++ [(j, candidate)] := by
  have h := (fighterAbortAbove_started d j _).trans (fighterCancel_started d j .replaced j s)
  change (fighterAbortAbove d j (fighterCancel d j .replaced j s)).started ++
    [(j, candidate)] = _
  rw [h]

private lemma fighterOpponent_started (P : FighterParams) (d j : ℕ) (e : ProgramEvent)
    (s : FighterState) : (fighterOpponent P d j e s).started = s.started := by
  unfold fighterOpponent
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · split
        · exact fighterCancel_started _ _ _ _ _
        · exact (fighterFulfillReady_started _ _ _ _).trans (putPhase_started d _ _)

/-- Servicing one level either preserves the `started` log, or appends the current event's
program at its owner level, provided the program is not longer than the level's scale. -/
private lemma fighterProcessLevel_started (P : FighterParams) (d l : ℕ)
    (event : Option TimedEvent) (state : FighterState) :
    (fighterProcessLevel P d l event state).started = state.started ∨
    ∃ t i p x, event = some (t, i, p, x) ∧ fighterOwner d p.length = some l ∧
      p.length ≤ levelScale l ∧
      (fighterProcessLevel P d l event state).started = state.started ++ [(l, (p, t))] := by
  unfold fighterProcessLevel fighterCloseLevel
  cases event with
  | none =>
    exact Or.inl ((fighterClosure_started _ _ _ _ _).trans (fighterFulfillReady_started _ _ _ _))
  | some e =>
    dsimp only
    split
    · rename_i hguard
      right
      refine ⟨e.1, e.2.1, e.2.2.1, e.2.2.2, rfl, hguard.1, hguard.2.1, ?_⟩
      exact (fighterClosure_started _ _ _ _ _).trans ((fighterStartPhase_started _ _ _ _ _).trans
        (congrArg (fun log => log ++ [(l, (e.2.2.1, e.1))])
          (fighterFulfillReady_started _ _ _ _)))
    · exact Or.inl (((fighterClosure_started _ _ _ _ _).trans
        (fighterOpponent_started _ _ _ _ _)).trans (fighterFulfillReady_started _ _ _ _))

/-- A sweep over distinct levels appends at most one candidate to the `started` log: only the
owner of the current event can start it. -/
private lemma foldl_fighterProcessLevel_started (P : FighterParams) (d : ℕ)
    (event : Option TimedEvent) (state : FighterState) (levels : List ℕ)
    (hnodup : levels.Nodup) :
    (levels.foldl (fun s k => fighterProcessLevel P d k event s) state).started =
      state.started ∨
    ∃ l t i p x, event = some (t, i, p, x) ∧ l ∈ levels ∧
      fighterOwner d p.length = some l ∧ p.length ≤ levelScale l ∧
      (levels.foldl (fun s k => fighterProcessLevel P d k event s) state).started =
        state.started ++ [(l, (p, t))] := by
  induction levels generalizing state with
  | nil => exact Or.inl rfl
  | cons k levels ih =>
    obtain ⟨hk, hlevels⟩ := List.nodup_cons.mp hnodup
    simp only [List.foldl_cons]
    rcases fighterProcessLevel_started P d k event state with
      hsame | ⟨t, i, p, x, he, ho, hlen, hstart⟩
    · rcases ih _ hlevels with htail | ⟨j, t, i, p, x, he, hj, ho, hlen, htail⟩
      · exact Or.inl (htail.trans hsame)
      · right
        refine ⟨j, t, i, p, x, he, List.mem_cons_of_mem k hj, ho, hlen, ?_⟩
        rw [htail, hsame]
    · rcases ih _ hlevels with htail | ⟨j, u, m, q, y, he', hj, ho', hlen', htail⟩
      · right
        exact ⟨k, t, i, p, x, he, List.mem_cons_self, ho, hlen, htail.trans hstart⟩
      · have heq := he.symm.trans he'
        simp only [Option.some.injEq, Prod.mk.injEq] at heq
        rcases heq with ⟨rfl, rfl, rfl, rfl⟩
        have hkj : k = j := Option.some.inj (ho.symm.trans ho')
        subst j
        exact (hk hj).elim

/-- A tick clears the `started` log at padding zero, or preserves it, or appends a single
candidate emitted at that tick by the master enumeration, whose length is within the scale of
its owner level. -/
private lemma fighter_actions_started (P : FighterParams) (d tick : ℕ) (state : FighterState) :
    (fighter_actions P d tick state).started = [] ∨
    (fighter_actions P d tick state).started = state.started ∨
    ∃ l i p x, eventAt P.B tick = some (tick, i, p, x) ∧
      fighterOwner d p.length = some l ∧ p.length ≤ levelScale l ∧
      (fighter_actions P d tick state).started = state.started ++ [(l, (p, tick))] := by
  unfold fighter_actions
  split
  · exact Or.inl rfl
  · right
    let current := { state with tick := tick, schedule := masterState P.B tick }
    let event := eventAt P.B tick
    let owner := event.bind (fun e => fighterOwner d e.2.2.1.length)
    let levels := (current.active.map FighterPhase.level ++ owner.toList).eraseDups
    have hnodup : (levels.mergeSort (· ≤ ·)).Nodup := by
      rw [List.nodup_mergeSort]
      exact nodup_eraseDups_list _
    rcases foldl_fighterProcessLevel_started P d event current (levels.mergeSort (· ≤ ·))
      hnodup with hsame | ⟨l, t, i, p, x, he, hl, ho, hlen, hstart⟩
    · exact Or.inl hsame
    · have ht : t = tick := (canonical_enumeration_spec_sound P.B he).1
      subst t
      exact Or.inr ⟨l, i, p, x, he, ho, hlen, hstart⟩

/-- Every entry of the `started` log records an actual event of the canonical enumeration,
emitted no later than the current tick. -/
lemma fighterState_started_event (P : FighterParams) (d tick : ℕ) :
    ∀ entry ∈ (fighterState P d tick).started,
      entry.2.2 ≤ tick ∧ ∃ i x,
        eventAt P.B entry.2.2 = some (entry.2.2, i, entry.2.1, x) := by
  induction tick with
  | zero => simp [fighterState, initialFighterState]
  | succ tick ih =>
    change ∀ entry ∈ (fighter_actions P d (tick + 1) (fighterState P d tick)).started, _
    rcases fighter_actions_started P d (tick + 1) (fighterState P d tick) with
      hempty | hsame | ⟨l, i, p, x, he, ho, hlen, hstart⟩
    · rw [hempty]
      simp
    · rw [hsame]
      intro entry hentry
      exact ⟨(ih entry hentry).1.trans (Nat.le_succ _), (ih entry hentry).2⟩
    · rw [hstart]
      intro entry hentry
      rcases List.mem_append.mp hentry with hold | hnew
      · exact ⟨(ih entry hold).1.trans (Nat.le_succ _), (ih entry hold).2⟩
      · obtain rfl := List.mem_singleton.mp hnew
        exact ⟨le_rfl, i, x, he⟩

/-- A program logged at a level is no longer than the level's scale. -/
private lemma fighterState_started_length_le (P : FighterParams) (d tick : ℕ) :
    ∀ entry ∈ (fighterState P d tick).started, entry.2.1.length ≤ levelScale entry.1 := by
  induction tick with
  | zero => simp [fighterState, initialFighterState]
  | succ tick ih =>
    change ∀ entry ∈ (fighter_actions P d (tick + 1) (fighterState P d tick)).started, _
    rcases fighter_actions_started P d (tick + 1) (fighterState P d tick) with
      hempty | hsame | ⟨l, i, p, x, he, ho, hlen, hstart⟩
    · rw [hempty]
      simp
    · rw [hsame]
      exact ih
    · rw [hstart]
      intro entry hentry
      rcases List.mem_append.mp hentry with hold | hnew
      · exact ih entry hold
      · obtain rfl := List.mem_singleton.mp hnew
        exact hlen

/-- The programs started at one level are pairwise distinct. -/
private lemma fighterState_startedPrograms_nodup (P : FighterParams) (d l tick : ℕ) :
    (((fighterState P d tick).started.filter (fun entry => entry.1 == l)).map
      (fun entry => entry.2.1)).Nodup := by
  induction tick with
  | zero => simp [fighterState, initialFighterState]
  | succ tick ih =>
    change (((fighter_actions P d (tick + 1) (fighterState P d tick)).started.filter
      (fun entry => entry.1 == l)).map (fun entry => entry.2.1)).Nodup
    rcases fighter_actions_started P d (tick + 1) (fighterState P d tick) with
      hempty | hsame | ⟨k, i, p, x, he, ho, hlen, hstart⟩
    · rw [hempty]
      simp
    · rw [hsame]
      exact ih
    · rw [hstart]
      have hfresh : p ∉ (((fighterState P d tick).started.filter
          (fun entry => entry.1 == l)).map (fun entry => entry.2.1)) := by
        intro hp
        obtain ⟨entry, hentry, hprog⟩ := List.mem_map.mp hp
        obtain ⟨hmem, hlevel⟩ := List.mem_filter.mp hentry
        obtain ⟨hle, j, y, hold⟩ := fighterState_started_event P d tick entry hmem
        rw [hprog] at hold
        have ht := (canonical_enumeration_spec_unique P.B he hold).1
        omega
      by_cases hkl : k = l
      · subst k
        have happend : ((((fighterState P d tick).started.filter
            (fun entry => entry.1 == l)).map (fun entry => entry.2.1)) ++ [p]).Nodup := by
          rw [List.nodup_append]
          refine ⟨ih, List.nodup_singleton _, ?_⟩
          intro a ha b hb hab
          obtain rfl := List.mem_singleton.mp hb
          exact hfresh (hab ▸ ha)
        simpa [List.filter_append, List.map_append] using happend
      · simpa [List.filter_append, hkl] using ih

/-! ### Counting short bit strings -/

/-- A bijection from bit strings to positive numbers, in length-lexicographic order. -/
private def bitStringRank : BitString → ℕ
  | [] => 0
  | false :: bs => 1 + 2 * bitStringRank bs
  | true :: bs => 2 + 2 * bitStringRank bs

private lemma bitStringRank_inj (a b : BitString) (h : bitStringRank a = bitStringRank b) :
    a = b := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => rfl
    | cons c bs => cases c <;> (simp only [bitStringRank] at h; omega)
  | cons c as ih =>
    cases b with
    | nil => cases c <;> (simp only [bitStringRank] at h; omega)
    | cons c' bs =>
      cases c <;> cases c' <;> simp only [bitStringRank] at h <;>
        first | omega | rw [ih bs (by omega)]

private lemma bitStringRank_lt (bs : BitString) :
    bitStringRank bs + 1 < 2 ^ (bs.length + 1) := by
  induction bs with
  | nil => simp [bitStringRank]
  | cons c bs ih =>
    have h2 : 2 ^ (bs.length + 1 + 1) = 2 * 2 ^ (bs.length + 1) := pow_succ' 2 _
    cases c <;> simp only [bitStringRank, List.length_cons] <;> omega

/-- There are fewer than `2 ^ (n + 1)` distinct bit strings of length at most `n`. -/
private lemma length_lt_two_pow_of_nodup (n : ℕ) (xs : List BitString) (hnodup : xs.Nodup)
    (hlen : ∀ c ∈ xs, c.length ≤ n) : xs.length < 2 ^ (n + 1) := by
  have hnd : (xs.map bitStringRank).Nodup := hnodup.map (fun a b h => bitStringRank_inj a b h)
  have hsub : (xs.map bitStringRank).toFinset ⊆ Finset.range (2 ^ (n + 1) - 1) := by
    intro x hx
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
    have h1 := bitStringRank_lt c
    have h2 : 2 ^ (c.length + 1) ≤ 2 ^ (n + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by have := hlen c hc; omega)
    rw [Finset.mem_range]
    omega
  have hcard := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hnd, List.length_map, Finset.card_range] at hcard
  have hpos : 0 < 2 ^ (n + 1) := Nat.two_pow_pos _
  omega

/-- The number of phases started at a level is below `2 ^ (levelScale l + 1)`, since the started
candidates are distinct programs of length at most `levelScale l`.
Blueprint node `constr:phasecount` (candidate count). -/
lemma fighterPhaseCount_lt_two_pow (P : FighterParams) (d l tick : ℕ) :
    fighterPhaseCount P d l tick < 2 ^ (levelScale l + 1) := by
  have hlen : ∀ c ∈ (((fighterState P d tick).started.filter (fun entry => entry.1 == l)).map
      (fun entry => entry.2.1)), c.length ≤ levelScale l := by
    intro c hc
    obtain ⟨entry, hentry, rfl⟩ := List.mem_map.mp hc
    obtain ⟨hmem, hl⟩ := List.mem_filter.mp hentry
    have h := fighterState_started_length_le P d tick entry hmem
    rwa [beq_iff_eq.mp hl] at h
  have hcount := length_lt_two_pow_of_nodup (levelScale l) _
    (fighterState_startedPrograms_nodup P d l tick) hlen
  rwa [List.length_map] at hcount

end Kolmogorov.Milovanov
