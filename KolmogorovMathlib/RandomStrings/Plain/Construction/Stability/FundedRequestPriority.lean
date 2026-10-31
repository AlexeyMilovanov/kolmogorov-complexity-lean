/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.Padding
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.SettledLowerFrames
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.SettledLowerLevels

/-!
# Priority stability of a surviving true-marker phase

Once a true-marker phase of level `l` survives, no smaller level can still destroy it by
priority. This module proves the corresponding statement for the fighter construction:
`ended_reason_ne_replaced_and_aborted_of_trueMarkerPhaseSurvives` shows that, from the
surviving tick on, no completed state archives the phase with the end reasons `replaced` or
`aborted`. It uses no rank, price, funding or future-survival premise; it is used in
`FundedRequest` together with the exclusion of the opponent budget and of saturation.

The argument runs along the schedule of one numerical tick, in which the active levels are
serviced in increasing order, all on a long event (longer than the level scale):

* a long event has neither a lower owner nor a lower opponent tuple, and the safety tests of
  the pending requests of lower levels lie below the protected scale, so they are unchanged
  by the tick; with the completed fixpoint of the previous tick this makes all lower levels
  quiescent, and their service is the identity;
* a service at or above the level cannot add a replacement or abortion record for the phase:
  abortion targets lie strictly above their issuing level, and a same-level start fails its
  candidate-length guard.
-/

namespace Kolmogorov.Milovanov

/-! ### Quiescent lower levels -/

/-- Advancing the master clock through a long event leaves every lower level at its completed
fixpoint. Its pending safety tests lie below its upper endpoint, hence below the protected
marker scale. -/
private lemma fighterLevelAction_advance_eq_none
    (P : FighterParams) (d l t : ℕ) (hd : 1 ≤ d)
    (hlong : ∀ e, eventAt P.B (t + 1) = some e → levelScale l < e.2.2.1.length) :
    ∀ j < l, fighterLevelAction P d j
      { fighterState P d t with tick := t + 1, schedule := masterState P.B (t + 1) } = none := by
  intro j hj
  have hb := fighterState_tick_and_requestRanges P d t hd
  refine fighterLevelAction_eq_none_of_advance P d j _ _ _ (fun phase hphase q hq ↦ ?_)
    (fighterLevelAction_fighterState_eq_none P d t j)
  have hbound := (hb.2 phase (List.mem_of_find?_eq_some hphase)).2 q hq
  have hupper := levelUpper_le_levelLower j l hj
  have hscale : levelLower l ≤ levelScale l := tower_le_tower (by omega)
  have hqbound : q.2 - halfPadding d ≤ levelScale l := by
    rw [FighterState.level_eq_of_activeAt_eq_some hphase] at hbound
    omega
  rw [hb.1]
  simpa only [Nat.add_sub_cancel] using
    fighterSafe_eq_pred_of_long_event P d (t + 1) (levelScale l) hlong q hqbound

/-! ### Services at or above the protected level -/

/-- No completed phase of level `l` with candidate `c` is archived with the end reason
`replaced` or `aborted`. -/
private def NoReplacedOrAborted (l : ℕ) (c : Candidate) (state : FighterState) : Prop :=
  ∀ e ∈ state.ended, e.1.level = l → e.1.candidate = c →
    e.2.2.1 ≠ .replaced ∧ e.2.2.1 ≠ .aborted

namespace NoReplacedOrAborted

variable {l : ℕ} {c : Candidate} {s : FighterState}

/-- Cancelling a level other than `l`, or `l` with a reason other than `replaced` or
`aborted`, preserves the property. -/
private lemma cancel {d j cause : ℕ} {reason : PhaseEnd} (hs : NoReplacedOrAborted l c s)
    (hreason : j = l → reason ≠ .replaced ∧ reason ≠ .aborted) :
    NoReplacedOrAborted l c (fighterCancel d j reason cause s) := by
  unfold fighterCancel
  split
  · exact hs
  · rename_i phase hphase
    intro e he hl hc
    rcases List.mem_append.mp he with hold | hnew
    · exact hs e hold hl hc
    · obtain rfl := List.mem_singleton.mp hnew
      exact hreason ((FighterState.level_eq_of_activeAt_eq_some hphase).symm.trans hl)

/-- Aborting the levels above `k ≥ l` preserves the property. -/
private lemma abortAbove {d k : ℕ} (hk : l ≤ k) (hs : NoReplacedOrAborted l c s) :
    NoReplacedOrAborted l c (fighterAbortAbove d k s) := by
  unfold fighterAbortAbove
  refine foldl_preserves_invariant _ _ _ (fun t p ht ↦ ?_) hs
  split
  · exact ht.cancel (fun heq ↦ by omega)
  · exact ht

/-- Allocation at a level `k ≥ l` preserves the property. -/
private lemma allocate {d k : ℕ} (hk : l ≤ k) (kind : DirectiveKind) (target : ℕ)
    (output : BitString) (hs : NoReplacedOrAborted l c s) :
    NoReplacedOrAborted l c (fighterAllocate d k kind target output s).1 := by
  unfold fighterAllocate
  split
  · exact hs
  · cases hf : (if target = 0 then (none : Option BitString) else
        (fighterInputs d (target - 1)).find? (fun p =>
          !s.allocated.any (fun a => a.input == p))) with
    | none => exact cancel hs (fun _ ↦ ⟨by decide, by decide⟩)
    | some input => exact abortAbove hk hs

/-- Paying off a request at a level `k ≥ l` preserves the property. -/
private lemma payoff {P : FighterParams} {d k : ℕ} (hk : l ≤ k) (q : Coordinate)
    (hs : NoReplacedOrAborted l c s) :
    NoReplacedOrAborted l c (fighterPayoff P d k q s) := by
  unfold fighterPayoff
  split
  · exact hs
  · split
    · have ha := allocate (d := d) hk .payoff q.2 q.1 hs
      cases he : fighterAllocate d k .payoff q.2 q.1 s with
      | mk next success =>
        simp only [he] at ha ⊢
        cases success <;> exact ha
    · exact hs

/-- Fulfilling the ready requests of a level `k ≥ l` preserves the property. -/
private lemma fulfillReady {P : FighterParams} {d k : ℕ} (hk : l ≤ k)
    (hs : NoReplacedOrAborted l c s) :
    NoReplacedOrAborted l c (fighterFulfillReady P d k s) := by
  unfold fighterFulfillReady
  split
  · exact hs
  · exact foldl_preserves_invariant _ _ _ (fun t q ht ↦ payoff hk q ht) hs

/-- One fuel unit at a level `k ≥ l` preserves the property. -/
private lemma fuelUnit {P : FighterParams} {d k : ℕ} (hk : l ≤ k) (q : Coordinate)
    (hs : NoReplacedOrAborted l c s) :
    NoReplacedOrAborted l c (fighterFuelUnit P d k q s) := by
  unfold fighterFuelUnit
  split
  · exact hs
  · rename_i phase hp
    split
    · let charged := { phase with controlledRemaining := phase.controlledRemaining - 1 }
      let index := fighterFreshString d
        (phase.indices[(phase.game d).coordinates.idxOf q]?.getD [])
      let out := pairCode (triple q.1 (q.2 - d) phase.candidate.1) index
      have ha := allocate (d := d) hk .fuel (levelUpper k + d) out (s := s.putPhase d charged)
        hs
      change NoReplacedOrAborted l c
        (match fighterAllocate d k .fuel (levelUpper k + d) out (s.putPhase d charged) with
          | (next, success) => if success then
            fighterFulfillReady P d k
              (next.putPhase d ((charged.insertIndex d q index).fundRequests d next.fulfilled))
            else next)
      cases he : fighterAllocate d k .fuel (levelUpper k + d) out (s.putPhase d charged) with
      | mk next success =>
        rw [he] at ha
        cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
        · exact ha
        · exact fulfillReady hk ha
    · exact hs

/-- Several consecutive fuel units at a level `k ≥ l` preserve the property. -/
private lemma fuelUnits {P : FighterParams} {d k : ℕ} (hk : l ≤ k) (q : Coordinate)
    (count : ℕ) (hs : NoReplacedOrAborted l c s) :
    NoReplacedOrAborted l c (fighterFuelUnits P d k q count s) := by
  induction count generalizing s with
  | zero => exact hs
  | succ count ih => exact ih (fuelUnit hk q hs)

/-- Allocating the dummy of a level `k ≥ l` preserves the property. -/
private lemma dummy {d k : ℕ} (hk : l ≤ k) (hs : NoReplacedOrAborted l c s) :
    NoReplacedOrAborted l c (fighterDummy d k s) := by
  unfold fighterDummy
  split
  · exact hs
  · split
    · exact hs
    · split
      · exact hs
      · have ha := allocate (d := d) hk .dummy (levelInput d k) ‹_› hs
        cases he : fighterAllocate d k .dummy (levelInput d k) ‹_› s with
        | mk next success =>
          simp only [he] at ha ⊢
          cases success <;> exact ha

/-- Reacting to an opponent event at a level `k ≥ l` preserves the property. -/
private lemma opponent {P : FighterParams} {d k : ℕ} (hk : l ≤ k) (e : ProgramEvent)
    (hs : NoReplacedOrAborted l c s) :
    NoReplacedOrAborted l c (fighterOpponent P d k e s) := by
  unfold fighterOpponent
  split
  · exact hs
  · split
    · exact hs
    · split
      · exact hs
      · split
        · exact cancel hs (fun _ ↦ ⟨by decide, by decide⟩)
        · exact fulfillReady hk hs

/-- Starting a phase at a level `k > l` preserves the property. -/
private lemma startPhase {P : FighterParams} {d k : ℕ} (hk : l < k) (candidate : Candidate)
    (hs : NoReplacedOrAborted l c s) :
    NoReplacedOrAborted l c (fighterStartPhase P d k candidate s) := by
  unfold fighterStartPhase
  exact abortAbove hk.le (cancel hs (fun heq ↦ by omega))

/-- Flushing the buffer of a level preserves the property, which concerns only `ended`. -/
private lemma flushBuffer {d k : ℕ} (hs : NoReplacedOrAborted l c s) :
    NoReplacedOrAborted l c ((fighterFlushBuffer d k s).getD s) := by
  unfold fighterFlushBuffer
  cases s.activeAt d k with
  | none => exact hs
  | some phase =>
    simp only [bind, Option.bind_some]
    split <;> exact hs

/-- The controlled strategy move of a level `k ≥ l` preserves the property. -/
private lemma strategyMove {P : FighterParams} {d k : ℕ} (hk : l ≤ k)
    (hs : NoReplacedOrAborted l c s) :
    NoReplacedOrAborted l c ((fighterStrategyMove P d k s).getD s) := by
  unfold fighterStrategyMove
  cases s.activeAt d k with
  | none => exact hs
  | some phase =>
    simp only [bind, Option.bind_some]
    split
    · cases hm : (phase.game d).strategy (phase.official d) with
      | none => exact hs
      | some move =>
        simp only [Option.bind_some]
        split
        · have hn := foldl_preserves_invariant (Good := NoReplacedOrAborted l c)
            (f := fun s (qi : Coordinate × ℕ) ↦
              fighterFuelUnits P d k qi.1 (move[qi.2]?.getD 0) s)
            (phase.game d).coordinates.zipIdx (fun t qi ht ↦ fuelUnits hk qi.1 _ ht) hs
          split <;> exact hn
        · exact hs
    · exact hs

/-- One enabled action of a level `k ≥ l` preserves the property. -/
private lemma levelAction {P : FighterParams} {d k : ℕ} (hk : l ≤ k)
    (hs : NoReplacedOrAborted l c s) :
    NoReplacedOrAborted l c ((fighterLevelAction P d k s).getD s) := by
  unfold fighterLevelAction
  cases s.activeAt d k with
  | none => exact hs
  | some phase =>
    simp only [bind, Option.bind_some]
    split
    · exact dummy hk hs
    · split
      · exact payoff hk _ hs
      · cases hf : fighterFlushBuffer d k s with
        | none => exact strategyMove hk hs
        | some next => simpa only [hf, Option.getD_some] using flushBuffer (d := d) (k := k) hs

/-- Closing a level `k ≥ l` under its enabled actions preserves the property. -/
private lemma closure {P : FighterParams} {d k : ℕ} (hk : l ≤ k) (fuel : ℕ)
    (hs : NoReplacedOrAborted l c s) :
    NoReplacedOrAborted l c (fighterClosure P d k fuel s) := by
  induction fuel generalizing s with
  | zero => exact hs
  | succ fuel ih =>
    simp only [fighterClosure]
    cases ha : fighterLevelAction P d k s with
    | none => exact hs
    | some next =>
      have hn := levelAction (P := P) (d := d) hk hs
      simp only [ha, Option.getD_some] at hn
      exact ih hn

/-- A service at or above the protected level `l` cannot add a replacement or abortion record
there when its event is longer than the protected marker scale. Abortion targets are strictly
above their issuing level, and same-level initialization fails its candidate-length guard. -/
private theorem processLevel
    (P : FighterParams) (d k : ℕ) (hk : l ≤ k) (event : Option TimedEvent)
    (hlong : ∀ e, event = some e → levelScale l < e.2.2.1.length)
    (hs : NoReplacedOrAborted l c s) :
    NoReplacedOrAborted l c (fighterProcessLevel P d k event s) := by
  unfold fighterProcessLevel fighterCloseLevel
  refine closure hk _ ?_
  have hc := fulfillReady (P := P) (d := d) hk hs
  cases event with
  | none => exact hc
  | some e =>
    dsimp only
    split
    · rename_i hguard
      have hlen := hlong e rfl
      exact startPhase (lt_of_le_of_ne hk (fun heq ↦ by rw [← heq] at hguard; omega)) _ hc
    · exact opponent hk _ hc

/-- An increasing list of services, all at or above the protected level, preserves the
property. -/
private lemma foldl_processLevel
    (P : FighterParams) (d : ℕ) (event : Option TimedEvent)
    (hlong : ∀ e, event = some e → levelScale l < e.2.2.1.length)
    (levels : List ℕ) (hlevels : ∀ k ∈ levels, l ≤ k) (hs : NoReplacedOrAborted l c s) :
    NoReplacedOrAborted l c (levels.foldl (fun s k => fighterProcessLevel P d k event s) s) := by
  induction levels generalizing s with
  | nil => exact hs
  | cons k levels ih =>
    exact ih (fun j hj => hlevels j (List.mem_cons_of_mem k hj))
      (processLevel P d k (hlevels k (by simp)) event hlong hs)

/-- An increasing service list first skips the quiet lower levels. All remaining services are
at or above the protected level and preserve the property. -/
private lemma sorted_foldl_processLevel
    (P : FighterParams) (d : ℕ) (event : Option TimedEvent)
    (hlong : ∀ e, event = some e → levelScale l < e.2.2.1.length)
    (levels : List ℕ) (hsorted : levels.Pairwise (· ≤ ·))
    (hquiet : ∀ j < l, fighterLevelAction P d j s = none) (hs : NoReplacedOrAborted l c s) :
    NoReplacedOrAborted l c (levels.foldl (fun s k => fighterProcessLevel P d k event s) s) := by
  induction levels with
  | nil => exact hs
  | cons k levels ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hsorted
    by_cases hk : k < l
    · rw [List.foldl_cons, fighterProcessLevel_eq_self_of_levelAction_eq_none P d k event s
        (hquiet k hk) (fun e he ↦
          fighterOwner_ne_and_fighterOpponentTuple_eq_none_of_levelLower_lt d l k hk e
          ((tower_le_tower (by omega) : levelLower l ≤ levelScale l).trans_lt (hlong e he)))]
      exact ih htail
    · refine foldl_processLevel P d event hlong (k :: levels) (fun j hj => ?_) hs
      rcases List.mem_cons.mp hj with rfl | hj
      · omega
      · have := hhead j hj
        omega

/-- One numerical tick with a long event preserves the property of the completed states. -/
private lemma fighterState_succ (P : FighterParams) (d t : ℕ) (hd : 1 ≤ d)
    (hlong : ∀ e, eventAt P.B (t + 1) = some e → levelScale l < e.2.2.1.length)
    (hs : NoReplacedOrAborted l c (fighterState P d t)) :
    NoReplacedOrAborted l c (fighterState P d (t + 1)) := by
  change NoReplacedOrAborted l c (fighter_actions P d (t + 1) (fighterState P d t))
  unfold fighter_actions
  simp only [show d ≠ 0 by omega, ite_false]
  exact sorted_foldl_processLevel P d (eventAt P.B (t + 1)) hlong _
    (List.pairwise_mergeSort' (· ≤ ·) _) (fighterLevelAction_advance_eq_none P d l t hd hlong) hs

end NoReplacedOrAborted

/-- The surviving true-marker phase of level `l` is never replaced or aborted by priority:
from the surviving tick on, no completed state archives it with the end reason `replaced` or
`aborted`. The explicit short-event hypothesis prevents same-level replacement. For every
smaller active level, admissibility puts all opponent tests and payoff safety tests below the
marker scale, and its completed closure cannot acquire new work; thus no smaller level starts
or issues a directive that aborts this phase. This is only priority stability, with no rank,
price, funding or future-survival premise.
Blueprint node `true_marker_funded_request_realized` (supporting lemma). -/
theorem ended_reason_ne_replaced_and_aborted_of_trueMarkerPhaseSurvives
    (P : FighterParams) (d l tick : ℕ) (hd : 1 ≤ d)
    (hsurvives : TrueMarkerPhaseSurvives P d l tick)
    (hquiet : ∀ t > markerTick P.B (levelScale l), ∀ i p x,
      eventAt P.B t = some (t, i, p, x) → levelScale l < p.length) :
    ∀ later ≥ tick, ∀ e ∈ (fighterState P d later).ended,
      e.1.level = l → e.1.candidate = markerCandidate P.B (levelScale l) →
        e.2.2.1 ≠ .replaced ∧ e.2.2.1 ≠ .aborted := by
  intro later hlater
  induction later, hlater using Nat.le_induction with
  | base =>
    intro e he hl hc
    exact (hsurvives.2.2.2 e he hl hc).elim
  | succ t ht ih =>
    refine NoReplacedOrAborted.fighterState_succ P d t hd (fun e he ↦ ?_) ih
    obtain ⟨u, i, p, x⟩ := e
    have hu : u = t + 1 := (canonical_enumeration_spec_sound P.B he).1
    subst u
    exact hquiet (t + 1) (lt_of_le_of_lt (hsurvives.2.1.trans ht) (Nat.lt_succ_self t))
      i p x he

end Kolmogorov.Milovanov
