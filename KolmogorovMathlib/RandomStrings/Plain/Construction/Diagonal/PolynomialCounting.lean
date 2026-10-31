/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Construction.Diagonal.OracleAgreement

/-!
# The constructed oracle defeats polynomial counting

This module concludes the diagonal argument of the construction. For a late admissible
occurrence of a referee-and-bound pair in the fixed family, the final virtual output of the
true-marker phase agrees with the actual normalized referee output
(`true_marker_final_output_agrees`, blueprint node `constr:agreement`). The controlled player of
that phase pursues an objective which, depending on whether a dummy was issued, forces the output
to differ from the true count of strings of bounded complexity.

The main result is `constructed_oracle_defeats_polynomial_counting` (blueprint node
`constr:diagonal`): no referee of the family, run with the constructed oracle, computes the
cumulative count `{x | plainK (fighterU P d) x ≤ m}.ncard` for all `m`. It is the diagonalization
step used by `Main` to show that the cumulative complexity oracle of the optimal decompressor does
not compute the halting language in polynomial time. The supporting definition
`RefereeFamily.Contains` expresses that a referee and its bound are represented in the family.

Along the way we prove that every phase of every reachable state keeps the role (equality or
inequality player) chosen at initialization, which is the invariant tying the controlled
objective to the dummy flag.
-/

namespace Kolmogorov.Milovanov

/-- The eventually constant virtual output is the actual normalized referee output.
Blueprint node `constr:agreement`. Finite-tree extensionality transfers the querywise result. -/
theorem true_marker_final_output_agrees (P : FighterParams) (C cGap cRank d₀ d l : ℕ)
    (hfixed : FighterFixedConstants P C cGap cRank d₀)
    (hgood : GoodPadding P d₀ cRank cGap d) (hlate : LateAdmissibleOccurrence P d l) :
    fighterFinalVirtualOutput P d l (markerCandidate P.B (levelScale l)) =
      refereeSetOutput (constructedLiteralConstant P.literal d)
        (P.family.tree d l (levelInput d l)) (fighterOracle P d) := by
  obtain ⟨s, _, hs⟩ :=
    true_marker_virtual_output_stabilizes P C cGap cRank d₀ d l hfixed hgood hlate
  obtain ⟨t, _, ht⟩ :=
    true_marker_virtual_actual_oracle_agreement P C cGap cRank d₀ d l hfixed hgood hlate
  rw [← (hs (max s t) (le_max_left _ _)).2]
  exact QueryTree.eval_eq_of_agree _ _ _ (ht (max s t) (le_max_right _ _))

/-- A referee-and-bound pair is represented at a positive index of the abstract family.
Blueprint node `constr:diagonal` (supporting definition). The index is a membership witness,
not the late admissible level eventually chosen to diagonalize against this pair. -/
def RefereeFamily.Contains (family : RefereeFamily) (d : ℕ)
    (M : ℕ → QueryTree) (p : ℕ → ℕ) : Prop :=
  ∃ index : ℕ, 1 ≤ index ∧ family.tree d index = M ∧ family.bound index = p

/-- A late admissible repetition of a represented referee and bound exists: the repetition
computes the same tree and the same bound as the represented pair. -/
private theorem exists_late_admissible_occurrence_of_contains
    (P : FighterParams) (C cGap cRank d₀ d : ℕ)
    (hfixed : FighterFixedConstants P C cGap cRank d₀)
    (hgood : GoodPadding P d₀ cRank cGap d)
    (M : ℕ → QueryTree) (p : ℕ → ℕ) (hmember : P.family.Contains d M p) :
    ∃ l, LateAdmissibleOccurrence P d l ∧
      P.family.tree d l = M ∧ P.family.bound l = p := by
  obtain ⟨index, hindex, htree, hbound⟩ := hmember
  obtain ⟨l₀, hl₀⟩ :=
    lower_levels_settled_at_true_marker P C cGap cRank d₀ d hfixed hgood
  obtain ⟨l, hl, htree', hbound', hadm⟩ :=
    clocked_machine_has_late_admissible_occurrence P.family P.literal.cV P.n₀ index
      P.threshold hindex d hgood.positive l₀
  exact ⟨l, ⟨hadm, (hl₀ l hl.le hadm).1.1⟩,
    htree'.trans htree, hbound'.trans hbound⟩

/-- A phase has a consistent role: its controlled game seeks equality exactly when its optional
dummy is present, and an issued dummy is always present. -/
private def FighterPhase.RoleConsistent (d : ℕ) (p : FighterPhase) : Prop :=
  (p.game d).equalityPlayer = !p.dummy.isSome ∧
    (p.dummyIssued = true → p.dummy.isSome = true)

/-- A state has consistent roles when all of its active phases do. -/
private def FighterState.RoleConsistent (d : ℕ) (s : FighterState) : Prop :=
  ∀ p ∈ s.active, p.RoleConsistent d

/-- At initialization the controlled game seeks equality exactly when a dummy is chosen,
and no dummy has yet been issued. This holds for every candidate and finite state. -/
private theorem FighterPhase.roleConsistent_fighter_construction
    (P : FighterParams) (d l : ℕ) (candidate : Candidate) (state : FighterState) :
    (fighter_construction P d l candidate state).RoleConsistent d := by
  dsimp only [FighterPhase.RoleConsistent, fighter_construction, FighterPhase.fundRequests,
    FighterPhase.game]
  rw [decode_encode_counter_game]
  unfold FiniteCounterGame.controlWinningPlayer
  split <;> simp_all [FiniteCounterGame.exchangeRoles, finite_counter_game]

/-- The phase found at a level of a state with consistent roles has a consistent role. -/
private theorem FighterState.RoleConsistent.of_activeAt {d l : ℕ} {s : FighterState}
    {p : FighterPhase} (hs : s.RoleConsistent d) (hp : s.activeAt d l = some p) :
    p.RoleConsistent d :=
  hs p (List.mem_of_find?_eq_some hp)

/-- Replacing the phase of a level by a consistent one preserves consistent roles. -/
private theorem FighterState.RoleConsistent.putPhase {d : ℕ} {s : FighterState}
    {p : FighterPhase} (hs : s.RoleConsistent d) (hp : p.RoleConsistent d) :
    (s.putPhase d p).RoleConsistent d := by
  intro next hn
  rcases List.mem_cons.mp hn with rfl | hn
  · exact hp
  · exact hs next (List.mem_filter.mp hn).1

/-- Cancelling phases preserves consistent roles. -/
private theorem FighterState.RoleConsistent.cancel {d : ℕ} {s : FighterState}
    (hs : s.RoleConsistent d) (l cause : ℕ) (reason : PhaseEnd) :
    (fighterCancel d l reason cause s).RoleConsistent d := by
  unfold fighterCancel
  split
  · exact hs
  · intro p hp
    exact hs p (List.mem_filter.mp hp).1

/-- Aborting the phases above a level preserves consistent roles. -/
private theorem FighterState.RoleConsistent.abortAbove {d : ℕ} {s : FighterState}
    (hs : s.RoleConsistent d) (l : ℕ) :
    (fighterAbortAbove d l s).RoleConsistent d := by
  unfold fighterAbortAbove
  refine foldl_preserves_invariant (FighterState.RoleConsistent d) _ _ (fun t p ht ↦ ?_) hs
  split
  · exact ht.cancel _ _ _
  · exact ht

/-- Allocating a directive preserves consistent roles. -/
private theorem FighterState.RoleConsistent.allocate {d : ℕ} {s : FighterState}
    (hs : s.RoleConsistent d) (l : ℕ) (kind : DirectiveKind) (target : ℕ) (out : BitString) :
    (fighterAllocate d l kind target out s).1.RoleConsistent d := by
  unfold fighterAllocate
  split
  · exact hs
  · cases hf : (if target = 0 then (none : Option BitString) else
        (fighterInputs d (target - 1)).find? (fun p =>
          !s.allocated.any (fun a => a.input == p))) with
    | none =>
      refine FighterState.RoleConsistent.cancel ?_ _ _ _
      exact hs
    | some p =>
      refine FighterState.RoleConsistent.abortAbove ?_ _
      exact hs

/-- Fulfilling a payoff request preserves consistent roles. -/
private theorem FighterState.RoleConsistent.payoff {P : FighterParams} {d : ℕ}
    {s : FighterState} (hs : s.RoleConsistent d) (l : ℕ) (q : Coordinate) :
    (fighterPayoff P d l q s).RoleConsistent d := by
  unfold fighterPayoff
  split
  · exact hs
  · split
    · have ha := hs.allocate l .payoff q.2 q.1
      cases he : fighterAllocate d l .payoff q.2 q.1 s with
      | mk next success =>
        simp only [he] at ha ⊢
        cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
        · exact ha
        · intro p hp
          obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hp
          exact ha old hold
    · exact hs

/-- Fulfilling all ready payoffs preserves consistent roles. -/
private theorem FighterState.RoleConsistent.fulfillReady {P : FighterParams} {d : ℕ}
    {s : FighterState} (hs : s.RoleConsistent d) (l : ℕ) :
    (fighterFulfillReady P d l s).RoleConsistent d := by
  unfold fighterFulfillReady
  split
  · exact hs
  · exact foldl_preserves_invariant (FighterState.RoleConsistent d) _ _
      (fun t q ht ↦ ht.payoff l q) hs

/-- Spending one unit of fuel on a coordinate preserves consistent roles. -/
private theorem FighterState.RoleConsistent.fuelUnit {P : FighterParams} {d : ℕ}
    {s : FighterState} (hs : s.RoleConsistent d) (l : ℕ) (q : Coordinate) :
    (fighterFuelUnit P d l q s).RoleConsistent d := by
  unfold fighterFuelUnit
  split
  · exact hs
  · rename_i phase hp
    have hq := hs.of_activeAt hp
    split
    · let charged := { phase with controlledRemaining := phase.controlledRemaining - 1 }
      let index := fighterFreshString d
        (phase.indices[(phase.game d).coordinates.idxOf q]?.getD [])
      let out := pairCode (triple q.1 (q.2 - d) phase.candidate.1) index
      have ha := (hs.putPhase (p := charged) hq).allocate l .fuel (levelUpper l + d) out
      change FighterState.RoleConsistent d
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
        · refine FighterState.RoleConsistent.fulfillReady
            (FighterState.RoleConsistent.putPhase ha ?_) l
          exact hq
    · exact hs

/-- Spending several units of fuel on a coordinate preserves consistent roles. -/
private theorem FighterState.RoleConsistent.fuelUnits {P : FighterParams} {d : ℕ}
    {s : FighterState} (hs : s.RoleConsistent d) (l : ℕ) (q : Coordinate) (count : ℕ) :
    (fighterFuelUnits P d l q count s).RoleConsistent d := by
  induction count generalizing s with
  | zero => exact hs
  | succ count ih => exact ih (hs.fuelUnit l q)

/-- Issuing the dummy of a level preserves consistent roles. -/
private theorem FighterState.RoleConsistent.dummy {d : ℕ}
    {s : FighterState} (hs : s.RoleConsistent d) (l : ℕ) :
    (fighterDummy d l s).RoleConsistent d := by
  unfold fighterDummy
  split
  · exact hs
  · rename_i phase hp
    have hq := hs.of_activeAt hp
    split
    · exact hs
    · rename_i output hout
      split
      · exact hs
      · have ha := hs.allocate l .dummy (levelInput d l) output
        cases he : fighterAllocate d l .dummy (levelInput d l) output s with
        | mk next success =>
          simp only [he] at ha ⊢
          cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
          · exact ha
          · exact ha.putPhase ⟨hq.1, fun _ ↦ by simp [hout]⟩

/-- Reacting to an opponent event preserves consistent roles. -/
private theorem FighterState.RoleConsistent.opponent {P : FighterParams} {d : ℕ}
    {s : FighterState} (hs : s.RoleConsistent d) (l : ℕ) (e : ProgramEvent) :
    (fighterOpponent P d l e s).RoleConsistent d := by
  unfold fighterOpponent
  split
  · exact hs
  · rename_i phase hp
    have hq := hs.of_activeAt hp
    split
    · exact hs
    · split
      · exact hs
      · split
        · exact hs.cancel _ _ _
        · refine FighterState.RoleConsistent.fulfillReady
            (FighterState.RoleConsistent.putPhase hs ?_) l
          exact hq

/-- Starting a new phase preserves consistent roles. -/
private theorem FighterState.RoleConsistent.startPhase {P : FighterParams} {d : ℕ}
    {s : FighterState} (hs : s.RoleConsistent d) (l : ℕ) (c : Candidate) :
    (fighterStartPhase P d l c s).RoleConsistent d := by
  unfold fighterStartPhase
  exact ((hs.cancel _ _ _).abortAbove l).putPhase
    (FighterPhase.roleConsistent_fighter_construction P d l c _)

/-- Flushing the buffered requests of a level preserves consistent roles. -/
private theorem FighterState.RoleConsistent.flushBuffer {d : ℕ} {s : FighterState}
    (hs : s.RoleConsistent d) (l : ℕ) :
    ((fighterFlushBuffer d l s).getD s).RoleConsistent d := by
  unfold fighterFlushBuffer
  cases hp : s.activeAt d l with
  | none => exact hs
  | some phase =>
    have hq := hs.of_activeAt hp
    simp only [bind, Option.bind_some]
    split
    · exact hs.putPhase hq
    · exact hs

/-- Playing the strategy move of a level preserves consistent roles. -/
private theorem FighterState.RoleConsistent.strategyMove {P : FighterParams} {d : ℕ}
    {s : FighterState} (hs : s.RoleConsistent d) (l : ℕ) :
    ((fighterStrategyMove P d l s).getD s).RoleConsistent d := by
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
          have hn : next.RoleConsistent d :=
            foldl_preserves_invariant (FighterState.RoleConsistent d) _ _
              (fun t qi ht ↦ ht.fuelUnits l qi.1 (move[qi.2]?.getD 0)) hs
          change FighterState.RoleConsistent d ((match next.activeAt d l with
            | none => some next
            | some live => some (next.putPhase d
              { live with officialCode :=
                  ((phase.game d).afterMove (phase.official d) move).encode })).getD s)
          split
          · exact hn
          · rename_i live hlive
            refine hn.putPhase ?_
            exact hn.of_activeAt (p := live) hlive
        · exact hs
    · exact hs

/-- Performing the next action of a level preserves consistent roles. -/
private theorem FighterState.RoleConsistent.levelAction {P : FighterParams} {d : ℕ}
    {s : FighterState} (hs : s.RoleConsistent d) (l : ℕ) :
    ((fighterLevelAction P d l s).getD s).RoleConsistent d := by
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
        | some next => simpa only [hf, Option.getD_some] using hs.flushBuffer l

/-- Closing a level by repeated actions preserves consistent roles. -/
private theorem FighterState.RoleConsistent.closure {P : FighterParams} {d : ℕ}
    {s : FighterState} (hs : s.RoleConsistent d) (l fuel : ℕ) :
    (fighterClosure P d l fuel s).RoleConsistent d := by
  induction fuel generalizing s with
  | zero => exact hs
  | succ fuel ih =>
    simp only [fighterClosure]
    cases ha : fighterLevelAction P d l s with
    | none => exact hs
    | some next =>
      have hn := hs.levelAction (P := P) l
      simp only [ha, Option.getD_some] at hn
      exact ih hn

/-- Processing a timed event at a level preserves consistent roles. -/
private theorem FighterState.RoleConsistent.processLevel {P : FighterParams} {d : ℕ}
    {s : FighterState} (hs : s.RoleConsistent d) (l : ℕ) (e : Option TimedEvent) :
    (fighterProcessLevel P d l e s).RoleConsistent d := by
  unfold fighterProcessLevel fighterCloseLevel
  refine FighterState.RoleConsistent.closure ?_ _ _
  cases e with
  | none => exact hs.fulfillReady l
  | some e =>
    dsimp only
    split
    · exact (hs.fulfillReady l).startPhase l _
    · exact (hs.fulfillReady l).opponent l _

/-- Every reachable phase retains the role chosen at initialization. Its game seeks equality
exactly when its optional dummy is present, and issuance always implies presence. -/
private theorem roleConsistent_fighterState (P : FighterParams) (d tick : ℕ) :
    (fighterState P d tick).RoleConsistent d := by
  induction tick with
  | zero => simp [fighterState, initialFighterState, FighterState.RoleConsistent]
  | succ tick ih =>
    change (fighter_actions P d (tick + 1) (fighterState P d tick)).RoleConsistent d
    unfold fighter_actions
    split
    · simp [FighterState.RoleConsistent, initialFighterState]
    · exact foldl_preserves_invariant (FighterState.RoleConsistent d)
        (fun s l ↦ fighterProcessLevel P d l (eventAt P.B (tick + 1)) s) _
        (fun s l hs ↦ hs.processLevel l _) ih

/-- A completed tick has issued every chosen dummy. Thus the controlled equality role is
recorded exactly by the successful-issuance flag, including the no-dummy case. -/
private theorem equalityPlayer_eq_not_dummyIssued
    (P : FighterParams) (d l tick : ℕ) (phase : FighterPhase)
    (hphase : (fighterState P d tick).activeAt d l = some phase) :
    (phase.game d).equalityPlayer = !phase.dummyIssued := by
  have hmem := List.mem_of_find?_eq_some hphase
  obtain ⟨hrole, hissued⟩ := roleConsistent_fighterState P d tick phase hmem
  have hlevel : phase.level = l :=
    beq_iff_eq.mp (List.find?_some (p := fun p : FighterPhase => p.level == l) hphase)
  have hcomplete := fighter_event_actions_complete P d tick phase hmem
  rw [hlevel] at hcomplete
  have hdone : (phase.dummy.isSome && !phase.dummyIssued) = false := by
    by_contra h
    have henabled : (phase.dummy.isSome && !phase.dummyIssued) = true := by
      cases hb : phase.dummy.isSome && !phase.dummyIssued <;> simp_all
    simp only [fighterLevelAction, hphase, bind, Option.bind_some, henabled] at hcomplete
    simp at hcomplete
  have heq : phase.dummy.isSome = phase.dummyIssued := by
    cases hd : phase.dummyIssued <;> cases hp : phase.dummy.isSome <;> simp_all
  rwa [heq] at hrole

/-- The final virtual output satisfies the controlled objective of the actual phase record
at its start tick. The common game comes with record identities at both ticks; eventual
predicate satisfaction and output stabilization are synchronized at their maximum. -/
private theorem exists_phase_objective_final_virtual_output
    (P : FighterParams) (C cGap cRank d₀ d l : ℕ)
    (hfixed : FighterFixedConstants P C cGap cRank d₀)
    (hgood : GoodPadding P d₀ cRank cGap d) (hlate : LateAdmissibleOccurrence P d l) :
    ∃ phase, TrueMarkerPhaseAt P d l (markerTick P.B (levelScale l)) phase ∧
      (phase.game d).objective false
        (fighterFinalVirtualOutput P d l (markerCandidate P.B (levelScale l))) = true := by
  obtain ⟨_, _, hlegal, tick₁, htick₁, hpredicate⟩ :=
    true_marker_opponent_stream_legal P C cGap cRank d₀ d l hfixed hgood hlate
  obtain ⟨_, game, _, hrecords, _⟩ := hlegal
  obtain ⟨phase, hphase, hgame, _, _⟩ :=
    hrecords (markerTick P.B (levelScale l)) le_rfl
  obtain ⟨tick₂, _, hstable⟩ :=
    true_marker_virtual_output_stabilizes P C cGap cRank d₀ d l hfixed hgood hlate
  let tick := max tick₁ tick₂
  have htime : markerTick P.B (levelScale l) ≤ tick :=
    htick₁.trans (le_max_left _ _)
  obtain ⟨later, hlater, hholds⟩ := hpredicate tick (le_max_left _ _)
  obtain ⟨record, hrecord, hrecordGame, hbuffer, _⟩ := hrecords tick htime
  have hsame : record = later :=
    Option.some.inj (hrecord.2.2.2.symm.trans hlater.2.2.2)
  subst record
  have hgame' : later.game d = phase.game d := hrecordGame.trans hgame.symm
  have hout := (hstable tick (le_max_right _ _)).2
  rw [true_marker_virtual_output_eq P d l tick later hlater] at hout
  change (later.game d).objective later.controlledPlayer (later.virtualOutput d) = true
    at hholds
  rw [hbuffer.1, hgame', hout] at hholds
  exact ⟨phase, hphase, hholds⟩

/-- The controlled objective contradicts the count obtained by adding the optional dummy.
This is just the two Boolean cases, with no construction or stabilization assumptions. -/
private theorem ne_target_add_ite_of_objective
    (game : FiniteCounterGame) (issued : Bool) (out : ℕ)
    (hrole : game.equalityPlayer = !issued)
    (hholds : game.objective false out = true) :
    out ≠ game.target + if issued then 1 else 0 := by
  cases issued <;> simp_all [FiniteCounterGame.objective]

/-- Every member of the fixed referee family fails to count the actual bounded-complexity set.
Blueprint node `constr:diagonal`. The member may be an arbitrary native tuple; only its
membership is required. The constants and good padding are shared by the entire family. -/
theorem constructed_oracle_defeats_polynomial_counting (P : FighterParams)
    (C cGap cRank d₀ d : ℕ) (hfixed : FighterFixedConstants P C cGap cRank d₀)
    (hgood : GoodPadding P d₀ cRank cGap d)
    (M : ℕ → QueryTree) (p : ℕ → ℕ) (hmember : P.family.Contains d M p) :
    ∃ m : ℕ, refereeSetOutput (constructedLiteralConstant P.literal d) (M m)
      (fighterOracle P d) ≠ {x | plainK (fighterU P d) x ≤ (m : ℕ)}.ncard := by
  obtain ⟨l, hlate, htree, _⟩ :=
    exists_late_admissible_occurrence_of_contains P C cGap cRank d₀ d hfixed hgood M p hmember
  obtain ⟨phase, hphase, hholds⟩ :=
    exists_phase_objective_final_virtual_output P C cGap cRank d₀ d l hfixed hgood hlate
  have hrole := equalityPlayer_eq_not_dummyIssued
    P d l (markerTick P.B (levelScale l)) phase hphase.2.2.2
  have hcount :=
    (true_marker_phase_separation P C cGap cRank d₀ d l hfixed hgood hlate
      phase hphase).final_count
  refine ⟨levelInput d l, ?_⟩
  rw [← htree, ← true_marker_final_output_agrees P C cGap cRank d₀ d l
    hfixed hgood hlate, hcount]
  exact ne_target_add_ite_of_objective (phase.game d) phase.dummyIssued _ hrole hholds

end Kolmogorov.Milovanov
