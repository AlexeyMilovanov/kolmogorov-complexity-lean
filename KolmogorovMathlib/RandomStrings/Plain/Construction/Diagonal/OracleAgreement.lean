/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Construction.Diagonal.AllocationGraph
import KolmogorovMathlib.RandomStrings.Plain.Construction.Diagonal.AllocationProvenance
import KolmogorovMathlib.RandomStrings.Plain.Construction.Diagonal.FundedFrames
import KolmogorovMathlib.RandomStrings.Plain.Construction.Diagonal.LiveCounters
import KolmogorovMathlib.RandomStrings.Plain.Construction.Diagonal.PayoffReceipts
import KolmogorovMathlib.RandomStrings.Plain.Construction.Diagonal.SimulationEvents

/-!
# Eventual agreement of the virtual and the actual oracle

For the true-marker phase of a late admissible level `l`, the final virtual oracle of the phase
and the actual oracle of the simulation answer every query of the complete finite query tree of
the level in the same way, from some stage on (`true_marker_virtual_actual_oracle_agreement`,
blueprint node `constr:agreement`).  Agreement is not claimed at every moment of play.

By the stabilization of the virtual output, from a certain tick the virtual answer is the final
virtual answer, so it remains to compare it with the actual answer.  An actual positive on the
tree is initially true, or a new simulation description (these two cases are proved in the
imported modules `Diagonal.FundedFrames`, `Diagonal.SimulationState` and
`Diagonal.SimulationEvents`), or a new payoff.  This module treats the payoff case: the
allocation provenance (`Diagonal.AllocationProvenance`) shows that a new allocated directive for
a query of the tree is a payoff of the true-marker phase, the payoff receipts
(`Diagonal.PayoffReceipts`) show that its coordinate is funded in the limiting phase oracle, and
hence the final virtual answer is positive.  The converse inequality is
`fighterActualAnswer_of_fighterFinalVirtualAnswer`, which is proved elsewhere.

The agreement is used in `Diagonal.PolynomialCounting` to identify the final virtual output of
the true-marker phase with the actual normalized referee output.
-/

namespace Kolmogorov.Milovanov

/-- A directive that was allocated for a query of the complete tree of the late admissible level
`l`, with input short enough for the queried threshold, but whose query is not initially true in
the true-marker phase, is a payoff directive of that phase: it has level `l`, the marker
candidate, exact target length, and a target at most the queried threshold.  The provenance
of allocations excludes saved initial truth, dummies, fuel and other levels. -/
private lemma exists_marker_payoff_of_allocated_output
    (P : FighterParams) (C cGap cRank d₀ d l : ℕ)
    (hfixed : FighterFixedConstants P C cGap cRank d₀)
    (hgood : GoodPadding P d₀ cRank cGap d)
    (hlate : LateAdmissibleOccurrence P d l) :
    ∀ q ∈ (P.family.tree d l (levelInput d l)).queries,
      (∃ tick a, a ∈ (fighterState P d tick).allocated ∧
        a.input.length + 1 ≤ q.2 ∧ a.output = q.1) →
      ((trueMarkerPhase P d l (markerTick P.B (levelScale l))).map
        (fun phase ↦ phase.initialAnswer P d q) ≠ some true) →
      ∃ tick a, a ∈ (fighterState P d tick).allocated ∧
        a.level = l ∧ a.candidate = markerCandidate P.B (levelScale l) ∧
        a.kind = DirectiveKind.payoff ∧ a.target = a.input.length + 1 ∧
        a.target ≤ q.2 ∧ a.output = q.1 := by
  intro q hq ⟨tick, a, ha, hlength, hout⟩ hnotinit
  obtain ⟨_, game, _, hrecords, _⟩ :=
    (true_marker_opponent_stream_legal P C cGap cRank d₀ d l hfixed hgood hlate).2.2.1
  obtain ⟨initial, hinitial, hinitialGame, _, _⟩ :=
    hrecords (markerTick P.B (levelScale l)) le_rfl
  have hlookup : trueMarkerPhase P d l (markerTick P.B (levelScale l)) =
      some initial := by
    simp [trueMarkerPhase, fighterPhaseAt, hinitial.2.2.2, hinitial.2.2.1]
  have hnotinitial : initial.initialAnswer P d q ≠ true := by
    intro h
    exact hnotinit (by simp [hlookup, h])
  have hnontrivial : q.2 < q.1.length + constructedLiteralConstant P.literal d := by
    by_contra h
    have hliteral : q.1.length + constructedLiteralConstant P.literal d ≤ q.2 := by omega
    exact hnotinitial (by simp [FighterPhase.initialAnswer, normalizedAnswer, hliteral])
  have hquerylength := P.family.query_bound d l (levelInput d l) hlate.1.1 q hq
  have hadmissible := hlate.1.2.2
  have hqueryrange : q.2 < levelRangeBound l := by
    unfold constructedLiteralConstant at hnontrivial
    omega
  have hrangeupper : levelRangeBound l < levelUpper l :=
    fighter_range_below_upper (levelScale l)
      (fighter_admissible_square P d l hlate.1).1 ⟨2 * l, rfl⟩
  have hqueryupper : q.2 < levelUpper l := hqueryrange.trans hrangeupper
  have hmetadata := (fighterState_allocated_provenance P d tick).1 a ha
  have hrange := (fighter_directive_target_ranges P d tick a ha).2
  have hminimum : levelScale a.level + d ≤ a.target := by
    have hscale : levelScale a.level < levelUpper a.level := Nat.lt_two_pow_self
    cases hk : a.kind <;> simp only [hk, FighterTargetRange] at hrange <;> omega
  have hlevelle : a.level ≤ l := by
    by_contra h
    have hprevious := fighter_previous_upper_bound l a.level hlate.1.1 (by omega)
    have hlog := Nat.log2_le_self (levelScale a.level)
    omega
  let later := max tick (markerTick P.B (levelScale l))
  have hanow : a ∈ (fighterState P d later).allocated :=
    fighterState_allocated_subset_of_le
      P d hgood.positive tick later (le_max_left _ _) ha
  obtain ⟨phase, hphase, hgame, _, _⟩ := hrecords later (le_max_right _ _)
  have hnotphase : phase.initialAnswer P d q ≠ true := by
    intro h
    apply hnotinitial
    rw [true_marker_initial_table_on_tree P d l _ initial hinitial q hq]
    rw [true_marker_initial_table_on_tree P d l later phase hphase q hq] at h
    simpa only [hinitialGame, hgame] using h
  have hclass := (fighterState_allocated_provenance P d later).2 phase
    (List.mem_of_find?_eq_some hphase.2.2.2) a hanow (by simpa only [hphase.2.1] using hlevelle)
  rcases hclass with hsaved | ⟨hlevel, hcandidate⟩
  · exfalso
    apply hnotphase
    unfold FighterPhase.initialAnswer normalizedAnswer
    rw [Bool.or_eq_true]
    right
    apply decide_eq_true
    simp only [fighterStageOutputs, fighterStageOutputList, List.mem_toFinset,
      List.mem_eraseDups, List.mem_append]
    right
    have hq1 : 1 ≤ q.2 := by omega
    simp only [hq1, hgood.positive, and_self, ↓reduceIte]
    exact List.mem_map.mpr ⟨a, List.mem_filter.mpr
      ⟨hsaved, decide_eq_true (by omega)⟩, hout⟩
  · have hlevel' : a.level = l := hlevel.trans hphase.2.1
    have hkind : a.kind = .payoff := by
      cases hk : a.kind with
      | dummy =>
        exact False.elim ((hmetadata.2 hk q (by simpa only [hlevel'] using hq)) hout.symm)
      | fuel =>
        have htarget : a.target = levelUpper l + d := by
          simpa only [hlevel', hk, FighterTargetRange] using hrange
        omega
      | payoff => rfl
    exact ⟨tick, a, ha, hlevel', hcandidate.trans hphase.2.2.1,
      hkind, hmetadata.1, by omega, hout⟩

/-- A payoff directive of the true-marker phase, whose target is at most the queried threshold
and whose output is the queried string, puts the query into the limiting oracle of the
true-marker phase.  A receipt of the payoff in the active phase of the level gives a funded
coordinate, and a receipt in a cancelled phase is impossible, since the true-marker phase is
never cancelled. -/
private lemma mem_fighterPhaseOracle_of_marker_payoff
    (P : FighterParams) (C cGap cRank d₀ d l : ℕ)
    (hfixed : FighterFixedConstants P C cGap cRank d₀)
    (hgood : GoodPadding P d₀ cRank cGap d)
    (hlate : LateAdmissibleOccurrence P d l) :
    ∀ q ∈ (P.family.tree d l (levelInput d l)).queries,
      (∃ tick a, a ∈ (fighterState P d tick).allocated ∧
        a.level = l ∧ a.candidate = markerCandidate P.B (levelScale l) ∧
        a.kind = DirectiveKind.payoff ∧ a.target = a.input.length + 1 ∧
        a.target ≤ q.2 ∧ a.output = q.1) →
      q ∈ fighterPhaseOracle P d l (markerCandidate P.B (levelScale l)) := by
  intro q hq ⟨tick, a, ha, hlevel, hcand, hkind, hlength, htarget, hout⟩
  rcases fighterState_payoff_receipt P d tick a ha hkind with
    ⟨phase, hphase, hc, hret, hfunded⟩ | ⟨e, he, hl, hc, hret, hfunded⟩
  · have hlookup : fighterPhaseAt P d l (markerCandidate P.B (levelScale l)) tick =
        some phase := by
      rw [hlevel] at hphase
      simp [fighterPhaseAt, hphase, hc.trans hcand]
    refine ⟨tick, phase, hlookup, ?_⟩
    unfold FighterPhase.virtualAnswer normalizedAnswer
    rw [Bool.or_eq_true]
    right
    apply (counter_answer_eq_true (phase.game d) phase.liveCounters q).mpr
    exact Or.inr ⟨(a.output, a.target), hret, hout, htarget, hfunded⟩
  · have htick : markerTick P.B (levelScale l) ≤ tick := by
      have h := (fighterState_candidate_time_le P d tick).2 e he
      rw [hc, hcand] at h
      exact h
    obtain ⟨_, _, _, hrecords, _⟩ :=
      (true_marker_opponent_stream_legal P C cGap cRank d₀ d l hfixed hgood hlate).2.2.1
    have hactive : ∀ t, markerTick P.B (levelScale l) ≤ t → t ≤ tick →
        ∃ phase, TrueMarkerPhaseAt P d l t phase := by
      intro t ht _
      obtain ⟨phase, hp, _⟩ := hrecords t ht
      exact ⟨phase, hp⟩
    exact False.elim
      (fighterState_ended_candidate_ne_marker
        P d l tick htick hactive e he (hl.trans hlevel) (hc.trans hcand))

/-- A new payoff of the true-marker phase is eventually recognized as true: if a directive is
allocated for a query of the tree with a short enough input and the query is not initially true
in the true-marker phase, then the final virtual answer of the phase to the query is positive. -/
private lemma fighterFinalVirtualAnswer_eq_true_of_allocated_output
    (P : FighterParams) (C cGap cRank d₀ d l : ℕ)
    (hfixed : FighterFixedConstants P C cGap cRank d₀)
    (hgood : GoodPadding P d₀ cRank cGap d)
    (hlate : LateAdmissibleOccurrence P d l) :
    ∀ q ∈ (P.family.tree d l (levelInput d l)).queries,
      (∃ tick a, a ∈ (fighterState P d tick).allocated ∧
        a.input.length + 1 ≤ q.2 ∧ a.output = q.1) →
      ((trueMarkerPhase P d l (markerTick P.B (levelScale l))).map
        (fun phase ↦ phase.initialAnswer P d q) ≠ some true) →
      fighterFinalVirtualAnswer P d l (markerCandidate P.B (levelScale l)) q = true := by
  intro q hq halloc hnotinit
  have hpayoff := exists_marker_payoff_of_allocated_output
    P C cGap cRank d₀ d l hfixed hgood hlate q hq halloc hnotinit
  have horacle := mem_fighterPhaseOracle_of_marker_payoff
    P C cGap cRank d₀ d l hfixed hgood hlate q hq hpayoff
  dsimp [fighterFinalVirtualAnswer, normalizedAnswer, coordinateOracleAnswer]
  rw [Bool.or_eq_true]
  right
  classical
  exact decide_eq_true horacle

/-- An actual positive answer on the complete tree implies a positive final virtual answer of
the true-marker phase.  An actual positive comes from initial truth, a new `V` simulation
description, or a payoff, and in each case the required witnesses make the virtual query
positive. -/
private lemma fighterFinalVirtualAnswer_eq_true_of_actual
    (P : FighterParams) (C cGap cRank d₀ d l : ℕ)
    (hfixed : FighterFixedConstants P C cGap cRank d₀)
    (hgood : GoodPadding P d₀ cRank cGap d)
    (hlate : LateAdmissibleOccurrence P d l) :
    ∀ q ∈ (P.family.tree d l (levelInput d l)).queries,
      fighterActualAnswer P d q = true →
      fighterFinalVirtualAnswer P d l (markerCandidate P.B (levelScale l)) q = true := by
  intro q hq hactual
  rcases true_marker_actual_answer_cases P C cGap cRank d₀ d l hfixed hgood hlate q hq hactual
    with hinit | ⟨hd, hsim, hnotinit⟩ | ⟨tick, a, ha, hlength, hout, hnotinit⟩
  · exact fighterFinalVirtualAnswer_eq_true_of_initialAnswer
      P C cGap cRank d₀ d l hfixed hgood hlate q hq hinit
  · exact fighterFinalVirtualAnswer_eq_true_of_simple_of_not_initialAnswer
      P C cGap cRank d₀ d l hfixed hgood hlate q hq hd hsim hnotinit
  · exact fighterFinalVirtualAnswer_eq_true_of_allocated_output
      P C cGap cRank d₀ d l hfixed hgood hlate q hq ⟨tick, a, ha, hlength, hout⟩ hnotinit

/-- Virtual and actual answers eventually agree on every query of the complete finite tree.
Blueprint node `constr:agreement`. The time precedes all queries and all later ticks;
neither agreement only along the realized branch nor instantaneous agreement is substituted. -/
theorem true_marker_virtual_actual_oracle_agreement (P : FighterParams)
    (C cGap cRank d₀ d l : ℕ) (hfixed : FighterFixedConstants P C cGap cRank d₀)
    (hgood : GoodPadding P d₀ cRank cGap d) (hlate : LateAdmissibleOccurrence P d l) :
    ∃ tick₀ ≥ markerTick P.B (levelScale l), ∀ tick ≥ tick₀,
      ∀ q ∈ (P.family.tree d l (levelInput d l)).queries,
        fighterVirtualAnswerAt P d l tick q = fighterActualAnswer P d q := by
  obtain ⟨tick₀, ht₀, hstab⟩ :=
    true_marker_virtual_output_stabilizes P C cGap cRank d₀ d l hfixed hgood hlate
  refine ⟨tick₀, ht₀, fun tick htick q hq ↦ ?_⟩
  rw [(hstab tick htick).1 q hq]
  have h1 := fighterActualAnswer_of_fighterFinalVirtualAnswer
    P C cGap cRank d₀ d l hfixed hgood hlate q hq
  have h2 := fighterFinalVirtualAnswer_eq_true_of_actual
    P C cGap cRank d₀ d l hfixed hgood hlate q hq
  cases hvirtual : fighterFinalVirtualAnswer P d l (markerCandidate P.B (levelScale l)) q <;>
  cases hactual : fighterActualAnswer P d q
  · rfl
  · exact False.elim (by simp_all)
  · exact False.elim (by simp_all)
  · rfl

end Kolmogorov.Milovanov
