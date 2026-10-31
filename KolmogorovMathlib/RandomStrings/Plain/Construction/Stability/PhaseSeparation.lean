/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.PhaseSeparationClasses
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.PhaseSeparationDummyFreshness

/-!
# Target and query separation at the true marker

This module proves blueprint node `constr:separation`, `true_marker_phase_separation`. For a
phase that is active at its true marker tick, it shows that

* the actual answers of the stage oracles and of the limit oracle on the referee's query tree
  at thresholds up to the level budget coincide with the answers recorded when the phase was
  initialized;
* no allocation of a higher level changes any query on the tree or the set of strings simple
  at the level budget, because higher-level targets exceed that budget;
* the number of strings of complexity at most the level budget is the initial target of the
  counter game, plus one exactly when the phase issued a dummy, because the dummy lies outside
  the query tree and outside the initial table.

The result is the `TrueMarkerSeparation` record consumed by the modules that assemble the
stability argument for the constructed decompressor. The freshness of the dummy, which the
count relies on, comes from `PhaseSeparationDummyFreshness`.
-/

namespace Kolmogorov.Milovanov

/-- The dummy of a true-marker phase is fresh with respect to its initial output table and the
referee's query tree, and an issued dummy is recorded by an exact-length allocation in some
reachable state at or after the marker. -/
private lemma dummy_fresh_and_recorded_of_true_marker
    (P : FighterParams) (d l : ℕ) (phase : FighterPhase)
    (hphase : TrueMarkerPhaseAt P d l (markerTick P.B (levelScale l)) phase) :
    (∀ z, phase.dummy = some z → z ∉ fighterStageOutputs P d (levelInput d l) phase.candidate.2
      phase.initialAllocations ∧
      ∀ q ∈ (P.family.tree d l (levelInput d l)).queries, q.1 ≠ z) ∧
    (phase.dummyIssued = true → ∃ z tick a,
      phase.dummy = some z ∧ markerTick P.B (levelScale l) ≤ tick ∧
      a ∈ (fighterState P d tick).allocated ∧
      a.output = z ∧ a.input.length + 1 = levelInput d l) := by
  have hp : phase ∈ (fighterState P d (markerTick P.B (levelScale l))).active :=
    List.mem_of_find?_eq_some hphase.2.2.2
  obtain ⟨hfresh, hissued⟩ :=
    active_phase_dummy_fresh_and_recorded P d (markerTick P.B (levelScale l)) phase hp
  constructor
  · simpa only [hphase.2.1] using hfresh
  · intro hi
    obtain ⟨z, a, hz, ha, ho, hn⟩ := hissued hi
    refine ⟨z, markerTick P.B (levelScale l), a, hz, le_rfl, ha, ho, ?_⟩
    simpa only [hphase.2.1] using hn

/-- On the referee's query tree, the stage answer at every tick from the marker on equals the
answer recorded in the phase at initialization, for thresholds up to the level budget. -/
private lemma stageAnswer_eq_initialAnswer_of_true_marker
    (P : FighterParams) (d l : ℕ) (hd : 1 ≤ d) (hlate : LateAdmissibleOccurrence P d l)
    (phase : FighterPhase)
    (hphase : TrueMarkerPhaseAt P d l (markerTick P.B (levelScale l)) phase) :
    ∀ tick ≥ markerTick P.B (levelScale l),
      ∀ q ∈ (P.family.tree d l (levelInput d l)).queries, q.2 ≤ levelInput d l →
        fighterStageAnswer P d tick q = phase.initialAnswer P d q := by
  intro tick htick q hq hqlen
  have h2 := simple_iff_mem_stageOutputList_of_markerTick_le P d l phase hphase
  have h3 := mem_allocated_of_mem_initialAllocations P d l hd phase hphase
  have h4 := allocation_mem_initial_or_dummy_of_true_marker P d l hd hlate phase hphase
  have h5 := dummy_fresh_and_recorded_of_true_marker P d l phase hphase
  unfold fighterStageAnswer FighterPhase.initialAnswer normalizedAnswer
  congr 2
  dsimp
  congr 1
  apply propext
  simp only [fighterStageOutputs, fighterStageOutputList, List.mem_toFinset, List.mem_eraseDups,
    List.mem_append]
  constructor
  · intro h
    cases h with
    | inl hbase =>
      left
      split_ifs at hbase with hd
      · rw [ite_eq_left_iff.mpr (fun hc ↦ (hc hd).elim)]
        apply (h2 q.2 hqlen hd tick htick q.1).1.mpr at hbase
        exact (h2 q.2 hqlen hd tick htick q.1).2.mp hbase
      · contradiction
    | inr halloc =>
      right
      split_ifs at halloc with hd2
      · rw [ite_eq_left_iff.mpr (fun hc ↦ (hc hd2).elim)]
        rw [List.mem_map] at halloc
        rcases halloc with ⟨a, hmem, haout⟩
        rw [List.mem_filter] at hmem
        have hain := hmem.1
        have halen := hmem.2
        have htlen : a.input.length + 1 ≤ levelInput d l := by
          have ht2 : a.input.length ≤ q.2 - 1 := decide_eq_true_eq.mp halen
          omega
        have hclass := h4 tick a hain htlen
        rcases hclass with hinit | hdum
        · rw [List.mem_map]
          exact ⟨a, by rw [List.mem_filter]; exact ⟨hinit, halen⟩, haout⟩
        · rcases hdum with ⟨_, _, _, hdum4, _⟩
          have hneq : q.1 ≠ a.output := (h5.1 a.output hdum4).2 q hq
          exfalso
          exact hneq (Eq.symm haout)
      · contradiction
  · intro h
    cases h with
    | inl hbase =>
      left
      split_ifs at hbase with hd
      · rw [ite_eq_left_iff.mpr (fun hc ↦ (hc hd).elim)]
        apply (h2 q.2 hqlen hd tick htick q.1).2.mpr at hbase
        exact (h2 q.2 hqlen hd tick htick q.1).1.mp hbase
      · contradiction
    | inr halloc =>
      right
      split_ifs at halloc with hd2
      · rw [ite_eq_left_iff.mpr (fun hc ↦ (hc hd2).elim)]
        rw [List.mem_map] at halloc
        rcases halloc with ⟨a, hmem, haout⟩
        rw [List.mem_filter] at hmem
        have hinit := hmem.1
        have halen := hmem.2
        have hpersist := h3 tick htick a hinit
        rw [List.mem_map]
        exact ⟨a, by rw [List.mem_filter]; exact ⟨hpersist, halen⟩, haout⟩
      · contradiction

/-- On the referee's query tree, the limit oracle answer equals the answer recorded in the
phase at initialization, for thresholds up to the level budget. -/
private lemma oracleAnswer_eq_initialAnswer_of_true_marker
    (P : FighterParams) (d l : ℕ) (hd : 1 ≤ d) (hlate : LateAdmissibleOccurrence P d l)
    (phase : FighterPhase)
    (hphase : TrueMarkerPhaseAt P d l (markerTick P.B (levelScale l)) phase) :
    ∀ q ∈ (P.family.tree d l (levelInput d l)).queries,
      q.2 ≤ levelInput d l →
        coordinateOracleAnswer (fighterOracle P d) q = phase.initialAnswer P d q := by
  intro q hq hqlen
  have h2 := simple_iff_mem_stageOutputList_of_markerTick_le P d l phase hphase
  have h3 := mem_allocated_of_mem_initialAllocations P d l hd phase hphase
  have h4 := allocation_mem_initial_or_dummy_of_true_marker P d l hd hlate phase hphase
  have h5 := dummy_fresh_and_recorded_of_true_marker P d l phase hphase
  have hbase : (d ≤ q.2 ∧ Simple P.B.V q.1 (q.2 - d)) ↔
      q.1 ∈ (if d ≤ q.2 then
        stageOutputList P.B (q.2 - d) phase.candidate.2 else []) := by
    by_cases hdq : d ≤ q.2
    · simp only [hdq, true_and, ite_true]
      exact (h2 q.2 hqlen hdq (markerTick P.B (levelScale l)) le_rfl q.1).2
    · simp [hdq]
  have halloc :
      (∃ tick a, a ∈ (fighterState P d tick).allocated ∧
        a.input.length + 1 ≤ q.2 ∧ a.output = q.1) ↔
      q.1 ∈ (if 1 ≤ q.2 ∧ 1 ≤ d then
        ((phase.initialAllocations.filter
          (fun a ↦ decide (a.input.length ≤ q.2 - 1))).map
            AllocatedDirective.output) else []) := by
    by_cases hk : 1 ≤ q.2
    · rw [ite_eq_left ⟨hk, hd⟩]
      simp only [List.mem_map, List.mem_filter, decide_eq_true_eq]
      constructor
      · rintro ⟨tick, a, ha, hlen, hout⟩
        rcases h4 tick a ha (hlen.trans hqlen) with hinit | hdummy
        · exact ⟨a, ⟨hinit, by omega⟩, hout⟩
        · exact False.elim ((h5.1 a.output hdummy.2.2.2.1).2 q hq hout.symm)
      · rintro ⟨a, ⟨hinit, hlen⟩, hout⟩
        exact ⟨markerTick P.B (levelScale l), a,
          h3 _ le_rfl a hinit, by omega, hout⟩
    · rw [ite_eq_right (fun h ↦ hk h.1)]
      simp only [List.not_mem_nil, iff_false]
      rintro ⟨tick, a, ha, hlen, hout⟩
      omega
  have hsimple : Simple (fighterU P d) q.1 q.2 ↔
      q.1 ∈ fighterStageOutputs P d q.2 phase.candidate.2 phase.initialAllocations := by
    rw [simple_fighterU_iff P d hd]
    simpa only [fighterStageOutputs, fighterStageOutputList,
      List.mem_toFinset, List.mem_eraseDups, List.mem_append] using (or_congr hbase halloc)
  by_cases hliteral : q.1.length + constructedLiteralConstant P.literal d ≤ q.2
  · have hx : Simple (fighterU P d) q.1 q.2 :=
      (constructed_machine_literal_bound P.B P.literal d hd
        (fighterG P d) q.1).trans (by exact_mod_cast hliteral)
    simp [coordinateOracleAnswer, fighterOracle, actualCoordinateOracle,
      FighterPhase.initialAnswer, normalizedAnswer, hliteral, hx]
  · simp only [FighterPhase.initialAnswer, normalizedAnswer, hliteral,
      decide_false, Bool.false_or]
    exact decide_eq_decide.mpr hsimple

/-- An allocation of a level above `l` has input too long to be simple at any threshold up to
`2 ^ levelScale l + d`. -/
private lemma budget_lt_input_length_of_level_gt
    (P : FighterParams) (d l : ℕ) (hd : 1 ≤ d)
    (tick : ℕ) (a : AllocatedDirective)
    (ha : a ∈ (fighterState P d tick).allocated) (hlt : l < a.level) :
    2 ^ levelScale l + d < a.input.length + 1 := by
  obtain ⟨hlen, hrange⟩ :=
    target_eq_and_targetRange_of_mem_allocated P d tick hd a ha
  have hgap : 2 ^ levelScale l < levelScale a.level := by
    change tower (2 * l + 1) < tower (2 * a.level)
    have hnext : tower (2 * l + 1) < tower (2 * l + 1 + 1) :=
      Nat.lt_two_pow_self
    exact hnext.trans_le
      (tower_le_tower (by omega))
  have hupper : levelScale a.level < levelUpper a.level := Nat.lt_two_pow_self
  cases hk : a.kind <;> simp only [hk, FighterTargetRange] at hrange <;> omega

/-- Every nontrivial threshold of a query of an admissible level lies below the range bound of
the level, which lies below the exponential `2 ^ levelScale l`. -/
private lemma threshold_lt_pow_levelScale_of_mem_tree
    (P : FighterParams) (d l : ℕ) (hadm : P.Admissible d l)
    (q : Coordinate) (hq : q ∈ (P.family.tree d l (levelInput d l)).queries)
    (hnt : q.2 < q.1.length + constructedLiteralConstant P.literal d) :
    q.2 < levelRangeBound l ∧ levelRangeBound l < 2 ^ levelScale l := by
  have hlen : q.1.length ≤ P.family.bound l (levelInput d l) :=
    P.family.query_bound d l (levelInput d l) hadm.1 q hq
  have hbound := hadm.2.2
  have hquery : q.2 < levelRangeBound l := by
    unfold constructedLiteralConstant at hnt
    omega
  exact ⟨hquery, fighter_range_below_upper (levelScale l)
    (fighter_admissible_square P d l hadm).1 ⟨2 * l, rfl⟩⟩

/-- Filtering the allocations down to levels at most `l` preserves the finite output table at
every threshold up to `2 ^ levelScale l + d`. -/
private lemma fighterStageOutputs_eq_filter_level_le
    (P : FighterParams) (d l : ℕ) (hd : 1 ≤ d) (tick k : ℕ)
    (hk : k ≤ 2 ^ levelScale l + d) :
    fighterStageOutputs P d k tick (fighterState P d tick).allocated =
      fighterStageOutputs P d k tick
        ((fighterState P d tick).allocated.filter (fun a ↦ decide (a.level ≤ l))) := by
  ext x
  by_cases hkpos : 1 ≤ k
  · simp only [fighterStageOutputs, fighterStageOutputList, List.mem_toFinset,
      List.mem_eraseDups, List.mem_append, ite_eq_left (And.intro hkpos hd),
      List.mem_map, List.mem_filter, decide_eq_true_eq]
    apply or_congr Iff.rfl
    constructor
    · rintro ⟨a, ⟨ha, hlen⟩, hout⟩
      have hlevel : a.level ≤ l := by
        by_contra h
        have hlong := budget_lt_input_length_of_level_gt P d l hd tick a ha (not_le.mp h)
        omega
      exact ⟨a, ⟨⟨ha, hlevel⟩, hlen⟩, hout⟩
    · rintro ⟨a, ⟨⟨ha, _⟩, hlen⟩, hout⟩
      exact ⟨a, ⟨ha, hlen⟩, hout⟩
  · simp [fighterStageOutputs, fighterStageOutputList, hkpos]

/-- At a threshold up to `2 ^ levelScale l + d`, simplicity for the constructed decompressor is
characterized by the base machine and the allocations of levels at most `l`. -/
private lemma simple_fighterU_iff_lowerSources
    (P : FighterParams) (d l : ℕ) (hd : 1 ≤ d) (k : ℕ)
    (hk : k ≤ 2 ^ levelScale l + d) (x : BitString) :
    Simple (fighterU P d) x k ↔ FighterLowerSources P d l k x := by
  rw [simple_fighterU_iff P d hd k x]
  unfold FighterLowerSources
  constructor
  · rintro (hbase | ⟨tick, a, ha, hlen, hout⟩)
    · exact Or.inl hbase
    · right
      refine ⟨tick, a, ha, ?_, hlen, hout⟩
      by_contra h
      have hlong := budget_lt_input_length_of_level_gt P d l hd tick a ha (not_le.mp h)
      omega
  · rintro (hbase | ⟨tick, a, ha, _, hlen, hout⟩)
    · exact Or.inl hbase
    · exact Or.inr ⟨tick, a, ha, hlen, hout⟩

/-- Allocations of levels above `l` change neither the stage answers on the referee's tree nor
the strings simple at the level budget. -/
private lemma higherLevelsIrrelevant_of_admissible
    (P : FighterParams) (d l : ℕ) (hd : 1 ≤ d) (hlate : LateAdmissibleOccurrence P d l) :
    FighterHigherLevelsIrrelevant P d l := by
  have hbudget (q : Coordinate)
      (hq : q ∈ (P.family.tree d l (levelInput d l)).queries)
      (hnt : q.2 < q.1.length + constructedLiteralConstant P.literal d) :
      q.2 ≤ 2 ^ levelScale l + d := by
    obtain ⟨hquery, hrange⟩ := threshold_lt_pow_levelScale_of_mem_tree P d l hlate.1 q hq hnt
    omega
  refine ⟨?_, ?_, ?_⟩
  · intro tick q hq
    by_cases htriv : q.1.length + constructedLiteralConstant P.literal d ≤ q.2
    · simp [fighterStageAnswer, normalizedAnswer, htriv]
    · have houtputs :=
        fighterStageOutputs_eq_filter_level_le P d l hd tick q.2 (hbudget q hq (by omega))
      simp only [fighterStageAnswer, normalizedAnswer]
      rw [houtputs]
  · intro q hq
    change Simple (fighterU P d) q.1 q.2 ↔ FighterLowerSources P d l q.2 q.1
    by_cases htriv : q.1.length + constructedLiteralConstant P.literal d ≤ q.2
    · have hdk : d ≤ q.2 := by
        unfold constructedLiteralConstant at htriv
        omega
      have hbase : Simple P.B.V q.1 (q.2 - d) :=
        simple_mono P.B.V q.1 (by
          unfold constructedLiteralConstant at htriv
          omega) (P.literal.bound q.1)
      have hsource : FighterLowerSources P d l q.2 q.1 := Or.inl ⟨hdk, hbase⟩
      exact iff_of_true ((simple_fighterU_iff P d hd q.2 q.1).mpr (Or.inl ⟨hdk, hbase⟩)) hsource
    · exact simple_fighterU_iff_lowerSources P d l hd q.2 (hbudget q hq (by omega)) q.1
  · ext x
    exact simple_fighterU_iff_lowerSources P d l hd (2 ^ levelScale l + d) le_rfl x

/-- The target of the counter game of a true-marker phase is the size of its initial output
table. -/
private lemma game_target_eq_card_stageOutputs
    (P : FighterParams) (d l : ℕ) (phase : FighterPhase)
    (hphase : TrueMarkerPhaseAt P d l (markerTick P.B (levelScale l)) phase) :
    (phase.game d).target =
      (fighterStageOutputs P d (levelInput d l) phase.candidate.2 phase.initialAllocations).card :=
  by
  have hactive := active_phase_of_construction P d
    (fun j c allocations code ↦ (decodeCounterGame code).target =
      (fighterStageOutputs P d (levelInput d j) c.2 allocations).card)
    (fun j c s ht ↦ by
      dsimp only [fighter_construction, FighterPhase.fundRequests]
      rw [decode_encode_counter_game, (symmetric_game_target_flip _).2.1, ht]
      rfl)
    (markerTick P.B (levelScale l))
  have hcount := hactive phase (List.mem_of_find?_eq_some hphase.2.2.2)
  change (phase.game d).target =
    (fighterStageOutputs P d (levelInput d phase.level)
      phase.candidate.2 phase.initialAllocations).card at hcount
  simpa only [hphase.2.1] using hcount

/-- A string is simple at the level budget exactly when it is in the initial output table of a
true-marker phase or is the dummy that the phase issued. -/
private lemma simple_fighterU_levelInput_iff
    (P : FighterParams) (d l : ℕ) (hd : 1 ≤ d) (hlate : LateAdmissibleOccurrence P d l)
    (phase : FighterPhase)
    (hphase : TrueMarkerPhaseAt P d l (markerTick P.B (levelScale l)) phase) (x : BitString) :
    Simple (fighterU P d) x (levelInput d l) ↔
      x ∈ fighterStageOutputs P d (levelInput d l) phase.candidate.2 phase.initialAllocations ∨
        (phase.dummyIssued = true ∧ phase.dummy = some x) := by
  have hsources := simple_fighterU_iff P d hd
  have hsim := simple_iff_mem_stageOutputList_of_markerTick_le P d l phase hphase
  have hpersist := mem_allocated_of_mem_initialAllocations P d l hd phase hphase
  have hclass := allocation_mem_initial_or_dummy_of_true_marker P d l hd hlate phase hphase
  have hfresh := dummy_fresh_and_recorded_of_true_marker P d l phase hphase
  have hdl : d ≤ levelInput d l := Nat.le_add_left d (levelScale l)
  have hm : 1 ≤ levelInput d l := hd.trans hdl
  have hv := (hsim (levelInput d l) le_rfl hdl (markerTick P.B (levelScale l)) le_rfl x).2
  simp only [fighterStageOutputs, List.mem_toFinset, fighterStageOutputList, List.mem_eraseDups,
    ite_eq_left hdl, ite_eq_left (And.intro hm hd), List.mem_append, List.mem_map,
    List.mem_filter, decide_eq_true_eq]
  rw [hsources]
  constructor
  · rintro (⟨_, hbase⟩ | ⟨tick, a, ha, hlen, hout⟩)
    · exact Or.inl (Or.inl (hv.mp hbase))
    · rcases hclass tick a ha hlen with hinit | ⟨_, _, hissued, hdummy, _⟩
      · exact Or.inl (Or.inr ⟨a, ⟨hinit, by omega⟩, hout⟩)
      · exact Or.inr ⟨hissued, hout ▸ hdummy⟩
  · rintro ((hbase | ⟨a, ⟨hinit, hlen⟩, hout⟩) | ⟨hissued, hdummy⟩)
    · exact Or.inl ⟨hdl, hv.mpr hbase⟩
    · exact Or.inr ⟨markerTick P.B (levelScale l), a, hpersist _ le_rfl a hinit, by omega, hout⟩
    · obtain ⟨z, tick, a, hz, -, ha, hout, hlen⟩ := hfresh.2 hissued
      have hzx : z = x := Option.some.inj (hz.symm.trans hdummy)
      exact Or.inr ⟨tick, a, ha, hlen.le, hout.trans hzx⟩

/-- The number of strings of complexity at most the level budget is the size of the initial
output table of a true-marker phase, plus one if the phase issued a dummy. -/
private lemma ncard_plainK_le_levelInput
    (P : FighterParams) (d l : ℕ) (hd : 1 ≤ d) (hlate : LateAdmissibleOccurrence P d l)
    (phase : FighterPhase)
    (hphase : TrueMarkerPhaseAt P d l (markerTick P.B (levelScale l)) phase) :
    {x | plainK (fighterU P d) x ≤ (levelInput d l : ℕ)}.ncard =
      (fighterStageOutputs P d (levelInput d l) phase.candidate.2
        phase.initialAllocations).card + if phase.dummyIssued then 1 else 0 := by
  have hiff := simple_fighterU_levelInput_iff P d l hd hlate phase hphase
  have hfresh := dummy_fresh_and_recorded_of_true_marker P d l phase hphase
  cases hissued : phase.dummyIssued
  · have hset : {x | plainK (fighterU P d) x ≤ (levelInput d l : ℕ)} =
        (fighterStageOutputs P d (levelInput d l) phase.candidate.2
          phase.initialAllocations : Set BitString) := by
      ext x
      refine (hiff x).trans ?_
      simp [hissued]
    rw [hset, Set.ncard_coe_finset]
    rfl
  · obtain ⟨z, tick, a, hz, -⟩ := hfresh.2 hissued
    have hset : {x | plainK (fighterU P d) x ≤ (levelInput d l : ℕ)} =
        insert z (fighterStageOutputs P d (levelInput d l) phase.candidate.2
          phase.initialAllocations : Set BitString) := by
      ext x
      refine (hiff x).trans ?_
      simp only [hissued, hz, Option.some.injEq, Set.mem_insert_iff, Finset.mem_coe, true_and]
      exact or_comm.trans (or_congr_left eq_comm)
    rw [hset, Set.ncard_insert_of_notMem (hfresh.1 z hz).1 (Finset.finite_toSet _),
      Set.ncard_coe_finset]
    rfl

/-- Tree-only low-answer stability, the exact count, and exclusion of later-level descriptions.
Blueprint node `constr:separation`. The phase record is taken after its start tick's closure,
so `dummyIssued` records the allocation actually performed at initialization. -/
theorem true_marker_phase_separation
    (P : FighterParams) (C cGap cRank d₀ d l : ℕ)
    (hfixed : FighterFixedConstants P C cGap cRank d₀)
    (hgood : GoodPadding P d₀ cRank cGap d) (hlate : LateAdmissibleOccurrence P d l)
    (phase : FighterPhase)
    (hphase : TrueMarkerPhaseAt P d l (markerTick P.B (levelScale l)) phase) :
    TrueMarkerSeparation P d l phase := by
  -- `hfixed` belongs to the frozen statement; the argument below does not need it.
  have _ := hfixed
  have hinit := game_target_eq_card_stageOutputs P d l phase hphase
  refine ⟨?_, ?_, (simple_finite_card_lt _ _).1, hinit, ?_, ?_⟩
  · exact stageAnswer_eq_initialAnswer_of_true_marker P d l hgood.positive hlate phase hphase
  · exact oracleAnswer_eq_initialAnswer_of_true_marker P d l hgood.positive hlate phase hphase
  · rw [hinit]
    exact ncard_plainK_le_levelInput P d l hgood.positive hlate phase hphase
  · exact higherLevelsIrrelevant_of_admissible P d l hgood.positive hlate

end Kolmogorov.Milovanov
