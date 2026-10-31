/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Construction.Diagonal.AllocationGraph
import KolmogorovMathlib.RandomStrings.Plain.Construction.Diagonal.VirtualOutput

/-!
# Stabilization of the virtual oracle and its initial positives

The virtual oracle of the true-marker phase answers a query by reading the live counters of the
phase active at the current tick.  This module proves, for blueprint node `constr:agreement`:

* `fighterFinalVirtualAnswer_eq_true_iff_exists_tick`: the limiting (existential) virtual answer
  is positive exactly when some tick of the marker tail answers positively;
* `true_marker_virtual_output_stabilizes`: on the finite query tree, the virtual answers and the
  virtual output reach their limit at a finite tick, because positives persist;
* `fighterFinalVirtualAnswer_cases`: a positive limiting answer is a literal positive, a positive
  of the initial table of a phase, or a funded positive at a retained threshold;
* `fighterActualAnswer_of_literal` and `fighterActualAnswer_of_initialAnswer`: the literal and
  initial positives are already positive for the actual oracle.

The case analysis and the two actual-answer lemmas are used by `Diagonal.FundedFrames` and
`Diagonal.OracleAgreement` to show that the final virtual oracle is bounded by the actual one; the
limit characterization is used by `Diagonal.SimulationState` and `Diagonal.SimulationEvents` for
the converse inequality.
-/

namespace Kolmogorov.Milovanov

/-- The existential phase oracle is precisely positivity at some live tick in the marker tail.
Universal literal positives need no phase record; every other positive carries its own lookup
witness, whose timestamp cannot precede the marker. -/
theorem fighterFinalVirtualAnswer_eq_true_iff_exists_tick
    (P : FighterParams) (d l : ℕ) (q : Coordinate) :
    fighterFinalVirtualAnswer P d l (markerCandidate P.B (levelScale l)) q = true ↔
      ∃ tick ≥ markerTick P.B (levelScale l),
        fighterVirtualAnswerAt P d l tick q = true := by
  classical
  constructor
  · intro hfinal
    change (decide (q.1.length + constructedLiteralConstant P.literal d ≤ q.2) ||
      coordinateOracleAnswer (fighterPhaseOracle P d l
        (markerCandidate P.B (levelScale l))) q) = true at hfinal
    rw [Bool.or_eq_true] at hfinal
    rcases hfinal with hliteral | horacle
    · have hliteral := of_decide_eq_true hliteral
      refine ⟨markerTick P.B (levelScale l), le_rfl, ?_⟩
      cases hlookup : trueMarkerPhase P d l (markerTick P.B (levelScale l)) <;>
        simp [fighterVirtualAnswerAt, hlookup, FighterPhase.virtualAnswer,
          normalizedAnswer, hliteral]
    · have hmem : q ∈ fighterPhaseOracle P d l (markerCandidate P.B (levelScale l)) :=
        of_decide_eq_true horacle
      obtain ⟨tick, phase, hlookup, hyes⟩ := hmem
      have htime : markerTick P.B (levelScale l) ≤ tick := by
        by_contra h
        have hearly := trueMarkerPhase_eq_none_of_lt
          P d l tick (by omega)
        change trueMarkerPhase P d l tick = some phase at hlookup
        rw [hearly] at hlookup
        contradiction
      refine ⟨tick, htime, ?_⟩
      change trueMarkerPhase P d l tick = some phase at hlookup
      simpa [fighterVirtualAnswerAt, hlookup] using hyes
  · rintro ⟨tick, _, hyes⟩
    cases hlookup : trueMarkerPhase P d l tick with
    | none =>
      simp only [fighterVirtualAnswerAt, hlookup, normalizedAnswer, Bool.or_false,
        decide_eq_true_eq] at hyes
      simp [fighterFinalVirtualAnswer, normalizedAnswer, hyes]
    | some phase =>
      have hphase : phase.virtualAnswer P d q = true := by
        simpa [fighterVirtualAnswerAt, hlookup] using hyes
      have hmem : q ∈ fighterPhaseOracle P d l (markerCandidate P.B (levelScale l)) :=
        ⟨tick, phase, hlookup, hphase⟩
      simp [fighterFinalVirtualAnswer, normalizedAnswer, coordinateOracleAnswer, hmem]

/-- On a finite list of queries, persistent Boolean positives attain their existential
limit simultaneously. The induction also handles an empty tree and an all-negative
limit without choosing any nonexistent positive witness. -/
private theorem exists_tick_forall_mem_answer_eq
    (queries : List Coordinate) (answer : ℕ → Coordinate → Bool)
    (finalAnswer : Coordinate → Bool) (first : ℕ)
    (hpersist : ∀ tick ≥ first, ∀ later ≥ tick, ∀ q,
      answer tick q = true → answer later q = true)
    (hlimit : ∀ q, finalAnswer q = true ↔ ∃ tick ≥ first, answer tick q = true) :
    ∃ tick₀ ≥ first, ∀ tick ≥ tick₀, ∀ q ∈ queries,
      answer tick q = finalAnswer q := by
  classical
  induction queries with
  | nil => exact ⟨first, le_rfl, by simp⟩
  | cons q queries ih =>
    obtain ⟨tick₀, hfirst, htail⟩ := ih
    by_cases hq : finalAnswer q = true
    · obtain ⟨witness, hwitness, hyes⟩ := (hlimit q).mp hq
      refine ⟨max tick₀ witness, hfirst.trans (le_max_left _ _), ?_⟩
      intro tick htick r hr
      rcases List.mem_cons.mp hr with hsame | hr
      · subst r
        rw [hq]
        exact hpersist witness hwitness tick ((le_max_right _ _).trans htick) q hyes
      · exact htail tick ((le_max_left _ _).trans htick) r hr
    · refine ⟨tick₀, hfirst, ?_⟩
      intro tick htick r hr
      rcases List.mem_cons.mp hr with hsame | hr
      · subst r
        cases hnow : answer tick q <;> cases hfinal : finalAnswer q
        · rfl
        · exact False.elim (hq hfinal)
        · exact False.elim (hq ((hlimit q).mpr ⟨tick, hfirst.trans htick, hnow⟩))
        · rfl
      · exact htail tick htick r hr

/-- The named virtual limit is attained eventually on the whole tree, including its output.
Blueprint node `constr:agreement`. This supplies the missing eventual-constancy contract
for the stage-4 `fighterFinalVirtualAnswer` and `fighterFinalVirtualOutput` definitions. -/
theorem true_marker_virtual_output_stabilizes (P : FighterParams) (C cGap cRank d₀ d l : ℕ)
    (hfixed : FighterFixedConstants P C cGap cRank d₀)
    (hgood : GoodPadding P d₀ cRank cGap d) (hlate : LateAdmissibleOccurrence P d l) :
    ∃ tick₀ ≥ markerTick P.B (levelScale l), ∀ tick ≥ tick₀,
      (∀ q ∈ (P.family.tree d l (levelInput d l)).queries,
        fighterVirtualAnswerAt P d l tick q =
          fighterFinalVirtualAnswer P d l (markerCandidate P.B (levelScale l)) q) ∧
      fighterVirtualOutputAt P d l tick =
        fighterFinalVirtualOutput P d l (markerCandidate P.B (levelScale l)) := by
  obtain ⟨_, game, _, hrecords, _⟩ :=
    (true_marker_opponent_stream_legal P C cGap cRank d₀ d l hfixed hgood hlate).2.2.1
  have hactive : ∀ tick ≥ markerTick P.B (levelScale l),
      ∃ phase, TrueMarkerPhaseAt P d l tick phase := by
    intro tick htick
    obtain ⟨phase, hphase, _⟩ := hrecords tick htick
    exact ⟨phase, hphase⟩
  obtain ⟨tick₀, hfirst, hstable⟩ :=
    exists_tick_forall_mem_answer_eq
      (P.family.tree d l (levelInput d l)).queries (fighterVirtualAnswerAt P d l)
      (fighterFinalVirtualAnswer P d l (markerCandidate P.B (levelScale l)))
      (markerTick P.B (levelScale l))
      (fighterVirtualAnswerAt_persists P d l hactive)
      (fighterFinalVirtualAnswer_eq_true_iff_exists_tick P d l)
  refine ⟨tick₀, hfirst, fun tick htick ↦ ⟨hstable tick htick, ?_⟩⟩
  exact QueryTree.eval_eq_of_agree _ _ _ (hstable tick htick)

/-- A positive final virtual answer is a literal positive, a positive of the initial answer
table of a phase of the marker tail, or a funded positive: a retained coordinate with the same
string and a threshold at most the queried one whose price is covered by the live counters. -/
lemma fighterFinalVirtualAnswer_cases
    (P : FighterParams) (C cGap cRank d₀ d l : ℕ)
    (hfixed : FighterFixedConstants P C cGap cRank d₀)
    (hgood : GoodPadding P d₀ cRank cGap d) (hlate : LateAdmissibleOccurrence P d l)
    (q : Coordinate)
    (hq_virt : fighterFinalVirtualAnswer P d l (markerCandidate P.B (levelScale l)) q = true) :
    (q.1.length + constructedLiteralConstant P.literal d ≤ q.2) ∨
    (∃ tick ≥ markerTick P.B (levelScale l), ∃ phase, TrueMarkerPhaseAt P d l tick phase ∧
        phase.initialAnswer P d q = true) ∨
    (∃ tick ≥ markerTick P.B (levelScale l), ∃ phase, TrueMarkerPhaseAt P d l tick phase ∧
        ∃ retained ∈ phase.J d, retained.1 = q.1 ∧ retained.2 ≤ q.2 ∧
        (phase.game d).price retained ≤
          (phase.game d).coordinateValue phase.liveCounters retained) := by
  by_cases hlit : q.1.length + constructedLiteralConstant P.literal d ≤ q.2
  · exact Or.inl hlit
  right
  obtain ⟨tick, htick, hyes⟩ :=
    (fighterFinalVirtualAnswer_eq_true_iff_exists_tick P d l q).mp hq_virt
  obtain ⟨_, _, _, hrecords, _⟩ :=
    (true_marker_opponent_stream_legal P C cGap cRank d₀ d l hfixed hgood hlate).2.2.1
  obtain ⟨phase, hphase, _⟩ := hrecords tick htick
  rw [fighterVirtualAnswerAt_eq_of_trueMarkerPhaseAt P d l tick phase hphase] at hyes
  have hcounter : (phase.game d).counterAnswer phase.liveCounters q = true := by
    simpa [FighterPhase.virtualAnswer, normalizedAnswer, hlit] using hyes
  rw [counter_answer_eq_true] at hcounter
  rcases hcounter with hinit | ⟨retained, hret, hx, hk, hfunded⟩
  · left
    refine ⟨tick, htick, phase, hphase, ?_⟩
    have hsub := fighterState_forall_active_of_init P d tick
      (fun j _ code _ ↦ ∀ r ∈ (decodeCounterGame code).initialYes,
        r ∈ (P.family.tree d j (levelInput d j)).queries)
      (by
        intro j c s r hr
        have hyes : (decodeCounterGame (fighter_construction P d j c s).gameCode).initialYes =
            (P.family.tree d j (levelInput d j)).queries.filter (fun q ↦
              decide (q.1 ∈ fighterStageOutputs P d q.2 s.tick s.allocated)) := by
          dsimp only [fighter_construction, FighterPhase.fundRequests]
          rw [decode_encode_counter_game]
          unfold FiniteCounterGame.controlWinningPlayer
          split <;> rfl
        rw [hyes] at hr
        exact (List.mem_filter.mp hr).1)
      phase (List.mem_of_find?_eq_some hphase.2.2.2)
    have hq : q ∈ (P.family.tree d l (levelInput d l)).queries := by
      have h := hsub q hinit
      rwa [hphase.2.1] at h
    rw [true_marker_initial_table_on_tree P d l tick phase hphase q hq]
    simp [normalizedAnswer, hinit]
  · right
    exact ⟨tick, htick, phase, hphase, retained, hret, hx, hk, hfunded⟩

/-- Literal positives hold directly for the actual oracle under the common normalization. -/
lemma fighterActualAnswer_of_literal (P : FighterParams) (d : ℕ) (q : Coordinate)
    (hliteral : q.1.length + constructedLiteralConstant P.literal d ≤ q.2) :
    fighterActualAnswer P d q = true := by
  simp [fighterActualAnswer, normalizedAnswer, hliteral]

/-- An output in a finite stage table of the base machine has a description of the
corresponding length by the constructed machine (the simulation prefix of length `d`). -/
private theorem simple_fighterU_of_mem_stageOutputList
    (P : FighterParams) (d k tick : ℕ) (x : BitString) (hdk : d ≤ k)
    (hx : x ∈ stageOutputList P.B (k - d) tick) :
    Simple (fighterU P d) x k := by
  have hsim : Simple P.B.V x (k - d) :=
    (canonical_enumeration_spec_union P.B (k - d) x).mpr ⟨tick, by
      unfold stageOutputs
      rw [List.mem_toFinset]
      exact hx⟩
  obtain ⟨p, hp, hprod⟩ := (simple_iff_exists_program P.B.V x (k - d)).mp hsim
  apply (simple_iff_exists_program (fighterU P d) x k).mpr
  refine ⟨List.replicate d false ++ p, ?_, ?_⟩
  · simp only [List.length_append, List.length_replicate]
    omega
  · simpa [produces, fighterU, constructed_conditional_machine] using hprod

/-- Positives of the initial answer table of a phase of the marker tail remain actual
descriptions: each is a literal positive, an output of the base machine, or a permanent
allocation. -/
lemma fighterActualAnswer_of_initialAnswer (P : FighterParams) (d l : ℕ) (hd : 1 ≤ d)
    (q : Coordinate)
    (hinitial : ∃ tick ≥ markerTick P.B (levelScale l), ∃ phase,
      TrueMarkerPhaseAt P d l tick phase ∧ phase.initialAnswer P d q = true) :
    fighterActualAnswer P d q = true := by
  obtain ⟨tick, _, phase, hphase, hyes⟩ := hinitial
  have hactive : phase ∈ (fighterState P d tick).active :=
    List.mem_of_find?_eq_some hphase.2.2.2
  have hsnap := fighterState_initialAllocations_subset_allocated P d tick hd phase hactive
  simp only [FighterPhase.initialAnswer, normalizedAnswer, Bool.or_eq_true,
    decide_eq_true_eq] at hyes
  rcases hyes with hlit | hmem
  · exact fighterActualAnswer_of_literal P d q hlit
  · have hsimple : Simple (fighterU P d) q.1 q.2 := by
      simp only [fighterStageOutputs, fighterStageOutputList, List.mem_toFinset,
        List.mem_eraseDups, List.mem_append] at hmem
      rcases hmem with hbase | halloc
      · split_ifs at hbase with hdk
        · exact simple_fighterU_of_mem_stageOutputList P d q.2 phase.candidate.2 q.1 hdk hbase
        · simp at hbase
      · split_ifs at halloc with hk
        · obtain ⟨a, ha, hout⟩ := List.mem_map.mp halloc
          obtain ⟨ha, hlen⟩ := List.mem_filter.mp ha
          have hlen' : a.input.length ≤ q.2 - 1 := of_decide_eq_true hlen
          obtain ⟨hk1, _⟩ := hk
          have h := simple_of_mem_fighterState_allocated P d tick hd a (hsnap ha)
          rw [hout] at h
          exact simple_mono _ _ (by omega) h
        · simp at halloc
    simp [fighterActualAnswer, normalizedAnswer, coordinateOracleAnswer, fighterOracle,
      actualCoordinateOracle, hsimple]

end Kolmogorov.Milovanov
