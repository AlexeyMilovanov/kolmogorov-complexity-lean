/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Construction.Diagonal.VirtualStabilization

/-!
# Saved phases and index growth along the fighter simulation

This module collects the state-level facts about the fighter construction that are needed to
compare the actual oracle with the virtual oracle of the true marker phase.

* `true_marker_actual_answer_cases` splits an actual positive of the level tree into three
  sources: the initial truth table of the true marker phase, a new simulation, or a new payoff.
* `fighterFinalVirtualAnswer_eq_true_of_initialAnswer` shows that an initially true query stays
  true in the final virtual answer.
* `active_phase_game_tables` records that a saved active phase keeps its initialised
  coordinate set and the exact candidate price table.
* `mem_J_of_simple_of_not_initialAnswer`, `price_le_strictExtensionCount` and
  `lt_length_of_markerTick_lt_eventAt` supply the retention, price and no-restart facts for a
  noninitial simulation positive.
* `FighterPhase.Descends` and `FighterState.Descends` track record ancestry together with the
  inclusion of the stored index sets through every operation of the construction; the lemmas
  `FighterState.Descends.*` prove that each operation, and hence a whole tick, preserves it.
  `TrueMarkerPhaseAt.indicesAt_subset_succ` is the resulting monotonicity of the stored indices
  of the true marker phase.

These facts are consumed by `Diagonal.SimulationEvents`, which proves the simulation case of the
oracle agreement, and by `Diagonal.OracleAgreement`, which assembles the three cases.
-/

namespace Kolmogorov.Milovanov

/-- At a late admissible occurrence with good padding, every actual positive query of the level
tree has one of three sources: its initial answer in the true marker phase is already true; it is
a simple noninitial query (`d ≤ q.2`); or it is the output of an allocated directive. In the last
two cases the initial answer is not true. -/
lemma true_marker_actual_answer_cases (P : FighterParams)
    (C cGap cRank d₀ d l : ℕ) (hfixed : FighterFixedConstants P C cGap cRank d₀)
    (hgood : GoodPadding P d₀ cRank cGap d) (hlate : LateAdmissibleOccurrence P d l) :
    ∀ q ∈ (P.family.tree d l (levelInput d l)).queries,
      fighterActualAnswer P d q = true →
      ((trueMarkerPhase P d l (markerTick P.B (levelScale l))).map
          (fun phase ↦ phase.initialAnswer P d q) = some true) ∨
      (d ≤ q.2 ∧ Simple P.B.V q.1 (q.2 - d) ∧
        (trueMarkerPhase P d l (markerTick P.B (levelScale l))).map
          (fun phase ↦ phase.initialAnswer P d q) ≠ some true) ∨
      (∃ tick a, a ∈ (fighterState P d tick).allocated ∧ a.input.length + 1 ≤ q.2 ∧
        a.output = q.1 ∧
        (trueMarkerPhase P d l (markerTick P.B (levelScale l))).map
          (fun phase ↦ phase.initialAnswer P d q) ≠ some true) := by
  intro q hq hactual
  obtain ⟨_, _, hlegal, _⟩ := true_marker_opponent_stream_legal P C cGap cRank d₀ d l
    hfixed hgood hlate
  obtain ⟨_, _, _, htick, _⟩ := hlegal
  obtain ⟨phase, hphase_at, _⟩ := htick (markerTick P.B (levelScale l)) (le_refl _)
  by_cases hinit : (trueMarkerPhase P d l (markerTick P.B (levelScale l))).map
      (fun phase ↦ phase.initialAnswer P d q) = some true
  · exact Or.inl hinit
  · right
    have heq : fighterActualAnswer P d q = coordinateOracleAnswer (fighterOracle P d) q :=
      congrFun (fighter_actual_answer_eq P d hgood.positive) q
    rw [heq] at hactual
    have hmem : q ∈ fighterOracle P d := by
      unfold coordinateOracleAnswer at hactual
      by_contra hnot
      have hdec : @decide (q ∈ fighterOracle P d) (Classical.propDecidable _) = false :=
        @decide_eq_false _ (Classical.propDecidable _) hnot
      rw [hdec] at hactual
      contradiction
    have hsep := true_marker_phase_separation P C cGap cRank d₀ d l hfixed hgood hlate phase
      hphase_at
    rcases (hsep.higher_levels.2.1 q hq).mp hmem with hsim | halloc
    · exact Or.inl ⟨hsim.1, hsim.2, hinit⟩
    · obtain ⟨tick, a, ha1, _, ha3, ha4⟩ := halloc
      exact Or.inr ⟨tick, a, ha1, ha3, ha4, hinit⟩

/-- A query that is true in the initial answer table of the true marker phase stays true in the
final virtual answer of the marker candidate. -/
lemma fighterFinalVirtualAnswer_eq_true_of_initialAnswer (P : FighterParams)
    (C cGap cRank d₀ d l : ℕ) (hfixed : FighterFixedConstants P C cGap cRank d₀)
    (hgood : GoodPadding P d₀ cRank cGap d) (hlate : LateAdmissibleOccurrence P d l) :
    ∀ q ∈ (P.family.tree d l (levelInput d l)).queries,
      (trueMarkerPhase P d l (markerTick P.B (levelScale l))).map
          (fun phase ↦ phase.initialAnswer P d q) = some true →
      fighterFinalVirtualAnswer P d l (markerCandidate P.B (levelScale l)) q = true := by
  intro q hq hinit
  rw [fighterFinalVirtualAnswer_eq_true_iff_exists_tick P d l q]
  refine ⟨markerTick P.B (levelScale l), le_rfl, ?_⟩
  rw [Option.map_eq_some_iff] at hinit
  rcases hinit with ⟨phase, hlookup, hyes⟩
  have hphase_virt : fighterVirtualAnswerAt P d l (markerTick P.B (levelScale l)) q =
      phase.virtualAnswer P d q := by
    simp [fighterVirtualAnswerAt, hlookup]
  rw [hphase_virt]
  obtain ⟨_, _, hlegal, _⟩ := true_marker_opponent_stream_legal P C cGap cRank d₀ d l
    hfixed hgood hlate
  obtain ⟨_, _, _, hrecords, _⟩ := hlegal
  obtain ⟨phase_record, hphase_rec, _⟩ := hrecords (markerTick P.B (levelScale l)) le_rfl
  have heq : phase = phase_record := by
    unfold trueMarkerPhase fighterPhaseAt at hlookup
    dsimp only at hlookup
    rw [hphase_rec.2.2.2] at hlookup
    dsimp only at hlookup
    rw [hphase_rec.2.2.1] at hlookup
    simp only [ite_true] at hlookup
    exact (Option.some.inj hlookup).symm
  subst heq
  have htable := true_marker_initial_table_on_tree P d l (markerTick P.B (levelScale l)) phase
    hphase_rec q hq
  rw [htable] at hyes
  unfold FighterPhase.virtualAnswer
  unfold normalizedAnswer at hyes ⊢
  simp only [Bool.or_eq_true, decide_eq_true_eq] at hyes ⊢
  rcases hyes with hlit | hmem
  · exact Or.inl hlit
  · rw [counter_answer_eq_true]
    exact Or.inr (Or.inl hmem)

/-- Any program emitted after the maximum short-program timestamp is longer than the scale.
This direct maximum argument uses no arbitrarily chosen asymptotic threshold. -/
lemma lt_length_of_markerTick_lt_eventAt
    (B : Base) (n tick pos : ℕ) (program output : BitString)
    (hlate : markerTick B n < tick)
    (hevent : eventAt B tick = some (tick, pos, program, output)) :
    n < program.length := by
  classical
  have ht : programTick B program = tick := by
    have heq : {t : ℕ | ∃ i x, eventAt B t = some (t, i, program, x)} = {tick} := by
      ext t
      constructor
      · rintro ⟨i, x, h⟩
        exact (canonical_enumeration_spec_unique B h hevent).1
      · rintro rfl
        exact ⟨pos, output, hevent⟩
    rw [programTick, heq, csInf_singleton]
  by_contra hlen
  have hmem : program ∈ (boundedPrograms n).toFinset := by
    simp only [List.mem_toFinset, mem_boundedPrograms_iff]
    omega
  have hm := Finset.le_sup (f := programTick B) hmem
  change programTick B program ≤ markerTick B n at hm
  omega

/-- A noninitial simulation positive is neither literal nor low, so its own coordinate is
retained in the coordinate set of the true marker phase. -/
lemma mem_J_of_simple_of_not_initialAnswer
    (P : FighterParams) (d l : ℕ) (q : Coordinate) (phase : FighterPhase)
    (hphase : TrueMarkerPhaseAt P d l (markerTick P.B (levelScale l)) phase)
    (hq : q ∈ (P.family.tree d l (levelInput d l)).queries)
    (hdq : d ≤ q.2) (hsim : Simple P.B.V q.1 (q.2 - d))
    (hnotinit : (trueMarkerPhase P d l (markerTick P.B (levelScale l))).map
      (fun p ↦ p.initialAnswer P d q) ≠ some true) :
    q ∈ phase.J d := by
  have hlookup : trueMarkerPhase P d l (markerTick P.B (levelScale l)) = some phase := by
    simp [trueMarkerPhase, fighterPhaseAt, hphase.2.2.2, hphase.2.2.1]
  have hnot : phase.initialAnswer P d q ≠ true := by
    intro h
    exact hnotinit (by simp [hlookup, h])
  have hnontrivial : q.2 < q.1.length + constructedLiteralConstant P.literal d := by
    by_contra h
    exact hnot (by simp [FighterPhase.initialAnswer, normalizedAnswer, Nat.le_of_not_gt h])
  have hhigh : levelInput d l < q.2 := by
    by_contra hlow
    obtain ⟨program, hlen, hprod⟩ := (simple_iff_exists_program _ _ _).mp hsim
    obtain ⟨seen, pos, hevent⟩ :=
      (canonical_enumeration_spec_complete P.B program q.1).mp hprod
    have hshort : program.length ≤ levelScale l := by
      have hlow' : q.2 ≤ levelInput d l := Nat.le_of_not_gt hlow
      dsimp only [levelInput] at hlow'
      omega
    have hseen : seen ≤ markerTick P.B (levelScale l) := by
      by_contra h
      have hlong := lt_length_of_markerTick_lt_eventAt P.B (levelScale l) seen pos program q.1
        (by omega) hevent
      omega
    have houtput : q.1 ∈ stageOutputs P.B (q.2 - d) seen := by
      simp only [stageOutputs, stageOutputList, List.mem_toFinset,
        List.mem_eraseDups, List.mem_filterMap]
      refine ⟨(seen, pos, program, q.1),
        List.mem_of_getElem? ((canonical_enumeration_spec_position P.B hevent).2.2), ?_⟩
      simp only [hlen, ite_true]
    have hinitial : q.1 ∈ fighterStageOutputs P d q.2 phase.candidate.2
        phase.initialAllocations := by
      simp only [fighterStageOutputs, fighterStageOutputList, List.mem_toFinset,
        List.mem_eraseDups, List.mem_append]
      left
      simp only [hdq, ↓reduceIte]
      apply List.mem_toFinset.mp
      simpa only [hphase.2.2.1, markerCandidate, stageOutputs] using
        (canonical_enumeration_spec_mono P.B (q.2 - d) hseen).1 houtput
    apply hnot
    simp only [FighterPhase.initialAnswer, normalizedAnswer, Bool.or_eq_true,
      decide_eq_true_eq]
    exact Or.inr hinitial
  rw [(active_phase_game_tables P d _ phase
    (List.mem_of_find?_eq_some hphase.2.2.2)).1, hphase.2.1]
  exact (mem_finite_referee_coordinates _ _ _ q.1 q.2).mpr
    ⟨q.2, hq, hnontrivial, by omega, le_rfl⟩

/-- The retained ranges and true marker let strict price completeness bound the price of a
retained simple coordinate by the finite set of extensions with base-machine descriptions of
length at most the upper scale. -/
lemma price_le_strictExtensionCount
    (P : FighterParams) (C cGap cRank d₀ d l : ℕ)
    (hfixed : FighterFixedConstants P C cGap cRank d₀)
    (hgood : GoodPadding P d₀ cRank cGap d) (hlate : LateAdmissibleOccurrence P d l)
    (q : Coordinate) (phase : FighterPhase)
    (hphase : TrueMarkerPhaseAt P d l (markerTick P.B (levelScale l)) phase)
    (hqJ : q ∈ phase.J d) (hsim : Simple P.B.V q.1 (q.2 - d)) :
    (phase.game d).price q ≤ strictExtensionCount P.B (levelScale l)
      (triple q.1 (q.2 - d) phase.candidate.1) := by
  obtain ⟨hcoords, hprices⟩ := active_phase_game_tables P d _ phase
    (List.mem_of_find?_eq_some hphase.2.2.2)
  have hret := hqJ
  rw [hcoords, hphase.2.1] at hret
  obtain ⟨hstr, hqrange, _⟩ := retained_coordinates_within_key_lemma_range
    P.family P.literal.cV P.n₀ d l P.threshold hgood.positive hlate.1 q.1 q.2 hret
  have hkey : KeyParameters P.B P.n₀ (levelScale l) phase.candidate q.1 (q.2 - d) :=
    ⟨(le_max_right _ _).trans hlate.1.2.1, ⟨2 * l, rfl⟩, hphase.2.2.1,
      hqrange, hstr.1.trans hstr.2.le⟩
  rw [hprices q hqJ, hphase.2.1]
  exact (hfixed.price.1 _ _ _ _ hkey).1 hsim

/-- `phase.Descends d next` records that `next` is a later record of the same phase as `phase`:
same level, same candidate and same game, and every stored index set of `phase` is included in
the one of `next`. -/
def FighterPhase.Descends (d : ℕ) (before after : FighterPhase) : Prop :=
  after.level = before.level ∧ after.candidate = before.candidate ∧
    after.game d = before.game d ∧
    ∀ q, before.indicesAt d q ⊆ after.indicesAt d q

private lemma FighterPhase.Descends.refl (d : ℕ) (phase : FighterPhase) :
    phase.Descends d phase :=
  ⟨rfl, rfl, rfl, fun _ ↦ Finset.Subset.refl _⟩

private lemma FighterPhase.Descends.trans {d : ℕ} {a b c : FighterPhase}
    (hab : a.Descends d b) (hbc : b.Descends d c) : a.Descends d c :=
  ⟨hbc.1.trans hab.1, hbc.2.1.trans hab.2.1, hbc.2.2.1.trans hab.2.2.1,
    fun q ↦ (hab.2.2.2 q).trans (hbc.2.2.2 q)⟩

private lemma FighterPhase.Descends.insertIndex
    (d : ℕ) (phase : FighterPhase) (q : Coordinate) (index : BitString) :
    phase.Descends d (phase.insertIndex d q index) := by
  classical
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro r
  by_cases hr : r ∈ (phase.game d).coordinates
  · rw [FighterPhase.indicesAt_insertIndex phase d q r index hr]
    split
    · exact Finset.subset_insert _ _
    · exact Finset.Subset.refl _
  · simp only [FighterPhase.indicesAt, hr, ite_false, Finset.empty_subset]

/-- `s.Descends d born t` records that every record of `t` is a descendant of a record of `s`
or was created at tick `born`: each active phase of `t` was born at tick `born` or descends from
the active phase of `s` at the same level, and each ended record of `t` was already ended in `s`,
was born at tick `born`, or descends from the active phase of `s` at its level. -/
def FighterState.Descends (d born : ℕ) (before after : FighterState) : Prop :=
  (∀ l next, after.activeAt d l = some next → next.candidate.2 = born ∨
    ∃ phase, before.activeAt d l = some phase ∧ phase.Descends d next) ∧
  ∀ e ∈ after.ended, e ∈ before.ended ∨ e.1.candidate.2 = born ∨
    ∃ phase, before.activeAt d e.1.level = some phase ∧ phase.Descends d e.1

private lemma FighterState.Descends.refl {d born : ℕ} (s : FighterState) :
    s.Descends d born s :=
  ⟨fun _ phase hp ↦ Or.inr ⟨phase, hp, FighterPhase.Descends.refl d phase⟩,
    fun _ he ↦ Or.inl he⟩

private lemma FighterState.Descends.trans {d born : ℕ} {a b c : FighterState}
    (hab : a.Descends d born b) (hbc : b.Descends d born c) : a.Descends d born c := by
  refine ⟨?_, ?_⟩
  · intro l next hn
    rcases hbc.1 l next hn with h | ⟨mid, hm, hmn⟩
    · exact Or.inl h
    · rcases hab.1 l mid hm with h | ⟨old, ho, hom⟩
      · exact Or.inl (by rw [hmn.2.1]; exact h)
      · exact Or.inr ⟨old, ho, hom.trans hmn⟩
  · intro e he
    rcases hbc.2 e he with he | h | ⟨mid, hm, hme⟩
    · exact hab.2 e he
    · exact Or.inr (Or.inl h)
    · rcases hab.1 e.1.level mid hm with h | ⟨old, ho, hom⟩
      · exact Or.inr (Or.inl (by rw [hme.2.1]; exact h))
      · exact Or.inr (Or.inr ⟨old, ho, hom.trans hme⟩)

private lemma FighterState.Descends.of_active_eq_of_ended_eq {d born : ℕ}
    (s t : FighterState) (ha : t.active = s.active) (he : t.ended = s.ended) :
    s.Descends d born t := by
  refine ⟨fun l next hn ↦ ?_, fun e h ↦ Or.inl (he ▸ h)⟩
  exact Or.inr ⟨next, by simpa [FighterState.activeAt, ha] using hn,
    FighterPhase.Descends.refl d next⟩

/-- `Descends` is preserved by folding a family of `Descends`-preserving steps over a list. -/
lemma FighterState.Descends.foldl {α : Type} (d born : ℕ)
    (f : α → FighterState → FighterState)
    (hf : ∀ a (s : FighterState), s.Descends d born (f a s)) (xs : List α) (s : FighterState) :
    s.Descends d born (xs.foldl (fun s a ↦ f a s) s) := by
  induction xs generalizing s with
  | nil => exact .refl s
  | cons a xs ih => exact (hf a s).trans (ih _)

private lemma FighterState.Descends.putPhase (d born : ℕ) (s : FighterState) (p : FighterPhase)
    (hp : p.candidate.2 = born ∨ ∃ old, s.activeAt d p.level = some old ∧ old.Descends d p) :
    s.Descends d born (s.putPhase d p) := by
  refine ⟨?_, fun _ h ↦ Or.inl h⟩
  intro j next hn
  by_cases hj : j = p.level
  · subst j
    have heq : next = p := by
      simpa [FighterState.putPhase, FighterState.activeAt] using hn.symm
    subst next
    exact hp
  · rw [FighterState.activeAt_putPhase_of_ne d j s p hj] at hn
    exact Or.inr ⟨next, hn, FighterPhase.Descends.refl d next⟩

private lemma FighterState.Descends.cancel (d born k : ℕ) (r : PhaseEnd) (cause : ℕ)
    (s : FighterState) : s.Descends d born (fighterCancel d k r cause s) := by
  unfold fighterCancel
  split
  · exact .refl s
  · rename_i phase hphase
    have hl : phase.level = k := FighterState.level_eq_of_activeAt_eq_some (p := phase) hphase
    refine ⟨?_, ?_⟩
    · intro j next hn
      have hj : j ≠ k := by
        intro h
        subst j
        have hmem := List.mem_of_find?_eq_some hn
        have hnlevel := FighterState.level_eq_of_activeAt_eq_some (p := next) hn
        simpa [hnlevel] using (List.mem_filter.mp hmem).2
      have hold : s.activeAt d j = some next := by
        change (s.active.filter (fun p ↦ p.level != k)).find?
          (fun p ↦ p.level == j) = some next at hn
        rwa [FighterState.find?_level_filter_ne _ _ _ hj] at hn
      exact Or.inr ⟨next, hold, FighterPhase.Descends.refl d next⟩
    · intro e he
      rcases List.mem_append.mp he with he | he
      · exact Or.inl he
      · have heq := List.mem_singleton.mp he
        subst e
        exact Or.inr (Or.inr ⟨phase, by simpa [hl] using hphase,
          FighterPhase.Descends.refl d phase⟩)

private lemma FighterState.Descends.abortAbove (d born l : ℕ) (s : FighterState) :
    s.Descends d born (fighterAbortAbove d l s) := by
  unfold fighterAbortAbove
  apply FighterState.Descends.foldl
  intro p t
  split
  · exact .cancel d born _ _ _ t
  · exact .refl t

private lemma FighterState.Descends.allocate (d born l : ℕ) (kind : DirectiveKind)
    (target : ℕ) (out : BitString) (s : FighterState) :
    s.Descends d born (fighterAllocate d l kind target out s).1 := by
  unfold fighterAllocate
  split
  · exact .refl s
  · cases hf : (if target = 0 then (none : Option BitString) else
        (fighterInputs d (target - 1)).find? (fun p ↦
          !s.allocated.any (fun a ↦ a.input == p))) with
    | none =>
      exact (FighterState.Descends.of_active_eq_of_ended_eq s _ rfl rfl).trans
        (.cancel d born l .saturated l _)
    | some input =>
      exact (FighterState.Descends.of_active_eq_of_ended_eq s _ rfl rfl).trans
        (.abortAbove d born l _)

private lemma FighterState.Descends.recordFulfilled (d born : ℕ) (q : Coordinate)
    (s : FighterState) :
    s.Descends d born
      { s with
        fulfilled := s.fulfilled ++ [q]
        active := s.active.map (fun p ↦ { p with pending := p.pending.filter (· != q) }) } := by
  refine ⟨?_, fun _ h ↦ Or.inl h⟩
  intro l next hn
  have hm :
      ({ s with
        fulfilled := s.fulfilled ++ [q]
        active := s.active.map (fun p ↦ { p with pending := p.pending.filter (· != q) }) }
        : FighterState).activeAt d l =
      (s.activeAt d l).map (fun p ↦ { p with pending := p.pending.filter (· != q) }) := by
    simp [FighterState.activeAt, List.find?_map]
  rw [hm] at hn
  cases hp : s.activeAt d l with
  | none => simp [hp] at hn
  | some p =>
    simp only [hp, Option.map_some, Option.some.injEq] at hn
    subst next
    exact Or.inr ⟨p, rfl, FighterPhase.Descends.refl d p⟩

private lemma FighterState.Descends.payoff (P : FighterParams) (d born l : ℕ)
    (q : Coordinate) (s : FighterState) : s.Descends d born (fighterPayoff P d l q s) := by
  unfold fighterPayoff
  split
  · exact .refl s
  · split
    · have ha := FighterState.Descends.allocate d born l .payoff q.2 q.1 s
      cases he : fighterAllocate d l .payoff q.2 q.1 s with
      | mk next success =>
        simp only [he] at ha ⊢
        cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
        · exact ha
        · exact ha.trans (.recordFulfilled d born q next)
    · exact .refl s

/-- A single `fighterFulfillReady` pass leads to a descendant state. -/
lemma FighterState.Descends.fulfillReady (P : FighterParams) (d born l : ℕ)
    (s : FighterState) : s.Descends d born (fighterFulfillReady P d l s) := by
  unfold fighterFulfillReady
  split
  · exact .refl s
  · apply FighterState.Descends.foldl
    intro q t
    exact .payoff P d born l q t

private lemma FighterState.Descends.fuelUnit (P : FighterParams) (d born l : ℕ)
    (q : Coordinate) (s : FighterState) :
    s.Descends d born (fighterFuelUnit P d l q s) := by
  unfold fighterFuelUnit
  split
  · exact .refl s
  · rename_i phase hphase
    have hl := FighterState.level_eq_of_activeAt_eq_some (p := phase) hphase
    split
    · let charged := { phase with controlledRemaining := phase.controlledRemaining - 1 }
      let index := fighterFreshString d (phase.indices[(phase.game d).coordinates.idxOf q]?.getD [])
      let out := pairCode (triple q.1 (q.2 - d) phase.candidate.1) index
      have hc : s.Descends d born (s.putPhase d charged) :=
        .putPhase d born s charged (Or.inr ⟨phase, by simpa [charged, hl] using hphase,
          FighterPhase.Descends.refl d phase⟩)
      have ha := FighterState.Descends.allocate d born l .fuel (levelUpper l + d) out
        (s.putPhase d charged)
      have hbefore := hc.trans ha
      change s.Descends d born
        (match fighterAllocate d l .fuel (levelUpper l + d) out (s.putPhase d charged) with
        | (next, success) => if success then
            fighterFulfillReady P d l (next.putPhase d
              ((charged.insertIndex d q index).fundRequests d next.fulfilled)) else next)
      cases he : fighterAllocate d l .fuel (levelUpper l + d) out (s.putPhase d charged) with
      | mk next success =>
        rw [he] at hbefore
        cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
        · exact hbefore
        · have hstay : next.activeAt d l = some charged := by
            have hh := FighterState.activeAt_fighterAllocate_of_success d l .fuel
              (levelUpper l + d) out (s.putPhase d charged) (by rw [he])
            rw [he] at hh
            exact hh.trans (by simp [FighterState.putPhase, FighterState.activeAt, charged, hl])
          refine hbefore.trans (.trans ?_ (.fulfillReady P d born l _))
          exact .putPhase d born next
            ((charged.insertIndex d q index).fundRequests d next.fulfilled)
            (Or.inr ⟨charged,
              by simpa [FighterPhase.fundRequests, FighterPhase.insertIndex, charged, hl]
                using hstay,
              FighterPhase.Descends.insertIndex d charged q index⟩)
    · exact .refl s

private lemma FighterState.Descends.fuelUnits (P : FighterParams) (d born l : ℕ)
    (q : Coordinate) (count : ℕ) (s : FighterState) :
    s.Descends d born (fighterFuelUnits P d l q count s) := by
  induction count generalizing s with
  | zero => exact .refl s
  | succ count ih => exact (FighterState.Descends.fuelUnit P d born l q s).trans (ih _)

/-- A single opponent move leads to a descendant state. -/
lemma FighterState.Descends.opponent (P : FighterParams) (d born l : ℕ)
    (event : ProgramEvent) (s : FighterState) :
    s.Descends d born (fighterOpponent P d l event s) := by
  unfold fighterOpponent
  split
  · exact .refl s
  · rename_i phase hphase
    have hl := FighterState.level_eq_of_activeAt_eq_some (p := phase) hphase
    split
    · exact .refl s
    · rename_i q index htuple
      split
      · exact .refl s
      · split
        · exact .cancel d born l .opponentExhausted l s
        · let inserted := phase.insertIndex d q index
          let next := { inserted with
            opponentRemaining := phase.opponentRemaining - 1
            buffer := (phase.game d).addCounters phase.buffer (phase.unitVector d q) }
          change s.Descends d born
            (fighterFulfillReady P d l (s.putPhase d (next.fundRequests d s.fulfilled)))
          refine .trans ?_ (.fulfillReady P d born l _)
          exact .putPhase d born s (next.fundRequests d s.fulfilled) (Or.inr ⟨phase,
            by simpa [FighterPhase.fundRequests, next, inserted, FighterPhase.insertIndex, hl]
              using hphase,
            FighterPhase.Descends.insertIndex d phase q index⟩)

private lemma FighterState.Descends.dummy (d born l : ℕ) (s : FighterState) :
    s.Descends d born (fighterDummy d l s) := by
  unfold fighterDummy
  split
  · exact .refl s
  · rename_i phase hphase
    have hl := FighterState.level_eq_of_activeAt_eq_some (p := phase) hphase
    split
    · exact .refl s
    · rename_i out hout
      split
      · exact .refl s
      · have ha := FighterState.Descends.allocate d born l .dummy (levelInput d l) out s
        cases he : fighterAllocate d l .dummy (levelInput d l) out s with
        | mk next success =>
          simp only [he] at ha ⊢
          cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
          · exact ha
          · have hstay : next.activeAt d l = some phase := by
              have hh := FighterState.activeAt_fighterAllocate_of_success d l .dummy
                (levelInput d l) out s (by rw [he])
              rw [he] at hh
              exact hh.trans hphase
            exact ha.trans (.putPhase d born next { phase with dummyIssued := true }
              (Or.inr ⟨phase, by simpa [hl] using hstay, FighterPhase.Descends.refl d phase⟩))

private lemma FighterState.Descends.flushBuffer (d born l : ℕ) (s : FighterState) :
    s.Descends d born ((fighterFlushBuffer d l s).getD s) := by
  cases hs : s.activeAt d l with
  | none =>
    simpa [fighterFlushBuffer, hs] using FighterState.Descends.refl (d := d) (born := born) s
  | some phase =>
    have hl := FighterState.level_eq_of_activeAt_eq_some (p := phase) hs
    simp only [fighterFlushBuffer, hs, bind, Option.bind_some]
    split
    · exact .putPhase d born s
        { phase with
          officialCode := ((phase.game d).afterMove (phase.official d) phase.buffer).encode
          buffer := List.replicate (phase.game d).coordinates.length 0 }
        (Or.inr ⟨phase, by simpa [hl] using hs, FighterPhase.Descends.refl d phase⟩)
    · exact .refl s

private lemma FighterState.Descends.strategyMove (P : FighterParams) (d born l : ℕ)
    (s : FighterState) : s.Descends d born ((fighterStrategyMove P d l s).getD s) := by
  cases hs : s.activeAt d l with
  | none =>
    simpa [fighterStrategyMove, hs] using FighterState.Descends.refl (d := d) (born := born) s
  | some phase =>
    simp only [fighterStrategyMove, hs, bind, Option.bind_some]
    split
    · cases hm : (phase.game d).strategy (phase.official d) with
      | none =>
        simp only [Option.bind_none, Option.getD_none]
        exact .refl s
      | some move =>
        simp only [Option.bind_some]
        split
        · let next := ((phase.game d).coordinates.zipIdx).foldl (fun s (q, i) ↦
            fighterFuelUnits P d l q (move[i]?.getD 0) s) s
          have hn : s.Descends d born next := by
            apply FighterState.Descends.foldl
            intro qi t
            exact .fuelUnits P d born l qi.1 (move[qi.2]?.getD 0) t
          change s.Descends d born
            ((match next.activeAt d l with
              | none => some next
              | some live => some (next.putPhase d
                  { live with officialCode :=
                      ((phase.game d).afterMove (phase.official d) move).encode })).getD s)
          cases hlive : next.activeAt d l with
          | none => exact hn
          | some live =>
            have hl := FighterState.level_eq_of_activeAt_eq_some (p := live) hlive
            exact hn.trans (.putPhase d born next
              { live with
                officialCode := ((phase.game d).afterMove (phase.official d) move).encode }
              (Or.inr ⟨live, by simpa [hl] using hlive, FighterPhase.Descends.refl d live⟩))
        · exact .refl s
    · exact .refl s

private lemma FighterState.Descends.levelAction (P : FighterParams) (d born l : ℕ)
    (s : FighterState) : s.Descends d born ((fighterLevelAction P d l s).getD s) := by
  cases hs : s.activeAt d l with
  | none =>
    simpa [fighterLevelAction, hs] using FighterState.Descends.refl (d := d) (born := born) s
  | some phase =>
    simp only [fighterLevelAction, hs, bind, Option.bind_some]
    split
    · exact .dummy d born l s
    · split
      · exact .payoff P d born l _ s
      · cases hf : fighterFlushBuffer d l s with
        | none => exact .strategyMove P d born l s
        | some next =>
          simpa only [hf] using FighterState.Descends.flushBuffer d born l s

/-- Running the closure of a level for any amount of fuel leads to a descendant state. -/
lemma FighterState.Descends.closure (P : FighterParams) (d born l fuel : ℕ)
    (s : FighterState) : s.Descends d born (fighterClosure P d l fuel s) := by
  induction fuel generalizing s with
  | zero => exact .refl s
  | succ fuel ih =>
    simp only [fighterClosure]
    cases ha : fighterLevelAction P d l s with
    | none => exact .refl s
    | some next =>
      have hn := FighterState.Descends.levelAction P d born l s
      simp only [ha, Option.getD_some] at hn
      exact hn.trans (ih next)

private lemma FighterState.Descends.startPhase (P : FighterParams) (d born l : ℕ)
    (candidate : Candidate) (s : FighterState) (hborn : candidate.2 = born) :
    s.Descends d born (fighterStartPhase P d l candidate s) := by
  let waiting := fighterAbortAbove d l (fighterCancel d l .replaced l s)
  have hw : s.Descends d born waiting :=
    (FighterState.Descends.cancel d born l .replaced l s).trans
      (.abortAbove d born l _)
  have hp := FighterState.Descends.putPhase d born waiting
    (fighter_construction P d l candidate waiting)
    (Or.inl (by simpa [fighter_construction, FighterPhase.fundRequests] using hborn))
  exact hw.trans (hp.trans (.of_active_eq_of_ended_eq _ _ rfl rfl))

/-- Processing one level at a tick, with an event that (if any) is born at tick `born`, leads to
a descendant state. -/
lemma FighterState.Descends.processLevel (P : FighterParams) (d born l : ℕ)
    (event : Option TimedEvent) (s : FighterState) (hevent : ∀ e, event = some e → e.1 = born) :
    s.Descends d born (fighterProcessLevel P d l event s) := by
  unfold fighterProcessLevel
  refine (FighterState.Descends.fulfillReady P d born l s).trans ?_
  cases event with
  | none => exact .closure P d born l _ _
  | some e =>
    dsimp only
    split
    · exact (FighterState.Descends.startPhase P d born l _ _ (hevent e rfl)).trans
        (.closure P d born l _ _)
    · exact (FighterState.Descends.opponent P d born l _ _).trans
        (.closure P d born l _ _)

/-- A whole tick of the construction, whose events are born at that tick, leads to a descendant
state. -/
private lemma FighterState.Descends.actions (P : FighterParams) (d tick : ℕ)
    (s : FighterState) : s.Descends d tick (fighter_actions P d tick s) := by
  unfold fighter_actions
  split
  · constructor
    · intro l phase hp
      simp [FighterState.activeAt, initialFighterState] at hp
    · intro e he
      simp [initialFighterState] at he
  · refine (FighterState.Descends.of_active_eq_of_ended_eq s _ rfl rfl).trans ?_
    apply FighterState.Descends.foldl
    intro l t
    exact .processLevel P d tick l (eventAt P.B tick) t
      (fun _ h ↦ (canonical_enumeration_spec_sound P.B h).1)

/-- One completed event preserves every stored index between surviving records of the same
true-marker phase. Only insertion changes an index set, and it never removes an index. -/
lemma TrueMarkerPhaseAt.indicesAt_subset_succ
    (P : FighterParams) (d l tick : ℕ) (phase next : FighterPhase)
    (hphase : TrueMarkerPhaseAt P d l tick phase)
    (hnext : TrueMarkerPhaseAt P d l (tick + 1) next) :
    ∀ q, phase.indicesAt d q ⊆ next.indicesAt d q := by
  have hstep := FighterState.Descends.actions P d (tick + 1) (fighterState P d tick)
  change (fighterState P d tick).Descends d (tick + 1) (fighterState P d (tick + 1)) at hstep
  rcases hstep.1 l next hnext.2.2.2 with hborn | ⟨old, hold, hgrowth⟩
  · rw [hnext.2.2.1] at hborn
    simp only [markerCandidate] at hborn
    have := hphase.1
    omega
  · have heq : old = phase := Option.some.inj (hold.symm.trans hphase.2.2.2)
    subst old
    exact hgrowth.2.2.2

end Kolmogorov.Milovanov
