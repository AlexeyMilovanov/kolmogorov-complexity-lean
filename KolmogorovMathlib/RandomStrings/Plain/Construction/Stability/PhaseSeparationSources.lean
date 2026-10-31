/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.FundedRequest
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.PhaseSeparationAllocationGrowth
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.SettledLowerLevels

/-!
# Sources of the simple strings of a fighter decompressor

This module collects the semantic facts about the fighter decompressor `fighterU P d` and
the permanent allocation table that blueprint node `constr:separation` rests on:

* `simple_fighterU_iff`: a string is simple for `fighterU P d` at level `k` exactly when it is
  simple for the base machine at `k - d`, or it is the output of a permanent allocation whose
  input fits in `k`;
* `simple_iff_mem_stageOutputList_of_markerTick_le`: from the true marker on, the simulated
  base stages do not change for inputs of length at most the level input;
* `mem_allocated_of_mem_initialAllocations`: the snapshot saved by the true-marker phase
  stays in the permanent table;
* `target_eq_and_targetRange_of_mem_allocated`, `level_le_of_targetRange` and
  `mem_initialAllocations_of_level_lt`: allocations of higher levels are too long, those of
  lower levels are already frozen into the phase snapshot, and a small allocation of the same
  level is a dummy of exactly the level input
  (`kind_eq_dummy_and_target_eq_levelInput`).

`PhaseSeparation` and `PhaseSeparationClasses` combine these facts to separate the
descriptions present at initialization from the unique dummy that can be added later.
-/

namespace Kolmogorov.Milovanov

/-- A string is simple for the fighter decompressor `fighterU P d` at level `k` exactly when
it is simple for the base machine at level `k - d`, or it is the output of a permanent
allocation whose input fits in `k`. -/
lemma simple_fighterU_iff
    (P : FighterParams) (d : ℕ) (hd : 1 ≤ d) :
    ∀ k x, Simple (fighterU P d) x k ↔
      (d ≤ k ∧ Simple P.B.V x (k - d)) ∨
      ∃ tick a, a ∈ (fighterState P d tick).allocated ∧
        a.input.length + 1 ≤ k ∧ a.output = x := by
  intro k x
  constructor
  · intro h
    obtain ⟨p, hp, hprod⟩ := (simple_iff_exists_program (fighterU P d) x k).mp h
    change x ∈ constructed_conditional_machine P.B d (fighterG P d) (p, []) at hprod
    unfold constructed_conditional_machine at hprod
    dsimp only at hprod
    split_ifs at hprod with hs
    · left
      have hdlen : d ≤ p.length := by
        have hz := congrArg List.length hs
        simp only [List.length_take, List.length_replicate] at hz
        omega
      refine ⟨hdlen.trans hp, ?_⟩
      apply (simple_iff_exists_program P.B.V x (k - d)).mpr
      exact ⟨p.drop d, by simp only [List.length_drop]; omega, hprod⟩
    · right
      cases p with
      | nil => simp at hprod
      | cons b p =>
        cases b with
        | false => simp at hprod
        | true =>
          change x ∈ fighterG P d p at hprod
          rw [fighterG, ite_eq_right (by omega : d ≠ 0)] at hprod
          obtain ⟨tick, _, hlookup⟩ := Part.mem_bind_iff.mp hprod
          have ho := Part.mem_ofOption.mp hlookup
          change fighterAllocationAt P d tick p = some x at ho
          unfold fighterAllocationAt at ho
          obtain ⟨a, hfind, hout⟩ := Option.map_eq_some_iff.mp ho
          have hm := List.mem_of_find?_eq_some hfind
          have hin : a.input = p := beq_iff_eq.mp
            (List.find?_some (p := fun a : AllocatedDirective ↦ a.input == p) hfind)
          refine ⟨tick, a, hm, ?_, hout⟩
          simpa only [hin, List.length_cons] using hp
  · rintro (⟨hdk, hsim⟩ | ⟨tick, a, ha, hlen, hx⟩)
    · obtain ⟨q, hq, hprod⟩ := (simple_iff_exists_program P.B.V x (k - d)).mp hsim
      apply (simple_iff_exists_program (fighterU P d) x k).mpr
      refine ⟨List.replicate d false ++ q, ?_, ?_⟩
      · simp only [List.length_append, List.length_replicate]
        omega
      · simpa [produces, fighterU, constructed_conditional_machine] using hprod
    · apply (simple_iff_exists_program (fighterU P d) x k).mpr
      refine ⟨true :: a.input, by simpa only [List.length_cons] using hlen, ?_⟩
      have hg := output_mem_fighterG_of_mem_allocated P d tick hd a ha
      cases d with
      | zero => omega
      | succ d =>
        simpa [produces, fighterU, constructed_conditional_machine, List.replicate_succ,
          hx] using hg

/-- For levels `k` up to the level input, a string is simple for the base machine at level
`k - d` exactly when it is listed in the stage outputs of the base machine at any tick from
the marker tick on, and at the tick of the true-marker phase's candidate. -/
lemma simple_iff_mem_stageOutputList_of_markerTick_le
    (P : FighterParams) (d l : ℕ) (phase : FighterPhase)
    (hphase : TrueMarkerPhaseAt P d l (markerTick P.B (levelScale l)) phase) :
    ∀ k ≤ levelInput d l, d ≤ k → ∀ tick ≥ markerTick P.B (levelScale l), ∀ x,
      (Simple P.B.V x (k - d) ↔ x ∈ stageOutputList P.B (k - d) tick) ∧
      (Simple P.B.V x (k - d) ↔ x ∈ stageOutputList P.B (k - d) phase.candidate.2) := by
  intro k hkd _hdk tick htick x
  have hp : phase.candidate.2 = markerTick P.B (levelScale l) := congrArg Prod.snd hphase.2.2.1
  have hu : k - d ≤ levelScale l := by
    unfold levelInput at hkd
    omega
  have hiff : ∀ t ≥ markerTick P.B (levelScale l),
      Simple P.B.V x (k - d) ↔ x ∈ stageOutputList P.B (k - d) t := by
    intro t ht
    constructor
    · intro hx
      obtain ⟨p, hp_len, hp_prod⟩ := (simple_iff_exists_program P.B.V x (k - d)).mp hx
      obtain ⟨t', i, h_event_t⟩ := (canonical_enumeration_spec_complete P.B p x).mp hp_prod
      have h_tick_eq_t : programTick P.B p = t' := by
        have h_t_in_set : t' ∈ {t'' : ℕ | ∃ i' x', eventAt P.B t'' = some (t'', i', p, x')} := by
          simp only [Set.mem_ofPred_eq]
          exact ⟨i, x, h_event_t⟩
        obtain ⟨i', x', h_event_inf⟩ := Nat.sInf_mem (Set.nonempty_of_mem h_t_in_set)
        exact (canonical_enumeration_spec_unique P.B h_event_t h_event_inf).1.symm
      have h_t_le_marker : t' ≤ markerTick P.B (levelScale l) := by
        rw [← h_tick_eq_t]
        unfold markerTick
        apply Finset.le_sup
        rw [List.mem_toFinset, mem_boundedPrograms_iff]
        omega
      have h_x_in_t : x ∈ stageOutputs P.B (k - d) t' := by
        unfold stageOutputs stageOutputList
        rw [List.mem_toFinset, List.mem_eraseDups, List.mem_filterMap]
        obtain ⟨_, _, h_get⟩ := canonical_enumeration_spec_position P.B h_event_t
        exact ⟨(t', i, p, x), List.mem_of_getElem? h_get, by simp only [hp_len, ite_true]⟩
      have h_x_in_t_final := (canonical_enumeration_spec_mono P.B (k - d)
        (by omega : t' ≤ t)).1 h_x_in_t
      unfold stageOutputs at h_x_in_t_final
      rwa [List.mem_toFinset] at h_x_in_t_final
    · intro hx
      refine (canonical_enumeration_spec_union P.B (k - d) x).mpr ⟨t, ?_⟩
      unfold stageOutputs
      rwa [List.mem_toFinset]
  refine ⟨hiff tick htick, ?_⟩
  rw [hp]
  exact hiff (markerTick P.B (levelScale l)) (by omega)

/-- The allocations saved in the true-marker phase's initial table persist in the permanent
allocation table at every tick from the marker on. -/
lemma mem_allocated_of_mem_initialAllocations
    (P : FighterParams) (d l : ℕ) (hd : 1 ≤ d) (phase : FighterPhase)
    (hphase : TrueMarkerPhaseAt P d l (markerTick P.B (levelScale l)) phase) :
    ∀ tick ≥ markerTick P.B (levelScale l), ∀ a,
      a ∈ phase.initialAllocations → a ∈ (fighterState P d tick).allocated := by
  intro tick htick a ha
  exact (fighterState_tables_mono P d _ tick hd htick).1
    (fighterState_initialAllocations_subset_allocated P d _ hd phase
      (List.mem_of_find?_eq_some hphase.2.2.2) ha)

/-- Every permanent allocation has a target one longer than its input, and the target lies in
the range of its level and kind. -/
lemma target_eq_and_targetRange_of_mem_allocated
    (P : FighterParams) (d tick : ℕ)
    (hd : 1 ≤ d) (a : AllocatedDirective) (ha : a ∈ (fighterState P d tick).allocated) :
    a.target = a.input.length + 1 ∧ FighterTargetRange d a.level a.kind a.target :=
  ⟨(fighterState_target_eq_input_length_add_one P d tick hd a ha).symm,
    (fighter_directive_target_ranges P d tick a ha).2⟩

/-- A target in the range of `level` that does not exceed the input budget `levelInput d l`
forces `level ≤ l`: the target ranges of higher levels lie strictly above the budget. -/
lemma level_le_of_targetRange (d l level : ℕ) (kind : DirectiveKind) (target : ℕ)
    (hrange : FighterTargetRange d level kind target) (htarget : target ≤ levelInput d l) :
    level ≤ l := by
  by_contra hle
  have hlt : l < level := not_le.mp hle
  have hscale : levelScale l < levelUpper l := levelScale_lt_levelUpper l
  have hgap : levelUpper l < levelScale level :=
    (tower_lt_tower_add_one (2 * l + 1)).trans_le (tower_le_tower (by omega))
  have hupper : levelUpper l < levelUpper level :=
    (tower_lt_tower_add_one (2 * l + 1)).trans_le (tower_le_tower (by omega))
  unfold levelInput at htarget
  cases kind <;> simp only [FighterTargetRange] at hrange <;> omega

/-- An allocation of a level below that of the true-marker phase is already frozen into the
phase's initial allocation table. -/
lemma mem_initialAllocations_of_level_lt
    (P : FighterParams) (d l : ℕ) (hd : 1 ≤ d) (hlate : LateAdmissibleOccurrence P d l)
    (phase : FighterPhase)
    (hphase : TrueMarkerPhaseAt P d l (markerTick P.B (levelScale l)) phase)
    (tick : ℕ) (a : AllocatedDirective) (ha : a ∈ (fighterState P d tick).allocated)
    (hlower : a.level < l) :
    a ∈ phase.initialAllocations := by
  classical
  let T := markerTick P.B (levelScale l)
  have hgap := hlate.2
  obtain ⟨u, i, p, x, hev⟩ :
      ∃ u i p x, eventAt P.B T = some (u, i, p, x) := by
    cases he : eventAt P.B T with
    | none =>
      have hz : lastProgram P.B (levelScale l) = [] := by
        simp [lastProgram, ← show T = markerTick P.B (levelScale l) from rfl, he]
      rw [hz] at hgap
      simp at hgap
    | some e =>
      obtain ⟨u, i, p, x⟩ := e
      exact ⟨u, i, p, x, rfl⟩
  have hu := (canonical_enumeration_spec_sound P.B hev).1
  change u = T at hu
  subst u
  have hT : 0 < T :=
    (canonical_enumeration_spec_position P.B hev).1
  have hevents : ∀ t ≥ T, ∀ e,
      eventAt P.B t = some e → levelLower l < e.2.2.1.length := by
    intro t ht e he
    by_cases heq : t = T
    · subst t
      have hp : lastProgram P.B (levelScale l) = e.2.2.1 := by
        simp [lastProgram, ← show T = markerTick P.B (levelScale l) from rfl, he]
      rwa [← hp]
    · obtain ⟨v, j, q, y⟩ := e
      have hv := (canonical_enumeration_spec_sound P.B he).1
      change v = t at hv
      subst v
      have hlong := length_gt_of_eventAt_of_markerTick_lt
        P.B (levelScale l) t (by dsimp [T] at *; omega) j q y he
      have hscale : levelLower l ≤ levelScale l := by
        apply tower_le_tower
        omega
      exact hscale.trans_lt hlong
  have hactive := List.mem_of_find?_eq_some hphase.2.2.2
  have hs := fighterState_allocated_subset_initialAllocations_of_lt P d T hd phase hactive
  have hc : phase.candidate.2 = T :=
    congrArg Prod.snd hphase.2.2.1
  by_cases ht : tick < T
  · exact hs tick (by rw [hc]; exact ht) ha
  · have hh := (fighterState_lower_frozen_of_long_events
        P d l T hd hT hevents tick (by omega)).1 a.level hlower
    have hf := congrArg (fun h ↦ h.2.2.1) hh
    change (fighterState P d tick).allocated.filter (fun b ↦ b.level == a.level) =
      (fighterState P d (T - 1)).allocated.filter (fun b ↦ b.level == a.level) at hf
    have hm : a ∈ (fighterState P d tick).allocated.filter
        (fun b ↦ b.level == a.level) := by simp [ha]
    rw [hf] at hm
    exact hs (T - 1) (by rw [hc]; omega) (List.mem_filter.mp hm).1

/-- The disjoint target ranges force every small same-level allocation to be a dummy at
exactly the level input. -/
lemma kind_eq_dummy_and_target_eq_levelInput
    (P : FighterParams) (d tick l : ℕ) (a : AllocatedDirective)
    (ha : a ∈ (fighterState P d tick).allocated) (hsame : a.level = l)
    (htarget : a.target ≤ levelInput d l) :
    a.kind = .dummy ∧ a.target = levelInput d l := by
  have hrange := (fighter_directive_target_ranges P d tick a ha).2
  rw [hsame] at hrange
  have hscale : levelScale l < levelUpper l := levelScale_lt_levelUpper l
  cases hk : a.kind with
  | dummy => exact ⟨rfl, by simpa only [FighterTargetRange, hk, levelInput] using hrange⟩
  | payoff =>
    simp only [FighterTargetRange, hk] at hrange
    unfold levelInput at htarget
    omega
  | fuel =>
    simp only [FighterTargetRange, hk] at hrange
    unfold levelInput at htarget
    omega

end Kolmogorov.Milovanov
