/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.PhaseSeparationSources
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.PhaseSeparationCandidates
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.PhaseSeparationDummyTrace
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.PhaseSeparationDummyRecords

/-!
# Classification of short allocations at the true marker

This module supplies the allocation classification for blueprint node `constr:separation`.
At a true-marker phase, every sufficiently short permanent allocation either belongs to the
phase's initial table or is its issued dummy. Allocations from lower levels are already frozen;
the target bound excludes higher levels. At the same level, candidate timing identifies the
phase, and persistence and agreement of dummy records identify the output.

`PhaseSeparation` uses this classification to separate descriptions present at initialization
from the unique dummy output that can be added later.
-/

namespace Kolmogorov.Milovanov

/-- The dummy output of an active phase agrees with every allocation bearing its identity,
even when the allocation occurs after the phase is observed. -/
private lemma dummy_eq_of_mem_active
    (P : FighterParams) (d phaseTick allocationTick : ℕ) (phase : FighterPhase)
    (hphase : phase ∈ (fighterState P d phaseTick).active)
    (a : AllocatedDirective) (ha : a ∈ (fighterState P d allocationTick).allocated)
    (hkind : a.kind = .dummy) (hsame : a.level = phase.level)
    (hcandidate : a.candidate = phase.candidate) :
    phase.dummy = some a.output := by
  by_cases hd : d = 0
  · subst d
    have hempty : (fighterState P 0 phaseTick).active = [] := by
      cases phaseTick <;> simp [fighterState, fighter_actions, initialFighterState]
    simp only [hempty, List.not_mem_nil] at hphase
  · have hpos : 1 ≤ d := by omega
    by_cases ht : allocationTick ≤ phaseTick
    · exact dummy_eq_of_mem_record (Or.inl hphase)
        ((fighterState_tables_mono
          P d allocationTick phaseTick hpos ht).1 ha) hkind hsame hcandidate
    · have htrace :=
        exists_dummy_record_of_le hpos (by omega : phaseTick ≤ allocationTick) hphase
      rcases htrace with ⟨p, hp, hl, hc, hdum⟩ | ⟨e, he, hl, hc, hdum⟩
      · rw [← hdum]
        exact dummy_eq_of_mem_record (Or.inl hp) ha hkind (hsame.trans hl.symm)
          (hcandidate.trans hc.symm)
      · rw [← hdum]
        exact dummy_eq_of_mem_record (Or.inr ⟨e, he, rfl⟩) ha hkind
          (hsame.trans hl.symm) (hcandidate.trans hc.symm)

/-- A completed active phase with a stored dummy has issued it: an unissued dummy would
still enable a closure action. -/
private lemma dummy_issued_of_active_at
    (P : FighterParams) (d tick l : ℕ) (phase : FighterPhase)
    (hphase : (fighterState P d tick).activeAt d l = some phase)
    (output : BitString) (hdummy : phase.dummy = some output) :
    phase.dummyIssued = true := by
  have hlevel : phase.level = l := beq_iff_eq.mp
    (List.find?_some (p := fun p : FighterPhase ↦ p.level == l) hphase)
  have hcomplete := fighter_event_actions_complete P d tick phase
    (List.mem_of_find?_eq_some hphase)
  rw [hlevel] at hcomplete
  cases hi : phase.dummyIssued with
  | true => rfl
  | false => simp [fighterLevelAction, hphase, hdummy, hi] at hcomplete

/-- A small same-level allocation outside the initial table is the issued dummy of the
true-marker phase. -/
private lemma same_level_allocation_eq_dummy
    (P : FighterParams) (d l : ℕ)
    (phase : FighterPhase)
    (hphase : TrueMarkerPhaseAt P d l (markerTick P.B (levelScale l)) phase)
    (tick : ℕ) (a : AllocatedDirective) (ha : a ∈ (fighterState P d tick).allocated)
    (hsame : a.level = l)
    (htarget : a.target ≤ levelInput d l)
    (hnot_init : a ∉ phase.initialAllocations) :
    a.kind = .dummy ∧ a.candidate = phase.candidate ∧
      phase.dummyIssued = true ∧ phase.dummy = some a.output ∧
      a.target = levelInput d l := by
  obtain ⟨hkind, htarget_eq⟩ :=
    kind_eq_dummy_and_target_eq_levelInput P d tick l a ha hsame htarget
  have hvalid := validCandidate_of_mem_allocated P d tick a ha
  rw [hsame] at hvalid
  obtain ⟨hbefore, hat_marker⟩ :=
    candidate_tick_le_markerTick P.B (levelScale l) a.candidate hvalid
  have hactive := List.mem_of_find?_eq_some hphase.2.2.2
  have htime : a.candidate.2 = markerTick P.B (levelScale l) := by
    by_contra hne
    have hmarker : phase.candidate.2 = markerTick P.B (levelScale l) :=
      congrArg Prod.snd hphase.2.2.1
    exact hnot_init
      (allocation_mem_initialAllocations_of_candidate_lt
        hactive ha (hsame.trans hphase.2.1.symm) (by omega))
  have hcandidate : a.candidate = phase.candidate :=
    (hat_marker htime).trans hphase.2.2.1.symm
  have hdummy := dummy_eq_of_mem_active
    P d _ tick phase hactive a ha hkind (hsame.trans hphase.2.1.symm) hcandidate
  exact ⟨hkind, hcandidate,
    dummy_issued_of_active_at P d _ l phase hphase.2.2.2 a.output hdummy,
    hdummy, htarget_eq⟩

/-- Every short allocation at any tick either belongs to the true-marker phase's initial
table or is its issued dummy, whose input has the maximal permitted length. -/
lemma allocation_mem_initial_or_dummy_of_true_marker
    (P : FighterParams) (d l : ℕ) (hd : 1 ≤ d) (hlate : LateAdmissibleOccurrence P d l)
    (phase : FighterPhase)
    (hphase : TrueMarkerPhaseAt P d l (markerTick P.B (levelScale l)) phase) :
    ∀ tick a, a ∈ (fighterState P d tick).allocated →
      a.input.length + 1 ≤ levelInput d l →
      a ∈ phase.initialAllocations ∨
        (a.kind = .dummy ∧ a.candidate = phase.candidate ∧
          phase.dummyIssued = true ∧ phase.dummy = some a.output ∧
          a.input.length + 1 = levelInput d l) := by
  intro tick a ha hlen
  have hinv := target_eq_and_targetRange_of_mem_allocated P d tick hd a ha
  have hlen_eq : a.target = a.input.length + 1 := hinv.1
  have htarget_le : a.target ≤ levelInput d l := by omega
  have hlevel_le : a.level ≤ l :=
    level_le_of_targetRange d l a.level a.kind a.target hinv.2 htarget_le
  by_cases hinit : a ∈ phase.initialAllocations
  · exact Or.inl hinit
  · right
    have hlevel_eq : a.level = l := by
      by_contra hne
      have hlower : a.level < l := by omega
      exact hinit
        (mem_initialAllocations_of_level_lt P d l hd hlate phase hphase tick a ha hlower)
    have hsame := same_level_allocation_eq_dummy
      P d l phase hphase tick a ha hlevel_eq htarget_le hinit
    refine ⟨hsame.1, hsame.2.1, hsame.2.2.1, hsame.2.2.2.1, ?_⟩
    exact hlen_eq.symm.trans hsame.2.2.2.2

end Kolmogorov.Milovanov
