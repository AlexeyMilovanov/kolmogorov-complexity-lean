/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/

import KolmogorovMathlib.Restricted.Family
import KolmogorovMathlib.Restricted.GreedyCover
import KolmogorovMathlib.Foundation.EnumerationComplexity
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.DescriptionSnapshot

/-!
# M4: Substrategy Bookkeeping

This file provides the finite-stage bookkeeping for the improving descriptions
strategy.  The proved selection lemmas choose a small indexed greedy subcover of
the currently visible high-multiplicity strings.  These lemmas feed the
effective/enumerable marked-code stream (see `EffectiveSelection.lean`) that
turns this finite selection into a complexity bound.
-/

namespace Kolmogorov

open StagedEnumeration
open Nat.Partrec (Code)

/-- A canonical code from the family enumeration representing a member of
`𝒜` of log-size at most `j`. -/
def IsFamilyModelCode (𝒜 : PreDescriptionFamily) (j : ℕ) (w : BitString) : Prop :=
  ∃ (S : Finset BitString) (hS : S.Nonempty),
    𝒜.mem S ∧ w = (codedUniformOn S hS).code ∧ S.card ≤ 2 ^ j

/-- A canonical family-model code whose decoded model contains `x`.  The
existential is phrased through canonical uniform codes so multiplicity is by
distinct model codes, not by repeated appearances in the enumeration. -/
def IsFamilyDescriptionCode (𝒜 : PreDescriptionFamily) (j : ℕ)
    (x w : BitString) : Prop :=
  ∃ (S : Finset BitString) (hS : S.Nonempty),
    𝒜.mem S ∧ w = (codedUniformOn S hS).code ∧ S.card ≤ 2 ^ j ∧ x ∈ S

/-- Distinct family-model codes of size at most `2^j` visible by stage `t`. -/
noncomputable def familyStageModelCodes (c : Code) (i : ℕ) (𝒜 : PreDescriptionFamily) (j t : ℕ) :
    Finset BitString := by
  classical
  exact ((𝒜.enumeration.enum t).toFinset ∩ (snapshotCodes c i t).toFinset).filter
    (fun w => IsFamilyModelCode 𝒜 j w)

theorem mem_familyStageModelCodes (c : Code) (i : ℕ) (𝒜 : PreDescriptionFamily)
    (j t : ℕ) (w : BitString) :
    w ∈ familyStageModelCodes c i 𝒜 j t ↔
      w ∈ ((𝒜.enumeration.enum t).toFinset ∩ (snapshotCodes c i t).toFinset) ∧
        IsFamilyModelCode 𝒜 j w := by
  unfold familyStageModelCodes
  simp

/-- Distinct visible family descriptions of `x` of size at most `2^j`. -/
noncomputable def familyStageDescriptionCodes (c : Code) (i : ℕ) (𝒜 : PreDescriptionFamily)
    (j t : ℕ) (x : BitString) : Finset BitString := by
  classical
  exact ((𝒜.enumeration.enum t).toFinset ∩ (snapshotCodes c i t).toFinset).filter
    (fun w => IsFamilyDescriptionCode 𝒜 j x w)

theorem mem_familyStageDescriptionCodes (c : Code) (i : ℕ) (𝒜 : PreDescriptionFamily)
    (j t : ℕ) (x w : BitString) :
    w ∈ familyStageDescriptionCodes c i 𝒜 j t x ↔
      w ∈ ((𝒜.enumeration.enum t).toFinset ∩ (snapshotCodes c i t).toFinset) ∧
        IsFamilyDescriptionCode 𝒜 j x w := by
  unfold familyStageDescriptionCodes
  simp

/-- The length-`n` strings covered by the family description code `w`. -/
noncomputable def selectionCoverSet (𝒜 : PreDescriptionFamily) (n j : ℕ)
    (w : BitString) : Finset BitString := by
  classical
  exact (stringsOfLength n).filter (fun x => IsFamilyDescriptionCode 𝒜 j x w)

theorem mem_selectionCoverSet (𝒜 : PreDescriptionFamily) (n j : ℕ)
    (x w : BitString) :
    x ∈ selectionCoverSet 𝒜 n j w ↔
      x ∈ stringsOfLength n ∧ IsFamilyDescriptionCode 𝒜 j x w := by
  unfold selectionCoverSet
  simp

/-- The currently rich length-`n` strings: those with at least `2^k` visible
restricted descriptions at this stage. -/
noncomputable def selectionTarget (c : Code) (𝒜 : PreDescriptionFamily)
    (n i j k t : ℕ) : Finset BitString := by
  classical
  exact (stringsOfLength n).filter
    (fun x => 2 ^ k ≤ (familyStageDescriptionCodes c i 𝒜 j t x).card)

theorem isFamilyModelCode_of_description {𝒜 : PreDescriptionFamily} {j : ℕ}
    {x w : BitString} (h : IsFamilyDescriptionCode 𝒜 j x w) :
    IsFamilyModelCode 𝒜 j w := by
  rcases h with ⟨S, hS, hmem, hcode, hcard, _hxS⟩
  exact ⟨S, hS, hmem, hcode, hcard⟩

theorem familyStageDescriptionCodes_eq_filter_cover (c : Code) (i : ℕ)
    (𝒜 : PreDescriptionFamily) (n j t : ℕ) (x : BitString) (hxlen : x.length = n) :
    familyStageDescriptionCodes c i 𝒜 j t x =
      (familyStageModelCodes c i 𝒜 j t).filter
        (fun w => x ∈ selectionCoverSet 𝒜 n j w) := by
  classical
  ext w
  constructor
  · intro hw
    rw [mem_familyStageDescriptionCodes] at hw
    rw [Finset.mem_filter, mem_familyStageModelCodes]
    refine ⟨⟨hw.1, isFamilyModelCode_of_description hw.2⟩, ?_⟩
    rw [mem_selectionCoverSet]
    exact ⟨(memStringsOfLength n x).mpr hxlen, hw.2⟩
  · intro hw
    rw [Finset.mem_filter, mem_familyStageModelCodes] at hw
    rw [mem_familyStageDescriptionCodes]
    have hdesc : IsFamilyDescriptionCode 𝒜 j x w := by
      exact (mem_selectionCoverSet 𝒜 n j x w).mp hw.2 |>.2
    exact ⟨hw.1.1, hdesc⟩

theorem familyStageModelCodes_card_le (c : Code) (i : ℕ)
    (𝒜 : PreDescriptionFamily) (j t : ℕ) :
    (familyStageModelCodes c i 𝒜 j t).card ≤ 2 ^ (i + 1) := by
  classical
  have hlt : (familyStageModelCodes c i 𝒜 j t).card < 2 ^ (i + 1) := by
    calc (familyStageModelCodes c i 𝒜 j t).card
        ≤ (((𝒜.enumeration.enum t).toFinset ∩ (snapshotCodes c i t).toFinset).card) := by
            unfold familyStageModelCodes
            exact Finset.card_filter_le _ _
      _ ≤ (snapshotCodes c i t).toFinset.card :=
            Finset.card_le_card Finset.inter_subset_right
      _ ≤ (snapshotCodes c i t).length := List.toFinset_card_le _
      _ ≤ (boundedPrograms i).length := by
            unfold snapshotCodes
            exact List.length_filterMap_le _ _
      _ < 2 ^ (i + 1) := length_boundedPrograms_lt i
  exact Nat.le_of_lt hlt

theorem selectionTarget_log_bound (c : Code) (𝒜 : PreDescriptionFamily)
    (n i j k t : ℕ) :
    Nat.log2 (selectionTarget c 𝒜 n i j k t).card + 1 ≤ n + 1 := by
  classical
  set T := selectionTarget c 𝒜 n i j k t
  have hsub : T ⊆ stringsOfLength n := by
    intro x hx
    have hx' : x ∈ selectionTarget c 𝒜 n i j k t := by simpa [T] using hx
    rw [selectionTarget, Finset.mem_filter] at hx'
    exact hx'.1
  have hcard : T.card ≤ 2 ^ n := by
    rw [← cardStringsOfLength n]
    exact Finset.card_le_card hsub
  by_cases hzero : T.card = 0
  · simp [hzero]
  · have hltpow : T.card < 2 ^ (n + 1) :=
      lt_of_le_of_lt hcard (Nat.pow_lt_pow_succ (by norm_num : 1 < 2))
    have hloglt : Nat.log 2 T.card < n + 1 :=
      Nat.log_lt_of_lt_pow hzero hltpow
    have hlogle : Nat.log2 T.card ≤ n := by
      rw [Nat.log2_eq_log_two]
      omega
    omega

theorem exists_selectionStrategy (c : Code) (𝒜 : PreDescriptionFamily)
    (n i j k t : ℕ) :
    ∃ L : List BitString,
      L.length ≤ (i + 1) * (i + 1) * (n + 1) * 2 ^ (i + 1 - k) ∧
      ∀ x : BitString, x.length = n →
        2 ^ k ≤ (familyStageDescriptionCodes c i 𝒜 j t x).card →
        ∃ w ∈ L, IsFamilyDescriptionCode 𝒜 j x w := by
  classical
  set T := selectionTarget c 𝒜 n i j k t
  set S := familyStageModelCodes c i 𝒜 j t
  set cover := selectionCoverSet 𝒜 n j
  by_cases hTne : T.Nonempty
  · have hm : ∀ x ∈ T, 2 ^ k ≤ (S.filter (fun w => x ∈ cover w)).card := by
      intro x hxT
      have hxT' : x ∈ selectionTarget c 𝒜 n i j k t := by simpa [T] using hxT
      rw [selectionTarget, Finset.mem_filter] at hxT'
      have hxlen : x.length = n := (memStringsOfLength n x).mp hxT'.1
      have hEq := familyStageDescriptionCodes_eq_filter_cover c i 𝒜 n j t x hxlen
      simpa [S, cover, hEq] using hxT'.2
    obtain ⟨C, hCS, hcov, hCbound⟩ :=
      greedy_cover_indexed T S cover (2 ^ k) (pow_pos (by decide) k) hm
    refine ⟨C.toList, ?_, ?_⟩
    · rw [Finset.length_toList]
      have hSbound : S.card ≤ 2 ^ (i + 1) := by
        simpa [S] using familyStageModelCodes_card_le c i 𝒜 j t
      have hTlog : Nat.log2 T.card + 1 ≤ n + 1 := by
        simpa [T] using selectionTarget_log_bound c 𝒜 n i j k t
      have hraw : C.card * 2 ^ k ≤ 2 ^ (i + 1) * (n + 1) := by
        calc C.card * 2 ^ k ≤ S.card * (Nat.log2 T.card + 1) := hCbound
          _ ≤ 2 ^ (i + 1) * (n + 1) := Nat.mul_le_mul hSbound hTlog
      obtain ⟨x0, hx0T⟩ := hTne
      have hkpow : 2 ^ k ≤ 2 ^ (i + 1) := by
        calc 2 ^ k ≤ (S.filter (fun w => x0 ∈ cover w)).card := hm x0 hx0T
          _ ≤ S.card := Finset.card_filter_le S _
          _ ≤ 2 ^ (i + 1) := hSbound
      have hki : k ≤ i + 1 :=
        (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hkpow
      have hfactor : 2 ^ (i + 1) = 2 ^ (i + 1 - k) * 2 ^ k := by
        rw [← pow_add, Nat.sub_add_cancel hki]
      have hmul : C.card * 2 ^ k ≤ ((n + 1) * 2 ^ (i + 1 - k)) * 2 ^ k := by
        have hrhs : 2 ^ (i + 1) * (n + 1) =
            ((n + 1) * 2 ^ (i + 1 - k)) * 2 ^ k := by
          rw [hfactor]
          ring
        rwa [hrhs] at hraw
      have hsmall : C.card ≤ (n + 1) * 2 ^ (i + 1 - k) :=
        Nat.le_of_mul_le_mul_right hmul (pow_pos (by decide) k)
      have hcoef : 1 ≤ (i + 1) * (i + 1) :=
        Nat.succ_le_of_lt (Nat.mul_pos (Nat.succ_pos i) (Nat.succ_pos i))
      calc C.card ≤ (n + 1) * 2 ^ (i + 1 - k) := hsmall
        _ = ((n + 1) * 2 ^ (i + 1 - k)) * 1 := by ring
        _ ≤ ((n + 1) * 2 ^ (i + 1 - k)) * ((i + 1) * (i + 1)) :=
            Nat.mul_le_mul_left _ hcoef
        _ = (i + 1) * (i + 1) * (n + 1) * 2 ^ (i + 1 - k) := by ring
    · intro x hxlen hxmany
      have hxT : x ∈ T := by
        have hxT' : x ∈ selectionTarget c 𝒜 n i j k t := by
          rw [selectionTarget, Finset.mem_filter]
          exact ⟨(memStringsOfLength n x).mpr hxlen, hxmany⟩
        simpa [T] using hxT'
      have hxU : x ∈ C.biUnion cover := hcov hxT
      rw [Finset.mem_biUnion] at hxU
      rcases hxU with ⟨w, hwC, hxcover⟩
      refine ⟨w, ?_, ?_⟩
      · rw [Finset.mem_toList]
        exact hwC
      · have hxcover' : x ∈ selectionCoverSet 𝒜 n j w := by simpa [cover] using hxcover
        exact (mem_selectionCoverSet 𝒜 n j x w).mp hxcover' |>.2
  · have hTempty : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hTne
    refine ⟨[], by simp, ?_⟩
    intro x hxlen hxmany
    have hxT : x ∈ T := by
      have hxT' : x ∈ selectionTarget c 𝒜 n i j k t := by
        rw [selectionTarget, Finset.mem_filter]
        exact ⟨(memStringsOfLength n x).mpr hxlen, hxmany⟩
      simpa [T] using hxT'
    rw [hTempty] at hxT
    simp at hxT

/-- Finite-stage bookkeeping for the restricted selection strategy.  This is an
indexed greedy subcover of the currently rich length-`n` strings. -/
noncomputable def selectionStrategy (c : Code) (𝒜 : PreDescriptionFamily)
    (n i j k : ℕ) (t : ℕ) : List BitString :=
  Classical.choose (exists_selectionStrategy c 𝒜 n i j k t)

/-- The total number of marked sets is bounded by an explicit formula. -/
theorem selectionStrategy_length_bound (c : Code) (𝒜 : PreDescriptionFamily) (n i j k : ℕ) (t : ℕ) :
  (selectionStrategy c 𝒜 n i j k t).length ≤
    (i + 1) * (i + 1) * (n + 1) * 2 ^ (i + 1 - k) := by
  exact (Classical.choose_spec (exists_selectionStrategy c 𝒜 n i j k t)).1

/-- Every `n`-bit string with `2^k` visible restricted descriptions is covered
by a selected family description, provided the visible game has at most
`2^(i+1)` distinct family-model moves. -/
theorem selectionStrategy_covers (c : Code) (𝒜 : PreDescriptionFamily) (n i j k t : ℕ) :
    ∀ x : BitString, x.length = n →
      2 ^ k ≤ (familyStageDescriptionCodes c i 𝒜 j t x).card →
      ∃ w ∈ selectionStrategy c 𝒜 n i j k t, IsFamilyDescriptionCode 𝒜 j x w := by
  exact (Classical.choose_spec (exists_selectionStrategy c 𝒜 n i j k t)).2

end Kolmogorov
