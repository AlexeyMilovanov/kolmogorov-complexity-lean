/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Construction.Accounting
import KolmogorovMathlib.RandomStrings.Plain.Construction.Actions
import KolmogorovMathlib.RandomStrings.Plain.Construction.Effective
import KolmogorovMathlib.RandomStrings.Plain.Construction.Referees
import KolmogorovMathlib.RandomStrings.Plain.Construction.State
import KolmogorovMathlib.RandomStrings.Plain.ExtensionPrice
import KolmogorovMathlib.RandomStrings.Plain.FiniteGame
import KolmogorovMathlib.RandomStrings.Plain.Markers
import Mathlib.Data.Nat.Sqrt

/-!
# Occupied inputs and the fighter allocator

The fighter allocates, for each directive of target length `r`, a fresh input of length `r - 1`
from the finite pool `fighterInputs d (r - 1)`.  This module records the exact behaviour of
`fighterAllocate` and the bookkeeping that is needed to compare two runs of the allocator.

* `occupiedInputs s r` is the finite set of inputs of directive length `r` that are already
  allocated in the state `s`.  Counting inputs as a set also handles duplicate entries in an
  arbitrary initial allocation list.
* `fighterAllocate_spec` describes a failed and a successful allocation of an active phase.
* `fighterAllocate_success_of_card_lt` and `fighterAllocate_success_of_card_le` say that an
  allocation succeeds as soon as strictly fewer inputs are occupied than the pool contains, and
  that success is monotone in the number of occupied inputs.
* `card_occupiedInputs_append` computes how one appended allocation changes the occupancy.

These facts are used in `StrategyPostponement` to prove that postponing a payoff cannot make a
failed fighter response disappear, and in `CommonGameInitial` for the opening of the common game.
-/

namespace Kolmogorov.Milovanov

/-- The finite set of occupied inputs of directive length `r`. Counting inputs as a set also
handles duplicate entries in an arbitrary initial allocation list. -/
def occupiedInputs (s : FighterState) (r : ℕ) : Finset BitString :=
  (s.allocated.map AllocatedDirective.input).toFinset.filter (fun p ↦ p.length + 1 = r)

/-- Priority abortion preserves the issuing lookup, tick, permanent allocation table, fulfilled
pairs, and failure flag, even when active levels are not unique. -/
lemma fighterAbortAbove_frame (d l : ℕ) (s : FighterState) :
    (fighterAbortAbove d l s).tick = s.tick ∧
    (fighterAbortAbove d l s).allocated = s.allocated ∧
    (fighterAbortAbove d l s).fulfilled = s.fulfilled ∧
    (fighterAbortAbove d l s).failed = s.failed ∧
    (fighterAbortAbove d l s).activeAt d l = s.activeAt d l := by
  have hcancel (j : ℕ) (hj : j ≠ l) (t : FighterState) :
      (fighterCancel d j .aborted l t).tick = t.tick ∧
      (fighterCancel d j .aborted l t).allocated = t.allocated ∧
      (fighterCancel d j .aborted l t).fulfilled = t.fulfilled ∧
      (fighterCancel d j .aborted l t).failed = t.failed ∧
      (fighterCancel d j .aborted l t).activeAt d l = t.activeAt d l := by
    unfold fighterCancel
    split
    · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    · refine ⟨rfl, rfl, rfl, rfl, ?_⟩
      simp only [FighterState.activeAt, List.find?_filter]
      apply List.find?_congr
      intro p hp
      by_cases h : p.level = l <;> simp [h, Ne.symm hj]
  have hfold (ps : List FighterPhase) (t : FighterState) :
      let u := ps.foldl (fun t p ↦ if l < p.level then
        fighterCancel d p.level .aborted l t else t) t
      u.tick = t.tick ∧ u.allocated = t.allocated ∧ u.fulfilled = t.fulfilled ∧
        u.failed = t.failed ∧ u.activeAt d l = t.activeAt d l := by
    induction ps generalizing t with
    | nil => exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    | cons p ps ih =>
      simp only [List.foldl_cons]
      split
      · have hc := hcancel p.level (by omega) t
        have hi := ih (fighterCancel d p.level .aborted l t)
        exact ⟨hi.1.trans hc.1, hi.2.1.trans hc.2.1, hi.2.2.1.trans hc.2.2.1,
          hi.2.2.2.1.trans hc.2.2.2.1, hi.2.2.2.2.trans hc.2.2.2.2⟩
      · exact ih t
  exact hfold s.active s

/-- The allocator enumerates exactly the strings of the specified length. -/
lemma mem_fighterInputs_iff (d k : ℕ) (p : BitString) :
    p ∈ fighterInputs d k ↔ p.length = k := by
  induction k generalizing p with
  | zero => simp [fighterInputs]
  | succ k ih =>
    cases p with
    | nil => simp [fighterInputs]
    | cons b p => cases b <;> simp [fighterInputs, ih]

/-- With an active issuing phase, a failed allocation sets the failure flag and removes the
lookup. A successful allocation appends its explicitly selected fresh input of the requested
length and preserves the remaining local data. -/
lemma fighterAllocate_spec
    (d l r : ℕ) (kind : DirectiveKind) (out : BitString)
    (s : FighterState) (p : FighterPhase) (hp : s.activeAt d l = some p) :
    let a := fighterAllocate d l kind r out s
    (a.2 = false → a.1.failed = true ∧ a.1.activeAt d l = none ∧
      a.1.tick = s.tick ∧ a.1.fulfilled = s.fulfilled) ∧
    (a.2 = true → ∃ input,
      input.length + 1 = r ∧ input ∉ (s.allocated.map AllocatedDirective.input).toFinset ∧
      a.1.allocated = s.allocated ++ [⟨l, p.candidate, s.tick, kind, r, input, out⟩] ∧
      a.1.tick = s.tick ∧ a.1.fulfilled = s.fulfilled ∧ a.1.failed = s.failed ∧
      a.1.activeAt d l = some p) := by
  have hcancel (t : FighterState) :
      (fighterCancel d l .saturated l t).failed = t.failed ∧
      (fighterCancel d l .saturated l t).activeAt d l = none ∧
      (fighterCancel d l .saturated l t).tick = t.tick ∧
      (fighterCancel d l .saturated l t).fulfilled = t.fulfilled := by
    unfold fighterCancel
    split
    · rename_i h
      exact ⟨rfl, h, rfl, rfl⟩
    · refine ⟨rfl, ?_, rfl, rfl⟩
      simp [FighterState.activeAt, List.find?_filter]
  simp only [fighterAllocate, hp]
  by_cases hr : r = 0
  · simp only [hr, ite_true]
    constructor
    · intro _
      exact hcancel _
    · intro h; cases h
  · simp only [hr, ite_false]
    cases hf : (fighterInputs d (r - 1)).find?
        (fun input ↦ !s.allocated.any (fun a ↦ a.input == input)) with
    | none =>
      dsimp only
      constructor
      · intro _
        exact hcancel _
      · intro h; cases h
    | some input =>
      dsimp only
      constructor
      · intro h; cases h
      · intro _
        have hmem := List.mem_of_find?_eq_some hf
        have hlen := (mem_fighterInputs_iff d (r - 1) input).mp hmem
        have hfresh := List.find?_some hf
        have habort := fighterAbortAbove_frame d l
          { s with allocated := s.allocated ++ [⟨l, p.candidate, s.tick, kind, r, input, out⟩] }
        refine ⟨input, by omega, ?_, habort.2.1, habort.1, habort.2.2.1,
          habort.2.2.2.1, habort.2.2.2.2.trans hp⟩
        simpa [List.any_eq_false] using hfresh

/-- A positive target with an unused input of the required length is allocated successfully. -/
lemma fighterAllocate_success_of_free_input
    (d l r : ℕ) (kind : DirectiveKind) (out : BitString)
    (s : FighterState) (p : FighterPhase) (hp : s.activeAt d l = some p)
    (hr : 0 < r) (hfree : ∃ input, input.length + 1 = r ∧
      input ∉ (s.allocated.map AllocatedDirective.input).toFinset) :
    (fighterAllocate d l kind r out s).2 = true := by
  simp only [fighterAllocate, hp, Nat.ne_of_gt hr, ite_false]
  cases hf : (fighterInputs d (r - 1)).find?
      (fun input ↦ !s.allocated.any (fun a ↦ a.input == input)) with
  | some input => rfl
  | none =>
    obtain ⟨input, hlen, hnot⟩ := hfree
    have hmem : input ∈ fighterInputs d (r - 1) :=
      (mem_fighterInputs_iff _ _ _).mpr (by omega)
    have h := List.find?_eq_none.mp hf input hmem
    simp only [Bool.not_eq_true', Bool.not_eq_false, List.any_eq_true, beq_iff_eq] at h
    obtain ⟨a, ha, heq⟩ := h
    exact False.elim (hnot (by simp only [List.mem_toFinset, List.mem_map]; exact ⟨a, ha, heq⟩))

/-- The allocator preserves an already set failure flag. -/
lemma fighterAllocate_failed_of_failed
    (d l r : ℕ) (kind : DirectiveKind) (out : BitString)
    (s : FighterState) (hs : s.failed = true) :
    (fighterAllocate d l kind r out s).1.failed = true := by
  cases hp : s.activeAt d l with
  | none => simpa [fighterAllocate, hp] using hs
  | some p =>
    have ha := fighterAllocate_spec d l r kind out s p hp
    cases hb : (fighterAllocate d l kind r out s).2 with
    | false => exact (ha.1 hb).1
    | true =>
      obtain ⟨_, _, _, _, _, _, h, _⟩ := ha.2 hb
      exact h.trans hs

/-- Appending one allocation with a fresh input increases precisely its input-length occupancy
by one. -/
lemma card_occupiedInputs_append
    (s t : FighterState) (a : AllocatedDirective)
    (ha : t.allocated = s.allocated ++ [a])
    (hfresh : a.input ∉ (s.allocated.map AllocatedDirective.input).toFinset) (r : ℕ) :
    (occupiedInputs t r).card =
      (occupiedInputs s r).card + if a.input.length + 1 = r then 1 else 0 := by
  have hnot : a.input ∉ occupiedInputs s r := by
    intro h
    exact hfresh (Finset.mem_filter.mp h).1
  have heq : occupiedInputs t r =
      if a.input.length + 1 = r then insert a.input (occupiedInputs s r)
      else occupiedInputs s r := by
    ext input
    by_cases h : a.input.length + 1 = r <;> simp [occupiedInputs, ha, h] <;> aesop
  rw [heq]
  split
  · rw [Finset.card_insert_of_notMem hnot]
  · simp

/-- At a positive target every occupied input counted for that target belongs to its finite
allocation pool. -/
lemma occupiedInputs_subset_fighterInputs (d r : ℕ) (s : FighterState) (hr : 0 < r) :
    occupiedInputs s r ⊆ (fighterInputs d (r - 1)).toFinset := by
  intro input h
  have hlen := (Finset.mem_filter.mp h).2
  exact List.mem_toFinset.mpr ((mem_fighterInputs_iff d _ _).mpr (by omega))

/-- Strictly fewer occupied inputs than the finite pool guarantees successful allocation,
without any uniqueness assumption on the initial allocation entries. -/
lemma fighterAllocate_success_of_card_lt
    (d l r : ℕ) (kind : DirectiveKind) (out : BitString)
    (s : FighterState) (p : FighterPhase) (hp : s.activeAt d l = some p)
    (hr : 0 < r)
    (hcard : (occupiedInputs s r).card < (fighterInputs d (r - 1)).toFinset.card) :
    (fighterAllocate d l kind r out s).2 = true := by
  apply fighterAllocate_success_of_free_input d l r kind out s p hp hr
  obtain ⟨input, hmem, hnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hlen := (mem_fighterInputs_iff d _ input).mp (List.mem_toFinset.mp hmem)
  refine ⟨input, by omega, ?_⟩
  intro h
  apply hnot
  exact Finset.mem_filter.mpr ⟨h, by omega⟩

/-- If the same target can be allocated with at least as many occupied inputs, it can also be
allocated with fewer occupied inputs. Only the finite pool and the successful allocator witness
are needed. -/
lemma fighterAllocate_success_of_card_le
    (d l r : ℕ) (kindS kindT : DirectiveKind)
    (outS outT : BitString) (s t : FighterState) (p p' : FighterPhase)
    (hsp : s.activeAt d l = some p) (htp : t.activeAt d l = some p')
    (hcount : (occupiedInputs s r).card ≤ (occupiedInputs t r).card)
    (ht : (fighterAllocate d l kindT r outT t).2 = true) :
    (fighterAllocate d l kindS r outS s).2 = true := by
  obtain ⟨input, hlen, hfresh, _⟩ := (fighterAllocate_spec d l r kindT outT t p' htp).2 ht
  have hr : 0 < r := by omega
  have hmem : input ∈ (fighterInputs d (r - 1)).toFinset :=
    List.mem_toFinset.mpr ((mem_fighterInputs_iff _ _ _).mpr (by omega))
  have hnot : input ∉ occupiedInputs t r := fun h ↦ hfresh (Finset.mem_filter.mp h).1
  have hsubset : insert input (occupiedInputs t r) ⊆ (fighterInputs d (r - 1)).toFinset :=
    Finset.insert_subset hmem (occupiedInputs_subset_fighterInputs d r t hr)
  have hcard := Finset.card_le_card hsubset
  rw [Finset.card_insert_of_notMem hnot] at hcard
  exact fighterAllocate_success_of_card_lt d l r kindS outS s p hsp hr (by omega)

end Kolmogorov.Milovanov
