import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import KolmogorovMathlib.Core.Basic

/-!
# Finite-sum plumbing between `List`, `Finset` and `tsum`

The counting arguments of this library move the same sum between three shapes: a sum over a
list, a sum over a `Finset`, and an unconditional sum `∑'` over `ℕ` of an indexed family.
This module is the single home of the passages between them:

* `sum_list_range_eq_finset_sum'` — a sum over `(List.range n).map g` is a `Finset.range` sum;
* `sum_toFinset_le_list_sum` — deduplicating the index list can only lower a `ℕ`-valued sum;
* `sum_biUnion_le'` — a sum over a `Finset.biUnion` is at most the double sum;
* `tsum_list_getElem?_elim` — a `tsum` over the optional entries of a list is the list sum.

Every statement here is about Mathlib notions only; they used to be restated as private
helpers in the modules that needed them.
-/

namespace Kolmogorov

open scoped ENNReal

/-- A sum over a mapped range list is the corresponding sum over `Finset.range`. -/
lemma sum_list_range_eq_finset_sum' (n : ℕ) (g : ℕ → ℕ) :
    ((List.range n).map g).sum = ∑ j ∈ Finset.range n, g j := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
      simp

/-- Removing duplicate indices from a list cannot increase a nonnegative
natural-valued sum. -/
lemma sum_toFinset_le_list_sum {α : Type*} [DecidableEq α]
    (values : α → ℕ) : ∀ items : List α,
    ∑ item ∈ items.toFinset, values item ≤ (items.map values).sum := by
  intro items
  induction items with
  | nil => simp
  | cons item items ih =>
      by_cases hitem : item ∈ items
      · have hle : (items.map values).sum ≤
            values item + (items.map values).sum := by omega
        simpa [hitem] using ih.trans hle
      · simpa [hitem] using Nat.add_le_add_left ih (values item)

/-- A sum over a finite union is at most the corresponding double sum. -/
lemma sum_biUnion_le' {α β : Type*} [DecidableEq β] (s : Finset α)
    (t : α → Finset β) (f : β → ℕ) :
    ∑ w ∈ s.biUnion t, f w ≤ ∑ a ∈ s, ∑ w ∈ t a, f w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert ha]
      calc ∑ w ∈ t a ∪ s.biUnion t, f w
          ≤ ∑ w ∈ t a, f w + ∑ w ∈ s.biUnion t, f w := by
            have hsub : t a ∪ s.biUnion t ⊆ t a ∪ (s.biUnion t \ t a) := by
              intro x hx
              rcases Finset.mem_union.mp hx with h | h
              · exact Finset.mem_union_left _ h
              · by_cases hxa : x ∈ t a
                · exact Finset.mem_union_left _ hxa
                · exact Finset.mem_union_right _
                    (Finset.mem_sdiff.mpr ⟨h, hxa⟩)
            calc ∑ w ∈ t a ∪ s.biUnion t, f w
                ≤ ∑ w ∈ t a ∪ (s.biUnion t \ t a), f w :=
                  Finset.sum_le_sum_of_subset hsub
              _ = ∑ w ∈ t a, f w + ∑ w ∈ s.biUnion t \ t a, f w :=
                  Finset.sum_union Finset.disjoint_sdiff
              _ ≤ ∑ w ∈ t a, f w + ∑ w ∈ s.biUnion t, f w :=
                  Nat.add_le_add_left
                    (Finset.sum_le_sum_of_subset Finset.sdiff_subset) _
        _ ≤ ∑ w ∈ t a, f w + ∑ a' ∈ s, ∑ w ∈ t a', f w :=
            Nat.add_le_add_left ih _

/-- Summing a nonnegative weight over the optional entries of a list at every
natural-number index recovers the list sum. -/
lemma tsum_list_getElem?_elim (l : List BitString) (h : BitString → ℝ≥0∞) :
    ∑' m : ℕ, (l[m]?).elim 0 h = (l.map h).sum := by
  have key : ∀ l' : List BitString,
      ∑ b ∈ Finset.range l'.length, (l'[b]?).elim 0 h = (l'.map h).sum := by
    intro l'
    induction l' with
    | nil => simp
    | cons a l' ih => simp [Finset.sum_range_succ', ih, add_comm]
  rw [tsum_eq_sum (s := Finset.range l.length) ?_]
  · exact key l
  · intro b hb
    simp only [Finset.mem_range, not_lt] at hb
    rw [List.getElem?_eq_none hb]; simp

end Kolmogorov
