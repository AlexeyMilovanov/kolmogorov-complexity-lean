import Mathlib.Data.List.Basic
import Mathlib.Data.List.Dedup
import Mathlib.Order.MinMax

/-!
# Generic list facts: `List.eraseDups` and list maxima

`List.eraseDups` removes the duplicates of a list, keeping the first occurrence of every
element.  Mathlib states its lemmas for `List.dedup` and, in this toolchain, proves nothing
about `eraseDups` itself, while the enumerations of this library are deduplicated with
`eraseDups`.  This module proves the two facts they need — membership is unchanged, and the
result has no repetition — once, for an arbitrary type with decidable equality.  The
specialised copies elsewhere in the library are corollaries of these.

The same is done for the two facts about the maximum `l.foldr max 0` of a list of naturals
(a common bound bounds the maximum; every entry is at most the maximum), which several
modules had proved for themselves.
-/

namespace Kolmogorov

variable {α : Type*} [BEq α] [LawfulBEq α]

/-- **Removing duplicates does not change membership.** -/
theorem mem_eraseDups_list {a : α} : ∀ {l : List α}, a ∈ l.eraseDups ↔ a ∈ l
  | [] => by simp
  | b :: l => by
      rw [List.eraseDups_cons]
      constructor
      · intro h
        rcases List.mem_cons.mp h with rfl | h
        · exact List.mem_cons_self
        · have := (mem_eraseDups_list (l := l.filter (fun x => x != b))).mp h
          exact List.mem_cons_of_mem _ (List.mem_of_mem_filter this)
      · intro h
        rcases List.mem_cons.mp h with rfl | h
        · exact List.mem_cons_self
        · by_cases hab : a = b
          · exact hab ▸ List.mem_cons_self
          · refine List.mem_cons_of_mem _ ?_
            exact (mem_eraseDups_list (l := l.filter (fun x => x != b))).mpr
              (List.mem_filter.mpr ⟨h, by simp [hab]⟩)
  termination_by l => l.length
  decreasing_by all_goals exact Nat.lt_succ_of_le (List.length_filter_le _ _)

/-- **Removing duplicates leaves a list with no repetition.** -/
theorem nodup_eraseDups_list : ∀ l : List α, l.eraseDups.Nodup
  | [] => by simp
  | a :: l => by
      rw [List.eraseDups_cons]
      refine List.nodup_cons.mpr ⟨?_, nodup_eraseDups_list _⟩
      intro hmem
      rw [mem_eraseDups_list, List.mem_filter] at hmem
      simp at hmem
  termination_by l => l.length
  decreasing_by exact Nat.lt_succ_of_le (List.length_filter_le _ _)

/-! ### The maximum of a list of naturals -/

/-- **A common bound on the entries of a list of naturals bounds their maximum.** -/
theorem foldr_max_le_of_forall_le {l : List ℕ} {M : ℕ} (h : ∀ a ∈ l, a ≤ M) :
    l.foldr max 0 ≤ M := by
  induction l with
  | nil => exact Nat.zero_le M
  | cons a t ih =>
    simp only [List.foldr_cons]
    exact max_le (h a (List.mem_cons_self ..)) (ih fun b hb => h b (List.mem_cons_of_mem _ hb))

/-- **Every entry of a list of naturals is at most the maximum of the list.** -/
theorem le_foldr_max_of_mem {l : List ℕ} {a : ℕ} (h : a ∈ l) : a ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons b t ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | h'
    · exact le_max_left _ _
    · exact le_trans (ih h') (le_max_right _ _)

end Kolmogorov
