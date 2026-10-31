/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Realization.Computability
import KolmogorovMathlib.Foundation.ListUtil

/-!
# List lemmas shared by the C-random-strings construction

Small generic facts about lists used throughout `RandomStrings/Plain`:

* `foldl_preserves_invariant`: a property preserved by every step of a left fold is
  preserved by the fold;
* `eraseDups_eq_foldl`: `List.eraseDups` is the left fold appending each element not yet
  seen, so that `primrec_eraseDups` shows it primitive recursive;
* `card_toFinset_eq_length_eraseDups`: the deduplicated list has as many entries as the
  underlying finite set.
-/

namespace Kolmogorov.Milovanov

/-- A predicate preserved by every step of a left fold holds for the result of the fold, if it
holds for the initial value. -/
theorem foldl_preserves_invariant {α β : Type} (Good : β → Prop) (f : β → α → β)
    (xs : List α) (hf : ∀ s a, Good s → Good (f s a)) {s : β} (hs : Good s) :
    Good (xs.foldl f s) := by
  induction xs generalizing s with
  | nil => exact hs
  | cons a xs ih => exact ih (hf s a hs)

/-- Removing duplicates is the left fold that appends each element not yet seen. -/
theorem eraseDups_eq_foldl {α : Type*} [BEq α] [LawfulBEq α] (l : List α) :
    l.eraseDups = l.foldl (fun acc a ↦ if a ∈ acc then acc else acc ++ [a]) [] := by
  have mem_foldl : ∀ (xs acc : List α) (x : α),
      x ∈ xs.foldl (fun acc a ↦ if a ∈ acc then acc else acc ++ [a]) acc ↔
        x ∈ acc ∨ x ∈ xs := by
    intro xs
    induction xs with
    | nil => simp
    | cons a xs ih =>
      intro acc x
      rw [List.foldl_cons, ih]
      by_cases ha : a ∈ acc <;> simp only [ha, ↓reduceIte, List.mem_append,
        List.mem_cons, List.not_mem_nil, or_false]
      · constructor
        · tauto
        · rintro (h | h | h)
          · exact Or.inl h
          · subst x; exact Or.inl ha
          · exact Or.inr h
      · tauto
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l x ih =>
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [List.eraseDups_append, ih]
    have hmem : x ∈ l.foldl
        (fun acc a ↦ if a ∈ acc then acc else acc ++ [a]) [] ↔ x ∈ l := by
      simpa using mem_foldl l [] x
    by_cases hx : x ∈ l
    · have hxfold := hmem.mpr hx
      simp [hxfold, List.removeAll, hx]
    · have hxfold : x ∉ l.foldl
          (fun acc a ↦ if a ∈ acc then acc else acc ++ [a]) [] := fun h ↦ hx (hmem.mp h)
      simp [hxfold, List.removeAll, hx, List.eraseDups_cons]

/-- `List.eraseDups` is primitive recursive. -/
theorem primrec_eraseDups {α : Type*} [Primcodable α] [BEq α] [LawfulBEq α] :
    Primrec (fun l : List α ↦ l.eraseDups) := by
  classical
  have hm : Primrec (fun a : List α × (List α × α) ↦ decide (a.2.2 ∈ a.2.1)) :=
    (list_mem_decide_primrec.comp (Primrec.snd.comp Primrec.snd)
      (Primrec.fst.comp Primrec.snd)).of_eq (fun a ↦ by
        apply decide_eq_decide.mpr; rfl)
  have hs : Primrec₂ (fun (_ : List α) (u : List α × α) ↦
      if u.2 ∈ u.1 then u.1 else u.1 ++ [u.2]) :=
    (Primrec.ite hm.primrecPred
      (Primrec.fst.comp Primrec.snd)
      (Primrec.list_concat.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd))).to₂
  exact (Primrec.list_foldl Primrec.id (Primrec.const []) hs).of_eq
    (fun l ↦ (eraseDups_eq_foldl l).symm)

/-- A list and its deduplication have the same number of distinct elements. -/
theorem card_toFinset_eq_length_eraseDups {α : Type*} [DecidableEq α] [BEq α]
    [LawfulBEq α] (l : List α) : l.toFinset.card = l.eraseDups.length := by
  have he : l.toFinset = l.eraseDups.toFinset := by
    ext x
    simp only [List.mem_toFinset, List.mem_eraseDups]
  rw [he]
  exact List.toFinset_card_of_nodup (Kolmogorov.nodup_eraseDups_list l)

end Kolmogorov.Milovanov
