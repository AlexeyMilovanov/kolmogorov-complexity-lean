/-
Copyright (c) 2024 Alexey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey
-/
import KolmogorovMathlib.Prefix.Basic

/-!
# Prefix-Free Codes Are Uniquely Decodable

This module supplies the combinatorial bridge between the repository's notion of a
*prefix-free* set of bitstrings (`IsPrefixFree`, see `KolmogorovMathlib.Prefix.Basic`)
and Mathlib's `InformationTheory.UniquelyDecodable`. That bridge is the missing
hypothesis needed to invoke Mathlib's `kraft_mcmillan_inequality` on the halting
domain of a prefix machine.

The one subtlety is the empty string. A prefix-free set *may* contain `[]`, but only
as the singleton `{[]}` (anything else would have `[]` as a strict prefix). The empty
string is *not* uniquely decodable, since `[]` flattens the same as `[[], []]`. We
therefore first isolate the empty-string case (`IsPrefixFree.eq_singleton_nil_of_mem`)
and then prove unique decodability under the extra hypothesis `[] ∉ S`
(`IsPrefixFree.uniquelyDecodable`). Both shapes are exactly what the Kraft slot needs:
the `[] ∈ S` branch is dispatched by the singleton lemma, the `[] ∉ S` branch by the
bridge.

This file is pure `List Bool` combinatorics: no machines, measures, or real numbers.
-/

namespace Kolmogorov

namespace InformationTheory

/-- Lean 4.28 compatibility copy of the unique-decodability predicate used by the
newer Mathlib coding API. -/
def UniquelyDecodable {α : Type*} (S : Set (List α)) : Prop :=
  ∀ L₁ L₂ : List (List α),
    (∀ w, w ∈ L₁ → w ∈ S) →
    (∀ w, w ∈ L₂ → w ∈ S) →
    L₁.flatten = L₂.flatten →
    L₁ = L₂

end InformationTheory

open InformationTheory

/-- A prefix-free set containing the empty string is exactly the singleton `{[]}`.
Any other element `q` would have the empty string as a *strict* prefix, which a
prefix-free set forbids. -/
theorem IsPrefixFree.eq_singleton_nil_of_mem {S : Set BitString} (hS : IsPrefixFree S)
    (hnil : [] ∈ S) : S = {[]} := by
  apply Set.eq_singleton_iff_unique_mem.mpr
  refine ⟨hnil, fun q hq => ?_⟩
  exact (hS hnil hq (List.nil_prefix)).symm

/-- **The bridge.** A prefix-free set of bitstrings that does *not* contain the empty
string is uniquely decodable: two lists of codewords with equal concatenations are
equal. The proof inducts on the first list, peeling matching heads. Two heads `a`, `b`
in a prefix relation (forced by the common concatenation) must be equal by
prefix-freeness; the empty-string hypothesis rules out a `[]` head meeting an empty
list. -/
theorem IsPrefixFree.uniquelyDecodable {S : Set BitString} (hS : IsPrefixFree S)
    (hnil : [] ∉ S) : UniquelyDecodable S := by
  intro L₁
  induction L₁ with
  | nil =>
    intro L₂ _ h₂ hflat
    cases L₂ with
    | nil => rfl
    | cons b bs =>
      exfalso
      simp only [List.flatten_nil, List.flatten_cons] at hflat
      -- `[] = b ++ bs.flatten` forces `b = []`, contradicting `[] ∉ S`.
      have hb : b = [] := (List.append_eq_nil_iff.mp hflat.symm).1
      exact hnil (hb ▸ h₂ b List.mem_cons_self)
  | cons a as ih =>
    intro L₂ h₁ h₂ hflat
    cases L₂ with
    | nil =>
      exfalso
      simp only [List.flatten_nil, List.flatten_cons] at hflat
      have ha : a = [] := (List.append_eq_nil_iff.mp hflat).1
      exact hnil (ha ▸ h₁ a List.mem_cons_self)
    | cons b bs =>
      simp only [List.flatten_cons] at hflat
      -- `hflat : a ++ as.flatten = b ++ bs.flatten`
      have haS : a ∈ S := h₁ a List.mem_cons_self
      have hbS : b ∈ S := h₂ b List.mem_cons_self
      -- One head is a prefix of the other; prefix-freeness collapses them to equal.
      have hab : a = b := by
        rcases List.append_eq_append_iff.mp hflat with ⟨a', hb_eq, _⟩ | ⟨c', ha_eq, _⟩
        · exact hS haS hbS ⟨a', hb_eq.symm⟩
        · exact (hS hbS haS ⟨c', ha_eq.symm⟩).symm
      subst hab
      have hrest : as.flatten = bs.flatten := List.append_cancel_left hflat
      have htail : as = bs :=
        ih bs (fun w hw => h₁ w (List.mem_cons_of_mem _ hw))
           (fun w hw => h₂ w (List.mem_cons_of_mem _ hw)) hrest
      rw [htail]

end Kolmogorov
