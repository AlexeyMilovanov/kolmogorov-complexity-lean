/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.TTMeet2014.TruthTable
import Mathlib.Tactic.FinCases

/-!
# Posner's trick

Section 4 of the paper meets requirements of the form `¬(Ψ_i^{R₀} = Ψ_i^{R₁} = Ψ_i^{R₂} = X)`, with
one index `i`.  A priori each `R_j` has its own reduction.  `posner_combine` turns three per-oracle
reductions into a single one, by hard-coding a finite list `Z` of distinguishing queries.

The three oracles need not be distinct: `exists_distinguishing` only separates the *distinct*
pairs, and a guard that also fires on another oracle means the two oracles are equal, where both
reductions compute `X`.  That is why the statement needs all three reductions to compute the same
`X`.  The guards depend non-uniformly on the oracles, which is harmless: only the existence of a
computable generator is claimed.
-/

namespace Kolmogorov.RandomStrings.TTMeet

/-- Prepending a guard to every clause of a table. -/
def guardTable (G : Clause) (t : TTable) : TTable := t.map fun c => G ++ c

/-- For a fixed guard `G`, `guardTable G` is primitive recursive. -/
theorem guardTable_primrec (G : Clause) : Primrec (guardTable G) :=
  Primrec.list_map Primrec.id
    ((Primrec.list_append.comp (Primrec.const G) Primrec.snd).to₂)

/-- A guarded table evaluates to `true` on `o` iff the guard holds on `o` and the table evaluates to
`true` on `o`. -/
theorem evalB_guardTable (G : Clause) (t : TTable) (o : Str → Bool) :
    (guardTable G t).evalB o = true ↔ G.holds o = true ∧ t.evalB o = true := by
  simp only [TTable.evalB_eq_true, guardTable, List.mem_map, Clause.holds_eq_true]
  constructor
  · rintro ⟨_, ⟨c, hc, rfl⟩, h⟩
    exact ⟨fun q hq => h q (List.mem_append_left _ hq), c, hc, fun q hq =>
      h q (List.mem_append_right _ hq)⟩
  · rintro ⟨hG, c, hc, h⟩
    refine ⟨G ++ c, ⟨c, hc, rfl⟩, fun q hq => ?_⟩
    rcases List.mem_append.1 hq with hq | hq
    · exact hG q hq
    · exact h q hq

/-- The guard recording the answers of the oracle `o` on the list `Z`. -/
def guardOf (Z : List Str) (o : Str → Bool) : Clause := Z.map fun z => (z, o z)

/-- The guard recording `o` on `Z` holds on `o'` iff `o'` agrees with `o` on every string of `Z`. -/
theorem holds_guardOf (Z : List Str) (o o' : Str → Bool) :
    (guardOf Z o).holds o' = true ↔ ∀ z ∈ Z, o' z = o z := by
  simp [guardOf, Clause.holds_eq_true]

/-- A finite list of queries separating every two distinct oracles of the family. -/
theorem exists_distinguishing (R : Fin 3 → Set Str) :
    ∃ Z : List Str, ∀ j k, (∀ z ∈ Z, (z ∈ R j ↔ z ∈ R k)) → R j = R k := by
  classical
  have hw : ∀ j k, ∃ w : Str, R j ≠ R k → ¬ (w ∈ R j ↔ w ∈ R k) := by
    intro j k
    by_cases h : R j = R k
    · exact ⟨[], fun h' => absurd h h'⟩
    · obtain ⟨w, hw⟩ : ∃ w, ¬ (w ∈ R j ↔ w ∈ R k) := by
        by_contra hcon
        exact h (Set.ext fun z => by_contra fun hz => hcon ⟨z, hz⟩)
      exact ⟨w, fun _ => hw⟩
  choose w hw using hw
  refine ⟨(List.finRange 3).flatMap fun j => (List.finRange 3).map fun k => w j k, fun j k h => ?_⟩
  by_contra hne
  refine hw j k hne (h _ ?_)
  simp only [List.mem_flatMap, List.mem_map]
  exact ⟨j, List.mem_finRange j, k, List.mem_finRange k, rfl⟩

/-- **Posner's trick.**  Three per-oracle reductions of `X` combine into one reduction that works
for all three oracles, including the cases where some of the oracles coincide. -/
theorem posner_combine {X : Set Str} {R : Fin 3 → Set Str} {g : Fin 3 → Str → TTable}
    (hg : ∀ j, Computable (g j)) (h : ∀ j, IsTTReduction (g j) X (R j)) :
    ∃ g' : Str → TTable, Computable g' ∧ ∀ j, IsTTReduction g' X (R j) := by
  classical
  obtain ⟨Z, hZ⟩ := exists_distinguishing R
  let G : Fin 3 → Clause := fun j => guardOf Z (chi (R j))
  refine ⟨fun x => guardTable (G 0) (g 0 x) ++ (guardTable (G 1) (g 1 x) ++
    guardTable (G 2) (g 2 x)), ?_, fun j x => ?_⟩
  · have hc : ∀ j, Computable fun x => guardTable (G j) (g j x) :=
      fun j => (guardTable_primrec (G j)).to_comp.comp (hg j)
    exact (Primrec.list_append.to_comp).comp (hc 0)
      ((Primrec.list_append.to_comp).comp (hc 1) (hc 2))
  · have hany : ∀ t₀ t₁ t₂ : TTable, ∀ o : Str → Bool,
        (t₀ ++ (t₁ ++ t₂)).evalB o = true ↔
          t₀.evalB o = true ∨ t₁.evalB o = true ∨ t₂.evalB o = true := by
      intro t₀ t₁ t₂ o
      simp [TTable.evalB, List.any_append]
    have hsame : ∀ j' : Fin 3, (G j').holds (chi (R j)) = true → R j' = R j := by
      intro j' hj'
      refine hZ j' j fun z hz => ?_
      have := (holds_guardOf Z (chi (R j')) (chi (R j))).1 hj' z hz
      rw [← chi_eq_true, ← chi_eq_true (R := R j), this]
    have hself : (G j).holds (chi (R j)) = true := (holds_guardOf Z _ _).2 fun _ _ => rfl
    have hthree : (∃ j', (G j').holds (chi (R j)) = true ∧ (g j' x).evalB (chi (R j)) = true) ↔
        x ∈ X := by
      constructor
      · rintro ⟨j', hG, he⟩
        rw [h j' x, TTable.Accepts, hsame j' hG]
        exact he
      · intro hx
        exact ⟨j, hself, (h j x).1 hx⟩
    refine hthree.symm.trans ?_
    change _ ↔ (guardTable (G 0) (g 0 x) ++ (guardTable (G 1) (g 1 x) ++
      guardTable (G 2) (g 2 x))).evalB (chi (R j)) = true
    rw [hany]
    constructor
    · rintro ⟨j', hG, he⟩
      fin_cases j'
      · exact Or.inl ((evalB_guardTable _ _ _).2 ⟨hG, he⟩)
      · exact Or.inr (Or.inl ((evalB_guardTable _ _ _).2 ⟨hG, he⟩))
      · exact Or.inr (Or.inr ((evalB_guardTable _ _ _).2 ⟨hG, he⟩))
    · rintro (hx | hx | hx)
      · exact ⟨0, (evalB_guardTable _ _ _).1 hx⟩
      · exact ⟨1, (evalB_guardTable _ _ _).1 hx⟩
      · exact ⟨2, (evalB_guardTable _ _ _).1 hx⟩

end Kolmogorov.RandomStrings.TTMeet
