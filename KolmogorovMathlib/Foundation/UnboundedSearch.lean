import Mathlib.Computability.Partrec
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Primrec.List
import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic

/-!
# Unbounded Search Computability (The Mu-Operator)

This module provides the "Computability Bridge" for unbounded search.
It proves that if a predicate `P` is decidable and computable, and if an answer
is guaranteed to exist for every input, then the search for the minimal such answer
(`Nat.find`) is a total computable function.
-/

namespace Kolmogorov

/-! ### Basic Math Computability -/

/-- Auxiliary lemma: Exponentiation `2^k` is a computable function. -/
lemma Computable.pow2 : Computable (fun k : ℕ => 2 ^ k) := by
  apply Primrec.to_comp
  rw [Primrec.nat_iff]
  have h_eq : (fun k => (Nat.pair 2 k).unpair.1 ^ (Nat.pair 2 k).unpair.2) =
              (fun k => 2 ^ k) := by
    funext k
    simp only [Nat.unpair_pair]
  rw [← h_eq]
  exact Nat.Primrec.pow.comp (Nat.Primrec.pair (Nat.Primrec.const 2) Nat.Primrec.id)

/-! ### Master Lemma (Unbounded Search) -/

/-- If a predicate `P` is decidable and its decision function is computable,
and if for every `k` there exists an `n` such that `P k n` holds,
then the search function `k ↦ Nat.find (h_unbounded k)` is computable. -/
lemma Computable.unboundedSearch {P : ℕ → ℕ → Prop} [∀ k n, Decidable (P k n)]
    (hP_comp : Computable (fun p : ℕ × ℕ => decide (P p.1 p.2)))
    (h_unbounded : ∀ k, ∃ n, P k n) :
    Computable (fun k => Nat.find (h_unbounded k)) := by
  have h_alg : Partrec (fun k => Nat.rfind (fun n => Part.some (decide (P k n)))) := by
    apply Partrec.rfind
    exact Computable.partrec hP_comp
  have h_eq : (fun k => Nat.rfind (fun n => Part.some (decide (P k n)))) =
              (fun k => Part.some (Nat.find (h_unbounded k))) := by
    funext k
    apply Part.eq_some_iff.mpr
    apply Nat.mem_rfind.mpr
    constructor
    · have h1 : decide (P k (Nat.find (h_unbounded k))) = true :=
        decide_eq_true (Nat.find_spec (h_unbounded k))
      rw [h1]
      exact ⟨trivial, rfl⟩
    · intro m hm
      have h2 : decide (P k m) = false :=
        decide_eq_false (Nat.find_min (h_unbounded k) hm)
      rw [h2]
      exact ⟨trivial, rfl⟩
  rw [h_eq] at h_alg
  exact h_alg

/-! ### Corollaries -/

/-- Equality Search: If a function `f` is computable and surjective,
its inverse search function is computable. -/
lemma Computable.inverse (f : ℕ → ℕ) (hf_comp : Computable f)
    (h_surj : ∀ y, ∃ x, f x = y) :
    Computable (fun y => Nat.find (h_surj y)) := by
  refine Computable.unboundedSearch ?_ h_surj
  exact (Primrec.to_comp Primrec.beq).comp
    (Computable.pair (hf_comp.comp Computable.snd) Computable.fst)

/-- Isolates the strict inequality comparison operator on natural numbers. -/
lemma Computable.natLt : Computable (fun p : ℕ × ℕ => decide (p.1 < p.2)) := by
  obtain ⟨_, h_prim⟩ := Primrec.nat_lt
  convert Primrec.to_comp h_prim

/-- Proves the computability of a predicate `P` defined by a strict inequality
between two computable functions. -/
lemma Computable.testP {P : ℕ → ℕ → Prop} [∀ k n, Decidable (P k n)]
    {f g : ℕ → ℕ} (hf : Computable f) (hg : Computable g)
    (h_equiv : ∀ k n, P k n ↔ f n > g k) :
    Computable (fun p : ℕ × ℕ => decide (P p.1 p.2)) := by
  let h_pair := (hg.comp Computable.fst).pair (hf.comp Computable.snd)
  let h_alg := Computable.natLt.comp h_pair
  convert h_alg using 1
  funext p
  simp only [h_equiv]

/-- Inequality Search: A modular search function over a predicate defined
by a strict inequality between two computable functions. -/
lemma Computable.searchCore {P : ℕ → ℕ → Prop} [∀ k n, Decidable (P k n)]
    (f : ℕ → ℕ) (hf_comp : Computable f)
    (g : ℕ → ℕ) (hg_comp : Computable g)
    (h_equiv : ∀ k n, P k n ↔ f n > g k)
    (h_unbounded : ∀ k, ∃ n, P k n) :
    Computable (fun k => Nat.find (h_unbounded k)) :=
  Computable.unboundedSearch (Computable.testP hf_comp hg_comp h_equiv) h_unbounded

end Kolmogorov
