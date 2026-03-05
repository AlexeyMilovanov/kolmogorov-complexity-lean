import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Partrec
import KolmogorovMathlib.Core.Basic
import KolmogorovMathlib.Complexity.Properties
import KolmogorovMathlib.Complexity.NatComplexity
import KolmogorovMathlib.Foundation.NatEncoding
import KolmogorovMathlib.Foundation.UnboundedSearch
import Mathlib.Order.Lattice

/-!
# Uncomputability of Kolmogorov Complexity

This module proves the crown jewel of Algorithmic Information Theory:
The uncomputability of `plainK`. The proof follows the formal structure
of Berry's Paradox: "the smallest number that cannot be described in less than
twenty words".

If `plainK` were computable, we could write an algorithm `g` that searches
for the first number whose complexity exceeds `2^k`.
Because `g` is computable, its output's complexity must be bounded by
the length of its input `k` plus a constant `c`. Thus, `2^k < |k| + c`.
However, `2^k` grows exponentially while `|k|` grows logarithmically,
creating a mathematical contradiction for sufficiently large `k`.
-/

namespace Kolmogorov

-- ==========================================================
-- 1. Growth Lemma & Paradox Base
-- ==========================================================

/-- Growth Lemma: 2^k eventually dominates logarithmic description.
    For any constant c, there exists a k such that |k| + c < 2^k. -/
lemma growth_lemma (c : ℕ) :
    ∃ k, (programLength (Nat.bits k) : ENat) + (c : ENat) < (2^k : ENat) := by
  -- We pick a k large enough to easily dominate the linear growth
  let k := c + 5
  use k
  have h_len := length_natBits_le k
  have h_arith : (programLength (Nat.bits k) : ENat) + c ≤ (k : ENat) + c := by
    dsimp [programLength]
    exact add_le_add (ENat.coe_le_coe.mpr h_len) (le_refl (c : ENat))
  have h_exp : (k : ENat) + c < (2^k : ENat) := by
    apply ENat.coe_lt_coe.mpr
    dsimp [k]
    have : ∀ n, n + 5 + n < 2 ^ (n + 5) := by
      intro n
      induction n with
      | zero => decide
      | succ n ih =>
        rw [Nat.pow_succ]
        omega
    exact this c
  exact lt_of_le_of_lt h_arith h_exp

-- ==========================================================
-- 2. Unbounded Search (Predicate Translation)
-- ==========================================================

/-- Translate the uncomputable predicate K(n) > L into a computable one f(n) > L. -/
lemma plainKNat_gt_iff (U : Map) (f : ℕ → ℕ) (L : ℕ)
    (h_f_eq : ∀ n, plainKNat U n = (f n : ENat)) (n : ℕ) :
    plainKNat U n > (L : ENat) ↔ f n > L := by
  rw [h_f_eq n]
  exact ENat.coe_lt_coe

-- ==========================================================
-- 3. Computability Bridge Integration
-- ==========================================================

/-- The unbounded search function (Berry's algorithm) is strictly computable. -/
lemma Computable.find_complex (U : Map) (f : ℕ → ℕ)
    (h_f_eq : ∀ n, plainKNat U n = (f n : ENat))
    (h_f_comp : Computable f) :
    Computable (fun k => Nat.find (exists_plainKNat_gt U (2^k))) := by
  apply Computable.searchCore f h_f_comp (fun k => 2^k) Computable.pow2
  intro k n
  exact plainKNat_gt_iff U f (2^k) h_f_eq n

/-- Computable functions on natural numbers do not increase complexity by more than a constant. -/
lemma plainKNat_comp_le (U : Map) (hU : isOptimalConditional U)
    (g : ℕ → ℕ) (hg : Computable g) :
    ∃ c_g : ℕ, ∀ k, plainKNat U (g k) ≤ plainKNat U k + (c_g : ENat) := by
  let f_str : BitString → BitString := fun s => Nat.bits (g (decodeBits s))
  have hf_comp : Computable f_str :=
    natBits_computable.comp (hg.comp decodeBits_computable)
  obtain ⟨c_g, hc⟩ := plainK_map_le U hU f_str hf_comp
  use c_g
  intro k
  have h_bound := hc (Nat.bits k)
  dsimp [f_str] at h_bound
  rw [decodeBits_bits] at h_bound
  exact h_bound

-- ==========================================================
-- 4. Main Theorem
-- ==========================================================

/-- Final assembly: the complexity of Berry's algorithm output is bounded by |k| + c. -/
lemma plainKNat_find_complex_le (U : Map) (hU : isOptimalConditional U)
    (f : ℕ → ℕ) (h_f_comp : Computable f) (h_f_eq : ∀ n, plainKNat U n = (f n : ENat)) :
    ∃ c : ℕ, ∀ k, plainKNat U (Nat.find (exists_plainKNat_gt U (2^k))) ≤
      (programLength (Nat.bits k) : ENat) + (c : ENat) := by
  let g := fun k => Nat.find (exists_plainKNat_gt U (2^k))
  have hg_comp : Computable g := Computable.find_complex U f h_f_eq h_f_comp
  obtain ⟨c_g, h_bound_g⟩ := plainKNat_comp_le U hU g hg_comp
  obtain ⟨c_len, h_bound_len⟩ := plainKNat_le_length U hU
  use (c_g + c_len)
  intro k
  calc
    plainKNat U (g k)
      ≤ plainKNat U k + (c_g : ENat) := h_bound_g k
    _ ≤ ((programLength (Nat.bits k) : ENat) + c_len) + c_g := by
      have h1 := h_bound_len k
      exact add_le_add h1 (le_refl _)
    _ = (programLength (Nat.bits k) : ENat) + ((c_g + c_len : ℕ) : ENat) := by
      push_cast
      rw [add_assoc]
      have h_swap : (c_len : ENat) + (c_g : ENat) = (c_g : ENat) + (c_len : ENat) := add_comm _ _
      rw [h_swap]

/-- Main Theorem: Kolmogorov complexity is not computable. -/
theorem not_computable_plainKNat (U : Map) (hU : isOptimalConditional U) :
    ¬ ∃ f : ℕ → ℕ, Computable f ∧ ∀ n, plainKNat U n = (f n : ENat) := by
  rintro ⟨f, h_f_comp, h_f_eq⟩
  let g (k : ℕ) := Nat.find (exists_plainKNat_gt U (2^k))
  have h_low (k : ℕ) : (2^k : ENat) < plainKNat U (g k) :=
    Nat.find_spec (exists_plainKNat_gt U (2^k))
  obtain ⟨c, hc⟩ := plainKNat_find_complex_le U hU f h_f_comp h_f_eq
  obtain ⟨k, hk⟩ := growth_lemma c
  have h_top := hc k
  have h_combined : plainKNat U (g k) < (2^k : ENat) := lt_of_le_of_lt h_top hk
  exact lt_irrefl _ (lt_trans (h_low k) h_combined)

end Kolmogorov
