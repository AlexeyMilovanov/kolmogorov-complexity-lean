import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Computability.PartrecCode
import KolmogorovMathlib.Foundation.UnboundedSearch

/-!
# Dyadic Numeration (Bijective Base-2)

This module formalizes a bijective base-2 numeration system.
Unlike standard binary representation, dyadic numeration avoids the "leading zeros"
problem, providing a strict bijection `ℕ ≃ List Bool`.
We prove its correctness, establish fundamental exponential length bounds,
and prove the computability of the encoding/decoding functions.
-/

namespace Kolmogorov

-- ==========================================================
-- 1. Definition of Bijective Base-2
-- ==========================================================

/-- Decodes a list of booleans into a natural number using bijective base-2.
    [] ↦ 0, [false] ↦ 1, [true] ↦ 2, [false, false] ↦ 3. -/
def bitsToNat : List Bool → ℕ
| [] => 0
| false :: bs => 1 + 2 * bitsToNat bs
| true :: bs => 2 + 2 * bitsToNat bs

/-- Encodes a natural number into a list of booleans using bijective base-2. -/
def natToBits (n : ℕ) : List Bool :=
  if h : n = 0 then
    []
  else
    ((n - 1) % 2 == 1) :: natToBits ((n - 1) / 2)
termination_by n
decreasing_by omega

-- ==========================================================
-- 2. Mutual Inverse Proofs
-- ==========================================================

@[simp]
lemma bitsToNat_natToBits (n : ℕ) : bitsToNat (natToBits n) = n := by
  rw [natToBits]
  split_ifs with h
  · subst h; rfl
  · have ih := bitsToNat_natToBits ((n - 1) / 2)
    have h_mod : (n - 1) % 2 = 0 ∨ (n - 1) % 2 = 1 := by omega
    obtain h0 | h1 := h_mod
    · have hb : ((n - 1) % 2 == 1) = false := by rw [h0]; rfl
      rw [hb]
      change 1 + 2 * bitsToNat (natToBits ((n - 1) / 2)) = _
      rw [ih]
      omega
    · have hb : ((n - 1) % 2 == 1) = true := by rw [h1]; rfl
      rw [hb]
      change 2 + 2 * bitsToNat (natToBits ((n - 1) / 2)) = _
      rw [ih]
      omega
termination_by n
decreasing_by omega

@[simp]
lemma natToBits_bitsToNat (bs : List Bool) : natToBits (bitsToNat bs) = bs := by
  induction bs with
  | nil =>
    change natToBits 0 = []
    rw [natToBits]
    split_ifs with h
    · rfl
    · omega
  | cons b bs ih =>
    cases b
    · have h_val : bitsToNat (false :: bs) = 1 + 2 * bitsToNat bs := rfl
      rw [h_val, natToBits]
      split_ifs with h_zero
      · omega
      · have h_math : 1 + 2 * bitsToNat bs - 1 = 2 * bitsToNat bs := by omega
        rw [h_math]
        have h_div : (2 * bitsToNat bs) / 2 = bitsToNat bs := by omega
        have h_mod : (2 * bitsToNat bs) % 2 = 0 := by omega
        rw [h_div, h_mod]
        have hb : (0 == 1) = false := rfl
        rw [hb]
        change false :: natToBits (bitsToNat bs) = false :: bs
        rw [ih]
    · have h_val : bitsToNat (true :: bs) = 2 + 2 * bitsToNat bs := rfl
      rw [h_val, natToBits]
      split_ifs with h_zero
      · omega
      · have h_math : 2 + 2 * bitsToNat bs - 1 = 2 * bitsToNat bs + 1 := by omega
        rw [h_math]
        have h_div : (2 * bitsToNat bs + 1) / 2 = bitsToNat bs := by omega
        have h_mod : (2 * bitsToNat bs + 1) % 2 = 1 := by omega
        rw [h_div, h_mod]
        have hb : (1 == 1) = true := rfl
        rw [hb]
        change true :: natToBits (bitsToNat bs) = true :: bs
        rw [ih]

/-- The formal mathematical bijection between Natural Numbers and Boolean Lists. -/
def dyadicEquiv : ℕ ≃ List Bool where
  toFun := natToBits
  invFun := bitsToNat
  left_inv := bitsToNat_natToBits
  right_inv := natToBits_bitsToNat

-- ==========================================================
-- 3. Length Bounds (The Key to Berry's Paradox)
-- ==========================================================

/-- The fundamental bounds of dyadic numeration: 2^|s| ≤ val(s) + 1 < 2^(|s|+1). -/
lemma bounds_bitsToNat (bs : List Bool) :
    2 ^ bs.length ≤ bitsToNat bs + 1 ∧ bitsToNat bs + 1 < 2 ^ (bs.length + 1) := by
  induction bs with
  | nil =>
    change 1 ≤ 1 ∧ 1 < 2
    omega
  | cons b bs ih =>
    obtain ⟨ih1, ih2⟩ := ih
    cases b
    · change 2 ^ (bs.length + 1) ≤ 1 + 2 * bitsToNat bs + 1 ∧
             1 + 2 * bitsToNat bs + 1 < 2 ^ (bs.length + 1 + 1)
      have h_pow_left : 2 ^ (bs.length + 1) = 2 * 2 ^ bs.length := by omega
      have h_pow_right : 2 ^ (bs.length + 1 + 1) = 2 * 2 ^ (bs.length + 1) := by omega
      rw [h_pow_left, h_pow_right]
      omega
    · change 2 ^ (bs.length + 1) ≤ 2 + 2 * bitsToNat bs + 1 ∧
             2 + 2 * bitsToNat bs + 1 < 2 ^ (bs.length + 1 + 1)
      have h_pow_left : 2 ^ (bs.length + 1) = 2 * 2 ^ bs.length := by omega
      have h_pow_right : 2 ^ (bs.length + 1 + 1) = 2 * 2 ^ (bs.length + 1) := by omega
      rw [h_pow_left, h_pow_right]
      omega

/-- Lower bound: The number generated is at least 2^length - 1. -/
lemma two_pow_length_le (n : ℕ) : 2 ^ (natToBits n).length ≤ n + 1 := by
  have h := bounds_bitsToNat (natToBits n)
  rw [bitsToNat_natToBits] at h
  exact h.1

/-- Upper bound: The number generated is strictly less than 2^(length + 1) - 1. -/
lemma lt_two_pow_length (n : ℕ) : n + 1 < 2 ^ ((natToBits n).length + 1) := by
  have h := bounds_bitsToNat (natToBits n)
  rw [bitsToNat_natToBits] at h
  exact h.2

/-- Every natural number's binary length is at most its value (crude bound). -/
lemma length_natToBits_le (k : ℕ) : (natToBits k).length ≤ k := by
  have h1 := two_pow_length_le k
  have h2 : ∀ n, n < 2^n := by
    intro n
    induction n with
    | zero => decide
    | succ n ih =>
      rw [Nat.pow_succ]
      omega
  have h3 := h2 (natToBits k).length
  omega

-- ==========================================================
-- 4. Computability Assumptions
-- ==========================================================

/-- Auxiliary lemma: our bijection from List Bool to Nat is computable. -/
lemma bitsToNat_computable : Computable bitsToNat := by
  apply Primrec.to_comp
  have hf : Primrec (fun (l : List Bool) => l) := Primrec.id
  have hg : Primrec (fun (_ : List Bool) => (0 : ℕ)) := Primrec.const 0
  have h_acc : Primrec (fun (p : List Bool × (Bool × List Bool × ℕ)) => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have h_2acc : Primrec (fun (p : List Bool × (Bool × List Bool × ℕ)) => 2 * p.2.2.2) :=
    Primrec.nat_mul.comp (Primrec.const 2) h_acc
  have hh : Primrec₂ (fun (_ : List Bool) (p : Bool × List Bool × ℕ) =>
      bif p.1 then 2 + 2 * p.2.2 else 1 + 2 * p.2.2) :=
    Primrec.cond (Primrec.fst.comp Primrec.snd)
      (Primrec.nat_add.comp (Primrec.const 2) h_2acc)
      (Primrec.nat_add.comp (Primrec.const 1) h_2acc)
  have h_rec := Primrec.list_rec hf hg hh
  convert h_rec using 1
  funext bs
  induction bs with
  | nil => rfl
  | cons b tl ih =>
    cases b
    · change 1 + 2 * bitsToNat tl = 1 + 2 * _
      rw [ih]
    · change 2 + 2 * bitsToNat tl = 2 + 2 * _
      rw [ih]

/-- Auxiliary lemma: our bijection from Nat to List Bool is computable. -/
lemma natToBits_computable : Computable natToBits := by
  -- Broken into multiple lines for the 100-character linter limit
  exact Computable.listInverse bitsToNat bitsToNat_computable natToBits
    bitsToNat_natToBits natToBits_bitsToNat

end Kolmogorov
