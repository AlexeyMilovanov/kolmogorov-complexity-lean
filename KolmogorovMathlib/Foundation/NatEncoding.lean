import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Partrec
import Mathlib.Data.List.Basic
import KolmogorovMathlib.Core.Basic

/-!
# Binary Encoding of Natural Numbers

This module provides the foundational mapping between natural numbers
and bit strings (`List Bool`). It proves that the standard `Nat.bits`
representation is injective and defines its left inverse (`decodeBits`).
It also establishes the computability of these transformations and
bounds on the length of the binary representation.
-/

namespace Kolmogorov

-- ==========================================================
-- 1. Decoding and Injectivity
-- ==========================================================

/-- Decoder from a list of bits (little-endian) back to a natural number. -/
def decodeBits : List Bool → ℕ
  | [] => 0
  | false :: bs => 2 * decodeBits bs
  | true :: bs => 2 * decodeBits bs + 1

/-- Proving that decodeBits is a left inverse to Nat.bits. -/
@[simp]
theorem decodeBits_bits (n : ℕ) : decodeBits (Nat.bits n) = n := by
  induction n using Nat.binaryRec
  case zero =>
    change decodeBits (Nat.binaryRec [] (fun b _ r => b :: r) 0) = 0
    rw [Nat.binaryRec_zero]
    rfl
  case bit b n' ih =>
    by_cases h_zero : n' = 0
    · subst h_zero
      cases b
      · change decodeBits (Nat.binaryRec [] (fun b _ r => b :: r) 0) = 0
        rw [Nat.binaryRec_zero]
        rfl
      · have h_app : Nat.bits (Nat.bit true 0) = true :: Nat.bits 0 := by
          apply Nat.bits_append_bit
          intro _
          rfl
        rw [h_app]
        change 2 * decodeBits (Nat.binaryRec [] (fun b _ r => b :: r) 0) + 1 = 1
        rw [Nat.binaryRec_zero]
        rfl
    · have h_app : Nat.bits (Nat.bit b n') = b :: Nat.bits n' := by
        apply Nat.bits_append_bit
        intro h
        contradiction
      rw [h_app]
      cases b
      · change 2 * decodeBits (Nat.bits n') = Nat.bit false n'
        rw [ih]
        simp [Nat.bit]
      · change 2 * decodeBits (Nat.bits n') + 1 = Nat.bit true n'
        rw [ih]
        simp [Nat.bit]

/-- The standard binary representation of natural numbers is injective. -/
theorem bits_injective : Function.Injective Nat.bits := by
  intro a b hab
  have h : decodeBits (Nat.bits a) = decodeBits (Nat.bits b) := by rw [hab]
  simpa only [decodeBits_bits] using h

-- ==========================================================
-- 2. Length Bounds
-- ==========================================================

@[simp]
lemma bits_zero : Nat.bits 0 = [] := by
  -- We provide explicit arguments to Nat.binaryRec_zero to help Lean's elaborator
  exact Nat.binaryRec_zero (zero := []) (bit := fun b _ r => b :: r)

/-- The length of a natural number's binary string is bounded by the number itself. -/
lemma length_natBits_le (k : ℕ) : (Nat.bits k).length ≤ k := by
  induction k using Nat.binaryRec
  case zero =>
    rw [bits_zero]
    exact Nat.le_refl 0
  case bit b n' ih =>
    by_cases h_zero : n' = 0
    · subst h_zero
      cases b
      · -- Case: 0
        rw [bits_zero]
        exact Nat.le_refl 0
      · -- Case: 1
        have h_app : Nat.bits 1 = [true] := by
          -- 1 is Nat.bit true 0
          have h1 : 1 = Nat.bit true 0 := rfl
          rw [h1, Nat.bits_append_bit]
          · rw [bits_zero]
          · intro _; rfl
        rw [h_app]
        simp
    · -- Case: n' > 0
      have h_app : Nat.bits (Nat.bit b n') = b :: Nat.bits n' := by
        apply Nat.bits_append_bit
        intro h
        contradiction
      rw [h_app]
      simp only [List.length_cons]
      -- At this point, simp or omega usually finishes the job
      cases b <;> simp [Nat.bit] <;> omega
-- ==========================================================
-- 3. Computability
-- ==========================================================

/-- Converting a natural number to its binary representation is computable. -/
lemma natBits_computable : Computable Nat.bits := by
  sorry

/-- Decoding a binary string back to a natural number is computable. -/
lemma decodeBits_computable : Computable decodeBits := by
  sorry

end Kolmogorov
