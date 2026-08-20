import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Partrec
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith

/-!
# Binary Encoding of Natural Numbers

This module provides the foundational mapping between natural numbers
and bit strings (`List Bool`). It proves that the standard `Nat.bits`
representation is injective and defines its left inverse (`decodeBits`).
It also establishes the computability of these transformations and
bounds on the length of the binary representation.
-/

namespace Kolmogorov

/-! ### Decoding and Injectivity -/

/-- Decoder from a list of bits (little-endian) back to a natural number. -/
def decodeBits : List Bool → ℕ
  | [] => 0
  | false :: bs => 2 * decodeBits bs
  | true :: bs => 2 * decodeBits bs + 1

/-- Proving that `decodeBits` is a left inverse to `Nat.bits`. -/
@[simp]
theorem decodeBits_natBits (n : ℕ) : decodeBits (Nat.bits n) = n := by
  induction n using Nat.binaryRec
  case zero =>
    simp [decodeBits]
  case bit b n' ih =>
    by_cases h_zero : n' = 0
    · subst h_zero
      cases b
      · simp [decodeBits, Nat.bit, Nat.bits]
      · have h_app : Nat.bits (Nat.bit true 0) = true :: Nat.bits 0 := by
          apply Nat.bits_append_bit
          intro _; rfl
        rw [h_app]
        simp [decodeBits, Nat.bit]
    · have h_app : Nat.bits (Nat.bit b n') = b :: Nat.bits n' := by
        apply Nat.bits_append_bit
        intro h; contradiction
      rw [h_app]
      cases b <;> simp [decodeBits, ih, Nat.bit]

/-- The standard binary representation of natural numbers is injective. -/
theorem natBitsInjective : Function.Injective Nat.bits := by
  intro a b hab
  have h : decodeBits (Nat.bits a) = decodeBits (Nat.bits b) := by rw [hab]
  simpa only [decodeBits_natBits] using h

/-! ### Length Bounds -/

@[simp]
lemma natBits_zero : Nat.bits 0 = [] := by
  simp [Nat.bits]

/-- The length of a natural number's binary string is bounded by the number itself. -/
lemma length_natBits_le (k : ℕ) : (Nat.bits k).length ≤ k := by
  induction k using Nat.binaryRec
  case zero =>
    simp
  case bit b n' ih =>
    by_cases h_zero : n' = 0
    · subst h_zero
      cases b
      · simp [Nat.bit, Nat.bits]
      · have h_app : Nat.bits (Nat.bit true 0) = true :: Nat.bits 0 := by
          apply Nat.bits_append_bit
          intro _; rfl
        rw [h_app]
        simp [Nat.bit]
    · have h_app : Nat.bits (Nat.bit b n') = b :: Nat.bits n' := by
        apply Nat.bits_append_bit
        intro h; contradiction
      rw [h_app]
      simp only [List.length_cons]
      cases b <;> simp [Nat.bit] <;> omega

/-! ### Computability -/

/-- A single step of decoding a bit, multiplying the accumulator and adding the bit. -/
def decodeStep (b : Bool) (n : ℕ) : ℕ :=
  Nat.bit b n

/-- Decoding bits is equivalent to a foldr operation. -/
lemma decodeBits_eq_foldr (bs : List Bool) :
    decodeBits bs = bs.foldr decodeStep 0 := by
  induction bs with
  | nil => rfl
  | cons b tail ih =>
    cases b <;> simp [decodeBits, decodeStep, ih, Nat.bit]

/-- The decode step function is primitive recursive. -/
lemma primrecDecodeStep : Primrec₂ decodeStep := by
  have h_eq : ∀ p : Bool × ℕ, decodeStep p.1 p.2 = bif p.1 then 2 * p.2 + 1 else 2 * p.2 := by
    intro p; cases p.1 <;> rfl
  apply Primrec.of_eq _ h_eq
  apply Primrec.cond Primrec.fst
  · apply Primrec₂.comp Primrec.nat_add
    · apply Primrec₂.comp Primrec.nat_mul
      · exact Primrec.const 2
      · exact Primrec.snd
    · exact Primrec.const 1
  · apply Primrec₂.comp Primrec.nat_mul
    · exact Primrec.const 2
    · exact Primrec.snd

/-- The bit decoder function is primitive recursive. -/
lemma primrecDecodeBits : Primrec decodeBits := by
  have h_fold : Primrec (fun bs : List Bool => bs.foldr decodeStep 0) := by
    have h_step : Primrec₂ (fun (_ : List Bool) (p : Bool × ℕ) => decodeStep p.1 p.2) :=
      primrecDecodeStep.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
    exact Primrec.list_foldr Primrec.id (Primrec.const 0) h_step
  exact Primrec.of_eq h_fold (fun bs => (decodeBits_eq_foldr bs).symm)

/-- The bit decoder is computable. -/
lemma decodeBitsComputable : Computable decodeBits :=
  Primrec.to_comp primrecDecodeBits

/-! ### Nat.bits Computability -/

/-- Helper function for the strong recursion of `Nat.bits`. -/
def bitsG (_ : Unit) (l : List (List Bool)) : Option (List Bool) :=
  let n := l.length
  bif n == 0 then some []
  else some ((n % 2 == 1) :: l.getD (n / 2) [])

/-- The helper function `bitsG` is primitive recursive. -/
lemma primrecBitsG : Primrec₂ bitsG := by
  have h_eq : ∀ p : Unit × List (List Bool), bitsG p.1 p.2 =
      bif (p.2.length == 0) then some []
      else some ((p.2.length % 2 == 1) :: p.2.getD (p.2.length / 2) []) := by
    intro p; rfl
  apply Primrec.of_eq _ h_eq
  apply Primrec.cond
  · apply Primrec₂.comp Primrec.beq
    · exact Primrec.comp Primrec.list_length Primrec.snd
    · exact Primrec.const 0
  · exact Primrec.const (some [])
  · apply Primrec.comp Primrec.option_some
    apply Primrec₂.comp Primrec.list_cons
    · apply Primrec₂.comp Primrec.beq
      · apply Primrec₂.comp Primrec.nat_mod
        · exact Primrec.comp Primrec.list_length Primrec.snd
        · exact Primrec.const 2
      · exact Primrec.const 1
    · apply Primrec₂.comp (Primrec.list_getD [])
      · exact Primrec.snd
      · apply Primrec₂.comp Primrec.nat_div
        · exact Primrec.comp Primrec.list_length Primrec.snd
        · exact Primrec.const 2

/-- `bitsG` correctly constructs the next bitstring based on the previously generated ones. -/
lemma bitsGValid (u : Unit) (n : ℕ) :
    bitsG u (List.map (fun x => Nat.bits x) (List.range n)) = some (Nat.bits n) := by
  unfold bitsG
  simp only [List.length_map, List.length_range]
  by_cases hn : n = 0
  · subst hn
    simp [Nat.bits]
  · have h_beq : (n == 0) = false := by
      cases h_eq : (n == 0)
      · rfl
      · have := beq_iff_eq.mp h_eq; contradiction
    have h_n_eq : n = Nat.bit (n % 2 == 1) (n / 2) := by
      simp [Nat.bit]
      by_cases h_odd : n % 2 = 1
      · simp [h_odd]; omega
      · have h_even : n % 2 = 0 := by omega
        have h_false : (n % 2 == 1) = false := by
          cases h_eq : (n % 2 == 1)
          · rfl
          · have := beq_iff_eq.mp h_eq; omega
        simp [h_false]; omega
    have h_bits : Nat.bits (Nat.bit (n % 2 == 1) (n / 2)) = (n % 2 == 1) :: Nat.bits (n / 2) := by
      apply Nat.bits_append_bit
      intro h_zero
      have h_n_one : n = 1 := by omega
      subst h_n_one
      rfl
    have h_rhs : Nat.bits n = (n % 2 == 1) :: Nat.bits (n / 2) := by
      conv_lhs => rw [h_n_eq]
      exact h_bits
    rw [h_beq, h_rhs]
    have h_lt : n / 2 < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by omega)
    have h_get : (List.range n)[n / 2]? = some (n / 2) := List.getElem?_range h_lt
    simp [List.getD, h_get, List.getElem?_map]

/-- The standard `Nat.bits` representation is primitive recursive. -/
lemma primrecNatBits : Primrec Nat.bits := by
  have h_strong : Primrec₂ (fun (u : Unit) (n : ℕ) => Nat.bits n) :=
    Primrec.nat_strong_rec (fun _ n => Nat.bits n) primrecBitsG bitsGValid
  exact h_strong.comp (Primrec.const ()) Primrec.id

/-- The standard `Nat.bits` representation is computable. -/
lemma natBitsComputable : Computable Nat.bits :=
  Primrec.to_comp primrecNatBits

/-
Any fixed linear function of `(Nat.bits n).length` (i.e. `O(log n)`) is
eventually dominated by `n`: for all `K A B`, there is a threshold `M` beyond
which `K * (A * (Nat.bits n).length + B) ≤ n`.
-/
lemma exists_bits_linear_domination (K A B : ℕ) :
    ∃ M : ℕ, ∀ n : ℕ, M ≤ n → K * (A * (Nat.bits n).length + B) ≤ n := by
  -- Beyond a fixed threshold, the exponential `2 ^ (m - 1)` dominates the
  -- linear expression in `m`.
  obtain ⟨m₀, hm₀⟩ : ∃ m₀ : ℕ, ∀ m ≥ m₀, K * (A * m + B) ≤ 2^(m-1) := by
    use 8 * K * ( A + B + 1 ) + 8;
    intro m hm;
    -- We'll use that $2^{m-1} \geq m^2$ for $m \geq 8$.
    have h_exp : 2 ^ (m - 1) ≥ m ^ 2 := by
      rcases m with ( _ | _ | _ | _ | _ | _ | _ | _ | m ) <;>
        simp +arith +decide only [
          ge_iff_le, add_le_add_iff_right, Nat.add_one_sub_one, Nat.pow_succ, pow_one
        ] at *;
      exact Nat.recOn m ( by norm_num ) fun n ihn => by norm_num [ Nat.pow_succ' ] at * ; nlinarith;
    nlinarith [mul_nonneg (Nat.zero_le K) (Nat.zero_le A),
      mul_nonneg (Nat.zero_le K) (Nat.zero_le B)]
  refine ⟨ 2 ^ m₀, fun n hn => le_trans ( hm₀ _ ?_ ) ?_ ⟩;
  · rw [ Nat.size_eq_bits_len ];
    exact Nat.le_of_not_lt fun h => by linarith [ Nat.size_le.mp h.le ] ;
  · convert Nat.pow_le_of_le_log ( by linarith [ Nat.one_le_pow m₀ 2 zero_lt_two ] ) _ using 1;
    rw [ Nat.le_iff_lt_or_eq ];
    refine lt_or_eq_of_le ( Nat.sub_le_of_le_add <| ?_ );
    convert Nat.size_le.2 _
    · convert Nat.size_eq_bits_len n
    · exact Nat.lt_pow_succ_log_self (by decide) _

end Kolmogorov
