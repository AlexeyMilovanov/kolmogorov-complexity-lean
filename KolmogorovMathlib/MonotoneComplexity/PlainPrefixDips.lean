import KolmogorovMathlib.Core.Basic
import KolmogorovMathlib.Complexity.Properties
import KolmogorovMathlib.Complexity.Incompressibility
import KolmogorovMathlib.Foundation.NatEncoding
import KolmogorovMathlib.AlgorithmicStatistics.Selector
import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.OmegaPrefix
import KolmogorovMathlib.AlgorithmicRandomness.Cantor
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Every sequence has prefixes of plain complexity below their length

The other side of the comparison: `plainK_prefix_le_length_sub_logb_infinitely_often` shows that
every infinite sequence has infinitely many prefixes `x` with
`C(x) ≤ |x| - log₂ |x|`, obtained by letting a prefix carry its own length in its leading digits
(`plainK_markedExpand_le`). The supporting material is the little-endian decoding
`decodeBits` with its bit-by-bit lemmas, the marked-expansion round trip
(`natBits_decodeBits_append_true`, `dropLast_natBits_decodeBits_append_true`), and the elementary
estimates `logb_two_add_le_of_pow_bounds` and `set_infinite_of_unbounded`.
-/

namespace Kolmogorov

/-- Prepending a zero bit doubles the value of the little-endian binary decoding. -/
lemma decodeBits_false (bs : List Bool) : decodeBits (false :: bs) = 2 * decodeBits bs := rfl
/-- Prepending a one bit doubles the value of the little-endian binary decoding and adds one. -/
lemma decodeBits_true (bs : List Bool) : decodeBits (true :: bs) = 2 * decodeBits bs + 1 := rfl

/-- Prepending a bit to a string performs one step of `Nat.bit` on its decoded value. -/
lemma decodeBits_cons (b : Bool) (bs : List Bool) :
    decodeBits (b :: bs) = Nat.bit b (decodeBits bs) := by
  cases b
  · exact decodeBits_false bs
  · change 2 * decodeBits bs + 1 = Nat.bit true (decodeBits bs)
    rfl

/-- A string with a terminal one bit decodes to a nonzero natural number. -/
lemma decodeBits_append_true_ne_zero (u : BitString) : decodeBits (u ++ [true]) ≠ 0 := by
  induction u with
  | nil => decide
  | cons b bs ih =>
    rw [List.cons_append, decodeBits_cons]
    intro h
    exact ih (Nat.bit_eq_zero_iff.mp h).1

/-- Appending a one bit makes the decoding lossless: the binary digits of the decoded number are the
original string again. -/
lemma natBits_decodeBits_append_true (u : BitString) :
    Nat.bits (decodeBits (u ++ [true])) = u ++ [true] := by
  induction u with
  | nil => rfl
  | cons b bs ih =>
    rw [List.cons_append, decodeBits_cons, Nat.bits_append_bit]
    · rw [ih]
    · intro h
      exfalso
      exact decodeBits_append_true_ne_zero bs h

/-- Dropping the leading one from the binary digits of `decodeBits (u ++ [true])` recovers `u`, so
`u ↦ decodeBits (u ++ [true])` is invertible. -/
lemma dropLast_natBits_decodeBits_append_true (u : BitString) :
    (Nat.bits (decodeBits (u ++ [true]))).dropLast = u := by
  rw [natBits_decodeBits_append_true]
  exact List.dropLast_concat

/-- The number coded by `u` with a terminal one bit is at least `2 ^ |u|`. -/
lemma pow_length_le_decodeBits_append_true (u : BitString) :
    2 ^ u.length ≤ decodeBits (u ++ [true]) := by
  induction u with
  | nil => decide
  | cons b bs ih =>
    rw [List.length_cons, List.cons_append, decodeBits_cons]
    calc
      2 ^ (bs.length + 1) = 2 * 2 ^ bs.length := by ring
      _ ≤ 2 * decodeBits (bs ++ [true]) := Nat.mul_le_mul_left 2 ih
      _ ≤ Nat.bit b (decodeBits (bs ++ [true])) := by
        cases b
        · exact Nat.le_refl _
        · exact Nat.le_succ _

/-- The number coded by `u` with a terminal one bit is below `2 ^ (|u| + 1)`. -/
lemma decodeBits_append_true_lt (u : BitString) :
    decodeBits (u ++ [true]) < 2 ^ (u.length + 1) := by
  induction u with
  | nil => decide
  | cons b bs ih =>
    rw [List.length_cons, List.cons_append, decodeBits_cons]
    have : Nat.bit b (decodeBits (bs ++ [true])) ≤ 2 * decodeBits (bs ++ [true]) + 1 := by
      cases b
      · exact Nat.le_succ _
      · exact Nat.le_refl _
    calc
      Nat.bit b (decodeBits (bs ++ [true])) ≤ 2 * decodeBits (bs ++ [true]) + 1 := this
      _ < 2 * 2 ^ (bs.length + 1) := by linarith
      _ = 2 ^ (bs.length + 1 + 1) := by ring

/-- Prefixing a string with the binary digits of its own length, leading one removed, is computable.
-/
lemma computable_markedExpand :
    Computable (fun p : BitString => (Nat.bits p.length).dropLast ++ p) := by
  have H : (fun p : List Bool => (Nat.bits p.length).dropLast ++ p) =
           (fun p : List Bool => (Nat.bits p.length).reverse.tail.reverse ++ p) := by
    funext p
    simp [List.dropLast_eq_take]
  rw [H]
  apply Primrec.to_comp
  refine Primrec.list_append.comp ?_ Primrec.id
  refine Primrec.list_reverse.comp ?_
  refine Primrec.list_tail.comp ?_
  refine Primrec.list_reverse.comp ?_
  exact Primrec.comp Kolmogorov.primrec_natBits Primrec.list_length

/-- The prefix of length `k + m` splits as the prefix of length `k` followed by the length-`m`
prefix
of the shifted sequence. -/
lemma cantorPrefix_add (w : CantorSeq) (k m : ℕ) :
    cantorPrefix w (k + m) =
      cantorPrefix w k ++ cantorPrefix (fun i => w (k + i)) m := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [cantorPrefix_getElem]
    by_cases h_lt : i < k
    · have h_lt2 : i < (cantorPrefix w k).length := by simp [h_lt]
      rw [List.getElem_append_left h_lt2]
      simp [cantorPrefix_getElem]
    · have h_ge : k ≤ i := Nat.le_of_not_lt h_lt
      have h_ge2 : (cantorPrefix w k).length ≤ i := by simp [h_ge]
      rw [List.getElem_append_right h_ge2]
      simp [cantorPrefix_getElem]
      congr 1
      omega

/-- Strings carrying their own length in their leading digits are compressible to their payload
length: the plain complexity of the marked expansion of `p` is at most `|p| + c`. -/
lemma plainK_markedExpand_le (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ p, (plainK V ((Nat.bits p.length).dropLast ++ p)).toNat ≤ p.length + c := by
  -- From plainK_map_le: C(markedExpand(p)) ≤ C(p) + c₁
  obtain ⟨c₁, h₁⟩ := plainK_map_le V hV
    (fun p : BitString => (Nat.bits p.length).dropLast ++ p) computable_markedExpand
  -- From plainK_le_length: C(p) ≤ |p| + c₂
  obtain ⟨c₂, h₂⟩ := plainK_le_length V hV
  use c₁ + c₂
  intro p
  -- plainK V (markedExpand p) ≤ plainK V p + c₁ ≤ |p| + c₂ + c₁
  have hle : plainK V ((Nat.bits p.length).dropLast ++ p) ≤ (p.length : ENat) + ↑(c₁ + c₂) := by
    calc plainK V ((Nat.bits p.length).dropLast ++ p)
        ≤ plainK V p + (c₁ : ENat) := h₁ p
      _ ≤ (programLength p : ENat) + (c₂ : ENat) + (c₁ : ENat) := by
          gcongr; exact h₂ p
      _ = (p.length : ENat) + ↑(c₁ + c₂) := by push_cast; ring
  -- Since the RHS is finite, the LHS is finite, so toNat is faithful
  have hrhs_fin : ((p.length : ENat) + ↑(c₁ + c₂)) ≠ ⊤ :=
    WithTop.add_ne_top.mpr ⟨ENat.coe_ne_top p.length, ENat.coe_ne_top (c₁ + c₂)⟩
  have hfin : plainK V ((Nat.bits p.length).dropLast ++ p) ≠ ⊤ :=
    ne_top_of_le_ne_top hrhs_fin hle
  have hconv := ENat.toNat_le_toNat hle hrhs_fin
  exact_mod_cast hconv

/-- If `N` lies between `2 ^ k` and `2 ^ (k + 1)` then `logb 2 (k + N) ≤ k + 2`. -/
lemma logb_two_add_le_of_pow_bounds {k N : ℕ} :
    2 ^ k ≤ N → N < 2 ^ (k + 1) →
    Real.logb 2 ((k : ℝ) + N) ≤ k + 2 := by
  intro h1 h2
  have H1 : (k : ℝ) ≤ (2^k : ℕ) := Nat.cast_le.mpr (Nat.lt_two_pow_self).le
  have H2 : (N : ℝ) < (2^(k+1) : ℕ) := Nat.cast_lt.mpr h2
  have H_pow : ((2^(k+1) : ℕ) : ℝ) = 2 * ((2^k : ℕ) : ℝ) := by
    push_cast
    ring
  have H_pow2 : ((2^(k+2) : ℕ) : ℝ) = 2 * ((2^(k+1) : ℕ) : ℝ) := by
    push_cast
    ring
  have hkN : (k : ℝ) + (N : ℝ) ≤ (2^(k + 2) : ℝ) := by
    have : (2^(k+2) : ℝ) = ((2^(k+2) : ℕ) : ℝ) := by norm_cast
    rw [this, H_pow2, H_pow]
    linarith
  have h_pos : 0 < (k : ℝ) + N := by
    have hN : 1 ≤ N := by
      calc
        1 ≤ 2^k := Nat.one_le_two_pow
        _ ≤ N := h1
    have hN_real : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hk_real : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have h_pos2 : (0 : ℝ) < 2^(k + 2) := by positivity
  have h_log : Real.logb 2 ((k : ℝ) + N) ≤ Real.logb 2 (2^(k + 2)) :=
    (Real.logb_le_logb (by norm_num) h_pos h_pos2).mpr hkN
  have H_log_pow : Real.logb 2 (2^(k + 2)) = (k : ℝ) + 2 := by
    have H3 : (2^(k+2) : ℝ) = (2 : ℝ) ^ ((k + 2 : ℕ) : ℝ) := by
      exact Real.rpow_natCast 2 (k + 2) |>.symm
    have H4 : ((k + 2 : ℕ) : ℝ) = (k : ℝ) + 2 := by push_cast; ring
    rw [H3, H4]
    exact Real.logb_rpow (by norm_num) (by norm_num)
  linarith

/-- A set of naturals containing arbitrarily large elements is infinite. -/
lemma set_infinite_of_unbounded (S : Set ℕ) : (∀ m, ∃ n ∈ S, m < n) → S.Infinite := by
  intro h
  rw [Set.infinite_iff_exists_gt]
  intro n
  obtain ⟨m, hm, hlt⟩ := h n
  exact ⟨m, hm, hlt⟩

/-- Every infinite sequence has infinitely many prefixes whose plain complexity dips at least
`log₂ n - c` below the prefix length `n`; no sequence is plain-complex at all lengths. -/
theorem plainK_prefix_le_length_sub_logb_infinitely_often
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℝ, ∀ w : CantorSeq,
      {n : ℕ | ((plainK V (cantorPrefix w n)).toNat : ℝ)
          ≤ (n : ℝ) - Real.logb 2 n + c}.Infinite := by
  obtain ⟨c₁, h_mark⟩ := plainK_markedExpand_le V hV
  use (c₁ : ℝ) + 2
  intro w
  apply set_infinite_of_unbounded
  intro m
  -- For k = m, define N and n
  set k := m with hk_def
  set u := cantorPrefix w k with hu_def
  have hulen : u.length = k := cantorPrefix_length w k
  set N := decodeBits (u ++ [true]) with hN_def
  set n := k + N with hn_def
  use n
  constructor
  · -- n is in the dip set
    -- Step 1: cantorPrefix w n = markedExpand p where p is the next N bits
    set p := cantorPrefix (fun i => w (k + i)) N with hp_def
    have hplen : p.length = N := cantorPrefix_length _ _
    have hdrop : (Nat.bits p.length).dropLast = u := by
      rw [hplen]
      exact dropLast_natBits_decodeBits_append_true u
    have hconcat : cantorPrefix w n = u ++ p := cantorPrefix_add w k N
    have hmarked : (Nat.bits p.length).dropLast ++ p = cantorPrefix w n := by
      rw [hdrop, hconcat]
    have hK : (plainK V (cantorPrefix w n)).toNat ≤ N + c₁ := by
      rw [← hmarked]
      calc (plainK V ((Nat.bits p.length).dropLast ++ p)).toNat
          ≤ p.length + c₁ := h_mark p
        _ = N + c₁ := by rw [hplen]
    -- Step 2: log₂ n ≤ k + 2 (from logb_two_add_le_of_pow_bounds)
    have hpow1 : 2 ^ k ≤ N := by rw [← hulen]; exact pow_length_le_decodeBits_append_true u
    have hpow2 : N < 2 ^ (k + 1) := by rw [← hulen]; exact decodeBits_append_true_lt u
    have hlogb : Real.logb 2 ((k : ℝ) + (N : ℝ)) ≤ (k : ℝ) + 2 :=
      logb_two_add_le_of_pow_bounds hpow1 hpow2
    -- Step 3: assemble the inequality
    have hn_eq : (n : ℝ) = (k : ℝ) + (N : ℝ) := by simp [hn_def]
    change ((plainK V (cantorPrefix w n)).toNat : ℝ) ≤ (n : ℝ) - Real.logb 2 ↑n + (↑c₁ + 2)
    calc ((plainK V (cantorPrefix w n)).toNat : ℝ)
        ≤ (N : ℝ) + (c₁ : ℝ) := by exact_mod_cast hK
      _ = (n : ℝ) - (k : ℝ) + (c₁ : ℝ) := by rw [hn_eq]; ring
      _ ≤ (n : ℝ) - (Real.logb 2 (n : ℝ) - 2) + (c₁ : ℝ) := by
          gcongr
          rw [hn_eq]
          linarith [hlogb]
      _ = (n : ℝ) - Real.logb 2 (n : ℝ) + ((c₁ : ℝ) + 2) := by ring
  · -- n > m: n = m + N ≥ m + 2^m > m
    change m < n
    have hpow1 : 2 ^ k ≤ N := by rw [← hulen]; exact pow_length_le_decodeBits_append_true u
    calc m = k := hk_def
      _ < k + 2 ^ k := Nat.lt_add_of_pos_right (Nat.pos_of_ne_zero (by positivity))
      _ ≤ k + N := Nat.add_le_add_left hpow1 k

end Kolmogorov
