import KolmogorovMathlib.Interface.Dovetailing
import KolmogorovMathlib.AlgorithmicRandomness.NatLogPrimrec
import KolmogorovMathlib.AlgorithmicStatistics.NormalizedCodedFiniteDistribution
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.ModelsToSets2
import KolmogorovMathlib.CommonInformation.ConditionalCounting
import KolmogorovMathlib.Foundation.EnumerationComplexity
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.AddNoise
import KolmogorovMathlib.Prefix.Properties
import KolmogorovMathlib.Prefix.Symmetry
import KolmogorovMathlib.Prefix.ConditionalSymmetry
import KolmogorovMathlib.Foundation.EffectiveNotions
import KolmogorovMathlib.CommonInformation.ConditionalIndependence
import KolmogorovMathlib.AlgorithmicProbability.PairProjection
import KolmogorovMathlib.Foundation.NatEncoding
import KolmogorovMathlib.Prefix.TwoStage
import KolmogorovMathlib.Encoding.Tuples
import KolmogorovMathlib.Complexity.Properties
import KolmogorovMathlib.Prefix.Machine
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.SlackArith
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.ENNReal.Inv
import KolmogorovMathlib.AlgorithmicStatistics.Selector
import KolmogorovMathlib.CommonInformation.Counting
import KolmogorovMathlib.Complexity.IncompressibleStrings.SplitDecompressors

/-!
# Randomness deficiency of a finite string

The two deficiencies of a length-`n` string — `n - C(x)` and `n - C(x | n)` — differ by at
most a logarithmic term: `deficiency_comparison_le_log` (SUV Exercise 55), through
`deficiency_bound_helper`.

The other half of the module is the block decompressor `infOftenDecompressor`, which
compresses infinitely many strings: `infOftenFindK` reads a block index off the length of the
program, `infOftenDecode` is the decoding rule, and `infOftenNatToBits` writes a number in a
fixed width; `infOften_bound`, `infOften_unique` and `infOftenFindK_spec` are its
correctness.  The module closes with the information exercises 58–65, starting with
`deterministic_information_conservation` (Exercise 58): a computable map cannot create
information.
-/

namespace Kolmogorov
open Nat.Partrec (Code)
open StagedEnumeration CodedFiniteDistribution
open Kolmogorov.CodedFiniteDistribution
variable (Q : ℕ × ℕ × BitString → Bool)

/-- Strings of equal length denoting the same number are equal. -/
lemma bitsToNat_inj_of_length_eq {s1 s2 : BitString} (hlen : s1.length = s2.length)
    (hval : bitsToNat s1 = bitsToNat s2) : s1 = s2 := by
  induction s1 generalizing s2 with
  | nil =>
    cases s2 with
    | nil => rfl
    | cons b t => dsimp at hlen; omega
  | cons b1 t1 ih =>
    cases s2 with
    | nil => dsimp at hlen; omega
    | cons b2 t2 =>
      have h1 : bitsToNat (b1 :: t1) = 2 * bitsToNat t1 + if b1 then 1 else 0 := rfl
      have h2 : bitsToNat (b2 :: t2) = 2 * bitsToNat t2 + if b2 then 1 else 0 := rfl
      rw [h1, h2] at hval
      dsimp at hlen
      have hb : b1 = b2 := by
        cases b1 <;> cases b2
        · rfl
        · exfalso
          have hmod : (2 * bitsToNat t1) % 2 = (2 * bitsToNat t2 + 1) % 2 := congrArg (· % 2) hval
          omega
        · exfalso
          have hmod : (2 * bitsToNat t1 + 1) % 2 = (2 * bitsToNat t2) % 2 := congrArg (· % 2) hval
          omega
        · rfl
      subst hb
      have ht : bitsToNat t1 = bitsToNat t2 := by
        cases b1 <;> omega
      rw [ih (by omega) ht]

/-- The number `v` written in exactly `k` bits. -/
def infOftenNatToBits (k v : ℕ) : BitString := padTo k (Nat.bits v)

private lemma infOftenNatToBits_bitsToNat (s : BitString) :
    infOftenNatToBits s.length (bitsToNat s) = s := by
  dsimp [infOftenNatToBits]
  have h_len : (padTo s.length (Nat.bits (bitsToNat s))).length = s.length := by
    apply length_padTo
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr (bitsToNat_lt_two_pow s)
  have h_val : bitsToNat (padTo s.length (Nat.bits (bitsToNat s))) = bitsToNat s := by
    rw [bitsToNat_padTo, bitsToNat_bits]
  exact bitsToNat_inj_of_length_eq h_len h_val

/-- The block index `k` a program of length `m` belongs to, namely the `k` with
`2 ^ (k + 1) - k ≤ m < 3 * 2 ^ k - k`, if there is one. -/
def infOftenFindK (m : ℕ) : Option ℕ :=
  (List.range (m + 1)).find? (fun k => decide (2^(k+1) - k ≤ m ∧ m < 3 * 2^k - k))

/-- Decoding rule of the block decompressor: the length of the program determines a block index
`k` and a value `v`, and the output is `v` written in `k` bits followed by the program. -/
def infOftenDecode (q : BitString) : Option BitString :=
  match infOftenFindK q.length with
  | none => none
  | some k =>
    let v := q.length + k - 2^(k+1)
    some (infOftenNatToBits k v ++ q)

/-- The decompressor given by the block decoding rule; it compresses infinitely many strings by
the length of their prepended block value. -/
def infOftenDecompressor : Map := fun pr => Part.ofOption (infOftenDecode pr.1)

private lemma infOften_bound (k d : ℕ) (hd : d ≥ 1) : 2^(k + d + 1) ≥ 3 * 2^k + d := by
  induction d, hd using Nat.le_induction with
  | base =>
    have h_pow : 2^(k + 1 + 1) = 4 * 2^k := by ring
    have h2 : 2^k ≥ 1 := Nat.two_pow_pos k
    omega
  | succ d hd ih =>
    have h_add : k + (d + 1) + 1 = (k + d + 1) + 1 := by omega
    have h_pow : 2^((k + d + 1) + 1) = 2 * 2^(k + d + 1) := by ring
    have h2 : 2^k ≥ 1 := Nat.two_pow_pos k
    rw [h_add, h_pow]
    omega

private lemma infOften_unique {m k1 k2 : ℕ}
    (h1 : 2 ^ (k1 + 1) - k1 ≤ m ∧ m < 3 * 2 ^ k1 - k1)
    (h2 : 2 ^ (k2 + 1) - k2 ≤ m ∧ m < 3 * 2 ^ k2 - k2) : k1 = k2 := by
  wlog h : k1 ≤ k2 with H
  · exact (H h2 h1 (by omega)).symm
  rcases eq_or_lt_of_le h with rfl | hlt
  · rfl
  · set d := k2 - k1
    have hd : d ≥ 1 := by omega
    have hk2 : k2 = k1 + d := by omega
    have h_b := infOften_bound k1 d hd
    have h_eq : k1 + d + 1 = k2 + 1 := by omega
    have h_ge : 2^(k2 + 1) - k2 ≥ 3 * 2^k1 - k1 := by
      rw [← h_eq, hk2]
      omega
    omega

private lemma infOftenFindK_spec {k : ℕ} (_ : k ≥ 1) {v : ℕ} (hv : v < 2 ^ k) :
    infOftenFindK (2^(k+1) + v - k) = some k := by
  dsimp [infOftenFindK]
  have h_pow2 : 2^(k+1) = 2 * 2^k := by ring
  have h_pow_pos : 2^k ≥ 1 := Nat.two_pow_pos k
  have h_pow_ge_k : 2^(k+1) ≥ k := by have := (k + 1).lt_pow_self (by decide : 1 < 2); omega
  have h_pow_ge_k' : 2 * 2^k ≥ k := by rw [← h_pow2]; exact h_pow_ge_k
  have hm_ge : 2^(k+1) - k ≤ 2^(k+1) + v - k :=
    Nat.sub_le_sub_right (Nat.le_add_right (2^(k+1)) v) k
  have hm_lt : 2^(k+1) + v - k < 3 * 2^k - k := by
    have h1 : 2^(k+1) = 2 * 2^k := h_pow2
    have h2 : 2 * 2^k + v < 3 * 2^k := by omega
    have h3 : 2^(k+1) + v < 3 * 2^k := by rw [h1]; exact h2
    have h4 : k ≤ 2^(k+1) + v := by
      have : k ≤ 2 * 2^k := h_pow_ge_k'
      rw [← h1] at this
      omega
    exact Nat.sub_lt_sub_right h4 h3
  have hk_mem : k ∈ List.range (2^(k+1) + v - k + 1) := by
    rw [List.mem_range, h_pow2]
    have h_k_lt : k < 2^k := k.lt_pow_self (by decide)
    have h_pow_pos : 1 ≤ 2^k := Nat.two_pow_pos k
    generalize hX : 2^k = X at h_k_lt h_pow_pos ⊢
    omega
  have h_some : (List.range (2^(k+1) + v - k + 1)).find?
        (fun k' => decide (2^(k'+1) - k' ≤ 2^(k+1) + v - k ∧
          2^(k+1) + v - k < 3 * 2^k' - k')) ≠ none := by
    rw [ne_eq, List.find?_eq_none]
    intro h_none
    have h_k := h_none k hk_mem
    have h_dec : decide (2^(k+1) - k ≤ 2^(k+1) + v - k ∧
        2^(k+1) + v - k < 3 * 2^k - k) = true :=
      decide_eq_true ⟨hm_ge, hm_lt⟩
    exact h_k h_dec
  rcases h_find : (List.range (2^(k+1) + v - k + 1)).find?
      (fun k' => decide (2^(k'+1) - k' ≤ 2^(k+1) + v - k ∧
        2^(k+1) + v - k < 3 * 2^k' - k')) with _ | k'
  · exact (h_some h_find).elim
  · have h_prop := List.find?_some h_find
    simp only [decide_eq_true_eq] at h_prop
    have h_uniq := infOften_unique ⟨hm_ge, hm_lt⟩ h_prop
    subst h_uniq
    rfl

private lemma infOftenDecode_q {w : ℕ → Bool} {k : ℕ} (hk : k ≥ 1) :
    infOftenDecode ((seqPrefix w (2^(k+1) + bitsToNat (seqPrefix w k))).drop k) =
      some (seqPrefix w (2^(k+1) + bitsToNat (seqPrefix w k))) := by
  set s_k := seqPrefix w k
  set v_k := bitsToNat s_k
  have h_sk_len : s_k.length = k := by simp [s_k, seqPrefix]
  have h_vk_lt : v_k < 2^k := by
    have h := bitsToNat_lt_two_pow s_k
    rw [h_sk_len] at h
    exact h
  have h_pow_ge : 2^(k+1) ≥ k := by have := (k + 1).lt_pow_self (by decide : 1 < 2); omega
  have h_qk_len : ((seqPrefix w (2^(k+1) + v_k)).drop k).length = 2^(k+1) + v_k - k := by
    have hs_len : (seqPrefix w (2^(k+1) + v_k)).length = 2^(k+1) + v_k := by simp [seqPrefix]
    rw [List.length_drop, hs_len]
  have h_v_eq : 2^(k+1) + v_k - k + k - 2^(k+1) = v_k := by omega
  have h_natToBits : infOftenNatToBits k v_k = s_k := by
    have h := infOftenNatToBits_bitsToNat s_k
    rw [h_sk_len] at h
    exact h
  have h_take : (seqPrefix w (2^(k+1) + v_k)).take k = s_k := by
    dsimp [s_k, seqPrefix]
    rw [← List.map_take, List.take_range]
    have : k ≤ 2^(k+1) + v_k := by omega
    simp [this]
  dsimp [infOftenDecode]
  rw [h_qk_len, infOftenFindK_spec hk h_vk_lt]
  have h_match : (match some k with
      | none => none
      | some k_1 => some (infOftenNatToBits k_1 (2 ^ (k + 1) + v_k - k + k_1 - 2 ^ (k_1 + 1)) ++
        List.drop k (seqPrefix w (2 ^ (k + 1) + v_k)))) =
      some (infOftenNatToBits k (2^(k+1) + v_k - k + k - 2^(k+1)) ++
        (seqPrefix w (2^(k+1) + v_k)).drop k) := rfl
  rw [h_match, h_v_eq, h_natToBits, ← h_take, List.take_append_drop]

private lemma infOftenFindK_primrec : Primrec infOftenFindK := by
  have h2pow : Primrec (fun n : ℕ => 2 ^ n) := primrec_two_pow_aux
  have h1 : Primrec (fun (p : ℕ × ℕ) => 2^(p.2+1) - p.2) :=
    Primrec.nat_sub.comp
      (h2pow.comp (Primrec.nat_add.comp Primrec.snd (Primrec.const 1))) Primrec.snd
  have h2 : Primrec (fun (p : ℕ × ℕ) => 3 * 2^p.2 - p.2) :=
    Primrec.nat_sub.comp
      (Primrec.nat_mul.comp (Primrec.const 3) (h2pow.comp Primrec.snd)) Primrec.snd
  have h_le : Primrec (fun (p : ℕ × ℕ) => decide (2^(p.2+1) - p.2 ≤ p.1)) :=
    PrimrecPred.decide (Primrec.nat_le.comp h1 Primrec.fst)
  have h_lt : Primrec (fun (p : ℕ × ℕ) => decide (p.1 < 3 * 2^p.2 - p.2)) :=
    PrimrecPred.decide (Primrec.nat_lt.comp Primrec.fst h2)
  have h_pred_bool : Primrec (fun (p : ℕ × ℕ) =>
      decide (2^(p.2+1) - p.2 ≤ p.1) && decide (p.1 < 3 * 2^p.2 - p.2)) :=
    Primrec.and.comp h_le h_lt
  have h_pred : Primrec₂ (fun (m : ℕ) (k : ℕ) => decide (2^(k+1) - k ≤ m ∧ m < 3 * 2^k - k)) :=
    h_pred_bool.to₂.of_eq (fun m k => by simp)
  have h_range : Primrec (fun m => List.range (m + 1)) :=
    Primrec.list_range.comp (Primrec.nat_add.comp Primrec.id (Primrec.const 1))
  exact list_find?_primrec h_range h_pred

private lemma infOftenNatToBits_primrec : Primrec₂ infOftenNatToBits := by
  have h_bits : Primrec (fun (p : ℕ × ℕ) => Nat.bits p.2) :=
    primrec_natBits.comp Primrec.snd
  have h_sub : Primrec (fun (p : ℕ × ℕ) => p.1 - (Nat.bits p.2).length) :=
    Primrec.nat_sub.comp Primrec.fst (Primrec.list_length.comp h_bits)
  have h_rep : Primrec (fun (p : ℕ × ℕ) => List.replicate (p.1 - (Nat.bits p.2).length) false) :=
    Primrec.list_replicate.comp h_sub (Primrec.const false)
  exact (Primrec.list_append.comp h_bits h_rep).to₂

private lemma infOftenDecode_primrec : Primrec infOftenDecode := by
  have h_m : Primrec (fun p : BitString => p.length) := Primrec.list_length
  have h_find : Primrec (fun p : BitString => infOftenFindK p.length) :=
    infOftenFindK_primrec.comp h_m
  have h_some : Primrec (fun (pair : BitString × ℕ) =>
      infOftenNatToBits pair.2 (pair.1.length + pair.2 - 2^(pair.2+1)) ++ pair.1) := by
    have h2pow : Primrec (fun n : ℕ => 2 ^ n) := primrec_two_pow_aux
    have h_v : Primrec (fun (pair : BitString × ℕ) => pair.1.length + pair.2 - 2^(pair.2+1)) :=
      Primrec.nat_sub.comp
        (Primrec.nat_add.comp (Primrec.list_length.comp Primrec.fst) Primrec.snd)
        (h2pow.comp (Primrec.nat_add.comp Primrec.snd (Primrec.const 1)))
    have h_nat : Primrec (fun (pair : BitString × ℕ) =>
        infOftenNatToBits pair.2 (pair.1.length + pair.2 - 2^(pair.2+1))) :=
      infOftenNatToBits_primrec.comp Primrec.snd h_v
    exact Primrec.list_append.comp h_nat Primrec.fst
  have h_option : Primrec (fun p : BitString =>
      (infOftenFindK p.length).map (fun k => infOftenNatToBits k (p.length + k - 2^(k+1)) ++ p)) :=
    Primrec.option_map h_find h_some.to₂
  exact h_option.of_eq (by
    intro p
    dsimp [infOftenDecode]
    cases infOftenFindK p.length <;> rfl)

/-- **Exercise 54, upper half.** Every infinite sequence has infinitely many
prefixes with `C(prefix_n) ≤ n - log n + O(1)`. -/
theorem exists_infinitely_many_prefix_plainK_le (U : Map) (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ w : ℕ → Bool, {n : ℕ | plainK U (seqPrefix w n) ≤
      ((n - Nat.log 2 n + c : ℕ) : ℕ∞)}.Infinite := by
  have h_comp : Computable (fun (pr : BitString × BitString) => infOftenDecode pr.1) :=
    infOftenDecode_primrec.to_comp.comp Computable.fst
  have h_D_is : isDecompressor infOftenDecompressor := Computable.ofOption h_comp
  obtain ⟨cD, hcD⟩ := hU.2 infOftenDecompressor h_D_is
  refine ⟨cD + 1, fun w => ?_⟩
  set f : ℕ → ℕ := fun k =>
    let k' := k + 1
    let s_k := seqPrefix w k'
    let v_k := bitsToNat s_k
    2^(k' + 1) + v_k
  have h_inj : Function.Injective f := by
    intro k1 k2 hk
    dsimp [f] at hk
    have h1 (k : ℕ) : 2^(k + 1) ≤ 2^(k + 1) + bitsToNat (seqPrefix w k) := by omega
    have h2 (k : ℕ) : 2^(k + 1) + bitsToNat (seqPrefix w k) < 2^(k + 2) := by
      have hs : (seqPrefix w k).length = k := by simp [seqPrefix]
      have h_bits := bitsToNat_lt_two_pow (seqPrefix w k)
      rw [hs] at h_bits
      have : 2^(k + 1) + 2^k = 3 * 2^k := by ring
      have : 2^(k + 2) = 4 * 2^k := by ring
      omega
    have h_pow1 := h1 (k1 + 1)
    have h_pow2 := h2 (k1 + 1)
    have h_pow3 := h1 (k2 + 1)
    have h_pow4 := h2 (k2 + 1)
    rw [hk] at h_pow1 h_pow2
    have hk_eq : k1 + 1 = k2 + 1 := by
      by_contra h_neq
      rcases lt_or_gt_of_ne h_neq with h_lt | h_gt
      · have : 2^(k1 + 1 + 2) ≤ 2^(k2 + 1 + 1) := Nat.pow_le_pow_right (by decide) (by omega)
        omega
      · have : 2^(k2 + 1 + 2) ≤ 2^(k1 + 1 + 1) := Nat.pow_le_pow_right (by decide) (by omega)
        omega
    exact Nat.succ.inj hk_eq
  have h_sub : Set.range f ⊆ {n : ℕ | plainK U (seqPrefix w n) ≤
      ((n - Nat.log 2 n + (cD + 1) : ℕ) : ℕ∞)} := by
    rintro n ⟨k, rfl⟩
    dsimp [f]
    set k' := k + 1
    have hk1 : k' ≥ 1 := by omega
    set s_k := seqPrefix w k'
    set v_k := bitsToNat s_k
    set n_k := 2^(k' + 1) + v_k
    set x_k := seqPrefix w n_k
    set q_k := x_k.drop k'
    have h_dec := infOftenDecode_q hk1 (w := w)
    have h_prod : produces infOftenDecompressor q_k [] x_k := by
      dsimp [produces, infOftenDecompressor]
      rw [h_dec]
      exact Part.mem_some _
    have h_plain_D : plainK infOftenDecompressor x_k ≤ (q_k.length : ℕ∞) :=
      sInf_le ⟨q_k, h_prod, rfl⟩
    have h_plain_U : plainK U x_k ≤ plainK infOftenDecompressor x_k + (cD : ℕ∞) := hcD x_k []
    have h_xk_len : x_k.length = n_k := by simp [x_k, seqPrefix]
    have h_qk_len : q_k.length = n_k - k' := by
      dsimp [q_k]
      rw [List.length_drop, h_xk_len]
    have h_le_m : plainK U x_k ≤ ((q_k.length + cD : ℕ) : ℕ∞) := by
      have h_add : plainK infOftenDecompressor x_k + (cD : ℕ∞) ≤ (q_k.length : ℕ∞) + (cD : ℕ∞) :=
        add_le_add_left h_plain_D (cD : ℕ∞)
      have h_sum : (q_k.length : ℕ∞) + (cD : ℕ∞) = ((q_k.length + cD : ℕ) : ℕ∞) := by push_cast; rfl
      exact (hcD x_k []).trans (h_add.trans_eq h_sum)
    have h_nk_lt : n_k < 2^(k' + 2) := by
      have hs_k_len : s_k.length = k' := by simp [s_k, seqPrefix]
      have h_vk : v_k < 2^k' := by
        have h := bitsToNat_lt_two_pow s_k
        rw [hs_k_len] at h
        exact h
      have h1 : 2^(k' + 1) = 2 * 2^k' := by ring
      have h2 : 2^(k' + 2) = 4 * 2^k' := by ring
      have h_nk_eq : n_k = 2 * 2^k' + v_k := by dsimp [n_k]; rw [h1]
      have h_lt_4 : 2 * 2^k' + v_k < 4 * 2^k' := by
        have h_le : 2 * 2^k' + v_k < 2 * 2^k' + 2^k' := Nat.add_lt_add_left h_vk _
        have h_sum : 2 * 2^k' + 2^k' = 3 * 2^k' := by ring
        have h_lt3 : 3 * 2^k' < 4 * 2^k' := by
          have hP : 1 ≤ 2^k' := Nat.two_pow_pos k'
          generalize hX : 2^k' = X at hP ⊢
          omega
        exact lt_trans h_le (h_sum.symm ▸ h_lt3)
      calc n_k = 2 * 2^k' + v_k := h_nk_eq
      _ < 4 * 2^k' := h_lt_4
      _ = 2^(k' + 2) := h2.symm
    have h_log : Nat.log 2 n_k ≤ k' + 1 := by
      have h_pos : n_k > 0 := by
        dsimp [n_k]
        have : 0 < 2^(k' + 1) := Nat.two_pow_pos (k' + 1)
        omega
      have h_lt := Nat.log_lt_of_lt_pow h_pos.ne' h_nk_lt
      exact Nat.le_of_lt_succ h_lt
    have h_arith : n_k - k' + cD ≤ n_k - Nat.log 2 n_k + (cD + 1) := by omega
    calc plainK U (seqPrefix w n_k) = plainK U x_k := rfl
    _ ≤ ((n_k - k' + cD : ℕ) : ℕ∞) := by rw [h_qk_len] at h_le_m; exact h_le_m
    _ ≤ ((n_k - Nat.log 2 n_k + (cD + 1) : ℕ) : ℕ∞) := by exact_mod_cast h_arith
  exact Set.Infinite.mono h_sub (Set.infinite_range_of_injective h_inj)

open Classical in
/-- `x` is good for the constant `c` when every prefix of `x` of length `n` has complexity at
least `n - 2 log n - c`. -/
def goodPrefix (U : Map) (c : ℕ) (x : BitString) : Prop :=
  ∀ n ≤ x.length, ((n : ℕ) : ℕ∞) ≤ plainK U (x.take n) + ((2 * Nat.log 2 n + c : ℕ) : ℕ∞)

open Classical in
/-- `s` is a valid prefix when it extends to good strings of infinitely many lengths. -/
def validPrefix (U : Map) (c : ℕ) (s : BitString) : Prop :=
  {N : ℕ | ∃ x : BitString, x.length = N ∧ s <+: x ∧ goodPrefix U c x}.Infinite

open Classical in
/-- The length-`n` prefix of the sequence built by always extending with a bit that keeps the
prefix valid. -/
noncomputable def matchingSeqAux (U : Map) (c : ℕ) : ℕ → BitString
  | 0 => []
  | n + 1 =>
    let s := matchingSeqAux U c n
    if validPrefix U c (s ++ [false]) then s ++ [false] else s ++ [true]

open Classical in
/-- The infinite sequence all of whose prefixes are valid, obtained from the greedy extension. -/
noncomputable def matchingSeq (U : Map) (c : ℕ) : ℕ → Bool := fun n =>
  ((matchingSeqAux U c (n + 1))[n]?).getD false

/-- The greedy prefix of index `n` has length `n`. -/
theorem matchingSeqAux_length (U : Map) (c : ℕ) (n : ℕ) :
    (matchingSeqAux U c n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    dsimp [matchingSeqAux]
    split_ifs <;> simp [ih]

/-- The greedy prefixes are nested. -/
lemma matchingSeqAux_prefix (U : Map) (c : ℕ) {m n : ℕ} (h : m ≤ n) :
    matchingSeqAux U c m <+: matchingSeqAux U c n := by
  induction n, h using Nat.le_induction with
  | base => exact ⟨[], by simp⟩
  | succ n h_le ih =>
    dsimp [matchingSeqAux]
    have h_sub (b : Bool) : matchingSeqAux U c n <+: matchingSeqAux U c n ++ [b] := ⟨[b], rfl⟩
    split_ifs
    · exact ih.trans (h_sub false)
    · exact ih.trans (h_sub true)

/-- The length-`n` prefix of the greedy sequence is the greedy prefix of index `n`. -/
theorem seqPrefix_matchingSeq (U : Map) (c : ℕ) (n : ℕ) :
    seqPrefix (matchingSeq U c) n = matchingSeqAux U c n := by
  ext i
  by_cases hi : i < n
  · have h1 : (seqPrefix (matchingSeq U c) n)[i]? = some (matchingSeq U c i) := by
      simp [seqPrefix, hi]
    have h_pref : matchingSeqAux U c (i + 1) <+: matchingSeqAux U c n :=
      matchingSeqAux_prefix U c hi
    rcases h_pref with ⟨u, hu⟩
    have h2 : (matchingSeqAux U c n)[i]? = (matchingSeqAux U c (i + 1))[i]? := by
      rw [← hu, List.getElem?_append]
      have : i < (matchingSeqAux U c (i + 1)).length := by
        rw [matchingSeqAux_length]; omega
      simp [this]
    rw [h1, h2]
    dsimp [matchingSeq]
    have h_get : (matchingSeqAux U c (i + 1))[i]? =
        some ((matchingSeqAux U c (i + 1))[i]'(by rw [matchingSeqAux_length]; omega)) := by
      rw [List.getElem?_eq_getElem]
    rw [h_get]
    rfl
  · have h1 : (seqPrefix (matchingSeq U c) n)[i]? = none := by simp [seqPrefix, hi]
    have h2 : (matchingSeqAux U c n)[i]? = none := by
      have : (matchingSeqAux U c n).length = n := matchingSeqAux_length U c n
      simp [this, hi]
    rw [h1, h2]

/-- A valid prefix stays valid after appending `0` or after appending `1`. -/
theorem validPrefix_step (U : Map) (c : ℕ) (s : BitString) (h : validPrefix U c s) :
    validPrefix U c (s ++ [false]) ∨ validPrefix U c (s ++ [true]) := by
  dsimp [validPrefix] at h ⊢
  set S := {N : ℕ | ∃ x : BitString, x.length = N ∧ s <+: x ∧ goodPrefix U c x}
  set S_f := {N : ℕ | ∃ x : BitString, x.length = N ∧ (s ++ [false]) <+: x ∧ goodPrefix U c x}
  set S_t := {N : ℕ | ∃ x : BitString, x.length = N ∧ (s ++ [true]) <+: x ∧ goodPrefix U c x}
  have h_sub : S \ ↑(Finset.range (s.length + 1)) ⊆ S_f ∪ S_t := by
    intro N hN
    rw [Set.mem_diff, Finset.mem_coe, Finset.mem_range] at hN
    rcases hN.1 with ⟨x, hx_len, hx_pref, hx_good⟩
    rcases hx_pref with ⟨t, ht⟩
    cases t with
    | nil =>
      exfalso
      have : x.length = s.length := by rw [← ht]; simp
      omega
    | cons b t' =>
      cases b
      · left
        refine ⟨x, hx_len, ⟨t', ?_⟩, hx_good⟩
        rw [List.append_assoc]
        exact ht
      · right
        refine ⟨x, hx_len, ⟨t', ?_⟩, hx_good⟩
        rw [List.append_assoc]
        exact ht
  have h_inf_diff : (S \ ↑(Finset.range (s.length + 1))).Infinite :=
    h.diff (Finset.finite_toSet _)
  have h_inf_union : (S_f ∪ S_t).Infinite := Set.Infinite.mono h_sub h_inf_diff
  by_cases hf : S_f.Infinite
  · exact Or.inl hf
  · right
    have h_diff : ((S_f ∪ S_t) \ S_f).Infinite := h_inf_union.diff (Set.not_infinite.mp hf)
    have h_sub_t : (S_f ∪ S_t) \ S_f ⊆ S_t := Set.diff_subset_iff.mpr (Set.Subset.refl _)
    exact h_diff.mono h_sub_t

/-- Decompressor that runs `U` on a self-delimiting initial field of the program and appends the
remaining bits of the program to the output. -/
def prefixDecompressor (U : Map) : Map := fun pr =>
  let p := pr.1
  let len := decodeBits (decodeFirst p)
  let rest := decodeSecond p
  let py := rest.take len
  let z := rest.drop len
  (U (py, [])).map (fun y => y ++ z)

/-- The prefix-extension decompressor is a decompressor whenever `U` is. -/
lemma prefixDecompressor_isDecompressor (U : Map) (hU : isDecompressor U) :
    isDecompressor (prefixDecompressor U) := by
  change Partrec (prefixDecompressor U)
  have h_len : Computable (fun pr : BitString × BitString => decodeBits (decodeFirst pr.1)) :=
    decodeBits_computable.comp (decodeFirst_computable.comp Computable.fst)
  have h_rest : Computable (fun pr : BitString × BitString => decodeSecond pr.1) :=
    decodeSecond_computable.comp Computable.fst
  have h_py : Computable (fun pr : BitString × BitString =>
      (decodeSecond pr.1).take (decodeBits (decodeFirst pr.1))) :=
    primrec_list_take.to_comp.comp h_rest h_len
  have h_z : Computable (fun pr : BitString × BitString =>
      (decodeSecond pr.1).drop (decodeBits (decodeFirst pr.1))) :=
    primrec_list_drop.to_comp.comp h_rest h_len
  have h_U_py : Partrec (fun pr : BitString × BitString =>
      U ((decodeSecond pr.1).take (decodeBits (decodeFirst pr.1)), [])) :=
    hU.comp (h_py.pair (Computable.const []))
  have h_map_fn : Computable (fun q : (BitString × BitString) × BitString =>
      q.2 ++ (decodeSecond q.1.1).drop (decodeBits (decodeFirst q.1.1))) :=
    (show Computable₂ (fun (a b : BitString) => a ++ b)
      from Primrec.to_comp Primrec.list_append).comp
      Computable.snd
      (h_z.comp Computable.fst)
  exact h_U_py.map h_map_fn

/-- There is a constant `c` such that strings good for `c` exist in every length. -/
lemma exists_goodPrefix (U : Map) (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ N : ℕ, ∃ x : BitString, x.length = N ∧ goodPrefix U c x := by
  obtain ⟨c_opt, hc_opt⟩ := plainK_le_length U hU
  obtain ⟨c_pref, hc_pref⟩ := hU.2 (prefixDecompressor U) (prefixDecompressor_isDecompressor U hU.1)
  refine ⟨2 * c_opt + c_pref + 10, fun N => ?_⟩
  obtain ⟨x, hx_len, hx_incomp⟩ := exists_incompressible_string U [] N
  refine ⟨x, hx_len, fun n hn => ?_⟩
  by_cases hn0 : n = 0
  · subst hn0; simp
  set y := x.take n
  set z := x.drop n
  obtain ⟨py, hpy_prod, hpy_len⟩ := exists_program_le_cVal U hU y
  set p := pairCode (Nat.bits py.length) (py ++ z)
  have hp_prod : produces (prefixDecompressor U) p [] x := by
    dsimp [produces, prefixDecompressor, p]
    rw [decodeFirst_pairCode, decodeBits_natBits, decodeSecond_pairCode]
    rw [List.take_left, List.drop_left]
    have h_map := Part.mem_map (fun u => u ++ z) hpy_prod
    have h_yz : y ++ z = x := List.take_append_drop n x
    have h_eq : (fun u => u ++ z) y = x := by dsimp; exact h_yz
    rw [← h_eq]
    exact h_map
  have hp_len : p.length = 2 * (Nat.bits py.length).length + 1 + py.length + z.length := by
    dsimp [p]
    rw [length_pairCode, List.length_append]
    ring
  have h_py_bound : py.length ≤ n + c_opt := by
    calc py.length ≤ cVal U y := hpy_len
    _ ≤ y.length + c_opt := ENat.toNat_le_of_le_coe (hc_opt y)
    _ = n + c_opt := by dsimp [y]; rw [List.length_take, hx_len]; omega
  have h_log_succ_le (m : ℕ) : Nat.log 2 (m + 1) ≤ Nat.log 2 m + 1 := by
    have := log_succ_le m
    omega
  have h_bits_len : (Nat.bits py.length).length ≤ Nat.log 2 n + c_opt + 1 := by
    have h1 := length_natBits_le_log py.length
    have h2 : Nat.log 2 py.length ≤ Nat.log 2 (n + c_opt) := Nat.log_mono_right h_py_bound
    have h3 : Nat.log 2 (n + c_opt) ≤ Nat.log 2 n + c_opt := by
      have h_log (n k : ℕ) : Nat.log 2 (n + k) ≤ Nat.log 2 n + k := by
        induction k with
        | zero => rfl
        | succ k' ih =>
          have h1 : n + (k' + 1) = (n + k') + 1 := by omega
          rw [h1]
          have h_step := log_succ_le (n + k')
          calc Nat.log 2 (n + k' + 1) ≤ Nat.log 2 (n + k') + 1 := h_step
          _ ≤ Nat.log 2 n + k' + 1 := Nat.add_le_add_right ih 1
          _ = Nat.log 2 n + (k' + 1) := by omega
      exact h_log n c_opt
    exact (h1.trans (Nat.add_le_add_right h2 1)).trans (Nat.add_le_add_right h3 1)
  have hz_len : z.length = N - n := by
    dsimp [z]; rw [List.length_drop, hx_len]
  have hp_bound : p.length ≤ cVal U y + 2 * Nat.log 2 n + 2 * c_opt + 3 + N - n := by
    rw [hp_len, hz_len]
    have hB : (Nat.bits py.length).length ≤ Nat.log 2 n + c_opt + 1 := h_bits_len
    have hL : py.length ≤ cVal U y := hpy_len
    have hn_le : n ≤ N := hx_len ▸ hn
    have h1 : 2 * (Nat.bits py.length).length + 1 + py.length ≤
        cVal U y + 2 * Nat.log 2 n + 2 * c_opt + 3 := by
      have h_bits := h_bits_len
      have h_py := hpy_len
      have h_mul : 2 * (Nat.bits py.length).length ≤ 2 * Nat.log 2 n + 2 * c_opt + 2 := by
        calc 2 * (Nat.bits py.length).length ≤ 2 * (Nat.log 2 n + c_opt + 1) :=
          Nat.mul_le_mul_left 2 h_bits
        _ = 2 * Nat.log 2 n + 2 * c_opt + 2 := by ring
      omega
    have h2 : 2 * (Nat.bits py.length).length + 1 + py.length + (N - n) ≤
        cVal U y + 2 * Nat.log 2 n + 2 * c_opt + 3 + (N - n) :=
      Nat.add_le_add_right h1 (N - n)
    have h3 : cVal U y + 2 * Nat.log 2 n + 2 * c_opt + 3 + (N - n) =
        cVal U y + 2 * Nat.log 2 n + 2 * c_opt + 3 + N - n :=
      (Nat.add_sub_assoc hn_le _).symm
    exact h2.trans_eq h3
  have h_plain_pref : plainK (prefixDecompressor U) x ≤ (p.length : ℕ∞) :=
    sInf_le ⟨p, hp_prod, rfl⟩
  have h_plain_U : plainK U x ≤ plainK (prefixDecompressor U) x + (c_pref : ℕ∞) :=
    hc_pref x []
  have h_cVal_le : (cVal U y : ℕ∞) ≤ plainK U y := by
    have h_ne : plainK U y ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top (y.length + c_opt))
      (by calc plainK U y ≤ (y.length : ℕ∞) + (c_opt : ℕ∞) := hc_opt y
      _ = ((y.length + c_opt : ℕ) : ℕ∞) := by push_cast; rfl)
    dsimp [cVal]
    rw [ENat.coe_toNat h_ne]
  have h_diff_ne : ((N - n : ℕ) : ℕ∞) ≠ ⊤ := ENat.coe_ne_top (N - n)
  have h_lhs : (N : ℕ∞) = (n : ℕ∞) + ((N - n : ℕ) : ℕ∞) := by
    have : N = n + (N - n) := by omega
    exact_mod_cast this
  have h_rhs : plainK U y + ((2 * Nat.log 2 n + 2 * c_opt + c_pref + 3 + N - n : ℕ) : ℕ∞) =
      plainK U y + ((2 * Nat.log 2 n + (2 * c_opt + c_pref + 3) : ℕ) : ℕ∞) +
        ((N - n : ℕ) : ℕ∞) := by
    calc plainK U y + ((2 * Nat.log 2 n + 2 * c_opt + c_pref + 3 + N - n : ℕ) : ℕ∞)
      _ = plainK U y + ((2 * Nat.log 2 n + (2 * c_opt + c_pref + 3) + (N - n) : ℕ) : ℕ∞) := by
        congr 2; omega
      _ = plainK U y + (((2 * Nat.log 2 n + (2 * c_opt + c_pref + 3) : ℕ) : ℕ∞) +
          ((N - n : ℕ) : ℕ∞)) := by push_cast; rfl
      _ = plainK U y + ((2 * Nat.log 2 n + (2 * c_opt + c_pref + 3) : ℕ) : ℕ∞) +
          ((N - n : ℕ) : ℕ∞) := by rw [← add_assoc]
  have h_chain : (n : ℕ∞) + ((N - n : ℕ) : ℕ∞) ≤ plainK U y +
      ((2 * Nat.log 2 n + (2 * c_opt + c_pref + 3) : ℕ) : ℕ∞) + ((N - n : ℕ) : ℕ∞) := by
    rw [← h_lhs, ← h_rhs]
    have h1 : plainK (prefixDecompressor U) x + (c_pref : ℕ∞) ≤
        (p.length : ℕ∞) + (c_pref : ℕ∞) := by gcongr
    have h2 : (cVal U y : ℕ∞) + ((2 * Nat.log 2 n + 2 * c_opt + c_pref + 3 + N - n : ℕ) : ℕ∞) ≤
        plainK U y + ((2 * Nat.log 2 n + 2 * c_opt + c_pref + 3 + N - n : ℕ) : ℕ∞) := by
      have h2_aux := add_le_add_right h_cVal_le
        ((2 * Nat.log 2 n + 2 * c_opt + c_pref + 3 + N - n : ℕ) : ℕ∞)
      rwa [add_comm _ (cVal U y : ℕ∞), add_comm _ (plainK U y)] at h2_aux
    calc (N : ℕ∞) ≤ plainK U x := hx_incomp
    _ ≤ plainK (prefixDecompressor U) x + (c_pref : ℕ∞) := h_plain_U
    _ ≤ (p.length : ℕ∞) + (c_pref : ℕ∞) := h1
    _ ≤ ((cVal U y + 2 * Nat.log 2 n + 2 * c_opt + 3 + N - n + c_pref : ℕ) : ℕ∞) := by
      have h_sum : p.length + c_pref ≤
          cVal U y + 2 * Nat.log 2 n + 2 * c_opt + 3 + N - n + c_pref :=
        Nat.add_le_add_right hp_bound c_pref
      exact_mod_cast h_sum
    _ ≤ plainK U y + ((2 * Nat.log 2 n + 2 * c_opt + c_pref + 3 + N - n : ℕ) : ℕ∞) := by
      have hn_le : n ≤ N := hx_len ▸ hn
      have h_nat : cVal U y + 2 * Nat.log 2 n + 2 * c_opt + 3 + N - n + c_pref =
          cVal U y + (2 * Nat.log 2 n + 2 * c_opt + c_pref + 3 + N - n) := by omega
      have : ((cVal U y + 2 * Nat.log 2 n + 2 * c_opt + 3 + N - n + c_pref : ℕ) : ℕ∞) =
          (cVal U y : ℕ∞) + ((2 * Nat.log 2 n + 2 * c_opt + c_pref + 3 + N - n : ℕ) : ℕ∞) := by
        rw [h_nat]
        push_cast
        rfl
      rw [this]
      exact h2
  have h_cancel := (WithTop.add_le_add_iff_right h_diff_ne).mp h_chain
  calc (n : ℕ∞) ≤ plainK U y + ((2 * Nat.log 2 n + (2 * c_opt + c_pref + 3) : ℕ) : ℕ∞) := h_cancel
  _ ≤ plainK U (x.take n) + ((2 * Nat.log 2 n + (2 * c_opt + c_pref + 10) : ℕ) : ℕ∞) := by
    have h_cast : ((2 * Nat.log 2 n + (2 * c_opt + c_pref + 3) : ℕ) : ℕ∞) ≤
        ((2 * Nat.log 2 n + (2 * c_opt + c_pref + 10) : ℕ) : ℕ∞) := by
      exact_mod_cast (by omega : 2 * Nat.log 2 n + (2 * c_opt + c_pref + 3) ≤
        2 * Nat.log 2 n + (2 * c_opt + c_pref + 10))
    have h_add := add_le_add_left h_cast (plainK U y)
    rw [add_comm _ (plainK U y), add_comm _ (plainK U y)] at h_add
    exact h_add

/-- **Exercise 54, matching lower bound.** There is a sequence with
`C(prefix_n) ≥ n - 2 log n - O(1)` for all `n`. -/
theorem exists_sequence_prefix_plainK_ge (U : Map) (hU : isOptimalConditional U) :
    ∃ (w : ℕ → Bool) (c : ℕ), ∀ n : ℕ,
      ((n : ℕ) : ℕ∞) ≤ plainK U (seqPrefix w n) + ((2 * Nat.log 2 n + c : ℕ) : ℕ∞) := by
  rcases exists_goodPrefix U hU with ⟨c, hc⟩
  refine ⟨matchingSeq U c, c, fun n => ?_⟩
  have h_valid0 : validPrefix U c [] := by
    dsimp [validPrefix]
    have h_univ : {N : ℕ | ∃ x : BitString,
        x.length = N ∧ [] <+: x ∧ goodPrefix U c x} = Set.univ := by
      ext N
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      rcases hc N with ⟨x, hx_len, hx_good⟩
      exact ⟨x, hx_len, ⟨x, by simp⟩, hx_good⟩
    rw [h_univ]
    exact Set.infinite_univ
  have h_valid_n (k : ℕ) : validPrefix U c (matchingSeqAux U c k) := by
    induction k with
    | zero => exact h_valid0
    | succ k ih =>
      dsimp [matchingSeqAux]
      split_ifs with h_val
      · exact h_val
      · cases validPrefix_step U c (matchingSeqAux U c k) ih with
        | inl h_f => contradiction
        | inr h_t => exact h_t
  have h_good_prefix : goodPrefix U c (matchingSeqAux U c n) := by
    intro m hm
    have h_m : m ≤ n := by rwa [matchingSeqAux_length] at hm
    have h_val := h_valid_n n
    dsimp [validPrefix] at h_val
    rcases h_val.nonempty with ⟨N, x, hx_len, hx_pref, hx_good⟩
    rcases hx_pref with ⟨t, ht⟩
    have h_take : x.take m = (matchingSeqAux U c n).take m := by
      rw [← ht, List.take_append_of_le_length]
      rw [matchingSeqAux_length]; exact h_m
    have h_le_N : m ≤ x.length := by
      rw [← ht, List.length_append, matchingSeqAux_length]
      omega
    have h_g := hx_good m h_le_N
    rwa [h_take] at h_g
  have h_good_n := h_good_prefix n (by rw [matchingSeqAux_length])
  unfold goodPrefix at h_good_n
  have h_take : (matchingSeqAux U c n).take n = matchingSeqAux U c n :=
    List.take_of_length_le (by rw [matchingSeqAux_length])
  rw [h_take] at h_good_n
  rw [seqPrefix_matchingSeq]
  exact h_good_n

/-- Randomness deficiency `d(x) = |x| - C(x)`. -/
noncomputable def plainDeficiency (U : Map) (x : BitString) : ℤ :=
  (x.length : ℤ) - (cVal U x : ℤ)

/-- Length-conditional randomness deficiency `dc(x) = |x| - C(x | |x|)`. -/
noncomputable def condDeficiency (U : Map) (x : BitString) : ℤ :=
  (x.length : ℤ) - (condCVal U x (Nat.bits x.length) : ℤ)

/-- Decompressor whose program carries the deficiency `d` self-delimitingly in front of a
conditional program `q`, and which runs `U` on `q` with condition `|q| + d`. -/
def deficiencyMap (U : Map) : Map := fun p =>
  let s := decodeFirst p.1
  let q := decodeSecond p.1
  let d := decodeBits s
  let L := q.length + d
  U (q, Nat.bits L)

/-- The deficiency decompressor is partial computable whenever `U` is. -/
theorem deficiencyMap_partrec {U : Map} (hU : Partrec U) : Partrec (deficiencyMap U) := by
  have hg : Computable (fun p : BitString × BitString =>
      (decodeSecond p.1,
       Nat.bits ((decodeSecond p.1).length + decodeBits (decodeFirst p.1)))) := by
    have h1 : Computable (fun p : BitString × BitString => decodeSecond p.1) :=
      decodeSecond_primrec.to_comp.comp Computable.fst
    have h2 : Computable (fun p : BitString × BitString => decodeBits (decodeFirst p.1)) :=
      decodeBits_computable.comp (decodeFirst_primrec.to_comp.comp Computable.fst)
    have h1_len : Computable (fun p : BitString × BitString => (decodeSecond p.1).length) :=
      Computable.list_length.comp h1
    have h3 : Computable (fun p : BitString × BitString =>
        (decodeSecond p.1).length + decodeBits (decodeFirst p.1)) :=
      Primrec.nat_add.to_comp.comp h1_len h2
    exact h1.pair (natBits_computable.comp h3)
  exact hU.comp hg

/-- A conditional program for `x` given its length, prefixed by the deficiency, is an
unconditional program for `x` under the deficiency decompressor. -/
lemma produces_deficiencyMap (U : Map) (x : BitString) (p : BitString) (D_c : ℕ)
    (hprod : produces U p (Nat.bits x.length) x) (hlen : p.length + D_c = x.length) :
    produces (deficiencyMap U) (pairCode (Nat.bits D_c) p) [] x := by
  change x ∈ deficiencyMap U (pairCode (Nat.bits D_c) p, [])
  unfold deficiencyMap
  dsimp
  rw [decodeFirst_pairCode, decodeSecond_pairCode, decodeBits_natBits]
  rw [hlen]
  exact hprod

/-- A finite conditional complexity is attained by a program of exactly that length. -/
lemma exists_min_program (U : Map) (x : BitString) (y : BitString)
    (h_ne_top : condK U x y ≠ ⊤) :
    ∃ p : BitString, p.length = condCVal U x y ∧ produces U p y x := by
  have h_eq : condK U x y = (condCVal U x y : ℕ∞) := (ENat.coe_toNat h_ne_top).symm
  have h_le : condK U x y ≤ (condCVal U x y : ℕ∞) := by rw [h_eq]
  rw [condK_le_iff] at h_le
  obtain ⟨p, hlen, hprod⟩ := h_le
  have hlen_eq : p.length = condCVal U x y := by
    by_contra hneq
    have hlt : p.length < condCVal U x y := Nat.lt_of_le_of_ne hlen hneq
    have h_contra : condK U x y ≤ (p.length : ℕ∞) := by
      rw [condK_le_iff]
      exact ⟨p, le_rfl, hprod⟩
    rw [h_eq] at h_contra
    have : condCVal U x y ≤ p.length := by exact_mod_cast h_contra
    omega
  exact ⟨p, hlen_eq, hprod⟩

/-- The unconditional complexity exceeds the length-conditional one by at most
`2 log d + O(1)`, where `d` is the length-conditional deficiency of `x`. -/
lemma deficiency_bound_helper (U : Map) (c_D : ℕ)
    (hc_D : ∀ x y, condK U x y ≤ condK (deficiencyMap U) x y + (c_D : ℕ∞))
    (x : BitString) (Dc : ℕ) (p : BitString)
    (hp_len : p.length = condCVal U x (Nat.bits x.length))
    (hp_prod : produces U p (Nat.bits x.length) x)
    (hlen_p : p.length + Dc = x.length)
    (h_plain_top : plainK U x ≠ ⊤) :
    cVal U x ≤ condCVal U x (Nat.bits x.length) + 2 * Nat.log 2 Dc + 3 + c_D := by
  have h_def_prod := produces_deficiencyMap U x p Dc hp_prod hlen_p
  have h_def_le : condK (deficiencyMap U) x [] ≤ ((pairCode (Nat.bits Dc) p).length : ℕ∞) := by
    rw [condK_le_iff]
    exact ⟨pairCode (Nat.bits Dc) p, le_rfl, h_def_prod⟩
  have h_opt := hc_D x []
  have h_plain_le : plainK U x ≤ ((pairCode (Nat.bits Dc) p).length + c_D : ℕ∞) := by
    calc plainK U x ≤ condK (deficiencyMap U) x [] + (c_D : ℕ∞) := h_opt
    _ ≤ ((pairCode (Nat.bits Dc) p).length : ℕ∞) + (c_D : ℕ∞) := by gcongr
  have h_cval_eq : plainK U x = (cVal U x : ℕ∞) := (ENat.coe_toNat h_plain_top).symm
  rw [h_cval_eq] at h_plain_le
  have h_cval_le_nat : cVal U x ≤ (pairCode (Nat.bits Dc) p).length + c_D := by
    exact_mod_cast h_plain_le
  have h_bits_len := length_natBits_le_log Dc
  have h_pair_len : (pairCode (Nat.bits Dc) p).length =
      (Nat.bits Dc).length + 1 + (Nat.bits Dc).length + p.length :=
    length_pairCode (Nat.bits Dc) p
  omega

/-- **Exercise 55.** The two deficiencies differ by at most a logarithmic term. -/
theorem deficiency_comparison_le_log (U : Map) (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ x : BitString,
      condDeficiency U x - 2 * (Nat.log 2 (condDeficiency U x).toNat : ℤ) - c
          ≤ plainDeficiency U x ∧
        plainDeficiency U x ≤ condDeficiency U x + c := by
  obtain ⟨c_cond, hc_cond⟩ := condK_le_plainK U hU
  obtain ⟨c_len, hc_len⟩ := plainK_le_length U hU
  have hD_rec : isDecompressor (deficiencyMap U) := deficiencyMap_partrec hU.1
  obtain ⟨c_D, hc_D⟩ := hU.2 (deficiencyMap U) hD_rec
  refine ⟨c_cond + c_len + c_D + 3, fun x => ?_⟩
  unfold plainDeficiency condDeficiency
  have h_plain_top : plainK U x ≠ ⊤ := by
    intro h_top
    have h_le := hc_len x
    rw [h_top] at h_le
    have h_top_le : (⊤ : ℕ∞) ≤ ((x.length + c_len : ℕ) : ℕ∞) := h_le
    exact WithTop.coe_ne_top (top_le_iff.mp h_top_le)
  have h_cond_top : condK U x (Nat.bits x.length) ≠ ⊤ := by
    intro h_top
    have h_le := hc_cond x (Nat.bits x.length)
    rw [h_top] at h_le
    have h_fin : plainK U x + (c_cond : ℕ∞) ≠ ⊤ := by
      rw [WithTop.add_ne_top]
      exact ⟨h_plain_top, ENat.coe_ne_top _⟩
    exact h_fin (top_le_iff.mp h_le)
  have h_cval_eq : plainK U x = (cVal U x : ℕ∞) := (ENat.coe_toNat h_plain_top).symm
  have h_condcval_eq : condK U x (Nat.bits x.length) =
      (condCVal U x (Nat.bits x.length) : ℕ∞) :=
    (ENat.coe_toNat h_cond_top).symm
  constructor
  · by_cases h_dc_pos : 0 < (x.length : ℤ) - (condCVal U x (Nat.bits x.length) : ℤ)
    · set Dc := ((x.length : ℤ) - (condCVal U x (Nat.bits x.length) : ℤ)).toNat with hDc_def
      have hDc_eq : (x.length : ℤ) - (condCVal U x (Nat.bits x.length) : ℤ) = (Dc : ℤ) := by
        exact (Int.toNat_of_nonneg (by omega)).symm
      rw [hDc_eq]
      have hlen_sum : condCVal U x (Nat.bits x.length) + Dc = x.length := by omega
      obtain ⟨p, hp_len, hp_prod⟩ := exists_min_program U x (Nat.bits x.length) h_cond_top
      have hlen_p : p.length + Dc = x.length := by rw [hp_len, hlen_sum]
      have h_cval_bound := deficiency_bound_helper U c_D hc_D x Dc p hp_len hp_prod
        hlen_p h_plain_top
      have h_cval_cast : (cVal U x : ℤ) ≤
          (condCVal U x (Nat.bits x.length) : ℤ) + 2 * (Nat.log 2 Dc : ℤ) + 3 + c_D := by
        exact_mod_cast h_cval_bound
      push_cast
      linarith
    · have h_dc_nonpos : (x.length : ℤ) - (condCVal U x (Nat.bits x.length) : ℤ) ≤ 0 :=
        by omega
      have h_toNat_zero :
          ((x.length : ℤ) - (condCVal U x (Nat.bits x.length) : ℤ)).toNat = 0 :=
        Int.toNat_eq_zero.mpr h_dc_nonpos
      rw [h_toNat_zero]
      have h_log_zero : Nat.log 2 0 = 0 := rfl
      rw [h_log_zero]
      simp only [CharP.cast_eq_zero, mul_zero, sub_zero]
      have h_plain_len := hc_len x
      rw [h_cval_eq] at h_plain_len
      have h_cval_le_len : cVal U x ≤ x.length + c_len := by exact_mod_cast h_plain_len
      have h_cval_cast : (cVal U x : ℤ) ≤ (x.length : ℤ) + (c_len : ℤ) := by
        exact_mod_cast h_cval_le_len
      push_cast
      linarith
  · have h_cond_le := hc_cond x (Nat.bits x.length)
    rw [h_condcval_eq, h_cval_eq] at h_cond_le
    have h_nat_le : condCVal U x (Nat.bits x.length) ≤ cVal U x + c_cond := by
      exact_mod_cast h_cond_le
    have h_cond_cast : (condCVal U x (Nat.bits x.length) : ℤ) ≤ (cVal U x : ℤ) + (c_cond : ℤ) := by
      exact_mod_cast h_nat_le
    push_cast
    linarith

-- `exercise56_deficiency_chain` (ch02-exercise-56) is archived; see `docs/ARCHIVED_TARGETS.md`.

-- `exercise57_turing_complete` (ch02-exercise-57) is archived; see `docs/ARCHIVED_TARGETS.md`.

/-! ### Exercises 58–65: information -/

/-- **Exercise 58.** Deterministic conservation of information:
`I(f x : y) ≤ I(x : y) + O(1)`. -/
theorem deterministic_information_conservation (U : Map) (hU : isOptimalConditional U)
    (f : BitString →. BitString) (hf : Partrec f) :
    ∃ c : ℕ, ∀ x y v : BitString, v ∈ f x → info U v y ≤ info U x y + (c : ℤ) := by
  have condKNeTopAux : ∀ (U : Map), isOptimalConditional U → ∀ (x y : BitString),
      condK U x y ≠ ⊤ := by
    intro U hU x y h
    obtain ⟨c, hc⟩ := condK_le_plainK U hU
    have h_le := hc x y
    have h_plain : plainK U x ≠ ⊤ := by
      obtain ⟨c', hc'⟩ := plainK_le_length U hU
      have h_le' := hc' x
      intro h'
      rw [h'] at h_le'
      cases h_le'
    have h_top_le : (⊤ : ℕ∞) ≤ plainK U x + (c : ℕ∞) := by
      calc (⊤ : ℕ∞) = condK U x y := h.symm
      _             ≤ plainK U x + (c : ℕ∞) := h_le
    have hc_ne : (c : ℕ∞) ≠ ⊤ := WithTop.coe_ne_top
    have hsum : plainK U x + (c : ℕ∞) ≠ ⊤ := WithTop.add_ne_top.mpr ⟨h_plain, hc_ne⟩
    exact hsum (top_unique h_top_le)
  let D : Map := fun (p, x) => (f x).bind (fun v => U (p, v))
  have hD : isDecompressor D := by
    have hf1 : Partrec (fun (px : BitString × BitString) => f px.2) :=
      hf.comp Computable.snd
    have hg1 : Partrec (fun (pxv : (BitString × BitString) × BitString) => U (pxv.1.1, pxv.2)) :=
      hU.1.comp (Computable.pair (Computable.fst.comp Computable.fst) Computable.snd)
    exact Partrec.bind hf1 hg1
  obtain ⟨c, hc⟩ := hU.2 D hD
  use c
  intro x y v hv
  dsimp [info]
  have h_le : condK U y x ≤ condK U y v + (c : ℕ∞) := by
    calc
      condK U y x ≤ condK D y x + (c : ℕ∞) := hc y x
      _ ≤ condK U y v + (c : ℕ∞) := by
        gcongr
        apply sInf_le_sInf
        rintro n ⟨p, hp, rfl⟩
        refine ⟨p, ?_, rfl⟩
        dsimp [D]
        exact Part.mem_bind hv hp
  have hx : condK U y x = (condCVal U y x : ℕ∞) :=
    (ENat.coe_toNat (condKNeTopAux U hU y x)).symm
  have hv_top : condK U y v = (condCVal U y v : ℕ∞) :=
    (ENat.coe_toNat (condKNeTopAux U hU y v)).symm
  rw [hx, hv_top] at h_le
  norm_cast at h_le
  omega

-- The refutation of the `O(C n)`-only reading of Problem 59, together with the
-- decompressor family it uses, lives in `KolmogorovCounterexamples/Problem59CnOnlyExponent.lean`.

end Kolmogorov
