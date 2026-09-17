import KolmogorovMathlib.AlgorithmicProbability.PairProjection
import KolmogorovMathlib.AlgorithmicRandomness.NatLogPrimrec
import KolmogorovMathlib.AlgorithmicStatistics.NormalizedCodedFiniteDistribution
import KolmogorovMathlib.AlgorithmicStatistics.Selector
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.AddNoise
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.ModelsToSets2
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.SlackArith
import KolmogorovMathlib.CommonInformation.ConditionalCounting
import KolmogorovMathlib.CommonInformation.ConditionalIndependence
import KolmogorovMathlib.CommonInformation.Counting
import KolmogorovMathlib.Complexity.Properties
import KolmogorovMathlib.Encoding.Tuples
import KolmogorovMathlib.Foundation.EffectiveNotions
import KolmogorovMathlib.Foundation.EnumerationComplexity
import KolmogorovMathlib.Foundation.NatEncoding
import KolmogorovMathlib.Interface.Dovetailing
import KolmogorovMathlib.MonotoneComplexity.APrioriComplexity
import KolmogorovMathlib.Prefix.ConditionalSymmetry
import KolmogorovMathlib.Prefix.Machine
import KolmogorovMathlib.Prefix.Properties
import KolmogorovMathlib.Prefix.Symmetry
import KolmogorovMathlib.Prefix.TwoStage
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.ENNReal.Inv

namespace Kolmogorov

open Nat.Partrec (Code)

/-! ### Notation for pairs, triples and information -/

/-- `C(x, y)`: plain complexity of the pair. -/
noncomputable def cPair (U : Map) (x y : BitString) : ℕ∞ := plainK U (pairCode x y)

/-- `C(x, y, z)`: plain complexity of the triple. -/
noncomputable def cTriple (U : Map) (x y z : BitString) : ℕ∞ := plainK U (listCode [x, y, z])

/-- `C(x, y | z)`: conditional complexity of a pair. -/
noncomputable def cCondPair (U : Map) (x y z : BitString) : ℕ∞ := condK U (pairCode x y) z

/-- Natural-number value of `C(x, y)`. -/
noncomputable def cPairVal (U : Map) (x y : BitString) : ℕ := (cPair U x y).toNat

/-- Natural-number value of `C(x, y, z)`. -/
noncomputable def cTripleVal (U : Map) (x y z : BitString) : ℕ := (cTriple U x y z).toNat

/-- The mutual information `I(x : y) = C(y) - C(y | x)`. -/
noncomputable def info (U : Map) (x y : BitString) : ℤ :=
  (cVal U y : ℤ) - (condCVal U y x : ℤ)

/-- The conditional mutual information `I(x : y | z) = C(y | z) - C(y | x, z)`. -/
noncomputable def condInfo (U : Map) (x y z : BitString) : ℤ :=
  (condCVal U y z : ℤ) - (condCVal U y (pairCode x z) : ℤ)

/-- The `n`-bit prefix of an infinite binary sequence. -/
def seqPrefix (w : ℕ → Bool) (n : ℕ) : BitString := (List.range n).map w

/-! ### Theorem 16: iterated self-delimiting bounds for pairs -/

/-- A natural number has at most `log₂ n + 1` binary digits. -/
lemma length_natBits_le_log (n : ℕ) : (Nat.bits n).length ≤ Nat.log 2 n + 1 := by
  rw [Nat.size_eq_bits_len]
  by_cases hn : n = 0
  · subst hn
    simp
  · apply Nat.size_le.mpr
    exact Nat.lt_pow_succ_log_self (by decide) n

/-- For an optimal conditional decompressor every string has an unconditional program of length
at most its complexity value `cVal U x`. -/
lemma exists_program_le_cVal (U : Map) (hU : isOptimalConditional U) (x : BitString) :
    ∃ p : BitString, produces U p [] x ∧ p.length ≤ cVal U x := by
  obtain ⟨c, hc⟩ := plainK_le_length U hU
  have h_ne : plainK U x ≠ ⊤ := by
    apply ne_top_of_le_ne_top (ENat.natCast_ne_top (x.length + c))
    calc plainK U x ≤ (x.length : ℕ∞) + (c : ℕ∞) := hc x
    _ = ((x.length + c : ℕ) : ℕ∞) := by push_cast; rfl
  have h_plain : plainK U x ≤ (cVal U x : ℕ∞) := by
    dsimp [cVal]
    rw [ENat.natCast_toNat h_ne]
  obtain ⟨p, hp_len, hp_prod⟩ := (condK_le_iff U x [] (cVal U x)).mp h_plain
  exact ⟨p, hp_prod, hp_len⟩

/-- First field of the one-layer self-delimiting layout: the prefix of the body whose length is
the number encoded in the first field of `w`. -/
def t16_first_S1 (w : BitString) : BitString :=
  (decodeSecond w).take (decodeBits (decodeFirst w))

/-- Second field of the one-layer self-delimiting layout: the rest of the body of `w`. -/
def t16_first_S2 (w : BitString) : BitString :=
  (decodeSecond w).drop (decodeBits (decodeFirst w))

private lemma t16_first_S1_comp : Computable t16_first_S1 := by
  have hA : Computable decodeFirst := decodeFirst_computable
  have hlen_p : Computable (fun w => decodeBits (decodeFirst w)) :=
    decodeBits_computable.comp hA
  have hrest : Computable decodeSecond := decodeSecond_computable
  exact Primrec.list_take.to_comp.comp hlen_p hrest

private lemma t16_first_S2_comp : Computable t16_first_S2 := by
  have hA : Computable decodeFirst := decodeFirst_computable
  have hlen_p : Computable (fun w => decodeBits (decodeFirst w)) :=
    decodeBits_computable.comp hA
  have hrest : Computable decodeSecond := decodeSecond_computable
  exact Primrec.list_drop.to_comp.comp hlen_p hrest

/-- The pair formed by the second component of the first argument block and the last argument;
used to state computability of the pairing step. -/
def t16_pair2 (q_x_y : ((BitString × BitString) × BitString) × BitString) : BitString × BitString :=
  (q_x_y.1.2, q_x_y.2)

private lemma t16_pair2_comp : Computable t16_pair2 :=
  (Computable.snd.comp Computable.fst).pair Computable.snd

/-- The code of the pair formed by the second component of the first argument block and the
last argument. -/
def t16_map2 (q_x_y : ((BitString × BitString) × BitString) × BitString) : BitString :=
  pairCode q_x_y.1.2 q_x_y.2

private lemma t16_map2_comp : Computable t16_map2 := by
  have h_eq : t16_map2 = (fun p => pairCode p.1 p.2) ∘ t16_pair2 := rfl
  rw [h_eq]
  exact pairCode_computable.comp t16_pair2_comp

/-- Decompressor for the pair bound whose program is a self-delimiting program for `x` followed
by a program for `y`; it runs `U` on both fields and pairs the outputs. -/
noncomputable def pairSelfDelimitingFirst (U : Map) : Map := fun pr =>
  (U (t16_first_S1 pr.1, [])).bind (fun x => (U (t16_first_S2 pr.1, [])).map (pairCode x))

private lemma pairSelfDelimitingFirst_isDecompressor (U : Map) (hU : isDecompressor U) :
    isDecompressor (pairSelfDelimitingFirst U) := by
  dsimp [isDecompressor, pairSelfDelimitingFirst]
  have hS1 : Computable (fun pr : BitString × BitString => t16_first_S1 pr.1) :=
    t16_first_S1_comp.comp Computable.fst
  have hU1 : Partrec (fun pr : BitString × BitString => U (t16_first_S1 pr.1, [])) :=
    Partrec.comp hU (hS1.pair (Computable.const []))
  have hU2 : Partrec (fun q_x : (BitString × BitString) × BitString =>
      (U (t16_first_S2 q_x.1.1, [])).map (pairCode q_x.2)) := by
    have hU2_inner : Partrec (fun q_x : (BitString × BitString) × BitString =>
        U (t16_first_S2 q_x.1.1, [])) :=
      Partrec.comp hU (((t16_first_S2_comp.comp
        (Computable.fst.comp Computable.fst)).pair (Computable.const [])))
    exact Partrec.map hU2_inner t16_map2_comp
  exact Partrec.bind hU1 hU2

/-- **Theorem 16, first inequality.**
`C(x, y) ≤ C(x) + 2 log C(x) + C(y) + O(1)`. -/
theorem plainK_pair_le_add_two_log (U : Map) (hU : isOptimalConditional U) :
    ∃ k : ℕ, ∀ x y : BitString,
      cPair U x y ≤ plainK U x + plainK U y + ((2 * Nat.log 2 (cVal U x) + k : ℕ) : ℕ∞) := by
  obtain ⟨c_opt, hc_opt⟩ := hU.2 (pairSelfDelimitingFirst U)
    (pairSelfDelimitingFirst_isDecompressor U hU.1)
  refine ⟨3 + c_opt, fun x y => ?_⟩
  obtain ⟨p, hp_prod, hp_len⟩ := exists_program_le_cVal U hU x
  obtain ⟨q, hq_prod, hq_len⟩ := exists_program_le_cVal U hU y
  set A := Nat.bits p.length
  set w := pairCode A p ++ q
  have hw_eq : w = pairCode A (p ++ q) := by
    dsimp [w, pairCode]
    rw [List.append_assoc, List.append_assoc]
  have hS1 : t16_first_S1 w = p := by
    dsimp [t16_first_S1]
    rw [hw_eq, decodeFirst_pairCode, decodeSecond_pairCode, decodeBits_natBits, List.take_left]
  have hS2 : t16_first_S2 w = q := by
    dsimp [t16_first_S2]
    rw [hw_eq, decodeFirst_pairCode, decodeSecond_pairCode, decodeBits_natBits, List.drop_left]
  have hprod : produces (pairSelfDelimitingFirst U) w [] (pairCode x y) := by
    dsimp [produces, pairSelfDelimitingFirst]
    rw [hS1, hS2]
    have hmap : pairCode x y ∈ (U (q, [])).map (pairCode x) := Part.mem_map (pairCode x) hq_prod
    exact Part.mem_bind hp_prod hmap
  have hw_len : w.length = p.length + 2 * A.length + 1 + q.length := by
    dsimp [w]
    rw [List.length_append, length_pairCode]
    omega
  have hA_len : A.length ≤ Nat.log 2 p.length + 1 := length_natBits_le_log p.length
  have hlog_le : Nat.log 2 p.length ≤ Nat.log 2 (cVal U x) := Nat.log_mono_right hp_len
  have hw_bound : w.length ≤ cVal U x + cVal U y + 2 * Nat.log 2 (cVal U x) + 3 := by
    omega
  have hcond_le : condK (pairSelfDelimitingFirst U) (pairCode x y) [] ≤ (w.length : ℕ∞) := by
    rw [condK_le_iff]
    exact ⟨w, le_rfl, hprod⟩
  have hcVal_x : (cVal U x : ℕ∞) = plainK U x := by
    dsimp [cVal]
    obtain ⟨c, hc⟩ := plainK_le_length U hU
    have h_ne : plainK U x ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top (x.length + c))
      (by calc plainK U x ≤ (x.length : ℕ∞) + (c : ℕ∞) := hc x
        _ = ((x.length + c : ℕ) : ℕ∞) := by push_cast; rfl)
    exact ENat.natCast_toNat h_ne
  have hcVal_y : (cVal U y : ℕ∞) = plainK U y := by
    dsimp [cVal]
    obtain ⟨c, hc⟩ := plainK_le_length U hU
    have h_ne : plainK U y ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top (y.length + c))
      (by calc plainK U y ≤ (y.length : ℕ∞) + (c : ℕ∞) := hc y
        _ = ((y.length + c : ℕ) : ℕ∞) := by push_cast; rfl)
    exact ENat.natCast_toNat h_ne
  have h_arith : (w.length : ℕ∞) + (c_opt : ℕ∞) ≤ plainK U x + plainK U y +
      ((2 * Nat.log 2 (cVal U x) + (3 + c_opt) : ℕ) : ℕ∞) := by
    have h1 : w.length + c_opt ≤ cVal U x + cVal U y + 2 * Nat.log 2 (cVal U x) +
        (3 + c_opt) := by omega
    have h2 : ((w.length + c_opt : ℕ) : ℕ∞) ≤ ((cVal U x + cVal U y +
        2 * Nat.log 2 (cVal U x) + (3 + c_opt) : ℕ) : ℕ∞) := Nat.cast_le.mpr h1
    have h3 : ((cVal U x + cVal U y + 2 * Nat.log 2 (cVal U x) + (3 + c_opt) : ℕ) : ℕ∞) =
        plainK U x + plainK U y +
        ((2 * Nat.log 2 (cVal U x) + (3 + c_opt) : ℕ) : ℕ∞) := by
      push_cast
      rw [hcVal_x, hcVal_y]
      ac_rfl
    have h4 : (w.length : ℕ∞) + (c_opt : ℕ∞) = ((w.length + c_opt : ℕ) : ℕ∞) := by
      push_cast; rfl
    rw [h4, ← h3]
    exact h2
  calc cPair U x y = plainK U (pairCode x y) := rfl
    _ = condK U (pairCode x y) [] := rfl
    _ ≤ condK (pairSelfDelimitingFirst U) (pairCode x y) [] + (c_opt : ℕ∞) :=
      hc_opt (pairCode x y) []
    _ ≤ (w.length : ℕ∞) + (c_opt : ℕ∞) := by gcongr
    _ ≤ plainK U x + plainK U y + ((2 * Nat.log 2 (cVal U x) + (3 + c_opt) : ℕ) : ℕ∞) := h_arith

/-- Length field of the two-layer self-delimiting layout: the first field of `w`. -/
def t16_second_A (w : BitString) : BitString := decodeFirst w
/-- The number encoded by the length field of the two-layer layout. -/
def t16_second_lenB (w : BitString) : ℕ := decodeBits (t16_second_A w)
/-- The body of the two-layer layout, that is everything after the first field. -/
def t16_second_rest1 (w : BitString) : BitString := decodeSecond w
/-- The second length field of the two-layer layout, read off the body. -/
def t16_second_B (w : BitString) : BitString := (t16_second_rest1 w).take (t16_second_lenB w)
/-- The body of the two-layer layout after the second length field. -/
def t16_second_rest2 (w : BitString) : BitString := (t16_second_rest1 w).drop (t16_second_lenB w)
/-- The length of the first program in the two-layer layout, encoded by its second length field. -/
def t16_second_lenp (w : BitString) : ℕ := decodeBits (t16_second_B w)
/-- The first program of the two-layer layout. -/
def t16_second_S1 (w : BitString) : BitString := (t16_second_rest2 w).take (t16_second_lenp w)
/-- The second program of the two-layer layout. -/
def t16_second_S2 (w : BitString) : BitString := (t16_second_rest2 w).drop (t16_second_lenp w)

private lemma t16_second_S1_comp : Computable t16_second_S1 := by
  have hA : Computable t16_second_A := decodeFirst_computable
  have hlenB : Computable t16_second_lenB := decodeBits_computable.comp hA
  have hrest1 : Computable t16_second_rest1 := decodeSecond_computable
  have hB : Computable t16_second_B := Primrec.list_take.to_comp.comp hlenB hrest1
  have hrest2 : Computable t16_second_rest2 := Primrec.list_drop.to_comp.comp hlenB hrest1
  have hlenp : Computable t16_second_lenp := decodeBits_computable.comp hB
  exact Primrec.list_take.to_comp.comp hlenp hrest2

private lemma t16_second_S2_comp : Computable t16_second_S2 := by
  have hA : Computable t16_second_A := decodeFirst_computable
  have hlenB : Computable t16_second_lenB := decodeBits_computable.comp hA
  have hrest1 : Computable t16_second_rest1 := decodeSecond_computable
  have hB : Computable t16_second_B := Primrec.list_take.to_comp.comp hlenB hrest1
  have hrest2 : Computable t16_second_rest2 := Primrec.list_drop.to_comp.comp hlenB hrest1
  have hlenp : Computable t16_second_lenp := decodeBits_computable.comp hB
  exact Primrec.list_drop.to_comp.comp hlenp hrest2

/-- Decompressor for the pair bound in which the length of the first program is itself given
self-delimitingly, at a cost of `log C(x) + 2 log log C(x) + O(1)` extra bits. -/
noncomputable def pairSelfDelimitingSecond (U : Map) : Map := fun pr =>
  (U (t16_second_S1 pr.1, [])).bind (fun x => (U (t16_second_S2 pr.1, [])).map (pairCode x))

private lemma pairSelfDelimitingSecond_isDecompressor (U : Map) (hU : isDecompressor U) :
    isDecompressor (pairSelfDelimitingSecond U) := by
  dsimp [isDecompressor, pairSelfDelimitingSecond]
  have hS1 : Computable (fun pr : BitString × BitString => t16_second_S1 pr.1) :=
    t16_second_S1_comp.comp Computable.fst
  have hU1 : Partrec (fun pr : BitString × BitString => U (t16_second_S1 pr.1, [])) :=
    Partrec.comp hU (hS1.pair (Computable.const []))
  have hU2 : Partrec (fun q_x : (BitString × BitString) × BitString =>
      (U (t16_second_S2 q_x.1.1, [])).map (pairCode q_x.2)) := by
    have hU2_inner : Partrec (fun q_x : (BitString × BitString) × BitString =>
        U (t16_second_S2 q_x.1.1, [])) :=
      Partrec.comp hU (((t16_second_S2_comp.comp (Computable.fst.comp Computable.fst)).pair
        (Computable.const [])))
    exact Partrec.map hU2_inner t16_map2_comp
  exact Partrec.bind hU1 hU2

/-- **Theorem 16, second inequality.**
`C(x, y) ≤ C(x) + log C(x) + 2 log log C(x) + C(y) + O(1)`. -/
theorem plainK_pair_le_add_log_add_two_logLog (U : Map) (hU : isOptimalConditional U) :
    ∃ k : ℕ, ∀ x y : BitString,
      cPair U x y ≤ plainK U x + plainK U y +
        ((Nat.log 2 (cVal U x) + 2 * Nat.log 2 (Nat.log 2 (cVal U x)) + k : ℕ) : ℕ∞) := by
  obtain ⟨c_opt, hc_opt⟩ := hU.2 (pairSelfDelimitingSecond U)
    (pairSelfDelimitingSecond_isDecompressor U hU.1)
  refine ⟨6 + c_opt, fun x y => ?_⟩
  obtain ⟨p, hp_prod, hp_len⟩ := exists_program_le_cVal U hU x
  obtain ⟨q, hq_prod, hq_len⟩ := exists_program_le_cVal U hU y
  set B := Nat.bits p.length
  set A := Nat.bits B.length
  set w := pairCode A B ++ p ++ q
  have hw_eq : w = pairCode A (B ++ (p ++ q)) := by
    dsimp [w, pairCode]
    rw [List.append_assoc, List.append_assoc, List.append_assoc]
  have hA_eval : t16_second_A w = A := by
    dsimp [t16_second_A]
    rw [hw_eq, decodeFirst_pairCode]
  have hlenB_eval : t16_second_lenB w = B.length := by
    dsimp [t16_second_lenB]
    rw [hA_eval, decodeBits_natBits]
  have hrest1_eval : t16_second_rest1 w = B ++ (p ++ q) := by
    dsimp [t16_second_rest1]
    rw [hw_eq, decodeSecond_pairCode]
  have hB_eval : t16_second_B w = B := by
    dsimp [t16_second_B]
    rw [hrest1_eval, hlenB_eval, List.take_left]
  have hrest2_eval : t16_second_rest2 w = p ++ q := by
    dsimp [t16_second_rest2]
    rw [hrest1_eval, hlenB_eval, List.drop_left]
  have hlenp_eval : t16_second_lenp w = p.length := by
    dsimp [t16_second_lenp]
    rw [hB_eval, decodeBits_natBits]
  have hS1 : t16_second_S1 w = p := by
    dsimp [t16_second_S1]
    rw [hrest2_eval, hlenp_eval, List.take_left]
  have hS2 : t16_second_S2 w = q := by
    dsimp [t16_second_S2]
    rw [hrest2_eval, hlenp_eval, List.drop_left]
  have hprod : produces (pairSelfDelimitingSecond U) w [] (pairCode x y) := by
    dsimp [produces, pairSelfDelimitingSecond]
    rw [hS1, hS2]
    have hmap : pairCode x y ∈ (U (q, [])).map (pairCode x) := Part.mem_map (pairCode x) hq_prod
    exact Part.mem_bind hp_prod hmap
  have hw_len : w.length = p.length + q.length + 2 * A.length + 1 + B.length := by
    dsimp [w]
    rw [List.length_append, List.length_append, length_pairCode]
    omega
  have hB_len : B.length ≤ Nat.log 2 p.length + 1 := length_natBits_le_log p.length
  have hA_len : A.length ≤ Nat.log 2 B.length + 1 := length_natBits_le_log B.length
  have hlogB_le : Nat.log 2 B.length ≤ Nat.log 2 (Nat.log 2 p.length) + 1 := by
    calc Nat.log 2 B.length ≤ Nat.log 2 (Nat.log 2 p.length + 1) := Nat.log_mono_right hB_len
      _ ≤ Nat.log 2 (Nat.log 2 p.length) + 1 := log_succ_le (Nat.log 2 p.length)
  have hlogp_le : Nat.log 2 p.length ≤ Nat.log 2 (cVal U x) := Nat.log_mono_right hp_len
  have hloglogp_le : Nat.log 2 (Nat.log 2 p.length) ≤ Nat.log 2 (Nat.log 2 (cVal U x)) :=
    Nat.log_mono_right hlogp_le
  have hw_bound : w.length ≤ cVal U x + cVal U y + Nat.log 2 (cVal U x) +
      2 * Nat.log 2 (Nat.log 2 (cVal U x)) + 6 := by
    omega
  have hcond_le : condK (pairSelfDelimitingSecond U) (pairCode x y) [] ≤
      (w.length : ℕ∞) := by
    rw [condK_le_iff]
    exact ⟨w, le_rfl, hprod⟩
  have hcVal_x : (cVal U x : ℕ∞) = plainK U x := by
    dsimp [cVal]
    obtain ⟨c, hc⟩ := plainK_le_length U hU
    have h_ne : plainK U x ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top (x.length + c))
      (by calc plainK U x ≤ (x.length : ℕ∞) + (c : ℕ∞) := hc x
        _ = ((x.length + c : ℕ) : ℕ∞) := by push_cast; rfl)
    exact ENat.natCast_toNat h_ne
  have hcVal_y : (cVal U y : ℕ∞) = plainK U y := by
    dsimp [cVal]
    obtain ⟨c, hc⟩ := plainK_le_length U hU
    have h_ne : plainK U y ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top (y.length + c))
      (by calc plainK U y ≤ (y.length : ℕ∞) + (c : ℕ∞) := hc y
        _ = ((y.length + c : ℕ) : ℕ∞) := by push_cast; rfl)
    exact ENat.natCast_toNat h_ne
  have h_arith : (w.length : ℕ∞) + (c_opt : ℕ∞) ≤ plainK U x + plainK U y +
      ((Nat.log 2 (cVal U x) + 2 * Nat.log 2 (Nat.log 2 (cVal U x)) +
        (6 + c_opt) : ℕ) : ℕ∞) := by
    have h1 : w.length + c_opt ≤ cVal U x + cVal U y + Nat.log 2 (cVal U x) +
        2 * Nat.log 2 (Nat.log 2 (cVal U x)) + (6 + c_opt) := by omega
    have h2 : ((w.length + c_opt : ℕ) : ℕ∞) ≤ ((cVal U x + cVal U y +
        Nat.log 2 (cVal U x) + 2 * Nat.log 2 (Nat.log 2 (cVal U x)) +
        (6 + c_opt) : ℕ) : ℕ∞) := Nat.cast_le.mpr h1
    have h3 : ((cVal U x + cVal U y + Nat.log 2 (cVal U x) +
        2 * Nat.log 2 (Nat.log 2 (cVal U x)) + (6 + c_opt) : ℕ) : ℕ∞) =
        plainK U x + plainK U y + ((Nat.log 2 (cVal U x) +
        2 * Nat.log 2 (Nat.log 2 (cVal U x)) + (6 + c_opt) : ℕ) : ℕ∞) := by
      push_cast
      rw [hcVal_x, hcVal_y]
      ac_rfl
    have h4 : (w.length : ℕ∞) + (c_opt : ℕ∞) = ((w.length + c_opt : ℕ) : ℕ∞) := by
      push_cast; rfl
    rw [h4, ← h3]
    exact h2
  calc cPair U x y = plainK U (pairCode x y) := rfl
    _ = condK U (pairCode x y) [] := rfl
    _ ≤ condK (pairSelfDelimitingSecond U) (pairCode x y) [] + (c_opt : ℕ∞) :=
      hc_opt (pairCode x y) []
    _ ≤ (w.length : ℕ∞) + (c_opt : ℕ∞) := by gcongr
    _ ≤ plainK U x + plainK U y + ((Nat.log 2 (cVal U x) +
        2 * Nat.log 2 (Nat.log 2 (cVal U x)) + (6 + c_opt) : ℕ) : ℕ∞) := h_arith

/-- Length field of the three-layer self-delimiting layout: the first field of `w`. -/
def t16_third_A (w : BitString) : BitString := decodeFirst w
/-- The number encoded by the length field of the three-layer layout. -/
def t16_third_lenB (w : BitString) : ℕ := decodeBits (t16_third_A w)
/-- The body of the three-layer layout, that is everything after the first field. -/
def t16_third_rest1 (w : BitString) : BitString := decodeSecond w
/-- The second length field of the three-layer layout, read off the body. -/
def t16_third_B (w : BitString) : BitString := (t16_third_rest1 w).take (t16_third_lenB w)
/-- The body of the three-layer layout after the second length field. -/
def t16_third_rest2 (w : BitString) : BitString := (t16_third_rest1 w).drop (t16_third_lenB w)
/-- The length of the third field of the three-layer layout. -/
def t16_third_lenC (w : BitString) : ℕ := decodeBits (t16_third_B w)
/-- The third length field of the three-layer layout. -/
def t16_third_C (w : BitString) : BitString := (t16_third_rest2 w).take (t16_third_lenC w)
/-- The body of the three-layer layout after all three length fields. -/
def t16_third_rest3 (w : BitString) : BitString := (t16_third_rest2 w).drop (t16_third_lenC w)
/-- The length of the first program in the three-layer layout. -/
def t16_third_lenp (w : BitString) : ℕ := decodeBits (t16_third_C w)
/-- The first program of the three-layer layout. -/
def t16_third_S1 (w : BitString) : BitString := (t16_third_rest3 w).take (t16_third_lenp w)
/-- The second program of the three-layer layout. -/
def t16_third_S2 (w : BitString) : BitString := (t16_third_rest3 w).drop (t16_third_lenp w)

private lemma t16_third_S1_comp : Computable t16_third_S1 := by
  have hA : Computable t16_third_A := decodeFirst_computable
  have hlenB : Computable t16_third_lenB := decodeBits_computable.comp hA
  have hrest1 : Computable t16_third_rest1 := decodeSecond_computable
  have hB : Computable t16_third_B := Primrec.list_take.to_comp.comp hlenB hrest1
  have hrest2 : Computable t16_third_rest2 := Primrec.list_drop.to_comp.comp hlenB hrest1
  have hlenC : Computable t16_third_lenC := decodeBits_computable.comp hB
  have hC : Computable t16_third_C := Primrec.list_take.to_comp.comp hlenC hrest2
  have hrest3 : Computable t16_third_rest3 := Primrec.list_drop.to_comp.comp hlenC hrest2
  have hlenp : Computable t16_third_lenp := decodeBits_computable.comp hC
  exact Primrec.list_take.to_comp.comp hlenp hrest3

private lemma t16_third_S2_comp : Computable t16_third_S2 := by
  have hA : Computable t16_third_A := decodeFirst_computable
  have hlenB : Computable t16_third_lenB := decodeBits_computable.comp hA
  have hrest1 : Computable t16_third_rest1 := decodeSecond_computable
  have hB : Computable t16_third_B := Primrec.list_take.to_comp.comp hlenB hrest1
  have hrest2 : Computable t16_third_rest2 := Primrec.list_drop.to_comp.comp hlenB hrest1
  have hlenC : Computable t16_third_lenC := decodeBits_computable.comp hB
  have hC : Computable t16_third_C := Primrec.list_take.to_comp.comp hlenC hrest2
  have hrest3 : Computable t16_third_rest3 := Primrec.list_drop.to_comp.comp hlenC hrest2
  have hlenp : Computable t16_third_lenp := decodeBits_computable.comp hC
  exact Primrec.list_drop.to_comp.comp hlenp hrest3

/-- Decompressor for the pair bound whose program carries the length of the first program
through three nested layers of self-delimiting length fields. -/
noncomputable def pairSelfDelimitingThird (U : Map) : Map := fun pr =>
  (U (t16_third_S1 pr.1, [])).bind (fun x => (U (t16_third_S2 pr.1, [])).map (pairCode x))

private lemma pairSelfDelimitingThird_isDecompressor (U : Map) (hU : isDecompressor U) :
    isDecompressor (pairSelfDelimitingThird U) := by
  dsimp [isDecompressor, pairSelfDelimitingThird]
  have hS1 : Computable (fun pr : BitString × BitString => t16_third_S1 pr.1) :=
    t16_third_S1_comp.comp Computable.fst
  have hU1 : Partrec (fun pr : BitString × BitString => U (t16_third_S1 pr.1, [])) :=
    Partrec.comp hU (hS1.pair (Computable.const []))
  have hU2 : Partrec (fun q_x : (BitString × BitString) × BitString =>
      (U (t16_third_S2 q_x.1.1, [])).map (pairCode q_x.2)) := by
    have hU2_inner : Partrec (fun q_x : (BitString × BitString) × BitString =>
        U (t16_third_S2 q_x.1.1, [])) :=
      Partrec.comp hU (((t16_third_S2_comp.comp (Computable.fst.comp Computable.fst)).pair
        (Computable.const [])))
    exact Partrec.map hU2_inner t16_map2_comp
  exact Partrec.bind hU1 hU2

/-- **Theorem 16, third inequality.**
`C(x, y) ≤ C(x) + log C(x) + log log C(x) + 2 log log log C(x) + C(y) + O(1)`. -/
theorem plainK_pair_le_add_log_add_logLog_add_two_logLogLog (U : Map)
    (hU : isOptimalConditional U) :
    ∃ k : ℕ, ∀ x y : BitString,
      cPair U x y ≤ plainK U x + plainK U y +
        ((Nat.log 2 (cVal U x) + Nat.log 2 (Nat.log 2 (cVal U x)) +
          2 * Nat.log 2 (Nat.log 2 (Nat.log 2 (cVal U x))) + k : ℕ) : ℕ∞) := by
  obtain ⟨c_opt, hc_opt⟩ := hU.2 (pairSelfDelimitingThird U)
    (pairSelfDelimitingThird_isDecompressor U hU.1)
  refine ⟨10 + c_opt, fun x y => ?_⟩
  obtain ⟨p, hp_prod, hp_len⟩ := exists_program_le_cVal U hU x
  obtain ⟨q, hq_prod, hq_len⟩ := exists_program_le_cVal U hU y
  set C := Nat.bits p.length
  set B := Nat.bits C.length
  set A := Nat.bits B.length
  set w := pairCode A B ++ C ++ p ++ q
  have hw_eq : w = pairCode A (B ++ (C ++ (p ++ q))) := by
    dsimp [w, pairCode]
    rw [List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc]
  have hA_eval : t16_third_A w = A := by
    dsimp [t16_third_A]
    rw [hw_eq, decodeFirst_pairCode]
  have hlenB_eval : t16_third_lenB w = B.length := by
    dsimp [t16_third_lenB]
    rw [hA_eval, decodeBits_natBits]
  have hrest1_eval : t16_third_rest1 w = B ++ (C ++ (p ++ q)) := by
    dsimp [t16_third_rest1]
    rw [hw_eq, decodeSecond_pairCode]
  have hB_eval : t16_third_B w = B := by
    dsimp [t16_third_B]
    rw [hrest1_eval, hlenB_eval, List.take_left]
  have hrest2_eval : t16_third_rest2 w = C ++ (p ++ q) := by
    dsimp [t16_third_rest2]
    rw [hrest1_eval, hlenB_eval, List.drop_left]
  have hlenC_eval : t16_third_lenC w = C.length := by
    dsimp [t16_third_lenC]
    rw [hB_eval, decodeBits_natBits]
  have hC_eval : t16_third_C w = C := by
    dsimp [t16_third_C]
    rw [hrest2_eval, hlenC_eval, List.take_left]
  have hrest3_eval : t16_third_rest3 w = p ++ q := by
    dsimp [t16_third_rest3]
    rw [hrest2_eval, hlenC_eval, List.drop_left]
  have hlenp_eval : t16_third_lenp w = p.length := by
    dsimp [t16_third_lenp]
    rw [hC_eval, decodeBits_natBits]
  have hS1 : t16_third_S1 w = p := by
    dsimp [t16_third_S1]
    rw [hrest3_eval, hlenp_eval, List.take_left]
  have hS2 : t16_third_S2 w = q := by
    dsimp [t16_third_S2]
    rw [hrest3_eval, hlenp_eval, List.drop_left]
  have hprod : produces (pairSelfDelimitingThird U) w [] (pairCode x y) := by
    dsimp [produces, pairSelfDelimitingThird]
    rw [hS1, hS2]
    have hmap : pairCode x y ∈ (U (q, [])).map (pairCode x) := Part.mem_map (pairCode x) hq_prod
    exact Part.mem_bind hp_prod hmap
  have hw_len : w.length = p.length + q.length + 2 * A.length + 1 + B.length + C.length := by
    dsimp [w]
    rw [List.length_append, List.length_append, List.length_append, length_pairCode]
    omega
  have hC_len : C.length ≤ Nat.log 2 p.length + 1 := length_natBits_le_log p.length
  have hB_len : B.length ≤ Nat.log 2 C.length + 1 := length_natBits_le_log C.length
  have hA_len : A.length ≤ Nat.log 2 B.length + 1 := length_natBits_le_log B.length
  have hlogC_le : Nat.log 2 C.length ≤ Nat.log 2 (Nat.log 2 p.length) + 1 := by
    calc Nat.log 2 C.length ≤ Nat.log 2 (Nat.log 2 p.length + 1) := Nat.log_mono_right hC_len
      _ ≤ Nat.log 2 (Nat.log 2 p.length) + 1 := log_succ_le (Nat.log 2 p.length)
  have hlogB_le : Nat.log 2 B.length ≤ Nat.log 2 (Nat.log 2 (Nat.log 2 p.length)) + 2 := by
    have h1 : B.length ≤ Nat.log 2 (Nat.log 2 p.length) + 2 := by omega
    calc Nat.log 2 B.length ≤ Nat.log 2 (Nat.log 2 (Nat.log 2 p.length) + 2) :=
        Nat.log_mono_right h1
      _ ≤ Nat.log 2 (Nat.log 2 (Nat.log 2 p.length) + 1) + 1 :=
        log_succ_le (Nat.log 2 (Nat.log 2 p.length) + 1)
      _ ≤ Nat.log 2 (Nat.log 2 (Nat.log 2 p.length)) + 1 + 1 := by
        have h_sub := log_succ_le (Nat.log 2 (Nat.log 2 p.length))
        omega
  have hlogp_le : Nat.log 2 p.length ≤ Nat.log 2 (cVal U x) := Nat.log_mono_right hp_len
  have hloglogp_le : Nat.log 2 (Nat.log 2 p.length) ≤ Nat.log 2 (Nat.log 2 (cVal U x)) :=
    Nat.log_mono_right hlogp_le
  have hlog3p_le : Nat.log 2 (Nat.log 2 (Nat.log 2 p.length)) ≤
      Nat.log 2 (Nat.log 2 (Nat.log 2 (cVal U x))) :=
    Nat.log_mono_right hloglogp_le
  have hw_bound : w.length ≤ cVal U x + cVal U y + Nat.log 2 (cVal U x) +
      Nat.log 2 (Nat.log 2 (cVal U x)) +
      2 * Nat.log 2 (Nat.log 2 (Nat.log 2 (cVal U x))) + 10 := by omega
  have hcond_le : condK (pairSelfDelimitingThird U) (pairCode x y) [] ≤ (w.length : ℕ∞) := by
    rw [condK_le_iff]
    exact ⟨w, le_rfl, hprod⟩
  have hcVal_x : (cVal U x : ℕ∞) = plainK U x := by
    dsimp [cVal]
    obtain ⟨c, hc⟩ := plainK_le_length U hU
    have h_ne : plainK U x ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top (x.length + c))
      (by calc plainK U x ≤ (x.length : ℕ∞) + (c : ℕ∞) := hc x
        _ = ((x.length + c : ℕ) : ℕ∞) := by push_cast; rfl)
    exact ENat.natCast_toNat h_ne
  have hcVal_y : (cVal U y : ℕ∞) = plainK U y := by
    dsimp [cVal]
    obtain ⟨c, hc⟩ := plainK_le_length U hU
    have h_ne : plainK U y ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top (y.length + c))
      (by calc plainK U y ≤ (y.length : ℕ∞) + (c : ℕ∞) := hc y
        _ = ((y.length + c : ℕ) : ℕ∞) := by push_cast; rfl)
    exact ENat.natCast_toNat h_ne
  have h_arith : (w.length : ℕ∞) + (c_opt : ℕ∞) ≤ plainK U x + plainK U y +
      ((Nat.log 2 (cVal U x) + Nat.log 2 (Nat.log 2 (cVal U x)) +
        2 * Nat.log 2 (Nat.log 2 (Nat.log 2 (cVal U x))) + (10 + c_opt) : ℕ) : ℕ∞) := by
    have h1 : w.length + c_opt ≤ cVal U x + cVal U y + Nat.log 2 (cVal U x) +
        Nat.log 2 (Nat.log 2 (cVal U x)) + 2 * Nat.log 2 (Nat.log 2 (Nat.log 2 (cVal U x))) +
        (10 + c_opt) := by omega
    have h2 : ((w.length + c_opt : ℕ) : ℕ∞) ≤ ((cVal U x + cVal U y + Nat.log 2 (cVal U x) +
        Nat.log 2 (Nat.log 2 (cVal U x)) + 2 * Nat.log 2 (Nat.log 2 (Nat.log 2 (cVal U x))) +
        (10 + c_opt) : ℕ) : ℕ∞) := Nat.cast_le.mpr h1
    have h3 : ((cVal U x + cVal U y + Nat.log 2 (cVal U x) + Nat.log 2 (Nat.log 2 (cVal U x)) +
        2 * Nat.log 2 (Nat.log 2 (Nat.log 2 (cVal U x))) + (10 + c_opt) : ℕ) : ℕ∞) =
        plainK U x + plainK U y +
        ((Nat.log 2 (cVal U x) +
          Nat.log 2 (Nat.log 2 (cVal U x)) +
          2 * Nat.log 2 (Nat.log 2 (Nat.log 2 (cVal U x))) +
          (10 + c_opt) : ℕ) : ℕ∞) := by
      push_cast
      rw [hcVal_x, hcVal_y]
      ac_rfl
    have h4 : (w.length : ℕ∞) + (c_opt : ℕ∞) = ((w.length + c_opt : ℕ) : ℕ∞) := by push_cast; rfl
    rw [h4, ← h3]
    exact h2
  calc cPair U x y = plainK U (pairCode x y) := rfl
    _ = condK U (pairCode x y) [] := rfl
    _ ≤ condK (pairSelfDelimitingThird U) (pairCode x y) [] + (c_opt : ℕ∞) :=
      hc_opt (pairCode x y) []
    _ ≤ (w.length : ℕ∞) + (c_opt : ℕ∞) := by gcongr
    _ ≤ plainK U x + plainK U y + ((Nat.log 2 (cVal U x) + Nat.log 2 (Nat.log 2 (cVal U x)) +
        2 * Nat.log 2 (Nat.log 2 (Nat.log 2 (cVal U x))) + (10 + c_opt) : ℕ) : ℕ∞) := h_arith

/-! ### Theorem 19: minimality of conditional complexity -/

end Kolmogorov
