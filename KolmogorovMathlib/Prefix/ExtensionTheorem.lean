import KolmogorovMathlib.Interface.ComputableReals
import KolmogorovMathlib.Interface.Dovetailing
import KolmogorovMathlib.Complexity.PairComplexity
import KolmogorovMathlib.Complexity.ConditionalComplexity
import KolmogorovMathlib.Complexity.KolmogorovLevin
import KolmogorovMathlib.Complexity.RandomConditions
import KolmogorovMathlib.Complexity.SelfComplexity
import KolmogorovMathlib.Complexity.InfiniteSequences
import KolmogorovMathlib.Complexity.IncompressibleStrings
import KolmogorovMathlib.Complexity.Information
import KolmogorovMathlib.Complexity.Incompressibility
import KolmogorovMathlib.AlgorithmicProbability.UniversalSemimeasure
import KolmogorovMathlib.AlgorithmicProbability.PairProjection
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitinAllocator
import KolmogorovMathlib.Prefix.ConditionalSymmetry
import KolmogorovMathlib.Prefix.TotalCountingBound
import KolmogorovMathlib.Prefix.KPPairSwap
import KolmogorovMathlib.Prefix.TwoStage
import KolmogorovMathlib.Prefix.CondTwoStage
import KolmogorovMathlib.Foundation.PrimrecExtras
import KolmogorovMathlib.Prefix.Properties
import KolmogorovMathlib.AlgorithmicStatistics.Selector
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Rat.Denumerable
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Partrec
import Mathlib.Computability.Halting
import KolmogorovMathlib.Prefix.PairComplexity

/-!
# Extending a string without decreasing its prefix complexity

Every string has an extension of prescribed length whose prefix complexity is at least
that of the original string (`exists_extension_KP_ge`, `exists_extension_KP_ge_sub`),
proved by the drop-decompressor `extDropMap`.  The second half of the file relates
conditional prefix complexity to plain complexity through the shift decoders
(`condKP_self_plainK_eq`, `plainK_eq_of_condKP_eq_add`).

SUV Theorem 71 and Exercise 113, pp. 147-149.
-/

namespace Kolmogorov
open scoped ENNReal
open Nat.Partrec (Code)
open Kolmogorov.ComputableReals

/-- Averaging bound: in a nonempty finite set `S` there is an element `y` whose value
`g y`, multiplied by the cardinality of `S`, is at most the total `∑ z ∈ S, g z`.
Take for `y` a minimiser of `g` on `S`. -/
lemma exists_le_card_mul_le_sum {α : Type*} (S : Finset α) (hS : S.Nonempty)
    (g : α → ℝ≥0∞) : ∃ y ∈ S, g y * (S.card : ℝ≥0∞) ≤ ∑ z ∈ S, g z := by
  obtain ⟨y, hyS, hyMin⟩ := S.exists_min_image g hS
  refine ⟨y, hyS, ?_⟩
  calc g y * (S.card : ℝ≥0∞) = (S.card : ℝ≥0∞) * g y := mul_comm _ _
    _ = ∑ z ∈ S, g y := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ z ∈ S, g z := Finset.sum_le_sum (fun z hz => hyMin z hz)

/-- The truncation step underlying `extDropMap` is computable: given a program, a
context `c` and an output string `z`, returning `z` with its last `bitsToNat c`
bits removed (and `none` when `z` is too short) is a computable partial function. -/
theorem extDropMap_opt_computable :
    Computable (fun p : (BitString × BitString) × BitString =>
      if decide (bitsToNat p.1.2 ≤ p.2.length) then
        some (p.2.take (p.2.length - bitsToNat p.1.2))
      else
        none) :=
  ((Primrec.cond
    ((PrimrecPred.decide Primrec.nat_le).comp
      ((bitsToNat_primrec.comp (Primrec.snd.comp Primrec.fst)).pair
        (Primrec.list_length.comp Primrec.snd)))
    (Primrec.option_some.comp
      (Primrec.list_take.comp
        Primrec.snd
        (Primrec.nat_sub.comp
          (Primrec.list_length.comp Primrec.snd)
          (bitsToNat_primrec.comp (Primrec.snd.comp Primrec.fst)))))
    (Primrec.const none)).to_comp).of_eq (fun p => by
      dsimp; cases h : decide (bitsToNat p.1.2 ≤ p.2.length) <;> rfl)

/-- The extension-drop machine: run `U` on program (empty context) and drop the last `n`
bits of output, where `n = bitsToNat ctx`. -/
def extDropMap (U : Map) : Map :=
  fun pr => (U (pr.1, [])).bind fun z =>
    if decide (bitsToNat pr.2 ≤ z.length) then
      Part.some (z.take (z.length - bitsToNat pr.2))
    else
      Part.none

/-- `extDropMap U` is again a prefix decompressor whenever `U` is: post-composing with
the truncation keeps the map partial recursive, and the halting set of
`extDropMap U` in any context is the halting set of `U` in the empty context,
which is prefix-free. -/
theorem extDropMap_isPrefixDecompressor (U : Map) (hU : IsPrefixDecompressor U) :
    IsPrefixDecompressor (extDropMap U) := by
  refine ⟨?_, ?_⟩
  · have hf : Partrec (fun pr : BitString × BitString => U (pr.1, [])) :=
      hU.isDecompressor.comp (Computable.fst.pair (Computable.const []))
    have hg : Partrec (fun p : (BitString × BitString) × BitString =>
        Part.ofOption (if decide (bitsToNat p.1.2 ≤ p.2.length) then
          some (p.2.take (p.2.length - bitsToNat p.1.2))
        else
          none)) :=
      Computable.ofOption extDropMap_opt_computable
    have hg' : Partrec₂ (fun (pr : BitString × BitString) (z : BitString) =>
        if decide (bitsToNat pr.2 ≤ z.length) then
          Part.some (z.take (z.length - bitsToNat pr.2))
        else
          Part.none) :=
      Partrec.of_eq hg.to₂ (fun _ => by dsimp; split_ifs <;> rfl)
    exact Partrec.bind hf hg'
  · intro ctx p1 hp1 p2 hp2 hpref
    have h1 : p1 ∈ domainAt U [] := by
      obtain ⟨x1, hx1⟩ := Part.dom_iff_mem.mp hp1
      obtain ⟨z, hz, _⟩ := Part.mem_bind_iff.mp hx1
      exact Part.dom_iff_mem.mpr ⟨z, hz⟩
    have h2 : p2 ∈ domainAt U [] := by
      obtain ⟨x2, hx2⟩ := Part.dom_iff_mem.mp hp2
      obtain ⟨z, hz, _⟩ := Part.mem_bind_iff.mp hx2
      exact Part.dom_iff_mem.mpr ⟨z, hz⟩
    exact hU.isPrefixMachine [] h1 h2 hpref

/-- A finite sum of `ℝ≥0∞`-valued series may be interchanged with the infinite sum:
`∑ y ∈ S, ∑' p, f p y = ∑' p, ∑ y ∈ S, f p y`. -/
lemma finset_sum_tsum_comm {α β : Type*} (S : Finset α) (f : β → α → ℝ≥0∞) :
    (∑ y ∈ S, ∑' p, f p y) = ∑' p, ∑ y ∈ S, f p y := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, ih, ← ENNReal.tsum_add]
    congr 1
    ext p
    exact (Finset.sum_insert ha).symm

/-- Every program of `U` producing an extension `x ++ y` with `y` of length `n` is a
program of `extDropMap U` producing `x` in context `natBits n`; hence the a priori
measure of `x` under `extDropMap U` in that context dominates the total a priori
measure that `U` gives to the extensions of `x` of length `n`. -/
lemma extDropMap_aprioriMeasure_ge (U : Map) (x : BitString) (n : ℕ) :
    (∑ y ∈ stringsOfLength n, aprioriMeasure U (x ++ y) []) ≤
      aprioriMeasure (extDropMap U) x (natBits n) := by
  classical
  dsimp [aprioriMeasure, extDropMap, produces]
  have h_bits : bitsToNat (natBits n) = n := bitsToNat_bits n
  rw [finset_sum_tsum_comm]
  refine ENNReal.tsum_le_tsum fun p => ?_
  by_cases h_ex : ∃ y ∈ stringsOfLength n, (x ++ y) ∈ U (p, [])
  · obtain ⟨y, hyS, hyU⟩ := h_ex
    have hy_len : y.length = n := (mem_stringsOfLength n y).mp hyS
    have h_sum_eq : (∑ y' ∈ stringsOfLength n,
        if (x ++ y') ∈ U (p, []) then progWeight p else 0) = progWeight p := by
      rw [Finset.sum_eq_single_of_mem y hyS]
      · rw [if_pos hyU]
      · intro y' hy'S hne
        have h_no : ¬ (x ++ y') ∈ U (p, []) := by
          intro hy'U
          have : x ++ y = x ++ y' := Part.mem_unique hyU hy'U
          exact hne (List.append_cancel_left this).symm
        rw [if_neg h_no]
    rw [h_sum_eq]
    have h_drop : x ∈ (U (p, [])).bind (fun z =>
        if decide (bitsToNat (natBits n) ≤ z.length) then
          Part.some (z.take (z.length - bitsToNat (natBits n)))
        else Part.none) := by
      refine Part.mem_bind hyU ?_
      have hz_len : (x ++ y).length = x.length + n := by simp [hy_len]
      have h_le : bitsToNat (natBits n) ≤ (x ++ y).length := by
        rw [h_bits, hz_len]; omega
      rw [decide_eq_true h_le]
      dsimp
      have h_take : (x ++ y).take ((x ++ y).length - bitsToNat (natBits n)) = x := by
        rw [h_bits, hz_len, Nat.add_sub_cancel, List.take_left]
      rw [h_take]
      exact Part.mem_some x
    rw [if_pos h_drop]
  · have h_sum_zero : (∑ y ∈ stringsOfLength n,
        if (x ++ y) ∈ U (p, []) then progWeight p else 0) = 0 := by
      refine Finset.sum_eq_zero fun y hyS => ?_
      have h_no : ¬ (x ++ y) ∈ U (p, []) := fun h => h_ex ⟨y, hyS, h⟩
      rw [if_neg h_no]
    rw [h_sum_zero]
    exact zero_le _

/-- **Theorem 71.** Some `n`-bit extension of `x` has prefix complexity at least
`K(x | n) + n - O(1)`. -/
theorem exists_extension_KP_ge (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (n : ℕ), ∃ y : BitString, y.length = n ∧
      KP U x (natBits n) + (n : ℕ∞) ≤ KPPlain U (x ++ y) + (c : ℕ∞) := by
  have hM := extDropMap_isPrefixDecompressor U hU.isPrefixDecompressor
  obtain ⟨c_opt, hc_opt⟩ := aprioriMeasure_le_complexityWeight_optimal hU hM
  refine ⟨c_opt, fun x n => ?_⟩
  set S := stringsOfLength n
  have hS_nonempty : S.Nonempty :=
    ⟨List.replicate n false, (mem_stringsOfLength n _).mpr (by simp)⟩
  set g : BitString → ℝ≥0∞ := fun y => complexityWeight (KPPlain U (x ++ y))
  obtain ⟨y, hyS, hyMin⟩ := exists_le_card_mul_le_sum S hS_nonempty g
  have hy_len : y.length = n := (mem_stringsOfLength n y).mp hyS
  refine ⟨y, hy_len, ?_⟩
  by_cases htop : KPPlain U (x ++ y) = ⊤
  · rw [htop]; exact le_top
  have h_f : (∑ z ∈ S, aprioriMeasure U (x ++ z) []) ≤
      aprioriMeasure (extDropMap U) x (natBits n) :=
    extDropMap_aprioriMeasure_ge U x n
  have h_sum_le : (∑ z ∈ S, g z) ≤ aprioriMeasure (extDropMap U) x (natBits n) := by
    refine (Finset.sum_le_sum fun z _ => ?_).trans h_f
    exact complexityWeight_KP_le_aprioriMeasure U (x ++ z) []
  have h_opt := hc_opt x (natBits n)
  have h_card : (S.card : ℝ≥0∞) = (2 : ℝ≥0∞) ^ n := by
    rw [card_stringsOfLength, Nat.cast_pow, Nat.cast_ofNat]
  have h_two_pow : (2 : ℝ≥0∞) ^ n * (2 : ℝ≥0∞)⁻¹ ^ n = 1 := by
    rw [← mul_pow, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow]
  have h_cw_bound : (2 : ℝ≥0∞)⁻¹ ^ c_opt * complexityWeight (KPPlain U (x ++ y))
      ≤ complexityWeight (KP U x (natBits n) + (n : ℕ∞)) := by
    rw [complexityWeight_add_nat]
    calc (2 : ℝ≥0∞)⁻¹ ^ c_opt * complexityWeight (KPPlain U (x ++ y))
        = (2 : ℝ≥0∞)⁻¹ ^ c_opt * g y * 1 := by rw [mul_one]
      _ = (2 : ℝ≥0∞)⁻¹ ^ c_opt * g y * ((2 : ℝ≥0∞) ^ n * (2 : ℝ≥0∞)⁻¹ ^ n) := by rw [h_two_pow]
      _ = (2 : ℝ≥0∞)⁻¹ ^ c_opt * (g y * (2 : ℝ≥0∞) ^ n) * (2 : ℝ≥0∞)⁻¹ ^ n := by ring
      _ = (2 : ℝ≥0∞)⁻¹ ^ c_opt * (g y * (S.card : ℝ≥0∞)) * (2 : ℝ≥0∞)⁻¹ ^ n := by rw [← h_card]
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ c_opt * (∑ z ∈ S, g z) * (2 : ℝ≥0∞)⁻¹ ^ n :=
          mul_le_mul_left (mul_le_mul_right hyMin _) _
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ c_opt * aprioriMeasure (extDropMap U) x (natBits n) * (2 : ℝ≥0∞)⁻¹ ^ n :=
          mul_le_mul_left (mul_le_mul_right h_sum_le _) _
      _ ≤ complexityWeight (KP U x (natBits n)) * (2 : ℝ≥0∞)⁻¹ ^ n :=
          mul_le_mul_left h_opt _
  exact le_add_nat_of_complexityWeight_le htop h_cw_bound

/-- Helper map for Exercise 116: deconstruct `pairCode (x ++ y) (natBits n)`
into `pairCode x y`. -/
def deconstructConcatPair (z : BitString) : BitString :=
  let w1 := decodeFirst z
  let w2 := decodeSecond z
  let n := bitsToNat w2
  let l := w1.length - n
  pairCode (w1.take l) (w1.drop l)

/-- `deconstructConcatPair` is computable. -/
lemma deconstructConcatPair_computable : Computable deconstructConcatPair := by
  have h1 : Primrec (fun z => decodeFirst z) := CodedFiniteDistribution.decodeFirst_primrec
  have h2 : Primrec (fun z => decodeSecond z) := CodedFiniteDistribution.decodeSecond_primrec
  have h3 : Primrec (fun z => bitsToNat (decodeSecond z)) :=
    bitsToNat_primrec.comp h2
  have h4 : Primrec (fun z => (decodeFirst z).length) :=
    Primrec.list_length.comp h1
  have h5 : Primrec (fun z => (decodeFirst z).length - bitsToNat (decodeSecond z)) :=
    Primrec.nat_sub.comp h4 h3
  have htake : Computable (fun z =>
      (decodeFirst z).take ((decodeFirst z).length - bitsToNat (decodeSecond z))) :=
    (Primrec.list_take.comp h1 h5).to_comp
  have hdrop : Computable (fun z =>
      (decodeFirst z).drop ((decodeFirst z).length - bitsToNat (decodeSecond z))) :=
    (Primrec.list_drop.comp h1 h5).to_comp
  exact (CodedFiniteDistribution.pairCode_primrec.to_comp).comp htake hdrop

/-- `deconstructConcatPair` inverts the concatenation encoding: applied to the pair
code of `x ++ y` together with the length `n` of `y`, it returns the pair code of
`x` and `y`. -/
lemma deconstructConcatPair_eval (x y : BitString) (n : ℕ) (hy : y.length = n) :
    deconstructConcatPair (pairCode (x ++ y) (natBits n)) = pairCode x y := by
  dsimp [deconstructConcatPair, natBits]
  rw [decodeFirst_pairCode, decodeSecond_pairCode, bitsToNat_bits]
  have hlen : (x ++ y).length = x.length + n := by
    rw [List.length_append, hy]
  have hsub : (x ++ y).length - n = x.length := by
    rw [hlen]; omega
  rw [hsub, List.take_left, List.drop_left]

/-- **Exercise 116.** The weaker form of Theorem 71 with `K(x) - K(n)` in place of
`K(x | n)`. -/
theorem exists_extension_KP_ge_sub (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (n : ℕ), ∃ y : BitString, y.length = n ∧
      (kVal U x : ℤ) - (kNatVal U n : ℤ) + (n : ℤ) - (c : ℤ) ≤ (kVal U (x ++ y) : ℤ) := by
  obtain ⟨c_map, hc_map⟩ :=
    KPPlain_map_le U hU deconstructConcatPair deconstructConcatPair_computable
  obtain ⟨c_pair, hc_pair⟩ := KPPair_le_KPPlain_add_KPPlain U hU
  obtain ⟨c_lower, hc_lower⟩ := KPPair_chain_lower U hU
  refine ⟨c_lower + c_map + c_pair, fun x n => ?_⟩
  set kx_nat := (KPPlain U x).toNat
  have hkx : HasPrefixComplexityValue U x kx_nat := by
    dsimp [HasPrefixComplexityValue]
    exact ENat.coe_toNat (KPPlain_ne_top_of_optimal U hU x)
  set z_ctx := prefixComplexityContext x kx_nat
  obtain ⟨y, hy_len, hy_incomp⟩ := exists_incompressible_string U z_ctx n
  refine ⟨y, hy_len, ?_⟩
  have h1 : KPPlain U x + (n : ENat) ≤ KPPair U x y + (c_lower : ENat) := by
    have h_add : KPPlain U x + (n : ENat) ≤ KPPlain U x + KP U y z_ctx := by
      gcongr
      exact hy_incomp
    exact h_add.trans (hc_lower x y kx_nat hkx)
  have h2 : KPPair U x y ≤ KPPlain U (x ++ y) + kNat U n + ((c_map + c_pair : ℕ) : ENat) := by
    have h_eval := hc_map (pairCode (x ++ y) (natBits n))
    rw [deconstructConcatPair_eval x y n hy_len] at h_eval
    have h_pair := hc_pair (x ++ y) (natBits n)
    dsimp [kNat]
    have h_step : KPPlain U (pairCode (x ++ y) (natBits n)) + (c_map : ENat) ≤
        KPPlain U (x ++ y) + KPPlain U (natBits n) + (c_pair : ENat) + (c_map : ENat) := by
      gcongr
      exact h_pair
    have h_trans := h_eval.trans h_step
    have h_eq : KPPlain U (x ++ y) + KPPlain U (natBits n) + (c_pair : ENat) + (c_map : ENat) =
        KPPlain U (x ++ y) + KPPlain U (natBits n) + ((c_map + c_pair : ℕ) : ENat) := by
      rw [add_assoc (KPPlain U (x ++ y) + KPPlain U (natBits n))]
      have h_sum : (c_pair : ENat) + (c_map : ENat) = ((c_map + c_pair : ℕ) : ENat) := by
        norm_cast; omega
      rw [h_sum]
    exact h_trans.trans_eq h_eq
  have h_combine : KPPlain U x + (n : ENat) ≤
      KPPlain U (x ++ y) + kNat U n + ((c_lower + c_map + c_pair : ℕ) : ENat) := by
    have h_step : KPPair U x y + (c_lower : ENat) ≤
        (KPPlain U (x ++ y) + kNat U n + ((c_map + c_pair : ℕ) : ENat)) + (c_lower : ENat) := by
      gcongr
    have h_trans := h1.trans h_step
    have h_eq : (KPPlain U (x ++ y) + kNat U n + ((c_map + c_pair : ℕ) : ENat)) +
        (c_lower : ENat) = KPPlain U (x ++ y) + kNat U n +
        ((c_lower + c_map + c_pair : ℕ) : ENat) := by
      rw [add_assoc (KPPlain U (x ++ y) + kNat U n)]
      have h_sum : ((c_map + c_pair : ℕ) : ENat) + (c_lower : ENat) =
          ((c_lower + c_map + c_pair : ℕ) : ENat) := by
        norm_cast; omega
      rw [h_sum]
    exact h_trans.trans_eq h_eq
  have hkx_eq : KPPlain U x = (kVal U x : ENat) := by
    dsimp [kVal]
    exact (ENat.coe_toNat (KPPlain_ne_top_of_optimal U hU x)).symm
  have hkn_eq : kNat U n = (kNatVal U n : ENat) := by
    dsimp [kNatVal, kNat]
    exact (ENat.coe_toNat (KPPlain_ne_top_of_optimal U hU (natBits n))).symm
  have hkxy_eq : KPPlain U (x ++ y) = (kVal U (x ++ y) : ENat) := by
    dsimp [kVal]
    exact (ENat.coe_toNat (KPPlain_ne_top_of_optimal U hU (x ++ y))).symm
  rw [hkx_eq, hkn_eq, hkxy_eq] at h_combine
  have h_nat : kVal U x + n ≤ kVal U (x ++ y) + kNatVal U n + (c_lower + c_map + c_pair) := by
    have h_cast : ((kVal U x + n : ℕ) : ENat) ≤
        ((kVal U (x ++ y) + kNatVal U n + (c_lower + c_map + c_pair) : ℕ) : ENat) := by
      push_cast
      exact h_combine
    exact WithTop.coe_le_coe.mp h_cast
  omega

/-- The argument transformation behind `diffDecoder`: the program `pairCode d q` is
sent to the pair consisting of the second component `q` and the binary code of
`q.length + d`, so that `d` acts as a length increment. -/
def diffDecoderPair (pr : BitString × BitString) : BitString × BitString :=
  (decodeSecond pr.1, Nat.bits ((decodeSecond pr.1).length + decodeBits (decodeFirst pr.1)))

/-- The decoder that reads a length increment `d` off its program and runs `V` on the
remaining program in the context describing the incremented length; see
`diffDecoderPair`. -/
def diffDecoder (V : Map) : Map := fun pr =>
  V (diffDecoderPair pr)

private lemma diffDecoderPair_primrec : Primrec diffDecoderPair := by
  have hd : Primrec (fun (pr : BitString × BitString) => decodeBits (decodeFirst pr.1)) :=
    primrec_decodeBits.comp (CodedFiniteDistribution.decodeFirst_primrec.comp Primrec.fst)
  have hq : Primrec (fun (pr : BitString × BitString) => decodeSecond pr.1) :=
    CodedFiniteDistribution.decodeSecond_primrec.comp Primrec.fst
  have hlen : Primrec (fun (pr : BitString × BitString) => (decodeSecond pr.1).length) :=
    Primrec.list_length.comp hq
  have hadd : Primrec (fun (pr : BitString × BitString) =>
      (decodeSecond pr.1).length + decodeBits (decodeFirst pr.1)) :=
    Primrec.nat_add.comp hlen hd
  have hcond : Primrec (fun (pr : BitString × BitString) =>
      Nat.bits ((decodeSecond pr.1).length + decodeBits (decodeFirst pr.1))) :=
    primrec_natBits.comp hadd
  exact hq.pair hcond

private lemma diffDecoder_isDecompressor (V : Map) (hV : isDecompressor V) :
    isDecompressor (diffDecoder V) :=
  (Partrec.comp hV diffDecoderPair_primrec.to_comp).of_eq (fun _ => rfl)

/-- **Theorem 72, first part.** `K(x | C(x)) = C(x) + O(1)`. -/
theorem condKP_self_plainK_eq (U V : Map)
    (hU : IsOptimalPrefixConditional U) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ x : BitString,
      |(kCondVal U x (natBits (cVal V x)) : ℤ) - (cVal V x : ℤ)| ≤ (c : ℤ) := by
  obtain ⟨c_pk, h_pk⟩ := KP_le_plainK_value_given_value_code U V hU hV
  obtain ⟨c_cond, h_cond⟩ := condK_le_KP V U hV hU.isPrefixDecompressor
  have hD_comp : isDecompressor (diffDecoder V) :=
    diffDecoder_isDecompressor V hV.1
  obtain ⟨c_V, hc_V⟩ := hV.2 (diffDecoder V) hD_comp
  set C_const := 1 + c_V
  obtain ⟨M_bound, hM_bound⟩ := exists_bits_linear_domination 1 4 C_const
  set d_max := M_bound
  refine ⟨c_pk + c_cond + d_max, ?_⟩
  intro x
  have h_plain_eq : plainK V x = (cVal V x : ENat) := by
    have h_ne_top : plainK V x ≠ ⊤ := by
      obtain ⟨c_len, hc_len⟩ := plainK_le_length V hV
      have h_le := hc_len x
      have h_fin : (programLength x : ENat) + (c_len : ENat) ≠ ⊤ := ENat.coe_ne_top _
      exact ne_top_of_le_ne_top h_fin h_le
    exact (ENat.coe_toNat h_ne_top).symm
  have h_up : kCondVal U x (natBits (cVal V x)) ≤ cVal V x + c_pk := by
    have h1 := h_pk x (cVal V x) h_plain_eq
    have h_fin : (cVal V x : ENat) + (c_pk : ENat) ≠ ⊤ := ENat.coe_ne_top _
    have h2 := ENat.toNat_le_toNat h1 h_fin
    simpa [kCondVal, natBits] using h2
  have h_down : cVal V x ≤ kCondVal U x (natBits (cVal V x)) + (c_cond + d_max) := by
    set k := kCondVal U x (natBits (cVal V x))
    have h_kp_toNat : (KP U x (Nat.bits (cVal V x))).toNat = k := rfl
    have h_cond_le : condK V x (Nat.bits (cVal V x)) ≤ (k + c_cond : ℕ) := by
      have h_ck := h_cond x (Nat.bits (cVal V x))
      have h_kp_le : KP U x (Nat.bits (cVal V x)) ≤ (k : ENat) := by
        have h_ne : KP U x (Nat.bits (cVal V x)) ≠ ⊤ := by
          obtain ⟨c_len, hc_len⟩ := KPPlain_le_two_mul_length U hU
          obtain ⟨c_drop, hc_drop⟩ := KP_le_KPPlain U hU
          have h1 := hc_drop x (Nat.bits (cVal V x))
          have h2 := hc_len x
          have h_le : KP U x (Nat.bits (cVal V x)) ≤
              (2 * x.length + c_len + c_drop : ℕ) := by
            calc KP U x (Nat.bits (cVal V x))
                ≤ KPPlain U x + (c_drop : ENat) := h1
              _ ≤ (2 * x.length + c_len : ENat) + (c_drop : ENat) := by gcongr
              _ = ((2 * x.length + c_len + c_drop : ℕ) : ENat) := by push_cast; rfl
          have h_fin2 : ((2 * x.length + c_len + c_drop : ℕ) : ENat) ≠ ⊤ := ENat.coe_ne_top _
          exact ne_top_of_le_ne_top h_fin2 h_le
        rw [← h_kp_toNat]
        exact (ENat.coe_toNat h_ne).symm ▸ le_rfl
      calc condK V x (Nat.bits (cVal V x))
          ≤ KP U x (Nat.bits (cVal V x)) + (c_cond : ENat) := h_ck
        _ ≤ (k : ENat) + (c_cond : ENat) := by gcongr
        _ = ((k + c_cond : ℕ) : ENat) := by push_cast; rfl
    have h_ex_q := (condK_le_iff V x (Nat.bits (cVal V x)) (k + c_cond)).mp h_cond_le
    obtain ⟨q, hq_len, hq_prod⟩ := h_ex_q
    have hq_len_val : q.length ≤ k + c_cond := hq_len
    by_cases hql : cVal V x ≤ q.length
    · omega
    · have hql_lt : q.length < cVal V x := by omega
      set d := cVal V x - q.length
      have hd_pos : 0 < d := by omega
      have hd_eq : cVal V x = q.length + d := by omega
      set p := pairCode (Nat.bits d) q
      have h_diff_prod : produces (diffDecoder V) p [] x := by
        unfold produces diffDecoder diffDecoderPair
        have h_p1 : decodeFirst p = Nat.bits d := decodeFirst_pairCode (Nat.bits d) q
        have h_p2 : decodeSecond p = q := decodeSecond_pairCode (Nat.bits d) q
        have h_add_eq : (decodeSecond p).length + decodeBits (decodeFirst p) = cVal V x := by
          rw [h_p2, h_p1, decodeBits_natBits]
          exact hd_eq.symm
        have h_run :
            V (decodeSecond p, Nat.bits ((decodeSecond p).length + decodeBits (decodeFirst p)))
              = V (q, Nat.bits (cVal V x)) := by
          rw [h_add_eq, h_p2]
        exact h_run ▸ hq_prod
      have h_cond_D : condK (diffDecoder V) x [] ≤ (p.length : ENat) :=
        KP_le_programLength_of_produces h_diff_prod
      have h_plain_D : plainK V x ≤ (p.length : ENat) + (c_V : ENat) := by
        calc plainK V x ≤ condK (diffDecoder V) x [] + (c_V : ENat) := hc_V x []
          _ ≤ (p.length : ENat) + (c_V : ENat) := by gcongr
      have h_cval_le : cVal V x ≤ p.length + c_V := by
        rw [h_plain_eq] at h_plain_D
        exact_mod_cast h_plain_D
      have h_plen : p.length = 2 * (Nat.bits d).length + q.length + 1 := by
        have h1 := length_pairCode (Nat.bits d) q
        change (pairCode (Nat.bits d) q).length = _
        rw [h1]
        omega
      rw [h_plen] at h_cval_le
      have hd_bound : d ≤ 2 * (Nat.bits d).length + C_const := by
        dsimp [C_const]
        omega
      by_cases h_d_small : d ≤ M_bound
      · omega
      · have h_dom := hM_bound d (by omega)
        have hd0 : d = 0 := by
          set L := (Nat.bits d).length
          have h1 : 4 * L + C_const ≤ d := by dsimp [L]; simpa using h_dom
          have h2 : d ≤ 2 * L + C_const := by dsimp [L]; exact hd_bound
          have hL0 : L = 0 := by omega
          dsimp [L] at hL0
          have h_dec := decodeBits_natBits d
          cases h_bits : Nat.bits d
          · rw [h_bits] at h_dec
            exact h_dec.symm
          · have : (Nat.bits d).length ≠ 0 := by simp [h_bits]
            omega
        omega
  have h_diff_up :
      (kCondVal U x (natBits (cVal V x)) : ℤ) - (cVal V x : ℤ) ≤ (c_pk + c_cond + d_max : ℤ) := by
    omega
  have h_diff_down :
      (cVal V x : ℤ) - (kCondVal U x (natBits (cVal V x)) : ℤ) ≤ (c_pk + c_cond + d_max : ℤ) := by
    omega
  have h_abs :
      |(kCondVal U x (natBits (cVal V x)) : ℤ) - (cVal V x : ℤ)| ≤
        (c_pk + c_cond + d_max : ℤ) := by
    rw [abs_le]
    constructor <;> linarith
  exact h_abs

/-- The output of `kpShiftDecoder`: from a program `pairCode d s` with a one-bit sign
`s` and a context coding the number `j`, it returns the binary code of `j + d` if
`s = [true]` and of `j - d` otherwise. -/
def shiftCode (pr : BitString × BitString) : BitString :=
  bif decide (decodeSecond pr.1 = [true])
  then Nat.bits (decodeBits pr.2 + decodeBits (decodeFirst pr.1))
  else Nat.bits (decodeBits pr.2 - decodeBits (decodeFirst pr.1))

private lemma shiftCode_computable : Computable shiftCode := by
  have hx : Primrec (fun (pr : BitString × BitString) => decodeFirst pr.1) :=
    CodedFiniteDistribution.decodeFirst_primrec.comp Primrec.fst
  have hb : Primrec (fun (pr : BitString × BitString) => decodeSecond pr.1) :=
    CodedFiniteDistribution.decodeSecond_primrec.comp Primrec.fst
  have hdist : Primrec (fun (pr : BitString × BitString) => decodeBits (decodeFirst pr.1)) :=
    primrec_decodeBits.comp hx
  have hj : Primrec (fun (pr : BitString × BitString) => decodeBits pr.2) :=
    primrec_decodeBits.comp Primrec.snd
  have hb_eq : Primrec (fun (pr : BitString × BitString) => decide (decodeSecond pr.1 = [true])) :=
    PrimrecPred.decide (Primrec.eq.comp hb (Primrec.const [true]))
  have hadd : Primrec (fun (pr : BitString × BitString) =>
      Nat.bits (decodeBits pr.2 + decodeBits (decodeFirst pr.1))) :=
    primrec_natBits.comp (Primrec.nat_add.comp hj hdist)
  have hsub : Primrec (fun (pr : BitString × BitString) =>
      Nat.bits (decodeBits pr.2 - decodeBits (decodeFirst pr.1))) :=
    primrec_natBits.comp (Primrec.nat_sub.comp hj hdist)
  exact (Primrec.cond hb_eq hadd hsub).to_comp

/-- The halting condition of `kpShiftDecoder`: the program must be exactly the pair
code of its two decoded components and the second component must be a single bit.
This makes the halting set prefix-free. -/
def shiftCond (pr : BitString × BitString) : Bool :=
  let x := decodeFirst pr.1
  let b := decodeSecond pr.1
  decide (pr.1 = pairCode x b) && decide (b.length = 1)

private lemma shiftCond_computable : Computable shiftCond := by
  have hx : Primrec (fun (pr : BitString × BitString) => decodeFirst pr.1) :=
    CodedFiniteDistribution.decodeFirst_primrec.comp Primrec.fst
  have hb : Primrec (fun (pr : BitString × BitString) => decodeSecond pr.1) :=
    CodedFiniteDistribution.decodeSecond_primrec.comp Primrec.fst
  have hpair : Primrec (fun (pr : BitString × BitString) =>
      pairCode (decodeFirst pr.1) (decodeSecond pr.1)) :=
    CodedFiniteDistribution.pairCode_primrec.comp hx hb
  have hc1 : PrimrecPred (fun (pr : BitString × BitString) =>
      pr.1 = pairCode (decodeFirst pr.1) (decodeSecond pr.1)) :=
    Primrec.eq.comp Primrec.fst hpair
  have hlen : Primrec (fun (pr : BitString × BitString) => (decodeSecond pr.1).length) :=
    Primrec.list_length.comp hb
  have hc2 : PrimrecPred (fun (pr : BitString × BitString) => (decodeSecond pr.1).length = 1) :=
    Primrec.eq.comp hlen (Primrec.const 1)
  have hc1_comp : Primrec (fun (pr : BitString × BitString) =>
      decide (pr.1 = pairCode (decodeFirst pr.1) (decodeSecond pr.1))) :=
    PrimrecPred.decide hc1
  have hc2_comp : Primrec (fun (pr : BitString × BitString) =>
      decide ((decodeSecond pr.1).length = 1)) :=
    PrimrecPred.decide hc2
  exact (Primrec.and.comp hc1_comp hc2_comp).to_comp

/-- The shift decoder: on programs satisfying `shiftCond` it outputs `shiftCode`, and
diverges otherwise. It converts a self-delimiting code for a signed offset into a
code for the shifted value. -/
def kpShiftDecoder : Map := fun pr =>
  bif shiftCond pr then Part.some (shiftCode pr) else Part.none

private lemma kpShiftDecoder_isDecompressor : isDecompressor kpShiftDecoder := by
  change Partrec (fun pr =>
    bif shiftCond pr then Part.some (shiftCode pr) else Part.none)
  exact Partrec.cond shiftCond_computable shiftCode_computable Partrec.none

private lemma kpShiftDecoder_isPrefixMachine : IsPrefixMachine kpShiftDecoder
    := by
  intro r p hp q hq hpre
  dsimp [domainAt, Set.mem_setOf_eq, kpShiftDecoder] at hp hq
  cases hp_cond : shiftCond (p, r)
  · rw [hp_cond] at hp; exact False.elim hp
  · cases hq_cond : shiftCond (q, r)
    · rw [hq_cond] at hq; exact False.elim hq
    · dsimp [shiftCond] at hp_cond hq_cond
      rw [Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff] at hp_cond hq_cond
      have hp_code : p = pairCode (decodeFirst p) (decodeSecond p) := hp_cond.1
      have hq_code : q = pairCode (decodeFirst q) (decodeSecond q) := hq_cond.1
      have hp_len1 : (decodeSecond p).length = 1 := hp_cond.2
      have hq_len1 : (decodeSecond q).length = 1 := hq_cond.2
      obtain ⟨rest, hrest⟩ := hpre
      have hp_code' : p = natCode (decodeFirst p).length ++ decodeFirst p ++ decodeSecond p :=
        hp_code
      have hq_code' : q = natCode (decodeFirst q).length ++ decodeFirst q ++ decodeSecond q :=
        hq_code
      have hrest' : natCode (decodeFirst p).length ++ (decodeFirst p ++ decodeSecond p ++ rest) =
          natCode (decodeFirst q).length ++ (decodeFirst q ++ decodeSecond q) := by
        calc natCode (decodeFirst p).length ++ (decodeFirst p ++ decodeSecond p ++ rest)
            = (natCode (decodeFirst p).length ++ decodeFirst p ++ decodeSecond p) ++ rest := by
              simp [List.append_assoc]
          _ = p ++ rest := by rw [← hp_code']
          _ = q := hrest
          _ = natCode (decodeFirst q).length ++ decodeFirst q ++ decodeSecond q := hq_code'
          _ = natCode (decodeFirst q).length ++ (decodeFirst q ++ decodeSecond q) := by
              simp [List.append_assoc]
      have h_inj := natCode_append_inj hrest'
      have h_len_eq : (decodeFirst p).length = (decodeFirst q).length := h_inj.1
      have h_tail := h_inj.2
      have h_tail' :
          decodeFirst p ++ (decodeSecond p ++ rest) = decodeFirst q ++ decodeSecond q := by
        simpa [List.append_assoc] using h_tail
      have h_inj2 := List.append_inj h_tail' h_len_eq
      have h_df_eq : decodeFirst p = decodeFirst q := h_inj2.1
      have h_ds_eq0 : decodeSecond p ++ rest = decodeSecond q := h_inj2.2
      have h_ds_eq : decodeSecond p = decodeSecond q := by
        have h_len : (decodeSecond p ++ rest).length = (decodeSecond q).length := by rw [h_ds_eq0]
        rw [List.length_append, hp_len1, hq_len1] at h_len
        have h_rest_len : rest.length = 0 := by omega
        cases rest
        · simpa using h_ds_eq0
        · contradiction
      rw [hp_code, hq_code, h_df_eq, h_ds_eq]

private lemma kpShiftDecoder_isPrefixDecompressor :
    IsPrefixDecompressor kpShiftDecoder :=
  ⟨kpShiftDecoder_isDecompressor, kpShiftDecoder_isPrefixMachine⟩

/-- The binary code of `dist` tagged with a one-bit sign is a `kpShiftDecoder` program that
turns the context `Nat.bits k` into `Nat.bits m`, for `m = k + dist` when the sign bit is
`true` and `m = k - dist` when it is `false`.  Hence a prefix decompressor `U` with
invariance constant `c` against `kpShiftDecoder` codes `Nat.bits m` from `Nat.bits k` in
`2 * (Nat.bits dist).length + 3 + c` bits. -/
private lemma kpShift_KP_le {U : Map} {c : ℕ}
    (hc : ∀ a r : BitString, KP U a r ≤ KP kpShiftDecoder a r + (c : ENat))
    (sgn : Bool) (k m dist : ℕ) (h : m = if sgn then k + dist else k - dist) :
    KP U (Nat.bits m) (Nat.bits k) ≤ ((2 * (Nat.bits dist).length + 3 + c : ℕ) : ENat) := by
  set p := pairCode (Nat.bits dist) [sgn] with hp
  have h_p1 : decodeFirst p = Nat.bits dist := decodeFirst_pairCode _ _
  have h_p2 : decodeSecond p = [sgn] := decodeSecond_pairCode _ _
  have h_eval : shiftCode (p, Nat.bits k) = Nat.bits m := by
    dsimp [shiftCode]
    rw [h_p1, h_p2, decodeBits_natBits, decodeBits_natBits]
    cases sgn <;> simp [h]
  have h_prod : produces kpShiftDecoder p (Nat.bits k) (Nat.bits m) := by
    have h1 : p = pairCode (decodeFirst p) (decodeSecond p) := by rw [h_p1, h_p2]
    have h2 : (decodeSecond p).length = 1 := by rw [h_p2]; rfl
    have h_cond : shiftCond (p, Nat.bits k) = true := by
      dsimp [shiftCond]
      rw [Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff]
      exact ⟨h1, h2⟩
    change Nat.bits m ∈ (bif shiftCond (p, Nat.bits k)
      then Part.some (shiftCode (p, Nat.bits k)) else Part.none)
    rw [h_cond, h_eval]
    exact Part.mem_some _
  have h_plen : p.length = 2 * (Nat.bits dist).length + 2 := by
    rw [hp, length_pairCode]
    dsimp
    omega
  have h_cast_le : (2 * (Nat.bits dist).length + 2 + c : ℕ) ≤
      2 * (Nat.bits dist).length + 3 + c := by omega
  have h_bound1 : KP kpShiftDecoder (Nat.bits m) (Nat.bits k) ≤ (p.length : ENat) :=
    KP_le_programLength_of_produces h_prod
  calc KP U (Nat.bits m) (Nat.bits k)
      ≤ KP kpShiftDecoder (Nat.bits m) (Nat.bits k) + (c : ENat) := hc _ _
    _ ≤ (p.length : ENat) + (c : ENat) := add_le_add_left h_bound1 (c : ENat)
    _ = ((2 * (Nat.bits dist).length + 2 + c : ℕ) : ENat) := by rw [h_plen]; push_cast; rfl
    _ ≤ ((2 * (Nat.bits dist).length + 3 + c : ℕ) : ENat) := by exact_mod_cast h_cast_le

/-- Conditional prefix complexity against an optimal prefix conditional decompressor is finite. -/
private lemma kpExtension_KP_ne_top {U : Map} (hU : IsOptimalPrefixConditional U)
    (x r : BitString) : KP U x r ≠ ⊤ := by
  obtain ⟨c_len, hc_len⟩ := KPPlain_le_two_mul_length U hU
  obtain ⟨c_drop, hc_drop⟩ := KP_le_KPPlain U hU
  have h2 := hc_len x
  have h_le : KP U x r ≤ ((2 * x.length + c_len + c_drop : ℕ) : ENat) := by
    calc KP U x r ≤ KPPlain U x + (c_drop : ENat) := hc_drop x r
      _ ≤ (2 * x.length + c_len : ENat) + (c_drop : ENat) := by gcongr
      _ = ((2 * x.length + c_len + c_drop : ℕ) : ENat) := by push_cast; rfl
  exact ne_top_of_le_ne_top (ENat.coe_ne_top _) h_le

/-- Chaining a `c_tri`-triangle inequality with a bound of `N` on the intermediate step
gives `KP U x r ≤ KP U x r' + (N + c_tri)`. -/
private lemma KP_triangle_shift {U : Map} {x r r' : BitString} {N c_tri : ℕ}
    (h_tri : KP U x r ≤ KP U x r' + KP U r' r + (c_tri : ENat))
    (h_shift : KP U r' r ≤ ((N : ℕ) : ENat)) :
    KP U x r ≤ KP U x r' + ((N + c_tri : ℕ) : ENat) := by
  calc KP U x r ≤ KP U x r' + KP U r' r + (c_tri : ENat) := h_tri
    _ ≤ KP U x r' + (N : ENat) + (c_tri : ENat) := by gcongr
    _ = KP U x r' + ((N + c_tri : ℕ) : ENat) := by push_cast; ring

/-- A bound between two finite conditional prefix complexities passes to their `ℕ`-valued
representatives `kCondVal`. -/
private lemma kCondVal_le_of_KP_le {U : Map} {x r x' r' : BitString} {N : ℕ}
    (hfin : KP U x r ≠ ⊤) (hfin' : KP U x' r' ≠ ⊤)
    (h : KP U x r ≤ KP U x' r' + ((N : ℕ) : ENat)) :
    kCondVal U x r ≤ kCondVal U x' r' + N := by
  rw [← ENat.coe_toNat hfin, ← ENat.coe_toNat hfin'] at h
  have h' : ((kCondVal U x r : ℕ) : ENat) ≤ ((kCondVal U x' r' + N : ℕ) : ENat) := by
    push_cast; exact h
  exact_mod_cast h'

/-- **Theorem 72, second part.** If `K(x | i) = i + δ`, then `C(x) = i + O(δ)`. -/
theorem plainK_eq_of_condKP_eq_add (U V : Map)
    (hU : IsOptimalPrefixConditional U) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ (x : BitString) (i : ℕ) (d : ℤ),
      (kCondVal U x (natBits i) : ℤ) = (i : ℤ) + d →
      |(cVal V x : ℤ) - (i : ℤ)| ≤ (c : ℤ) * (d.natAbs + 1) := by
  obtain ⟨c_fix, hc_fix⟩ := condKP_self_plainK_eq U V hU hV
  obtain ⟨c_inv, hc_inv⟩ := hU.invariance kpShiftDecoder_isPrefixDecompressor
  obtain ⟨c_tri, hc_tri⟩ := condKP_triangle U hU
  set C_sum := c_fix + c_inv + c_tri + 3
  obtain ⟨M_bound, hM_bound⟩ := exists_bits_linear_domination 1 4 C_sum
  set c_stab := M_bound + C_sum + 32
  refine ⟨c_stab, ?_⟩
  intro x i d hd
  set C := cVal V x
  set dist := if i ≤ C then C - i else i - C
  have h_shift_i_to_C : KP U (Nat.bits C) (Nat.bits i) ≤
      (2 * (Nat.bits dist).length + 3 + c_inv : ℕ) := by
    by_cases h_ic : i ≤ C
    · have hd : dist = C - i := by dsimp [dist]; rw [if_pos h_ic]
      exact kpShift_KP_le hc_inv true i C dist (by change C = i + dist; omega)
    · have hd : dist = i - C := by dsimp [dist]; rw [if_neg h_ic]
      exact kpShift_KP_le hc_inv false i C dist (by change C = i - dist; omega)
  have h_shift_C_to_i : KP U (Nat.bits i) (Nat.bits C) ≤
      (2 * (Nat.bits dist).length + 3 + c_inv : ℕ) := by
    by_cases h_ic : i ≤ C
    · have hd : dist = C - i := by dsimp [dist]; rw [if_pos h_ic]
      exact kpShift_KP_le hc_inv false C i dist (by change i = C - dist; omega)
    · have hd : dist = i - C := by dsimp [dist]; rw [if_neg h_ic]
      exact kpShift_KP_le hc_inv true C i dist (by change i = C + dist; omega)
  have h_kp_i_le : KP U x (Nat.bits i) ≤
      KP U x (Nat.bits C) + ((2 * (Nat.bits dist).length + 3 + c_inv + c_tri : ℕ) : ENat) :=
    KP_triangle_shift (hc_tri x (Nat.bits C) (Nat.bits i)) h_shift_i_to_C
  have h_kp_C_le : KP U x (Nat.bits C) ≤
      KP U x (Nat.bits i) + ((2 * (Nat.bits dist).length + 3 + c_inv + c_tri : ℕ) : ENat) :=
    KP_triangle_shift (hc_tri x (Nat.bits i) (Nat.bits C)) h_shift_C_to_i
  have h_kC_fin : KP U x (Nat.bits C) ≠ ⊤ := kpExtension_KP_ne_top hU x (Nat.bits C)
  have h_ki_fin : KP U x (Nat.bits i) ≠ ⊤ := kpExtension_KP_ne_top hU x (Nat.bits i)
  set Ki := kCondVal U x (Nat.bits i)
  set KC := kCondVal U x (Nat.bits C)
  have h_nat_i_le : Ki ≤ KC + (2 * (Nat.bits dist).length + 3 + c_inv + c_tri) :=
    kCondVal_le_of_KP_le h_ki_fin h_kC_fin h_kp_i_le
  have h_nat_C_le : KC ≤ Ki + (2 * (Nat.bits dist).length + 3 + c_inv + c_tri) :=
    kCondVal_le_of_KP_le h_kC_fin h_ki_fin h_kp_C_le
  have h_dist_bound : dist ≤ d.natAbs + 2 * (Nat.bits dist).length + C_sum := by
    have h_abs := hc_fix x
    have h_kc_val : (kCondVal U x (natBits C) : ℤ) = (KC : ℤ) := rfl
    rw [h_kc_val] at h_abs
    have h_kc_b := abs_le.mp h_abs
    have h_kc_lower : (C : ℤ) - (c_fix : ℤ) ≤ (KC : ℤ) := by linarith
    have h_kc_upper : (KC : ℤ) ≤ (C : ℤ) + (c_fix : ℤ) := by linarith
    have h_ki_z : (Ki : ℤ) = (i : ℤ) + d := by dsimp [Ki, kCondVal]; exact hd
    have h_i_z : (Ki : ℤ) ≤ (KC : ℤ) +
        (2 * ((Nat.bits dist).length : ℤ) + 3 + (c_inv : ℤ) + (c_tri : ℤ)) := by
      have h_le := h_nat_i_le
      zify at h_le
      exact h_le
    have h_C_z : (KC : ℤ) ≤ (Ki : ℤ) +
        (2 * ((Nat.bits dist).length : ℤ) + 3 + (c_inv : ℤ) + (c_tri : ℤ)) := by
      have h_le := h_nat_C_le
      zify at h_le
      exact h_le
    rw [h_ki_z] at h_i_z h_C_z
    have h_bound_z : (dist : ℤ) ≤
        (d.natAbs : ℤ) + 2 * ((Nat.bits dist).length : ℤ) + (C_sum : ℤ) := by
      have h_Csum_eq : (C_sum : ℤ) = (c_fix : ℤ) + (c_inv : ℤ) + (c_tri : ℤ) + 3 := by rfl
      rw [h_Csum_eq]
      by_cases h_ic : i ≤ C
      · have h_dist_eq : (dist : ℤ) = (C : ℤ) - (i : ℤ) := by
          dsimp [dist]
          rw [if_pos h_ic, Nat.cast_sub h_ic]
        have h_abs_d : d ≤ (d.natAbs : ℤ) := by omega
        linarith
      · have h_dist_eq : (dist : ℤ) = (i : ℤ) - (C : ℤ) := by
          dsimp [dist]
          rw [if_neg h_ic, Nat.cast_sub (by omega)]
        have h_abs_d : -d ≤ (d.natAbs : ℤ) := by omega
        linarith
    exact_mod_cast h_bound_z
  have h_abs_eq : |(C : ℤ) - (i : ℤ)| = (dist : ℤ) := by
    dsimp [dist]
    split_ifs with h_ic
    · rw [abs_of_nonneg (by omega), Nat.cast_sub h_ic]
    · rw [abs_of_nonpos (by omega)]
      have : (C : ℤ) - (i : ℤ) = -((i : ℤ) - (C : ℤ)) := by omega
      rw [this, neg_neg, Nat.cast_sub (by omega)]
  by_cases h_dist_small : dist ≤ M_bound
  · have h_c_stab : dist ≤ c_stab * (d.natAbs + 1) := by
      have h1 : dist ≤ c_stab := by dsimp [c_stab]; omega
      have h2 : c_stab ≤ c_stab * (d.natAbs + 1) := Nat.le_mul_of_pos_right _ (by omega)
      exact le_trans h1 h2
    rw [h_abs_eq]
    exact_mod_cast h_c_stab
  · have h_dom := hM_bound dist (by omega)
    have h_c_stab : dist ≤ c_stab * (d.natAbs + 1) := by
      have h1 : 4 * (Nat.bits dist).length + C_sum ≤ dist := by simpa using h_dom
      have h2 : dist ≤ d.natAbs + 2 * (Nat.bits dist).length + C_sum := h_dist_bound
      have hL : 2 * (Nat.bits dist).length ≤ d.natAbs := by omega
      have h_dist_le : dist ≤ 3 * d.natAbs + C_sum := by omega
      have h_c_stab_ge_3 : 3 ≤ c_stab := by dsimp [c_stab]; omega
      have h_c_stab_ge_C : C_sum ≤ c_stab := by dsimp [c_stab]; omega
      have h_m1 : 3 * d.natAbs ≤ c_stab * d.natAbs := Nat.mul_le_mul_right _ h_c_stab_ge_3
      have h_m2 : dist ≤ c_stab * d.natAbs + c_stab := by
        calc dist ≤ 3 * d.natAbs + C_sum := h_dist_le
          _ ≤ c_stab * d.natAbs + c_stab := Nat.add_le_add h_m1 h_c_stab_ge_C
      have h_m3 : c_stab * d.natAbs + c_stab = c_stab * (d.natAbs + 1) := by ring
      exact h_m3 ▸ h_m2
    rw [h_abs_eq]
    exact_mod_cast h_c_stab

end Kolmogorov
