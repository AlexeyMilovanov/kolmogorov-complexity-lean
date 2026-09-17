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
import KolmogorovMathlib.Complexity.Information.ConservationBounds

/-!
# Mutual information: the chain rule and the Markov reversal

`info_pair_chain_rule` (SUV Exercise 63): `I(xy : z) = I(x : z) + I(y : z | x)` up to the usual
logarithmic error.  `markov_reversal` is the algorithmic form of reversing a Markov chain: for
strings of bounded complexity the conditional independences read the same in both directions.

The independence example of Exercise 64 is built on bitwise xor: `xorStr` with its length,
computability and involution lemmas (`xorStr_xorStr_left`, `xorStr_xorStr_right`).  The
`condCVal_*` lemmas — dropping, reassociating and permuting the components of a condition —
are the bookkeeping the proofs run on.
-/

namespace Kolmogorov
open Nat.Partrec (Code)
open StagedEnumeration CodedFiniteDistribution
open Kolmogorov.CodedFiniteDistribution
variable (Q : ℕ × ℕ × BitString → Bool)

/-- **Exercise 63.** The chain identity for mutual information:
`I(xy : z) = I(x : z) + I(y : z | x) + O(log n)`. -/
theorem info_pair_chain_rule (U : Map) (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ (n : ℕ) (x y z : BitString),
      plainK U x ≤ (n : ℕ∞) → plainK U y ≤ (n : ℕ∞) → plainK U z ≤ (n : ℕ∞) →
      |info U (pairCode x y) z - (info U x z + condInfo U y z x)| ≤ ((logSlack c n : ℕ) : ℤ) := by
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
  obtain ⟨c, hc⟩ := condK_cond_swapPairCode_le U hU
  refine ⟨c, fun n x y z _ _ _ => ?_⟩
  have h1 : condK U z (pairCode y x) ≤ condK U z (pairCode x y) + (c : ℕ∞) := hc z x y
  have h2 : condK U z (pairCode x y) ≤ condK U z (pairCode y x) + (c : ℕ∞) := hc z y x
  have hne1 : condK U z (pairCode x y) ≠ ⊤ := condKNeTopAux U hU z (pairCode x y)
  have hne2 : condK U z (pairCode y x) ≠ ⊤ := condKNeTopAux U hU z (pairCode y x)
  have h1' : condK U z (pairCode y x) ≤ ((condK U z (pairCode x y)).toNat + c : ℕ) := by
    calc condK U z (pairCode y x)
        ≤ condK U z (pairCode x y) + (c : ℕ∞) := h1
      _ = ((condK U z (pairCode x y)).toNat : ℕ∞) + (c : ℕ∞) := by rw [ENat.natCast_toNat hne1]
      _ = ((condK U z (pairCode x y)).toNat + c : ℕ) := by push_cast; rfl
  have hcVal1 : condCVal U z (pairCode y x) ≤ condCVal U z (pairCode x y) + c := by
    unfold condCVal
    exact ENat.toNat_le_of_le_natCast h1'
  have h2' : condK U z (pairCode x y) ≤ ((condK U z (pairCode y x)).toNat + c : ℕ) := by
    calc condK U z (pairCode x y)
        ≤ condK U z (pairCode y x) + (c : ℕ∞) := h2
      _ = ((condK U z (pairCode y x)).toNat : ℕ∞) + (c : ℕ∞) := by rw [ENat.natCast_toNat hne2]
      _ = ((condK U z (pairCode y x)).toNat + c : ℕ) := by push_cast; rfl
  have hcVal2 : condCVal U z (pairCode x y) ≤ condCVal U z (pairCode y x) + c := by
    unfold condCVal
    exact ENat.toNat_le_of_le_natCast h2'
  have hdiff : info U (pairCode x y) z - (info U x z + condInfo U y z x) =
      (condCVal U z (pairCode y x) : ℤ) - (condCVal U z (pairCode x y) : ℤ) := by
    unfold info condInfo
    ring
  rw [hdiff]
  have hcVal1Z : (condCVal U z (pairCode y x) : ℤ) ≤ (condCVal U z (pairCode x y) : ℤ) + (c : ℤ) :=
    by exact_mod_cast hcVal1
  have hcVal2Z : (condCVal U z (pairCode x y) : ℤ) ≤ (condCVal U z (pairCode y x) : ℤ) + (c : ℤ) :=
    by exact_mod_cast hcVal2
  have habs :
      |(condCVal U z (pairCode y x) : ℤ) - (condCVal U z (pairCode x y) : ℤ)| ≤ (c : ℤ) := by
    rw [abs_le]
    constructor <;> linarith
  have hcSlack : (c : ℤ) ≤ ((logSlack c n : ℕ) : ℤ) := by
    have : c ≤ logSlack c n := by
      unfold logSlack
      omega
    exact_mod_cast this
  linarith

/-! ### Machinery for Exercise 64 -/

/-- Bitwise `xor` of two strings, truncated to the length of the first. -/
def xorStr (a b : BitString) : BitString :=
  (List.range a.length).map (fun i => xor (a.getD i false) (b.getD i false))

/-- The bitwise xor of two strings has the length of its first argument. -/
@[simp] lemma length_xorStr (a b : BitString) : (xorStr a b).length = a.length := by
  simp [xorStr]

/-- Bitwise xor of two bit strings is primitive recursive in both arguments. -/
lemma xorStr_primrec : Primrec₂ xorStr := by
  have h : Primrec (fun p : BitString × BitString =>
      (List.range p.1.length).map (fun i => xor (p.1.getD i false) (p.2.getD i false))) := by
    refine Primrec.list_map (Primrec.list_range.comp (Primrec.list_length.comp Primrec.fst)) ?_
    exact ((Primrec.dom_bool₂ xor).comp
      ((Primrec.list_getD false).comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
      ((Primrec.list_getD false).comp (Primrec.snd.comp Primrec.fst) Primrec.snd)).to₂
  exact h.to₂

/-- Below the length of `a`, the `i`-th bit of `xorStr a b` is the xor of the `i`-th
bits of `a` and `b`. -/
lemma getD_xorStr (a b : BitString) (i : ℕ) (hi : i < a.length) :
    (xorStr a b).getD i false = xor (a.getD i false) (b.getD i false) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp [xorStr]

/-- Xoring twice with the same string on the right restores the original string. -/
lemma xorStr_xorStr_right (a b : BitString) :
    xorStr (xorStr a b) b = a := by
  refine List.ext_getElem (by simp) (fun i h1 h2 => ?_)
  have hi : i < a.length := h2
  rw [← List.getD_eq_getElem _ _ h1, ← List.getD_eq_getElem _ _ h2,
    getD_xorStr _ _ _ (by simpa using hi), getD_xorStr _ _ _ hi]
  cases a.getD i false <;> cases b.getD i false <;> simp

/-- For strings of equal length, xoring with `a` is an involution: `a ⊕ (a ⊕ b) = b`. -/
lemma xorStr_xorStr_left (a b : BitString) (hab : a.length = b.length) :
    xorStr a (xorStr a b) = b := by
  refine List.ext_getElem (by simp [hab]) (fun i h1 h2 => ?_)
  have hi : i < a.length := by simpa using h1
  rw [← List.getD_eq_getElem _ _ h1, ← List.getD_eq_getElem _ _ h2,
    getD_xorStr _ _ _ hi, getD_xorStr _ _ _ hi]
  cases a.getD i false <;> cases b.getD i false <;> simp

attribute [irreducible] xorStr

private lemma independenceExample_toNat_le₁ {a b : ℕ∞} {k : ℕ} (hb : b ≠ ⊤) (h : a ≤ b + (k : ℕ∞)) :
    a.toNat ≤ b.toNat + k := by
  refine ENat.toNat_le_of_le_natCast ?_
  refine h.trans (le_of_eq ?_)
  rw [Nat.cast_add, ENat.natCast_toNat hb]

private lemma independenceExample_toNat_le₂ {a b₁ b₂ : ℕ∞} {k : ℕ} (h1 : b₁ ≠ ⊤) (h2 : b₂ ≠ ⊤)
    (h : a ≤ b₁ + b₂ + (k : ℕ∞)) : a.toNat ≤ b₁.toNat + b₂.toNat + k := by
  refine ENat.toNat_le_of_le_natCast ?_
  refine h.trans (le_of_eq ?_)
  rw [Nat.cast_add, Nat.cast_add, ENat.natCast_toNat h1, ENat.natCast_toNat h2]

private lemma independenceExample_le_toNat {a : ℕ} {b : ℕ∞} (hb : b ≠ ⊤) (h : (a : ℕ∞) ≤ b) :
    a ≤ b.toNat := by
  rw [← Nat.cast_le (α := ℕ∞), ENat.natCast_toNat hb]
  exact h

private lemma independenceExample_log_le_bits (a n : ℕ) (h : a ≤ n) :
    Nat.log 2 a ≤ (Nat.bits n).length := by
  have h1 : Nat.log 2 a ≤ Nat.log 2 n := Nat.log_mono_right h
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.log_zero_right, Nat.le_zero] at h1
    omega
  · have h2 : Nat.log 2 n < Nat.size n := Nat.lt_size.mpr (Nat.pow_log_le_self 2 hn.ne')
    have h3 : (Nat.bits n).length = Nat.size n := by rw [Nat.size_eq_bits_len]
    omega

private lemma independenceExample_le_logSlack (c n : ℕ) : c ≤ logSlack c n := by
  unfold logSlack
  omega

/-- **Exercise 64, first example.** Independence does not imply conditional
independence. -/
theorem exists_independent_not_conditionally_independent (U : Map) (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ n : ℕ, c ≤ n → ∃ x y z : BitString,
      plainK U x ≤ (n : ℕ∞) ∧ plainK U y ≤ (n : ℕ∞) ∧ plainK U z ≤ (n : ℕ∞) ∧
        |info U x y| ≤ ((logSlack c n : ℕ) : ℤ) ∧
        ((n : ℤ) - ((logSlack c n : ℕ) : ℤ)) ≤ condInfo U x y z := by
  obtain ⟨c0, hc0⟩ := plainK_le_length U hU
  obtain ⟨c3, hc3⟩ := condK_le_plainK U hU
  obtain ⟨k20, h20⟩ := plainK_pair_le_add_two_log_add_condK U hU
  have hf4 : Computable (fun s : BitString => decodeFirst s ++ decodeSecond s) :=
    Primrec.list_append.to_comp.comp decodeFirst_computable decodeSecond_computable
  obtain ⟨c4, hc4⟩ := plainK_map_le U hU _ hf4
  have hf5 : Computable (fun s : BitString => xorStr (decodeFirst s) (decodeSecond s)) :=
    xorStr_primrec.to_comp.comp decodeFirst_computable decodeSecond_computable
  obtain ⟨c5, hc5⟩ := condK_comp U hU _ hf5
  have hf6 : Computable (fun s : BitString =>
      pairCode (xorStr (decodeFirst s) (decodeSecond s)) (decodeSecond s)) :=
    pairCode_primrec.to_comp.comp hf5 decodeSecond_computable
  obtain ⟨c6, hc6⟩ := plainK_map_le U hU _ hf6
  refine ⟨2 * (c0 + c3 + c4 + c5 + c6 + k20) + 2, fun n hn => ?_⟩
  set c := 2 * (c0 + c3 + c4 + c5 + c6 + k20) + 2 with hcdef
  set B := (Nat.bits n).length with hB
  set m := n - c0 with hmdef
  have hmn : m + c0 = n := by omega
  obtain ⟨w, hwlen, hwinc⟩ := exists_incompressible_string U [] (2 * m)
  set x := w.take m with hx
  set y := w.drop m with hy
  set z := xorStr x y with hz
  have hxlen : x.length = m := by rw [hx, List.length_take, hwlen]; omega
  have hylen : y.length = m := by rw [hy, List.length_drop, hwlen]; omega
  have hzlen : z.length = m := by rw [hz, length_xorStr, hxlen]
  have hxy : x.length = y.length := by rw [hxlen, hylen]
  have hw_eq : x ++ y = w := List.take_append_drop m w
  have hlenbound : ∀ s : BitString, s.length = m → plainK U s ≤ (n : ℕ∞) := by
    intro s hs
    calc plainK U s ≤ (s.length : ℕ∞) + (c0 : ℕ∞) := hc0 s
      _ = ((m + c0 : ℕ) : ℕ∞) := by rw [hs]; push_cast; rfl
      _ = (n : ℕ∞) := by rw [hmn]
  have hAle : cVal U x ≤ n := ENat.toNat_le_of_le_natCast (hlenbound x hxlen)
  have hByle : cVal U y ≤ n := ENat.toNat_le_of_le_natCast (hlenbound y hylen)
  have hCzle : cVal U z ≤ n := ENat.toNat_le_of_le_natCast (hlenbound z hzlen)
  have hWge : 2 * m ≤ cVal U w :=
    independenceExample_le_toNat (plainK_ne_top U hU w) hwinc
  have hf2 : cVal U w ≤ cVal U (pairCode x y) + c4 := by
    have h := hc4 (pairCode x y)
    rw [decodeFirst_pairCode, decodeSecond_pairCode, hw_eq] at h
    exact independenceExample_toNat_le₁ (plainK_ne_top U hU _) h
  have hf3 : cVal U (pairCode x y)
      ≤ cVal U x + condCVal U y x + (2 * Nat.log 2 (cVal U x) + k20) :=
    independenceExample_toNat_le₂ (plainK_ne_top U hU x)
      (avgCond_condK_ne_top U hU y x) (h20 x y)
  have hf5' : condCVal U y (pairCode x z) ≤ c5 := by
    have h := hc5 (pairCode x z)
    rw [decodeFirst_pairCode, decodeSecond_pairCode, hz, xorStr_xorStr_left x y hxy] at h
    exact ENat.toNat_le_of_le_natCast h
  have hf6' : cVal U (pairCode x y) ≤ cVal U (pairCode z y) + c6 := by
    have h := hc6 (pairCode z y)
    rw [decodeFirst_pairCode, decodeSecond_pairCode, hz, xorStr_xorStr_right x y] at h
    exact independenceExample_toNat_le₁ (plainK_ne_top U hU _) h
  have hf8 : condCVal U y x ≤ cVal U y + c3 :=
    independenceExample_toNat_le₁ (plainK_ne_top U hU y) (hc3 y x)
  have hf9 : cVal U (pairCode z y)
      ≤ cVal U z + condCVal U y z + (2 * Nat.log 2 (cVal U z) + k20) :=
    independenceExample_toNat_le₂ (plainK_ne_top U hU z)
      (avgCond_condK_ne_top U hU y z) (h20 z y)
  have hlogA : Nat.log 2 (cVal U x) ≤ B := independenceExample_log_le_bits _ _ hAle
  have hlogC : Nat.log 2 (cVal U z) ≤ B := independenceExample_log_le_bits _ _ hCzle
  have hcB : 2 * B ≤ c * B := Nat.mul_le_mul_right B (by omega)
  have hslack : logSlack c n = c * B + c := by rw [logSlack, hB]
  refine ⟨x, y, z, hlenbound x hxlen, hlenbound y hylen, hlenbound z hzlen, ?_, ?_⟩
  · unfold info
    rw [abs_le]
    constructor <;> omega
  · unfold condInfo
    omega

/-- **Exercise 64, second example.** Conditional independence does not imply
independence. -/
theorem exists_conditionally_independent_not_independent (U : Map) (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ n : ℕ, c ≤ n → ∃ x y z : BitString,
      plainK U x ≤ (n : ℕ∞) ∧ plainK U y ≤ (n : ℕ∞) ∧ plainK U z ≤ (n : ℕ∞) ∧
        |condInfo U x y z| ≤ ((logSlack c n : ℕ) : ℤ) ∧
        ((n : ℤ) - ((logSlack c n : ℕ) : ℤ)) ≤ info U x y := by
  obtain ⟨c0, hc0⟩ := plainK_le_length U hU
  obtain ⟨c1, hc1⟩ := condK_self U hU
  obtain ⟨c2, hc2⟩ := condK_comp U hU decodeFirst decodeFirst_computable
  refine ⟨c0 + c1 + c2 + 1, fun n hn => ?_⟩
  set m := n - c0 with hm
  obtain ⟨w, hwlen, hwinc⟩ := exists_incompressible_string U [] m
  have hmn : m + c0 = n := by omega
  have hlen : plainK U w ≤ (n : ℕ∞) := by
    calc plainK U w ≤ (w.length : ℕ∞) + (c0 : ℕ∞) := hc0 w
      _ = ((m + c0 : ℕ) : ℕ∞) := by rw [hwlen]; push_cast; rfl
      _ = (n : ℕ∞) := by rw [hmn]
  -- numerical facts
  have hW : m ≤ cVal U w :=
    independenceExample_le_toNat (plainK_ne_top U hU w) hwinc
  have hWle : cVal U w ≤ n := ENat.toNat_le_of_le_natCast hlen
  have hself : condCVal U w w ≤ c1 := ENat.toNat_le_of_le_natCast (hc1 w)
  have hpair : condCVal U w (pairCode w w) ≤ c2 := by
    have := hc2 (pairCode w w)
    rw [decodeFirst_pairCode] at this
    exact ENat.toNat_le_of_le_natCast this
  have hslack : c0 + c1 + c2 + 1 ≤ logSlack (c0 + c1 + c2 + 1) n :=
    independenceExample_le_logSlack _ _
  refine ⟨w, w, w, hlen, hlen, hlen, ?_, ?_⟩
  · unfold condInfo
    rw [abs_le]
    constructor <;> omega
  · unfold info
    omega

private lemma markovReversal_condK_eq_condCVal (U : Map) (hU : isOptimalConditional U)
    (x y : BitString) :
    condK U x y = (condCVal U x y : ENat) := by
  have hne := avgCond_condK_ne_top U hU x y
  exact (ENat.natCast_toNat hne).symm

/-- A bound between two conditional complexities transports to their `ℕ`-valued representatives
`condCVal`, which are the values of the (finite) conditional complexities. -/
private lemma condCVal_le_of_condK_le (U : Map) (hU : isOptimalConditional U)
    {a b a' b' : BitString} {c : ℕ}
    (h : condK U a b ≤ condK U a' b' + (c : ENat)) :
    condCVal U a b ≤ condCVal U a' b' + c := by
  rw [markovReversal_condK_eq_condCVal U hU a b,
    markovReversal_condK_eq_condCVal U hU a' b'] at h
  have h' : ((condCVal U a b : ℕ) : ENat) ≤ ((condCVal U a' b' + c : ℕ) : ENat) := by
    push_cast; exact h
  exact_mod_cast h'

private lemma hasValue_condCVal (U : Map) (hU : isOptimalConditional U) (x y : BitString) :
    HasPlainConditionalComplexityValue U x y (condCVal U x y) := by
  unfold HasPlainConditionalComplexityValue
  exact markovReversal_condK_eq_condCVal U hU x y

/-- Replacing the *condition* by something computable from it can only help. -/
theorem condK_cond_map_le (V : Map) (hV : isOptimalConditional V)
    (s : BitString → BitString) (hs : Computable s) :
    ∃ c : ℕ, ∀ x y : BitString, condK V x y ≤ condK V x (s y) + (c : ENat) := by
  let D : Map := fun pr => V (pr.1, s pr.2)
  have hD : isDecompressor D :=
    hV.1.comp (Computable.pair Computable.fst (hs.comp Computable.snd))
  obtain ⟨c, hc⟩ := hV.2 D hD
  refine ⟨c, fun x y => ?_⟩
  refine le_trans (hc x y) ?_
  gcongr
  apply sInf_le_sInf
  rintro n ⟨p, hp, rfl⟩
  exact ⟨p, hp, rfl⟩

private def assocRightToLeft (w : BitString) : BitString :=
  pairCode (pairCode (decodeFirst w) (decodeFirst (decodeSecond w))) (decodeSecond (decodeSecond w))

private def assocRightToLeft_p1 (w : BitString) : BitString × BitString :=
  (decodeFirst w, decodeFirst (decodeSecond w))

private def assocRightToLeft_p2 (w : BitString) : BitString × BitString :=
  (pairCode (decodeFirst w) (decodeFirst (decodeSecond w)), decodeSecond (decodeSecond w))

private theorem assocRightToLeft_p1_comp : Computable assocRightToLeft_p1 :=
  Computable.pair decodeFirst_computable
    (@Computable.comp BitString BitString BitString _ _ _ decodeFirst decodeSecond
      decodeFirst_computable decodeSecond_computable)

private theorem assocRightToLeft_p2_comp : Computable assocRightToLeft_p2 :=
  Computable.pair
    (@Computable.comp BitString (BitString × BitString) BitString _ _ _
      (fun p => pairCode p.1 p.2) assocRightToLeft_p1 pairCode_computable
      assocRightToLeft_p1_comp)
    (@Computable.comp BitString BitString BitString _ _ _ decodeSecond decodeSecond
      decodeSecond_computable decodeSecond_computable)

private theorem assocRightToLeft_computable : Computable assocRightToLeft :=
  @Computable.comp BitString (BitString × BitString) BitString _ _ _
    (fun p => pairCode p.1 p.2) assocRightToLeft_p2 pairCode_computable
    assocRightToLeft_p2_comp

private lemma assocRightToLeft_spec (x y z : BitString) :
    assocRightToLeft (pairCode x (pairCode y z)) = pairCode (pairCode x y) z := by
  dsimp [assocRightToLeft]
  rw [decodeFirst_pairCode, decodeSecond_pairCode, decodeFirst_pairCode, decodeSecond_pairCode]

private lemma condK_assocRightToLeft_cond_le (U : Map) (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ t x y z : BitString,
      condK U t (pairCode x (pairCode y z)) ≤
        condK U t (pairCode (pairCode x y) z) + (c : ENat) := by
  obtain ⟨c, hc⟩ := condK_cond_map_le U hU assocRightToLeft assocRightToLeft_computable
  use c
  intro t x y z
  have h := hc t (pairCode x (pairCode y z))
  rw [assocRightToLeft_spec] at h
  exact h

private def assocLeftToRight (w : BitString) : BitString :=
  pairCode (decodeFirst (decodeFirst w)) (pairCode (decodeSecond (decodeFirst w)) (decodeSecond w))

private def assocLeftToRight_p1 (w : BitString) : BitString × BitString :=
  (decodeSecond (decodeFirst w), decodeSecond w)

private def assocLeftToRight_p2 (w : BitString) : BitString × BitString :=
  (decodeFirst (decodeFirst w), pairCode (decodeSecond (decodeFirst w)) (decodeSecond w))

private theorem assocLeftToRight_p1_comp : Computable assocLeftToRight_p1 :=
  Computable.pair
    (@Computable.comp BitString BitString BitString _ _ _ decodeSecond decodeFirst
      decodeSecond_computable decodeFirst_computable)
    decodeSecond_computable

private theorem assocLeftToRight_p2_comp : Computable assocLeftToRight_p2 :=
  Computable.pair
    (@Computable.comp BitString BitString BitString _ _ _ decodeFirst decodeFirst
      decodeFirst_computable decodeFirst_computable)
    (@Computable.comp BitString (BitString × BitString) BitString _ _ _
      (fun p => pairCode p.1 p.2) assocLeftToRight_p1 pairCode_computable
      assocLeftToRight_p1_comp)

private theorem assocLeftToRight_computable : Computable assocLeftToRight :=
  @Computable.comp BitString (BitString × BitString) BitString _ _ _
    (fun p => pairCode p.1 p.2) assocLeftToRight_p2 pairCode_computable
    assocLeftToRight_p2_comp

private lemma assocLeftToRight_spec (x y z : BitString) :
    assocLeftToRight (pairCode (pairCode x y) z) = pairCode x (pairCode y z) := by
  dsimp [assocLeftToRight]
  rw [decodeFirst_pairCode, decodeSecond_pairCode, decodeFirst_pairCode, decodeSecond_pairCode]

private lemma condK_assocLeftToRight_cond_le (U : Map) (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ t x y z : BitString,
      condK U t (pairCode (pairCode x y) z) ≤
        condK U t (pairCode x (pairCode y z)) + (c : ENat) := by
  obtain ⟨c, hc⟩ := condK_cond_map_le U hU assocLeftToRight assocLeftToRight_computable
  use c
  intro t x y z
  have h := hc t (pairCode (pairCode x y) z)
  rw [assocLeftToRight_spec] at h
  exact h

private def permCond (w : BitString) : BitString :=
  pairCode (decodeFirst (decodeFirst w)) (pairCode (decodeSecond w) (decodeSecond (decodeFirst w)))

private def permCond_p1 (w : BitString) : BitString × BitString :=
  (decodeSecond w, decodeSecond (decodeFirst w))

private def permCond_p2 (w : BitString) : BitString × BitString :=
  (decodeFirst (decodeFirst w), pairCode (decodeSecond w) (decodeSecond (decodeFirst w)))

private theorem permCond_p1_comp : Computable permCond_p1 :=
  Computable.pair decodeSecond_computable
    (@Computable.comp BitString BitString BitString _ _ _ decodeSecond decodeFirst
      decodeSecond_computable decodeFirst_computable)

private theorem permCond_p2_comp : Computable permCond_p2 :=
  Computable.pair
    (@Computable.comp BitString BitString BitString _ _ _ decodeFirst decodeFirst
      decodeFirst_computable decodeFirst_computable)
    (@Computable.comp BitString (BitString × BitString) BitString _ _ _
      (fun p => pairCode p.1 p.2) permCond_p1 pairCode_computable
      permCond_p1_comp)

private theorem permCond_computable : Computable permCond :=
  @Computable.comp BitString (BitString × BitString) BitString _ _ _
    (fun p => pairCode p.1 p.2) permCond_p2 pairCode_computable
    permCond_p2_comp

private lemma permCond_spec (x y z : BitString) :
    permCond (pairCode (pairCode x y) z) = pairCode x (pairCode z y) := by
  dsimp [permCond]
  rw [decodeFirst_pairCode, decodeSecond_pairCode, decodeFirst_pairCode, decodeSecond_pairCode]

private lemma condK_perm_cond_le (U : Map) (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ t x y z : BitString,
      condK U t (pairCode (pairCode x y) z) ≤
        condK U t (pairCode x (pairCode z y)) + (c : ENat) := by
  obtain ⟨c, hc⟩ := condK_cond_map_le U hU permCond permCond_computable
  use c
  intro t x y z
  have h := hc t (pairCode (pairCode x y) z)
  rw [permCond_spec] at h
  exact h

private lemma goal1_arith
    (C_y_z C_y_tz C_t_z C_ty_z C_yt_z C_t_yz C_t_xyz s cSwap cRight cAssocLR
      L_yt L_ty L_log L_final : ℤ)
    (h3_lo : C_y_z + C_t_yz ≤ C_yt_z + L_yt)
    (h4_up : C_ty_z ≤ C_t_z + C_y_tz + L_ty)
    (h_swap_yt : C_yt_z ≤ C_ty_z + cSwap)
    (h_mono_t1 : C_t_xyz ≤ C_t_yz + cRight + cAssocLR)
    (hI2 : C_t_z ≤ C_t_xyz + s)
    (h_slack_yt : L_yt ≤ L_log)
    (h_slack_ty : L_ty ≤ L_log)
    (h_raw_le : 2 * L_log + cSwap + cRight + cAssocLR ≤ L_final) :
    C_y_z - C_y_tz ≤ s + L_final := by
  linarith

private lemma goal2_arith
    (C_x_y C_x_tzy C_xz_y C_z_xy C_zx_y C_z_y C_x_zy C_tx_zy C_t_zy C_x_t_zy C_xt_zy C_t_x_zy C_t_z
      C_t_xyz s cSwap cLeft cAssocRL cPerm L_xz L_zx L_tx L_xt L_log L_final : ℤ)
    (h6_lo : C_x_y + C_z_xy ≤ C_xz_y + L_xz)
    (h1_up : C_zx_y ≤ C_z_y + C_x_zy + L_zx)
    (h_swap_zx : C_xz_y ≤ C_zx_y + cSwap)
    (hI1 : C_z_y ≤ C_z_xy + s)
    (h_assoc_x_tzy : C_x_t_zy ≤ C_x_tzy + cAssocRL)
    (h_soi_tx1 : C_tx_zy ≤ C_t_zy + C_x_t_zy + L_tx)
    (h_swap_xt : C_xt_zy ≤ C_tx_zy + cSwap)
    (h_soi_xt2 : C_x_zy + C_t_x_zy ≤ C_xt_zy + L_xt)
    (h_mono_t_zy : C_t_zy ≤ C_t_z + cLeft)
    (h_assoc_t_xzy : C_t_xyz ≤ C_t_x_zy + cPerm)
    (hI2 : C_t_z ≤ C_t_xyz + s)
    (h_slack_xz : L_xz ≤ L_log)
    (h_slack_zx : L_zx ≤ L_log)
    (h_slack_tx : L_tx ≤ L_log)
    (h_slack_xt : L_xt ≤ L_log)
    (h_raw_le : 4 * L_log + 2 * cSwap + cLeft + cAssocRL + cPerm ≤ L_final) :
    C_x_y - C_x_tzy ≤ 2 * s + L_final := by
  linarith

private lemma log_slack_bound (Clog C_raw n : ℕ) :
    4 * (logSlack Clog n : ℤ) + (C_raw : ℤ) ≤ (logSlack (5 * Clog + C_raw) n : ℤ) := by
  dsimp [logSlack]
  have : 0 ≤ (Clog : ℤ) * (Nat.bits n).length := by positivity
  have : 0 ≤ (C_raw : ℤ) * (Nat.bits n).length := by positivity
  linarith

/-- Bounds the conditional complexity `condCVal U (pairCode A B) C` in terms of `n`
when the plain complexity of `pairCode A B` is bounded by `2 * n + k24`. -/
private lemma markov_reversal_condCVal_pair_bound (U : Map) (hU : isOptimalConditional U)
    (cCond k24 n : ℕ) (hcCond : ∀ x y, condK U x y ≤ plainK U x + (cCond : ENat))
    (A B C : BitString) (h24 : plainK U (pairCode A B) ≤ ((2 * n + k24 : ℕ) : ENat)) :
    condCVal U (pairCode A B) C ≤ 2 * n + k24 + cCond := by
  have h_cond := hcCond (pairCode A B) C
  have h_b : condK U (pairCode A B) C ≤ ((2 * n + k24 + cCond : ℕ) : ENat) := by
    calc condK U (pairCode A B) C ≤ plainK U (pairCode A B) + (cCond : ENat) := h_cond
      _ ≤ ((2 * n + k24 : ℕ) : ENat) + (cCond : ENat) := by gcongr
      _ = ((2 * n + k24 + cCond : ℕ) : ENat) := by push_cast; ring
  have h_eq : condK U (pairCode A B) C = (condCVal U (pairCode A B) C : ENat) :=
    markovReversal_condK_eq_condCVal U hU _ _
  exact ENat.toNat_le_of_le_natCast (h_eq ▸ h_b)

/-- Bounds logarithmic slack when argument `M + 1` is bounded linearly in `n`. -/
private lemma markov_reversal_logSlack_le (cUpper cLower Clog k24 cCond C_raw n M : ℕ)
    (hlog : ∀ n, logSlack (cUpper + cLower) (4 * n + (k24 + cCond + C_raw + 1)) ≤ logSlack Clog n)
    (c : ℕ) (hc : c ≤ cUpper + cLower) (hM : M ≤ 2 * n + k24 + cCond) :
    (logSlack c (M + 1) : ℤ) ≤ (logSlack Clog n : ℤ) := by
  have h1 : M + 1 ≤ 4 * n + (k24 + cCond + C_raw + 1) := by omega
  have h2 := logSlack_mono_right (cUpper + cLower) h1
  have h3 := hlog n
  exact_mod_cast (logSlack_mono_left hc (M + 1)).trans (h2.trans h3)

/-- Swapping components of a pair in the first argument of `condCVal` increases
complexity by at most `cSwap`. -/
private lemma condCVal_swapPairCode_le (U : Map) (hU : isOptimalConditional U) (cSwap : ℕ)
    (hSwap : ∀ x y w, condK U (pairCode y x) w ≤ condK U (pairCode x y) w + (cSwap : ENat))
    (x y z : BitString) :
    condCVal U (pairCode y x) z ≤ condCVal U (pairCode x y) z + cSwap :=
  condCVal_le_of_condK_le U hU (hSwap x y z)

/-- `cRight` and `cAssocLR` are pair-handling constants for the conditional map `U`: dropping
the left component of a pair costs at most `cRight`, and re-associating a nested pair to the
right costs at most `cAssocLR`. -/
private def CondPairReassocBounds (U : Map) (cRight cAssocLR : ℕ) : Prop :=
  (∀ t x y, condK U t (pairCode x y) ≤ condK U t y + (cRight : ENat)) ∧
    ∀ t x y z, condK U t (pairCode (pairCode x y) z) ≤
      condK U t (pairCode x (pairCode y z)) + (cAssocLR : ENat)

/-- Bounds dropping a pair component and re-associating in the second argument of
`condCVal`. -/
private lemma condCVal_mono_right_assoc (U : Map) (hU : isOptimalConditional U)
    (cRight cAssocLR : ℕ) (hbounds : CondPairReassocBounds U cRight cAssocLR)
    (t x y z : BitString) :
    condCVal U t (pairCode (pairCode x y) z) ≤ condCVal U t (pairCode y z) + cRight + cAssocLR := by
  obtain ⟨hRight, hAssocLR⟩ := hbounds
  have hk : condK U t (pairCode (pairCode x y) z)
      ≤ condK U t (pairCode y z) + ((cRight + cAssocLR : ℕ) : ENat) := by
    calc condK U t (pairCode (pairCode x y) z)
        ≤ condK U t (pairCode x (pairCode y z)) + (cAssocLR : ENat) := hAssocLR t x y z
      _ ≤ condK U t (pairCode y z) + (cRight : ENat) + (cAssocLR : ENat) := by
          gcongr; exact hRight t x (pairCode y z)
      _ = condK U t (pairCode y z) + ((cRight + cAssocLR : ℕ) : ENat) := by push_cast; ring
  have h := condCVal_le_of_condK_le U hU hk
  omega

/-- Dropping second component in condition of `condCVal` increases complexity by
at most `cLeft`. -/
private lemma condCVal_condPair_left_le (U : Map) (hU : isOptimalConditional U) (cLeft : ℕ)
    (hLeft : ∀ t x y, condK U t (pairCode x y) ≤ condK U t x + (cLeft : ENat))
    (t z y : BitString) :
    condCVal U t (pairCode z y) ≤ condCVal U t z + cLeft :=
  condCVal_le_of_condK_le U hU (hLeft t z y)

/-- Reassociating condition from right to left in `condCVal`. -/
private lemma condCVal_assocRightToLeft_le (U : Map) (hU : isOptimalConditional U)
    (cAssocRL : ℕ)
    (hAssocRL : ∀ t x y z, condK U t (pairCode x (pairCode y z)) ≤
      condK U t (pairCode (pairCode x y) z) + (cAssocRL : ENat))
    (x t z y : BitString) :
    condCVal U x (pairCode t (pairCode z y)) ≤
      condCVal U x (pairCode (pairCode t z) y) + cAssocRL :=
  condCVal_le_of_condK_le U hU (hAssocRL x t z y)

/-- Permuting components in condition of `condCVal`. -/
private lemma condCVal_perm_cond_le (U : Map) (hU : isOptimalConditional U) (cPerm : ℕ)
    (hPerm : ∀ t x y z, condK U t (pairCode (pairCode x y) z) ≤
      condK U t (pairCode x (pairCode z y)) + (cPerm : ENat))
    (t x y z : BitString) :
    condCVal U t (pairCode (pairCode x y) z) ≤
      condCVal U t (pairCode x (pairCode z y)) + cPerm :=
  condCVal_le_of_condK_le U hU (hPerm t x y z)

/-- Reversal of a Markov chain in the algorithmic setting: if `x, y, z, t` all have
complexity at most `n` and both `I(x : y | z)` and `I(⟨x,y⟩ : t | z)` are at most `s`,
then `I(t : y | z) ≤ s + O(log n)` and `I(⟨t,z⟩ : x | y) ≤ 2s + O(log n)`.
SUV Exercise 65. -/
theorem markov_reversal (U : Map) (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ (n s : ℕ) (x y z t : BitString),
      plainK U x ≤ (n : ℕ∞) → plainK U y ≤ (n : ℕ∞) → plainK U z ≤ (n : ℕ∞) →
      plainK U t ≤ (n : ℕ∞) →
      condInfo U x z y ≤ (s : ℤ) → condInfo U (pairCode x y) t z ≤ (s : ℤ) →
      condInfo U t y z ≤ (s : ℤ) + ((logSlack c n : ℕ) : ℤ) ∧
        condInfo U (pairCode t z) x y ≤ 2 * (s : ℤ) + ((logSlack c n : ℕ) : ℤ) := by
  obtain ⟨cUpper, hUpper⟩ := condK_pairCode_chain_upper_values U hU
  obtain ⟨cLower, hLower⟩ := condK_pairCode_chain_lower_values U hU
  obtain ⟨cLeft, hLeft⟩ := condK_condPair_left_le U hU
  obtain ⟨cRight, hRight⟩ := condK_condPair_right_le U hU
  obtain ⟨cAssocRL, hAssocRL⟩ := condK_assocRightToLeft_cond_le U hU
  obtain ⟨cAssocLR, hAssocLR⟩ := condK_assocLeftToRight_cond_le U hU
  obtain ⟨cPerm, hPerm⟩ := condK_perm_cond_le U hU
  obtain ⟨cSwap, hSwap⟩ := condK_swapPairCode_le U hU
  obtain ⟨k24, hk24⟩ := plainK_pair_le_two_mul U hU
  obtain ⟨cCond, hcCond⟩ := condK_le_plainK U hU
  --
  set C_raw := 2 * (cUpper + cLower + cLeft + cRight + cAssocRL + cAssocLR + cPerm +
    cSwap + k24 + cCond + 1)
  obtain ⟨Clog, hlog⟩ := logSlack_linear_bound (cUpper + cLower) 4 (k24 + cCond + C_raw + 1)
  refine ⟨5 * Clog + C_raw, fun n s x y z t hx hy hz ht hI1 hI2 => ?_⟩
  --
  have h_val (a b : BitString) : HasPlainConditionalComplexityValue U a b (condCVal U a b) :=
    hasValue_condCVal U hU a b
  --
  -- Complexities
  generalize h_Cz_y : condCVal U z y = Cz_y
  generalize h_Cx_zy : condCVal U x (pairCode z y) = Cx_zy
  generalize h_Czx_y : condCVal U (pairCode z x) y = Czx_y
  generalize h_Ct_xyz : condCVal U t (pairCode (pairCode x y) z) = Ct_xyz
  generalize h_Cy_z : condCVal U y z = Cy_z
  generalize h_Ct_yz : condCVal U t (pairCode y z) = Ct_yz
  generalize h_Cyt_z : condCVal U (pairCode y t) z = Cyt_z
  generalize h_Ct_z : condCVal U t z = Ct_z
  generalize h_Cy_tz : condCVal U y (pairCode t z) = Cy_tz
  generalize h_Cty_z : condCVal U (pairCode t y) z = Cty_z
  generalize h_Cx_tzy : condCVal U x (pairCode (pairCode t z) y) = Cx_tzy
  generalize h_Cx_y : condCVal U x y = Cx_y
  generalize h_Cz_xy : condCVal U z (pairCode x y) = Cz_xy
  generalize h_Cxz_y : condCVal U (pairCode x z) y = Cxz_y
  generalize h_Ctx_zy : condCVal U (pairCode t x) (pairCode z y) = Ctx_zy
  generalize h_Cxt_zy : condCVal U (pairCode x t) (pairCode z y) = Cxt_zy
  generalize h_Ct_zy : condCVal U t (pairCode z y) = Ct_zy
  generalize h_Ct_x_zy : condCVal U t (pairCode x (pairCode z y)) = Ct_x_zy
  generalize h_Cx_t_zy : condCVal U x (pairCode t (pairCode z y)) = Cx_t_zy
  --
  have hv (a b : BitString) (K : ℕ) (hK : condCVal U a b = K) :
      HasPlainConditionalComplexityValue U a b K := hK ▸ h_val a b
  --
  have h1_lo := hLower z x y Cz_y Cx_zy Czx_y (hv z y _ h_Cz_y) (hv x _ _ h_Cx_zy)
    (hv _ y _ h_Czx_y)
  have h1_up := hUpper z x y Cz_y Cx_zy Czx_y (hv z y _ h_Cz_y) (hv x _ _ h_Cx_zy)
    (hv _ y _ h_Czx_y)
  have h3_lo := hLower y t z Cy_z Ct_yz Cyt_z (hv y z _ h_Cy_z) (hv t _ _ h_Ct_yz)
    (hv _ z _ h_Cyt_z)
  have h4_up := hUpper t y z Ct_z Cy_tz Cty_z (hv t z _ h_Ct_z) (hv y _ _ h_Cy_tz)
    (hv _ z _ h_Cty_z)
  have h6_lo := hLower x z y Cx_y Cz_xy Cxz_y (hv x y _ h_Cx_y) (hv z _ _ h_Cz_xy)
    (hv _ y _ h_Cxz_y)
  have h_soi_tx1 :=
    hUpper t x (pairCode z y) Ct_zy Cx_t_zy Ctx_zy (hv t _ _ h_Ct_zy) (hv x _ _ h_Cx_t_zy)
      (hv _ _ _ h_Ctx_zy)
  have h_soi_xt2 :=
    hLower x t (pairCode z y) Cx_zy Ct_x_zy Cxt_zy (hv x _ _ h_Cx_zy) (hv t _ _ h_Ct_x_zy)
      (hv _ _ _ h_Cxt_zy)
  --
  have h_mono_t1 : Ct_xyz ≤ Ct_yz + cRight + cAssocLR :=
    h_Ct_xyz.symm ▸ h_Ct_yz.symm ▸
      condCVal_mono_right_assoc U hU cRight cAssocLR ⟨hRight, hAssocLR⟩ t x y z
  have h_swap_yt : Cyt_z ≤ Cty_z + cSwap :=
    h_Cyt_z.symm ▸ h_Cty_z.symm ▸ condCVal_swapPairCode_le U hU cSwap hSwap t y z
  have h_swap_zx : Cxz_y ≤ Czx_y + cSwap :=
    h_Cxz_y.symm ▸ h_Czx_y.symm ▸ condCVal_swapPairCode_le U hU cSwap hSwap z x y
  have h_swap_xt : Cxt_zy ≤ Ctx_zy + cSwap :=
    h_Cxt_zy.symm ▸ h_Ctx_zy.symm ▸ condCVal_swapPairCode_le U hU cSwap hSwap t x (pairCode z y)
  have h_mono_t_zy : Ct_zy ≤ Ct_z + cLeft :=
    h_Ct_zy.symm ▸ h_Ct_z.symm ▸ condCVal_condPair_left_le U hU cLeft hLeft t z y
  have h_assoc_x_tzy : Cx_t_zy ≤ Cx_tzy + cAssocRL :=
    h_Cx_t_zy.symm ▸ h_Cx_tzy.symm ▸ condCVal_assocRightToLeft_le U hU cAssocRL hAssocRL x t z y
  have h_assoc_t_xzy : Ct_xyz ≤ Ct_x_zy + cPerm :=
    h_Ct_xyz.symm ▸ h_Ct_x_zy.symm ▸ condCVal_perm_cond_le U hU cPerm hPerm t x y z
  --
  have h_bound_yt_z := h_Cyt_z ▸ markov_reversal_condCVal_pair_bound U hU cCond k24 n hcCond y t z
    (hk24 n y t hy ht)
  have h_bound_ty_z := h_Cty_z ▸ markov_reversal_condCVal_pair_bound U hU cCond k24 n hcCond t y z
    (hk24 n t y ht hy)
  have h_bound_xz_y := h_Cxz_y ▸ markov_reversal_condCVal_pair_bound U hU cCond k24 n hcCond x z y
    (hk24 n x z hx hz)
  have h_bound_zx_y := h_Czx_y ▸ markov_reversal_condCVal_pair_bound U hU cCond k24 n hcCond z x y
    (hk24 n z x hz hx)
  have h_bound_tx_zy := h_Ctx_zy ▸ markov_reversal_condCVal_pair_bound U hU cCond k24 n hcCond t x
    (pairCode z y) (hk24 n t x ht hx)
  have h_bound_xt_zy := h_Cxt_zy ▸ markov_reversal_condCVal_pair_bound U hU cCond k24 n hcCond x t
    (pairCode z y) (hk24 n x t hx ht)
  --
  have h_slack_yt' := markov_reversal_logSlack_le cUpper cLower Clog k24 cCond C_raw n Cyt_z
    hlog cLower (Nat.le_add_left cLower cUpper) h_bound_yt_z
  have h_slack_ty' := markov_reversal_logSlack_le cUpper cLower Clog k24 cCond C_raw n Cty_z
    hlog cUpper (Nat.le_add_right cUpper cLower) h_bound_ty_z
  have h_slack_xz' := markov_reversal_logSlack_le cUpper cLower Clog k24 cCond C_raw n Cxz_y
    hlog cLower (Nat.le_add_left cLower cUpper) h_bound_xz_y
  have h_slack_zx' := markov_reversal_logSlack_le cUpper cLower Clog k24 cCond C_raw n Czx_y
    hlog cUpper (Nat.le_add_right cUpper cLower) h_bound_zx_y
  have h_slack_tx' := markov_reversal_logSlack_le cUpper cLower Clog k24 cCond C_raw n Ctx_zy
    hlog cUpper (Nat.le_add_right cUpper cLower) h_bound_tx_zy
  have h_slack_xt' := markov_reversal_logSlack_le cUpper cLower Clog k24 cCond C_raw n Cxt_zy
    hlog cLower (Nat.le_add_left cLower cUpper) h_bound_xt_zy
  --
  dsimp [condInfo] at hI1 hI2
  rw [h_Cz_y, h_Cz_xy] at hI1
  rw [h_Ct_z, h_Ct_xyz] at hI2
  --
  have hI1_cast : (Cz_y : ℤ) ≤ (Cz_xy : ℤ) + (s : ℤ) := by omega
  have hI2_cast : (Ct_z : ℤ) ≤ (Ct_xyz : ℤ) + (s : ℤ) := by omega
  --
  have h_goal1_lem := goal1_arith Cy_z Cy_tz Ct_z Cty_z Cyt_z Ct_yz Ct_xyz (s : ℤ)
    (cSwap : ℤ) (cRight : ℤ) (cAssocLR : ℤ) (logSlack cLower (Cyt_z + 1) : ℤ)
    (logSlack cUpper (Cty_z + 1) : ℤ) (logSlack Clog n : ℤ) (logSlack (5 * Clog + C_raw) n : ℤ)
    (by exact_mod_cast h3_lo) (by exact_mod_cast h4_up) (by exact_mod_cast h_swap_yt)
    (by exact_mod_cast h_mono_t1) hI2_cast h_slack_yt' h_slack_ty' (by
      have h1 : (cSwap : ℤ) + (cRight : ℤ) + (cAssocLR : ℤ) ≤ (C_raw : ℤ) := by omega
      have hlog := log_slack_bound Clog C_raw n
      linarith)
  --
  have h_goal2_lem := goal2_arith Cx_y Cx_tzy Cxz_y Cz_xy Czx_y Cz_y Cx_zy Ctx_zy Ct_zy
    Cx_t_zy Cxt_zy Ct_x_zy Ct_z Ct_xyz (s : ℤ) (cSwap : ℤ) (cLeft : ℤ) (cAssocRL : ℤ) (cPerm : ℤ)
    (logSlack cLower (Cxz_y + 1) : ℤ) (logSlack cUpper (Czx_y + 1) : ℤ)
    (logSlack cUpper (Ctx_zy + 1) : ℤ) (logSlack cLower (Cxt_zy + 1) : ℤ)
    (logSlack Clog n : ℤ) (logSlack (5 * Clog + C_raw) n : ℤ)
    (by exact_mod_cast h6_lo) (by exact_mod_cast h1_up) (by exact_mod_cast h_swap_zx)
    hI1_cast (by exact_mod_cast h_assoc_x_tzy) (by exact_mod_cast h_soi_tx1)
    (by exact_mod_cast h_swap_xt) (by exact_mod_cast h_soi_xt2)
    (by exact_mod_cast h_mono_t_zy) (by exact_mod_cast h_assoc_t_xzy) hI2_cast
    h_slack_xz' h_slack_zx' h_slack_tx' h_slack_xt' (by
      have h2 : 2 * (cSwap : ℤ) + (cLeft : ℤ) + (cAssocRL : ℤ) + (cPerm : ℤ) ≤ (C_raw : ℤ) := by
        omega
      have hlog := log_slack_bound Clog C_raw n
      linarith)
  --
  constructor
  · rw [condInfo, h_Cy_z, h_Cy_tz]
    exact h_goal1_lem
  --
  · rw [condInfo, h_Cx_y, h_Cx_tzy]
    exact h_goal2_lem

end Kolmogorov
