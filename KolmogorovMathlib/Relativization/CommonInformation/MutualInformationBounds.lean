/-
Copyright (c) 2026 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Relativization.Definitions
import KolmogorovMathlib.Relativization.Typization
import KolmogorovMathlib.Relativization.Bunches
import KolmogorovMathlib.CommonInformation.ConditionalIndependence.Part01
import KolmogorovMathlib.CommonInformation.Intermediate
import KolmogorovMathlib.CommonInformation.PlainCoding
import KolmogorovMathlib.Complexity.PairComplexity.ConditionalMinimality
import KolmogorovMathlib.Complexity.PairComplexity.LogarithmicTerms.PlainBounds
import KolmogorovMathlib.Multisource.ConditionalEncoding.ProgramCount
import KolmogorovMathlib.StrongMerging.Coding.Programs
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Mutual Information Bounds

This module proves bounds relating extractable common information to mutual information and
develops estimates for relativized typization. It formalizes the common information bound from
Section 1 and cut and counting estimates associated with Theorem 2 in Section 6 of Muchnik and
Romashchenko's paper on stability under relativization.
-/

namespace Kolmogorov.Relativization

open Filter Asymptotics

/-- Applying a computable map to a string increases conditional complexity by at most a constant
when the conditional description map is optimal. -/
lemma condK_le_add_condMutualInfo_nat_map (D : Map)
    (hD : isOptimalConditional D) (f : BitString → BitString) (hf : Computable f) :
    ∃ c : ℕ, ∀ x z : BitString,
      natCondK D (f x) z ≤ natCondK D x z + c := by
  obtain ⟨c, hc⟩ := condK_map_le D hD f hf
  refine ⟨c, fun x z => ?_⟩
  have h := hc x z
  rw [← ENat.natCast_toNat (condK_ne_top_of_optimal D hD (f x) z),
    ← ENat.natCast_toNat (condK_ne_top_of_optimal D hD x z)] at h
  exact_mod_cast h

private lemma condK_le_add_condMutualInfo_nat_context (D : Map)
    (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ x a z : BitString,
      natCondK D x (pairCode a z) ≤ natCondK D x z + c := by
  obtain ⟨c, hc⟩ := condK_condPair_right_le D hD
  refine ⟨c, fun x a z => ?_⟩
  have h := hc x a z
  rw [← ENat.natCast_toNat (condK_ne_top_of_optimal D hD x (pairCode a z)),
    ← ENat.natCast_toNat (condK_ne_top_of_optimal D hD x z)] at h
  exact_mod_cast h

/-- Optimal conditional complexity is finite and equals its natural-number presentation. -/
lemma condK_le_add_condMutualInfo_value (D : Map)
    (hD : isOptimalConditional D) (x z : BitString) :
    HasPlainConditionalComplexityValue D x z (natCondK D x z) := by
  unfold HasPlainConditionalComplexityValue natCondK
  exact (ENat.natCast_toNat (condK_ne_top_of_optimal D hD x z)).symm

/-- `K(v | z) ≤ K(v | x₁, z) + K(v | x₂, z) + I(x₁ : x₂ | z) + O(log N)`, where
`I(x₁ : x₂ | z) = K(x₁ | z) + K(x₂ | z) − K(x₁, x₂ | z)` and `N = K(x₁, x₂, v | z)`.  The
inequality that bounds the number of iterations in the proof of Theorem 2 (Section 6). -/
theorem condK_le_add_condMutualInfo (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ x₁ x₂ v z : BitString,
      natCondK D v z + natCondK D (pairCode x₁ x₂) z ≤
        natCondK D v (pairCode x₁ z) + natCondK D v (pairCode x₂ z) +
          natCondK D x₁ z + natCondK D x₂ z +
          logSlack c (natCondK D (pairCode (pairCode x₁ x₂) v) z) := by
  obtain ⟨cMapV, hMapV⟩ := condK_le_add_condMutualInfo_nat_map D hD
    decodeSecond decodeSecond_computable
  obtain ⟨cMap12, hMap12⟩ := condK_le_add_condMutualInfo_nat_map D hD
    decodeFirst decodeFirst_computable
  obtain ⟨cMap1, hMap1⟩ := condK_le_add_condMutualInfo_nat_map D hD
    (decodeFirst ∘ decodeFirst) (decodeFirst_computable.comp decodeFirst_computable)
  obtain ⟨cMap2, hMap2⟩ := condK_le_add_condMutualInfo_nat_map D hD
    (decodeSecond ∘ decodeFirst) (decodeSecond_computable.comp decodeFirst_computable)
  obtain ⟨cCtx, hCtx⟩ := condK_le_add_condMutualInfo_nat_context D hD
  obtain ⟨cBase, hBase⟩ := Kolmogorov.base_conditional_mutualInformation_inequality D hD
  let b := 3 * cMapV + cMap12 + cMap1 + cMap2 + 2 * cCtx + 1
  obtain ⟨cFold, hFold⟩ := logSlack_linear_bound cBase 6 b
  refine ⟨cFold, fun x₁ x₂ v z => ?_⟩
  let t := pairCode (pairCode x₁ x₂) v
  let n := natCondK D t z
  let kv := natCondK D v z
  let k12 := natCondK D (pairCode x₁ x₂) z
  let k1 := natCondK D x₁ z
  let k2 := natCondK D x₂ z
  let kv1 := natCondK D v (pairCode x₁ z)
  let kv2 := natCondK D v (pairCode x₂ z)
  have hkvVal := condK_le_add_condMutualInfo_value D hD v z
  have hk12Val := condK_le_add_condMutualInfo_value D hD (pairCode x₁ x₂) z
  have hk1Val := condK_le_add_condMutualInfo_value D hD x₁ z
  have hk2Val := condK_le_add_condMutualInfo_value D hD x₂ z
  have hkv1Val := condK_le_add_condMutualInfo_value D hD v (pairCode x₁ z)
  have hkv2Val := condK_le_add_condMutualInfo_value D hD v (pairCode x₂ z)
  have hnV : kv ≤ n + cMapV := by
    simpa [kv, n, t, decodeSecond_pairCode] using
      hMapV (pairCode (pairCode x₁ x₂) v) z
  have hn12 : k12 ≤ n + cMap12 := by
    simpa [k12, n, t, decodeFirst_pairCode] using
      hMap12 (pairCode (pairCode x₁ x₂) v) z
  have hn1 : k1 ≤ n + cMap1 := by
    simpa [k1, n, t, decodeFirst_pairCode] using
      hMap1 (pairCode (pairCode x₁ x₂) v) z
  have hn2 : k2 ≤ n + cMap2 := by
    simpa [k2, n, t, decodeFirst_pairCode, decodeSecond_pairCode] using
      hMap2 (pairCode (pairCode x₁ x₂) v) z
  have hnKv1 : kv1 ≤ n + cMapV + cCtx := by
    calc
      kv1 ≤ kv + cCtx := by
        simpa [kv1, kv] using hCtx v x₁ z
      _ ≤ n + cMapV + cCtx := Nat.add_le_add_right hnV cCtx
  have hnKv2 : kv2 ≤ n + cMapV + cCtx := by
    calc
      kv2 ≤ kv + cCtx := by
        simpa [kv2, kv] using hCtx v x₂ z
      _ ≤ n + cMapV + cCtx := Nat.add_le_add_right hnV cCtx
  have hBaseInst := hBase v x₁ x₂ z kv k12 kv1 kv2 k1 k2
    hkvVal hk12Val hkv1Val hkv2Val hk1Val hk2Val
  have hArg : kv + k12 + kv1 + kv2 + k1 + k2 + 1 ≤ 6 * n + b := by
    dsimp [b]
    omega
  have hSlack :
      logSlack cBase (kv + k12 + kv1 + kv2 + k1 + k2 + 1) ≤ logSlack cFold n := by
    calc
      logSlack cBase (kv + k12 + kv1 + kv2 + k1 + k2 + 1)
          ≤ logSlack cBase (6 * n + b) := logSlack_mono_right cBase hArg
      _ ≤ logSlack cFold n := hFold n
  have hfinal : kv + k12 ≤ k1 + kv1 + k2 + kv2 + logSlack cFold n := by
    omega
  simpa [kv, k12, k1, kv1, k2, kv2, n, t, Nat.add_assoc, Nat.add_left_comm,
    Nat.add_comm] using hfinal

/-- The natural-number presentation of plain complexity is attained as a finite value. -/
theorem commonInfo_le_mutualInfo_hasPlainValue (D : Map)
    (hD : isOptimalConditional D) (x : BitString) :
    HasPlainComplexityValue D x (natK D x) := by
  have hfinite : plainK D x ≠ ⊤ := by
    obtain ⟨c, hc⟩ := plainK_le_length D hD
    exact ne_top_of_le_natCast_add (hc x)
  unfold HasPlainComplexityValue natK
  exact (ENat.natCast_toNat hfinite).symm

/-- The natural-number presentation of conditional complexity is attained as a finite value. -/
theorem commonInfo_le_mutualInfo_hasCondValue (D : Map)
    (hD : isOptimalConditional D) (x y : BitString) :
    HasPlainConditionalComplexityValue D x y (natCondK D x y) := by
  obtain ⟨cPlain, hPlain⟩ := plainK_le_length D hD
  obtain ⟨cCond, hCond⟩ := condK_le_plainK D hD
  have hbound : condK D x y ≤
      ((programLength x + cPlain + cCond : ℕ) : ℕ∞) := by
    calc
      condK D x y ≤ plainK D x + (cCond : ℕ∞) := hCond x y
      _ ≤ (programLength x : ℕ∞) + (cPlain : ℕ∞) + (cCond : ℕ∞) := by
        gcongr
        exact hPlain x
      _ = ((programLength x + cPlain + cCond : ℕ) : ℕ∞) := by push_cast; ring
  have hfinite : condK D x y ≠ ⊤ :=
    ne_top_of_le_natCast (n := programLength x + cPlain + cCond) hbound
  unfold HasPlainConditionalComplexityValue natCondK
  exact (ENat.natCast_toNat hfinite).symm

/-- The binary logarithm of a natural number is at most the length of its binary expansion. -/
theorem commonInfo_le_mutualInfo_natLog_le_bits (n : ℕ) :
    Nat.log 2 n ≤ (Nat.bits n).length := by
  by_cases hn : n = 0
  · simp [hn]
  · have hsize : Nat.log 2 n < Nat.size n :=
        Nat.lt_size.mpr (Nat.pow_log_le_self 2 hn)
    have hbits : (Nat.bits n).length = Nat.size n := Nat.size_eq_bits_len n
    omega

/-- Algorithmic submodularity for
the two pairs that share `y`. -/
private theorem commonInfo_le_mutualInfo_submodularity (D : Map)
    (hD : isOptimalConditional D) :
    ∃ C : ℕ, ∀ (x₁ x₂ y : BitString),
      natK D y + natK D (pairCode x₁ x₂) ≤
        natK D (pairCode x₁ y) + natK D (pairCode x₂ y) +
          logSlack C (natK D y + natK D (pairCode x₁ x₂) +
            natK D (pairCode x₁ y) + natK D (pairCode x₂ y) + 1) := by
  obtain ⟨C, hC⟩ := condK_pairCode_submodularity_values D hD
  refine ⟨C, fun x₁ x₂ y => ?_⟩
  have hy : HasPlainConditionalComplexityValue D y [] (natK D y) := by
    change HasPlainComplexityValue D y (natK D y)
    exact commonInfo_le_mutualInfo_hasPlainValue D hD y
  have hpair : HasPlainConditionalComplexityValue D (pairCode x₁ x₂) []
      (natK D (pairCode x₁ x₂)) := by
    change HasPlainComplexityValue D (pairCode x₁ x₂) _
    exact commonInfo_le_mutualInfo_hasPlainValue D hD (pairCode x₁ x₂)
  have hleft : HasPlainConditionalComplexityValue D (pairCode x₁ y) []
      (natK D (pairCode x₁ y)) := by
    change HasPlainComplexityValue D (pairCode x₁ y) _
    exact commonInfo_le_mutualInfo_hasPlainValue D hD (pairCode x₁ y)
  have hright : HasPlainConditionalComplexityValue D (pairCode x₂ y) []
      (natK D (pairCode x₂ y)) := by
    change HasPlainComplexityValue D (pairCode x₂ y) _
    exact commonInfo_le_mutualInfo_hasPlainValue D hD (pairCode x₂ y)
  exact hC x₁ x₂ y [] (natK D y) (natK D (pairCode x₁ x₂))
    (natK D (pairCode x₁ y)) (natK D (pairCode x₂ y)) hy hpair hleft hright

/-- Encode each pair using the
corresponding short conditional description, then absorb the resulting logarithmic overheads
into the complexity of `(x₁, x₂)` and the threshold `k`. -/
private theorem commonInfo_le_mutualInfo_encodeDescriptions (D : Map)
    (hD : isOptimalConditional D) (Csub : ℕ) :
    ∃ c : ℕ, ∀ (x₁ x₂ y : BitString) (k : ℕ),
      natCondK D y x₁ ≤ k → natCondK D y x₂ ≤ k →
        natK D (pairCode x₁ y) + natK D (pairCode x₂ y) +
            logSlack Csub (natK D y + natK D (pairCode x₁ x₂) +
              natK D (pairCode x₁ y) + natK D (pairCode x₂ y) + 1) ≤
          natK D x₁ + natK D x₂ + c * k +
            logSlack c (natK D (pairCode x₁ x₂)) := by
  obtain ⟨cPair, hPair⟩ := plainK_pair_le_add_two_log_add_condK D hD
  obtain ⟨cLeft, hLeft⟩ := pairPlainK_left_le D hD
  obtain ⟨cRight, hRight⟩ := pairPlainK_right_le D hD
  obtain ⟨cY, hYRight⟩ := pairPlainK_right_le D hD
  obtain ⟨cFold, hFold⟩ := logSlack_absorb_of_le_linear Csub 13
    (2 * (cLeft + cRight + 2 * ((Nat.bits cLeft).length + (Nat.bits cRight).length + 2) +
      2 * cPair) + cY + 1)
  let cp := 4 + cLeft + cRight + 2 * ((Nat.bits cLeft).length + (Nat.bits cRight).length + 2) +
    2 * cPair
  let c := cp + 2 * cFold + 2
  refine ⟨c, ?_⟩
  intro x₁ x₂ y k hyx₁ hyx₂
  let P := natK D (pairCode x₁ x₂)
  let K₁ := natK D x₁
  let K₂ := natK D x₂
  let A := natK D (pairCode x₁ y)
  let B := natK D (pairCode x₂ y)
  have hproj₁ : K₁ ≤ P + cLeft := by
    have hv₁ := commonInfo_le_mutualInfo_hasPlainValue D hD x₁
    have hvp := commonInfo_le_mutualInfo_hasPlainValue D hD (pairCode x₁ x₂)
    have hh := hLeft x₁ x₂
    change plainK D x₁ ≤ plainK D (pairCode x₁ x₂) + (cLeft : ℕ∞) at hh
    rw [hv₁, hvp] at hh
    exact_mod_cast hh
  have hproj₂ : K₂ ≤ P + cRight := by
    have hv₂ := commonInfo_le_mutualInfo_hasPlainValue D hD x₂
    have hvp := commonInfo_le_mutualInfo_hasPlainValue D hD (pairCode x₁ x₂)
    have hh := hRight x₁ x₂
    change plainK D x₂ ≤ plainK D (pairCode x₁ x₂) + (cRight : ℕ∞) at hh
    rw [hv₂, hvp] at hh
    exact_mod_cast hh
  have hpair₁ : A ≤ K₁ + natCondK D y x₁ +
      (2 * Nat.log 2 K₁ + cPair) := by
    have hval₁ := commonInfo_le_mutualInfo_hasPlainValue D hD x₁
    have hvout₁ := commonInfo_le_mutualInfo_hasPlainValue D hD (pairCode x₁ y)
    have hvcond₁ := commonInfo_le_mutualInfo_hasCondValue D hD y x₁
    have hh := hPair x₁ y
    change plainK D (pairCode x₁ y) ≤ plainK D x₁ + condK D y x₁ +
      ((2 * Nat.log 2 (cVal D x₁) + cPair : ℕ) : ℕ∞) at hh
    rw [hvout₁, hval₁, hvcond₁] at hh
    have hcv : cVal D x₁ = K₁ := rfl
    rw [hcv] at hh
    exact_mod_cast hh
  have hpair₂ : B ≤ K₂ + natCondK D y x₂ +
      (2 * Nat.log 2 K₂ + cPair) := by
    have hval₂ := commonInfo_le_mutualInfo_hasPlainValue D hD x₂
    have hvout₂ := commonInfo_le_mutualInfo_hasPlainValue D hD (pairCode x₂ y)
    have hvcond₂ := commonInfo_le_mutualInfo_hasCondValue D hD y x₂
    have hh := hPair x₂ y
    change plainK D (pairCode x₂ y) ≤ plainK D x₂ + condK D y x₂ +
      ((2 * Nat.log 2 (cVal D x₂) + cPair : ℕ) : ℕ∞) at hh
    rw [hvout₂, hval₂, hvcond₂] at hh
    have hcv : cVal D x₂ = K₂ := rfl
    rw [hcv] at hh
    exact_mod_cast hh
  have hlog₁ : Nat.log 2 K₁ ≤ (Nat.bits P).length + (Nat.bits cLeft).length + 1 := by
    calc
      Nat.log 2 K₁ ≤ Nat.log 2 (P + cLeft) := Nat.log_mono_right hproj₁
      _ ≤ (Nat.bits (P + cLeft)).length := commonInfo_le_mutualInfo_natLog_le_bits _
      _ ≤ (Nat.bits P).length + (Nat.bits cLeft).length + 1 := length_natBits_add_le P cLeft
  have hlog₂ : Nat.log 2 K₂ ≤ (Nat.bits P).length + (Nat.bits cRight).length + 1 := by
    calc
      Nat.log 2 K₂ ≤ Nat.log 2 (P + cRight) := Nat.log_mono_right hproj₂
      _ ≤ (Nat.bits (P + cRight)).length := commonInfo_le_mutualInfo_natLog_le_bits _
      _ ≤ (Nat.bits P).length + (Nat.bits cRight).length + 1 := length_natBits_add_le P cRight
  have hpairs : A + B ≤ K₁ + K₂ + 2 * k +
      4 * (Nat.bits P).length +
        (cLeft + cRight + 2 * ((Nat.bits cLeft).length + (Nat.bits cRight).length + 2) +
          2 * cPair) := by
    have hsum := Nat.add_le_add hpair₁ hpair₂
    omega
  have hbitP : (Nat.bits P).length ≤ P := length_natBits_le P
  have hpairs' : A + B ≤ 6 * P + 2 * k +
      (cLeft + cRight + 2 * ((Nat.bits cLeft).length + (Nat.bits cRight).length + 2) +
        2 * cPair) := by omega
  have hYBound : natK D y ≤ A + cY := by
    have hvY := commonInfo_le_mutualInfo_hasPlainValue D hD y
    have hvA := commonInfo_le_mutualInfo_hasPlainValue D hD (pairCode x₁ y)
    have hh := hYRight x₁ y
    change plainK D y ≤ plainK D (pairCode x₁ y) + (cY : ℕ∞) at hh
    rw [hvY, hvA] at hh
    exact_mod_cast hh
  have harg : natK D y + P + A + B + 1 ≤
      13 * (P + k) +
        (2 * (cLeft + cRight + 2 * ((Nat.bits cLeft).length + (Nat.bits cRight).length + 2) +
          2 * cPair) + cY + 1) := by
    calc
      natK D y + P + A + B + 1 ≤ (A + cY) + P + A + B + 1 := by omega
      _ ≤ 2 * (A + B) + P + cY + 1 := by omega
      _ ≤ 2 * (6 * P + 2 * k +
          (cLeft + cRight + 2 * ((Nat.bits cLeft).length + (Nat.bits cRight).length + 2) +
            2 * cPair)) + P + cY + 1 := by omega
      _ ≤ 13 * (P + k) +
          (2 * (cLeft + cRight + 2 * ((Nat.bits cLeft).length + (Nat.bits cRight).length + 2) +
            2 * cPair) + cY + 1) := by omega
  have hlogarg := hFold (P + k) (natK D y + P + A + B + 1) harg
  have hpairSlack : 4 * (Nat.bits P).length +
      (cLeft + cRight + 2 * ((Nat.bits cLeft).length + (Nat.bits cRight).length + 2) +
        2 * cPair) ≤ logSlack cp P := by
    have hcpBits : 4 ≤ cp := by dsimp [cp]; omega
    have hcpConst : cLeft + cRight +
        2 * ((Nat.bits cLeft).length + (Nat.bits cRight).length + 2) + 2 * cPair ≤ cp := by
      dsimp [cp]
      omega
    unfold logSlack
    exact Nat.add_le_add (Nat.mul_le_mul_right _ hcpBits) hcpConst
  have hlogk : logSlack cFold k ≤ cFold * k + cFold := by
    unfold logSlack
    nlinarith [length_natBits_le k]
  have hslack : logSlack cp P + logSlack cFold P + cFold ≤
      logSlack c P := by
    calc
      logSlack cp P + logSlack cFold P + cFold =
          logSlack (cp + cFold) P + cFold := by
            exact (congrArg (fun n => n + cFold)
              (logSlack_add_constants cp cFold P)).symm
      _ ≤ logSlack (cp + cFold) P + logSlack cFold P := by
        exact Nat.add_le_add_left (by unfold logSlack; omega) _
      _ = logSlack (cp + 2 * cFold) P := by
        calc
          logSlack (cp + cFold) P + logSlack cFold P =
              logSlack ((cp + cFold) + cFold) P :=
            (logSlack_add_constants (cp + cFold) cFold P).symm
          _ = logSlack (cp + 2 * cFold) P := by congr 1; omega
      _ ≤ logSlack c P := logSlack_mono_left (by dsimp [c]; omega) P
  have hmain : A + B + logSlack Csub (natK D y + P + A + B + 1) ≤
      K₁ + K₂ + (2 + cFold) * k + logSlack cp P + logSlack cFold P + cFold := by
    have hcoefFold : 2 * k + logSlack cFold k ≤ (2 + cFold) * k + cFold := by
      calc
        2 * k + logSlack cFold k ≤ 2 * k + (cFold * k + cFold) :=
          Nat.add_le_add_left hlogk _
        _ = (2 + cFold) * k + cFold := by rw [Nat.add_mul]; ring
    calc
      A + B + logSlack Csub (natK D y + P + A + B + 1)
          ≤ A + B + logSlack cFold (P + k) := Nat.add_le_add_left hlogarg _
      _ ≤ K₁ + K₂ + 2 * k + logSlack cp P +
            (logSlack cFold P + logSlack cFold k) := by
        have hsplit := logSlack_add_le cFold P k
        omega
      _ ≤ K₁ + K₂ + (2 + cFold) * k + logSlack cp P + logSlack cFold P + cFold := by
        have := hcoefFold
        omega
  have hfinal : K₁ + K₂ + (2 + cFold) * k + logSlack cp P + logSlack cFold P + cFold
      ≤ K₁ + K₂ + c * k + logSlack c P := by
    have hcoef : (2 + cFold) * k ≤ c * k :=
      Nat.mul_le_mul_right k (by dsimp [c]; omega)
    have hlogs : logSlack cp P + logSlack cFold P + cFold ≤ logSlack c P := hslack
    have htail := Nat.add_le_add hcoef hlogs
    calc
      K₁ + K₂ + (2 + cFold) * k + logSlack cp P + logSlack cFold P + cFold
          = (K₁ + K₂) + ((2 + cFold) * k +
              (logSlack cp P + logSlack cFold P + cFold)) := by omega
      _ ≤ (K₁ + K₂) + (c * k + logSlack c P) := Nat.add_le_add_left htail _
      _ = K₁ + K₂ + c * k + logSlack c P := by omega
  simpa [P, K₁, K₂, A, B, c] using hmain.trans hfinal

/-- Extractable common information is at most the mutual information: if `K(y | xᵢ) ≤ k` for
`i = 1, 2`, then `K(y) ≤ I(x₁ : x₂) + O(k + log K(x₁, x₂))`, with
`I(x₁ : x₂) = K(x₁) + K(x₂) − K(x₁, x₂)` (Section 1). -/
theorem commonInfo_le_mutualInfo (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ (x₁ x₂ y : BitString) (k : ℕ),
      natCondK D y x₁ ≤ k → natCondK D y x₂ ≤ k →
        natK D y + natK D (pairCode x₁ x₂) ≤
          natK D x₁ + natK D x₂ + c * k + logSlack c (natK D (pairCode x₁ x₂)) := by
  obtain ⟨Csub, hsub⟩ := commonInfo_le_mutualInfo_submodularity D hD
  obtain ⟨c, hcode⟩ := commonInfo_le_mutualInfo_encodeDescriptions D hD Csub
  refine ⟨c, ?_⟩
  intro x₁ x₂ y k hyx₁ hyx₂
  calc
    natK D y + natK D (pairCode x₁ x₂) ≤
        natK D (pairCode x₁ y) + natK D (pairCode x₂ y) +
          logSlack Csub (natK D y + natK D (pairCode x₁ x₂) +
            natK D (pairCode x₁ y) + natK D (pairCode x₂ y) + 1) := hsub x₁ x₂ y
    _ ≤ natK D x₁ + natK D x₂ + c * k +
          logSlack c (natK D (pairCode x₁ x₂)) := hcode x₁ x₂ y k hyx₁ hyx₂

/-- Bound the
complexity of the extracted string given `z` by encoding it through `x₁` and the tuple whose
complexity is `M`. -/
theorem theorem2_bound_original
    (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ (x₁ x₂ z v : BitString) (t M : ℕ),
      M = natK D (pairCode (pairCode x₁ x₂) z) →
      natCondK D v (pairCode x₁ z) ≤ t →
      t ≤ M →
      natCondK D v z ≤ 2 * M + logSlack c M := by
  let conditionFromTriple : BitString → BitString := fun s =>
    pairCode (decodeFirst (decodeFirst s)) (decodeSecond s)
  have hConditionFromTriple : Computable conditionFromTriple := by
    exact Computable₂.comp pairCode_computable
      (decodeFirst_computable.comp decodeFirst_computable) decodeSecond_computable
  obtain ⟨cMap, hMap⟩ := condK_le_add_condMutualInfo_nat_map D hD
    conditionFromTriple hConditionFromTriple
  obtain ⟨cCondPlain, hCondPlain⟩ := condK_le_plainK D hD
  obtain ⟨cChain, hChain⟩ := Kolmogorov.condK_chain_upper_values D hD
  let b := cMap + cCondPlain
  obtain ⟨cFold, hFold⟩ := logSlack_linear_bound cChain 2 (b + 1)
  refine ⟨cFold + b, ?_⟩
  intro x₁ x₂ z v t M hM hv₁ ht
  let triple := pairCode (pairCode x₁ x₂) z
  let condition := pairCode x₁ z
  have hMapInstance :
      natCondK D condition z ≤ natCondK D triple z + cMap := by
    simpa only [conditionFromTriple, condition, triple, decodeFirst_pairCode,
      decodeSecond_pairCode] using hMap triple z
  have hTripleCondValue := condK_le_add_condMutualInfo_value D hD triple z
  have hTriplePlainValue := commonInfo_le_mutualInfo_hasPlainValue D hD triple
  have hTripleCondNat : natCondK D triple z ≤ natK D triple + cCondPlain := by
    have h := hCondPlain triple z
    rw [hTripleCondValue, hTriplePlainValue] at h
    exact_mod_cast h
  have hConditionBound : natCondK D condition z ≤ M + b := by
    calc
      natCondK D condition z ≤ natCondK D triple z + cMap := hMapInstance
      _ ≤ natK D triple + cCondPlain + cMap :=
        Nat.add_le_add_right hTripleCondNat cMap
      _ = M + b := by
        rw [← hM]
        dsimp [b]
        omega
  have hChainInstance := hChain z v condition
    (natCondK D condition z) (natCondK D v condition) (natCondK D v z)
    (condK_le_add_condMutualInfo_value D hD condition z)
    (condK_le_add_condMutualInfo_value D hD v condition)
    (condK_le_add_condMutualInfo_value D hD v z)
  have hVConditionBound : natCondK D v condition ≤ M := hv₁.trans ht
  have hArg : natCondK D condition z + natCondK D v condition + 1 ≤
      2 * M + (b + 1) := by
    calc
      natCondK D condition z + natCondK D v condition + 1 ≤
          (M + b) + M + 1 := by
        exact Nat.add_le_add_right (Nat.add_le_add hConditionBound hVConditionBound) 1
      _ = 2 * M + (b + 1) := by omega
  have hSlack : logSlack cChain
      (natCondK D condition z + natCondK D v condition + 1) ≤ logSlack cFold M := by
    calc
      logSlack cChain (natCondK D condition z + natCondK D v condition + 1)
          ≤ logSlack cChain (2 * M + (b + 1)) := logSlack_mono_right cChain hArg
      _ ≤ logSlack cFold M := hFold M
  have hParts : natCondK D condition z + natCondK D v condition ≤ (M + b) + t :=
    Nat.add_le_add hConditionBound hv₁
  have hBeforeFold : natCondK D v z ≤ (M + b) + t + logSlack cFold M := by
    calc
      natCondK D v z ≤ natCondK D condition z + natCondK D v condition +
          logSlack cChain (natCondK D condition z + natCondK D v condition + 1) :=
        hChainInstance
      _ ≤ (M + b) + t + logSlack cFold M := Nat.add_le_add hParts hSlack
  calc
    natCondK D v z ≤ (M + b) + t + logSlack cFold M := hBeforeFold
    _ ≤ 2 * M + logSlack (cFold + b) M := by
      have hAbsorb := logSlack_add_nat_le cFold b M
      omega

/-- A shortest program's
`q`-bit prefix cannot have conditional complexity much below `q`, since the remaining suffix
reconstructs the original output. -/
private theorem theorem2_lower_bound
    (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ (v z p : BitString) (q k : ℕ),
      k = natCondK D v z →
      q ≤ k →
      p.length = k →
      produces D p z v →
      q ≤ natCondK D (p.take q) z + logSlack c k := by
  let suffixDecoder : Map := fun pr =>
    (D ((parsePair pr.1).1, pr.2)).bind
      (fun u => D (u ++ (parsePair pr.1).2, pr.2))
  have hFirstProgram : Computable (fun pr : BitString × BitString =>
      (parsePair pr.1).1) :=
    (Computable.fst.comp parsePair_computable).comp Computable.fst
  have hFirstInput : Computable (fun pr : BitString × BitString =>
      ((parsePair pr.1).1, pr.2)) := hFirstProgram.pair Computable.snd
  have hFirst : Partrec (fun pr : BitString × BitString =>
      D ((parsePair pr.1).1, pr.2)) := Partrec.comp hD.1 hFirstInput
  have hSuffix : Computable
      (fun pr : (BitString × BitString) × BitString => (parsePair pr.1.1).2) :=
    (Computable.snd.comp parsePair_computable).comp
      (Computable.fst.comp Computable.fst)
  have hSecondProgram : Computable
      (fun pr : (BitString × BitString) × BitString => pr.2 ++ (parsePair pr.1.1).2) :=
    Computable.list_append.comp Computable.snd hSuffix
  have hSecondInput : Computable
      (fun pr : (BitString × BitString) × BitString =>
        (pr.2 ++ (parsePair pr.1.1).2, pr.1.2)) :=
    hSecondProgram.pair (Computable.snd.comp Computable.fst)
  have hSecond : Partrec
      (fun pr : (BitString × BitString) × BitString =>
        D (pr.2 ++ (parsePair pr.1.1).2, pr.1.2)) := Partrec.comp hD.1 hSecondInput
  have hSuffixDecoder : isDecompressor suffixDecoder := by
    change Partrec suffixDecoder
    unfold suffixDecoder
    exact Partrec.bind hFirst hSecond
  obtain ⟨cSim, hSim⟩ := hD.2 suffixDecoder hSuffixDecoder
  let c := cSim + 2
  refine ⟨c, ?_⟩
  intro v z p q k hk hq hpLength hpProduces
  have hKfinite := condK_ne_top_of_optimal D hD v z
  have hkCast : condK D v z = (k : ℕ∞) := by
    unfold natCondK at hk
    rw [← ENat.natCast_toNat hKfinite, hk]
  let u := p.take q
  let a := natCondK D u z
  by_cases hqa : q ≤ a
  · have hslack : 0 ≤ logSlack c k := Nat.zero_le _
    simpa [a, u] using (show q ≤ a + logSlack c k by omega)
  · have haq : a < q := Nat.lt_of_not_ge hqa
    have haFinite := condK_ne_top_of_optimal D hD u z
    have haCast : condK D u z = (a : ℕ∞) := by
      dsimp [a, natCondK]
      exact (ENat.natCast_toNat haFinite).symm
    have haBound : condK D u z ≤ (a : ℕ∞) := by rw [haCast]
    obtain ⟨r, hrLengthLe, hrProduces⟩ := (condK_le_iff D u z a).mp haBound
    have haInf : condK D u z ≤ (r.length : ℕ∞) :=
      sInf_le ⟨r, hrProduces, rfl⟩
    have haLe : a ≤ r.length := by
      rw [haCast] at haInf
      exact_mod_cast haInf
    change r.length ≤ a at hrLengthLe
    have hrLength : r.length = a := by omega
    let code := pairCode (Nat.bits r.length) (r ++ p.drop q)
    have hcodeProduces : produces suffixDecoder code z v := by
      change v ∈ suffixDecoder (code, z)
      simp only [suffixDecoder, code, parsePair_encode]
      rw [Part.mem_bind_iff]
      refine ⟨u, hrProduces, ?_⟩
      have hconcat : u ++ p.drop q = p := by
        dsimp [u]
        exact List.take_append_drop q p
      rw [hconcat]
      exact hpProduces
    have hcodeBound : condK suffixDecoder v z ≤ (code.length : ℕ∞) :=
      sInf_le ⟨code, hcodeProduces, rfl⟩
    have hkBoundENat : (k : ℕ∞) ≤ ((code.length + cSim : ℕ) : ℕ∞) := by
      calc
        (k : ℕ∞) = condK D v z := hkCast.symm
        _ ≤ condK suffixDecoder v z + cSim := hSim v z
        _ ≤ (code.length : ℕ∞) + cSim := by
          simpa [add_comm] using add_le_add_right hcodeBound cSim
        _ = ((code.length + cSim : ℕ) : ℕ∞) := by push_cast; rfl
    have hkBound : k ≤ code.length + cSim := by exact_mod_cast hkBoundENat
    have hcodeLength : code.length =
        2 * (Nat.bits r.length).length + 1 + r.length + (k - q) := by
      simp [code, length_pairCode, List.length_append, List.length_drop, hpLength]
      omega
    have haqk : a ≤ k := by omega
    have hbits : (Nat.bits r.length).length ≤ (Nat.bits k).length := by
      exact length_natBits_mono (by rw [hrLength]; exact haqk)
    have hbitsA : (Nat.bits a).length ≤ (Nat.bits k).length := by
      rw [← hrLength]
      exact hbits
    have hprefixBound : q ≤ a + 2 * (Nat.bits k).length + (cSim + 1) := by
      rw [hcodeLength, hrLength] at hkBound
      have hsplit : q + (k - q) = k := by omega
      have hbound' : q + (k - q) ≤ a + (k - q) +
          2 * (Nat.bits k).length + (cSim + 1) := by
        calc
          q + (k - q) = k := hsplit
          _ ≤ 2 * (Nat.bits a).length + 1 + a + (k - q) + cSim := by
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hkBound
          _ ≤ a + (k - q) + 2 * (Nat.bits k).length + (cSim + 1) := by omega
      exact Nat.le_of_add_le_add_right (by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hbound')
    have hcoef : 2 * (Nat.bits k).length ≤ (cSim + 2) * (Nat.bits k).length :=
      Nat.mul_le_mul_right _ (by omega)
    have hconst : cSim + 1 ≤ cSim + 2 := by omega
    have hslack : 2 * (Nat.bits k).length + (cSim + 1) ≤ logSlack c k := by
      unfold logSlack
      dsimp [c]
      exact Nat.add_le_add hcoef hconst
    have hfinal : q ≤ a + logSlack c k := by
      calc
        q ≤ a + (2 * (Nat.bits k).length + (cSim + 1)) := by omega
        _ ≤ a + logSlack c k := Nat.add_le_add_left hslack a
    simpa [a, u] using hfinal

/-- Dovetail over programs of
the optimal length `k` and select a description whose `q`-bit prefix is recoverable from `(v,z)`
with logarithmic advice for `q` and `k`. -/
private theorem theorem2_search
    (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ (v z : BitString) (q k : ℕ),
      k = natCondK D v z →
      q ≤ k →
      ∃ p : BitString,
        p.length = k ∧
        produces D p z v ∧
        natCondK D (p.take q) (pairCode v z) ≤ logSlack c k := by
  obtain ⟨cShort, hShort⟩ := condK_conditionalShortestDescription_le_log_length D hD
  obtain ⟨cChain, hChain⟩ := condK_chain_upper_values D hD
  let truncationDecoder : Map := fun pr =>
    Part.some (pr.2.take (bitsToNat pr.1))
  have hTruncationDecoder : isDecompressor truncationDecoder :=
    Computable.partrec
      (Primrec.list_take.comp (bitsToNat_primrec.comp Primrec.fst) Primrec.snd).to_comp
  obtain ⟨cTake, hTake⟩ := hD.2 truncationDecoder hTruncationDecoder
  obtain ⟨cFold, hFold⟩ :=
    logSlack_absorb_of_le_linear cChain (cShort + 1) (cShort + cTake + 1)
  let C := cShort + cFold + cTake + 1
  refine ⟨C, fun v z q k hk hq => ?_⟩
  have hKfinite := condK_ne_top_of_optimal D hD v z
  have hKcast : condK D v z = (k : ℕ∞) := by
    unfold natCondK at hk
    rw [← ENat.natCast_toNat hKfinite, hk]
  have hKle : condK D v z ≤ (k : ℕ∞) := by rw [hKcast]
  obtain ⟨p, hpLe, hpProduces⟩ := (condK_le_iff D v z k).mp hKle
  have hKinf : condK D v z ≤ (p.length : ℕ∞) :=
    sInf_le ⟨p, hpProduces, rfl⟩
  have hpGe : k ≤ p.length := by
    rw [hKcast] at hKinf
    exact_mod_cast hKinf
  change p.length ≤ k at hpLe
  have hpLength : p.length = k := by omega
  have hShortest : condK D p (pairCode v z) ≤ (logSlack cShort k : ℕ∞) := by
    simpa [hpLength] using
      hShort v z p hpProduces (by rw [hpLength, hKcast])
  have hTakeProd : produces truncationDecoder (Nat.bits q) p (p.take q) := by
    simp [produces, truncationDecoder, bitsToNat_bits]
  have hTakeBound : condK D (p.take q) p ≤
      (((Nat.bits q).length + cTake : ℕ) : ℕ∞) := by
    calc
      condK D (p.take q) p ≤ condK truncationDecoder (p.take q) p + cTake :=
        hTake (p.take q) p
      _ ≤ (Nat.bits q).length + cTake := by
        have hProgram : condK truncationDecoder (p.take q) p ≤
            ((Nat.bits q).length : ℕ∞) :=
          sInf_le ⟨Nat.bits q, hTakeProd, rfl⟩
        exact add_le_add hProgram le_rfl
  have hAVal := condK_le_add_condMutualInfo_value D hD p (pairCode v z)
  have hBVal := condK_le_add_condMutualInfo_value D hD (p.take q) p
  have hDVal := condK_le_add_condMutualInfo_value D hD (p.take q) (pairCode v z)
  let a := natCondK D p (pairCode v z)
  let b := natCondK D (p.take q) p
  let d := natCondK D (p.take q) (pairCode v z)
  have hA : a ≤ logSlack cShort k := by
    have h := ENat.toNat_le_of_le_natCast hShortest
    simpa [a, natCondK] using h
  have hB : b ≤ (Nat.bits q).length + cTake := by
    have h := ENat.toNat_le_of_le_natCast hTakeBound
    simpa [b, natCondK] using h
  have hB' : b ≤ (Nat.bits k).length + cTake := by
    exact hB.trans (Nat.add_le_add_right (length_natBits_mono hq) cTake)
  have hArg : a + b + 1 ≤ (cShort + 1) * k + (cShort + cTake + 1) := by
    calc
      a + b + 1 ≤ logSlack cShort k + (Nat.bits k).length + cTake + 1 := by omega
      _ ≤ cShort * k + cShort + (Nat.bits k).length + cTake + 1 := by
        have hLogLinear := logSlack_le_self_linear cShort k
        omega
      _ ≤ (cShort + 1) * k + (cShort + cTake + 1) := by
        rw [Nat.add_mul]
        have hBits := length_natBits_le k
        omega
  have hArgFold : logSlack cChain (a + b + 1) ≤ logSlack cFold k :=
    hFold k (a + b + 1) hArg
  have hFoldAll :
      logSlack cShort k + ((Nat.bits k).length + cTake) + logSlack cFold k ≤
        logSlack C k := by
    unfold logSlack
    dsimp [C]
    nlinarith [Nat.zero_le (cTake * (Nat.bits k).length),
      Nat.zero_le (cFold * (Nat.bits k).length)]
  have hChainInst : d ≤ a + b + logSlack cChain (a + b + 1) := by
    exact hChain (pairCode v z) (p.take q) p a b d hAVal hBVal hDVal
  have hFinal : d ≤ logSlack C k := by
    calc
      d ≤ a + b + logSlack cChain (a + b + 1) := hChainInst
      _ ≤ logSlack cShort k + ((Nat.bits k).length + cTake) +
          logSlack cFold k := by omega
      _ ≤ logSlack C k := hFoldAll
  exact ⟨p, hpLength, hpProduces, hFinal⟩

/-- Search for
a shortest description of `v` given `z` and retain its first `q` bits.  The retained prefix has
complexity `q ± O(log M)` given `z`, and it can be recovered from `(v,z)` using `O(log M)` bits. -/
private theorem theorem2_search_prefix
    (D : Map) (hD : isOptimalConditional D) (c₀ : ℕ) :
    ∃ c : ℕ, ∀ (v z : BitString) (q k M : ℕ),
      k = natCondK D v z →
      q ≤ k →
      k ≤ 2 * M + logSlack c₀ M →
      ∃ v₀ : BitString,
        q ≤ natCondK D v₀ z + logSlack c M ∧
        natCondK D v₀ z ≤ q + logSlack c M ∧
        natCondK D v₀ (pairCode v z) ≤ logSlack c M := by
  obtain ⟨cLower, hLower⟩ :=
    theorem2_lower_bound D hD
  obtain ⟨cSearch, hSearch⟩ :=
    theorem2_search D hD
  obtain ⟨cLowerFold, hLowerFold⟩ :=
    logSlack_absorb_of_le_linear cLower (c₀ + 2) c₀
  obtain ⟨cSearchFold, hSearchFold⟩ :=
    logSlack_absorb_of_le_linear cSearch (c₀ + 2) c₀
  obtain ⟨cPlain, hPlain⟩ := plainK_le_length D hD
  obtain ⟨cCond, hCond⟩ := condK_le_plainK D hD
  let cUpper := cPlain + cCond
  let c := cUpper + cLowerFold + cSearchFold
  have hcLower : cLowerFold ≤ c := by dsimp [c]; omega
  have hcSearch : cSearchFold ≤ c := by dsimp [c]; omega
  have hcUpper : cUpper ≤ c := by dsimp [c]; omega
  refine ⟨c, ?_⟩
  intro v z q k M hk hq hkM
  have hkBound : k ≤ (c₀ + 2) * M + c₀ := by
    calc
      k ≤ 2 * M + logSlack c₀ M := hkM
      _ ≤ 2 * M + (c₀ * M + c₀) :=
        Nat.add_le_add_left (logSlack_le_self_linear c₀ M) _
      _ = (c₀ + 2) * M + c₀ := by rw [Nat.add_mul]; omega
  obtain ⟨p, hpLength, hpProduces, hpRecover⟩ := hSearch v z q k hk hq
  let v₀ := p.take q
  have hv₀Length : v₀.length ≤ q := by
    simp [v₀, List.length_take]
  have hLower₀ := hLower v z p q k hk hq hpLength hpProduces
  have hLower₁ : q ≤ natCondK D v₀ z + logSlack cLowerFold M := by
    calc
      q ≤ natCondK D (p.take q) z + logSlack cLower k := hLower₀
      _ ≤ natCondK D (p.take q) z + logSlack cLowerFold M :=
        Nat.add_le_add_left (hLowerFold M k hkBound) _
  have hLower₂ : q ≤ natCondK D v₀ z + logSlack c M := by
    calc
      q ≤ natCondK D v₀ z + logSlack cLowerFold M := hLower₁
      _ ≤ natCondK D v₀ z + logSlack c M :=
        Nat.add_le_add_left (logSlack_mono_left hcLower M) _
  have hPlainBudget : plainK D v₀ ≤ ((q + cPlain : ℕ) : ℕ∞) := by
    calc
      plainK D v₀ ≤ (programLength v₀ : ℕ∞) + cPlain := hPlain v₀
      _ ≤ (q : ℕ∞) + cPlain := by
        gcongr
      _ = ((q + cPlain : ℕ) : ℕ∞) := by push_cast; rfl
  have hCondBudget : condK D v₀ z ≤ ((q + cUpper : ℕ) : ℕ∞) := by
    calc
      condK D v₀ z ≤ plainK D v₀ + cCond := hCond v₀ z
      _ ≤ ((q + cPlain : ℕ) : ℕ∞) + cCond := add_le_add hPlainBudget le_rfl
      _ = ((q + cUpper : ℕ) : ℕ∞) := by
        simp [cUpper, Nat.cast_add, add_assoc]
  have hCondNat : natCondK D v₀ z ≤ q + cUpper :=
    ENat.toNat_le_of_le_natCast hCondBudget
  have hcUnder : c ≤ logSlack c M := by
    unfold logSlack
    exact Nat.le_add_left _ _
  have hUpper : natCondK D v₀ z ≤ q + logSlack c M := by
    calc
      natCondK D v₀ z ≤ q + cUpper := hCondNat
      _ ≤ q + logSlack c M := Nat.add_le_add_left (hcUpper.trans hcUnder) _
  have hSearch₁ : natCondK D v₀ (pairCode v z) ≤ logSlack cSearchFold M := by
    exact (hpRecover.trans (hSearchFold M k hkBound))
  have hSearch₂ : natCondK D v₀ (pairCode v z) ≤ logSlack c M :=
    hSearch₁.trans (logSlack_mono_left hcSearch M)
  exact ⟨v₀, hLower₂, hUpper, hSearch₂⟩

/-- Compose a
short description of the prefix from `(v,z)` with a short description of `v` from `(x,z)`. -/
private theorem theorem2_transfer_context
    (D : Map) (hD : isOptimalConditional D) (c₀ : ℕ) :
    ∃ c : ℕ, ∀ (x v z w : BitString) (M t : ℕ),
      natCondK D w (pairCode v z) ≤ logSlack c₀ M →
      natCondK D v (pairCode x z) ≤ t →
      t ≤ M →
      natCondK D w (pairCode x z) ≤ t + logSlack c M := by
  obtain ⟨cPair, hPair⟩ := Kolmogorov.condK_pair_le_add D hD
  obtain ⟨cSelf, hSelf⟩ := Kolmogorov.condK_self D hD
  let contextToOracle : BitString → BitString := fun p =>
    pairCode (decodeFirst p) (decodeSecond (decodeSecond p))
  have hContextToOracle : Computable contextToOracle := by
    change Computable
      (fun p : BitString => pairCode (decodeFirst p) (decodeSecond (decodeSecond p)))
    have hPair : Computable₂ (fun a b : BitString => pairCode a b) := pairCode_computable
    exact hPair.comp decodeFirst_computable
      (decodeSecond_computable.comp decodeSecond_computable)
  obtain ⟨cContext, hContext⟩ :=
    Kolmogorov.condK_cond_map_le D hD contextToOracle hContextToOracle
  obtain ⟨cChain, hChain⟩ := Kolmogorov.condK_chain_upper_values D hD
  obtain ⟨cPairFold, hPairFold⟩ :=
    logSlack_linear_bound cPair 1 (cSelf + 1)
  obtain ⟨cChainFold, hChainFold⟩ :=
    logSlack_linear_bound cChain (cPair + 1 + c₀)
      (cSelf + cPair * (cSelf + 1) + cPair + c₀ + cContext + 1)
  let c := cSelf + cContext + cPairFold + c₀ + cChainFold
  refine ⟨c, ?_⟩
  intro x v z w M t hw hv ht
  let ctx := pairCode x z
  let mid := pairCode v ctx
  let kV := natCondK D v ctx
  let kSelf := natCondK D ctx ctx
  let kMid := natCondK D mid ctx
  let kWmid := natCondK D w mid
  let kW := natCondK D w ctx
  have hVValue := condK_le_add_condMutualInfo_value D hD v ctx
  have hSelfValue := condK_le_add_condMutualInfo_value D hD ctx ctx
  have hMidValue := condK_le_add_condMutualInfo_value D hD mid ctx
  have hWmidValue := condK_le_add_condMutualInfo_value D hD w mid
  have hWValue := condK_le_add_condMutualInfo_value D hD w ctx
  have hSelfNat : kSelf ≤ cSelf := by
    have h := hSelf ctx
    rw [hSelfValue] at h
    exact_mod_cast h
  have hPairBound : kMid ≤ kV + kSelf + logSlack cPair (kV + kSelf + 1) := by
    have h := hPair v ctx ctx kV kSelf hVValue hSelfValue
    rw [hMidValue] at h
    exact_mod_cast h
  have hVt : kV ≤ t := by simpa [kV, ctx] using hv
  have hPairArg : kV + kSelf + 1 ≤ M + cSelf + 1 := by omega
  have hPairSlack : logSlack cPair (kV + kSelf + 1) ≤ logSlack cPairFold M := by
    calc
      logSlack cPair (kV + kSelf + 1) ≤ logSlack cPair (M + cSelf + 1) :=
        logSlack_mono_right cPair hPairArg
      _ = logSlack cPair (1 * M + (cSelf + 1)) := by
        congr 1
        omega
      _ ≤ logSlack cPairFold M := hPairFold M
  have hMidT : kMid ≤ t + cSelf + logSlack cPairFold M := by
    calc
      kMid ≤ kV + kSelf + logSlack cPair (kV + kSelf + 1) := hPairBound
      _ ≤ t + cSelf + logSlack cPairFold M := by omega
  have hContextMid : contextToOracle mid = pairCode v z := by
    change pairCode (decodeFirst (pairCode v ctx))
      (decodeSecond (decodeSecond (pairCode v ctx))) = pairCode v z
    simp only [decodeFirst_pairCode, decodeSecond_pairCode, ctx]
  have hContextNat : kWmid ≤ natCondK D w (pairCode v z) + cContext := by
    have h := hContext w mid
    rw [hContextMid, hWmidValue,
      condK_le_add_condMutualInfo_value D hD w (pairCode v z)] at h
    exact_mod_cast h
  have hWmidBound : kWmid ≤ logSlack c₀ M + cContext := by
    exact hContextNat.trans (Nat.add_le_add_right hw cContext)
  have hWmidLinear : kWmid ≤ c₀ * M + c₀ + cContext := by
    calc
      kWmid ≤ logSlack c₀ M + cContext := hWmidBound
      _ ≤ (c₀ * M + c₀) + cContext := by
        exact Nat.add_le_add_right (logSlack_le_self_linear c₀ M) cContext
  have hMidLinear : kMid ≤ (cPair + 1) * M +
      (cSelf + cPair * (cSelf + 1) + cPair) := by
    calc
      kMid ≤ kV + kSelf + logSlack cPair (kV + kSelf + 1) := hPairBound
      _ ≤ M + cSelf + logSlack cPair (M + cSelf + 1) := by
        have hFirst : kV + kSelf ≤ M + cSelf := by omega
        exact Nat.add_le_add hFirst (logSlack_mono_right cPair hPairArg)
      _ ≤ M + cSelf + (cPair * (M + cSelf + 1) + cPair) := by
        exact Nat.add_le_add_left
          (logSlack_le_self_linear cPair (M + cSelf + 1)) (M + cSelf)
      _ = (cPair + 1) * M + (cSelf + cPair * (cSelf + 1) + cPair) := by ring
  have hChainArg : kMid + kWmid + 1 ≤
      (cPair + 1 + c₀) * M +
        (cSelf + cPair * (cSelf + 1) + cPair + c₀ + cContext + 1) := by
    calc
      kMid + kWmid + 1 ≤
          ((cPair + 1) * M + (cSelf + cPair * (cSelf + 1) + cPair)) +
            (c₀ * M + c₀ + cContext) + 1 := by omega
      _ = (cPair + 1 + c₀) * M +
          (cSelf + cPair * (cSelf + 1) + cPair + c₀ + cContext + 1) := by ring
  have hChainSlack : logSlack cChain (kMid + kWmid + 1) ≤ logSlack cChainFold M := by
    calc
      logSlack cChain (kMid + kWmid + 1) ≤
          logSlack cChain
            ((cPair + 1 + c₀) * M +
              (cSelf + cPair * (cSelf + 1) + cPair + c₀ + cContext + 1)) :=
        logSlack_mono_right cChain hChainArg
      _ ≤ logSlack cChainFold M := hChainFold M
  have hSlack : logSlack cPairFold M + logSlack c₀ M + logSlack cChainFold M +
      cSelf + cContext ≤ logSlack c M := by
    have hSelfSlack : cSelf ≤ logSlack cSelf M := by
      unfold logSlack
      omega
    have hContextSlack : cContext ≤ logSlack cContext M := by
      unfold logSlack
      omega
    have heq : logSlack cPairFold M + logSlack c₀ M + logSlack cChainFold M +
        logSlack cSelf M + logSlack cContext M = logSlack c M := by
      dsimp [c]
      unfold logSlack
      ring
    calc
      logSlack cPairFold M + logSlack c₀ M + logSlack cChainFold M + cSelf + cContext
          ≤ logSlack cPairFold M + logSlack c₀ M + logSlack cChainFold M +
            logSlack cSelf M + logSlack cContext M := by omega
      _ = logSlack c M := heq
  have hChainNat : kW ≤ kMid + kWmid + logSlack cChain (kMid + kWmid + 1) :=
    hChain ctx w mid kMid kWmid kW hMidValue hWmidValue hWValue
  calc
    kW ≤ kMid + kWmid + logSlack cChain (kMid + kWmid + 1) := hChainNat
    _ ≤ t + logSlack c M := by omega

/-- Cut the extracted
string down to about `q` bits of complexity given `z`.  If `K(v | z) ≥ q` and `K(v | xᵢ, z) ≤ t`,
take `v₀` the first `q` bits of a shortest description of `v` given `z` (found by searching all
programs of length `K(v | z)` for `v` given `z`); then `K(v₀ | z) = q ± O(log M)` and
`K(v₀ | xᵢ, z) ≤ t + O(log M)`, using `K(v | z) ≤ 2M + O(log M)`. -/
theorem theorem2_cut (D : Map)
    (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ (x₁ x₂ z : BitString) (q t M : ℕ),
      M = natK D (pairCode (pairCode x₁ x₂) z) →
      CommonInfoExtractableRel D x₁ x₂ z q t →
      t ≤ M →
      ∃ v : BitString,
        q ≤ natCondK D v z + logSlack c M ∧
        natCondK D v z ≤ q + logSlack c M ∧
        natCondK D v (pairCode x₁ z) ≤ t + logSlack c M ∧
        natCondK D v (pairCode x₂ z) ≤ t + logSlack c M := by
  obtain ⟨cBound, hBound⟩ :=
    theorem2_bound_original D hD
  obtain ⟨cPrefix, hPrefix⟩ :=
    theorem2_search_prefix D hD cBound
  obtain ⟨cTransfer, hTransfer⟩ :=
    theorem2_transfer_context D hD cPrefix
  let c := max cPrefix cTransfer
  have hcPrefix : cPrefix ≤ c := Nat.le_max_left _ _
  have hcTransfer : cTransfer ≤ c := Nat.le_max_right _ _
  refine ⟨c, ?_⟩
  intro x₁ x₂ z q t M hM hExtract ht
  obtain ⟨v, hqv, hv₁, hv₂⟩ := hExtract
  have hkv := hBound x₁ x₂ z v t M hM hv₁ ht
  obtain ⟨v₀, hvq, hvz, hvctx⟩ :=
    hPrefix v z q (natCondK D v z) M rfl hqv hkv
  have hv₁' := hTransfer x₁ v z v₀ M t hvctx hv₁ ht
  have hv₂' := hTransfer x₂ v z v₀ M t hvctx hv₂ ht
  refine ⟨v₀, ?_, ?_, ?_, ?_⟩
  · exact hvq.trans (Nat.add_le_add_left
      (logSlack_mono_left hcPrefix M) (natCondK D v₀ z))
  · exact hvz.trans (Nat.add_le_add_left
      (logSlack_mono_left hcPrefix M) q)
  · exact hv₁'.trans (Nat.add_le_add_left (logSlack_mono_left hcTransfer M) t)
  · exact hv₂'.trans (Nat.add_le_add_left (logSlack_mono_left hcTransfer M) t)

/-- A conditional description of `v` from `(x₁,z)` of length at most `t + O(log M)`, with
`t ≤ M`, gives a linear bound in `M` for the joint complexity of `(v,z,x₁,x₂)`. -/
theorem theorem2_total_complexity_budget
    (D : Map) (hD : isOptimalConditional D) (c₀ : ℕ) :
    ∃ b : ℕ, ∀ (x₁ x₂ z v : BitString) (t M : ℕ),
      M = natK D (pairCode (pairCode x₁ x₂) z) →
      natCondK D v (pairCode x₁ z) ≤ t + logSlack c₀ M →
      t ≤ M →
      natK D (tupleCode (Fin.append ![v, z] ![x₁, x₂])) ≤ 5 * M + b := by
  let s : BitString → BitString := fun a =>
    pairCode (decodeFirst (decodeFirst a)) (decodeSecond a)
  have hs : Computable s := by
    dsimp [s]
    exact Computable₂.comp pairCode_computable
      (decodeFirst_computable.comp decodeFirst_computable) decodeSecond_computable
  obtain ⟨cCtx, hCtx⟩ := condK_cond_map_le D hD s hs
  obtain ⟨cPair, hPair⟩ := plainK_pair_le_add_two_log_add_condK D hD
  let F : BitString → BitString := fun a => listCode
    [decodeSecond a, decodeSecond (decodeFirst a),
      decodeFirst (decodeFirst (decodeFirst a)),
      decodeSecond (decodeFirst (decodeFirst a))]
  have hF : Computable F := by
    dsimp [F]
    have hv : Primrec (fun a : BitString => decodeSecond a) :=
      CodedFiniteDistribution.decodeSecond_primrec
    have hz : Primrec (fun a : BitString => decodeSecond (decodeFirst a)) :=
      CodedFiniteDistribution.decodeSecond_primrec.comp
        CodedFiniteDistribution.decodeFirst_primrec
    have hx₁ : Primrec (fun a : BitString =>
        decodeFirst (decodeFirst (decodeFirst a))) :=
      CodedFiniteDistribution.decodeFirst_primrec.comp
        (CodedFiniteDistribution.decodeFirst_primrec.comp
          CodedFiniteDistribution.decodeFirst_primrec)
    have hx₂ : Primrec (fun a : BitString =>
        decodeSecond (decodeFirst (decodeFirst a))) :=
      CodedFiniteDistribution.decodeSecond_primrec.comp
        (CodedFiniteDistribution.decodeFirst_primrec.comp
          CodedFiniteDistribution.decodeFirst_primrec)
    exact listCode_computable.comp
      ((Primrec.list_cons.comp hv
        (Primrec.list_cons.comp hz
          (Primrec.list_cons.comp hx₁
            (Primrec.list_cons.comp hx₂ (Primrec.const []))))).to_comp)
  obtain ⟨cMap, hMap⟩ := plainK_map_le D hD F hF
  obtain ⟨bSlack, hSlack⟩ := Kolmogorov.logSlack_le_add_const c₀
  refine ⟨bSlack + cCtx + cPair + cMap, ?_⟩
  intro x₁ x₂ z v t M hM hv ht
  let w := pairCode (pairCode x₁ x₂) z
  have hSCode : s w = pairCode x₁ z := by
    simp [s, w, decodeFirst_pairCode, decodeSecond_pairCode]
  have hCtxRaw := hCtx v w
  rw [hSCode] at hCtxRaw
  have hCtxNat : natCondK D v w ≤ natCondK D v (pairCode x₁ z) + cCtx := by
    rw [← ENat.natCast_toNat (condK_ne_top_of_optimal D hD v w),
      ← ENat.natCast_toNat (condK_ne_top_of_optimal D hD v (pairCode x₁ z))] at hCtxRaw
    exact_mod_cast hCtxRaw
  have hCondBound : natCondK D v w ≤ t + logSlack c₀ M + cCtx := by omega
  have hPairNat : natK D (pairCode w v) ≤
      M + natCondK D v w + 2 * Nat.log 2 M + cPair := by
    have hh := hPair w v
    change plainK D (pairCode w v) ≤ plainK D w + condK D v w +
      ((2 * Nat.log 2 (cVal D w) + cPair : ℕ) : ℕ∞) at hh
    rw [← ENat.natCast_toNat (plainK_ne_top D hD (pairCode w v)),
      ← ENat.natCast_toNat (plainK_ne_top D hD w),
      ← ENat.natCast_toNat (condK_ne_top_of_optimal D hD v w)] at hh
    have hNat : natK D (pairCode w v) ≤
        natK D w + natCondK D v w + (2 * Nat.log 2 (cVal D w) + cPair) := by
      exact_mod_cast hh
    have hcv : cVal D w = natK D w := rfl
    rw [hcv, ← hM] at hNat
    simpa [Nat.add_assoc] using hNat
  let x : Fin 2 → BitString := ![v, z]
  let y : Fin 2 → BitString := ![x₁, x₂]
  have hList : List.ofFn (Fin.append x y) = [v, z, x₁, x₂] := by
    rw [List.ofFn_fin_append]
    simp [x, y]
  have hFCode : F (pairCode w v) = tupleCode (Fin.append x y) := by
    simp only [F, w, decodeFirst_pairCode, decodeSecond_pairCode]
    rw [tupleCode, hList]
  have hOutput : natK D (tupleCode (Fin.append x y)) ≤ natK D (pairCode w v) + cMap := by
    have hh := hMap (pairCode w v)
    rw [hFCode] at hh
    rw [← ENat.natCast_toNat (plainK_ne_top D hD (tupleCode (Fin.append x y))),
      ← ENat.natCast_toNat (plainK_ne_top D hD (pairCode w v))] at hh
    exact_mod_cast hh
  have hlog : Nat.log 2 M ≤ M := by
    exact (commonInfo_le_mutualInfo_natLog_le_bits M).trans (length_natBits_le M)
  have hSlackM := hSlack M
  have hCore : natK D (tupleCode (Fin.append x y)) ≤
      5 * M + (bSlack + cCtx + cPair + cMap) := by
    calc
      natK D (tupleCode (Fin.append x y)) ≤ natK D (pairCode w v) + cMap := hOutput
      _ ≤ M + natCondK D v w + 2 * Nat.log 2 M + cPair + cMap := by omega
      _ ≤ 5 * M + (bSlack + cCtx + cPair + cMap) := by omega
  simpa [x, y] using hCore

/-- The strong typization at logarithmic scale in the joint tuple complexity has cardinality at
least the indicated power of two, up to the logarithmic loss in the conditional complexity. -/
theorem theorem2_typization_cardinality
    (D : Map) (hD : isOptimalConditional D) :
    ∃ C c : ℕ, ∀ (x : Fin 2 → BitString) (y : Fin 2 → BitString),
      2 ^ (natCondK D (tupleCode x) (tupleCode y) -
        (logSlack c (natK D (tupleCode (Fin.append x y))) + 1)) ≤
        (strongTypization D (logSlack C (natK D (tupleCode (Fin.append x y)))) x y).ncard := by
  obtain ⟨c₁, h₁⟩ := lemma1 D hD 2 2
  obtain ⟨C, h₂⟩ := lemma2 D hD 2 2
  refine ⟨C, c₁, fun x y => ?_⟩
  let T := typization D x y
  let N := natK D (tupleCode (Fin.append x y))
  let k := natCondK D (tupleCode x) (tupleCode y)
  let s := logSlack c₁ N
  let S := strongTypization D (logSlack C N) x y
  let q := k - (s + 1)
  have hlow : 2 ^ k ≤ T.ncard * 2 ^ s := by
    simpa [T, N, k, s] using (h₁ x y).2.2
  have hhalf : T.ncard < 2 * S.ncard := by
    simpa [T, N, S] using h₂ x y
  have hxT : x ∈ T := by
    change ExtProfileLe D (Fin.append x y) (Fin.append x y)
    intro V W hV hdis
    exact le_rfl
  have hTpos : 0 < T.ncard :=
    Nat.pos_of_ne_zero (Set.ncard_ne_zero_of_mem hxT (h₁ x y).1)
  by_cases hq : q = 0
  · have hSpos : 0 < S.ncard := by omega
    have hSge : 1 ≤ S.ncard := by omega
    have hq' : k - (s + 1) = 0 := by simpa [q] using hq
    rw [hq']
    simpa using hSge
  · have hqpos : 0 < q := Nat.pos_of_ne_zero hq
    have hk : k = q + (s + 1) := by
      dsimp [q]
      omega
    have hpow_eq : 2 ^ (q + 1) * 2 ^ s = 2 ^ k := by
      calc
        2 ^ (q + 1) * 2 ^ s = 2 ^ q * 2 * 2 ^ s := by rw [Nat.pow_succ]
        _ = 2 ^ q * (2 ^ s * 2) := by ring
        _ = 2 ^ q * 2 ^ (s + 1) := by rw [Nat.pow_succ]
        _ = 2 ^ (q + (s + 1)) := (Nat.pow_add 2 q (s + 1)).symm
        _ = 2 ^ k := by rw [hk]
    have hmul : 2 ^ (q + 1) * 2 ^ s ≤ T.ncard * 2 ^ s := by
      rw [hpow_eq]
      exact hlow
    have hpow_le : 2 ^ (q + 1) ≤ T.ncard :=
      Nat.le_of_mul_le_mul_right hmul (Nat.pow_pos (by decide : 0 < 2))
    have hmul' : 2 ^ q * 2 ≤ S.ncard * 2 := by
      rw [Nat.pow_succ] at hpow_le
      omega
    have hresult : 2 ^ q ≤ S.ncard :=
      Nat.le_of_mul_le_mul_right hmul' (by decide : 0 < 2)
    simpa [q] using hresult

/-- Conditional complexity using fixed pair codes is bounded by that using the corresponding
two-coordinate tuple codes, up to a uniform additive constant. -/
theorem theorem2_pair_code_conversion
    (D : Map) (hD : isOptimalConditional D) :
    ∃ d : ℕ, ∀ (x₁ x₂ v z : BitString),
      natCondK D (pairCode v z) (pairCode x₁ x₂) ≤
        natCondK D (tupleCode ![v, z]) (tupleCode ![x₁, x₂]) + d := by
  let toTuple : BitString → BitString := fun w =>
    listCode [decodeFirst w, decodeSecond w]
  let toPair : BitString → BitString := fun w =>
    pairCode ((decodeListCode w).getD 0 []) ((decodeListCode w).getD 1 [])
  have hTuple : Computable toTuple := by
    dsimp [toTuple]
    exact listCode_computable.comp
      ((Primrec.list_cons.comp CodedFiniteDistribution.decodeFirst_primrec
        (Primrec.list_cons.comp CodedFiniteDistribution.decodeSecond_primrec
          (Primrec.const []))).to_comp)
  have hPair : Computable toPair := by
    dsimp [toPair]
    have hfirst : Primrec (fun w : BitString => (decodeListCode w).getD 0 []) :=
      (Primrec.list_getD ([] : BitString)).comp decodeListCode_primrec (Primrec.const 0)
    have hsecond : Primrec (fun w : BitString => (decodeListCode w).getD 1 []) :=
      (Primrec.list_getD ([] : BitString)).comp decodeListCode_primrec (Primrec.const 1)
    exact Computable₂.comp pairCode_computable hfirst.to_comp hsecond.to_comp
  obtain ⟨cOut, hOut⟩ := condK_map_le D hD toPair hPair
  obtain ⟨cCtx, hCtx⟩ := condK_cond_map_le D hD toTuple hTuple
  refine ⟨cOut + cCtx, fun x₁ x₂ v z => ?_⟩
  have hTupleX : toTuple (pairCode x₁ x₂) = tupleCode ![x₁, x₂] := by
    simp [toTuple, tupleCode, decodeFirst_pairCode, decodeSecond_pairCode]
  have hPairV : toPair (tupleCode ![v, z]) = pairCode v z := by
    change pairCode ((decodeListCode (listCode [v, z])).getD 0 [])
      ((decodeListCode (listCode [v, z])).getD 1 []) = pairCode v z
    rw [decodeListCode_listCode]
    simp
  have h1 := hOut (tupleCode ![v, z]) (pairCode x₁ x₂)
  have h2 := hCtx (tupleCode ![v, z]) (pairCode x₁ x₂)
  rw [hPairV] at h1
  rw [hTupleX] at h2
  have hnat1 : natCondK D (pairCode v z) (pairCode x₁ x₂) ≤
      natCondK D (tupleCode ![v, z]) (pairCode x₁ x₂) + cOut := by
    rw [← ENat.natCast_toNat (condK_ne_top_of_optimal D hD (pairCode v z) (pairCode x₁ x₂)),
      ← ENat.natCast_toNat (condK_ne_top_of_optimal D hD (tupleCode ![v, z])
        (pairCode x₁ x₂))] at h1
    exact_mod_cast h1
  have hnat2 : natCondK D (tupleCode ![v, z]) (pairCode x₁ x₂) ≤
      natCondK D (tupleCode ![v, z]) (tupleCode ![x₁, x₂]) + cCtx := by
    rw [← ENat.natCast_toNat (condK_ne_top_of_optimal D hD (tupleCode ![v, z])
        (pairCode x₁ x₂)),
      ← ENat.natCast_toNat (condK_ne_top_of_optimal D hD (tupleCode ![v, z])
        (tupleCode ![x₁, x₂]))] at h2
    exact_mod_cast h2
  omega

end Kolmogorov.Relativization
