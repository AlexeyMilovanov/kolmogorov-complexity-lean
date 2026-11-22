/-
Copyright (c) 2026 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Relativization.CommonInformation.MutualInformationBounds

/-!
# Extraction Index Bounds

This module proves bounds on the amount of common information extractable from two strings,
including the semibunching and oracle replacement results. It formalizes the extraction-index
arguments in Sections 3 and 4 of Muchnik and Romashchenko's paper on relativization.
-/

namespace Kolmogorov.Relativization
open Filter Asymptotics

/-- The logarithmic slack of a number is bounded by a linear function of that number. -/
private lemma theorem2_extracted_amount_bound_logSlack_linear_upper
    (c n : ℕ) : logSlack c n ≤ c * n + 2 * c := by
  have hbits : (Nat.bits n).length ≤ n := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr (Nat.lt_two_pow_self)
  have hmul : c * (Nat.bits n).length ≤ c * n := Nat.mul_le_mul_left c hbits
  unfold logSlack
  omega

/-- Chain-rule bounds for an explicit extracted witness, one for each coordinate. -/
private theorem theorem2_extracted_amount_bound_chain_bounds
    (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ (x₁ x₂ z v : BitString) (q t M : ℕ),
      M = natK D (pairCode (pairCode x₁ x₂) z) →
      q ≤ natCondK D v z →
      natCondK D v (pairCode x₁ z) ≤ t →
      natCondK D v (pairCode x₂ z) ≤ t →
      t ≤ M →
      q ≤ natK D x₁ + t + logSlack c M ∧
        q ≤ natK D x₂ + t + logSlack c M := by
  obtain ⟨cProj₁, hProj₁⟩ := Kolmogorov.plainK_map_le D hD
    (decodeFirst ∘ decodeFirst)
    (decodeFirst_computable.comp decodeFirst_computable)
  obtain ⟨cProj₂, hProj₂⟩ := Kolmogorov.plainK_map_le D hD
    (decodeSecond ∘ decodeFirst)
    (decodeSecond_computable.comp decodeFirst_computable)
  obtain ⟨cCond, hCond⟩ := Kolmogorov.condK_le_plainK D hD
  obtain ⟨cSelf, hSelf⟩ := Kolmogorov.condK_self D hD
  obtain ⟨cPair, hPair⟩ := Kolmogorov.condK_pair_le_add D hD
  obtain ⟨cChain, hChain⟩ := Kolmogorov.condK_chain_upper_values D hD
  let cProj := max cProj₁ cProj₂
  let b := cProj + cCond + cSelf
  let aPair := cPair + 1
  let bPair := b + cPair * (b + 1) + 2 * cPair
  let aChain := aPair + 1
  let bChain := bPair + 1
  obtain ⟨cPairFold, hPairFold⟩ := logSlack_linear_bound cPair 1 (b + 1)
  obtain ⟨cChainFold, hChainFold⟩ :=
    logSlack_linear_bound cChain aChain bChain
  let c := cCond + cSelf + cPairFold + cChainFold
  refine ⟨c, ?_⟩
  intro x₁ x₂ z v q t M hM hq hv₁ hv₂ ht
  let triple := pairCode (pairCode x₁ x₂) z
  have hProjX₁ : natK D x₁ ≤ M + cProj := by
    have h := hProj₁ (pairCode (pairCode x₁ x₂) z)
    have hplain : plainK D x₁ ≤ plainK D triple + (cProj₁ : ℕ∞) := by
      simpa only [Function.comp_apply, decodeFirst_pairCode, decodeSecond_pairCode,
        triple] using h
    have hnat : ((natK D x₁ : ℕ) : ℕ∞) ≤ (M + cProj₁ : ℕ) := by
      calc
        ((natK D x₁ : ℕ) : ℕ∞) = plainK D x₁ :=
          (commonInfo_le_mutualInfo_hasPlainValue D hD x₁).symm
        _ ≤ plainK D triple + (cProj₁ : ℕ∞) := hplain
        _ = (M + cProj₁ : ℕ) := by
          rw [commonInfo_le_mutualInfo_hasPlainValue D hD triple]
          rw [← hM]
          push_cast
          rfl
    have hnat' : natK D x₁ ≤ M + cProj₁ := by exact_mod_cast hnat
    exact hnat'.trans (Nat.add_le_add_left (le_max_left cProj₁ cProj₂) M)
  have hProjX₂ : natK D x₂ ≤ M + cProj := by
    have h := hProj₂ (pairCode (pairCode x₁ x₂) z)
    have hplain : plainK D x₂ ≤ plainK D triple + (cProj₂ : ℕ∞) := by
      simpa only [Function.comp_apply, decodeFirst_pairCode, decodeSecond_pairCode,
        triple] using h
    have hnat : ((natK D x₂ : ℕ) : ℕ∞) ≤ (M + cProj₂ : ℕ) := by
      calc
        ((natK D x₂ : ℕ) : ℕ∞) = plainK D x₂ :=
          (commonInfo_le_mutualInfo_hasPlainValue D hD x₂).symm
        _ ≤ plainK D triple + (cProj₂ : ℕ∞) := hplain
        _ = (M + cProj₂ : ℕ) := by
          rw [commonInfo_le_mutualInfo_hasPlainValue D hD triple]
          rw [← hM]
          push_cast
          rfl
    have hnat' : natK D x₂ ≤ M + cProj₂ := by exact_mod_cast hnat
    exact hnat'.trans (Nat.add_le_add_left (le_max_right cProj₁ cProj₂) M)
  have hSelfNat : natCondK D z z ≤ cSelf := by
    unfold natCondK
    exact ENat.toNat_le_of_le_natCast (hSelf z)
  have hOne (x : BitString) (hv : natCondK D v (pairCode x z) ≤ t)
      (hProj : natK D x ≤ M + cProj) :
      q ≤ natK D x + t + logSlack c M := by
    have hXCond : natCondK D x z ≤ natK D x + cCond := by
      have h := hCond x z
      rw [commonInfo_le_mutualInfo_hasCondValue D hD x z,
        commonInfo_le_mutualInfo_hasPlainValue D hD x] at h
      exact_mod_cast h
    have hXCondBound : natCondK D x z ≤ M + cProj + cCond := by
      exact hXCond.trans (Nat.add_le_add_right hProj cCond)
    have hPairArgs : natCondK D x z + natCondK D z z + 1 ≤ M + b + 1 := by
      dsimp [b]
      omega
    have hPairNat : natCondK D (pairCode x z) z ≤
        natCondK D x z + natCondK D z z +
          logSlack cPair (natCondK D x z + natCondK D z z + 1) := by
      have h := hPair x z z (natCondK D x z) (natCondK D z z)
        (commonInfo_le_mutualInfo_hasCondValue D hD x z)
        (commonInfo_le_mutualInfo_hasCondValue D hD z z)
      unfold natCondK
      exact ENat.toNat_le_of_le_natCast h
    have hPairSlack :
        logSlack cPair (natCondK D x z + natCondK D z z + 1) ≤
          logSlack cPair (M + b + 1) :=
      logSlack_mono_right cPair hPairArgs
    have hPairLoose : natCondK D (pairCode x z) z ≤
        M + b + logSlack cPair (M + b + 1) := by
      calc
        natCondK D (pairCode x z) z ≤
            natCondK D x z + natCondK D z z +
              logSlack cPair (natCondK D x z + natCondK D z z + 1) := hPairNat
        _ ≤ M + b + logSlack cPair (M + b + 1) := by
          have hsum : natCondK D x z + natCondK D z z ≤ M + b := by
            dsimp [b]
            omega
          omega
    have hPairLinear : natCondK D (pairCode x z) z ≤ aPair * M + bPair := by
      calc
        natCondK D (pairCode x z) z ≤ M + b + logSlack cPair (M + b + 1) := hPairLoose
        _ ≤ M + b + (cPair * (M + b + 1) + 2 * cPair) := by
          exact Nat.add_le_add_left
            (theorem2_extracted_amount_bound_logSlack_linear_upper
              cPair (M + b + 1)) _
        _ = aPair * M + bPair := by
          dsimp [aPair, bPair]
          ring
    have hVPair : natCondK D v (pairCode x z) ≤ M := hv.trans ht
    have hChainArgs : natCondK D (pairCode x z) z +
        natCondK D v (pairCode x z) + 1 ≤ aChain * M + bChain := by
      calc
        _ ≤ (aPair * M + bPair) + M + 1 := by
          exact Nat.add_le_add_right (Nat.add_le_add hPairLinear hVPair) 1
        _ = aChain * M + bChain := by
          dsimp [aChain, aPair, bChain, bPair]
          ring
    have hChainSlack :
        logSlack cChain (natCondK D (pairCode x z) z +
          natCondK D v (pairCode x z) + 1) ≤ logSlack cChainFold M := by
      calc
        _ ≤ logSlack cChain (aChain * M + bChain) :=
          logSlack_mono_right cChain hChainArgs
        _ ≤ logSlack cChainFold M := hChainFold M
    have hChainBound : natCondK D v z ≤
        natCondK D (pairCode x z) z + natCondK D v (pairCode x z) +
          logSlack cChainFold M := by
      have h := hChain z v (pairCode x z)
        (natCondK D (pairCode x z) z) (natCondK D v (pairCode x z))
        (natCondK D v z)
        (commonInfo_le_mutualInfo_hasCondValue D hD (pairCode x z) z)
        (commonInfo_le_mutualInfo_hasCondValue D hD v (pairCode x z))
        (commonInfo_le_mutualInfo_hasCondValue D hD v z)
      calc
        natCondK D v z ≤ natCondK D (pairCode x z) z +
            natCondK D v (pairCode x z) +
              logSlack cChain (natCondK D (pairCode x z) z +
                natCondK D v (pairCode x z) + 1) := h
        _ ≤ natCondK D (pairCode x z) z + natCondK D v (pairCode x z) +
            logSlack cChainFold M := by omega
    have hPairFolded : logSlack cPair (M + b + 1) ≤ logSlack cPairFold M := by
      simpa [Nat.one_mul, Nat.add_assoc] using hPairFold M
    have hPairBound : natCondK D (pairCode x z) z ≤
        natCondK D x z + cSelf + logSlack cPairFold M := by
      calc
        natCondK D (pairCode x z) z ≤
            natCondK D x z + natCondK D z z +
              logSlack cPair (natCondK D x z + natCondK D z z + 1) := hPairNat
        _ ≤ natCondK D x z + cSelf + logSlack cPair (M + b + 1) := by omega
        _ ≤ natCondK D x z + cSelf + logSlack cPairFold M := by omega
    have hConst : cCond + cSelf ≤ logSlack (cCond + cSelf) M := by
      unfold logSlack
      omega
    have hSlackEq : logSlack c M =
        logSlack (cCond + cSelf) M + logSlack cPairFold M + logSlack cChainFold M := by
      dsimp [c]
      calc
        logSlack (cCond + cSelf + cPairFold + cChainFold) M =
            logSlack (cCond + cSelf + cPairFold) M + logSlack cChainFold M := by
          simpa [Nat.add_assoc] using
            (logSlack_add_const (cCond + cSelf + cPairFold) cChainFold M).symm
        _ = logSlack (cCond + cSelf) M + logSlack cPairFold M +
            logSlack cChainFold M := by
          rw [(logSlack_add_const (cCond + cSelf) cPairFold M).symm]
    have hSlackSum : cCond + cSelf + logSlack cPairFold M +
        logSlack cChainFold M ≤ logSlack c M := by
      rw [hSlackEq]
      omega
    calc
      q ≤ natCondK D v z := hq
      _ ≤ natCondK D (pairCode x z) z + natCondK D v (pairCode x z) +
          logSlack cChainFold M := hChainBound
      _ ≤ natK D x + t +
          (cCond + cSelf + logSlack cPairFold M + logSlack cChainFold M) := by
        have := hPairBound
        omega
      _ ≤ natK D x + t + logSlack c M := by omega
  exact ⟨hOne x₁ hv₁ hProjX₁, hOne x₂ hv₂ hProjX₂⟩

/-- The amount `q` of common information
extractable relative to an oracle is at most `K(xᵢ) + t` and at most `2M`, up to logarithmic
overhead.  (`K(v | z) ≤ K(v | xᵢ, z) + K(xᵢ | z) + O(log M) ≤ t + K(xᵢ) + O(log M)` and
`K(xᵢ) ≤ M + O(1)`.) -/
private theorem theorem2_extracted_amount_bound
    (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ (x₁ x₂ z : BitString) (q t M : ℕ),
      M = natK D (pairCode (pairCode x₁ x₂) z) →
      CommonInfoExtractableRel D x₁ x₂ z q t →
      t ≤ M →
      q ≤ 2 * M + logSlack c M ∧ q ≤ natK D x₁ + t + logSlack c M ∧
        q ≤ natK D x₂ + t + logSlack c M := by
  obtain ⟨cAmount, hAmount⟩ :=
    theorem2_extracted_amount_bound_chain_bounds
      D hD
  obtain ⟨cLarge, hLarge⟩ :=
    theorem2_bound_original D hD
  let c := max cAmount cLarge
  refine ⟨c, ?_⟩
  intro x₁ x₂ z q t M hM hExtract ht
  obtain ⟨v, hq, hv₁, hv₂⟩ := hExtract
  obtain ⟨h₁, h₂⟩ := hAmount x₁ x₂ z v q t M hM hq hv₁ hv₂ ht
  have h₀ : q ≤ 2 * M + logSlack cLarge M := by
    calc
      q ≤ natCondK D v z := hq
      _ ≤ 2 * M + logSlack cLarge M := hLarge x₁ x₂ z v t M hM hv₁ ht
  exact ⟨h₀.trans (Nat.add_le_add_left
      (logSlack_mono_left (le_max_right cAmount cLarge) M) (2 * M)),
    h₁.trans (Nat.add_le_add_left
      (logSlack_mono_left (le_max_left cAmount cLarge) M) (natK D x₁ + t)),
    h₂.trans (Nat.add_le_add_left
      (logSlack_mono_left (le_max_left cAmount cLarge) M) (natK D x₂ + t))⟩

/-- When the error allowance is at least
the input complexity, the empty string is a witness. -/
private theorem theorem2_large_delta
    (D : Map) (hD : isOptimalConditional D) (c₀ : ℕ) :
    ∃ c : ℕ, ∀ (x₁ x₂ : BitString) (q t δ M : ℕ),
      8 * (t + logSlack 1 M) ≤ δ →
      M ≤ δ →
      q ≤ 2 * M + logSlack c₀ M →
      ∃ w : BitString,
        q ≤ natK D w + 2 * δ + logSlack c M ∧
        natCondK D w x₁ ≤ 3 * δ + logSlack c M ∧
        natCondK D w x₂ ≤ 3 * δ + logSlack c M ∧
        natK D w ≤ c * (M + 1) := by
  obtain ⟨cCond, hCond⟩ := condK_le_plainK D hD
  obtain ⟨cLen, hLen⟩ := plainK_le_length D hD
  let c := max c₀ (cCond + cLen + 1)
  have hc₀ : c₀ ≤ c := le_max_left _ _
  have hcb : cCond + cLen ≤ c := by dsimp [c]; omega
  refine ⟨c, ?_⟩
  intro x₁ x₂ q t δ M hδ hM hq
  have hlog₀ : logSlack c₀ M ≤ logSlack c M := logSlack_mono_left hc₀ M
  have hlogLower : c ≤ logSlack c M := by
    unfold logSlack
    omega
  have hEmptyK : natK D [] ≤ cLen := by
    have hh := hLen []
    rw [commonInfo_le_mutualInfo_hasPlainValue D hD []] at hh
    have hh' : natK D [] ≤ ([] : BitString).length + cLen := by
      exact_mod_cast hh
    simpa using hh'
  have hEmpty₁ : natCondK D [] x₁ ≤ cCond + cLen := by
    have hh := hCond [] x₁
    rw [commonInfo_le_mutualInfo_hasCondValue D hD [] x₁,
      commonInfo_le_mutualInfo_hasPlainValue D hD []] at hh
    have hh' : natCondK D [] x₁ ≤ natK D [] + cCond := by
      exact_mod_cast hh
    omega
  have hEmpty₂ : natCondK D [] x₂ ≤ cCond + cLen := by
    have hh := hCond [] x₂
    rw [commonInfo_le_mutualInfo_hasCondValue D hD [] x₂,
      commonInfo_le_mutualInfo_hasPlainValue D hD []] at hh
    have hh' : natCondK D [] x₂ ≤ natK D [] + cCond := by
      exact_mod_cast hh
    omega
  have hKlinear : natK D [] ≤ c * (M + 1) := by
    calc
      natK D [] ≤ c := hEmptyK.trans (by dsimp [c]; omega)
      _ = c * 1 := by simp
      _ ≤ c * (M + 1) := Nat.mul_le_mul_left c (by omega)
  refine ⟨[], ?_, ?_, ?_, hKlinear⟩
  · omega
  · exact hEmpty₁.trans (by omega)
  · exact hEmpty₂.trans (by omega)

/-- The binary length of a valid cover index, with the exponent offset retained additively.
This also covers the index zero and derives the necessary exponent comparison from the
nonempty index range. -/
private theorem theorem2_lemma6_index_aux_length
    (a b cnt i : ℕ) (hi : i < cnt) (hcnt : cnt * 2 ^ a ≤ 2 ^ b) :
    (Nat.bits i).length + a ≤ b := by
  have hp : 0 < 2 ^ a := by positivity
  have hOne : 1 ≤ cnt := by omega
  have hab : a ≤ b := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    calc
      2 ^ a = 1 * 2 ^ a := by simp
      _ ≤ cnt * 2 ^ a := Nat.mul_le_mul_right _ hOne
      _ ≤ 2 ^ b := hcnt
  have hlt : i * 2 ^ a < 2 ^ b :=
    (Nat.mul_lt_mul_of_pos_right hi hp).trans_le hcnt
  have hsplit : 2 ^ b = 2 ^ (b - a) * 2 ^ a := by
    rw [← pow_add, Nat.sub_add_cancel hab]
  rw [hsplit] at hlt
  have hiPow : i < 2 ^ (b - a) := Nat.lt_of_mul_lt_mul_right hlt
  have hsize : (Nat.bits i).length ≤ b - a := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr hiPow
  omega

/-- A fixed partial recursive function of four natural numbers can be run from a code
containing their binary representations.  The first three fields are delimited by `pairCode`;
the last field, the cover index, occurs only once in the code's length. -/
private theorem theorem2_lemma6_index_aux_decode
    (D : Map) (hD : isOptimalConditional D)
    (F : ℕ × ℕ × ℕ × ℕ →. BitString) (hF : Partrec F) :
    ∃ c : ℕ, ∀ (α β γ i : ℕ) (s : BitString), s ∈ F (α, β, γ, i) →
      natCondK D s
        (pairCode (Nat.bits α) (pairCode (Nat.bits β) (pairCode (Nat.bits γ) (Nat.bits i))))
        ≤ c := by
  let dec : BitString → ℕ × ℕ × ℕ × ℕ := fun w =>
    (bitsToNat (decodeFirst w),
      bitsToNat (decodeFirst (decodeSecond w)),
      bitsToNat (decodeFirst (decodeSecond (decodeSecond w))),
      bitsToNat (decodeSecond (decodeSecond (decodeSecond w))))
  have hdec : Computable dec := by
    have h₁ := bitsToNat_primrec.to_comp.comp decodeFirst_computable
    have h₂ := bitsToNat_primrec.to_comp.comp
      (decodeFirst_computable.comp decodeSecond_computable)
    have h₃ := bitsToNat_primrec.to_comp.comp
      (decodeFirst_computable.comp (decodeSecond_computable.comp decodeSecond_computable))
    have h₄ := bitsToNat_primrec.to_comp.comp
      (decodeSecond_computable.comp (decodeSecond_computable.comp decodeSecond_computable))
    exact h₁.pair (h₂.pair (h₃.pair h₄))
  let E : Map := fun pr => F (dec pr.2)
  have hE : isDecompressor E := hF.comp (hdec.comp Computable.snd)
  obtain ⟨c, hc⟩ := hD.2 E hE
  refine ⟨c, fun α β γ i s hs => ?_⟩
  let w := pairCode (Nat.bits α)
    (pairCode (Nat.bits β) (pairCode (Nat.bits γ) (Nat.bits i)))
  have hprod : produces E [] w s := by
    simpa only [produces, E, w, dec, decodeFirst_pairCode, decodeSecond_pairCode,
      bitsToNat_bits] using hs
  have hzero : condK E s w ≤ (0 : ℕ∞) := sInf_le ⟨[], hprod, rfl⟩
  have hbound : condK D s w ≤ (c : ℕ∞) := by
    calc
      condK D s w ≤ condK E s w + (c : ℕ∞) := hc s w
      _ ≤ 0 + (c : ℕ∞) := add_le_add hzero le_rfl
      _ = (c : ℕ∞) := zero_add _
  exact ENat.toNat_le_of_le_natCast hbound

/-- Applying the plain chain rules to `(v', z')` and `(v'', z'')` bounds their joint complexity
by the complexities of `z'`, `z''`, and the regrouped conditional pair, up to logarithmic terms. -/
theorem theorem2_regrouped_chain_rule
    (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ (v' z' v'' z'' : BitString),
      natK D (pairCode v' z') + natCondK D (pairCode v'' z'') (pairCode v' z') ≤
        natK D z' + natK D z'' +
          natCondK D (pairCode v' v'') (pairCode z' z'') +
          logSlack c (natK D (pairCode (pairCode v' z') (pairCode v'' z'')) + 1) +
          logSlack c (natK D (pairCode (pairCode z' z'') (pairCode v' v'')) + 1) +
          logSlack c (natK D (pairCode z' z'') + 1) + c := by
  obtain ⟨cLower, hLower⟩ := pairPlainK_chain_lower_values D hD
  obtain ⟨cUpper, hUpper⟩ := pairPlainK_chain_upper_values D hD
  obtain ⟨cCond, hCond⟩ := condK_le_plainK D hD
  let regroup : BitString → BitString := fun w =>
    pairCode
      (pairCode (decodeFirst (decodeSecond w)) (decodeFirst (decodeFirst w)))
      (pairCode (decodeSecond (decodeSecond w)) (decodeSecond (decodeFirst w)))
  have hRegroup : Computable regroup := by
    apply Computable.of_eq
      (pairCode_computable.comp
        ((pairCode_computable.comp
            ((decodeFirst_computable.comp decodeSecond_computable).pair
              (decodeFirst_computable.comp decodeFirst_computable))).pair
          (pairCode_computable.comp
            ((decodeSecond_computable.comp decodeSecond_computable).pair
              (decodeSecond_computable.comp decodeFirst_computable)))))
    intro w
    rfl
  obtain ⟨cMap, hMap⟩ := plainK_map_le D hD regroup hRegroup
  let c := max cLower (max cUpper (cMap + cCond))
  refine ⟨c, ?_⟩
  intro v' z' v'' z''
  let a := pairCode v' z'
  let b := pairCode v'' z''
  let ab := pairCode a b
  let zPair := pairCode z' z''
  let vPair := pairCode v' v''
  let regrouped := pairCode zPair vPair
  have ha : HasPlainComplexityValue D a (natK D a) :=
    commonInfo_le_mutualInfo_hasPlainValue D hD a
  have hb : HasPlainConditionalComplexityValue D b a (natCondK D b a) :=
    condK_le_add_condMutualInfo_value D hD b a
  have hab : HasPlainComplexityValue D ab (natK D ab) :=
    commonInfo_le_mutualInfo_hasPlainValue D hD ab
  have hLower' := hLower a b (natK D a) (natCondK D b a) (natK D ab) ha hb hab
  have hz' : HasPlainComplexityValue D z' (natK D z') :=
    commonInfo_le_mutualInfo_hasPlainValue D hD z'
  have hz'' : HasPlainComplexityValue D z'' (natK D z'') :=
    commonInfo_le_mutualInfo_hasPlainValue D hD z''
  have hzCond : HasPlainConditionalComplexityValue D z'' z' (natCondK D z'' z') :=
    condK_le_add_condMutualInfo_value D hD z'' z'
  have hzPair : HasPlainComplexityValue D zPair (natK D zPair) :=
    commonInfo_le_mutualInfo_hasPlainValue D hD zPair
  have hvPair : HasPlainComplexityValue D vPair (natK D vPair) :=
    commonInfo_le_mutualInfo_hasPlainValue D hD vPair
  have hRegrouped : HasPlainComplexityValue D regrouped (natK D regrouped) :=
    commonInfo_le_mutualInfo_hasPlainValue D hD regrouped
  have hZChain := hUpper z' z'' (natK D z') (natCondK D z'' z')
    (natK D zPair) hz' hzCond hzPair
  have hPairChain := hUpper zPair vPair (natK D zPair)
    (natCondK D vPair zPair) (natK D regrouped) hzPair
    (condK_le_add_condMutualInfo_value D hD vPair zPair) hRegrouped
  have hRegroupMap := hMap regrouped
  have hRegroupMapNat : natK D ab ≤ natK D regrouped + cMap := by
    have hRegroupEq : regroup regrouped = ab := by
      simp only [regroup, regrouped, zPair, vPair, decodeFirst_pairCode,
        decodeSecond_pairCode, ab, a, b]
    rw [hRegroupEq] at hRegroupMap
    rw [hab, hRegrouped] at hRegroupMap
    exact_mod_cast hRegroupMap
  have hCondNat : natCondK D z'' z' ≤ natK D z'' + cCond := by
    have h := hCond z'' z'
    rw [hzCond, hz''] at h
    exact_mod_cast h
  have hLowerNat : natK D a + natCondK D b a ≤
      natK D ab + logSlack cLower (natK D ab + 1) := by
    exact hLower'
  have hZChainNat : natK D zPair ≤
      natK D z' + natCondK D z'' z' + logSlack cUpper (natK D zPair + 1) := by
    exact hZChain
  have hPairChainNat : natK D regrouped ≤
      natK D zPair + natCondK D vPair zPair +
        logSlack cUpper (natK D regrouped + 1) := by
    exact hPairChain
  have hLowerSlack : logSlack cLower (natK D ab + 1) ≤
      logSlack c (natK D ab + 1) :=
    logSlack_mono_left (Nat.le_max_left cLower (max cUpper (cMap + cCond))) _
  have hPairSlack : logSlack cUpper (natK D regrouped + 1) ≤
      logSlack c (natK D regrouped + 1) :=
    logSlack_mono_left
      (Nat.le_trans (Nat.le_max_left cUpper (cMap + cCond))
        (Nat.le_max_right cLower (max cUpper (cMap + cCond)))) _
  have hZSlack : logSlack cUpper (natK D zPair + 1) ≤
      logSlack c (natK D zPair + 1) :=
    logSlack_mono_left
      (Nat.le_trans (Nat.le_max_left cUpper (cMap + cCond))
        (Nat.le_max_right cLower (max cUpper (cMap + cCond)))) _
  have hFinal : natK D a + natCondK D b a ≤
      natK D z' + natK D z'' + natCondK D vPair zPair +
        logSlack c (natK D ab + 1) + logSlack c (natK D regrouped + 1) +
        logSlack c (natK D zPair + 1) + c := by
    omega
  simpa [a, b, ab, zPair, vPair, regrouped] using hFinal

private theorem theorem2_aux_pair_projection
    (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ (x y : BitString),
      natK D x ≤ natK D (pairCode x y) + c ∧
      natK D y ≤ natK D (pairCode x y) + c := by
  obtain ⟨cLeft, hLeft⟩ := Kolmogorov.pairPlainK_left_le D hD
  obtain ⟨cRight, hRight⟩ := Kolmogorov.pairPlainK_right_le D hD
  let c := max cLeft cRight
  refine ⟨c, fun x y => ?_⟩
  have hLeft' : plainK D x ≤ plainK D (pairCode x y) + (cLeft : ℕ∞) := by
    simpa [Kolmogorov.pairPlainK] using hLeft x y
  have hRight' : plainK D y ≤ plainK D (pairCode x y) + (cRight : ℕ∞) := by
    simpa [Kolmogorov.pairPlainK] using hRight x y
  rw [commonInfo_le_mutualInfo_hasPlainValue D hD x,
    commonInfo_le_mutualInfo_hasPlainValue D hD (pairCode x y)] at hLeft'
  rw [commonInfo_le_mutualInfo_hasPlainValue D hD y,
    commonInfo_le_mutualInfo_hasPlainValue D hD (pairCode x y)] at hRight'
  have hLeftNat : natK D x ≤ natK D (pairCode x y) + cLeft := by
    have hcast : (natK D x : ℕ∞) ≤
        ((natK D (pairCode x y) + cLeft : ℕ) : ℕ∞) := by
      rw [Nat.cast_add]
      exact hLeft'
    exact_mod_cast hcast
  have hRightNat : natK D y ≤ natK D (pairCode x y) + cRight := by
    have hcast : (natK D y : ℕ∞) ≤
        ((natK D (pairCode x y) + cRight : ℕ) : ℕ∞) := by
      rw [Nat.cast_add]
      exact hRight'
    exact_mod_cast hcast
  exact ⟨hLeftNat.trans (Nat.add_le_add_left (le_max_left _ _) _),
    hRightNat.trans (Nat.add_le_add_left (le_max_right _ _) _)⟩

private theorem theorem2_aux_pair_linear
    (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ (C n : ℕ) (x y : BitString), 0 < n →
      natK D x ≤ C * n → natK D y ≤ C * n →
      natK D (pairCode x y) ≤ (2 * C + c) * n := by
  obtain ⟨c, hPair⟩ := Kolmogorov.plainK_pair_le_two_mul D hD
  refine ⟨c, fun C n x y hn hx hy => ?_⟩
  have hx' : plainK D x ≤ ((C * n : ℕ) : ℕ∞) := by
    rw [commonInfo_le_mutualInfo_hasPlainValue D hD x]
    exact_mod_cast hx
  have hy' : plainK D y ≤ ((C * n : ℕ) : ℕ∞) := by
    rw [commonInfo_le_mutualInfo_hasPlainValue D hD y]
    exact_mod_cast hy
  have h := hPair (C * n) x y hx' hy'
  change plainK D (pairCode x y) ≤ ((2 * (C * n) + c : ℕ) : ℕ∞) at h
  rw [commonInfo_le_mutualInfo_hasPlainValue D hD (pairCode x y)] at h
  have hNat : natK D (pairCode x y) ≤ 2 * (C * n) + c := by
    exact_mod_cast h
  have hn' : 1 ≤ n := by omega
  have hc : c ≤ c * n := by
    calc
      c = c * 1 := by simp
      _ ≤ c * n := Nat.mul_le_mul_left c hn'
  calc
    natK D (pairCode x y) ≤ 2 * (C * n) + c := hNat
    _ = 2 * C * n + c := by ring
    _ ≤ 2 * C * n + c * n := Nat.add_le_add_left hc _
    _ = (2 * C + c) * n := by rw [Nat.add_mul]

/-- The size bounds on `z'`, `z''`, and `(v', v'')` bound all regrouped chain-rule arguments
linearly in the ambient complexity. -/
theorem theorem2_linear_regrouped_complexities
    (D : Map) (hD : isOptimalConditional D) (c₀ A : ℕ) :
    ∃ B : ℕ, ∀ (x₁ x₂ z : BitString) (M : ℕ) (v' z' v'' z'' : BitString),
      M = natK D (pairCode (pairCode x₁ x₂) z) →
      natK D (pairCode v' v'') ≤ A * (M + 1) →
      natK D z' ≤ natK D z + logSlack c₀ M →
      natK D z'' ≤ natK D z + logSlack c₀ M →
      natK D (pairCode (pairCode v' z') (pairCode v'' z'')) ≤ B * (M + 1) ∧
      natK D (pairCode (pairCode z' z'') (pairCode v' v'')) ≤ B * (M + 1) ∧
        natK D (pairCode z' z'') ≤ B * (M + 1) := by
  obtain ⟨cProj, hProj⟩ :=
    theorem2_aux_pair_projection
      D hD
  obtain ⟨cPair, hPair⟩ :=
    theorem2_aux_pair_linear
      D hD
  let C₀ := cProj + c₀ + 1
  let Cᵥ := A + cProj
  let C := max C₀ Cᵥ
  let Cpair := 2 * C + cPair
  let Cfour := 2 * Cpair + cPair
  let Cinner := max Cpair A
  let Cregroup := 2 * Cinner + cPair
  let B := max Cfour (max Cregroup Cpair)
  refine ⟨B, ?_⟩
  intro x₁ x₂ z M v' z' v'' z'' hM hPairBound hz' hz''
  have hC₀ : C₀ ≤ C := le_max_left _ _
  have hCᵥ : Cᵥ ≤ C := le_max_right _ _
  have hMpos : 0 < M + 1 := by omega
  have hZ : natK D z ≤ M + cProj := by
    simpa [hM] using (hProj (pairCode x₁ x₂) z).2
  have hSlack : logSlack c₀ M ≤ c₀ * (M + 1) := by
    calc
      logSlack c₀ M ≤ c₀ * M + c₀ := logSlack_le_self_linear c₀ M
      _ = c₀ * (M + 1) := by rw [Nat.mul_add]; simp
  have hZ' : natK D z' ≤ C₀ * (M + 1) := by
    calc
      natK D z' ≤ natK D z + logSlack c₀ M := hz'
      _ ≤ M + cProj + c₀ * (M + 1) := Nat.add_le_add hZ hSlack
      _ ≤ C₀ * (M + 1) := by
        dsimp [C₀]
        nlinarith [Nat.zero_le (cProj * M)]
  have hZ'' : natK D z'' ≤ C₀ * (M + 1) := by
    calc
      natK D z'' ≤ natK D z + logSlack c₀ M := hz''
      _ ≤ M + cProj + c₀ * (M + 1) := Nat.add_le_add hZ hSlack
      _ ≤ C₀ * (M + 1) := by
        dsimp [C₀]
        nlinarith [Nat.zero_le (cProj * M)]
  have hV'Proj := (hProj v' v'').1
  have hV''Proj := (hProj v' v'').2
  have hV' : natK D v' ≤ C * (M + 1) := by
    have h0 : natK D v' ≤ A * (M + 1) + cProj :=
      hV'Proj.trans (Nat.add_le_add_right hPairBound cProj)
    have hc : cProj ≤ cProj * (M + 1) := by
      nlinarith
    have h1 : natK D v' ≤ Cᵥ * (M + 1) := by
      calc
        natK D v' ≤ A * (M + 1) + cProj := h0
        _ ≤ A * (M + 1) + cProj * (M + 1) := Nat.add_le_add_left hc _
        _ = Cᵥ * (M + 1) := by dsimp [Cᵥ]; rw [Nat.add_mul]
    exact h1.trans (Nat.mul_le_mul_right (M + 1) hCᵥ)
  have hV'' : natK D v'' ≤ C * (M + 1) := by
    have h0 : natK D v'' ≤ A * (M + 1) + cProj :=
      hV''Proj.trans (Nat.add_le_add_right hPairBound cProj)
    have hc : cProj ≤ cProj * (M + 1) := by
      nlinarith
    have h1 : natK D v'' ≤ Cᵥ * (M + 1) := by
      calc
        natK D v'' ≤ A * (M + 1) + cProj := h0
        _ ≤ A * (M + 1) + cProj * (M + 1) := Nat.add_le_add_left hc _
        _ = Cᵥ * (M + 1) := by dsimp [Cᵥ]; rw [Nat.add_mul]
    exact h1.trans (Nat.mul_le_mul_right (M + 1) hCᵥ)
  have hZ'bound : natK D z' ≤ C * (M + 1) :=
    hZ'.trans (Nat.mul_le_mul_right (M + 1) hC₀)
  have hZ''bound : natK D z'' ≤ C * (M + 1) :=
    hZ''.trans (Nat.mul_le_mul_right (M + 1) hC₀)
  have hVZ' := hPair C (M + 1) v' z' hMpos hV' hZ'bound
  have hVZ'' := hPair C (M + 1) v'' z'' hMpos hV'' hZ''bound
  have hZpair := hPair C (M + 1) z' z'' hMpos hZ'bound hZ''bound
  have hVpair : natK D (pairCode v' v'') ≤ A * (M + 1) := hPairBound
  have hOuter := hPair Cpair (M + 1) (pairCode v' z') (pairCode v'' z'')
    hMpos (by simpa [Cpair] using hVZ') (by simpa [Cpair] using hVZ'')
  have hZpair' : natK D (pairCode z' z'') ≤ Cinner * (M + 1) :=
    hZpair.trans (Nat.mul_le_mul_right (M + 1) (le_max_left _ _))
  have hVpair' : natK D (pairCode v' v'') ≤ Cinner * (M + 1) :=
    hVpair.trans (Nat.mul_le_mul_right (M + 1) (le_max_right _ _))
  have hRegroup := hPair Cinner (M + 1) (pairCode z' z'') (pairCode v' v'')
    hMpos hZpair' hVpair'
  have hCfour : Cfour ≤ B := le_max_left _ _
  have hCregroup : Cregroup ≤ B := le_trans (le_max_left _ _) (le_max_right _ _)
  have hCpair : Cpair ≤ B := le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨?_, ?_, ?_⟩
  · calc
      natK D (pairCode (pairCode v' z') (pairCode v'' z'')) ≤ Cfour * (M + 1) := by
        simpa [Cfour] using hOuter
      _ ≤ B * (M + 1) := Nat.mul_le_mul_right (M + 1) hCfour
  · calc
      natK D (pairCode (pairCode z' z'') (pairCode v' v'')) ≤ Cregroup * (M + 1) := by
        simpa [Cregroup] using hRegroup
      _ ≤ B * (M + 1) := Nat.mul_le_mul_right (M + 1) hCregroup
  · calc
      natK D (pairCode z' z'') ≤ Cpair * (M + 1) := by
        simpa [Cpair] using hZpair
      _ ≤ B * (M + 1) := Nat.mul_le_mul_right (M + 1) hCpair

/-- Lemma 6 (`lemma6`, with its
cover constant `c6`) to the reservoir `A`.  Let `U = U_{α,β,γ,i}` be the cover element that meets
`A` in at least `2 ^ (2α - β - c6)` points and let `w` be a code of `(α, β, γ, i)`.  Then `U` is
an `(α, β, γ)`-semi-bunch (so `|U| = 2 ^ α`), `list(U)` is computable from `w`
(`K(list U | w) ≤ O(log M)`, since `α, β, γ = O(M)` here), and, as `i < cnt ≤ 2 ^ (β + γ - 2α +
c6)`,
`K(w) ≤ β + γ - 2α + O(log M)`. -/
private theorem theorem2_lemma6_index
    (D : Map) (hD : isOptimalConditional D) (c₀ cQ : ℕ) :
    ∃ c6 c : ℕ, ∀ (x₁ x₂ z : BitString) (q t δ M α β γ : ℕ)
      (A : Finset BitString),
      M = natK D (pairCode (pairCode x₁ x₂) z) →
      t ≤ M → δ ≤ M →
      natK D z ≤ α + t + logSlack c₀ M →
      α ≤ natK D z + t + logSlack c₀ M →
      2 * (natK D z + logSlack c₀ M) + δ ≤ 2 * β →
      2 * β ≤ 2 * (natK D z + logSlack c₀ M) + δ + 1 →
      γ ≤ natK D z + q + logSlack c₀ M + 1 →
      q ≤ 2 * M + logSlack cQ M →
      IsSemiBunch D α β γ A →
      ∃ (w : BitString) (U : Finset BitString),
        U.card = 2 ^ α ∧
        2 ^ (2 * α) ≤ (A ∩ U).card * 2 ^ (β + c6) ∧
        natCondK D (finsetListCode U) w ≤ logSlack c M ∧
        natK D w + 2 * α ≤ β + γ + logSlack c M := by
  obtain ⟨c6, cnt, U, ⟨F, hF, hFspec⟩, hCover⟩ := lemma6 D hD
  obtain ⟨cDecode, hDecode⟩ :=
    theorem2_lemma6_index_aux_decode
      D hD F hF
  obtain ⟨cLit, hLit⟩ := plainK_le_length D hD
  obtain ⟨cProj, hProj⟩ := pairPlainK_right_le D hD
  let a := 3 + c₀ + cQ
  let b := cProj + c₀ + cQ + 1
  obtain ⟨cHead, hHead⟩ := logSlack_linear_bound 1 a b
  let c := 6 * cHead + cLit + c6 + cDecode + 3
  refine ⟨c6, c, ?_⟩
  intro x₁ x₂ z q t δ M α β γ A hM ht hδ hsize₁ hsize₂ hbeta hbeta' hgamma hq hsemi
  have hz : natK D z ≤ M + cProj := by
    have h := hProj (pairCode x₁ x₂) z
    change plainK D z ≤ plainK D (pairCode (pairCode x₁ x₂) z) + (cProj : ℕ∞) at h
    rw [← ENat.natCast_toNat (plainK_ne_top D hD z),
      ← ENat.natCast_toNat (plainK_ne_top D hD (pairCode (pairCode x₁ x₂) z))] at h
    have hNat : natK D z ≤ natK D (pairCode (pairCode x₁ x₂) z) + cProj := by
      exact_mod_cast h
    omega
  have hsl₀ := logSlack_le_self_linear c₀ M
  have hslQ := logSlack_le_self_linear cQ M
  have hα : α ≤ a * M + b := by
    dsimp [a, b]
    nlinarith [Nat.zero_le (cQ * M)]
  have hβ : β ≤ a * M + b := by
    dsimp [a, b]
    nlinarith [Nat.zero_le (cQ * M)]
  have hγ : γ ≤ a * M + b := by
    dsimp [a, b]
    nlinarith
  have hlen (p : ℕ) (hp : p ≤ a * M + b) : (Nat.bits p).length ≤ logSlack cHead M := by
    have h := (logSlack_mono_right 1 hp).trans (hHead M)
    simpa only [logSlack, Nat.one_mul] using (Nat.le_trans (Nat.le_succ _) h)
  have hlenα := hlen α hα
  have hlenβ := hlen β hβ
  have hlenγ := hlen γ hγ
  obtain ⟨hU, hMeet, hCount⟩ := hCover α β γ
  obtain ⟨i, hi, hmeet⟩ := hMeet A hsemi
  let w := pairCode (Nat.bits α)
    (pairCode (Nat.bits β) (pairCode (Nat.bits γ) (Nat.bits i)))
  have hlist : natCondK D (finsetListCode (U α β γ i)) w ≤ cDecode := by
    exact hDecode α β γ i _ ((hFspec α β γ i _).mpr ⟨hi, rfl⟩)
  have hindex : (Nat.bits i).length + 2 * α ≤ β + γ + c6 :=
    theorem2_lemma6_index_aux_length
      (2 * α) (β + γ + c6) (cnt α β γ) i hi hCount
  have hwlen : w.length = (Nat.bits i).length +
      2 * (Nat.bits α).length + 2 * (Nat.bits β).length + 2 * (Nat.bits γ).length + 3 := by
    dsimp [w]
    simp only [length_pairCode]
    omega
  have hwK : natK D w ≤ w.length + cLit := by
    have h := hLit w
    have h' : plainK D w ≤ ((w.length + cLit : ℕ) : ℕ∞) := by
      simpa only [programLength, Nat.cast_add] using h
    exact ENat.toNat_le_of_le_natCast h'
  have hslack : 6 * logSlack cHead M + cLit + c6 + 3 ≤ logSlack c M := by
    dsimp [c]
    unfold logSlack
    nlinarith [Nat.zero_le (cLit * (Nat.bits M).length),
      Nat.zero_le (c6 * (Nat.bits M).length),
      Nat.zero_le (cDecode * (Nat.bits M).length)]
  have hDecodeSlack : cDecode ≤ logSlack c M := by
    have hc : cDecode ≤ c := by dsimp [c]; omega
    exact hc.trans (by unfold logSlack; omega)
  refine ⟨w, U α β γ i, (hU i hi).1, hmeet, hlist.trans hDecodeSlack, ?_⟩
  omega

/-- Double-counting the
pairs consisting of a condition in `U` and a short conditional output in an arbitrary finite
set `S`. Each condition has fewer than `2^(k+1)` possible outputs. -/
private theorem theorem2_pairs
    (D : Map) (hD : isOptimalConditional D) (U S : Finset BitString) (k : ℕ) :
    ∑ y ∈ S, (U.filter (fun a => natCondK D y a ≤ k)).card ≤ U.card * 2 ^ (k + 1) := by
  classical
  have hswap : ∑ y ∈ S, (U.filter (fun a => natCondK D y a ≤ k)).card =
      ∑ a ∈ U, (S.filter (fun y => natCondK D y a ≤ k)).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
  rw [hswap]
  calc
    ∑ a ∈ U, (S.filter (fun y => natCondK D y a ≤ k)).card ≤
        ∑ _a ∈ U, 2 ^ (k + 1) := by
      apply Finset.sum_le_sum
      intro a ha
      have hsub : S.filter (fun y => natCondK D y a ≤ k) ⊆ compressibleWords D a k := by
        intro y hy
        rw [mem_compressibleWords_iff]
        rw [← ENat.natCast_toNat (condK_ne_top_of_optimal D hD y a)]
        exact_mod_cast (Finset.mem_filter.mp hy).2
      exact (Finset.card_le_card hsub).trans (card_compressibleWordsLt D a k).le
    _ = U.card * 2 ^ (k + 1) := by simp

/-- The set of outputs
having the required number of distinct short-producing conditions is finite. Double counting
bounds its cardinality, with truncated subtraction also covering `β + c6 < α`. -/
private theorem theorem2_frequent_card
    (D : Map) (hD : isOptimalConditional D) (U : Finset BitString) (α β k c6 : ℕ)
    (hU : U.card ≤ 2 ^ α) :
    let S : Set BitString := {y | 2 ^ (2 * α) ≤
      (U.filter (fun a => natCondK D y a ≤ k)).card * 2 ^ (β + c6)}
    S.Finite ∧ S.ncard ≤ 2 ^ (k + (β + c6 - α) + 1) := by
  classical
  intro S
  let E := U.biUnion (fun a => compressibleWords D a k)
  have hsub : S ⊆ (E : Set BitString) := by
    intro y hy
    have hpos : 0 < (U.filter (fun a => natCondK D y a ≤ k)).card := by
      have hpow : 0 < 2 ^ (2 * α) := by positivity
      change 2 ^ (2 * α) ≤ _ at hy
      by_contra hn
      have hzero : (U.filter (fun a => natCondK D y a ≤ k)).card = 0 := by omega
      rw [hzero] at hy
      simp at hy
    obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos
    obtain ⟨haU, hya⟩ := Finset.mem_filter.mp ha
    apply Finset.mem_biUnion.mpr
    refine ⟨a, haU, ?_⟩
    rw [mem_compressibleWords_iff]
    rw [← ENat.natCast_toNat (condK_ne_top_of_optimal D hD y a)]
    exact_mod_cast hya
  have hfin : S.Finite := E.finite_toSet.subset hsub
  refine ⟨hfin, ?_⟩
  let F := hfin.toFinset
  have hcount :=
      theorem2_pairs
    D hD U F k
  have hweighted : F.card * 2 ^ (2 * α) ≤
      (U.card * 2 ^ (k + 1)) * 2 ^ (β + c6) := by
    calc
      F.card * 2 ^ (2 * α) = ∑ _y ∈ F, 2 ^ (2 * α) := by simp
      _ ≤ ∑ y ∈ F, (U.filter (fun a => natCondK D y a ≤ k)).card * 2 ^ (β + c6) := by
        apply Finset.sum_le_sum
        intro y hy
        exact hfin.mem_toFinset.mp hy
      _ = (∑ y ∈ F, (U.filter (fun a => natCondK D y a ≤ k)).card) * 2 ^ (β + c6) := by
        rw [Finset.sum_mul]
      _ ≤ (U.card * 2 ^ (k + 1)) * 2 ^ (β + c6) := Nat.mul_le_mul_right _ hcount
  have hbound : F.card * 2 ^ (2 * α) ≤ 2 ^ (α + k + 1 + β + c6) := by
    calc
      F.card * 2 ^ (2 * α) ≤ (U.card * 2 ^ (k + 1)) * 2 ^ (β + c6) := hweighted
      _ ≤ (2 ^ α * 2 ^ (k + 1)) * 2 ^ (β + c6) := by gcongr
      _ = 2 ^ (α + k + 1 + β + c6) := by rw [← pow_add, ← pow_add]; congr 1; omega
  have hexp : α + k + 1 + β + c6 ≤ (k + (β + c6 - α) + 1) + 2 * α := by omega
  have hbound' : F.card * 2 ^ (2 * α) ≤
      2 ^ (k + (β + c6 - α) + 1) * 2 ^ (2 * α) := by
    rw [← pow_add]
    exact hbound.trans (Nat.pow_le_pow_right (by decide) hexp)
  have hcard := Nat.le_of_mul_le_mul_right hbound' (by positivity : 0 < 2 ^ (2 * α))
  simpa [F, Set.ncard_eq_toFinset_card S hfin] using hcard

/-- Members of any
uniformly enumerable finite family with at most `2^(n w)` outputs in condition `w` have
conditional complexity at most `n w + O(1)`. The argument uses only enumeration and never
claims a short description of the completed finite list. -/
private theorem theorem2_index
    (D : Map) (hD : isOptimalConditional D) (R : BitString → BitString → Prop)
    (hR : IsRE (fun p : BitString × BitString => R p.1 p.2))
    (n : BitString → ℕ) (hn : Computable n)
    (hfin : ∀ w, {x | R x w}.Finite)
    (hcard : ∀ w, {x | R x w}.ncard ≤ 2 ^ (n w)) :
    ∃ c : ℕ, ∀ x w, R x w → natCondK D x w ≤ n w + c := by
  classical
  let f : BitString → BitString → ℕ∞ := fun x w => if R x w then (n w : ℕ∞) else ⊤
  have hsemi : IsUpperSemicomputable₂ f := by
    have hr := hR.comp_computable
      (Computable.fst.pair (Computable.fst.comp Computable.snd) :
        Computable (fun p : BitString × BitString × ℕ => (p.1, p.2.1)))
    have ht : Computable (fun p : BitString × BitString × ℕ => decide (n p.2.1 < p.2.2)) :=
      (PrimrecRel.decide Primrec.nat_lt).to_comp.comp
        (hn.comp (Computable.fst.comp Computable.snd)) (Computable.snd.comp Computable.snd)
    exact (hr.and_computable ht).of_iff (fun p => by
      dsimp [f]
      by_cases h : R p.1 p.2.1 <;> simp [h])
  have hlevels (w : BitString) (m : ℕ) :
      {x | f x w < (m : ℕ∞)} = if n w < m then {x | R x w} else ∅ := by
    ext x
    by_cases h : R x w <;> by_cases hm : n w < m <;> simp [f, h, hm]
  have hfinite : ∀ (w : BitString) (m : ℕ), {x | f x w < (m : ℕ∞)}.Finite := by
    intro w m
    rw [hlevels]
    split_ifs <;> simp_all
  have hsmall : ∀ (w : BitString) (m : ℕ), {x | f x w < (m : ℕ∞)}.ncard < 2 ^ m := by
    intro w m
    rw [hlevels]
    split_ifs with hm
    · exact (hcard w).trans_lt ((Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mpr hm)
    · simp
  obtain ⟨c, hc⟩ := condK_minimal_upperSemicomputable D hD f hsemi hfinite hsmall
  refine ⟨c, fun x w hx => ?_⟩
  have hh := hc x w
  simp only [f, ite_eq_left hx, ← Nat.cast_add] at hh
  exact ENat.toNat_le_of_le_natCast hh


/-- The weighted
number of distinct elements of a supplied finite list that give a short description of an
output is lower semicomputable. Thus reaching any supplied threshold is enumerable,
uniformly in the list code, complexity bound, multiplier, and threshold. -/
private theorem theorem2_frequent_re
    (D : Map) (hD : isOptimalConditional D) :
    IsRE (fun q : (BitString × BitString) × ℕ × ℕ × ℕ =>
      q.2.2.2 ≤ ((decodeListCode q.1.2).toFinset.filter
        (fun a => natCondK D q.1.1 a ≤ q.2.1)).card * q.2.2.1) := by
  classical
  obtain ⟨chk, hchk, hmono, hiff⟩ := (condK_le_isRE D hD).exists_stageApprox
  let Q := (BitString × BitString) × ℕ × ℕ × ℕ
  let L : Q → List BitString := fun q => canonicalFinsetList (decodeListCode q.1.2).toFinset
  let count : Q × ℕ → ℕ := fun r => ((L r.1).filter
    (fun a => chk (r.1.1.1, a, r.1.2.1) r.2)).length
  have hL : Computable L :=
    canonicalFinsetList_toFinset_primrec.to_comp.comp
      (decodeListCode_primrec.to_comp.comp (Computable.snd.comp Computable.fst))
  have hpred : Computable₂ (fun (r : Q × ℕ) (a : BitString) =>
      chk (r.1.1.1, a, r.1.2.1) r.2) :=
    hchk.comp
      ((Computable.fst.comp (Computable.fst.comp (Computable.fst.comp Computable.fst))).pair
        (Computable.snd.pair
          (Computable.fst.comp (Computable.snd.comp (Computable.fst.comp Computable.fst)))))
      (Computable.snd.comp Computable.fst)
  have hcount : Computable count :=
    Computable.list_length.comp (computable_list_filter (hL.comp Computable.fst) hpred)
  have htest : Computable (fun r : Q × ℕ =>
      decide (r.1.2.2.2 ≤ count r * r.1.2.2.1)) :=
    (PrimrecRel.decide Primrec.nat_le).to_comp.comp
      (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.fst)))
      (Primrec.nat_mul.to_comp.comp hcount
        (Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))))
  have hRE : IsRE (fun r : Q × ℕ => r.1.2.2.2 ≤ count r * r.1.2.2.1) :=
    isRE_of_computable_bool _ _ (fun _ => by simp) htest
  apply (IsRE.exists_encodable
    (R := fun (q : Q) (s : ℕ) => q.2.2.2 ≤ count (q, s) * q.2.2.1) hRE).of_iff
  intro q
  let U := (decodeListCode q.1.2).toFinset
  let F := U.filter (fun a => natCondK D q.1.1 a ≤ q.2.1)
  have hcountEq (s : ℕ) : count (q, s) =
      (U.filter (fun a => chk (q.1.1, a, q.2.1) s = true)).card := by
    dsimp [count, L]
    rw [← List.toFinset_card_of_nodup ((canonicalFinsetList_nodup _).filter _)]
    congr 1
    ext a
    simp [U]
  have hshort (a : BitString) :
      natCondK D q.1.1 a ≤ q.2.1 ↔ ∃ s, chk (q.1.1, a, q.2.1) s = true := by
    rw [← hiff]
    rw [← ENat.natCast_toNat (condK_ne_top_of_optimal D hD q.1.1 a)]
    exact_mod_cast Iff.rfl
  have hsub (s : ℕ) : U.filter (fun a => chk (q.1.1, a, q.2.1) s = true) ⊆ F := by
    intro a ha
    obtain ⟨haU, has⟩ := Finset.mem_filter.mp ha
    exact Finset.mem_filter.mpr ⟨haU, (hshort a).mpr ⟨s, has⟩⟩
  constructor
  · rintro ⟨s, hs⟩
    change q.2.2.2 ≤ F.card * q.2.2.1
    rw [hcountEq] at hs
    exact hs.trans (Nat.mul_le_mul_right _ (Finset.card_le_card (hsub s)))
  · intro h
    have hcommon : ∀ V : Finset BitString,
        (∀ a ∈ V, ∃ s, chk (q.1.1, a, q.2.1) s = true) →
        ∃ s, ∀ a ∈ V, chk (q.1.1, a, q.2.1) s = true := by
      intro V
      induction V using Finset.induction_on with
      | empty => intro _; exact ⟨0, by simp⟩
      | @insert a V ha ih =>
        intro hV
        obtain ⟨s₁, hs₁⟩ := hV a (by simp)
        obtain ⟨s₂, hs₂⟩ := ih (fun b hb => hV b (by simp [hb]))
        refine ⟨max s₁ s₂, ?_⟩
        intro b hb
        rcases Finset.mem_insert.mp hb with rfl | hb
        · exact hmono _ _ _ (le_max_left _ _) hs₁
        · exact hmono _ _ _ (le_max_right _ _) (hs₂ b hb)
    obtain ⟨s, hs⟩ := hcommon F (fun a ha =>
      (hshort a).mp (Finset.mem_filter.mp ha).2)
    refine ⟨s, ?_⟩
    have heq : U.filter (fun a => chk (q.1.1, a, q.2.1) s = true) = F := by
      apply Finset.Subset.antisymm (hsub s)
      intro a ha
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ha).1, hs a ha⟩
    rw [hcountEq, heq]
    exact h


/-- Enumerable
index coding to the frequent outputs. The supplied condition includes the list of `U` and the
three numeric parameters, so the decoder can dovetail without knowing when the enumeration
ends. -/
private theorem theorem2_rank
    (D : Map) (hD : isOptimalConditional D) (c6 : ℕ) :
    ∃ c : ℕ, ∀ (U : Finset BitString) (x : BitString) (α β k : ℕ),
      U.card ≤ 2 ^ α →
      2 ^ (2 * α) ≤ (U.filter (fun a => natCondK D x a ≤ k)).card * 2 ^ (β + c6) →
      natCondK D x (pairCode
        (pairCode (Nat.bits α) (pairCode (Nat.bits β) (Nat.bits k))) (finsetListCode U)) ≤
        k + (β + c6 - α) + 1 + c := by
  classical
  let a : BitString → ℕ := fun w => bitsToNat (decodeFirst (decodeFirst w))
  let b : BitString → ℕ := fun w => bitsToNat (decodeFirst (decodeSecond (decodeFirst w)))
  let k : BitString → ℕ := fun w => bitsToNat (decodeSecond (decodeSecond (decodeFirst w)))
  let U : BitString → Finset BitString := fun w => (decodeListCode (decodeSecond w)).toFinset
  let R : BitString → BitString → Prop := fun x w =>
    (U w).card ≤ 2 ^ a w ∧
      2 ^ (2 * a w) ≤ ((U w).filter (fun u => natCondK D x u ≤ k w)).card * 2 ^ (b w + c6)
  have ha : Computable a := bitsToNat_primrec.to_comp.comp
    (decodeFirst_computable.comp decodeFirst_computable)
  have hb : Computable b := bitsToNat_primrec.to_comp.comp
    (decodeFirst_computable.comp (decodeSecond_computable.comp decodeFirst_computable))
  have hk : Computable k := bitsToNat_primrec.to_comp.comp
    (decodeSecond_computable.comp (decodeSecond_computable.comp decodeFirst_computable))
  have hpow : Computable₂ (fun m n : ℕ => m ^ n) :=
    (Primrec.nat_iff.mpr Nat.Primrec.pow).to_comp
  have hcard : Computable (fun w => (U w).card) := by
    have hh := Computable.list_length.comp
      (canonicalFinsetList_toFinset_primrec.to_comp.comp
        (decodeListCode_primrec.to_comp.comp decodeSecond_computable))
    simpa [U] using hh
  have hsize : Computable (fun w => decide ((U w).card ≤ 2 ^ a w)) :=
    (PrimrecRel.decide Primrec.nat_le).to_comp.comp hcard
      (hpow.comp (Computable.const 2) ha)
  let arg : BitString × BitString → (BitString × BitString) × ℕ × ℕ × ℕ := fun p =>
    ((p.1, decodeSecond p.2), k p.2, 2 ^ (b p.2 + c6), 2 ^ (2 * a p.2))
  have harg : Computable arg :=
    (Computable.fst.pair (decodeSecond_computable.comp Computable.snd)).pair
      ((hk.comp Computable.snd).pair
        ((hpow.comp (Computable.const 2)
            (Primrec.nat_add.to_comp.comp (hb.comp Computable.snd) (Computable.const c6))).pair
          (hpow.comp (Computable.const 2)
            (Primrec.nat_mul.to_comp.comp (Computable.const 2) (ha.comp Computable.snd)))))
  have hraw : IsRE (fun p : BitString × BitString =>
      2 ^ (2 * a p.2) ≤ ((U p.2).filter
        (fun u => natCondK D p.1 u ≤ k p.2)).card * 2 ^ (b p.2 + c6)) :=
    (theorem2_frequent_re
      D hD).comp_computable harg
  have hR : IsRE (fun p : BitString × BitString => R p.1 p.2) :=
    (hraw.and_computable (hsize.comp Computable.snd)).of_iff (fun p => by simp [R])
  let n : BitString → ℕ := fun w => k w + (b w + c6 - a w) + 1
  have hn : Computable n :=
    Primrec.nat_add.to_comp.comp
      (Primrec.nat_add.to_comp.comp hk
        (Primrec.nat_sub.to_comp.comp
          (Primrec.nat_add.to_comp.comp hb (Computable.const c6)) ha)) (Computable.const 1)
  have hf : ∀ w, {x | R x w}.Finite := by
    intro w
    by_cases hw : (U w).card ≤ 2 ^ a w
    · simpa [R, hw] using
        (theorem2_frequent_card
          D hD (U w) (a w) (b w) (k w) c6 hw).1
    · simp [R, hw]
  have hc : ∀ w, {x | R x w}.ncard ≤ 2 ^ n w := by
    intro w
    by_cases hw : (U w).card ≤ 2 ^ a w
    · simpa [R, hw, n] using
        (theorem2_frequent_card
          D hD (U w) (a w) (b w) (k w) c6 hw).2
    · simp [R, hw]
  obtain ⟨c, hc⟩ :=
    theorem2_index
      D hD R hR n hn hf hc
  refine ⟨c, fun V x α β j hV hx => ?_⟩
  have hUdecode : (decodeListCode (finsetListCode V)).toFinset = V := by
    simp [finsetListCode]
  have hinst := hc x (pairCode
    (pairCode (Nat.bits α) (pairCode (Nat.bits β) (Nat.bits j))) (finsetListCode V))
  simp only [R, U, a, b, k, n, decodeFirst_pairCode, decodeSecond_pairCode,
    bitsToNat_bits, hUdecode] at hinst
  exact hinst ⟨hV, hx⟩


/-- Supplying the three
linearly bounded integers in binary alongside the list of `U`. The resulting condition still
has logarithmic conditional complexity given `w`. -/
private theorem theorem2_advice
    (D : Map) (hD : isOptimalConditional D) (cCover B : ℕ) :
    ∃ c : ℕ, ∀ (L w : BitString) (M α β k : ℕ),
      α ≤ B * (M + 1) → β ≤ B * (M + 1) → k ≤ B * (M + 1) →
      natCondK D L w ≤ logSlack cCover M →
      natCondK D (pairCode
        (pairCode (Nat.bits α) (pairCode (Nat.bits β) (Nat.bits k))) L) w ≤ logSlack c M := by
  obtain ⟨cBits, hBits⟩ := logSlack_linear_bound 1 B B
  obtain ⟨cPlain, hPlain⟩ := plainK_le_length D hD
  obtain ⟨cCond, hCond⟩ := condK_le_plainK D hD
  obtain ⟨cPair, hPair⟩ := condK_pair_le_add D hD
  let a := 5 * cBits + cPlain + cCond + 2
  obtain ⟨cFold, hFold⟩ := logSlack_linear_bound cPair (a + cCover) (a + cCover + 1)
  refine ⟨a + cCover + cFold, ?_⟩
  intro L w M α β k hα hβ hk hL
  let p := pairCode (Nat.bits α) (pairCode (Nat.bits β) (Nat.bits k))
  have hbits (i : ℕ) (hi : i ≤ B * (M + 1)) : (Nat.bits i).length ≤ logSlack cBits M := by
    have hi' : i ≤ B * M + B := by simpa [Nat.mul_add] using hi
    have hh := (logSlack_mono_right 1 hi').trans (hBits M)
    simpa [logSlack] using (by omega : logSlack 1 i - 1 ≤ logSlack cBits M)
  have hp : natCondK D p w ≤ logSlack a M := by
    have hpc : condK D p w ≤ ((p.length + cPlain + cCond : ℕ) : ℕ∞) := by
      calc
        condK D p w ≤ plainK D p + (cCond : ℕ∞) := hCond p w
        _ ≤ ((programLength p : ℕ∞) + cPlain) + cCond := add_le_add (hPlain p) le_rfl
        _ = ((p.length + cPlain + cCond : ℕ) : ℕ∞) := by simp [programLength]
    have hnat : natCondK D p w ≤ p.length + cPlain + cCond :=
      ENat.toNat_le_of_le_natCast hpc
    have hplen : p.length = 2 * (Nat.bits α).length + 2 * (Nat.bits β).length +
        (Nat.bits k).length + 2 := by simp [p, length_pairCode]; omega
    have h1 := hbits α hα
    have h2 := hbits β hβ
    have h3 := hbits k hk
    have hslack : 5 * logSlack cBits M + (cPlain + cCond + 2) ≤ logSlack a M := by
      dsimp [a]
      unfold logSlack
      nlinarith [Nat.zero_le ((cPlain + cCond + 2) * (Nat.bits M).length)]
    omega
  have hlinear : natCondK D p w + natCondK D L w + 1 ≤
      (a + cCover) * M + (a + cCover + 1) := by
    have h1 := logSlack_le_self_linear a M
    have h2 := logSlack_le_self_linear cCover M
    calc
      natCondK D p w + natCondK D L w + 1 ≤
          (a * M + a) + (cCover * M + cCover) + 1 := by omega
      _ = (a + cCover) * M + (a + cCover + 1) := by ring
  have hfolded := (logSlack_mono_right cPair hlinear).trans (hFold M)
  have hpair := hPair p L w (natCondK D p w) (natCondK D L w)
    (by unfold HasPlainConditionalComplexityValue natCondK
        exact (ENat.natCast_toNat (condK_ne_top_of_optimal D hD p w)).symm)
    (by unfold HasPlainConditionalComplexityValue natCondK
        exact (ENat.natCast_toNat (condK_ne_top_of_optimal D hD L w)).symm)
  have hpairNat : natCondK D (pairCode p L) w ≤
      natCondK D p w + natCondK D L w +
        logSlack cPair (natCondK D p w + natCondK D L w + 1) :=
    ENat.toNat_le_of_le_natCast hpair
  have hsum : logSlack (a + cCover + cFold) M =
      logSlack a M + logSlack cCover M + logSlack cFold M := by unfold logSlack; ring
  change natCondK D (pairCode p L) w ≤ _
  rw [hsum]
  omega

/-- Counting the pairs `(a, x')` with
`a ∈ U` and `K(x' | a) ≤ k`, where `k = K(x) - q + t + O(log M)` (each `a ∈ U` has at most
`2 ^ (k + 1)` such `x'`, so at most `2 ^ (α + k + 1)` pairs).  The strings `x'` occurring with at
least `2 ^ (2α - β - c6)` elements `a ∈ U` (at most `2 ^ (k + β - α + c6 + 1)` of them, and they
are enumerable from `list(U)` and `k`) include `x = xᵢ`, because the `≥ 2 ^ (2α - β - c6)`
elements of `A ∩ U` are all at distance `≤ k` from `x`.  Hence
`K(x | w) ≤ K(x) - q + (β - α) + t + O(log M) ≤ K(x) - q + δ + 3t + O(log M)`
(`β - α ≤ t + δ/2 + O(log M)` by the two bounds on `β` and the lower bound on `α`; `K(x), α, β, q`
are `O(M)`, which makes the logarithmic overheads `O(log M)`). -/
private theorem theorem2_counting
    (D : Map) (hD : isOptimalConditional D) (c₀ c6 cCover cQ : ℕ) :
    ∃ c : ℕ, ∀ (x₁ x₂ z x : BitString) (q t δ M α β : ℕ)
      (A U : Finset BitString) (w : BitString),
      x = x₁ ∨ x = x₂ →
      M = natK D (pairCode (pairCode x₁ x₂) z) →
      t ≤ M → δ ≤ M →
      natK D z ≤ α + t + logSlack c₀ M →
      α ≤ natK D z + t + logSlack c₀ M →
      2 * (natK D z + logSlack c₀ M) + δ ≤ 2 * β →
      2 * β ≤ 2 * (natK D z + logSlack c₀ M) + δ + 1 →
      q ≤ 2 * M + logSlack cQ M →
      U.card = 2 ^ α →
      2 ^ (2 * α) ≤ (A ∩ U).card * 2 ^ (β + c6) →
      natCondK D (finsetListCode U) w ≤ logSlack cCover M →
      (∀ a ∈ A, natCondK D x a ≤ natK D x - q + t + logSlack c₀ M) →
      natCondK D x w ≤ natK D x - q + δ + 3 * t + logSlack c M := by
  obtain ⟨cZ, hZmap⟩ := plainK_map_le D hD decodeSecond decodeSecond_computable
  obtain ⟨cX₁, hX₁map⟩ := plainK_map_le D hD (decodeFirst ∘ decodeFirst)
    (decodeFirst_computable.comp decodeFirst_computable)
  obtain ⟨cX₂, hX₂map⟩ := plainK_map_le D hD (decodeSecond ∘ decodeFirst)
    (decodeSecond_computable.comp decodeFirst_computable)
  let B := c₀ + cZ + cX₁ + cX₂ + 5
  obtain ⟨cRank, hRank⟩ :=
    theorem2_rank D hD c6
  obtain ⟨cAdvice, hAdvice⟩ :=
    theorem2_advice
      D hD cCover B
  obtain ⟨cChain, hChain⟩ := condK_chain_upper_values D hD
  let H := cAdvice + 2 * B + c6 + cRank + 1
  obtain ⟨cFold, hFold⟩ := logSlack_linear_bound cChain H (H + 1)
  refine ⟨3 * c₀ + cAdvice + cFold + c6 + cRank + 3, ?_⟩
  intro x₁ x₂ z x q t δ M α β A U w hx hM ht hδ hsize₁ hsize₂ hbeta hbeta' hq
    hU hcover hlist hclone
  have hVal (s : BitString) : plainK D s = (natK D s : ℕ∞) :=
    (ENat.natCast_toNat (plainK_ne_top D hD s)).symm
  have hCVal (s y : BitString) :
      HasPlainConditionalComplexityValue D s y (natCondK D s y) :=
    (ENat.natCast_toNat (condK_ne_top_of_optimal D hD s y)).symm
  have hZ : natK D z ≤ M + cZ := by
    have hh := hZmap (pairCode (pairCode x₁ x₂) z)
    simp only [decodeSecond_pairCode] at hh
    rw [hVal, hVal, ← hM] at hh
    exact_mod_cast hh
  have hX₁ : natK D x₁ ≤ M + cX₁ := by
    have hh := hX₁map (pairCode (pairCode x₁ x₂) z)
    simp only [Function.comp_apply, decodeFirst_pairCode] at hh
    rw [hVal, hVal, ← hM] at hh
    exact_mod_cast hh
  have hX₂ : natK D x₂ ≤ M + cX₂ := by
    have hh := hX₂map (pairCode (pairCode x₁ x₂) z)
    simp only [Function.comp_apply, decodeFirst_pairCode, decodeSecond_pairCode] at hh
    rw [hVal, hVal, ← hM] at hh
    exact_mod_cast hh
  have hX : natK D x ≤ M + cX₁ + cX₂ := by
    rcases hx with rfl | rfl <;> omega
  let L := logSlack c₀ M
  let k := natK D x - q + t + L
  have hlinear (r C : ℕ) (hC : c₀ + C ≤ B) (hr : r ≤ 2 * M + L + C) :
      r ≤ B * (M + 1) := by
    have hL := logSlack_le_self_linear c₀ M
    have hcoeff : c₀ + 2 ≤ B := by dsimp [B]; omega
    have hmul := Nat.mul_le_mul_right M hcoeff
    have hr' : r ≤ (c₀ + 2) * M + (c₀ + C) := by
      dsimp [L] at hr
      nlinarith only [hL, hr]
    calc
      r ≤ (c₀ + 2) * M + (c₀ + C) := hr'
      _ ≤ B * M + B := Nat.add_le_add hmul hC
      _ = B * (M + 1) := by ring
  have hαlinear : α ≤ B * (M + 1) :=
    hlinear α cZ (by dsimp [B]; omega) (by dsimp [L]; omega)
  have hβlinear : β ≤ B * (M + 1) :=
    hlinear β (cZ + 1) (by dsimp [B]; omega) (by dsimp [L]; omega)
  have hklinear : k ≤ B * (M + 1) :=
    hlinear k (cX₁ + cX₂) (by dsimp [B]; omega) (by dsimp [k, L]; omega)
  have hsub : A ∩ U ⊆ U.filter (fun a => natCondK D x a ≤ k) := by
    intro a ha
    obtain ⟨haA, haU⟩ := Finset.mem_inter.mp ha
    exact Finset.mem_filter.mpr ⟨haU, hclone a haA⟩
  have hdense : 2 ^ (2 * α) ≤
      (U.filter (fun a => natCondK D x a ≤ k)).card * 2 ^ (β + c6) :=
    hcover.trans (Nat.mul_le_mul_right _ (Finset.card_le_card hsub))
  let ctx := pairCode
    (pairCode (Nat.bits α) (pairCode (Nat.bits β) (Nat.bits k))) (finsetListCode U)
  let r := k + (β + c6 - α) + 1 + cRank
  have hrank : natCondK D x ctx ≤ r := hRank U x α β k hU.le hdense
  have hadvice : natCondK D ctx w ≤ logSlack cAdvice M :=
    hAdvice (finsetListCode U) w M α β k hαlinear hβlinear hklinear hlist
  have hrlinear : r ≤ (2 * B + c6 + cRank + 1) * (M + 1) := by
    have hc : c6 + cRank + 1 ≤ (c6 + cRank + 1) * (M + 1) := by
      simp
    have hsub : β + c6 - α ≤ β + c6 := Nat.sub_le _ _
    dsimp [r]
    nlinarith only [hklinear, hβlinear, hc, hsub]
  have halinear : natCondK D ctx w ≤ cAdvice * (M + 1) := by
    have hh := logSlack_le_self_linear cAdvice M
    calc
      natCondK D ctx w ≤ logSlack cAdvice M := hadvice
      _ ≤ cAdvice * (M + 1) := by simpa [Nat.mul_add] using hh
  have harg : natCondK D ctx w + natCondK D x ctx + 1 ≤ H * M + (H + 1) := by
    have hh := Nat.add_le_add halinear (hrank.trans hrlinear)
    calc
      natCondK D ctx w + natCondK D x ctx + 1 ≤
          cAdvice * (M + 1) + (2 * B + c6 + cRank + 1) * (M + 1) + 1 :=
        Nat.add_le_add_right hh 1
      _ = H * M + (H + 1) := by dsimp [H]; ring
  have hlog := (logSlack_mono_right cChain harg).trans (hFold M)
  have hchain := hChain w x ctx (natCondK D ctx w) (natCondK D x ctx)
    (natCondK D x w) (hCVal ctx w) (hCVal x ctx) (hCVal x w)
  have hraw : natCondK D x w ≤ logSlack cAdvice M + r + logSlack cFold M := by omega
  have hgap : β + c6 - α ≤ δ + t + 2 * L + c6 + 1 := by
    dsimp [L]
    omega
  have hconst : c6 + cRank + 3 ≤ logSlack (c6 + cRank + 3) M := by
    unfold logSlack
    omega
  have hlogs : logSlack (3 * c₀ + cAdvice + cFold + c6 + cRank + 3) M =
      3 * L + logSlack cAdvice M + logSlack cFold M + logSlack (c6 + cRank + 3) M := by
    dsimp [L]
    unfold logSlack
    ring
  rw [hlogs]
  dsimp [r, k] at hraw
  omega

/-- An
element of a finite set by its rank in the canonical list. -/
private theorem theorem2_lower_bound_index
    (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ (α : ℕ) (U : Finset BitString) (a : BitString),
      U.card = 2 ^ α → a ∈ U →
      natCondK D a (finsetListCode U) ≤ α + c := by
  let f : BitString → List BitString := decodeListCode
  have hf : Computable f := decodeListCode_primrec.to_comp
  let decoder : Map := fun q => Part.some ((f q.2).getD (decodeBits q.1) [])
  have hget : Computable (fun q : BitString × BitString =>
      (f q.2).getD (decodeBits q.1) []) := by
    have hf' : Computable (fun q : BitString × BitString => f q.2) := hf.comp Computable.snd
    have hi : Computable (fun q : BitString × BitString => decodeBits q.1) :=
      decodeBits_computable.comp Computable.fst
    exact (Primrec.list_getD []).to_comp.comp hf' hi
  have hdecoder : isDecompressor decoder := Computable.partrec hget
  obtain ⟨c, hc⟩ := hD.2 decoder hdecoder
  refine ⟨c, fun α U a hcard ha => ?_⟩
  let L := canonicalFinsetList U
  have hmem : a ∈ L := mem_canonicalFinsetList.mpr ha
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hmem
  have hi' : i < L.length := (List.getElem?_eq_some_iff.mp hi).1
  have hAt : L.getD i [] = a := by
    rw [List.getD_eq_getElem L [] hi']
    exact (List.getElem?_eq_some_iff.mp hi).2
  have hList : decodeListCode (finsetListCode U) = L := by
    simp [finsetListCode, L]
  have hLen : (f (finsetListCode U)).length = 2 ^ α := by
    simp [f, finsetListCode, hcard]
  have hprod : produces decoder (Nat.bits i) (finsetListCode U)
      ((f (finsetListCode U)).getD i []) := by
    simp [produces, decoder, f, decodeBits_natBits]
  have hcond : condK decoder ((f (finsetListCode U)).getD i [])
      (finsetListCode U) ≤ ((Nat.bits i).length : ℕ∞) := by
    change sInf (candidateLengths decoder ((f (finsetListCode U)).getD i [])
      (finsetListCode U)) ≤ _
    exact sInf_le ⟨Nat.bits i, hprod, rfl⟩
  have hD_bound : condK D ((f (finsetListCode U)).getD i []) (finsetListCode U) ≤
      ((Nat.bits i).length + c : ℕ∞) := by
    calc
      condK D ((f (finsetListCode U)).getD i []) (finsetListCode U)
          ≤ condK decoder ((f (finsetListCode U)).getD i []) (finsetListCode U) + c :=
            hc _ _
      _ ≤ ((Nat.bits i).length : ℕ∞) + c := by
            simpa [add_comm] using add_le_add_left hcond (c : ℕ∞)
      _ = ((Nat.bits i).length + c : ℕ∞) := by norm_cast
  have hNat : natCondK D ((f (finsetListCode U)).getD i []) (finsetListCode U) ≤
      (Nat.bits i).length + c := ENat.toNat_le_of_le_natCast hD_bound
  have hbit : (Nat.bits i).length ≤ Nat.clog 2 (f (finsetListCode U)).length := by
    rw [Nat.size_eq_bits_len]
    apply (Nat.size_le).2
    have hi'' : i < (f (finsetListCode U)).length := by simpa [f, hList] using hi'
    exact lt_of_lt_of_le hi''
      (Nat.le_pow_clog (b := 2) (by norm_num) (f (finsetListCode U)).length)
  have hAt' : (f (finsetListCode U)).getD i [] = a := by
    simpa [f, hList] using hAt
  rw [hLen, Nat.clog_pow (2 : ℕ) α (by norm_num : 1 < 2)] at hbit
  rw [hAt'] at hNat
  exact hNat.trans (Nat.add_le_add_right hbit c)

/-- Composing the
description of the list given `w` with the rank description of an element, when all descriptions
have linear size in `M`. -/
private theorem theorem2_list_recovery
    (D : Map) (hD : isOptimalConditional D) (cIndex cCover B : ℕ) :
    ∃ c : ℕ, ∀ (a L w : BitString) (M α : ℕ),
      natK D w ≤ B * (M + 1) →
      natCondK D L w ≤ logSlack cCover M →
      α ≤ B * (M + 1) →
      natCondK D a L ≤ α + cIndex →
      natCondK D a w ≤ natCondK D L w + α + logSlack c M := by
  obtain ⟨cChain, hChain⟩ := Kolmogorov.condK_chain_upper_values D hD
  let aLin := cCover + B
  let bLin := aLin + cIndex + 1
  obtain ⟨cFold, hFold⟩ := logSlack_linear_bound cChain aLin bLin
  let c := cFold + cIndex
  refine ⟨c, ?_⟩
  intro a L w M α _hW hL hα hIndex
  let k₁ := natCondK D L w
  let k₂ := natCondK D a L
  have hk₁ : k₁ ≤ cCover * (M + 1) := by
    calc
      k₁ ≤ logSlack cCover M := hL
      _ ≤ cCover * (M + 1) := by
        simpa [Nat.mul_succ] using logSlack_le_self_linear cCover M
  have hk₂ : k₂ ≤ B * (M + 1) + cIndex :=
    hIndex.trans (Nat.add_le_add_right hα cIndex)
  have hArg : k₁ + k₂ + 1 ≤ aLin * M + bLin := by
    calc
      k₁ + k₂ + 1 ≤ cCover * (M + 1) + (B * (M + 1) + cIndex) + 1 := by omega
      _ = aLin * M + bLin := by dsimp [aLin, bLin]; ring
  have hSlack : logSlack cChain (k₁ + k₂ + 1) ≤ logSlack cFold M := by
    calc
      logSlack cChain (k₁ + k₂ + 1) ≤ logSlack cChain (aLin * M + bLin) :=
        logSlack_mono_right cChain hArg
      _ ≤ logSlack cFold M := hFold M
  have hChainInst := hChain w a L k₁ k₂ (natCondK D a w)
    (condK_le_add_condMutualInfo_value D hD L w)
    (condK_le_add_condMutualInfo_value D hD a L)
    (condK_le_add_condMutualInfo_value D hD a w)
  have hMain : natCondK D a w ≤ k₁ + k₂ + logSlack cFold M := by
    calc
      natCondK D a w ≤ k₁ + k₂ + logSlack cChain (k₁ + k₂ + 1) := hChainInst
      _ ≤ k₁ + k₂ + logSlack cFold M := Nat.add_le_add_left hSlack (k₁ + k₂)
  have hFinal : natCondK D a w ≤ k₁ + α + logSlack (cFold + cIndex) M := by
    calc
      natCondK D a w ≤ k₁ + k₂ + logSlack cFold M := hMain
      _ ≤ k₁ + α + (logSlack cFold M + cIndex) := by omega
      _ ≤ k₁ + α + logSlack (cFold + cIndex) M :=
        Nat.add_le_add_left (logSlack_add_nat_le cFold cIndex M) (k₁ + α)
  simpa [c, k₁] using hFinal

/-- A description
of `a` given `w` and a description of `w` yield a description of `a`, with logarithmic overhead
when `w` has linear complexity. -/
theorem theorem2_plain_from_conditional
    (D : Map) (hD : isOptimalConditional D) (B : ℕ) :
    ∃ c : ℕ, ∀ (a w : BitString) (M : ℕ),
      natK D w ≤ B * (M + 1) →
      natK D a ≤ natK D w + natCondK D a w + logSlack c M := by
  obtain ⟨cPair, hPair⟩ := plainK_pair_le_add_two_log_add_condK D hD
  obtain ⟨cRight, hRight⟩ := pairPlainK_right_le D hD
  obtain ⟨cFold, hFold⟩ := logSlack_linear_bound 1 B B
  refine ⟨2 * cFold + cPair + cRight, fun a w M hW => ?_⟩
  have hPairNat : natK D (pairCode w a) ≤
      natK D w + natCondK D a w + (2 * Nat.log 2 (natK D w) + cPair) := by
    have h := hPair w a
    change plainK D (pairCode w a) ≤ plainK D w + condK D a w +
      ((2 * Nat.log 2 (cVal D w) + cPair : ℕ) : ℕ∞) at h
    rw [← ENat.natCast_toNat (plainK_ne_top D hD (pairCode w a)),
      ← ENat.natCast_toNat (plainK_ne_top D hD w),
      ← ENat.natCast_toNat (condK_ne_top_of_optimal D hD a w)] at h
    have h' : natK D (pairCode w a) ≤ natK D w + natCondK D a w +
        (2 * Nat.log 2 (cVal D w) + cPair) := by exact_mod_cast h
    have hcv : cVal D w = natK D w := rfl
    simpa [hcv] using h'
  have hRightNat : natK D a ≤ natK D (pairCode w a) + cRight := by
    have h := hRight w a
    change plainK D a ≤ plainK D (pairCode w a) + (cRight : ℕ∞) at h
    rw [← ENat.natCast_toNat (plainK_ne_top D hD a),
      ← ENat.natCast_toNat (plainK_ne_top D hD (pairCode w a))] at h
    exact_mod_cast h
  have hWlin : natK D w ≤ B * M + B := by
    simpa [Nat.mul_succ] using hW
  have hLogW : Nat.log 2 (natK D w) ≤ Nat.log 2 (B * M + B) :=
    Nat.log_mono_right hWlin
  have hLogBits : Nat.log 2 (B * M + B) ≤
      (Nat.bits (B * M + B)).length := commonInfo_le_mutualInfo_natLog_le_bits _
  have hBitsBound : (Nat.bits (B * M + B)).length + 1 ≤
      cFold * (Nat.bits M).length + cFold := by
    have hh := hFold M
    simpa [logSlack] using hh
  have hSlack : 2 * Nat.log 2 (natK D w) + cPair + cRight ≤
      logSlack (2 * cFold + cPair + cRight) M := by
    have hb := hLogW.trans hLogBits
    have hb' : Nat.log 2 (natK D w) ≤ cFold * (Nat.bits M).length + cFold := by
      have hh : (Nat.bits (B * M + B)).length ≤
          cFold * (Nat.bits M).length + cFold := by omega
      exact hb.trans hh
    have htwice : 2 * Nat.log 2 (natK D w) ≤
        2 * cFold * (Nat.bits M).length + 2 * cFold := by
      calc
        2 * Nat.log 2 (natK D w) ≤ 2 * (cFold * (Nat.bits M).length + cFold) :=
          Nat.mul_le_mul_left 2 hb'
        _ = 2 * cFold * (Nat.bits M).length + 2 * cFold := by ring
    have hbase : 2 * Nat.log 2 (natK D w) + cPair + cRight ≤
        2 * cFold * (Nat.bits M).length + 2 * cFold + cPair + cRight := by omega
    calc
      2 * Nat.log 2 (natK D w) + cPair + cRight
          ≤ 2 * cFold * (Nat.bits M).length + 2 * cFold + cPair + cRight := hbase
      _ ≤ logSlack (2 * cFold + cPair + cRight) M := by
        unfold logSlack
        nlinarith [Nat.zero_le (cPair * (Nat.bits M).length),
          Nat.zero_le (cRight * (Nat.bits M).length)]
  calc
    natK D a ≤ natK D (pairCode w a) + cRight := hRightNat
    _ ≤ natK D w + natCondK D a w +
          (2 * Nat.log 2 (natK D w) + cPair + cRight) := by omega
    _ ≤ natK D w + natCondK D a w +
          logSlack (2 * cFold + cPair + cRight) M := by omega

/-- The cover index `w` satisfies `K(w) ≥ q - t - O(log M)`.  For
`a ∈ U`; `K(a | w) ≤ K(a | list U) + K(list U | w) + O(1) ≤ α + O(log M)` (index of `a` in
the list of `U`), so `K(w) ≥ K(a) - K(a | w) - O(log M) ≥ K(z) + q - α - O(log M) ≥ q - t - O(log
M)`.
(If `K(w)` is large then `q ≤ 2M + O(log M) ≤ K(w)` already.) -/
private theorem theorem2_cover_semibunch_lower_bound
    (D : Map) (hD : isOptimalConditional D) (c₀ cCover cQ : ℕ) :
    ∃ c : ℕ, ∀ (x₁ x₂ z a w : BitString) (q t M α : ℕ) (U : Finset BitString),
      M = natK D (pairCode (pairCode x₁ x₂) z) →
      a ∈ U → U.card = 2 ^ α →
      natCondK D (finsetListCode U) w ≤ logSlack cCover M →
      natK D z + q ≤ natK D a + logSlack c₀ M →
      α ≤ natK D z + t + logSlack c₀ M →
      q ≤ 2 * M + logSlack cQ M →
      q ≤ natK D w + t + logSlack c M := by
  obtain ⟨cIndex, hIndex⟩ :=
    theorem2_lower_bound_index
      D hD
  obtain ⟨cZ, hZmap⟩ := plainK_map_le D hD decodeSecond decodeSecond_computable
  let B := cZ + cQ + c₀ + cIndex + 10
  obtain ⟨cStage, hStage⟩ :=
    theorem2_list_recovery
      D hD cIndex cCover B
  obtain ⟨cInfo, hInfo⟩ :=
    theorem2_plain_from_conditional
      D hD B
  let c := cCover + cStage + cInfo + 2 * c₀
  refine ⟨c, ?_⟩
  intro x₁ x₂ z a w q t M α U hM ha hcard hlist hK hAlpha hq
  by_cases htq : q ≤ t
  · omega
  by_cases hwq : q ≤ natK D w
  · omega
  have htlt : t < q := Nat.lt_of_not_ge htq
  have hwlt : natK D w < q := Nat.lt_of_not_ge hwq
  have hZ : natK D z ≤ M + cZ := by
    have h := hZmap (pairCode (pairCode x₁ x₂) z)
    have h' : plainK D z ≤
        plainK D (pairCode (pairCode x₁ x₂) z) + (cZ : ℕ∞) := by
      simpa only [decodeSecond_pairCode] using h
    rw [← ENat.natCast_toNat (plainK_ne_top D hD z),
      ← ENat.natCast_toNat
        (plainK_ne_top D hD (pairCode (pairCode x₁ x₂) z))] at h'
    have hNat : natK D z ≤ natK D (pairCode (pairCode x₁ x₂) z) + cZ := by
      exact_mod_cast h'
    simpa [hM] using hNat
  have hqLinear : q ≤ (2 + cQ) * (M + 1) := by
    have hs := logSlack_le_self_linear cQ M
    have hs' : logSlack cQ M ≤ cQ * (M + 1) := by
      simpa [Nat.mul_succ] using hs
    calc
      q ≤ 2 * M + logSlack cQ M := hq
      _ ≤ 2 * M + cQ * (M + 1) := Nat.add_le_add_left hs' _
      _ ≤ 2 * (M + 1) + cQ * (M + 1) := by omega
      _ = (2 + cQ) * (M + 1) := by rw [Nat.add_mul]
  have hcoefW : 2 + cQ ≤ B := by dsimp [B]; omega
  have hWbound : natK D w ≤ B * (M + 1) := by
    calc
      natK D w ≤ q := hwlt.le
      _ ≤ (2 + cQ) * (M + 1) := hqLinear
      _ ≤ B * (M + 1) := Nat.mul_le_mul_right _ hcoefW
  have hZbound : natK D z ≤ (1 + cZ) * (M + 1) := by
    calc
      natK D z ≤ M + cZ := hZ
      _ ≤ (1 + cZ) * (M + 1) := by nlinarith [Nat.zero_le (cZ * M)]
  have hslack₀ : logSlack c₀ M ≤ c₀ * (M + 1) := by
    simpa [Nat.mul_succ] using logSlack_le_self_linear c₀ M
  have hαbound : α ≤ B * (M + 1) := by
    have htBound : t ≤ (2 + cQ) * (M + 1) :=
      (Nat.le_of_lt htlt).trans hqLinear
    have hAlpha' :
        α ≤ (1 + cZ) * (M + 1) + (2 + cQ) * (M + 1) + c₀ * (M + 1) := by
      calc
        α ≤ natK D z + t + logSlack c₀ M := hAlpha
        _ ≤ (1 + cZ) * (M + 1) + (2 + cQ) * (M + 1) + c₀ * (M + 1) := by
          exact Nat.add_le_add (Nat.add_le_add hZbound htBound) hslack₀
    have hcoef : (1 + cZ) + (2 + cQ) + c₀ ≤ B := by dsimp [B]; omega
    calc
      α ≤ ((1 + cZ) + (2 + cQ) + c₀) * (M + 1) := by
        simpa [Nat.add_mul] using hAlpha'
      _ ≤ B * (M + 1) := Nat.mul_le_mul_right _ hcoef
  have hIndex' := hIndex α U a hcard ha
  have hAw := hStage a (finsetListCode U) w M α hWbound hlist hαbound hIndex'
  have hKa := hInfo a w M hWbound
  have hKaup : natK D a ≤
      natK D w + logSlack cCover M + α + logSlack cStage M + logSlack cInfo M := by
    have hAwBound : natCondK D a w ≤
        logSlack cCover M + α + logSlack cStage M := by
      calc
        natCondK D a w ≤ natCondK D (finsetListCode U) w + α + logSlack cStage M := hAw
        _ ≤ logSlack cCover M + α + logSlack cStage M :=
          Nat.add_le_add_right (Nat.add_le_add_right hlist α) _
    calc
      natK D a ≤ natK D w + natCondK D a w + logSlack cInfo M := hKa
      _ ≤ natK D w + (logSlack cCover M + α + logSlack cStage M) +
          logSlack cInfo M := by
        exact Nat.add_le_add_right
          (Nat.add_le_add_left hAwBound (natK D w)) (logSlack cInfo M)
      _ = natK D w + logSlack cCover M + α + logSlack cStage M + logSlack cInfo M := by
        ac_rfl
  have hSlackSum :
      logSlack cCover M + logSlack cStage M + logSlack cInfo M +
          2 * logSlack c₀ M = logSlack c M := by
    unfold logSlack
    dsimp [c]
    ring
  have hmain : q ≤ natK D w + t + logSlack cCover M + logSlack cStage M +
      logSlack cInfo M + 2 * logSlack c₀ M := by omega
  calc
    q ≤ natK D w + t + logSlack cCover M + logSlack cStage M +
        logSlack cInfo M + 2 * logSlack c₀ M := hmain
    _ = natK D w + t +
        (logSlack cCover M + logSlack cStage M + logSlack cInfo M +
          2 * logSlack c₀ M) := by ac_rfl
    _ = natK D w + t + logSlack c M := by rw [hSlackSum]

/-- Symmetry of information gives bounds on `K(xᵢ | w)` and `K(w | xᵢ)`.  With
`K(w) ≤ q + δ + 3t + O(log M)`, `K(xᵢ | w) ≤ K(xᵢ) - q + δ + 3t + O(log M)` and
`q ≤ K(xᵢ) + t + O(log M)` (so `K(xᵢ) - q ≥ K(xᵢ) - q` loses at most `t + O(log M)` through the
truncated subtraction), `K(w | xᵢ) ≤ K(w) + K(xᵢ | w) - K(xᵢ) + O(log M) ≤ 2δ + 7t + O(log M)
≤ 3δ + O(log M)` (using `8t ≤ δ`, `K(w), K(xᵢ) = O(M)`); the other conclusions follow from
`q ≤ K(w) + t + O(log M)` and `K(w) ≤ q + δ + 3t + O(log M) = O(M)`. -/
private theorem theorem2_symmetry
    (D : Map) (hD : isOptimalConditional D) (cQ cL cU cC : ℕ) :
    ∃ c : ℕ, ∀ (x₁ x₂ z w : BitString) (q t δ M : ℕ),
      M = natK D (pairCode (pairCode x₁ x₂) z) →
      t ≤ M → 8 * (t + logSlack 1 M) ≤ δ → δ ≤ M →
      q ≤ 2 * M + logSlack cQ M →
      q ≤ natK D x₁ + t + logSlack cQ M →
      q ≤ natK D x₂ + t + logSlack cQ M →
      q ≤ natK D w + t + logSlack cL M →
      natK D w ≤ q + δ + 3 * t + logSlack cU M →
      natCondK D x₁ w ≤ natK D x₁ - q + δ + 3 * t + logSlack cC M →
      natCondK D x₂ w ≤ natK D x₂ - q + δ + 3 * t + logSlack cC M →
        q ≤ natK D w + 2 * δ + logSlack c M ∧
        natCondK D w x₁ ≤ 3 * δ + logSlack c M ∧
        natCondK D w x₂ ≤ 3 * δ + logSlack c M ∧
        natK D w ≤ c * (M + 1) := by
  obtain ⟨cSym, hSym⟩ := Kolmogorov.pairPlainK_symmetryOfInformation_values D hD
  obtain ⟨cSwap, hSwap⟩ := plainK_map_le D hD swapPairCode swapPairCode_computable
  obtain ⟨cProj₁, hProj₁⟩ := plainK_map_le D hD
    (decodeFirst ∘ decodeFirst)
    (decodeFirst_computable.comp decodeFirst_computable)
  obtain ⟨cProj₂, hProj₂⟩ := plainK_map_le D hD
    (decodeSecond ∘ decodeFirst)
    (decodeSecond_computable.comp decodeFirst_computable)
  obtain ⟨cPair, hPair⟩ := plainK_pair_le_two_mul D hD
  let b := max (max (cProj₁ + 1) (cProj₂ + 1)) (6 + cQ + cU)
  obtain ⟨cFold, hFold⟩ := logSlack_linear_bound cSym (2 * b) (2 * b + cPair + 1)
  let c := b + cL + cC + cU + cQ + 2 * cFold + cSwap
  refine ⟨c, ?_⟩
  intro x₁ x₂ z w q t δ M hM ht hδ hδM hq₀ hq₁ hq₂ hqL hKw hCond₁ hCond₂
  have hb₁ : cProj₁ + 1 ≤ b := by
    dsimp [b]
    exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hb₂ : cProj₂ + 1 ≤ b := by
    dsimp [b]
    exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hb₃ : 6 + cQ + cU ≤ b := by
    dsimp [b]
    exact le_max_right _ _
  have hcL : cL ≤ c := by dsimp [c]; omega
  have hcC : cC ≤ c := by dsimp [c]; omega
  have hcU : cU ≤ c := by dsimp [c]; omega
  have hcQ : cQ ≤ c := by dsimp [c]; omega
  have hcSwap : cSwap ≤ c := by dsimp [c]; omega
  have hKx₁ : natK D x₁ ≤ M + cProj₁ := by
    have hh := hProj₁ (pairCode (pairCode x₁ x₂) z)
    have hh' : plainK D x₁ ≤ plainK D (pairCode (pairCode x₁ x₂) z) + (cProj₁ : ℕ∞) := by
      simpa [Function.comp_apply, decodeFirst_pairCode] using hh
    rw [commonInfo_le_mutualInfo_hasPlainValue D hD x₁,
      commonInfo_le_mutualInfo_hasPlainValue D hD (pairCode (pairCode x₁ x₂) z)] at hh'
    have hhNat : natK D x₁ ≤ M + cProj₁ := by
      have hcast : (natK D x₁ : ℕ∞) ≤ ((M + cProj₁ : ℕ) : ℕ∞) := by
        rw [Nat.cast_add, hM]
        exact hh'
      exact_mod_cast hcast
    exact hhNat
  have hKx₂ : natK D x₂ ≤ M + cProj₂ := by
    have hh := hProj₂ (pairCode (pairCode x₁ x₂) z)
    have hh' : plainK D x₂ ≤ plainK D (pairCode (pairCode x₁ x₂) z) + (cProj₂ : ℕ∞) := by
      simpa [Function.comp_apply, decodeFirst_pairCode, decodeSecond_pairCode] using hh
    rw [commonInfo_le_mutualInfo_hasPlainValue D hD x₂,
      commonInfo_le_mutualInfo_hasPlainValue D hD (pairCode (pairCode x₁ x₂) z)] at hh'
    have hcast : (natK D x₂ : ℕ∞) ≤ ((M + cProj₂ : ℕ) : ℕ∞) := by
      rw [Nat.cast_add, hM]
      exact hh'
    exact_mod_cast hcast
  have hLogQ : logSlack cQ M ≤ cQ * (M + 1) := by
    unfold logSlack
    calc
      cQ * (Nat.bits M).length + cQ ≤ cQ * M + cQ := by
        exact Nat.add_le_add_right (Nat.mul_le_mul_left cQ (length_natBits_le M)) cQ
      _ = cQ * (M + 1) := by rw [Nat.mul_add]; simp
  have hLogU : logSlack cU M ≤ cU * (M + 1) := by
    unfold logSlack
    calc
      cU * (Nat.bits M).length + cU ≤ cU * M + cU := by
        exact Nat.add_le_add_right (Nat.mul_le_mul_left cU (length_natBits_le M)) cU
      _ = cU * (M + 1) := by rw [Nat.mul_add]; simp
  have hKwLinear : natK D w ≤ (6 + cQ + cU) * (M + 1) := by
    calc
      natK D w ≤ q + δ + 3 * t + logSlack cU M := hKw
      _ ≤ 2 * M + logSlack cQ M + M + 3 * M + logSlack cU M := by omega
      _ ≤ 6 * M + cQ * (M + 1) + cU * (M + 1) := by omega
      _ = 6 * M + (cQ * (M + 1) + cU * (M + 1)) := by omega
      _ = 6 * M + (cQ + cU) * (M + 1) := by rw [← Nat.add_mul]
      _ ≤ 6 * (M + 1) + (cQ + cU) * (M + 1) := by gcongr; omega
      _ = 6 * (M + 1) + cQ * (M + 1) + cU * (M + 1) := by
        rw [Nat.add_mul]
        rw [Nat.add_assoc]
      _ = (6 + cQ) * (M + 1) + cU * (M + 1) := by rw [← Nat.add_mul]
      _ = (6 + cQ + cU) * (M + 1) := by rw [← Nat.add_mul]
  have hX₁Linear : natK D x₁ ≤ b * (M + 1) := by
    have hFactor : M + cProj₁ ≤ (cProj₁ + 1) * (M + 1) := by
      calc
        M + cProj₁ ≤ M + cProj₁ * (M + 1) := by
          have hmul : cProj₁ ≤ cProj₁ * (M + 1) := by
            have hh := Nat.mul_le_mul_left cProj₁ (by omega : 1 ≤ M + 1)
            simpa using hh
          exact Nat.add_le_add_left hmul M
        _ ≤ cProj₁ * (M + 1) + (M + 1) := by omega
        _ = (cProj₁ + 1) * (M + 1) := by rw [Nat.add_mul]; simp
    exact hKx₁.trans (hFactor.trans (Nat.mul_le_mul_right (M + 1) hb₁))
  have hX₂Linear : natK D x₂ ≤ b * (M + 1) := by
    have hFactor : M + cProj₂ ≤ (cProj₂ + 1) * (M + 1) := by
      calc
        M + cProj₂ ≤ M + cProj₂ * (M + 1) := by
          have hmul : cProj₂ ≤ cProj₂ * (M + 1) := by
            have hh := Nat.mul_le_mul_left cProj₂ (by omega : 1 ≤ M + 1)
            simpa using hh
          exact Nat.add_le_add_left hmul M
        _ ≤ cProj₂ * (M + 1) + (M + 1) := by omega
        _ = (cProj₂ + 1) * (M + 1) := by rw [Nat.add_mul]; simp
    exact hKx₂.trans (hFactor.trans (Nat.mul_le_mul_right (M + 1) hb₂))
  have hWLinear : natK D w ≤ b * (M + 1) :=
    hKwLinear.trans (Nat.mul_le_mul_right (M + 1) hb₃)
  have hPairBound : ∀ x y : BitString, natK D x ≤ b * (M + 1) →
      natK D y ≤ b * (M + 1) →
      natK D (pairCode x y) ≤ 2 * (b * (M + 1)) + cPair := by
    intro x y hx hy
    have hxENat : plainK D x ≤ (b * (M + 1) : ℕ∞) := by
      rw [commonInfo_le_mutualInfo_hasPlainValue D hD x]
      exact_mod_cast hx
    have hyENat : plainK D y ≤ (b * (M + 1) : ℕ∞) := by
      rw [commonInfo_le_mutualInfo_hasPlainValue D hD y]
      exact_mod_cast hy
    have hPairInst := hPair (b * (M + 1)) x y hxENat hyENat
    change plainK D (pairCode x y) ≤ _ at hPairInst
    rw [commonInfo_le_mutualInfo_hasPlainValue D hD (pairCode x y)] at hPairInst
    exact_mod_cast hPairInst
  have hLogPair : ∀ x y : BitString, natK D x ≤ b * (M + 1) →
      natK D y ≤ b * (M + 1) →
      logSlack cSym (natK D (pairCode x y) + 1) ≤ logSlack cFold M := by
    intro x y hx hy
    have hArg : natK D (pairCode x y) + 1 ≤
        2 * b * M + (2 * b + cPair + 1) := by
      calc
        natK D (pairCode x y) + 1 ≤ 2 * (b * (M + 1)) + cPair + 1 :=
          Nat.add_le_add_right (hPairBound x y hx hy) 1
        _ = 2 * b * M + (2 * b + cPair + 1) := by ring
    calc
      logSlack cSym (natK D (pairCode x y) + 1) ≤
          logSlack cSym (2 * b * M + (2 * b + cPair + 1)) :=
        logSlack_mono_right cSym hArg
      _ ≤ logSlack cFold M := hFold M
  have hSymFor : ∀ x : BitString, natK D x ≤ b * (M + 1) →
      q ≤ natK D x + t + logSlack cQ M →
      natCondK D x w ≤ natK D x - q + δ + 3 * t + logSlack cC M →
      natCondK D w x ≤ 3 * δ + logSlack c M := by
    intro x hx hqX hcondX
    let kx := natK D x
    let kw := natK D w
    let kpairXW := natK D (pairCode x w)
    let kpairWX := natK D (pairCode w x)
    let kwx := natCondK D w x
    let kxw := natCondK D x w
    have hxVal : HasPlainComplexityValue D x kx := commonInfo_le_mutualInfo_hasPlainValue D hD x
    have hwVal : HasPlainComplexityValue D w kw := commonInfo_le_mutualInfo_hasPlainValue D hD w
    have hkwxVal : HasPlainConditionalComplexityValue D w x kwx :=
      condK_le_add_condMutualInfo_value D hD w x
    have hkxwVal : HasPlainConditionalComplexityValue D x w kxw :=
      condK_le_add_condMutualInfo_value D hD x w
    have hpXWVal : HasPlainComplexityValue D (pairCode x w) kpairXW :=
      commonInfo_le_mutualInfo_hasPlainValue D hD (pairCode x w)
    have hpWXVal : HasPlainComplexityValue D (pairCode w x) kpairWX :=
      commonInfo_le_mutualInfo_hasPlainValue D hD (pairCode w x)
    have hSymX := hSym x w kx kwx kpairXW hxVal hkwxVal hpXWVal
    have hSymW := hSym w x kw kxw kpairWX hwVal hkxwVal hpWXVal
    have hSwapNat : kpairXW ≤ kpairWX + cSwap := by
      have hh := hSwap (pairCode w x)
      have hh' : plainK D (pairCode x w) ≤ plainK D (pairCode w x) + (cSwap : ℕ∞) := by
        simpa only [swapPairCode_pairCode] using hh
      rw [commonInfo_le_mutualInfo_hasPlainValue D hD (pairCode x w),
        commonInfo_le_mutualInfo_hasPlainValue D hD (pairCode w x)] at hh'
      have hcast : (kpairXW : ℕ∞) ≤ ((kpairWX + cSwap : ℕ) : ℕ∞) := by
        rw [Nat.cast_add]
        exact hh'
      exact_mod_cast hcast
    have hLogXW := hLogPair x w hx hWLinear
    have hLogWX := hLogPair w x hWLinear hx
    have hLogXW' : logSlack cSym (kpairXW + 1) ≤ logSlack cFold M := by
      simpa [kpairXW] using hLogXW
    have hLogWX' : logSlack cSym (kpairWX + 1) ≤ logSlack cFold M := by
      simpa [kpairWX] using hLogWX
    have hStep1 : kpairXW + logSlack cSym (kpairXW + 1) ≤
        kpairWX + cSwap + logSlack cFold M := by
      calc
        kpairXW + logSlack cSym (kpairXW + 1) ≤
            kpairWX + cSwap + logSlack cSym (kpairXW + 1) :=
          Nat.add_le_add_right hSwapNat _
        _ ≤ kpairWX + cSwap + logSlack cFold M :=
          Nat.add_le_add_left hLogXW' _
    have hStep2 : kpairWX + cSwap + logSlack cFold M ≤
        kw + kxw + logSlack cSym (kpairWX + 1) + cSwap + logSlack cFold M := by
      have hh := Nat.add_le_add_right hSymW.1 (cSwap + logSlack cFold M)
      simpa [Nat.add_assoc] using hh
    have hCore : kx + kwx ≤ kw + kxw +
        (logSlack cFold M + cSwap + logSlack cFold M) := by
      calc
        kx + kwx ≤ kpairXW + logSlack cSym (kpairXW + 1) := hSymX.2
        _ ≤ kpairWX + cSwap + logSlack cFold M := hStep1
        _ ≤ kw + kxw + logSlack cSym (kpairWX + 1) + cSwap + logSlack cFold M := hStep2
        _ ≤ kw + kxw + (logSlack cFold M + cSwap + logSlack cFold M) := by
          have hh := Nat.add_le_add_left hLogWX' (kw + kxw + cSwap + logSlack cFold M)
          omega
    have hTotalLogs : logSlack cFold M + cSwap + logSlack cFold M +
        logSlack cC M + logSlack cU M + logSlack cQ M ≤ logSlack c M := by
      have hsum : logSlack c M = logSlack b M + logSlack cL M + logSlack cC M +
          logSlack cU M + logSlack cQ M + logSlack cFold M + logSlack cFold M +
          logSlack cSwap M := by
        dsimp [c]
        unfold logSlack
        ring
      have hconst : cSwap ≤ logSlack cSwap M := by
        unfold logSlack
        omega
      rw [hsum]
      omega
    have hcondBound : kwx ≤ 2 * δ + 7 * t +
        logSlack cFold M + cSwap + logSlack cFold M +
          logSlack cC M + logSlack cU M + logSlack cQ M := by
      have hCore' : natK D x + natCondK D w x ≤ natK D w + natCondK D x w +
          (logSlack cFold M + cSwap + logSlack cFold M) := hCore
      have hqsub : q + (natK D x - q) ≤ natK D x + t + logSlack cQ M := by omega
      have hkw' : natK D w ≤ q + δ + 3 * t + logSlack cU M := hKw
      have hcondX' : natCondK D x w ≤ natK D x - q + δ + 3 * t +
          logSlack cC M := hcondX
      omega
    have hδt : 7 * t ≤ δ := by omega
    calc
      natCondK D w x ≤ 2 * δ + 7 * t +
          logSlack cFold M + cSwap + logSlack cFold M +
            logSlack cC M + logSlack cU M + logSlack cQ M := hcondBound
      _ ≤ 3 * δ + logSlack c M := by omega
  have hLogL : logSlack cL M ≤ logSlack c M := logSlack_mono_left hcL M
  have hQGoal : q ≤ natK D w + 2 * δ + logSlack c M := by
    calc
      q ≤ natK D w + t + logSlack cL M := hqL
      _ ≤ natK D w + 2 * δ + logSlack c M := by
        have htδ : t ≤ δ := by omega
        omega
  have hBLeC : b ≤ c := by dsimp [c]; omega
  have hLinear : natK D w ≤ c * (M + 1) :=
    hWLinear.trans (Nat.mul_le_mul_right (M + 1) hBLeC)
  exact ⟨hQGoal, hSymFor x₁ hX₁Linear hq₁ hCond₁,
    hSymFor x₂ hX₂Linear hq₂ hCond₂, hLinear⟩

/-- In Case 1 of `theorem2_typization_and_cover`, the reservoir
is an `(α, β, γ)`-semi-bunch with `β - α = t + δ/2 + O(log M)` (both bounds on `β` are hypotheses).
Apply Lemma 6 to get a semi-bunch `U_j` with `|A ∩ U_j| ≥ 2 ^ (2α - β - O(1))` and
`K(j) ≤ β + γ - 2α + O(log M)`; counting, for each `x_i`, the pairs `(a, x)` with `a ∈ U_j` and
`K(x | a) ≤ K(x_i) - q + t + O(log M)` gives `K(x_i | j) ≤ K(x_i) - q + δ/2 + 3t + O(log M)`;
`K(j) ≥ q - t - O(log M)` from `K(a) ≥ m + q - O(log)` and `K(a | j) ≤ α + O(log)`; symmetry of
information gives `K(j | x_i) ≤ δ + 5t + O(log M)`; take `w = j`.  (When `δ ≥ M` take `w = ∅`,
as `q ≤ 2M + O(log M)`.) -/
theorem theorem2_cover_semibunch (D : Map)
    (hD : isOptimalConditional D) (c₀ : ℕ) :
    ∃ c : ℕ, ∀ (x₁ x₂ z : BitString) (q t δ M α β γ : ℕ)
      (A : Finset BitString),
      M = natK D (pairCode (pairCode x₁ x₂) z) →
      MutualInfoLe D (pairCode x₁ x₂) z t →
      CommonInfoExtractableRel D x₁ x₂ z q t →
      t ≤ M → 8 * (t + logSlack 1 M) ≤ δ →
      A.card = 2 ^ α →
      natK D z ≤ α + t + logSlack c₀ M →
      α ≤ natK D z + t + logSlack c₀ M →
      2 * (natK D z + logSlack c₀ M) + δ ≤ 2 * β →
      2 * β ≤ 2 * (natK D z + logSlack c₀ M) + δ + 1 →
      γ ≤ natK D z + q + logSlack c₀ M + 1 →
      (∀ a ∈ A, ∃ v' z', a = pairCode v' z' ∧
        q ≤ natCondK D v' z' + logSlack c₀ M ∧
        natCondK D v' (pairCode x₁ z') ≤ t + logSlack c₀ M ∧
        natCondK D v' (pairCode x₂ z') ≤ t + logSlack c₀ M ∧
        natCondK D x₁ a ≤ natK D x₁ - q + t + logSlack c₀ M ∧
        natCondK D x₂ a ≤ natK D x₂ - q + t + logSlack c₀ M ∧
        natK D z' ≤ natK D z + logSlack c₀ M ∧
        natK D z ≤ natK D z' + logSlack c₀ M ∧
        natK D a ≤ natK D z + q + logSlack c₀ M ∧
        natK D z + q ≤ natK D a + logSlack c₀ M ∧
        MutualInfoLe D (pairCode x₁ x₂) z' (t + logSlack c₀ M) ∧
        natCondK D a (pairCode x₁ x₂) ≤ α + logSlack c₀ M ∧
        α ≤ natCondK D a (pairCode x₁ x₂) + logSlack c₀ M) →
      IsSemiBunch D α β γ A →
      ∃ w : BitString,
        q ≤ natK D w + 2 * δ + logSlack c M ∧
        natCondK D w x₁ ≤ 3 * δ + logSlack c M ∧
        natCondK D w x₂ ≤ 3 * δ + logSlack c M ∧
        natK D w ≤ c * (M + 1) := by
  obtain ⟨cQ, hQ⟩ :=
    theorem2_extracted_amount_bound
      D hD
  obtain ⟨cLarge, hLarge⟩ :=
    theorem2_large_delta D hD cQ
  obtain ⟨c6, cCov, hCover⟩ :=
    theorem2_lemma6_index D hD c₀ cQ
  obtain ⟨cCount, hCount⟩ :=
    theorem2_counting
      D hD c₀ c6 cCov cQ
  obtain ⟨cLow, hLow⟩ :=
    theorem2_cover_semibunch_lower_bound
      D hD c₀ cCov cQ
  obtain ⟨cSym, hSym⟩ :=
    theorem2_symmetry
      D hD cQ cLow (cCov + 4 * c₀ + 1) cCount
  let c := max cLarge cSym
  have hcLarge : cLarge ≤ c := le_max_left _ _
  have hcSym : cSym ≤ c := le_max_right _ _
  refine ⟨c, ?_⟩
  intro x₁ x₂ z q t δ M α β γ A hM hMI hExtract ht hδ hcard hsize₁ hsize₂
    hbeta hbeta' hgamma hclones hsemi
  obtain ⟨hQ₀, hQ₁, hQ₂⟩ := hQ x₁ x₂ z q t M hM hExtract ht
  by_cases hlarge : M ≤ δ
  · obtain ⟨w, hq, hx₁, hx₂, hw⟩ := hLarge x₁ x₂ q t δ M hδ hlarge hQ₀
    have hlog := logSlack_mono_left hcLarge M
    refine ⟨w, ?_, ?_, ?_, ?_⟩
    · omega
    · omega
    · omega
    · exact hw.trans (Nat.mul_le_mul_right (M + 1) hcLarge)
  · have hsmall : δ ≤ M := by omega
    obtain ⟨w, U, hUcard, hcover, hlist, hwK⟩ :=
      hCover x₁ x₂ z q t δ M α β γ A hM ht hsmall hsize₁ hsize₂ hbeta hbeta' hgamma hQ₀
        hsemi
    have hne : (A ∩ U).Nonempty := by
      rw [← Finset.card_pos]
      by_contra h
      have h0 : (A ∩ U).card = 0 := by omega
      rw [h0] at hcover
      simp at hcover
    obtain ⟨a, haAU⟩ := hne
    obtain ⟨haA, haU⟩ := Finset.mem_inter.1 haAU
    obtain ⟨v', z', hpair, hq', hv₁, hv₂, hcx₁, hcx₂, hz₁, hz₂, ha₁, ha₂, hMI', hcond,
      hcond'⟩ := hclones a haA
    have hcloneX₁ : ∀ b ∈ A, natCondK D x₁ b ≤ natK D x₁ - q + t + logSlack c₀ M := by
      intro b hb
      obtain ⟨v', z', hpair, hq', hv₁, hv₂, hcx₁, hcx₂, hz₁, hz₂, ha₁, ha₂, hMI', hcond,
        hcond'⟩ := hclones b hb
      exact hcx₁
    have hcloneX₂ : ∀ b ∈ A, natCondK D x₂ b ≤ natK D x₂ - q + t + logSlack c₀ M := by
      intro b hb
      obtain ⟨v', z', hpair, hq', hv₁, hv₂, hcx₁, hcx₂, hz₁, hz₂, ha₁, ha₂, hMI', hcond,
        hcond'⟩ := hclones b hb
      exact hcx₂
    have hcount₁ := hCount x₁ x₂ z x₁ q t δ M α β A U w (Or.inl rfl) hM ht hsmall hsize₁
      hsize₂ hbeta hbeta' hQ₀ hUcard hcover hlist hcloneX₁
    have hcount₂ := hCount x₁ x₂ z x₂ q t δ M α β A U w (Or.inr rfl) hM ht hsmall hsize₁
      hsize₂ hbeta hbeta' hQ₀ hUcard hcover hlist hcloneX₂
    have hlow := hLow x₁ x₂ z a w q t M α U hM haU hUcard hlist ha₂ hsize₂ hQ₀
    have hsl : logSlack (cCov + 4 * c₀ + 1) M =
        logSlack cCov M + 4 * logSlack c₀ M + logSlack 1 M := by
      unfold logSlack; ring
    have hwK' : natK D w ≤ q + δ + 3 * t + logSlack (cCov + 4 * c₀ + 1) M := by
      have h1 : 1 ≤ logSlack 1 M := by unfold logSlack; omega
      omega
    obtain ⟨hs₁, hs₂, hs₃, hs₄⟩ := hSym x₁ x₂ z w q t δ M hM ht hδ hsmall hQ₀ hQ₁ hQ₂
      hlow hwK' hcount₁ hcount₂
    have hlog := logSlack_mono_left hcSym M
    refine ⟨w, ?_, ?_, ?_, ?_⟩
    · omega
    · omega
    · omega
    · exact hs₄.trans (Nat.mul_le_mul_right (M + 1) hcSym)

/-- The far-clone half of the dichotomy contains a far pair whose second member has conditional
complexity at least `α - 1` given the original pair and the first clone, by counting. -/
theorem theorem2_select_pair
    (D : Map) (hD : isOptimalConditional D) (x₁ x₂ : BitString) (α β : ℕ)
    (A : Finset BitString) (hcard : A.card = 2 ^ α)
    (hbad : ∃ a ∈ A, A.card ≤ 2 * (A.filter fun b => β ≤ natCondK D b a).card) :
    ∃ a b : BitString, a ∈ A ∧ b ∈ A ∧ β ≤ natCondK D b a ∧
      α ≤ natCondK D b (pairCode (pairCode x₁ x₂) a) + 1 := by
  classical
  obtain ⟨a, ha, hcount⟩ := hbad
  let S := A.filter fun b => β ≤ natCondK D b a
  have hcountS : 2 ^ α ≤ 2 * S.card := by
    simpa [S, hcard] using hcount
  have hSpos : 0 < S.card := by
    have hpow : 0 < 2 ^ α := Nat.pow_pos (by decide)
    omega
  obtain ⟨b₀, hb₀⟩ := Finset.card_pos.mp hSpos
  have hex : ∃ b ∈ S, α ≤ natCondK D b (pairCode (pairCode x₁ x₂) a) + 1 := by
    by_cases hα : α ≤ 1
    · exact ⟨b₀, hb₀, by omega⟩
    · have hα2 : 2 ≤ α := by omega
      by_contra hn
      push Not at hn
      have hsub : S ⊆ compressibleWords D (pairCode (pairCode x₁ x₂) a) (α - 2) := by
        intro y hy
        rw [mem_compressibleWords_iff]
        have hbound : natCondK D y (pairCode (pairCode x₁ x₂) a) ≤ α - 2 := by
          have hnot := hn y hy
          omega
        have hne : condK D y (pairCode (pairCode x₁ x₂) a) ≠ ⊤ := by
          obtain ⟨c, hc⟩ := condK_le_plainK D hD
          obtain ⟨c', hc'⟩ := plainK_le_length D hD
          have hp : plainK D y ≠ ⊤ := ne_top_of_le_natCast_add (hc' y)
          obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hp
          refine ne_top_of_le_natCast (n := k + c) ((hc y _).trans ?_)
          rw [← hk]
          push_cast
          exact le_rfl
        calc
          condK D y (pairCode (pairCode x₁ x₂) a) =
              (natCondK D y (pairCode (pairCode x₁ x₂) a) : ℕ∞) :=
            (ENat.natCast_toNat hne).symm
          _ ≤ ((α - 2 : ℕ) : ℕ∞) := by exact_mod_cast hbound
      have hsmall : S.card < 2 ^ (α - 1) := by
        have h := (Finset.card_le_card hsub).trans_lt
          (card_compressibleWordsLt D (pairCode (pairCode x₁ x₂) a) (α - 2))
        have hshift : α - 2 + 1 = α - 1 := by omega
        rw [hshift] at h
        exact h
      have hpow : 2 ^ α = 2 * 2 ^ (α - 1) := by
        calc
          2 ^ α = 2 ^ ((α - 1) + 1) := by congr 1; omega
          _ = 2 ^ (α - 1) * 2 := by rw [Nat.pow_succ]
          _ = 2 * 2 ^ (α - 1) := by omega
      rw [hpow] at hcountS
      omega
  obtain ⟨b, hb, hcomplex⟩ := hex
  rw [Finset.mem_filter] at hb
  exact ⟨a, b, ha, hb.1, hb.2, hcomplex⟩

end Kolmogorov.Relativization
