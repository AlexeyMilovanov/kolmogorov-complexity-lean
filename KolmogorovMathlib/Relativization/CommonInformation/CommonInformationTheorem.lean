/-
Copyright (c) 2026 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Relativization.CommonInformation.PairPaddingBounds
import KolmogorovMathlib.Relativization.CommonInformation.SublinearDelta
import KolmogorovMathlib.Relativization.CommonInformation.FiniteIteration

/-!
# Common Information Theorem

This module proves the common information theorem and derives a profile consequence from
Conjecture 3.  It formalizes the common information argument in Theorem 2 and the related
conjecture implications in Muchnik and Romashchenko's paper on relativization.
-/

namespace Kolmogorov.Relativization
open Filter Asymptotics

/-- For a small initial tuple,
the extracted amount is bounded by its tuple complexity, threshold, and a logarithmic coding
term.  Thus the empty string handles the finite initial segment after the error functions are
enlarged there. -/
private theorem theorem2_small_input_bound
    (D : Map) (hD : isOptimalConditional D) :
    ∃ a b : ℕ, ∀ (x₁ x₂ z : BitString) (q t : ℕ),
      MutualInfoLe D (pairCode x₁ x₂) z t →
      CommonInfoExtractableRel D x₁ x₂ z q t →
      q ≤ a * (natK D (pairCode (pairCode x₁ x₂) z) + t +
        logSlack a (natK D (pairCode (pairCode x₁ x₂) z) + t + 1)) + a ∧
      natCondK D [] x₁ ≤ b ∧ natCondK D [] x₂ ≤ b ∧ natK D [] ≤ b := by
  obtain ⟨cCtx, hCtx⟩ := condK_le_condK_pair_add_two_plainK D hD
  obtain ⟨cProj, hProj⟩ := pairPlainK_left_le D hD
  obtain ⟨cCond, hCond⟩ := condK_le_plainK D hD
  obtain ⟨cLen, hLen⟩ := plainK_le_length D hD
  let a := cCtx + 4 * cProj + 4
  let b := cCond + cLen
  refine ⟨a, b, ?_⟩
  intro x₁ x₂ z q t hMI hExtract
  let N := natK D (pairCode (pairCode x₁ x₂) z)
  rcases hExtract with ⟨v, hq, hv₁, hv₂⟩
  have hPair12 : natK D (pairCode x₁ x₂) ≤ N + cProj := by
    have h := hProj (pairCode x₁ x₂) z
    change plainK D (pairCode x₁ x₂) ≤
      plainK D (pairCode (pairCode x₁ x₂) z) + (cProj : ℕ∞) at h
    rw [commonInfo_le_mutualInfo_hasPlainValue D hD (pairCode x₁ x₂),
      commonInfo_le_mutualInfo_hasPlainValue D hD (pairCode (pairCode x₁ x₂) z)] at h
    exact_mod_cast h
  have hX₁ : natK D x₁ ≤ N + 2 * cProj := by
    have h := hProj x₁ x₂
    change plainK D x₁ ≤ plainK D (pairCode x₁ x₂) + (cProj : ℕ∞) at h
    rw [commonInfo_le_mutualInfo_hasPlainValue D hD x₁,
      commonInfo_le_mutualInfo_hasPlainValue D hD (pairCode x₁ x₂)] at h
    have hNat : natK D x₁ ≤ natK D (pairCode x₁ x₂) + cProj := by
      exact_mod_cast h
    omega
  have hCtxNat : natCondK D v z ≤
      natCondK D v (pairCode x₁ z) + 2 * natK D x₁ + cCtx := by
    have h := hCtx v x₁ z
    rw [commonInfo_le_mutualInfo_hasCondValue D hD v z,
      commonInfo_le_mutualInfo_hasCondValue D hD v (pairCode x₁ z)] at h
    have hcv : cVal D x₁ = natK D x₁ := rfl
    rw [hcv] at h
    have hNat : natCondK D v z ≤
        natCondK D v (pairCode x₁ z) + (2 * natK D x₁ + cCtx) := by
      exact_mod_cast h
    simpa [Nat.add_assoc] using hNat
  have hqBound : q ≤ t + 2 * (N + 2 * cProj) + cCtx := by
    calc
      q ≤ natCondK D v z := hq
      _ ≤ natCondK D v (pairCode x₁ z) + 2 * natK D x₁ + cCtx := hCtxNat
      _ ≤ t + 2 * (N + 2 * cProj) + cCtx := by omega
  have ha : 2 ≤ a := by dsimp [a]; omega
  have hProdN : 2 * N ≤ a * N := Nat.mul_le_mul_right N ha
  have haOne : 1 ≤ a := by omega
  have hProdT : t ≤ a * t := by
    simpa using (Nat.mul_le_mul_right t haOne)
  have hConst : 4 * cProj + cCtx ≤ a := by dsimp [a]; omega
  have hqLargeBase : t + 2 * (N + 2 * cProj) + cCtx ≤ a * (N + t) + a := by
    nlinarith [hProdN, hProdT, hConst]
  have hArg : N + t ≤ N + t + logSlack a (N + t + 1) := by omega
  have hMulArg := Nat.mul_le_mul_left a hArg
  have hqLarge : t + 2 * (N + 2 * cProj) + cCtx ≤
      a * (N + t + logSlack a (N + t + 1)) + a := by
    calc
      t + 2 * (N + 2 * cProj) + cCtx ≤ a * (N + t) + a := hqLargeBase
      _ ≤ a * (N + t + logSlack a (N + t + 1)) + a :=
        Nat.add_le_add_right hMulArg a
  have hQ : q ≤ a * (N + t + logSlack a (N + t + 1)) + a := hqBound.trans hqLarge
  have hEmpty₁ : natCondK D [] x₁ ≤ b := by
    have h := hCond [] x₁
    rw [commonInfo_le_mutualInfo_hasCondValue D hD [] x₁,
      commonInfo_le_mutualInfo_hasPlainValue D hD []] at h
    have hNat : natCondK D [] x₁ ≤ natK D [] + cCond := by exact_mod_cast h
    have hEmpty : natK D [] ≤ cLen := by
      have hh := hLen []
      rw [commonInfo_le_mutualInfo_hasPlainValue D hD []] at hh
      exact_mod_cast (by simpa using hh)
    dsimp [b]
    omega
  have hEmpty₂ : natCondK D [] x₂ ≤ b := by
    have h := hCond [] x₂
    rw [commonInfo_le_mutualInfo_hasCondValue D hD [] x₂,
      commonInfo_le_mutualInfo_hasPlainValue D hD []] at h
    have hNat : natCondK D [] x₂ ≤ natK D [] + cCond := by exact_mod_cast h
    have hEmpty : natK D [] ≤ cLen := by
      have hh := hLen []
      rw [commonInfo_le_mutualInfo_hasPlainValue D hD []] at hh
      exact_mod_cast (by simpa using hh)
    dsimp [b]
    omega
  have hEmptyK : natK D [] ≤ b := by
    have hh := hLen []
    rw [commonInfo_le_mutualInfo_hasPlainValue D hD []] at hh
    have hEmpty : natK D [] ≤ cLen := by exact_mod_cast (by simpa using hh)
    dsimp [b]
    omega
  exact ⟨hQ, hEmpty₁, hEmpty₂, hEmptyK⟩

/-- Iterate the single-stage alternative from
`theorem2_typization_and_cover`.  Replacing the oracle multiplies the current threshold,
while the extracted amount increases; the conditional mutual-information inequality bounds the
number of replacements.  The resulting string has complexity at least `q - loss N` and has
conditional complexity at most `threshold N`, with both error functions sublinear. -/
private theorem theorem2_iterate_oracle
    (D : Map) (hD : isOptimalConditional D) (f : ℕ → ℕ)
    (hf : (fun N : ℕ => (f N : ℝ)) =o[atTop] fun N : ℕ => (N : ℝ))
    (hStage : ∃ c : ℕ, ∀ (x₁ x₂ z : BitString) (q t δ M : ℕ),
      M = natK D (pairCode (pairCode x₁ x₂) z) →
      MutualInfoLe D (pairCode x₁ x₂) z t →
      CommonInfoExtractableRel D x₁ x₂ z q t →
      t ≤ M → 8 * (t + logSlack 1 M) ≤ δ →
      (∃ w : BitString,
        q ≤ natK D w + 2 * δ + logSlack c M ∧
        natCondK D w x₁ ≤ 3 * δ + logSlack c M ∧
        natCondK D w x₂ ≤ 3 * δ + logSlack c M ∧
        natK D w ≤ c * (M + 1)) ∨
      (∃ (z' : BitString) (q' : ℕ),
        2 * q + δ ≤ 2 * q' ∧
        MutualInfoLe D (pairCode x₁ x₂) z' (3 * t + logSlack c M) ∧
        CommonInfoExtractableRel D x₁ x₂ z' q' (3 * t + logSlack c M) ∧
        natK D (pairCode (pairCode x₁ x₂) z') ≤ 4 * M + logSlack c M)) :
    ∃ loss threshold : ℕ → ℕ, ∃ C : ℕ,
      ((fun N : ℕ => (loss N : ℝ)) =o[atTop] fun N : ℕ => (N : ℝ)) ∧
      ((fun N : ℕ => (threshold N : ℝ)) =o[atTop] fun N : ℕ => (N : ℝ)) ∧
      ∀ (x₁ x₂ z : BitString) (q : ℕ),
        MutualInfoLe D (pairCode x₁ x₂) z
          (f (natK D (pairCode (pairCode x₁ x₂) z))) →
        CommonInfoExtractableRel D x₁ x₂ z q
          (f (natK D (pairCode (pairCode x₁ x₂) z))) →
        ∃ w : BitString,
          q ≤ natK D w + loss (natK D (pairCode (pairCode x₁ x₂) z)) ∧
          natCondK D w x₁ ≤ threshold (natK D (pairCode (pairCode x₁ x₂) z)) ∧
          natCondK D w x₂ ≤ threshold (natK D (pairCode (pairCode x₁ x₂) z)) ∧
          natK D w ≤ C * (natK D (pairCode (pairCode x₁ x₂) z) + 1) := by
  obtain ⟨c, hStage'⟩ := hStage
  obtain ⟨A, B, CIter, hFinite⟩ :=
    theorem2_finite_iteration D hD c hStage'
  obtain ⟨a, b, hSmall⟩ := theorem2_small_input_bound D hD
  obtain ⟨loss, threshold, rounds, delta, N₀, hLoss, hThreshold,
      hSmallBudget, hLargeBudget⟩ :=
    theorem2_choose_budgets f hf a b A B
  refine ⟨loss, threshold, max CIter b, hLoss, hThreshold, ?_⟩
  intro x₁ x₂ z q hMI hExtract
  let N := natK D (pairCode (pairCode x₁ x₂) z)
  change MutualInfoLe D (pairCode x₁ x₂) z (f N) at hMI
  change CommonInfoExtractableRel D x₁ x₂ z q (f N) at hExtract
  by_cases hN : N < N₀
  · obtain ⟨hQ, hEmpty₁, hEmpty₂, hEmptyK⟩ := hSmall x₁ x₂ z q (f N) hMI hExtract
    obtain ⟨hLossN, hThresholdN⟩ := hSmallBudget N hN
    refine ⟨[], ?_, ?_, ?_, ?_⟩
    · calc
        q ≤ a * (N + f N + logSlack a (N + f N + 1)) + a := hQ
        _ ≤ loss N := hLossN
        _ ≤ natK D [] + loss N := by omega
    · exact hEmpty₁.trans hThresholdN
    · exact hEmpty₂.trans hThresholdN
    · calc
        natK D [] ≤ b := hEmptyK
        _ ≤ max CIter b := Nat.le_max_right _ _
        _ = max CIter b * 1 := by simp
        _ ≤ max CIter b * (N + 1) :=
          Nat.mul_le_mul_left _ (by omega)
  · have hN₀ : N ≥ N₀ := by omega
    obtain ⟨hTwo, hRounds, hDelta, hLog, hProgress, hGrowth, hLossN,
        hThresholdN⟩ := hLargeBudget N hN₀
    have hFactor : 1 ≤ 8 * 3 ^ (rounds N) := by
      have hp : 0 < 8 * 3 ^ (rounds N) := by positivity
      omega
    have hFactorSum : f N + logSlack B N ≤
        8 * 3 ^ (rounds N) * (f N + logSlack B N) := by
      have hmul := Nat.mul_le_mul_right (f N + logSlack B N) hFactor
      simpa using hmul
    have hfN : f N ≤ delta N := by omega
    obtain ⟨w, hq, hx₁, hx₂, hw⟩ := hFinite x₁ x₂ z q (f N) N
      (delta N) (rounds N) rfl hMI hExtract (by omega) hTwo hRounds hDelta hLog
      hProgress hGrowth
    refine ⟨w, ?_, ?_, ?_, ?_⟩
    · calc
        q ≤ natK D w + (4 * delta N + logSlack A N) := by
          simpa [Nat.add_assoc] using hq
        _ ≤ natK D w + loss N := Nat.add_le_add_left hLossN _
    · exact hx₁.trans hThresholdN
    · exact hx₂.trans hThresholdN
    · calc
        natK D w ≤ CIter * (N + 1) := hw
        _ ≤ max CIter b * (N + 1) :=
          Nat.mul_le_mul_right _ (Nat.le_max_left _ _)

/- The first part of the padding argument is independent of the asymptotic choice of the final
threshold.  It records the actual properties needed of the padded witness, including a linear
complexity bound for the new string. -/
/-- Add a string that is
incompressible relative to the intermediate witness.  At linear scale, its complexity raises the
plain complexity to the requested amount, while the conditional description costs are bounded by
the padding length and a logarithmic term. -/
private theorem theorem2_pad_at_linear_scale_aux_pair_upper
    (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ (w s : BitString),
      natK D (pairCode w s) ≤ 3 * natK D w + s.length + c := by
  obtain ⟨cPair, hPair⟩ := plainK_pair_le_add_two_log D hD
  obtain ⟨cLen, hLen⟩ := plainK_le_length D hD
  have hPlainFinite (x : BitString) : plainK D x ≠ ⊤ := by
    exact Kolmogorov.ne_top_of_le_natCast_add (hLen x)
  have hPlainValue (x : BitString) : plainK D x = (natK D x : ℕ∞) := by
    change plainK D x = ((plainK D x).toNat : ℕ∞)
    exact (ENat.natCast_toNat (hPlainFinite x)).symm
  refine ⟨cPair + cLen, fun w s => ?_⟩
  have hPairCast :
      (natK D (pairCode w s) : ℕ∞) ≤
        (natK D w : ℕ∞) + (natK D s : ℕ∞) +
          ((2 * Nat.log 2 (natK D w) + cPair : ℕ) : ℕ∞) := by
    simpa [Kolmogorov.cPair, Kolmogorov.cVal, hPlainValue] using hPair w s
  have hPairNat : natK D (pairCode w s) ≤
      natK D w + natK D s + (2 * Nat.log 2 (natK D w) + cPair) := by
    exact_mod_cast hPairCast
  have hLenCast : (natK D s : ℕ∞) ≤ (s.length + cLen : ℕ∞) := by
    have h := hLen s
    rw [hPlainValue s] at h
    simpa [programLength] using h
  have hLenNat : natK D s ≤ s.length + cLen := by
    exact_mod_cast hLenCast
  have hLog : Nat.log 2 (natK D w) ≤ natK D w := Nat.log_le_self 2 _
  nlinarith [hPairNat, hLog, hLenNat]

/-- Absorb the symmetry slack at a pair complexity with one logarithmic padding term. -/
private theorem theorem2_pad_at_linear_scale_aux_absorb_log_overhead
    (a c m : ℕ) :
    ∃ p : ℕ, ∀ N : ℕ,
      logSlack a N +
        logSlack c (m * (N + 1) + logSlack p N + 1) ≤ logSlack p N := by
  let T := a + c + m + 4
  let p := 2 ^ (4 * T)
  refine ⟨p, fun N => ?_⟩
  let A := m + p + 1
  let X := m * (N + 1) + logSlack p N + 1
  have hT : 4 ≤ T := by dsimp [T]; omega
  have hTpow : T < 2 ^ T := Nat.lt_pow_self (by decide : 1 < 2)
  have hpowT : 2 ^ T ≤ p := by
    dsimp [p]
    exact Nat.pow_le_pow_right (by omega : 0 < 2) (by dsimp [T]; omega)
  have hMpow : m + 1 ≤ 2 ^ T := by
    have hm : m + 1 ≤ T := by dsimp [T]; omega
    exact hm.trans hTpow.le
  have hMA : m + 1 ≤ p := hMpow.trans hpowT
  have hAexp : A < 2 ^ (4 * T + 2) := by
    calc
      A ≤ 2 * p := by dsimp [A]; omega
      _ = 2 ^ (4 * T + 1) := by
        dsimp [p]
        rw [Nat.pow_succ]
        ring
      _ < 2 ^ (4 * T + 2) := by
        calc
          2 ^ (4 * T + 1) < 2 ^ (4 * T + 1) * 2 := by
            nlinarith [Nat.two_pow_pos (4 * T + 1)]
          _ = 2 ^ (4 * T + 2) := by rw [Nat.pow_succ]; ring
  have hlogA : Nat.log 2 A ≤ 4 * T + 1 := by
    have h := Nat.log_lt_of_lt_pow' (by omega : 4 * T + 2 ≠ 0) hAexp
    omega
  have hpEq : p = (2 ^ T) ^ 4 := by
    dsimp [p]
    rw [show 4 * T = T * 4 by omega, Nat.pow_mul]
  have hpLarge : T ^ 4 ≤ p := by
    rw [hpEq]
    exact Nat.pow_le_pow_left hTpow.le 4
  have hT2 : 16 ≤ T ^ 2 := by nlinarith [hT]
  have hT4 : 4 * T ^ 2 + 6 * T ≤ T ^ 4 := by
    have hm := Nat.mul_le_mul_right (T ^ 2) hT2
    nlinarith [hm, hT2, hT]
  have hconst : a + c + c * (Nat.log 2 A + 3) ≤ p := by
    have ha : a ≤ T := by dsimp [T]; omega
    have hc : c ≤ T := by dsimp [T]; omega
    have hmul : c * (Nat.log 2 A + 3) ≤ T * (4 * T + 4) :=
      Nat.mul_le_mul hc (by omega)
    nlinarith [ha, hc, hmul, hT4, hpLarge]
  have hNlt : N < 2 ^ (Nat.bits N).length := by
    simpa [Nat.size_eq_bits_len] using Nat.lt_size_self N
  have hNplus : N + 1 ≤ 2 ^ (Nat.bits N).length := by omega
  have hAlength : A < 2 ^ (Nat.log 2 A + 1) :=
    Nat.lt_pow_succ_log_self (by decide : 1 < 2) A
  have hXbound : X ≤ A * (N + 1) := by
    have hSlack := logSlack_le_self_linear p N
    dsimp [X, A]
    nlinarith [hSlack]
  have hProduct :
      A * (N + 1) ≤ 2 ^ (Nat.log 2 A + 1) * 2 ^ (Nat.bits N).length :=
    Nat.mul_le_mul hAlength.le hNplus
  have hXlt : X < 2 ^ ((Nat.bits N).length + Nat.log 2 A + 2) := by
    calc
      X ≤ A * (N + 1) := hXbound
      _ ≤ 2 ^ (Nat.log 2 A + 1) * 2 ^ (Nat.bits N).length := hProduct
      _ = 2 ^ (Nat.log 2 A + 1 + (Nat.bits N).length) := by rw [← Nat.pow_add]
      _ ≤ 2 ^ ((Nat.bits N).length + Nat.log 2 A + 1) := by
        apply Nat.pow_le_pow_right (by omega : 0 < 2)
        omega
      _ < 2 ^ ((Nat.bits N).length + Nat.log 2 A + 2) := by
        calc
          2 ^ ((Nat.bits N).length + Nat.log 2 A + 1) <
              2 ^ ((Nat.bits N).length + Nat.log 2 A + 1) * 2 := by
            nlinarith [Nat.two_pow_pos ((Nat.bits N).length + Nat.log 2 A + 1)]
          _ = 2 ^ ((Nat.bits N).length + Nat.log 2 A + 2) := by
            rw [Nat.pow_succ]
            congr 1
  have hBitsX :
      (Nat.bits X).length ≤ (Nat.bits N).length + Nat.log 2 A + 2 := by
    have hsize := Nat.size_le.mpr hXlt
    simpa [Nat.size_eq_bits_len] using hsize
  have hSlackTotal :
      logSlack a N + logSlack c X ≤
        logSlack (a + c) N + c * (Nat.log 2 A + 2) := by
    unfold logSlack
    nlinarith [hBitsX]
  have hFinal : logSlack a N + logSlack c X ≤ logSlack p N := by
    calc
      logSlack a N + logSlack c X ≤
          logSlack (a + c) N + c * (Nat.log 2 A + 2) := hSlackTotal
      _ ≤ logSlack p N := by
        have hCoeff : a + c ≤ p := by omega
        have hConst' : a + c + c * (Nat.log 2 A + 2) ≤ p := by
          nlinarith [hconst]
        have hCoeffMul := Nat.mul_le_mul_right (Nat.bits N).length hCoeff
        unfold logSlack
        omega
  simpa [X] using hFinal

private theorem theorem2_pad_at_linear_scale
    (D : Map) (hD : isOptimalConditional D) (C A : ℕ) :
    ∃ B c : ℕ, ∀ (x₁ x₂ w : BitString) (q N lossN : ℕ),
      q ≤ natK D w + lossN →
      natK D w ≤ C * (N + 1) →
      lossN ≤ N + A →
      ∃ w' : BitString,
        q ≤ natK D w' ∧
        natK D w' ≤ B * (N + 1) ∧
        natCondK D w' x₁ ≤ natCondK D w x₁ + lossN + logSlack c (N + 1) + c ∧
        natCondK D w' x₂ ≤ natCondK D w x₂ + lossN + logSlack c (N + 1) + c := by
  obtain ⟨cPair, hPair⟩ :=
    theorem2_pad_at_linear_scale_aux_pair_upper D hD
  obtain ⟨cLower, hLower⟩ := pairPlainK_chain_lower_values D hD
  obtain ⟨cChain, hChain⟩ := condK_pairCode_chain_upper_values D hD
  obtain ⟨cCond, hCond⟩ := condK_le_plainK D hD
  obtain ⟨cLen, hLen⟩ := plainK_le_length D hD
  let M := 3 * C + (A + 1) + cPair
  obtain ⟨cAbs, hAbs⟩ :=
    theorem2_pad_at_linear_scale_aux_absorb_log_overhead 0 cLower M
  let B := M + 2 * cAbs
  obtain ⟨cFold, hFold⟩ := logSlack_linear_bound cChain B (B + cCond + 1)
  let c := cAbs + cLen + cCond + cFold
  refine ⟨B, c, ?_⟩
  intro x₁ x₂ w q N lossN hq hw hloss
  let r := lossN + logSlack cAbs (N + 1)
  obtain ⟨s, hsLen, hsIncomp⟩ := exists_incompressible_string D w r
  have hsIncompNat : r ≤ natCondK D s w := by
    rw [← ENat.natCast_toNat (condK_ne_top_of_optimal D hD s w)] at hsIncomp
    exact_mod_cast hsIncomp
  have hrBound : r ≤ (A + 1 + 2 * cAbs) * (N + 1) := by
    have hN : 1 ≤ N + 1 := by omega
    have hLoss : lossN ≤ (A + 1) * (N + 1) := by
      calc
        lossN ≤ N + A := hloss
        _ ≤ (A + 1) * (N + 1) := by nlinarith
    have hSlack := logSlack_le_self_linear cAbs (N + 1)
    have hSlack' : logSlack cAbs (N + 1) ≤ 2 * cAbs * (N + 1) := by
      unfold logSlack at hSlack ⊢
      nlinarith [Nat.mul_le_mul_left cAbs hN]
    dsimp [r]
    nlinarith
  have hPairBound : natK D (pairCode w s) ≤ B * (N + 1) := by
    have h := hPair w s
    rw [hsLen] at h
    have hK3 := Nat.mul_le_mul_left 3 hw
    have hConst : cPair ≤ cPair * (N + 1) :=
      by simpa using Nat.mul_le_mul_left cPair (by omega : 1 ≤ N + 1)
    dsimp [B, M]
    nlinarith [h, hK3, hrBound, hConst]
  have hPairAbsBound : natK D (pairCode w s) ≤
      M * (N + 2) + logSlack cAbs (N + 1) := by
    have h := hPair w s
    rw [hsLen] at h
    have hK3 := Nat.mul_le_mul_left 3 hw
    have hConst : cPair ≤ cPair * (N + 1) :=
      by simpa using Nat.mul_le_mul_left cPair (by omega : 1 ≤ N + 1)
    have hSlack := logSlack_le_self_linear cAbs (N + 1)
    have hSlack' : logSlack cAbs (N + 1) ≤ 2 * cAbs * (N + 1) := by
      unfold logSlack at hSlack ⊢
      nlinarith [Nat.mul_le_mul_left cAbs (by omega : 1 ≤ N + 1)]
    dsimp [r, M] at h ⊢
    nlinarith [h, hK3, hConst, hSlack', hloss]
  have hPairPlus : natK D (pairCode w s) + 1 ≤ (B + 1) * (N + 1) := by
    have hN : 1 ≤ N + 1 := by omega
    nlinarith [hPairBound]
  have hAbsArg : natK D (pairCode w s) + 1 ≤
      M * (N + 2) + logSlack cAbs (N + 1) + 1 := by
    omega
  have hError :
      logSlack cLower (natK D (pairCode w s) + 1) ≤ logSlack cAbs (N + 1) := by
    calc
      logSlack cLower (natK D (pairCode w s) + 1) ≤
          logSlack cLower (M * (N + 2) + logSlack cAbs (N + 1) + 1) :=
        logSlack_mono_right cLower hAbsArg
      _ ≤ logSlack cAbs (N + 1) := by
        have h := hAbs (N + 1)
        simpa [logSlack] using h
  have hLowerNat :
      natK D w + r ≤ natK D (pairCode w s) +
        logSlack cLower (natK D (pairCode w s) + 1) := by
    have h := hLower w s (natK D w) (natCondK D s w)
      (natK D (pairCode w s))
      (commonInfo_le_mutualInfo_hasPlainValue D hD w)
      (condK_le_add_condMutualInfo_value D hD s w)
      (commonInfo_le_mutualInfo_hasPlainValue D hD (pairCode w s))
    omega
  have hq' : q ≤ natK D (pairCode w s) := by
    have hPadLower : natK D w + lossN + logSlack cAbs (N + 1) ≤
        natK D (pairCode w s) + logSlack cAbs (N + 1) := by
      calc
        natK D w + lossN + logSlack cAbs (N + 1) = natK D w + r := by
          dsimp [r]
          omega
        _ ≤ natK D (pairCode w s) +
            logSlack cLower (natK D (pairCode w s) + 1) := hLowerNat
        _ ≤ natK D (pairCode w s) + logSlack cAbs (N + 1) :=
          Nat.add_le_add_left hError _
    omega
  have hPlainValue (y : BitString) : plainK D y = (natK D y : ℕ∞) := by
    change plainK D y = ((plainK D y).toNat : ℕ∞)
    exact (ENat.natCast_toNat (ne_top_of_le_natCast_add (hLen y))).symm
  have hCondPairPlain (x : BitString) :
      natCondK D (pairCode w s) x ≤ natK D (pairCode w s) + cCond := by
    have h := hCond (pairCode w s) x
    rw [condK_le_add_condMutualInfo_value D hD (pairCode w s) x,
      hPlainValue (pairCode w s)] at h
    exact_mod_cast h
  have hCondPairPlus (x : BitString) :
      natCondK D (pairCode w s) x + 1 ≤ B * N + (B + cCond + 1) := by
    have h0 := Nat.add_le_add_right (hCondPairPlain x) 1
    nlinarith [hPairBound]
  have hSlackPair (x : BitString) :
      logSlack cChain (natCondK D (pairCode w s) x + 1) ≤ logSlack cFold (N + 1) := by
    calc
      logSlack cChain (natCondK D (pairCode w s) x + 1) ≤
          logSlack cChain (B * N + (B + cCond + 1)) :=
        logSlack_mono_right cChain (hCondPairPlus x)
      _ ≤ logSlack cFold N := hFold N
      _ ≤ logSlack cFold (N + 1) := logSlack_mono_right cFold (by omega)
  have hLiteral : natK D s ≤ s.length + cLen := by
    have h := hLen s
    rw [hPlainValue s] at h
    have h' : (natK D s : ℕ∞) ≤ (s.length + cLen : ℕ∞) := by
      simpa [programLength] using h
    exact_mod_cast h'
  have hCondLiteral (x : BitString) :
      natCondK D s (pairCode w x) ≤ s.length + cLen + cCond := by
    have h := hCond s (pairCode w x)
    rw [condK_le_add_condMutualInfo_value D hD s (pairCode w x), hPlainValue s] at h
    have hNat : natCondK D s (pairCode w x) ≤ natK D s + cCond := by
      exact_mod_cast h
    omega
  have hConditionalBound (x : BitString) :
      natCondK D (pairCode w s) x ≤
        natCondK D w x + s.length + cLen + cCond + logSlack cFold (N + 1) := by
    have h := hChain w s x
      (natCondK D w x) (natCondK D s (pairCode w x))
      (natCondK D (pairCode w s) x)
      (condK_le_add_condMutualInfo_value D hD w x)
      (condK_le_add_condMutualInfo_value D hD s (pairCode w x))
      (condK_le_add_condMutualInfo_value D hD (pairCode w s) x)
    have hS := hCondLiteral x
    have hLog := hSlackPair x
    omega
  have hSlackCombined :
      logSlack cAbs (N + 1) + cLen + cCond + logSlack cFold (N + 1) ≤
        logSlack c (N + 1) := by
    calc
      logSlack cAbs (N + 1) + cLen + cCond + logSlack cFold (N + 1) =
          logSlack cAbs (N + 1) + logSlack cFold (N + 1) + (cLen + cCond) := by omega
      _ = logSlack (cAbs + cFold) (N + 1) + (cLen + cCond) := by
        rw [← logSlack_add_constants]
      _ ≤ logSlack (cAbs + cFold + (cLen + cCond)) (N + 1) :=
        logSlack_add_nat_le (cAbs + cFold) (cLen + cCond) (N + 1)
      _ = logSlack c (N + 1) := by congr 1; dsimp [c]; omega
  refine ⟨pairCode w s, hq', hPairBound, ?_, ?_⟩
  · calc
      natCondK D (pairCode w s) x₁ ≤
          natCondK D w x₁ + s.length + cLen + cCond + logSlack cFold (N + 1) :=
        hConditionalBound x₁
      _ = natCondK D w x₁ + lossN +
          (logSlack cAbs (N + 1) + cLen + cCond + logSlack cFold (N + 1)) := by
        rw [hsLen]
        dsimp [r]
        omega
      _ ≤ natCondK D w x₁ + lossN + logSlack c (N + 1) + c := by
        omega
  · calc
      natCondK D (pairCode w s) x₂ ≤
          natCondK D w x₂ + s.length + cLen + cCond + logSlack cFold (N + 1) :=
        hConditionalBound x₂
      _ = natCondK D w x₂ + lossN +
          (logSlack cAbs (N + 1) + cLen + cCond + logSlack cFold (N + 1)) := by
        rw [hsLen]
        dsimp [r]
        omega
      _ ≤ natCondK D w x₂ + lossN + logSlack c (N + 1) + c := by
        omega

/- A little-o function is globally bounded by a linear function after absorbing its finitely many
initial values into a constant. -/
/-- Use sublinearity of the loss to
obtain a uniform linear bound that also covers the finitely many small arguments. -/
private theorem theorem2_loss_has_linear_bound
    (loss : ℕ → ℕ)
    (hLoss : (fun N : ℕ => (loss N : ℝ)) =o[atTop] fun N : ℕ => (N : ℝ)) :
    ∃ A : ℕ, ∀ N : ℕ, loss N ≤ N + A := by
  have hEventually := hLoss.def (by norm_num : (0 : ℝ) < 1)
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hEventually
  refine ⟨∑ n ∈ Finset.range N₀, loss n, fun N => ?_⟩
  by_cases hN : N < N₀
  · have hmem : N ∈ Finset.range N₀ := Finset.mem_range.mpr hN
    have hle : loss N ≤ ∑ n ∈ Finset.range N₀, loss n :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) hmem
    omega
  · have h := hN₀ N (by omega)
    have hnonneg₁ : 0 ≤ (loss N : ℝ) := Nat.cast_nonneg _
    have hnonneg₂ : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
    have hreal : (loss N : ℝ) ≤ (N : ℝ) := by
      simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg₁, abs_of_nonneg hnonneg₂] using h
    have hnat : loss N ≤ N := by exact_mod_cast hreal
    omega

/- The only asymptotic fact needed at the end is that the two input budgets and the padding
description overhead still form a little-o function. -/
/-- Combine the two sublinear budgets
with the logarithmic padding overhead into one sublinear threshold. -/
private theorem theorem2_combine_sublinear_budgets
    (loss threshold : ℕ → ℕ) (c : ℕ)
    (hLoss : (fun N : ℕ => (loss N : ℝ)) =o[atTop] fun N : ℕ => (N : ℝ))
    (hThreshold : (fun N : ℕ => (threshold N : ℝ)) =o[atTop] fun N : ℕ => (N : ℝ)) :
    ∃ g : ℕ → ℕ,
      ((fun N : ℕ => (g N : ℝ)) =o[atTop] fun N : ℕ => (N : ℝ)) ∧
      ∀ N : ℕ,
        threshold N + loss N + logSlack c (N + 1) + c ≤ g N := by
  let g : ℕ → ℕ := fun N => threshold N + loss N + logSlack c (N + 1) + c
  have hLogShift :
      (fun N : ℕ => Real.log ((N : ℝ) + 1)) =o[atTop]
        fun N : ℕ => (N : ℝ) + 1 :=
    Real.isLittleO_log_id_atTop.comp_tendsto
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hPlus :
      (fun N : ℕ => (N : ℝ) + 1) =O[atTop] fun N : ℕ => (N : ℝ) := by
    apply Asymptotics.isBigO_iff.mpr
    refine ⟨2, ?_⟩
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    have hNReal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hbound : (N : ℝ) + 1 ≤ 2 * (N : ℝ) := by linarith
    have hnormL : ‖(N : ℝ) + 1‖ = (N : ℝ) + 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hnormR : ‖(N : ℝ)‖ = (N : ℝ) := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by exact_mod_cast (Nat.zero_le N))]
    rw [hnormL, hnormR]
    linarith
  have hLogNat :
      (fun N : ℕ => Real.log ((N : ℝ) + 1)) =o[atTop]
        fun N : ℕ => (N : ℝ) := hLogShift.trans_isBigO hPlus
  have hLogb :
      (fun N : ℕ => Real.logb 2 ((N : ℝ) + 1)) =o[atTop]
        fun N : ℕ => (N : ℝ) := by
    have heq : (fun N : ℕ => Real.logb 2 ((N : ℝ) + 1)) =
        fun N : ℕ => (1 / Real.log 2) * Real.log ((N : ℝ) + 1) := by
      funext N
      rw [Real.logb]
      ring
    rw [heq]
    exact Asymptotics.IsLittleO.const_mul_left hLogNat (1 / Real.log 2)
  have hLogbPlus :
      (fun N : ℕ => Real.logb 2 ((N : ℝ) + 1) + 1) =o[atTop]
        fun N : ℕ => (N : ℝ) := by
    have hConstOne : (fun _ : ℕ => (1 : ℝ)) =o[atTop]
        fun N : ℕ => (N : ℝ) :=
      (Asymptotics.isLittleO_const_id_atTop (1 : ℝ)).comp_tendsto
        tendsto_natCast_atTop_atTop
    exact Asymptotics.IsLittleO.add hLogb hConstOne
  have hBits :
      (fun N : ℕ => ((Nat.bits (N + 1)).length : ℝ)) =o[atTop]
        fun N : ℕ => (N : ℝ) := by
    have hBound :
        (fun N : ℕ => ((Nat.bits (N + 1)).length : ℝ)) =O[atTop]
          fun N : ℕ => Real.logb 2 ((N : ℝ) + 1) + 1 := by
      apply Asymptotics.isBigO_iff.mpr
      refine ⟨1, ?_⟩
      filter_upwards [] with N
      have hLength := length_natBits_le_log (N + 1)
      have hLog := Real.natLog_le_logb (N + 1) 2
      have hLog' : (Nat.log 2 (N + 1) : ℝ) ≤
          Real.logb 2 ((N : ℝ) + 1) := by simpa using hLog
      have hLength' : ((Nat.bits (N + 1)).length : ℝ) ≤
          (Nat.log 2 (N + 1) : ℝ) + 1 := by exact_mod_cast hLength
      have hArg : (1 : ℝ) ≤ (N : ℝ) + 1 := by
        exact_mod_cast (show 1 ≤ N + 1 by omega)
      have hLogNonneg : 0 ≤ Real.logb 2 ((N : ℝ) + 1) :=
        Real.logb_nonneg (by norm_num) hArg
      have hFinal : ((Nat.bits (N + 1)).length : ℝ) ≤
          Real.logb 2 ((N : ℝ) + 1) + 1 := by linarith
      have hNormL : ‖((Nat.bits (N + 1)).length : ℝ)‖ =
          ((Nat.bits (N + 1)).length : ℝ) := by
        rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
      have hNormR : ‖Real.logb 2 ((N : ℝ) + 1) + 1‖ =
          Real.logb 2 ((N : ℝ) + 1) + 1 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      rw [hNormL, hNormR]
      simpa using hFinal
    exact hBound.trans_isLittleO hLogbPlus
  have hLogSlack :
      (fun N : ℕ => (logSlack c (N + 1) : ℝ)) =o[atTop]
        fun N : ℕ => (N : ℝ) := by
    have heq : (fun N : ℕ => (logSlack c (N + 1) : ℝ)) =
        fun N : ℕ => (c : ℝ) * ((Nat.bits (N + 1)).length : ℝ) + c := by
      funext N
      simp [logSlack]
    rw [heq]
    have hConst : (fun _ : ℕ => (c : ℝ)) =o[atTop]
        fun N : ℕ => (N : ℝ) :=
      (Asymptotics.isLittleO_const_id_atTop (c : ℝ)).comp_tendsto
        tendsto_natCast_atTop_atTop
    exact Asymptotics.IsLittleO.add
      (Asymptotics.IsLittleO.const_mul_left hBits (c : ℝ)) hConst
  have hBudgets :
      (fun N : ℕ => ((threshold N + loss N : ℕ) : ℝ)) =o[atTop]
        fun N : ℕ => (N : ℝ) := by
    simpa only [Nat.cast_add] using Asymptotics.IsLittleO.add hThreshold hLoss
  have hConst : (fun _ : ℕ => (c : ℝ)) =o[atTop]
      fun N : ℕ => (N : ℝ) :=
    (Asymptotics.isLittleO_const_id_atTop (c : ℝ)).comp_tendsto
      tendsto_natCast_atTop_atTop
  have hg : (fun N : ℕ => (g N : ℝ)) =o[atTop] fun N : ℕ => (N : ℝ) := by
    have h₁ := Asymptotics.IsLittleO.add hBudgets hLogSlack
    have h₂ := Asymptotics.IsLittleO.add h₁ hConst
    simpa only [g, Nat.cast_add] using h₂
  refine ⟨g, hg, ?_⟩
  intro N
  exact le_rfl

/-- Pad the string returned by the iteration with
enough incompressible bits to recover the exact requested complexity.  The linear complexity
bound on the intermediate string keeps the description cost of this padding logarithmic in `N`;
the two sublinear budgets therefore still combine into one sublinear threshold. -/
private theorem theorem2_pad_to_q
    (D : Map) (hD : isOptimalConditional D) (loss threshold : ℕ → ℕ) (C : ℕ)
    (hLoss : (fun N : ℕ => (loss N : ℝ)) =o[atTop] fun N : ℕ => (N : ℝ))
    (hThreshold : (fun N : ℕ => (threshold N : ℝ)) =o[atTop] fun N : ℕ => (N : ℝ)) :
    ∃ g : ℕ → ℕ,
      ((fun N : ℕ => (g N : ℝ)) =o[atTop] fun N : ℕ => (N : ℝ)) ∧
      ∀ (x₁ x₂ w : BitString) (q N : ℕ),
        q ≤ natK D w + loss N →
        natK D w ≤ C * (N + 1) →
        natCondK D w x₁ ≤ threshold N →
        natCondK D w x₂ ≤ threshold N →
        CommonInfoExtractable D x₁ x₂ q (g N) := by
  obtain ⟨A, hA⟩ := theorem2_loss_has_linear_bound loss hLoss
  obtain ⟨B, c, hPad⟩ := theorem2_pad_at_linear_scale D hD C A
  obtain ⟨g, hg, hBudget⟩ :=
    theorem2_combine_sublinear_budgets loss threshold c hLoss hThreshold
  refine ⟨g, hg, ?_⟩
  intro x₁ x₂ w q N hq hw hx₁ hx₂
  obtain ⟨w', hq', hw', hcx₁, hcx₂⟩ := hPad x₁ x₂ w q N (loss N) hq hw (hA N)
  have hbg := hBudget N
  unfold CommonInfoExtractable
  refine ⟨w', hq', ?_, ?_⟩
  · exact hcx₁.trans (by omega)
  · exact hcx₂.trans (by omega)

/-- **Theorem 2.** For every `f(N) = o(N)` there is `g(N) = o(N)` such that for all
`x₁, x₂, z` with `N = K(x₁, x₂, z)`: if `I(z : x̄) ≤ f(N)` and `q` bits of common information can
be extracted from `x₁, x₂` with the oracle `z` for the threshold `f(N)`, then `q` bits can be
extracted without the oracle for the threshold `g(N)`.  Proof: Section 6 (typization of
`⟨v, z⟩` given `x̄`, Lemma 6, and an iteration that replaces the oracle); the string produced
there has complexity `≥ q − g(N)` and is padded to complexity `≥ q`. -/
theorem theorem2 (D : Map) (hD : isOptimalConditional D) (f : ℕ → ℕ)
    (hf : (fun N : ℕ => (f N : ℝ)) =o[atTop] fun N : ℕ => (N : ℝ)) :
    ∃ g : ℕ → ℕ, ((fun N : ℕ => (g N : ℝ)) =o[atTop] fun N : ℕ => (N : ℝ)) ∧
      ∀ (x₁ x₂ z : BitString) (q : ℕ),
        MutualInfoLe D (pairCode x₁ x₂) z (f (natK D (pairCode (pairCode x₁ x₂) z))) →
        CommonInfoExtractableRel D x₁ x₂ z q (f (natK D (pairCode (pairCode x₁ x₂) z))) →
        CommonInfoExtractable D x₁ x₂ q (g (natK D (pairCode (pairCode x₁ x₂) z))) := by
  obtain hStage := theorem2_typization_and_cover D hD
  obtain ⟨loss, threshold, C, hLoss, hThreshold, hIter⟩ :=
    theorem2_iterate_oracle D hD f hf hStage
  obtain ⟨g, hg, hPad⟩ := theorem2_pad_to_q D hD loss threshold C
    hLoss hThreshold
  refine ⟨g, hg, ?_⟩
  intro x₁ x₂ z q hMI hExtract
  obtain ⟨w, hq, hx₁, hx₂, hw⟩ := hIter x₁ x₂ z q hMI hExtract
  exact hPad x₁ x₂ w q (natK D (pairCode (pairCode x₁ x₂) z)) hq hw hx₁ hx₂

/-- Apply Conjecture 3 to a two-coordinate tuple and a one-coordinate extracted string. -/
private theorem conjecture2_of_conjecture3_apply_c3
    (D : Map) (hC3 : Conjecture3 D) :
    ∃ c : ℕ, ∀ (x : Fin 2 → BitString) (z v : BitString) (δ : ℕ),
      MutualInfoLe D (tupleCode x) z δ →
        ∃ w₀ : BitString,
          ProfileWithin
            (subKRel D (Fin.append x (fun _ : Fin 1 => v)) z)
            (subK D (Fin.append x (fun _ : Fin 1 => w₀)))
            (δ + logSlack c
              (natK D (pairCode (tupleCode (Fin.append x (fun _ : Fin 1 => v))) z))) := by
  obtain ⟨c, hc⟩ := hC3 2 1
  refine ⟨c, fun x z v δ hInfo => ?_⟩
  let y : Fin 1 → BitString := fun _ => v
  obtain ⟨y', hProfile⟩ := hc x z δ hInfo y
  let w₀ := y' ⟨0, by omega⟩
  have hy' : y' = fun _ : Fin 1 => w₀ := by
    funext i
    have hi : i = (⟨0, by omega⟩ : Fin 1) := Fin.ext (by omega)
    simp [w₀, hi]
  refine ⟨w₀, ?_⟩
  have hy : y = (fun _ : Fin 1 => v) := rfl
  rw [hy, hy'] at hProfile
  exact hProfile

/-- Transfer a small mutual-information bound from the pair encoding of two strings to their
two-coordinate tuple code. -/
private theorem conjecture2_of_conjecture3_tuple_mutual_info
    (D : Map) (hD : isOptimalConditional D) (C₁ : ℕ) :
    ∃ C₂ : ℕ, ∀ (x₁ x₂ z : BitString),
      MutualInfoLe D (pairCode x₁ x₂) z
          (logSlack C₁ (natK D (pairCode (pairCode x₁ x₂) z))) →
      MutualInfoLe D
        (tupleCode (fun i : Fin 2 => if i.val = 0 then x₁ else x₂)) z
        (logSlack C₂ (natK D (pairCode (pairCode x₁ x₂) z))) := by
  let f : BitString → BitString := fun s =>
    listCode [decodeFirst s, decodeSecond s]
  let g : BitString → BitString := fun s =>
    pairCode ((decodeListCode s).getD 0 []) ((decodeListCode s).getD 1 [])
  have hf : Computable f := by
    dsimp [f]
    exact listCode_computable.comp
      ((Primrec.list_cons.comp CodedFiniteDistribution.decodeFirst_primrec
        (Primrec.list_cons.comp CodedFiniteDistribution.decodeSecond_primrec
          (Primrec.const []))).to_comp)
  have hg : Computable g := by
    dsimp [g]
    have hfirst : Primrec (fun s : BitString => (decodeListCode s).getD 0 []) :=
      (Primrec.list_getD ([] : BitString)).comp decodeListCode_primrec (Primrec.const 0)
    have hsecond : Primrec (fun s : BitString => (decodeListCode s).getD 1 []) :=
      (Primrec.list_getD ([] : BitString)).comp decodeListCode_primrec (Primrec.const 1)
    exact Computable₂.comp pairCode_computable hfirst.to_comp hsecond.to_comp
  obtain ⟨cF, hF⟩ := plainK_map_le D hD f hf
  obtain ⟨cG, hG⟩ := condK_map_le D hD g hg
  refine ⟨C₁ + cF + cG, ?_⟩
  intro x₁ x₂ z hInfo
  let x : Fin 2 → BitString := fun i => if i.val = 0 then x₁ else x₂
  have hList : List.ofFn x = [x₁, x₂] := by
    rw [List.ofFn_succ', List.ofFn_succ, List.ofFn_zero, List.concat_eq_append]
    simp [x]
  have hfEq : f (pairCode x₁ x₂) = tupleCode x := by
    change listCode [decodeFirst (pairCode x₁ x₂), decodeSecond (pairCode x₁ x₂)] =
      listCode (List.ofFn x)
    rw [decodeFirst_pairCode, decodeSecond_pairCode, hList]
  have hgEq : g (tupleCode x) = pairCode x₁ x₂ := by
    change pairCode ((decodeListCode (listCode (List.ofFn x))).getD 0 [])
      ((decodeListCode (listCode (List.ofFn x))).getD 1 []) = pairCode x₁ x₂
    rw [decodeListCode_listCode, hList]
    rfl
  let N := natK D (pairCode (pairCode x₁ x₂) z)
  have hPlain : natK D (tupleCode x) ≤ natK D (pairCode x₁ x₂) + cF := by
    have h := hF (pairCode x₁ x₂)
    rw [hfEq] at h
    rw [← ENat.natCast_toNat (plainK_ne_top D hD (tupleCode x)),
      ← ENat.natCast_toNat (plainK_ne_top D hD (pairCode x₁ x₂))] at h
    exact_mod_cast h
  have hConditional : natCondK D (pairCode x₁ x₂) z ≤ natCondK D (tupleCode x) z + cG := by
    have h := hG (tupleCode x) z
    rw [hgEq] at h
    rw [← ENat.natCast_toNat (condK_ne_top_of_optimal D hD (pairCode x₁ x₂) z),
      ← ENat.natCast_toNat (condK_ne_top_of_optimal D hD (tupleCode x) z)] at h
    exact_mod_cast h
  have hMain : natK D (tupleCode x) ≤ natCondK D (tupleCode x) z +
      logSlack C₁ N + cF + cG := by
    have hInfo' : natK D (pairCode x₁ x₂) ≤ natCondK D (pairCode x₁ x₂) z +
        logSlack C₁ N := by simpa [MutualInfoLe, N] using hInfo
    omega
  have hSlack : logSlack C₁ N + cF + cG ≤ logSlack (C₁ + cF + cG) N := by
    have h : logSlack C₁ N + (cF + cG) ≤ logSlack (C₁ + cF + cG) N := by
      simpa [Nat.add_assoc] using logSlack_add_nat_le C₁ (cF + cG) N
    omega
  have hResult : natK D (tupleCode x) ≤
      natCondK D (tupleCode x) z + logSlack (C₁ + cF + cG) N := by
    omega
  simpa [MutualInfoLe, x, N, Nat.add_assoc] using hResult

/-- Bound the joint complexity of the extracted string and two-coordinate tuple linearly at the
Conjecture 3 input. -/
private theorem conjecture2_of_conjecture3_tuple_input_bound
    (D : Map) (hD : isOptimalConditional D) (C₁ : ℕ) :
    ∃ B : ℕ, ∀ (x₁ x₂ z v : BitString),
      natCondK D v (pairCode x₁ z) ≤
          logSlack C₁ (natK D (pairCode (pairCode x₁ x₂) z)) →
      natK D
          (pairCode
            (tupleCode
              (Fin.append (fun i : Fin 2 => if i.val = 0 then x₁ else x₂)
                (fun _ : Fin 1 => v))) z) ≤
        B * (natK D (pairCode (pairCode x₁ x₂) z) + 1) := by
  obtain ⟨cContext, hContext⟩ := condK_cond_map_le D hD
    (fun t => pairCode (decodeFirst (decodeFirst t)) (decodeSecond t))
    (Computable₂.comp pairCode_computable
      (decodeFirst_computable.comp decodeFirst_computable) decodeSecond_computable)
  obtain ⟨cPair, hPair⟩ := plainK_pair_le_add_two_log_add_condK D hD
  let F : BitString → BitString := fun s =>
    pairCode
      (listCode [decodeFirst (decodeFirst (decodeFirst s)),
        decodeSecond (decodeFirst (decodeFirst s)), decodeSecond s])
      (decodeSecond (decodeFirst s))
  have hF : Computable F := by
    dsimp [F]
    have hx₁ : Primrec (fun s : BitString =>
        decodeFirst (decodeFirst (decodeFirst s))) :=
      CodedFiniteDistribution.decodeFirst_primrec.comp
        (CodedFiniteDistribution.decodeFirst_primrec.comp
          CodedFiniteDistribution.decodeFirst_primrec)
    have hx₂ : Primrec (fun s : BitString =>
        decodeSecond (decodeFirst (decodeFirst s))) :=
      CodedFiniteDistribution.decodeSecond_primrec.comp
        (CodedFiniteDistribution.decodeFirst_primrec.comp
          CodedFiniteDistribution.decodeFirst_primrec)
    have hv : Primrec (fun s : BitString => decodeSecond s) :=
      CodedFiniteDistribution.decodeSecond_primrec
    have hz : Computable (fun s : BitString => decodeSecond (decodeFirst s)) :=
      decodeSecond_computable.comp decodeFirst_computable
    have hList : Computable (fun s : BitString =>
        listCode [decodeFirst (decodeFirst (decodeFirst s)),
          decodeSecond (decodeFirst (decodeFirst s)), decodeSecond s]) := by
      exact listCode_computable.comp
        ((Primrec.list_cons.comp hx₁
          (Primrec.list_cons.comp hx₂
            (Primrec.list_cons.comp hv (Primrec.const [])))).to_comp)
    exact Computable₂.comp pairCode_computable hList hz
  obtain ⟨cMap, hMap⟩ := plainK_map_le D hD F hF
  refine ⟨2 * C₁ + 3 + cContext + cPair + cMap, ?_⟩
  intro x₁ x₂ z v hExtract₁
  let t := pairCode (pairCode x₁ x₂) z
  let N := natK D t
  let x : Fin 2 → BitString := fun i => if i.val = 0 then x₁ else x₂
  let y : Fin 1 → BitString := fun _ => v
  have hList₂ : List.ofFn x = [x₁, x₂] := by
    rw [List.ofFn_succ', List.ofFn_succ, List.ofFn_zero, List.concat_eq_append]
    simp [x]
  have hList₃ : List.ofFn (Fin.append x y) = [x₁, x₂, v] := by
    rw [List.ofFn_succ']
    have hCast : (fun i : Fin 2 => Fin.append x y (Fin.castSucc i)) = x := by
      funext i
      exact Fin.append_left x y i
    have hLast : Fin.append x y (Fin.last 2) = v := by
      change Fin.append x y (Fin.natAdd 2 (0 : Fin 1)) = v
      rw [Fin.append_right]
    rw [hCast, hList₂, hLast]
    rfl
  have hMapCode : F (pairCode t v) = pairCode (tupleCode (Fin.append x y)) z := by
    simp only [F, t, decodeFirst_pairCode, decodeSecond_pairCode, tupleCode]
    rw [← hList₃]
  have hProject :
      pairCode (decodeFirst (decodeFirst t)) (decodeSecond t) = pairCode x₁ z := by
    simp [t, decodeFirst_pairCode, decodeSecond_pairCode]
  have hCond : natCondK D v t ≤ natCondK D v (pairCode x₁ z) + cContext := by
    have h := hContext v t
    rw [hProject] at h
    rw [← ENat.natCast_toNat (condK_ne_top_of_optimal D hD v t),
      ← ENat.natCast_toNat (condK_ne_top_of_optimal D hD v (pairCode x₁ z))] at h
    exact_mod_cast h
  have hCondBound : natCondK D v t ≤ logSlack C₁ N + cContext := by
    have hExtract₁' : natCondK D v (pairCode x₁ z) ≤ logSlack C₁ N := by
      simpa [N, t] using hExtract₁
    omega
  have hPairBound : natK D (pairCode t v) ≤
      N + natCondK D v t + 2 * Nat.log 2 N + cPair := by
    have h := hPair t v
    change plainK D (pairCode t v) ≤ plainK D t + condK D v t +
      ((2 * Nat.log 2 (cVal D t) + cPair : ℕ) : ℕ∞) at h
    rw [← ENat.natCast_toNat (plainK_ne_top D hD (pairCode t v)),
      ← ENat.natCast_toNat (plainK_ne_top D hD t),
      ← ENat.natCast_toNat (condK_ne_top_of_optimal D hD v t)] at h
    have hNat : natK D (pairCode t v) ≤
        natK D t + natCondK D v t + (2 * Nat.log 2 (cVal D t) + cPair) := by
      exact_mod_cast h
    have hcv : cVal D t = natK D t := rfl
    rw [hcv] at hNat
    simpa [N, Nat.add_assoc] using hNat
  have hOutputBound : natK D (pairCode (tupleCode (Fin.append x y)) z) ≤
      natK D (pairCode t v) + cMap := by
    have h := hMap (pairCode t v)
    rw [hMapCode] at h
    rw [← ENat.natCast_toNat (plainK_ne_top D hD
        (pairCode (tupleCode (Fin.append x y)) z)),
      ← ENat.natCast_toNat (plainK_ne_top D hD (pairCode t v))] at h
    exact_mod_cast h
  have hLogN : Nat.log 2 N ≤ N := by
    exact (commonInfo_le_mutualInfo_natLog_le_bits N).trans (length_natBits_le N)
  have hSlackN : logSlack C₁ N ≤ C₁ * N + C₁ := by
    unfold logSlack
    exact Nat.add_le_add_right (Nat.mul_le_mul_left C₁ (length_natBits_le N)) C₁
  have hCore : natK D (pairCode (tupleCode (Fin.append x y)) z) ≤
      (C₁ + 3) * N + (C₁ + cContext + cPair + cMap) := by
    calc
      natK D (pairCode (tupleCode (Fin.append x y)) z)
          ≤ N + natCondK D v t + 2 * Nat.log 2 N + cPair + cMap := by omega
      _ ≤ N + (C₁ * N + C₁ + cContext) + 2 * N + cPair + cMap := by
        have h := Nat.add_le_add_right hCondBound (2 * Nat.log 2 N + cPair + cMap)
        omega
      _ = (C₁ + 3) * N + (C₁ + cContext + cPair + cMap) := by
        simp [Nat.add_mul]
        omega
  have hCoeff : C₁ + 3 ≤ 2 * C₁ + 3 + cContext + cPair + cMap := by omega
  have hConst : C₁ + cContext + cPair + cMap ≤ 2 * C₁ + 3 + cContext + cPair + cMap := by omega
  have hScale := Nat.mul_le_mul_right N hCoeff
  have hTotal := Nat.add_le_add hScale hConst
  have hFinal : natK D (pairCode (tupleCode (Fin.append x y)) z) ≤
      (2 * C₁ + 3 + cContext + cPair + cMap) * (N + 1) := by
    calc
      natK D (pairCode (tupleCode (Fin.append x y)) z)
          ≤ (C₁ + 3) * N + (C₁ + cContext + cPair + cMap) := hCore
      _ ≤ (2 * C₁ + 3 + cContext + cPair + cMap) * N +
          (2 * C₁ + 3 + cContext + cPair + cMap) := hTotal
      _ = (2 * C₁ + 3 + cContext + cPair + cMap) * (N + 1) := by
        rw [Nat.mul_add]
        simp
  simpa [N, t, x, y, Fin.append] using hFinal

/-- Absorb the Conjecture 3 profile error after changing its input complexity by a linear bound. -/
private theorem conjecture2_of_conjecture3_absorb_profile_slack
    (a b c₃ : ℕ) :
    ∃ c : ℕ, ∀ (N δ N' : ℕ),
      δ ≤ logSlack a N →
      N' ≤ b * (N + 1) →
      δ + logSlack c₃ N' ≤ logSlack c N := by
  obtain ⟨cFold, hFold⟩ := logSlack_linear_bound c₃ b b
  refine ⟨a + cFold, fun N δ N' hδ hN' => ?_⟩
  have hFold' : logSlack c₃ N' ≤ logSlack cFold N := by
    calc
      logSlack c₃ N' ≤ logSlack c₃ (b * N + b) :=
        logSlack_mono_right c₃ (by simpa [Nat.mul_add] using hN')
      _ ≤ logSlack cFold N := hFold N
  calc
    δ + logSlack c₃ N' ≤ logSlack a N + logSlack cFold N :=
      Nat.add_le_add hδ hFold'
    _ = logSlack (a + cFold) N := (logSlack_add_constants a cFold N).symm

/-- Applying Conjecture 3 to the two-coordinate tuple and extracted string gives a nearby
profile. -/
theorem conjecture2_of_conjecture3_c3_profile
    (D : Map) (hD : isOptimalConditional D) (hC3 : Conjecture3 D) (C₁ : ℕ) :
    ∃ c : ℕ, ∀ (x₁ x₂ z : BitString) (q : ℕ),
      MutualInfoLe D (pairCode x₁ x₂) z
          (logSlack C₁ (natK D (pairCode (pairCode x₁ x₂) z))) →
      CommonInfoExtractableRel D x₁ x₂ z q
          (logSlack C₁ (natK D (pairCode (pairCode x₁ x₂) z))) →
      ∃ v w₀ : BitString,
        q ≤ natCondK D v z ∧
        natCondK D v (pairCode x₁ z) ≤
          logSlack C₁ (natK D (pairCode (pairCode x₁ x₂) z)) ∧
        natCondK D v (pairCode x₂ z) ≤
          logSlack C₁ (natK D (pairCode (pairCode x₁ x₂) z)) ∧
        ProfileWithin
          (subKRel D
            (Fin.append (fun i : Fin 2 => if i.val = 0 then x₁ else x₂)
              (fun _ : Fin 1 => v)) z)
          (subK D
            (Fin.append (fun i : Fin 2 => if i.val = 0 then x₁ else x₂)
              (fun _ : Fin 1 => w₀)))
          (logSlack c (natK D (pairCode (pairCode x₁ x₂) z))) := by
  obtain ⟨cC3, hC3Profile⟩ :=
    conjecture2_of_conjecture3_apply_c3 D hC3
  obtain ⟨cMI, hTupleMI⟩ :=
    conjecture2_of_conjecture3_tuple_mutual_info
      D hD C₁
  obtain ⟨cInput, hInput⟩ :=
    conjecture2_of_conjecture3_tuple_input_bound
      D hD C₁
  obtain ⟨c, hAbsorb⟩ :=
    conjecture2_of_conjecture3_absorb_profile_slack
      cMI cInput cC3
  refine ⟨c, fun x₁ x₂ z q hMI hExtract => ?_⟩
  obtain ⟨v, hqv, hv₁, hv₂⟩ := hExtract
  let N := natK D (pairCode (pairCode x₁ x₂) z)
  let x : Fin 2 → BitString := fun i => if i.val = 0 then x₁ else x₂
  have hTupleInfo := hTupleMI x₁ x₂ z hMI
  obtain ⟨w₀, hProfile⟩ := hC3Profile x z v (logSlack cMI N) (by simpa [x] using hTupleInfo)
  have hN' := hInput x₁ x₂ z v hv₁
  have hBudget : logSlack cMI N +
      logSlack cC3 (natK D (pairCode (tupleCode (Fin.append x (fun _ : Fin 1 => v))) z)) ≤
        logSlack c N := by
    exact hAbsorb N (logSlack cMI N)
      (natK D (pairCode (tupleCode (Fin.append x (fun _ : Fin 1 => v))) z)) le_rfl
      (by simpa [x, N] using hN')
  have hProfileAligned : ProfileWithin
      (subKRel D
        (Fin.append (fun i : Fin 2 => if i.val = 0 then x₁ else x₂)
          (fun _ : Fin 1 => v)) z)
      (subK D
        (Fin.append (fun i : Fin 2 => if i.val = 0 then x₁ else x₂)
          (fun _ : Fin 1 => w₀)))
      (logSlack cMI N +
        logSlack cC3 (natK D (pairCode (tupleCode (Fin.append x (fun _ : Fin 1 => v))) z))) := by
    simpa [x] using hProfile
  refine ⟨v, w₀, hqv, hv₁, hv₂, ?_⟩
  have hProfile' : ProfileWithin
      (subKRel D
        (Fin.append (fun i : Fin 2 => if i.val = 0 then x₁ else x₂)
          (fun _ : Fin 1 => v)) z)
      (subK D
        (Fin.append (fun i : Fin 2 => if i.val = 0 then x₁ else x₂)
          (fun _ : Fin 1 => w₀)))
      (logSlack c N) := by
    intro V hV
    obtain ⟨hForward, hBackward⟩ := hProfileAligned V hV
    constructor <;> omega
  simpa [N] using hProfile'

end Kolmogorov.Relativization
