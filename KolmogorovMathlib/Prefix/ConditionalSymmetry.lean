/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/

import KolmogorovMathlib.Prefix.CondTwoStage
import KolmogorovMathlib.Prefix.Properties
import KolmogorovMathlib.Prefix.Symmetry

/-!
# Conditional Prefix Complexity of Pairs

This module starts the conditional version of the staged prefix
symmetry-of-information interface.  The upper, two-stage coding direction is
proved by the relativized two-stage builder in `Prefix.CondTwoStage`.  The lower
direction is intentionally left as a theorem-level obligation: it should be
closed by the conditional semimeasure/section-coding argument, not by a local
GapCounting-specific proof.
-/

namespace Kolmogorov

open scoped ENNReal

/-- Conditional prefix complexity of the pair `(x, y)` given `z`. -/
noncomputable def KPCondPair (U : Map) (x y z : BitString) : ENat :=
  KP U (pairCode x y) z

/-- A context containing `z`, `x`, and a natural witness for `K(x | z)`. -/
def prefixCondComplexityContext (z x : BitString) (kx : Nat) : BitString :=
  pairCode z (pairCode x (natCode kx))

/-- `kx` is a natural-number witness for the finite conditional prefix
complexity of `x` given `z`. -/
def HasCondPrefixComplexityValue (U : Map) (x z : BitString) (kx : Nat) : Prop :=
  (kx : ENat) = KP U x z

/-- The conditional `(z, x, K(x | z))` context encoder is computable. -/
theorem prefixCondComplexityContext_computable :
    Computable
      (fun p : (BitString × BitString) × ℕ ↦
        prefixCondComplexityContext p.1.1 p.1.2 p.2) := by
  apply Computable.of_eq
    (pairCode_computable.comp
      ((Computable.fst.comp Computable.fst).pair
        (pairCode_computable.comp
          ((Computable.snd.comp Computable.fst).pair
            (natCode_computable.comp Computable.snd)))))
  intro p
  rfl

/-- A prefix decompressor with a direct conditional two-stage coding bound proves
the upper direction for any optimal prefix decompressor. -/
theorem KPCondPair_chain_upper_of_prefix_decompressor (U M : Map)
    (hU : IsOptimalPrefixConditional U) (hM : IsPrefixDecompressor M) (c0 : Nat)
    (hbound : ∀ x y z : BitString, ∀ kx : Nat,
      HasCondPrefixComplexityValue U x z kx →
        KP M (pairCode x y) z ≤
          KP U x z + KP U y (prefixCondComplexityContext z x kx) + (c0 : ENat)) :
    ∃ c : Nat, ∀ x y z : BitString, ∀ kx : Nat,
      HasCondPrefixComplexityValue U x z kx →
        KPCondPair U x y z
          ≤ KP U x z + KP U y (prefixCondComplexityContext z x kx) + (c : ENat) := by
  obtain ⟨c1, h1⟩ := hU.invariance hM
  refine ⟨c0 + c1, ?_⟩
  intro x y z kx hkx
  calc
    KPCondPair U x y z = KP U (pairCode x y) z := rfl
    _ ≤ KP M (pairCode x y) z + (c1 : ENat) := h1 (pairCode x y) z
    _ ≤ (KP U x z + KP U y (prefixCondComplexityContext z x kx) + (c0 : ENat))
        + (c1 : ENat) := add_le_add_left (hbound x y z kx hkx) _
    _ = KP U x z + KP U y (prefixCondComplexityContext z x kx)
        + ((c0 + c1 : Nat) : ENat) := by
      rw [Nat.cast_add]
      ac_rfl

/-- The upper, coding direction of conditional prefix symmetry of information. -/
theorem KPCondPair_chain_upper (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : Nat, ∀ x y z : BitString, ∀ kx : Nat,
      HasCondPrefixComplexityValue U x z kx →
        KPCondPair U x y z
          ≤ KP U x z + KP U y (prefixCondComplexityContext z x kx) + (c : ENat) := by
  have hM : IsPrefixDecompressor
      (condTwoStagePairBuilder U prefixCondComplexityContext) :=
    condTwoStagePairBuilder_isPrefixDecompressor hU.isDecompressor hU.isPrefixMachine
      prefixCondComplexityContext_computable
  refine KPCondPair_chain_upper_of_prefix_decompressor U
    (condTwoStagePairBuilder U prefixCondComplexityContext) hU hM 0 ?_
  intro x y z kx hkx
  have hKx : KP U x z ≠ ⊤ := by
    rw [← hkx]
    exact ENat.coe_ne_top kx
  obtain ⟨p, hp, hplen⟩ := exists_program_of_KP_ne_top (M := U) (x := x) (y := z) hKx
  have hpl_eq : (p.length : ENat) = KP U x z := hplen
  have hp_kx : p.length = kx := by
    have : (p.length : ENat) = (kx : ENat) := by rw [hpl_eq, ← hkx]
    exact_mod_cast this
  by_cases hKy : KP U y (prefixCondComplexityContext z x kx) = ⊤
  · rw [hKy]
    simp
  · obtain ⟨q, hq, hqlen⟩ :=
      exists_program_of_KP_ne_top (M := U) (x := y)
        (y := prefixCondComplexityContext z x kx) hKy
    have hq' : produces U q (prefixCondComplexityContext z x p.length) y := by
      rw [hp_kx]
      exact hq
    have hbound := KP_condTwoStagePairBuilder_le_of_produces
      (U := U) (ctx := prefixCondComplexityContext) hU.isPrefixMachine hp hq'
    calc
      KP (condTwoStagePairBuilder U prefixCondComplexityContext) (pairCode x y) z
          ≤ ((p.length + q.length : Nat) : ENat) := hbound
      _ = KP U x z + KP U y (prefixCondComplexityContext z x kx) := by
            rw [Nat.cast_add, hpl_eq, hqlen]
      _ = KP U x z + KP U y (prefixCondComplexityContext z x kx) + (0 : ENat) := by
            rw [add_zero]

open scoped ENNReal in
/-- **Reduction of the conditional lower direction to a single conditional coding
bound.**

This is the `z`-relativized analogue of
`KPPair_chain_lower_of_conditional_coding`.  Given the conditional coding
hypothesis `hcode` — in the context `(z, x, k)` *with `k = K(x | z)`* the
conditional prefix complexity weight `2^{-K(y | z, x, k)}` dominates the scaled
section mass `2^{-c₁} · m_U(⟨x,y⟩ | z) · 2^{k}` — the additive conditional lower
bound follows by pure `ENat`/`ENNReal` arithmetic, exactly as in the
unconditional case.  The bound is only requested at `k = K(x | z)` (guard
`HasCondPrefixComplexityValue U x z k`); the unguarded `∀ k` version is false. -/
theorem KPCondPair_chain_lower_of_conditional_coding (U : Map)
    (hcode : ∃ c₁ : ℕ, ∀ x y z : BitString, ∀ k : ℕ,
        HasCondPrefixComplexityValue U x z k →
        (2 : ℝ≥0∞)⁻¹ ^ c₁ * (aprioriMeasure U (pairCode x y) z * (2 : ℝ≥0∞) ^ k)
          ≤ complexityWeight (KP U y (prefixCondComplexityContext z x k))) :
    ∃ c : Nat, ∀ x y z : BitString, ∀ kx : Nat,
      HasCondPrefixComplexityValue U x z kx →
        KP U x z + KP U y (prefixCondComplexityContext z x kx)
          ≤ KPCondPair U x y z + (c : ENat) := by
  obtain ⟨c₁, hc₁⟩ := hcode
  refine ⟨c₁, ?_⟩
  intro x y z kx hkx
  -- Replace `K(x | z)` by its natural witness `kx`.
  rw [← hkx]
  by_cases hP : KPCondPair U x y z = ⊤
  · rw [hP]; simp
  · -- Easy coding bound for the pair: `2^{-K(x,y | z)} ≤ m_U(⟨x,y⟩ | z)`.
    have heasy : complexityWeight (KPCondPair U x y z)
        ≤ aprioriMeasure U (pairCode x y) z :=
      complexityWeight_KP_le_aprioriMeasure U (pairCode x y) z
    -- `2^{kx} · 2^{-kx} = 1`.
    have hcancel : (2 : ℝ≥0∞) ^ kx * (2 : ℝ≥0∞)⁻¹ ^ kx = 1 := by
      rw [← mul_pow, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow]
    -- `2^{-(kx + K(y | z,x,kx))} = 2^{-K(y | z,x,kx)} · 2^{-kx}`.
    have hcw : complexityWeight ((kx : ENat) + KP U y (prefixCondComplexityContext z x kx))
        = complexityWeight (KP U y (prefixCondComplexityContext z x kx)) * (2 : ℝ≥0∞)⁻¹ ^ kx := by
      rw [add_comm, complexityWeight_add_nat]
    -- The multiplicative coding chain.
    have key : (2 : ℝ≥0∞)⁻¹ ^ c₁ * complexityWeight (KPCondPair U x y z)
        ≤ complexityWeight ((kx : ENat) + KP U y (prefixCondComplexityContext z x kx)) := by
      rw [hcw]
      calc
        (2 : ℝ≥0∞)⁻¹ ^ c₁ * complexityWeight (KPCondPair U x y z)
            ≤ (2 : ℝ≥0∞)⁻¹ ^ c₁ * aprioriMeasure U (pairCode x y) z :=
          mul_le_mul_right heasy _
        _ = ((2 : ℝ≥0∞)⁻¹ ^ c₁ *
              (aprioriMeasure U (pairCode x y) z * (2 : ℝ≥0∞) ^ kx)) * (2 : ℝ≥0∞)⁻¹ ^ kx := by
              rw [mul_assoc, mul_assoc, hcancel, mul_one]
        _ ≤ complexityWeight (KP U y (prefixCondComplexityContext z x kx)) * (2 : ℝ≥0∞)⁻¹ ^ kx :=
          mul_le_mul_left (hc₁ x y z kx hkx) _
    -- Read the multiplicative bound back as the additive lower bound.
    exact le_add_nat_of_complexityWeight_le hP key

/-- The lower, section-coding direction of conditional prefix symmetry of
information, obtained by discharging the conditional coding hypothesis with the
fully-proved `section_coding_bound`. -/
theorem KPCondPair_chain_lower (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : Nat, ∀ x y z : BitString, ∀ kx : Nat,
      HasCondPrefixComplexityValue U x z kx →
        KP U x z + KP U y (prefixCondComplexityContext z x kx)
          ≤ KPCondPair U x y z + (c : ENat) := by
  apply KPCondPair_chain_lower_of_conditional_coding U
  obtain ⟨c₁, hc₁⟩ := section_coding_bound U hU
  refine ⟨c₁, ?_⟩
  intro x y z k hk
  simpa [prefixCondComplexityContext] using hc₁ z x y k hk

/-- Conditional staged symmetry of information. -/
theorem KPCondPair_symmetryOfInformation_staged (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ cUpper : Nat, ∃ cLower : Nat,
      ∀ x y z : BitString, ∀ kx : Nat,
        HasCondPrefixComplexityValue U x z kx →
          KPCondPair U x y z
              ≤ KP U x z + KP U y (prefixCondComplexityContext z x kx) + (cUpper : ENat) ∧
          KP U x z + KP U y (prefixCondComplexityContext z x kx)
              ≤ KPCondPair U x y z + (cLower : ENat) := by
  obtain ⟨cUpper, hUpper⟩ := KPCondPair_chain_upper U hU
  obtain ⟨cLower, hLower⟩ := KPCondPair_chain_lower U hU
  exact ⟨cUpper, cLower, fun x y z kx hkx ↦ ⟨hUpper x y z kx hkx, hLower x y z kx hkx⟩⟩

/-- The ordinary lower direction, recovered from the conditional lower direction
at empty external condition. -/
theorem KPPair_chain_lower (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : Nat, ∀ x y : BitString, ∀ kx : Nat,
      HasPrefixComplexityValue U x kx →
        KPPlain U x + KP U y (prefixComplexityContext x kx)
          ≤ KPPair U x y + (c : ENat) := by
  obtain ⟨cCond, hCond⟩ := KPCondPair_chain_lower U hU
  let addEmptyCondition : BitString → BitString := fun ctx ↦ pairCode [] ctx
  have hAdd : Computable addEmptyCondition :=
    pairCode_computable.comp ((Computable.const []).pair Computable.id)
  obtain ⟨cMap, hMap⟩ := KP_cond_map_le U hU addEmptyCondition hAdd
  refine ⟨cCond + cMap, ?_⟩
  intro x y kx hkx
  have hkxCond : HasCondPrefixComplexityValue U x [] kx := hkx
  have hLower := hCond x y [] kx hkxCond
  have hCtx :
      addEmptyCondition (prefixComplexityContext x kx)
        = prefixCondComplexityContext [] x kx := rfl
  have hMap' := hMap y (prefixComplexityContext x kx)
  rw [hCtx] at hMap'
  calc
    KPPlain U x + KP U y (prefixComplexityContext x kx)
        ≤ KPPlain U x
            + (KP U y (prefixCondComplexityContext [] x kx) + (cMap : ENat)) := by
          gcongr
    _ = (KP U x [] + KP U y (prefixCondComplexityContext [] x kx)) + (cMap : ENat) := by
          rw [KPPlain_eq_KP]
          ac_rfl
    _ ≤ (KPCondPair U x y [] + (cCond : ENat)) + (cMap : ENat) := by
          simpa [add_assoc, add_comm, add_left_comm] using
            add_le_add_right hLower (cMap : ENat)
    _ = KPPair U x y + ((cCond + cMap : Nat) : ENat) := by
          change KP U (pairCode x y) [] + (cCond : ENat) + (cMap : ENat)
            = KP U (pairCode x y) [] + ((cCond + cMap : Nat) : ENat)
          rw [Nat.cast_add]
          ac_rfl

/-- Staged prefix symmetry of information, packaged from the existing upper
direction and the controlled lower obligation above. -/
theorem KPPair_symmetryOfInformation_staged (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ cUpper : Nat, ∃ cLower : Nat,
      ∀ x y : BitString, ∀ kx : Nat,
        HasPrefixComplexityValue U x kx →
          KPPair U x y
              ≤ KPPlain U x + KP U y (prefixComplexityContext x kx) + (cUpper : ENat) ∧
          KPPlain U x + KP U y (prefixComplexityContext x kx)
              ≤ KPPair U x y + (cLower : ENat) := by
  obtain ⟨cUpper, hUpper⟩ := KPPair_chain_upper U hU
  obtain ⟨cLower, hLower⟩ := KPPair_chain_lower U hU
  exact ⟨cUpper, cLower, fun x y kx hkx ↦ ⟨hUpper x y kx hkx, hLower x y kx hkx⟩⟩

end Kolmogorov
