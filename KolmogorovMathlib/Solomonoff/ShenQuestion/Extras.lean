/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Solomonoff.ShenQuestion.Main

/-!
# A7.  Regression guards: non-vacuity, the literal supremum, monotonicity in `Q`

This file collects three regression guards for the main theorem:

* **Non-vacuity.** The hypotheses of `shen_negative` are satisfiable: `lengthMeasure`
  (viewed as a condition-independent conditional semimeasure) is a lower semicomputable
  conditional continuous semimeasure, and a lower semicomputable discrete semimeasure
  exists; hence `shen_negative_lengthMeasure` is a non-vacuous instance.
* **Literal supremum.**  `⨆ x, f x / m x = ⊤`, the division form of
  `shen_negative_not_bounded`.
* **Monotonicity in `Q`.**  `shenF M Q x` is antitone in `Q`; this is the first half of the
  root-normalisation remark (rescaling `Q` downwards can only increase `shenF`).
-/

namespace Kolmogorov
namespace Shen

open scoped ENNReal

/-! ### Non-vacuity of the hypotheses -/

/-- The length measure `y ↦ 2^{-|y|}`, read as a conditional semimeasure that ignores its
condition, is a lower semicomputable conditional continuous semimeasure.  In particular the
hypothesis `IsLSCConditionalContinuousSemimeasure Q` of `shen_negative` is satisfiable. -/
theorem lengthMeasure_isLSCConditional :
    IsLSCConditionalContinuousSemimeasure (fun y _ => lengthMeasure y) :=
  ⟨fun _ => lengthMeasure_isContinuousTreeSemimeasure, lengthMeasure_isLSC_core⟩

/-- A lower semicomputable discrete semimeasure exists; in particular the hypothesis
`IsLowerSemicomputableSemimeasure m` of `shen_negative` is satisfiable. -/
theorem exists_isLowerSemicomputableSemimeasure :
    ∃ m : BitString → ℝ≥0∞, IsLowerSemicomputableSemimeasure m :=
  let ⟨m, hm⟩ := exists_universalSemimeasure
  ⟨m, hm.1⟩

/-- The main theorem instantiated at `Q = lengthMeasure` (a concrete, condition-independent
`Q`): a fully instantiated, non-vacuous form of `shen_negative`. -/
theorem shen_negative_lengthMeasure (m : BitString → ℝ≥0∞)
    (hm : IsLowerSemicomputableSemimeasure m) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ R : ℕ, ∃ u : BitString,
      0 < shenF universalContinuousSemimeasure (fun y _ => lengthMeasure y) u ∧
      c * R * m u ≤ shenF universalContinuousSemimeasure (fun y _ => lengthMeasure y) u :=
  shen_negative _ lengthMeasure_isLSCConditional m hm

/-! ### The literal supremum form -/

/-- Corollary in the literal division form:
`⨆ x, f(x) / m(x) = ∞`. -/
theorem shen_negative_iSup_div (Q : BitString → BitString → ℝ≥0∞)
    (hQ : IsLSCConditionalContinuousSemimeasure Q)
    (m : BitString → ℝ≥0∞) (hm : IsLowerSemicomputableSemimeasure m) :
    (⨆ x : BitString, shenF universalContinuousSemimeasure Q x / m x) = ⊤ := by
  rw [iSup_eq_top]
  intro b hb
  obtain ⟨x, hx⟩ := shen_negative_lt Q hQ m hm b hb.ne
  refine ⟨x, ?_⟩
  rcases eq_or_ne (m x) 0 with hmx | hmx
  · have hfx : shenF universalContinuousSemimeasure Q x ≠ 0 := by
      have : (0 : ℝ≥0∞) < shenF universalContinuousSemimeasure Q x := by
        simpa [hmx] using hx
      exact this.ne'
    rw [hmx, ENNReal.div_zero hfx]
    exact hb
  · have hmtop : m x ≠ ⊤ := shenF_semimeasure_ne_top hm.1 x
    exact (ENNReal.lt_div_iff_mul_lt (Or.inl hmx) (Or.inl hmtop)).mpr hx

/-! ### Monotonicity of `shenF` in `Q` -/

/-- `shenF M Q x` is antitone in `Q`: a smaller conditional semimeasure gives a larger
functional, because every `λ` feasible for `Q'` is feasible for the smaller `Q`. -/
theorem shenF_anti_of_le {M : BitString → ℝ≥0∞} {Q Q' : BitString → BitString → ℝ≥0∞}
    (h : ∀ y x, Q y x ≤ Q' y x) (x : BitString) : shenF M Q' x ≤ shenF M Q x :=
  sSup_le_sSup fun _ hl y => le_trans (mul_le_mul_right (h y x) _) (hl y)

end Shen
end Kolmogorov
