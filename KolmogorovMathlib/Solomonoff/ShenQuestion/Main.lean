/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Solomonoff.ShenQuestion.Stuck

/-!
# A6.  Assembly of the main theorem

The main theorem `shen_negative` (frozen statement) is assembled here from the lemmas of
the other files; its corollaries follow.  The assembly below contains **no `sorry`**: all
the mathematical content sits in the lemmas of `Sanitize`, `FlowCompletion`,
`Construction` and `Stuck`.

The constant is `c = (c₀ + 1)⁻¹` where `ν ≤ c₀ · M` is the universality constant of the
constructed `ν`; the `+1` is the cheap way to get `c ≠ 0` *and* `c ≠ ⊤` at once
(`c₀ ≠ ⊤` is all that `universalContinuousSemimeasure_isMaximal` provides, and `c₀ = 0`
would have to be excluded by hand otherwise).
-/

namespace Kolmogorov
namespace Shen

open scoped ENNReal

/-- **Main theorem** (negative answer to Shen's question, strong form).  For every lower
semicomputable conditional continuous semimeasure `Q` and every lower semicomputable
discrete semimeasure `m` there is a constant `c > 0` such that for every `R : ℕ` some
string `u` satisfies `0 < f(u)` and `c · R · m(u) ≤ f(u)`, where
`f = shenF universalContinuousSemimeasure Q`.

Universality of `Q` is not assumed; only universality of `M` is used in the proof. -/
theorem shen_negative (Q : BitString → BitString → ℝ≥0∞)
    (hQ : IsLSCConditionalContinuousSemimeasure Q)
    (m : BitString → ℝ≥0∞) (hm : IsLowerSemicomputableSemimeasure m) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ R : ℕ, ∃ u : BitString,
      0 < shenF universalContinuousSemimeasure Q u ∧
      c * R * m u ≤ shenF universalContinuousSemimeasure Q u := by
  obtain ⟨qa, hqmono, hqsup, hqcomp⟩ := hQ.2
  obtain ⟨ma, hmmono₀, hmsup₀, hmcomp⟩ := hm.2
  have hmmono : ∀ s x, dyadicValue (ma s x []) s ≤ dyadicValue (ma (s + 1) x []) (s + 1) :=
    fun s x => hmmono₀ s x []
  have hmsup : ∀ x, ⨆ s, dyadicValue (ma s x []) s = m x := fun x => hmsup₀ x []
  have hlsc : IsLowerSemicomputableContinuousSemimeasure (nu qa ma) :=
    nu_isLowerSemicomputableContinuousSemimeasure (Q := Q) hQ.1 hqmono hqsup hqcomp hmcomp
  obtain ⟨c₀, hc₀top, hc₀⟩ := universalContinuousSemimeasure_isMaximal _ hlsc
  have hne_top : c₀ + 1 ≠ ⊤ := by
    simp only [ne_eq, ENNReal.add_eq_top, not_or]
    exact ⟨hc₀top, ENNReal.one_ne_top⟩
  have hne_zero : c₀ + 1 ≠ 0 := by
    intro h
    have h1 : (1 : ℝ≥0∞) = 0 := (add_eq_zero.mp h).2
    exact one_ne_zero h1
  refine ⟨(c₀ + 1)⁻¹, ?_, ?_, ?_⟩
  · exact ENNReal.inv_ne_zero.mpr hne_top
  · exact ENNReal.inv_ne_top.mpr hne_zero
  · intro R
    obtain ⟨u, b, σ, hbpos, hdom, hmass⟩ :=
      exists_stuck (Q := Q) (m := m) hQ.1 hm.1 hqmono hqsup hmmono hmsup R
    -- the witnessing constant `λ = (c₀+1)⁻¹ * (b / 2^σ)`
    set lam : ℝ≥0∞ := (c₀ + 1)⁻¹ * dyadicValue b σ with hlam
    have hdyad_pos : dyadicValue b σ ≠ 0 := by
      simp only [dyadicValue, ne_eq, ENNReal.div_eq_zero_iff, not_or]
      refine ⟨?_, ?_⟩
      · exact_mod_cast hbpos.ne'
      · exact ENNReal.pow_ne_top (by simp)
    have hlam_le : lam ≤ shenF universalContinuousSemimeasure Q u := by
      refine le_shenF (fun y => ?_)
      have h1 : dyadicValue b σ * Q y u ≤ nu qa ma (u ++ y) := hdom y
      have h2 : nu qa ma (u ++ y)
          ≤ (c₀ + 1) * universalContinuousSemimeasure (u ++ y) :=
        le_trans (hc₀ (u ++ y)) (by gcongr; exact le_self_add)
      calc lam * Q y u = (c₀ + 1)⁻¹ * (dyadicValue b σ * Q y u) := by
              rw [hlam, mul_assoc]
        _ ≤ (c₀ + 1)⁻¹ * ((c₀ + 1) * universalContinuousSemimeasure (u ++ y)) :=
              mul_le_mul' le_rfl (le_trans h1 h2)
        _ = universalContinuousSemimeasure (u ++ y) := by
              rw [← mul_assoc, ENNReal.inv_mul_cancel hne_zero hne_top, one_mul]
    refine ⟨u, lt_of_lt_of_le ?_ hlam_le, le_trans ?_ hlam_le⟩
    · refine pos_iff_ne_zero.mpr ?_
      rw [hlam]
      exact mul_ne_zero (ENNReal.inv_ne_zero.mpr hne_top) hdyad_pos
    · calc (c₀ + 1)⁻¹ * (R : ℝ≥0∞) * m u
            = (c₀ + 1)⁻¹ * ((R : ℝ≥0∞) * m u) := by rw [mul_assoc]
        _ ≤ (c₀ + 1)⁻¹ * (((R : ℝ≥0∞) + 1) * m u) := by gcongr; exact le_self_add
        _ ≤ (c₀ + 1)⁻¹ * dyadicValue b σ := by gcongr
        _ = lam := hlam.symm

/-! ### Corollaries -/

/-- Values of a semimeasure are finite (each value is bounded by the total mass `≤ 1`). -/
theorem shenF_semimeasure_ne_top {m : BitString → ℝ≥0∞} (hm : IsSemimeasure m)
    (x : BitString) : m x ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (le_trans (ENNReal.le_tsum x) hm)

/-- Corollary: no finite constant `C` bounds `f` by `C · m`: for every `C ≠ ⊤` there is `x`
with `C · m(x) < f(x)`. -/
theorem shen_negative_lt (Q : BitString → BitString → ℝ≥0∞)
    (hQ : IsLSCConditionalContinuousSemimeasure Q)
    (m : BitString → ℝ≥0∞) (hm : IsLowerSemicomputableSemimeasure m) :
    ∀ C : ℝ≥0∞, C ≠ ⊤ → ∃ x : BitString,
      C * m x < shenF universalContinuousSemimeasure Q x := by
  intro C hC
  obtain ⟨c, hc0, hctop, hcR⟩ := shen_negative Q hQ m hm
  obtain ⟨R, hR⟩ : ∃ R : ℕ, C / c < (R : ℝ≥0∞) :=
    ENNReal.exists_nat_gt (ENNReal.div_lt_top hC hc0).ne
  have hCR : C < c * R := by
    have := (ENNReal.div_lt_iff (Or.inl hc0) (Or.inl hctop)).mp hR
    simpa [mul_comm] using this
  obtain ⟨u, hupos, hule⟩ := hcR R
  refine ⟨u, ?_⟩
  rcases eq_or_ne (m u) 0 with hmu | hmu
  · simpa [hmu] using hupos
  · have hmutop : m u ≠ ⊤ := shenF_semimeasure_ne_top hm.1 u
    have hlt : C * m u < c * R * m u := by
      simpa [mul_comm] using ENNReal.mul_lt_mul_right hmu hmutop hCR
    exact lt_of_lt_of_le hlt hule

/-- Corollary: `sup_x f(x) / m(x) = ∞`, i.e. `f ≤ C · m` fails for every finite `C`. -/
theorem shen_negative_not_bounded (Q : BitString → BitString → ℝ≥0∞)
    (hQ : IsLSCConditionalContinuousSemimeasure Q)
    (m : BitString → ℝ≥0∞) (hm : IsLowerSemicomputableSemimeasure m) :
    ¬ ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ x : BitString,
      shenF universalContinuousSemimeasure Q x ≤ C * m x := by
  rintro ⟨C, hC, hall⟩
  obtain ⟨x, hx⟩ := shen_negative_lt Q hQ m hm C hC
  exact absurd (hall x) (not_le.mpr hx)

/-- Shen's question proper: `Q` a universal conditional continuous semimeasure and `m` a
universal discrete semimeasure (only the lower semicomputability of both is used). -/
theorem shen_negative_universal (Q : BitString → BitString → ℝ≥0∞)
    (hQ : IsUniversalConditionalContinuousSemimeasure Q)
    (m : BitString → ℝ≥0∞) (hm : IsUniversalSemimeasure m) :
    ¬ ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ x : BitString,
      shenF universalContinuousSemimeasure Q x ≤ C * m x :=
  shen_negative_not_bounded Q hQ.1 m hm.1

/-- In terms of prefix complexity: `f(x) ≥ 2^D · 2^{-K(x)}` has a solution for every `D`,
i.e. `K(x) - (-log f(x))` is unbounded (via the coding theorem
`universalSemimeasure_equiv_prefixComplexity`). -/
theorem shen_negative_prefixComplexity (Q : BitString → BitString → ℝ≥0∞)
    (hQ : IsLSCConditionalContinuousSemimeasure Q)
    (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∀ C : ℝ≥0∞, C ≠ ⊤ → ∃ x : BitString,
      C * prefixComplexityWeight U x < shenF universalContinuousSemimeasure Q x := by
  intro C hC
  obtain ⟨m, hm⟩ := exists_universalSemimeasure
  obtain ⟨c1, c2, _hc1, hc2, _hfwd, hbwd⟩ :=
    universalSemimeasure_equiv_prefixComplexity hm hU
  -- replace `c2` by `min c2 1`, which is positive, finite and still dominates
  set d : ℝ≥0∞ := min c2 1 with hd
  have hd0 : d ≠ 0 := (lt_min hc2 zero_lt_one).ne'
  have hdtop : d ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  have hbwd' : ∀ x, d * prefixComplexityWeight U x ≤ m x := fun x =>
    le_trans (by gcongr; exact min_le_left _ _) (hbwd x)
  obtain ⟨x, hx⟩ :=
    shen_negative_lt Q hQ m hm.1 (C * d⁻¹)
      (ENNReal.mul_ne_top hC (ENNReal.inv_ne_top.mpr hd0))
  refine ⟨x, ?_⟩
  calc C * prefixComplexityWeight U x
      = C * d⁻¹ * (d * prefixComplexityWeight U x) := by
        rw [mul_assoc, ← mul_assoc d⁻¹, ENNReal.inv_mul_cancel hd0 hdtop, one_mul]
    _ ≤ C * d⁻¹ * m x := by gcongr; exact hbwd' x
    _ < shenF universalContinuousSemimeasure Q x := hx

end Shen
end Kolmogorov
