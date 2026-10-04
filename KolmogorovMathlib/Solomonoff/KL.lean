/-
Copyright (c) 2024 Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Author
-/
import KolmogorovMathlib.Solomonoff.Expectation
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The Kullback–Leibler route: Pinsker's inequality and the chain rule

The quantitative heart of Solomonoff's theorem. For a probability measure `μ` and a continuous
tree semimeasure `a` that is positive wherever `μ` is:

* at each node `x` of positive `μ`-mass, the one-step divergence
  `KL_x = Σ_b μ(b | x) ln(μ(b | x) / a(b | x))` bounds the squared prediction error of either bit,
  `2 (a(b | x) − μ(b | x))² ≤ KL_x` (`two_mul_sq_condProb_sub_le_stepKL`). This is Pinsker's
  inequality for a Bernoulli law against a *sub-probability* (`two_mul_sq_sub_le_binaryKL`),
  reduced to the classical Bernoulli case (`two_mul_sq_sub_le_bernoulliKL`) by moving the deficit
  `1 − a(0 | x) − a(1 | x)` onto the other bit, which only lowers the divergence;
* the expected divergences telescope (chain rule): `Σ_{n<N} E_n[KL] = E_N[ln(μ(x)/a(x))]`
  (`sum_prefixExpectation_stepKL_eq`), since `E_0[ln(μ/a)] = ln(1/1) = 0`;
* if `c · μ ≤ a` then `ln(μ(x)/a(x)) ≤ ln(1/c)` on the support, so the total expected divergence
  is at most `ln(1/c)` at every horizon `N` (`sum_prefixExpectation_stepKL_le`, target KL-TOTAL).

Logarithms are natural (`Real.log`), so divergences are in nats. `stepKL` uses Lean's conventions
`0 · ln(…) = 0` (a bit of `μ`-probability zero contributes nothing, the correct value) and
`ln 0 = 0`; the latter would give a wrong value for a bit with `μ(b | x) > 0 = a(b | x)`, a case
that every statement below excludes by its positivity or domination hypothesis.

Sources: Hutter (2005) Lemma 3.11 (entropy inequalities for semi-probabilities) and the proof of
Theorem 3.19; Li–Vitányi (3rd ed.) §5.2 (proof of Theorem 5.2.1 through the Kullback–Leibler
divergence); Solomonoff (1978).
-/

namespace Kolmogorov

open MeasureTheory
open scoped ENNReal

/-- The one-step Kullback–Leibler divergence
`KL(μ(· | x) ‖ a(· | x)) = Σ_b μ(b | x) ln(μ(b | x) / a(b | x))` (in nats) between the next-bit
laws of the measure `μ` and of the tree mass function `a` after the string `x`. For a semimeasure
`a` the second law is a sub-probability. Item SOL-K-KL; Hutter (2005) §3.2
(`d_t = Σ_{x_t} μ ln(μ/ξ)`), Li–Vitányi (3rd ed.) §5.2. -/
noncomputable def stepKL (μ : Measure CantorSeq) (a : BitString → ℝ≥0∞) (x : BitString) : ℝ :=
  ∑ b : Bool, condProb (cantorMass μ) x b *
    Real.log (condProb (cantorMass μ) x b / condProb a x b)

/-- The log-likelihood ratio `ln(μ(Ω_x) / a(x))` of the measure `μ` against the tree mass
function `a` at the string `x`. Item SOL-K-LR; Hutter (2005) §3.2 (`ln(μ(x_{1:n})/ξ(x_{1:n}))`). -/
noncomputable def logRatio (μ : Measure CantorSeq) (a : BitString → ℝ≥0∞) (x : BitString) :
    ℝ :=
  Real.log ((cantorMass μ x).toReal / (a x).toReal)

open Filter Topology Set
private lemma log_bound_deriv (x : ℝ) (hx₀ : 0 < x) (hx₁ : x < 1) :
    HasDerivAt (fun x => -Real.log (1 - x) - 2 * x ^ 2) ((1 - x)⁻¹ - 4 * x) x := by
  have _ := hx₀
  have hd1 : HasDerivAt (fun x => 1 - x) (-1) x := by
    have eq_func : (fun x : ℝ => 1 - x) = (fun x => 1) - id := by ext; rfl
    have hd_sub := HasDerivAt.sub (hasDerivAt_const x 1) (hasDerivAt_id x)
    exact HasDerivAt.congr_deriv (eq_func ▸ hd_sub) (by ring)
  have hd2 : HasDerivAt (fun x => Real.log (1 - x)) (-(1 - x)⁻¹) x := by
    have h_pos : 0 < 1 - x := sub_pos.mpr hx₁
    exact HasDerivAt.congr_deriv (hd1.log h_pos.ne') (by ring)
  have hd3 : HasDerivAt (fun x : ℝ => -Real.log (1 - x)) ((1 - x)⁻¹) x := by
    exact HasDerivAt.congr_deriv (HasDerivAt.neg hd2) (by ring)
  have hd4_inner_raw : HasDerivAt (fun x : ℝ => x ^ 2) (2 * x ^ (2 - 1)) x := hasDerivAt_pow 2 x
  have hd4_inner : HasDerivAt (fun x : ℝ => x ^ 2) (2 * x) x :=
    HasDerivAt.congr_deriv hd4_inner_raw (by ring)
  have hd4 : HasDerivAt (fun x : ℝ => 2 * x ^ 2) (4 * x) x :=
    HasDerivAt.congr_deriv (HasDerivAt.const_mul 2 hd4_inner) (by ring)
  exact HasDerivAt.congr_deriv (HasDerivAt.sub hd3 hd4) (by ring)
private lemma log_bound (x : ℝ) (hx₀ : 0 < x) (hx₁ : x < 1) :
    0 ≤ -Real.log (1 - x) - 2 * x ^ 2 := by
  let f := fun z => -Real.log (1 - z) - 2 * z ^ 2
  have Hf_deriv : ∀ z ∈ Ioo (0 : ℝ) x, HasDerivAt f ((1 - z)⁻¹ - 4 * z) z := by
    intro z hz
    exact log_bound_deriv z hz.1 (lt_trans hz.2 hx₁)
  have hf_cont : ContinuousOn f (Icc 0 x) := by
    apply ContinuousOn.sub
    · apply ContinuousOn.neg
      apply ContinuousOn.comp Real.continuousOn_log
      · apply ContinuousOn.sub continuousOn_const continuousOn_id
      · intro z hz
        exact (sub_pos.mpr (lt_of_le_of_lt hz.2 hx₁)).ne'
    · apply ContinuousOn.mul continuousOn_const
      have hc2 : ContinuousOn (fun z : ℝ => z ^ 2) (Icc 0 x) := by
        exact Continuous.continuousOn (continuous_pow 2)
      exact hc2
  have H_mean := exists_hasDerivAt_eq_slope f ((fun z => (1 - z)⁻¹ - 4 * z)) hx₀ hf_cont Hf_deriv
  rcases H_mean with ⟨c, hc, hc_deriv⟩
  have hc_deriv_val : f x - f 0 = ((1 - c)⁻¹ - 4 * c) * x := by
    have h_sub : x - 0 = x := by ring
    rw [h_sub] at hc_deriv
    exact (div_eq_iff hx₀.ne').mp hc_deriv.symm
  have hc_pos : 0 ≤ (1 - c)⁻¹ - 4 * c := by
    have hc_lt1 : c < 1 := lt_trans hc.2 hx₁
    have h1c_pos : 0 < 1 - c := sub_pos.mpr hc_lt1
    rw [inv_eq_one_div]
    have h_iff : 4 * c ≤ 1 / (1 - c) := by
      have h_mul : 4 * c * (1 - c) ≤ 1 := by
        have H_mul : 4 * c * (1 - c) = 1 - (2 * c - 1) ^ 2 := by ring
        rw [H_mul]
        have h_sq : 0 ≤ (2 * c - 1) ^ 2 := sq_nonneg (2 * c - 1)
        linarith
      exact (le_div_iff₀ h1c_pos).mpr h_mul
    linarith
  have h_fx_pos : f x - f 0 ≥ 0 := by
    rw [hc_deriv_val]
    exact mul_nonneg hc_pos (le_of_lt hx₀)
  have hf0 : f 0 = 0 := by
    have H : f 0 = -Real.log (1 - 0) - 2 * 0 ^ 2 := rfl
    have H2 : 1 - 0 = (1 : ℝ) := by norm_num
    rw [H, H2, Real.log_one]
    ring
  rw [hf0, sub_zero] at h_fx_pos
  exact h_fx_pos
private lemma test_deriv_has_all (q :
   ℝ) (hq₀ : 0 < q) (hq₁ : q < 1) (y : ℝ) (hy₀ : 0 < y) (hy₁ : y < 1) :
    HasDerivAt (fun x => (1 - x) * Real.log ((1 - x) / (1 - q)) +
        x * Real.log (x / q) - 2 * (x - q) ^ 2)
               (-Real.log ((1 - y) / (1 - q)) + Real.log (y / q) - 4 * (y - q)) y := by
  have hd1_inner1 : HasDerivAt (fun x : ℝ => 1 - x) (-1) y := by
    have eq_func : (fun x : ℝ => 1 - x) = (fun x => 1) - id := by ext; rfl
    have hd_sub := HasDerivAt.sub (hasDerivAt_const y 1) (hasDerivAt_id y)
    exact HasDerivAt.congr_deriv (eq_func ▸ hd_sub) (by ring)
  have h_pos : 0 < (1 - y) / (1 - q) := div_pos (sub_pos.mpr hy₁) (sub_pos.mpr hq₁)
  have hd1_inner2_inner : HasDerivAt (fun x => (1 - x) / (1 - q)) (-(1 - q)⁻¹) y := by
    have H : -1 / (1 - q) = -(1 - q)⁻¹ := by ring
    exact HasDerivAt.congr_deriv (HasDerivAt.div_const hd1_inner1 (1 - q)) H
  have hd1_inner2 : HasDerivAt (fun x => Real.log ((1 - x) / (1 - q))) (-(1 - y)⁻¹) y := by
    have hd_log := hd1_inner2_inner.log h_pos.ne'
    have H : -(1 - q)⁻¹ / ((1 - y) / (1 - q)) = -(1 - y)⁻¹ := by
      have h_1q_pos : 1 - q > 0 := sub_pos.mpr hq₁
      have h1 : -(1 - q)⁻¹ / ((1 - y) / (1 - q)) = -(1 - q)⁻¹ * ((1 - q) / (1 - y)) := by
        have h_div : ((1 - y) / (1 - q)) = (1 - y) * (1 - q)⁻¹ := rfl
        rw [h_div]
        have h_inv : ((1 - y) * (1 - q)⁻¹)⁻¹ = (1 - q) * (1 - y)⁻¹ :=
          mul_inv_rev (1 - y) (1 - q)⁻¹ |>.trans (by rw [inv_inv])
        have h_div2 : -(1 - q)⁻¹ / ((1 - y) * (1 - q)⁻¹) = -(1 - q)⁻¹ * ((1 - y) * (1 - q)⁻¹)⁻¹ :=
          rfl
        rw [h_div2, h_inv]
        rfl
      rw [h1]
      have h2 : -(1 - q)⁻¹ * ((1 - q) / (1 - y)) = -(1 - q)⁻¹ * (1 - q) * (1 - y)⁻¹ := by ring
      rw [h2]
      have h3 : -(1 - q)⁻¹ * (1 - q) = -1 := by
        have h_mul : -(1 - q)⁻¹ * (1 - q) = -((1 - q)⁻¹ * (1 - q)) := by ring
        rw [h_mul, inv_mul_cancel₀ h_1q_pos.ne']
      rw [h3]
      ring
    exact HasDerivAt.congr_deriv hd_log H
  have hd1 : HasDerivAt (fun x => (1 - x) * Real.log ((1 - x) / (1 - q)))
      (-Real.log ((1 - y) / (1 - q)) - 1) y :=
    by
    have hd_mul := HasDerivAt.mul hd1_inner1 hd1_inner2
    have H : -1 * Real.log ((1 - y) / (1 - q)) + (1 - y) * -(1 - y)⁻¹ =
        -Real.log ((1 - y) / (1 - q)) - 1 :=
      by
      have H_inv : (1 - y) * -(1 - y)⁻¹ = -1 := by
        have H_mul : (1 - y) * -(1 - y)⁻¹ = -((1 - y) * (1 - y)⁻¹) := by ring
        rw [H_mul, mul_inv_cancel₀ (sub_pos.mpr hy₁).ne']
      linarith
    exact HasDerivAt.congr_deriv hd_mul H
  have hd2_inner1 : HasDerivAt (fun x : ℝ => x) 1 y := hasDerivAt_id y
  have h_pos2 : 0 < y / q := div_pos hy₀ hq₀
  have hd2_inner2_inner : HasDerivAt (fun x => x / q) (q⁻¹) y := by
    exact HasDerivAt.congr_deriv (HasDerivAt.div_const hd2_inner1 q) (by ring)
  have hd2_inner2 : HasDerivAt (fun x => Real.log (x / q)) (y⁻¹) y := by
    have hd_log := hd2_inner2_inner.log h_pos2.ne'
    have H : q⁻¹ / (y / q) = y⁻¹ := by
      have h1 : q⁻¹ / (y / q) = q⁻¹ * (q / y) := by
        have h_div : (y / q) = y * q⁻¹ := rfl
        rw [h_div]
        have h_inv : (y * q⁻¹)⁻¹ = q * y⁻¹ := mul_inv_rev y q⁻¹ |>.trans (by rw [inv_inv])
        have h_div2 : q⁻¹ / (y * q⁻¹) = q⁻¹ * (y * q⁻¹)⁻¹ := rfl
        rw [h_div2, h_inv]
        rfl
      rw [h1]
      have h2 : q⁻¹ * (q / y) = q⁻¹ * q * y⁻¹ := by ring
      rw [h2]
      have h3 : q⁻¹ * q = 1 := inv_mul_cancel₀ hq₀.ne'
      rw [h3]
      ring
    exact HasDerivAt.congr_deriv hd_log H
  have hd2 : HasDerivAt (fun x => x * Real.log (x / q)) (Real.log (y / q) + 1) y := by
    have hd_mul := HasDerivAt.mul hd2_inner1 hd2_inner2
    have H : 1 * Real.log (y / q) + y * y⁻¹ = Real.log (y / q) + 1 := by
      rw [mul_inv_cancel₀ hy₀.ne']
      ring
    exact HasDerivAt.congr_deriv hd_mul H
  have hd3 : HasDerivAt (fun x : ℝ => 2 * (x - q) ^ 2) (4 * (y - q)) y := by
    have eq_func : (fun x : ℝ => x - q) = id - (fun x => q) := by ext; rfl
    have hd_sub := HasDerivAt.sub (hasDerivAt_id y) (hasDerivAt_const y q)
    have hd_sub_rw : HasDerivAt (fun x : ℝ => x - q) (1 - 0) y := eq_func ▸ hd_sub
    have hd3_inner1 : HasDerivAt (fun x : ℝ => x - q) 1 y :=
      HasDerivAt.congr_deriv hd_sub_rw (by ring)
    have hd_pow_raw := hasDerivAt_pow 2 (y - q)
    have hd_pow : HasDerivAt (fun x : ℝ => x ^ 2) (2 * (y - q)) (y - q) :=
      HasDerivAt.congr_deriv hd_pow_raw (by ring)
    have eq_func2 : (fun x : ℝ => (x - q) ^ 2) = (fun x => x ^ 2) ∘ (fun x => x - q) := by ext; rfl
    have hd3_inner2_raw : HasDerivAt ((fun x => x ^ 2) ∘ (fun x => x - q)) (2 * (y - q) * 1) y :=
      HasDerivAt.comp y hd_pow hd3_inner1
    have hd3_inner2_rw : HasDerivAt (fun x : ℝ => (x - q) ^ 2) (2 * (y - q) * 1) y :=
      eq_func2 ▸ hd3_inner2_raw
    have hd3_inner2 : HasDerivAt (fun x : ℝ => (x - q) ^ 2) (2 * (y - q)) y :=
      HasDerivAt.congr_deriv hd3_inner2_rw (by ring)
    exact HasDerivAt.congr_deriv (HasDerivAt.const_mul 2 hd3_inner2) (by ring)
  have hd_add := HasDerivAt.add hd1 hd2
  have hd_sub := HasDerivAt.sub hd_add hd3
  have H : (-Real.log ((1 - y) / (1 - q)) - 1) + (Real.log (y / q) + 1) - 4 * (y - q) =
      -Real.log ((1 - y) / (1 - q)) + Real.log (y / q) - 4 * (y - q) := by ring
  have eq_func : (fun x : ℝ => (1 - x) * Real.log ((1 - x) / (1 - q)) + x * Real.log (x / q)
    - 2 * (x - q) ^ 2) =
    (fun x : ℝ => (fun x => (1 - x) * Real.log ((1 - x) / (1 - q))) x +
    (fun x => x * Real.log (x / q)) x - (fun x => 2 * (x - q) ^ 2) x) := by ext; rfl
  have hd_sub_rw : HasDerivAt (fun x => (1 - x) * Real.log ((1 - x) / (1 - q)) +
      x * Real.log (x / q) - 2 * (x - q) ^ 2)
      ((-Real.log ((1 - y) / (1 - q)) - 1) + (Real.log (y / q) + 1) - 4 * (y - q)) y := by
    exact eq_func ▸ hd_sub
  exact HasDerivAt.congr_deriv hd_sub_rw H
private lemma test_deriv_has_all_2 (q :
   ℝ) (hq₀ : 0 < q) (hq₁ : q < 1) (y : ℝ) (hy₀ : 0 < y) (hy₁ : y < 1) :
    HasDerivAt (fun x => -Real.log ((1 - x) / (1 - q)) + Real.log (x / q) - 4 * (x - q))
      ((1 - y)⁻¹ + y⁻¹ - 4) y :=
      by
  have hd1_inner1 : HasDerivAt (fun x : ℝ => 1 - x) (-1) y := by
    have eq_func : (fun x : ℝ => 1 - x) = (fun x => 1) - id := by ext; rfl
    have hd_sub := HasDerivAt.sub (hasDerivAt_const y 1) (hasDerivAt_id y)
    exact HasDerivAt.congr_deriv (eq_func ▸ hd_sub) (by ring)
  have h_pos : 0 < (1 - y) / (1 - q) := div_pos (sub_pos.mpr hy₁) (sub_pos.mpr hq₁)
  have hd1_inner2_inner : HasDerivAt (fun x => (1 - x) / (1 - q)) (-(1 - q)⁻¹) y := by
    have H : -1 / (1 - q) = -(1 - q)⁻¹ := by ring
    exact HasDerivAt.congr_deriv (HasDerivAt.div_const hd1_inner1 (1 - q)) H
  have hd1_inner2 : HasDerivAt (fun x => Real.log ((1 - x) / (1 - q))) (-(1 - y)⁻¹) y := by
    have hd_log := hd1_inner2_inner.log h_pos.ne'
    have H : -(1 - q)⁻¹ / ((1 - y) / (1 - q)) = -(1 - y)⁻¹ := by
      have h_1q_pos : 1 - q > 0 := sub_pos.mpr hq₁
      have h1 : -(1 - q)⁻¹ / ((1 - y) / (1 - q)) = -(1 - q)⁻¹ * ((1 - q) / (1 - y)) := by
        have h_div : ((1 - y) / (1 - q)) = (1 - y) * (1 - q)⁻¹ := rfl
        rw [h_div]
        have h_inv : ((1 - y) * (1 - q)⁻¹)⁻¹ = (1 - q) * (1 - y)⁻¹ :=
          mul_inv_rev (1 - y) (1 - q)⁻¹ |>.trans (by rw [inv_inv])
        have h_div2 : -(1 - q)⁻¹ / ((1 - y) * (1 - q)⁻¹) = -(1 - q)⁻¹ * ((1 - y) * (1 - q)⁻¹)⁻¹ :=
          rfl
        rw [h_div2, h_inv]
        rfl
      rw [h1]
      have h2 : -(1 - q)⁻¹ * ((1 - q) / (1 - y)) = -(1 - q)⁻¹ * (1 - q) * (1 - y)⁻¹ := by ring
      rw [h2]
      have h3 : -(1 - q)⁻¹ * (1 - q) = -1 := by
        have h_mul : -(1 - q)⁻¹ * (1 - q) = -((1 - q)⁻¹ * (1 - q)) := by ring
        rw [h_mul, inv_mul_cancel₀ h_1q_pos.ne']
      rw [h3]
      ring
    exact HasDerivAt.congr_deriv hd_log H
  have hd1 : HasDerivAt (fun x => -Real.log ((1 - x) / (1 - q))) ((1 - y)⁻¹) y := by
    exact HasDerivAt.congr_deriv (HasDerivAt.neg hd1_inner2) (by ring)
  have hd2_inner1 : HasDerivAt (fun x : ℝ => x) 1 y := hasDerivAt_id y
  have h_pos2 : 0 < y / q := div_pos hy₀ hq₀
  have hd2_inner2_inner : HasDerivAt (fun x => x / q) (q⁻¹) y := by
    exact HasDerivAt.congr_deriv (HasDerivAt.div_const hd2_inner1 q) (by ring)
  have hd2 : HasDerivAt (fun x => Real.log (x / q)) (y⁻¹) y := by
    have hd_log := hd2_inner2_inner.log h_pos2.ne'
    have H : q⁻¹ / (y / q) = y⁻¹ := by
      have h1 : q⁻¹ / (y / q) = q⁻¹ * (q / y) := by
        have h_div : (y / q) = y * q⁻¹ := rfl
        rw [h_div]
        have h_inv : (y * q⁻¹)⁻¹ = q * y⁻¹ := mul_inv_rev y q⁻¹ |>.trans (by rw [inv_inv])
        have h_div2 : q⁻¹ / (y * q⁻¹) = q⁻¹ * (y * q⁻¹)⁻¹ := rfl
        rw [h_div2, h_inv]
        rfl
      rw [h1]
      have h2 : q⁻¹ * (q / y) = q⁻¹ * q * y⁻¹ := by ring
      rw [h2]
      have h3 : q⁻¹ * q = 1 := inv_mul_cancel₀ hq₀.ne'
      rw [h3]
      ring
    exact HasDerivAt.congr_deriv hd_log H
  have hd3 : HasDerivAt (fun x : ℝ => 4 * (x - q)) 4 y := by
    have eq_func : (fun x : ℝ => x - q) = id - (fun x => q) := by ext; rfl
    have hd_sub := HasDerivAt.sub (hasDerivAt_id y) (hasDerivAt_const y q)
    have hd_sub_rw : HasDerivAt (fun x : ℝ => x - q) (1 - 0) y := eq_func ▸ hd_sub
    have hd3_inner1 : HasDerivAt (fun x : ℝ => x - q) 1 y :=
      HasDerivAt.congr_deriv hd_sub_rw (by ring)
    exact HasDerivAt.congr_deriv (HasDerivAt.const_mul 4 hd3_inner1) (by ring)
  have hd_add := HasDerivAt.add hd1 hd2
  have hd_sub := HasDerivAt.sub hd_add hd3
  have H : (1 - y)⁻¹ + y⁻¹ - 4 = (1 - y)⁻¹ + y⁻¹ - 4 := rfl
  exact HasDerivAt.congr_deriv hd_sub H
private lemma test_mono (q : ℝ) (hq₀ : 0 < q) (hq₁ : q < 1) :
    let f' := fun y => -Real.log ((1 - y) / (1 - q)) + Real.log (y / q) - 4 * (y - q)
    MonotoneOn f' (Ioo (0 : ℝ) 1) := by
  intro f' x hx y hy hxy
  have hd_mean_ex : ∀ z ∈ Ioo x y, ∃ f'_z, HasDerivAt f' f'_z z ∧ 0 ≤ f'_z := by
    intro z hz
    have hz_sub : z ∈ Ioo (0 : ℝ) 1 := ⟨lt_trans hx.1 hz.1, lt_trans hz.2 hy.2⟩
    have h_deriv := test_deriv_has_all_2 q hq₀ hq₁ z hz_sub.1 hz_sub.2
    have h1 : 0 ≤ (1 - z)⁻¹ + z⁻¹ - 4 := by
      have hpos1 : 0 < z := hz_sub.1
      have hpos2 : 0 < 1 - z := sub_pos.mpr hz_sub.2
      have heq : (1 - z)⁻¹ + z⁻¹ = z⁻¹ + (1 - z)⁻¹ := by ring
      rw [heq]
      have heq2 : z⁻¹ + (1 - z)⁻¹ = 1 / (z * (1 - z)) := by
        have h_add : 1 / z + 1 / (1 - z) = (1 - z + z) / (z * (1 - z)) := by
          have H1 : 1 / z + 1 / (1 - z) = (1 * (1 - z) + z * 1) / (z * (1 - z)) :=
            div_add_div _ _ (ne_of_gt hpos1) (ne_of_gt hpos2)
          have H2 : 1 * (1 - z) + z * 1 = 1 - z + z := by ring
          rw [H2] at H1
          exact H1
        have h_num : 1 - z + z = 1 := by ring
        rw [h_num] at h_add
        have H_inv1 : z⁻¹ = 1 / z := inv_eq_one_div z
        have H_inv2 : (1 - z)⁻¹ = 1 / (1 - z) := inv_eq_one_div (1 - z)
        rw [H_inv1, H_inv2]
        exact h_add
      rw [heq2]
      have h_bound : z * (1 - z) ≤ 1 / 4 := by
        have h_sq : z * (1 - z) = 1 / 4 - (z - 1/2) ^ 2 := by ring
        linarith [sq_nonneg (z - 1/2)]
      have h_pos : 0 < z * (1 - z) := mul_pos hpos1 hpos2
      have h_div : 4 ≤ 1 / (z * (1 - z)) := by
        have h_tmp : 1 / (1 / 4 : ℝ) ≤ 1 / (z * (1 - z)) := one_div_le_one_div_of_le h_pos h_bound
        have H_val : 1 / (1 / 4 : ℝ) = 4 := by norm_num
        rw [H_val] at h_tmp
        exact h_tmp
      linarith
    exact ⟨(1 - z)⁻¹ + z⁻¹ - 4, h_deriv, h1⟩
  by_cases h_eq : x = y
  · rw [h_eq]
  have hxy_lt : x < y := lt_of_le_of_ne hxy h_eq
  have hcont : ContinuousOn f' (Ioo (0 : ℝ) 1) := by
    apply ContinuousOn.sub
    · apply ContinuousOn.add
      · apply ContinuousOn.neg
        apply ContinuousOn.comp (Real.continuousOn_log)
        · apply ContinuousOn.div
          · apply ContinuousOn.sub continuousOn_const continuousOn_id
          · exact continuousOn_const
          · intro z hz
            exact ne_of_gt (sub_pos.mpr hq₁)
        · intro z hz
          exact ne_of_gt (div_pos (sub_pos.mpr hz.2) (sub_pos.mpr hq₁))
      · apply ContinuousOn.comp (Real.continuousOn_log)
        · apply ContinuousOn.div continuousOn_id continuousOn_const
          intro z hz
          exact ne_of_gt hq₀
        · intro z hz
          exact ne_of_gt (div_pos hz.1 hq₀)
    · apply ContinuousOn.mul continuousOn_const
      exact ContinuousOn.sub continuousOn_id continuousOn_const
  have H_mean :=
    exists_hasDerivAt_eq_slope f' (fun z => (1 - z)⁻¹ + z⁻¹ - 4) hxy_lt (hcont.mono (fun z hz => by
    have hz_sub : z ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_lt_of_le hx.1 hz.1, lt_of_le_of_lt hz.2 hy.2⟩
    exact hz_sub
  )) (fun z hz => by
    rcases hd_mean_ex z hz with ⟨f'_z, hdf'_z, hpos_z⟩
    have heq : f'_z = (1 - z)⁻¹ + z⁻¹ - 4 := by
      have h_deriv := test_deriv_has_all_2 q hq₀ hq₁ z (lt_trans hx.1 hz.1) (lt_trans hz.2 hy.2)
      have hu := hdf'_z.unique h_deriv
      exact hu
    simpa only [heq] using hdf'_z
  )
  rcases H_mean with ⟨c, hc, hc_deriv⟩
  have hc_pos : 0 ≤ (1 - c)⁻¹ + c⁻¹ - 4 := by
    rcases hd_mean_ex c hc with ⟨f'_c, hdf'_c, hpos_c⟩
    have h_deriv := test_deriv_has_all_2 q hq₀ hq₁ c (lt_trans hx.1 hc.1) (lt_trans hc.2 hy.2)
    have heq : f'_c = (1 - c)⁻¹ + c⁻¹ - 4 := hdf'_c.unique h_deriv
    rw [←heq]
    exact hpos_c
  have hc_eq : (1 - c)⁻¹ + c⁻¹ - 4 = (f' y - f' x) / (y - x) := hc_deriv
  rw [hc_eq] at hc_pos
  have h_mul : 0 ≤ ((f' y - f' x) / (y - x)) * (y - x) := mul_nonneg hc_pos (sub_nonneg.mpr hxy)
  have h_mul2 : ((f' y - f' x) / (y - x)) * (y - x) = f' y - f' x :=
    div_mul_cancel₀ _ (ne_of_gt (sub_pos.mpr hxy_lt))
  rw [h_mul2] at h_mul
  exact sub_nonneg.mp h_mul
private lemma min_q (q : ℝ) (hq₀ : 0 < q) (hq₁ : q < 1) :
    let f :=
      fun x => (1 - x) * Real.log ((1 - x) / (1 - q)) + x * Real.log (x / q) - 2 * (x - q) ^ 2
    ∀ y ∈ Ioo (0 : ℝ) 1, 0 ≤ f y := by
  intro f y hy
  have Hf0 : f q = 0 := by
    dsimp [f]
    have h1 : (1 - q) / (1 - q) = 1 := div_self (ne_of_gt (sub_pos.mpr hq₁))
    have h2 : q / q = 1 := div_self (ne_of_gt hq₀)
    rw [h1, h2]
    rw [Real.log_one, mul_zero, mul_zero, sub_self, zero_pow (by norm_num),
      mul_zero, add_zero, sub_zero]
  let f' := fun z => -Real.log ((1 - z) / (1 - q)) + Real.log (z / q) - 4 * (z - q)
  have Hf_deriv : ∀ z ∈ Ioo (0 : ℝ) 1, HasDerivAt f (f' z) z := by
    intro z hz
    exact test_deriv_has_all q hq₀ hq₁ z hz.1 hz.2
  have hf_cont : ContinuousOn f (Ioo (0 : ℝ) 1) := by
    apply ContinuousOn.sub
    · apply ContinuousOn.add
      · apply ContinuousOn.mul
        · exact ContinuousOn.sub continuousOn_const continuousOn_id
        · apply ContinuousOn.comp Real.continuousOn_log
          · apply ContinuousOn.div
            · exact ContinuousOn.sub continuousOn_const continuousOn_id
            · exact continuousOn_const
            · intro z hz
              exact ne_of_gt (sub_pos.mpr hq₁)
          · intro z hz
            exact ne_of_gt (div_pos (sub_pos.mpr hz.2) (sub_pos.mpr hq₁))
      · apply ContinuousOn.mul continuousOn_id
        apply ContinuousOn.comp Real.continuousOn_log
        · apply ContinuousOn.div continuousOn_id continuousOn_const
          intro z hz
          exact ne_of_gt hq₀
        · intro z hz
          exact ne_of_gt (div_pos hz.1 hq₀)
    · apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.pow
      exact ContinuousOn.sub continuousOn_id continuousOn_const
  have Hf'_mono := test_mono q hq₀ hq₁
  have Hf'0 : f' q = 0 := by
    dsimp [f']
    have h1 : (1 - q) / (1 - q) = 1 := div_self (ne_of_gt (sub_pos.mpr hq₁))
    have h2 : q / q = 1 := div_self (ne_of_gt hq₀)
    rw [h1, h2]
    rw [Real.log_one, neg_zero, zero_add, sub_self, mul_zero, sub_zero]
  by_cases h_y : y = q
  · rw [h_y]
    exact le_of_eq Hf0.symm
  · rcases lt_trichotomy y q with h_lt | h_eq | h_gt
    · have h_yq : y < q := h_lt
      have hq_sub : q ∈ Ioo (0 : ℝ) 1 := ⟨hq₀, hq₁⟩
      have h_f_anti : AntitoneOn f (Icc y q) := by
        apply antitoneOn_of_deriv_nonpos (convex_Icc y q)
        · exact hf_cont.mono (fun z hz => ⟨lt_of_lt_of_le hy.1 hz.1, lt_of_le_of_lt hz.2 hq₁⟩)
        · have h_inter : interior (Icc y q) = Ioo y q := interior_Icc
          rw [h_inter]
          intro z hz
          have hz_sub : z ∈ Ioo (0 : ℝ) 1 := ⟨lt_trans hy.1 hz.1, lt_trans hz.2 hq₁⟩
          exact (Hf_deriv z hz_sub).differentiableAt.differentiableWithinAt
        · have h_inter : interior (Icc y q) = Ioo y q := interior_Icc
          rw [h_inter]
          intro z hz
          have hz_sub : z ∈ Ioo (0 : ℝ) 1 := ⟨lt_trans hy.1 hz.1, lt_trans hz.2 hq₁⟩
          have H_deriv := Hf_deriv z hz_sub
          have heq : deriv f z = f' z := H_deriv.deriv
          rw [heq]
          have Hf'z : f' z ≤ f' q := Hf'_mono hz_sub hq_sub (le_of_lt hz.2)
          rw [Hf'0] at Hf'z
          exact Hf'z
      have h_le : f q ≤ f y :=
        h_f_anti (left_mem_Icc.mpr (le_of_lt h_yq))
          (right_mem_Icc.mpr (le_of_lt h_yq)) (le_of_lt h_yq)
      rw [Hf0] at h_le
      exact h_le
    · exfalso
      exact h_y h_eq
    · have h_qy : q < y := h_gt
      have hq_sub : q ∈ Ioo (0 : ℝ) 1 := ⟨hq₀, hq₁⟩
      have h_f_mono : MonotoneOn f (Icc q y) := by
        apply monotoneOn_of_deriv_nonneg (convex_Icc q y)
        · exact hf_cont.mono (fun z hz => ⟨lt_of_lt_of_le hq₀ hz.1, lt_of_le_of_lt hz.2 hy.2⟩)
        · have h_inter : interior (Icc q y) = Ioo q y := interior_Icc
          rw [h_inter]
          intro z hz
          have hz_sub : z ∈ Ioo (0 : ℝ) 1 := ⟨lt_trans hq₀ hz.1, lt_trans hz.2 hy.2⟩
          exact (Hf_deriv z hz_sub).differentiableAt.differentiableWithinAt
        · have h_inter : interior (Icc q y) = Ioo q y := interior_Icc
          rw [h_inter]
          intro z hz
          have hz_sub : z ∈ Ioo (0 : ℝ) 1 := ⟨lt_trans hq₀ hz.1, lt_trans hz.2 hy.2⟩
          have H_deriv := Hf_deriv z hz_sub
          have heq : deriv f z = f' z := H_deriv.deriv
          rw [heq]
          have Hf'z : f' q ≤ f' z := Hf'_mono hq_sub hz_sub (le_of_lt hz.1)
          rw [Hf'0] at Hf'z
          exact Hf'z
      have h_le : f q ≤ f y :=
        h_f_mono (left_mem_Icc.mpr (le_of_lt h_qy))
          (right_mem_Icc.mpr (le_of_lt h_qy)) (le_of_lt h_qy)
      rw [Hf0] at h_le
      exact h_le
private lemma two_mul_sq_sub_le_bernoulliKL_pos (p q : ℝ) (hp₀ : 0 < p) (hp₁ : p < 1) (hq₀ : 0 < q)
    (hq₁ : q < 1) :
    2 * (p - q) ^ 2 ≤ (1 - p) * Real.log ((1 - p) / (1 - q)) + p * Real.log (p / q) := by
  have H := min_q q hq₀ hq₁ p ⟨hp₀, hp₁⟩
  linarith
/-- **Pinsker's inequality for Bernoulli laws.** For `p ∈ [0, 1]` and `q ∈ (0, 1)`,
`2 (p − q)² ≤ (1 − p) ln((1 − p)/(1 − q)) + p ln(p/q)`. Item SOL-K-PINSKER; classical, e.g.
Hutter (2005) Lemma 3.11 in the binary case. -/
theorem two_mul_sq_sub_le_bernoulliKL {p q : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (hq₀ : 0 < q)
    (hq₁ : q < 1) :
    2 * (p - q) ^ 2 ≤ (1 - p) * Real.log ((1 - p) / (1 - q)) + p * Real.log (p / q) := by
  by_cases h_p0 : p = 0
  · rw [h_p0]
    have H1 : 2 * (0 - q) ^ 2 = 2 * q ^ 2 := by ring
    have H2 : (1 - 0) * Real.log ((1 - 0) / (1 - q)) + 0 * Real.log (0 / q) = -Real.log (1 - q) :=
      by
      have H2a : (1 - 0) * Real.log ((1 - 0) / (1 - q)) = Real.log (1 / (1 - q)) := by ring_nf
      have H2c : 0 * Real.log (0 / q) = 0 := by ring
      rw [H2a, H2c, add_zero]
      have H2b : 1 / (1 - q) = (1 - q)⁻¹ := by ring
      rw [H2b, Real.log_inv]
    rw [H1, H2]
    have h_bnd := log_bound q hq₀ hq₁
    linarith
  have hp₀_pos : 0 < p := lt_of_le_of_ne hp₀ (Ne.symm h_p0)
  by_cases h_p1 : p = 1
  · rw [h_p1]
    have H1 : 2 * (1 - q) ^ 2 = 2 * (1 - q) ^ 2 := rfl
    have H2 : (1 - 1) * Real.log ((1 - 1) / (1 - q)) + 1 * Real.log (1 / q) = -Real.log q := by
      have H2a : (1 - 1) * Real.log ((1 - 1) / (1 - q)) = 0 := by ring_nf
      rw [H2a, zero_add, one_mul]
      have H2b : 1 / q = q⁻¹ := by ring
      rw [H2b, Real.log_inv]
    rw [H1, H2]
    have h_sub : 1 - (1 - q) = q := by ring
    have h_lt_sub : 1 - q < 1 := by linarith
    have h_pos_sub : 0 < 1 - q := sub_pos.mpr hq₁
    have H_bound := log_bound (1 - q) h_pos_sub h_lt_sub
    rw [h_sub] at H_bound
    linarith
  have hp₁_lt : p < 1 := lt_of_le_of_ne hp₁ h_p1
  exact two_mul_sq_sub_le_bernoulliKL_pos p q hp₀_pos hp₁_lt hq₀ hq₁

/-- **Pinsker's inequality against a sub-probability.** For a Bernoulli law `(1 − p, p)` and
weights `q₀, q₁ ≥ 0` with `q₀ + q₁ ≤ 1` that are positive wherever the law is,
`2 (p − q₁)² ≤ (1 − p) ln((1 − p)/q₀) + p ln(p/q₁)`: the deficit `1 − q₀ − q₁` never helps the
predictor. Item SOL-K-PINSKER-SUB; Hutter (2005) Lemma 3.11 (entropy inequality, `Σ z_i ≤ 1`). -/
theorem two_mul_sq_sub_le_binaryKL {p q₀ q₁ : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (hq₀ : 0 ≤ q₀)
    (hq₁ : 0 ≤ q₁) (hq : q₀ + q₁ ≤ 1) (hpos₀ : p < 1 → 0 < q₀) (hpos₁ : 0 < p → 0 < q₁) :
    2 * (p - q₁) ^ 2 ≤ (1 - p) * Real.log ((1 - p) / q₀) + p * Real.log (p / q₁) := by
  by_cases h_p1 : p = 1
  · rw [h_p1]
    have h_q1_pos : 0 < q₁ := hpos₁ (by linarith)
    have H1 : 2 * (1 - q₁) ^ 2 = 2 * (1 - q₁) ^ 2 := rfl
    have H2 : (1 - 1) * Real.log ((1 - 1) / q₀) + 1 * Real.log (1 / q₁) = -Real.log q₁ := by
      have H2a : (1 - 1) * Real.log ((1 - 1) / q₀) = 0 := by ring_nf
      rw [H2a, zero_add, one_mul]
      have H2b : 1 / q₁ = q₁⁻¹ := by ring
      rw [H2b, Real.log_inv]
    rw [H1, H2]
    have h_q1_lt1 : q₁ ≤ 1 := by linarith
    by_cases h_q1_eq1 : q₁ = 1
    · rw [h_q1_eq1]
      have H3 : 2 * (1 - 1) ^ 2 = 0 := by ring
      have H4 : -Real.log (1:ℝ) = 0 := by rw [Real.log_one, neg_zero]
      linarith
    · have h_q1_lt1' : q₁ < 1 := lt_of_le_of_ne h_q1_lt1 h_q1_eq1
      have H_bound := log_bound (1 - q₁) (by linarith) (by linarith)
      have h_sub : 1 - (1 - q₁) = q₁ := by ring
      rw [h_sub] at H_bound
      linarith
  by_cases h_p0 : p = 0
  · rw [h_p0]
    have h_q0_pos : 0 < q₀ := hpos₀ (by linarith)
    have H1 : 2 * (0 - q₁) ^ 2 = 2 * q₁ ^ 2 := by ring
    have H2 : (1 - 0) * Real.log ((1 - 0) / q₀) + 0 * Real.log (0 / q₁) = -Real.log q₀ := by
      have H2a : (1 - 0) * Real.log ((1 - 0) / q₀) = Real.log (1 / q₀) := by ring_nf
      have H2c : 0 * Real.log (0 / q₁) = 0 := by ring
      rw [H2a, H2c, add_zero]
      have H2b : 1 / q₀ = q₀⁻¹ := by ring
      rw [H2b, Real.log_inv]
    rw [H1, H2]
    have h_q1_bound : q₁ ≤ 1 - q₀ := by linarith
    have h_q1_pos_le : 0 ≤ q₁ := hq₁
    have h_q0_bound_pos : 0 ≤ 1 - q₀ := by linarith
    have h_sq : q₁ ^ 2 ≤ (1 - q₀) ^ 2 := by
      nlinarith
    have h_q0_lt1 : q₀ ≤ 1 := by linarith
    by_cases h_q0_eq1 : q₀ = 1
    · rw [h_q0_eq1]
      have h_q1_0 : q₁ = 0 := by linarith
      rw [h_q1_0]
      have H3 : 2 * (0:ℝ) ^ 2 = 0 := by ring
      have H4 : -Real.log (1:ℝ) = 0 := by rw [Real.log_one, neg_zero]
      linarith
    · have h_q0_lt1' : q₀ < 1 := lt_of_le_of_ne h_q0_lt1 h_q0_eq1
      have H_bound := log_bound q₀ h_q0_pos h_q0_lt1'
      -- Wait, H_bound is 2q0^2 <= -log(1-q0). But we want 2q1^2 <= -log(q0).
      have h_sub_1_q1 : q₁ < 1 := by linarith
      by_cases h_q1_eq0 : q₁ = 0
      · rw [h_q1_eq0]
        have h_0_sq : 2 * (0:ℝ) ^ 2 = 0 := by ring
        rw [h_0_sq]
        have h_log_pos : 0 ≤ -Real.log q₀ := by
          have h_q0_le_1 : q₀ ≤ 1 := by linarith
          have h_log_le_0 : Real.log q₀ ≤ 0 := Real.log_nonpos (le_of_lt h_q0_pos) h_q0_le_1
          linarith
        linarith
      · have h_q1_pos' : 0 < q₁ := lt_of_le_of_ne hq₁ (Ne.symm h_q1_eq0)
        have H_bound2 := log_bound q₁ h_q1_pos' h_sub_1_q1
        have h_log_mono : -Real.log (1 - q₁) ≤ -Real.log q₀ := by
          have h_log_le : Real.log q₀ ≤ Real.log (1 - q₁) := Real.log_le_log h_q0_pos (by linarith)
          linarith
        linarith
  have hp₀_pos : 0 < p := lt_of_le_of_ne hp₀ (Ne.symm h_p0)
  have hp₁_lt : p < 1 := lt_of_le_of_ne hp₁ h_p1
  have h_q0_pos : 0 < q₀ := hpos₀ hp₁_lt
  have h_q1_pos : 0 < q₁ := hpos₁ hp₀_pos
  have h_q1_lt1 : q₁ < 1 := by linarith
  have H_ber : 2 * (p - q₁) ^ 2 ≤ (1 - p) * Real.log ((1 - p) / (1 - q₁)) + p * Real.log (p / q₁) :=
    two_mul_sq_sub_le_bernoulliKL_pos p q₁ hp₀_pos hp₁_lt h_q1_pos h_q1_lt1
  have h_q0_bound : q₀ ≤ 1 - q₁ := by linarith
  have h_1_p_pos : 0 < 1 - p := sub_pos.mpr hp₁_lt
  have h_1_q1_pos : 0 < 1 - q₁ := sub_pos.mpr h_q1_lt1
  have h_log_le : Real.log ((1 - p) / (1 - q₁)) ≤ Real.log ((1 - p) / q₀) := by
    apply Real.log_le_log (div_pos h_1_p_pos h_1_q1_pos)
    exact div_le_div_of_nonneg_left (le_of_lt h_1_p_pos) h_q0_pos h_q0_bound
  have h_mul_le : (1 - p) * Real.log ((1 - p) / (1 - q₁)) ≤ (1 - p) * Real.log ((1 - p) / q₀) :=
    mul_le_mul_of_nonneg_left h_log_le (le_of_lt h_1_p_pos)
  linarith

/-- **Pinsker at a node.** For a probability measure `μ` and a continuous tree semimeasure `a`
positive wherever `μ` is, at every node `x` of positive `μ`-mass and for either bit `b`,
`2 (a(b | x) − μ(b | x))² ≤ KL(μ(· | x) ‖ a(· | x))`. Item SOL-K-NODE; Hutter (2005) Lemma 3.11
and Theorem 3.19 (`s_t ≤ d_t`), Li–Vitányi (3rd ed.) §5.2. -/
theorem two_mul_sq_condProb_sub_le_stepKL (μ : Measure CantorSeq) [IsProbabilityMeasure μ]
    {a : BitString → ℝ≥0∞} (ha : IsContinuousTreeSemimeasure a)
    (hac : ∀ y, cantorMass μ y ≠ 0 → a y ≠ 0) {x : BitString} (hx : cantorMass μ x ≠ 0)
    (b : Bool) :
    2 * (condProb a x b - condProb (cantorMass μ) x b) ^ 2 ≤ stepKL μ a x := by
  let p := condProb (cantorMass μ) x b
  let q₁ := condProb a x b
  let q₀ := condProb a x (!b)
  have hp₀ : 0 ≤ p := condProb_nonneg _ _ _
  have hp₁ : p ≤ 1 := by
    have h1 := condProb_cantorMass_add_eq_one μ hx
    cases b
    · exact le_trans (le_add_of_nonneg_right (condProb_nonneg (cantorMass μ) x true)) (le_of_eq h1)
    · exact le_trans (le_add_of_nonneg_left (condProb_nonneg (cantorMass μ) x false)) (le_of_eq h1)
  have hq₀ : 0 ≤ q₀ := condProb_nonneg _ _ _
  have hq₁ : 0 ≤ q₁ := condProb_nonneg _ _ _
  have hq : q₀ + q₁ ≤ 1 := by
    cases b
    · change condProb a x true + condProb a x false ≤ 1
      rw [add_comm]
      exact ha.condProb_add_le_one x
    · change condProb a x false + condProb a x true ≤ 1
      exact ha.condProb_add_le_one x
  have hp_not_b : condProb (cantorMass μ) x (!b) = 1 - p := by
    have h1 := condProb_cantorMass_add_eq_one μ hx
    cases b
    · change condProb (cantorMass μ) x true = 1 - condProb (cantorMass μ) x false
      linarith
    · change condProb (cantorMass μ) x false = 1 - condProb (cantorMass μ) x true
      linarith
  have hpos₀ : p < 1 → 0 < q₀ := by
    intro _
    have h_cond_mu : 0 < (cantorMass μ (x ++ [!b])).toReal := by
      have hh := (isContinuousTreeSemimeasure_cantorMass μ).toReal_mul_condProb x (!b)
      rw [←hh]
      have hmux_pos : 0 < (cantorMass μ x).toReal := ENNReal.toReal_pos hx (measure_ne_top μ _)
      have h_not_p : 0 < condProb (cantorMass μ) x (!b) := by linarith
      positivity
    have hmuxb_ne : cantorMass μ (x ++ [!b]) ≠ 0 := by
      intro h_zero
      simp [h_zero] at h_cond_mu
    have ha_pos : 0 < (a (x ++ [!b])).toReal := ENNReal.toReal_pos (hac _ hmuxb_ne) (ha.ne_top _)
    have ha_x_pos : 0 < (a x).toReal := ENNReal.toReal_pos (hac _ hx) (ha.ne_top _)
    have hq0_eq : q₀ = (a (x ++ [!b])).toReal / (a x).toReal := rfl
    rw [hq0_eq]
    exact div_pos ha_pos ha_x_pos
  have hpos₁ : 0 < p → 0 < q₁ := by
    intro _
    have h_cond_mu : 0 < (cantorMass μ (x ++ [b])).toReal := by
      have hh := (isContinuousTreeSemimeasure_cantorMass μ).toReal_mul_condProb x b
      rw [←hh]
      have hmux_pos : 0 < (cantorMass μ x).toReal := ENNReal.toReal_pos hx (measure_ne_top μ _)
      positivity
    have hmuxb_ne : cantorMass μ (x ++ [b]) ≠ 0 := by
      intro h_zero
      simp [h_zero] at h_cond_mu
    have ha_pos : 0 < (a (x ++ [b])).toReal := ENNReal.toReal_pos (hac _ hmuxb_ne) (ha.ne_top _)
    have ha_x_pos : 0 < (a x).toReal := ENNReal.toReal_pos (hac _ hx) (ha.ne_top _)
    have hq1_eq : q₁ = (a (x ++ [b])).toReal / (a x).toReal := rfl
    rw [hq1_eq]
    exact div_pos ha_pos ha_x_pos
  have ht := two_mul_sq_sub_le_binaryKL hp₀ hp₁ hq₀ hq₁ hq hpos₀ hpos₁
  have hs : stepKL μ a x = (1 - p) * Real.log ((1 - p) / q₀) + p * Real.log (p / q₁) := by
    unfold stepKL
    rw [Fintype.sum_bool]
    cases b
    · have h_p_eq : condProb (cantorMass μ) x false = p := rfl
      have h_not_p_eq : condProb (cantorMass μ) x true = 1 - p := hp_not_b
      have h_q1_eq : condProb a x false = q₁ := rfl
      have h_q0_eq : condProb a x true = q₀ := rfl
      rw [h_p_eq, h_not_p_eq, h_q1_eq, h_q0_eq]
    · have h_p_eq : condProb (cantorMass μ) x true = p := rfl
      have h_not_p_eq : condProb (cantorMass μ) x false = 1 - p := hp_not_b
      have h_q1_eq : condProb a x true = q₁ := rfl
      have h_q0_eq : condProb a x false = q₀ := rfl
      rw [h_p_eq, h_not_p_eq, h_q1_eq, h_q0_eq]
      exact add_comm _ _
  have hz : 2 * (q₁ - p) ^ 2 = 2 * (p - q₁) ^ 2 := by ring
  have ht2 : 2 * (q₁ - p) ^ 2 ≤ (1 - p) * Real.log ((1 - p) / q₀) + p * Real.log (p / q₁) := by
    rw [hz]
    exact ht
  rw [hs]
  exact ht2

/-- The one-step divergence is nonnegative at every node of positive `μ`-mass, under the
hypotheses of `two_mul_sq_condProb_sub_le_stepKL`. Item SOL-K-NODE-NONNEG. -/
theorem stepKL_nonneg (μ : Measure CantorSeq) [IsProbabilityMeasure μ] {a : BitString → ℝ≥0∞}
    (ha : IsContinuousTreeSemimeasure a) (hac : ∀ y, cantorMass μ y ≠ 0 → a y ≠ 0)
    {x : BitString} (hx : cantorMass μ x ≠ 0) : 0 ≤ stepKL μ a x := by
  have ht := two_mul_sq_condProb_sub_le_stepKL μ ha hac hx true
  have hz : 0 ≤ 2 * (condProb a x true - condProb (cantorMass μ) x true) ^ 2 := by positivity
  exact le_trans hz ht

/-- One step of the chain rule: the expected one-step divergence at level `n` is the increment
`E_{n+1}[ln(μ/a)] − E_n[ln(μ/a)]` of the expected log-likelihood ratio. Item SOL-K-STEP;
Hutter (2005) §3.2 (chain rule for relative entropy). -/
theorem prefixExpectation_stepKL_eq_sub (μ : Measure CantorSeq) [IsProbabilityMeasure μ]
    {a : BitString → ℝ≥0∞} (ha : IsContinuousTreeSemimeasure a)
    (hac : ∀ y, cantorMass μ y ≠ 0 → a y ≠ 0) (n : ℕ) :
    prefixExpectation μ n (stepKL μ a) =
      prefixExpectation μ (n + 1) (logRatio μ a) - prefixExpectation μ n (logRatio μ a) := by
  rw [prefixExpectation_succ]
  have h_log_sum : ∀ x, cantorMass μ x ≠ 0 →
      ∑ b : Bool, condProb (cantorMass μ) x b * logRatio μ a (x ++ [b]) =
      logRatio μ a x + stepKL μ a x := by
    intro x hx
    unfold stepKL logRatio
    have h_sum_cond_mu : ∑ b : Bool, condProb (cantorMass μ) x b = 1 := by
      have h1 := condProb_cantorMass_add_eq_one μ hx
      rw [Fintype.sum_bool]
      simpa [add_comm] using h1
    have h_sum_split :
        ∑ b : Bool, condProb (cantorMass μ) x b *
            (Real.log ((cantorMass μ x).toReal / (a x).toReal) +
              Real.log (condProb (cantorMass μ) x b / condProb a x b)) =
          (∑ b : Bool, condProb (cantorMass μ) x b *
              Real.log ((cantorMass μ x).toReal / (a x).toReal)) +
            ∑ b : Bool, condProb (cantorMass μ) x b *
              Real.log (condProb (cantorMass μ) x b / condProb a x b) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro b _
      exact mul_add _ _ _
    apply Eq.symm
    calc
      Real.log ((cantorMass μ x).toReal / (a x).toReal) +
          ∑ b : Bool, condProb (cantorMass μ) x b *
            Real.log (condProb (cantorMass μ) x b / condProb a x b)
          = (∑ b : Bool, condProb (cantorMass μ) x b) *
                Real.log ((cantorMass μ x).toReal / (a x).toReal) +
              ∑ b : Bool, condProb (cantorMass μ) x b *
                Real.log (condProb (cantorMass μ) x b / condProb a x b) := by
        rw [h_sum_cond_mu, one_mul]
      _ = (∑ b : Bool, condProb (cantorMass μ) x b *
              Real.log ((cantorMass μ x).toReal / (a x).toReal)) +
            ∑ b : Bool, condProb (cantorMass μ) x b *
              Real.log (condProb (cantorMass μ) x b / condProb a x b) := by
        rw [Finset.sum_mul]
      _ = ∑ b : Bool, condProb (cantorMass μ) x b *
            (Real.log ((cantorMass μ x).toReal / (a x).toReal) +
              Real.log (condProb (cantorMass μ) x b / condProb a x b)) := by
        rw [h_sum_split]
      _ = ∑ b : Bool, condProb (cantorMass μ) x b *
            Real.log
              ((cantorMass μ (x ++ [b])).toReal / (a (x ++ [b])).toReal) := by
        apply Finset.sum_congr rfl
        intro b _
        by_cases hb : condProb (cantorMass μ) x b = 0
        · simp [hb]
        have hμx : 0 < (cantorMass μ x).toReal :=
          ENNReal.toReal_pos hx (measure_ne_top μ _)
        have hax : 0 < (a x).toReal := ENNReal.toReal_pos (hac x hx) (ha.ne_top x)
        have hμb : 0 < condProb (cantorMass μ) x b :=
          lt_of_le_of_ne (condProb_nonneg _ _ _) (Ne.symm hb)
        have hμxb :
            (cantorMass μ (x ++ [b])).toReal =
              (cantorMass μ x).toReal * condProb (cantorMass μ) x b :=
          (isContinuousTreeSemimeasure_cantorMass μ).toReal_mul_condProb x b |>.symm
        have hμxb_pos : 0 < (cantorMass μ (x ++ [b])).toReal := by
          rw [hμxb]
          positivity
        have hμxb_ne : cantorMass μ (x ++ [b]) ≠ 0 := by
          intro hzero
          simp [hzero] at hμxb_pos
        have haxb : 0 < (a (x ++ [b])).toReal :=
          ENNReal.toReal_pos (hac _ hμxb_ne) (ha.ne_top _)
        have hab : 0 < condProb a x b := by
          unfold condProb
          positivity
        have ha_xb :
            (a (x ++ [b])).toReal = (a x).toReal * condProb a x b :=
          (ha.toReal_mul_condProb x b).symm
        congr 1
        rw [hμxb, ha_xb, mul_div_mul_comm]
        exact (Real.log_mul (div_ne_zero hμx.ne' hax.ne')
          (div_ne_zero hμb.ne' hab.ne')).symm
  have h_tower :
      prefixExpectation μ n
          (fun x => ∑ b : Bool,
            condProb (cantorMass μ) x b * logRatio μ a (x ++ [b])) =
        prefixExpectation μ n (fun x => logRatio μ a x + stepKL μ a x) := by
    unfold prefixExpectation
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : cantorMass μ x = 0
    · simp [hx]
    · change (cantorMass μ x).toReal *
          (∑ b : Bool, condProb (cantorMass μ) x b * logRatio μ a (x ++ [b])) =
          (cantorMass μ x).toReal * (logRatio μ a x + stepKL μ a x)
      rw [h_log_sum x hx]
  rw [h_tower, prefixExpectation_add]
  ring

/-- **Chain rule.** The expected one-step divergences telescope:
`Σ_{n<N} E_n[KL(μ(· | x) ‖ a(· | x))] = E_N[ln(μ(x)/a(x))]`. Item SOL-K-CHAIN; Hutter (2005)
§3.2 (`D_n = Σ_t E[d_t] = E[ln(μ(x_{1:n})/ξ(x_{1:n}))]`), Li–Vitányi (3rd ed.) §5.2. -/
theorem sum_prefixExpectation_stepKL_eq (μ : Measure CantorSeq) [IsProbabilityMeasure μ]
    {a : BitString → ℝ≥0∞} (ha : IsContinuousTreeSemimeasure a)
    (hac : ∀ y, cantorMass μ y ≠ 0 → a y ≠ 0) (N : ℕ) :
    ∑ n ∈ Finset.range N, prefixExpectation μ n (stepKL μ a) =
      prefixExpectation μ N (logRatio μ a) := by
  induction N with
  | zero =>
      rw [Finset.range_zero, Finset.sum_empty, prefixExpectation_zero]
      unfold logRatio
      rw [(isContinuousTreeSemimeasure_cantorMass μ).1, ha.1]
      norm_num
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, prefixExpectation_stepKL_eq_sub μ ha hac N]
      ring

/-- If `c · μ ≤ a` with `c > 0`, the expected log-likelihood ratio at every level is at most
`ln(1/c)`. Item SOL-K-LRBOUND; Hutter (2005) §3.2 (`D_n ≤ ln w_μ^{-1}`). -/
theorem prefixExpectation_logRatio_le (μ : Measure CantorSeq) [IsProbabilityMeasure μ]
    {a : BitString → ℝ≥0∞} (ha : IsContinuousTreeSemimeasure a) {c : ℝ} (hc : 0 < c)
    (hdom : ∀ x, ENNReal.ofReal c * cantorMass μ x ≤ a x) (N : ℕ) :
    prefixExpectation μ N (logRatio μ a) ≤ Real.log c⁻¹ := by
  apply prefixExpectation_le_const
  intro x hx
  unfold logRatio
  have H1 : ENNReal.ofReal c * cantorMass μ x ≤ a x := hdom x
  have H2 : c * (cantorMass μ x).toReal ≤ (a x).toReal := by
    have H_eq : (ENNReal.ofReal c * cantorMass μ x).toReal = c * (cantorMass μ x).toReal := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (le_of_lt hc)]
    have H_mono : (ENNReal.ofReal c * cantorMass μ x).toReal ≤ (a x).toReal := by
      apply ENNReal.toReal_mono
      · exact IsContinuousTreeSemimeasure.ne_top ha x
      · exact H1
    rwa [H_eq] at H_mono
  have Hu : 0 < (cantorMass μ x).toReal := ENNReal.toReal_pos hx (measure_ne_top μ _)
  have Hv : 0 < (a x).toReal := by
    nlinarith
  have H_log : Real.log ((cantorMass μ x).toReal / (a x).toReal) ≤ Real.log c⁻¹ := by
    have H_div : (cantorMass μ x).toReal / (a x).toReal ≤ c⁻¹ := by
      rw [inv_eq_one_div, div_le_iff₀ Hv, div_mul_eq_mul_div, one_mul, le_div_iff₀ hc, mul_comm]
      exact H2
    apply Real.log_le_log _ H_div
    exact div_pos Hu Hv
  exact H_log

/-- **KL-TOTAL.** If the continuous tree semimeasure `a` dominates the probability measure `μ`
with constant `c > 0` (`c · μ ≤ a`), then at every horizon `N` the total expected one-step
divergence is at most `ln(1/c)`:
`Σ_{n<N} E_{x ∼ μ, |x| = n} KL(μ(· | x) ‖ a(· | x)) ≤ ln(1/c)`. Item SOL-K-TOTAL (target
KL-TOTAL, for any dominating semimeasure; `a = M` in `solomonoff_tsum_stepKL_le_log`);
Hutter (2005) Theorem 3.19 (`D_∞ ≤ ln w_μ^{-1}`), Li–Vitányi (3rd ed.) §5.2. -/
theorem sum_prefixExpectation_stepKL_le (μ : Measure CantorSeq) [IsProbabilityMeasure μ]
    {a : BitString → ℝ≥0∞} (ha : IsContinuousTreeSemimeasure a) {c : ℝ} (hc : 0 < c)
    (hdom : ∀ x, ENNReal.ofReal c * cantorMass μ x ≤ a x) (N : ℕ) :
    ∑ n ∈ Finset.range N, prefixExpectation μ n (stepKL μ a) ≤ Real.log c⁻¹ := by
  rw [sum_prefixExpectation_stepKL_eq μ ha]
  · apply prefixExpectation_logRatio_le μ ha hc hdom
  · intro y hy
    have h1 : ENNReal.ofReal c * cantorMass μ y ≤ a y := hdom y
    have h_pos1 : 0 < ENNReal.ofReal c := ENNReal.ofReal_pos.mpr hc
    have h_pos : 0 < ENNReal.ofReal c * cantorMass μ y := by
      exact ENNReal.mul_pos h_pos1.ne' hy
    intro ha_eq
    rw [ha_eq] at h1
    exact not_le_of_gt h_pos h1

end Kolmogorov
