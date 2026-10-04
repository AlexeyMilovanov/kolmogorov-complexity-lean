/-
Copyright (c) 2024 Author Name. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Author Name
-/
import KolmogorovMathlib.StoppingComplexity.Universal
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Mass depth and the stopping gap

The two real quantities of the stopping-complexity separation (blueprint 01 F5, 03 §8, 04
integer-ceiling-shift): the *mass depth* `m(z) = -log₂ M_stop(z)` of a string and the *stopping gap*
`g(z) = K_stop(z) - m(z)`, together with the foundational facts `0 ≤ m ≤ K_stop`, `g ≥ 0`, the
forward ceiling inequality `m ≤ n + a → ⌈m⌉ ≤ n + a`, the bounded-shift step of the
integer-ceiling-shift lemma, and the transfer lemma of blueprint 03 §8 that turns the raw witness
inequality (RAW) into an excess of the gap over the discount `f(⌈m⌉)`.

Real logarithms enter the development here for the first time: everything before this module is
stated in `ℕ`, `ℚ`, `ℕ∞` or `ℝ≥0∞`. `massDepth` is defined after positivity, finiteness and the
bound by one of `univStopProb` (blueprint F5), so that the logarithm has a positive argument.
-/

namespace Kolmogorov

open scoped ENNReal

/-- The mass depth `m(z) = -log₂ M_stop(z)` of a string `z` under the fixed universal stopping
machine, a real number (finite and nonnegative by `massDepth_nonneg` and the F5 facts).
Blueprint 01 F5 / F0 (`m(z) = -log_2 M(z)`). -/
noncomputable def massDepth (z : BitString) : ℝ :=
  -Real.logb 2 (univStopProb z).toReal

/-- The stopping gap `g(z) = K_stop(z) - m(z)`, with `K_stop` read through its `ℕ` shadow
`univStopComplexityNat` (legitimate because `univStopComplexity z ≠ ⊤`).
Blueprint 01 F5 / F0 (`g(z) = K_s(z) - m(z)`). -/
noncomputable def stoppingGap (z : BitString) : ℝ :=
  (univStopComplexityNat z : ℝ) - massDepth z

/-- The mass depth is nonnegative, because `M_stop(z) ≤ 1` (time-semimeasure bound).
Blueprint 01 F5 (`0 ≤ m(x)`). -/
theorem massDepth_nonneg (z : BitString) : 0 ≤ massDepth z := by
  have hle : (univStopProb z).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top (univStopProb_le_one z)
  have h := Real.logb_nonpos (b := 2) (by norm_num) ENNReal.toReal_nonneg hle
  unfold massDepth
  linarith

/-- A lower bound `2^{-k} ≤ M_stop(z)` on the stopping probability bounds the mass depth,
`m(z) ≤ k`: apply the increasing `log₂` to the real bound `2^{-k} ≤ M_stop(z).toReal`. -/
private theorem massDepth_le_of_half_pow_le {z : BitString} {k : ℕ}
    (h : (2 : ℝ≥0∞)⁻¹ ^ k ≤ univStopProb z) : massDepth z ≤ k := by
  have hne : univStopProb z ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (univStopProb_le_one z)
  have hr : (1 / 2 : ℝ) ^ k ≤ (univStopProb z).toReal := by
    simpa [ENNReal.toReal_pow, ENNReal.toReal_inv] using ENNReal.toReal_mono hne h
  have hlog := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) hr
  rw [Real.logb_pow, one_div, Real.logb_inv, Real.logb_self_eq_one (by norm_num)] at hlog
  unfold massDepth
  linarith

/-- The mass depth is at most the stopping complexity: a shortest witness contributes its weight
`2^{-K_stop(z)}` to `M_stop(z)`. Blueprint 01 F5 (`m(x) ≤ K_s(x)`). -/
theorem massDepth_le_univStopComplexityNat (z : BitString) :
    massDepth z ≤ univStopComplexityNat z :=
  massDepth_le_of_half_pow_le (two_pow_neg_univStopComplexityNat_le z)

/-- The stopping gap is nonnegative. Blueprint 01 F5 (`g(x) ≥ 0`). -/
theorem stoppingGap_nonneg (z : BitString) : 0 ≤ stoppingGap z := by
  have h := massDepth_le_univStopComplexityNat z
  unfold stoppingGap
  linarith

/-- A lower bound `2^{-(n+a)} ≤ M_stop(z)` on the stopping probability is an upper bound
`m(z) ≤ n + a` on the mass depth; this is how the second half of (RAW) is read.
Blueprint 01 F5 (`M(z) ≥ 2^{-(n+a)}` gives `m(z) ≤ n + a`). -/
theorem massDepth_le_of_two_pow_neg_le {z : BitString} {n a : ℕ}
    (h : (2 : ℝ≥0∞)⁻¹ ^ (n + a) ≤ univStopProb z) : massDepth z ≤ n + a := by
  exact_mod_cast massDepth_le_of_half_pow_le h

/-- The stopping probability is at least `2^{-⌈m(z)⌉}`: the mass depth rounded up still bounds the
probability from below. Used by the level-colouring upper bound (`z ∈ T_{⌈m⌉+1}`).
Blueprint 03 Lemma U3 (`M_stop(z) ≥ 2^{-k}` for `k = ⌈m(z)⌉`). -/
theorem two_pow_neg_ceil_le (z : BitString) :
    (2 : ℝ≥0∞)⁻¹ ^ ⌈massDepth z⌉₊ ≤ univStopProb z := by
  have hne : univStopProb z ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (univStopProb_le_one z)
  have hx : 0 < (univStopProb z).toReal := ENNReal.toReal_pos (univStopProb_pos z).ne' hne
  have hceil : massDepth z ≤ ⌈massDepth z⌉₊ := Nat.le_ceil _
  have hreal : (1 / 2 : ℝ) ^ ⌈massDepth z⌉₊ ≤ (univStopProb z).toReal := by
    rw [← Real.logb_le_logb (b := 2) (by norm_num) (by positivity) hx, Real.logb_pow, one_div,
      Real.logb_inv, Real.logb_self_eq_one (by norm_num)]
    have hm : massDepth z = -Real.logb 2 (univStopProb z).toReal := rfl
    linarith
  rw [← ENNReal.toReal_le_toReal (by simp) hne]
  simpa [ENNReal.toReal_pow, ENNReal.toReal_inv] using hreal

/-- Forward ceiling inequality: a nonnegative real bounded by the natural number `n + a` has its
ceiling bounded by `n + a`. Stated with `n + a` directly, never with `⌈m⌉ - a`.
Blueprint 01 F5 and 04 Lemma integer-ceiling-shift, first half (`⌈m⌉ ≤ n + a`). -/
theorem natCeil_le_of_le_natCast {m : ℝ} {n a : ℕ} (h0 : 0 ≤ m) (h : m ≤ n + a) :
    ⌈m⌉₊ ≤ n + a := by
  have h1 : (⌈m⌉₊ : ℝ) < (n + a : ℕ) + 1 := by
    push_cast
    linarith [Nat.ceil_lt_add_one h0]
  exact Nat.lt_add_one_iff.mp (by exact_mod_cast h1)

/-- Second half of the integer-ceiling-shift lemma: for a nondecreasing `f` with the bounded-shift
property `f (n + a) ≤ f n + D` and a nonnegative real `m ≤ n + a`, one has `f ⌈m⌉₊ ≤ f n + D`.
Blueprint 04 Lemma integer-ceiling-shift (CS), second inequality. -/
theorem discount_natCeil_le_of_shift {f : ℕ → ℕ} (hmono : Monotone f) {m : ℝ} {n a D : ℕ}
    (hD : ∀ n, f (n + a) ≤ f n + D) (h0 : 0 ≤ m) (h : m ≤ n + a) : f ⌈m⌉₊ ≤ f n + D :=
  (hmono (natCeil_le_of_le_natCast h0 h)).trans (hD n)

/-- Transfer, first step: the raw witness inequalities `K_stop(z) > n + f(n) + c` and
`M_stop(z) ≥ 2^{-(n+a)}` give the gap excess `g(z) > f(n) + c - a`, as a real inequality.
Blueprint 03 §8 transfer (`gap(z_c) > f(n_c) + c - a`). -/
theorem stoppingGap_gt_of_raw {f : ℕ → ℕ} {z : BitString} {n c a : ℕ}
    (hK : (n + f n + c : ℕ∞) < univStopComplexity z)
    (hM : (2 : ℝ≥0∞)⁻¹ ^ (n + a) ≤ univStopProb z) : (f n : ℝ) + c - a < stoppingGap z := by
  rw [← univStopComplexityNat_eq_coe] at hK
  have hK' : ((n + f n + c : ℕ) : ℝ) < univStopComplexityNat z := by exact_mod_cast hK
  have hm := massDepth_le_of_two_pow_neg_le hM
  unfold stoppingGap
  push_cast at hK'
  linarith

/-- Transfer, second step: for a nondecreasing `f` with the bounded-shift constant `D` for the shift
`a`, the raw witness inequalities give the excess of the gap over the discount at the rounded mass
depth, `g(z) > f(⌈m(z)⌉) + c - a - D`. No expression `f(⌈m⌉ - a)` is used.
Blueprint 03 §8 transfer (`gap(z_c) > f(k_c) + c - a - B_a`, `k_c = ⌈m(z_c)⌉`). -/
theorem stoppingGap_gt_discount_ceil {f : ℕ → ℕ} (hmono : Monotone f) {z : BitString}
    {n c a D : ℕ} (hD : ∀ n, f (n + a) ≤ f n + D)
    (hK : (n + f n + c : ℕ∞) < univStopComplexity z)
    (hM : (2 : ℝ≥0∞)⁻¹ ^ (n + a) ≤ univStopProb z) :
    (f ⌈massDepth z⌉₊ : ℝ) + c - a - D < stoppingGap z := by
  have h1 := stoppingGap_gt_of_raw hK hM
  have h2 := discount_natCeil_le_of_shift hmono hD (massDepth_nonneg z)
    (massDepth_le_of_two_pow_neg_le hM)
  have h3 : (f ⌈massDepth z⌉₊ : ℝ) ≤ f n + D := by exact_mod_cast h2
  linarith

end Kolmogorov
