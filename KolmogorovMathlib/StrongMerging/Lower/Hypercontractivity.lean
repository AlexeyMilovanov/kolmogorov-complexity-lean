import KolmogorovMathlib.StrongMerging.Basic
import KolmogorovMathlib.Restricted.Examples.HammingBalls.Part01
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.MeanInequalities
import Mathlib.InformationTheory.Hamming

/-!
# Hypercontractivity and small-set expansion on the Boolean cube

Blueprint node L11 (`cubeSmallSetExpansion`) of the formalization of `sublinear-merging.tex`
(appendix "Finite geometry and analytical obligations", tex lines 4512-4583; main text
`lem:ham-hypercontractive-distance`, lines 1848-1890; O'Donnell, *Analysis of Boolean
Functions*, §9.5).  The proof follows the blueprint's sub-DAG:

1. `twoPointHypercontractive`: `a² + ρ² b² ≤ ((|a+b|^p + |a-b|^p)/2)^(2/p)` for `1 ≤ p ≤ 2`,
   `ρ² ≤ p - 1`;
2. `mixedNormSwap`: `‖g‖_{L²_t L^p_s} ≤ ‖g‖_{L^p_s L²_t}` (Minkowski), stated squared;
3. `cubeHypercontractive`: `‖T_ρ f‖₂ ≤ ‖f‖_p` on `{0,1}^n` by induction on `n`, stated squared;
4. `noiseSemigroup`, `noiseSelfAdjoint`: `T_α T_β = T_{αβ}` and `⟨f, T_ρ g⟩ = ⟨T_ρ f, g⟩`;
5. `indicatorNoiseBound`: `⟨1_U, T_γ 1_U⟩ = ‖T_√γ 1_U‖₂² ≤ μ^(2/(1+γ))`;

and finally, with `γ = 1 - 2q`, the small-set expansion bound
`Pr[Y ∈ U | X uniform in U] ≤ μ^(q/(1-q))`, `μ = |U| / 2^M`, for `Y` obtained from `X` by
flipping each bit independently with probability `q ∈ [0, 1/2]`
(`cubeSmallSetExpansion_fin` on `Fin n → Bool`, transported to length-`M` bit strings in
`cubeSmallSetExpansion`).  All expectations are normalized finite averages `unifAvg`.  The
noise operator is defined directly by its kernel; the definitions are independent of the Fourier
development in `Complexitylib.BooleanAnalysis.FourierExpansion`.
-/

namespace Kolmogorov.StrongMerging.Lower

open Finset

/-! ### Uniform averages -/

/-- The uniform average `E F = (∑_a F a) / |α|` of a real function on a finite type. -/
noncomputable def unifAvg {α : Type*} [Fintype α] (F : α → ℝ) : ℝ :=
  (∑ a, F a) / Fintype.card α

/-- Averages are monotone. -/
theorem unifAvg_mono {α : Type*} [Fintype α] {F G : α → ℝ} (h : ∀ a, F a ≤ G a) :
    unifAvg F ≤ unifAvg G :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum fun a _ => h a) (Nat.cast_nonneg _)

/-- Averages of nonnegative functions are nonnegative. -/
theorem unifAvg_nonneg {α : Type*} [Fintype α] {F : α → ℝ} (h : ∀ a, 0 ≤ F a) :
    0 ≤ unifAvg F :=
  div_nonneg (Finset.sum_nonneg fun a _ => h a) (Nat.cast_nonneg _)

/-- **Fubini for uniform averages.**

Proof sketch: unfold `unifAvg`; `Finset.sum_div`, `Finset.sum_comm`, and
`div_div`/`mul_comm` for the two normalizations.
Reference: tex 4530-4540 (mixed norms, finite probability spaces); node L11.  [leaf: easy] -/
theorem unifAvg_comm {α β : Type*} [Fintype α] [Fintype β] (G : α → β → ℝ) :
    unifAvg (fun a => unifAvg (fun b => G a b)) = unifAvg (fun b => unifAvg (fun a => G a b)) := by
  simp only [unifAvg, ← Finset.sum_div]
  rw [Finset.sum_comm]
  ring

/-! ### The noise operator -/

/-- The one-bit noise weight: a bit is kept with probability `(1 + ρ) / 2` and flipped with
probability `(1 - ρ) / 2`. -/
noncomputable def noiseWeight (ρ : ℝ) (b c : Bool) : ℝ :=
  if b = c then (1 + ρ) / 2 else (1 - ρ) / 2

/-- The noise kernel on `{0,1}^n`: independent one-bit noise on every coordinate. -/
noncomputable def noiseKernel (n : ℕ) (ρ : ℝ) (x y : Fin n → Bool) : ℝ :=
  ∏ i, noiseWeight ρ (x i) (y i)

/-- The noise operator `T_ρ f (x) = E[f(y)]`, `y` obtained from `x` by flipping each bit
independently with probability `(1 - ρ) / 2`. -/
noncomputable def noiseOp (n : ℕ) (ρ : ℝ) (f : (Fin n → Bool) → ℝ) (x : Fin n → Bool) : ℝ :=
  ∑ y, noiseKernel n ρ x y * f y

/-- The one-dimensional noise operator on functions of one bit. -/
noncomputable def noiseOp1 (ρ : ℝ) (φ : Bool → ℝ) (t : Bool) : ℝ :=
  ∑ s, noiseWeight ρ t s * φ s

/-- `consBit t x` prepends the bit `t` to `x ∈ {0,1}^n`. -/
def consBit {n : ℕ} (t : Bool) (x : Fin n → Bool) : Fin (n + 1) → Bool :=
  Fin.cons t x

/-- The restriction `y ↦ f (t, y)` of a function on `{0,1}^(n+1)` to the face `x₀ = t`. -/
def restrictBit {n : ℕ} (f : (Fin (n + 1) → Bool) → ℝ) (t : Bool) : (Fin n → Bool) → ℝ :=
  fun y => f (consBit t y)

/-! ### Step 1: the two-point inequality -/

/-- **Nonnegativity from a nonnegative derivative**: a function continuous on `[a, b]`, with
derivative `f' ≥ 0` on `(a, b)` and `f a = 0`, is nonnegative on `[a, b]`. -/
theorem nonneg_of_hasDerivAt_nonneg {f f' : ℝ → ℝ} {a b : ℝ}
    (hcont : ContinuousOn f (Set.Icc a b))
    (hderiv : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Set.Ioo a b, 0 ≤ f' x) (hfa : f a = 0) :
    ∀ x ∈ Set.Icc a b, 0 ≤ f x := by
  intro x hx
  have hmono := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b) hcont
    (fun y hy => by
      rw [interior_Icc] at hy ⊢
      exact (hderiv y hy).hasDerivWithinAt)
    (fun y hy => by
      rw [interior_Icc] at hy
      exact hf' y hy)
  have := hmono ⟨le_refl a, hx.1.trans hx.2⟩ hx hx.1
  rwa [hfa] at this

/-- The odd gap `H_q(x) = (1 + x)^q - (1 - x)^q - 2 q x` of the two-point inequality. -/
noncomputable def twoPointOddGap (q x : ℝ) : ℝ :=
  (1 + x) ^ q - (1 - x) ^ q - 2 * q * x

/-- The even gap `G_p(x) = (1 + x)^p + (1 - x)^p - 2 - p (p - 1) x²` of the two-point
inequality. -/
noncomputable def twoPointEvenGap (p x : ℝ) : ℝ :=
  (1 + x) ^ p + (1 - x) ^ p - 2 - p * (p - 1) * x ^ 2

/-- **Symmetric convexity of a nonpositive power**: `(1 + x)^c + (1 - x)^c ≥ 2` for `c ≤ 0`
and `0 ≤ x < 1`.

Proof sketch: AM-GM, `a + b ≥ 2 √(a b)` for `a, b > 0` (`nlinarith [sq_nonneg (√a - √b)]`),
with `a b = (1 - x²)^c ≥ 1` because `0 < 1 - x² ≤ 1` and `c ≤ 0` (`Real.mul_rpow`,
`Real.one_le_rpow_of_pos_of_le_one_of_nonpos`).
Reference: tex 4519-4527 (`twoPointHypercontractive`); node L11.  [leaf: easy] -/
theorem two_le_rpow_add_rpow {c x : ℝ} (hc : c ≤ 0) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    2 ≤ (1 + x) ^ c + (1 - x) ^ c := by
  have ha : 0 < (1 + x) ^ c := Real.rpow_pos_of_pos (by linarith) c
  have hb : 0 < (1 - x) ^ c := Real.rpow_pos_of_pos (by linarith) c
  have hab : 1 ≤ (1 + x) ^ c * (1 - x) ^ c := by
    rw [← Real.mul_rpow (by linarith) (by linarith)]
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos (by nlinarith) (by nlinarith) hc
  nlinarith [sq_nonneg ((1 + x) ^ c - (1 - x) ^ c)]

/-- The odd gap is continuous on `[0, 1]` for `q ≥ 0`.

Proof sketch: `ContinuousOn.sub`/`.mul`; `(1 + x)^q` has a positive base
(`Real.continuousAt_rpow_const`), and `(1 - x)^q` is continuous for `q > 0` at every base and
constant `1` for `q = 0` (`Real.rpow_zero`); split `q = 0 ∨ 0 < q`.
Reference: tex 4519-4527; node L11.  [leaf: easy] -/
theorem continuousOn_twoPointOddGap {q : ℝ} (hq : 0 ≤ q) :
    ContinuousOn (twoPointOddGap q) (Set.Icc 0 1) := by
  have h1 : Continuous fun x : ℝ => (1 + x) ^ q :=
    (continuous_const.add continuous_id).rpow_const fun _ => Or.inr hq
  have h2 : Continuous fun x : ℝ => (1 - x) ^ q :=
    (continuous_const.sub continuous_id).rpow_const fun _ => Or.inr hq
  exact ((h1.sub h2).sub (continuous_const.mul continuous_id)).continuousOn

/-- The derivative of the odd gap on `(-1, 1)`:
`H_q'(x) = q (1 + x)^(q-1) + q (1 - x)^(q-1) - 2 q`.

Proof sketch: `Real.hasDerivAt_rpow_const` (positive bases `1 ± x`) composed with
`hasDerivAt_id`, `HasDerivAt.const_sub`, `HasDerivAt.sub`, `HasDerivAt.const_mul`; `ring`.
Reference: tex 4519-4527; node L11.  [leaf: easy] -/
theorem hasDerivAt_twoPointOddGap (q : ℝ) {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt (twoPointOddGap q)
      (q * (1 + x) ^ (q - 1) + q * (1 - x) ^ (q - 1) - 2 * q) x := by
  have h1 : HasDerivAt (fun y : ℝ => (1 + y) ^ q) (1 * q * (1 + x) ^ (q - 1)) x :=
    ((hasDerivAt_id' x).const_add 1).rpow_const (Or.inl (by linarith [hx.1]))
  have h2 : HasDerivAt (fun y : ℝ => (1 - y) ^ q) (-1 * q * (1 - x) ^ (q - 1)) x :=
    ((hasDerivAt_id' x).const_sub 1).rpow_const (Or.inl (by linarith [hx.2]))
  have h3 : HasDerivAt (fun y : ℝ => 2 * q * y) (2 * q * 1) x :=
    (hasDerivAt_id' x).const_mul (2 * q)
  have h := (h1.sub h2).sub h3
  rw [show q * (1 + x) ^ (q - 1) + q * (1 - x) ^ (q - 1) - 2 * q =
    1 * q * (1 + x) ^ (q - 1) - -1 * q * (1 - x) ^ (q - 1) - 2 * q * 1 by ring]
  exact h

/-- `H_q(x) ≥ 0` on `[0, 1]` for `0 ≤ q ≤ 1`: its derivative is
`q ((1 + x)^(q-1) + (1 - x)^(q-1) - 2) ≥ 0` and `H_q(0) = 0`. -/
theorem twoPointOddGap_nonneg {q x : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ twoPointOddGap q x := by
  refine nonneg_of_hasDerivAt_nonneg (continuousOn_twoPointOddGap hq0)
    (fun y hy => hasDerivAt_twoPointOddGap q ⟨by linarith [hy.1], hy.2⟩) (fun y hy => ?_) ?_ x hx
  · have h2 := two_le_rpow_add_rpow (c := q - 1) (by linarith) hy.1.le hy.2
    nlinarith [mul_le_mul_of_nonneg_left h2 hq0]
  · norm_num [twoPointOddGap]

/-- The even gap is continuous on `[0, 1]` for `p ≥ 0`.

Proof sketch: as `continuousOn_twoPointOddGap`, plus the polynomial term (`continuousOn_pow`).
Reference: tex 4519-4527; node L11.  [leaf: easy] -/
theorem continuousOn_twoPointEvenGap {p : ℝ} (hp : 0 ≤ p) :
    ContinuousOn (twoPointEvenGap p) (Set.Icc 0 1) := by
  have h1 : Continuous fun x : ℝ => (1 + x) ^ p :=
    (continuous_const.add continuous_id).rpow_const fun _ => Or.inr hp
  have h2 : Continuous fun x : ℝ => (1 - x) ^ p :=
    (continuous_const.sub continuous_id).rpow_const fun _ => Or.inr hp
  exact (((h1.add h2).sub continuous_const).sub
    (continuous_const.mul (continuous_pow 2))).continuousOn

/-- The derivative of the even gap on `(-1, 1)`:
`G_p'(x) = p (1 + x)^(p-1) - p (1 - x)^(p-1) - 2 p (p - 1) x`.

Proof sketch: `Real.hasDerivAt_rpow_const` on the positive bases `1 ± x`, `hasDerivAt_pow`,
`HasDerivAt.add`/`.sub`/`.const_mul`; `ring`.
Reference: tex 4519-4527; node L11.  [leaf: easy] -/
theorem hasDerivAt_twoPointEvenGap (p : ℝ) {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt (twoPointEvenGap p)
      (p * (1 + x) ^ (p - 1) - p * (1 - x) ^ (p - 1) - 2 * p * (p - 1) * x) x := by
  have h1 : HasDerivAt (fun y : ℝ => (1 + y) ^ p) (1 * p * (1 + x) ^ (p - 1)) x :=
    ((hasDerivAt_id' x).const_add 1).rpow_const (Or.inl (by linarith [hx.1]))
  have h2 : HasDerivAt (fun y : ℝ => (1 - y) ^ p) (-1 * p * (1 - x) ^ (p - 1)) x :=
    ((hasDerivAt_id' x).const_sub 1).rpow_const (Or.inl (by linarith [hx.2]))
  have h3 : HasDerivAt (fun y : ℝ => p * (p - 1) * y ^ 2)
      (p * (p - 1) * ((2 : ℕ) * x ^ (2 - 1))) x :=
    (hasDerivAt_pow 2 x).const_mul (p * (p - 1))
  have h := ((h1.add h2).sub_const 2).sub h3
  rw [show p * (1 + x) ^ (p - 1) - p * (1 - x) ^ (p - 1) - 2 * p * (p - 1) * x =
    1 * p * (1 + x) ^ (p - 1) + -1 * p * (1 - x) ^ (p - 1) -
      p * (p - 1) * ((2 : ℕ) * x ^ (2 - 1)) by push_cast; ring]
  exact h

/-- `G_p(x) ≥ 0` on `[0, 1]` for `1 ≤ p ≤ 2`: its derivative is `p H_{p-1}(x) ≥ 0` and
`G_p(0) = 0`. -/
theorem twoPointEvenGap_nonneg {p x : ℝ} (hp1 : 1 ≤ p) (hp2 : p ≤ 2)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ twoPointEvenGap p x := by
  refine nonneg_of_hasDerivAt_nonneg (continuousOn_twoPointEvenGap (by linarith))
    (fun y hy => hasDerivAt_twoPointEvenGap p ⟨by linarith [hy.1], hy.2⟩) (fun y hy => ?_) ?_ x hx
  · have h := twoPointOddGap_nonneg (q := p - 1) (by linarith) (by linarith) ⟨hy.1.le, hy.2.le⟩
    unfold twoPointOddGap at h
    have hp0 : 0 ≤ p := by linarith
    nlinarith [mul_nonneg hp0 h]
  · norm_num [twoPointEvenGap]

/-- **Taylor lower bound for the two-point norm**: for `1 ≤ p ≤ 2` and `0 ≤ x ≤ 1`,
`((1 + x)^p + (1 - x)^p) / 2 ≥ 1 + p (p - 1) x² / 2` (the binomial series of the left side has
nonnegative coefficients); this is `twoPointEvenGap_nonneg`. -/
theorem twoPoint_taylor {p x : ℝ} (hp1 : 1 ≤ p) (hp2 : p ≤ 2) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    1 + p * (p - 1) / 2 * x ^ 2 ≤ ((1 + x) ^ p + (1 - x) ^ p) / 2 := by
  have h := twoPointEvenGap_nonneg hp1 hp2 ⟨hx0, hx1⟩
  unfold twoPointEvenGap at h
  linarith

/-- **Normalized two-point inequality**: `1 + (p - 1) x² ≤ (((1+x)^p + (1-x)^p)/2)^(2/p)` for
`1 ≤ p ≤ 2`, `0 ≤ x ≤ 1`; from `twoPoint_taylor` and Bernoulli's inequality with exponent
`2 / p ≥ 1`. -/
theorem twoPoint_normalized {p x : ℝ} (hp1 : 1 ≤ p) (hp2 : p ≤ 2) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    1 + (p - 1) * x ^ 2 ≤ (((1 + x) ^ p + (1 - x) ^ p) / 2) ^ (2 / p) := by
  have hp0 : 0 < p := by linarith
  have hpne : p ≠ 0 := hp0.ne'
  have hy : 0 ≤ p * (p - 1) / 2 * x ^ 2 := by
    have : 0 ≤ p - 1 := by linarith
    positivity
  have h1 := twoPoint_taylor hp1 hp2 hx0 hx1
  have hexp : 1 ≤ 2 / p := by rw [le_div_iff₀ hp0]; linarith
  calc 1 + (p - 1) * x ^ 2 = 1 + 2 / p * (p * (p - 1) / 2 * x ^ 2) := by field_simp
    _ ≤ (1 + p * (p - 1) / 2 * x ^ 2) ^ (2 / p) :=
        one_add_mul_self_le_rpow_one_add (by linarith) hexp
    _ ≤ (((1 + x) ^ p + (1 - x) ^ p) / 2) ^ (2 / p) :=
        Real.rpow_le_rpow (by linarith) h1 (by linarith)

/-- **Homogeneity of the two-point norm**: for `a ≠ 0` and `|b| ≤ |a|`, with
`x = |b| / |a| ∈ [0, 1]`: `|a + b|^p + |a - b|^p = |a|^p ((1 + x)^p + (1 - x)^p)`.

Proof sketch: `{|a + b|, |a - b|} = {|a| (1 + x), |a| (1 - x)}`: if `a` and `b` have the same
sign then `|a + b| = |a| + |b|` and `|a - b| = |a| - |b|`, otherwise the roles are swapped
(case analysis on the signs, `abs_of_nonneg`/`abs_of_nonpos`, `field_simp`); then
`Real.mul_rpow` (`|a| ≥ 0`, `1 ± x ≥ 0`) and `add_comm`.
Reference: tex 4519-4527 (`twoPointHypercontractive`, "the sign of `b`"); node L11.
[leaf: medium] -/
theorem abs_add_rpow_add_abs_sub_rpow {a b : ℝ} (p : ℝ) (ha : a ≠ 0) (hab : |b| ≤ |a|) :
    |a + b| ^ p + |a - b| ^ p = |a| ^ p * ((1 + |b| / |a|) ^ p + (1 - |b| / |a|) ^ p) := by
  have haa : 0 < |a| := abs_pos.mpr ha
  have hx0 : 0 ≤ |b| / |a| := div_nonneg (abs_nonneg b) haa.le
  have hx1 : |b| / |a| ≤ 1 := (div_le_one haa).mpr hab
  have h1 : 0 ≤ 1 + |b| / |a| := by linarith
  have h2 : 0 ≤ 1 - |b| / |a| := by linarith
  have hplus : |a| * (1 + |b| / |a|) = |a| + |b| := by field_simp
  have hminus : |a| * (1 - |b| / |a|) = |a| - |b| := by field_simp
  rw [mul_add, ← Real.mul_rpow haa.le h1, ← Real.mul_rpow haa.le h2, hplus, hminus]
  have hpair : (|a + b| = |a| + |b| ∧ |a - b| = |a| - |b|) ∨
      (|a + b| = |a| - |b| ∧ |a - b| = |a| + |b|) := by
    rcases le_total 0 a with ha0 | ha0 <;> rcases le_total 0 b with hb0 | hb0
    · rw [abs_of_nonneg ha0, abs_of_nonneg hb0] at hab ⊢
      left
      rw [abs_of_nonneg (by linarith : 0 ≤ a + b), abs_of_nonneg (by linarith : 0 ≤ a - b)]
      exact ⟨rfl, rfl⟩
    · rw [abs_of_nonneg ha0, abs_of_nonpos hb0] at hab ⊢
      right
      rw [abs_of_nonneg (by linarith : 0 ≤ a + b), abs_of_nonneg (by linarith : 0 ≤ a - b)]
      constructor <;> ring
    · rw [abs_of_nonpos ha0, abs_of_nonneg hb0] at hab ⊢
      right
      rw [abs_of_nonpos (by linarith : a + b ≤ 0), abs_of_nonpos (by linarith : a - b ≤ 0)]
      constructor <;> ring
    · rw [abs_of_nonpos ha0, abs_of_nonpos hb0] at hab ⊢
      left
      rw [abs_of_nonpos (by linarith : a + b ≤ 0), abs_of_nonpos (by linarith : a - b ≤ 0)]
      constructor <;> ring
  rcases hpair with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rw [e1, e2]
  · rw [e1, e2, add_comm]

/-- **From `p`-th powers back to squares**: `(|a|^p N)^(2/p) = a² N^(2/p)` for `N ≥ 0`,
`p > 0`.

Proof sketch: `Real.mul_rpow` (both factors nonnegative), `← Real.rpow_mul (abs_nonneg a)`,
`p * (2 / p) = 2` (`field_simp`), `Real.rpow_two`, `sq_abs`.
Reference: tex 4519-4527; node L11.  [leaf: easy] -/
theorem abs_rpow_mul_rpow_two_div {a N p : ℝ} (hN : 0 ≤ N) (hp : 0 < p) :
    (|a| ^ p * N) ^ (2 / p) = a ^ 2 * N ^ (2 / p) := by
  have hmul : p * (2 / p) = 2 := by field_simp
  rw [Real.mul_rpow (Real.rpow_nonneg (abs_nonneg a) p) hN, ← Real.rpow_mul (abs_nonneg a), hmul,
    Real.rpow_two, sq_abs]

/-- **The two-point inequality when `|b| ≤ |a|`**: scale by `|a|` and apply
`twoPoint_normalized` at `x = |b| / |a|`. -/
theorem twoPoint_of_abs_le {a b ρ p : ℝ} (hp1 : 1 ≤ p) (hp2 : p ≤ 2) (hρ : ρ ^ 2 ≤ p - 1)
    (hab : |b| ≤ |a|) :
    a ^ 2 + ρ ^ 2 * b ^ 2 ≤ ((|a + b| ^ p + |a - b| ^ p) / 2) ^ (2 / p) := by
  have hp0 : 0 < p := by linarith
  rcases eq_or_ne a 0 with rfl | ha
  · have hb : b = 0 := by simpa using hab
    subst hb
    have h0p : (0 : ℝ) ^ p = 0 := Real.zero_rpow hp0.ne'
    simp only [add_zero, sub_zero, abs_zero, h0p, zero_div]
    rw [Real.zero_rpow (div_pos two_pos hp0).ne']
    norm_num
  · have haa : 0 < |a| := abs_pos.mpr ha
    obtain ⟨x, hx⟩ : ∃ x, x = |b| / |a| := ⟨_, rfl⟩
    have hx0 : 0 ≤ x := hx ▸ div_nonneg (abs_nonneg b) haa.le
    have hx1 : x ≤ 1 := hx ▸ (div_le_one haa).mpr hab
    have hN0 : 0 ≤ ((1 + x) ^ p + (1 - x) ^ p) / 2 := by
      have h1 : 0 ≤ (1 + x) ^ p := Real.rpow_nonneg (by linarith) _
      have h2 : 0 ≤ (1 - x) ^ p := Real.rpow_nonneg (by linarith) _
      linarith
    have hnorm := twoPoint_normalized hp1 hp2 hx0 hx1
    have hbx : b ^ 2 = a ^ 2 * x ^ 2 := by
      rw [hx, div_pow, sq_abs, sq_abs, mul_div_assoc', mul_div_cancel_left₀ _ (pow_ne_zero 2 ha)]
    rw [abs_add_rpow_add_abs_sub_rpow p ha hab, ← hx, mul_div_assoc,
      abs_rpow_mul_rpow_two_div hN0 hp0]
    calc a ^ 2 + ρ ^ 2 * b ^ 2 = a ^ 2 * (1 + ρ ^ 2 * x ^ 2) := by rw [hbx]; ring
      _ ≤ a ^ 2 * (1 + (p - 1) * x ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg a)
          nlinarith [sq_nonneg x]
      _ ≤ a ^ 2 * (((1 + x) ^ p + (1 - x) ^ p) / 2) ^ (2 / p) :=
          mul_le_mul_of_nonneg_left hnorm (sq_nonneg a)

/-- **Two-point hypercontractive inequality** (blueprint sub-node `twoPointHypercontractive`).
For real `a, b, ρ` and `1 ≤ p ≤ 2` with `ρ² ≤ p - 1`:
`a² + ρ² b² ≤ ((|a + b|^p + |a - b|^p) / 2)^(2/p)`. -/
theorem twoPointHypercontractive {a b ρ p : ℝ} (hp1 : 1 ≤ p) (hp2 : p ≤ 2)
    (hρ : ρ ^ 2 ≤ p - 1) :
    a ^ 2 + ρ ^ 2 * b ^ 2 ≤ ((|a + b| ^ p + |a - b| ^ p) / 2) ^ (2 / p) := by
  rcases le_total |b| |a| with hab | hba
  · exact twoPoint_of_abs_le hp1 hp2 hρ hab
  · have h := twoPoint_of_abs_le (a := b) (b := a) hp1 hp2 hρ hba
    have hρ1 : ρ ^ 2 ≤ 1 := by linarith
    have hsq : a ^ 2 ≤ b ^ 2 := sq_le_sq.mpr hba
    rw [add_comm b a, abs_sub_comm b a] at h
    calc a ^ 2 + ρ ^ 2 * b ^ 2 ≤ b ^ 2 + ρ ^ 2 * a ^ 2 := by
          nlinarith [mul_nonneg (sub_nonneg.2 hρ1) (sub_nonneg.2 hsq)]
      _ ≤ _ := h

/-- **The one-bit noise in coordinates**: with `a = (φ true + φ false)/2` and
`b = (φ true - φ false)/2`, `E_t (T_ρ φ)(t)² = a² + ρ² b²`.

Proof sketch: `unifAvg`, `Fintype.card_bool`, `Fintype.sum_bool`; `noiseOp1 ρ φ true = a + ρ b`
and `noiseOp1 ρ φ false = a - ρ b` (unfold `noiseOp1`, `noiseWeight`, `Fintype.sum_bool`);
`ring`.
Reference: tex 4519-4527, 4542-4546; node L11.  [leaf: easy] -/
theorem unifAvg_noiseOp1_sq (ρ : ℝ) (φ : Bool → ℝ) :
    unifAvg (fun t => noiseOp1 ρ φ t ^ 2) =
      ((φ true + φ false) / 2) ^ 2 + ρ ^ 2 * ((φ true - φ false) / 2) ^ 2 := by
  simp only [unifAvg, Fintype.univ_bool, noiseOp1, noiseWeight, ite_mul, mem_singleton,
    Bool.true_eq_false, not_false_eq_true, sum_insert, sum_singleton, ↓reduceIte,
    Bool.false_eq_true, Fintype.card_bool, Nat.cast_ofNat]
  ring

/-- **The `L^p` average of a function of one bit** in the coordinates `a ± b`.

Proof sketch: `unifAvg`, `Fintype.card_bool`, `Fintype.sum_bool`, and
`a + b = φ true`, `a - b = φ false` (`ring_nf`).
Reference: tex 4519-4527; node L11.  [leaf: easy] -/
theorem unifAvg_abs_rpow_bool (p : ℝ) (φ : Bool → ℝ) :
    unifAvg (fun s => |φ s| ^ p) =
      (|(φ true + φ false) / 2 + (φ true - φ false) / 2| ^ p +
        |(φ true + φ false) / 2 - (φ true - φ false) / 2| ^ p) / 2 := by
  have h1 : (φ true + φ false) / 2 + (φ true - φ false) / 2 = φ true := by ring
  have h2 : (φ true + φ false) / 2 - (φ true - φ false) / 2 = φ false := by ring
  rw [h1, h2, unifAvg, Fintype.sum_bool, Fintype.card_bool]
  norm_num

/-- **The one-dimensional hypercontractive inequality**:
`E_t (T_ρ φ)(t)² ≤ (E_s |φ s|^p)^(2/p)` for a function `φ` of one uniform bit; this is the
two-point inequality at `a = (φ true + φ false)/2`, `b = (φ true - φ false)/2`. -/
theorem noiseOp1_hypercontractive {ρ p : ℝ} (hp1 : 1 ≤ p) (hp2 : p ≤ 2) (hρ : ρ ^ 2 ≤ p - 1)
    (φ : Bool → ℝ) :
    unifAvg (fun t => noiseOp1 ρ φ t ^ 2) ≤ (unifAvg (fun s => |φ s| ^ p)) ^ (2 / p) := by
  rw [unifAvg_noiseOp1_sq, unifAvg_abs_rpow_bool]
  exact twoPointHypercontractive hp1 hp2 hρ

/-! ### Step 2: the mixed-norm swap -/

/-- Minkowski's inequality for a finite sum of nonnegative functions on a finite type. -/
private theorem minkowski_unifAvg_aux {α β : Type*} [Fintype β] {r : ℝ} (hr : 1 ≤ r)
    (F : α → β → ℝ) (hF : ∀ s t, 0 ≤ F s t) (S : Finset α) :
    (∑ t, (∑ s ∈ S, F s t) ^ r) ^ (1 / r) ≤ ∑ s ∈ S, (∑ t, F s t ^ r) ^ (1 / r) := by
  classical
  have hr0 : 0 < r := by linarith
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [Real.zero_rpow hr0.ne', Finset.sum_const_zero, Real.zero_rpow (by positivity)]
  | insert a S ha ih =>
    simp only [Finset.sum_insert ha]
    calc (∑ t, (F a t + ∑ s ∈ S, F s t) ^ r) ^ (1 / r)
        ≤ (∑ t, F a t ^ r) ^ (1 / r) + (∑ t, (∑ s ∈ S, F s t) ^ r) ^ (1 / r) :=
          Real.Lp_add_le_of_nonneg Finset.univ hr (fun t _ => hF a t)
            (fun t _ => Finset.sum_nonneg fun s _ => hF s t)
      _ ≤ _ := by linarith

/-- **Minkowski's integral inequality for uniform averages**: for `r ≥ 1` and nonnegative
`F`, `(E_t (E_s F(s,t))^r)^(1/r) ≤ E_s (E_t F(s,t)^r)^(1/r)`.

Proof sketch: the `L^r(t)` norm is a seminorm: iterate Minkowski's inequality `Real.Lp_add_le`
(or `NNReal.Lp_add_le`) over the finite sum in `s` (`Finset.induction_on`), using
homogeneity `(∑ (c F)^r)^(1/r) = c (∑ F^r)^(1/r)` for the normalizations `c = 1/|α|`,
`1/|β|` (`Real.mul_rpow`).  Empty `α` or `β`: both sides are `0` (`Real.zero_rpow`).
Reference: tex 4529-4540 (`mixedNormSwap`); node L11.  [leaf: medium] -/
theorem minkowski_unifAvg {α β : Type*} [Fintype α] [Fintype β] {r : ℝ} (hr : 1 ≤ r)
    (F : α → β → ℝ) (hF : ∀ s t, 0 ≤ F s t) :
    (unifAvg (fun t => (unifAvg (fun s => F s t)) ^ r)) ^ (1 / r) ≤
      unifAvg (fun s => (unifAvg (fun t => F s t ^ r)) ^ (1 / r)) := by
  have hr0 : 0 < r := by linarith
  have hA : (0 : ℝ) ≤ (Fintype.card α : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hB : (0 : ℝ) ≤ (Fintype.card β : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hS : ∀ t, 0 ≤ ∑ s, F s t := fun t => Finset.sum_nonneg fun s _ => hF s t
  have hT : ∀ s, 0 ≤ ∑ t, F s t ^ r := fun s =>
    Finset.sum_nonneg fun t _ => Real.rpow_nonneg (hF s t) r
  have hS1 : 0 ≤ ∑ t, (∑ s, F s t) ^ r := Finset.sum_nonneg fun t _ => Real.rpow_nonneg (hS t) r
  have hmink := minkowski_unifAvg_aux hr F hF Finset.univ
  simp only [unifAvg, div_eq_mul_inv]
  rw [show (1 : ℝ) * r⁻¹ = 1 / r by ring]
  have hL : ((∑ t, ((∑ s, F s t) * (Fintype.card α : ℝ)⁻¹) ^ r) * (Fintype.card β : ℝ)⁻¹) ^
      (1 / r) = (∑ t, (∑ s, F s t) ^ r) ^ (1 / r) * (Fintype.card α : ℝ)⁻¹ *
        (Fintype.card β : ℝ)⁻¹ ^ (1 / r) := by
    simp_rw [Real.mul_rpow (hS _) hA]
    rw [← Finset.sum_mul, Real.mul_rpow (mul_nonneg hS1 (Real.rpow_nonneg hA _)) hB,
      Real.mul_rpow hS1 (Real.rpow_nonneg hA _), ← Real.rpow_mul hA, mul_one_div_cancel hr0.ne',
      Real.rpow_one]
  have hR : (∑ s, ((∑ t, F s t ^ r) * (Fintype.card β : ℝ)⁻¹) ^ (1 / r)) *
      (Fintype.card α : ℝ)⁻¹ = (∑ s, (∑ t, F s t ^ r) ^ (1 / r)) * (Fintype.card α : ℝ)⁻¹ *
        (Fintype.card β : ℝ)⁻¹ ^ (1 / r) := by
    simp_rw [Real.mul_rpow (hT _) hB]
    rw [← Finset.sum_mul]
    ring
  rw [hL, hR]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmink hA) (Real.rpow_nonneg hB _)

/-- **Mixed-norm swap** (blueprint sub-node `mixedNormSwap`), in squared form: for
`1 ≤ p ≤ 2` and real `g(s, t)` on finite uniform probability spaces,
`E_t (E_s |g|^p)^(2/p) ≤ (E_s (E_t g²)^(p/2))^(2/p)`, i.e.
`‖g‖_{L²_t L^p_s} ≤ ‖g‖_{L^p_s L²_t}` after taking square roots. -/
theorem mixedNormSwap {α β : Type*} [Fintype α] [Fintype β] {p : ℝ} (hp1 : 1 ≤ p)
    (hp2 : p ≤ 2) (g : α → β → ℝ) :
    unifAvg (fun t => (unifAvg (fun s => |g s t| ^ p)) ^ (2 / p)) ≤
      (unifAvg (fun s => (unifAvg (fun t => g s t ^ 2)) ^ (p / 2))) ^ (2 / p) := by
  have hp0 : 0 < p := by linarith
  have hpne : p ≠ 0 := hp0.ne'
  have hr : 1 ≤ 2 / p := by rw [le_div_iff₀ hp0]; linarith
  have h := minkowski_unifAvg hr (fun s t => |g s t| ^ p) (fun s t => by positivity)
  have hmul : p * (2 / p) = 2 := by field_simp
  have hpow : ∀ s t, (|g s t| ^ p) ^ (2 / p) = g s t ^ 2 := by
    intro s t
    rw [← Real.rpow_mul (abs_nonneg _), hmul, Real.rpow_two, sq_abs]
  have hinv : 1 / (2 / p) = p / 2 := by field_simp
  simp only [hpow, hinv] at h
  have hL : 0 ≤ unifAvg (fun t => (unifAvg (fun s => |g s t| ^ p)) ^ (2 / p)) :=
    unifAvg_nonneg fun t => Real.rpow_nonneg (unifAvg_nonneg fun s => by positivity) _
  have hexp : p / 2 * (2 / p) = 1 := by field_simp
  calc unifAvg (fun t => (unifAvg (fun s => |g s t| ^ p)) ^ (2 / p))
      = ((unifAvg (fun t => (unifAvg (fun s => |g s t| ^ p)) ^ (2 / p))) ^ (p / 2)) ^
          (2 / p) := by
        rw [← Real.rpow_mul hL, hexp, Real.rpow_one]
    _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hL _) h (div_nonneg zero_le_two hp0.le)

/-! ### Step 3: tensorization -/

/-- **Splitting the first coordinate of an average**:
`E_{z ∈ {0,1}^(n+1)} g z = E_t E_{x ∈ {0,1}^n} g (t, x)`.

Proof sketch: `Fintype.sum_equiv (Fin.consEquiv fun _ => Bool)`, `Fintype.sum_prod_type`;
`Fintype.card (Fin (n+1) → Bool) = 2 * 2^n` (`Fintype.card_fun`, `pow_succ`).
Reference: tex 4542-4549 (independence of coordinates); node L11.  [leaf: easy] -/
theorem unifAvg_cube_succ {n : ℕ} (g : (Fin (n + 1) → Bool) → ℝ) :
    unifAvg g = unifAvg (fun t : Bool => unifAvg (fun x : Fin n → Bool => g (consBit t x))) := by
  have hsum : ∑ z, g z = ∑ t : Bool, ∑ x : Fin n → Bool, g (consBit t x) := by
    rw [← Fintype.sum_prod_type']
    exact (Fintype.sum_equiv (Fin.consEquiv fun _ => Bool) _ _ fun _ => rfl).symm
  simp only [unifAvg]
  rw [← Finset.sum_div, div_div, hsum]
  congr 1
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  push_cast
  ring

/-- **Splitting a sum over `{0,1}^(n+1)` by the first bit**.

Proof sketch: `Fintype.sum_equiv (Fin.consEquiv fun _ => Bool)` and `Fintype.sum_prod_type`
(`consBit t x = Fin.cons t x`).
Reference: tex 4542-4549; node L11.  [leaf: easy] -/
theorem sum_cube_succ {n : ℕ} (g : (Fin (n + 1) → Bool) → ℝ) :
    ∑ z, g z = ∑ s : Bool, ∑ y : Fin n → Bool, g (consBit s y) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv fun _ => Bool) _ _ fun _ => rfl).symm

/-- **The noise kernel factorizes over the first coordinate**.

Proof sketch: `noiseKernel`, `Fin.prod_univ_succ`, `consBit`, `Fin.cons_zero`, `Fin.cons_succ`.
Reference: tex 4542-4549; node L11.  [leaf: easy] -/
theorem noiseKernel_consBit {n : ℕ} (ρ : ℝ) (t s : Bool) (x y : Fin n → Bool) :
    noiseKernel (n + 1) ρ (consBit t x) (consBit s y) =
      noiseWeight ρ t s * noiseKernel n ρ x y := by
  simp only [noiseKernel, consBit, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]

/-- **Tensor structure of the noise operator**: on `{0,1}^(n+1)`, `T_ρ` is the one-bit noise
in the first coordinate applied to the `n`-dimensional noise of the faces. -/
theorem noiseOp_succ {n : ℕ} (ρ : ℝ) (f : (Fin (n + 1) → Bool) → ℝ) (t : Bool)
    (x : Fin n → Bool) :
    noiseOp (n + 1) ρ f (consBit t x) =
      noiseOp1 ρ (fun s => noiseOp n ρ (restrictBit f s) x) t := by
  rw [noiseOp, sum_cube_succ, noiseOp1]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [noiseOp, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [noiseKernel_consBit, restrictBit]
  ring

/-- **Dimension zero**: on `{0,1}^0` the noise operator is the identity and both sides equal
`f(∅)²`.

Proof sketch: `Fin 0 → Bool` has exactly one element (`Unique`); `noiseKernel 0 ρ x y = 1`
(empty product), `Fintype.card = 1`, and `(|c|^p)^(2/p) = |c|^2 = c²` (`Real.rpow_mul`,
`p ≠ 0`, `Real.rpow_two`, `sq_abs`).
Reference: tex 4542-4549 ("include dimension zero"); node L11.  [leaf: easy] -/
theorem cubeHypercontractive_zero {ρ p : ℝ} (hp1 : 1 ≤ p) (f : (Fin 0 → Bool) → ℝ) :
    unifAvg (fun x => noiseOp 0 ρ f x ^ 2) ≤ (unifAvg (fun x => |f x| ^ p)) ^ (2 / p) := by
  have hp0 : 0 < p := by linarith
  have hmul : p * (2 / p) = 2 := by field_simp
  simp only [unifAvg, Fintype.sum_unique, Fintype.card_unique, Nat.cast_one, div_one, noiseOp,
    noiseKernel, Fin.prod_univ_zero, one_mul]
  rw [← Real.rpow_mul (abs_nonneg _), hmul, Real.rpow_two, sq_abs]

/-- **Hypercontractivity of the Boolean cube** (blueprint sub-node `cubeHypercontractive`), in
squared form: for `1 ≤ p ≤ 2` and `ρ² ≤ p - 1`, every `f` on `{0,1}^n` satisfies
`E (T_ρ f)² ≤ (E |f|^p)^(2/p)`, i.e. `‖T_ρ f‖₂ ≤ ‖f‖_p`.  Induction on the dimension: the
one-bit inequality on the first coordinate, the mixed-norm swap, and the induction hypothesis on
the two faces. -/
theorem cubeHypercontractive {ρ p : ℝ} (hp1 : 1 ≤ p) (hp2 : p ≤ 2) (hρ : ρ ^ 2 ≤ p - 1) :
    ∀ (n : ℕ) (f : (Fin n → Bool) → ℝ),
      unifAvg (fun x => noiseOp n ρ f x ^ 2) ≤ (unifAvg (fun x => |f x| ^ p)) ^ (2 / p) := by
  have hp0 : 0 < p := by linarith
  have hpne : p ≠ 0 := hp0.ne'
  have hexp : 2 / p * (p / 2) = 1 := by field_simp
  intro n
  induction n with
  | zero => exact fun f => cubeHypercontractive_zero hp1 f
  | succ n ih =>
    intro f
    calc unifAvg (fun z => noiseOp (n + 1) ρ f z ^ 2)
        = unifAvg (fun t : Bool => unifAvg (fun x : Fin n → Bool =>
            noiseOp (n + 1) ρ f (consBit t x) ^ 2)) := unifAvg_cube_succ _
      _ = unifAvg (fun x : Fin n → Bool => unifAvg (fun t : Bool =>
            noiseOp1 ρ (fun s => noiseOp n ρ (restrictBit f s) x) t ^ 2)) := by
          simp only [noiseOp_succ]
          exact unifAvg_comm
            (fun t x => noiseOp1 ρ (fun s => noiseOp n ρ (restrictBit f s) x) t ^ 2)
      _ ≤ unifAvg (fun x : Fin n → Bool =>
            (unifAvg (fun s : Bool => |noiseOp n ρ (restrictBit f s) x| ^ p)) ^ (2 / p)) :=
          unifAvg_mono fun x =>
            noiseOp1_hypercontractive hp1 hp2 hρ (fun s => noiseOp n ρ (restrictBit f s) x)
      _ ≤ (unifAvg (fun s : Bool => (unifAvg (fun x : Fin n → Bool =>
            noiseOp n ρ (restrictBit f s) x ^ 2)) ^ (p / 2))) ^ (2 / p) :=
          mixedNormSwap hp1 hp2 (fun s x => noiseOp n ρ (restrictBit f s) x)
      _ ≤ (unifAvg (fun s : Bool => ((unifAvg (fun x : Fin n → Bool =>
            |restrictBit f s x| ^ p)) ^ (2 / p)) ^ (p / 2))) ^ (2 / p) := by
          refine Real.rpow_le_rpow (unifAvg_nonneg fun s => Real.rpow_nonneg
            (unifAvg_nonneg fun x => sq_nonneg _) _) (unifAvg_mono fun s => ?_)
            (div_nonneg zero_le_two hp0.le)
          exact Real.rpow_le_rpow (unifAvg_nonneg fun x => sq_nonneg _) (ih (restrictBit f s))
            (div_nonneg hp0.le zero_le_two)
      _ = (unifAvg (fun s : Bool => unifAvg (fun x : Fin n → Bool =>
            |restrictBit f s x| ^ p))) ^ (2 / p) := by
          congr 1
          congr 1
          funext s
          rw [← Real.rpow_mul (unifAvg_nonneg fun x => by positivity), hexp, Real.rpow_one]
      _ = (unifAvg (fun z => |f z| ^ p)) ^ (2 / p) :=
          (congrArg (· ^ (2 / p)) (unifAvg_cube_succ (fun z => |f z| ^ p))).symm

/-! ### Step 4: semigroup and self-adjointness -/

/-- **One-bit kernel composition**:
`∑_c w_α(a, c) w_β(c, b) = w_{αβ}(a, b)`.

Proof sketch: `Fintype.sum_bool` and the four cases of `a, b` (`noiseWeight`, `ring`):
`(1+α)(1+β) + (1-α)(1-β) = 2 (1 + αβ)` and `(1+α)(1-β) + (1-α)(1+β) = 2 (1 - αβ)`.
Reference: tex 4551-4555 (`noiseSemigroup`); node L11.  [leaf: easy] -/
theorem noiseWeight_comp (α β : ℝ) (a b : Bool) :
    ∑ c, noiseWeight α a c * noiseWeight β c b = noiseWeight (α * β) a b := by
  rw [Fintype.sum_bool]
  cases a <;> cases b <;> simp only [noiseWeight, ite_eq_left, ite_eq_right, Bool.true_eq_false,
    Bool.false_eq_true, not_false_eq_true] <;> ring

/-- **Sums of coordinatewise products over the cube**:
`∑_{y ∈ {0,1}^n} ∏_i g i (y i) = ∏_i ∑_c g i c`.

Proof sketch: this is `Fintype.prod_sum` (or `Finset.prod_univ_sum` with
`Fintype.piFinset_univ`), read backwards.
Reference: tex 4551-4555 (independent coordinates); node L11.  [leaf: easy] -/
theorem sum_prod_cube {n : ℕ} (g : Fin n → Bool → ℝ) :
    ∑ y : Fin n → Bool, ∏ i, g i (y i) = ∏ i, ∑ c, g i c := by
  exact (Fintype.prod_sum g).symm

/-- **Kernel composition**: `∑_y K_α(x, y) K_β(y, z) = K_{αβ}(x, z)` on `{0,1}^n`, coordinatewise
from `noiseWeight_comp`. -/
theorem noiseKernel_comp (n : ℕ) (α β : ℝ) (x z : Fin n → Bool) :
    ∑ y, noiseKernel n α x y * noiseKernel n β y z = noiseKernel n (α * β) x z := by
  simp only [noiseKernel, ← Finset.prod_mul_distrib]
  rw [sum_prod_cube (fun i c => noiseWeight α (x i) c * noiseWeight β c (z i))]
  exact Finset.prod_congr rfl fun i _ => noiseWeight_comp α β (x i) (z i)

/-- **Noise semigroup** (blueprint sub-node `noiseSemigroup`): `T_α (T_β f) = T_{αβ} f`. -/
theorem noiseSemigroup (n : ℕ) (α β : ℝ) (f : (Fin n → Bool) → ℝ) (x : Fin n → Bool) :
    noiseOp n α (noiseOp n β f) x = noiseOp n (α * β) f x := by
  simp only [noiseOp, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [← noiseKernel_comp n α β x z, Finset.sum_mul]
  exact Finset.sum_congr rfl fun y _ => by ring

/-- **Self-adjointness** (blueprint sub-node `noiseSelfAdjoint`):
`E[f · T_ρ g] = E[T_ρ f · g]` on the normalized cube.

Proof sketch: the kernel is symmetric, `noiseKernel n ρ x y = noiseKernel n ρ y x`
(`noiseWeight` is symmetric: `b = c ↔ c = b`); unfold `unifAvg`, `noiseOp`, distribute
(`Finset.mul_sum`, `Finset.sum_mul`) and swap the double sum (`Finset.sum_comm`).
Reference: tex 4551-4555; node L11.  [leaf: easy] -/
theorem noiseSelfAdjoint (n : ℕ) (ρ : ℝ) (f g : (Fin n → Bool) → ℝ) :
    unifAvg (fun x => f x * noiseOp n ρ g x) = unifAvg (fun x => noiseOp n ρ f x * g x) := by
  have hsymm : ∀ x y, noiseKernel n ρ x y = noiseKernel n ρ y x := fun x y =>
    Finset.prod_congr rfl fun i _ => by simp only [noiseWeight, eq_comm]
  simp only [unifAvg, noiseOp, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm (f := fun x y => noiseKernel n ρ x y * f y * g x)]
  refine congrArg (· / _) (Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_)
  rw [hsymm]
  ring

/-! ### Step 5: indicators and small-set expansion -/

/-- The indicator `1_U` of a set of cube points, as a real function. -/
noncomputable def cubeIndicator {n : ℕ} (U : Finset (Fin n → Bool)) (x : Fin n → Bool) : ℝ :=
  if x ∈ U then 1 else 0

/-- **`L^p` mass of an indicator**: `E |1_U|^p = |U| / 2^n` for `p > 0`.

Proof sketch: `|1_U x|^p = 1_U x` (`Real.one_rpow`, `Real.zero_rpow hp.ne'`); then
`Finset.sum_boole`/`sum_ite_mem` and `Fintype.card (Fin n → Bool) = 2^n`
(`Fintype.card_fun`, `Fintype.card_bool`, `Fintype.card_fin`).
Reference: tex 4557-4566 (`‖f‖_{1+γ}² = μ^(2/(1+γ))`); node L11.  [leaf: easy] -/
theorem unifAvg_abs_indicator_rpow {n : ℕ} (U : Finset (Fin n → Bool)) {p : ℝ} (hp : 0 < p) :
    unifAvg (fun x => |cubeIndicator U x| ^ p) = U.card / 2 ^ n := by
  have h : ∀ x, |cubeIndicator U x| ^ p = if x ∈ U then 1 else 0 := by
    intro x
    unfold cubeIndicator
    split_ifs
    · rw [abs_one, Real.one_rpow]
    · rw [abs_zero, Real.zero_rpow hp.ne']
  simp only [unifAvg, h, Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter,
    Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  push_cast
  rfl

/-- **Indicator noise bound** (blueprint sub-node `indicatorNoiseBound`): for `γ ∈ [0, 1]`,
`E[1_U · T_γ 1_U] = ‖T_√γ 1_U‖₂² ≤ ‖1_U‖_{1+γ}² = μ^(2/(1+γ))`, `μ = |U| / 2^n`. -/
theorem indicatorNoiseBound {n : ℕ} (U : Finset (Fin n → Bool)) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ ≤ 1) :
    unifAvg (fun x => cubeIndicator U x * noiseOp n γ (cubeIndicator U) x) ≤
      ((U.card : ℝ) / 2 ^ n) ^ (2 / (1 + γ)) := by
  have hsq : Real.sqrt γ * Real.sqrt γ = γ := Real.mul_self_sqrt hγ0
  have hρ : Real.sqrt γ ^ 2 ≤ (1 + γ) - 1 := by rw [Real.sq_sqrt hγ0]; linarith
  have hHC := cubeHypercontractive (ρ := Real.sqrt γ) (p := 1 + γ) (by linarith) (by linarith)
    hρ n (cubeIndicator U)
  rw [unifAvg_abs_indicator_rpow U (by linarith)] at hHC
  calc unifAvg (fun x => cubeIndicator U x * noiseOp n γ (cubeIndicator U) x)
      = unifAvg (fun x => cubeIndicator U x *
          noiseOp n (Real.sqrt γ) (noiseOp n (Real.sqrt γ) (cubeIndicator U)) x) := by
        congr 1
        funext x
        rw [noiseSemigroup, hsq]
    _ = unifAvg (fun x => noiseOp n (Real.sqrt γ) (cubeIndicator U) x *
          noiseOp n (Real.sqrt γ) (cubeIndicator U) x) :=
        noiseSelfAdjoint n _ _ _
    _ = unifAvg (fun x => noiseOp n (Real.sqrt γ) (cubeIndicator U) x ^ 2) := by
        congr 1
        funext x
        ring
    _ ≤ _ := hHC

/-- **The noise kernel at `ρ = 1 - 2q`**: `K(x, y) = q^dist(x,y) (1 - q)^(n - dist(x,y))`
(each bit flips independently with probability `q`).

Proof sketch: `noiseWeight (1 - 2q) b c` is `1 - q` if `b = c` and `q` otherwise; split
`∏_i` by `x i = y i` (`Finset.prod_ite`, `prod_const`), with
`#{i | x i ≠ y i} = hammingDist x y` and `#{i | x i = y i} = n - hammingDist x y`
(`Finset.filter_card_add_filter_neg_card_eq_card`, `Finset.card_univ`, `Fintype.card_fin`).
Reference: tex 4562-4566 ("substitute γ = 1 - 2q"); node L11.  [leaf: medium] -/
theorem noiseKernel_one_sub_two_mul (n : ℕ) (q : ℝ) (x y : Fin n → Bool) :
    noiseKernel n (1 - 2 * q) x y =
      q ^ (_root_.hammingDist x y) * (1 - q) ^ (n - _root_.hammingDist x y) := by
  have hw : ∀ i, noiseWeight (1 - 2 * q) (x i) (y i) = if x i ≠ y i then q else 1 - q := by
    intro i
    by_cases h : x i = y i
    · rw [noiseWeight, ite_eq_left h, ite_eq_right (not_not.2 h)]
      ring
    · rw [noiseWeight, ite_eq_right h, ite_eq_left h]
      ring
  have hcard := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun i => x i ≠ y i)
  rw [Finset.card_univ, Fintype.card_fin] at hcard
  rw [noiseKernel, Finset.prod_congr rfl fun i _ => hw i, Finset.prod_ite, Finset.prod_const,
    Finset.prod_const, _root_.hammingDist]
  congr 2
  omega

/-- **The indicator correlation as a double sum**:
`E[1_U · T_ρ 1_U] = (∑_{x ∈ U} ∑_{y ∈ U} K_ρ(x, y)) / 2^n`.

Proof sketch: unfold `unifAvg`, `noiseOp`, `cubeIndicator`; `Finset.sum_ite_mem`/`sum_filter`
with `univ.filter (· ∈ U) = U`, `Finset.mul_sum`, `Fintype.card (Fin n → Bool) = 2^n`.
Reference: tex 4557-4566; node L11.  [leaf: easy] -/
theorem unifAvg_indicator_mul_noiseOp {n : ℕ} (U : Finset (Fin n → Bool)) (ρ : ℝ) :
    unifAvg (fun x => cubeIndicator U x * noiseOp n ρ (cubeIndicator U) x) =
      (∑ x ∈ U, ∑ y ∈ U, noiseKernel n ρ x y) / 2 ^ n := by
  simp only [unifAvg, noiseOp, cubeIndicator, ite_mul, one_mul, zero_mul, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_mem, Finset.univ_inter, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin]
  push_cast
  rfl

/-- **Exponent arithmetic**: for `μ > 0` and `q ≤ 1/2`,
`μ^(2/(1 + (1 - 2q))) c = μ c μ^(q/(1-q))`.

Proof sketch: `2 / (2 - 2q) = 1 + q / (1 - q)` (`1 - q ≥ 1/2 > 0`, `field_simp`, `ring`);
`Real.rpow_add hμ`, `Real.rpow_one`, `ring`.
Reference: tex 4562-4566; node L11.  [leaf: easy] -/
theorem sse_exponent_arith {μ q c : ℝ} (hμ : 0 < μ) (hq1 : q ≤ 1 / 2) :
    μ ^ (2 / (1 + (1 - 2 * q))) * c = μ * c * μ ^ (q / (1 - q)) := by
  have hq : 0 < 1 - q := by linarith
  have h2 : 1 + (1 - 2 * q) ≠ 0 := by linarith
  have he : 2 / (1 + (1 - 2 * q)) = 1 + q / (1 - q) := by
    field_simp
    ring
  rw [he, Real.rpow_add hμ, Real.rpow_one]
  ring

/-- **Small-set expansion on `Fin n → Bool`**: for nonempty `U` and `0 ≤ q ≤ 1/2`,
`∑_{x, y ∈ U} q^dist (1 - q)^(n - dist) ≤ |U| μ^(q/(1-q))`, `μ = |U| / 2^n`; equivalently
`Pr[Y ∈ U | X uniform in U] ≤ μ^(q/(1-q))` for `q`-noise `Y` of `X`. -/
theorem cubeSmallSetExpansion_fin {n : ℕ} (U : Finset (Fin n → Bool)) (hU : U.Nonempty)
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2) :
    ∑ x ∈ U, ∑ y ∈ U, q ^ (_root_.hammingDist x y) * (1 - q) ^ (n - _root_.hammingDist x y) ≤
      U.card * ((U.card : ℝ) / 2 ^ n) ^ (q / (1 - q)) := by
  have hb := indicatorNoiseBound U (γ := 1 - 2 * q) (by linarith) (by linarith)
  rw [unifAvg_indicator_mul_noiseOp] at hb
  simp only [noiseKernel_one_sub_two_mul] at hb
  have hμ : 0 < (U.card : ℝ) / 2 ^ n := by
    have := hU.card_pos
    positivity
  rw [div_le_iff₀ (by positivity)] at hb
  calc _ ≤ ((U.card : ℝ) / 2 ^ n) ^ (2 / (1 + (1 - 2 * q))) * 2 ^ n := hb
    _ = (U.card : ℝ) / 2 ^ n * 2 ^ n * ((U.card : ℝ) / 2 ^ n) ^ (q / (1 - q)) :=
        sse_exponent_arith hμ hq1
    _ = U.card * ((U.card : ℝ) / 2 ^ n) ^ (q / (1 - q)) := by
        rw [div_mul_cancel₀ _ (by positivity)]

/-! ### Transport to bit strings -/

/-- The cube point of a string: its first `M` bits (`u[i]!`). -/
def toCube (M : ℕ) (u : BitString) : Fin M → Bool :=
  fun i => u[(i : ℕ)]!

/-- `toCube M` is injective on the strings of length `M`.

Proof sketch: for `u, v` of length `M` with equal images, `List.ext_getElem` (lengths agree,
and `u[i] = u[i]! = v[i]! = v[i]` for `i < M`, `getElem!_pos`).
Reference: tex 4512-4517 (cube encoding); node L11.  [leaf: easy] -/
theorem toCube_injOn (M : ℕ) : Set.InjOn (toCube M) (stringsOfLength M : Set BitString) := by
  intro u hu v hv huv
  have hu' : u.length = M := (mem_stringsOfLength M u).1 hu
  have hv' : v.length = M := (mem_stringsOfLength M v).1 hv
  refine List.ext_getElem (hu'.trans hv'.symm) fun i hi1 hi2 => ?_
  have h := congrFun huv ⟨i, hu' ▸ hi1⟩
  simp only [toCube] at h
  rwa [getElem!_pos u i hi1, getElem!_pos v i hi2] at h

/-- The library's list Hamming distance is Mathlib's `hammingDist` of the cube points.

Proof sketch: `hammingDist_eq_filter_card` gives `#{i < M | u[i]! ≠ v[i]!}`; Mathlib's
`hammingDist` is `#{i : Fin M | toCube M u i ≠ toCube M v i}`; transport along
`Fin.val : Fin M ↪ ℕ` (`Finset.card_map`, `Fin.univ_val_map`/`Finset.map_valEmbedding_univ`
= `range M`, `Finset.filter_map`).
Reference: tex 4512-4517; node L11.  [leaf: easy] -/
theorem hammingDist_eq_toCube {M : ℕ} {u v : BitString} (hu : u.length = M)
    (hv : v.length = M) : hammingDist u v = _root_.hammingDist (toCube M u) (toCube M v) := by
  rw [hammingDist_eq_filter_card M u v hu hv, _root_.hammingDist, Finset.card_filter,
    Finset.card_filter, Finset.sum_range]
  rfl

/-- **Small-set expansion of the Boolean cube** (blueprint node L11).  For a nonempty set `U`
of strings of length `M` and `0 ≤ q ≤ 1/2`, with `μ = |U| / 2^M`:
`∑_{u, v ∈ U} q^dist(u,v) (1 - q)^(M - dist(u,v)) ≤ |U| μ^(q/(1-q))`.  Dividing by `|U|`:
if `X` is uniform in `U` and `Y` flips each bit of `X` independently with probability `q`, then
`Pr[Y ∈ U] ≤ μ^(q/(1-q))`. -/
theorem cubeSmallSetExpansion (M : ℕ) (U : Finset BitString) (hUM : U ⊆ stringsOfLength M)
    (hU : U.Nonempty) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2) :
    ∑ u ∈ U, ∑ v ∈ U, q ^ hammingDist u v * (1 - q) ^ (M - hammingDist u v) ≤
      U.card * ((U.card : ℝ) / 2 ^ M) ^ (q / (1 - q)) := by
  have hinj : Set.InjOn (toCube M) (U : Set BitString) :=
    (toCube_injOn M).mono (Finset.coe_subset.mpr hUM)
  have hcard : (U.image (toCube M)).card = U.card := Finset.card_image_of_injOn hinj
  have h := cubeSmallSetExpansion_fin (U.image (toCube M)) (hU.image _) hq0 hq1
  rw [hcard, Finset.sum_image hinj] at h
  calc ∑ u ∈ U, ∑ v ∈ U, q ^ hammingDist u v * (1 - q) ^ (M - hammingDist u v)
      = ∑ u ∈ U, ∑ y ∈ U.image (toCube M), q ^ _root_.hammingDist (toCube M u) y *
          (1 - q) ^ (M - _root_.hammingDist (toCube M u) y) := by
        refine Finset.sum_congr rfl fun u hu => ?_
        rw [Finset.sum_image hinj]
        refine Finset.sum_congr rfl fun v hv => ?_
        rw [hammingDist_eq_toCube ((mem_stringsOfLength M u).1 (hUM hu))
          ((mem_stringsOfLength M v).1 (hUM hv))]
    _ ≤ _ := h

end Kolmogorov.StrongMerging.Lower
