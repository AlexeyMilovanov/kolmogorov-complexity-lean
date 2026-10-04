/-
Copyright (c) 2024 Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Author
-/
import KolmogorovMathlib.Solomonoff.Basic
import KolmogorovMathlib.AlgorithmicRandomness.LevelStrings

/-!
# Expectations over prefixes and the prediction error

The expectation of a function of the first `n` bits under a measure `μ` on Cantor space is the
finite sum `E_{x ∼ μ, |x| = n} f(x) = Σ_{|x| = n} μ(Ω_x) f(x)` over the strings of length `n`
(`levelFinset n`), which is also the integral `∫ f(w_{<n}) dμ(w)`. The `n`-th prediction error of
a predictor `a` for the bit `b` is the expected squared difference between its conditional and the
true one, `S_n^b = E_{x ∼ μ, |x| = n} (a(b | x) − μ(b | x))²`.

### Outline

* `prefixExpectation μ n f`, the finite-sum expectation, and its integral form
  `prefixExpectation_eq_integral`;
* the tower property `prefixExpectation_succ`: the level-`(n+1)` expectation is the level-`n`
  expectation of the one-step conditional expectation `Σ_b μ(b | x) f(xb)`;
* level zero (`prefixExpectation_zero`), additivity, monotonicity on the support, the bound by a
  constant, nonnegativity;
* `predictionError μ a b n`, its nonnegativity and its integral form
  `predictionError_eq_integral` (Hutter's `E[(ξ(b | x_{<n}) − μ(b | x_{<n}))²]`).

Strings of `μ`-mass zero carry weight zero, so the junk values of the conditionals there (see
`condProb`) never contribute.

Sources: Li–Vitányi (3rd ed.) Theorem 5.2.1 (`S_n = Σ_{l(x)=n-1} μ(x) (M(0|x) − μ(0|x))²`),
Hutter (2005) §3.2 (expectations `E[…]` of the instantaneous errors).
-/

namespace Kolmogorov

open MeasureTheory
open scoped ENNReal

/-- The expectation `E_{x ∼ μ, |x| = n} f(x) = Σ_{|x| = n} μ(Ω_x) f(x)` of a real function of the
length-`n` prefix of a `μ`-random sequence, as a finite sum over the strings of length `n`.
Item SOL-E-EXP; Li–Vitányi (3rd ed.) Theorem 5.2.1 (`Σ_{l(x)=n} μ(x) …`). -/
noncomputable def prefixExpectation (μ : Measure CantorSeq) (n : ℕ) (f : BitString → ℝ) : ℝ :=
  ∑ x ∈ levelFinset n, (cantorMass μ x).toReal * f x


private lemma sum_indicator_cantorCylinder_real (n : ℕ) (f : BitString → ℝ) (w : CantorSeq) :
    ∑ x ∈ levelFinset n, (cantorCylinder x).indicator (fun _ => f x) w
      = f (cantorPrefix w n) := by
  classical
  rw [Finset.sum_eq_single (cantorPrefix w n)]
  · have hmem : w ∈ cantorCylinder (cantorPrefix w n) := by
      change IsCantorPrefix (cantorPrefix w n) w
      rw [isCantorPrefix_iff_cantorPrefix_eq]
      simp
    simp [Set.indicator_of_mem hmem]
  · intro x hx hne
    have hlen : x.length = n := mem_levelFinset.1 hx
    have hnot : w ∉ cantorCylinder x := by
      intro hmem
      have : cantorPrefix w x.length = x :=
        (isCantorPrefix_iff_cantorPrefix_eq x w).1 hmem
      rw [hlen] at this
      exact hne this.symm
    simp [Set.indicator_of_notMem hnot]
  · intro hnot
    exact absurd (mem_levelFinset.2 (by simp)) hnot

/-- The prefix expectation is the integral of `f` evaluated at the length-`n` prefix.
Item SOL-E-INT; the real-valued analogue of `lintegral_comp_cantorPrefix`. -/
theorem prefixExpectation_eq_integral (μ : Measure CantorSeq) [IsProbabilityMeasure μ] (n : ℕ)
    (f : BitString → ℝ) :
    prefixExpectation μ n f = ∫ w, f (cantorPrefix w n) ∂μ := by
  classical
  have hpt : (fun w => f (cantorPrefix w n))
      = fun w => ∑ x ∈ levelFinset n, (cantorCylinder x).indicator (fun _ => f x) w := by
    funext w
    exact (sum_indicator_cantorCylinder_real n f w).symm
  rw [hpt]
  rw [integral_finsetSum]
  · rw [prefixExpectation]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [integral_indicator (measurableSet_cantorCylinder x)]
    rw [setIntegral_const]
    simp only [cantorMass, smul_eq_mul]
    have h_real : μ.real (cantorCylinder x) = (μ (cantorCylinder x)).toReal := rfl
    rw [h_real, mul_comm]
  · intro x _
    apply Integrable.indicator
    · exact integrable_const (f x)
    · exact measurableSet_cantorCylinder x

/-- At level zero the expectation is the value at the empty string. Item SOL-E-ZERO. -/
theorem prefixExpectation_zero (μ : Measure CantorSeq) [IsProbabilityMeasure μ]
    (f : BitString → ℝ) : prefixExpectation μ 0 f = f [] := by
  unfold prefixExpectation levelFinset levelList
  simp only [List.toFinset_cons, List.toFinset_nil, insert_empty_eq, Finset.sum_singleton]
  have hm : (cantorMass μ []).toReal = 1 := by
    rw [cantorMass, cantorCylinder_nil, measure_univ]
    exact ENNReal.toReal_one
  rw [hm, one_mul]

private lemma sum_levelFinset_succ (n : ℕ) (f : BitString → ℝ) :
    ∑ x ∈ levelFinset (n + 1), f x =
      ∑ x ∈ levelFinset n, (f (x ++ [false]) + f (x ++ [true])) := by
  have H : ∑ x ∈ levelFinset (n + 1), f x = ((levelList (n + 1)).map f).sum := by
    rw [sum_levelFinset_eq_sum_levelList]
  rw [H]
  change (((levelList n).map (fun x => x ++ [false]) ++
    (levelList n).map (fun x => x ++ [true])).map f).sum = _
  rw [List.map_append, List.sum_append, List.map_map, List.map_map]
  have heq1 : (List.map (f ∘ fun x => x ++ [false]) (levelList n)).sum =
    (List.map (fun x => f (x ++ [false])) (levelList n)).sum := rfl
  have heq2 : (List.map (f ∘ fun x => x ++ [true]) (levelList n)).sum =
    (List.map (fun x => f (x ++ [true])) (levelList n)).sum := rfl
  rw [heq1, heq2]
  have h1 : (List.map (fun x => f (x ++ [false])) (levelList n)).sum =
    ∑ x ∈ levelFinset n, f (x ++ [false]) := by
    rw [← sum_levelFinset_eq_sum_levelList]
  have h2 : (List.map (fun x => f (x ++ [true])) (levelList n)).sum =
    ∑ x ∈ levelFinset n, f (x ++ [true]) := by
    rw [← sum_levelFinset_eq_sum_levelList]
  rw [h1, h2, ← Finset.sum_add_distrib]

/-- Tower property: the expectation at level `n + 1` is the level-`n` expectation of the one-step
conditional expectation `Σ_b μ(b | x) f(xb)`. Item SOL-E-TOWER. -/
theorem prefixExpectation_succ (μ : Measure CantorSeq) [IsProbabilityMeasure μ] (n : ℕ)
    (f : BitString → ℝ) :
    prefixExpectation μ (n + 1) f =
      prefixExpectation μ n
        (fun x => ∑ b : Bool, condProb (cantorMass μ) x b * f (x ++ [b])) := by
  unfold prefixExpectation
  rw [sum_levelFinset_succ]
  apply Finset.sum_congr rfl
  intro x _
  have hcts : IsContinuousTreeSemimeasure (cantorMass μ) := by
    constructor
    · rw [cantorMass, cantorCylinder_nil]
      exact measure_univ (μ := μ)
    · intro y
      exact le_of_eq (cantorMass_add μ y).symm
  have ha1 := hcts.toReal_mul_condProb x false
  have ha2 := hcts.toReal_mul_condProb x true
  calc
    (cantorMass μ (x ++ [false])).toReal * f (x ++ [false]) +
      (cantorMass μ (x ++ [true])).toReal * f (x ++ [true])
      = (cantorMass μ x).toReal * (condProb (cantorMass μ) x false * f (x ++ [false])) +
        (cantorMass μ x).toReal * (condProb (cantorMass μ) x true * f (x ++ [true])) := by
        have h1 : (cantorMass μ x).toReal * (condProb (cantorMass μ) x false * f (x ++ [false])) =
          (cantorMass μ (x ++ [false])).toReal * f (x ++ [false]) := by rw [← mul_assoc, ha1]
        have h2 : (cantorMass μ x).toReal * (condProb (cantorMass μ) x true * f (x ++ [true])) =
          (cantorMass μ (x ++ [true])).toReal * f (x ++ [true]) := by rw [← mul_assoc, ha2]
        exact Eq.symm (congr (congrArg HAdd.hAdd h1) h2)
    _ = (cantorMass μ x).toReal * (condProb (cantorMass μ) x false * f (x ++ [false]) +
        condProb (cantorMass μ) x true * f (x ++ [true])) := by rw [← mul_add]
    _ = (cantorMass μ x).toReal * (∑ b : Bool, condProb (cantorMass μ) x b * f (x ++ [b])) := by
        have h_sum : (∑ b : Bool, condProb (cantorMass μ) x b * f (x ++ [b])) =
          condProb (cantorMass μ) x false * f (x ++ [false]) +
          condProb (cantorMass μ) x true * f (x ++ [true]) := by
          rw [Fintype.sum_bool]
          exact add_comm _ _
        rw [h_sum]


/-- The prefix expectation is additive in the function. Item SOL-E-ADD. -/
theorem prefixExpectation_add (μ : Measure CantorSeq) (n : ℕ) (f g : BitString → ℝ) :
    prefixExpectation μ n (fun x => f x + g x) =
      prefixExpectation μ n f + prefixExpectation μ n g := by
  unfold prefixExpectation
  have h_add : ∑ x ∈ levelFinset n, (cantorMass μ x).toReal * (f x + g x) =
    ∑ x ∈ levelFinset n, ((cantorMass μ x).toReal * f x + (cantorMass μ x).toReal * g x) := by
    apply Finset.sum_congr rfl
    intro x _
    rw [mul_add]
  rw [h_add, Finset.sum_add_distrib]

/-- Monotonicity of the prefix expectation; the inequality is needed only on the strings of
positive mass. Item SOL-E-MONO. -/
theorem prefixExpectation_mono (μ : Measure CantorSeq) (n : ℕ) {f g : BitString → ℝ}
    (h : ∀ x, cantorMass μ x ≠ 0 → f x ≤ g x) :
    prefixExpectation μ n f ≤ prefixExpectation μ n g := by
  unfold prefixExpectation
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : cantorMass μ x = 0
  · simp [hx]
  · have h_le := h x hx
    have h_pos : 0 ≤ (cantorMass μ x).toReal := ENNReal.toReal_nonneg
    gcongr

private theorem sum_cantorMass_toReal (μ : Measure CantorSeq) [IsProbabilityMeasure μ] (n : ℕ) :
    ∑ x ∈ levelFinset n, (cantorMass μ x).toReal = 1 := by
  have h_int : ∫⁻ _, 1 ∂μ = ∑ x ∈ levelFinset n, 1 * cantorMass μ x :=
    lintegral_comp_cantorPrefix μ n (fun _ => 1)
  have h1 : ∫⁻ _, 1 ∂μ = 1 := by rw [lintegral_one, measure_univ]
  simp only [h1, one_mul] at h_int
  rw [← ENNReal.toReal_sum]
  · rw [← h_int, ENNReal.toReal_one]
  · intro x _
    exact measure_ne_top μ (cantorCylinder x)

/-- Under a probability measure, a bound on the strings of positive mass bounds the expectation.
Item SOL-E-LE. -/
theorem prefixExpectation_le_const (μ : Measure CantorSeq) [IsProbabilityMeasure μ] (n : ℕ)
    {f : BitString → ℝ} {B : ℝ} (h : ∀ x, cantorMass μ x ≠ 0 → f x ≤ B) :
    prefixExpectation μ n f ≤ B := by
  have h_mono : prefixExpectation μ n f ≤ prefixExpectation μ n (fun _ => B) :=
    prefixExpectation_mono μ n h
  have h_const : prefixExpectation μ n (fun _ => B) = B := by
    unfold prefixExpectation
    rw [← Finset.sum_mul]
    rw [sum_cantorMass_toReal μ n]
    exact one_mul B
  exact h_const ▸ h_mono

/-- The expectation of a nonnegative function is nonnegative. Item SOL-E-NONNEG. -/
theorem prefixExpectation_nonneg (μ : Measure CantorSeq) (n : ℕ) {f : BitString → ℝ}
    (h : ∀ x, 0 ≤ f x) : 0 ≤ prefixExpectation μ n f := by
  unfold prefixExpectation
  apply Finset.sum_nonneg
  intro x _
  apply mul_nonneg
  · exact ENNReal.toReal_nonneg
  · exact h x

/-- The expected squared error at step `n` of the prediction of the bit `b` by the tree mass
function `a`, measured against the true measure `μ`:
`S_n^b = E_{x ∼ μ, |x| = n} (a(b | x) − μ(b | x))²`, the prediction of the bit number `n`
(counting from `0`) made after seeing the first `n` bits. With `a = M` and `b = true` this is the
`n`-th term of Solomonoff's error sum. Item SOL-E-ERR; Li–Vitányi (3rd ed.) Theorem 5.2.1 (`S_n`,
stated there for the bit `0`), Hutter (2005) Theorem 3.19. -/
noncomputable def predictionError (μ : Measure CantorSeq) (a : BitString → ℝ≥0∞) (b : Bool)
    (n : ℕ) : ℝ :=
  prefixExpectation μ n (fun x => (condProb a x b - condProb (cantorMass μ) x b) ^ 2)

/-- Prediction errors are nonnegative. Item SOL-E-ERR-NONNEG. -/
theorem predictionError_nonneg (μ : Measure CantorSeq) (a : BitString → ℝ≥0∞) (b : Bool)
    (n : ℕ) : 0 ≤ predictionError μ a b n := by
  unfold predictionError
  apply prefixExpectation_nonneg
  intro x
  exact sq_nonneg _

/-- The prediction error is the `μ`-expectation over sequences `w` of the squared error at step
`n`, Hutter's `E[(ξ(b | w_{<n}) − μ(b | w_{<n}))²]`. Item SOL-E-ERR-INT; Hutter (2005)
Theorem 3.19. -/
theorem predictionError_eq_integral (μ : Measure CantorSeq) [IsProbabilityMeasure μ]
    (a : BitString → ℝ≥0∞) (b : Bool) (n : ℕ) :
    predictionError μ a b n =
      ∫ w, (condProb a (cantorPrefix w n) b -
        condProb (cantorMass μ) (cantorPrefix w n) b) ^ 2 ∂μ := by
  unfold predictionError
  apply prefixExpectation_eq_integral

end Kolmogorov
