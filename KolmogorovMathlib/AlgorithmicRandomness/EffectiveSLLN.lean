import KolmogorovMathlib.AlgorithmicRandomness.MartinLof
import KolmogorovMathlib.AlgorithmicRandomness.StrongLaw
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The effective strong law for the uniform measure

This file proves SUV Theorem 32: the set of bit sequences whose limit frequency of
ones is not `1/2` is an effectively null set for the uniform measure.

The construction is the standard one.  For each level `k` we consider the deviation
sets `devSet k n = {w | 1/(k+1) ≤ |freq(w, n) - 1/2|}`, whose uniform measure is
bounded by `2 exp (-2n/(k+1)^2)` by Hoeffding's inequality.  For each `m` we take the
tail union of these sets from an explicit threshold `devThresh k m` on, which has
measure at most `2⁻ᵐ`, and which is effectively open because a deviation set is a
computable union of cylinders.  Every sequence whose frequencies do not converge to
`1/2` deviates at some level `k` infinitely often, and hence lies in all of these
tail unions.
-/

namespace Kolmogorov

open MeasureTheory ProbabilityTheory Filter Topology ENNReal
open scoped NNReal

/-! ### The deviation predicate -/

/-- The absolute difference of two naturals. -/
def natAbsDiff (a b : ℕ) : ℕ := (a - b) + (b - a)

/-- The natural absolute difference agrees with the absolute value of the rational
difference. -/
lemma natAbsDiff_cast_rat (a b : ℕ) : (natAbsDiff a b : ℚ) = |(a : ℚ) - b| := by
  unfold natAbsDiff
  rcases le_total a b with h | h
  · have hb : ((b - a : ℕ) : ℚ) = (b : ℚ) - a := by
      have := Nat.cast_sub (R := ℚ) h; simpa using this
    have hab : (a : ℚ) - b ≤ 0 := by
      have : (a : ℚ) ≤ b := by exact_mod_cast h
      linarith
    rw [Nat.sub_eq_zero_of_le h, abs_of_nonpos hab]
    push_cast [hb]
    ring
  · have ha : ((a - b : ℕ) : ℚ) = (a : ℚ) - b := by
      have := Nat.cast_sub (R := ℚ) h; simpa using this
    have hab : (0 : ℚ) ≤ (a : ℚ) - b := by
      have : (b : ℚ) ≤ a := by exact_mod_cast h
      linarith
    rw [Nat.sub_eq_zero_of_le h, abs_of_nonneg hab]
    push_cast [ha]
    ring

/-- `devBool k n c` says that a string of length `n` with `c` ones deviates from the
balanced frequency by at least `1/(k+1)`; equivalently `2n ≤ (k+1) * |2c - n|`. -/
def devBool (k n c : ℕ) : Bool := (2 * n - (k + 1) * natAbsDiff (2 * c) n) == 0

/-- The deviation test, unfolded into an inequality between natural numbers. -/
lemma devBool_iff (k n c : ℕ) :
    devBool k n c = true ↔ 2 * n ≤ (k + 1) * natAbsDiff (2 * c) n := by
  unfold devBool
  rw [beq_iff_eq, Nat.sub_eq_zero_iff_le]

/-- The deviation of the empirical frequency `c / n` from `1/2`, written as a single rational
quotient. -/
lemma devAbs_eq (n c : ℕ) (hn : 0 < n) :
    |(c : ℚ) / n - 1 / 2| = (natAbsDiff (2 * c) n : ℚ) / (2 * n) := by
  have hn' : (0 : ℚ) < n := by exact_mod_cast hn
  have h1 : (c : ℚ) / n - 1 / 2 = (2 * (c : ℚ) - n) / (2 * n) := by field_simp
  rw [h1, abs_div, abs_of_pos (show (0:ℚ) < 2 * n by positivity), natAbsDiff_cast_rat,
    show ((2 * c : ℕ) : ℚ) = 2 * (c : ℚ) by push_cast; ring]

/-- The deviation test succeeds exactly when the empirical frequency differs from `1/2` by at
least `1 / (k + 1)`. -/
lemma devBool_iff_rat (k n c : ℕ) (hn : 0 < n) :
    devBool k n c = true ↔ (1 : ℚ) / (k + 1) ≤ |(c : ℚ) / n - 1 / 2| := by
  have hn' : (0 : ℚ) < n := by exact_mod_cast hn
  rw [devBool_iff, devAbs_eq n c hn,
    div_le_div_iff₀ (by positivity : (0:ℚ) < (k:ℚ) + 1) (by positivity : (0:ℚ) < 2 * n)]
  constructor
  · intro h
    have hq : ((2 * n : ℕ) : ℚ) ≤ (((k + 1) * natAbsDiff (2 * c) n : ℕ) : ℚ) := by
      exact_mod_cast h
    push_cast at hq
    nlinarith [hq]
  · intro h
    have hq : ((2 * n : ℕ) : ℚ) ≤ (((k + 1) * natAbsDiff (2 * c) n : ℕ) : ℚ) := by
      push_cast
      nlinarith [h]
    exact_mod_cast hq

/-- The set of sequences whose length-`n` prefix deviates at level `k`. -/
def devSet (k n : ℕ) : Set CantorSeq :=
  {w | devBool k n ((cantorPrefix w n).count true) = true}

/-! ### The measure of a deviation set (Hoeffding's inequality) -/

/-- Each coordinate has expectation `1/2` under the uniform measure. -/
lemma uniform_integral_bitVal (i : ℕ) :
    ∫ w, bitVal (w i) ∂uniformMeasure = 1 / 2 := by
  have h := bernoulli_identDistrib (1 / 2) (by norm_num) i
  have h0 := bernoulli_integral_coord (1 / 2 : NNReal) (by norm_num)
  rw [uniformMeasure, h.integral_eq]
  rw [h0]
  norm_num

/-- A centred coordinate is sub-Gaussian with variance proxy `1/4`. -/
lemma hasSubgaussian_centered (i : ℕ) :
    HasSubgaussianMGF (fun w : CantorSeq => bitVal (w i) - 1 / 2) (1 / 4 : ℝ≥0)
      uniformMeasure := by
  have hm : AEMeasurable (fun w : CantorSeq => bitVal (w i)) uniformMeasure :=
    (measurable_bitVal.comp (measurable_pi_apply i)).aemeasurable
  have hb : ∀ᵐ w ∂uniformMeasure, bitVal (w i) ∈ Set.Icc (0 : ℝ) 1 := by
    filter_upwards with w
    cases w i <;> simp [bitVal]
  have h := hasSubgaussianMGF_of_mem_Icc (μ := uniformMeasure)
    (X := fun w : CantorSeq => bitVal (w i)) hm hb
  rw [uniform_integral_bitVal i] at h
  have hc : ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2 : ℝ≥0) = (1 / 4 : ℝ≥0) := by
    simp
    norm_num
  rwa [hc] at h

/-- The centred coordinates are independent under the uniform measure. -/
lemma iIndepFun_centered :
    iIndepFun (fun (i : ℕ) (w : CantorSeq) => bitVal (w i) - 1 / 2) uniformMeasure := by
  have h := bernoulli_iIndepFun (1 / 2) (by norm_num)
  have h2 := h.comp (fun (_ : ℕ) (x : ℝ) => x - 1 / 2) (fun _ => measurable_id.sub_const _)
  change iIndepFun (fun (i : ℕ) => (fun x : ℝ => x - 1 / 2) ∘ fun w => bitVal (w i)) uniformMeasure
  simpa only [uniformMeasure] using h2

/-- The negatives of the centred coordinates are independent under the uniform measure. -/
lemma iIndepFun_centered_neg :
    iIndepFun (fun (i : ℕ) (w : CantorSeq) => 1 / 2 - bitVal (w i)) uniformMeasure := by
  have h := bernoulli_iIndepFun (1 / 2) (by norm_num)
  have h2 := h.comp (fun (_ : ℕ) (x : ℝ) => 1 / 2 - x)
    (fun _ => (measurable_const.sub measurable_id))
  change iIndepFun (fun (i : ℕ) => (fun x : ℝ => 1 / 2 - x) ∘ fun w => bitVal (w i)) uniformMeasure
  simpa only [uniformMeasure] using h2

/-- The negative of a centred coordinate is sub-Gaussian with variance proxy `1/4`. -/
lemma hasSubgaussian_centered_neg (i : ℕ) :
    HasSubgaussianMGF (fun w : CantorSeq => 1 / 2 - bitVal (w i)) (1 / 4 : ℝ≥0)
      uniformMeasure := by
  have h := (hasSubgaussian_centered i).neg
  have heq : (-(fun w : CantorSeq => bitVal (w i) - 1 / 2))
      = fun w : CantorSeq => 1 / 2 - bitVal (w i) := by
    funext w; simp [neg_sub]
  rwa [heq] at h

/-- Hoeffding's bound: for independent sub-Gaussian summands the probability that the sum of the
first `n` reaches `n / (k+1)` is at most `exp(-2n / (k+1)²)`. -/
lemma measureReal_sum_ge (μ : Measure CantorSeq) (k n : ℕ) (X : ℕ → CantorSeq → ℝ)
    (hind : iIndepFun X μ)
    (hsub : ∀ i, HasSubgaussianMGF (X i) (1 / 4 : ℝ≥0) μ) :
    μ.real {w | (n : ℝ) / ((k : ℝ) + 1) ≤ ∑ i ∈ Finset.range n, X i w}
      ≤ Real.exp (-(2 * n) / ((k : ℝ) + 1) ^ 2) := by
  have hε : (0 : ℝ) ≤ (n : ℝ) / ((k : ℝ) + 1) := by positivity
  have h := HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun (n := n) hind
    (fun i _ => hsub i) hε
  refine h.trans (le_of_eq ?_)
  congr 1
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · norm_num
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    push_cast
    field_simp
    ring

/-- A deviation of the empirical frequency forces a large deviation of the centred sum in one of
the two directions. -/
lemma devSet_subset_union (k n : ℕ) :
    devSet k n
      ⊆ {w : CantorSeq |
            (n : ℝ) / ((k : ℝ) + 1) ≤ ∑ i ∈ Finset.range n, (bitVal (w i) - 1 / 2)}
        ∪ {w : CantorSeq |
            (n : ℝ) / ((k : ℝ) + 1) ≤ ∑ i ∈ Finset.range n, (1 / 2 - bitVal (w i))} := by
  intro w hw
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · left; simp
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  set c := (cantorPrefix w n).count true with hc
  have hq : (1 : ℚ) / (k + 1) ≤ |(c : ℚ) / n - 1 / 2| := (devBool_iff_rat k n c hn).1 hw
  have hr : (1 : ℝ) / ((k : ℝ) + 1) ≤ |(c : ℝ) / n - 1 / 2| := by
    have h := (Rat.cast_le (K := ℝ)).2 hq
    push_cast at h
    exact h
  have hsum1 : ∑ i ∈ Finset.range n, (bitVal (w i) - 1 / 2) = (c : ℝ) - n / 2 := by
    rw [Finset.sum_sub_distrib, sum_bitVal_eq_count, ← hc, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
    ring
  have hsum2 : ∑ i ∈ Finset.range n, ((1 : ℝ) / 2 - bitVal (w i)) = (n : ℝ) / 2 - c := by
    rw [Finset.sum_sub_distrib, sum_bitVal_eq_count, ← hc, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
    ring
  rcases le_abs.1 hr with h | h
  · left
    have h2 : (n : ℝ) * (1 / ((k : ℝ) + 1)) ≤ (n : ℝ) * ((c : ℝ) / n - 1 / 2) :=
      mul_le_mul_of_nonneg_left h hn'.le
    have h3 : (n : ℝ) * ((c : ℝ) / n - 1 / 2) = (c : ℝ) - n / 2 := by
      field_simp
    have h4 : (n : ℝ) * (1 / ((k : ℝ) + 1)) = (n : ℝ) / ((k : ℝ) + 1) := by ring
    change (n : ℝ) / ((k : ℝ) + 1) ≤ _
    rw [hsum1]
    linarith
  · right
    have h2 : (n : ℝ) * (1 / ((k : ℝ) + 1)) ≤ (n : ℝ) * (-((c : ℝ) / n - 1 / 2)) :=
      mul_le_mul_of_nonneg_left h hn'.le
    have h3 : (n : ℝ) * (-((c : ℝ) / n - 1 / 2)) = (n : ℝ) / 2 - c := by
      field_simp; ring
    have h4 : (n : ℝ) * (1 / ((k : ℝ) + 1)) = (n : ℝ) / ((k : ℝ) + 1) := by ring
    change (n : ℝ) / ((k : ℝ) + 1) ≤ _
    rw [hsum2]
    linarith

/-- The deviation sets have uniform measure at most `2 exp(-2n / (k+1)²)`. -/
lemma measure_devSet_le (k n : ℕ) :
    uniformMeasure (devSet k n)
      ≤ ENNReal.ofReal (2 * Real.exp (-(2 * n) / ((k : ℝ) + 1) ^ 2)) := by
  set A : Set CantorSeq :=
    {w : CantorSeq | (n : ℝ) / ((k : ℝ) + 1) ≤ ∑ i ∈ Finset.range n, (bitVal (w i) - 1 / 2)}
    with hA
  set B : Set CantorSeq :=
    {w : CantorSeq | (n : ℝ) / ((k : ℝ) + 1) ≤ ∑ i ∈ Finset.range n, (1 / 2 - bitVal (w i))}
    with hB
  have hAle : uniformMeasure A ≤ ENNReal.ofReal (Real.exp (-(2 * n) / ((k : ℝ) + 1) ^ 2)) := by
    have h := measureReal_sum_ge uniformMeasure k n (fun i w => bitVal (w i) - 1 / 2)
      iIndepFun_centered hasSubgaussian_centered
    have hfin : uniformMeasure A ≠ ⊤ := measure_ne_top _ _
    calc uniformMeasure A = ENNReal.ofReal (uniformMeasure.real A) :=
          (ENNReal.ofReal_toReal hfin).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal h
  have hBle : uniformMeasure B ≤ ENNReal.ofReal (Real.exp (-(2 * n) / ((k : ℝ) + 1) ^ 2)) := by
    have h := measureReal_sum_ge uniformMeasure k n (fun i w => 1 / 2 - bitVal (w i))
      iIndepFun_centered_neg hasSubgaussian_centered_neg
    have hfin : uniformMeasure B ≠ ⊤ := measure_ne_top _ _
    calc uniformMeasure B = ENNReal.ofReal (uniformMeasure.real B) :=
          (ENNReal.ofReal_toReal hfin).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal h
  have hsub : uniformMeasure (devSet k n) ≤ uniformMeasure (A ∪ B) :=
    measure_mono (devSet_subset_union k n)
  refine hsub.trans ?_
  refine (measure_union_le A B).trans ?_
  have hexp : (0 : ℝ) ≤ Real.exp (-(2 * n) / ((k : ℝ) + 1) ^ 2) := (Real.exp_pos _).le
  calc uniformMeasure A + uniformMeasure B
      ≤ ENNReal.ofReal (Real.exp (-(2 * n) / ((k : ℝ) + 1) ^ 2))
        + ENNReal.ofReal (Real.exp (-(2 * n) / ((k : ℝ) + 1) ^ 2)) := add_le_add hAle hBle
    _ = ENNReal.ofReal (2 * Real.exp (-(2 * n) / ((k : ℝ) + 1) ^ 2)) := by
        rw [← ENNReal.ofReal_add hexp hexp]
        ring_nf

/-! ### Tail unions of deviation sets -/

/-- The threshold from which the tail union of the level-`k` deviation sets has
measure at most `2⁻ᵐ`. -/
def devThresh (k m : ℕ) : ℕ := (k + 1) ^ 2 * (m + 2 * k + 4)

/-- The tail union of the level-`k` deviation sets from `devThresh k m` on. -/
def devUnion (k m : ℕ) : Set CantorSeq := ⋃ j : ℕ, devSet k (devThresh k m + j)

/-- `exp 2 ≤ 8`. -/
lemma exp_two_le_eight : Real.exp 2 ≤ 8 := by
  have h : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h0 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  nlinarith [h, h0]

/-- `2 ≤ exp 2`. -/
lemma two_le_exp_two : (2 : ℝ) ≤ Real.exp 2 := by
  have h := Real.add_one_le_exp (1 : ℝ)
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  nlinarith [Real.exp_pos 1]

/-- The exponential term written as a geometric sequence. -/
lemma exp_term_eq (k T : ℕ) (j : ℕ) :
    (2 : ℝ) * Real.exp (-(2 * ((T : ℝ) + j)) / ((k : ℝ) + 1) ^ 2)
      = (2 * Real.exp (-(2 * (T : ℝ)) / ((k : ℝ) + 1) ^ 2))
        * (Real.exp (-(2 / ((k : ℝ) + 1) ^ 2))) ^ j := by
  have hk : ((k : ℝ) + 1) ^ 2 ≠ 0 := by positivity
  have harg : -(2 * ((T : ℝ) + j)) / ((k : ℝ) + 1) ^ 2
      = -(2 * (T : ℝ)) / ((k : ℝ) + 1) ^ 2 + (j : ℝ) * -(2 / ((k : ℝ) + 1) ^ 2) := by ring
  rw [← Real.exp_nat_mul, mul_assoc, ← Real.exp_add, ← harg]

/-- The geometric tail of the Hoeffding bounds is summable. -/
lemma expTail_summable (k T : ℕ) :
    Summable (fun j : ℕ => (2 : ℝ) * Real.exp (-(2 * ((T : ℝ) + j)) / ((k : ℝ) + 1) ^ 2)) := by
  have hq : |Real.exp (-(2 / ((k : ℝ) + 1) ^ 2))| < 1 := by
    rw [abs_of_pos (Real.exp_pos _)]
    apply Real.exp_lt_one_iff.2
    have : (0 : ℝ) < 2 / ((k : ℝ) + 1) ^ 2 := by positivity
    linarith
  have := (summable_geometric_of_abs_lt_one hq).mul_left
    (2 * Real.exp (-(2 * (T : ℝ)) / ((k : ℝ) + 1) ^ 2))
  exact this.congr (fun j => (exp_term_eq k T j).symm)

/-- The tail of the Hoeffding bounds sums to a geometric series in closed form. -/
lemma expTail_sum_eq (k T : ℕ) :
    ∑' j : ℕ, (2 : ℝ) * Real.exp (-(2 * ((T : ℝ) + j)) / ((k : ℝ) + 1) ^ 2)
      = (2 * Real.exp (-(2 * (T : ℝ)) / ((k : ℝ) + 1) ^ 2))
        * (1 - Real.exp (-(2 / ((k : ℝ) + 1) ^ 2)))⁻¹ := by
  have hq : |Real.exp (-(2 / ((k : ℝ) + 1) ^ 2))| < 1 := by
    rw [abs_of_pos (Real.exp_pos _)]
    apply Real.exp_lt_one_iff.2
    have : (0 : ℝ) < 2 / ((k : ℝ) + 1) ^ 2 := by positivity
    linarith
  calc ∑' j : ℕ, (2 : ℝ) * Real.exp (-(2 * ((T : ℝ) + j)) / ((k : ℝ) + 1) ^ 2)
      = ∑' j : ℕ, (2 * Real.exp (-(2 * (T : ℝ)) / ((k : ℝ) + 1) ^ 2))
          * (Real.exp (-(2 / ((k : ℝ) + 1) ^ 2))) ^ j := by
        exact tsum_congr (fun j => exp_term_eq k T j)
    _ = (2 * Real.exp (-(2 * (T : ℝ)) / ((k : ℝ) + 1) ^ 2))
          * ∑' j : ℕ, (Real.exp (-(2 / ((k : ℝ) + 1) ^ 2))) ^ j := by
        rw [tsum_mul_left]
    _ = _ := by rw [tsum_geometric_of_lt_one (Real.exp_pos _).le
          (by rw [← abs_of_pos (Real.exp_pos (-(2 / ((k : ℝ) + 1) ^ 2)))]; exact hq)]

/-- `exp(-2) ≤ 1/2`. -/
lemma exp_neg_two_le_half : Real.exp (-2 : ℝ) ≤ 1 / 2 := by
  have hmul : Real.exp (-2 : ℝ) * Real.exp 2 = 1 := by
    rw [← Real.exp_add]; norm_num
  nlinarith [Real.exp_pos (-2 : ℝ), two_le_exp_two, hmul]

/-- `1/8 ≤ exp(-2)`. -/
lemma one_eighth_le_exp_neg_two : (1 : ℝ) / 8 ≤ Real.exp (-2 : ℝ) := by
  have hmul : Real.exp (-2 : ℝ) * Real.exp 2 = 1 := by
    rw [← Real.exp_add]; norm_num
  nlinarith [Real.exp_pos (-2 : ℝ), exp_two_le_eight, hmul]

/-- `exp(-2m) ≤ 2^{-m}` for every natural number `m`. -/
lemma exp_neg_two_mul_le (m : ℕ) : Real.exp (-(2 * (m : ℝ))) ≤ (1 / 2) ^ m := by
  have hrw : Real.exp (-(2 * (m : ℝ))) = (Real.exp (-2)) ^ m := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  rw [hrw]
  exact pow_le_pow_left₀ (Real.exp_pos _).le exp_neg_two_le_half m

/-- `8(k+1)² ≤ exp(4k + 8)`, the estimate that makes the chosen thresholds work. -/
lemma eight_sq_le_exp (k : ℕ) : 8 * ((k : ℝ) + 1) ^ 2 ≤ Real.exp (4 * (k : ℝ) + 8) := by
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hk1 : (k : ℝ) + 1 ≤ Real.exp (k : ℝ) := by
    have := Real.add_one_le_exp (k : ℝ); linarith
  have hsq : ((k : ℝ) + 1) ^ 2 ≤ Real.exp (2 * (k : ℝ)) := by
    have h : Real.exp (2 * (k : ℝ)) = Real.exp (k : ℝ) * Real.exp (k : ℝ) := by
      rw [← Real.exp_add]; ring_nf
    rw [h]; nlinarith [Real.exp_pos (k : ℝ)]
  have h8 : (8 : ℝ) ≤ Real.exp 8 := by
    have h : Real.exp 8 = (Real.exp 2) ^ 4 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [h]
    have h16 : (2 : ℝ) ^ 4 ≤ Real.exp 2 ^ 4 := pow_le_pow_left₀ (by norm_num) two_le_exp_two 4
    norm_num at h16 ⊢
    linarith
  calc 8 * ((k : ℝ) + 1) ^ 2 ≤ Real.exp 8 * Real.exp (2 * (k : ℝ)) :=
        mul_le_mul h8 hsq (by positivity) (Real.exp_pos _).le
    _ = Real.exp (8 + 2 * (k : ℝ)) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (4 * (k : ℝ) + 8) := Real.exp_le_exp.2 (by linarith)

/-- Beyond the threshold `T = (k+1)²(m + 2k + 4)` the tail of the Hoeffding bounds is at most
`2^{-m}`. -/
lemma expTail_le (k m T : ℕ)
    (hT : (T : ℝ) = ((k : ℝ) + 1) ^ 2 * ((m : ℝ) + 2 * k + 4)) :
    ∑' j : ℕ, (2 : ℝ) * Real.exp (-(2 * ((T : ℝ) + j)) / ((k : ℝ) + 1) ^ 2)
      ≤ (1 / 2) ^ m := by
  set u : ℝ := 2 / ((k : ℝ) + 1) ^ 2 with hu
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hkpos : (0 : ℝ) < ((k : ℝ) + 1) ^ 2 := by positivity
  have hupos : 0 < u := by rw [hu]; positivity
  have hule : u ≤ 2 := by
    rw [hu, div_le_iff₀ hkpos]; nlinarith
  have hq8 : (1 : ℝ) / 8 ≤ Real.exp (-u) := by
    have h1 : Real.exp (-2 : ℝ) ≤ Real.exp (-u) := Real.exp_le_exp.2 (by linarith)
    linarith [one_eighth_le_exp_neg_two]
  have hone : u * Real.exp (-u) ≤ 1 - Real.exp (-u) := by
    have h := Real.add_one_le_exp u
    have hmul : Real.exp (-u) * Real.exp u = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (-u), Real.exp_pos u]
  have hden : u / 8 ≤ 1 - Real.exp (-u) := by nlinarith
  have hdenpos : (0 : ℝ) < 1 - Real.exp (-u) := lt_of_lt_of_le (by positivity) hden
  have hinv : (1 - Real.exp (-u))⁻¹ ≤ 8 / u := by
    have h := inv_anti₀ (show (0:ℝ) < u / 8 by positivity) hden
    calc (1 - Real.exp (-u))⁻¹ ≤ (u / 8)⁻¹ := h
      _ = 8 / u := by rw [inv_div]
  have hexpT : Real.exp (-(2 * (T : ℝ)) / ((k : ℝ) + 1) ^ 2)
      = Real.exp (-(2 * ((m : ℝ) + 2 * k + 4))) := by
    congr 1
    rw [hT]
    field_simp
  have hEpos : (0 : ℝ) ≤ Real.exp (-(2 * ((m : ℝ) + 2 * k + 4))) := (Real.exp_pos _).le
  rw [expTail_sum_eq k T, hexpT]
  have hstep : 2 * Real.exp (-(2 * ((m : ℝ) + 2 * k + 4))) * (1 - Real.exp (-u))⁻¹
      ≤ 2 * Real.exp (-(2 * ((m : ℝ) + 2 * k + 4))) * (8 / u) := by
    apply mul_le_mul_of_nonneg_left hinv (by positivity)
  refine hstep.trans ?_
  have h8u : 8 / u = 4 * ((k : ℝ) + 1) ^ 2 := by
    rw [hu]; field_simp; ring
  rw [h8u]
  have hsplit : Real.exp (-(2 * ((m : ℝ) + 2 * k + 4)))
      = Real.exp (-(4 * (k : ℝ) + 8)) * Real.exp (-(2 * (m : ℝ))) := by
    rw [← Real.exp_add]; congr 1; ring
  have hB : 8 * ((k : ℝ) + 1) ^ 2 * Real.exp (-(4 * (k : ℝ) + 8)) ≤ 1 := by
    have hne : Real.exp (-(4 * (k : ℝ) + 8)) = (Real.exp (4 * (k : ℝ) + 8))⁻¹ := by
      rw [← Real.exp_neg]
    rw [hne, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
    exact eight_sq_le_exp k
  calc 2 * Real.exp (-(2 * ((m : ℝ) + 2 * k + 4))) * (4 * ((k : ℝ) + 1) ^ 2)
      = (8 * ((k : ℝ) + 1) ^ 2 * Real.exp (-(4 * (k : ℝ) + 8)))
        * Real.exp (-(2 * (m : ℝ))) := by rw [hsplit]; ring
    _ ≤ 1 * (1 / 2) ^ m :=
        mul_le_mul hB (exp_neg_two_mul_le m) (Real.exp_pos _).le (by norm_num)
    _ = (1 / 2) ^ m := one_mul _

/-- The union of the deviation sets beyond the threshold has uniform measure at most `2^{-m}`. -/
lemma measure_devUnion_le (k m : ℕ) :
    uniformMeasure (devUnion k m) ≤ dyadicValue 1 m := by
  set T := devThresh k m with hTdef
  have hle : uniformMeasure (devUnion k m)
      ≤ ∑' j : ℕ, uniformMeasure (devSet k (T + j)) := measure_iUnion_le _
  have hterm : ∀ j : ℕ, uniformMeasure (devSet k (T + j))
      ≤ ENNReal.ofReal (2 * Real.exp (-(2 * ((T : ℝ) + j)) / ((k : ℝ) + 1) ^ 2)) := by
    intro j
    have h := measure_devSet_le k (T + j)
    push_cast at h
    exact h
  refine hle.trans ((ENNReal.tsum_le_tsum hterm).trans ?_)
  have hnonneg : ∀ j : ℕ,
      (0 : ℝ) ≤ 2 * Real.exp (-(2 * ((T : ℝ) + j)) / ((k : ℝ) + 1) ^ 2) := by
    intro j; positivity
  have hsum := (ENNReal.ofReal_tsum_of_nonneg hnonneg (expTail_summable k T)).symm
  rw [hsum]
  have hT : (T : ℝ) = ((k : ℝ) + 1) ^ 2 * ((m : ℝ) + 2 * k + 4) := by
    rw [hTdef, devThresh]; push_cast; ring
  have hb := expTail_le k m T hT
  refine (ENNReal.ofReal_le_ofReal hb).trans ?_
  rw [dyadicValue_one_eq_inv_two_pow']
  rw [show ((1 : ℝ) / 2) = (2 : ℝ)⁻¹ by norm_num, ENNReal.ofReal_pow (by norm_num),
    ENNReal.ofReal_inv_of_pos (by norm_num)]
  norm_num

/-! ### Enumerating the strings of a given length -/

/-- Auxiliary recursion producing, from `n` and `i`, the number `i / 2 ^ n`, the
big-endian `n`-bit representation of `i`, and its number of ones. -/
def bitsAux (n i : ℕ) : ℕ × BitString × ℕ :=
  Nat.rec (motive := fun _ => ℕ × BitString × ℕ) (i, [], 0)
    (fun _ p => (p.1 / 2, (p.1 % 2 == 1) :: p.2.1, p.2.2 + p.1 % 2)) n

/-- The bit-extraction loop starts from the number itself with no bits read. -/
@[simp] lemma bitsAux_zero (i : ℕ) : bitsAux 0 i = (i, [], 0) := rfl

/-- Each step of the bit-extraction loop halves the number, prepends the extracted bit and
updates the count of ones. -/
@[simp] lemma bitsAux_succ (n i : ℕ) :
    bitsAux (n + 1) i =
      ((bitsAux n i).1 / 2, ((bitsAux n i).1 % 2 == 1) :: (bitsAux n i).2.1,
        (bitsAux n i).2.2 + (bitsAux n i).1 % 2) := rfl

/-- The big-endian `n`-bit representation of `i`. -/
def natToBits (n i : ℕ) : BitString := (bitsAux n i).2.1

/-- No bits are extracted at length zero. -/
@[simp] lemma natToBits_zero (i : ℕ) : natToBits 0 i = [] := rfl

/-- The length-`n+1` binary expansion prepends the next bit to the length-`n` one. -/
lemma natToBits_succ (n i : ℕ) :
    natToBits (n + 1) i = ((bitsAux n i).1 % 2 == 1) :: natToBits n i := rfl

/-- The length-`n` binary expansion of a number has length `n`. -/
@[simp] lemma natToBits_length (n i : ℕ) : (natToBits n i).length = n := by
  induction n with
  | zero => simp
  | succ n ih => rw [natToBits_succ, List.length_cons, ih]

/-- After `n` steps the bit-extraction loop holds `i / 2^n`. -/
lemma bitsAux_fst (n i : ℕ) : (bitsAux n i).1 = i / 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [bitsAux_succ, ih, Nat.div_div_eq_div_mul, pow_succ]

/-- The counter of the bit-extraction loop counts the ones of the extracted string. -/
lemma bitsAux_count (n i : ℕ) : (bitsAux n i).2.2 = (natToBits n i).count true := by
  induction n with
  | zero => simp [natToBits]
  | succ n ih =>
    rw [bitsAux_succ, natToBits_succ, List.count_cons, ih]
    have hmod : (bitsAux n i).1 % 2 = 0 ∨ (bitsAux n i).1 % 2 = 1 := by omega
    rcases hmod with h | h <;> simp [h]

/-- The length-`n` binary expansion only depends on the number modulo `2^n`. -/
lemma natToBits_add_mul (n i v : ℕ) : natToBits n (i + v * 2 ^ n) = natToBits n i := by
  induction n generalizing i v with
  | zero => simp
  | succ n ih =>
    rw [natToBits_succ, natToBits_succ, bitsAux_fst, bitsAux_fst]
    have hpow : (0 : ℕ) < 2 ^ n := pow_pos (by norm_num : (0:ℕ) < 2) n
    have h1 : (i + v * 2 ^ (n + 1)) / 2 ^ n = i / 2 ^ n + 2 * v := by
      have : i + v * 2 ^ (n + 1) = i + (2 * v) * 2 ^ n := by ring
      rw [this, Nat.add_mul_div_right _ _ hpow]
    have h2 : natToBits n (i + v * 2 ^ (n + 1)) = natToBits n i := by
      have : i + v * 2 ^ (n + 1) = i + (2 * v) * 2 ^ n := by ring
      rw [this, ih]
    rw [h1, h2]
    congr 2
    omega

/-- The number encoded by a bit string, most significant bit first. -/
def devBitsToNat : BitString → ℕ
  | [] => 0
  | b :: t => (if b then 1 else 0) * 2 ^ t.length + devBitsToNat t

/-- The number coded by a bit string of length `n` is below `2^n`. -/
lemma bitsToNat_lt (s : BitString) : devBitsToNat s < 2 ^ s.length := by
  induction s with
  | nil => simp [devBitsToNat]
  | cons b t ih =>
    rw [devBitsToNat, List.length_cons, pow_succ]
    have hb : (if b then 1 else 0) ≤ 1 := by split <;> omega
    have hpow : (0 : ℕ) < 2 ^ t.length := pow_pos (by norm_num : (0:ℕ) < 2) _
    nlinarith [ih, hb, hpow]

/-- Decoding the number coded by a bit string returns the string. -/
lemma natToBits_bitsToNat (s : BitString) : natToBits s.length (devBitsToNat s) = s := by
  induction s with
  | nil => simp
  | cons b t ih =>
    have hpow : (0 : ℕ) < 2 ^ t.length := pow_pos (by norm_num : (0:ℕ) < 2) _
    have hval : devBitsToNat (b :: t) = devBitsToNat t + (if b then 1 else 0) * 2 ^ t.length := by
      rw [devBitsToNat]; ring
    rw [List.length_cons, natToBits_succ, bitsAux_fst, hval, natToBits_add_mul, ih]
    have hdiv : (devBitsToNat t + (if b then 1 else 0) * 2 ^ t.length) / 2 ^ t.length
        = (if b then 1 else 0) := by
      rw [Nat.add_mul_div_right _ _ hpow, Nat.div_eq_of_lt (bitsToNat_lt t), zero_add]
    rw [hdiv]
    cases b <;> simp

/-- Every bit string is the binary expansion of some natural number. -/
lemma exists_natToBits (s : BitString) : ∃ i, natToBits s.length i = s :=
  ⟨devBitsToNat s, natToBits_bitsToNat s⟩

/-- The bit-extraction loop is computable. -/
lemma computable_bitsAux : Computable₂ bitsAux := by
  have hstep : Computable₂ (fun (_ : ℕ × ℕ) (p : ℕ × (ℕ × BitString × ℕ)) =>
      (p.2.1 / 2, ((p.2.1 % 2 == 1) :: p.2.2.1, p.2.2.2 + p.2.1 % 2))) := by
    have hr : Computable (fun q : (ℕ × ℕ) × (ℕ × (ℕ × BitString × ℕ)) => q.2.2.1) :=
      Computable.fst.comp (Computable.snd.comp Computable.snd)
    have hdiv : Computable (fun q : (ℕ × ℕ) × (ℕ × (ℕ × BitString × ℕ)) => q.2.2.1 / 2) :=
      Primrec.nat_div.to_comp.comp hr (Computable.const 2)
    have hmod : Computable (fun q : (ℕ × ℕ) × (ℕ × (ℕ × BitString × ℕ)) => q.2.2.1 % 2) :=
      Primrec.nat_mod.to_comp.comp hr (Computable.const 2)
    have hbit : Computable (fun q : (ℕ × ℕ) × (ℕ × (ℕ × BitString × ℕ)) =>
        (q.2.2.1 % 2 == 1)) := Primrec.beq.to_comp.comp hmod (Computable.const 1)
    have hlist : Computable (fun q : (ℕ × ℕ) × (ℕ × (ℕ × BitString × ℕ)) => q.2.2.2.1) :=
      Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
    have hcnt : Computable (fun q : (ℕ × ℕ) × (ℕ × (ℕ × BitString × ℕ)) => q.2.2.2.2) :=
      Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
    exact (Computable.pair hdiv
      (Computable.pair (Computable.list_cons.comp hbit hlist)
        (Primrec.nat_add.to_comp.comp hcnt hmod)))
  exact Computable.nat_rec (α := ℕ × ℕ) (σ := ℕ × BitString × ℕ)
    (f := fun a : ℕ × ℕ => a.1)
    (g := fun a : ℕ × ℕ => (a.2, [], 0))
    (h := fun (_ : ℕ × ℕ) (p : ℕ × (ℕ × BitString × ℕ)) =>
      (p.2.1 / 2, ((p.2.1 % 2 == 1) :: p.2.2.1, p.2.2.2 + p.2.1 % 2)))
    Computable.fst
    (Computable.pair Computable.snd (Computable.pair (Computable.const []) (Computable.const 0)))
    hstep

/-- The deviation test is computable in the accuracy level, the length and the count. -/
lemma computable_devBool {α : Type} [Primcodable α] {k n c : α → ℕ}
    (hk : Computable k) (hn : Computable n) (hc : Computable c) :
    Computable (fun a => devBool (k a) (n a) (c a)) := by
  have h2c : Computable (fun a => 2 * c a) :=
    Primrec.nat_mul.to_comp.comp (Computable.const 2) hc
  have hd1 : Computable (fun a => 2 * c a - n a) := Primrec.nat_sub.to_comp.comp h2c hn
  have hd2 : Computable (fun a => n a - 2 * c a) := Primrec.nat_sub.to_comp.comp hn h2c
  have hdiff : Computable (fun a => natAbsDiff (2 * c a) (n a)) :=
    Primrec.nat_add.to_comp.comp hd1 hd2
  have hk1 : Computable (fun a => k a + 1) := Computable.succ.comp hk
  have hmul : Computable (fun a => (k a + 1) * natAbsDiff (2 * c a) (n a)) :=
    Primrec.nat_mul.to_comp.comp hk1 hdiff
  have h2n : Computable (fun a => 2 * n a) :=
    Primrec.nat_mul.to_comp.comp (Computable.const 2) hn
  have hsub : Computable (fun a => 2 * n a - (k a + 1) * natAbsDiff (2 * c a) (n a)) :=
    Primrec.nat_sub.to_comp.comp h2n hmul
  exact Primrec.beq.to_comp.comp hsub (Computable.const 0)

/-- The computable enumeration of the deviating cylinders of level `k` and length at
least `T`. -/
def devEnum (k T j : ℕ) : Option BitString :=
  bif devBool k (T + j.unpair.1) ((bitsAux (T + j.unpair.1) j.unpair.2).2.2)
    then some ((bitsAux (T + j.unpair.1) j.unpair.2).2.1) else none

/-- Guarding a computable value by a computable boolean. -/
lemma Computable.cond_some_none {α σ : Type} [Primcodable α] [Primcodable σ]
    {b : α → Bool} {s : α → σ} (hb : Computable b) (hs : Computable s) :
    Computable (fun a => bif b a then some (s a) else none) :=
  Computable.cond hb (Computable.option_some.comp hs) (Computable.const none)

/-- The enumeration of the cylinders making up the deviation sets is computable. -/
lemma computable_devEnum {α : Type} [Primcodable α] {k T j : α → ℕ}
    (hk : Computable k) (hT : Computable T) (hj : Computable j) :
    Computable (fun a => devEnum (k a) (T a) (j a)) := by
  have hj1 : Computable (fun a => (j a).unpair.1) :=
    (Primrec.fst.comp Primrec.unpair).to_comp.comp hj
  have hj2 : Computable (fun a => (j a).unpair.2) :=
    (Primrec.snd.comp Primrec.unpair).to_comp.comp hj
  have hn : Computable (fun a => T a + (j a).unpair.1) :=
    Primrec.nat_add.to_comp.comp hT hj1
  have haux : Computable (fun a => bitsAux (T a + (j a).unpair.1) (j a).unpair.2) :=
    computable_bitsAux.comp hn hj2
  have hcnt : Computable (fun a => (bitsAux (T a + (j a).unpair.1) (j a).unpair.2).2.2) :=
    Computable.snd.comp (Computable.snd.comp haux)
  have hstr : Computable (fun a => (bitsAux (T a + (j a).unpair.1) (j a).unpair.2).2.1) :=
    Computable.fst.comp (Computable.snd.comp haux)
  have hdev : Computable (fun a => devBool (k a) (T a + (j a).unpair.1)
      (bitsAux (T a + (j a).unpair.1) (j a).unpair.2).2.2) :=
    computable_devBool hk hn hcnt
  exact Computable.cond_some_none hdev hstr

/-- The threshold length chosen for accuracy `k` and level `m` is computable. -/
lemma computable_devThresh {α : Type} [Primcodable α] {k m : α → ℕ}
    (hk : Computable k) (hm : Computable m) :
    Computable (fun a => devThresh (k a) (m a)) := by
  have h1 : Computable (fun a => k a + 1) := Computable.succ.comp hk
  have hsq : Computable (fun a => (k a + 1) ^ 2) :=
    (Primrec.nat_mul.to_comp.comp h1 h1).of_eq (fun a => by ring)
  have h2k : Computable (fun a => 2 * k a) :=
    Primrec.nat_mul.to_comp.comp (Computable.const 2) hk
  have hsum : Computable (fun a => m a + 2 * k a) := Primrec.nat_add.to_comp.comp hm h2k
  have hsum4 : Computable (fun a => m a + 2 * k a + 4) :=
    Primrec.nat_add.to_comp.comp hsum (Computable.const 4)
  exact Primrec.nat_mul.to_comp.comp hsq hsum4

/-- Membership in the deviation set is decided by the number of ones in the length-`n` prefix. -/
lemma mem_devSet_iff_prefix (k n : ℕ) (w : CantorSeq) :
    w ∈ devSet k n ↔ devBool k n ((cantorPrefix w n).count true) = true := Iff.rfl

/-- The cylinders enumerated from stage `T` on cover exactly the union of the deviation sets of
length at least `T`. -/
lemma iUnion_devEnum (k T : ℕ) :
    (⋃ j, (devEnum k T j).elim ∅ cantorCylinder) = ⋃ j : ℕ, devSet k (T + j) := by
  ext w
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨j, hj⟩
    set n := T + j.unpair.1 with hn
    by_cases hdev : devBool k n ((bitsAux n j.unpair.2).2.2) = true
    · refine ⟨j.unpair.1, ?_⟩
      rw [devEnum] at hj
      rw [hdev] at hj
      simp only [cond_true, Option.elim_some] at hj
      have hpref : cantorPrefix w n = natToBits n j.unpair.2 := by
        have hlen : (natToBits n j.unpair.2).length = n := natToBits_length _ _
        have := (isCantorPrefix_iff_cantorPrefix_eq (natToBits n j.unpair.2) w).1 hj
        rw [hlen] at this
        exact this
      rw [mem_devSet_iff_prefix, ← hn, hpref, ← bitsAux_count]
      exact hdev
    · exfalso
      rw [devEnum] at hj
      have hfalse : devBool k n ((bitsAux n j.unpair.2).2.2) = false := by
        simpa using hdev
      rw [hfalse] at hj
      simp at hj
  · rintro ⟨j, hj⟩
    set n := T + j with hn
    rw [mem_devSet_iff_prefix] at hj
    obtain ⟨i, hi⟩ := exists_natToBits (cantorPrefix w n)
    rw [cantorPrefix_length] at hi
    refine ⟨Nat.pair j i, ?_⟩
    have hdev : devBool k n ((bitsAux n i).2.2) = true := by
      rw [bitsAux_count, hi]
      exact hj
    rw [devEnum, Nat.unpair_pair]
    simp only [← hn, hdev, cond_true, Option.elim_some]
    have : (bitsAux n i).2.1 = cantorPrefix w n := hi
    rw [this]
    exact mem_cantorCylinder_cantorPrefix w n

/-! ### The effectively null family -/

/-- The uniformly effective open family witnessing effective nullity. -/
def devW (p : ℕ) : Set CantorSeq := devUnion p.unpair.1 p.unpair.2

/-- The deviation test levels form a uniformly effectively open family. -/
lemma isUniformlyEffectiveOpen_devW : IsUniformlyEffectiveOpen devW := by
  refine ⟨fun p i => devEnum p.unpair.1 (devThresh p.unpair.1 p.unpair.2) i, ?_, fun p => ?_⟩
  · have hp1 : Computable (fun q : ℕ × ℕ => q.1.unpair.1) :=
      (Primrec.fst.comp Primrec.unpair).to_comp.comp Computable.fst
    have hp2 : Computable (fun q : ℕ × ℕ => q.1.unpair.2) :=
      (Primrec.snd.comp Primrec.unpair).to_comp.comp Computable.fst
    exact computable_devEnum hp1 (computable_devThresh hp1 hp2) Computable.snd
  · exact (iUnion_devEnum p.unpair.1 (devThresh p.unpair.1 p.unpair.2)).symm

/-- The sequences that deviate at level `k` infinitely often. -/
def devInfSet (k : ℕ) : Set CantorSeq := {x | ∀ M, ∃ n, M ≤ n ∧ x ∈ devSet k n}

/-- The set of sequences deviating infinitely often at accuracy `k` is contained in every level
of the corresponding test. -/
lemma devInfSet_subset_iInter (k : ℕ) : devInfSet k ⊆ ⋂ m, devW (Nat.pair k m) := by
  intro x hx
  refine Set.mem_iInter.2 fun m => ?_
  have hw : devW (Nat.pair k m) = devUnion k m := by simp [devW, Nat.unpair_pair]
  rw [hw]
  obtain ⟨n, hn, hxn⟩ := hx (devThresh k m)
  refine Set.mem_iUnion.2 ⟨n - devThresh k m, ?_⟩
  have hsum : devThresh k m + (n - devThresh k m) = n := by omega
  rw [hsum]
  exact hxn

/-- The sets of sequences deviating infinitely often are uniformly effectively null for the
uniform measure. -/
lemma isUniformlyEffectivelyNull_devInfSet :
    IsUniformlyEffectivelyNull uniformMeasure devInfSet := by
  refine ⟨devW, isUniformlyEffectiveOpen_devW, devInfSet_subset_iInter, fun k m => ?_⟩
  have : devW (Nat.pair k m) = devUnion k m := by
    simp [devW, Nat.unpair_pair]
  rw [this]
  exact measure_devUnion_le k m

/-- A sequence whose frequency of ones does not converge to `1/2` deviates infinitely often at
some accuracy level. -/
lemma notTendsto_subset_iUnion_devInfSet :
    {x : CantorSeq | ¬ Tendsto (fun n => freqOne x n) atTop (𝓝 (1 / 2 : ℚ))}
      ⊆ ⋃ k, devInfSet k := by
  intro x hx
  by_contra hmem
  apply hx
  simp only [Set.mem_iUnion, not_exists] at hmem
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  have hnk := hmem k
  simp only [devInfSet, Set.mem_ofPred_eq, not_forall, not_exists, not_and] at hnk
  obtain ⟨M, hM⟩ := hnk
  refine ⟨max M 1, fun n hn => ?_⟩
  have hn1 : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_right M 1) hn)
  have hnM : M ≤ n := le_trans (le_max_left M 1) hn
  have hnot : ¬ (devBool k n ((cantorPrefix x n).count true) = true) := hM n hnM
  rw [devBool_iff_rat k n _ hn1] at hnot
  push Not at hnot
  have hfreq : freqOne x n = ((cantorPrefix x n).count true : ℚ) / n := rfl
  have hq : |freqOne x n - 1 / 2| < 1 / ((k : ℚ) + 1) := by
    rw [hfreq]; exact hnot
  have hcast : |((freqOne x n : ℝ)) - 1 / 2| < 1 / ((k : ℝ) + 1) := by
    have := (Rat.cast_lt (K := ℝ)).2 hq
    push_cast at this
    simpa using this
  rw [Rat.dist_eq]
  have h12 : ((1 / 2 : ℚ) : ℝ) = 1 / 2 := by norm_num
  rw [h12]
  exact lt_trans hcast hk

/-- **SUV Theorem 32.** The set of bit sequences that do not have limit frequency
`1/2` is effectively null for the uniform measure. -/
theorem isEffectivelyNull_notTendsto_freqOne :
    IsEffectivelyNull uniformMeasure
      {x : CantorSeq | ¬ Tendsto (fun n => freqOne x n) atTop (𝓝 (1 / 2 : ℚ))} :=
  (isUniformlyEffectivelyNull_devInfSet.isEffectivelyNull_iUnion).mono
    notTendsto_subset_iUnion_devInfSet

end Kolmogorov
