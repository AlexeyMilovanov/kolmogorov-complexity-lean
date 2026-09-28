import KolmogorovMathlib.AlgorithmicRandomness.ProbabilityBounded
import KolmogorovMathlib.AlgorithmicRandomness.ExpectationBounded
import KolmogorovMathlib.AlgorithmicRandomness.NatLogPrimrec
import Mathlib.Analysis.PSeries

/-!
# Probability-bounded versus expectation-bounded tests

A randomness test may be normalised by requiring `μ{t > c} ≤ 1/c` (probability bounded) or
`∫ t dμ ≤ 1` (expectation bounded).  Halving an expectation-bounded test makes it probability
bounded (`isProbabilityBounded_of_expectationBounded`); the converse fails, and this module
proves the sharp form of what does hold.

The construction is the *band transform* `bandTransform`: the weighted sum of the indicators
of the dyadic superlevel sets of a test, with weights `bandWeight k = 1 / ((k+1)(log₂(k+1)+1)²)`
chosen summable but decaying slower than any power.  `isLowerSemicomputableFun_bandTransform`
and `lintegral_bandTransform_le` show the transform of a probability-bounded test is an
expectation-bounded test, and `le_bandTransform_mul_logarithmicCorrection` bounds the original
test by the transform times `logarithmicCorrection`.

The conclusions are `deficiency_bounds` — the maximal expectation-bounded test is dominated by
the maximal probability-bounded one up to a constant, and conversely up to a squared
logarithmic correction — and `deficiency_bounds_sharp`, which does the converse with a
logarithmic correction of any exponent greater than one.
-/

namespace Kolmogorov

open MeasureTheory Topology
open scoped ENNReal NNReal

/-- A total logarithmic correction on `ℝ≥0∞`.  Taking `max 1` implements the
source's harmless correction at small values, while the explicit top branch
preserves the intended asymptotics at infinite test values. -/
noncomputable def logarithmicCorrection (a : ℝ) (x : ℝ≥0∞) : ℝ≥0∞ :=
  if x = ∞ then ∞ else
    (ENNReal.ofReal (max 1 (Real.log x.toReal))) ^ a

/-- The weight `1 / ((k+1)(log₂(k+1)+1)²)` of the `k`-th band, chosen so that the weights are
summable while decaying only logarithmically faster than `1/k`. -/
def bandWeight (k : ℕ) : ℚ := 1 / (((k : ℚ) + 1) * ((Nat.log 2 (k + 1) : ℚ) + 1) ^ 2)

/-- The band transform of a test: the weighted sum of the indicators of its dyadic superlevel
sets, turning a probability-bounded test into an expectation-bounded one. -/
noncomputable def bandTransform (u : CantorSeq → ℝ≥0∞) (w : CantorSeq) : ℝ≥0∞ :=
  1 + ∑' k : ℕ, Set.indicator {x | (2 : ℝ≥0∞) ^ k < u x}
        (fun _ => ENNReal.ofReal ((bandWeight k : ℝ)) * 2 ^ k) w

/-- Half an expectation-bounded randomness test is a probability-bounded randomness test; this is
the easy direction of the comparison, by Markov's inequality. -/
lemma isProbabilityBounded_of_expectationBounded {μ : Measure CantorSeq} {u : CantorSeq → ℝ≥0∞}
    (hu : IsExpectationBoundedRandomnessTest μ u) :
    IsProbabilityBoundedRandomnessTest μ (fun w => ENNReal.ofReal ((1 / 2 : ℚ) : ℝ) * u w) := by
  obtain ⟨hLSC, hint⟩ := hu
  refine ⟨hLSC.rat_smul (by norm_num), ?_⟩
  intro c hc
  have hc' : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  have humeas : Measurable u := hLSC.measurable
  have hofc0 : ENNReal.ofReal (c : ℝ) ≠ 0 := (ENNReal.ofReal_pos.2 hc').ne'
  have hofct : ENNReal.ofReal (c : ℝ) ≠ ⊤ := ENNReal.ofReal_ne_top
  set half : ℝ≥0∞ := ENNReal.ofReal ((1 / 2 : ℚ) : ℝ) with hhalf
  change μ {w | ENNReal.ofReal (c : ℝ) < half * u w} < (ENNReal.ofReal (c : ℝ))⁻¹
  have hgmeas : Measurable (fun w => half * u w) := humeas.const_mul half
  have hintg : ∫⁻ w, half * u w ∂μ ≤ half := by
    rw [lintegral_const_mul half humeas]
    calc half * ∫⁻ w, u w ∂μ ≤ half * 1 := mul_le_mul_right hint half
      _ = half := mul_one half
  have hmarkov := mul_meas_ge_le_lintegral (μ := μ) hgmeas (ENNReal.ofReal (c : ℝ))
  have hkey : ENNReal.ofReal (c : ℝ) * μ {w | ENNReal.ofReal (c : ℝ) < half * u w} ≤ half := by
    calc ENNReal.ofReal (c : ℝ) * μ {w | ENNReal.ofReal (c : ℝ) < half * u w}
        ≤ ENNReal.ofReal (c : ℝ) * μ {w | ENNReal.ofReal (c : ℝ) ≤ half * u w} := by
          apply mul_le_mul_right
          apply measure_mono
          intro w hw
          rw [Set.mem_setOf_eq] at hw ⊢
          exact le_of_lt hw
      _ ≤ ∫⁻ w, half * u w ∂μ := hmarkov
      _ ≤ half := hintg
  have hhalflt1 : half < 1 := by rw [hhalf]; exact ENNReal.ofReal_lt_one.2 (by norm_num)
  have hlt1 : ENNReal.ofReal (c : ℝ) * μ {w | ENNReal.ofReal (c : ℝ) < half * u w} < 1 :=
    lt_of_le_of_lt hkey hhalflt1
  have hinv0 : (ENNReal.ofReal (c : ℝ))⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 hofct
  have hinvt : (ENNReal.ofReal (c : ℝ))⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 hofc0
  have hfinal := ENNReal.mul_lt_mul_left hinv0 hinvt hlt1
  rw [one_mul, mul_right_comm, ENNReal.mul_inv_cancel hofc0 hofct, one_mul] at hfinal
  exact hfinal

/-- The band weights form a computable sequence of rationals. -/
lemma computable_bandWeight : Computable bandWeight := by
  have hD : Computable
      (fun k : ℕ => (k + 1) * ((Nat.log 2 (k + 1) + 1) * (Nat.log 2 (k + 1) + 1))) := by
    have hk : Primrec (fun k : ℕ => k + 1) := Primrec.succ
    have hl : Primrec (fun k : ℕ => Nat.log 2 (k + 1) + 1) :=
      Primrec.succ.comp (primrec_natLogTwo.comp Primrec.succ)
    exact (Primrec.nat_mul.comp hk (Primrec.nat_mul.comp hl hl)).to_comp
  refine computable_of_num_den (Computable.const (1 : ℤ)) hD
    (fun k => Nat.mul_pos (Nat.succ_pos k) (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _))) ?_
  intro k
  unfold bandWeight
  push_cast
  ring
/-- Every band weight is positive. -/
lemma bandWeight_pos (k : ℕ) : 0 < bandWeight k := by
  unfold bandWeight
  positivity
/-- The band weight, read in the reals. -/
lemma bandWeight_real (k : ℕ) :
    ((bandWeight k : ℚ) : ℝ) = 1 / (((k : ℝ) + 1) * ((Nat.log 2 (k + 1) : ℝ) + 1) ^ 2) := by
  unfold bandWeight
  push_cast
  ring

/-- The band weights are nonnegative reals. -/
lemma bandWeight_real_nonneg (k : ℕ) : 0 ≤ ((bandWeight k : ℚ) : ℝ) := by
  rw [bandWeight_real]; positivity

/-- The band weights decrease with the index. -/
lemma bandWeight_real_antitone {m n : ℕ} (h : m ≤ n) :
    ((bandWeight n : ℚ) : ℝ) ≤ ((bandWeight m : ℚ) : ℝ) := by
  rw [bandWeight_real, bandWeight_real]
  apply one_div_le_one_div_of_le
  · positivity
  · have h1 : ((m : ℝ) + 1) ≤ ((n : ℝ) + 1) := by
      have : (m : ℝ) ≤ n := by exact_mod_cast h
      linarith
    have h2 : (Nat.log 2 (m + 1) : ℝ) ≤ (Nat.log 2 (n + 1) : ℝ) := by
      exact_mod_cast Nat.log_mono_right (by omega : m + 1 ≤ n + 1)
    have h3 : ((Nat.log 2 (m + 1) : ℝ) + 1) ^ 2 ≤ ((Nat.log 2 (n + 1) : ℝ) + 1) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    have hm0 : (0:ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hpos : (0:ℝ) < ((Nat.log 2 (m + 1) : ℝ) + 1) ^ 2 := by positivity
    nlinarith

/-- The band weights are summable. -/
lemma summable_bandWeight_real : Summable (fun k : ℕ => ((bandWeight k : ℚ) : ℝ)) := by
  rw [← summable_condensed_iff_of_nonneg bandWeight_real_nonneg
    (fun m n _ hmn => bandWeight_real_antitone hmn)]
  have hcomp : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2) := by
    have := (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) 1).2
      (Real.summable_one_div_nat_pow.mpr one_lt_two)
    simpa using this
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) hcomp
  · have := bandWeight_real_nonneg (2 ^ k)
    positivity
  · have hlog : (k : ℝ) ≤ (Nat.log 2 (2 ^ k + 1) : ℝ) := by
      have hk : k ≤ Nat.log 2 (2 ^ k + 1) := by
        calc k = Nat.log 2 (2 ^ k) := (Nat.log_pow (by norm_num) k).symm
          _ ≤ Nat.log 2 (2 ^ k + 1) := Nat.log_mono_right (by omega)
      exact_mod_cast hk
    have hc : (((2 ^ k : ℕ) : ℝ)) = (2:ℝ) ^ k := by push_cast; ring
    have h2k : (0:ℝ) < (2:ℝ) ^ k := by positivity
    have hden : (2:ℝ) ^ k * ((k : ℝ) + 1) ^ 2
        ≤ (((2 ^ k : ℕ) : ℝ) + 1) * ((Nat.log 2 (2 ^ k + 1) : ℝ) + 1) ^ 2 := by
      rw [hc]
      have h1 : ((k : ℝ) + 1) ^ 2 ≤ ((Nat.log 2 (2 ^ k + 1) : ℝ) + 1) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (by linarith) 2
      nlinarith [sq_nonneg ((k:ℝ)+1)]
    rw [bandWeight_real, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    exact hden

/-- The total band weight is finite. -/
lemma tsum_bandWeight_ne_top : ∑' k, ENNReal.ofReal ((bandWeight k : ℝ)) ≠ ⊤ := by
  rw [← ENNReal.ofReal_tsum_of_nonneg bandWeight_real_nonneg summable_bandWeight_real]
  exact ENNReal.ofReal_ne_top

/-- For every exponent `a > 1` the reciprocal band weights grow at most like
`(K log 2)^a` up to a constant. -/
lemma exists_const_bandWeight_bound {a : ℝ} (ha : 1 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ K : ℕ,
      2 / (bandWeight K : ℝ) ≤ C * (max 1 ((K : ℝ) * Real.log 2)) ^ a := by
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos one_lt_two
  set c : ℝ := (a - 1) / 4 with hcdef
  have hcpos : 0 < c := by rw [hcdef]; linarith
  set A : ℝ := 1 / (c * Real.log 2) + 1 with hAdef
  have hApos : 0 < A := by rw [hAdef]; positivity
  set B : ℝ := 1 / Real.log 2 + 1 with hBdef
  have hBpos : 0 < B := by
    have h : 0 < 1 / Real.log 2 := div_pos one_pos hlog2
    rw [hBdef]; linarith
  have hsq : ∀ x : ℝ, 0 ≤ x → (x ^ c) ^ 2 = x ^ (2 * c) := by
    intro x hx
    rw [← Real.rpow_natCast (x ^ c) 2, ← Real.rpow_mul hx]
    norm_num
    ring_nf
  have hCpos : (0:ℝ) < 2 * B * B ^ (2 * c) * A ^ 2 :=
    mul_pos (mul_pos (by linarith) (Real.rpow_pos_of_pos hBpos _)) (pow_pos hApos 2)
  refine ⟨2 * B * B ^ (2 * c) * A ^ 2, hCpos, ?_⟩
  intro K
  set t : ℝ := (K : ℝ) + 1 with htdef
  set L : ℝ := (Nat.log 2 (K + 1) : ℝ) with hLdef
  set M : ℝ := max 1 ((K : ℝ) * Real.log 2) with hMdef
  have hK0 : (0:ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
  have ht1 : (1:ℝ) ≤ t := by rw [htdef]; linarith
  have htpos : (0:ℝ) < t := by linarith
  have hM1 : (1:ℝ) ≤ M := le_max_left _ _
  have hMK : (K : ℝ) * Real.log 2 ≤ M := le_max_right _ _
  have hMpos : (0:ℝ) < M := by linarith
  have hL0 : (0:ℝ) ≤ L := by rw [hLdef]; positivity
  -- `t ≤ B * M`
  have htM : t ≤ B * M := by
    have hKM : (K : ℝ) ≤ M / Real.log 2 := by
      rw [le_div_iff₀ hlog2]; exact hMK
    have hBM : B * M = (1 / Real.log 2) * M + M := by rw [hBdef]; ring
    have h1 : (K : ℝ) ≤ (1 / Real.log 2) * M := by
      rw [one_div, inv_mul_eq_div]; exact hKM
    rw [htdef, hBM]
    linarith
  -- `t ^ c ≥ 1`
  have htc1 : (1:ℝ) ≤ t ^ c := Real.one_le_rpow ht1 hcpos.le
  have htcpos : (0:ℝ) < t ^ c := lt_of_lt_of_le zero_lt_one htc1
  -- `log t ≤ t ^ c / c`
  have hlogt : Real.log t ≤ t ^ c / c := by
    have h1 : Real.log (t ^ c) ≤ t ^ c - 1 := Real.log_le_sub_one_of_pos htcpos
    rw [Real.log_rpow htpos] at h1
    rw [le_div_iff₀ hcpos]
    linarith
  -- `L * log 2 ≤ log t`
  have hLlog : L * Real.log 2 ≤ Real.log t := by
    have hpow : ((2:ℝ) ^ (Nat.log 2 (K + 1)) : ℝ) ≤ t := by
      have hnat := Nat.pow_log_le_self 2 (x := K + 1) (Nat.succ_ne_zero K)
      have hcast : (((2 ^ (Nat.log 2 (K + 1)) : ℕ)) : ℝ) ≤ ((K + 1 : ℕ) : ℝ) := by
        exact_mod_cast hnat
      push_cast at hcast
      rw [htdef]
      exact hcast
    have hpp : (0:ℝ) < (2:ℝ) ^ (Nat.log 2 (K + 1)) := by positivity
    have hll := Real.log_le_log hpp hpow
    rw [Real.log_pow] at hll
    rw [← hLdef] at hll
    exact hll
  have hstep1 : L + 1 ≤ A * t ^ c := by
    have hLb : L ≤ t ^ c / (c * Real.log 2) := by
      rw [le_div_iff₀ (by positivity)]
      calc L * (c * Real.log 2) = (L * Real.log 2) * c := by ring
        _ ≤ Real.log t * c := mul_le_mul_of_nonneg_right hLlog hcpos.le
        _ ≤ (t ^ c / c) * c := mul_le_mul_of_nonneg_right hlogt hcpos.le
        _ = t ^ c := by field_simp
    have hrw : t ^ c / (c * Real.log 2) = (1 / (c * Real.log 2)) * t ^ c := by ring
    rw [hAdef]
    rw [hrw] at hLb
    linarith
  have hsq2 : (L + 1) ^ 2 ≤ A ^ 2 * t ^ (2 * c) := by
    have h := mul_self_le_mul_self (by linarith : (0:ℝ) ≤ L + 1) hstep1
    have hA2 : (A * t ^ c) * (A * t ^ c) = A ^ 2 * (t ^ c) ^ 2 := by ring
    rw [hA2, hsq t htpos.le] at h
    calc (L + 1) ^ 2 = (L + 1) * (L + 1) := by ring
      _ ≤ A ^ 2 * t ^ (2 * c) := h
  have htcM : t ^ (2 * c) ≤ B ^ (2 * c) * M ^ (2 * c) := by
    have h1 : t ^ (2 * c) ≤ (B * M) ^ (2 * c) :=
      Real.rpow_le_rpow htpos.le htM (by positivity)
    rwa [Real.mul_rpow hBpos.le hMpos.le] at h1
  have hMfin : M * M ^ (2 * c) ≤ M ^ a := by
    have h1 : M * M ^ (2 * c) = M ^ (1 + 2 * c) := by
      rw [Real.rpow_add hMpos, Real.rpow_one]
    rw [h1]
    exact Real.rpow_le_rpow_of_exponent_le hM1 (by rw [hcdef]; linarith)
  have hLHS : 2 / (bandWeight K : ℝ) = 2 * (t * (L + 1) ^ 2) := by
    rw [bandWeight_real, ← htdef, ← hLdef]
    have hne : t * (L + 1) ^ 2 ≠ 0 := by positivity
    field_simp
  rw [hLHS]
  have hMc : (0:ℝ) ≤ M ^ (2 * c) := Real.rpow_nonneg hMpos.le _
  have hBc : (0:ℝ) < B ^ (2 * c) := Real.rpow_pos_of_pos hBpos _
  have hBM0 : (0:ℝ) ≤ B * M := by positivity
  calc 2 * (t * (L + 1) ^ 2)
      ≤ 2 * ((B * M) * (A ^ 2 * t ^ (2 * c))) := by
        have := mul_le_mul htM hsq2 (sq_nonneg _) hBM0
        linarith
    _ ≤ 2 * ((B * M) * (A ^ 2 * (B ^ (2 * c) * M ^ (2 * c)))) := by
        have hinner : A ^ 2 * t ^ (2 * c) ≤ A ^ 2 * (B ^ (2 * c) * M ^ (2 * c)) :=
          mul_le_mul_of_nonneg_left htcM (sq_nonneg A)
        have := mul_le_mul_of_nonneg_left hinner hBM0
        linarith
    _ = (2 * B * B ^ (2 * c) * A ^ 2) * (M * M ^ (2 * c)) := by ring
    _ ≤ (2 * B * B ^ (2 * c) * A ^ 2) * M ^ a := mul_le_mul_of_nonneg_left hMfin hCpos.le


/-- The value of `bandTransform u w` at a point contained in exactly the first
`m` bands. -/
def bandPartial (m : ℕ) : ℚ := 1 + ∑ k ∈ Finset.range m, bandWeight k * 2 ^ k

/-- The partial band sums are at least one. -/
lemma one_le_bandPartial (m : ℕ) : 1 ≤ bandPartial m := by
  unfold bandPartial
  have : (0:ℚ) ≤ ∑ k ∈ Finset.range m, bandWeight k * 2 ^ k :=
    Finset.sum_nonneg (fun k _ => mul_nonneg (bandWeight_pos k).le (by positivity))
  linarith

/-- The partial band sums are positive reals. -/
lemma bandPartial_pos (m : ℕ) : (0:ℝ) < ((bandPartial m : ℚ) : ℝ) := by
  have := one_le_bandPartial m
  have : (1:ℝ) ≤ ((bandPartial m : ℚ) : ℝ) := by exact_mod_cast this
  linarith

/-- The partial band sum, read in the extended nonnegative reals, is `1` plus the weighted
dyadic contributions of the bands below `m`. -/
lemma ofReal_bandPartial (m : ℕ) :
    ENNReal.ofReal ((bandPartial m : ℚ) : ℝ)
      = 1 + ∑ k ∈ Finset.range m, ENNReal.ofReal ((bandWeight k : ℝ)) * 2 ^ k := by
  induction m with
  | zero => simp [bandPartial]
  | succ m ih =>
      have hterm : ENNReal.ofReal ((bandWeight m : ℝ)) * 2 ^ m
          = ENNReal.ofReal (((bandWeight m * 2 ^ m : ℚ)) : ℝ) := by
        have h2 : ((2:ℝ) ^ m) = (((2 ^ m : ℚ)) : ℝ) := by push_cast; ring
        rw [show (((bandWeight m * 2 ^ m : ℚ)) : ℝ)
              = ((bandWeight m : ℚ) : ℝ) * ((2:ℝ) ^ m) by push_cast; ring,
          ENNReal.ofReal_mul (le_of_lt (by exact_mod_cast bandWeight_pos m))]
        congr 1
        rw [h2]
        norm_num [ENNReal.ofReal_pow]
      have hnn : (0:ℝ) ≤ (((bandWeight m * 2 ^ m : ℚ)) : ℝ) := by
        have : (0:ℚ) ≤ bandWeight m * 2 ^ m :=
          mul_nonneg (bandWeight_pos m).le (by positivity)
        exact_mod_cast this
      rw [Finset.sum_range_succ, ← add_assoc, ← ih, hterm,
        ← ENNReal.ofReal_add (le_of_lt (bandPartial_pos m)) hnn]
      congr 1
      unfold bandPartial
      push_cast [Finset.sum_range_succ]
      ring

/-- If `w` lies in the first `m` bands, the band transform is at least the
corresponding partial value. -/
lemma ofReal_bandPartial_le_bandTransform {u : CantorSeq → ℝ≥0∞} {w : CantorSeq} {m : ℕ}
    (h : ∀ k, k < m → (2 : ℝ≥0∞) ^ k < u w) :
    ENNReal.ofReal ((bandPartial m : ℚ) : ℝ) ≤ bandTransform u w := by
  rw [ofReal_bandPartial, bandTransform]
  refine add_le_add le_rfl ?_
  refine le_trans (le_of_eq ?_)
    (ENNReal.sum_le_tsum (f := fun k : ℕ => Set.indicator {x | (2 : ℝ≥0∞) ^ k < u x}
      (fun _ => ENNReal.ofReal ((bandWeight k : ℝ)) * 2 ^ k) w) (Finset.range m))
  refine Finset.sum_congr rfl (fun k hk => ?_)
  exact (Set.indicator_of_mem (h k (Finset.mem_range.1 hk)) _).symm

/-- Conversely, any value strictly below the band transform is strictly below
one of the partial values realised at `w`. -/
lemma exists_bandPartial_gt {u : CantorSeq → ℝ≥0∞} {w : CantorSeq} {q : ℚ}
    (h : ENNReal.ofReal ((q : ℚ) : ℝ) < bandTransform u w) :
    ∃ m : ℕ, q < bandPartial m ∧ ∀ k, k < m → (2 : ℝ≥0∞) ^ k < u w := by
  classical
  set g : ℕ → ℝ≥0∞ := fun k => Set.indicator {x | (2 : ℝ≥0∞) ^ k < u x}
    (fun _ => ENNReal.ofReal ((bandWeight k : ℝ)) * 2 ^ k) w with hg
  have hsup : bandTransform u w = ⨆ m : ℕ, (1 + ∑ k ∈ Finset.range m, g k) := by
    rw [bandTransform, hg, ENNReal.tsum_eq_iSup_nat, ENNReal.add_iSup]
  rw [hsup, lt_iSup_iff] at h
  obtain ⟨m, hm⟩ := h
  by_cases hex : ∃ k, ¬ ((2 : ℝ≥0∞) ^ k < u w)
  · set m₀ := Nat.find hex with hm₀
    have hlt : ∀ k, k < m₀ → (2 : ℝ≥0∞) ^ k < u w := by
      intro k hk
      by_contra hc
      have hle : Nat.find hex ≤ k := Nat.find_le hc
      rw [← hm₀] at hle
      omega
    have hge : ∀ k, m₀ ≤ k → g k = 0 := by
      intro k hk
      have h0 : ¬ ((2 : ℝ≥0∞) ^ (m₀) < u w) := Nat.find_spec hex
      have hmono : (2 : ℝ≥0∞) ^ m₀ ≤ (2 : ℝ≥0∞) ^ k := by
        exact pow_le_pow_right₀ (by norm_num) hk
      have : ¬ ((2 : ℝ≥0∞) ^ k < u w) := by
        intro hlt'
        exact h0 (lt_of_le_of_lt hmono hlt')
      rw [hg]
      exact Set.indicator_of_notMem this _
    set m' := min m m₀ with hm'
    have hsum : ∑ k ∈ Finset.range m, g k = ∑ k ∈ Finset.range m', g k := by
      have hsub : Finset.range m' ⊆ Finset.range m := by
        intro x hx
        rw [Finset.mem_range] at hx ⊢
        have : m' ≤ m := min_le_left m m₀
        omega
      refine (Finset.sum_subset hsub ?_).symm
      · intro x hx hnx
        rw [Finset.mem_range] at hx
        rw [Finset.mem_range] at hnx
        exact hge x (by omega)
    have hval : (1 : ℝ≥0∞) + ∑ k ∈ Finset.range m', g k
        = ENNReal.ofReal ((bandPartial m' : ℚ) : ℝ) := by
      rw [ofReal_bandPartial]
      congr 1
      refine Finset.sum_congr rfl (fun k hk => ?_)
      have hk' : k < m' := Finset.mem_range.1 hk
      rw [hg]
      exact Set.indicator_of_mem (hlt k (by omega)) _
    rw [hsum, hval] at hm
    have hq : q < bandPartial m' := by
      have := (ENNReal.ofReal_lt_ofReal_iff (bandPartial_pos m')).1 hm
      exact_mod_cast this
    refine ⟨m', hq, ?_⟩
    intro k hk
    exact hlt k (by omega)
  · push_neg at hex
    have hval : (1 : ℝ≥0∞) + ∑ k ∈ Finset.range m, g k
        = ENNReal.ofReal ((bandPartial m : ℚ) : ℝ) := by
      rw [ofReal_bandPartial]
      congr 1
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [hg]
      exact Set.indicator_of_mem (hex k) _
    rw [hval] at hm
    have hq : q < bandPartial m := by
      have := (ENNReal.ofReal_lt_ofReal_iff (bandPartial_pos m)).1 hm
      exact_mod_cast this
    exact ⟨m, hq, fun k _ => hex k⟩

/-- The band contributions `bandWeight k · 2^k` form a computable sequence. -/
lemma computable_bandTerm : Computable (fun k : ℕ => bandWeight k * 2 ^ k) := by
  have hnat : Primrec (fun k : ℕ => 2 ^ k) :=
    (Primrec₂.unpaired'.1 Nat.Primrec.pow).comp (Primrec.const 2) Primrec.id
  have hD : Computable
      (fun k : ℕ => (k + 1) * ((Nat.log 2 (k + 1) + 1) * (Nat.log 2 (k + 1) + 1))) := by
    have hk : Primrec (fun k : ℕ => k + 1) := Primrec.succ
    have hl : Primrec (fun k : ℕ => Nat.log 2 (k + 1) + 1) :=
      Primrec.succ.comp (primrec_natLogTwo.comp Primrec.succ)
    exact (Primrec.nat_mul.comp hk (Primrec.nat_mul.comp hl hl)).to_comp
  refine computable_of_num_den (N := fun k : ℕ => ((2 ^ k : ℕ) : ℤ))
    (ComputableReals.primrec_natCastInt.to_comp.comp hnat.to_comp) hD
    (fun k => Nat.mul_pos (Nat.succ_pos k) (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)))
    (fun k => ?_)
  unfold bandWeight
  push_cast
  ring

/-- The partial band sums satisfy the expected one-step recurrence. -/
lemma bandPartial_succ (m : ℕ) :
    bandPartial (m + 1) = bandPartial m + bandWeight m * 2 ^ m := by
  unfold bandPartial
  rw [Finset.sum_range_succ]
  ring

/-- The partial band sums form a computable sequence of rationals. -/
lemma computable_bandPartial : Computable bandPartial := by
  have hh : Computable₂ (fun (_ : ℕ) (p : ℕ × ℚ) => p.2 + bandWeight p.1 * 2 ^ p.1) := by
    have h1 : Computable (fun x : ℕ × (ℕ × ℚ) => x.2.2) := Computable.snd.comp Computable.snd
    have h2 : Computable (fun x : ℕ × (ℕ × ℚ) => bandWeight x.2.1 * 2 ^ x.2.1) :=
      computable_bandTerm.comp (Computable.fst.comp Computable.snd)
    exact (Computable₂.comp computable₂_ratAdd h1 h2).to₂
  have hrec := Computable.nat_rec (f := fun m : ℕ => m) (g := fun _ : ℕ => (1 : ℚ))
    Computable.id (Computable.const 1) hh
  refine hrec.of_eq (fun m => ?_)
  induction m with
  | zero => simp [bandPartial]
  | succ m ih => rw [bandPartial_succ, ← ih]

/-- The band transform of a lower semicomputable function is lower semicomputable. -/
lemma isLowerSemicomputableFun_bandTransform {u : CantorSeq → ℝ≥0∞}
    (hu : IsLowerSemicomputableFun u) : IsLowerSemicomputableFun (bandTransform u) := by
  classical
  obtain ⟨enum, hcomp, hspec⟩ := hu
  have hcyl : cantorCylinder ([] : BitString) = Set.univ := by
    ext w; simp [cantorCylinder, IsCantorPrefix]
  refine ⟨fun q i => if q < bandPartial (Nat.unpair i).1 then
      (if (Nat.unpair i).1 = 0 then some ([] : BitString)
        else enum ((2 : ℚ) ^ ((Nat.unpair i).1 - 1)) (Nat.unpair i).2)
      else none, ?_, ?_⟩
  · have hfstu : Computable (fun p : ℚ × ℕ => (Nat.unpair p.2).1) :=
      (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)).to_comp
    have hsndu : Computable (fun p : ℚ × ℕ => (Nat.unpair p.2).2) :=
      (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)).to_comp
    have hb1 : Computable (fun p : ℚ × ℕ => decide (p.1 < bandPartial (Nat.unpair p.2).1)) :=
      Computable₂.comp (f := fun a b : ℚ => decide (a < b)) computable₂_ratLt
        Computable.fst (computable_bandPartial.comp hfstu)
    have hb2 : Computable (fun p : ℚ × ℕ => decide ((Nat.unpair p.2).1 = 0)) := by
      have hltc : Computable (fun p : ℕ × ℕ => decide (p.1 < p.2)) := by
        obtain ⟨_, hlt⟩ := Primrec.nat_lt
        convert Primrec.to_comp hlt
      have h := hltc.comp (hfstu.pair (Computable.const 1))
      refine h.of_eq (fun p => ?_)
      simp [Nat.lt_one_iff]
    have hpred : Computable (fun p : ℚ × ℕ => (Nat.unpair p.2).1 - 1) :=
      (Primrec.pred.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))).to_comp
    have hinner : Computable (fun p : ℚ × ℕ =>
        enum ((2 : ℚ) ^ ((Nat.unpair p.2).1 - 1)) (Nat.unpair p.2).2) :=
      Computable₂.comp hcomp (computable_two_pow_rat.comp hpred) hsndu
    have hc2 := Computable.cond hb2 (Computable.const (some ([] : BitString))) hinner
    have hc1 := Computable.cond hb1 hc2 (Computable.const (none : Option BitString))
    refine hc1.of_eq (fun p => ?_)
    by_cases h1 : p.1 < bandPartial (Nat.unpair p.2).1
    · by_cases h2 : (Nat.unpair p.2).1 = 0 <;> simp [h1, h2]
    · simp [h1]
  · intro q
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro h
      have hbT : ENNReal.ofReal ((q : ℚ) : ℝ) < bandTransform u w := by
        rcases h with h | h
        · have h0 : ENNReal.ofReal ((q : ℚ) : ℝ) = 0 := by
            simp [ENNReal.ofReal_eq_zero.2 h.le]
          rw [h0]
          refine lt_of_lt_of_le zero_lt_one ?_
          rw [bandTransform]
          exact self_le_add_right 1 _
        · exact h
      obtain ⟨m, hqm, hband⟩ := exists_bandPartial_gt hbT
      by_cases hm0 : m = 0
      · refine ⟨Nat.pair 0 0, ?_⟩
        subst hm0
        simp only [Nat.unpair_pair, if_pos hqm]
        simp [hcyl]
      · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
        have hlt : (2 : ℝ≥0∞) ^ (m - 1) < u w := hband (m - 1) (by omega)
        have hmem : w ∈ ⋃ i, (enum ((2 : ℚ) ^ (m - 1)) i).elim ∅ cantorCylinder := by
          rw [← hspec ((2 : ℚ) ^ (m - 1))]
          refine Or.inr ?_
          rwa [ofReal_rat_two_pow]
        obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hmem
        refine ⟨Nat.pair m j, ?_⟩
        simp only [Nat.unpair_pair, if_pos hqm, if_neg hm0]
        exact hj
    · rintro ⟨i, hi⟩
      set m := (Nat.unpair i).1 with hmdef
      by_cases h1 : q < bandPartial m
      · by_cases hm0 : m = 0
        · refine Or.inr ?_
          have hq1 : q < 1 := by
            have : bandPartial 0 = 1 := by simp [bandPartial]
            rw [hm0, this] at h1
            exact h1
          have hlt1 : ENNReal.ofReal ((q : ℚ) : ℝ) < 1 := by
            rw [ENNReal.ofReal_lt_one]
            exact_mod_cast hq1
          refine lt_of_lt_of_le hlt1 ?_
          rw [bandTransform]
          exact self_le_add_right 1 _
        · refine Or.inr ?_
          rw [if_pos h1, if_neg hm0] at hi
          have hmem : w ∈ ⋃ j, (enum ((2 : ℚ) ^ (m - 1)) j).elim ∅ cantorCylinder :=
            Set.mem_iUnion.2 ⟨(Nat.unpair i).2, hi⟩
          rw [← hspec ((2 : ℚ) ^ (m - 1))] at hmem
          have hlt : (2 : ℝ≥0∞) ^ (m - 1) < u w := by
            rcases hmem with hneg | hpos
            · exfalso
              have : (0:ℝ) < (((2 : ℚ) ^ (m - 1) : ℚ) : ℝ) := by
                have : (0:ℚ) < (2 : ℚ) ^ (m - 1) := by positivity
                exact_mod_cast this
              linarith
            · rwa [ofReal_rat_two_pow] at hpos
          have hall : ∀ k, k < m → (2 : ℝ≥0∞) ^ k < u w := by
            intro k hk
            refine lt_of_le_of_lt ?_ hlt
            exact pow_le_pow_right₀ (by norm_num) (by omega)
          refine lt_of_lt_of_le ?_ (ofReal_bandPartial_le_bandTransform hall)
          refine (ENNReal.ofReal_lt_ofReal_iff (bandPartial_pos m)).2 ?_
          exact_mod_cast h1
      · rw [if_neg h1] at hi
        simp at hi


/-- The band transform of a probability-bounded test has integral at most the total mass plus the
total band weight, hence is finite. -/
lemma lintegral_bandTransform_le {μ : Measure CantorSeq} {u : CantorSeq → ℝ≥0∞}
    (hu : IsProbabilityBoundedRandomnessTest μ u) :
    ∫⁻ w, bandTransform u w ∂μ ≤ μ Set.univ + ∑' k, ENNReal.ofReal ((bandWeight k : ℝ)) := by
  obtain ⟨hLSC, hbound⟩ := hu
  have humeas : Measurable u := hLSC.measurable
  have hset : ∀ k : ℕ, MeasurableSet {x | (2 : ℝ≥0∞) ^ k < u x} := fun k =>
    measurableSet_lt measurable_const humeas
  have hcast : ∀ k : ℕ, ENNReal.ofReal (((2 : ℚ) ^ k : ℚ) : ℝ) = (2 : ℝ≥0∞) ^ k := by
    intro k
    have hr : (((2 : ℚ) ^ k : ℚ) : ℝ) = (2 : ℝ) ^ k := by push_cast; ring
    rw [hr, ENNReal.ofReal_pow (by norm_num)]
    norm_num
  have hmeas : ∀ k : ℕ, Measurable (fun w => Set.indicator {x | (2 : ℝ≥0∞) ^ k < u x}
      (fun _ => ENNReal.ofReal ((bandWeight k : ℝ)) * 2 ^ k) w) := fun k =>
    (measurable_const.indicator (hset k))
  have hterm : ∀ k : ℕ, ∫⁻ w, Set.indicator {x | (2 : ℝ≥0∞) ^ k < u x}
      (fun _ => ENNReal.ofReal ((bandWeight k : ℝ)) * 2 ^ k) w ∂μ
      ≤ ENNReal.ofReal ((bandWeight k : ℝ)) := by
    intro k
    rw [lintegral_indicator_const (hset k)]
    have hb := hbound ((2 : ℚ) ^ k) (by positivity)
    have hsetEq : {w | u w > ENNReal.ofReal (((2 : ℚ) ^ k : ℚ) : ℝ)}
        = {x | (2 : ℝ≥0∞) ^ k < u x} := by
      ext w
      simp
    rw [hsetEq, hcast k] at hb
    have h2k0 : ((2 : ℝ≥0∞) ^ k) ≠ 0 := by
      simp
    have h2kt : ((2 : ℝ≥0∞) ^ k) ≠ ⊤ := by
      simp [ENNReal.pow_eq_top_iff]
    calc ENNReal.ofReal ((bandWeight k : ℝ)) * 2 ^ k * μ {x | (2 : ℝ≥0∞) ^ k < u x}
        ≤ ENNReal.ofReal ((bandWeight k : ℝ)) * 2 ^ k * ((2 : ℝ≥0∞) ^ k)⁻¹ :=
          mul_le_mul' le_rfl hb.le
      _ = ENNReal.ofReal ((bandWeight k : ℝ)) * ((2 : ℝ≥0∞) ^ k * ((2 : ℝ≥0∞) ^ k)⁻¹) := by
          rw [mul_assoc]
      _ = ENNReal.ofReal ((bandWeight k : ℝ)) := by
          rw [ENNReal.mul_inv_cancel h2k0 h2kt, mul_one]
  have hsum : ∫⁻ w, (∑' k : ℕ, Set.indicator {x | (2 : ℝ≥0∞) ^ k < u x}
      (fun _ => ENNReal.ofReal ((bandWeight k : ℝ)) * 2 ^ k) w) ∂μ
      ≤ ∑' k, ENNReal.ofReal ((bandWeight k : ℝ)) := by
    rw [lintegral_tsum (fun k => (hmeas k).aemeasurable)]
    exact ENNReal.tsum_le_tsum hterm
  have hsplit : ∫⁻ w, bandTransform u w ∂μ
      = μ Set.univ + ∫⁻ w, (∑' k : ℕ, Set.indicator {x | (2 : ℝ≥0∞) ^ k < u x}
        (fun _ => ENNReal.ofReal ((bandWeight k : ℝ)) * 2 ^ k) w) ∂μ := by
    simp only [bandTransform]
    rw [lintegral_add_left measurable_const, lintegral_const, one_mul]
  rw [hsplit]
  exact add_le_add le_rfl hsum


/-- Every real greater than one lies in a dyadic band: some power `2 ^ K` is below it while
`4 * 2 ^ K` is above it. -/
private lemma exists_dyadic_band {r : ℝ} (hr1 : 1 < r) :
    ∃ K : ℕ, (2 : ℝ) ^ K < r ∧ r < 4 * (2 : ℝ) ^ K := by
  have hr0 : (0:ℝ) < r := by linarith
  set n : ℕ := ⌈r⌉₊ with hndef
  have hn2 : 2 ≤ n := by
    have : (1:ℕ) < ⌈r⌉₊ := Nat.lt_ceil.2 (by exact_mod_cast hr1)
    omega
  have hlogpos : 0 < Nat.log 2 n := Nat.log_pos one_lt_two hn2
  set K : ℕ := Nat.log 2 n - 1 with hKdef
  have hK1 : K + 1 = Nat.log 2 n := by omega
  have hpow1 : 2 ^ (K + 1) ≤ n := by
    rw [hK1]
    exact Nat.pow_log_le_self 2 (by omega)
  have hpow2 : n < 2 ^ (K + 2) := by
    have h := Nat.lt_pow_succ_log_self (b := 2) one_lt_two n
    have hsucc : Nat.log 2 n + 1 = K + 2 := by omega
    rwa [Nat.succ_eq_add_one, hsucc] at h
  have hone_le : 1 ≤ 2 ^ K := Nat.one_le_two_pow
  have h2Kn : 2 ^ K ≤ n - 1 := by
    have : 2 ^ (K + 1) = 2 * 2 ^ K := by ring
    omega
  have hcast1 : ((2 ^ K : ℕ) : ℝ) = (2:ℝ) ^ K := by push_cast; ring
  have hrn : r ≤ (n : ℝ) := Nat.le_ceil r
  have hnr : (n : ℝ) - 1 < r := by
    have := Nat.ceil_lt_add_one hr0.le
    rw [← hndef] at this
    linarith
  refine ⟨K, ?_, ?_⟩
  · have h1 : ((2 ^ K : ℕ) : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast h2Kn
    have h2 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      have h1n : (1:ℕ) ≤ n := by omega
      push_cast [Nat.cast_sub h1n]
      ring
    rw [hcast1, h2] at h1
    linarith
  · have h1 : ((n : ℕ) : ℝ) < ((2 ^ (K + 2) : ℕ) : ℝ) := by exact_mod_cast hpow2
    have h2 : ((2 ^ (K + 2) : ℕ) : ℝ) = 4 * (2:ℝ) ^ K := by push_cast; ring
    rw [h2] at h1
    linarith

/-- A point above the `K`-th dyadic level contributes the whole `K`-th band to the band
transform. -/
private lemma bandWeight_mul_two_pow_le_bandTransform {u : CantorSeq → ℝ≥0∞} {w : CantorSeq}
    {K : ℕ} (hmem : (2 : ℝ≥0∞) ^ K < u w) :
    ENNReal.ofReal ((bandWeight K : ℝ)) * 2 ^ K ≤ bandTransform u w := by
  have h1 : Set.indicator {x | (2 : ℝ≥0∞) ^ K < u x}
      (fun _ => ENNReal.ofReal ((bandWeight K : ℝ)) * 2 ^ K) w
      = ENNReal.ofReal ((bandWeight K : ℝ)) * 2 ^ K :=
    Set.indicator_of_mem hmem _
  have h2 := ENNReal.le_tsum (f := fun k : ℕ => Set.indicator {x | (2 : ℝ≥0∞) ^ k < u x}
      (fun _ => ENNReal.ofReal ((bandWeight k : ℝ)) * 2 ^ k) w) K
  rw [h1] at h2
  refine h2.trans ?_
  rw [bandTransform]
  exact le_add_self

/-- A test is bounded by its band transform times a logarithmic correction of exponent `a > 1`,
up to a constant. -/
lemma le_bandTransform_mul_logarithmicCorrection {u : CantorSeq → ℝ≥0∞}
    {a : ℝ} (ha : 1 < a) :
    ∃ c : NNReal, ∀ w, u w ≤ c * bandTransform u w * logarithmicCorrection a (u w) := by
  obtain ⟨C, hCpos, hC⟩ := exists_const_bandWeight_bound ha
  have ha0 : (0:ℝ) < a := by linarith
  refine ⟨1 + (⌈2 * C⌉₊ : NNReal), fun w => ?_⟩
  set c : NNReal := 1 + (⌈2 * C⌉₊ : NNReal) with hcdef
  have hcR : (2 : ℝ) * C ≤ (c : ℝ) := by
    have h := Nat.le_ceil (2 * C)
    rw [hcdef]
    push_cast
    linarith
  have hc1 : (1:ℝ) ≤ (c : ℝ) := by
    have hnn : (0:ℝ) ≤ (⌈2 * C⌉₊ : ℝ) := Nat.cast_nonneg _
    rw [hcdef]
    push_cast
    linarith
  have hc1' : (1:ℝ≥0∞) ≤ (c : ℝ≥0∞) := by
    rw [ENNReal.one_le_coe_iff, ← NNReal.coe_le_coe]
    simpa using hc1
  have hc0 : (c : ℝ≥0∞) ≠ 0 := by
    intro h
    rw [h] at hc1'
    simp at hc1'
  -- the band transform is at least one
  have hbT1 : (1:ℝ≥0∞) ≤ bandTransform u w := by
    rw [bandTransform]
    exact self_le_add_right 1 _
  -- the logarithmic correction is at least one
  have hcorr1 : (1:ℝ≥0∞) ≤ logarithmicCorrection a (u w) := by
    rw [logarithmicCorrection]
    split_ifs with h
    · exact le_top
    · exact ENNReal.one_le_rpow (ENNReal.one_le_ofReal.2 (le_max_left _ _)) ha0
  by_cases hinf : u w = ∞
  · have hcorr : logarithmicCorrection a (u w) = ∞ := by
      rw [logarithmicCorrection, if_pos hinf]
    have hne : (c : ℝ≥0∞) * bandTransform u w ≠ 0 := by
      have : (1:ℝ≥0∞) ≤ (c : ℝ≥0∞) * bandTransform u w := by
        simpa using mul_le_mul' hc1' hbT1
      intro h
      rw [h] at this
      simp at this
    rw [hcorr, hinf, ENNReal.mul_top hne]
  · set r : ℝ := (u w).toReal with hrdef
    have hv : u w = ENNReal.ofReal r := (ENNReal.ofReal_toReal hinf).symm
    by_cases hle1 : u w ≤ 1
    · calc u w ≤ 1 := hle1
        _ ≤ (c : ℝ≥0∞) * bandTransform u w * logarithmicCorrection a (u w) := by
            simpa using mul_le_mul' (mul_le_mul' hc1' hbT1) hcorr1
    · push_neg at hle1
      have hr1 : (1:ℝ) < r := by
        rw [hv] at hle1
        exact ENNReal.one_lt_ofReal.1 hle1
      have hr0 : (0:ℝ) < r := by linarith
      obtain ⟨K, h2Kr, hr4⟩ := exists_dyadic_band hr1
      -- the `K`-th band contains `w`
      have hpowE : ((2:ℝ≥0∞) ^ K) = ENNReal.ofReal ((2:ℝ) ^ K) := by
        rw [ENNReal.ofReal_pow (by norm_num)]
        norm_num
      have hmemK : (2:ℝ≥0∞) ^ K < u w := by
        rw [hpowE, hv]
        exact (ENNReal.ofReal_lt_ofReal_iff hr0).2 h2Kr
      have hterm : ENNReal.ofReal ((bandWeight K : ℝ)) * 2 ^ K ≤ bandTransform u w :=
        bandWeight_mul_two_pow_le_bandTransform hmemK
      have hbwpos : (0:ℝ) < (bandWeight K : ℝ) := by exact_mod_cast bandWeight_pos K
      have hv4 : u w ≤ ENNReal.ofReal (4 / (bandWeight K : ℝ)) *
          (ENNReal.ofReal ((bandWeight K : ℝ)) * 2 ^ K) := by
        have hfac : ENNReal.ofReal (4 / (bandWeight K : ℝ)) *
            (ENNReal.ofReal ((bandWeight K : ℝ)) * 2 ^ K) = ENNReal.ofReal (4 * (2:ℝ) ^ K) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
            div_mul_cancel₀ _ (ne_of_gt hbwpos), hpowE, ← ENNReal.ofReal_mul (by norm_num)]
        rw [hfac, hv]
        exact ENNReal.ofReal_le_ofReal hr4.le
      -- the constant bound
      have hcorr : logarithmicCorrection a (u w)
          = (ENNReal.ofReal (max 1 (Real.log r))) ^ a := by
        rw [logarithmicCorrection, if_neg hinf, hrdef]
      have hlogK : (K : ℝ) * Real.log 2 ≤ max 1 (Real.log r) := by
        have h1 : Real.log ((2:ℝ) ^ K) ≤ Real.log r :=
          Real.log_le_log (by positivity) h2Kr.le
        rw [Real.log_pow] at h1
        exact h1.trans (le_max_right _ _)
      have hmaxle : max 1 ((K : ℝ) * Real.log 2) ≤ max 1 (Real.log r) :=
        max_le (le_max_left _ _) hlogK
      have hRbound : 4 / (bandWeight K : ℝ) ≤ (c : ℝ) * (max 1 (Real.log r)) ^ a := by
        have h1 : 2 / (bandWeight K : ℝ) ≤ C * (max 1 ((K : ℝ) * Real.log 2)) ^ a := hC K
        have h2 : (max 1 ((K : ℝ) * Real.log 2)) ^ a ≤ (max 1 (Real.log r)) ^ a :=
          Real.rpow_le_rpow (le_trans zero_le_one (le_max_left _ _)) hmaxle ha0.le
        have h3 : (0:ℝ) ≤ (max 1 (Real.log r)) ^ a :=
          Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) a
        have h4 : (1:ℝ) ≤ (max 1 (Real.log r)) ^ a :=
          Real.one_le_rpow (le_max_left _ _) ha0.le
        have h5 : 4 / (bandWeight K : ℝ) = 2 * (2 / (bandWeight K : ℝ)) := by ring
        calc 4 / (bandWeight K : ℝ) = 2 * (2 / (bandWeight K : ℝ)) := h5
          _ ≤ 2 * (C * (max 1 ((K : ℝ) * Real.log 2)) ^ a) := by linarith
          _ ≤ 2 * (C * (max 1 (Real.log r)) ^ a) := by nlinarith
          _ = (2 * C) * (max 1 (Real.log r)) ^ a := by ring
          _ ≤ (c : ℝ) * (max 1 (Real.log r)) ^ a := by nlinarith
      have hCbound : ENNReal.ofReal (4 / (bandWeight K : ℝ))
          ≤ (c : ℝ≥0∞) * logarithmicCorrection a (u w) := by
        have h1 : ENNReal.ofReal (4 / (bandWeight K : ℝ))
            ≤ ENNReal.ofReal ((c : ℝ) * (max 1 (Real.log r)) ^ a) :=
          ENNReal.ofReal_le_ofReal hRbound
        have h2 : ENNReal.ofReal ((c : ℝ) * (max 1 (Real.log r)) ^ a)
            = (c : ℝ≥0∞) * logarithmicCorrection a (u w) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_coe_nnreal, hcorr,
            ENNReal.ofReal_rpow_of_nonneg (le_trans zero_le_one (le_max_left _ _)) ha0.le]
        rwa [h2] at h1
      calc u w ≤ ENNReal.ofReal (4 / (bandWeight K : ℝ)) *
              (ENNReal.ofReal ((bandWeight K : ℝ)) * 2 ^ K) := hv4
        _ ≤ ((c : ℝ≥0∞) * logarithmicCorrection a (u w)) * bandTransform u w :=
            mul_le_mul' hCbound hterm
        _ = (c : ℝ≥0∞) * bandTransform u w * logarithmicCorrection a (u w) := by ring


/-- Maximal expectation-bounded and probability-bounded tests agree up to a constant in one
direction and up to a logarithmic correction of any exponent `a > 1` in the other. -/
lemma deficiency_bounds_of_one_lt {μ : Measure CantorSeq}
    (hμ : IsComputableMeasure μ)
    (u_P : CantorSeq → ℝ≥0∞)
    (h_P_max : IsProbabilityBoundedRandomnessTest μ u_P ∧
      ∀ v, IsProbabilityBoundedRandomnessTest μ v → ∃ c : NNReal, ∀ w, v w ≤ c * u_P w)
    (u_E : CantorSeq → ℝ≥0∞)
    (h_E_max : IsExpectationBoundedRandomnessTest μ u_E ∧
      ∀ v, IsExpectationBoundedRandomnessTest μ v → ∃ c : NNReal, ∀ w, v w ≤ c * u_E w)
    {a : ℝ} (ha : 1 < a) :
    ∃ c1 c2 : NNReal, ∀ w,
      u_E w ≤ c1 * u_P w ∧
      u_P w ≤ c2 * u_E w * logarithmicCorrection a (u_P w) := by
  classical
  -- first bound : `u_E ≤ c1 * u_P`
  obtain ⟨cA, hcA⟩ := h_P_max.2 _ (isProbabilityBounded_of_expectationBounded h_E_max.1)
  have hhalf : (2 : ℝ≥0∞) * ENNReal.ofReal ((1 / 2 : ℚ) : ℝ) = 1 := by
    rw [show ((1 / 2 : ℚ) : ℝ) = (1 / 2 : ℝ) by norm_num,
      show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by simp,
      ← ENNReal.ofReal_mul (by norm_num)]
    norm_num
  have h1 : ∀ w, u_E w ≤ (2 * cA : NNReal) * u_P w := by
    intro w
    have h := hcA w
    have h2 : (2 : ℝ≥0∞) * (ENNReal.ofReal ((1 / 2 : ℚ) : ℝ) * u_E w) = u_E w := by
      rw [← mul_assoc, hhalf, one_mul]
    calc u_E w = (2 : ℝ≥0∞) * (ENNReal.ofReal ((1 / 2 : ℚ) : ℝ) * u_E w) := h2.symm
      _ ≤ (2 : ℝ≥0∞) * ((cA : ℝ≥0∞) * u_P w) := mul_le_mul' le_rfl h
      _ = ((2 * cA : NNReal) : ℝ≥0∞) * u_P w := by
          push_cast
          ring
  -- second bound : through the band transform
  obtain ⟨c0, hc0⟩ := le_bandTransform_mul_logarithmicCorrection (u := u_P) ha
  have hbTlsc : IsLowerSemicomputableFun (bandTransform u_P) :=
    isLowerSemicomputableFun_bandTransform h_P_max.1.1
  have hbTint : ∫⁻ w, bandTransform u_P w ∂μ
      ≤ μ Set.univ + ∑' k, ENNReal.ofReal ((bandWeight k : ℝ)) :=
    lintegral_bandTransform_le h_P_max.1
  have hNtop : μ Set.univ + ∑' k, ENNReal.ofReal ((bandWeight k : ℝ)) ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨hμ.measure_univ_ne_top, tsum_bandWeight_ne_top⟩
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hNtop
  set N : ℕ := n + 1 with hNdef
  have hNpos : (0 : ℚ) < (N : ℚ) := by positivity
  have hNle : μ Set.univ + ∑' k, ENNReal.ofReal ((bandWeight k : ℝ)) ≤ (N : ℝ≥0∞) := by
    refine hn.le.trans ?_
    exact_mod_cast Nat.le_succ n
  have hofN : ENNReal.ofReal (((N : ℚ) : ℝ)) = (N : ℝ≥0∞) := by
    rw [show (((N : ℚ) : ℝ)) = (N : ℝ) by push_cast; ring]
    simp
  have hinvN : ENNReal.ofReal (((1 / (N : ℚ) : ℚ) : ℝ)) * (N : ℝ≥0∞) = 1 := by
    rw [← hofN, ← ENNReal.ofReal_mul (by positivity)]
    have : ((1 / (N : ℚ) : ℚ) : ℝ) * (((N : ℚ)) : ℝ) = 1 := by
      have hne : ((N : ℕ) : ℝ) ≠ 0 := by
        rw [hNdef]; positivity
      push_cast
      field_simp
    rw [this]
    simp
  have hvE : IsExpectationBoundedRandomnessTest μ
      (fun w => ENNReal.ofReal (((1 / (N : ℚ) : ℚ)) : ℝ) * bandTransform u_P w) := by
    refine ⟨hbTlsc.rat_smul (by positivity), ?_⟩
    rw [lintegral_const_mul _ hbTlsc.measurable]
    calc ENNReal.ofReal (((1 / (N : ℚ) : ℚ)) : ℝ) * ∫⁻ w, bandTransform u_P w ∂μ
        ≤ ENNReal.ofReal (((1 / (N : ℚ) : ℚ)) : ℝ) * (N : ℝ≥0∞) :=
          mul_le_mul' le_rfl (hbTint.trans hNle)
      _ = 1 := hinvN
  obtain ⟨cB, hcB⟩ := h_E_max.2 _ hvE
  have hbT : ∀ w, bandTransform u_P w ≤ ((N : NNReal) * cB : NNReal) * u_E w := by
    intro w
    have h := hcB w
    have hmul : (N : ℝ≥0∞) * (ENNReal.ofReal (((1 / (N : ℚ) : ℚ)) : ℝ) * bandTransform u_P w)
        = bandTransform u_P w := by
      rw [← mul_assoc, mul_comm (N : ℝ≥0∞), hinvN, one_mul]
    calc bandTransform u_P w
        = (N : ℝ≥0∞) * (ENNReal.ofReal (((1 / (N : ℚ) : ℚ)) : ℝ) * bandTransform u_P w) :=
          hmul.symm
      _ ≤ (N : ℝ≥0∞) * ((cB : ℝ≥0∞) * u_E w) := mul_le_mul' le_rfl h
      _ = ((N : NNReal) * cB : NNReal) * u_E w := by
          push_cast
          ring
  refine ⟨2 * cA, c0 * ((N : NNReal) * cB), fun w => ⟨h1 w, ?_⟩⟩
  calc u_P w ≤ (c0 : ℝ≥0∞) * bandTransform u_P w * logarithmicCorrection a (u_P w) := hc0 w
    _ ≤ (c0 : ℝ≥0∞) * (((N : NNReal) * cB : NNReal) * u_E w)
          * logarithmicCorrection a (u_P w) :=
        mul_le_mul' (mul_le_mul' le_rfl (hbT w)) le_rfl
    _ = ((c0 * ((N : NNReal) * cB) : NNReal) : ℝ≥0∞) * u_E w * logarithmicCorrection a (u_P w) := by
        push_cast
        ring

-- Theorem 43
/-- The maximal expectation-bounded test is bounded by the maximal probability-bounded test up to
a constant, and conversely up to a squared logarithmic correction. -/
theorem deficiency_bounds {μ : Measure CantorSeq}
    (hμ : IsComputableMeasure μ)
    (u_P : CantorSeq → ℝ≥0∞)
    (h_P_max : IsProbabilityBoundedRandomnessTest μ u_P ∧
      ∀ v, IsProbabilityBoundedRandomnessTest μ v → ∃ c : NNReal, ∀ w, v w ≤ c * u_P w)
    (u_E : CantorSeq → ℝ≥0∞)
    (h_E_max : IsExpectationBoundedRandomnessTest μ u_E ∧
      ∀ v, IsExpectationBoundedRandomnessTest μ v → ∃ c : NNReal, ∀ w, v w ≤ c * u_E w) :
    ∃ c1 c2 : NNReal, ∀ w,
      u_E w ≤ c1 * u_P w ∧
      u_P w ≤ c2 * u_E w * logarithmicCorrection 2 (u_P w) :=
  deficiency_bounds_of_one_lt hμ u_P h_P_max u_E h_E_max (by norm_num)

-- Problem 93
/-- The comparison of maximal probability-bounded and expectation-bounded tests holds with a
logarithmic correction of any exponent greater than one. -/
theorem deficiency_bounds_sharp {μ : Measure CantorSeq}
    (hμ : IsComputableMeasure μ)
    (u_P : CantorSeq → ℝ≥0∞)
    (h_P_max : IsProbabilityBoundedRandomnessTest μ u_P ∧
      ∀ v, IsProbabilityBoundedRandomnessTest μ v → ∃ c : NNReal, ∀ w, v w ≤ c * u_P w)
    (u_E : CantorSeq → ℝ≥0∞)
    (h_E_max : IsExpectationBoundedRandomnessTest μ u_E ∧
      ∀ v, IsExpectationBoundedRandomnessTest μ v → ∃ c : NNReal, ∀ w, v w ≤ c * u_E w)
    (a : NNReal) (ha : 1 < a) :
    ∃ c1 c2 : NNReal, ∀ w,
      u_E w ≤ c1 * u_P w ∧
      u_P w ≤ c2 * u_E w * logarithmicCorrection a.toReal (u_P w) :=
  deficiency_bounds_of_one_lt hμ u_P h_P_max u_E h_E_max (by exact_mod_cast ha)

end Kolmogorov
