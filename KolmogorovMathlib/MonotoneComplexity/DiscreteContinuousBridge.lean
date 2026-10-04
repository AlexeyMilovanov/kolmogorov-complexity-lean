import KolmogorovMathlib.MonotoneComplexity.PrefixFreeEnvelope
import KolmogorovMathlib.MonotoneComplexity.APrioriComplexity
import KolmogorovMathlib.AlgorithmicProbability.UniversalSemimeasure
import KolmogorovMathlib.Prefix.TwoStage
import KolmogorovMathlib.Foundation.EnumerationComplexity

/-!
# Discrete and continuous a priori probability agree on self-delimiting codes

On the prefix-free codes `natCode n` of the naturals the universal discrete semimeasure and the
universal continuous semimeasure are equal up to a multiplicative constant
(`universalSemimeasure_natCode_equiv_continuous`), each inequality being proved by restricting
one semimeasure to the range of the coding (`IsLSC.indicator_range`,
`natCodeRangeSection_isLowerSemicomputableSemimeasure`) and invoking maximality of the other.

### Logarithmic form

Taking negative logarithms, `KA (natCode n)` and the discrete complexity
`-log₂ m(n)` differ by at most a constant: `KA_natCode_le_neg_logb_universalSemimeasure_add_const`,
`neg_logb_universalSemimeasure_natCode_le_KA_add_const`, and their combination
`abs_KA_natCode_sub_neg_logb_universalSemimeasure_le`.

Source: SUV, Problem 126.
-/

namespace Kolmogorov

open scoped ENNReal BigOperators

/-- Restricting a lower semicomputable function to the range of a computable enumeration keeps it
lower semicomputable. -/
theorem IsLSC.indicator_range {m : BitString → BitString → ℝ≥0∞} (hm : IsLSC m)
    {x : ℕ → BitString} (hx : Computable x) :
    IsLSC (fun y ctx => Set.indicator (Set.range x) (fun y => m y ctx) y) := by
  obtain ⟨approx, hmono, hsup, hcomp⟩ := hm
  refine ⟨fun s out ctx => if hitUpTo x s out then approx s out ctx else 0, ?_, ?_, ?_⟩
  · intro s out ctx
    dsimp only
    by_cases h : hitUpTo x s out = true
    · rw [ite_eq_left h, ite_eq_left (hitUpTo_succ_of_true h)]
      exact hmono s out ctx
    · simp [h, dyadicValue]
  · intro out ctx
    dsimp only
    have hd_mono : Monotone (fun s => dyadicValue (approx s out ctx) s) :=
      monotone_nat_of_le_succ (fun s => hmono s out ctx)
    by_cases hmem : out ∈ Set.range x
    · obtain ⟨i, hi⟩ := hmem
      have hhit : ∀ s, i ≤ s → hitUpTo x s out = true :=
        fun s hs => (hitUpTo_iff x s out).mpr ⟨i, hs, hi⟩
      have hval : (⨆ s, dyadicValue (if hitUpTo x s out then approx s out ctx else 0) s)
          = ⨆ s, dyadicValue (approx s out ctx) s := by
        apply le_antisymm
        · refine iSup_le fun s => ?_
          by_cases h : hitUpTo x s out = true
          · rw [ite_eq_left h]
            exact le_iSup (fun s => dyadicValue (approx s out ctx) s) s
          · simp [h, dyadicValue]
        · refine iSup_le fun s => ?_
          have hle : dyadicValue (approx s out ctx) s
              ≤ dyadicValue (approx (max s i) out ctx) (max s i) :=
            hd_mono (le_max_left s i)
          refine hle.trans ?_
          have := hhit (max s i) (le_max_right s i)
          calc dyadicValue (approx (max s i) out ctx) (max s i)
              = dyadicValue (if hitUpTo x (max s i) out then approx (max s i) out ctx else 0)
                  (max s i) := by rw [ite_eq_left this]
            _ ≤ _ := le_iSup
                  (fun s => dyadicValue (if hitUpTo x s out then approx s out ctx else 0) s)
                  (max s i)
      rw [hval, hsup out ctx]
      rw [Set.indicator_of_mem (Set.mem_range.mpr ⟨i, hi⟩)]
    · have hfalse : ∀ s, hitUpTo x s out ≠ true := by
        intro s hs
        obtain ⟨i, _, hi⟩ := (hitUpTo_iff x s out).mp hs
        exact hmem ⟨i, hi⟩
      have hzero : ∀ s, dyadicValue (if hitUpTo x s out then approx s out ctx else 0) s = 0 := by
        intro s
        rw [ite_eq_right (hfalse s), dyadicValue]
        simp
      rw [Set.indicator_of_notMem hmem]
      simp [hzero]
  · refine (Computable.cond (hitUpTo_computable hx) hcomp (Computable.const 0)).of_eq
      (fun p => ?_)
    dsimp only
    cases h : hitUpTo x p.1 p.2.1 <;> simp


/-- The universal continuous semimeasure restricted to the self-delimiting codes of the naturals is
a
lower semicomputable discrete semimeasure. -/
theorem natCodeRangeSection_isLowerSemicomputableSemimeasure :
    IsLowerSemicomputableSemimeasure (fun y => Set.indicator (Set.range natCode)
      universalContinuousSemimeasure y) := by
  constructor
  · have h_incomp : ∀ i j, i ≠ j → ¬ natCode i <+: natCode j :=
      fun i j hne hpre => hne (natCode_prefix_iff.mp hpre)
    exact tsum_rangeSection_le_one h_incomp []
  · have h_lsc : IsLSC (fun y ctx => universalContinuousSemimeasure y) :=
      universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.2
    exact IsLSC.indicator_range h_lsc natCode_computable

/-- Every finite partial sum of a discrete semimeasure is at most `1`. -/
theorem finset_sum_le_of_isSemimeasure {m : BitString → ℝ≥0∞} (hm : IsSemimeasure m)
    (S : Finset BitString) : ∑ x ∈ S, m x ≤ 1 := by
  calc
    ∑ x ∈ S, m x ≤ ∑' x, m x := ENNReal.sum_le_tsum S
    _ ≤ 1 := hm

/-- On the codes of the naturals the universal discrete semimeasure is below the universal
continuous
semimeasure up to a positive finite factor. -/
theorem universalSemimeasure_le_continuous_on_natCode
    {m : BitString → ℝ≥0∞} (hm : IsUniversalSemimeasure m) :
    ∃ c : ℝ≥0∞, 0 < c ∧ c ≠ ⊤ ∧
      ∀ n, c * m (natCode n) ≤ universalContinuousSemimeasure (natCode n) := by
  have h_free : ∀ S : Finset BitString, IsPrefixFree (S : Set BitString) → ∑ x ∈ S, m x ≤ 1 :=
    fun S _ => finset_sum_le_of_isSemimeasure hm.1.1 S
  obtain ⟨a, ha, hma⟩ := exists_lsc_continuousTreeSemimeasure_dominating_prefixFree m hm.1.2 h_free
  obtain ⟨c, hc_top, hca⟩ := universalContinuousSemimeasure_isMaximal a ha
  by_cases hc : c = 0
  · refine ⟨1, by norm_num, by norm_num, fun n => ?_⟩
    have : a (natCode n) = 0 := by
      have := hca (natCode n)
      rw [hc, zero_mul] at this
      exact le_antisymm this (zero_le)
    have h_mz : m (natCode n) = 0 := le_antisymm (this ▸ hma (natCode n)) (zero_le)
    rw [h_mz, mul_zero]
    exact zero_le
  · refine ⟨c⁻¹, ENNReal.inv_pos.mpr hc_top, ENNReal.inv_ne_top.mpr hc, fun n => ?_⟩
    calc
      c⁻¹ * m (natCode n) ≤ c⁻¹ * a (natCode n) := by gcongr; apply hma
      _ ≤ c⁻¹ * (c * universalContinuousSemimeasure (natCode n)) := by gcongr; apply hca
      _ = (c⁻¹ * c) * universalContinuousSemimeasure (natCode n) := by rw [mul_assoc]
      _ = 1 * universalContinuousSemimeasure (natCode n) := by
        rw [ENNReal.inv_mul_cancel hc hc_top]
      _ = universalContinuousSemimeasure (natCode n) := one_mul _

/-- On the codes of the naturals the universal continuous semimeasure is below the universal
discrete
semimeasure up to a positive finite factor. -/
theorem continuousSemimeasure_le_universal_on_natCode
    {m : BitString → ℝ≥0∞} (hm : IsUniversalSemimeasure m) :
    ∃ c : ℝ≥0∞, 0 < c ∧ c ≠ ⊤ ∧
      ∀ n, c * universalContinuousSemimeasure (natCode n) ≤ m (natCode n) := by
  have hm_c := natCodeRangeSection_isLowerSemicomputableSemimeasure
  obtain ⟨c, hc_pos, hc⟩ := hm.2 _ hm_c
  by_cases hc_top : c = ⊤
  · refine ⟨1, by norm_num, by norm_num, fun n => ?_⟩
    have : Set.indicator (Set.range natCode) universalContinuousSemimeasure (natCode n) = 0 := by
      have h := hc (natCode n)
      rw [hc_top] at h
      by_cases hz : Set.indicator (Set.range natCode) universalContinuousSemimeasure (natCode n) = 0
      · exact hz
      · rw [ENNReal.top_mul hz] at h
        have := hm.1.1
        have h_m : m (natCode n) ≤ 1 := by
          calc m (natCode n) ≤ ∑' x, m x := ENNReal.le_tsum _
            _ ≤ 1 := this
        have : (⊤ : ℝ≥0∞) ≤ 1 := h.trans h_m
        exact False.elim (by norm_num at this)
    have h_mz : universalContinuousSemimeasure (natCode n) = 0 := by
      rwa [Set.indicator_of_mem (Set.mem_range_self n)] at this
    rw [h_mz, mul_zero]
    exact zero_le
  · refine ⟨c, hc_pos, hc_top, fun n => ?_⟩
    calc
      c * universalContinuousSemimeasure (natCode n)
          = c * Set.indicator (Set.range natCode) universalContinuousSemimeasure (natCode n) := by
            rw [Set.indicator_of_mem (Set.mem_range_self n)]
      _ ≤ m (natCode n) := hc (natCode n)

/-- On the codes of the naturals the universal discrete and continuous semimeasures agree up to
constant factors. -/
theorem universalSemimeasure_natCode_equiv_continuous
    {m : BitString → ℝ≥0∞} (hm : IsUniversalSemimeasure m) :
    ∃ c₁ c₂ : ℝ≥0∞, 0 < c₁ ∧ c₁ ≠ ⊤ ∧ 0 < c₂ ∧ c₂ ≠ ⊤ ∧
      (∀ n, c₁ * m (natCode n) ≤ universalContinuousSemimeasure (natCode n)) ∧
      (∀ n, c₂ * universalContinuousSemimeasure (natCode n) ≤ m (natCode n)) := by
  obtain ⟨c₁, hc1_pos, hc1_top, hc1⟩ := universalSemimeasure_le_continuous_on_natCode hm
  obtain ⟨c₂, hc2_pos, hc2_top, hc2⟩ := continuousSemimeasure_le_universal_on_natCode hm
  exact ⟨c₁, c₂, hc1_pos, hc1_top, hc2_pos, hc2_top, hc1, hc2⟩


/-! ### Logarithmic form of Problem 126

The multiplicative two-sided comparison above is equivalent to an additive
comparison of the associated logarithmic complexities: the a priori complexity
`KA (natCode n)` and the discrete complexity `-log₂ m (natCode n)` differ by at
most an additive constant, uniformly in `n`. -/

/-- A multiplicative bound `c * u ≤ v` with positive finite `c`, `u` and finite `v`
turns into an additive bound between the negated base-2 logarithms. -/
theorem neg_logb_le_neg_logb_add_of_mul_le {c u v : ℝ≥0∞}
    (hc_pos : 0 < c) (hc_top : c ≠ ⊤) (hu_pos : 0 < u) (hu_top : u ≠ ⊤)
    (hv_top : v ≠ ⊤) (h : c * u ≤ v) :
    -Real.logb 2 v.toReal ≤ -Real.logb 2 u.toReal + -Real.logb 2 c.toReal := by
  have hcr : 0 < c.toReal := ENNReal.toReal_pos hc_pos.ne' hc_top
  have hur : 0 < u.toReal := ENNReal.toReal_pos hu_pos.ne' hu_top
  have hmul : c.toReal * u.toReal ≤ v.toReal := by
    have hle := ENNReal.toReal_mono hv_top h
    rwa [ENNReal.toReal_mul] at hle
  have hlog : Real.logb 2 (c.toReal * u.toReal) ≤ Real.logb 2 v.toReal :=
    Real.logb_le_logb_of_le (by norm_num) (mul_pos hcr hur) hmul
  rw [Real.logb_mul hcr.ne' hur.ne'] at hlog
  linarith

/-- Every semimeasure is bounded by `1`, hence finite. -/
theorem semimeasure_ne_top {m : BitString → ℝ≥0∞} (hm : IsSemimeasure m) (x : BitString) :
    m x ≠ ⊤ := by
  have : m x ≤ 1 := le_trans (ENNReal.le_tsum x) hm
  exact ne_top_of_le_ne_top (by norm_num) this

/-- A universal semimeasure is strictly positive on the prefix-free codes of integers,
because it dominates the (strictly positive) maximal continuous semimeasure there. -/
theorem universalSemimeasure_natCode_pos {m : BitString → ℝ≥0∞}
    (hm : IsUniversalSemimeasure m) (n : ℕ) : 0 < m (natCode n) := by
  obtain ⟨c, hc_pos, _, hc⟩ := continuousSemimeasure_le_universal_on_natCode hm
  refine lt_of_lt_of_le (ENNReal.mul_pos hc_pos.ne'
    (universalContinuousSemimeasure_pos (natCode n)).ne') (hc n)

/-- One half of the logarithmic form of Problem 126: a priori complexity of `natCode n`
is at most the discrete complexity `-log₂ m (natCode n)` plus a constant. -/
theorem KA_natCode_le_neg_logb_universalSemimeasure_add_const {m : BitString → ℝ≥0∞}
    (hm : IsUniversalSemimeasure m) :
    ∃ c : ℝ, ∀ n, KA (natCode n) ≤ -Real.logb 2 (m (natCode n)).toReal + c := by
  obtain ⟨c₁, hc_pos, hc_top, hc⟩ := universalSemimeasure_le_continuous_on_natCode hm
  refine ⟨-Real.logb 2 c₁.toReal, fun n => ?_⟩
  have hu_pos : 0 < m (natCode n) := universalSemimeasure_natCode_pos hm n
  have hu_top : m (natCode n) ≠ ⊤ := semimeasure_ne_top hm.1.1 _
  have hv_top : universalContinuousSemimeasure (natCode n) ≠ ⊤ :=
    universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.1.ne_top _
  exact neg_logb_le_neg_logb_add_of_mul_le hc_pos hc_top hu_pos hu_top hv_top (hc n)

/-- The other half of the logarithmic form of Problem 126: the discrete complexity
`-log₂ m (natCode n)` is at most the a priori complexity of `natCode n` plus a constant. -/
theorem neg_logb_universalSemimeasure_natCode_le_KA_add_const {m : BitString → ℝ≥0∞}
    (hm : IsUniversalSemimeasure m) :
    ∃ c : ℝ, ∀ n, -Real.logb 2 (m (natCode n)).toReal ≤ KA (natCode n) + c := by
  obtain ⟨c₂, hc_pos, hc_top, hc⟩ := continuousSemimeasure_le_universal_on_natCode hm
  refine ⟨-Real.logb 2 c₂.toReal, fun n => ?_⟩
  have hu_pos : 0 < universalContinuousSemimeasure (natCode n) :=
    universalContinuousSemimeasure_pos _
  have hu_top : universalContinuousSemimeasure (natCode n) ≠ ⊤ :=
    universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.1.ne_top _
  have hv_top : m (natCode n) ≠ ⊤ := semimeasure_ne_top hm.1.1 _
  exact neg_logb_le_neg_logb_add_of_mul_le hc_pos hc_top hu_pos hu_top hv_top (hc n)

/-- Logarithmic form of Problem 126: `KA (natCode n)` and the discrete complexity
`-log₂ m (natCode n)` of a universal semimeasure `m` differ by at most an additive
constant, uniformly in `n`. -/
theorem abs_KA_natCode_sub_neg_logb_universalSemimeasure_le {m : BitString → ℝ≥0∞}
    (hm : IsUniversalSemimeasure m) :
    ∃ c : ℝ, ∀ n, |KA (natCode n) - -Real.logb 2 (m (natCode n)).toReal| ≤ c := by
  obtain ⟨c₁, h₁⟩ := KA_natCode_le_neg_logb_universalSemimeasure_add_const hm
  obtain ⟨c₂, h₂⟩ := neg_logb_universalSemimeasure_natCode_le_KA_add_const hm
  refine ⟨max c₁ c₂, fun n => abs_le.mpr ⟨?_, ?_⟩⟩
  · have := h₂ n
    have hle : c₂ ≤ max c₁ c₂ := le_max_right _ _
    linarith
  · have := h₁ n
    have hle : c₁ ≤ max c₁ c₂ := le_max_left _ _
    linarith

end Kolmogorov
