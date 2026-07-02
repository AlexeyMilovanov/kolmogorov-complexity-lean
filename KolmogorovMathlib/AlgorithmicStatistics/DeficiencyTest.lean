import KolmogorovMathlib.AlgorithmicStatistics.Stochasticity
import KolmogorovMathlib.AlgorithmicProbability.OptimalCoding
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitinCore

/-!
# Deficiency Tests for Coded Finite Distributions

The canonical test is now indexed by `CodedFiniteDistribution`, and therefore
conditions on `P.code` use the canonical code of the finite rational
distribution data.
-/

namespace Kolmogorov

open scoped ENNReal

/-- A randomness test for a coded probability model `P`. -/
structure RandomnessTest (P : CodedFiniteDistribution) where
  val : BitString -> ENNReal
  expectation_le_one : ∑ x ∈ P.support, P.mass x * val x <= 1

theorem RandomnessTest.val_bound (P : CodedFiniteDistribution) (t : RandomnessTest P) :
    ∑ x ∈ P.support, P.mass x * t.val x <= 1 :=
  t.expectation_le_one

/-- The conditional semimeasure associated to a test at the canonical model code. -/
noncomputable def weightedTestSemimeasure (P : CodedFiniteDistribution) (t : RandomnessTest P) :
    BitString -> BitString -> ENNReal :=
  fun x z => if z = P.code then P.mass x * t.val x else 0

/-
The weighted mass of a randomness test is a conditional semimeasure.

For coded list distributions this needs the finite-support zero-mass lemma for
`CodedFiniteDistribution.mass`, which is tracked separately.
-/
theorem weightedTestSemimeasure_isConditionalSemimeasure
    (P : CodedFiniteDistribution) (t : RandomnessTest P) :
    IsConditionalSemimeasure (weightedTestSemimeasure P t) := by
  intro z;
  by_cases h : z = P.code <;> simp +decide [ h, weightedTestSemimeasure ];
  rw [ tsum_eq_sum ];
  exact t.expectation_le_one;
  exact fun x hx => mul_eq_zero_of_left ( P.mass_eq_zero_of_not_mem_support x hx ) _

/-- The canonical test is `2^{-K(x|P.code)} / P.mass x`. -/
noncomputable def canonicalTest (U : Map) (P : CodedFiniteDistribution) : BitString -> ENNReal :=
  fun x => complexityWeight (KP U x P.code) * (P.mass x)⁻¹

/-- Conditional Kraft bound for prefix complexity weights at a fixed condition. -/
theorem KP_kraft_sum_le_one (U : Map) (hU : IsPrefixDecompressor U) (z : BitString) :
    (∑' x : BitString, complexityWeight (KP U x z)) <= 1 := by
  have h := tsum_aprioriMeasure_le_one U z hU.isPrefixMachine
  have h_le : ∀ x, complexityWeight (KP U x z) <= aprioriMeasure U x z := fun x =>
    complexityWeight_KP_le_aprioriMeasure U x z
  exact le_trans (ENNReal.tsum_le_tsum h_le) h

/-
Expectation bound for the coded canonical test.
-/
theorem canonicalTest_expectation_le_one (U : Map) (hU : IsOptimalPrefixConditional U)
    (P : CodedFiniteDistribution) :
    Finset.sum P.support (fun x => P.mass x * canonicalTest U P x) <= 1 := by
  apply le_trans _ ((KP_kraft_sum_le_one U (hU.isPrefixDecompressor) P.code) )
  apply le_trans _ ( ENNReal.sum_le_tsum P.support )
  apply Finset.sum_le_sum fun x hx => ?_
  convert mul_le_mul (le_refl ( complexityWeight ( KP U x P.code ) ))
      ( ENNReal.mul_inv_le_one ( P.mass x ) ) (zero_le _) (zero_le _) using 1 ; ring_nf;
  · unfold canonicalTest; ring_nf;
  · rw [ mul_one ]

/-- The canonical test is bounded by `2^beta` exactly when deficiency is bounded,
away from zero and infinite masses. -/
theorem canonicalTest_le_iff_deficiencyLe_of_mass_ne_zero_ne_top
    (U : Map) (P : CodedFiniteDistribution) (x : BitString) (beta : Nat)
    (h0 : P.mass x ≠ 0) (htop : P.mass x ≠ ⊤) :
    canonicalTest U P x <= (2 : ENNReal) ^ beta ↔ DeficiencyLe U P x beta := by
  unfold canonicalTest DeficiencyLe CodedFiniteDistribution.DeficiencyLe
  exact ENNReal.mul_inv_le_iff h0 htop

/-- If `x` has zero mass but finite conditional complexity, the canonical test is top. -/
theorem canonicalTest_top_of_mass_zero_of_KP_ne_top (U : Map) (P : CodedFiniteDistribution)
    (x : BitString) (h0 : P.mass x = 0) (hKP : KP U x P.code ≠ ⊤) :
    canonicalTest U P x = ⊤ := by
  unfold canonicalTest
  rw [h0, ENNReal.inv_zero]
  have hpos : 0 < complexityWeight (KP U x P.code) := (complexityWeight_pos_iff _).mpr hKP
  exact ENNReal.mul_top (ne_of_gt hpos)

/-- High deficiency is canonical-test largeness, under the usual positivity hypotheses. -/
theorem highDeficiency_iff_canonicalTest_gt_of_mass_ne_zero_ne_top
    (U : Map) (P : CodedFiniteDistribution) (x : BitString) (beta : Nat)
    (h0 : P.mass x ≠ 0) (htop : P.mass x ≠ ⊤) :
    HighDeficiency U P beta x ↔ (2 : ENNReal) ^ beta < canonicalTest U P x := by
  unfold HighDeficiency
  rw [← not_le]
  exact not_congr (canonicalTest_le_iff_deficiencyLe_of_mass_ne_zero_ne_top U P x beta h0 htop).symm

/-
Coding obligation behind maximality of the canonical deficiency test.
-/
theorem weightedTestSemimeasure_le_complexityWeight
    (U : Map) (hU : IsOptimalPrefixConditional U)
    (P : CodedFiniteDistribution) (t : RandomnessTest P)
    (hlsc : IsLSC (weightedTestSemimeasure P t)) :
    ∃ c : Nat, ∀ x : BitString,
      (2 : ENNReal)⁻¹ ^ c * (P.mass x * t.val x) <=
        complexityWeight (KP U x P.code) := by
  obtain ⟨M', hM', c₀, hreal⟩ := kraftChaitin_realization_bound_unit hlsc (by
  convert weightedTestSemimeasure_isConditionalSemimeasure P t using 1);
  obtain ⟨ c, hc ⟩ := complexityWeight_dominates_of_prefix_realization hU hM' hreal;
  exact ⟨ c, fun x => by simpa [ weightedTestSemimeasure ] using hc x P.code ⟩

/-
Pointwise algebra turning weighted-semimeasure domination into canonical-test domination.
-/
theorem randomnessTest_le_canonicalTest_of_weighted_bound
    (U : Map) (P : CodedFiniteDistribution) (t : RandomnessTest P) (c : Nat)
    {x : BitString} (hmass0 : P.mass x ≠ 0) (hmass_top : P.mass x ≠ ⊤)
    (hbound :
      (2 : ENNReal)⁻¹ ^ c * (P.mass x * t.val x) <=
        complexityWeight (KP U x P.code)) :
    t.val x <= (2 : ENNReal) ^ c * canonicalTest U P x := by
  have h_mul : P.mass x * t.val x ≤ (2 : ENNReal) ^ c * complexityWeight (KP U x P.code) := by
    have htmp := mul_le_mul (le_refl ((2 : ENNReal) ^ c)) hbound (zero_le _) (zero_le _)
    have hcancel :
        (2 : ENNReal) ^ c * ((2 : ENNReal)⁻¹ ^ c * (P.mass x * t.val x)) =
          P.mass x * t.val x := by
      rw [← mul_assoc, ← mul_pow, ENNReal.mul_inv_cancel] <;> norm_num
    simpa [hcancel] using htmp
  have htmp := mul_le_mul h_mul (le_refl ((P.mass x)⁻¹)) (zero_le _) (zero_le _)
  calc
    t.val x = t.val x * (P.mass x * (P.mass x)⁻¹) := by
      rw [ENNReal.mul_inv_cancel hmass0 hmass_top, mul_one]
    _ = (P.mass x * t.val x) * (P.mass x)⁻¹ := by
      ac_rfl
    _ ≤ ((2 : ENNReal) ^ c * complexityWeight (KP U x P.code)) * (P.mass x)⁻¹ := htmp
    _ = (2 : ENNReal) ^ c * canonicalTest U P x := by
      unfold canonicalTest
      ac_rfl

/-
Maximality of the coded canonical deficiency test, with explicit support
positivity and finite-mass hypotheses.
-/
theorem canonicalTest_is_maximal (U : Map) (P : CodedFiniteDistribution)
    (hU : IsOptimalPrefixConditional U) (t : RandomnessTest P) (c : Nat)
    (hlsc : IsLSC (weightedTestSemimeasure P t))
    (hsupport_pos : ∀ x ∈ P.support, P.mass x ≠ 0)
    (hsupport_finite : ∀ x ∈ P.support, P.mass x ≠ ⊤) :
    ∃ O1 : Nat, ∀ x ∈ P.support,
      t.val x <= (2 : ENNReal) ^ (c + O1) * canonicalTest U P x := by
  obtain ⟨c', hc'⟩ := weightedTestSemimeasure_le_complexityWeight U hU P t hlsc;
  refine ⟨ c', fun x hx => ?_ ⟩;
  exact le_trans
    (randomnessTest_le_canonicalTest_of_weighted_bound U P t c'
      (hsupport_pos x hx) (hsupport_finite x hx) (hc' x))
    (by
      exact mul_le_mul
        (pow_le_pow_right₀ (by norm_num : (1 : ENNReal) ≤ 2) (Nat.le_add_left c' c))
        (le_refl _) (zero_le _) (zero_le _))

end Kolmogorov
