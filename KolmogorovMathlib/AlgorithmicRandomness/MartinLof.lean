import KolmogorovMathlib.AlgorithmicRandomness.EffectiveNull
import KolmogorovMathlib.AlgorithmicRandomness.ComputableMeasure
import KolmogorovMathlib.AlgorithmicRandomness.Multiplicity
import KolmogorovMathlib.AlgorithmicRandomness.Disjointify
import KolmogorovMathlib.AlgorithmicRandomness.Universal

/-!
# Martin-Lof Randomness

This module defines Martin-Lof tests, Martin-Lof randomness, and develops
the theory of universal tests for computable measures (SUV Chapter 3.3).
-/

namespace Kolmogorov

open MeasureTheory ENNReal

/-- A Martin-Lof test for a measure `μ` is a uniformly effective open sequence
of sets whose measures decrease as `2⁻ⁿ`. -/
def IsMartinLofTest (μ : Measure CantorSeq) (U : ℕ → Set CantorSeq) : Prop :=
  IsUniformlyEffectiveOpen U ∧ ∀ n, μ (U n) ≤ dyadicValue 1 n

/-- A sequence `w` is Martin-Lof random with respect to `μ` if it does not
belong to the intersection of any Martin-Lof test. -/
def IsMartinLofRandom (μ : Measure CantorSeq) (w : CantorSeq) : Prop :=
  ∀ U, IsMartinLofTest μ U → w ∉ ⋂ n, U n

/-- A Martin-Lof test is universal if it subsumes all other effectively null sets.
Equivalently, it is the largest effectively null set. -/
def IsUniversalMartinLofTest (μ : Measure CantorSeq) (U : ℕ → Set CantorSeq) : Prop :=
  IsMartinLofTest μ U ∧ ∀ A, IsEffectivelyNull μ A → A ⊆ ⋂ n, U n

/-- **SUV Theorem 28.** For every computable measure, there exists a largest
effectively null set (equivalently, a universal Martin-Lof test). -/
theorem exists_universal_martinLof_test {μ : Measure CantorSeq}
    (hμ : IsComputableMeasure μ) : ∃ U, IsUniversalMartinLofTest μ U := by
  obtain ⟨a, hacomp, ha⟩ := hμ
  refine ⟨universalTest a, ⟨isUniformlyEffectiveOpen_universalTest hacomp,
    fun n => measure_universalTest_le ha n⟩, ?_⟩
  intro A hA
  obtain ⟨U, ⟨h, hh, hUeq⟩, hAU, hUbound⟩ := hA
  have hh' : Computable₂ (fun m i => h (m + 1) i) :=
    hh.comp (Primrec.succ.comp Primrec.fst).to_comp Computable.snd
  obtain ⟨c, hc⟩ := exists_code_candEnum hh'
  intro x hx
  refine Set.mem_iInter.2 fun n => ?_
  refine Set.mem_iUnion.2 ⟨c, ?_⟩
  have hlevel : (Nat.unpair (Nat.pair c (n + c + 1))).2 = n + c + 1 := by
    rw [Nat.unpair_pair]
  have hcand : (⋃ s, coverSet (candEnum (Nat.pair c (n + c + 1))) s) = U (n + c + 3) := by
    rw [hc (n + c + 1), hUeq (n + c + 3)]
    refine Set.iUnion_congr fun i => ?_
    rw [coverSet]
  have hsmall : μ (⋃ s, coverSet (candEnum (Nat.pair c (n + c + 1))) s)
      ≤ (2 : ℝ≥0∞)⁻¹ ^ ((Nat.unpair (Nat.pair c (n + c + 1))).2 + 2) := by
    rw [hcand, hlevel]
    have hb := hUbound (n + c + 3)
    rw [dyadicValue_one_eq_inv_two_pow'] at hb
    rwa [show n + c + 1 + 2 = n + c + 3 by ring]
  have huniv : univSet a (Nat.pair c (n + c + 1)) = U (n + c + 3) := by
    rw [univSet_eq_of_measure_le ha hsmall, hcand]
  rw [huniv]
  exact Set.mem_iInter.1 (hAU hx) (n + c + 3)

/-- The largest effectively null set is the set of all non-ML-random sequences.
(SUV Theorem 29) -/
theorem not_isMartinLofRandom_iff_mem_universal_test {μ : Measure CantorSeq}
    {U : ℕ → Set CantorSeq} (hU : IsUniversalMartinLofTest μ U) (w : CantorSeq) :
    ¬ IsMartinLofRandom μ w ↔ w ∈ ⋂ n, U n := by
  unfold IsMartinLofRandom
  constructor
  · intro h
    push_neg at h
    rcases h with ⟨V, hV, hwV⟩
    have hV_null : IsEffectivelyNull μ (⋂ n, V n) := by
      exact ⟨V, hV.1, Set.Subset.refl _, hV.2⟩
    have h_sub : (⋂ n, V n) ⊆ ⋂ n, U n := hU.2 _ hV_null
    exact h_sub hwV
  · intro hwU h_rand
    exact h_rand U hU.1 hwU

/-- A set is effectively null if and only if all its elements are not ML-random.
(SUV Theorem 29, set formulation) -/
theorem isEffectivelyNull_iff_forall_not_random {μ : Measure CantorSeq}
    (hμ : IsComputableMeasure μ) (A : Set CantorSeq) :
    IsEffectivelyNull μ A ↔ ∀ w ∈ A, ¬ IsMartinLofRandom μ w := by
  constructor
  · intro h w hw
    rcases h with ⟨U, hU1, hU2, hU3⟩
    intro h_rand
    exact h_rand U ⟨hU1, hU3⟩ (hU2 hw)
  · intro h
    rcases exists_universal_martinLof_test hμ with ⟨U, hU⟩
    have h_sub : A ⊆ ⋂ n, U n := by
      intro w hw
      have hnrand := h w hw
      rw [not_isMartinLofRandom_iff_mem_universal_test hU w] at hnrand
      exact hnrand
    exact ⟨U, hU.1.1, h_sub, hU.1.2⟩

/-- The set of all computable sequences is an effectively null set for the
uniform measure. (SUV Theorem 30) -/
theorem isEffectivelyNull_setOf_computable :
    IsEffectivelyNull uniformMeasure {w : CantorSeq | Computable w} := by
  rw [isEffectivelyNull_iff_forall_not_random isComputableMeasure_uniform]
  intro w hw
  have hsingle : IsEffectivelyNull uniformMeasure {w} :=
    isEffectivelyNull_singleton_of_computable hw
  have h := (isEffectivelyNull_iff_forall_not_random isComputableMeasure_uniform {w}).mp hsingle
  exact h w (Set.mem_singleton w)

/-- **SUV Theorem 31, easy direction.** If a computable sequence of intervals has
finite total measure and covers `w` infinitely many times, then `w` is not
ML-random: the multiplicity sets `M_N` of the family form a Martin-Lof test
containing `w`.

The computability hypothesis on the measure is kept to match the source
statement; the proof below does not use it, which is why the binder is named
`_hμ`. -/
theorem not_isMartinLofRandom_of_solovay_test {μ : Measure CantorSeq}
    (_hμ : IsComputableMeasure μ) (w : CantorSeq)
    (f : ℕ → Option BitString) (hf : Computable f)
    (h_sum : (∑' i, (f i).elim 0 (cantorMass μ)) < ∞)
    (h_inf : {i | w ∈ (f i).elim ∅ cantorCylinder}.Infinite) :
    ¬ IsMartinLofRandom μ w := by
  intro h_rand
  -- The total measure of the intervals is finite, so it is bounded by some integer `C`.
  have hsum' : (∑' i, μ (coverSet f i)) < ∞ := by
    have : (∑' i, μ (coverSet f i)) = ∑' i, (f i).elim 0 (cantorMass μ) :=
      tsum_congr fun i => measure_coverSet μ f i
    rw [this]; exact h_sum
  obtain ⟨C, hC⟩ := ENNReal.exists_nat_gt (ne_of_lt hsum')
  -- The multiplicity levels of the test.
  set N : ℕ → ℕ := fun m => (C + 1) * 2 ^ m with hNdef
  have hNcomp : Computable N :=
    (Primrec.nat_mul.comp (Primrec.const (C + 1)) primrec_two_pow_aux).to_comp
  have hNpos : ∀ m, N m ≠ 0 := by
    intro m
    simp [hNdef]
  refine h_rand (multiplicitySet f N)
    ⟨isUniformlyEffectiveOpen_multiplicitySet hf hNcomp, fun m => ?_⟩ ?_
  · -- Markov's inequality bounds the measure of the `m`-th multiplicity set.
    have hmono : μ (multiplicitySet f N m)
        ≤ μ {x | (N m : ℝ≥0∞) ≤ coverMultiplicity f x} :=
      measure_mono (multiplicitySet_subset m)
    have hmark := markov_coverMultiplicity μ f (N m)
    have hkey : (N m : ℝ≥0∞) * μ (multiplicitySet f N m) ≤ (C : ℝ≥0∞) :=
      le_trans (le_trans (by gcongr) hmark) (le_of_lt hC)
    have hprod : (N m : ℝ≥0∞) * dyadicValue 1 m = ((C : ℝ≥0∞) + 1) := by
      have hpow : ((2 : ℝ≥0∞) ^ m) * ((2 : ℝ≥0∞)⁻¹ ^ m) = 1 := by
        rw [← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow]
      rw [dyadicValue_one_eq_inv_two_pow']
      have hcast : ((N m : ℕ) : ℝ≥0∞) = ((C : ℝ≥0∞) + 1) * (2 : ℝ≥0∞) ^ m := by
        simp [hNdef]
      rw [hcast, mul_assoc, hpow, mul_one]
    have hle : (N m : ℝ≥0∞) * μ (multiplicitySet f N m)
        ≤ (N m : ℝ≥0∞) * dyadicValue 1 m := by
      rw [hprod]
      exact le_trans hkey (le_add_right (le_refl _))
    have hne0 : (N m : ℝ≥0∞) ≠ 0 := by
      simpa using hNpos m
    exact (ENNReal.mul_le_mul_iff_right hne0 (ENNReal.natCast_ne_top _)).mp hle
  · -- `w` is covered infinitely often, hence lies in every multiplicity set.
    refine Set.mem_iInter.2 fun m => ?_
    obtain ⟨S, hSsub, hScard⟩ := h_inf.exists_subset_card_eq (N m)
    set L : ℕ := S.sup (fun i => ((f i).getD []).length) with hL
    set s : BitString := cantorPrefix w L with hs
    have hcov : ∀ i ∈ S, coverBit f s i = true := by
      intro i hi
      have hwi : w ∈ coverSet f i := hSsub hi
      cases hfi : f i with
      | none => rw [coverSet, hfi] at hwi; simp at hwi
      | some t =>
        have hwt : w ∈ cantorCylinder t := by rw [coverSet, hfi] at hwi; simpa using hwi
        have hlen : t.length ≤ L := by
          have := Finset.le_sup (f := fun i => ((f i).getD []).length) hi
          simpa [hfi] using this
        have hpref : t <+: s := by
          have h1 : cantorPrefix w t.length = t :=
            (isCantorPrefix_iff_cantorPrefix_eq t w).1 hwt
          rw [hs, ← h1]
          exact cantorPrefix_mono w hlen
        simp [coverBit, hfi, (bitPrefixCheck_iff t s).2 hpref]
    have hsub : S ⊆ (Finset.range (S.sup id + 1)).filter (fun i => coverBit f s i = true) := by
      intro i hi
      refine Finset.mem_filter.2 ⟨Finset.mem_range.2 ?_, hcov i hi⟩
      have : i ≤ S.sup id := Finset.le_sup (f := id) hi
      omega
    have hcount : N m ≤ coverCount f s (S.sup id + 1) := by
      rw [coverCount_eq_card, ← hScard]
      exact Finset.card_le_card hsub
    exact mem_multiplicitySet hcount (mem_cantorCylinder_cantorPrefix w L)

/-- **SUV Theorem 31, hard direction.** If `w` is not ML-random, disjointifying the
levels of a Martin-Lof test covering `w` produces a Solovay test for `w`.

The computability hypothesis on the measure is kept to match the source
statement; the proof below does not use it, which is why the binder is named
`_hμ`. -/
theorem solovay_test_of_not_isMartinLofRandom {μ : Measure CantorSeq}
    (_hμ : IsComputableMeasure μ) (w : CantorSeq)
    (h : ¬ IsMartinLofRandom μ w) :
    ∃ f : ℕ → Option BitString, Computable f ∧
      (∑' i, (f i).elim 0 (cantorMass μ)) < ∞ ∧
      {i | w ∈ (f i).elim ∅ cantorCylinder}.Infinite := by
  unfold IsMartinLofRandom at h
  push_neg at h
  obtain ⟨U, hU, hwU⟩ := h
  obtain ⟨g, hg, hUeq⟩ := hU.1
  -- the levels of the test, disjointified and flattened
  refine ⟨fun i => disjEnum (g (Nat.unpair i).1) (Nat.unpair i).2, ?_, ?_, ?_⟩
  · exact (computable_disjEnum hg).comp
      (Primrec.fst.comp Primrec.unpair).to_comp (Primrec.snd.comp Primrec.unpair).to_comp
  · -- the total mass of the level `m` intervals is `μ (U m) ≤ 2 ^ (-m)`
    have hlevel : ∀ m, (∑' p, (disjEnum (g m) p).elim 0 (cantorMass μ)) ≤ dyadicValue 1 m := by
      intro m
      rw [tsum_measure_disjEnum μ (g m)]
      have hset : (⋃ j, coverSet (g m) j) = U m := (hUeq m).symm
      rw [hset]
      exact hU.2 m
    have hflat : (∑' i, (disjEnum (g (Nat.unpair i).1) (Nat.unpair i).2).elim 0 (cantorMass μ))
        = ∑' m, ∑' p, (disjEnum (g m) p).elim 0 (cantorMass μ) := by
      rw [← ENNReal.tsum_prod, ← Equiv.tsum_eq Nat.pairEquiv
        (fun i => (disjEnum (g (Nat.unpair i).1) (Nat.unpair i).2).elim 0 (cantorMass μ))]
      refine tsum_congr fun c => ?_
      have hpc : (Nat.pairEquiv c) = Nat.pair c.1 c.2 := rfl
      rw [hpc, Nat.unpair_pair]
    rw [hflat]
    have hgeo : (∑' m : ℕ, (2 : ℝ≥0∞)⁻¹ ^ m) = 2 := by
      rw [ENNReal.tsum_geometric]
      rw [show (1 : ℝ≥0∞) - 2⁻¹ = 2⁻¹ by
        rw [ENNReal.sub_eq_of_eq_add (by simp)]
        rw [ENNReal.inv_two_add_inv_two]]
      simp
    calc (∑' m, ∑' p, (disjEnum (g m) p).elim 0 (cantorMass μ))
        ≤ ∑' m : ℕ, (2 : ℝ≥0∞)⁻¹ ^ m := by
          refine ENNReal.tsum_le_tsum fun m => ?_
          simpa [dyadicValue_one_eq_inv_two_pow'] using hlevel m
      _ = 2 := hgeo
      _ < ∞ := by simp
  · -- `w` belongs to every level, hence to infinitely many of the intervals
    refine Set.infinite_of_forall_exists_gt fun a => ?_
    have hwUm : w ∈ U (a + 1) := Set.mem_iInter.mp hwU (a + 1)
    have hmem : w ∈ ⋃ p, coverSet (disjEnum (g (a + 1))) p := by
      rw [coverSet_disjEnum_iUnion]
      have hset : (⋃ j, coverSet (g (a + 1)) j) = U (a + 1) := (hUeq (a + 1)).symm
      rw [hset]
      exact hwUm
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hmem
    refine ⟨Nat.pair (a + 1) p, ?_, ?_⟩
    · change w ∈ (disjEnum (g (Nat.unpair (Nat.pair (a + 1) p)).1)
        (Nat.unpair (Nat.pair (a + 1) p)).2).elim ∅ cantorCylinder
      rw [Nat.unpair_pair]
      exact hp
    · have := Nat.left_le_pair (a + 1) p
      omega

/-- **SUV Theorem 31 (Solovay criterion).** A sequence `w` is not ML-random
if and only if there exists a computable sequence of intervals with finite
total measure covering `w` infinitely many times. -/
theorem not_isMartinLofRandom_iff_solovay_test {μ : Measure CantorSeq}
    (hμ : IsComputableMeasure μ) (w : CantorSeq) :
    ¬ IsMartinLofRandom μ w ↔
      ∃ f : ℕ → Option BitString, Computable f ∧
        (∑' i, (f i).elim 0 (cantorMass μ)) < ∞ ∧
        {i | w ∈ (f i).elim ∅ cantorCylinder}.Infinite := by
  constructor
  · exact solovay_test_of_not_isMartinLofRandom hμ w
  · rintro ⟨f, hf, h_sum, h_inf⟩
    exact not_isMartinLofRandom_of_solovay_test hμ w f hf h_sum h_inf

end Kolmogorov
