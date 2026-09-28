/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.MonotoneComplexity.LevinSchnorr.AmpleExcess
import KolmogorovMathlib.MonotoneComplexity.LevinSchnorr.Basic
import KolmogorovMathlib.MonotoneComplexity.LevinSchnorr.ComputableCover
import KolmogorovMathlib.MonotoneComplexity.LevinSchnorr.CondArithmeticCoding
import KolmogorovMathlib.MonotoneComplexity.LevinSchnorr.Converse
import KolmogorovMathlib.MonotoneComplexity.LevinSchnorr.PlainCriteria
import KolmogorovMathlib.MonotoneComplexity.LevinSchnorr.SummableWeight
import KolmogorovMathlib.MonotoneComplexity.LevinSchnorr.UniformFinsetCriterion
import KolmogorovMathlib.MonotoneComplexity.LevinSchnorr.Exercises
import KolmogorovMathlib.MonotoneComplexity.PlainPrefixDips
import KolmogorovMathlib.Prefix.OptimalExistence

/-!
# Section 5.6: the Levin-Schnorr theorem and the prefix/plain characterisations

Skeleton (milestone C10) for Theorems 89-99 of Shen-Uspensky-Vereshchagin, Section 5.6.

Everything is stated for a *computable probability measure* `μ` on Cantor space with
`p(x) = μ(Ω_x) = cantorMass μ x`, and for an *optimal* monotone decompressor `D`
(`KM = KMOf D`), an *optimal* prefix decompressor `U` (`K = KPPlain U`, `KP U`) and an
*optimal* conditional plain decompressor `V` (`C = plainK V`, `C(· | ·) = condK V`).
The a priori complexity `KA` is `- log₂` of `universalContinuousSemimeasure`.

The source inequality `-log p(x) - complexity(x) ≤ c` is rendered multiplicatively; see the
module docstring of `LevinSchnorr/Basic.lean` for why.

Directions of an "iff" that the source proves separately are stated as separate leaves; the
combined `iff` is then a one-line consequence and carries no `sorry` of its own.
-/

namespace Kolmogorov

open MeasureTheory
open scoped ENNReal

/-! ## Theorem 89: computable measures are monotone-compressible -/

/-! ## Theorem 90: the Levin-Schnorr theorem

The source proof has two named lemmas.  Lemma 1 is the measure bound on the set of sequences
with a prefix in `D_c`; Lemma 2 (disjointification of an enumerable set of strings) is already
available in Chapter 3 and is only recorded here.
-/

/-- SUV Theorem 90, Lemma 1 (Section 5.6, p. 146): the set of infinite sequences that have a
prefix in `D_c` has `μ`-measure at most `2^(-c)`.

The source argument: pass to the prefix-minimal elements `x₀, x₁, …` of `D_c`, take a minimal
program `pᵢ` for each `xᵢ`; the `pᵢ` are pairwise incomparable, so `∑ 2^(-l(pᵢ)) ≤ 1`, and
each `μ(Ω_{xᵢ})` is `2^c` times smaller than `2^(-l(pᵢ))`. -/
theorem measure_prefixHitSet_le_of_tsum_antichain_le (μ : Measure CantorSeq)
    (f : BitString → ℝ≥0∞) (c : ℕ)
    (hf : ∀ S : Set BitString, (∀ y ∈ S, ∀ z ∈ S, y <+: z → y = z) →
      ∑' x : S, f (x : BitString) ≤ 1) :
    μ (prefixHitSet {x : BitString | (2 : ℝ≥0∞) ^ c * cantorMass μ x < f x})
      ≤ (2 : ℝ≥0∞)⁻¹ ^ c := by
  classical
  set S : Set BitString := {x : BitString | (2 : ℝ≥0∞) ^ c * cantorMass μ x < f x} with hSdef
  have hinv : ((2 : ℝ≥0∞)⁻¹) ^ c * (2 : ℝ≥0∞) ^ c = 1 := by
    rw [← mul_pow, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_pow]
  have hterm : ∀ x : minimalPrefixElements S,
      cantorMass μ (x : BitString) ≤ (2 : ℝ≥0∞)⁻¹ ^ c * f (x : BitString) := by
    rintro ⟨x, hx⟩
    have hxS : (2 : ℝ≥0∞) ^ c * cantorMass μ x < f x := hx.1
    calc cantorMass μ x
        = (2 : ℝ≥0∞)⁻¹ ^ c * ((2 : ℝ≥0∞) ^ c * cantorMass μ x) := by
          rw [← mul_assoc, hinv, one_mul]
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ c * f x := by gcongr
  calc μ (prefixHitSet S)
      ≤ ∑' x : minimalPrefixElements S, cantorMass μ (x : BitString) :=
        measure_prefixHitSet_le_tsum_minimalPrefixElements μ S
    _ ≤ ∑' x : minimalPrefixElements S, (2 : ℝ≥0∞)⁻¹ ^ c * f (x : BitString) :=
        ENNReal.tsum_le_tsum hterm
    _ = (2 : ℝ≥0∞)⁻¹ ^ c * ∑' x : minimalPrefixElements S, f (x : BitString) :=
        ENNReal.tsum_mul_left
    _ ≤ (2 : ℝ≥0∞)⁻¹ ^ c * 1 := by
        gcongr
        exact hf _ (minimalPrefixElements_antichain S)
    _ = (2 : ℝ≥0∞)⁻¹ ^ c := mul_one _

/-- SUV Theorem 90, Lemma 1 (Section 5.6, p. 146): the set of infinite sequences that have a
prefix in `D_c` has `μ`-measure at most `2^(-c)`. -/
theorem measure_prefixHitSet_monotoneDeficiencySet_le {μ : Measure CantorSeq}
    [IsProbabilityMeasure μ] {D : BitStream → BitStream}
    (hD : IsOptimalMonotoneDecompressor D) (c : ℕ) :
    μ (prefixHitSet (monotoneDeficiencySet μ D c)) ≤ (2 : ℝ≥0∞)⁻¹ ^ c :=
  measure_prefixHitSet_le_of_tsum_antichain_le μ (fun x => complexityWeight (KMOf D x)) c
    (fun S hS => tsum_antichain_complexityWeight_KMOf_le_one hD.1 S hS)

/-- SUV Theorem 90, Lemma 2 (Section 5.6, p. 147): every enumerable set of strings can be
effectively transformed into an enumerable set of pairwise incompatible strings with the same
union of cylinders.

Already available in Chapter 3 as `disjEnum` together with `computable_disjEnum`; this
statement only records the two set-theoretic halves under the Section 5.6 name. -/
theorem coverSet_disjEnum_spec (h : ℕ → Option BitString) :
    (⋃ i, coverSet (disjEnum h) i) = (⋃ j, coverSet h j) ∧
      Pairwise (Function.onFun Disjoint (coverSet (disjEnum h))) :=
  ⟨coverSet_disjEnum_iUnion h, coverSet_disjEnum_pairwise h⟩

/-- SUV Theorem 90 (Levin-Schnorr, Section 5.6, p. 146), first direction: if `w` is
Martin-Löf random with respect to the computable probability measure `μ`, then
`-log p(x) - KM(x) ≤ c` for one constant `c` and every prefix `x` of `w`.

Source proof: `D_c` is enumerable (`isRE_monotoneDeficiencySet`), Lemma 1 bounds the measure
of `prefixHitSet (D_c)` by `2^(-c)`, and Lemma 2 turns the covering into a family of disjoint
intervals; the resulting family is a Martin-Löf test containing `w`. -/
theorem boundedMonotoneDeficiency_of_isMartinLofRandom {μ : Measure CantorSeq}
    [IsProbabilityMeasure μ] (hμ : IsComputableMeasure μ) {D : BitStream → BitStream}
    (hD : IsOptimalMonotoneDecompressor D) {w : CantorSeq}
    (hw : IsMartinLofRandom μ w) :
    BoundedMonotoneDeficiency μ D w := by
  by_contra hcon
  rw [boundedMonotoneDeficiency_iff_forall_not_mem] at hcon
  push_neg at hcon
  refine hw _ (isMartinLofTest_prefixHitSet (isRE_monotoneDeficiencySet hμ hD)
    (fun c => measure_prefixHitSet_monotoneDeficiencySet_le hD c))
    (Set.mem_iInter.2 fun c => ?_)
  obtain ⟨n, hn⟩ := hcon c
  exact ⟨n, hn⟩

/-- SUV Theorem 90 (Levin-Schnorr, Section 5.6, p. 146), converse direction: if
`-log p(x) - KM(x) ≤ c` for one constant `c` and every prefix `x` of `w`, then `w` is
Martin-Löf random with respect to `μ`.

Source proof: from a cover of an effectively null set by intervals of total measure `< 2^(-c)`
build, by Kraft-Chaitin (Theorem 59, p. 96), a prefix-free decompressor `D_c` with
`K_{D_c}(x_i) ≤ -log μ(Ω_{x_i}) - c + 2`, then combine the `D_c` into one decompressor with an
`O(log c)` self-delimiting tag. -/
theorem isMartinLofRandom_of_boundedMonotoneDeficiency {μ : Measure CantorSeq}
    [IsProbabilityMeasure μ] (hμ : IsComputableMeasure μ) {D : BitStream → BitStream}
    (hD : IsOptimalMonotoneDecompressor D) {w : CantorSeq}
    (hw : BoundedMonotoneDeficiency μ D w) :
    IsMartinLofRandom μ w := by
  obtain ⟨U, hU⟩ := exists_isOptimalPrefixConditional
  exact isMartinLofRandom_of_boundedPrefixDeficiency_core hμ hU
    (boundedPrefixDeficiency_of_boundedMonotoneDeficiency hD hU hw)

/-- SUV Theorem 90 (Levin-Schnorr, Section 5.6, p. 146): a sequence `w` is Martin-Löf random
with respect to a computable probability distribution `μ` if and only if
`-log p(x) - KM(x) ≤ c` for some `c` and every prefix `x` of `w`. -/
theorem isMartinLofRandom_iff_boundedMonotoneDeficiency {μ : Measure CantorSeq}
    [IsProbabilityMeasure μ] (hμ : IsComputableMeasure μ) {D : BitStream → BitStream}
    (hD : IsOptimalMonotoneDecompressor D) (w : CantorSeq) :
    IsMartinLofRandom μ w ↔ BoundedMonotoneDeficiency μ D w :=
  ⟨fun hw => boundedMonotoneDeficiency_of_isMartinLofRandom hμ hD hw,
    fun hw => isMartinLofRandom_of_boundedMonotoneDeficiency hμ hD hw⟩

/-! ## Theorem 91: the same criterion with a priori complexity -/

/-- SUV Theorem 91, Lemma 1 in a priori form (Section 5.6, p. 148): the set of sequences with
a prefix of a priori deficiency above `c` has `μ`-measure at most `2^(-c)`.

Source proof: `∑ᵢ 2^(-KA(xᵢ)) ≤ 1` because this is the sum of a priori measures of disjoint
intervals `Ω_{xᵢ}`. -/
theorem measure_prefixHitSet_aPrioriDeficiencySet_le {μ : Measure CantorSeq}
    [IsProbabilityMeasure μ] (c : ℕ) :
    μ (prefixHitSet (aPrioriDeficiencySet μ c)) ≤ (2 : ℝ≥0∞)⁻¹ ^ c :=
  measure_prefixHitSet_le_of_tsum_antichain_le μ universalContinuousSemimeasure c
    tsum_antichain_universalContinuousSemimeasure_le_one

/-- SUV Theorem 91 (Section 5.6, p. 148), first direction: a Martin-Löf random sequence
satisfies `-log p(x) - KA(x) ≤ c` for one constant `c` and every prefix `x`.  This is the only
half the source has to redo, since `KA ≤ KM + O(1)`. -/
theorem boundedAPrioriDeficiency_of_isMartinLofRandom {μ : Measure CantorSeq}
    [IsProbabilityMeasure μ] (hμ : IsComputableMeasure μ) {w : CantorSeq}
    (hw : IsMartinLofRandom μ w) :
    BoundedAPrioriDeficiency μ w := by
  by_contra hcon
  rw [boundedAPrioriDeficiency_iff_forall_not_mem] at hcon
  push_neg at hcon
  refine hw _ (isMartinLofTest_prefixHitSet (isRE_aPrioriDeficiencySet hμ)
    (fun c => measure_prefixHitSet_aPrioriDeficiencySet_le c))
    (Set.mem_iInter.2 fun c => ?_)
  obtain ⟨n, hn⟩ := hcon c
  exact ⟨n, hn⟩

/-- SUV Theorem 91 (Section 5.6, p. 148), converse direction: if `-log p(x) - KA(x) ≤ c` for
one `c` and every prefix `x` of `w`, then `w` is Martin-Löf random with respect to `μ`.
Since `KA ≤ KM + O(1)`, the a priori hypothesis implies the monotone one of Theorem 90. -/
theorem isMartinLofRandom_of_boundedAPrioriDeficiency {μ : Measure CantorSeq}
    [IsProbabilityMeasure μ] (hμ : IsComputableMeasure μ) {w : CantorSeq}
    (hw : BoundedAPrioriDeficiency μ w) :
    IsMartinLofRandom μ w := by
  obtain ⟨D, hD⟩ := exists_optimalMonotoneDecompressor
  obtain ⟨c, hc⟩ := hw
  obtain ⟨c₀, hc₀⟩ := exists_nat_complexityWeight_KMOf_le_universalContinuousSemimeasure hD.1
  refine isMartinLofRandom_of_boundedMonotoneDeficiency hμ hD ⟨c₀ + c, fun n => ?_⟩
  calc complexityWeight (KMOf D (cantorPrefix w n))
      ≤ (2 : ℝ≥0∞) ^ c₀ * universalContinuousSemimeasure (cantorPrefix w n) := hc₀ _
    _ ≤ (2 : ℝ≥0∞) ^ c₀ * ((2 : ℝ≥0∞) ^ c * cantorMass μ (cantorPrefix w n)) := by
        gcongr
        exact hc n
    _ = (2 : ℝ≥0∞) ^ (c₀ + c) * cantorMass μ (cantorPrefix w n) := by
        rw [pow_add]; ring

/-- SUV Theorem 91 (Section 5.6, p. 148): the Levin-Schnorr criterion holds verbatim with the
monotone complexity `KM` replaced by the a priori complexity `KA`. -/
theorem isMartinLofRandom_iff_boundedAPrioriDeficiency {μ : Measure CantorSeq}
    [IsProbabilityMeasure μ] (hμ : IsComputableMeasure μ) (w : CantorSeq) :
    IsMartinLofRandom μ w ↔ BoundedAPrioriDeficiency μ w :=
  ⟨fun hw => boundedAPrioriDeficiency_of_isMartinLofRandom hμ hw,
    fun hw => isMartinLofRandom_of_boundedAPrioriDeficiency hμ hw⟩

/-! ## Theorem 92: the same criterion with prefix complexity -/

/-- SUV Theorem 92 (Section 5.6, p. 148), first direction: a Martin-Löf random sequence
satisfies `-log p(x) - K(x) ≤ c` for one constant `c` and every prefix `x`.  Since
`KM ≤ K + O(1)`, this follows from the corresponding half of Theorem 90. -/
theorem boundedPrefixDeficiency_of_isMartinLofRandom {μ : Measure CantorSeq}
    [IsProbabilityMeasure μ] (hμ : IsComputableMeasure μ) {U : Map}
    (hU : IsOptimalPrefixConditional U) {w : CantorSeq} (hw : IsMartinLofRandom μ w) :
    BoundedPrefixDeficiency μ U w := by
  obtain ⟨D, hD⟩ := exists_optimalMonotoneDecompressor
  exact boundedPrefixDeficiency_of_boundedMonotoneDeficiency hD hU
    (boundedMonotoneDeficiency_of_isMartinLofRandom hμ hD hw)

/-- SUV Theorem 92 (Section 5.6, p. 148): the Levin-Schnorr criterion holds with the monotone
complexity `KM` replaced by the prefix complexity `K`. -/
theorem isMartinLofRandom_iff_boundedPrefixDeficiency {μ : Measure CantorSeq}
    [IsProbabilityMeasure μ] (hμ : IsComputableMeasure μ) {U : Map}
    (hU : IsOptimalPrefixConditional U) (w : CantorSeq) :
    IsMartinLofRandom μ w ↔ BoundedPrefixDeficiency μ U w :=
  ⟨fun hw => boundedPrefixDeficiency_of_isMartinLofRandom hμ hU hw,
    fun hw => isMartinLofRandom_of_boundedPrefixDeficiency_core hμ hU hw⟩

/-! ## Theorem 93: for a non-random sequence the monotone deficiency tends to infinity -/

/-- SUV Theorem 93 (Section 5.6, p. 149): "if a sequence `ω` is not random with respect to
measure `μ`, then the difference `-log p(x) - KM(x)` for prefixes `x` (of `ω`) is not only
unbounded but also tends to infinity".  Spelled out: for every `c` all sufficiently long
prefixes have deficiency at least `c`, i.e. `-log p(x) - KM(x) ≥ c`, which in the
multiplicative form of `Basic.lean` is `2^c * p(x) ≤ 2^(-KM(x))`.

No positivity hypothesis on `p(x)` is needed: at a null prefix the deficiency is `+∞`, and the
multiplicative form is then the true inequality `0 ≤ 2^(-KM(x))`.  (The positivity of
`μ(Ω_x)` is needed only inside the proof, in the relativised Theorem 89
`exists_const_condCantorMass_mul_le_complexityWeight_condKMOf`.)

Source proof: use `KM(xy) ≤ K(x) + KM(y | x) + O(1)` (Problem 135) together with the
relativised Theorem 89 `KM(y | x) ≤ -log μ_x(Ω_y) + O(1)`. -/
theorem tendsto_monotoneDeficiency_of_not_isMartinLofRandom {μ : Measure CantorSeq}
    [IsProbabilityMeasure μ] (hμ : IsComputableMeasure μ) {D : BitStream → BitStream}
    (hD : IsOptimalMonotoneDecompressor D) {w : CantorSeq}
    (hw : ¬ IsMartinLofRandom μ w) :
    ∀ c : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (2 : ℝ≥0∞) ^ c * cantorMass μ (cantorPrefix w n)
        ≤ complexityWeight (KMOf D (cantorPrefix w n)) := by
  intro c
  obtain ⟨U, hU⟩ := exists_isOptimalPrefixConditional
  obtain ⟨Dc, hDc⟩ := exists_optimalConditionalMonotoneDecompressor
  obtain ⟨c₁, hc₁⟩ := problem_135_KMOf_append_le_KPPlain_add_condKMOf hD hU hDc
  obtain ⟨c₂, hc₂⟩ := exists_const_condCantorMass_mul_le_complexityWeight_condKMOf μ hμ hDc
  obtain ⟨N, hN⟩ := exists_prefix_two_pow_mul_cantorMass_lt_complexityWeight_KPPlain
    hμ hU hw (c + c₁ + c₂)
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨y, hy⟩ := cantorPrefix_mono w hn
  rw [← hy]
  set x : BitString := cantorPrefix w N with hxdef
  rcases eq_or_ne (cantorMass μ x) 0 with hzero | hpos
  · have hsub : cantorMass μ (x ++ y) ≤ cantorMass μ x :=
      measure_mono (cantorCylinder_subset_of_prefix ⟨y, rfl⟩)
    have hxy0 : cantorMass μ (x ++ y) = 0 := by
      rw [hzero] at hsub
      exact le_antisymm hsub (zero_le _)
    rw [hxy0, mul_zero]
    exact zero_le _
  · have hmassne : cantorMass μ x ≠ ⊤ := measure_ne_top μ _
    have hcancel1 : (2 : ℝ≥0∞) ^ c₁ * (2 : ℝ≥0∞)⁻¹ ^ c₁ = 1 := by
      rw [← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow]
    have hcancel2 : (2 : ℝ≥0∞) ^ c₂ * (2 : ℝ≥0∞)⁻¹ ^ c₂ = 1 := by
      rw [← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow]
    have hdiv : cantorMass μ x * condCantorMass μ x y = cantorMass μ (x ++ y) := by
      rw [condCantorMass]
      exact ENNReal.mul_div_cancel' (fun h => absurd h hpos) (fun h => absurd h hmassne)
    have hstep : complexityWeight (KPPlain U x)
          * ((2 : ℝ≥0∞)⁻¹ ^ c₂ * condCantorMass μ x y) * (2 : ℝ≥0∞)⁻¹ ^ c₁
        ≤ complexityWeight (KMOf D (x ++ y)) := by
      refine le_trans ?_ (complexityWeight_le_of_le (hc₁ x y))
      rw [complexityWeight_add', complexityWeight_add', complexityWeight_coe]
      gcongr
      exact hc₂ x hpos y
    refine le_trans ?_ hstep
    calc (2 : ℝ≥0∞) ^ c * cantorMass μ (x ++ y)
        = (2 : ℝ≥0∞) ^ c * ((2 : ℝ≥0∞) ^ c₁ * (2 : ℝ≥0∞)⁻¹ ^ c₁)
            * ((2 : ℝ≥0∞) ^ c₂ * (2 : ℝ≥0∞)⁻¹ ^ c₂)
            * (cantorMass μ x * condCantorMass μ x y) := by
          rw [hcancel1, hcancel2, hdiv]; ring
      _ = ((2 : ℝ≥0∞) ^ (c + c₁ + c₂) * cantorMass μ x)
            * ((2 : ℝ≥0∞)⁻¹ ^ c₂ * condCantorMass μ x y) * (2 : ℝ≥0∞)⁻¹ ^ c₁ := by
          rw [pow_add, pow_add]; ring
      _ ≤ complexityWeight (KPPlain U x)
            * ((2 : ℝ≥0∞)⁻¹ ^ c₂ * condCantorMass μ x y) * (2 : ℝ≥0∞)⁻¹ ^ c₁ := by
          gcongr

/-- SUV Theorem 93, reformulation (Section 5.6, p. 149): "if the difference `log p(x) - KM(x)`
is uniformly bounded for infinitely many prefixes `x` of some sequence `ω`, then `ω` is
random."  The hypothesis is the deficiency bound `-log p(x) - KM(x) ≤ c` of
`BoundedMonotoneDeficiency`, imposed only at infinitely many `n`; this is the contrapositive of
the leaf above, whose conclusion makes the set of such `n` finite. -/
theorem isMartinLofRandom_of_boundedMonotoneDeficiency_infinitely_often
    {μ : Measure CantorSeq} [IsProbabilityMeasure μ] (hμ : IsComputableMeasure μ)
    {D : BitStream → BitStream} (hD : IsOptimalMonotoneDecompressor D) {w : CantorSeq}
    (hw : ∃ c : ℕ, {n : ℕ | complexityWeight (KMOf D (cantorPrefix w n))
      ≤ (2 : ℝ≥0∞) ^ c * cantorMass μ (cantorPrefix w n)}.Infinite) :
    IsMartinLofRandom μ w := by
  by_contra hnr
  obtain ⟨c, hinf⟩ := hw
  obtain ⟨N, hN⟩ := tendsto_monotoneDeficiency_of_not_isMartinLofRandom hμ hD hnr (c + 1)
  obtain ⟨n, hnmem, hngt⟩ := hinf.exists_gt N
  have h1 := hN n hngt.le
  have h2 : complexityWeight (KMOf D (cantorPrefix w n))
      ≤ (2 : ℝ≥0∞) ^ c * cantorMass μ (cantorPrefix w n) := hnmem
  have hmfin : cantorMass μ (cantorPrefix w n) ≠ ⊤ := measure_ne_top μ _
  have h2m : (2 : ℝ≥0∞) ^ c * cantorMass μ (cantorPrefix w n) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top (by norm_num)) hmfin
  have hchain : (2 : ℝ≥0∞) ^ (c + 1) * cantorMass μ (cantorPrefix w n)
      ≤ (2 : ℝ≥0∞) ^ c * cantorMass μ (cantorPrefix w n) := le_trans h1 h2
  have hdouble : (2 : ℝ≥0∞) ^ c * cantorMass μ (cantorPrefix w n)
      + (2 : ℝ≥0∞) ^ c * cantorMass μ (cantorPrefix w n)
      ≤ 0 + (2 : ℝ≥0∞) ^ c * cantorMass μ (cantorPrefix w n) := by
    rw [zero_add, ← two_mul, ← mul_assoc, ← pow_succ']
    exact hchain
  have hzero : (2 : ℝ≥0∞) ^ c * cantorMass μ (cantorPrefix w n) = 0 :=
    le_antisymm ((ENNReal.add_le_add_iff_right h2m).1 hdouble) (zero_le _)
  have hcw : complexityWeight (KMOf D (cantorPrefix w n)) = 0 :=
    le_antisymm (hzero ▸ h2) (zero_le _)
  exact KMOf_ne_top_of_isOptimal hD (cantorPrefix w n)
    ((complexityWeight_eq_zero_iff _).1 hcw)

/-! ## Theorem 94: the uniform measure -/

/-- SUV Theorem 94(a) (Section 5.6, p. 151): `KA(x) ≤ KM(x) + O(1) ≤ l(x) + O(1)`.

Both halves are already proved in Chapter 5 (Theorem 85(e) and Theorem 85(c)); this
statement only packages them under the Section 5.6 name. -/
theorem KA_le_KMOf_le_length {D : BitStream → BitStream}
    (hD : IsOptimalMonotoneDecompressor D) :
    (∃ c : ℝ, ∀ x : BitString, KA x ≤ ((KMOf D x).toNat : ℝ) + c) ∧
      (∃ c : ℕ, ∀ x : BitString, KMOf D x ≤ (x.length : ℕ∞) + c) :=
  ⟨exists_const_KA_le_KMOf hD, exists_const_KMOf_le_length hD⟩

/-- SUV Theorem 94(b) (Section 5.6, p. 151): `w` is Martin-Löf random with respect to the
uniform measure if and only if the inequalities of 94(a) become equalities on its prefixes,
`KA((w)_n) = KM((w)_n) + O(1) = n + O(1)`, with one constant for all `n`. -/
theorem isMartinLofRandom_uniform_iff_KA_KMOf_eq_length {D : BitStream → BitStream}
    (hD : IsOptimalMonotoneDecompressor D) (w : CantorSeq) :
    IsMartinLofRandom uniformMeasure w ↔
      ∃ c : ℝ, ∀ n : ℕ, |KA (cantorPrefix w n) - (n : ℝ)| ≤ c ∧
        |((KMOf D (cantorPrefix w n)).toNat : ℝ) - (n : ℝ)| ≤ c := by
  constructor
  · intro hrand
    obtain ⟨c₁, hc₁⟩ := exists_const_le_KA_cantorPrefix_of_isMartinLofRandom hrand
    obtain ⟨c₂, hc₂⟩ := exists_const_KA_le_KMOf hD
    obtain ⟨c₃, hc₃⟩ := exists_const_KMOf_le_length hD
    refine ⟨(c₁ : ℝ) + (c₃ : ℝ) + |c₂|, fun n => ?_⟩
    have hfin := KMOf_ne_top_of_isOptimal hD (cantorPrefix w n)
    have h3 := hc₃ (cantorPrefix w n)
    rw [cantorPrefix_length] at h3
    have hKMnat : (KMOf D (cantorPrefix w n)).toNat ≤ n + c₃ := by
      have h5 : ((KMOf D (cantorPrefix w n)).toNat : ℕ∞) ≤ ((n + c₃ : ℕ) : ℕ∞) := by
        rw [ENat.coe_toNat hfin, Nat.cast_add]
        exact h3
      exact_mod_cast h5
    have hKMreal : ((KMOf D (cantorPrefix w n)).toNat : ℝ) ≤ (n : ℝ) + (c₃ : ℝ) := by
      exact_mod_cast hKMnat
    have hKA1 := hc₁ n
    have hKA2 := hc₂ (cantorPrefix w n)
    have habs1 : c₂ ≤ |c₂| := le_abs_self c₂
    have habs0 : (0 : ℝ) ≤ |c₂| := abs_nonneg c₂
    have hc1nn : (0 : ℝ) ≤ (c₁ : ℝ) := Nat.cast_nonneg c₁
    have hc3nn : (0 : ℝ) ≤ (c₃ : ℝ) := Nat.cast_nonneg c₃
    refine ⟨abs_le.2 ⟨by linarith, by linarith⟩, abs_le.2 ⟨by linarith, by linarith⟩⟩
  · rintro ⟨c, hc⟩
    refine isMartinLofRandom_of_exists_const_le_KA_cantorPrefix ⟨c, fun n => ?_⟩
    have h := (abs_le.1 (hc n).1).1
    linarith

/-- SUV Theorem 94(c) (Section 5.6, p. 151): if `w` is not Martin-Löf random with respect to
the uniform measure, then `n - KM((w)_n)` (and therefore `n - KA((w)_n)`) tends to infinity. -/
theorem tendsto_length_sub_KMOf_of_not_isMartinLofRandom_uniform {D : BitStream → BitStream}
    (hD : IsOptimalMonotoneDecompressor D) {w : CantorSeq}
    (hw : ¬ IsMartinLofRandom uniformMeasure w) :
    (∀ c : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → KMOf D (cantorPrefix w n) + (c : ℕ∞) ≤ (n : ℕ∞)) ∧
      (∀ c : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → KA (cantorPrefix w n) + c ≤ (n : ℝ)) := by
  have hKM : ∀ c : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      KMOf D (cantorPrefix w n) + (c : ℕ∞) ≤ (n : ℕ∞) := by
    intro c
    obtain ⟨N, hN⟩ := tendsto_monotoneDeficiency_of_not_isMartinLofRandom
      isComputableMeasure_uniform hD hw c
    refine ⟨max N c, fun n hn => ?_⟩
    have hNn : N ≤ n := le_trans (le_max_left _ _) hn
    have hcn : c ≤ n := le_trans (le_max_right _ _) hn
    have h := hN n hNn
    rw [cantorMass_uniformMeasure, cantorPrefix_length] at h
    have hpow : (2 : ℝ≥0∞) ^ c * (2 : ℝ≥0∞)⁻¹ ^ n = (2 : ℝ≥0∞)⁻¹ ^ (n - c) := by
      have hsplit : ((2 : ℝ≥0∞)⁻¹) ^ n = (2 : ℝ≥0∞)⁻¹ ^ c * (2 : ℝ≥0∞)⁻¹ ^ (n - c) := by
        rw [← pow_add]
        congr 1
        omega
      rw [hsplit, ← mul_assoc, ← mul_pow,
        ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow, one_mul]
    rw [hpow] at h
    have hle : KMOf D (cantorPrefix w n) ≤ ((n - c : ℕ) : ℕ∞) + ((0 : ℕ) : ℕ∞) := by
      refine le_add_nat_of_complexityWeight_le (ENat.coe_ne_top _) ?_
      rw [pow_zero, one_mul, complexityWeight_coe]
      exact h
    have hle' : KMOf D (cantorPrefix w n) ≤ ((n - c : ℕ) : ℕ∞) := by simpa using hle
    calc KMOf D (cantorPrefix w n) + (c : ℕ∞)
        ≤ ((n - c : ℕ) : ℕ∞) + (c : ℕ∞) := by gcongr
      _ = (((n - c) + c : ℕ) : ℕ∞) := by push_cast; ring
      _ = (n : ℕ∞) := by congr 1; omega
  refine ⟨hKM, fun c => ?_⟩
  obtain ⟨c₂, hc₂⟩ := exists_const_KA_le_KMOf hD
  obtain ⟨k, hk⟩ := exists_nat_ge (c + c₂)
  obtain ⟨N, hN⟩ := hKM k
  refine ⟨N, fun n hn => ?_⟩
  have hfin := KMOf_ne_top_of_isOptimal hD (cantorPrefix w n)
  have h := hN n hn
  have hnat : (KMOf D (cantorPrefix w n)).toNat + k ≤ n := by
    have : ((KMOf D (cantorPrefix w n)).toNat : ℕ∞) + (k : ℕ∞) ≤ (n : ℕ∞) := by
      rwa [ENat.coe_toNat hfin]
    exact_mod_cast this
  have hreal : ((KMOf D (cantorPrefix w n)).toNat : ℝ) + (k : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hnat
  have hKA := hc₂ (cantorPrefix w n)
  linarith

/-- SUV Theorem 94(d) (Section 5.6, p. 151): `w` is Martin-Löf random with respect to the
uniform measure if and only if `K((w)_n) ≥ n - c` for some `c` and all `n`. -/
theorem isMartinLofRandom_uniform_iff_le_KPPlain_cantorPrefix {U : Map}
    (hU : IsOptimalPrefixConditional U) (w : CantorSeq) :
    IsMartinLofRandom uniformMeasure w ↔
      ∃ c : ℕ, ∀ n : ℕ, (n : ℕ∞) ≤ KPPlain U (cantorPrefix w n) + c := by
  rw [isMartinLofRandom_iff_boundedPrefixDeficiency isComputableMeasure_uniform hU]
  have hmass : ∀ n : ℕ, cantorMass uniformMeasure (cantorPrefix w n) = (2 : ℝ≥0∞)⁻¹ ^ n := by
    intro n
    rw [cantorMass_uniformMeasure, cantorPrefix_length]
  constructor
  · rintro ⟨c, hc⟩
    have hinvc : ((2 : ℝ≥0∞)⁻¹) ^ c * (2 : ℝ≥0∞) ^ c = 1 := by
      rw [← mul_pow, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_pow]
    refine ⟨c, fun n => ?_⟩
    have h := hc n
    rw [hmass n] at h
    rcases eq_or_ne (KPPlain U (cantorPrefix w n)) ⊤ with htop | hfin
    · rw [htop]
      simp
    · refine le_add_nat_of_complexityWeight_le hfin ?_
      rw [complexityWeight_coe]
      calc (2 : ℝ≥0∞)⁻¹ ^ c * complexityWeight (KPPlain U (cantorPrefix w n))
          ≤ (2 : ℝ≥0∞)⁻¹ ^ c * ((2 : ℝ≥0∞) ^ c * (2 : ℝ≥0∞)⁻¹ ^ n) := by gcongr
        _ = (2 : ℝ≥0∞)⁻¹ ^ n := by rw [← mul_assoc, hinvc, one_mul]
  · rintro ⟨c, hc⟩
    have hpowc : (2 : ℝ≥0∞) ^ c * ((2 : ℝ≥0∞)⁻¹) ^ c = 1 := by
      rw [← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow]
    refine ⟨c, fun n => ?_⟩
    rw [hmass n]
    have h := complexityWeight_le_of_le (hc n)
    rw [complexityWeight_add_nat, complexityWeight_coe] at h
    calc complexityWeight (KPPlain U (cantorPrefix w n))
        = (2 : ℝ≥0∞) ^ c
            * (complexityWeight (KPPlain U (cantorPrefix w n)) * (2 : ℝ≥0∞)⁻¹ ^ c) := by
          rw [← mul_assoc, mul_comm ((2 : ℝ≥0∞) ^ c) _, mul_assoc, hpowc, mul_one]
      _ ≤ (2 : ℝ≥0∞) ^ c * (2 : ℝ≥0∞)⁻¹ ^ n := by gcongr

/-- SUV Theorem 94(d), second form (Section 5.6, p. 151) / Problem 146 (p. 150), the hard
direction -- the **ample excess lemma** of Gacs, rediscovered by J. Miller and L. Yu: for a
Martin-Loef random sequence (uniform measure) the series `∑ₙ 2^(n - K((w)_n))` converges.

This is the only half of 94(d') that does not follow from 94(d): the criterion `K((w)_n) ≥
n - c` bounds every term of the series by `2^c` but says nothing about its sum.  The source
proves it as Problem 146: `w ↦ ∑_{x ⊑ w} m(x)/p(x)` is a *maximal* expectation-bounded
randomness test (`problem_146_isMaximalExpectationBoundedTest`, `Exercises.lean`), so it is
finite exactly on the random sequences, and for the uniform measure it equals the present
series up to a constant factor (`problem_147_uniform_prefixSupRatio_eq_prefixExcessSup`). -/
theorem tsum_prefixExcess_ne_top_of_isMartinLofRandom_uniform {U : Map}
    (hU : IsOptimalPrefixConditional U) {w : CantorSeq}
    (hw : IsMartinLofRandom uniformMeasure w) :
    (∑' n : ℕ, (2 : ℝ≥0∞) ^ n * complexityWeight (KPPlain U (cantorPrefix w n))) ≠ ⊤ :=
  tsum_two_pow_mul_complexityWeight_KPPlain_ne_top_of_isMartinLofRandom_uniform
    hU.isPrefixDecompressor hw

/-- SUV Theorem 94(d), second form (Section 5.6, p. 151): "another version of the statement
(d) is that a sequence `w` is ML-random if and only if the sum `∑ₙ 2^(n - K((w)_n))` is
finite (Problem 146)".

The `←` half is elementary and is proved here: a finite sum bounds every one of its terms, so
`2^n · 2^(-K((w)_n)) ≤ 2^c` for one `c`, which is exactly the criterion of 94(d).  The `→`
half is the ample excess lemma and is the leaf
`tsum_prefixExcess_ne_top_of_isMartinLofRandom_uniform` above. -/
theorem isMartinLofRandom_uniform_iff_tsum_prefixExcess_ne_top {U : Map}
    (hU : IsOptimalPrefixConditional U) (w : CantorSeq) :
    IsMartinLofRandom uniformMeasure w ↔
      (∑' n : ℕ, (2 : ℝ≥0∞) ^ n * complexityWeight (KPPlain U (cantorPrefix w n))) ≠ ⊤ := by
  refine ⟨fun hw => tsum_prefixExcess_ne_top_of_isMartinLofRandom_uniform hU hw, fun hw => ?_⟩
  obtain ⟨m, hm⟩ := ENNReal.exists_nat_gt hw
  have hSle : (∑' n : ℕ, (2 : ℝ≥0∞) ^ n * complexityWeight (KPPlain U (cantorPrefix w n)))
      ≤ (2 : ℝ≥0∞) ^ m := by
    refine le_trans hm.le ?_
    have hn2 : m < 2 ^ m := Nat.lt_two_pow_self
    calc (m : ℝ≥0∞) ≤ ((2 ^ m : ℕ) : ℝ≥0∞) := by exact_mod_cast hn2.le
      _ = (2 : ℝ≥0∞) ^ m := by push_cast; ring
  have hinvm : ((2 : ℝ≥0∞)⁻¹) ^ m * (2 : ℝ≥0∞) ^ m = 1 := by
    rw [← mul_pow, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_pow]
  rw [isMartinLofRandom_uniform_iff_le_KPPlain_cantorPrefix hU]
  refine ⟨m, fun n => ?_⟩
  have hterm : (2 : ℝ≥0∞) ^ n * complexityWeight (KPPlain U (cantorPrefix w n))
      ≤ (2 : ℝ≥0∞) ^ m := le_trans (ENNReal.le_tsum n) hSle
  rcases eq_or_ne (KPPlain U (cantorPrefix w n)) ⊤ with htop | hfin
  · rw [htop]
    simp
  · refine le_add_nat_of_complexityWeight_le hfin ?_
    rw [complexityWeight_coe]
    have hinvn : ((2 : ℝ≥0∞)⁻¹) ^ n * (2 : ℝ≥0∞) ^ n = 1 := by
      rw [← mul_pow, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_pow]
    calc (2 : ℝ≥0∞)⁻¹ ^ m * complexityWeight (KPPlain U (cantorPrefix w n))
        = (2 : ℝ≥0∞)⁻¹ ^ m * (((2 : ℝ≥0∞)⁻¹ ^ n * (2 : ℝ≥0∞) ^ n)
            * complexityWeight (KPPlain U (cantorPrefix w n))) := by rw [hinvn, one_mul]
      _ = (2 : ℝ≥0∞)⁻¹ ^ m * ((2 : ℝ≥0∞)⁻¹ ^ n
            * ((2 : ℝ≥0∞) ^ n * complexityWeight (KPPlain U (cantorPrefix w n)))) := by ring
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ m * ((2 : ℝ≥0∞)⁻¹ ^ n * (2 : ℝ≥0∞) ^ m) := by gcongr
      _ = (2 : ℝ≥0∞)⁻¹ ^ n * ((2 : ℝ≥0∞)⁻¹ ^ m * (2 : ℝ≥0∞) ^ m) := by ring
      _ = ((2 : ℝ≥0∞)⁻¹) ^ n := by rw [hinvm, mul_one]

/-- SUV Theorem 94(e) (Section 5.6, p. 151): `w` is Martin-Löf random with respect to the
uniform measure if and only if `K(F, w(F)) ≥ |F| - c` for some `c` and all finite index sets
`F ⊆ ℕ`.  This is the index-permutation-invariant criterion of A. Rumyantsev.

The finite set `F` enters through the canonical computable injective coding `finsetCode` of
`SharedCoding.lean`; the criterion is coding-independent, since replacing `finsetCode` by any
other computable injective coding changes `K` by `O(1)`
(`exists_const_KPPlain_finsetCode_invariant`) and is absorbed by `c`. -/
theorem isMartinLofRandom_uniform_iff_le_KPPair_restrictSeq {U : Map}
    (hU : IsOptimalPrefixConditional U) (w : CantorSeq) :
    IsMartinLofRandom uniformMeasure w ↔
      ∃ c : ℕ, ∀ F : Finset ℕ,
        (F.card : ℕ∞) ≤ KPPair U (finsetCode F) (restrictSeq F w) + c :=
  isMartinLofRandom_uniform_iff_le_KPPair_restrictSeq' hU w
    (isMartinLofRandom_uniform_iff_le_KPPlain_cantorPrefix hU w)

/-! ## Theorems 95-98: criteria in terms of plain complexity -/

/-- SUV Theorem 95 (Section 5.6, p. 151): if `f : ℕ → ℕ` is total computable and the series
`∑ 2^(-f(n))` converges, then every Martin-Löf random sequence `w` (uniform measure) satisfies
`C((w)_n | n) ≥ n - f(n) - c` for one constant `c` and all `n`.

The natural number `n` is supplied as the condition through the canonical binary code
`natToBitString n` of `KolmogorovMathlib.MonotoneComplexity.SharedCoding`.  The claim is
coding-independent: `natToBitString` is a computable bijection with computable inverse
(`computable_natToBitString`, `computable_bitStringToNat`), so re-coding the condition costs
`O(1)` and is absorbed by `c`; cf. `exists_const_KPNat_natBits_equiv` for the argument slot. -/
theorem le_condK_cantorPrefix_add_of_isMartinLofRandom_uniform {V : Map}
    (hV : isOptimalConditional V) {f : ℕ → ℕ} (hf : Computable f)
    (hconv : (∑' n : ℕ, (2 : ℝ≥0∞)⁻¹ ^ f n) ≠ ⊤) {w : CantorSeq}
    (hw : IsMartinLofRandom uniformMeasure w) :
    ∃ c : ℕ, ∀ n : ℕ, (n : ℕ∞) ≤ condK V (cantorPrefix w n) (natToBitString n) + f n + c := by
  refine le_condK_cantorPrefix_add_of_isMartinLofRandom_uniform_general hV.1 ?_ ?_ hw
  · refine isRE_of_computable_bool _ (fun q : ℕ × ℕ => decide (f q.1 < q.2))
      (fun q => by rw [decide_eq_true_iff]; exact_mod_cast Iff.rfl) ?_
    exact (Primrec.to_comp (PrimrecPred.decide Primrec.nat_lt)).comp
      (Computable.pair (hf.comp Computable.fst) Computable.snd)
  · simpa using hconv

/-- SUV Theorem 95, Remark (Section 5.6, p. 152): the proof uses only that `f` is upper
semicomputable, so the statement remains true for `f(n) = K(n)`: every Martin-Löf random
sequence (uniform measure) satisfies `C((w)_n | n) ≥ n - K(n) - O(1)`. -/
theorem le_condK_cantorPrefix_add_KPPlain_of_isMartinLofRandom_uniform {V : Map}
    (hV : isOptimalConditional V) {U : Map} (hU : IsOptimalPrefixConditional U)
    {w : CantorSeq} (hw : IsMartinLofRandom uniformMeasure w) :
    ∃ c : ℕ, ∀ n : ℕ,
      (n : ℕ∞) ≤ condK V (cantorPrefix w n) (natToBitString n) + KPNat U n + c := by
  refine le_condK_cantorPrefix_add_of_isMartinLofRandom_uniform_general hV.1 ?_ ?_ hw
  · have hmap : Computable fun q : ℕ × ℕ => (natToBitString q.1, q.2) :=
      Computable.pair (computable_natToBitString.comp Computable.fst) Computable.snd
    exact (isRE_KPPlain_lt hU.isDecompressor).comp_computable hmap
  · have hsemi : (∑' x : BitString, complexityWeight (KPPlain U x)) ≤ 1 :=
      prefixComplexityWeight_isSemimeasure U hU.isPrefixDecompressor
    have heq : (∑' n : ℕ, complexityWeight (KPNat U n))
        = ∑' x : BitString, complexityWeight (KPPlain U x) :=
      tsum_comp_natToBitString (fun x => complexityWeight (KPPlain U x))
    rw [heq]
    exact ne_top_of_le_ne_top (by norm_num) hsemi

/-- SUV Theorem 97 (Section 5.6, p. 154), first direction: for a Martin-Löf random sequence
and any total computable `f` with `∑ 2^(-f(n)) < ∞` one has `C((w)_n) ≥ n - f(n) - O(1)`,
now with the *unconditional* plain complexity. -/
theorem forall_computable_summable_le_plainK_of_isMartinLofRandom_uniform {V : Map}
    (hV : isOptimalConditional V) {w : CantorSeq}
    (hw : IsMartinLofRandom uniformMeasure w) :
    ∀ f : ℕ → ℕ, Computable f → (∑' n : ℕ, (2 : ℝ≥0∞)⁻¹ ^ f n) ≠ ⊤ →
      ∃ c : ℕ, ∀ n : ℕ, (n : ℕ∞) ≤ plainK V (cantorPrefix w n) + f n + c := by
  intro f hf hconv
  obtain ⟨c₁, hc₁⟩ := le_condK_cantorPrefix_add_of_isMartinLofRandom_uniform hV hf hconv hw
  obtain ⟨c₂, hc₂⟩ := exists_const_condK_le_plainK hV
  refine ⟨c₁ + c₂, fun n => ?_⟩
  refine le_trans (hc₁ n) ?_
  have h := hc₂ (cantorPrefix w n) (natToBitString n)
  calc condK V (cantorPrefix w n) (natToBitString n) + (f n : ℕ∞) + (c₁ : ℕ∞)
      ≤ (plainK V (cantorPrefix w n) + (c₂ : ℕ∞)) + (f n : ℕ∞) + (c₁ : ℕ∞) := by gcongr
    _ = plainK V (cantorPrefix w n) + (f n : ℕ∞) + ((c₁ + c₂ : ℕ) : ℕ∞) := by
        push_cast
        ring

/-- SUV Theorem 97 (Section 5.6, p. 154), the Miller-Yu criterion: `w` is Martin-Löf random
if and only if for every total computable `f : ℕ → ℕ` with convergent `∑ 2^(-f(n))` the
inequality `C((w)_n) ≥ n - f(n) - O(1)` holds. -/
theorem isMartinLofRandom_uniform_iff_forall_computable_summable_le_plainK {V : Map}
    (hV : isOptimalConditional V) (w : CantorSeq) :
    IsMartinLofRandom uniformMeasure w ↔
      ∀ f : ℕ → ℕ, Computable f → (∑' n : ℕ, (2 : ℝ≥0∞)⁻¹ ^ f n) ≠ ⊤ →
        ∃ c : ℕ, ∀ n : ℕ, (n : ℕ∞) ≤ plainK V (cantorPrefix w n) + f n + c :=
  ⟨fun hw => forall_computable_summable_le_plainK_of_isMartinLofRandom_uniform hV hw,
    fun hw => isMartinLofRandom_uniform_of_forall_computable_summable_le_plainK' hV hw⟩

/-- SUV Theorem 98 (Section 5.6, p. 154), first direction: a Martin-Löf random sequence
satisfies `C((w)_n) ≥ n - K(n) - O(1)`, where `K(n) = KPNat U n` is the shared prefix
complexity of a natural number (`SharedCoding.lean`).  Coding-independent: `KPNat` and the
skeleton's earlier `KPPlain U (Nat.bits n)` differ by `O(1)` in both directions
(`exists_const_KPNat_natBits_equiv`), which `c` absorbs. -/
theorem le_plainK_add_KPPlain_of_isMartinLofRandom_uniform {V : Map}
    (hV : isOptimalConditional V) {U : Map} (hU : IsOptimalPrefixConditional U)
    {w : CantorSeq} (hw : IsMartinLofRandom uniformMeasure w) :
    ∃ c : ℕ, ∀ n : ℕ,
      (n : ℕ∞) ≤ plainK V (cantorPrefix w n) + KPNat U n + c := by
  obtain ⟨c₁, hc₁⟩ :=
    le_condK_cantorPrefix_add_KPPlain_of_isMartinLofRandom_uniform hV hU hw
  obtain ⟨c₂, hc₂⟩ := exists_const_condK_le_plainK hV
  refine ⟨c₁ + c₂, fun n => ?_⟩
  refine le_trans (hc₁ n) ?_
  have h := hc₂ (cantorPrefix w n) (natToBitString n)
  calc condK V (cantorPrefix w n) (natToBitString n) + KPNat U n + (c₁ : ℕ∞)
      ≤ (plainK V (cantorPrefix w n) + (c₂ : ℕ∞)) + KPNat U n + (c₁ : ℕ∞) := by gcongr
    _ = plainK V (cantorPrefix w n) + KPNat U n + ((c₁ + c₂ : ℕ) : ℕ∞) := by
        push_cast
        ring

/-- SUV Theorem 98 (Section 5.6, p. 154), converse direction: if `C((w)_n) ≥ n - K(n) - O(1)`
then `w` is Martin-Löf random.

Proved here by the source's own argument (p. 154, first two lines of the proof of
Theorem 98): "If `∑ₙ 2^(-f(n))` converges for a computable `f`, then `K(n) ⩽ f(n) + O(1)`.
Therefore the condition with prefix complexity is stronger than that in Theorem 97".  The
inequality `K(n) ≤ f(n) + O(1)` is `exists_const_KPNat_le_of_computable_summable`
(`LevinSchnorr/SummableWeight.lean`); the remaining implication is Theorem 97 ⇐. -/
theorem isMartinLofRandom_uniform_of_le_plainK_add_KPPlain {V : Map}
    (hV : isOptimalConditional V) {U : Map} (hU : IsOptimalPrefixConditional U)
    {w : CantorSeq}
    (hw : ∃ c : ℕ, ∀ n : ℕ,
      (n : ℕ∞) ≤ plainK V (cantorPrefix w n) + KPNat U n + c) :
    IsMartinLofRandom uniformMeasure w := by
  obtain ⟨c, hc⟩ := hw
  refine isMartinLofRandom_uniform_of_forall_computable_summable_le_plainK' hV ?_
  intro f hf hconv
  obtain ⟨c₀, hc₀⟩ := exists_const_KPNat_le_of_computable_summable hU hf hconv
  refine ⟨c + c₀, fun n => ?_⟩
  refine le_trans (hc n) ?_
  calc plainK V (cantorPrefix w n) + KPNat U n + (c : ℕ∞)
      ≤ plainK V (cantorPrefix w n) + ((f n : ℕ∞) + (c₀ : ℕ∞)) + (c : ℕ∞) := by
        gcongr
        exact hc₀ n
    _ = plainK V (cantorPrefix w n) + (f n : ℕ∞) + ((c + c₀ : ℕ) : ℕ∞) := by
        push_cast
        ring

/-- SUV Theorem 98 (Section 5.6, p. 154): `w` is Martin-Löf random with respect to the uniform
measure if and only if `C((w)_n) ≥ n - K(n) - O(1)`. -/
theorem isMartinLofRandom_uniform_iff_le_plainK_add_KPPlain {V : Map}
    (hV : isOptimalConditional V) {U : Map} (hU : IsOptimalPrefixConditional U)
    (w : CantorSeq) :
    IsMartinLofRandom uniformMeasure w ↔
      ∃ c : ℕ, ∀ n : ℕ,
        (n : ℕ∞) ≤ plainK V (cantorPrefix w n) + KPNat U n + c :=
  ⟨fun hw => le_plainK_add_KPPlain_of_isMartinLofRandom_uniform hV hU hw,
    fun hw => isMartinLofRandom_uniform_of_le_plainK_add_KPPlain hV hU hw⟩

/-! ## Theorem 99: the unavoidable logarithmic dip -/

end Kolmogorov
