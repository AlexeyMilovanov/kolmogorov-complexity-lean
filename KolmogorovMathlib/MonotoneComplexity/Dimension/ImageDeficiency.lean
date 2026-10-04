/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.MonotoneComplexity.Dimension.DeficiencySemimeasure
import KolmogorovMathlib.MonotoneComplexity.Dimension.PullbackTest

/-!
# The image deficiency semimeasure (SUV Problem 187, §5.9.3, p. 185)

The hint of Problem 187 reads:

> "The set of sequences having large `ν`-deficiencies can be covered by a set of
> small `ν`-measure, therefore their preimages can be covered by a set of small
> `μ`-measure and have large `μ`-deficiency.  Note that this statement is a
> generalization of Theorem 124." (p. 185)

This module is the image analogue of `Dimension/DeficiencySemimeasure.lean`,
which builds the semimeasure of Theorem 124.  The only new ingredient is the
family of sets it mixes: `imgDeficiencySet ν f k` is the set of sequences whose
*image* already carries a prefix of `ν`-deficiency above `k`.

* `measure_imgDeficiencySet_le`: its `μ`-measure is at most `2^{-k}`, because the
  prefix-minimal strings of the `ν`-deficiency set form an antichain, their
  preimages are disjoint and have `μ`-measure `ν(Ω_u)` (the image relation), and
  those add up to at most `2^{-k}` (`measure_prefixHitSet_aPrioriDeficiencySet_le`);
* `imgRel`/`isRE_imgRel`/`cantorOpen_imgRel`: `Ω_y ∩ f⁻¹(S_k)` is effectively
  open uniformly in `(k, y)` -- the generating strings are those extending `y`
  whose image already carries a prefix of deficiency above `k`, and the
  continuity of `f` supplies such a finite generator for every sequence of the
  set;
* everything after that is the construction of `DeficiencySemimeasure.lean` with
  `defMeasure` replaced by `imgMeasure`: the measures `2^k·μ(Ω_· ∩ f⁻¹(S_k))` are
  continuous tree semimeasures, they admit a uniform lower-semicomputable
  approximation (`cantorOpenMass_isLSC_of_isComputableMeasure`), and the block
  mixture of `AlgorithmicProbability`'s `continuousTreeMixture` gives each of
  them the weight `2^{-2⌊log₂k⌋-1} ≥ 1/(2k²)` of the source.
-/

namespace Kolmogorov

open MeasureTheory
open scoped ENNReal

/-- The set of sequences whose image already carries a prefix of `ν`-deficiency
above `k`. -/
def imgDeficiencySet (ν : Measure CantorSeq) (f : BitStream → BitStream) (k : ℕ) :
    Set CantorSeq :=
  {ω : CantorSeq | ∃ u ∈ aPrioriDeficiencySet ν k, BitStream.finite u ≤ f (BitStream.infinite ω)}

/-- The sequences whose image under `f` has `ν`-deficiency above `k` have `μ`-measure at most
`2 ^ (-k)`. -/
lemma measure_imgDeficiencySet_le {μ ν : Measure CantorSeq} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {f : BitStream → BitStream}
    (hν : IsImageMeasure μ f ν) (k : ℕ) :
    μ (imgDeficiencySet ν f k) ≤ ((2 : ℝ≥0∞)⁻¹) ^ k := by
  classical
  set S : Set BitString := aPrioriDeficiencySet ν k with hS
  set M : Set BitString := minimalPrefixElements S with hM
  set Pre : BitString → Set CantorSeq :=
    fun u => {ω : CantorSeq | BitStream.finite u ≤ f (BitStream.infinite ω)} with hPre
  have hsub : imgDeficiencySet ν f k ⊆ ⋃ u ∈ M, Pre u := by
    rintro ω ⟨u, huS, huω⟩
    obtain ⟨u', hu', hpre⟩ := exists_minimalPrefixElement huS
    refine Set.mem_biUnion hu' ?_
    exact le_trans (BitStream.finite_le_finite_iff.2 hpre) huω
  calc μ (imgDeficiencySet ν f k) ≤ μ (⋃ u ∈ M, Pre u) := measure_mono hsub
    _ ≤ ∑' u : M, μ (Pre (u : BitString)) := by
        rw [Set.biUnion_eq_iUnion]
        exact measure_iUnion_le _
    _ = ∑' u : M, cantorMass ν (u : BitString) := by
        refine tsum_congr fun u => ?_
        rw [hν (u : BitString)]
    _ = ν (⋃ u ∈ M, cantorCylinder u) := by
        rw [Set.biUnion_eq_iUnion]
        refine (measure_iUnion ?_ ?_).symm
        · intro a b hab
          refine Set.disjoint_left.2 fun ω hωa hωb => hab ?_
          have h1 : IsCantorPrefix (a : BitString) ω := hωa
          have h2 : IsCantorPrefix (b : BitString) ω := hωb
          have hanti := minimalPrefixElements_antichain S
          rcases le_total (a : BitString).length (b : BitString).length with hle | hle
          · exact Subtype.ext (hanti _ a.2 _ b.2 (prefix_of_isCantorPrefix h1 h2 hle))
          · exact Subtype.ext (hanti _ b.2 _ a.2 (prefix_of_isCantorPrefix h2 h1 hle)).symm
        · intro u
          exact measurableSet_cantorCylinder _
    _ = ν (prefixHitSet S) := by
        rw [iUnion_cantorCylinder_minimalPrefixElements S,
          prefixHitSet_eq_iUnion_cantorCylinder]
    _ ≤ ((2 : ℝ≥0∞)⁻¹) ^ k := measure_prefixHitSet_aPrioriDeficiencySet_le k

/-- The r.e. relation generating `Ω_y ∩ f⁻¹(S_k)`: the strings extending `y`
whose image already carries a prefix of `ν`-deficiency above `k`. -/
def imgRel (ν : Measure CantorSeq) (f : BitStream → BitStream) (p x : BitString) : Prop :=
  defString x <+: p ∧ ∃ u : BitString, BitStream.finite u ≤ f (BitStream.finite p) ∧
    u ∈ aPrioriDeficiencySet ν (defLevel x)

/-- For a computable measure and a computable stream map the relation enumerating the image
deficiency sets is recursively enumerable. -/
lemma isRE_imgRel {ν : Measure CantorSeq} [IsProbabilityMeasure ν] {f : BitStream → BitStream}
    (hν : IsComputableMeasure ν) (hf : IsComputableStreamMap f) :
    IsRE fun q : BitString × BitString => imgRel ν f q.1 q.2 := by
  have h1 : IsRE fun r : (BitString × BitString) × BitString =>
      streamLowerGraph f r.1.1 r.2 :=
    hf.2.compComputable (Computable.pair (Computable.fst.comp Computable.fst) Computable.snd)
  have h2 : IsRE fun r : (BitString × BitString) × BitString =>
      r.2 ∈ aPrioriDeficiencySet ν (defLevel r.1.2) :=
    (isRE_aPrioriDeficiencySet hν).compComputable
      (Computable.pair (primrec_defLevel.to_comp.comp (Computable.snd.comp Computable.fst))
        Computable.snd)
  have hex : IsRE fun q : BitString × BitString =>
      ∃ u : BitString, streamLowerGraph f q.1 u ∧
        u ∈ aPrioriDeficiencySet ν (defLevel q.2) :=
    IsRE.exists_encodable (h1.and h2)
  have hcheck : Computable fun q : BitString × BitString =>
      normalFormIsPrefixB (defString q.2) q.1 :=
    (primrec₂_normalFormIsPrefixB.to_comp).comp
      (primrec_defString.to_comp.comp Computable.snd) Computable.fst
  refine (hex.and_computable hcheck).of_iff fun q => ?_
  rw [normalFormIsPrefixB_iff]
  exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

/-- The effective open set enumerated at the parameter `(k, y)` is the part of the cylinder of `y`
whose image deficiency exceeds `k`. -/
lemma cantorOpen_imgRel {ν : Measure CantorSeq} {f : BitStream → BitStream}
    (hf : IsComputableStreamMap f) (k : ℕ) (y : BitString) :
    cantorOpen (imgRel ν f) (defParam k y) = cantorCylinder y ∩ imgDeficiencySet ν f k := by
  ext w
  simp only [cantorOpen, Set.mem_iUnion, Set.mem_inter_iff, imgRel, defLevel_defParam,
    defString_defParam, imgDeficiencySet, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨p, ⟨hyp, u, hu1, hu2⟩, hwp⟩
    refine ⟨cantorCylinder_subset_of_prefix hyp hwp, u, hu2, ?_⟩
    have hpw : BitStream.finite p ≤ BitStream.infinite w := BitStream.finite_le_infinite_iff.2 hwp
    exact le_trans hu1 (hf.1.1 hpw)
  · rintro ⟨hwy, u, hu2, hu1⟩
    obtain ⟨n, hn⟩ := (continuousStreamMap_finite_le_infinite_iff f hf.1 w u).1 hu1
    have hyw : IsCantorPrefix y w := hwy
    have hylen : cantorPrefix w y.length = y := (isCantorPrefix_iff_cantorPrefix_eq y w).1 hyw
    refine ⟨cantorPrefix w (max n y.length), ⟨?_, u, ?_, hu2⟩,
      mem_cantorCylinder_cantorPrefix w _⟩
    · have h1 : cantorPrefix w y.length <+: cantorPrefix w (max n y.length) :=
        cantorPrefix_mono w (le_max_right n y.length)
      rwa [hylen] at h1
    · refine le_trans hn (hf.1.1 ?_)
      exact BitStream.finite_le_finite_iff.2
        (cantorPrefix_mono w (le_max_left n y.length))

/-! ## The image deficiency measures -/

/-- The set of sequences whose image has deficiency above `k` is measurable. -/
lemma measurableSet_imgDeficiencySet {ν : Measure CantorSeq} {f : BitStream → BitStream}
    (hf : IsComputableStreamMap f) (k : ℕ) : MeasurableSet (imgDeficiencySet ν f k) := by
  classical
  obtain ⟨E, hE, hEspec⟩ := exists_uniform_enumerator_setOf_le_comp hf
  have hPre : ∀ u : BitString,
      MeasurableSet {ω : CantorSeq | BitStream.finite u ≤ f (BitStream.infinite ω)} := by
    intro u
    rw [hEspec u]
    refine MeasurableSet.iUnion fun i => ?_
    cases hEi : E u i with
    | none => simp
    | some z => simpa using measurableSet_cantorCylinder z
  have hEq : imgDeficiencySet ν f k
      = ⋃ u ∈ aPrioriDeficiencySet ν k,
        {ω : CantorSeq | BitStream.finite u ≤ f (BitStream.infinite ω)} := by
    ext ω
    simp [imgDeficiencySet]
  rw [hEq]
  exact MeasurableSet.biUnion (Set.to_countable _) fun u _ => hPre u

/-- The image analogue of `defMeasure`: zero outside `f⁻¹(S_k)` and `2^k·μ`
inside, with the defect assigned to the root. -/
noncomputable def imgMeasure (μ ν : Measure CantorSeq) (f : BitStream → BitStream) (k : ℕ)
    (y : BitString) : ℝ≥0∞ :=
  if y = [] then 1 else (2 : ℝ≥0∞) ^ k * μ (cantorCylinder y ∩ imgDeficiencySet ν f k)

/-- Away from the root the level-`k` image measure is `2 ^ k` times the `μ`-mass of the cylinder
intersected with the deficiency set. -/
lemma imgMeasure_of_ne_nil {μ ν : Measure CantorSeq} {f : BitStream → BitStream} {k : ℕ}
    {y : BitString} (hy : y ≠ []) :
    imgMeasure μ ν f k y = (2 : ℝ≥0∞) ^ k * μ (cantorCylinder y ∩ imgDeficiencySet ν f k) :=
  ite_eq_right hy

/-- The level-`k` image measure is a continuous tree semimeasure. -/
lemma isContinuousTreeSemimeasure_imgMeasure {μ ν : Measure CantorSeq} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {f : BitStream → BitStream} (hf : IsComputableStreamMap f)
    (hν : IsImageMeasure μ f ν) (k : ℕ) :
    IsContinuousTreeSemimeasure (imgMeasure μ ν f k) := by
  refine ⟨by simp [imgMeasure], fun x => ?_⟩
  have hne0 : x ++ [false] ≠ [] := by simp
  have hne1 : x ++ [true] ≠ [] := by simp
  rw [imgMeasure_of_ne_nil hne0, imgMeasure_of_ne_nil hne1, ← mul_add,
    ← measure_inter_split μ x (measurableSet_imgDeficiencySet hf k)]
  by_cases hx : x = []
  · subst hx
    rw [imgMeasure, ite_eq_left rfl, cantorCylinder_nil, Set.univ_inter]
    calc (2 : ℝ≥0∞) ^ k * μ (imgDeficiencySet ν f k)
        ≤ (2 : ℝ≥0∞) ^ k * ((2 : ℝ≥0∞)⁻¹) ^ k := by
          gcongr
          exact measure_imgDeficiencySet_le hν k
      _ = 1 := by
          rw [← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow]
  · rw [imgMeasure_of_ne_nil hx]

/-- For computable data the family of level-`k` image measures admits a monotone dyadic
approximation that is computable uniformly in the level, the stage and both strings. -/
lemma exists_uniform_approx_imgMeasure {μ ν : Measure CantorSeq} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {f : BitStream → BitStream} (hμ : IsComputableMeasure μ)
    (hν' : IsComputableMeasure ν) (hf : IsComputableStreamMap f) :
    ∃ A : ℕ → ℕ → BitString → BitString → ℕ,
      (∀ k s out ctx, dyadicValue (A k s out ctx) s
        ≤ dyadicValue (A k (s + 1) out ctx) (s + 1)) ∧
      (∀ k out ctx, ⨆ s, dyadicValue (A k s out ctx) s = imgMeasure μ ν f k out) ∧
      Computable (fun p : ℕ × ℕ × BitString × BitString => A p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  classical
  obtain ⟨approx, hmono, hsup, hcomp⟩ :=
    cantorOpenMass_isLSC_of_isComputableMeasure hμ (isRE_imgRel hν' hf)
  refine ⟨fun k s y ctx => if y = [] then 2 ^ s else 2 ^ k * approx s (defParam k y) ctx,
    ?_, ?_, ?_⟩
  · intro k s y ctx
    by_cases hy : y = []
    · simp [hy, dyadicValue_two_pow_self]
    · simp only [ite_eq_right hy, dyadicValue_nat_mul]
      have hcast : ((2 ^ k : ℕ) : ℝ≥0∞) = (2 : ℝ≥0∞) ^ k := by push_cast; ring
      rw [hcast]
      exact mul_le_mul_right (hmono s (defParam k y) ctx) _
  · intro k y ctx
    by_cases hy : y = []
    · simp [hy, dyadicValue_two_pow_self, imgMeasure]
    · simp only [ite_eq_right hy, dyadicValue_nat_mul, imgMeasure_of_ne_nil hy]
      have hcast : ((2 ^ k : ℕ) : ℝ≥0∞) = (2 : ℝ≥0∞) ^ k := by push_cast; ring
      rw [hcast, ← ENNReal.mul_iSup]
      have hs := hsup (defParam k y) ctx
      simp only at hs
      rw [hs, cantorOpen_imgRel hf]
  · have hpow : Computable fun n : ℕ => 2 ^ n := primrec_two_pow_aux.to_comp
    have hparam : Computable fun p : ℕ × ℕ × BitString × BitString =>
        defParam p.1 p.2.2.1 :=
      (Primrec.list_append.comp (primrec_natCode.comp Primrec.fst)
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))).to_comp
    have happ : Computable fun p : ℕ × ℕ × BitString × BitString =>
        approx p.2.1 (defParam p.1 p.2.2.1) p.2.2.2 :=
      hcomp.comp (Computable.pair (Computable.fst.comp Computable.snd)
        (Computable.pair hparam (Computable.snd.comp (Computable.snd.comp Computable.snd))))
    have hthen : Computable fun p : ℕ × ℕ × BitString × BitString => 2 ^ p.2.1 :=
      hpow.comp (Computable.fst.comp Computable.snd)
    have helse : Computable fun p : ℕ × ℕ × BitString × BitString =>
        2 ^ p.1 * approx p.2.1 (defParam p.1 p.2.2.1) p.2.2.2 :=
      (Primrec.nat_mul.to_comp).comp (hpow.comp Computable.fst) happ
    have hdec : Computable fun p : ℕ × ℕ × BitString × BitString =>
        decide (p.2.2.1 = ([] : BitString)) := by
      have : PrimrecPred fun p : ℕ × ℕ × BitString × BitString => p.2.2.1 = ([] : BitString) :=
        Primrec.eq.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)) (Primrec.const [])
      exact (PrimrecPred.decide this).to_comp
    exact (Computable.cond hdec hthen helse).of_eq fun p => by
      by_cases hy : p.2.2.1 = ([] : BitString) <;> simp [hy]

/-! ## The weighted image semimeasure -/

/-- The average of the image deficiency measures of the levels `2^i ≤ k < 2^{i+1}`. -/
noncomputable def imgBlockAverage (μ ν : Measure CantorSeq) (f : BitStream → BitStream)
    (i : ℕ) (y : BitString) : ℝ≥0∞ :=
  ((2 : ℝ≥0∞)⁻¹) ^ i * ∑ j ∈ Finset.range (2 ^ i), imgMeasure μ ν f (2 ^ i + j) y

/-- The average of the image measures over the `i`-th block of levels is a continuous tree
semimeasure. -/
lemma isContinuousTreeSemimeasure_imgBlockAverage {μ ν : Measure CantorSeq}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {f : BitStream → BitStream}
    (hf : IsComputableStreamMap f) (hν : IsImageMeasure μ f ν) (i : ℕ) :
    IsContinuousTreeSemimeasure (imgBlockAverage μ ν f i) := by
  refine ⟨?_, fun x => ?_⟩
  · have h1 : ∀ j ∈ Finset.range (2 ^ i),
        imgMeasure μ ν f (2 ^ i + j) ([] : BitString) = 1 := fun j _ => by simp [imgMeasure]
    rw [imgBlockAverage, Finset.sum_congr rfl h1, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one, mul_comm]
    exact nat_two_pow_mul_inv_two_pow i
  · rw [imgBlockAverage, imgBlockAverage, imgBlockAverage, ← mul_add, ← Finset.sum_add_distrib]
    gcongr with j hj
    exact (isContinuousTreeSemimeasure_imgMeasure hf hν (2 ^ i + j)).2 x

/-- The staged block approximations converge upward to the block average of the image measures. -/
lemma imgBlockApprox_sup {μ ν : Measure CantorSeq} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {f : BitStream → BitStream}
    {A : ℕ → ℕ → BitString → BitString → ℕ}
    (hmono : ∀ k s out ctx, dyadicValue (A k s out ctx) s
      ≤ dyadicValue (A k (s + 1) out ctx) (s + 1))
    (hsup : ∀ k out ctx, ⨆ s, dyadicValue (A k s out ctx) s = imgMeasure μ ν f k out)
    (i : ℕ) (y ctx : BitString) :
    ⨆ s, dyadicValue (blockApprox A i s y ctx) s = imgBlockAverage μ ν f i y := by
  refine le_antisymm (iSup_le fun s => ?_) ?_
  · by_cases his : i ≤ s
    · rw [dyadicValue_blockApprox his y ctx, imgBlockAverage]
      gcongr with j hj
      rw [← hsup (2 ^ i + j) y ctx]
      exact le_iSup (fun t => dyadicValue (A (2 ^ i + j) t y ctx) t) (s - i)
    · rw [blockApprox, ite_eq_left (by omega)]
      simp [dyadicValue]
  · rw [imgBlockAverage]
    have hswap : ∑ j ∈ Finset.range (2 ^ i), imgMeasure μ ν f (2 ^ i + j) y
        = ⨆ t, ∑ j ∈ Finset.range (2 ^ i), dyadicValue (A (2 ^ i + j) t y ctx) t := by
      have h1 : ∀ j, imgMeasure μ ν f (2 ^ i + j) y
          = ⨆ t, dyadicValue (A (2 ^ i + j) t y ctx) t :=
        fun j => (hsup (2 ^ i + j) y ctx).symm
      simp_rw [h1]
      exact ENNReal.finsetSum_iSup (fun t₁ t₂ => ⟨max t₁ t₂, fun j =>
        ⟨dyadicValue_mono_of_le hmono _ y ctx (le_max_left t₁ t₂),
          dyadicValue_mono_of_le hmono _ y ctx (le_max_right t₁ t₂)⟩⟩)
    rw [hswap, ENNReal.mul_iSup]
    refine iSup_le fun t => ?_
    have hle := le_iSup (fun s => dyadicValue (blockApprox A i s y ctx) s) (t + i)
    rw [dyadicValue_blockApprox (by omega : i ≤ t + i) y ctx, Nat.add_sub_cancel] at hle
    exact hle

/-- The image analogue of `defWeightedSemimeasure`. -/
noncomputable def imgWeightedSemimeasure (μ ν : Measure CantorSeq) (f : BitStream → BitStream) :
    BitString → ℝ≥0∞ :=
  continuousTreeMixture (imgBlockAverage μ ν f)

/-- The weighted sum of the block averages is a lower semicomputable continuous semimeasure. -/
lemma isLSCContinuousSemimeasure_imgWeightedSemimeasure {μ ν : Measure CantorSeq}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {f : BitStream → BitStream}
    (hμ : IsComputableMeasure μ) (hν' : IsComputableMeasure ν) (hf : IsComputableStreamMap f)
    (hν : IsImageMeasure μ f ν) :
    IsLowerSemicomputableContinuousSemimeasure (imgWeightedSemimeasure μ ν f) := by
  obtain ⟨A, hmono, hsup, hcomp⟩ := exists_uniform_approx_imgMeasure hμ hν' hf
  exact continuousTreeMixture_dyadicWeight_isLowerSemicomputableContinuousSemimeasure
    (a := blockApprox A) (imgBlockAverage μ ν f)
    (fun i s out ctx => blockApprox_mono hmono i s out ctx)
    (fun i out ctx => imgBlockApprox_sup hmono hsup i out ctx)
    (fun i => isContinuousTreeSemimeasure_imgBlockAverage hf hν i)
    (computable_blockApprox hcomp)

/-- Each level-`k` image measure appears in the weighted semimeasure with weight at least
`2 ^ (-2 log₂ k - 1)`. -/
lemma imgMeasure_le_imgWeightedSemimeasure {μ ν : Measure CantorSeq} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {f : BitStream → BitStream} {k : ℕ} (hk : 1 ≤ k) (y : BitString) :
    ((2 : ℝ≥0∞)⁻¹) ^ (2 * Nat.log 2 k + 1) * imgMeasure μ ν f k y
      ≤ imgWeightedSemimeasure μ ν f y := by
  set i := Nat.log 2 k with hi
  have hkpos : k ≠ 0 := by omega
  have hlow : 2 ^ i ≤ k := Nat.pow_log_le_self 2 hkpos
  have hhigh : k < 2 ^ (i + 1) := Nat.lt_pow_succ_log_self (by norm_num) k
  have hj : k - 2 ^ i < 2 ^ i := by
    have : 2 ^ (i + 1) = 2 ^ i + 2 ^ i := by ring
    omega
  have hk_eq : 2 ^ i + (k - 2 ^ i) = k := by omega
  have hterm : imgMeasure μ ν f k y
      ≤ ∑ j ∈ Finset.range (2 ^ i), imgMeasure μ ν f (2 ^ i + j) y := by
    refine le_trans (le_of_eq ?_) (Finset.single_le_sum
      (f := fun j => imgMeasure μ ν f (2 ^ i + j) y) (fun j _ => zero_le)
      (Finset.mem_range.2 hj))
    rw [hk_eq]
  calc ((2 : ℝ≥0∞)⁻¹) ^ (2 * i + 1) * imgMeasure μ ν f k y
      = dyadicWeight i * (((2 : ℝ≥0∞)⁻¹) ^ i * imgMeasure μ ν f k y) := by
        rw [dyadicWeight, ← mul_assoc, ← pow_add]
        congr 2
        omega
    _ ≤ dyadicWeight i * imgBlockAverage μ ν f i y := by
        gcongr
        rw [imgBlockAverage]
        gcongr
    _ ≤ imgWeightedSemimeasure μ ν f y := continuousTreeMixture_dominates_component _ i y

/-! ## The leaf of Problem 187 -/

/-- For a computable measure and a computable stream map there is a lower semicomputable continuous
semimeasure that exceeds `2 ^ k / (2 k ²)` times the `μ`-mass of every string whose image has
`ν`-deficiency above `k`: image deficiency is paid for by a priori mass. -/
theorem exists_imageDeficiencyWeightedSemimeasure {μ ν : Measure CantorSeq}
    {f : BitStream → BitStream} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : IsComputableMeasure μ) (hf : IsComputableStreamMap f) (hν : IsImageMeasure μ f ν) :
    ∃ S : BitString → ℝ≥0∞, IsLowerSemicomputableContinuousSemimeasure S ∧
      ∀ (k : ℕ) (u w : BitString) (D : ℝ), 1 ≤ k →
        BitStream.finite u ≤ f (BitStream.finite w) → deficiency ν u = (D : EReal) →
        (k : ℝ) < D →
          ENNReal.ofReal ((2 : ℝ) ^ k / (2 * (k : ℝ) ^ 2)) * cantorMass μ w ≤ S w := by
  have hν' : IsComputableMeasure ν := isComputableMeasure_of_isImageMeasure hμ hf hν
  refine ⟨imgWeightedSemimeasure μ ν f,
    isLSCContinuousSemimeasure_imgWeightedSemimeasure hμ hν' hf hν, ?_⟩
  intro k u w D hk hle hdu hkD
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have huD : u ∈ aPrioriDeficiencySet ν k := by
    by_contra hcon
    rw [aPrioriDeficiencySet, Set.mem_ofPred_eq, not_lt] at hcon
    have hle2 := deficiency_le_of_apriori_le (P := ν) (x := u) (c := k) hcon
    rw [hdu, EReal.coe_le_coe_iff] at hle2
    linarith
  have hw : w ≠ [] := by
    intro h0
    subst h0
    have huniv : cantorMass ν u = 1 := by
      rw [hν u]
      have hset : {x : CantorSeq | BitStream.finite u ≤ f (BitStream.infinite x)} = Set.univ := by
        ext x
        simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
        exact le_trans hle (hf.1.1 (by simp))
      rw [hset]
      simp
    have hA1 : universalContinuousSemimeasure u ≤ 1 :=
      universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.1.le_one u
    have hKA : 0 ≤ KA u := by
      rw [KA, neg_nonneg]
      refine Real.logb_nonpos (by norm_num) ENNReal.toReal_nonneg ?_
      have h1 : (universalContinuousSemimeasure u).toReal ≤ (1 : ℝ≥0∞).toReal :=
        ENNReal.toReal_mono (by norm_num) hA1
      simpa using h1
    have hval : deficiency ν u = ((-KA u : ℝ) : EReal) := by
      rw [deficiency_of_ne_zero (by rw [huniv]; norm_num), huniv]
      simp
    rw [hval, EReal.coe_eq_coe_iff] at hdu
    rw [← hdu] at hkD
    linarith
  have hsub : cantorCylinder w ⊆ imgDeficiencySet ν f k := by
    intro x hx
    exact ⟨u, huD, le_trans hle (hf.1.1 (BitStream.finite_le_infinite_iff.2 hx))⟩
  have hmass : imgMeasure μ ν f k w = (2 : ℝ≥0∞) ^ k * cantorMass μ w := by
    rw [imgMeasure_of_ne_nil hw, Set.inter_eq_self_of_subset_left hsub]
    rfl
  have hdom := imgMeasure_le_imgWeightedSemimeasure (μ := μ) (ν := ν) (f := f) hk w
  rw [hmass] at hdom
  refine le_trans ?_ hdom
  set i := Nat.log 2 k with hi
  have hlow : 2 ^ i ≤ k := Nat.pow_log_le_self 2 (by omega)
  have hlowR : (2 : ℝ) ^ i ≤ (k : ℝ) := by exact_mod_cast hlow
  have hnum : ((2 : ℝ)) ^ (2 * i + 1) ≤ 2 * (k : ℝ) ^ 2 := by
    have h1 : ((2 : ℝ)) ^ (2 * i + 1) = 2 * ((2 : ℝ) ^ i) ^ 2 := by
      rw [show 2 * i + 1 = i * 2 + 1 by ring, pow_succ, pow_mul]
      ring
    have h2 : ((2 : ℝ) ^ i) ^ 2 ≤ (k : ℝ) ^ 2 := by
      have hpos : (0 : ℝ) ≤ (2 : ℝ) ^ i := by positivity
      nlinarith
    rw [h1]
    linarith
  have hsplit : ENNReal.ofReal ((2 : ℝ) ^ k / (2 * (k : ℝ) ^ 2))
      = (2 : ℝ≥0∞) ^ k * ENNReal.ofReal (1 / (2 * (k : ℝ) ^ 2)) := by
    rw [div_eq_mul_one_div, ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  have hweight : ENNReal.ofReal (1 / (2 * (k : ℝ) ^ 2))
      ≤ ((2 : ℝ≥0∞)⁻¹) ^ (2 * i + 1) := by
    rw [← ENNReal.inv_pow, ENNReal.le_inv_iff_mul_le]
    have hpow : ((2 : ℝ≥0∞)) ^ (2 * i + 1) = ENNReal.ofReal ((2 : ℝ) ^ (2 * i + 1)) := by
      rw [ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 2)]
      norm_num
    rw [hpow, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_one.2 ?_
    rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
    exact hnum
  calc ENNReal.ofReal ((2 : ℝ) ^ k / (2 * (k : ℝ) ^ 2)) * cantorMass μ w
      = (2 : ℝ≥0∞) ^ k * ENNReal.ofReal (1 / (2 * (k : ℝ) ^ 2)) * cantorMass μ w := by
        rw [hsplit]
    _ ≤ (2 : ℝ≥0∞) ^ k * ((2 : ℝ≥0∞)⁻¹) ^ (2 * i + 1) * cantorMass μ w := by gcongr
    _ = ((2 : ℝ≥0∞)⁻¹) ^ (2 * i + 1) * ((2 : ℝ≥0∞) ^ k * cantorMass μ w) := by ring

end Kolmogorov
