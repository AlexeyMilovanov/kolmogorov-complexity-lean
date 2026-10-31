/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.PackingEquivalences.BSDimension.CoveringComparison

/-!
# A raw-threshold counterexample for BS capacities

The finite and the zero raw thresholds of the Barreira–Schmeling capacities cannot be identified
on a set merely because all of its pointwise Birkhoff averages are positive: this is why the
packing equivalences of Appendix A first localize to pieces on which the averages are uniformly
positive.

This file proves the existential counterexample `rawThresholdCounterexample` (blueprint node
`pack:raw-threshold-counterexample`).  The system is the binary shift on `ℕ → Bool` with the
first-difference metric, the potential is the first bit, and `Z` is the countable set of the
sequences `0ʲ1^∞`.  Along the orbit of the `j`-th point the Birkhoff sums are `(n - j)₊`, so all
averages tend to one.  For the radius `1/2`, up to a bounded multiplicity the Bowen balls
around the points of `Z` are determined by the number of leading zeros of their centers, and the
covering and separated BS sums at every exponent `a > 0` are bounded by a fixed multiple of the
geometric series `∑ₖ 2⁻ᵃᵏ`.  Nevertheless, for centers far out the whole Bowen ball has potential
sum zero, so every BS sum is at least one for every `a ≥ 0`.  Hence the raw finite thresholds are
zero, the raw zero thresholds are infinite, while the (countably modified) upper and separated
BS dimensions vanish, and so does the packing BS dimension, by the uniform-positivity
equivalences.

The module is used by `KolmogorovMathlib.PointToSet.PackingEquivalences.BSDimension`.
-/

namespace Kolmogorov.PointToSet

open Filter Set
open scoped Topology ENNReal

/-! ### The binary shift system -/

/-- The space of binary sequences. -/
private abbrev BinarySequence := ℕ → Bool

/-- The first-difference metric on binary sequences. -/
private noncomputable abbrev binarySequenceMetricSpace : MetricSpace BinarySequence :=
  PiNat.metricSpaceOfDiscreteUniformity (fun _ ↦ rfl)

/-- The canonical dense-sequence presentation of the binary shift space. -/
private noncomputable def binarySequencePresentation :
    @Presentation BinarySequence binarySequenceMetricSpace :=
  letI := binarySequenceMetricSpace
  { ι := TopologicalSpace.denseSeq BinarySequence
    dense := TopologicalSpace.denseRange_denseSeq BinarySequence
    complete := inferInstance }

/-- The left shift on binary sequences. -/
private def binaryShift (x : BinarySequence) : BinarySequence :=
  fun i ↦ x (i + 1)

/-- The potential recording whether the initial coordinate is true. -/
private noncomputable def firstBitPotential (x : BinarySequence) : ℝ :=
  if x 0 then 1 else 0

/-- The binary sequence that becomes permanently true starting at time `j`. -/
private def delayedTruePoint (j : ℕ) : BinarySequence :=
  fun i ↦ decide (j ≤ i)

/-- The countable set of binary sequences that eventually become permanently true. -/
private def eventuallyTrueSet : Set BinarySequence :=
  Set.range delayedTruePoint

/-- The fixed radius used to separate the delayed binary sequences. -/
private noncomputable def separationRadius : ℝ := 1 / 2

attribute [local instance] binarySequenceMetricSpace

/-- The left shift is continuous in the binary sequence metric. -/
private lemma continuous_binaryShift : Continuous binaryShift :=
  continuous_pi fun i ↦ continuous_apply (i + 1)

/-- The potential recording the initial binary coordinate is uniformly continuous. -/
private lemma uniformContinuous_firstBitPotential : UniformContinuous firstBitPotential := by
  refine (LipschitzWith.of_dist_le_mul (K := 1) fun x y ↦ ?_).uniformContinuous
  by_cases h : x 0 = y 0
  · simp [firstBitPotential, h]
  · have hdist : dist x y = 1 := by
      have hfirst : PiNat.firstDiff x y = 0 := by
        by_contra hne
        exact h (PiNat.apply_eq_of_lt_firstDiff (Nat.pos_of_ne_zero hne))
      rw [PiNat.dist_eq_of_ne (fun hxy ↦ h (by rw [hxy])), hfirst, pow_zero]
    rw [hdist, NNReal.coe_one, one_mul]
    unfold firstBitPotential
    cases hx : x 0 <;> cases hy : y 0 <;> simp_all [Real.dist_eq]

local notation "Ω" => BinarySequence
local notation "T₀" => binaryShift
local notation "u₀" => firstBitPotential
local notation "Z₀" => eventuallyTrueSet
local notation "r₀" => separationRadius
local notation "z₀" => delayedTruePoint

/-! ### The orbit of a point of `Z` -/

/-- Coordinate `i` of the `k`-th shift of `0ʲ1^∞` is `1` exactly when `j ≤ i + k`. -/
private lemma iterate_shift_point (k j i : ℕ) :
    (T₀^[k] (z₀ j)) i = decide (j ≤ i + k) := by
  induction k generalizing i with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    change (T₀^[k] (z₀ j)) (i + 1) = _
    rw [ih]
    simp only [decide_eq_decide]
    omega

/-- The potential along the orbit of `0ʲ1^∞` switches from `0` to `1` at time `j`. -/
private lemma u_iterate_point (k j : ℕ) :
    u₀ (T₀^[k] (z₀ j)) = if j ≤ k then (1 : ℝ) else 0 := by
  simp only [firstBitPotential, iterate_shift_point, zero_add, decide_eq_true_eq]

/-- The Birkhoff sums along the orbit of `0ʲ1^∞` are `n - j` (truncated subtraction). -/
private lemma birkhoffSum_point (j n : ℕ) :
    birkhoffSum T₀ u₀ n (z₀ j) = ((n - j : ℕ) : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    unfold birkhoffSum at ih ⊢
    rw [Finset.sum_range_succ, ih, u_iterate_point]
    split_ifs with h
    · rw [Nat.succ_sub h, Nat.cast_succ]
    · rw [Nat.sub_eq_zero_of_le (by omega), Nat.sub_eq_zero_of_le (by omega)]
      simp

/-- The ratio `(n - j) / n` tends to `1`. -/
private lemma tendsto_natCast_sub_div_natCast (j : ℕ) :
    Tendsto (fun n : ℕ ↦ ((n - j : ℕ) : ℝ) / n) atTop (𝓝 1) := by
  have h : Tendsto (fun n : ℕ ↦ (1 : ℝ) - j / n) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat (j : ℝ))
  rw [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [Ici_mem_atTop (j + 1)] with n (hn : j + 1 ≤ n)
  rw [Nat.cast_sub (by omega), sub_div, div_self (Nat.cast_ne_zero.mpr (by omega))]

/-- The Birkhoff averages along the orbit of each point of `Z` tend to one. -/
private lemma tendsto_birkhoffSum_div_point (j : ℕ) :
    Tendsto (fun n : ℕ ↦ birkhoffSum T₀ u₀ n (z₀ j) / n) atTop (𝓝 (1 : ℝ)) := by
  simp only [birkhoffSum_point]
  exact tendsto_natCast_sub_div_natCast j

/-- The lower Birkhoff average along the orbit of each point of `Z` is positive. -/
private lemma lowerBirkhoffAverage_point_pos (j : ℕ) : 0 < lowerBirkhoffAverage T₀ u₀ (z₀ j) := by
  have h : Tendsto (fun n : ℕ ↦ ((birkhoffSum T₀ u₀ n (z₀ j) / n : ℝ) : EReal)) atTop (𝓝 1) :=
    (continuous_coe_real_ereal.tendsto 1).comp (tendsto_birkhoffSum_div_point j)
  unfold lowerBirkhoffAverage
  rw [h.liminf_eq]
  norm_num

/-! ### Bowen balls and BS weights around the points of `Z` -/

/-- The radius `1/2` of the counterexample is positive. -/
private lemma radius_pos : 0 < r₀ := by
  norm_num [separationRadius]

/-- If `n < j` and `n < l`, the first `n` shifts of `0ʲ1^∞` and `0ˡ1^∞` are at distance at most
`(1/2)²`: they agree on the first two coordinates. -/
private lemma dist_iterate_point_le {n j l k : ℕ} (hj : ¬ j ≤ n) (hl : ¬ l ≤ n) (hk : k < n) :
    dist (T₀^[k] (z₀ j)) (T₀^[k] (z₀ l)) ≤ (1 / 2 : ℝ) ^ 2 := by
  refine PiNat.mem_cylinder_iff_dist_le.mp fun i hi ↦ ?_
  rw [iterate_shift_point, iterate_shift_point]
  have hij : ¬ j ≤ i + k := by omega
  have hil : ¬ l ≤ i + k := by omega
  simp [hij, hil]

/-- Two points of `Z` whose first one occurs after time `n` are within `1/4` in the Bowen
distance of order `n`. -/
private lemma bowenDist_point_le {n j l : ℕ} (hj : ¬ j ≤ n) (hl : ¬ l ≤ n) :
    bowenDist T₀ n (z₀ j) (z₀ l) ≤ 1 / 4 := by
  have hsup : (Finset.range n).sup (fun k ↦ nndist (T₀^[k] (z₀ j)) (T₀^[k] (z₀ l))) ≤
      (⟨1 / 4, by norm_num⟩ : NNReal) := by
    refine Finset.sup_le fun k hk ↦ ?_
    have h := dist_iterate_point_le hj hl (Finset.mem_range.mp hk)
    norm_num at h
    exact_mod_cast h
  exact_mod_cast hsup

/-- For `n + 2` points of `Z`, the Bowen balls of order `n` and radius `1/2` cover `Z`. -/
private lemma Z_subset_iUnion_bowenBall (n : ℕ) :
    Z₀ ⊆ ⋃ i : Fin (n + 2), bowenBall T₀ n (z₀ i) r₀ := by
  rintro _ ⟨j, rfl⟩
  refine mem_iUnion.mpr ?_
  by_cases hj : j ≤ n
  · exact ⟨⟨j, by omega⟩, self_mem_bowenBall T₀ n _ r₀ radius_pos⟩
  · refine ⟨⟨n + 1, by omega⟩, mem_bowenBall_iff.mpr fun k hk ↦ ?_⟩
    calc dist (T₀^[k] (z₀ (n + 1))) (T₀^[k] (z₀ j))
        ≤ (1 / 2 : ℝ) ^ 2 := dist_iterate_point_le (Nat.not_succ_le_self n) hj hk
      _ < r₀ := by norm_num [separationRadius]

/-- The BS weight of the Bowen ball around the `j`-th point of `Z` is at most `2 ^ (-a (n - j))`:
the ball contains its center, where the Birkhoff sum is `n - j`. -/
private lemma bsBallWeight_point_le {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (j n : ℕ) :
    bsBallWeight T₀ u₀ a n (z₀ j) r ≤ (2 : ℝ≥0∞) ^ (-a * ((n - j : ℕ) : ℝ)) := by
  have hbase : (2 : ℝ≥0∞) ^ ((n - j : ℕ) : ℝ) ≤ pressureBallWeight T₀ u₀ .supremum n (z₀ j) r := by
    rw [← birkhoffSum_point j n]
    exact le_iSup₂_of_le (z₀ j) (self_mem_bowenBall T₀ n _ r hr) le_rfl
  unfold bsBallWeight
  rw [ENNReal.rpow_neg]
  calc (pressureBallWeight T₀ u₀ .supremum n (z₀ j) r ^ a)⁻¹
      ≤ (((2 : ℝ≥0∞) ^ ((n - j : ℕ) : ℝ)) ^ a)⁻¹ :=
        ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow hbase ha.le)
    _ = (2 : ℝ≥0∞) ^ (-a * ((n - j : ℕ) : ℝ)) := by
        rw [← ENNReal.rpow_neg, ← ENNReal.rpow_mul]
        congr 1
        ring

/-- If the Bowen ball of order `n` around `y` contains the point `0ⁿ⁺¹1^∞`, then all its points
have vanishing Birkhoff sum of order `n`, hence its BS weight is at least one. -/
private lemma one_le_bsBallWeight_of_mem_bowenBall {a : ℝ} (ha : 0 ≤ a) {n : ℕ} {y : Ω}
    (hx : z₀ (n + 1) ∈ bowenBall T₀ n y r₀) : 1 ≤ bsBallWeight T₀ u₀ a n y r₀ := by
  have hbit : ∀ q ∈ bowenBall T₀ n y r₀, ∀ k < n, (T₀^[k] y) 0 = (T₀^[k] q) 0 := fun q hq k hk ↦
    PiNat.apply_eq_of_dist_lt (n := 1)
      (by simpa only [pow_one, separationRadius]
        using mem_bowenBall_iff.mp hq k hk)
      (Nat.zero_le 1)
  have hsum : ∀ z ∈ bowenBall T₀ n y r₀, birkhoffSum T₀ u₀ n z = 0 := by
    intro z hz
    refine Finset.sum_eq_zero fun k hk ↦ ?_
    have hk' := Finset.mem_range.mp hk
    have e : (T₀^[k] z) 0 = (T₀^[k] (z₀ (n + 1))) 0 :=
      (hbit z hz k hk').symm.trans (hbit _ hx k hk')
    have hk0 : ¬ n + 1 ≤ k := by omega
    rw [firstBitPotential, e, ← firstBitPotential, u_iterate_point]
    simp only [hk0, ↓reduceIte]
  have hbase : pressureBallWeight T₀ u₀ .supremum n y r₀ ≤ 1 :=
    iSup₂_le fun z hz ↦ by simp only [hsum z hz, ENNReal.rpow_zero, le_refl]
  unfold bsBallWeight
  rw [ENNReal.rpow_neg]
  simpa only [ENNReal.one_rpow, inv_one] using
    ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow hbase ha)

/-! ### Real-exponent geometric series -/

/-- The ratio `2 ^ (-a)` is less than one for `a > 0`. -/
private lemma two_rpow_neg_lt_one {a : ℝ} (ha : 0 < a) : (2 : ℝ≥0∞) ^ (-a) < 1 :=
  ENNReal.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_lt_zero.mpr ha)

/-- A geometric series with ratio `2 ^ (-a)` has finite sum. -/
private lemma one_add_tsum_two_rpow_lt_top {a : ℝ} (ha : 0 < a) :
    1 + ∑' k : ℕ, (2 : ℝ≥0∞) ^ (-a * (k : ℝ)) < ⊤ := by
  refine ENNReal.add_lt_top.mpr ⟨ENNReal.one_lt_top, ?_⟩
  simp only [ENNReal.rpow_mul, ENNReal.rpow_natCast]
  exact tsum_geometric_lt_top.mpr (two_rpow_neg_lt_one ha)

/-- The terms `2 ^ (-a (n - i))`, `i ≤ n + 1`, sum to at most one plus the full series. -/
private lemma sum_fin_two_rpow_le {a : ℝ} (n : ℕ) :
    ∑ i : Fin (n + 2), (2 : ℝ≥0∞) ^ (-a * ((n - i : ℕ) : ℝ)) ≤
      1 + ∑' k : ℕ, (2 : ℝ≥0∞) ^ (-a * (k : ℝ)) := by
  rw [Fin.sum_univ_eq_sum_range (fun i ↦ (2 : ℝ≥0∞) ^ (-a * ((n - i : ℕ) : ℝ))) (n + 2),
    Finset.sum_range_succ, Nat.sub_eq_zero_of_le (Nat.le_succ n), Nat.cast_zero, mul_zero,
    ENNReal.rpow_zero, add_comm]
  gcongr
  have h := Finset.sum_range_reflect (fun k : ℕ ↦ (2 : ℝ≥0∞) ^ (-a * (k : ℝ))) (n + 1)
  simp only [Nat.add_sub_cancel] at h
  rw [h]
  exact ENNReal.sum_le_tsum _

/-! ### The covering and the separated sums stay bounded -/

/-- A finite family of centers whose Bowen balls cover `Z` bounds the fixed-order BS covering
sum by the total weight of the balls. -/
private lemma bsPartitionSum_le_sum_fin_cover {X : Type*} [MetricSpace X] (T : X → X)
    (u : X → ℝ) (Z : Set X) (s r : ℝ) (n k : ℕ) (c : Fin k → X)
    (hc : Z ⊆ ⋃ i, bowenBall T n (c i) r) :
    bsPartitionSum T u Z s r n ≤ ∑ i, bsBallWeight T u s n (c i) r := by
  refine iInf_le_of_le (range c) (iInf_le_of_le ⟨countable_range c, ?_⟩ ?_)
  · refine hc.trans (iUnion_subset fun i ↦ ?_)
    exact subset_biUnion_of_mem (u := fun y ↦ bowenBall T n y r) (mem_range_self i)
  · have h : ∑' y : range c, bsBallWeight T u s n y r ≤
        ∑' i : Fin k, bsBallWeight T u s n (rangeFactorization c i) r :=
      ENNReal.tsum_le_tsum_comp_of_surjective (f := rangeFactorization c)
        rangeFactorization_surjective (fun y : range c ↦ bsBallWeight T u s n y r)
    exact h.trans_eq (tsum_fintype _)

/-- The fixed-order BS covering sums of `Z` have finite upper limit at every exponent `a > 0`. -/
private lemma limsup_bsPartitionSum_lt_top {a : ℝ} (ha : 0 < a) :
    limsup (bsPartitionSum T₀ u₀ Z₀ a r₀) atTop < ⊤ := by
  refine lt_of_le_of_lt (limsup_le_of_le (by isBoundedDefault) (Eventually.of_forall fun n ↦ ?_))
    (one_add_tsum_two_rpow_lt_top ha)
  refine (bsPartitionSum_le_sum_fin_cover _ _ _ _ _ _ _ _ (Z_subset_iUnion_bowenBall n)).trans ?_
  exact (Finset.sum_le_sum fun (i : Fin (n + 2)) _ ↦
    bsBallWeight_point_le ha radius_pos i.val n).trans
    (sum_fin_two_rpow_le (a := a) n)

/-- A Bowen-separated subset of `Z` can be coded injectively by the number `n - j + 1` of its
first ones in the window, with the code `0` reserved for all indices beyond `n`: two
representatives beyond `n` are within `1/4`, hence not separated at radius `1/2`. -/
private lemma exists_injective_code {n : ℕ} {F : Set Ω} (hsub : F ⊆ Z₀)
    (hsep : IsBowenSeparated T₀ n r₀ F) :
    ∃ J : F → ℕ, (∀ x, z₀ (J x) = x.val) ∧
      Function.Injective (fun x ↦ if J x ≤ n then n - J x + 1 else 0) := by
  choose J hJ using fun x : F ↦ hsub x.property
  refine ⟨J, hJ, fun x y hcode ↦ Subtype.ext ?_⟩
  by_cases hx : J x ≤ n <;> by_cases hy : J y ≤ n
  · simp only [hx, hy, ↓reduceIte] at hcode
    rw [← hJ x, ← hJ y, show J x = J y by omega]
  · simp only [hx, hy, ↓reduceIte] at hcode
    omega
  · simp only [hx, hy, ↓reduceIte] at hcode
    omega
  · by_contra hxy
    have hfar := hsep x.property y.property hxy
    have hclose := bowenDist_point_le hx hy
    rw [hJ x, hJ y] at hclose
    norm_num [separationRadius] at hfar
    linarith

/-- The BS cost of a Bowen-separated subset of `Z` is at most one plus the geometric series. -/
private lemma bsPartitionCoverCost_le_of_separated {a : ℝ} (ha : 0 < a) {n : ℕ} {F : Set Ω}
    (hsub : F ⊆ Z₀) (hsep : IsBowenSeparated T₀ n r₀ F) :
    bsPartitionCoverCost T₀ u₀ a r₀ n F ≤ 1 + ∑' k : ℕ, (2 : ℝ≥0∞) ^ (-a * (k : ℝ)) := by
  classical
  obtain ⟨J, hJ, hcode⟩ := exists_injective_code hsub hsep
  let g : ℕ → ℝ≥0∞
    | 0 => 1
    | k + 1 => (2 : ℝ≥0∞) ^ (-a * (k : ℝ))
  have hweight (x : F) :
      bsBallWeight T₀ u₀ a n x.val r₀ ≤ g (if J x ≤ n then n - J x + 1 else 0) := by
    rw [← hJ x]
    have h := bsBallWeight_point_le ha radius_pos (J x) n
    by_cases hx : J x ≤ n
    · simpa [g, hx] using h
    · simpa [g, hx, show n - J x = 0 by omega] using h
  calc bsPartitionCoverCost T₀ u₀ a r₀ n F
      ≤ ∑' x : F, g (if J x ≤ n then n - J x + 1 else 0) := ENNReal.tsum_le_tsum hweight
    _ ≤ ∑' k : ℕ, g k := ENNReal.tsum_comp_le_tsum_of_injective hcode g
    _ = 1 + ∑' k : ℕ, (2 : ℝ≥0∞) ^ (-a * (k : ℝ)) := tsum_eq_zero_add' ENNReal.summable

/-- The separated BS sums of `Z` have finite upper limit at every exponent `a > 0`. -/
private lemma limsup_separatedBSSum_lt_top {a : ℝ} (ha : 0 < a) :
    limsup (separatedBSSum T₀ u₀ Z₀ a r₀) atTop < ⊤ := by
  refine lt_of_le_of_lt (limsup_le_of_le (by isBoundedDefault) (Eventually.of_forall fun n ↦ ?_))
    (one_add_tsum_two_rpow_lt_top ha)
  exact iSup₂_le fun F hF ↦ bsPartitionCoverCost_le_of_separated ha hF.1 hF.2

/-! ### The covering and the separated sums are at least one -/

/-- A sequence of terms that are all at least one has upper limit at least one. -/
private lemma one_le_limsup_of_forall_one_le {f : ℕ → ℝ≥0∞} (h : ∀ n, 1 ≤ f n) :
    1 ≤ limsup f atTop :=
  calc (1 : ℝ≥0∞) = limsup (fun _ : ℕ ↦ (1 : ℝ≥0∞)) atTop := (limsup_const 1).symm
    _ ≤ limsup f atTop := limsup_le_limsup (Eventually.of_forall h)

/-- Every cover of `Z` by Bowen balls of order `n` contains the ball around some center of
`0ⁿ⁺¹1^∞`, of weight at least one. -/
private lemma one_le_bsPartitionSum {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    1 ≤ bsPartitionSum T₀ u₀ Z₀ a r₀ n := by
  refine le_iInf₂ fun F hF ↦ ?_
  obtain ⟨y, hyF, hxy⟩ := mem_iUnion₂.mp (hF.2 (mem_range_self (n + 1) : z₀ (n + 1) ∈ Z₀))
  exact (one_le_bsBallWeight_of_mem_bowenBall ha hxy).trans
    (ENNReal.le_tsum (f := fun w : F ↦ bsBallWeight T₀ u₀ a n w.val r₀) ⟨y, hyF⟩)

/-- The singleton `{0ⁿ⁺¹1^∞}` is a Bowen-separated subset of `Z` of weight at least one. -/
private lemma one_le_separatedBSSum {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    1 ≤ separatedBSSum T₀ u₀ Z₀ a r₀ n := by
  have hx : z₀ (n + 1) ∈ bowenBall T₀ n (z₀ (n + 1)) r₀ :=
    self_mem_bowenBall T₀ n _ r₀ radius_pos
  refine le_iSup₂_of_le {z₀ (n + 1)}
    ⟨singleton_subset_iff.mpr (mem_range_self (n + 1)), pairwise_singleton _ _⟩ ?_
  rw [bsPartitionCoverCost, tsum_singleton (z₀ (n + 1)) (fun y ↦ bsBallWeight T₀ u₀ a n y r₀)]
  exact one_le_bsBallWeight_of_mem_bowenBall ha hx

/-! ### Capacities -/

/-- An infimum of `ENNReal.ofReal s` over `s ≥ 0` satisfying a predicate vanishes as soon as
every positive `s` satisfies it. -/
private lemma iInf_ofReal_eq_zero {p : ℝ → Prop} (h : ∀ a : ℝ, 0 < a → p a) :
    (⨅ (s : ℝ) (_ : 0 ≤ s) (_ : p s), ENNReal.ofReal s) = 0 := by
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_) bot_le
  have hε' : (0 : ℝ) < ε := NNReal.coe_pos.mpr hε
  rw [zero_add]
  calc (⨅ (s : ℝ) (_ : 0 ≤ s) (_ : p s), ENNReal.ofReal s) ≤ ENNReal.ofReal ε :=
      iInf_le_of_le (ε : ℝ) (iInf_le_of_le hε'.le (iInf_le_of_le (h _ hε') le_rfl))
    _ = ε := ENNReal.ofReal_coe_nnreal

/-- The upper BS capacity of `Z` at radius `1/2` is zero. -/
private lemma upperBSCapacityAt_Z_eq_zero : upperBSCapacityAt T₀ u₀ Z₀ r₀ = 0 :=
  iInf_ofReal_eq_zero (p := fun s ↦ limsup (bsPartitionSum T₀ u₀ Z₀ s r₀) atTop < ⊤)
    fun _ ha ↦ limsup_bsPartitionSum_lt_top ha

/-- The upper BS zero capacity of `Z` at radius `1/2` is infinite. -/
private lemma upperBSZeroCapacityAt_Z_eq_top : upperBSZeroCapacityAt T₀ u₀ Z₀ r₀ = ⊤ :=
  eq_top_iff.mpr <| le_iInf fun a ↦ le_iInf fun ha ↦ le_iInf fun hz ↦ by
    have h := one_le_limsup_of_forall_one_le (one_le_bsPartitionSum ha)
    rw [hz] at h
    exact absurd h (by simp)

/-- The finite separated capacity of `Z` at radius `1/2` is zero. -/
private lemma separatedBSFiniteCapacityAt_Z_eq_zero :
    separatedBSFiniteCapacityAt T₀ u₀ Z₀ r₀ = 0 :=
  iInf_ofReal_eq_zero (p := fun s ↦ limsup (separatedBSSum T₀ u₀ Z₀ s r₀) atTop < ⊤)
    fun _ ha ↦ limsup_separatedBSSum_lt_top ha

/-- The separated zero capacity of `Z` at radius `1/2` is infinite. -/
private lemma separatedBSZeroCapacityAt_Z_eq_top : separatedBSZeroCapacityAt T₀ u₀ Z₀ r₀ = ⊤ :=
  eq_top_iff.mpr <| le_iInf fun a ↦ le_iInf fun ha ↦ le_iInf fun hz ↦ by
    have h := one_le_limsup_of_forall_one_le (one_le_separatedBSSum ha)
    rw [hz] at h
    exact absurd h (by simp)

/-! ### Singletons have vanishing capacities -/

/-- A single point has upper BS capacity zero at any positive radius: at exponent `0`, the
point alone covers itself with weight one. -/
private lemma upperBSCapacityAt_singleton_eq_zero (j : ℕ) {r : ℝ} (hr : 0 < r) :
    upperBSCapacityAt T₀ u₀ {z₀ j} r = 0 := by
  refine le_antisymm (iInf_le_of_le 0 (iInf_le_of_le le_rfl (iInf_le_of_le ?_ (by simp)))) bot_le
  have hle (n : ℕ) : bsPartitionSum T₀ u₀ {z₀ j} 0 r n ≤ 1 := by
    have hcover : ({z₀ j} : Set Ω) ⊆ ⋃ _ : Fin 1, bowenBall T₀ n (z₀ j) r := by
      rintro _ rfl
      exact mem_iUnion.mpr ⟨0, self_mem_bowenBall T₀ n _ r hr⟩
    refine (bsPartitionSum_le_sum_fin_cover _ _ _ _ _ _ _ (fun _ : Fin 1 ↦ z₀ j) hcover).trans ?_
    simp [bsBallWeight]
  exact (limsup_le_of_le (by isBoundedDefault) (Eventually.of_forall hle)).trans_lt
    ENNReal.one_lt_top

/-- The separated BS sum of a single point is at most the weight of its Bowen ball. -/
private lemma separatedBSSum_singleton_le (j n : ℕ) (a r : ℝ) :
    separatedBSSum T₀ u₀ {z₀ j} a r n ≤ bsBallWeight T₀ u₀ a n (z₀ j) r := by
  refine iSup₂_le fun F hF ↦ ?_
  rcases subset_singleton_iff_eq.mp hF.1 with rfl | rfl
  · simp [bsPartitionCoverCost]
  · rw [bsPartitionCoverCost, tsum_singleton (z₀ j) (fun y ↦ bsBallWeight T₀ u₀ a n y r)]

/-- The sequence `2 ^ (-a (n - j))` tends to zero for `a > 0`. -/
private lemma tendsto_two_rpow_neg_mul_sub {a : ℝ} (ha : 0 < a) (j : ℕ) :
    Tendsto (fun n : ℕ ↦ (2 : ℝ≥0∞) ^ (-a * ((n - j : ℕ) : ℝ))) atTop (𝓝 0) := by
  have h := (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (two_rpow_neg_lt_one ha)).comp
    (tendsto_sub_atTop_nat j)
  refine h.congr fun n ↦ ?_
  simp only [Function.comp_apply]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]

/-- A single point has separated zero capacity zero at any positive radius: its separated BS
sums are at most `2 ^ (-a (n - j))`. -/
private lemma separatedBSZeroCapacityAt_singleton_eq_zero (j : ℕ) {r : ℝ} (hr : 0 < r) :
    separatedBSZeroCapacityAt T₀ u₀ {z₀ j} r = 0 :=
  iInf_ofReal_eq_zero (p := fun s ↦ limsup (separatedBSSum T₀ u₀ {z₀ j} s r) atTop = 0) fun a ha ↦
    le_antisymm
      (calc limsup (separatedBSSum T₀ u₀ {z₀ j} a r) atTop
          ≤ limsup (fun n : ℕ ↦ (2 : ℝ≥0∞) ^ (-a * ((n - j : ℕ) : ℝ))) atTop :=
            limsup_le_limsup (Eventually.of_forall fun n ↦
              (separatedBSSum_singleton_le j n a r).trans (bsBallWeight_point_le ha hr j n))
        _ = 0 := (tendsto_two_rpow_neg_mul_sub ha j).limsup_eq)
      bot_le

/-! ### Dimensions -/

/-- If a set function vanishes on the singletons `{0ʲ1^∞}`, its countably modified supremum over
covers of `Z` vanishes. -/
private lemma iInf_cover_eq_zero_of_singletons {c : Set Ω → ℝ≥0∞} (h : ∀ j, c {z₀ j} = 0) :
    (⨅ Y : ℕ → Set Ω, ⨅ (_ : (∀ k, Y k ⊆ Z₀) ∧ Z₀ ⊆ ⋃ k, Y k), ⨆ k, c (Y k)) = 0 := by
  refine le_antisymm (iInf_le_of_le (fun j ↦ {z₀ j}) (iInf_le_of_le ⟨fun j ↦ ?_, ?_⟩ ?_)) bot_le
  · rintro _ rfl
    exact mem_range_self j
  · rintro _ ⟨j, rfl⟩
    exact mem_iUnion.mpr ⟨j, rfl⟩
  · simp [h]

/-- The upper BS dimension of `Z` is zero. -/
private lemma upperBSDimension_Z_eq_zero : upperBSDimension T₀ u₀ Z₀ = 0 :=
  ENNReal.iSup_eq_zero.mpr fun p ↦
    iInf_cover_eq_zero_of_singletons (c := fun Y ↦ upperBSCapacityAt T₀ u₀ Y (dyadicRadius p))
      fun j ↦ upperBSCapacityAt_singleton_eq_zero j (dyadicRadius_pos p)

/-- The separated BS dimension of `Z` is zero. -/
private lemma separatedBSDimension_Z_eq_zero : separatedBSDimension T₀ u₀ Z₀ = 0 :=
  ENNReal.iSup_eq_zero.mpr fun p ↦
    iInf_cover_eq_zero_of_singletons
      (c := fun Y ↦ separatedBSZeroCapacityAt T₀ u₀ Y (dyadicRadius p))
      fun j ↦ separatedBSZeroCapacityAt_singleton_eq_zero j (dyadicRadius_pos p)

/-- The packing BS dimension of `Z` is zero: the potential has positive lower averages on `Z`, so
it agrees with the separated BS dimension. -/
private lemma packingBSDimension_Z_eq_zero : packingBSDimension T₀ u₀ Z₀ = 0 := by
  let _ : TopologicalSpace.SeparableSpace Ω :=
    TopologicalSpace.SeparableSpace.of_denseRange
      binarySequencePresentation.ι binarySequencePresentation.dense
  rw [bsEquivalence T₀ continuous_binaryShift u₀ Z₀
    (by rintro _ ⟨j, rfl⟩; exact lowerBirkhoffAverage_point_pos j)]
  exact separatedBSDimension_Z_eq_zero

/-- A countable set in a complete separable system has averages tending to one but raw
finite thresholds zero and raw zero thresholds infinity; countable modification is zero.
The intended witness is the binary shift, first-bit potential and sequences `0^j 1^∞`.
Blueprint node `pack:raw-threshold-counterexample`. -/
theorem rawThresholdCounterexample :
    ∃ (Y : Type) (_m : MetricSpace Y) (_P : Presentation Y) (T : Y → Y) (u : Y → ℝ)
      (Z : Set Y) (r : ℝ),
      Continuous T ∧ UniformContinuous u ∧ Z.Countable ∧ Z.Nonempty ∧ 0 < r ∧
      (∀ x ∈ Z, Tendsto (fun n => birkhoffSum T u n x / n) atTop (𝓝 (1 : ℝ)) ∧
        0 < lowerBirkhoffAverage T u x) ∧
      (∀ a : ℝ, 0 < a → limsup (bsPartitionSum T u Z a r) atTop < ⊤ ∧
        limsup (separatedBSSum T u Z a r) atTop < ⊤) ∧
      (∀ a : ℝ, 0 ≤ a → ∀ n ≥ 1, 1 ≤ separatedBSSum T u Z a r n) ∧
      upperBSCapacityAt T u Z r = 0 ∧ upperBSZeroCapacityAt T u Z r = ⊤ ∧
      separatedBSFiniteCapacityAt T u Z r = 0 ∧ separatedBSZeroCapacityAt T u Z r = ⊤ ∧
      upperBSDimension T u Z = 0 ∧ separatedBSDimension T u Z = 0 ∧
      packingBSDimension T u Z = 0 :=
  ⟨Ω, binarySequenceMetricSpace, binarySequencePresentation, T₀, u₀, Z₀, r₀,
    continuous_binaryShift, uniformContinuous_firstBitPotential, countable_range _,
    ⟨z₀ 0, mem_range_self 0⟩, radius_pos,
    by rintro _ ⟨j, rfl⟩; exact ⟨tendsto_birkhoffSum_div_point j, lowerBirkhoffAverage_point_pos j⟩,
    fun _ ha ↦ ⟨limsup_bsPartitionSum_lt_top ha, limsup_separatedBSSum_lt_top ha⟩,
    fun _ ha n _ ↦ one_le_separatedBSSum ha n,
    upperBSCapacityAt_Z_eq_zero, upperBSZeroCapacityAt_Z_eq_top,
    separatedBSFiniteCapacityAt_Z_eq_zero, separatedBSZeroCapacityAt_Z_eq_top,
    upperBSDimension_Z_eq_zero, separatedBSDimension_Z_eq_zero, packingBSDimension_Z_eq_zero⟩

end Kolmogorov.PointToSet
