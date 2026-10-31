/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.Conformal.Classical
import KolmogorovMathlib.PointToSet.Pressure.Lower
import KolmogorovMathlib.PointToSet.Pressure.Upper

/-!
# Dimensions of subsets of symbolic shifts

For a countable alphabet `α` and `0 < β < 1`, let `ℕ → α` carry a metric with
`dist x y = β ^ firstDiff x y` for `x ≠ y`, the first-difference formula used in the pressure
chapter. This file proves the corollary of blueprint node `pressure:symbolic-set`: for every
set `Z`, the Hausdorff dimension of `Z` is the lower entropy of the left shift on `Z` divided by
the logarithmic metric scale `-log₂ β`, and the packing dimension is the upper entropy (equivalently
the zero-potential upper pressure) divided by the same scale.

The proof fixes a presentation of `ℕ → α` (a dense sequence of eventually constant strings),
chooses one oracle attaining the entropy minima and the point-to-set minima, and compares the
orbit complexities with the static point dimensions through `symbolic_orbitComplexity_lower` and
`symbolic_orbitComplexity_upper`. Countable alphabets include finite and empty alphabets. All
divisions are in `ENNReal`; the denominator is the positive finite scale
`ENNReal.ofReal (-Real.logb 2 β)`.
-/

namespace Kolmogorov.PointToSet

open scoped ENNReal

section FirstDiffMetric

variable {α : Type*} [MetricSpace (ℕ → α)] {β : ℝ}

omit [MetricSpace (ℕ → α)] in
/-- Two distinct sequences agreeing before `N` first differ at an index at least `N`. -/
private lemma le_firstDiff_of_forall_eq {x y : ℕ → α} (hxy : x ≠ y) {N : ℕ}
    (h : ∀ i < N, x i = y i) : N ≤ PiNat.firstDiff x y := by
  by_contra hlt
  exact PiNat.apply_firstDiff_ne hxy (h _ (not_le.mp hlt))

/-- If two sequences are closer than `β ^ i`, they agree at the coordinate `i`. -/
private lemma apply_eq_of_dist_lt_pow (hβ : 0 < β) (hβ₁ : β < 1)
    (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y)
    {x y : ℕ → α} {i : ℕ} (h : dist x y < β ^ i) : x i = y i := by
  by_cases hxy : x = y
  · rw [hxy]
  · rw [hd x y hxy] at h
    refine PiNat.apply_eq_of_lt_firstDiff (lt_of_not_ge fun hle ↦ ?_)
    exact h.not_ge (pow_le_pow_of_le_one hβ.le hβ₁.le hle)

/-- Sequences agreeing before `N` are at distance less than any `ε > β ^ N`. -/
private lemma dist_lt_of_forall_eq (hβ : 0 < β) (hβ₁ : β < 1)
    (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y)
    {x y : ℕ → α} {N : ℕ} {ε : ℝ} (hN : β ^ N < ε) (h : ∀ i < N, x i = y i) :
    dist x y < ε := by
  by_cases hxy : x = y
  · rw [hxy, dist_self]
    exact (pow_pos hβ N).trans hN
  · rw [hd x y hxy]
    exact (pow_le_pow_of_le_one hβ.le hβ₁.le (le_firstDiff_of_forall_eq hxy h)).trans_lt hN

/-- A countable nonempty alphabet gives a dense sequence of eventually constant strings. -/
private lemma exists_denseRange_of_dist_eq_pow_firstDiff [Countable α] [Nonempty α]
    (hβ : 0 < β) (hβ₁ : β < 1)
    (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y) :
    ∃ ι : ℕ → (ℕ → α), DenseRange ι := by
  obtain ⟨a⟩ := ‹Nonempty α›
  obtain ⟨f, hf⟩ := exists_surjective_nat (List α)
  refine ⟨fun n i ↦ if h : i < (f n).length then (f n).get ⟨i, h⟩ else a, ?_⟩
  rw [Metric.denseRange_iff]
  intro x ε hε
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε hβ₁
  obtain ⟨n, hn⟩ := hf (List.ofFn fun i : Fin N ↦ x i)
  refine ⟨n, ?_⟩
  rw [dist_comm]
  refine dist_lt_of_forall_eq hβ hβ₁ hd hN fun i hi ↦ ?_
  have hge : ¬ N ≤ i := not_le.mpr hi
  simp [hn, hge]

/-- A metric on `ℕ → α` given by the first-difference formula is complete. -/
private lemma completeSpace_of_dist_eq_pow_firstDiff (hβ : 0 < β) (hβ₁ : β < 1)
    (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y) :
    CompleteSpace (ℕ → α) := by
  refine Metric.complete_of_convergent_controlled_sequences (fun n ↦ β ^ n)
    (fun n ↦ by positivity) fun u hu ↦ ⟨fun i ↦ u i i, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε hβ₁
  refine ⟨N, fun n hn ↦ dist_lt_of_forall_eq hβ hβ₁ hd hN fun i hi ↦ ?_⟩
  exact apply_eq_of_dist_lt_pow hβ hβ₁ hd (hu i n i (hi.le.trans hn) le_rfl)

/-- The left shift is Lipschitz, hence continuous, for the first-difference metric. -/
private lemma continuous_shift_of_dist_eq_pow_firstDiff (hβ : 0 < β) (hβ₁ : β < 1)
    (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y) :
    Continuous (fun (y : ℕ → α) j ↦ y (j + 1)) := by
  set f := fun (y : ℕ → α) j ↦ y (j + 1)
  have hlip : LipschitzWith (Real.toNNReal β⁻¹) f := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    by_cases h : f x = f y
    · rw [h, dist_self]
      exact mul_nonneg (NNReal.coe_nonneg _) dist_nonneg
    · have hxy : x ≠ y := fun h_eq ↦ h (by rw [h_eq])
      have hdiff : PiNat.firstDiff x y ≤ PiNat.firstDiff (f x) (f y) + 1 := by
        refine not_lt.mp fun hlt ↦ PiNat.apply_firstDiff_ne h ?_
        exact (PiNat.apply_eq_of_lt_firstDiff hlt : x (PiNat.firstDiff (f x) (f y) + 1) = _)
      rw [hd x y hxy, hd (f x) (f y) h, Real.coe_toNNReal _ (inv_nonneg.mpr hβ.le),
        inv_mul_eq_div, le_div_iff₀ hβ, ← pow_succ]
      exact pow_le_pow_of_le_one hβ.le hβ₁.le hdiff
  exact hlip.continuous

/-- For a countable nonempty alphabet, `ℕ → α` has a presentation: the dense sequence of
eventually constant strings in the complete first-difference metric. -/
private lemma nonempty_presentation_of_dist_eq_pow_firstDiff [Countable α] [Nonempty α]
    (hβ : 0 < β) (hβ₁ : β < 1)
    (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y) :
    Nonempty (Presentation (ℕ → α)) := by
  obtain ⟨ι, hι⟩ := exists_denseRange_of_dist_eq_pow_firstDiff hβ hβ₁ hd
  exact ⟨{ ι := ι, dense := hι, complete := completeSpace_of_dist_eq_pow_firstDiff hβ hβ₁ hd }⟩

end FirstDiffMetric

/-- A supremum over `s` equals the supremum of its multiples by a finite nonzero `c`,
divided by `c`. -/
private lemma iSup_eq_iSup_mul_div {ι : Type*} {c : ℝ≥0∞} (hc0 : c ≠ 0) (hctop : c ≠ ⊤)
    (s : Set ι) (g : ι → ℝ≥0∞) :
    ⨆ x ∈ s, g x = (⨆ x ∈ s, c * g x) / c := by
  rw [ENNReal.eq_div_iff hc0 hctop, ENNReal.mul_iSup]
  exact iSup_congr fun x ↦ ENNReal.mul_iSup _ _

/-- The metric scale `-log₂ β` is positive for `0 < β < 1`. -/
private lemma ofReal_neg_logb_pos {β : ℝ} (hβ : 0 < β) (hβ₁ : β < 1) :
    0 < ENNReal.ofReal (-Real.logb 2 β) :=
  ENNReal.ofReal_pos.mpr (neg_pos.mpr (Real.logb_neg (by norm_num) hβ hβ₁))

/-- Over the empty alphabet every set is empty, so both sides vanish. -/
private theorem dimH_eq_lowerEntropy_div_of_isEmpty {α : Type*} [IsEmpty α]
    [MetricSpace (ℕ → α)] (β : ℝ) (Z : Set (ℕ → α)) :
    _root_.dimH Z = lowerEntropy (fun y j ↦ y (j + 1)) Z / ENNReal.ofReal (-Real.logb 2 β) := by
  rw [Set.eq_empty_of_isEmpty Z, dimH_empty, entropiesAndOrbitComplexities_empty,
    ENNReal.zero_div]

/-- For a fixed presentation, a single oracle attains the lower entropy of the map `T` and the
Hausdorff dimension of `Z` at the same time. -/
private theorem exists_oracle_attaining_lowerEntropy_and_dimH {α : Type*} [Countable α]
    [MetricSpace (ℕ → α)] (P : Presentation (ℕ → α)) (T : (ℕ → α) → (ℕ → α))
    (hT : Continuous T) (Z : Set (ℕ → α)) :
    ∃ A : Set ℕ,
      (lowerEntropy T Z = ⨆ x ∈ Z, (orbitComplexities P T A x).1) ∧
      (_root_.dimH Z = ⨆ x ∈ Z, (staticPointDimensions P A x).1) := by
  obtain ⟨B_ent, hB_ent⟩ := entropy_effectiveCharacterization_allOracles_cone P T hT Z
  obtain ⟨A_dim, -, hA_dim⟩ := classicalPointToSet_attained P Z ∅
  exact ⟨oracleJoin B_ent A_dim, hB_ent _ (oracle_joins B_ent A_dim),
    (hA_dim _ (oracle_joins_right B_ent A_dim)).1⟩

/-- Hausdorff dimension of any symbolic subset is lower entropy divided by the metric scale.
Blueprint node `pressure:symbolic-set`. -/
theorem symbolic_setDimensions_eq_entropies {α : Type*} [Countable α]
    [MetricSpace (ℕ → α)] (β : ℝ) (hβ : 0 < β) (hβ₁ : β < 1)
    (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y)
    (Z : Set (ℕ → α)) :
    _root_.dimH Z = lowerEntropy (fun y j => y (j + 1)) Z /
      ENNReal.ofReal (-Real.logb 2 β) := by
  rcases isEmpty_or_nonempty α with _ | _
  · exact dimH_eq_lowerEntropy_div_of_isEmpty β Z
  · obtain ⟨P⟩ := nonempty_presentation_of_dist_eq_pow_firstDiff hβ hβ₁ hd
    obtain ⟨A, h_ent, h_dim⟩ := exists_oracle_attaining_lowerEntropy_and_dimH P _
      (continuous_shift_of_dist_eq_pow_firstDiff hβ hβ₁ hd) Z
    rw [h_ent, h_dim, iSup_eq_iSup_mul_div (ofReal_neg_logb_pos hβ hβ₁).ne' ENNReal.ofReal_ne_top]
    refine congrArg (· / _) (iSup_congr fun x ↦ iSup_congr fun _ ↦ ?_)
    exact (symbolic_orbitComplexity_lower β hβ hβ₁ hd P A x).symm

section EmptySet

variable {X : Type*} [MetricSpace X]

/-- The partition sum of the empty set vanishes: the empty cover has zero cost. -/
private lemma partitionSum_empty (T : X → X) (φ : X → ℝ) (w : PressureWeight) (n : ℕ) (r : ℝ) :
    partitionSum T φ w ∅ n r = 0 := by
  refine le_antisymm ?_ bot_le
  unfold partitionSum
  refine iInf_le_of_le (∅ : Set X) <| iInf_le_of_le ?_ ?_
  · exact ⟨Set.countable_empty, Set.empty_subset _⟩
  · simp [partitionCoverCost]

/-- The upper capacity of the empty set is `⊥`. -/
private lemma upperCapacity_empty (T : X → X) (φ : X → ℝ) (w : PressureWeight) (r : ℝ) :
    upperCapacity T φ w ∅ r = ⊥ := by
  unfold upperCapacity
  have hrate : pressureRate (fun n ↦ partitionSum T φ w ∅ n r) = fun _ ↦ ⊥ := by
    funext n
    simp only [partitionSum_empty]
    exact pressureRate_zero n
  rw [hrate]
  exact Filter.limsup_const_bot

/-- The modified upper pressure of the empty set is `⊥`. -/
private lemma modifiedUpperPressure_empty (T : X → X) (φ : X → ℝ) (w : PressureWeight)
    (r : ℝ) : modifiedUpperPressure T φ w ∅ r = ⊥ := by
  refine le_antisymm ?_ bot_le
  calc modifiedUpperPressure T φ w ∅ r ≤ ⨆ _ : ℕ, upperCapacity T φ w ∅ r := by
        unfold modifiedUpperPressure
        exact iInf_le_of_le (fun _ ↦ ∅) (iInf_le_of_le (Set.empty_subset _) le_rfl)
    _ = ⊥ := by simp only [upperCapacity_empty, iSup_const]

/-- The upper pressure of the empty set is `⊥`, the bottom of the signed pressure values. -/
private lemma upperPressure_empty (T : X → X) (φ : X → ℝ) (p₀ : ℕ) :
    upperPressure T φ p₀ ∅ = ⊥ := by
  unfold upperPressure
  simp [modifiedUpperPressure_empty]

/-- The specified-radius packing dimension of the empty set is zero. -/
private lemma metricPackingDimension_empty :
    metricPackingDimension (∅ : Set X) = 0 := by
  have hcontent (s δ : ℝ) : metricPackingContent (∅ : Set X) s δ = 0 := by
    refine le_antisymm ?_ bot_le
    unfold metricPackingContent
    refine iSup_le fun F ↦ iSup_le fun hF ↦ ?_
    have hFempty : F = ∅ :=
      Set.eq_empty_of_forall_notMem fun a ha ↦ (hF.1.2.1 a ha).1
    simp [hFempty, metricPackingSum]
  have hpre (s : ℝ) : metricPackingPremeasure (∅ : Set X) s = 0 := by
    refine le_antisymm ?_ bot_le
    unfold metricPackingPremeasure
    exact iInf_le_of_le (1 : ℝ) <| iInf_le_of_le one_pos (hcontent s 1).le
  have hout : metricPackingOuterMeasure (∅ : Set X) 0 = 0 := by
    refine le_antisymm ?_ bot_le
    unfold metricPackingOuterMeasure
    refine iInf_le_of_le (fun _ : ℕ ↦ (∅ : Set X)) <| iInf_le_of_le (Set.empty_subset _) ?_
    simp [hpre]
  refine le_antisymm ?_ bot_le
  unfold metricPackingDimension
  exact iInf_le_of_le (0 : ℝ) <| iInf_le_of_le le_rfl <| iInf_le_of_le hout ENNReal.ofReal_zero.le

end EmptySet

/-- With a fixed presentation, the packing dimension of any symbolic subset is the upper entropy
of the shift divided by the metric scale. The same presentation is used for every oracle.
Blueprint node `pressure:symbolic-set`. -/
theorem symbolic_setDimensions_eq_entropies_upper_entropy {α : Type*} [Countable α]
    [MetricSpace (ℕ → α)] (β : ℝ) (hβ : 0 < β) (hβ₁ : β < 1)
    (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y)
    (P : Presentation (ℕ → α)) (Z : Set (ℕ → α)) :
    metricPackingDimension Z = upperEntropy P (fun y j => y (j + 1)) Z /
      ENNReal.ofReal (-Real.logb 2 β) := by
  obtain ⟨E, hE⟩ := upperEntropy_pointToSet_cone P _
    (continuous_shift_of_dist_eq_pow_firstDiff hβ hβ₁ hd) Z
  obtain ⟨A, hEA, hA⟩ := classicalPointToSet_attained P Z E
  rw [(hA A (TuringReducible.refl _)).2, hE A hEA,
    iSup_eq_iSup_mul_div (ofReal_neg_logb_pos hβ hβ₁).ne' ENNReal.ofReal_ne_top]
  refine congrArg (· / _) (iSup_congr fun x ↦ iSup_congr fun _ ↦ ?_)
  exact (symbolic_orbitComplexity_upper β hβ hβ₁ hd P A x).symm

/-- Packing dimension of any symbolic subset is the zero-potential upper pressure of the shift
divided by the metric scale. The pressure formulation covers the empty alphabet as well, which
the presentation-dependent upper entropy does not. Blueprint node `pressure:symbolic-set`. -/
theorem symbolic_setDimensions_eq_entropies_upper {α : Type*} [Countable α]
    [MetricSpace (ℕ → α)] (β : ℝ) (hβ : 0 < β) (hβ₁ : β < 1)
    (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y)
    (Z : Set (ℕ → α)) :
    metricPackingDimension Z =
      (upperPressure (fun y j => y (j + 1)) (fun _ => 0) 0 Z).toENNReal /
        ENNReal.ofReal (-Real.logb 2 β) := by
  by_cases hZ : Z = ∅
  · rw [hZ, upperPressure_empty, metricPackingDimension_empty, EReal.toENNReal_bot,
      ENNReal.zero_div]
  · have hZ_nonempty := Set.nonempty_iff_ne_empty.mpr hZ
    let : Nonempty α := ⟨hZ_nonempty.some 0⟩
    obtain ⟨P⟩ := nonempty_presentation_of_dist_eq_pow_firstDiff hβ hβ₁ hd
    have hp := congrArg EReal.toENNReal
      (entropy_eq_zeroPotentialPressure_of_nonempty_upper P _
        (continuous_shift_of_dist_eq_pow_firstDiff hβ hβ₁ hd) Z hZ_nonempty)
    simp only [EReal.toENNReal_coe] at hp
    rw [symbolic_setDimensions_eq_entropies_upper_entropy β hβ hβ₁ hd P Z, hp]

end Kolmogorov.PointToSet
