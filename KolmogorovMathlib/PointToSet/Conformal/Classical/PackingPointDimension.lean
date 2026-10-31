/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.Conformal.Classical.PackingModifiedBox

/-!
# Packing dimension is bounded by point dimensions

This module relates the order-one, zero-potential partition sum of the pressure formalism
to classical covering numbers, and uses the resulting box-dimension interface to prove the
easy half of the point-to-set principle for packing dimension.

* `packingEqModifiedUpperBox_open_covering` identifies the partition sum at radius `r` with
  the extended cardinality of a smallest set of centers whose open `r`-balls cover the set.
* `packingEqModifiedUpperBox_coveringNumber` (blueprint node `conf:packing-box-interface`)
  shows that upper box dimension is the `limsup` of the logarithmic rates of Mathlib's
  closed-ball external covering numbers at the dyadic radii `2⁻ⁿ`; the two kinds of covering
  numbers interlace across consecutive dyadic radii, and an index shift does not change the
  `limsup`.
* `packingLeSupPointDimension` (blueprint node `conf:packing-any-oracle`) bounds the packing
  dimension of a set by the supremum of the upper point dimensions relative to any oracle.
  The sets of points whose complexity at all small dyadic scales stays below `s * r` are
  covered, at radius `2⁻ʳ`, by the balls around the at most `2 ^ ⌊s * r⌋` ideal points of
  small oracle complexity (Kraft's inequality), so each has upper box dimension at most `s`.

`packingLeSupPointDimension` is the starting point for the oracle construction in
`KolmogorovMathlib.PointToSet.Conformal.Classical.PointToSetPrinciple`, and
`packingEqModifiedUpperBox_coveringNumber` is used there to compare with covering numbers.
-/

namespace Kolmogorov.PointToSet
open Filter TopologicalSpace MeasureTheory Measure
open scoped Topology ENNReal Computability
variable {X : Type*} [MetricSpace X]

private lemma dyadicRadius_succ_lt (k : ℕ) : dyadicRadius (k + 1) < dyadicRadius k :=
  pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) k.lt_succ_self

/-- With zero potential at order one, the cost of a set of centers is its cardinality. -/
private lemma partitionCoverCost_zero_centered (F : Set X) (r : ℝ) :
    partitionCoverCost id (fun _ : X => 0) .centered F 1 r = F.encard := by
  simp [partitionCoverCost, pressureBallWeight]

/-- The existing zero-potential order-one partition sum is the open-ball covering number.
Its value is the extended cardinal infimum, so infinite covering numbers are retained.
Blueprint node `conf:packing-box-interface`. -/
theorem packingEqModifiedUpperBox_open_covering (Z : Set X) (r : ℝ) :
    partitionSum id (fun _ : X => 0) .centered Z 1 r =
      ⨅ F : Set X, ⨅ (_ : Z ⊆ ⋃ x ∈ F, Metric.ball x r), (F.encard : ℝ≥0∞) := by
  simp only [partitionSum, partitionCoverCost_zero_centered, bowenBall_id_one]
  refine iInf_congr fun F ↦ le_antisymm (le_iInf fun hcover ↦ ?_) (le_iInf fun hcover ↦ ?_)
  · by_cases hF : F.Countable
    · exact iInf_le_of_le ⟨hF, hcover⟩ le_rfl
    · rw [Set.encard_eq_top_iff.mpr fun hfin ↦ hF hfin.countable]
      exact le_top
  · exact iInf_le_of_le hcover.2 le_rfl

/-- The closed-ball external covering number at radius `r` is at most the open-ball covering
number at the same radius. -/
private lemma externalCoveringNumber_le_partitionSum (Z : Set X) {r : ℝ} (hr : 0 < r) :
    (Metric.externalCoveringNumber r.toNNReal Z : ℝ≥0∞) ≤
      partitionSum id (fun _ : X => 0) .centered Z 1 r := by
  rw [packingEqModifiedUpperBox_open_covering Z r]
  refine le_iInf fun F ↦ le_iInf fun hF ↦ ?_
  have hcover : Metric.IsCover r.toNNReal Z F := fun z hz ↦ by
    obtain ⟨x, hx, hzx⟩ := Set.mem_iUnion₂.mp (hF hz)
    exact ⟨x, hx, (edist_le_ofReal hr.le).2 (Metric.mem_ball.mp hzx).le⟩
  exact ENat.toENNReal_le.mpr hcover.externalCoveringNumber_le_encard

/-- The open-ball covering number at radius `r` is at most the closed-ball external covering
number at any smaller positive radius `s`. -/
private lemma partitionSum_le_externalCoveringNumber (Z : Set X) {r s : ℝ} (hs : 0 < s)
    (hsr : s < r) :
    partitionSum id (fun _ : X => 0) .centered Z 1 r ≤
      (Metric.externalCoveringNumber s.toNNReal Z : ℝ≥0∞) := by
  have : Nonempty {C : Set X // Metric.IsCover s.toNNReal Z C} :=
    ⟨⟨Set.univ, fun z _ ↦ ⟨z, Set.mem_univ z, by simp⟩⟩⟩
  obtain ⟨⟨C, hC⟩, hCmin⟩ := ENat.exists_eq_iInf
    (fun C : {C : Set X // Metric.IsCover s.toNNReal Z C} ↦ C.1.encard)
  have hcard : Metric.externalCoveringNumber s.toNNReal Z = C.encard := by
    rw [Metric.externalCoveringNumber, iInf_subtype']
    exact hCmin.symm
  have hsub : Z ⊆ ⋃ x ∈ C, Metric.ball x r := fun z hz ↦ by
    obtain ⟨x, hx, hzx⟩ := hC hz
    exact Set.mem_iUnion₂.mpr ⟨x, hx, Metric.mem_ball.mpr
      (lt_of_le_of_lt ((edist_le_ofReal hs.le).1 hzx) hsr)⟩
  rw [hcard, packingEqModifiedUpperBox_open_covering Z r]
  exact iInf_le_of_le C (iInf_le_of_le hsub le_rfl)

/-- Away from order zero, the nonnegative projection of `pressureRate` is the product of the
projected logarithm, the constant `1 / log 2` and the inverse order. -/
private lemma toENNReal_pressureRate_eq (q : ℕ → ℝ≥0∞) {n : ℕ} (hn : n ≠ 0) :
    (pressureRate q n).toENNReal = (ENNReal.log (q n)).toENNReal *
      ENNReal.ofReal (Real.log 2)⁻¹ * (n : ℝ≥0∞)⁻¹ := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  rw [pressureRate, ite_eq_right hn, pressureLog,
    EReal.toENNReal_mul' (EReal.coe_nonneg.mpr (inv_nonneg.mpr hn'.le)),
    EReal.toENNReal_mul'
      (EReal.coe_nonneg.mpr (inv_nonneg.mpr (Real.log_nonneg (by norm_num))))]
  simp [ENNReal.ofReal_inv_of_pos hn']

/-- The projected rate is monotone in the covering numbers at every positive order. -/
private lemma toENNReal_pressureRate_mono {q r : ℕ → ℝ≥0∞} {n : ℕ} (hn : n ≠ 0)
    (h : q n ≤ r n) : (pressureRate q n).toENNReal ≤ (pressureRate r n).toENNReal := by
  rw [toENNReal_pressureRate_eq q hn, toENNReal_pressureRate_eq r hn]
  exact mul_le_mul_left (mul_le_mul_left (EReal.toENNReal_le_toENNReal
    (ENNReal.log_le_log h)) _) _

/-- If `r n ≤ q (n + 1)`, the projected rate of `r` at order `n` is at most the projected
rate of `q` at order `n + 1`, times the factor `1 + 1 / n` that changes the order. -/
private lemma toENNReal_pressureRate_le_succ {q r : ℕ → ℝ≥0∞} {n : ℕ} (hn : n ≠ 0)
    (h : r n ≤ q (n + 1)) :
    (pressureRate r n).toENNReal ≤
      (pressureRate q (n + 1)).toENNReal * (1 + (n : ℝ≥0∞)⁻¹) := by
  rw [toENNReal_pressureRate_eq r hn, toENNReal_pressureRate_eq q n.succ_ne_zero]
  have hn0 : (n : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hsucc : ((n + 1 : ℕ) : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr n.succ_ne_zero
  have hfactor : (1 : ℝ≥0∞) + (n : ℝ≥0∞)⁻¹ = ((n + 1 : ℕ) : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹ := by
    rw [Nat.cast_succ, add_mul, ENNReal.mul_inv_cancel hn0 (ENNReal.natCast_ne_top n), one_mul]
  have hinv : (n : ℝ≥0∞)⁻¹ = ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ * (1 + (n : ℝ≥0∞)⁻¹) := by
    rw [hfactor, ← mul_assoc, ENNReal.inv_mul_cancel hsucc (ENNReal.natCast_ne_top _), one_mul]
  calc (ENNReal.log (r n)).toENNReal * ENNReal.ofReal (Real.log 2)⁻¹ * (n : ℝ≥0∞)⁻¹
      ≤ (ENNReal.log (q (n + 1))).toENNReal * ENNReal.ofReal (Real.log 2)⁻¹ *
          (n : ℝ≥0∞)⁻¹ :=
        mul_le_mul_left (mul_le_mul_left (EReal.toENNReal_le_toENNReal
          (ENNReal.log_le_log h)) _) _
    _ = (ENNReal.log (q (n + 1))).toENNReal * ENNReal.ofReal (Real.log 2)⁻¹ *
          ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ * (1 + (n : ℝ≥0∞)⁻¹) := by
        rw [mul_assoc _ _ (1 + (n : ℝ≥0∞)⁻¹), ← hinv]

/-- A sequence squeezed between a sequence and its shift, up to a factor `1 + 1 / n`, has
the same `limsup`. -/
private lemma limsup_eq_of_le_le_mul_succ {a b : ℕ → ℝ≥0∞} (hab : ∀ᶠ n in atTop, a n ≤ b n)
    (hba : ∀ᶠ n in atTop, b n ≤ a (n + 1) * (1 + (n : ℝ≥0∞)⁻¹)) :
    limsup a atTop = limsup b atTop := by
  refine le_antisymm (limsup_le_limsup hab) ?_
  have hlim : Tendsto (fun n : ℕ ↦ 1 + (n : ℝ≥0∞)⁻¹) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add (ENNReal.tendsto_inv_nat_nhds_zero)
  calc limsup b atTop
      ≤ limsup (fun n ↦ a (n + 1) * (1 + (n : ℝ≥0∞)⁻¹)) atTop := limsup_le_limsup hba
    _ ≤ limsup (fun n ↦ a (n + 1)) atTop * limsup (fun n : ℕ ↦ 1 + (n : ℝ≥0∞)⁻¹) atTop :=
        ENNReal.limsup_mul_le' (Or.inr (by rw [hlim.limsup_eq]; exact ENNReal.one_ne_top))
          (Or.inr (by rw [hlim.limsup_eq]; exact one_ne_zero))
    _ = limsup a atTop := by
        rw [hlim.limsup_eq, mul_one]
        exact (limsup_comp a (· + 1) atTop).trans (by rw [map_add_atTop_eq_nat])

/-- Covering numbers interlaced across consecutive scales, `q n ≤ r n ≤ q (n + 1)`, give the
same `limsup` of projected logarithmic rates. -/
private lemma limsup_toENNReal_pressureRate_eq {q r : ℕ → ℝ≥0∞} (hqr : ∀ n, q n ≤ r n)
    (hrq : ∀ n, r n ≤ q (n + 1)) :
    limsup (fun n ↦ (pressureRate q n).toENNReal) atTop =
      limsup (fun n ↦ (pressureRate r n).toENNReal) atTop :=
  limsup_eq_of_le_le_mul_succ
    ((eventually_ne_atTop 0).mono fun n hn ↦ toENNReal_pressureRate_mono hn (hqr n))
    ((eventually_ne_atTop 0).mono fun n hn ↦ toENNReal_pressureRate_le_succ hn (hrq n))

/-- Closed-ball covering numbers from Mathlib give the same upper box dimension.
This comparison only changes radii by a fixed factor before taking the limit.
Blueprint node `conf:packing-box-interface`. -/
theorem packingEqModifiedUpperBox_coveringNumber (Z : Set X) :
    upperBoxDimension Z = limsup (fun n => (pressureRate
      (fun k => (Metric.externalCoveringNumber (Real.toNNReal (dyadicRadius k)) Z : ℝ≥0∞))
      n).toENNReal) atTop :=
  (limsup_toENNReal_pressureRate_eq
    (fun k ↦ externalCoveringNumber_le_partitionSum Z (dyadicRadius_pos k))
    (fun k ↦ partitionSum_le_externalCoveringNumber Z (dyadicRadius_pos (k + 1))
      (dyadicRadius_succ_lt k))).symm

/-- To bound the packing dimension by `S` it suffices to bound it by `ofReal s` for every
nonnegative real `s` with `S < ofReal s`. -/
private lemma metricPackingDimension_le_of_forall_ofReal (Z : Set X) (S : ℝ≥0∞)
    (H : ∀ s : ℝ, 0 ≤ s → S < ENNReal.ofReal s → metricPackingDimension Z ≤ ENNReal.ofReal s) :
    metricPackingDimension Z ≤ S := by
  refine le_of_forall_gt_imp_ge_of_dense fun c hc ↦ ?_
  rcases eq_or_ne c ⊤ with rfl | hct
  · exact le_top
  · rw [← ENNReal.ofReal_toReal hct] at hc ⊢
    exact H _ ENNReal.toReal_nonneg hc

/-- The upper point dimension is the `limsup` of the normalized precision complexities at
the dyadic radii `2⁻ᵐ`. -/
private lemma staticPointDimensions_snd_eq_limsup_dyadic (P : Presentation X) (A : Set ℕ)
    (x : X) :
    (staticPointDimensions P A x).2 =
      limsup (fun m => normalizedPrecisionComplexity P A x (dyadicRadius m)) atTop :=
  dimension_along_scales_upper P A x dyadicRadius dyadicRadius_pos
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
    (Real.tendsto_log_pow_succ_div_log_pow (β := (2 : ℝ)⁻¹) (by norm_num) (by norm_num))

/-- The points of `Z` whose normalized precision complexity is at most `s` at every dyadic
scale `2⁻ʳ` with `r ≥ N`. -/
private def lowComplexityPiece (P : Presentation X) (A : Set ℕ) (Z : Set X) (s : ℝ) (N : ℕ) :
    Set X :=
  {x ∈ Z | ∀ r ≥ N, normalizedPrecisionComplexity P A x (dyadicRadius r) ≤ ENNReal.ofReal s}

/-- If `s` exceeds all upper point dimensions of points of `Z`, the pieces
`lowComplexityPiece P A Z s N` cover `Z`. -/
private lemma subset_iUnion_lowComplexityPiece (P : Presentation X) (A : Set ℕ) (Z : Set X)
    {s : ℝ} (hs : ⨆ x ∈ Z, (staticPointDimensions P A x).2 < ENNReal.ofReal s) :
    Z ⊆ ⋃ N, lowComplexityPiece P A Z s N := by
  intro x hx
  have hlt : (staticPointDimensions P A x).2 < ENNReal.ofReal s :=
    lt_of_le_of_lt (le_iSup₂ (f := fun y _ ↦ (staticPointDimensions P A y).2) x hx) hs
  rw [staticPointDimensions_snd_eq_limsup_dyadic] at hlt
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_lt_of_limsup_lt hlt)
  exact Set.mem_iUnion.mpr ⟨N, hx, fun r hr ↦ (hN r hr).le⟩

/-- `ENNReal.ofReal` only sees the positive part of a real number. -/
private lemma ofReal_max_zero (s : ℝ) : ENNReal.ofReal (max s 0) = ENNReal.ofReal s := by
  rcases le_total s 0 with h | h
  · rw [max_eq_right h, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h]
  · rw [max_eq_left h]

/-- Kraft's inequality bounds a finite set of indices of oracle complexity at most `b` by
`2 ^ b`. -/
private lemma card_le_two_pow_of_oracleNatComplexity_le (A : Set ℕ) (b : ℕ) (S : Finset ℕ)
    (hS : ∀ i ∈ S, oracleNatComplexity A i ≤ b) : (S.card : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ b := by
  have hsum : ∑ i ∈ S, ((2 : ℝ≥0∞)⁻¹) ^ oracleNatComplexity A i ≤ 1 :=
    (ENNReal.sum_le_tsum S).trans (oracle_kraft A)
  have hterm : ∑ i ∈ S, ((2 : ℝ≥0∞)⁻¹) ^ b ≤
      ∑ i ∈ S, ((2 : ℝ≥0∞)⁻¹) ^ oracleNatComplexity A i :=
    Finset.sum_le_sum fun i hi ↦ pow_le_pow_right_of_le_one' (by norm_num) (hS i hi)
  rw [Finset.sum_const, nsmul_eq_mul] at hterm
  have hcard : (S.card : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ b)⁻¹ ≤ 1 := by
    rw [ENNReal.inv_pow]
    exact hterm.trans hsum
  rw [← div_eq_mul_inv] at hcard
  simpa using (ENNReal.div_le_iff (by positivity) (by simp)).mp hcard

/-- A point of a low-complexity piece has, at every scale `2⁻ʳ` with `r ≥ max N 1`, an ideal
point within distance `2⁻ʳ` of oracle complexity at most `max s 0 * r`. -/
private lemma exists_ideal_complexity_le_of_mem_lowComplexityPiece (P : Presentation X)
    (A : Set ℕ) (Z : Set X) (s : ℝ) (N r : ℕ) (hr : max N 1 ≤ r) (x : X)
    (hx : x ∈ lowComplexityPiece P A Z s N) :
    ∃ i, dist (P.ι i) x < dyadicRadius r ∧ (oracleNatComplexity A i : ℝ) ≤ max s 0 * r := by
  obtain ⟨_, hxN⟩ := hx
  have hrN : N ≤ r := (le_max_left _ _).trans hr
  have hr1 : 1 ≤ r := (le_max_right _ _).trans hr
  obtain ⟨i, hi, hcomp⟩ := staticPointDimensions_attained P A x (dyadicRadius r)
    (dyadicRadius_pos r)
  refine ⟨i, hi, ?_⟩
  have hnorm := hxN r hrN
  unfold normalizedPrecisionComplexity precisionComplexityNat at hnorm
  rw [hcomp, ENat.toNat_natCast, neg_logb_dyadicRadius, ENNReal.ofReal_natCast] at hnorm
  have hr0 : (r : ℝ≥0∞) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hr1
  have hle := (ENNReal.div_le_iff hr0 (ENNReal.natCast_ne_top r)).mp hnorm
  have hmul : ENNReal.ofReal s * (r : ℝ≥0∞) = ENNReal.ofReal (max s 0 * r) := by
    rw [ENNReal.ofReal_mul (le_max_right _ _), ofReal_max_zero, ENNReal.ofReal_natCast]
  rw [hmul, ← ENNReal.ofReal_natCast, ENNReal.ofReal_le_ofReal_iff (by positivity)] at hle
  exact hle

/-- A cover by open balls of radius `r > 0` with centers in `F` bounds the order-one partition
sum by the extended cardinality of `F`. -/
private lemma partitionSum_le_encard_of_cover (Z F : Set X) {r : ℝ}
    (hcover : Z ⊆ ⋃ x ∈ F, Metric.ball x r) :
    partitionSum id (fun _ : X => 0) .centered Z 1 r ≤ (F.encard : ℝ≥0∞) := by
  rw [packingEqModifiedUpperBox_open_covering Z r]
  exact iInf_le_of_le F (iInf_le_of_le hcover le_rfl)

/-- For `r ≥ max N 1`, the balls of radius `2⁻ʳ` around the finitely many ideal points of
oracle complexity at most `⌊max s 0 * r⌋₊` cover the piece `lowComplexityPiece P A Z s N`, so
its radius-`2⁻ʳ` partition sum is at most `2 ^ ⌊max s 0 * r⌋₊`. -/
private lemma partitionSum_lowComplexityPiece_le (P : Presentation X) (A : Set ℕ) (Z : Set X)
    (s : ℝ) (N r : ℕ) (hr : max N 1 ≤ r) :
    partitionSum id (fun _ : X => 0) .centered (lowComplexityPiece P A Z s N) 1
      (dyadicRadius r) ≤ (2 : ℝ≥0∞) ^ ⌊max s 0 * r⌋₊ := by
  obtain ⟨I, hI⟩ : ∃ I : Finset ℕ,
      ∀ i, i ∈ I ↔ oracleNatComplexity A i ≤ ⌊max s 0 * (r : ℝ)⌋₊ :=
    ⟨(oracle_kraft_finite_sublevels A ⌊max s 0 * (r : ℝ)⌋₊).toFinset, fun i ↦ by simp⟩
  have hcover : lowComplexityPiece P A Z s N ⊆
      ⋃ y ∈ P.ι '' (I : Set ℕ), Metric.ball y (dyadicRadius r) := by
    intro x hx
    obtain ⟨i, hi, hK⟩ := exists_ideal_complexity_le_of_mem_lowComplexityPiece P A Z s N r hr x hx
    refine Set.mem_iUnion₂.mpr ⟨P.ι i, ⟨i, (hI i).mpr (Nat.le_floor hK), rfl⟩, ?_⟩
    rw [Metric.mem_ball, dist_comm]
    exact hi
  calc partitionSum id (fun _ : X => 0) .centered (lowComplexityPiece P A Z s N) 1
        (dyadicRadius r)
      ≤ ((P.ι '' (I : Set ℕ)).encard : ℝ≥0∞) :=
        partitionSum_le_encard_of_cover _ _ hcover
    _ ≤ (I.card : ℝ≥0∞) := by
        have : (P.ι '' (I : Set ℕ)).encard ≤ (I.card : ℕ∞) :=
          (Set.encard_image_le _ _).trans (Set.encard_coe_eq_coe_finsetCard I).le
        exact_mod_cast ENat.toENNReal_le.mpr this
    _ ≤ (2 : ℝ≥0∞) ^ ⌊max s 0 * (r : ℝ)⌋₊ :=
        card_le_two_pow_of_oracleNatComplexity_le A _ I fun i hi ↦ (hI i).mp hi

/-- If `q n ≤ 2 ^ k` and `k ≤ max s 0 * n`, the projected logarithmic rate of `q` at the
positive order `n` is at most `ENNReal.ofReal s`. -/
private lemma toENNReal_pressureRate_le_ofReal (s : ℝ) (q : ℕ → ℝ≥0∞) (k n : ℕ) (hn : 0 < n)
    (hq : q n ≤ (2 : ℝ≥0∞) ^ k) (hk : (k : ℝ) ≤ max s 0 * n) :
    (pressureRate q n).toENNReal ≤ ENNReal.ofReal s := by
  have hn0 : n ≠ 0 := hn.ne'
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h2 : ENNReal.log (2 : ℝ≥0∞) = ((Real.log 2 : ℝ) : EReal) := by
    simpa using ENNReal.log_ofReal_of_pos (x := 2) (by norm_num)
  have hlog : ENNReal.log (q n) ≤ (((k : ℝ) * Real.log 2 : ℝ) : EReal) := by
    calc ENNReal.log (q n) ≤ ENNReal.log ((2 : ℝ≥0∞) ^ k) := ENNReal.log_monotone hq
      _ = (((k : ℝ) * Real.log 2 : ℝ) : EReal) := by
        rw [ENNReal.log_pow, h2]
        norm_cast
  have hrate : pressureRate q n ≤ (((k : ℝ) * (n : ℝ)⁻¹ : ℝ) : EReal) := by
    have hnn : (0 : EReal) ≤ (((Real.log 2)⁻¹ * (n : ℝ)⁻¹ : ℝ) : EReal) :=
      EReal.coe_nonneg.mpr (by positivity)
    have := mul_le_mul_of_nonneg_right hlog hnn
    simp only [pressureRate, ite_eq_right hn0, pressureLog, mul_assoc, ← EReal.coe_mul]
    refine this.trans (le_of_eq ?_)
    rw [← EReal.coe_mul]
    congr 1
    field_simp
  refine (EReal.toENNReal_le_toENNReal hrate).trans ?_
  have hkn : (k : ℝ) * (n : ℝ)⁻¹ ≤ max s 0 := by
    rw [← div_eq_mul_inv, div_le_iff₀ hnR]
    exact hk
  exact (ENNReal.ofReal_le_ofReal hkn).trans (ofReal_max_zero s).le

/-- Each low-complexity piece has upper box dimension at most `s`. -/
private lemma upperBoxDimension_lowComplexityPiece_le (P : Presentation X) (A : Set ℕ)
    (Z : Set X) (s : ℝ) (N : ℕ) :
    upperBoxDimension (lowComplexityPiece P A Z s N) ≤ ENNReal.ofReal s := by
  refine limsup_le_of_le (by isBoundedDefault) (eventually_atTop.mpr ⟨max N 1, fun n hn ↦ ?_⟩)
  exact toENNReal_pressureRate_le_ofReal s _ ⌊max s 0 * (n : ℝ)⌋₊ n
    ((le_max_right N 1).trans hn)
    (partitionSum_lowComplexityPiece_le P A Z s N n hn)
    (Nat.floor_le (mul_nonneg (le_max_right _ _) (Nat.cast_nonneg n)))

/-- Every oracle bounds packing dimension by the supremum of its upper point dimensions.
Blueprint node `conf:packing-any-oracle`. -/
theorem packingLeSupPointDimension (P : Presentation X) (Z : Set X) (A : Set ℕ) :
    metricPackingDimension Z ≤ ⨆ x ∈ Z, (staticPointDimensions P A x).2 := by
  refine metricPackingDimension_le_of_forall_ofReal _ _ fun s _ hs ↦ ?_
  have : SeparableSpace X := ⟨⟨Set.range P.ι, Set.countable_range P.ι, P.dense⟩⟩
  rw [packingEqModifiedUpperBox Z, modifiedUpperBoxDimension]
  exact iInf_le_of_le (lowComplexityPiece P A Z s) (iInf_le_of_le
    (subset_iUnion_lowComplexityPiece P A Z hs)
    (iSup_le fun N ↦ upperBoxDimension_lowComplexityPiece_le P A Z s N))

end Kolmogorov.PointToSet
