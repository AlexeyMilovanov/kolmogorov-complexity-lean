/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.Examples.MiddleThirds

/-!
# The packing dimension of the middle-thirds Cantor set

This file proves the classical half of the middle-thirds Cantor example (blueprint node
`example:cantor`): the specified-radius packing dimension of the ternary Cantor set
`cantorSet` equals `log 2 / log 3`, the value that `middleThirds_dimensions` establishes for
its Hausdorff dimension.

The argument runs through the upper box dimension.  On the one hand, the Cantor set is covered
by `2 ^ m` balls of radius `2 · 3⁻ᵐ`, which bounds the dyadic partition sums and gives
`upperBoxDimension cantorSet ≤ log 2 / log 3`; since the modified upper box dimension is an
infimum of countable-union box dimensions, so is the packing dimension.  On the other hand,
Hausdorff dimension is at most upper box dimension for any subset of a metric space (finite
covers by `2 ^ (t n)` dyadic balls force vanishing Hausdorff measure above `t`), so the packing
dimension is at least `dimH cantorSet = log 2 / log 3`.

The result `middleThirds_dimensions_upper` is the last statement of the Cantor example; it
is re-exported through `KolmogorovMathlib.PointToSet.Examples`.
-/

namespace Kolmogorov.PointToSet
open Filter
open scoped Topology ENNReal NNReal
open Kolmogorov

/-- The order-one, zero-potential partition sum at the dyadic radius `2⁻ᵏ`: the quantity whose
logarithmic growth rate defines `upperBoxDimension`. -/
private noncomputable abbrev dyadicPartitionSum {X : Type*} [MetricSpace X] (Z : Set X)
    (k : ℕ) : ℝ≥0∞ :=
  partitionSum id (fun _ : X ↦ 0) .centered Z 1 (dyadicRadius k)

/-- The dyadic radius `2⁻ⁿ`, viewed in `ℝ≥0∞`, is the `n`-th power of `2⁻¹`. -/
private lemma ofReal_dyadicRadius (n : ℕ) : ENNReal.ofReal (dyadicRadius n) = 2⁻¹ ^ n := by
  rw [dyadicRadius, ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_inv_of_pos two_pos,
    ENNReal.ofReal_ofNat]

/-- If the upper box dimension of `Z` is below `t`, the dyadic growth rate of the partition sums
is eventually bounded by some `b` with `0 < b < t`. -/
private lemma exists_pos_lt_eventually_pressureRate_le {X : Type*} [MetricSpace X] (Z : Set X)
    {t : ℝ} (h : upperBoxDimension Z < ENNReal.ofReal t) :
    ∃ b : ℝ, 0 < b ∧ b < t ∧
      ∀ᶠ n : ℕ in atTop, pressureRate (dyadicPartitionSum Z) n ≤ (b : EReal) := by
  have ht : 0 < t := by
    by_contra h0
    rw [ENNReal.ofReal_of_nonpos (not_lt.mp h0)] at h
    exact not_lt_bot h
  obtain ⟨b', hb', hbt'⟩ := exists_between h
  have hb'top : b' ≠ ⊤ := (hbt'.trans ENNReal.ofReal_lt_top).ne
  refine ⟨b'.toReal, ENNReal.toReal_pos (zero_le.trans_lt hb').ne' hb'top, ?_, ?_⟩
  · rw [← ENNReal.ofReal_lt_ofReal_iff ht, ENNReal.ofReal_toReal hb'top]
    exact hbt'
  · filter_upwards [Filter.eventually_lt_of_limsup_lt hb'] with n hn
    generalize pressureRate (dyadicPartitionSum Z) n = x at hn
    induction x using EReal.rec with
    | bot => exact bot_le
    | top => simp at hn
    | coe r =>
      rw [EReal.real_coe_toENNReal] at hn
      exact EReal.coe_le_coe_iff.mpr ((ENNReal.ofReal_le_iff_le_toReal hb'top).mp hn.le)

/-- A growth rate of at most `b < t` forces the terms of a sequence `q` to be eventually below
`2 ^ (t n)`. -/
private lemma eventually_lt_rpow_of_pressureRate_le (q : ℕ → ℝ≥0∞) {b t : ℝ} (hbt : b < t)
    (h : ∀ᶠ n : ℕ in atTop, pressureRate q n ≤ (b : EReal)) :
    ∀ᶠ n : ℕ in atTop, q n < (2 : ℝ≥0∞) ^ (t * n) := by
  filter_upwards [h, eventually_ge_atTop 1] with n hn hn1
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hc : 0 < (n : ℝ) * Real.log 2 := by positivity
  have hq : ENNReal.log (q n) * (((Real.log 2)⁻¹ * (n : ℝ)⁻¹ : ℝ) : EReal) ≤ b := by
    simpa only [pressureRate, ite_eq_right (by omega : n ≠ 0), pressureLog, mul_assoc,
      ← EReal.coe_mul] using hn
  rw [← ENNReal.log_lt_log_iff, ENNReal.log_rpow, show ENNReal.log 2 = Real.log 2 by
    simpa using ENNReal.log_ofReal_of_pos (x := 2) two_pos]
  calc ENNReal.log (q n)
      = (ENNReal.log (q n) * (((Real.log 2)⁻¹ * (n : ℝ)⁻¹ : ℝ) : EReal)) *
          ((n * Real.log 2 : ℝ) : EReal) := by
        rw [mul_assoc, ← EReal.coe_mul,
          show (Real.log 2)⁻¹ * (n : ℝ)⁻¹ * (n * Real.log 2) = 1 by field_simp,
          EReal.coe_one, mul_one]
    _ ≤ (b : EReal) * ((n * Real.log 2 : ℝ) : EReal) :=
        mul_le_mul_of_nonneg_right hq (EReal.coe_nonneg.mpr hc.le)
    _ < (t * n : ℝ) * (Real.log 2 : EReal) := by
        rw [← EReal.coe_mul, ← EReal.coe_mul, EReal.coe_lt_coe_iff]
        nlinarith

/-- A dyadic partition sum below `c` is witnessed by a finite cover of `Z` by open balls of
radius `2⁻ⁿ` with fewer than `c` centers. -/
private lemma exists_finset_cover_of_dyadicPartitionSum_lt {X : Type*} [MetricSpace X]
    {Z : Set X} {c : ℝ≥0∞} {n : ℕ} (h : dyadicPartitionSum Z n < c) :
    ∃ F : Finset X, Z ⊆ ⋃ x ∈ F, Metric.ball x (dyadicRadius n) ∧ (F.card : ℝ≥0∞) < c := by
  unfold dyadicPartitionSum at h
  rw [packingEqModifiedUpperBox_open_covering Z _ (dyadicRadius_pos n)] at h
  obtain ⟨F, hF⟩ := iInf_lt_iff.mp h
  obtain ⟨hcov, hlt⟩ := iInf_lt_iff.mp hF
  have hfin : F.Finite := by
    by_contra hinf
    simp [Set.Infinite.encard_eq hinf] at hlt
  refine ⟨hfin.toFinset, by simpa using hcov, ?_⟩
  simpa [hfin.encard_eq_coe_toFinset_card] using hlt

/-- Below every real `t` exceeding the upper box dimension of `Z`, all sufficiently fine dyadic
scales admit a cover of `Z` by at most `2 ^ (t n)` balls of radius `2⁻ⁿ`. -/
private lemma eventually_exists_finset_cover_of_upperBoxDimension_lt {X : Type*} [MetricSpace X]
    (Z : Set X) {t : ℝ} (h : upperBoxDimension Z < ENNReal.ofReal t) :
    ∀ᶠ n : ℕ in atTop, ∃ F : Finset X,
      Z ⊆ ⋃ x ∈ F, Metric.ball x (dyadicRadius n) ∧ (F.card : ℝ≥0∞) ≤ 2 ^ (t * n) := by
  obtain ⟨b, -, hbt, hrate⟩ := exists_pos_lt_eventually_pressureRate_le Z h
  filter_upwards [eventually_lt_rpow_of_pressureRate_le _ hbt hrate] with n hn
  obtain ⟨F, hF, hcard⟩ := exists_finset_cover_of_dyadicPartitionSum_lt hn
  exact ⟨F, hF, hcard.le⟩

/-- The cover sizes `2 ^ (t n)` against the diameters `2 · 2⁻ⁿ` raised to a power `s > t`
tend to zero. -/
private lemma tendsto_rpow_mul_diam_rpow {t : ℝ} {s : ℝ≥0} (hts : t < s) :
    Tendsto (fun n : ℕ ↦ (2 : ℝ≥0∞) ^ (t * n) * (2 * 2⁻¹ ^ n) ^ (s : ℝ)) atTop (𝓝 0) := by
  have hbase : (2 : ℝ≥0∞) ^ t * (2⁻¹) ^ (s : ℝ) < 1 := by
    rw [ENNReal.inv_rpow, ← div_eq_mul_inv,
      ENNReal.div_lt_iff (Or.inl (by positivity)) (Or.inl (by simp)), one_mul]
    exact ENNReal.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num) hts
  have h := ENNReal.Tendsto.const_mul (a := (2 : ℝ≥0∞) ^ (s : ℝ))
    (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hbase)
    (Or.inr (ENNReal.rpow_ne_top_of_nonneg s.2 ENNReal.ofNat_ne_top))
  rw [mul_zero] at h
  refine h.congr fun n ↦ ?_
  rw [ENNReal.mul_rpow_of_nonneg _ _ s.coe_nonneg, mul_pow, ← ENNReal.rpow_natCast,
    ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, ← ENNReal.rpow_natCast
      (2⁻¹ : ℝ≥0∞) n, ← ENNReal.rpow_mul, mul_comm (n : ℝ) s]
  ring

/-- If for all large `n` the set `Z` is covered by at most `2 ^ (t n)` balls of radius `2⁻ⁿ`,
then `Z` has vanishing `s`-dimensional Hausdorff measure for every `s > t`. -/
private lemma hausdorffMeasure_eq_zero_of_eventually_finset_cover {X : Type*} [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X] (Z : Set X) {t : ℝ} {s : ℝ≥0} (hts : t < s)
    (h : ∀ᶠ n : ℕ in atTop, ∃ F : Finset X,
      Z ⊆ ⋃ x ∈ F, Metric.ball x (dyadicRadius n) ∧ (F.card : ℝ≥0∞) ≤ 2 ^ (t * n)) :
    MeasureTheory.Measure.hausdorffMeasure s Z = 0 := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  choose! G hGcover hGcard using hN
  have hr : Tendsto (fun n : ℕ ↦ (2 : ℝ≥0∞) * 2⁻¹ ^ n) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul
      (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by simp : (2 : ℝ≥0∞)⁻¹ < 1))
      (Or.inr ENNReal.ofNat_ne_top)
  have hdiam : ∀ n (i : G n),
      Metric.ediam (Metric.ball (i : X) (dyadicRadius n)) ≤ 2 * 2⁻¹ ^ n := by
    intro n i
    rw [← Metric.eball_ofReal, ofReal_dyadicRadius]
    exact Metric.ediam_eball_le
  refine le_antisymm ?_ bot_le
  calc MeasureTheory.Measure.hausdorffMeasure s Z
      ≤ liminf (fun n : ℕ ↦ ∑ i : G n,
          Metric.ediam (Metric.ball (i : X) (dyadicRadius n)) ^ (s : ℝ)) atTop :=
        MeasureTheory.Measure.hausdorffMeasure_le_liminf_sum (s : ℝ) Z _ hr
          (fun n (i : G n) ↦ Metric.ball (i : X) (dyadicRadius n))
          (Eventually.of_forall hdiam) (by
            filter_upwards [eventually_ge_atTop N] with n hn z hz
            obtain ⟨x, hx, hzx⟩ := Set.mem_iUnion₂.mp (hGcover n hn hz)
            exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hzx⟩)
    _ ≤ liminf (fun n : ℕ ↦ (2 : ℝ≥0∞) ^ (t * n) * (2 * 2⁻¹ ^ n) ^ (s : ℝ)) atTop := by
        refine Filter.liminf_le_liminf ?_ (by isBoundedDefault) (by isBoundedDefault)
        filter_upwards [eventually_ge_atTop N] with n hn
        calc ∑ i : G n, Metric.ediam (Metric.ball (i : X) (dyadicRadius n)) ^ (s : ℝ)
            ≤ ∑ _i : G n, (2 * 2⁻¹ ^ n) ^ (s : ℝ) :=
              Finset.sum_le_sum fun i _ ↦ ENNReal.rpow_le_rpow (hdiam n i) s.coe_nonneg
          _ = (G n).card * (2 * 2⁻¹ ^ n) ^ (s : ℝ) := by simp
          _ ≤ _ := by gcongr; exact hGcard n hn
    _ = 0 := (tendsto_rpow_mul_diam_rpow hts).liminf_eq

/-- The Hausdorff dimension of any subset of a metric space is at most its upper box
dimension. -/
private lemma dimH_le_upperBoxDimension {X : Type*} [MetricSpace X] (Z : Set X) :
    dimH Z ≤ upperBoxDimension Z := by
  borelize X
  refine dimH_le fun d hd ↦ ?_
  by_contra hlt
  obtain ⟨b, hZb, hbd⟩ := exists_between (not_le.mp hlt)
  have hbtop : b ≠ ⊤ := (hbd.trans ENNReal.coe_lt_top).ne
  have hts : b.toReal < d := by
    simpa using (ENNReal.toReal_lt_toReal hbtop ENNReal.coe_ne_top).mpr hbd
  have hZt : upperBoxDimension Z < ENNReal.ofReal b.toReal := by
    rwa [ENNReal.ofReal_toReal hbtop]
  have := hausdorffMeasure_eq_zero_of_eventually_finset_cover Z hts
    (eventually_exists_finset_cover_of_upperBoxDimension_lt Z hZt)
  simp [this] at hd

/-- Under the scaling `x ↦ (c + x) / 3`, a ball of radius `ρ` about `a` lands in the ball of
radius `ρ / 3` about the image of `a`. -/
private lemma div_three_add_mem_ball {c a y ρ : ℝ} (hy : y ∈ Metric.ball a ρ) :
    (c + y) / 3 ∈ Metric.ball ((c + a) / 3) (ρ / 3) := by
  rw [Metric.mem_ball, Real.dist_eq] at hy ⊢
  have : (c + y) / 3 - (c + a) / 3 = (y - a) / 3 := by ring
  rw [this, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
  linarith

/-- The Cantor set is covered by `2 ^ m` balls of radius `2 · 3⁻ᵐ`, one around each of the
points obtained by iterating the two ternary contractions `m` times. -/
private lemma exists_finset_cover_cantorSet (m : ℕ) :
    ∃ F : Finset ℝ, F.card ≤ 2 ^ m ∧
      cantorSet ⊆ ⋃ a ∈ F, Metric.ball a (2 * (3⁻¹ : ℝ) ^ m) := by
  induction m with
  | zero =>
    refine ⟨{1 / 2}, by simp, fun x hx ↦ ?_⟩
    obtain ⟨h0, h1⟩ := cantorSet_subset_unitInterval hx
    simp only [Finset.mem_singleton, Set.iUnion_iUnion_eq_left, Metric.mem_ball, Real.dist_eq,
      pow_zero, mul_one, abs_lt]
    constructor <;> linarith
  | succ m ih =>
    obtain ⟨Fm, hcard, hsub⟩ := ih
    have hρ : 2 * (3⁻¹ : ℝ) ^ (m + 1) = 2 * 3⁻¹ ^ m / 3 := by
      rw [pow_succ]
      ring
    refine ⟨Fm.image (fun a ↦ a / 3) ∪ Fm.image (fun a ↦ (2 + a) / 3), ?_, fun x hx ↦ ?_⟩
    · calc _ ≤ (Fm.image (fun a ↦ a / 3)).card + (Fm.image (fun a ↦ (2 + a) / 3)).card :=
            Finset.card_union_le _ _
        _ ≤ Fm.card + Fm.card := add_le_add Finset.card_image_le Finset.card_image_le
        _ ≤ 2 ^ (m + 1) := by rw [pow_succ]; omega
    · rw [cantorSet_eq_union_halves] at hx
      rcases hx with ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩
      · obtain ⟨a, ha, hya⟩ := Set.mem_iUnion₂.mp (hsub hy)
        refine Set.mem_iUnion₂.mpr
          ⟨a / 3, Finset.mem_union_left _ (Finset.mem_image_of_mem _ ha), ?_⟩
        rw [hρ]
        simpa using div_three_add_mem_ball (c := 0) hya
      · obtain ⟨a, ha, hya⟩ := Set.mem_iUnion₂.mp (hsub hy)
        refine Set.mem_iUnion₂.mpr ⟨(2 + a) / 3,
          Finset.mem_union_right _ (Finset.mem_image_of_mem _ ha), ?_⟩
        rw [hρ]
        exact div_three_add_mem_ball (c := 2) hya

/-- The ceiling `⌈(n + 1) d⌉` grows like `d n`: `⌈(n + 1) d⌉ / n → d` for `d ≥ 0`. -/
private lemma tendsto_natCeil_succ_mul_div {d : ℝ} (hd : 0 ≤ d) :
    Tendsto (fun n : ℕ ↦ (⌈((n : ℝ) + 1) * d⌉₊ : ℝ) / n) atTop (𝓝 d) := by
  have hlow : Tendsto (fun n : ℕ ↦ d + d / n) atTop (𝓝 d) := by
    simpa using tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat d)
  have hup : Tendsto (fun n : ℕ ↦ d + (d + 1) / n) atTop (𝓝 d) := by
    simpa using tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat (d + 1))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_ <;>
    filter_upwards [eventually_gt_atTop 0] with n hn <;>
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  · rw [show d + d / n = ((n : ℝ) + 1) * d / n by field_simp]
    exact div_le_div_of_nonneg_right (Nat.le_ceil _) hn'.le
  · rw [show d + (d + 1) / n = (((n : ℝ) + 1) * d + 1) / n by field_simp; ring]
    exact div_le_div_of_nonneg_right (Nat.ceil_lt_add_one (by positivity)).le hn'.le

/-- If `m ≥ (n + 1) log 2 / log 3`, then `2 · 3⁻ᵐ ≤ 2⁻ⁿ`, so a ball of radius `2 · 3⁻ᵐ` lies in
one of radius `2⁻ⁿ`. -/
private lemma two_mul_inv_three_pow_ceil_le (n : ℕ) :
    2 * (3⁻¹ : ℝ) ^ ⌈((n : ℝ) + 1) * (Real.log 2 / Real.log 3)⌉₊ ≤ dyadicRadius n := by
  generalize hm : ⌈((n : ℝ) + 1) * (Real.log 2 / Real.log 3)⌉₊ = m
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have h1 : ((n : ℝ) + 1) * Real.log 2 ≤ m * Real.log 3 := by
    have := hm ▸ Nat.le_ceil (((n : ℝ) + 1) * (Real.log 2 / Real.log 3))
    calc ((n : ℝ) + 1) * Real.log 2
        = ((n : ℝ) + 1) * (Real.log 2 / Real.log 3) * Real.log 3 := by field_simp
      _ ≤ m * Real.log 3 := mul_le_mul_of_nonneg_right this hlog3.le
  have h2 : (2 : ℝ) ^ (n + 1) ≤ 3 ^ m := by
    rw [← Real.log_le_log_iff (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    push_cast
    exact h1
  rw [dyadicRadius, inv_pow, inv_pow, ← div_eq_mul_inv, div_le_iff₀ (by positivity),
    inv_mul_eq_div, le_div_iff₀ (by positivity)]
  calc 2 * 2 ^ n = (2 : ℝ) ^ (n + 1) := by ring
    _ ≤ 3 ^ m := h2

/-- Covers of `Z` by `2 ^ m` balls of radius `2 · 3⁻ᵐ`, for all `m`, bound the dyadic partition
sums by `2 ^ ⌈(n + 1) log 2 / log 3⌉`. -/
private lemma dyadicPartitionSum_le_pow_ceil {X : Type*} [MetricSpace X] {Z : Set X}
    (hcover : ∀ m : ℕ, ∃ F : Finset X, F.card ≤ 2 ^ m ∧
      Z ⊆ ⋃ a ∈ F, Metric.ball a (2 * (3⁻¹ : ℝ) ^ m)) (n : ℕ) :
    dyadicPartitionSum Z n ≤ 2 ^ ⌈((n : ℝ) + 1) * (Real.log 2 / Real.log 3)⌉₊ := by
  obtain ⟨F, hcard, hZ⟩ := hcover ⌈((n : ℝ) + 1) * (Real.log 2 / Real.log 3)⌉₊
  unfold dyadicPartitionSum
  rw [packingEqModifiedUpperBox_open_covering Z _ (dyadicRadius_pos n)]
  have hcov : Z ⊆ ⋃ x ∈ (F : Set X), Metric.ball x (dyadicRadius n) := by
    intro z hz
    obtain ⟨a, ha, hza⟩ := Set.mem_iUnion₂.mp (hZ hz)
    exact Set.mem_iUnion₂.mpr
      ⟨a, ha, Metric.ball_subset_ball (two_mul_inv_three_pow_ceil_le n) hza⟩
  refine (iInf₂_le (F : Set X) hcov).trans ?_
  rw [Set.encard_coe_eq_coe_finsetCard]
  exact_mod_cast hcard

/-- If `Z` is covered, for every `m`, by `2 ^ m` balls of radius `2 · 3⁻ᵐ`, then its upper box
dimension is at most `log 2 / log 3`. -/
private theorem upperBoxDimension_le_of_ternary_covers {X : Type*} [MetricSpace X] (Z : Set X)
    (hcover : ∀ m : ℕ, ∃ F : Finset X, F.card ≤ 2 ^ m ∧
      Z ⊆ ⋃ a ∈ F, Metric.ball a (2 * (3⁻¹ : ℝ) ^ m)) :
    upperBoxDimension Z ≤ ENNReal.ofReal (Real.log 2 / Real.log 3) := by
  have hrate : ∀ᶠ n : ℕ in atTop, (pressureRate (dyadicPartitionSum Z) n).toENNReal ≤
      ENNReal.ofReal (⌈((n : ℝ) + 1) * (Real.log 2 / Real.log 3)⌉₊ / n) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : n ≠ 0 := by omega
    have hle : ENNReal.log (dyadicPartitionSum Z n) ≤
        ((⌈((n : ℝ) + 1) * (Real.log 2 / Real.log 3)⌉₊ * Real.log 2 : ℝ) : EReal) := by
      have := ENNReal.log_le_log (dyadicPartitionSum_le_pow_ceil hcover n)
      rw [ENNReal.log_pow, show ENNReal.log 2 = Real.log 2 by
        simpa using ENNReal.log_ofReal_of_pos (x := 2) two_pos] at this
      rwa [EReal.coe_mul, EReal.coe_natCast]
    calc (pressureRate (dyadicPartitionSum Z) n).toENNReal
        ≤ (((⌈((n : ℝ) + 1) * (Real.log 2 / Real.log 3)⌉₊ / n : ℝ)) : EReal).toENNReal := by
          refine EReal.toENNReal_le_toENNReal ?_
          rw [pressureRate, ite_eq_right hn0, pressureLog]
          calc _ ≤ ((⌈((n : ℝ) + 1) * (Real.log 2 / Real.log 3)⌉₊ * Real.log 2 : ℝ) : EReal) *
                  ((Real.log 2)⁻¹ : ℝ) * ((n : ℝ)⁻¹ : ℝ) :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right hle (EReal.coe_nonneg.mpr (by positivity)))
                  (EReal.coe_nonneg.mpr (by positivity))
            _ = _ := by
                rw [← EReal.coe_mul, ← EReal.coe_mul]
                congr 1
                field_simp
      _ = _ := EReal.real_coe_toENNReal _
  unfold upperBoxDimension
  exact (limsup_le_limsup hrate).trans_eq
    (ENNReal.tendsto_ofReal (tendsto_natCeil_succ_mul_div (by positivity))).limsup_eq

/-- Specified-radius packing dimension of the same real Cantor set has the same value.
Blueprint node `example:cantor`. -/
theorem middleThirds_dimensions_upper :
    metricPackingDimension cantorSet = ENNReal.ofReal (Real.log 2 / Real.log 3) := by
  rw [packingEqModifiedUpperBox]
  apply le_antisymm
  · unfold modifiedUpperBoxDimension
    exact iInf_le_of_le (fun _ : ℕ ↦ cantorSet)
      (iInf_le_of_le (fun _ hx ↦ Set.mem_iUnion.mpr ⟨0, hx⟩)
        (iSup_le fun _ ↦
          upperBoxDimension_le_of_ternary_covers cantorSet exists_finset_cover_cantorSet))
  · rw [← middleThirds_dimensions]
    unfold modifiedUpperBoxDimension
    refine le_iInf fun Y ↦ le_iInf fun hY ↦ ?_
    calc _root_.dimH cantorSet ≤ _root_.dimH (⋃ j, Y j) := dimH_mono hY
      _ = ⨆ j, _root_.dimH (Y j) := dimH_iUnion Y
      _ ≤ ⨆ j, upperBoxDimension (Y j) := iSup_mono fun j ↦ dimH_le_upperBoxDimension (Y j)

end Kolmogorov.PointToSet
