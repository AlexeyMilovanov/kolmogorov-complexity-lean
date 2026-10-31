/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Oracle.Joins
import KolmogorovMathlib.Oracle.KraftChaitin
import KolmogorovMathlib.PointToSet.ComputableMetric
import KolmogorovMathlib.PointToSet.Conformal.Defs
import KolmogorovMathlib.PointToSet.PackingEquivalences.Pressure
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.Topology.MetricSpace.HausdorffDimension

/-!
# Hausdorff dimension via ideal dyadic ball covers

This module proves the Hausdorff interface of the conformal dimension theorem
(blueprint node `conf:hausdorff-interface`), which relates the metric Hausdorff dimension of a
set `Z` to covers of `Z` by dyadic balls centred at the ideal points of a presentation `P`:

* `hausdorffDyadicIdealCover`: if `dimH Z < s`, then for every precision `M` and every
  `ε > 0` there is an ideal dyadic cover of `Z` by balls of radius at most `2⁻ᴹ` whose
  power-gauge cost `∑ 2^(-s r)` is below `ε`.  Each member of a small countable cover is
  enclosed in an ideal ball of comparable radius (the cost grows by at most the factor `4^s`),
  and zero-diameter members receive balls of arbitrarily small cost.
* `hausdorffDyadicIdealCover_converse`: arbitrarily fine ideal dyadic covers of arbitrarily
  small cost conclude `dimH Z ≤ s`, since a ball of radius `r` has diameter at most `2 r`.

The two statements are used by the point-to-set comparison between effective and classical
Hausdorff dimension in the modules that import this one.
-/

namespace Kolmogorov.PointToSet

open Filter TopologicalSpace MeasureTheory Measure
open scoped Topology ENNReal Computability

variable {X : Type*} [MetricSpace X]

/-! ### From Hausdorff dimension to small covers -/

/-- A set of Hausdorff dimension below `s` forces `s` to be positive. -/
private lemma pos_of_dimH_lt_ofReal {Z : Set X} {s : ℝ} (h : dimH Z < ENNReal.ofReal s) :
    0 < s :=
  ENNReal.ofReal_pos.mp (lt_of_le_of_lt bot_le h)

/-- The diameter power of a set, taken only over nonempty sets, is just its diameter power
(the empty set has diameter power `0` for positive exponents). -/
private lemma iSup_nonempty_ediam_rpow {C : Set X} {s : ℝ} (hs : 0 < s) :
    (⨆ (_ : C.Nonempty), Metric.ediam C ^ s) = Metric.ediam C ^ s := by
  by_cases h : C.Nonempty
  · rw [iSup_pos h]
  · rw [iSup_neg h, Set.not_nonempty_iff_eq_empty.mp h, Metric.ediam_empty,
      ENNReal.zero_rpow_of_pos hs, bot_eq_zero]

/-- A set of Hausdorff dimension below `s` has, for all `δ, ε > 0`, a countable cover by sets
of diameter at most `δ` whose total `s`-th diameter power is below `ε`. -/
private lemma exists_small_cover_of_dimH_lt (Z : Set X) (s : ℝ)
    (hs : _root_.dimH Z < ENNReal.ofReal s) :
    ∀ δ > 0, ∀ ε > 0, ∃ C : ℕ → Set X, Z ⊆ ⋃ i, C i ∧
      (∀ i, Metric.ediam (C i) ≤ ENNReal.ofReal δ) ∧
      (∑' i, (Metric.ediam (C i)) ^ s) < ENNReal.ofReal ε := by
  intro δ hδ ε hε
  let b : MeasurableSpace X := borel X
  have hb : BorelSpace X := ⟨rfl⟩
  have hs_pos : 0 < s := pos_of_dimH_lt_ofReal hs
  set d : NNReal := ⟨s, hs_pos.le⟩
  have h_eq : ENNReal.ofReal s = (d : ℝ≥0∞) := ENNReal.ofReal_eq_coe_nnreal hs_pos.le
  have hs_nnreal : dimH Z < (d : ℝ≥0∞) := by rwa [← h_eq]
  have h_meas : μH[s] Z = 0 := @hausdorffMeasure_of_dimH_lt X _ b hb Z d hs_nnreal
  have H := (@hausdorffMeasure_apply X _ b hb s Z).symm.trans h_meas
  have h_inf := iSup_le_iff.mp (iSup_le_iff.mp H.le (ENNReal.ofReal δ))
    (ENNReal.ofReal_pos.mpr hδ)
  obtain ⟨C, hC⟩ := iInf_lt_iff.mp (lt_of_le_of_lt h_inf (ENNReal.ofReal_pos.mpr hε))
  obtain ⟨hC_sub, hC⟩ := iInf_lt_iff.mp hC
  obtain ⟨hC_diam, hC_sum⟩ := iInf_lt_iff.mp hC
  refine ⟨C, hC_sub, hC_diam, ?_⟩
  simpa only [iSup_nonempty_ediam_rpow hs_pos] using hC_sum

/-- If arbitrarily fine covers of arbitrarily small `s`-th diameter power sum exist, then
`s` is positive: a single member of diameter at most `1` already costs at least `1`. -/
private lemma pos_of_small_covers (Z : Set X) (s : ℝ)
    (h_cover : ∀ δ > 0, ∀ ε > 0, ∃ C : ℕ → Set X, Z ⊆ ⋃ i, C i ∧
      (∀ i, Metric.ediam (C i) ≤ ENNReal.ofReal δ) ∧
      (∑' i, (Metric.ediam (C i)) ^ s) < ENNReal.ofReal ε) :
    0 < s := by
  by_contra! hs
  obtain ⟨C, _, h_diam, h_sum⟩ := h_cover 1 one_pos (1 / 2) (by norm_num)
  have h_lt : (Metric.ediam (C 0)) ^ s < 1 := by
    refine lt_of_le_of_lt (ENNReal.le_tsum (f := fun i ↦ (Metric.ediam (C i)) ^ s) 0)
      (h_sum.trans ?_)
    rw [← ENNReal.ofReal_one, ENNReal.ofReal_lt_ofReal_iff one_pos]
    norm_num
  have h_diam_le : Metric.ediam (C 0) ≤ 1 := by simpa only [ENNReal.ofReal_one] using h_diam 0
  have h_ge : 1 ≤ (Metric.ediam (C 0)) ^ s := by
    simpa only [ENNReal.rpow_zero] using ENNReal.rpow_le_rpow_of_exponent_ge h_diam_le hs
  exact absurd h_lt (not_lt.mpr h_ge)

/-! ### Enclosing a single set in an ideal dyadic ball -/

/-- For a positive `d ≤ 2⁻⁽ᴹ⁺²⁾` there is a dyadic radius `2⁻ᵏ` with `k ≥ M` between `2 d`
and `4 d`. -/
private lemma exists_dyadicRadius_between (d : ℝ) (hd_pos : 0 < d) (M : ℕ)
    (h_diam_le : d ≤ (2 : ℝ)⁻¹ ^ (M + 2)) :
    ∃ k : ℕ, M ≤ k ∧ 2 * d ≤ dyadicRadius k ∧ dyadicRadius k < 4 * d := by
  have h_quarter : (2 : ℝ)⁻¹ ^ (M + 2) ≤ 1 / 4 := by
    calc (2 : ℝ)⁻¹ ^ (M + 2) ≤ (2 : ℝ)⁻¹ ^ 2 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 4 := by norm_num
  obtain ⟨k, h1, h2⟩ : ∃ k : ℕ, (2⁻¹ : ℝ) ^ (k + 1) < 2 * d ∧ 2 * d ≤ (2⁻¹ : ℝ) ^ k :=
    exists_nat_pow_near_of_lt_one (by linarith) (by linarith) (by norm_num) (by norm_num)
  refine ⟨k, ?_, h2, ?_⟩
  · by_contra! h_lt
    have h_contra : 2 * d ≤ (2 : ℝ)⁻¹ ^ (k + 1) :=
      calc 2 * d ≤ 2 * ((2 : ℝ)⁻¹ ^ (M + 2)) := by linarith
        _ ≤ 2 * ((2 : ℝ)⁻¹ ^ (k + 2)) :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)) (by norm_num)
        _ = (2 : ℝ)⁻¹ ^ (k + 1) := by ring
    linarith
  · have h_rad_next : (2 : ℝ)⁻¹ ^ (k + 1) = dyadicRadius k / 2 := by
      rw [dyadicRadius, pow_succ]
      ring
    rw [h_rad_next] at h1
    linarith

/-- A set of diameter `d` is contained in an ideal ball of radius at least `2 d`. -/
private lemma exists_ideal_ball_superset (P : Presentation X) {C : Set X} (hC : C.Nonempty)
    {d : ℝ} (h_diam : Metric.ediam C = ENNReal.ofReal d) (hd_pos : 0 < d) {k : ℕ}
    (h_radius : 2 * d ≤ dyadicRadius k) :
    ∃ i : ℕ, C ⊆ Metric.ball (P.ι i) (dyadicRadius k) := by
  obtain ⟨x, hx⟩ := hC
  obtain ⟨i, hi⟩ := Metric.denseRange_iff.mp P.dense x (dyadicRadius k - d) (by linarith)
  refine ⟨i, fun y hy ↦ ?_⟩
  have h_dist : dist y x ≤ d := by
    have h_edist : edist y x ≤ Metric.ediam C := Metric.edist_le_ediam_of_mem hy hx
    rwa [h_diam, edist_dist, ENNReal.ofReal_le_ofReal_iff hd_pos.le] at h_edist
  rw [Metric.mem_ball]
  linarith [dist_triangle y x (P.ι i)]

/-- The cost `2^(-s k)` of a dyadic radius `2⁻ᵏ < 4 d` is at most `4^s` times `d^s`. -/
private lemma two_rpow_neg_mul_le_of_dyadicRadius_lt {s d : ℝ} (hs : 0 < s) {k : ℕ}
    (h_radius : dyadicRadius k < 4 * d) :
    (2 : ℝ≥0∞) ^ (-s * (k : ℝ)) ≤ ENNReal.ofReal (4 ^ s) * (ENNReal.ofReal d) ^ s := by
  have h_rad : ENNReal.ofReal (dyadicRadius k) = (2 : ℝ≥0∞) ^ (-(k : ℝ)) := by
    rw [dyadicRadius, ENNReal.ofReal_pow (by norm_num),
      ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat, ← ENNReal.inv_pow,
      ENNReal.rpow_neg, ENNReal.rpow_natCast]
  have h_le : ENNReal.ofReal (dyadicRadius k) ≤ ENNReal.ofReal (4 * d) :=
    ENNReal.ofReal_le_ofReal h_radius.le
  calc (2 : ℝ≥0∞) ^ (-s * (k : ℝ))
      = (ENNReal.ofReal (dyadicRadius k)) ^ s := by
        rw [h_rad, ← ENNReal.rpow_mul]
        congr 1
        ring
    _ ≤ ENNReal.ofReal (4 * d) ^ s := ENNReal.rpow_le_rpow h_le hs.le
    _ = ENNReal.ofReal (4 ^ s) * (ENNReal.ofReal d) ^ s := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.mul_rpow_of_nonneg _ _ hs.le,
          ENNReal.ofReal_rpow_of_pos (by norm_num)]

/-- A nonempty set of positive finite diameter at most `2⁻⁽ᴹ⁺²⁾` lies in an ideal dyadic ball of
precision at least `M` whose cost is at most `4^s` times the `s`-th power of its diameter. -/
private lemma exists_ideal_ball_of_ediam_pos (P : Presentation X) {s : ℝ} (hs : 0 < s) (M : ℕ)
    {C : Set X} (hC : C.Nonempty) (h_diam_pos : 0 < Metric.ediam C)
    (h_diam_le : Metric.ediam C ≤ ENNReal.ofReal ((2 : ℝ)⁻¹ ^ (M + 2))) :
    ∃ a : ℕ × ℕ, M ≤ a.2 ∧ C ⊆ Metric.ball (P.ι a.1) (dyadicRadius a.2) ∧
      (2 : ℝ≥0∞) ^ (-s * a.2) ≤ ENNReal.ofReal (4 ^ s) * (Metric.ediam C) ^ s := by
  have h_ne_top : Metric.ediam C ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top h_diam_le
  have hd_eq : Metric.ediam C = ENNReal.ofReal (Metric.ediam C).toReal :=
    (ENNReal.ofReal_toReal h_ne_top).symm
  have hd_pos : 0 < (Metric.ediam C).toReal := ENNReal.toReal_pos h_diam_pos.ne' h_ne_top
  obtain ⟨k, h_M, h_k1, h_k2⟩ := exists_dyadicRadius_between (Metric.ediam C).toReal hd_pos M
    ((ENNReal.ofReal_le_ofReal_iff (by positivity)).mp (hd_eq ▸ h_diam_le))
  obtain ⟨i, h_cover⟩ := exists_ideal_ball_superset P hC hd_eq hd_pos h_k1
  refine ⟨⟨i, k⟩, h_M, h_cover, ?_⟩
  rw [hd_eq]
  exact two_rpow_neg_mul_le_of_dyadicRadius_lt hs h_k2

/-- A nonempty set of diameter zero lies in an ideal dyadic ball of precision at least `M` and
arbitrarily small cost. -/
private lemma exists_ideal_ball_of_ediam_eq_zero (P : Presentation X) {s : ℝ} (hs : 0 < s)
    (M : ℕ) {C : Set X} (hC : C.Nonempty) (h_diam_zero : Metric.ediam C = 0) {η : ℝ}
    (hη : 0 < η) :
    ∃ a : ℕ × ℕ, M ≤ a.2 ∧ C ⊆ Metric.ball (P.ι a.1) (dyadicRadius a.2) ∧
      (2 : ℝ≥0∞) ^ (-s * a.2) ≤ ENNReal.ofReal η := by
  obtain ⟨x, hx⟩ := hC
  have h_singleton : C ⊆ {x} := fun y hy ↦ by
    have h : edist y x ≤ Metric.ediam C := Metric.edist_le_ediam_of_mem hy hx
    rw [h_diam_zero] at h
    exact edist_eq_zero.mp (le_bot_iff.mp h)
  have h_tendsto : Tendsto (fun k : ℕ ↦ (2 : ℝ≥0∞) ^ (-s * (k : ℝ))) atTop (𝓝 0) := by
    have h_lt : (2 : ℝ≥0∞) ^ (-s) < 1 :=
      ENNReal.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    have h_eq : (fun k : ℕ ↦ (2 : ℝ≥0∞) ^ (-s * (k : ℝ))) = fun k : ℕ ↦ ((2 : ℝ≥0∞) ^ (-s)) ^ k :=
      funext fun k ↦ by rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    rw [h_eq]
    exact ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one h_lt
  obtain ⟨k, hk_cost, hk_M⟩ := ((h_tendsto.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hη))).and
    (eventually_ge_atTop M)).exists
  obtain ⟨i, hi⟩ := Metric.denseRange_iff.mp P.dense x (dyadicRadius k) (by
    unfold dyadicRadius
    positivity)
  refine ⟨⟨i, k⟩, hk_M, fun y hy ↦ ?_, hk_cost.le⟩
  rw [Set.mem_singleton_iff.mp (h_singleton hy)]
  exact Metric.mem_ball.mpr (by simpa only [dist_comm] using hi)

/-! ### Assembling an ideal dyadic cover -/

/-- Selecting one ideal ball for each nonempty member of a cover of `Z` gives an ideal dyadic
cover of `Z`. -/
private lemma isIdealDyadicCover_image (P : Presentation X) {Z : Set X} {M : ℕ} {C : ℕ → Set X}
    (hZ : Z ⊆ ⋃ i, C i) {f : ℕ → ℕ × ℕ}
    (h_cover : ∀ i, (C i).Nonempty →
      M ≤ (f i).2 ∧ C i ⊆ Metric.ball (P.ι (f i).1) (dyadicRadius (f i).2)) :
    IsIdealDyadicCover P Z M (f '' {i | (C i).Nonempty}) := by
  refine ⟨?_, fun z hz ↦ ?_⟩
  · rintro _ ⟨i, hi, rfl⟩
    exact (h_cover i hi).1
  · obtain ⟨i, hzi⟩ := Set.mem_iUnion.mp (hZ hz)
    exact Set.mem_iUnion₂.mpr ⟨f i, ⟨i, ⟨z, hzi⟩, rfl⟩, (h_cover i ⟨z, hzi⟩).2 hzi⟩

omit [MetricSpace X] in
/-- The cost of the distinct selected pairs is at most the sum of the per-member costs. -/
private lemma idealDyadicCoverCost_image_le {s : ℝ} {C : ℕ → Set X} {f : ℕ → ℕ × ℕ}
    {g : ℕ → ℝ≥0∞} (h_cost : ∀ i, (C i).Nonempty → (2 : ℝ≥0∞) ^ (-s * (f i).2) ≤ g i) :
    idealDyadicCoverCost s (f '' {i | (C i).Nonempty}) ≤ ∑' i, g i := by
  let I : Set ℕ := {i | (C i).Nonempty}
  have h_surj : Function.Surjective
      (fun i : I ↦ (⟨f i, Set.mem_image_of_mem f i.property⟩ : f '' I)) := by
    rintro ⟨_, i, hi, rfl⟩
    exact ⟨⟨i, hi⟩, rfl⟩
  calc idealDyadicCoverCost s (f '' I)
      ≤ ∑' i : I, (2 : ℝ≥0∞) ^ (-s * (f i.val).2) :=
        ENNReal.tsum_le_tsum_comp_of_surjective h_surj
          (fun a : f '' I ↦ (2 : ℝ≥0∞) ^ (-s * a.val.2))
    _ ≤ ∑' i : I, g i.val := ENNReal.tsum_le_tsum fun i ↦ h_cost i.val i.property
    _ ≤ ∑' i, g i := ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective g

/-- The margins `ε / 2^(i+2)` of the individual members sum to `ε / 2`. -/
private lemma tsum_ofReal_mul_inv_two_pow_add_two {ε : ℝ} (hε : 0 < ε) :
    (∑' i : ℕ, ENNReal.ofReal (ε * (2 : ℝ)⁻¹ ^ (i + 2))) = ENNReal.ofReal (ε / 2) := by
  have h_term : (fun i : ℕ ↦ ε * (2 : ℝ)⁻¹ ^ (i + 2)) =
      fun i : ℕ ↦ (ε * (2 : ℝ)⁻¹ ^ 2) * (2 : ℝ)⁻¹ ^ i := funext fun i ↦ by ring
  have h_geom : HasSum (fun i : ℕ ↦ (2 : ℝ)⁻¹ ^ i) 2 := by
    simpa only [one_div] using hasSum_geometric_two
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun i ↦ by positivity)
    (by rw [h_term]; exact (h_geom.mul_left _).summable), h_term, tsum_mul_left, h_geom.tsum_eq]
  congr 1
  ring

/-- If the weighted diameter powers sum below `ε / (2 · 4^s)`, then the weighted cost plus the
margins stays below `ε`. -/
private lemma ofReal_mul_tsum_add_lt {s ε : ℝ} {C : ℕ → Set X} (hε : 0 < ε)
    (h_sum : (∑' i, (Metric.ediam (C i)) ^ s) < ENNReal.ofReal (ε / (2 * 4 ^ s))) :
    ENNReal.ofReal (4 ^ s) * (∑' i, (Metric.ediam (C i)) ^ s) + ENNReal.ofReal (ε / 2) <
      ENNReal.ofReal ε := by
  have h4s : 0 < (4 : ℝ) ^ s := Real.rpow_pos_of_pos (by positivity) s
  have h_mul : ENNReal.ofReal (4 ^ s) * ENNReal.ofReal (ε / (2 * 4 ^ s)) =
      ENNReal.ofReal (ε / 2) := by
    rw [← ENNReal.ofReal_mul h4s.le]
    congr 1
    field_simp
  have h_lt := ENNReal.mul_lt_mul_left (ENNReal.ofReal_pos.mpr h4s).ne' ENNReal.ofReal_ne_top
    h_sum
  rw [mul_comm, mul_comm (ENNReal.ofReal (ε / (2 * 4 ^ s))), h_mul] at h_lt
  calc _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
        ENNReal.add_lt_add_right ENNReal.ofReal_ne_top h_lt
    _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

/-- Above Hausdorff dimension there are arbitrarily fine ideal dyadic covers of arbitrarily
small power-gauge cost. Blueprint node `conf:hausdorff-interface`. -/
theorem hausdorffDyadicIdealCover (P : Presentation X) (Z : Set X) (s : ℝ)
    (hs : _root_.dimH Z < ENNReal.ofReal s) (M : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ E : Set (ℕ × ℕ), IsIdealDyadicCover P Z M E ∧
      idealDyadicCoverCost s E < ENNReal.ofReal ε := by
  have h_small := exists_small_cover_of_dimH_lt Z s hs
  have hs_pos : 0 < s := pos_of_small_covers Z s h_small
  have hε' : (0 : ℝ) < ε / (2 * 4 ^ s) :=
    div_pos hε (mul_pos two_pos (Real.rpow_pos_of_pos (by positivity) s))
  obtain ⟨C, hZ_sub, h_diam, h_sum⟩ :=
    h_small ((2 : ℝ)⁻¹ ^ (M + 2)) (by positivity) (ε / (2 * 4 ^ s)) hε'
  have h_choice : ∀ i : ℕ, ∃ a : ℕ × ℕ, (C i).Nonempty → M ≤ a.2 ∧
      C i ⊆ Metric.ball (P.ι a.1) (dyadicRadius a.2) ∧
      (2 : ℝ≥0∞) ^ (-s * a.2) ≤
        ENNReal.ofReal (4 ^ s) * (Metric.ediam (C i)) ^ s +
          ENNReal.ofReal (ε * (2 : ℝ)⁻¹ ^ (i + 2)) := by
    intro i
    by_cases h_ne : (C i).Nonempty
    · by_cases h_zero : Metric.ediam (C i) = 0
      · obtain ⟨a, h_M, h_sub, h_cost⟩ := exists_ideal_ball_of_ediam_eq_zero P hs_pos M h_ne
          h_zero (η := ε * (2 : ℝ)⁻¹ ^ (i + 2)) (by positivity)
        exact ⟨a, fun _ ↦ ⟨h_M, h_sub, h_cost.trans le_add_self⟩⟩
      · obtain ⟨a, h_M, h_sub, h_cost⟩ := exists_ideal_ball_of_ediam_pos P hs_pos M h_ne
          (pos_iff_ne_zero.mpr h_zero) (h_diam i)
        exact ⟨a, fun _ ↦ ⟨h_M, h_sub, h_cost.trans le_self_add⟩⟩
    · exact ⟨(0, 0), fun h ↦ absurd h h_ne⟩
  choose f hf using h_choice
  have h_cost := idealDyadicCoverCost_image_le (C := C) (f := f)
    (g := fun i ↦ ENNReal.ofReal (4 ^ s) * (Metric.ediam (C i)) ^ s +
      ENNReal.ofReal (ε * (2 : ℝ)⁻¹ ^ (i + 2))) fun i hi ↦ (hf i hi).2.2
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, tsum_ofReal_mul_inv_two_pow_add_two hε] at h_cost
  exact ⟨_, isIdealDyadicCover_image P hZ_sub fun i hi ↦ ⟨(hf i hi).1, (hf i hi).2.1⟩,
    h_cost.trans_lt (ofReal_mul_tsum_add_lt hε h_sum)⟩

/-! ### From small ideal covers to Hausdorff dimension -/

/-- An open ball of radius `r` has diameter at most `2 r`. -/
private lemma ediam_ball_le (x : X) (r : ℝ) :
    Metric.ediam (Metric.ball x r) ≤ ENNReal.ofReal (2 * r) := by
  refine Metric.ediam_le_of_forall_dist_le fun y hy z hz ↦ ?_
  rw [Metric.mem_ball] at hy hz
  linarith [dist_triangle y x z, dist_comm x z]

/-- The `s`-th diameter powers of the balls of an ideal dyadic cover sum to at most `2^s` times
its cost. -/
private lemma tsum_ediam_ball_rpow_le (P : Presentation X) {s : ℝ} (hs : 0 ≤ s)
    (E : Set (ℕ × ℕ)) :
    (∑' a : E, Metric.ediam (Metric.ball (P.ι a.1.1) (dyadicRadius a.1.2)) ^ s) ≤
      (2 : ℝ≥0∞) ^ s * idealDyadicCoverCost s E := by
  rw [idealDyadicCoverCost, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun a ↦ ?_
  have h_rad : ENNReal.ofReal (dyadicRadius a.1.2) = (2 : ℝ≥0∞) ^ (-(a.1.2 : ℝ)) := by
    rw [dyadicRadius, ENNReal.ofReal_pow (by norm_num),
      ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat, ← ENNReal.inv_pow,
      ENNReal.rpow_neg, ENNReal.rpow_natCast]
  calc Metric.ediam (Metric.ball (P.ι a.1.1) (dyadicRadius a.1.2)) ^ s
      ≤ (ENNReal.ofReal (2 * dyadicRadius a.1.2)) ^ s :=
        ENNReal.rpow_le_rpow (ediam_ball_le _ _) hs
    _ = (2 : ℝ≥0∞) ^ s * (2 : ℝ≥0∞) ^ (-s * a.1.2) := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, h_rad,
          ENNReal.mul_rpow_of_nonneg _ _ hs, ← ENNReal.rpow_mul]
        congr 2
        ring

/-- Ideal dyadic covers of every precision whose costs tend to `0` show that the Hausdorff
measure `μH[s] Z` vanishes. -/
private lemma hausdorffMeasure_eq_zero_of_ideal_covers (P : Presentation X) (Z : Set X) {s : ℝ}
    (hs : 0 ≤ s) (E : ℕ → Set (ℕ × ℕ)) (hE : ∀ n, IsIdealDyadicCover P Z n (E n))
    (hcost : Tendsto (fun n ↦ idealDyadicCoverCost s (E n)) atTop (𝓝 0)) :
    @hausdorffMeasure X _ (borel X) (@BorelSpace.mk X _ (borel X) rfl) s Z = 0 := by
  classical
  let _ : MeasurableSpace X := borel X
  let _ : BorelSpace X := ⟨rfl⟩
  let C : (n : ℕ) → E n → Set X := fun _ a ↦ Metric.ball (P.ι a.val.1) (dyadicRadius a.val.2)
  let r : ℕ → ℝ≥0∞ := fun n ↦ ENNReal.ofReal (2 * dyadicRadius n)
  have hr : Tendsto r atTop (𝓝 0) := by
    have hrad : Tendsto dyadicRadius atTop (𝓝 (0 : ℝ)) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa only [mul_zero, ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal (hrad.const_mul 2)
  have hdiam : ∀ n (a : E n), Metric.ediam (C n a) ≤ r n := fun n a ↦
    (ediam_ball_le _ _).trans (ENNReal.ofReal_le_ofReal (by
      have := pow_le_pow_of_le_one (a := (2 : ℝ)⁻¹) (by norm_num) (by norm_num)
        ((hE n).1 a.val a.property)
      unfold dyadicRadius
      linarith))
  have hcover : ∀ n, Z ⊆ ⋃ a : E n, C n a := fun n x hx ↦ by
    obtain ⟨a, ha, hxball⟩ := Set.mem_iUnion₂.mp ((hE n).2 hx)
    exact Set.mem_iUnion.mpr ⟨⟨a, ha⟩, hxball⟩
  have hscale : Tendsto (fun n ↦ (2 : ℝ≥0∞) ^ s * idealDyadicCoverCost s (E n)) atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul (a := (2 : ℝ≥0∞) ^ s) hcost
      (Or.inr (ENNReal.rpow_ne_top_of_nonneg hs (by norm_num)))
  have hsum : Tendsto (fun n ↦ ∑' a : E n, Metric.ediam (C n a) ^ s) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hscale
      (Eventually.of_forall fun _ ↦ bot_le)
      (Eventually.of_forall fun n ↦ tsum_ediam_ball_rpow_le P hs (E n))
  have hmeasure := hausdorffMeasure_le_liminf_tsum s Z r hr C (Eventually.of_forall hdiam)
    (Eventually.of_forall hcover)
  exact le_zero_iff.mp (by simpa only [hsum.liminf_eq] using hmeasure)

/-- Arbitrarily fine ideal dyadic covers of arbitrarily small cost bound Hausdorff dimension.
Blueprint node `conf:hausdorff-interface`. -/
theorem hausdorffDyadicIdealCover_converse (P : Presentation X) (Z : Set X) (s : ℝ)
    (hs : 0 ≤ s)
    (hcovers : ∀ M : ℕ, ∀ ε : ℝ, 0 < ε → ∃ E : Set (ℕ × ℕ),
      IsIdealDyadicCover P Z M E ∧ idealDyadicCoverCost s E < ENNReal.ofReal ε) :
    _root_.dimH Z ≤ ENNReal.ofReal s := by
  choose E hE using fun n : ℕ ↦ hcovers n (1 / (n + 1 : ℝ)) (one_div_pos.mpr (by positivity))
  have hcost : Tendsto (fun n ↦ idealDyadicCoverCost s (E n)) atTop (𝓝 0) := by
    have h_ofReal : Tendsto (fun n : ℕ ↦ ENNReal.ofReal (1 / (n + 1 : ℝ))) atTop (𝓝 0) := by
      simpa only [ENNReal.ofReal_zero] using
        ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_ofReal
      (Eventually.of_forall fun _ ↦ bot_le) (Eventually.of_forall fun n ↦ (hE n).2.le)
  have h_meas := hausdorffMeasure_eq_zero_of_ideal_covers P Z hs E (fun n ↦ (hE n).1) hcost
  let _ : MeasurableSpace X := borel X
  have _ : BorelSpace X := ⟨rfl⟩
  have hd_le : dimH Z ≤ (Real.toNNReal s : ℝ≥0∞) := by
    refine dimH_le_of_hausdorffMeasure_ne_top (d := Real.toNNReal s) ?_
    rw [Real.coe_toNNReal s hs, h_meas]
    exact ENNReal.zero_ne_top
  exact hd_le

end Kolmogorov.PointToSet
