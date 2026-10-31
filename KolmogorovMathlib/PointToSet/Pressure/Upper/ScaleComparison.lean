/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.Pressure.Lower
import KolmogorovMathlib.PointToSet.Pressure.Defs
import KolmogorovMathlib.Oracle.KraftChaitin
import KolmogorovMathlib.Oracle.Joins
import KolmogorovMathlib.PointToSet.Order

/-!
# Scale comparison for upper pressure

The upper capacity and the countable modification of upper pressure come in two weight
conventions: the centered one (`PressureWeight.centered`, the Birkhoff sum at the center of a
Bowen ball) and the supremum one (`PressureWeight.supremum`, the supremum of the Birkhoff sums on
the ball).  This file compares them at the dyadic scales `dyadicRadius p` of a `PressureData`
(blueprint node `pressure:upper-scale`):

* `upperPressure_scale_comparison` and `upperPressure_scale_comparison_modified` sandwich the
  supremum quantities between the centered ones and the centered ones plus the oscillation bound
  `D.ω p`;
* `upperPressure_scale_comparison_capacity_radius` and
  `upperPressure_scale_comparison_modified_radius` show that the centered quantities increase
  when the radius decreases;
* `upperPressure_scale_comparison_centered_limit` and `upperPressure_scale_comparison_limit` show
  that the scale-zero limit exists, for both weights, and equals `upperPressure`;
* `upperPressure_scale_comparison_countable` and `upperPressure_scale_comparison_countable_limit`
  give stability under countable coverings;
* `exists_partitionSum_approximation`, `exists_partitionSum_approximation_pos` and
  `exists_partitionSum_approximation_rate` (blueprint node `pressure:partition-approx`) choose
  near-optimal countable covering families at each order.

These facts feed the comparison of upper pressure with the effective pressure supremum and the
uniform-net bounds of `KolmogorovMathlib.PointToSet.Pressure.Upper`.
-/

namespace Kolmogorov.PointToSet

open Filter
open scoped Topology ENNReal Computability

variable {X : Type*} [MetricSpace X]

/-- Bounded Birkhoff distortion multiplies the partition sum by at most `2 ^ (n * ω p)` when
passing from centered to supremum weights. -/
private lemma partitionSum_supremum_le_mul_centered (D : PressureData X) (Y : Set X) (p : ℕ)
    (hp : D.p₀ ≤ p)
    (n : ℕ) :
    partitionSum D.T D.φ .supremum Y n (dyadicRadius p) ≤
      partitionSum D.T D.φ .centered Y n (dyadicRadius p) *
        (2 : ℝ≥0∞) ^ ((n : ℝ) * D.ω p) := by
  have hzero : (2 : ℝ≥0∞) ^ ((n : ℝ) * D.ω p) ≠ 0 := by positivity
  have htop : (2 : ℝ≥0∞) ^ ((n : ℝ) * D.ω p) ≠ ⊤ := by finiteness
  unfold partitionSum
  rw [ENNReal.iInf_mul_of_ne hzero htop]
  refine iInf_mono fun F => ?_
  rw [ENNReal.iInf_mul_of_ne hzero htop]
  refine iInf_mono fun _ => ?_
  unfold partitionCoverCost
  rw [← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro y
  dsimp [pressureBallWeight]
  apply iSup₂_le
  intro z hz
  rw [← ENNReal.rpow_add _ _ (by norm_num) (by norm_num)]
  apply ENNReal.rpow_le_rpow_of_exponent_le (by norm_num)
  have hdist := recenter_bowen_cover_distortion D p hp n y z hz
  linarith [(abs_le.mp hdist).2]

/-- The upper capacities for centered and supremum weights differ by at most the oscillation
bound `D.ω p`.  Blueprint node `pressure:upper-scale`. -/
theorem upperPressure_scale_comparison (D : PressureData X) (Y : Set X)
    (p : ℕ) (hp : D.p₀ ≤ p) :
    upperCapacity D.T D.φ .centered Y (dyadicRadius p) ≤
      upperCapacity D.T D.φ .supremum Y (dyadicRadius p) ∧
    upperCapacity D.T D.φ .supremum Y (dyadicRadius p) ≤
      upperCapacity D.T D.φ .centered Y (dyadicRadius p) + (D.ω p : EReal) := by
  unfold upperCapacity
  constructor
  · apply limsup_le_limsup
    · filter_upwards with n
      exact pressureRate_le_of_le _ _ n
        (partitionSum_centered_le_supremum D.T D.φ Y n (dyadicRadius_pos p))
    · isBoundedDefault
    · isBoundedDefault
  · have hr : ∀ᶠ n : ℕ in atTop,
        pressureRate (fun n => partitionSum D.T D.φ .supremum Y n (dyadicRadius p)) n ≤
          pressureRate (fun n => partitionSum D.T D.φ .centered Y n (dyadicRadius p)) n +
            (D.ω p : EReal) := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      exact pressureRate_le_add_of_le_mul _ _ (D.ω p) n hn
        (partitionSum_supremum_le_mul_centered D Y p hp n)
    refine (limsup_le_limsup hr).trans ?_
    have hlim := EReal.limsup_add_le
      (u := pressureRate (fun n => partitionSum D.T D.φ .centered Y n (dyadicRadius p)))
      (v := fun _ : ℕ => (D.ω p : EReal)) (f := atTop)
      (Or.inr (by simp)) (Or.inr (by simp))
    simpa only [Pi.add_def, limsup_const] using hlim

/-- Countable modifications of the upper capacity with centered and supremum weights differ by at
most the oscillation bound `D.ω p`.  Blueprint node `pressure:upper-scale`. -/
theorem upperPressure_scale_comparison_modified (D : PressureData X) (Z : Set X)
    (p : ℕ) (hp : D.p₀ ≤ p) :
    modifiedUpperPressure D.T D.φ .centered Z (dyadicRadius p) ≤
      modifiedUpperPressure D.T D.φ .supremum Z (dyadicRadius p) ∧
    modifiedUpperPressure D.T D.φ .supremum Z (dyadicRadius p) ≤
      modifiedUpperPressure D.T D.φ .centered Z (dyadicRadius p) + (D.ω p : EReal) := by
  unfold modifiedUpperPressure
  refine ⟨iInf_mono fun Y => iInf_mono fun _ => iSup_mono fun k => ?_, ?_⟩
  · exact (upperPressure_scale_comparison D (Y k) p hp).1
  · calc
      _ ≤ ⨅ Y : ℕ → Set X, ⨅ (_ : Z ⊆ ⋃ k, Y k),
          (⨆ k, upperCapacity D.T D.φ .centered (Y k) (dyadicRadius p)) + (D.ω p : EReal) :=
        iInf_mono fun Y => iInf_mono fun _ =>
          (iSup_mono fun k => (upperPressure_scale_comparison D (Y k) p hp).2).trans
            (EReal.iSup_add_coe_le _ _)
      _ ≤ ⨅ Y : ℕ → Set X, (⨅ (_ : Z ⊆ ⋃ k, Y k),
          ⨆ k, upperCapacity D.T D.φ .centered (Y k) (dyadicRadius p)) + (D.ω p : EReal) :=
        iInf_mono fun Y => EReal.iInf_add_coe_le _ _
      _ ≤ _ := EReal.iInf_add_coe_le _ _

/-- The partition sum is antitone in the radius: smaller balls need more cost to cover. -/
private lemma partitionSum_centered_antitone_radius (T : X → X) (φ : X → ℝ)
    (Z : Set X) (n : ℕ) {r R : ℝ} (h : r ≤ R) :
    partitionSum T φ .centered Z n R ≤ partitionSum T φ .centered Z n r := by
  unfold partitionSum
  refine iInf_mono' fun F => ⟨F, iInf_mono' fun hF => ⟨⟨hF.1, ?_⟩, le_rfl⟩⟩
  exact hF.2.trans (Set.iUnion_mono fun y => Set.iUnion_mono fun _ =>
    bowenBall_subset_of_le T n y h)

/-- Centered upper capacity increases when a positive radius decreases.
Blueprint node `pressure:upper-scale`. -/
theorem upperPressure_scale_comparison_capacity_radius (D : PressureData X) (Y : Set X)
    (r R : ℝ) (hrR : r ≤ R) :
    upperCapacity D.T D.φ .centered Y R ≤ upperCapacity D.T D.φ .centered Y r := by
  unfold upperCapacity
  refine limsup_le_limsup (Eventually.of_forall fun n => ?_) (by isBoundedDefault)
    (by isBoundedDefault)
  exact pressureRate_le_of_le _ _ n (partitionSum_centered_antitone_radius D.T D.φ Y n hrR)

/-- The centered countable modification is also antitone in the positive radius.
Blueprint node `pressure:upper-scale`. -/
theorem upperPressure_scale_comparison_modified_radius (D : PressureData X) (Z : Set X)
    (r R : ℝ) (hrR : r ≤ R) :
    modifiedUpperPressure D.T D.φ .centered Z R ≤
      modifiedUpperPressure D.T D.φ .centered Z r := by
  unfold modifiedUpperPressure
  exact iInf_mono fun Y => iInf_mono fun _ => iSup_mono fun k =>
    upperPressure_scale_comparison_capacity_radius D (Y k) r R hrR

/-- A supremum over the indices `p ≥ p₀` of a monotone sequence is the supremum over all
indices. -/
private lemma iSup_ge_eq_iSup_of_monotone {f : ℕ → EReal} (hf : Monotone f) (p₀ : ℕ) :
    (⨆ p, ⨆ (_ : p₀ ≤ p), f p) = ⨆ p, f p :=
  le_antisymm (iSup₂_le fun p _ => le_iSup f p)
    (iSup_le fun p => le_iSup₂_of_le (max p p₀) (le_max_right _ _) (hf (le_max_left _ _)))

/-- The centered upper modifications converge to their small-scale supremum.
Blueprint node `pressure:upper-scale`. -/
theorem upperPressure_scale_comparison_centered_limit (D : PressureData X) (Z : Set X) :
    Tendsto (fun p => modifiedUpperPressure D.T D.φ .centered Z (dyadicRadius p)) atTop
      (𝓝 (upperPressure D.T D.φ D.p₀ Z)) := by
  have h_mono :
      Monotone (fun p => modifiedUpperPressure D.T D.φ .centered Z (dyadicRadius p)) := by
    intro p q hpq
    refine upperPressure_scale_comparison_modified_radius D Z (dyadicRadius q) (dyadicRadius p)
      (dyadicRadius_antitone hpq)
  have heq : upperPressure D.T D.φ D.p₀ Z =
      ⨆ p, modifiedUpperPressure D.T D.φ .centered Z (dyadicRadius p) :=
    iSup_ge_eq_iSup_of_monotone h_mono D.p₀
  rw [heq]
  exact tendsto_atTop_iSup h_mono

/-- The source's supremum-weight upper scale limit exists and equals centered pressure.
Blueprint node `pressure:upper-scale`. -/
theorem upperPressure_scale_comparison_limit (D : PressureData X) (Z : Set X) :
    Tendsto (fun p => modifiedUpperPressure D.T D.φ .supremum Z (dyadicRadius p)) atTop
      (𝓝 (upperPressure D.T D.φ D.p₀ Z)) := by
  have hω : Tendsto (fun p => (D.ω p : EReal)) atTop (𝓝 (0 : EReal)) := by
    simpa only [EReal.coe_zero] using EReal.tendsto_coe.mpr D.ω_tendsto
  have hupper : Tendsto
      (fun p => modifiedUpperPressure D.T D.φ .centered Z (dyadicRadius p) + (D.ω p : EReal))
      atTop (𝓝 (upperPressure D.T D.φ D.p₀ Z)) := by
    have h := (EReal.continuousAt_add (p := (upperPressure D.T D.φ D.p₀ Z, 0))
      (Or.inr EReal.zero_ne_bot) (Or.inr EReal.zero_ne_top)).tendsto.comp
      ((upperPressure_scale_comparison_centered_limit D Z).prodMk_nhds hω)
    simpa only [Function.comp_def, add_zero] using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (upperPressure_scale_comparison_centered_limit D Z) hupper ?_ ?_
  · filter_upwards [Ici_mem_atTop D.p₀] with p hp
    exact (upperPressure_scale_comparison_modified D Z p hp).1
  · filter_upwards [Ici_mem_atTop D.p₀] with p hp
    exact (upperPressure_scale_comparison_modified D Z p hp).2

/-- At a valid radius, either countable modification is stable under countable coverings.
Blueprint node `pressure:upper-scale`. -/
theorem upperPressure_scale_comparison_countable (D : PressureData X) (w : PressureWeight) (r : ℝ)
    (Z : Set X) (Y : ℕ → Set X) (hZY : Z ⊆ ⋃ j, Y j) :
    modifiedUpperPressure D.T D.φ w Z r ≤ ⨆ j, modifiedUpperPressure D.T D.φ w (Y j) r := by
  refine le_of_forall_gt_imp_ge_of_dense fun a ha => ?_
  have H : ∀ j, ∃ Y' : ℕ → Set X, Y j ⊆ ⋃ k, Y' k ∧
      ⨆ k, upperCapacity D.T D.φ w (Y' k) r < a := by
    intro j
    have hj : modifiedUpperPressure D.T D.φ w (Y j) r < a :=
      (le_iSup (fun j => modifiedUpperPressure D.T D.φ w (Y j) r) j).trans_lt ha
    obtain ⟨Y', hY'⟩ := iInf_lt_iff.mp hj
    obtain ⟨hcov, hlt⟩ := iInf_lt_iff.mp hY'
    exact ⟨Y', hcov, hlt⟩
  choose Y' hcov hY' using H
  let Y'' : ℕ → Set X := fun n => Y' n.unpair.1 n.unpair.2
  have hcov'' : Z ⊆ ⋃ k, Y'' k := by
    intro z hz
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hZY hz)
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (hcov j hj)
    exact Set.mem_iUnion.mpr ⟨Nat.pair j k, by simpa only [Y'', Nat.unpair_pair] using hk⟩
  have hsup : ⨆ k, upperCapacity D.T D.φ w (Y'' k) r ≤ a := by
    refine iSup_le fun k => ?_
    exact ((le_iSup (fun k₂ => upperCapacity D.T D.φ w (Y' k.unpair.1 k₂) r) k.unpair.2).trans_lt
      (hY' k.unpair.1)).le
  exact (iInf₂_le Y'' hcov'').trans hsup

/-- Scale-zero upper pressure is stable under countable coverings.
Blueprint node `pressure:upper-scale`. -/
theorem upperPressure_scale_comparison_countable_limit (D : PressureData X)
    (Z : Set X) (Y : ℕ → Set X) (hZY : Z ⊆ ⋃ j, Y j) :
    upperPressure D.T D.φ D.p₀ Z ≤ ⨆ j, upperPressure D.T D.φ D.p₀ (Y j) := by
  unfold upperPressure
  refine iSup₂_le fun p hp => ?_
  exact (upperPressure_scale_comparison_countable D .centered (dyadicRadius p)
    Z Y hZY).trans
    (iSup_mono fun j => le_iSup₂_of_le p hp le_rfl)

/-- At a valid scale the partition infimum of a nonempty set is strictly positive.
Blueprint node `pressure:partition-approx`. -/
theorem exists_partitionSum_approximation_pos (D : PressureData X) (w : PressureWeight)
    (Y : Set X) (hY : Y.Nonempty) (p : ℕ) (hp : D.p₀ ≤ p) (n : ℕ) :
    0 < partitionSum D.T D.φ w Y n (dyadicRadius p) := by
  obtain ⟨x, hx⟩ := hY
  refine lt_of_lt_of_le
    (b := (2 : ℝ≥0∞) ^ (birkhoffSum D.T D.φ n x - (n : ℝ) * D.ω p))
    (ENNReal.rpow_pos (by norm_num) (by norm_num)) ?_
  unfold partitionSum
  refine le_iInf fun F => le_iInf fun hF => ?_
  obtain ⟨y, hyF, hxy⟩ : ∃ y ∈ F, x ∈ bowenBall D.T n y (dyadicRadius p) := by
    simpa only [Set.mem_iUnion, exists_prop] using hF.2 hx
  refine le_trans ?_ (ENNReal.le_tsum
    (f := fun z : F => pressureBallWeight D.T D.φ w n z (dyadicRadius p)) ⟨y, hyF⟩)
  have hdist := recenter_bowen_cover_distortion D p hp n y x hxy
  have hωn : 0 ≤ (n : ℝ) * D.ω p := mul_nonneg (Nat.cast_nonneg n) (D.ω_pos p hp).le
  cases w with
  | centered =>
    refine ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    linarith [le_abs_self (birkhoffSum D.T D.φ n x - birkhoffSum D.T D.φ n y)]
  | supremum =>
    refine le_trans (ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) (sub_le_self _ hωn)) ?_
    exact le_iSup₂ (f := fun z (_ : z ∈ bowenBall D.T n y (dyadicRadius p)) =>
      (2 : ℝ≥0∞) ^ birkhoffSum D.T D.φ n z) x hxy

/-- A finite partition infimum of a nonempty set is approximated within a factor two by the cost
of a countable cover.  Blueprint node `pressure:partition-approx`. -/
theorem exists_partitionSum_approximation (D : PressureData X) (w : PressureWeight) (Y : Set X)
    (hY : Y.Nonempty) (p : ℕ) (hp : D.p₀ ≤ p) (n : ℕ)
    (hfinite : partitionSum D.T D.φ w Y n (dyadicRadius p) < ⊤) :
    ∃ F : Set X, F.Countable ∧ Y ⊆ ⋃ y ∈ F, bowenBall D.T n y (dyadicRadius p) ∧
      partitionCoverCost D.T D.φ w F n (dyadicRadius p) <
        2 * partitionSum D.T D.φ w Y n (dyadicRadius p) := by
  have hpos := exists_partitionSum_approximation_pos D w Y hY p hp n
  have hdouble : partitionSum D.T D.φ w Y n (dyadicRadius p) <
      2 * partitionSum D.T D.φ w Y n (dyadicRadius p) := by
    rw [two_mul]
    exact ENNReal.lt_add_right hfinite.ne hpos.ne'
  obtain ⟨F, hF⟩ := iInf_lt_iff.mp hdouble
  obtain ⟨hF_prop, hF_cost⟩ := iInf_lt_iff.mp hF
  exact ⟨F, hF_prop.1, hF_prop.2, hF_cost⟩

/-- If the rate of `q` has `limsup` below a real `a`, then eventually its rate is at most some
real `b < a`. -/
private lemma exists_eventually_pressureRate_le {q : ℕ → ℝ≥0∞} {a : ℝ}
    (h : limsup (pressureRate q) atTop < (a : EReal)) :
    ∃ (N : ℕ) (b : ℝ), (b : EReal) < (a : EReal) ∧ ∀ n ≥ N, pressureRate q n ≤ (b : EReal) := by
  obtain ⟨b, hb₁, hb₂⟩ := EReal.exists_between_coe_real h
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_lt_of_limsup_lt hb₁)
  exact ⟨N, b, hb₂, fun n hn => (hN n hn).le⟩

/-- Countable covers at all positive orders, with cost at most twice the partition sum from the
order `M` on and arbitrary (possibly infinite) cost before it. -/
private lemma exists_covers_cost_le_two_mul (D : PressureData X) (w : PressureWeight)
    (Y : Set X) (p : ℕ) (hp : D.p₀ ≤ p) (M : ℕ) (hM : 1 ≤ M)
    (h_finite : ∀ n ≥ M, partitionSum D.T D.φ w Y n (dyadicRadius p) < ⊤) :
    ∃ F : ℕ → Set X,
      (∀ n ≥ 1, (F n).Countable ∧ Y ⊆ ⋃ y ∈ F n, bowenBall D.T n y (dyadicRadius p)) ∧
      ∀ n ≥ M, partitionCoverCost D.T D.φ w (F n) n (dyadicRadius p) ≤
        2 * partitionSum D.T D.φ w Y n (dyadicRadius p) := by
  have hpos : 0 < dyadicRadius p := by
    unfold dyadicRadius
    positivity
  have hrange (n : ℕ) (hn : 1 ≤ n) :
      Y ⊆ ⋃ y ∈ Set.range D.presentation.ι, bowenBall D.T n y (dyadicRadius p) := by
    intro x _
    obtain ⟨i, hi⟩ := bowen_geometry_dense D n hn x (dyadicRadius p) hpos
    have h_mem : D.presentation.ι i ∈ bowenBall D.T n x (dyadicRadius p) :=
      (bowen_ball_dense_iff D.T n hn x (D.presentation.ι i) (dyadicRadius p)).mpr hi
    have hsymm := bowen_geometry_symm D n hn x (D.presentation.ι i) (dyadicRadius p)
    simp only [Set.mem_iUnion, exists_prop]
    exact ⟨D.presentation.ι i, ⟨i, rfl⟩, hsymm.mp h_mem⟩
  have H : ∀ n : ℕ, ∃ F : Set X,
      (1 ≤ n → F.Countable ∧ Y ⊆ ⋃ y ∈ F, bowenBall D.T n y (dyadicRadius p)) ∧
      (M ≤ n → partitionCoverCost D.T D.φ w F n (dyadicRadius p) ≤
        2 * partitionSum D.T D.φ w Y n (dyadicRadius p)) := by
    intro n
    by_cases hn : 1 ≤ n
    · by_cases hMn : M ≤ n
      · rcases Y.eq_empty_or_nonempty with rfl | hY
        · exact ⟨∅, fun _ => ⟨Set.countable_empty, Set.empty_subset _⟩,
            fun _ => by simp [partitionCoverCost]⟩
        · obtain ⟨F, hF_count, hF_cov, hF_cost⟩ :=
            exists_partitionSum_approximation D w Y hY p hp n (h_finite n hMn)
          exact ⟨F, fun _ => ⟨hF_count, hF_cov⟩, fun _ => hF_cost.le⟩
      · exact ⟨Set.range D.presentation.ι, fun _ => ⟨Set.countable_range _, hrange n hn⟩,
          fun h => absurd h hMn⟩
    · exact ⟨∅, fun h => absurd h hn, fun h => absurd (hM.trans h) hn⟩
  choose F hF using H
  exact ⟨F, fun n hn => (hF n).1 hn, fun n hn => (hF n).2 hn⟩

/-- If the partition sums have rate at most `b < a` from the order `M` on, and the costs of the
covers `F n` are at most twice the partition sums from `M` on, then the cost rates have `limsup`
below `a`: the factor two only adds `1 / n` to the rate. -/
private lemma limsup_pressureRate_cost_lt (D : PressureData X) (w : PressureWeight)
    (Y : Set X) (p : ℕ) (a b : ℝ) (M : ℕ) (hM : 1 ≤ M) (F : ℕ → Set X)
    (hF_cost : ∀ n ≥ M, partitionCoverCost D.T D.φ w (F n) n (dyadicRadius p) ≤
      2 * partitionSum D.T D.φ w Y n (dyadicRadius p))
    (hb : (b : EReal) < (a : EReal))
    (hN : ∀ n ≥ M, pressureRate (fun n => partitionSum D.T D.φ w Y n (dyadicRadius p)) n ≤
      (b : EReal)) :
    limsup (pressureRate (fun n => partitionCoverCost D.T D.φ w (F n) n
      (dyadicRadius p))) atTop < (a : EReal) := by
  obtain ⟨c, hbc_ereal, hca_ereal⟩ := EReal.exists_between_coe_real hb
  have hbc : b < c := EReal.coe_lt_coe_iff.mp hbc_ereal
  have H_ev : ∀ᶠ n : ℕ in atTop, 1 / (n : ℝ) < c - b :=
    (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).eventually (gt_mem_nhds (sub_pos.mpr hbc))
  have H_main : ∀ᶠ n : ℕ in atTop,
      pressureRate (fun n => partitionCoverCost D.T D.φ w (F n) n (dyadicRadius p)) n ≤
        (c : EReal) := by
    filter_upwards [H_ev, eventually_ge_atTop M] with n hn_diff hn_ge
    have hn1 : 1 ≤ n := hM.trans hn_ge
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have h_cost : partitionCoverCost D.T D.φ w (F n) n (dyadicRadius p) ≤
        partitionSum D.T D.φ w Y n (dyadicRadius p) * (2 : ℝ≥0∞) ^ ((n : ℝ) * (n : ℝ)⁻¹) := by
      rw [mul_inv_cancel₀ hn0, ENNReal.rpow_one, mul_comm]
      exact hF_cost n hn_ge
    calc
      _ ≤ pressureRate (fun n => partitionSum D.T D.φ w Y n (dyadicRadius p)) n +
            (((n : ℝ)⁻¹ : ℝ) : EReal) :=
        pressureRate_le_add_of_le_mul _ _ _ n hn1 h_cost
      _ ≤ (b : EReal) + ((c - b : ℝ) : EReal) := by
        gcongr
        · exact hN n hn_ge
        · simpa only [one_div] using hn_diff.le
      _ = (c : EReal) := by
        rw [← EReal.coe_add]
        congr 1
        ring
  exact lt_of_le_of_lt (limsup_le_of_le (by isBoundedDefault) H_main) hca_ereal

/-- Countable covering families can be chosen at every positive order while preserving a strict
upper rate bound; finitely many early costs may be infinite.
Blueprint node `pressure:partition-approx`. -/
theorem exists_partitionSum_approximation_rate (D : PressureData X) (w : PressureWeight)
    (Y : Set X) (p : ℕ) (hp : D.p₀ ≤ p) (a : ℝ)
    (ha : upperCapacity D.T D.φ w Y (dyadicRadius p) < (a : EReal)) :
    ∃ F : ℕ → Set X,
      (∀ n ≥ 1, (F n).Countable ∧ Y ⊆ ⋃ y ∈ F n, bowenBall D.T n y (dyadicRadius p)) ∧
      limsup (pressureRate (fun n => partitionCoverCost D.T D.φ w (F n) n
        (dyadicRadius p))) atTop < (a : EReal) := by
  obtain ⟨N, b, hb, hN⟩ := exists_eventually_pressureRate_le ha
  have hN' : ∀ n ≥ max 1 N,
      pressureRate (fun n => partitionSum D.T D.φ w Y n (dyadicRadius p)) n ≤ (b : EReal) :=
    fun n hn => hN n ((le_max_right 1 N).trans hn)
  have h_finite : ∀ n ≥ max 1 N, partitionSum D.T D.φ w Y n (dyadicRadius p) < ⊤ :=
    fun n hn => lt_top_of_pressureRate_le ((le_max_left 1 N).trans hn) (hN' n hn)
  obtain ⟨F, hF_covers, hF_cost⟩ :=
    exists_covers_cost_le_two_mul D w Y p hp (max 1 N) (le_max_left 1 N) h_finite
  exact ⟨F, hF_covers,
    limsup_pressureRate_cost_lt D w Y p a b (max 1 N) (le_max_left 1 N) F hF_cost hb hN'⟩

end Kolmogorov.PointToSet
