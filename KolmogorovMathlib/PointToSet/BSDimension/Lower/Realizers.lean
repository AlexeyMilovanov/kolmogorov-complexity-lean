/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.BSDimension.Defs
import KolmogorovMathlib.PointToSet.Order
import KolmogorovMathlib.Oracle.KraftChaitin
import KolmogorovMathlib.Oracle.PrefixComplexity
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Topology.Order.OrderClosed

/-!
# Ideal realizers and lower covering masses

This module collects the analytic facts about ideal realizers of Bowen balls and about the
lower Barreira–Schmeling covering masses that the lower point-to-set principle for the
Barreira–Schmeling dimension is built on.

* Realizers: Birkhoff sums over a Bowen ball differ from the sum at its center by at most the
  oscillation of the potential times the order (`birkhoffSum_le_add_of_mem_bowenBall`).  Hence
  on the good tail of a point with positive lower average, every ideal point in the ball is a
  positive realizer (`birkhoffRealizerBounds`, `birkhoffRealizerBounds_positive`, blueprint
  node `bs:realizer-bounds`), the sets of uniform tail bounds exhaust a set of positive lower
  average (`positiveAverageExhaustion`, `bs:exhaustion`) and the infimum of the normalized
  complexity is attained (`idealRealizerInfimumAttained`,
  `idealRealizerInfimumAttained_affine`, `bs:attainment`).
* Pointwise dimension: the cost `finiteScaleBSCost` is antitone in the radius, so the scale
  limits may be taken along any dyadic tail or along any sequence of radii tending to zero
  (`pointwiseBSDimension_eq_tail`, `pointwiseBSDimension_eq_good_radii`), and the positivity
  filter is immaterial on a positive tail (`pointwiseBSDimension_eq_unfiltered_tail`;
  blueprint node `bs:pointwise`).
* Lower mass: the sup-weight of a Bowen ball is the exponential of its finite Birkhoff
  supremum (`lowerBSMass_weight`), and the lower masses are monotone in the order cutoff and
  antitone in the radius, which gives the limit statements
  `lowerBSMass_cutoff_limit`, `lowerBSMass_antitone_radius_limit` and
  `lowerBSMass_antitone_radius_dimension` (blueprint node `bs:lower-mass`).

The neighbouring modules of `KolmogorovMathlib.PointToSet.BSDimension.Lower` use these facts
to prove the null-cover characterization and the effective bounds on the lower dimension.
-/

namespace Kolmogorov.PointToSet

open Filter
open scoped Topology ENNReal Computability

variable {X : Type*} [MetricSpace X]

/-- A uniformly continuous function oscillates by at most `ε` on balls of some dyadic radius. -/
private lemma exists_dyadicRadius_oscillation_le {u : X → ℝ} (hu : UniformContinuous u)
    {ε : ℝ} (hε : 0 < ε) : ∃ p, ∀ y z, dist y z < dyadicRadius p → |u y - u z| ≤ ε := by
  obtain ⟨δ, hδ, hδu⟩ := Metric.uniformContinuous_iff.1 hu ε hε
  obtain ⟨p, hp⟩ := exists_dyadicRadius_lt hδ
  exact ⟨p, fun y z h ↦ (hδu (h.trans hp)).le⟩

/-- If `u` oscillates by at most `ω` on `r`-balls, then the Birkhoff sums over a Bowen ball
of radius `r` and order `n` differ from the sum at its center by at most `n * ω`.
Blueprint node `bs:realizer-bounds`. -/
theorem abs_birkhoffSum_sub_le_of_mem_bowenBall (T : X → X) (u : X → ℝ) {x y : X} {n : ℕ}
    {r ω : ℝ} (hω : ∀ y z, dist y z < r → |u y - u z| ≤ ω) (hy : y ∈ bowenBall T n x r) :
    |birkhoffSum T u n y - birkhoffSum T u n x| ≤ n * ω := by
  rw [birkhoffSum, birkhoffSum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ k ∈ Finset.range n, |u (T^[k] y) - u (T^[k] x)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range n, ω := Finset.sum_le_sum fun k hk ↦ by
      rw [Finset.mem_range] at hk
      exact hω _ _ (by rw [dist_comm]; exact mem_bowenBall_iff.1 hy k hk)
    _ = n * ω := by simp

/-- Upper bound for the Birkhoff sum over a Bowen ball in terms of the sum at its center.
Blueprint node `bs:realizer-bounds`. -/
theorem birkhoffSum_le_add_of_mem_bowenBall (T : X → X) (u : X → ℝ) {x y : X} {n : ℕ}
    {r ω : ℝ} (hω : ∀ y z, dist y z < r → |u y - u z| ≤ ω) (hy : y ∈ bowenBall T n x r) :
    birkhoffSum T u n y ≤ birkhoffSum T u n x + n * ω := by
  linarith [le_of_abs_le (abs_birkhoffSum_sub_le_of_mem_bowenBall T u hω hy)]

omit [MetricSpace X] in
/-- A rational `ρ > 0` below a positive lower Birkhoff average. -/
private lemma exists_rat_pos_lt_lowerBirkhoffAverage {T : X → X} {u : X → ℝ} {x : X}
    (hx : 0 < lowerBirkhoffAverage T u x) :
    ∃ ρ : ℚ, 0 < ρ ∧ ((ρ : ℝ) : EReal) < lowerBirkhoffAverage T u x := by
  have h₀ : ((0 : ℝ) : EReal) < lowerBirkhoffAverage T u x := by rwa [EReal.coe_zero]
  obtain ⟨r, h₁, h₂⟩ := EReal.exists_between_coe_real h₀
  obtain ⟨ρ, hρ₁, hρ₂⟩ := exists_rat_btwn (EReal.coe_lt_coe_iff.1 h₁)
  exact ⟨ρ, by exact_mod_cast hρ₁, (EReal.coe_lt_coe_iff.2 hρ₂).trans h₂⟩

omit [MetricSpace X] in
/-- A real number below the lower Birkhoff average bounds the averages from below eventually. -/
private lemma eventually_le_birkhoffSum_div {T : X → X} {u : X → ℝ} {x : X} {c : ℝ}
    (hc : (c : EReal) < lowerBirkhoffAverage T u x) :
    ∀ᶠ n : ℕ in atTop, c ≤ birkhoffSum T u n x / n := by
  unfold lowerBirkhoffAverage at hc
  filter_upwards [eventually_lt_of_lt_liminf hc
    (isBoundedUnder_of ⟨⊥, fun _ ↦ bot_le⟩)] with n hn
  exact (EReal.coe_lt_coe_iff.1 hn).le

omit [MetricSpace X] in
/-- A real number above the upper Birkhoff average bounds the averages from above
eventually. -/
private lemma eventually_birkhoffSum_div_le {T : X → X} {u : X → ℝ} {x : X} {c : ℝ}
    (hc : upperBirkhoffAverage T u x < (c : EReal)) :
    ∀ᶠ n : ℕ in atTop, birkhoffSum T u n x / n ≤ c := by
  unfold upperBirkhoffAverage at hc
  filter_upwards [eventually_lt_of_limsup_lt hc
    (isBoundedUnder_of ⟨⊤, fun _ ↦ le_top⟩)] with n hn
  exact (EReal.coe_lt_coe_iff.1 hn).le

omit [MetricSpace X] in
/-- Positive lower averages give a countable exhaustion by rational uniform tail bounds.
Blueprint node `bs:exhaustion`. -/
theorem positiveAverageExhaustion (T : X → X) (u : X → ℝ) (Z : Set X)
    (hZ : ∀ x ∈ Z, 0 < lowerBirkhoffAverage T u x) :
    Z = ⋃ N : ℕ, ⋃ (_ : 1 ≤ N), ⋃ ρ : ℚ, ⋃ (_ : 0 < ρ),
      positiveAveragePiece T u Z N ρ := by
  ext x
  simp only [Set.mem_iUnion]
  refine ⟨fun hx ↦ ?_, fun ⟨_, _, _, _, hx⟩ ↦ hx.1⟩
  obtain ⟨ρ, hρ, hlt⟩ := exists_rat_pos_lt_lowerBirkhoffAverage (hZ x hx)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (eventually_le_birkhoffSum_div hlt)
  refine ⟨max N₀ 1, le_max_right _ _, ρ, hρ, hx, fun n hn ↦ ?_⟩
  have hn_pos : (0 : ℝ) < n :=
    Nat.cast_pos.2 (lt_of_lt_of_le one_pos ((le_max_right _ _).trans hn))
  exact (le_div_iff₀ hn_pos).1 (hN₀ n ((le_max_left _ _).trans hn))

/-- Every ideal realizer has the two-sided average bounds at all sufficiently small
positive radii and all sufficiently large orders. Blueprint node `bs:realizer-bounds`. -/
theorem birkhoffRealizerBounds (P : Presentation X) (T : X → X) (u : X → ℝ)
    (hu : UniformContinuous u) (x : X) (ℓ b : ℝ) (hlower : lowerBirkhoffAverage T u x = (ℓ : EReal))
    (hupper : upperBirkhoffAverage T u x = (b : EReal)) (η : ℝ) (hη : 0 < η) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r ≤ r₀ →
      ∃ N : ℕ, 1 ≤ N ∧ ∀ n ≥ N, ∀ i, P.ι i ∈ bowenBall T n x r →
        ℓ - η ≤ birkhoffSum T u n (P.ι i) / n ∧
          birkhoffSum T u n (P.ι i) / n ≤ b + η := by
  obtain ⟨p, hp⟩ := exists_dyadicRadius_oscillation_le hu (half_pos hη)
  refine ⟨dyadicRadius p, dyadicRadius_pos p, fun r _ hr ↦ ?_⟩
  have h_lower : ((ℓ - η / 2 : ℝ) : EReal) < lowerBirkhoffAverage T u x := by
    rw [hlower]
    exact EReal.coe_lt_coe_iff.2 (by linarith)
  have h_upper : upperBirkhoffAverage T u x < ((b + η / 2 : ℝ) : EReal) := by
    rw [hupper]
    exact EReal.coe_lt_coe_iff.2 (by linarith)
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((eventually_ge_atTop 1).and
    ((eventually_le_birkhoffSum_div h_lower).and (eventually_birkhoffSum_div_le h_upper)))
  refine ⟨N, (hN N le_rfl).1, fun n hn i hi ↦ ?_⟩
  obtain ⟨hn₁, hlow, hup⟩ := hN n hn
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.2 hn₁
  have habs := abs_birkhoffSum_sub_le_of_mem_bowenBall T u
    (fun y z h ↦ hp y z (h.trans_le hr)) hi
  have hdiv : |birkhoffSum T u n (P.ι i) / n - birkhoffSum T u n x / n| ≤ η / 2 := by
    rw [← sub_div, abs_div, abs_of_pos hn_pos, div_le_iff₀ hn_pos]
    linarith
  obtain ⟨h₁, h₂⟩ := abs_le.1 hdiv
  constructor <;> linarith

/-- Positive lower average alone supplies a rational positive bound for every realizer
on arbitrarily small radii and an eventual tail. Blueprint node `bs:realizer-bounds`. -/
theorem birkhoffRealizerBounds_positive (P : Presentation X) (T : X → X) (u : X → ℝ)
    (hu : UniformContinuous u) (x : X)
    (hx : 0 < lowerBirkhoffAverage T u x) :
    ∃ ρ : ℚ, 0 < ρ ∧ ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r ≤ r₀ →
      ∃ N : ℕ, 1 ≤ N ∧ ∀ n ≥ N, ∀ i, P.ι i ∈ bowenBall T n x r →
        (ρ : ℝ) * n ≤ birkhoffSum T u n (P.ι i) ∧
          0 < birkhoffSum T u n (P.ι i) := by
  obtain ⟨ρ, hρ, hlt⟩ := exists_rat_pos_lt_lowerBirkhoffAverage hx
  have hρ_real : (0 : ℝ) < ρ := Rat.cast_pos.2 hρ
  obtain ⟨p, hp⟩ := exists_dyadicRadius_oscillation_le hu (half_pos hρ_real)
  refine ⟨ρ / 2, half_pos hρ, dyadicRadius p, dyadicRadius_pos p, fun r _ hr ↦ ?_⟩
  obtain ⟨N, hN⟩ := eventually_atTop.1
    ((eventually_ge_atTop 1).and (eventually_le_birkhoffSum_div hlt))
  refine ⟨N, (hN N le_rfl).1, fun n hn i hi ↦ ?_⟩
  obtain ⟨hn₁, hlow⟩ := hN n hn
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.2 hn₁
  have habs := abs_birkhoffSum_sub_le_of_mem_bowenBall T u
    (fun y z h ↦ hp y z (h.trans_le hr)) hi
  have hx_bound : (ρ : ℝ) * n ≤ birkhoffSum T u n x := (le_div_iff₀ hn_pos).1 hlow
  have hbound : ((ρ / 2 : ℚ) : ℝ) * n ≤ birkhoffSum T u n (P.ι i) := by
    push_cast
    linarith [(abs_le.1 habs).1]
  exact ⟨hbound, lt_of_lt_of_le (mul_pos (Rat.cast_pos.2 (half_pos hρ)) hn_pos) hbound⟩

/-- Restricting a supremum of a monotone sequence to a tail does not change it. -/
private lemma iSup_eq_iSup_ge_of_monotone {α : Type*} [CompleteLattice α] {f : ℕ → α}
    (hf : Monotone f) (p₀ : ℕ) : ⨆ p, f p = ⨆ p, ⨆ (_ : p₀ ≤ p), f p := by
  refine le_antisymm (iSup_le fun p ↦ ?_) (iSup₂_le fun p _ ↦ le_iSup f p)
  rcases le_total p₀ p with h | h
  · exact le_iSup₂_of_le p h le_rfl
  · exact (hf h).trans (le_iSup₂_of_le p₀ le_rfl le_rfl)

/-- The lower or upper time limit of the BS cost is antitone in the radius. -/
private lemma antitone_timeLimit_finiteScaleBSCost (P : Presentation X) (T : X → X)
    (u : X → ℝ) (A : Set ℕ) (x : X) (σ : LimitSide) :
    Antitone fun r ↦ σ.timeLimit (fun n ↦ finiteScaleBSCost P T u A x n r) := by
  intro r₁ r₂ hr
  have h := fun n ↦ pointwiseBSDimension_antitone_radius P T u A x n hr
  cases σ
  · exact liminf_le_liminf (Eventually.of_forall h)
  · exact limsup_le_limsup (Eventually.of_forall h)

/-- Any dyadic tail gives the frozen lower or upper pointwise dimension.
Blueprint node `bs:pointwise`. -/
theorem pointwiseBSDimension_eq_tail (P : Presentation X) (T : X → X) (u : X → ℝ)
    (A : Set ℕ) (x : X) (σ : LimitSide) (p₀ : ℕ) :
    σ.choose (pointwiseBSDimension P T u A x) =
      ⨆ p : ℕ, ⨆ (_ : p₀ ≤ p),
        σ.timeLimit (fun n => finiteScaleBSCost P T u A x n (dyadicRadius p)) := by
  have hmono := (antitone_timeLimit_finiteScaleBSCost P T u A x σ).comp
    dyadicRadius_antitone
  unfold pointwiseBSDimension
  cases σ
  · exact iSup_eq_iSup_ge_of_monotone hmono p₀
  · exact iSup_eq_iSup_ge_of_monotone hmono p₀

/-- Any positive radii tending to zero recover the same pointwise scale limit.
Blueprint node `bs:pointwise`. -/
theorem pointwiseBSDimension_eq_good_radii (P : Presentation X) (T : X → X)
    (u : X → ℝ) (A : Set ℕ) (x : X) (σ : LimitSide) (r : ℕ → ℝ)
    (hr : ∀ p, 0 < r p) (hrzero : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun p => σ.timeLimit (fun n => finiteScaleBSCost P T u A x n (r p)))
      atTop (𝓝 (σ.choose (pointwiseBSDimension P T u A x))) := by
  set F := fun r ↦ σ.timeLimit (fun n ↦ finiteScaleBSCost P T u A x n r) with hF_def
  have hF : Antitone F := antitone_timeLimit_finiteScaleBSCost P T u A x σ
  have hL : σ.choose (pointwiseBSDimension P T u A x) = sSup (F '' Set.Ioi 0) := by
    rw [pointwiseBSDimension_eq_tail P T u A x σ 0]
    refine le_antisymm (iSup₂_le fun p _ ↦ le_sSup ⟨_, dyadicRadius_pos p, rfl⟩)
      (sSup_le ?_)
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨p, hp⟩ := exists_dyadicRadius_lt hs
    exact (hF hp.le).trans (le_iSup₂_of_le p (Nat.zero_le p) le_rfl)
  have h_r_tendsto : Tendsto r atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hrzero (Eventually.of_forall hr)
  rw [hL]
  exact (hF.tendsto_nhdsGT 0).comp h_r_tendsto

/-- On a positive realizer tail, the positive filter removes no candidates; discarding
the finite prefix preserves either time limit. Blueprint node `bs:pointwise`. -/
theorem pointwiseBSDimension_eq_unfiltered_tail (P : Presentation X) (T : X → X)
    (u : X → ℝ) (A : Set ℕ) (x : X) (r : ℝ) (σ : LimitSide)
    (hpos : ∀ᶠ n in atTop, ∀ i, P.ι i ∈ bowenBall T n x r →
      0 < birkhoffSum T u n (P.ι i)) :
    σ.timeLimit (fun n => finiteScaleBSCost P T u A x n r) =
      σ.timeLimit (fun n => ⨅ i : ℕ, ⨅ (_ : P.ι i ∈ bowenBall T n x r),
        (oracleNatComplexity A i : ℝ≥0∞) /
          ENNReal.ofReal (birkhoffSum T u n (P.ι i))) := by
  have h_eq : ∀ᶠ n in atTop, finiteScaleBSCost P T u A x n r =
      ⨅ i : ℕ, ⨅ (_ : P.ι i ∈ bowenBall T n x r),
        (oracleNatComplexity A i : ℝ≥0∞) / ENNReal.ofReal (birkhoffSum T u n (P.ι i)) := by
    filter_upwards [hpos, eventually_ne_atTop 0] with n hn hne
    unfold finiteScaleBSCost
    rw [ite_eq_right_iff.2 fun h ↦ (hne h).elim]
    exact iInf_congr fun i ↦ iInf_congr fun h ↦ iInf_pos (hn i h)
  cases σ
  · exact liminf_congr h_eq
  · exact limsup_congr h_eq

/-- At every sufficiently small positive radius the ratio infimum is attained on the
eventual positive-average tail. Blueprint node `bs:attainment`. -/
theorem idealRealizerInfimumAttained (P : Presentation X) (T : X → X)
    (hT : Continuous T) (u : X → ℝ) (hu : UniformContinuous u) (A : Set ℕ)
    (x : X) (hx : 0 < lowerBirkhoffAverage T u x) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r ≤ r₀ →
      ∃ N : ℕ, 1 ≤ N ∧ ∀ n ≥ N, ∃ i, P.ι i ∈ bowenBall T n x r ∧
        0 < birkhoffSum T u n (P.ι i) ∧ finiteScaleBSCost P T u A x n r =
          (oracleNatComplexity A i : ℝ≥0∞) /
            ENNReal.ofReal (birkhoffSum T u n (P.ι i)) := by
  obtain ⟨ρ, hρ, r₁, hr₁, hbound⟩ := birkhoffRealizerBounds_positive P T u hu x hx
  obtain ⟨p, hp⟩ := exists_dyadicRadius_oscillation_le hu one_pos
  refine ⟨min r₁ (dyadicRadius p), lt_min hr₁ (dyadicRadius_pos p), fun r hr hr_le ↦ ?_⟩
  obtain ⟨N, hN, hN_bound⟩ := hbound r hr (hr_le.trans (min_le_left _ _))
  refine ⟨N, hN, fun n hn ↦ ?_⟩
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.2 (hN.trans hn)
  have hω : ∀ y z, dist y z < r → |u y - u z| ≤ 1 := fun y z h ↦
    hp y z (h.trans_le (hr_le.trans (min_le_right _ _)))
  obtain ⟨i, hi, h_eq⟩ := finite_scale_min_attained_ratio P T hT u A x n (hN.trans hn) r hr
    ((ρ : ℝ) * n) (birkhoffSum T u n x + n * 1) (mul_pos (Rat.cast_pos.2 hρ) hn_pos)
    fun i hi ↦ ⟨(hN_bound n hn i hi).1, birkhoffSum_le_add_of_mem_bowenBall T u hω hi⟩
  exact ⟨i, hi, (hN_bound n hn i hi).2, h_eq⟩

/-- Two-sided realizer average bounds give attainment of each affine normalized cost.
Blueprint node `bs:attainment`. -/
theorem idealRealizerInfimumAttained_affine (P : Presentation X) (T : X → X) (hT : Continuous T)
    (u : X → ℝ) (A : Set ℕ) (x : X) (r : ℝ) (hr : 0 < r) (n : ℕ) (hn : 1 ≤ n) (a b : ℝ) (ha : 0 < a)
    (hbounds : ∀ i, P.ι i ∈ bowenBall T n x r →
      a ≤ birkhoffSum T u n (P.ι i) / n ∧ birkhoffSum T u n (P.ι i) / n ≤ b)
    (s : ℝ) :
    ∃ i, P.ι i ∈ bowenBall T n x r ∧
      finiteScalePressureRate P T (fun y => -s * u y) A x n r =
        (((oracleNatComplexity A i - s * birkhoffSum T u n (P.ι i)) / n : ℝ) : EReal) := by
  classical
  have hn0 : n ≠ 0 := by omega
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  obtain ⟨i₀, hi₀⟩ := bowen_ball_dense P T hT x n hn r hr
  let f : ℕ → ℝ := fun i =>
    (oracleNatComplexity A i - s * birkhoffSum T u n (P.ι i)) / n
  have hrate : finiteScalePressureRate P T (fun y => -s * u y) A x n r =
      ⨅ i : ℕ, ⨅ (_ : P.ι i ∈ bowenBall T n x r), (f i : EReal) := by
    unfold finiteScalePressureRate
    rw [ite_eq_right hn0]
    apply iInf_congr
    intro i
    have hsum : birkhoffSum T (fun y => -s * u y) n (P.ι i) =
        -s * birkhoffSum T u n (P.ι i) := by
      simp only [birkhoffSum, Finset.mul_sum]
    rw [hsum]
    simp only [f, neg_mul, sub_eq_add_neg]
  let S : Set ℕ := {i | P.ι i ∈ bowenBall T n x r ∧ f i ≤ f i₀}
  -- Every candidate improving the initial cost has bounded complexity.
  obtain ⟨N, hN⟩ := exists_nat_ge (f i₀ * n + |s| * (b * n))
  have hfinite : S.Finite := by
    apply (oracle_kraft_finite_sublevels A N).subset
    intro i hi
    obtain ⟨hlower, hupper⟩ := hbounds i hi.1
    have hsum_nonneg : 0 ≤ birkhoffSum T u n (P.ι i) := by
      have hlow := (le_div_iff₀ hnpos).mp hlower
      exact (mul_pos ha hnpos).le.trans hlow
    have hsum_upper : birkhoffSum T u n (P.ι i) ≤ b * n :=
      (div_le_iff₀ hnpos).mp hupper
    have hweight : s * birkhoffSum T u n (P.ι i) ≤ |s| * (b * n) :=
      (mul_le_mul_of_nonneg_right (le_abs_self s) hsum_nonneg).trans
        (mul_le_mul_of_nonneg_left hsum_upper (abs_nonneg s))
    have hcost : (oracleNatComplexity A i : ℝ) -
        s * birkhoffSum T u n (P.ι i) ≤ f i₀ * n :=
      (div_le_iff₀ hnpos).mp hi.2
    have hcomplexity : (oracleNatComplexity A i : ℝ) ≤ N := by linarith
    exact Nat.cast_le.mp hcomplexity
  have hi₀S : i₀ ∈ S := ⟨hi₀, le_rfl⟩
  obtain ⟨i, hi, hmin⟩ := Set.exists_min_image S f hfinite ⟨i₀, hi₀S⟩
  have hglobal : ∀ j, P.ι j ∈ bowenBall T n x r → f i ≤ f j := by
    intro j hj
    by_cases hcost : f j ≤ f i₀
    · exact hmin j ⟨hj, hcost⟩
    · exact hi.2.trans (le_of_lt (lt_of_not_ge hcost))
  refine ⟨i, hi.1, ?_⟩
  change finiteScalePressureRate P T (fun y => -s * u y) A x n r = (f i : EReal)
  rw [hrate]
  exact le_antisymm (iInf₂_le i hi.1)
    (le_iInf₂ fun j hj => EReal.coe_le_coe_iff.mpr (hglobal j hj))

/-- Every point of a Bowen ball has Birkhoff sum at most a finite Birkhoff supremum over
the ball. -/
private lemma birkhoffSum_le_of_bowenPotentialSup_eq
    {T : X → X} {u : X → ℝ} {n : ℕ} {y : X} {r w : ℝ}
    (hw : bowenPotentialSup T u n y r = (w : EReal)) :
    ∀ z ∈ bowenBall T n y r, birkhoffSum T u n z ≤ w := fun z hz ↦ by
  apply EReal.coe_le_coe_iff.mp
  rw [← hw]
  exact le_iSup₂ (f := fun z _ ↦ ((birkhoffSum T u n z : ℝ) : EReal)) z hz

/-- Every real number below a finite Birkhoff supremum is exceeded by the Birkhoff sum of
some point of the ball. -/
private lemma exists_lt_birkhoffSum_of_bowenPotentialSup_eq
    {T : X → X} {u : X → ℝ} {n : ℕ} {y : X} {r w : ℝ}
    (hw : bowenPotentialSup T u n y r = (w : EReal)) {a : ℝ} (ha : a < w) :
    ∃ z ∈ bowenBall T n y r, a < birkhoffSum T u n z := by
  have h : (a : EReal) < bowenPotentialSup T u n y r := by
    rw [hw]
    exact EReal.coe_lt_coe_iff.mpr ha
  unfold bowenPotentialSup at h
  obtain ⟨z, hz⟩ := lt_iSup_iff.mp h
  obtain ⟨hz_mem, haz⟩ := lt_iSup_iff.mp hz
  exact ⟨z, hz_mem, EReal.coe_lt_coe_iff.mp haz⟩

/-- An upper bound for `2 ^ a` at all `a < w` is also an upper bound at `w`, by continuity
of the extended exponential. -/
private lemma two_rpow_le_of_forall_lt {w : ℝ} {b : ℝ≥0∞}
    (h : ∀ a : ℝ, a < w → (2 : ℝ≥0∞) ^ a ≤ b) : (2 : ℝ≥0∞) ^ w ≤ b := by
  have hcont : Continuous fun a : ℝ ↦ (2 : ℝ≥0∞) ^ a := by
    have h_eq : (fun a : ℝ ↦ (2 : ℝ≥0∞) ^ a) = fun a ↦ ENNReal.ofReal ((2 : ℝ) ^ a) := by
      ext a
      rw [← ENNReal.ofReal_rpow_of_pos two_pos, ENNReal.ofReal_ofNat]
    rw [h_eq]
    exact ENNReal.continuous_ofReal.comp (Real.continuous_const_rpow two_ne_zero)
  have h_lim : Tendsto (fun a : ℝ ↦ (2 : ℝ≥0∞) ^ a) (𝓝[<] w) (𝓝 ((2 : ℝ≥0∞) ^ w)) :=
    (hcont.tendsto w).mono_left inf_le_left
  exact le_of_tendsto h_lim (eventually_nhdsWithin_iff.2 (Eventually.of_forall h))

/-- At a finite Birkhoff supremum the reused exponential weight has the blueprint's
literal BS formula. Blueprint node `bs:lower-mass`. -/
theorem lowerBSMass_weight (T : X → X) (u : X → ℝ) (s : ℝ) (n : ℕ)
    (y : X) (r w : ℝ) (hw : bowenPotentialSup T u n y r = (w : EReal)) :
    bsBallWeight T u s n y r = (2 : ℝ≥0∞) ^ (-s * w) := by
  have hW : pressureBallWeight T u .supremum n y r = (2 : ℝ≥0∞) ^ w := by
    apply le_antisymm
    · change (⨆ z ∈ bowenBall T n y r, (2 : ℝ≥0∞) ^ (birkhoffSum T u n z : ℝ)) ≤ _
      exact iSup₂_le fun z hz ↦ ENNReal.rpow_le_rpow_of_exponent_le (by norm_num)
        (birkhoffSum_le_of_bowenPotentialSup_eq hw z hz)
    · refine two_rpow_le_of_forall_lt fun a ha ↦ ?_
      obtain ⟨z, hz, haz⟩ := exists_lt_birkhoffSum_of_bowenPotentialSup_eq hw ha
      exact le_iSup₂_of_le z hz (ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) haz.le)
  unfold bsBallWeight
  rw [hW, ← ENNReal.rpow_mul]
  congr 1
  ring

/-- Lower cutoff masses increase as the cutoff increases.
Blueprint node `bs:lower-mass`. -/
theorem lowerBSMass_mono_cutoff (T : X → X) (u : X → ℝ) (Z : Set X) (s r : ℝ) :
    Monotone (lowerBSMass T u Z s r) := fun _ _ hN ↦
  iInf_mono fun _ ↦ iInf_mono' fun hC ↦
    ⟨⟨fun j ↦ (max_le_max le_rfl hN).trans (hC.1 j), hC.2⟩, le_rfl⟩

/-- Smaller radii increase lower cutoff mass at every nonnegative exponent.
Blueprint node `bs:lower-mass`. -/
theorem lowerBSMass_antitone_radius (T : X → X) (u : X → ℝ) (Z : Set X)
    (s : ℝ) (hs : 0 ≤ s) (N : ℕ) :
    AntitoneOn (fun r => lowerBSMass T u Z s r N) (Set.Ioi 0) := by
  intro r₁ _ r₂ _ hr
  refine iInf_mono fun C ↦ iInf_mono' fun hC ↦ ⟨⟨hC.1, fun x hx ↦ ?_⟩, ?_⟩
  · obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (hC.2 hx)
    exact Set.mem_iUnion.2 ⟨j, bowenBall_subset_of_le T _ _ hr hj⟩
  · refine ENNReal.tsum_le_tsum fun j ↦ ?_
    have h_sup : pressureBallWeight T u .supremum (C.order j) (C.center j) r₁ ≤
        pressureBallWeight T u .supremum (C.order j) (C.center j) r₂ := by
      unfold pressureBallWeight
      exact iSup_mono fun z ↦ iSup_mono' fun h ↦
        ⟨bowenBall_subset_of_le T _ _ hr h, le_rfl⟩
    unfold bsBallWeight
    rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
    exact ENNReal.inv_le_inv.2 (ENNReal.rpow_le_rpow h_sup hs)

/-- Smaller radii increase limiting lower mass at every nonnegative exponent.
Blueprint node `bs:lower-mass`. -/
theorem lowerBSMass_antitone_radius_limit (T : X → X) (u : X → ℝ) (Z : Set X)
    (s : ℝ) (hs : 0 ≤ s) :
    AntitoneOn (lowerBSMassLimit T u Z s) (Set.Ioi 0) := by
  intro r₁ hr₁ r₂ hr₂ h_le
  exact iSup_mono fun N ↦ iSup_mono fun _ ↦
    lowerBSMass_antitone_radius T u Z s hs N hr₁ hr₂ h_le

/-- Smaller radii increase the lower critical dimension at one radius.
Blueprint node `bs:lower-mass`. -/
theorem lowerBSMass_antitone_radius_dimension (T : X → X) (u : X → ℝ) (Z : Set X) :
    AntitoneOn (lowerBSDimensionAt T u Z) (Set.Ioi 0) := by
  intro r₁ hr₁ r₂ hr₂ h
  unfold lowerBSDimensionAt
  refine iInf_mono fun s ↦ iInf_mono fun hs ↦ iInf_mono' fun h₀ ↦ ⟨?_, le_rfl⟩
  exact le_zero_iff.1
    ((lowerBSMass_antitone_radius_limit T u Z s hs hr₁ hr₂ h).trans_eq h₀)

/-- The cutoff supremum is the increasing limit of lower masses.
Blueprint node `bs:lower-mass`. -/
theorem lowerBSMass_cutoff_limit (T : X → X) (u : X → ℝ) (Z : Set X) (s r : ℝ) :
    Tendsto (lowerBSMass T u Z s r) atTop (𝓝 (lowerBSMassLimit T u Z s r)) := by
  have hm := lowerBSMass_mono_cutoff T u Z s r
  unfold lowerBSMassLimit
  rw [← iSup_eq_iSup_ge_of_monotone hm 1]
  exact tendsto_atTop_iSup hm

end Kolmogorov.PointToSet
