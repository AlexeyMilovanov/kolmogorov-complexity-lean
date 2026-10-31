/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.Pressure.Upper.ScaleComparison

/-!
# Uniform nets and the upper pressure

A uniform `s`-net of a set `Z` is a family of ideal-point Bowen balls, indexed by quadruples
`(i, n, p, k)`, whose weighted slice sums grow at rate at most `s` and which covers every point
of `Z` at every positive order for a suitable slice parameter `k` (`IsUniformPressureNet`).
This file shows that such nets compute the classical upper pressure, and derives the basic
properties of the effective version (nets that are relatively enumerable in an oracle `A`).

* `exists_uniformNet_of_upperPressure_lt` : every real exponent above the upper pressure admits
  a uniform net (blueprint node `pressure:upper-to-net`); covers are recentered on ideal points
  using the Bowen-ball distortion estimates.
* `upperPressure_le_of_uniformNet` : a uniform `s`-net bounds the upper pressure by `s`
  (blueprint node `pressure:net-to-upper`).
* `upperPressure_eq_iInf_uniformNet` : the upper pressure is the infimum of net exponents
  (blueprint node `pressure:upper-discrete`).
* `effectiveUpperPressure_ge`, `effectiveUpperPressure_mono`,
  `effectiveUpperPressure_mono_oracle`, `effectiveUpperPressure_exists_net` : the basic
  properties of the effective upper pressure (blueprint node `pressure:effective-upper`).
* `upperThreshold_isUniformNet` : for an admissible oracle and a rational `s`, the Kraft-bounded
  set `upperPressureThreshold` is a uniform `s`-net of the points whose oracle pointwise upper
  pressure is below `s` (blueprint node `pressure:upper-threshold`).

These facts are the net-theoretic half of the point-to-set principle for the upper pressure
proved in the modules importing this file.
-/

namespace Kolmogorov.PointToSet
open Filter
open scoped Topology ENNReal Computability
variable {X : Type*} [MetricSpace X]

/-! ### From classical upper pressure to uniform nets -/

/-- For every `ε > 0` and `p` there is a scale `q > p` beyond `D.p₀` whose analytical error
`D.ω q` is below `ε`. -/
private lemma exists_omega_lt (D : PressureData X) {ε : ℝ} (hε : 0 < ε) (p : ℕ) :
    ∃ q : ℕ, p + 1 ≤ q ∧ D.p₀ ≤ q ∧ D.ω q < ε := by
  obtain ⟨q, hq, hωq⟩ := ((eventually_ge_atTop (max (p + 1) D.p₀)).and
    (D.ω_tendsto.eventually (gt_mem_nhds hε))).exists
  exact ⟨q, (le_max_left _ _).trans hq, (le_max_right _ _).trans hq, hωq⟩

/-- A set of centered modified upper pressure below `a` at radius `r` is covered by countably
many sets of centered upper capacity below `a` at radius `r`. -/
private lemma exists_cover_upperCapacity_lt (D : PressureData X) (Z : Set X) (a r : ℝ)
    (h : modifiedUpperPressure D.T D.φ .centered Z r < (a : EReal)) :
    ∃ Y : ℕ → Set X, Z ⊆ ⋃ k, Y k ∧
      ∀ k, upperCapacity D.T D.φ .centered (Y k) r < (a : EReal) := by
  unfold modifiedUpperPressure at h
  obtain ⟨Y, hY⟩ := iInf_lt_iff.mp h
  obtain ⟨hcov, hsup⟩ := iInf_lt_iff.mp hY
  exact ⟨Y, hcov, fun k ↦
    (le_iSup (fun k ↦ upperCapacity D.T D.φ .centered (Y k) r) k).trans_lt hsup⟩

/-- A multiplicative comparison `g n ≤ 2 ^ c * f n` at one order bounds the pressure rate of `g`
by the pressure rate of `f` plus `c / n`. -/
private lemma pressureRate_le_add_of_le_rpow_mul {f g : ℕ → ℝ≥0∞} {n : ℕ} (hn : 1 ≤ n) {c : ℝ}
    (h : g n ≤ (2 : ℝ≥0∞) ^ c * f n) :
    pressureRate g n ≤ pressureRate f n + ((c / n : ℝ) : EReal) := by
  have hn0 : n ≠ 0 := by omega
  have hlpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let k : ℝ := (Real.log 2)⁻¹ * (n : ℝ)⁻¹
  have hk : 0 ≤ (k : EReal) := EReal.coe_nonneg.mpr
    (mul_nonneg (inv_nonneg.mpr hlpos.le) (inv_nonneg.mpr (Nat.cast_nonneg n)))
  have hrate (q : ℕ → ℝ≥0∞) : pressureRate q n = ENNReal.log (q n) * (k : EReal) := by
    simp only [pressureRate, ite_eq_right hn0, pressureLog, mul_assoc, ← EReal.coe_mul]
    rfl
  rw [hrate, hrate]
  have hlogtwo : ENNReal.log 2 = ((Real.log 2 : ℝ) : EReal) := by
    simpa using ENNReal.log_ofReal_of_pos (by norm_num : (0 : ℝ) < 2)
  have hm := mul_le_mul_of_nonneg_right (ENNReal.log_le_log h) hk
  rw [ENNReal.log_mul_add, ENNReal.log_rpow, hlogtwo,
    EReal.right_distrib_of_nonneg_of_ne_top hk (EReal.coe_ne_top k)] at hm
  have hc : (c : EReal) * (Real.log 2 : EReal) * (k : EReal) = ((c / n : ℝ) : EReal) := by
    rw [← EReal.coe_mul, ← EReal.coe_mul]
    congr 1
    dsimp [k]
    field_simp
  rw [hc] at hm
  exact hm.trans_eq (add_comm _ _)

/-- A comparison `g n ≤ 2 ^ (n * c) * f n` at every positive order shifts the limsup of the
pressure rate by at most `c`. -/
private lemma limsup_pressureRate_le_of_le_rpow_mul (f g : ℕ → ℝ≥0∞) (c a : ℝ)
    (hpoint : ∀ n ≥ 1, g n ≤ (2 : ℝ≥0∞) ^ ((n : ℝ) * c) * f n)
    (hrate : limsup (pressureRate f) atTop < (a : EReal)) :
    limsup (pressureRate g) atTop ≤ (a + c : EReal) := by
  have H : ∀ᶠ n in atTop, pressureRate g n ≤ pressureRate f n + (c : EReal) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    simpa only [mul_div_cancel_left₀ _ hn0] using
      pressureRate_le_add_of_le_rpow_mul hn (hpoint n hn)
  have hlim := EReal.limsup_add_le (u := pressureRate f) (v := fun _ : ℕ ↦ (c : EReal))
    (f := atTop) (Or.inr (by simp)) (Or.inr (by simp))
  rw [limsup_const] at hlim
  have h₁ := limsup_le_limsup H (by isBoundedDefault)
  have h₂ : limsup (pressureRate f) atTop + (c : EReal) ≤ (a : EReal) + (c : EReal) :=
    add_le_add_left hrate.le _
  exact_mod_cast h₁.trans (hlim.trans h₂)

/-- Countable covers of `Y` by Bowen balls of radius `r_q` can be recentered on ideal points: the
resulting slice `E` covers `Y` by balls of radius `r_p` at every positive order, and its weighted
sum is at most `2 ^ (n ω_q)` times the weighted sum of the original cover. -/
private lemma exists_slice_of_countable_covers (D : PressureData X) (p q k : ℕ)
    (hpq : p + 1 ≤ q) (hq : D.p₀ ≤ q) (Y : Set X) (F : ℕ → Set X)
    (hF : ∀ n ≥ 1, (F n).Countable ∧
      Y ⊆ ⋃ y ∈ F n, bowenBall D.T n y (dyadicRadius q)) :
    ∃ E : Set (ℕ × ℕ × ℕ × ℕ),
      (∀ t ∈ E, 1 ≤ t.2.1 ∧ p = t.2.2.1 ∧ k = t.2.2.2) ∧
      (∀ n ≥ 1, ∀ x ∈ Y, ∃ i, (i, n, p, k) ∈ E ∧
        x ∈ bowenBall D.T n (D.presentation.ι i) (dyadicRadius p)) ∧
      ∀ n ≥ 1, uniformPressureSum D.presentation D.T D.φ E n p k ≤
        (2 : ℝ≥0∞) ^ ((n : ℝ) * D.ω q) *
          partitionCoverCost D.T D.φ .centered (F n) n (dyadicRadius q) := by
  classical
  have hchoose : ∀ (n : ℕ) (hn : 1 ≤ n) (y : F n),
      ∃ i, bowenDist D.T n y (D.presentation.ι i) < dyadicRadius q :=
    fun n hn y ↦ bowen_geometry_dense D n hn y (dyadicRadius q) (dyadicRadius_pos q)
  choose g hg using hchoose
  let E : Set (ℕ × ℕ × ℕ × ℕ) :=
    {t | ∃ hn : 1 ≤ t.2.1, p = t.2.2.1 ∧ k = t.2.2.2 ∧ t.1 ∈ Set.range (g t.2.1 hn)}
  have hslice (n : ℕ) (hn : 1 ≤ n) :
      {i : ℕ | (i, n, p, k) ∈ E} = Set.range (g n hn) := by
    ext i
    exact ⟨fun ⟨_, _, _, hi⟩ ↦ hi, fun hi ↦ ⟨hn, rfl, rfl, hi⟩⟩
  have hradius : dyadicRadius q + dyadicRadius q ≤ dyadicRadius p := by
    have hqr : dyadicRadius q ≤ dyadicRadius (p + 1) := dyadicRadius_antitone hpq
    calc
      dyadicRadius q + dyadicRadius q ≤ dyadicRadius (p + 1) + dyadicRadius (p + 1) :=
        add_le_add hqr hqr
      _ = dyadicRadius p := by
        unfold dyadicRadius
        rw [pow_succ]
        ring
  refine ⟨E, fun t ⟨hn, hp, hk, _⟩ ↦ ⟨hn, hp, hk⟩, ?_, ?_⟩
  · intro n hn x hx
    obtain ⟨y, hyF, hyball⟩ :
        ∃ y ∈ F n, x ∈ bowenBall D.T n y (dyadicRadius q) := by
      simpa only [Set.mem_iUnion, exists_prop] using (hF n hn).2 hx
    let y' : F n := ⟨y, hyF⟩
    refine ⟨g n hn y', ⟨hn, rfl, rfl, y', rfl⟩, ?_⟩
    have hball := bowen_geometry_subset D n hn y (D.presentation.ι (g n hn y'))
      (dyadicRadius q) (dyadicRadius q) (hg n hn y') hyball
    exact bowenBall_subset_of_le
      D.T n (D.presentation.ι (g n hn y')) hradius hball
  · intro n hn
    have hweight (y : F n) :
        (2 : ℝ≥0∞) ^ birkhoffSum D.T D.φ n (D.presentation.ι (g n hn y)) ≤
          (2 : ℝ≥0∞) ^ ((n : ℝ) * D.ω q) *
            (2 : ℝ≥0∞) ^ birkhoffSum D.T D.φ n y := by
      have hyball : D.presentation.ι (g n hn y) ∈ bowenBall D.T n y (dyadicRadius q) :=
        (bowen_ball_dense_iff D.T n hn y _ _).mpr (hg n hn y)
      have hdist := recenter_bowen_cover_distortion D q hq n y _ hyball
      calc
        _ ≤ (2 : ℝ≥0∞) ^ (birkhoffSum D.T D.φ n y + (n : ℝ) * D.ω q) := by
          apply ENNReal.rpow_le_rpow_of_exponent_le (by norm_num)
          linarith [(abs_le.mp hdist).2]
        _ = _ := by
          rw [ENNReal.rpow_add _ _ (by norm_num) (by norm_num)]
          exact mul_comm _ _
    unfold uniformPressureSum
    rw [hslice n hn]
    calc
      _ ≤ ∑' y : F n, (2 : ℝ≥0∞) ^ birkhoffSum D.T D.φ n (D.presentation.ι (g n hn y)) :=
        ENNReal.tsum_le_tsum_comp_of_surjective
          (Set.rangeFactorization_surjective (f := g n hn))
          (fun i : Set.range (g n hn) ↦
            (2 : ℝ≥0∞) ^ birkhoffSum D.T D.φ n (D.presentation.ι i))
      _ ≤ ∑' y : F n, (2 : ℝ≥0∞) ^ ((n : ℝ) * D.ω q) *
          (2 : ℝ≥0∞) ^ birkhoffSum D.T D.φ n y := ENNReal.tsum_le_tsum hweight
      _ = _ := ENNReal.tsum_mul_left

/-- A set `Y` whose centered upper capacity at radius `r_q` is below `a` is covered, at every
positive order, by one slice `E` of ideal-point balls of radius `r_p` whose slice rate has
limsup at most `a + ω_q`. -/
private lemma exists_slice_rate_le (D : PressureData X) (a : ℝ) (p q k : ℕ)
    (hpq : p + 1 ≤ q) (hq : D.p₀ ≤ q) (Y : Set X)
    (hY : upperCapacity D.T D.φ .centered Y (dyadicRadius q) < (a : EReal)) :
    ∃ E : Set (ℕ × ℕ × ℕ × ℕ),
      (∀ t ∈ E, 1 ≤ t.2.1 ∧ p = t.2.2.1 ∧ k = t.2.2.2) ∧
      limsup (pressureRate (fun n ↦ uniformPressureSum D.presentation D.T D.φ E n p k))
        atTop ≤ (a + D.ω q : EReal) ∧
      ∀ n ≥ 1, ∀ x ∈ Y, ∃ i, (i, n, p, k) ∈ E ∧
        x ∈ bowenBall D.T n (D.presentation.ι i) (dyadicRadius p) := by
  obtain ⟨F, hF, hF_rate⟩ := exists_partitionSum_approximation_rate D .centered Y q hq a hY
  obtain ⟨E, hE_dom, hE_cov, hE_sum⟩ :=
    exists_slice_of_countable_covers D p q k hpq hq Y F hF
  exact ⟨E, hE_dom, limsup_pressureRate_le_of_le_rpow_mul _ _ (D.ω q) a hE_sum hF_rate,
    hE_cov⟩

/-- Slices `E p k` (whose elements have `p` and `k` as third and fourth coordinates) assemble
into one uniform `s`-net of `Z`, provided each slice has rate at most `s` and every point of `Z`
is covered at every positive order by some slice `E p k` at each scale `p ≥ D.p₀`. -/
private lemma exists_uniformNet_of_slices (D : PressureData X) (Z : Set X) (s : ℝ)
    (E : ℕ → ℕ → Set (ℕ × ℕ × ℕ × ℕ))
    (hdom : ∀ p k, ∀ t ∈ E p k, 1 ≤ t.2.1 ∧ p = t.2.2.1 ∧ k = t.2.2.2)
    (hrate : ∀ p ≥ D.p₀, ∀ k,
      limsup (pressureRate (fun n ↦ uniformPressureSum D.presentation D.T D.φ (E p k) n p k))
        atTop ≤ (s : EReal))
    (hcov : ∀ p ≥ D.p₀, ∀ x ∈ Z, ∃ k, ∀ n ≥ 1, ∃ i, (i, n, p, k) ∈ E p k ∧
      x ∈ bowenBall D.T n (D.presentation.ι i) (dyadicRadius p)) :
    ∃ E' : Set (ℕ × ℕ × ℕ × ℕ), IsUniformPressureNet D.presentation D.T D.φ D.p₀ Z s E' := by
  let U : Set (ℕ × ℕ × ℕ × ℕ) := ⋃ (p ≥ D.p₀) (k), E p k
  have hmem : ∀ i n p k, (i, n, p, k) ∈ U ↔ D.p₀ ≤ p ∧ (i, n, p, k) ∈ E p k := by
    intro i n p k
    simp only [U, Set.mem_iUnion, exists_prop]
    refine ⟨?_, fun ⟨hp, h⟩ ↦ ⟨p, hp, k, h⟩⟩
    rintro ⟨p', hp', k', h⟩
    obtain ⟨-, rfl, rfl⟩ := hdom p' k' _ h
    exact ⟨hp', h⟩
  have hsum : ∀ p ≥ D.p₀, ∀ k n, uniformPressureSum D.presentation D.T D.φ U n p k =
      uniformPressureSum D.presentation D.T D.φ (E p k) n p k := by
    intro p hp k n
    have hset : {i : ℕ | (i, n, p, k) ∈ U} = {i : ℕ | (i, n, p, k) ∈ E p k} := by
      ext i
      exact (hmem i n p k).trans (and_iff_right hp)
    unfold uniformPressureSum
    rw [hset]
  refine ⟨U, ?_, fun p hp k ↦ ?_, fun p hp x hx ↦ ?_⟩
  · rintro ⟨i, n, p, k⟩ ht
    obtain ⟨hp, h⟩ := (hmem i n p k).1 ht
    exact ⟨(hdom p k _ h).1, hp⟩
  · have hfun : (fun n ↦ uniformPressureSum D.presentation D.T D.φ U n p k) =
        fun n ↦ uniformPressureSum D.presentation D.T D.φ (E p k) n p k :=
      funext fun n ↦ hsum p hp k n
    rw [hfun]
    exact hrate p hp k
  · obtain ⟨k, hk⟩ := hcov p hp x hx
    refine ⟨k, fun n hn ↦ ?_⟩
    obtain ⟨i, hi, hball⟩ := hk n hn
    exact ⟨i, (hmem i n p k).2 ⟨hp, hi⟩, hball⟩

/-- Every real exponent above classical upper pressure admits a uniform net.
Blueprint node `pressure:upper-to-net`. -/
theorem exists_uniformNet_of_upperPressure_lt (D : PressureData X) (Z : Set X) (s : ℝ)
    (hs : upperPressure D.T D.φ D.p₀ Z < (s : EReal)) :
    ∃ E, IsUniformPressureNet D.presentation D.T D.φ D.p₀ Z s E := by
  obtain ⟨a, ha_lt, ha_s⟩ := EReal.exists_between_coe_real hs
  have has : a < s := EReal.coe_lt_coe_iff.mp ha_s
  choose q hpq hq hω using fun p ↦ exists_omega_lt D (sub_pos.mpr has) p
  have hmod (p : ℕ) :
      modifiedUpperPressure D.T D.φ .centered Z (dyadicRadius (q p)) < (a : EReal) := by
    refine lt_of_le_of_lt ?_ ha_lt
    unfold upperPressure
    exact le_iSup₂_of_le (q p) (hq p) le_rfl
  choose Y hY_cover hY_cap using fun p ↦ exists_cover_upperCapacity_lt D Z a _ (hmod p)
  choose E hE_dom hE_rate hE_cov using fun p k ↦
    exists_slice_rate_le D a p (q p) k (hpq p) (hq p) (Y p k) (hY_cap p k)
  refine exists_uniformNet_of_slices D Z s E hE_dom (fun p _ k ↦ (hE_rate p k).trans ?_)
    fun p _ x hx ↦ ?_
  · have : a + D.ω (q p) < s := by linarith [hω p]
    exact_mod_cast this.le
  · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (hY_cover p hx)
    exact ⟨k, fun n hn ↦ hE_cov p k n hn x hk⟩

/-! ### From uniform nets to the upper pressure -/

/-- The points covered at every positive order by the radius-`r_p` Bowen balls around the ideal
points of the slice `(·, n, p, k)` of `E`. -/
private def netSlice (D : PressureData X) (E : Set (ℕ × ℕ × ℕ × ℕ)) (p k : ℕ) : Set X :=
  {x | ∀ n ≥ 1, ∃ i, (i, n, p, k) ∈ E ∧
    x ∈ bowenBall D.T n (D.presentation.ι i) (dyadicRadius p)}

/-- The partition sum of a net slice at order `n` is bounded by the uniform-net sum. -/
private lemma partitionSum_netSlice_le (D : PressureData X) (E : Set (ℕ × ℕ × ℕ × ℕ))
    (p k n : ℕ) (hn : 1 ≤ n) :
    partitionSum D.T D.φ .centered (netSlice D E p k) n (dyadicRadius p) ≤
      uniformPressureSum D.presentation D.T D.φ E n p k := by
  dsimp [partitionSum, uniformPressureSum]
  let I : Set ℕ := {i | (i, n, p, k) ∈ E}
  let F : Set X := D.presentation.ι '' I
  refine iInf_le_of_le F (iInf_le_of_le ⟨(Set.to_countable I).image _, ?_⟩ ?_)
  · intro x hx
    obtain ⟨i, hi, hx⟩ := hx n hn
    exact Set.mem_iUnion₂.mpr ⟨D.presentation.ι i, ⟨i, hi, rfl⟩, hx⟩
  · dsimp [partitionCoverCost, pressureBallWeight]
    exact ENNReal.tsum_le_tsum_comp_of_surjective Set.imageFactorization_surjective
      (fun y : F ↦ (2 : ℝ≥0∞) ^ birkhoffSum D.T D.φ n y)

/-- A net slice has centered upper capacity at most the exponent of the net. -/
private lemma upperCapacity_netSlice_le (D : PressureData X) (Z : Set X) (s : ℝ)
    (E : Set (ℕ × ℕ × ℕ × ℕ)) (hE : IsUniformPressureNet D.presentation D.T D.φ D.p₀ Z s E)
    (p : ℕ) (hp : D.p₀ ≤ p) (k : ℕ) :
    upperCapacity D.T D.φ .centered (netSlice D E p k) (dyadicRadius p) ≤ (s : EReal) := by
  unfold upperCapacity
  refine (limsup_le_limsup ?_ (by isBoundedDefault) (by isBoundedDefault)).trans
    (hE.2.1 p hp k)
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact pressureRate_le_of_le _ _ n (partitionSum_netSlice_le D E p k n hn)

/-- A uniform `s`-net bounds the centered modified upper pressure at every scale `p ≥ D.p₀`
by `s`. -/
private lemma modifiedUpperPressure_le_of_uniformNet (D : PressureData X) (Z : Set X) (s : ℝ)
    (E : Set (ℕ × ℕ × ℕ × ℕ)) (hE : IsUniformPressureNet D.presentation D.T D.φ D.p₀ Z s E)
    (p : ℕ) (hp : D.p₀ ≤ p) :
    modifiedUpperPressure D.T D.φ .centered Z (dyadicRadius p) ≤ (s : EReal) := by
  unfold modifiedUpperPressure
  refine iInf_le_of_le (netSlice D E p) (iInf_le_of_le ?_
    (iSup_le fun k ↦ upperCapacity_netSlice_le D Z s E hE p hp k))
  intro x hx
  obtain ⟨k, hk⟩ := hE.2.2 p hp x hx
  exact Set.mem_iUnion.mpr ⟨k, hk⟩

/-- Every uniform net bounds the classical upper pressure by its real exponent.
Blueprint node `pressure:net-to-upper`. -/
theorem upperPressure_le_of_uniformNet (D : PressureData X) (Z : Set X) (s : ℝ)
    (E : Set (ℕ × ℕ × ℕ × ℕ))
    (hE : IsUniformPressureNet D.presentation D.T D.φ D.p₀ Z s E) :
    upperPressure D.T D.φ D.p₀ Z ≤ (s : EReal) := by
  unfold upperPressure
  exact iSup₂_le fun p hp ↦ modifiedUpperPressure_le_of_uniformNet D Z s E hE p hp

/-- Uniform-net exponents recover the signed upper pressure by an extended infimum.
Blueprint node `pressure:upper-discrete`. -/
theorem upperPressure_eq_iInf_uniformNet (D : PressureData X) (Z : Set X) :
    upperPressure D.T D.φ D.p₀ Z =
      ⨅ s : ℝ, ⨅ (_ : ∃ E, IsUniformPressureNet D.presentation D.T D.φ D.p₀ Z s E),
        (s : EReal) := by
  apply le_antisymm
  · refine le_iInf₂ fun s hs ↦ ?_
    obtain ⟨E, hE⟩ := hs
    exact upperPressure_le_of_uniformNet D Z s E hE
  · by_contra h
    obtain ⟨r, hr₁, hr₂⟩ := EReal.exists_between_coe_real (not_le.mp h)
    obtain ⟨E, hE⟩ := exists_uniformNet_of_upperPressure_lt D Z r hr₁
    exact absurd hr₂ (not_lt.mpr (iInf₂_le r ⟨E, hE⟩))

/-! ### The effective upper pressure -/

/-- Effective upper pressure bounds classical upper pressure for every oracle.
Blueprint node `pressure:effective-upper`. -/
theorem effectiveUpperPressure_ge (D : PressureData X) (A : Set ℕ) (Z : Set X) :
    upperPressure D.T D.φ D.p₀ Z ≤
      effectiveUpperPressure D.presentation D.T D.φ D.p₀ A Z := by
  rw [upperPressure_eq_iInf_uniformNet D Z, effectiveUpperPressure]
  refine le_iInf₂ fun s E ↦ le_iInf fun hE ↦ ?_
  exact iInf₂_le s ⟨E, hE.1⟩

/-- Effective upper pressure is monotone in the covered set.
Blueprint node `pressure:effective-upper`. -/
theorem effectiveUpperPressure_mono (D : PressureData X) (A : Set ℕ)
    (Z Y : Set X) (hZY : Z ⊆ Y) :
    effectiveUpperPressure D.presentation D.T D.φ D.p₀ A Z ≤
      effectiveUpperPressure D.presentation D.T D.φ D.p₀ A Y := by
  unfold effectiveUpperPressure
  refine iInf_mono fun s ↦ iInf_mono fun E ↦ iInf_mono' fun h ↦ ⟨⟨?_, h.2⟩, le_rfl⟩
  obtain ⟨h₁, h₂, h₃⟩ := h.1
  exact ⟨h₁, h₂, fun p hp x hx ↦ h₃ p hp x (hZY hx)⟩

/-- Effective upper pressure decreases under oracle strengthening.
Blueprint node `pressure:effective-upper`. -/
theorem effectiveUpperPressure_mono_oracle (D : PressureData X) (A B : Set ℕ)
    (hAB : charOracle A ≤ᵀ charOracle B) (Z : Set X) :
    effectiveUpperPressure D.presentation D.T D.φ D.p₀ B Z ≤
      effectiveUpperPressure D.presentation D.T D.φ D.p₀ A Z := by
  unfold effectiveUpperPressure
  refine iInf_mono fun s ↦ iInf_mono fun E ↦ le_iInf fun h ↦ ?_
  exact iInf_le_of_le ⟨h.1, h.2.mono_oracle hAB⟩ le_rfl

/-- Every exponent strictly above effective upper pressure admits an effective net.
Blueprint node `pressure:effective-upper`. -/
theorem effectiveUpperPressure_exists_net (D : PressureData X) (A : Set ℕ) (Z : Set X)
    (s : ℝ)
    (hs : effectiveUpperPressure D.presentation D.T D.φ D.p₀ A Z < (s : EReal)) :
    ∃ E, IsUniformPressureNet D.presentation D.T D.φ D.p₀ Z s E ∧ IsREIn A E := by
  unfold effectiveUpperPressure at hs
  obtain ⟨s', hs'⟩ := iInf_lt_iff.mp hs
  obtain ⟨E, hE⟩ := iInf_lt_iff.mp hs'
  obtain ⟨⟨⟨h₁, h₂, h₃⟩, hre⟩, hlt⟩ := iInf_lt_iff.mp hE
  exact ⟨E, ⟨h₁, fun p hp k ↦ (h₂ p hp k).trans hlt.le, h₃⟩, hre⟩

/-! ### The upper-complexity threshold net -/

/-- Kraft's inequality bounds each slice sum of the upper threshold by `2 ^ (s n + k)`. -/
private lemma uniformPressureSum_upperPressureThreshold_le (D : PressureData X) (A : Set ℕ)
    (s : ℚ) (n p k : ℕ) :
    uniformPressureSum D.presentation D.T D.φ
      (upperPressureThreshold D.presentation D.T D.φ D.p₀ A s) n p k ≤
        (2 : ℝ≥0∞) ^ ((s : ℝ) * n + k) := by
  unfold uniformPressureSum
  set S : Set ℕ := {i | (i, n, p, k) ∈ upperPressureThreshold D.presentation D.T D.φ D.p₀ A s}
  have hweight : ∀ i : S, (2 : ℝ≥0∞) ^ birkhoffSum D.T D.φ n (D.presentation.ι i) ≤
      (2 : ℝ≥0∞) ^ ((s : ℝ) * n + k) * (2⁻¹ : ℝ≥0∞) ^ oracleNatComplexity A i := by
    rintro ⟨i, hi⟩
    have hle : birkhoffSum D.T D.φ n (D.presentation.ι i) ≤
        (s : ℝ) * n + k - (oracleNatComplexity A i : ℝ) := by
      linarith [hi.2.2]
    calc
      _ ≤ (2 : ℝ≥0∞) ^ ((s : ℝ) * n + k - (oracleNatComplexity A i : ℝ)) :=
        ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) hle
      _ = _ := by
        rw [ENNReal.rpow_sub _ _ (by norm_num) (by norm_num), ENNReal.rpow_natCast,
          div_eq_mul_inv, ENNReal.inv_pow]
  calc
    _ ≤ ∑' i : S, (2 : ℝ≥0∞) ^ ((s : ℝ) * n + k) * (2⁻¹ : ℝ≥0∞) ^ oracleNatComplexity A i :=
      ENNReal.tsum_le_tsum hweight
    _ = (2 : ℝ≥0∞) ^ ((s : ℝ) * n + k) * ∑' i : S, (2⁻¹ : ℝ≥0∞) ^ oracleNatComplexity A i :=
      ENNReal.tsum_mul_left
    _ ≤ (2 : ℝ≥0∞) ^ ((s : ℝ) * n + k) * 1 := by
      gcongr
      exact (ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective
        fun i ↦ (2⁻¹ : ℝ≥0∞) ^ oracleNatComplexity A i).trans (oracle_kraft A)
    _ = _ := mul_one _

/-- A sequence of extended reals eventually below `(s n + k) / n` has limsup at most `s`. -/
private lemma limsup_le_of_eventually_le_div (s k : ℝ) (f : ℕ → EReal)
    (hf : ∀ᶠ n : ℕ in atTop, f n ≤ (((s * n + k) / n : ℝ) : EReal)) :
    limsup f atTop ≤ (s : EReal) := by
  have h₁ : Tendsto (fun n : ℕ ↦ s + k / n) atTop (𝓝 s) := by
    simpa using tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat k)
  have h₂ : Tendsto (fun n : ℕ ↦ (((s * n + k) / n : ℝ) : EReal)) atTop (𝓝 (s : EReal)) := by
    refine Tendsto.congr' ?_ (continuous_coe_real_ereal.continuousAt.tendsto.comp h₁)
    filter_upwards [eventually_ne_atTop 0] with n hn
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    simp only [Function.comp_apply]
    congr 1
    field_simp
  calc
    limsup f atTop ≤ limsup (fun n : ℕ ↦ (((s * n + k) / n : ℝ) : EReal)) atTop :=
      limsup_le_limsup hf (by isBoundedDefault) (by isBoundedDefault)
    _ = (s : EReal) := h₂.limsup_eq

/-- Every slice rate of the upper threshold has limsup at most `s`. -/
private lemma limsup_pressureRate_upperPressureThreshold_le (D : PressureData X) (A : Set ℕ)
    (s : ℚ) (p k : ℕ) :
    limsup (pressureRate (fun n ↦ uniformPressureSum D.presentation D.T D.φ
      (upperPressureThreshold D.presentation D.T D.φ D.p₀ A s) n p k)) atTop ≤
        ((s : ℝ) : EReal) := by
  refine limsup_le_of_eventually_le_div s k _ ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hone : pressureRate (fun _ ↦ (1 : ℝ≥0∞)) n = 0 := by
    simp [pressureRate, pressureLog, Nat.pos_iff_ne_zero.mp hn]
  have h := pressureRate_le_add_of_le_rpow_mul (f := fun _ ↦ (1 : ℝ≥0∞))
    (g := fun n ↦ uniformPressureSum D.presentation D.T D.φ
      (upperPressureThreshold D.presentation D.T D.φ D.p₀ A s) n p k) hn
    (c := (s : ℝ) * n + k) (by
      rw [mul_one]
      exact uniformPressureSum_upperPressureThreshold_le D A s n p k)
  rwa [hone, zero_add] at h

/-- If the scale-`p` pressure rate of `x` has limsup below `s`, then for all large orders `n`
there is an ideal point whose ball of radius `r_p` contains `x` and whose complexity plus
Birkhoff sum is below `s n`. -/
private lemma exists_realizers_of_limsup_lt (D : PressureData X) (A : Set ℕ) (s : ℚ) (p : ℕ)
    (x : X)
    (h : limsup (fun n ↦ finiteScalePressureRate D.presentation D.T D.φ A x n
      (dyadicRadius p)) atTop < ((s : ℝ) : EReal)) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ i,
      (oracleNatComplexity A i : ℝ) + birkhoffSum D.T D.φ n (D.presentation.ι i) <
        (s : ℝ) * n ∧
      x ∈ bowenBall D.T n (D.presentation.ι i) (dyadicRadius p) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_lt_of_limsup_lt h)
  refine ⟨max 1 N, fun n hn ↦ ?_⟩
  have hn1 : 1 ≤ n := (le_max_left 1 N).trans hn
  have hn0 : n ≠ 0 := by omega
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hcost := hN n ((le_max_right 1 N).trans hn)
  rw [finiteScalePressureRate, ite_eq_right hn0] at hcost
  obtain ⟨i, hi⟩ := iInf_lt_iff.mp hcost
  obtain ⟨hball, hi⟩ := iInf_lt_iff.mp hi
  refine ⟨i, ?_, (bowen_geometry_symm D n hn1 x _ _).mp hball⟩
  exact (div_lt_iff₀ hnpos).mp (EReal.coe_lt_coe_iff.mp hi)

/-- Density provides an ideal point at each of finitely many positive orders, and a single
natural slack `k` absorbs all of their cost excesses. -/
private lemma exists_slack_for_early_orders (D : PressureData X) (A : Set ℕ) (s : ℚ)
    (p N : ℕ) (x : X) :
    ∃ k : ℕ, ∀ n, 1 ≤ n → n < N → ∃ i,
      (oracleNatComplexity A i : ℝ) <
        (s : ℝ) * n - birkhoffSum D.T D.φ n (D.presentation.ι i) + k ∧
      x ∈ bowenBall D.T n (D.presentation.ι i) (dyadicRadius p) := by
  induction N with
  | zero => exact ⟨0, fun n hn hnN ↦ by omega⟩
  | succ N ih =>
    obtain ⟨k, hk⟩ := ih
    by_cases hN : 1 ≤ N
    · obtain ⟨i, hi⟩ := bowen_ball_dense D.presentation D.T D.continuous_T
        x N hN (dyadicRadius p) (dyadicRadius_pos p)
      obtain ⟨K, hK⟩ := exists_nat_gt ((oracleNatComplexity A i : ℝ) -
        (s : ℝ) * N + birkhoffSum D.T D.φ N (D.presentation.ι i))
      refine ⟨max k K, fun n hn hnN ↦ ?_⟩
      by_cases hnlt : n < N
      · obtain ⟨j, hj, hxj⟩ := hk n hn hnlt
        refine ⟨j, ?_, hxj⟩
        have hle : (k : ℝ) ≤ (max k K : ℕ) := by exact_mod_cast le_max_left k K
        linarith
      · obtain rfl : n = N := by omega
        refine ⟨i, ?_, (bowen_geometry_symm D n hN x _ _).mp hi⟩
        have hle : (K : ℝ) ≤ (max k K : ℕ) := by exact_mod_cast le_max_right k K
        linarith
    · exact ⟨k, fun n hn hnN ↦ by omega⟩

/-- The rational upper threshold is a uniform net of its strict upper-pressure sublevel.
Blueprint node `pressure:upper-threshold`. -/
theorem upperThreshold_isUniformNet (D : PressureData X) (A : Set ℕ)
    (s : ℚ) :
    IsUniformPressureNet D.presentation D.T D.φ D.p₀
      {x | (pointwisePressure D.presentation D.T D.φ A x).2 < ((s : ℝ) : EReal)} s
      (upperPressureThreshold D.presentation D.T D.φ D.p₀ A s) := by
  refine ⟨fun t ht ↦ ⟨ht.1, ht.2.1⟩,
    fun p _ k ↦ limsup_pressureRate_upperPressureThreshold_le D A s p k, ?_⟩
  intro p hp x hx
  have hscale : limsup (fun n ↦ finiteScalePressureRate D.presentation D.T D.φ A x n
      (dyadicRadius p)) atTop < ((s : ℝ) : EReal) :=
    (le_iSup (fun q ↦ limsup (fun n ↦ finiteScalePressureRate
      D.presentation D.T D.φ A x n (dyadicRadius q)) atTop) p).trans_lt hx
  obtain ⟨N, htail⟩ := exists_realizers_of_limsup_lt D A s p x hscale
  obtain ⟨k, hprefix⟩ := exists_slack_for_early_orders D A s p N x
  refine ⟨k, fun n hn ↦ ?_⟩
  by_cases hnN : n < N
  · obtain ⟨i, hi, hball⟩ := hprefix n hn hnN
    exact ⟨i, ⟨hn, hp, hi⟩, hball⟩
  · obtain ⟨i, hi, hball⟩ := htail n (Nat.le_of_not_gt hnN)
    refine ⟨i, ⟨hn, hp, ?_⟩, hball⟩
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith

end Kolmogorov.PointToSet
