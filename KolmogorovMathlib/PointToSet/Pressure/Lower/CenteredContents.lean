/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.Pressure.Lower.BowenGeometry

/-!
# Centered pressure limits and failure of supremum-weight monotonicity

For blueprint node `pressure:lower-scale`, this module proves that the centered critical
values along dyadic radii converge to the scale-zero lower pressure. It also constructs a
three-point identity system whose supremum-weight critical values alternate between zero
and one at four consecutive dyadic radii, arbitrarily far along the small-scale tail.

Thus centered values supply the monotone limit used in the lower point-to-set principle,
while supremum-weight values require the oscillation comparison proved in `BowenGeometry`.
Both results are exported by `KolmogorovMathlib.PointToSet.Pressure.Lower`.
-/

namespace Kolmogorov.PointToSet

open Filter
open scoped Topology ENNReal Computability

variable {X : Type*} [MetricSpace X]

/-- Distances `h`, `3h`, and `4h` on the three pairs of distinct points. -/
private def threePointDist (h : ℝ) (x y : Fin 3) : ℝ :=
  if x = y then 0
  else if (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0) then h
  else if (x = 0 ∧ y = 2) ∨ (x = 2 ∧ y = 0) then 3 * h
  else 4 * h

private lemma threePointDist_self (h : ℝ) (x : Fin 3) : threePointDist h x x = 0 := by
  simp [threePointDist]

private lemma threePointDist_comm (h : ℝ) (x y : Fin 3) :
    threePointDist h x y = threePointDist h y x := by
  unfold threePointDist
  split_ifs <;> aesop

private lemma threePointDist_eq_zero_iff (h : ℝ) (h_pos : 0 < h) (x y : Fin 3) :
    threePointDist h x y = 0 ↔ x = y := by
  unfold threePointDist
  split_ifs <;> simp_all [h_pos.ne']

private lemma threePointDist_triangle (h : ℝ) (h_pos : 0 ≤ h) (x y z : Fin 3) :
    threePointDist h x z ≤ threePointDist h x y + threePointDist h y z := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;>
    norm_num [threePointDist] <;> linarith

private noncomputable abbrev threePointMetric (h : ℝ) (h_pos : 0 < h) : MetricSpace (Fin 3) where
  dist := threePointDist h
  dist_self := threePointDist_self h
  dist_comm := threePointDist_comm h
  dist_triangle := threePointDist_triangle h h_pos.le
  eq_of_dist_eq_zero := by
    intro x y hxy
    exact (threePointDist_eq_zero_iff h h_pos x y).mp hxy
  edist_dist := fun _ _ ↦ ENNReal.coe_nnreal_eq _

/-- Potential one at point `1` and zero at the other two points. -/
private def spikePotential : Fin 3 → ℝ
  | 0 => 0
  | 1 => 1
  | 2 => 0

/-- The spike potential is bounded above by one, so every order-`n` ball has weight at most `2ⁿ`. -/
private lemma pressureBallWeight_spike_le [MetricSpace (Fin 3)] (n : ℕ) (x : Fin 3) (r : ℝ) :
    pressureBallWeight id spikePotential .supremum n x r ≤ (2 : ENNReal) ^ (n : ℝ) := by
  refine iSup₂_le fun z _ ↦ ?_
  have hφ : spikePotential z ≤ 1 := by
    fin_cases z <;> norm_num [spikePotential]
  have hsum : birkhoffSum id spikePotential n z = (n : ℝ) * spikePotential z := by
    simp [birkhoffSum]
  rw [hsum]
  apply ENNReal.rpow_le_rpow_of_exponent_le (by norm_num)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hφ (Nat.cast_nonneg n : (0 : ℝ) ≤ n)

private lemma uniformContinuous_spikePotential (h : ℝ) (h_pos : 0 < h) :
    letI := threePointMetric h h_pos
    UniformContinuous spikePotential := by
  let : MetricSpace (Fin 3) := threePointMetric h h_pos
  apply Metric.uniformContinuous_iff.mpr
  intro ε hε
  use h
  refine ⟨h_pos, ?_⟩
  intro x y hxy
  change threePointDist h x y < h at hxy
  unfold threePointDist at hxy
  split_ifs at hxy with h_eq
  · subst h_eq
    simp [hε]
  · linarith
  · linarith
  · linarith

/-- At radius `h`, the ball centered at zero avoids the spike,
so positive exponents give zero content. -/
private lemma lowerContentLimit_spike_smallest_eq_zero
    (p₀ : ℕ) (s : ℝ) (hs : 0 < s) :
    let h := dyadicRadius (p₀ + 3)
    let h_pos : 0 < h := dyadicRadius_pos (p₀ + 3)
    letI := threePointMetric h h_pos
    lowerContentLimit id spikePotential
      .supremum {0} s h = 0 := by
  classical
  let h := dyadicRadius (p₀ + 3)
  have h_pos : 0 < h := dyadicRadius_pos (p₀ + 3)
  let m : MetricSpace (Fin 3) := threePointMetric h h_pos
  change @lowerContentLimit (Fin 3) m id
    spikePotential .supremum {0} s h = 0
  have hmem (n : ℕ) : (0 : Fin 3) ∈ bowenBall id n (0 : Fin 3) h :=
    self_mem_bowenBall id n 0 h h_pos
  have hweight (n : ℕ) (hn : 1 ≤ n) :
      pressureBallWeight id spikePotential
        .supremum n (0 : Fin 3) h ≤ 1 := by
    apply iSup₂_le
    intro z hz
    have hz0 := (Dynamics.mem_dynEntourage.mp hz) 0 (show 0 < n by omega)
    change threePointDist h 0 z < h at hz0
    fin_cases z
    · simp [birkhoffSum, spikePotential]
    · norm_num [threePointDist] at hz0
    · simp [birkhoffSum, spikePotential]
  have hlim : Tendsto (fun n : ℕ ↦ (2 : ENNReal) ^ (-s * (n : ℝ)))
      atTop (𝓝 0) := by
    have hq : (2 : ENNReal) ^ (-s) < 1 :=
      ENNReal.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_lt_zero.mpr hs)
    simpa only [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul] using
      ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hq
  unfold lowerContentLimit
  apply iSup_eq_bot.mpr
  intro N
  apply iSup_eq_bot.mpr
  intro _
  apply le_antisymm _ bot_le
  apply ge_of_tendsto hlim
  filter_upwards [eventually_ge_atTop (max 1 N)] with n hn
  let C : BowenCoverFamily (Fin 3) := ⟨{0}, fun _ ↦ (0 : Fin 3), fun _ ↦ n⟩
  have hC : IsBowenCover id {0} h N C := by
    refine ⟨fun _ ↦ hn, ?_⟩
    intro x hx
    have hx0 : x = 0 := Set.mem_singleton_iff.mp hx
    subst x
    exact Set.mem_iUnion.mpr ⟨(⟨0, by simp [C]⟩ : C.index), hmem n⟩
  have hcost : bowenCoverCost id spikePotential
      .supremum s h C ≤ (2 : ENNReal) ^ (-s * (n : ℝ)) := by
    have hw := hweight n ((le_max_left 1 N).trans hn)
    simpa [bowenCoverCost, C] using
      mul_le_mul' (le_rfl : (2 : ENNReal) ^ (-s * (n : ℝ)) ≤ _) hw
  exact (iInf_le_of_le C (iInf_le_of_le hC le_rfl)).trans hcost

/-- Every cover of the zero-potential point has cost at least one at nonpositive exponents. -/
private lemma one_le_lowerContentLimit_spike [MetricSpace (Fin 3)]
    (r s : ℝ) (hs : s ≤ 0) :
    1 ≤ lowerContentLimit id spikePotential .supremum {0} s r := by
  classical
  unfold lowerContentLimit
  refine le_iSup_of_le 1 (le_iSup_of_le (le_refl 1) ?_)
  unfold lowerContent
  refine le_iInf fun C ↦ le_iInf fun hC ↦ ?_
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp
    (hC.2 (by simp : (0 : Fin 3) ∈ ({0} : Set (Fin 3))))
  have hsum : birkhoffSum id spikePotential (C.order j) (0 : Fin 3) = 0 := by
    simp [birkhoffSum, spikePotential]
  have hw : (1 : ENNReal) ≤ pressureBallWeight id spikePotential .supremum
      (C.order j) (C.center j) r := by
    unfold pressureBallWeight
    refine le_iSup_of_le (0 : Fin 3) (le_iSup_of_le hj ?_)
    simp only [hsum, ENNReal.rpow_zero, le_refl]
  have he : (1 : ENNReal) ≤ (2 : ENNReal) ^ (-s * (C.order j : ℝ)) := by
    calc
      (1 : ENNReal) = (2 : ENNReal) ^ (0 : ℝ) := ENNReal.rpow_zero.symm
      _ ≤ (2 : ENNReal) ^ (-s * (C.order j : ℝ)) :=
        ENNReal.rpow_le_rpow_of_exponent_le (by norm_num)
          (mul_nonneg (neg_nonneg.mpr hs) (Nat.cast_nonneg _))
  have hterm : (1 : ENNReal) ≤ (2 : ENNReal) ^ (-s * (C.order j : ℝ)) *
      pressureBallWeight id spikePotential .supremum (C.order j) (C.center j) r := by
    simpa only [one_mul] using mul_le_mul' he hw
  exact hterm.trans (ENNReal.le_tsum (f := fun i : C.index ↦
    (2 : ENNReal) ^ (-s * (C.order i : ℝ)) *
      pressureBallWeight id spikePotential .supremum (C.order i) (C.center i) r) j)

/-- The strict ball of radius `h` at zero gives critical value zero. -/
private lemma lowerPressureAt_spike_smallest (p₀ : ℕ) :
    let h := dyadicRadius (p₀ + 3)
    let h_pos : 0 < h := dyadicRadius_pos (p₀ + 3)
    letI := threePointMetric h h_pos
    lowerPressureAt id spikePotential .supremum {0} (dyadicRadius (p₀ + 3)) = 0 := by
  let h := dyadicRadius (p₀ + 3)
  let h_pos : 0 < h := dyadicRadius_pos (p₀ + 3)
  let m : MetricSpace (Fin 3) := threePointMetric h h_pos
  change @lowerPressureAt (Fin 3) m id
    spikePotential .supremum {0} h = 0
  unfold lowerPressureAt
  apply le_antisymm
  · apply EReal.le_of_forall_lt_iff_le.mp
    intro t ht
    have hz : lowerContentLimit id
        spikePotential .supremum
        {0} t h = 0 :=
      lowerContentLimit_spike_smallest_eq_zero
        p₀ t (EReal.coe_pos.mp ht)
    exact iInf_le_of_le t (iInf_le_of_le hz le_rfl)
  · refine le_iInf fun s ↦ le_iInf fun hs ↦ ?_
    have hs_pos : 0 < s := by
      by_contra hn
      have hge : (1 : ENNReal) ≤ lowerContentLimit id
          spikePotential .supremum
          {0} s h :=
        one_le_lowerContentLimit_spike h s (le_of_not_gt hn)
      rw [hs] at hge
      norm_num at hge
    exact EReal.coe_nonneg.mpr hs_pos.le

/-- At radius `2h`, the points zero and one share a ball, while point two is isolated. -/
private lemma bowenBall_threePoint_twice (p₀ : ℕ) (n : ℕ) (hn : 1 ≤ n) :
    let h := dyadicRadius (p₀ + 3)
    let h_pos : 0 < h := dyadicRadius_pos (p₀ + 3)
    letI := threePointMetric h h_pos
    let r := dyadicRadius (p₀ + 2)
    @bowenBall (Fin 3) _ id n 0 r = {0, 1} ∧
    @bowenBall (Fin 3) _ id n 1 r = {0, 1} ∧
    @bowenBall (Fin 3) _ id n 2 r = {2} := by
  classical
  let scale : ℝ := dyadicRadius (p₀ + 3)
  have scale_pos : 0 < scale :=
    dyadicRadius_pos (p₀ + 3)
  let metric : MetricSpace (Fin 3) :=
    threePointMetric scale scale_pos
  let radius : ℝ := dyadicRadius (p₀ + 2)
  change
    @bowenBall (Fin 3) metric id n 0 radius = {0, 1} ∧
    @bowenBall (Fin 3) metric id n 1 radius = {0, 1} ∧
    @bowenBall (Fin 3) metric id n 2 radius = {2}
  have hr : radius = 2 * scale := by
    dsimp [radius, scale, dyadicRadius]
    rw [show p₀ + 3 = (p₀ + 2) + 1 by omega, pow_succ]
    ring
  have hmem (x y : Fin 3) :
      y ∈ @bowenBall (Fin 3) metric id n x radius ↔
        threePointDist scale x y < radius := by
    constructor
    · intro H
      have H0 := (Dynamics.mem_dynEntourage.mp H)
        0 (show 0 < n by omega)
      change threePointDist scale x y < radius at H0
      exact H0
    · intro H
      apply Dynamics.mem_dynEntourage.mpr
      intro k _
      change dist (id^[k] x) (id^[k] y) < radius
      simp only [Function.iterate_id, id_eq]
      change threePointDist scale x y < radius
      exact H
  refine ⟨?_, ?_, ?_⟩ <;>
    ext z <;>
    rw [hmem] <;>
    fin_cases z <;>
    norm_num [threePointDist, hr] <;>
    linarith [scale_pos]

/-- At radius `2h`, any ball covering zero also contains the point with potential one. -/
private lemma rpow_le_lowerContent_spike_twice (p₀ : ℕ) (s : ℝ) (hs : s ≤ 1) (N : ℕ) :
    let h := dyadicRadius (p₀ + 3)
    letI := threePointMetric h (dyadicRadius_pos (p₀ + 3))
    (2 : ENNReal) ^ ((1 - s) * (N : ℝ)) ≤
      lowerContent id spikePotential .supremum {0} s (dyadicRadius (p₀ + 2)) N := by
  classical
  let h := dyadicRadius (p₀ + 3)
  let := threePointMetric h (dyadicRadius_pos (p₀ + 3))
  let r := dyadicRadius (p₀ + 2)
  have hmem (n : ℕ) (hn : 1 ≤ n) (y : Fin 3)
      (hy : (0 : Fin 3) ∈ bowenBall id n y r) :
      (1 : Fin 3) ∈ bowenBall id n y r := by
    obtain ⟨h0, h1, h2⟩ := bowenBall_threePoint_twice p₀ n hn
    fin_cases y <;> simp_all [r]
  unfold lowerContent
  refine le_iInf fun C ↦ le_iInf fun hC ↦ ?_
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp
    (hC.2 (by simp : (0 : Fin 3) ∈ ({0} : Set (Fin 3))))
  let n := C.order j
  have hn : 1 ≤ n := (le_max_left 1 N).trans (hC.1 j)
  have hN_le : N ≤ n := (le_max_right 1 N).trans (hC.1 j)
  have hw : (2 : ENNReal) ^ (n : ℝ) ≤
      pressureBallWeight id spikePotential .supremum n (C.center j) r := by
    refine le_iSup_of_le (1 : Fin 3) (le_iSup_of_le (hmem n hn (C.center j) hj) ?_)
    simp [birkhoffSum, spikePotential]
  calc
    (2 : ENNReal) ^ ((1 - s) * (N : ℝ)) ≤ (2 : ENNReal) ^ ((1 - s) * (n : ℝ)) :=
      ENNReal.rpow_le_rpow_of_exponent_le (by norm_num)
        (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hN_le) (sub_nonneg.mpr hs))
    _ = (2 : ENNReal) ^ (-s * (n : ℝ)) * (2 : ENNReal) ^ (n : ℝ) := by
      rw [← ENNReal.rpow_add _ _ (by norm_num) (by norm_num)]
      congr 1
      ring
    _ ≤ (2 : ENNReal) ^ (-s * (n : ℝ)) *
        pressureBallWeight id spikePotential .supremum n (C.center j) r :=
      mul_le_mul' le_rfl hw
    _ ≤ bowenCoverCost id spikePotential .supremum s r C :=
      ENNReal.le_tsum (f := fun i ↦ (2 : ENNReal) ^ (-s * (C.order i : ℝ)) *
        pressureBallWeight id spikePotential .supremum (C.order i) (C.center i) r) j

/-- A single ball of increasing order makes the cutoff content vanish above exponent one. -/
private lemma lowerContent_spike_twice_eq_zero (p₀ : ℕ) (s : ℝ) (hs : 1 < s) (N : ℕ) :
    let h := dyadicRadius (p₀ + 3)
    letI := threePointMetric h (dyadicRadius_pos (p₀ + 3))
    lowerContent id spikePotential .supremum {0} s (dyadicRadius (p₀ + 2)) N = 0 := by
  classical
  let h := dyadicRadius (p₀ + 3)
  let := threePointMetric h (dyadicRadius_pos (p₀ + 3))
  let r := dyadicRadius (p₀ + 2)
  have hlim : Tendsto (fun n : ℕ ↦ (2 : ENNReal) ^ ((1 - s) * (n : ℝ))) atTop (𝓝 0) := by
    have hq : (2 : ENNReal) ^ (1 - s) < 1 :=
      ENNReal.rpow_lt_one_of_one_lt_of_neg (by norm_num) (sub_neg.mpr hs)
    simpa only [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul] using
      ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hq
  apply le_antisymm _ bot_le
  apply ge_of_tendsto hlim
  filter_upwards [eventually_ge_atTop (max 1 N)] with n hn
  let C : BowenCoverFamily (Fin 3) := ⟨{0}, fun _ ↦ (0 : Fin 3), fun _ ↦ n⟩
  have hC : IsBowenCover id {0} r N C := by
    refine ⟨fun _ ↦ hn, ?_⟩
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact Set.mem_iUnion.mpr ⟨⟨0, by simp [C]⟩,
      self_mem_bowenBall id n 0 r (dyadicRadius_pos (p₀ + 2))⟩
  have hcost : bowenCoverCost id spikePotential .supremum s r C ≤
      (2 : ENNReal) ^ ((1 - s) * (n : ℝ)) := by
    calc
      bowenCoverCost id spikePotential .supremum s r C =
          (2 : ENNReal) ^ (-s * (n : ℝ)) *
            pressureBallWeight id spikePotential .supremum n 0 r := by
        simp [bowenCoverCost, C]
      _ ≤ (2 : ENNReal) ^ (-s * (n : ℝ)) * (2 : ENNReal) ^ (n : ℝ) :=
        mul_le_mul' le_rfl (pressureBallWeight_spike_le n 0 r)
      _ = (2 : ENNReal) ^ ((1 - s) * (n : ℝ)) := by
        rw [← ENNReal.rpow_add _ _ (by norm_num) (by norm_num)]
        congr 1
        ring
  exact (iInf_le_of_le C (iInf_le_of_le hC le_rfl)).trans hcost

/-- At radius `2h`, the least supremum potential of a ball covering zero is one. -/
private lemma lowerPressureAt_spike_twice (p₀ : ℕ) :
    let h := dyadicRadius (p₀ + 3)
    letI := threePointMetric h (dyadicRadius_pos (p₀ + 3))
    lowerPressureAt id spikePotential .supremum {0} (dyadicRadius (p₀ + 2)) = 1 := by
  let h := dyadicRadius (p₀ + 3)
  let := threePointMetric h (dyadicRadius_pos (p₀ + 3))
  let r := dyadicRadius (p₀ + 2)
  unfold lowerPressureAt
  apply le_antisymm
  · apply EReal.le_of_forall_lt_iff_le.mp
    intro t ht
    have ht' : 1 < t := by exact_mod_cast ht
    have hz : lowerContentLimit id spikePotential .supremum {0} t r = 0 := by
      unfold lowerContentLimit
      exact iSup_eq_bot.mpr fun N ↦ iSup_eq_bot.mpr fun _ ↦
        lowerContent_spike_twice_eq_zero p₀ t ht' N
    exact iInf_le_of_le t (iInf_le_of_le hz le_rfl)
  · refine le_iInf fun s ↦ le_iInf fun hs ↦ ?_
    by_contra! hlt
    have hs' : s ≤ 1 := le_of_lt (by exact_mod_cast hlt)
    have hbound : (2 : ENNReal) ^ ((1 - s) * ((1 : ℕ) : ℝ)) ≤
        lowerContentLimit id spikePotential .supremum {0} s r :=
      (rpow_le_lowerContent_spike_twice p₀ s hs' 1).trans
        (le_iSup_of_le 1 (le_iSup_of_le (le_refl 1) le_rfl))
    rw [hs] at hbound
    exact (not_le_of_gt (ENNReal.rpow_pos (by norm_num) (by norm_num))) hbound

/-- At radius `4h`, the ball centered at two covers zero but excludes the spike at one. -/
private lemma lowerContentLimit_spike_fourfold_eq_zero
    (p₀ : ℕ) (s : ℝ) (hs : 0 < s) :
    let h := dyadicRadius (p₀ + 3)
    let h_pos : 0 < h := dyadicRadius_pos (p₀ + 3)
    letI := threePointMetric h h_pos
    lowerContentLimit id spikePotential
      .supremum {0} s (dyadicRadius (p₀ + 1)) = 0 := by
  classical
  let h := dyadicRadius (p₀ + 3)
  have h_pos : 0 < h := dyadicRadius_pos (p₀ + 3)
  let m : MetricSpace (Fin 3) := threePointMetric h h_pos
  let r := dyadicRadius (p₀ + 1)
  change @lowerContentLimit (Fin 3) m id
    spikePotential .supremum {0} s r = 0
  have hr : r = 4 * h := by
    dsimp [r, h, dyadicRadius]
    rw [show p₀ + 3 = (p₀ + 1) + 2 by omega, pow_add]
    norm_num
    ring
  have hmem (n : ℕ) : (0 : Fin 3) ∈ bowenBall id n (2 : Fin 3) r := by
    apply Dynamics.mem_dynEntourage.mpr
    intro k _
    change dist (id^[k] (2 : Fin 3)) (id^[k] (0 : Fin 3)) < r
    simp only [Function.iterate_id, id_eq]
    change threePointDist h 2 0 < r
    norm_num [threePointDist, hr]
    linarith
  have hweight (n : ℕ) (hn : 1 ≤ n) :
      pressureBallWeight id spikePotential
        .supremum n (2 : Fin 3) r ≤ 1 := by
    apply iSup₂_le
    intro z hz
    have hz0 := (Dynamics.mem_dynEntourage.mp hz) 0 (show 0 < n by omega)
    change dist (id^[0] (2 : Fin 3)) (id^[0] z) < r at hz0
    change threePointDist h 2 z < r at hz0
    fin_cases z
    · simp [birkhoffSum, spikePotential]
    · norm_num [threePointDist, hr] at hz0
    · simp [birkhoffSum, spikePotential]
  have hlim : Tendsto (fun n : ℕ ↦ (2 : ENNReal) ^ (-s * (n : ℝ)))
      atTop (𝓝 0) := by
    have hq : (2 : ENNReal) ^ (-s) < 1 :=
      ENNReal.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hs)
    simpa only [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul] using
      ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hq
  unfold lowerContentLimit
  apply iSup_eq_bot.mpr
  intro N
  apply iSup_eq_bot.mpr
  intro _
  apply le_antisymm _ bot_le
  apply ge_of_tendsto hlim
  filter_upwards [eventually_ge_atTop (max 1 N)] with n hn
  let C : BowenCoverFamily (Fin 3) := ⟨{0}, fun _ ↦ (2 : Fin 3), fun _ ↦ n⟩
  have hC : IsBowenCover id {0} r N C := by
    refine ⟨fun _ ↦ hn, ?_⟩
    intro x hx
    have hx0 : x = 0 := Set.mem_singleton_iff.mp hx
    subst x
    exact Set.mem_iUnion.mpr ⟨(⟨0, by simp [C]⟩ : C.index), hmem n⟩
  have hcost : bowenCoverCost id spikePotential
      .supremum s r C ≤ (2 : ENNReal) ^ (-s * (n : ℝ)) := by
    have hw := hweight n ((le_max_left 1 N).trans hn)
    simpa [bowenCoverCost, C] using
      mul_le_mul' (le_rfl : (2 : ENNReal) ^ (-s * (n : ℝ)) ≤ _) hw
  exact (iInf_le_of_le C (iInf_le_of_le hC le_rfl)).trans hcost

/-- At radius `4h`, recentering at point two gives critical value zero. -/
private lemma lowerPressureAt_spike_fourfold (p₀ : ℕ) :
    let h := dyadicRadius (p₀ + 3)
    let h_pos : 0 < h := dyadicRadius_pos (p₀ + 3)
    letI := threePointMetric h h_pos
    lowerPressureAt id spikePotential .supremum {0} (dyadicRadius (p₀ + 1)) = 0 := by
  let h := dyadicRadius (p₀ + 3)
  let h_pos : 0 < h := dyadicRadius_pos (p₀ + 3)
  let m : MetricSpace (Fin 3) := threePointMetric h h_pos
  change @lowerPressureAt (Fin 3) m id
    spikePotential .supremum
    {0} (dyadicRadius (p₀ + 1)) = 0
  unfold lowerPressureAt
  apply le_antisymm
  · apply EReal.le_of_forall_lt_iff_le.mp
    intro t ht
    have hz : lowerContentLimit id
        spikePotential .supremum
        {0} t (dyadicRadius (p₀ + 1)) = 0 :=
      lowerContentLimit_spike_fourfold_eq_zero
        p₀ t (EReal.coe_pos.mp ht)
    exact iInf_le_of_le t (iInf_le_of_le hz le_rfl)
  · refine le_iInf fun s ↦ le_iInf fun hs ↦ ?_
    have hs_pos : 0 < s := by
      by_contra hn
      have hge : 1 ≤ lowerContentLimit id
          spikePotential .supremum
          {0} s (dyadicRadius (p₀ + 1)) :=
        one_le_lowerContentLimit_spike (dyadicRadius (p₀ + 1)) s (le_of_not_gt hn)
      rw [hs] at hge
      norm_num at hge
    exact EReal.coe_nonneg.mpr hs_pos.le

/-- At radius `8h`, every ball is the whole space, so the critical value is one. -/
private lemma lowerPressureAt_spike_eightfold (p₀ : ℕ) :
    let h := dyadicRadius (p₀ + 3)
    let h_pos : 0 < h := dyadicRadius_pos (p₀ + 3)
    letI := threePointMetric h h_pos
    lowerPressureAt id spikePotential .supremum {0} (dyadicRadius p₀) = 1 := by
  classical
  let h := dyadicRadius (p₀ + 3)
  have h_pos : 0 < h := dyadicRadius_pos (p₀ + 3)
  let := threePointMetric h h_pos
  have hr : dyadicRadius p₀ = 8 * h := by
    dsimp [h, dyadicRadius]
    norm_num [pow_add]
    ring
  have hball (n : ℕ) (x : Fin 3) :
      bowenBall id n x (dyadicRadius p₀) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    simp only [bowenBall, Dynamics.mem_dynEntourage, Set.mem_ofPred_eq,
      Function.iterate_id, id_eq]
    intro k _
    change threePointDist h x y < dyadicRadius p₀
    rw [hr]
    unfold threePointDist
    split_ifs <;> linarith
  have hweight (n : ℕ) (x : Fin 3) :
      pressureBallWeight id spikePotential .supremum
        n x (dyadicRadius p₀) = (2 : ℝ≥0∞) ^ (n : ℝ) := by
    refine le_antisymm (pressureBallWeight_spike_le n x _) ?_
    unfold pressureBallWeight
    rw [hball]
    refine le_iSup_of_le (1 : Fin 3) (le_iSup_of_le (Set.mem_univ _) ?_)
    simp [birkhoffSum, spikePotential]
  have hcost (s : ℝ) (C : BowenCoverFamily (Fin 3)) :
      bowenCoverCost id spikePotential .supremum
        s (dyadicRadius p₀) C =
        ∑' j, (2 : ℝ≥0∞) ^ ((1 - s) * (C.order j : ℝ)) := by
    unfold bowenCoverCost
    apply tsum_congr
    intro j
    rw [hweight, ← ENNReal.rpow_add _ _ (by norm_num) (by norm_num)]
    congr 1
    ring
  have hnonzero (s : ℝ) (hs : s ≤ 1) :
      1 ≤ lowerContentLimit id spikePotential
        .supremum {0} s (dyadicRadius p₀) := by
    have hlim :
        lowerContent id spikePotential .supremum
          {0} s (dyadicRadius p₀) 1 ≤
        lowerContentLimit id spikePotential .supremum
          {0} s (dyadicRadius p₀) := by
      unfold lowerContentLimit
      exact le_iSup_of_le 1 (le_iSup_of_le (le_refl 1) le_rfl)
    apply le_trans ?_ hlim
    unfold lowerContent
    refine le_iInf fun C ↦ le_iInf fun hC ↦ ?_
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hC.2 (by simp : (0 : Fin 3) ∈ ({0} : Set (Fin 3))))
    rw [hcost]
    calc
      (1 : ℝ≥0∞) = (2 : ℝ≥0∞) ^ (0 : ℝ) := ENNReal.rpow_zero.symm
      _ ≤ (2 : ℝ≥0∞) ^ ((1 - s) * (C.order j : ℝ)) :=
        ENNReal.rpow_le_rpow_of_exponent_le (by norm_num)
          (mul_nonneg (sub_nonneg.mpr hs) (Nat.cast_nonneg _))
      _ ≤ ∑' j, (2 : ℝ≥0∞) ^ ((1 - s) * (C.order j : ℝ)) :=
        ENNReal.le_tsum (f := fun j : C.index ↦
          (2 : ℝ≥0∞) ^ ((1 - s) * (C.order j : ℝ))) j
  have hzero (s : ℝ) (hs : 1 < s) :
      lowerContentLimit id spikePotential
        .supremum {0} s (dyadicRadius p₀) = 0 := by
    have hq : (2 : ℝ≥0∞) ^ (1 - s) < 1 :=
      ENNReal.rpow_lt_one_of_one_lt_of_neg (by norm_num) (sub_neg.mpr hs)
    have ht : Tendsto (fun n : ℕ ↦ (2 : ℝ≥0∞) ^ ((1 - s) * (n : ℝ)))
        atTop (𝓝 0) := by
      simpa only [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul] using
        ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hq
    apply le_antisymm _ zero_le
    unfold lowerContentLimit
    refine iSup_le fun N ↦ iSup_le fun _ ↦ ?_
    apply ge_of_tendsto ht
    filter_upwards [eventually_ge_atTop (max 1 N)] with n hn
    let C : BowenCoverFamily (Fin 3) :=
      ⟨{0}, fun _ ↦ 0, fun _ ↦ n⟩
    have hC : IsBowenCover id {0} (dyadicRadius p₀) N C := by
      refine ⟨fun _ ↦ hn, ?_⟩
      intro x hx
      exact Set.mem_iUnion.mpr ⟨⟨0, by simp [C]⟩, by rw [hball]; trivial⟩
    calc
      lowerContent id spikePotential .supremum
          {0} s (dyadicRadius p₀) N ≤
          bowenCoverCost id spikePotential .supremum
            s (dyadicRadius p₀) C :=
        iInf_le_of_le C (iInf_le_of_le hC le_rfl)
      _ = (2 : ℝ≥0∞) ^ ((1 - s) * (n : ℝ)) := by
        rw [hcost]
        simp [C]
  apply le_antisymm
  · by_contra! hp
    obtain ⟨s, hs, hsp⟩ := EReal.exists_between_coe_real hp
    have hsR : 1 < s := by exact_mod_cast hs
    have hle : lowerPressureAt id spikePotential
        .supremum {0} (dyadicRadius p₀) ≤ (s : EReal) :=
      iInf_le_of_le s (iInf_le_of_le (hzero s hsR) le_rfl)
    exact (not_le.mpr hsp) hle
  · unfold lowerPressureAt
    refine le_iInf fun s ↦ le_iInf fun hs ↦ ?_
    have hsR : 1 ≤ s := by
      by_contra! hlt
      have hb := hnonzero s hlt.le
      rw [hs] at hb
      norm_num at hb
    exact_mod_cast hsR

/-- On a three-point identity system the supremum-weight dyadic values can alternate
between zero and one, even on a prescribed small-scale tail.
Blueprint node `pressure:lower-scale`. -/
theorem lowerPressure_eq_centered_nonmonotone (p₀ : ℕ) :
    ∃ m : MetricSpace (Fin 3),
      letI : MetricSpace (Fin 3) := m
      ∃ φ : Fin 3 → ℝ, UniformContinuous φ ∧
        lowerPressureAt id φ .supremum {0} (dyadicRadius (p₀ + 3)) = 0 ∧
        lowerPressureAt id φ .supremum {0} (dyadicRadius (p₀ + 2)) = 1 ∧
        lowerPressureAt id φ .supremum {0} (dyadicRadius (p₀ + 1)) = 0 ∧
        lowerPressureAt id φ .supremum {0} (dyadicRadius p₀) = 1 := by
  let h := dyadicRadius (p₀ + 3)
  have h_pos : 0 < h := dyadicRadius_pos (p₀ + 3)
  use threePointMetric h h_pos
  use spikePotential
  refine ⟨uniformContinuous_spikePotential h h_pos, ?_, ?_, ?_, ?_⟩
  · exact lowerPressureAt_spike_smallest p₀
  · exact lowerPressureAt_spike_twice p₀
  · exact lowerPressureAt_spike_fourfold p₀
  · exact lowerPressureAt_spike_eightfold p₀

end Kolmogorov.PointToSet
