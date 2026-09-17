import KolmogorovMathlib.AlgorithmicRandomness.ProbabilityBounded
import KolmogorovMathlib.MonotoneComplexity.GacsDayMass

/-!
# What the server must spend to serve a request

The lower bounds on server mass that make the client's win costly. `dyadicLevel r` is the least
`k` with `r ≤ 2 ^ (-k)`, computed on the rationals with `rat_le_half_pow_iff_real` and
`length_le_den` for the bookkeeping. `serves_iff_exists_length_le` restates serving a request as
containing a short enough cell, from which `serves_imp_exists_mass_ge` and
`serves_mass_ge_of_req_gt` extract a mass at least `2 ^ (-m)` for a request larger than
`2 ^ (-(m+1))`. Summed over the children of a coherent server move this gives
`sum_children_mass_ge_of_serves`, the waste estimate the counting argument uses.
-/

namespace Kolmogorov
open MeasureTheory ENNReal BigOperators

/-- The least depth `k` with `r ≤ 2⁻ᵏ`, for a positive rational `r`, and `0` otherwise. -/
def dyadicLevel (r : ℚ) : ℕ :=
  if r > 0 then
    Nat.findGreatest (fun k => (r : ℚ) ≤ (1 / 2)^k) r.den
  else 0

/-- Comparing a rational with a power of one half is the same over the rationals and over the
reals. -/
lemma rat_le_half_pow_iff_real (r : ℚ) (k : ℕ) :
    (r : ℚ) ≤ (1 / 2 : ℚ) ^ k ↔ (r : ℝ) ≤ (1 / 2 : ℝ) ^ k := by
  have h : (1 / 2 : ℝ) = ((1 / 2 : ℚ) : ℝ) := by norm_num
  rw [h, ← Rat.cast_pow]
  exact Rat.cast_le.symm

/-- If a positive rational `r` is at most `2⁻ᵏ` then `k` does not exceed the denominator of `r`. -/
lemma length_le_den {r : ℚ} {k : ℕ} (hr : 0 < r) (h : (r : ℚ) ≤ (1 / 2 : ℚ) ^ k) : k ≤ r.den := by
  have h1 : (r : ℚ) ≤ 1 / (2^k : ℚ) := by
    calc (r : ℚ) ≤ (1 / 2 : ℚ) ^ k := h
      _ = 1^k / (2^k : ℚ) := by rw [div_pow]
      _ = 1 / (2^k : ℚ) := by rw [one_pow]
  have hk_pos : (0 : ℚ) < 2^k := by positivity
  have h2 : r * (2^k : ℚ) ≤ 1 := by
    exact (le_div_iff₀ hk_pos).mp h1
  have h_num : 1 ≤ r.num := by
    have : 0 < r.num := Rat.num_pos.mpr hr
    omega
  have h_den : (2^k : ℚ) ≤ r.den := by
    have h_r_eq : (r : ℚ) = r.num / r.den := by exact Rat.cast_def r
    rw [h_r_eq] at h2
    have h3 : (r.num : ℚ) / (r.den : ℚ) * (2^k : ℚ) ≤ 1 := h2
    have h_den_pos : (0 : ℚ) < r.den := by exact_mod_cast r.pos
    have h4 : (r.num : ℚ) * (2^k : ℚ) ≤ r.den := by
      rw [div_mul_eq_mul_div] at h3
      have := (div_le_iff₀ h_den_pos).mp h3
      linarith
    have h5 : (2^k : ℚ) ≤ (r.num : ℚ) * (2^k : ℚ) := by
      calc (2^k : ℚ) = 1 * (2^k : ℚ) := by ring
        _ ≤ (r.num : ℚ) * (2^k : ℚ) :=
          by exact mul_le_mul_of_nonneg_right (by exact_mod_cast h_num) (by positivity)
    exact le_trans h5 h4
  have h_den2 : 2^k ≤ r.den := by exact_mod_cast h_den
  exact le_trans (k_le_two_pow_k k) h_den2

/-- Powers of one half decrease with the exponent. -/
lemma pow_le_pow_of_le (k m : ℕ) (h : k ≤ m) : (1 / 2 : ℚ) ^ m ≤ (1 / 2 : ℚ) ^ k := by
  have h_pos : (0 : ℚ) ≤ 1 / 2 := by norm_num
  have h_le_one : (1 / 2 : ℚ) ≤ 1 := by norm_num
  exact pow_le_pow_of_le_one h_pos h_le_one h

/-- If `Nat.findGreatest P b` is positive then it satisfies `P`. -/
lemma P_findGreatest {b : ℕ} {P : ℕ → Prop} [DecidablePred P] (h : Nat.findGreatest P b
  > 0) : P (Nat.findGreatest P b) := by
  have h2 : ¬ (Nat.findGreatest P b = 0) := ne_of_gt h
  rw [Nat.findGreatest_eq_zero_iff] at h2
  push Not at h2
  rcases h2 with ⟨n, hn_pos, hn_le, hn_P⟩
  exact Nat.findGreatest_spec hn_le hn_P

/-- An allocation serves a request `r ∈ (0, 1]` exactly when it contains a cell of length at most
`dyadicLevel r`. -/
theorem serves_iff_exists_length_le {a : Allocation} {r : ℚ} (hr : 0 < r) (hr_le : r ≤ 1) :
    Serves a r ↔ ∃ c ∈ a, c.length ≤ dyadicLevel r := by
  dsimp [Serves]
  constructor
  · rintro ⟨c, hc_in, hc_le⟩
    use c, hc_in
    have h_le_den := length_le_den hr (rat_le_half_pow_iff_real r c.length |>.mpr hc_le)
    have h_greatest :=
      Nat.le_findGreatest (P := fun k =>
      (r : ℚ) ≤ (1 / 2 : ℚ)^k) h_le_den (rat_le_half_pow_iff_real r c.length |>.mpr hc_le)
    unfold dyadicLevel
    rw [if_pos hr]
    exact h_greatest
  · rintro ⟨c, hc_in, hc_le⟩
    use c, hc_in
    unfold dyadicLevel at hc_le
    rw [if_pos hr] at hc_le
    rw [← rat_le_half_pow_iff_real]
    by_cases h0 : Nat.findGreatest (fun k => r ≤ (1 / 2) ^ k) r.den = 0
    · rw [h0] at hc_le
      have hc0 : c.length = 0 := by omega
      rw [hc0]
      norm_num
      exact hr_le
    · have h_find_pos : 0 < Nat.findGreatest (fun k => r ≤ (1 / 2) ^ k) r.den := by omega
      have h_P := P_findGreatest h_find_pos
      exact le_trans h_P (pow_le_pow_of_le _ _ hc_le)

/-- If an allocation serves a positive request `r`, one of its cells has mass at least
`2 ^ (-dyadicLevel r)`. -/
theorem serves_imp_exists_mass_ge {a : Allocation} {r : ℚ} (hr : 0 < r) (hServes : Serves a r) :
    ∃ c ∈ a, (2:ℝ≥0∞)^(-(dyadicLevel r : ℤ)) ≤ (2:ℝ≥0∞)^(-(c.length : ℤ)) := by
  dsimp [Serves] at hServes
  rcases hServes with ⟨c, hc_in, hc_le⟩
  use c, hc_in
  have hc_le_rat : (r : ℚ) ≤ (1 / 2 : ℚ) ^ c.length := by
    rw [rat_le_half_pow_iff_real]
    exact hc_le
  have h_le_den := length_le_den hr hc_le_rat
  have h_greatest := Nat.le_findGreatest (P := fun k => (r : ℚ) ≤ (1 / 2 : ℚ)^k) h_le_den hc_le_rat
  have h_dyadic : dyadicLevel r = Nat.findGreatest (fun k => (r : ℚ) ≤ (1 / 2)^k) r.den := by
    unfold dyadicLevel
    rw [if_pos hr]
  rw [h_dyadic]
  have h1 : -(Nat.findGreatest (fun k => r ≤ (1 / 2) ^ k) r.den : ℤ) ≤ -(c.length : ℤ) :=
    neg_le_neg (by exact_mod_cast h_greatest)
  exact ENNReal.zpow_le_of_le (by norm_num) h1

/-- A request larger than `2 ^ (-(m+1))` has dyadic level at most `m`. -/
theorem two_pow_neg_dyadicLevel_gt_of_lt_two_mul {m : ℕ} {r : ℚ}
    (hr : (2 : ℚ) ^ (-(m + 1 : ℤ)) < r) : dyadicLevel r ≤ m := by
  have h_pos : 0 < r := by
    have h_pow_pos : (0 : ℚ) < (2 : ℚ) ^ (-(m + 1 : ℤ)) := by positivity
    exact lt_trans h_pow_pos hr
  unfold dyadicLevel
  rw [if_pos h_pos]
  by_contra h_gt
  push Not at h_gt
  have h_find_pos : 0 < Nat.findGreatest (fun k => r ≤ (1 / 2) ^ k) r.den := by omega
  have h_P := P_findGreatest h_find_pos
  have h_le_pow : (1 / 2 : ℚ) ^ Nat.findGreatest (fun k =>
    r ≤ (1 / 2) ^ k) r.den ≤ (1 / 2 : ℚ) ^ (m + 1) := by
    apply pow_le_pow_of_le
    omega
  have h_r_le : r ≤ (1 / 2 : ℚ) ^ (m + 1) := le_trans h_P h_le_pow
  have h_pow_eq : (1 / 2 : ℚ) ^ (m + 1) = (2 : ℚ) ^ (-(m + 1 : ℤ)) := by
    calc (1 / 2 : ℚ) ^ (m + 1) = 1 ^ (m + 1) / (2 : ℚ) ^ (m + 1) := by rw [div_pow]
      _ = 1 / (2 : ℚ) ^ (m + 1) := by rw [one_pow]
      _ = ((2 : ℚ) ^ (m + 1))⁻¹ := by exact one_div _
      _ = (2 : ℚ) ^ (-(m + 1 : ℤ)) := by
        rw [zpow_neg]
        have h_cast : (2 : ℚ) ^ (m + 1 : ℤ) = (2 : ℚ) ^ (m + 1 : ℕ) := by norm_cast
        rw [h_cast]
  rw [h_pow_eq] at h_r_le
  linarith

/-- An allocation serving a request larger than `2 ^ (-(m+1))` has mass at least `2 ^ (-m)`. -/
lemma serves_mass_ge_of_req_gt {a : Allocation} {m : ℕ} {r : ℚ}
    (h_req : (2 : ℚ) ^ (-(m + 1 : ℤ)) < r) (hServes : Serves a r) :
    (2:ℝ≥0∞)^(- (m:ℤ)) ≤ allocationMass a := by
  have hr_pos : 0 < r := lt_trans (by positivity) h_req
  rcases serves_imp_exists_mass_ge hr_pos hServes with ⟨cy, hcy_in, hcy_le⟩
  have h_m := two_pow_neg_dyadicLevel_gt_of_lt_two_mul h_req
  have h_le1 : (2:ℝ≥0∞)^(-(m:ℤ)) ≤ (2:ℝ≥0∞)^(-(dyadicLevel r : ℤ)) := by
    apply ENNReal.zpow_le_of_le (by norm_num)
    exact neg_le_neg (by exact_mod_cast h_m)
  have h_le3 : uniformMeasure (cantorCylinder cy) ≤ allocationMass a := by
    have h_subset : cantorCylinder cy ⊆ allocationSet a := by
      intro w hw
      simp only [allocationSet, Set.mem_iUnion, exists_prop]
      exact ⟨cy, hcy_in, hw⟩
    exact measure_mono h_subset
  have h_pow : (2:ℝ≥0∞) ^ (-(cy.length : ℤ)) = (2⁻¹ : ℝ≥0∞) ^ cy.length := by
    calc (2:ℝ≥0∞) ^ (-(cy.length : ℤ)) = ((2:ℝ≥0∞) ^ (cy.length : ℤ))⁻¹ :=
      ENNReal.zpow_neg 2 (cy.length : ℤ)
      _ = ((2:ℝ≥0∞) ^ cy.length)⁻¹ := by rw [zpow_natCast]
      _ = (2⁻¹ : ℝ≥0∞) ^ cy.length := by rw [← ENNReal.inv_pow]
  rw [uniformMeasure_cantorCylinder] at h_le3
  calc (2:ℝ≥0∞)^(- (m:ℤ)) ≤ (2:ℝ≥0∞)^(-(dyadicLevel r : ℤ)) := h_le1
    _ ≤ (2:ℝ≥0∞) ^ (-(cy.length : ℤ)) := hcy_le
    _ = (2⁻¹ : ℝ≥0∞) ^ cy.length := h_pow
    _ ≤ allocationMass a := h_le3

/-- If a coherent server move serves, at each child in `S`, a request larger than `2 ^ (-(m+1))`,
then the mass allocated at `x` is at least `|S| * 2 ^ (-m)`. -/
theorem sum_children_mass_ge_of_serves
    {b : ℕ} {sm : ServerMove} (h_coh : serverMoveCoherent b sm)
    (x : GacsDayNode) (m : ℕ)
    (S : Finset (Fin b))
    (req : Fin b → ℚ)
    (h_req : ∀ c ∈ S, (2 : ℚ) ^ (-(m + 1 : ℤ)) < req c)
    (h_served : ∀ c ∈ S, Serves (getAlloc sm (x ++ [c.val])) (req c)) :
    (S.card : ℝ≥0∞) * (2:ℝ≥0∞)^(- (m:ℤ)) ≤ allocationMass (getAlloc sm x) := by
  have h_meas : ∑ c ∈ S, allocationMass (getAlloc sm (x ++ [c.val])) = uniformMeasure (⋃ c ∈ S,
    allocationSet (getAlloc sm (x ++ [c.val]))) := by
    symm
    apply measure_biUnion_finset
    · intro c hc d hd hne
      have hd_alloc : disjointAllocations (getAlloc sm (x ++ [c.val])) (getAlloc sm (x
        ++ [d.val])) :=
        h_coh.2 x c d hne
      exact disjoint_allocationSet_of_disjointAllocations hd_alloc
    · intro c _
      exact measurableSet_allocationSet _
  have h_sum_le : ∑ c ∈ S,
    allocationMass (getAlloc sm (x ++ [c.val])) ≤ allocationMass (getAlloc sm x) := by
    rw [h_meas]
    have h_subset : (⋃ c ∈ S,
      allocationSet (getAlloc sm (x ++ [c.val]))) ⊆ allocationSet (getAlloc sm x) := by
      intro w hw
      simp only [Set.mem_iUnion] at hw
      rcases hw with ⟨c, hc, hw_in⟩
      have h_alloc_subset : allocationSubset (getAlloc sm (x ++ [c.val])) (getAlloc sm x) :=
        h_coh.1 x c
      exact allocationSet_mono_of_allocationSubset h_alloc_subset hw_in
    exact measure_mono h_subset
  calc (S.card : ℝ≥0∞) * (2:ℝ≥0∞)^(- (m:ℤ)) = ∑ c ∈ S, (2:ℝ≥0∞)^(- (m:ℤ)) := by simp
    _ ≤ ∑ c ∈ S, allocationMass (getAlloc sm (x ++ [c.val])) := by
      apply Finset.sum_le_sum
      intro c hc
      apply serves_mass_ge_of_req_gt (h_req c hc) (h_served c hc)
    _ ≤ allocationMass (getAlloc sm x) := h_sum_le

end Kolmogorov
