/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.Geometry.CoverCenters.CenterPolicies

/-!
# Pressure independence of cover centers

Relocating useful Bowen balls compares ambient and self-centered covering contents,
partition sums, capacities, and modified upper pressures. For uniformly continuous
potentials, the variation error vanishes with the radius, so both center policies give
the same lower and upper pressure (blueprint node `geometry:pressure-centers`). The
final comparisons also allow unrestricted decomposition pieces, as used by the
BS dimension independence module.
-/

namespace Kolmogorov.PointToSet
open Filter TopologicalSpace
open scoped Topology ENNReal
variable {X : Type*} [MetricSpace X]
section Pressure
variable [SeparableSpace X] (T : X → X) (hT : Continuous T) (f : X → ℝ)
  (hf : UniformContinuous f) (E : Set X)
include hT hf

omit [SeparableSpace X] hT hf in
/-- Self-centered covers form a subclass of the ambient covers, so the ambient content is at
most the self-centered one. -/
private lemma lowerContent_supremum_le_self (t r : ℝ) (N : ℕ) :
    lowerContent T f .supremum E t (2 * r) N ≤
      lowerContentWithCenters .self T f E t (2 * r) N := by
  unfold lowerContent lowerContentWithCenters
  refine le_iInf fun C => le_iInf fun hC => ?_
  exact iInf_le_of_le C (iInf_le_of_le hC.1 le_rfl)

/-- The cover obtained from `C` by keeping only the balls that meet `E` and moving each
remaining center to a chosen point of `E` in its ball. -/
private noncomputable def relocatedBowenCover (C : BowenCoverFamily X) (r : ℝ) :
    BowenCoverFamily X where
  index := { n | ∃ (hn : n ∈ C.index), (E ∩ bowenBall T (C.order ⟨n, hn⟩) (C.center ⟨n, hn⟩)
    r).Nonempty }
  center := fun j => Classical.choose (Classical.choose_spec j.property)
  order := fun j => C.order ⟨j.val, Classical.choose j.property⟩

omit [SeparableSpace X] hT hf in
/-- Relocating a radius-`r` Bowen cover of `E` gives a radius-`2 * r` Bowen cover of `E`
whose centers all lie in `E`. -/
private lemma isBowenCover_relocatedBowenCover (C :
  BowenCoverFamily X) (r : ℝ) (N : ℕ) (hr : 0 < r)
    (hC : IsBowenCover T E r N C) :
    IsBowenCover T E (2 * r) N (relocatedBowenCover T E
      C r) ∧
    ∀ (j : (relocatedBowenCover T E C r).index),
      (relocatedBowenCover T E C r).center j ∈ E := by
  constructor
  · constructor
    · intro j
      dsimp [relocatedBowenCover]
      have h1 := hC.1
      apply h1
    · intro x hx
      have h2 := hC.2 hx
      simp only [Set.mem_iUnion] at h2 ⊢
      rcases h2 with ⟨j', hj'⟩
      have H_nonempty : (E ∩ bowenBall T (C.order j') (C.center j') r).Nonempty := ⟨x, hx, hj'⟩
      let j_idx : ℕ := j'.val
      have hj_idx : j_idx ∈ C.index := j'.property
      have h_prop : ∃ (hn : j_idx ∈ C.index), (E ∩ bowenBall T (C.order ⟨j_idx, hn⟩) (C.center
        ⟨j_idx, hn⟩) r).Nonempty := ⟨hj_idx, H_nonempty⟩
      let j : (relocatedBowenCover T E C r).index :=
        ⟨j_idx, h_prop⟩
      use j
      dsimp [relocatedBowenCover]
      have hz_prop := Classical.choose_spec (Classical.choose_spec j.property)
      let j_sub : C.index := ⟨j.val, Classical.choose j.property⟩
      have h_j_eq : j' = j_sub := Subtype.ext rfl
      have h_subset := relocateCoverBall T E (C.order j_sub) (C.center j_sub) (Classical.choose
        (Classical.choose_spec j.property)) r hr hz_prop
      have hx_ball : x ∈ bowenBall T (C.order j_sub) (C.center j_sub) r := by
        rw [← h_j_eq]
        exact hj'
      exact h_subset hx_ball
  · intro j
    dsimp [relocatedBowenCover]
    have hz_prop := Classical.choose_spec (Classical.choose_spec j.property)
    exact hz_prop.1

omit [SeparableSpace X] hT hf in
/-- Relocating a cover to radius `2 * r` costs at most the original cover with the exponent
shifted by the potential variation. -/
private lemma bowenCoverCost_relocatedBowenCover_le (C : BowenCoverFamily X) (t r : ℝ)
    (hr : 0 < r)
    (hvar : potentialVariation f (2 * r) < ⊤) :
    bowenCoverCost T f .supremum t (2 * r)
      (relocatedBowenCover T E C r) ≤
      bowenCoverCost T f .supremum (t - (potentialVariation f (2 * r)).toReal) r C := by
  unfold bowenCoverCost
  let I := (relocatedBowenCover T E C r)
  have h1 : (∑' (j : I.index), (2 : ℝ≥0∞) ^ (-t * (I.order j : ℝ)) * pressureBallWeight T f
    .supremum (I.order j) (I.center j) (2 * r)) ≤
            (∑' (j : I.index), (2 : ℝ≥0∞) ^ (-(t - (potentialVariation f (2 * r)).toReal) *
              (C.order ⟨j.val, Classical.choose j.property⟩ : ℝ)) * pressureBallWeight T f
              .supremum (C.order ⟨j.val, Classical.choose j.property⟩) (C.center ⟨j.val,
              Classical.choose j.property⟩) r) := by
    apply ENNReal.tsum_le_tsum
    intro j
    have hz : (Classical.choose (Classical.choose_spec j.property)) ∈ E ∩ bowenBall T (C.order
      ⟨j.val, Classical.choose j.property⟩) (C.center ⟨j.val, Classical.choose j.property⟩) r :=
      Classical.choose_spec (Classical.choose_spec j.property)
    have H := relocateCoverBall_pressure T f E (C.order ⟨j.val, Classical.choose j.property⟩)
      (C.center ⟨j.val, Classical.choose j.property⟩) (Classical.choose (Classical.choose_spec
      j.property)) r hr hz hvar t
    exact H
  let I_set : Set C.index := { j | (E ∩ bowenBall T (C.order j) (C.center j) r).Nonempty }
  have h2 : (∑' (j : I.index), (2 : ℝ≥0∞) ^ (-(t - (potentialVariation f (2 * r)).toReal) *
    (C.order ⟨j.val, Classical.choose j.property⟩ : ℝ)) * pressureBallWeight T f .supremum
    (C.order ⟨j.val, Classical.choose j.property⟩) (C.center ⟨j.val, Classical.choose j.property⟩)
    r) =
            ∑' (j : C.index), I_set.indicator (fun j => (2 : ℝ≥0∞) ^ (-(t - (potentialVariation f
              (2 * r)).toReal) * (C.order j : ℝ)) * pressureBallWeight T f .supremum (C.order j)
              (C.center j) r) j := by
    have h_eq : (∑' (j : I.index), (2 : ℝ≥0∞) ^ (-(t - (potentialVariation f (2 * r)).toReal) *
      (C.order ⟨j.val, Classical.choose j.property⟩ : ℝ)) * pressureBallWeight T f .supremum
      (C.order ⟨j.val, Classical.choose j.property⟩) (C.center ⟨j.val, Classical.choose
      j.property⟩) r) =
                (∑' (j : I_set), (2 : ℝ≥0∞) ^ (-(t - (potentialVariation f (2 * r)).toReal) *
                  (C.order j.val : ℝ)) * pressureBallWeight T f .supremum (C.order j.val)
                  (C.center j.val) r) := by
      let e : I.index ≃ I_set := {
        toFun := fun j => ⟨⟨j.val, Classical.choose j.property⟩, Classical.choose_spec j.property⟩
        invFun := fun j => ⟨j.val.1, ⟨j.val.2, j.property⟩⟩
        left_inv := fun j => Subtype.ext rfl
        right_inv := fun j => Subtype.ext (Subtype.ext rfl)
      }
      exact Equiv.tsum_eq e (fun j => (2 : ℝ≥0∞) ^ (-(t - (potentialVariation f (2 * r)).toReal) *
        (C.order j.val : ℝ)) * pressureBallWeight T f .supremum (C.order j.val) (C.center j.val)
        r)
    rw [h_eq]
    exact tsum_subtype I_set (fun (j : C.index) => (2 : ℝ≥0∞) ^ (-(t - (potentialVariation f (2 *
      r)).toReal) * (C.order j : ℝ)) * pressureBallWeight T f .supremum (C.order j) (C.center j)
      r)
  have h3 : (∑' (j : C.index), I_set.indicator (fun j => (2 : ℝ≥0∞) ^ (-(t - (potentialVariation f
    (2 * r)).toReal) * (C.order j : ℝ)) * pressureBallWeight T f .supremum (C.order j) (C.center
    j) r) j) ≤
            ∑' (j : C.index), (2 : ℝ≥0∞) ^ (-(t - (potentialVariation f (2 * r)).toReal) *
              (C.order j : ℝ)) * pressureBallWeight T f .supremum (C.order j) (C.center j) r := by
    apply ENNReal.tsum_le_tsum
    intro j
    by_cases hj : j ∈ I_set
    · rw [Set.indicator_of_mem hj]
    · have h_zero : I_set.indicator (fun j => (2 : ℝ≥0∞) ^ (-(t - (potentialVariation f (2 *
      r)).toReal) * (C.order j : ℝ)) * pressureBallWeight T f .supremum (C.order j) (C.center j)
      r) j = 0 := by
        apply Set.indicator_apply_eq_zero.mpr
        intro _
        contradiction
      rw [h_zero]
      exact bot_le
  calc
    (∑' (j : I.index), (2 : ℝ≥0∞) ^ (-t * (I.order j : ℝ)) * pressureBallWeight T f .supremum
      (I.order j) (I.center j) (2 * r)) ≤ _ := h1
    _ = _ := h2
    _ ≤ _ := h3

/-- The lower cutoff-content sandwich uses the existing ambient sup-weight content.
Blueprint node `geometry:pressure-centers`. -/
theorem pressureIndependentOfCoverCenters_content (t r : ℝ) (hr : 0 < r)
    (hvar : potentialVariation f (2 * r) < ⊤) (N : ℕ) (hN : 1 ≤ N) :
    lowerContent T f .supremum E t (2 * r) N ≤
        lowerContentWithCenters .self T f E t (2 * r) N ∧
      lowerContentWithCenters .self T f E t (2 * r) N ≤
        lowerContent T f .supremum E (t - (potentialVariation f (2 * r)).toReal) r N := by
  have _ := hT
  have _ := hf
  have _ := (inferInstance : SeparableSpace X)
  have _ := hN
  constructor
  · apply lowerContent_supremum_le_self T f E t r N
  · unfold lowerContentWithCenters lowerContent
    refine le_iInf (fun C => le_iInf (fun hC => ?_))
    refine iInf_le_of_le (relocatedBowenCover T E C r) ?_
    have h3 := isBowenCover_relocatedBowenCover T E C r N
      hr hC
    refine iInf_le_of_le ⟨h3.1, h3.2⟩ ?_
    apply bowenCoverCost_relocatedBowenCover_le T f E C t r hr hvar

/-- The fixed-order partition sandwich has the exponential finite-variation factor.
Blueprint node `geometry:pressure-centers`. -/
theorem pressureIndependentOfCoverCenters_partition (r : ℝ) (hr : 0 < r)
    (hvar : potentialVariation f (2 * r) < ⊤) (n : ℕ) (hn : 1 ≤ n) :
    partitionSum T f .supremum E n (2 * r) ≤
        partitionSumWithCenters .self T f E n (2 * r) ∧
      partitionSumWithCenters .self T f E n (2 * r) ≤
        (2 : ℝ≥0∞) ^ ((n : ℝ) * (potentialVariation f (2 * r)).toReal) *
          partitionSum T f .supremum E n r := by
  have _ := hT
  have _ := hf
  have _ := (inferInstance : SeparableSpace X)
  classical
  constructor
  · unfold partitionSum partitionSumWithCenters
    refine le_iInf fun F => le_iInf fun hF => ?_
    exact iInf_le_of_le F (iInf_le_of_le ⟨hF.1, hF.2.2⟩ le_rfl)
  · let c : ℝ≥0∞ := (2 : ℝ≥0∞) ^
      ((n : ℝ) * (potentialVariation f (2 * r)).toReal)
    have hc0 : c ≠ 0 := by dsimp [c]; positivity
    have hctop : c ≠ ⊤ := by dsimp [c]; finiteness
    change partitionSumWithCenters .self T f E n (2 * r) ≤
      c * partitionSum T f .supremum E n r
    unfold partitionSum
    rw [ENNReal.mul_iInf_of_ne hc0 hctop]
    refine le_iInf fun F => ?_
    rw [ENNReal.mul_iInf_of_ne hc0 hctop]
    refine le_iInf fun hF => ?_
    -- Keep exactly the balls meeting E, and choose a point of each intersection.
    let I := {y : F // (E ∩ bowenBall T n y r).Nonempty}
    let z : I → X := fun y => Classical.choose y.property
    have hz (y : I) : z y ∈ E ∩ bowenBall T n y.val r :=
      Classical.choose_spec y.property
    let G : Set X := Set.range z
    have hGcount : G.Countable := by
      let : Countable F := hF.1.to_subtype
      exact Set.countable_range z
    have hGE : G ⊆ E := by
      rintro x ⟨y, rfl⟩
      exact (hz y).1
    have hGcover : E ⊆ ⋃ y ∈ G, bowenBall T n y (2 * r) := by
      intro x hx
      obtain ⟨y, hy, hxy⟩ : ∃ y ∈ F, x ∈ bowenBall T n y r := by
        simpa only [Set.mem_iUnion, exists_prop] using hF.2 hx
      let i : I := ⟨⟨y, hy⟩, ⟨x, hx, hxy⟩⟩
      have hball : x ∈ bowenBall T n (z i) (2 * r) :=
        relocateCoverBall T E n y (z i) r hr (hz i) hxy
      exact Set.mem_iUnion.mpr ⟨z i,
        Set.mem_iUnion.mpr ⟨Set.mem_range_self i, hball⟩⟩
    have hcost : partitionCoverCost T f .supremum G n (2 * r) ≤
        c * partitionCoverCost T f .supremum F n r := by
      let g : I → G := fun y => ⟨z y, Set.mem_range_self y⟩
      have hg : Function.Surjective g := by
        rintro ⟨x, y, hxy⟩
        exact ⟨y, Subtype.ext hxy⟩
      unfold partitionCoverCost
      calc
        -- Passing from indexed choices to their range only decreases the cost.
        (∑' y : G, pressureBallWeight T f .supremum n y (2 * r)) ≤
            ∑' y : I, pressureBallWeight T f .supremum n (z y) (2 * r) :=
          ENNReal.tsum_le_tsum_comp_of_surjective hg _
        _ ≤ ∑' y : I, c * pressureBallWeight T f .supremum n y.val r := by
          apply ENNReal.tsum_le_tsum
          intro y
          have h := relocateCoverBall_pressure T f E n y.val (z y) r hr (hz y) hvar 0
          simpa only [neg_zero, zero_mul, ENNReal.rpow_zero, one_mul, zero_sub,
            neg_neg, mul_comm (potentialVariation f (2 * r)).toReal (n : ℝ)] using h
        _ = c * ∑' y : I, pressureBallWeight T f .supremum n y.val r :=
          ENNReal.tsum_mul_left
        _ ≤ c * ∑' y : F, pressureBallWeight T f .supremum n y r := by
          gcongr
          exact ENNReal.tsum_comp_le_tsum_of_injective
            (f := fun y : I => y.val) Subtype.val_injective
            (fun y : F => pressureBallWeight T f .supremum n y r)
    unfold partitionSumWithCenters
    exact iInf_le_of_le G (iInf_le_of_le ⟨hGcount, hGE, hGcover⟩ hcost)

/-- The ambient lower content limit is at most the self-centered one. -/
private lemma lowerContentLimit_supremum_le_self (r : ℝ) (hr : 0 < r)
    (hvar : potentialVariation f (2 * r) < ⊤) (t : ℝ) :
    lowerContentLimit T f .supremum E t (2 * r) ≤
      lowerContentLimitWithCenters .self T f E t (2 * r) := by
  have H := pressureIndependentOfCoverCenters_content T hT f hf E t r hr hvar
  unfold lowerContentLimit lowerContentLimitWithCenters
  apply iSup_mono
  intro N
  apply iSup_mono
  intro hN
  exact (H N hN).1

/-- The ambient lower pressure at radius `2 * r` is at most the self-centered one. -/
private lemma lowerPressureAt_supremum_le_self (r : ℝ) (hr : 0 < r)
    (hvar : potentialVariation f (2 * r) < ⊤) :
    lowerPressureAt T f .supremum E (2 * r) ≤
      lowerPressureAtWithCenters .self T f E (2 * r) := by
  unfold lowerPressureAt lowerPressureAtWithCenters
  refine le_iInf (fun t => le_iInf (fun ht => ?_))
  have hz : lowerContentLimit T f .supremum E t (2 * r) = 0 := by
    have h := lowerContentLimit_supremum_le_self
      T hT f hf E r hr hvar t
    rw [ht] at h
    exact le_antisymm h bot_le
  exact iInf_le_of_le t (iInf_le _ hz)

/-- Lower critical pressures inherit the radius-doubled additive-error sandwich.
Blueprint node `geometry:pressure-centers`. -/
theorem pressureIndependentOfCoverCenters_lower (r : ℝ) (hr : 0 < r)
    (hvar : potentialVariation f (2 * r) < ⊤) :
    lowerPressureAt T f .supremum E (2 * r) ≤
        lowerPressureAtWithCenters .self T f E (2 * r) ∧
      lowerPressureAtWithCenters .self T f E (2 * r) ≤
        lowerPressureAt T f .supremum E r +
          ((potentialVariation f (2 * r)).toReal : EReal) := by
  exact ⟨lowerPressureAt_supremum_le_self T hT f hf E r hr hvar,
    lowerPressureAt_self_le_add_variation T f E r hr hvar⟩

omit hT hf in
/-- A finite exponential factor `2 ^ (n * C)` between two sequences becomes an additive
error `C` between their normalized logarithmic rates, and passes through `limsup`,
including infinite endpoints. -/
private lemma limsup_pressureRate_le_add_of_le_mul
    (q1 q2 : ℕ → ℝ≥0∞) (C : ℝ)
    (H : ∀ n, 1 ≤ n →
      q1 n ≤ (2 : ℝ≥0∞) ^ ((n : ℝ) * C) * q2 n) :
    limsup (pressureRate q1) atTop ≤
      limsup (pressureRate q2) atTop + (C : EReal) := by
  have pointwise (f g : ℕ → ℝ≥0∞) (c : ℝ)
      (n : ℕ) (hn : 1 ≤ n)
      (h : g n ≤ f n * (2 : ℝ≥0∞) ^ ((n : ℝ) * c)) :
      pressureRate g n ≤ pressureRate f n + (c : EReal) := by
    have hn0 : n ≠ 0 := by omega
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn0
    have hlpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    let k : ℝ := (Real.log 2)⁻¹ * (n : ℝ)⁻¹
    have hk : 0 ≤ (k : EReal) := EReal.coe_nonneg.mpr
      (mul_nonneg (inv_nonneg.mpr hlpos.le)
        (inv_nonneg.mpr (Nat.cast_nonneg n)))
    have hrate (q : ℕ → ℝ≥0∞) :
        pressureRate q n = ENNReal.log (q n) * (k : EReal) := by
      simp only [pressureRate, ite_eq_right hn0, pressureLog,
        mul_assoc, ← EReal.coe_mul]
      rfl
    rw [hrate, hrate]
    have hlogtwo : ENNReal.log 2 = ((Real.log 2 : ℝ) : EReal) := by
      simpa using ENNReal.log_ofReal_of_pos (by norm_num : (0 : ℝ) < 2)
    have hm := mul_le_mul_of_nonneg_right (ENNReal.log_monotone h) hk
    rw [ENNReal.log_mul_add, ENNReal.log_rpow, hlogtwo,
      EReal.right_distrib_of_nonneg_of_ne_top hk (EReal.coe_ne_top k)] at hm
    have hc : (((n : ℝ) * c : ℝ) : EReal) *
        (Real.log 2 : EReal) * (k : EReal) = (c : EReal) := by
      rw [← EReal.coe_mul, ← EReal.coe_mul]
      congr 1
      dsimp [k]
      field_simp
    rwa [hc] at hm
  have hr : ∀ᶠ n : ℕ in atTop,
      pressureRate q1 n ≤ pressureRate q2 n + (C : EReal) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact pointwise q2 q1 C n hn (by
      simpa only [mul_comm] using H n hn)
  refine (limsup_le_limsup hr).trans ?_
  have hlim := EReal.limsup_add_le
    (u := pressureRate q2) (v := fun _ : ℕ => (C : EReal))
    (f := atTop) (Or.inr (by simp)) (Or.inr (by simp))
  simpa only [Pi.add_def, limsup_const] using hlim

/-- Taking upper logarithmic rates gives the corresponding raw capacity sandwich.
Blueprint node `geometry:pressure-centers`. -/
theorem pressureIndependentOfCoverCenters_capacity (r : ℝ) (hr : 0 < r)
    (hvar : potentialVariation f (2 * r) < ⊤) :
    upperCapacity T f .supremum E (2 * r) ≤
        upperCapacityWithCenters .self T f E (2 * r) ∧
      upperCapacityWithCenters .self T f E (2 * r) ≤
        upperCapacity T f .supremum E r +
          ((potentialVariation f (2 * r)).toReal : EReal) := by
  unfold upperCapacity upperCapacityWithCenters
  constructor
  · simpa using
      (limsup_pressureRate_le_add_of_le_mul
        (fun n => partitionSum T f .supremum E n (2 * r))
        (fun n => partitionSumWithCenters .self T f E n (2 * r))
        0 (fun n hn => by
          simpa using
            (pressureIndependentOfCoverCenters_partition
              T hT f hf E r hr hvar n hn).1))
  · exact limsup_pressureRate_le_add_of_le_mul
      (fun n => partitionSumWithCenters .self T f E n (2 * r))
      (fun n => partitionSum T f .supremum E n r)
      (potentialVariation f (2 * r)).toReal
      (fun n hn => (pressureIndependentOfCoverCenters_partition
        T hT f hf E r hr hvar n hn).2)

/-- The capacity comparison survives modification with self centers in each piece.
Blueprint node `geometry:pressure-centers`. -/
theorem pressureIndependentOfCoverCenters_modified (r : ℝ) (hr : 0 < r)
    (hvar : potentialVariation f (2 * r) < ⊤) :
    modifiedUpperPressure T f .supremum E (2 * r) ≤
        modifiedUpperPressureWithCenters .self T f E (2 * r) ∧
      modifiedUpperPressureWithCenters .self T f E (2 * r) ≤
        modifiedUpperPressure T f .supremum E r +
          ((potentialVariation f (2 * r)).toReal : EReal) := by
  constructor
  · rw [← modifiedUpperPressureWithCenters_ambient T f E (2 * r)]
    unfold modifiedUpperPressureWithCenters
    apply le_iInf
    intro Y
    apply le_iInf
    intro hY
    have H1 : (⨅ Y : ℕ → Set X, ⨅ (_ : (∀ j, Y j ⊆ E) ∧ E ⊆ ⋃ j, Y j), ⨆ j,
      upperCapacityWithCenters .ambient T f (Y j) (2 * r)) ≤ ⨆ j, upperCapacityWithCenters
      .ambient T f (Y j) (2 * r) := by
      exact iInf_le_of_le Y (iInf_le_of_le hY (le_refl _))
    refine le_trans H1 ?_
    apply iSup_mono
    intro j
    have H2 : upperCapacityWithCenters .ambient T f (Y j) (2 * r) = upperCapacity T f .supremum (Y
      j) (2 * r) := rfl
    rw [H2]
    exact (pressureIndependentOfCoverCenters_capacity T hT f hf (Y j) r hr hvar).1
  · rw [← modifiedUpperPressureWithCenters_ambient T f E r]
    unfold modifiedUpperPressureWithCenters
    let c : ℝ := (potentialVariation f (2 * r)).toReal
    apply (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot c)) (Or.inl (EReal.coe_ne_top c))).mp
    apply le_iInf
    intro Y
    apply le_iInf
    intro hY
    have H1 : (⨅ (Y : ℕ → Set X), ⨅ (_ : (∀ (j : ℕ), Y j ⊆ E) ∧ E ⊆ ⋃ (j : ℕ), Y j), ⨆ (j : ℕ),
      upperCapacityWithCenters CoverCenterPolicy.ambient T f (Y j) r) ≤ ⨆ (j : ℕ),
      upperCapacityWithCenters CoverCenterPolicy.ambient T f (Y j) r := by
      have H_1_1 := @iInf_le _ _ _ (fun Y => ⨅ (_ : (∀ j, Y j ⊆ E) ∧ E ⊆ ⋃ j, Y j), ⨆ (j : ℕ),
        upperCapacityWithCenters CoverCenterPolicy.ambient T f (Y j) r) Y
      have H_1_2 := @iInf_le _ _ _ (fun _ => ⨆ (j : ℕ), upperCapacityWithCenters
        CoverCenterPolicy.ambient T f (Y j) r) hY
      exact le_trans H_1_1 H_1_2
    have H_cap : ∀ j, upperCapacityWithCenters .self T f (Y j) (2 * r) ≤ upperCapacityWithCenters
      .ambient T f (Y j) r + (c : EReal) := by
      intro j
      have H3 := (pressureIndependentOfCoverCenters_capacity T hT f hf (Y j) r hr hvar).2
      exact H3
    have H_sup : (⨆ j, upperCapacityWithCenters .self T f (Y j) (2 * r)) ≤ (⨆ j,
      upperCapacityWithCenters .ambient T f (Y j) r) + (c : EReal) := by
      apply iSup_le
      intro j
      refine le_trans (H_cap j) (add_le_add (le_iSup (fun j => upperCapacityWithCenters .ambient T
        f (Y j) r) j) (le_refl _))
    have H_sub : (⨆ j, upperCapacityWithCenters .self T f (Y j) (2 * r)) - (c : EReal) ≤ ⨆ j,
      upperCapacityWithCenters .ambient T f (Y j) r := by
      apply (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot c)) (Or.inl (EReal.coe_ne_top
        c))).mpr
      exact H_sup
    have H_inf : (⨅ (Y : ℕ → Set X), ⨅ (_ : (∀ (j : ℕ), Y j ⊆ E) ∧ E ⊆ ⋃ (j : ℕ), Y j), ⨆ (j : ℕ),
      upperCapacityWithCenters CoverCenterPolicy.self T f (Y j) (2 * r)) - (c : EReal) ≤ (⨆ j,
      upperCapacityWithCenters .self T f (Y j) (2 * r)) - (c : EReal) := by
      apply EReal.sub_le_sub _ (le_refl _)
      exact iInf_le_of_le Y (iInf_le_of_le hY (le_refl _))
    have H1' : ⨆ j, upperCapacityWithCenters .ambient T f (Y j) r ≤ ⨆ (j : ℕ),
      upperCapacityWithCenters CoverCenterPolicy.ambient T f (Y j) r := le_refl _
    refine le_trans H_inf (le_trans H_sub H1')

/-- Both policy quantities converge as positive radii tend to zero, also at infinite values.
Blueprint node `geometry:pressure-centers`. -/
theorem pressureIndependentOfCoverCenters_limit (policy : CoverCenterPolicy) (σ : LimitSide) :
    Tendsto (fun r => σ.choose (lowerPressureAtWithCenters policy T f E r,
      modifiedUpperPressureWithCenters policy T f E r)) (𝓝[Set.Ioi 0] 0)
        (𝓝 (σ.choose (lowerPressure T f 0 E, upperPressure T f 0 E))) := by
  have hamb : Tendsto (fun r => σ.choose
      (lowerPressureAt T f .supremum E r, modifiedUpperPressure T f .supremum E r))
      (𝓝[Set.Ioi 0] 0)
      (𝓝 (σ.choose (lowerPressure T f 0 E, upperPressure T f 0 E))) := by
    cases σ with
    | lower => exact tendsto_lowerPressureAt_supremum T f E hf
    | upper => exact tendsto_modifiedUpperPressure_supremum T f E hT hf
  cases policy with
  | ambient =>
    cases σ with
    | lower => exact hamb
    | upper =>
      simpa only [LimitSide.choose, modifiedUpperPressureWithCenters_ambient] using hamb
  | self =>
    have hhalf : Tendsto (fun r : ℝ => r / 2)
        (𝓝[Set.Ioi 0] 0) (𝓝[Set.Ioi 0] 0) := by
      have hd : Tendsto (fun r : ℝ => r / 2) (𝓝 0) (𝓝 0) := by
        simpa using (tendsto_id : Tendsto (fun r : ℝ => r) (𝓝 0) (𝓝 0)).div_const 2
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · exact hd.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with r hr
        have hr' : 0 < r := hr
        exact half_pos hr'
    have hvar := tendsto_potentialVariation_zero f hf
    have herror : Tendsto (fun r => ((potentialVariation f r).toReal : EReal))
        (𝓝[Set.Ioi 0] 0) (𝓝 0) := by
      exact EReal.tendsto_coe.mpr
        ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hvar)
    have hadd : Tendsto (fun r => σ.choose
        (lowerPressureAt T f .supremum E (r / 2),
          modifiedUpperPressure T f .supremum E (r / 2)) +
        ((potentialVariation f r).toReal : EReal)) (𝓝[Set.Ioi 0] 0)
        (𝓝 (σ.choose (lowerPressure T f 0 E, upperPressure T f 0 E))) := by
      have hc : ContinuousAt (fun p : EReal × EReal => p.1 + p.2)
          (σ.choose (lowerPressure T f 0 E, upperPressure T f 0 E), (0 : EReal)) :=
        EReal.continuousAt_add (Or.inr (by simp)) (Or.inr (by simp))
      simpa only [Function.comp_def, add_zero] using
        hc.tendsto.comp ((hamb.comp hhalf).prodMk_nhds herror)
    have hfin : ∀ᶠ r : ℝ in 𝓝[Set.Ioi 0] 0, potentialVariation f r < ⊤ :=
      hvar.eventually (gt_mem_nhds (by simp : (0 : ℝ≥0∞) < ⊤))
    have hbounds : ∀ᶠ r : ℝ in 𝓝[Set.Ioi 0] 0,
        σ.choose (lowerPressureAt T f .supremum E r,
          modifiedUpperPressure T f .supremum E r) ≤
          σ.choose (lowerPressureAtWithCenters .self T f E r,
            modifiedUpperPressureWithCenters .self T f E r) ∧
        σ.choose (lowerPressureAtWithCenters .self T f E r,
          modifiedUpperPressureWithCenters .self T f E r) ≤
          σ.choose (lowerPressureAt T f .supremum E (r / 2),
            modifiedUpperPressure T f .supremum E (r / 2)) +
            ((potentialVariation f r).toReal : EReal) := by
      filter_upwards [self_mem_nhdsWithin, hfin] with r hr hv
      have hr' : 0 < r := hr
      have hv' : potentialVariation f (2 * (r / 2)) < ⊤ := by
        simpa only [two_mul, add_halves] using hv
      cases σ with
      | lower =>
        simpa only [LimitSide.choose, two_mul, add_halves] using
          pressureIndependentOfCoverCenters_lower T hT f hf E (r / 2) (half_pos hr') hv'
      | upper =>
        simpa only [LimitSide.choose, two_mul, add_halves] using
          pressureIndependentOfCoverCenters_modified T hT f hf E (r / 2) (half_pos hr') hv'
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hamb hadd
      (hbounds.mono fun _ h => h.1) (hbounds.mono fun _ h => h.2)


/-- Both center policies have the existing lower or modified upper scale-zero pressure.
Blueprint node `geometry:pressure-centers`. -/
theorem pressureIndependentOfCoverCenters (policy : CoverCenterPolicy) (σ : LimitSide) :
    coverCenterPressure policy σ T f E =
      σ.choose (lowerPressure T f 0 E, upperPressure T f 0 E) := by
  unfold coverCenterPressure
  exact (pressureIndependentOfCoverCenters_limit T hT f hf E policy σ).limsup_eq

omit [SeparableSpace X] hT hf in
/-- The unrestricted self-centered upper pressure is at most the modified one, since
restricted decompositions are particular unrestricted ones. -/
private lemma unrestrictedSelfUpperPressure_le_modified (T : X → X) (f : X → ℝ) (E : Set X)
    (r : ℝ) :
    unrestrictedSelfUpperPressure T f E r ≤ modifiedUpperPressureWithCenters .self T f E r := by
  unfold unrestrictedSelfUpperPressure modifiedUpperPressureWithCenters
  refine le_iInf (fun Y => le_iInf (fun hY => ?_))
  exact iInf_le_of_le Y (iInf_le_of_le hY.2 (le_refl _))

omit [SeparableSpace X] hT hf in
/-- The fixed-order self-centered partition sum of `Y ∩ E` at radius `2 * r` is at most that
of `Y` at radius `r` times the variation factor `2 ^ (n * ω)`. -/
private lemma self_partitionSum_inter_le_mul
    (r : ℝ) (hr : 0 < r) (hvar : potentialVariation f (2 * r) < ⊤) (Y : Set X) (n : ℕ) (hn : 1 ≤
      n) :
    partitionSumWithCenters .self T f (Y ∩ E) n (2 * r) ≤
      (2 : ℝ≥0∞) ^ ((n : ℝ) * (potentialVariation f (2 * r)).toReal) *
        partitionSumWithCenters .self T f Y n r := by
  classical
  let c : ℝ≥0∞ := (2 : ℝ≥0∞) ^
    ((n : ℝ) * (potentialVariation f (2 * r)).toReal)
  have hc0 : c ≠ 0 := by dsimp [c]; positivity
  have hctop : c ≠ ⊤ := by dsimp [c]; finiteness
  change partitionSumWithCenters .self T f (Y ∩ E) n (2 * r) ≤
    c * partitionSumWithCenters .self T f Y n r
  unfold partitionSumWithCenters
  rw [ENNReal.mul_iInf_of_ne hc0 hctop]
  refine le_iInf fun F => ?_
  rw [ENNReal.mul_iInf_of_ne hc0 hctop]
  refine le_iInf fun hF => ?_
  let I := {y : F // (Y ∩ E ∩ bowenBall T n y r).Nonempty}
  let z : I → X := fun y => Classical.choose y.property
  have hz (y : I) : z y ∈ Y ∩ E ∩ bowenBall T n y.val r :=
    Classical.choose_spec y.property
  let G : Set X := Set.range z
  have hGcount : G.Countable := by
    let _ : Countable F := hF.1.to_subtype
    exact Set.countable_range z
  have hG_subset : G ⊆ Y ∩ E := by
    rintro x ⟨y, rfl⟩
    exact (hz y).1
  have hGcover : Y ∩ E ⊆ ⋃ y ∈ G, bowenBall T n y (2 * r) := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ : ∃ y ∈ F, x ∈ bowenBall T n y r := by
      simpa only [Set.mem_iUnion, exists_prop] using hF.2.2 hx.1
    let i : I := ⟨⟨y, hy⟩, ⟨x, hx, hxy⟩⟩
    have hball : x ∈ bowenBall T n (z i) (2 * r) :=
      relocateCoverBall T (Y ∩ E) n y (z i) r hr (hz i) hxy
    exact Set.mem_iUnion.mpr ⟨z i,
      Set.mem_iUnion.mpr ⟨Set.mem_range_self i, hball⟩⟩
  have hcost : partitionCoverCost T f .supremum G n (2 * r) ≤
      c * partitionCoverCost T f .supremum F n r := by
    let g : I → G := fun y => ⟨z y, Set.mem_range_self y⟩
    have hg : Function.Surjective g := by
      rintro ⟨x, y, hxy⟩
      exact ⟨y, Subtype.ext hxy⟩
    unfold partitionCoverCost
    calc
      (∑' y : G, pressureBallWeight T f .supremum n y (2 * r)) ≤
          ∑' y : I, pressureBallWeight T f .supremum n (z y) (2 * r) :=
        ENNReal.tsum_le_tsum_comp_of_surjective hg _
      _ ≤ ∑' y : I, c * pressureBallWeight T f .supremum n y.val r := by
        apply ENNReal.tsum_le_tsum
        intro y
        have h := relocateCoverBall_pressure T f (Y ∩ E) n y.val (z y) r hr (hz y) hvar 0
        simpa only [neg_zero, zero_mul, ENNReal.rpow_zero, one_mul, zero_sub,
          neg_neg, mul_comm (potentialVariation f (2 * r)).toReal (n : ℝ)] using h
      _ = c * ∑' y : I, pressureBallWeight T f .supremum n y.val r :=
        ENNReal.tsum_mul_left
      _ ≤ c * ∑' y : F, pressureBallWeight T f .supremum n y r := by
        gcongr
        exact ENNReal.tsum_comp_le_tsum_of_injective
          (f := fun y : I => y.val) Subtype.val_injective
          (fun y : F => pressureBallWeight T f .supremum n y r)
  exact iInf_le_of_le G (iInf_le_of_le ⟨hGcount, hG_subset, hGcover⟩ hcost)

omit [SeparableSpace X] hT hf in
/-- Intersecting a piece with `E` and relocating its self-centered covers doubles the radius
at the cost of an additive potential-variation error in the self-centered upper capacity. -/
private theorem self_upperCapacity_inter_le_add
    (r : ℝ) (hr : 0 < r) (hvar : potentialVariation f (2 * r) < ⊤)
    (Y : Set X) :
    upperCapacityWithCenters .self T f (Y ∩ E) (2 * r) ≤
      upperCapacityWithCenters .self T f Y r +
        ((potentialVariation f (2 * r)).toReal : EReal) := by
  unfold upperCapacityWithCenters
  apply limsup_pressureRate_le_add_of_le_mul
  intro n hn
  exact self_partitionSum_inter_le_mul T f E r hr hvar Y n hn

omit [SeparableSpace X] hT hf in
/-- The additive error of `self_upperCapacity_inter_le_add` passes through the supremum over
a sequence of pieces. -/
private lemma iSup_self_upperCapacity_inter_le_add (r : ℝ) (hr : 0 < r)
    (hvar : potentialVariation f (2 * r) < ⊤) (Y : ℕ → Set X) :
    (⨆ j, upperCapacityWithCenters .self T f (Y j ∩ E) (2 * r)) ≤
      (⨆ j, upperCapacityWithCenters .self T f (Y j) r) + ((potentialVariation f (2 * r)).toReal :
        EReal) := by
  let c : ℝ := (potentialVariation f (2 * r)).toReal
  have h1 : ∀ j, upperCapacityWithCenters .self T f (Y j ∩ E) (2 * r) ≤ upperCapacityWithCenters
    .self T f (Y j) r + (c : EReal) := fun j => self_upperCapacity_inter_le_add T f E r hr
    hvar (Y j)
  have h2 : ∀ j, upperCapacityWithCenters .self T f (Y j ∩ E) (2 * r) ≤ (⨆ j,
    upperCapacityWithCenters .self T f (Y j) r) + (c : EReal) := fun j => le_trans (h1 j)
    (add_le_add (le_iSup (f := fun j => upperCapacityWithCenters .self T f (Y j) r) j) (le_refl
    _))
  exact iSup_le h2

omit [SeparableSpace X] hT hf in
/-- The modified self-centered upper pressure at radius `2 * r` is at most the unrestricted
one at radius `r` plus the potential variation: pieces of an unrestricted decomposition are
intersected with `E`. -/
private lemma modified_self_le_unrestricted_add (r : ℝ) (hr : 0 < r)
    (_hvar : potentialVariation f (2 * r) < ⊤) :
    modifiedUpperPressureWithCenters .self T f E (2 * r) ≤
      unrestrictedSelfUpperPressure T f E r + ((potentialVariation f (2 * r)).toReal : EReal) := by
  unfold modifiedUpperPressureWithCenters unrestrictedSelfUpperPressure
  let c : ℝ := (potentialVariation f (2 * r)).toReal
  apply (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot c)) (Or.inl (EReal.coe_ne_top c))).mp
  refine le_iInf (fun Y => ?_)
  refine le_iInf (fun hY => ?_)
  let Y' := fun j => Y j ∩ E
  have hY' : (∀ j, Y' j ⊆ E) ∧ E ⊆ ⋃ j, Y' j := by
    constructor
    · intro j x hx
      exact hx.2
    · intro x hx
      have h1 := hY hx
      simp only [Set.mem_iUnion] at h1 ⊢
      rcases h1 with ⟨j, hj⟩
      exact ⟨j, hj, hx⟩
  have H1 := @iInf_le _ _ _ (fun Y => ⨅ (_ : (∀ j, Y j ⊆ E) ∧ E ⊆ ⋃ j, Y j), ⨆ j,
    upperCapacityWithCenters .self T f (Y j) (2 * r)) Y'
  have H2 := @iInf_le _ _ _ (fun (_ : (∀ j, Y' j ⊆ E) ∧ E ⊆ ⋃ j, Y' j) => ⨆ j,
    upperCapacityWithCenters .self T f (Y' j) (2 * r)) hY'
  have H3 : (⨅ (Y : ℕ → Set X), ⨅ (_ : (∀ (j : ℕ), Y j ⊆ E) ∧ E ⊆ ⋃ (j : ℕ), Y j), ⨆ (j : ℕ),
    upperCapacityWithCenters CoverCenterPolicy.self T f (Y j) (2 * r)) - ↑c ≤ (⨆ (j : ℕ),
    upperCapacityWithCenters CoverCenterPolicy.self T f (Y' j) (2 * r)) - ↑c := by
    apply EReal.sub_le_sub _ (le_refl _)
    exact le_trans H1 H2
  have H4_hyp : (⨆ j, upperCapacityWithCenters .self T f (Y j ∩ E) (2 * r)) ≤ (⨆ j,
    upperCapacityWithCenters .self T f (Y j) r) + ↑c :=
      iSup_self_upperCapacity_inter_le_add T f E r hr _hvar Y
  have H4 : (⨆ j, upperCapacityWithCenters .self T f (Y j ∩ E) (2 * r)) - ↑c ≤ ⨆ j,
    upperCapacityWithCenters .self T f (Y j) r := by
    apply (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot c)) (Or.inl (EReal.coe_ne_top c))).mpr
    exact H4_hyp
  exact le_trans H3 H4

/-- Unrestricted self decompositions compare to restricted ones only after relocation.
No same-radius monotonicity under intersection is assumed.
Blueprint node `geometry:pressure-centers`. -/
theorem pressureIndependentOfCoverCenters_unrestricted_sandwich (r : ℝ) (hr : 0 < r)
    (hvar : potentialVariation f (2 * r) < ⊤) :
    unrestrictedSelfUpperPressure T f E r ≤ modifiedUpperPressureWithCenters .self T f E r ∧
      modifiedUpperPressureWithCenters .self T f E (2 * r) ≤
        unrestrictedSelfUpperPressure T f E r +
          ((potentialVariation f (2 * r)).toReal : EReal) := by
  have _ := hT
  have _ := hf
  have _ := (inferInstance : SeparableSpace X)
  constructor
  · exact unrestrictedSelfUpperPressure_le_modified T f E r
  · exact modified_self_le_unrestricted_add T f E r hr hvar

end Pressure
end Kolmogorov.PointToSet
