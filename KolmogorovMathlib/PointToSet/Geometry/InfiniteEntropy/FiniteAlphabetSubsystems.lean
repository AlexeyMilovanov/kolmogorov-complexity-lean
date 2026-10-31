/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.Conformal.Classical
import KolmogorovMathlib.PointToSet.Conformal.Defs
import KolmogorovMathlib.PointToSet.Pressure.Lower
import KolmogorovMathlib.PointToSet.Pressure.Upper
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.UniformOn

/-!
# Pressure and cylinder covers of finite-alphabet subsystems

Inside the full Baire shift, `finiteAlphabetSubsystem m` consists of sequences with symbols
less than `m`. For the first-difference metric and constant potential `-s`, its lower and
countably modified upper pressures both equal `Real.logb 2 m - s`. The proofs use explicit
cylinder covers and an ambient Bernoulli outer measure, allowing centers outside the subsystem.

This establishes the pressure calculation in blueprint node `geometry:finite-alphabet-pressure`.
The finite covers with controlled diameter cost and the Bernoulli measure are also used in
`NoBowenRoot` to compute Hausdorff dimension and construct the infinite-entropy counterexample.
-/

namespace Kolmogorov.PointToSet

open scoped ENNReal

/-- Sequences using only the first `m` natural symbols, inside the full Baire shift.
Blueprint node `geometry:finite-alphabet-pressure`. -/
def finiteAlphabetSubsystem (m : ℕ) : Set (ℕ → ℕ) :=
  {x | ∀ j, x j < m}

/-- An order-`n` Bowen ball of the shift at radius `2⁻ᵖ` fixes exactly `n + p` symbols. -/
private lemma bowenBall_shift_eq_cylinder
    [MetricSpace (ℕ → ℕ)]
    (hd : ∀ x y : ℕ → ℕ, x ≠ y → dist x y = (1 / 2 : ℝ) ^ PiNat.firstDiff x y)
    (x : ℕ → ℕ) (n p : ℕ) (hn : 1 ≤ n) :
    bowenBall (fun y j ↦ y (j + 1)) n x (dyadicRadius p) =
      PiNat.cylinder x (n + p) := by
  have hr : dyadicRadius p = (1 / 2 : ℝ) ^ p := by simp [dyadicRadius, one_div]
  rw [hr]
  rw [symbolic_orbitComplexity (1 / 2) (by norm_num) (by norm_num) hd x n p hn]
  ext y
  rw [Metric.mem_ball, dist_comm]
  by_cases hxy : x = y
  · subst y
    simp
  · rw [hd x y hxy, pow_lt_pow_iff_right_of_lt_one₀ (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)]
    rw [PiNat.mem_cylinder_comm, PiNat.mem_cylinder_iff_le_firstDiff hxy]
    omega

/-- The Birkhoff sum of a constant potential is its value times the orbit length. -/
private lemma birkhoffSum_const {X : Type*} (T : X → X) (a : ℝ) (n : ℕ) (x : X) :
    birkhoffSum T (fun _ ↦ a) n x = a * n := by
  simp [birkhoffSum, mul_comm]

open MeasureTheory in
/-- The uniform product measure on `Fin m` sequences induces an ambient outer measure of
mass one on the subsystem, with length-`L` cylinder mass at most `m⁻ᴸ`. -/
lemma exists_outerMeasure_finiteAlphabetSubsystem
    (m : ℕ) (hm : 2 ≤ m) :
    ∃ μ : OuterMeasure (ℕ → ℕ),
      μ (finiteAlphabetSubsystem m) = 1 ∧
      ∀ (x : ℕ → ℕ) (L : ℕ),
        μ (PiNat.cylinder x L ∩ finiteAlphabetSubsystem m) ≤ ((m : ℝ≥0∞) ^ L)⁻¹ := by
  classical
  let : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
  let ν : Measure (ℕ → Fin m) :=
    Measure.infinitePi (fun _ : ℕ ↦ ProbabilityTheory.uniformOn (Set.univ : Set (Fin m)))
  let e : (ℕ → Fin m) → (ℕ → ℕ) := fun z j ↦ (z j).val
  let μ : OuterMeasure (ℕ → ℕ) := OuterMeasure.map e ν.toOuterMeasure
  refine ⟨μ, ?_, ?_⟩
  · have hpre : e ⁻¹' finiteAlphabetSubsystem m = Set.univ := by
      ext z
      simp [e, finiteAlphabetSubsystem]
    change ν.toOuterMeasure (e ⁻¹' finiteAlphabetSubsystem m) = 1
    rw [hpre]
    exact measure_univ
  · intro x L
    by_cases hx : ∀ j < L, x j < m
    · let c : ℕ → Fin m := fun j ↦ if hj : j < L then ⟨x j, hx j hj⟩ else ⟨0, by omega⟩
      have hpre : e ⁻¹' (PiNat.cylinder x L ∩ finiteAlphabetSubsystem m) =
          Set.pi (Finset.range L : Set ℕ) (fun j ↦ {c j}) := by
        ext z
        simp only [Set.mem_preimage, Set.mem_inter_iff, PiNat.mem_cylinder_iff,
          finiteAlphabetSubsystem, Set.mem_ofPred_eq, Set.mem_pi, Finset.mem_coe,
          Finset.mem_range, Set.mem_singleton_iff]
        constructor
        · intro hz j hj
          apply Fin.ext
          simpa [e, c, hj] using hz.1 j hj
        · intro hz
          refine ⟨fun j hj ↦ ?_, fun j ↦ (z j).isLt⟩
          have := congrArg Fin.val (hz j hj)
          simpa [e, c, hj] using this
      change ν.toOuterMeasure (e ⁻¹' (PiNat.cylinder x L ∩ finiteAlphabetSubsystem m)) ≤ _
      rw [hpre]
      change ν (Set.pi (Finset.range L : Set ℕ) (fun j ↦ {c j})) ≤ _
      rw [Measure.infinitePi_pi _ (fun _ _ ↦ measurableSet_singleton _)]
      simp only [ProbabilityTheory.uniformOn_univ, Measure.count_singleton,
        Fintype.card_fin, one_div, Finset.prod_const, Finset.card_range]
      rw [ENNReal.inv_pow]
    · push Not at hx
      obtain ⟨j, hj, hjm⟩ := hx
      have hpre : e ⁻¹' (PiNat.cylinder x L ∩ finiteAlphabetSubsystem m) = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro z hz
        have heq := PiNat.mem_cylinder_iff.mp hz.1 j hj
        have hlt := hz.2 j
        omega
      change ν.toOuterMeasure (e ⁻¹' (PiNat.cylinder x L ∩ finiteAlphabetSubsystem m)) ≤ _
      rw [hpre, measure_empty]
      exact zero_le

/-- A cylinder mass bound gives the corresponding bound for ambient Bowen balls. -/
private lemma outerMeasure_bowenBall_inter_le
    [MetricSpace (ℕ → ℕ)]
    (hd : ∀ x y : ℕ → ℕ, x ≠ y → dist x y = (1 / 2 : ℝ) ^ PiNat.firstDiff x y)
    (m : ℕ) (μ : MeasureTheory.OuterMeasure (ℕ → ℕ))
    (hcyl : ∀ (x : ℕ → ℕ) (L : ℕ),
      μ (PiNat.cylinder x L ∩ finiteAlphabetSubsystem m) ≤ ((m : ℝ≥0∞) ^ L)⁻¹)
    (x : ℕ → ℕ) (n k : ℕ) (hn : 1 ≤ n) :
    μ (bowenBall (fun y j ↦ y (j + 1)) n x (dyadicRadius k) ∩ finiteAlphabetSubsystem m) ≤
      ((m : ℝ≥0∞) ^ (n + k))⁻¹ := by
  rw [bowenBall_shift_eq_cylinder hd x n k hn]
  exact hcyl x (n + k)

/-- Below the alphabet logarithm, a centered pressure weight dominates the mass bound
for a cylinder of length `n + k`. -/
private lemma inv_alphabet_pow_le_pressure_cost
    (m : ℕ) (hm : 2 ≤ m) (s t : ℝ) (n k : ℕ) (ht : t + s < Real.logb 2 m) :
    ((m : ℝ≥0∞) ^ (n + k))⁻¹ ≤
      (2 : ℝ≥0∞) ^ (-t * (n : ℝ)) * (2 : ℝ≥0∞) ^ (-s * (n : ℝ)) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hmone : (1 : ℝ≥0∞) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hreal : (2 : ℝ) ^ (t + s) ≤ m :=
    (Real.le_logb_iff_rpow_le (by norm_num) hmpos).mp ht.le
  have hbase : (2 : ℝ≥0∞) ^ (t + s) ≤ m := by
    have h := ENNReal.ofReal_le_ofReal hreal
    rw [← ENNReal.ofReal_rpow_of_pos (by norm_num)] at h
    simpa only [ENNReal.ofReal_ofNat, ENNReal.ofReal_natCast] using h
  calc
    ((m : ℝ≥0∞) ^ (n + k))⁻¹ ≤ ((m : ℝ≥0∞) ^ n)⁻¹ :=
      ENNReal.inv_le_inv.mpr (pow_le_pow_right' hmone (Nat.le_add_right n k))
    _ ≤ (((2 : ℝ≥0∞) ^ (t + s)) ^ n)⁻¹ :=
      ENNReal.inv_le_inv.mpr (pow_le_pow_left' hbase n)
    _ = _ := by
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, ← ENNReal.rpow_neg,
        ← ENNReal.rpow_add _ _ (by norm_num) (by norm_num)]
      congr 1
      ring

/-- Below the alphabet logarithm, every Bowen cover has cost at least one, so the
limiting lower content is positive. -/
private lemma lowerContentLimit_finiteAlphabetSubsystem_pos [MetricSpace (ℕ → ℕ)]
    (hd : ∀ x y : ℕ → ℕ, x ≠ y → dist x y = (1 / 2 : ℝ) ^ PiNat.firstDiff x y)
    (m : ℕ) (hm : 2 ≤ m) (s t : ℝ) (k : ℕ) (ht : t + s < Real.logb 2 m) :
    (0 : ℝ≥0∞) < lowerContentLimit (fun y j ↦ y (j + 1)) (fun _ ↦ -s) .centered
      (finiteAlphabetSubsystem m) t (dyadicRadius k) := by
  classical
  obtain ⟨μ, hμ, hcyl⟩ :=
    exists_outerMeasure_finiteAlphabetSubsystem m hm
  have hcontent : (1 : ℝ≥0∞) ≤
      lowerContent (fun y j ↦ y (j + 1)) (fun _ ↦ -s) .centered
        (finiteAlphabetSubsystem m) t (dyadicRadius k) 1 := by
    unfold lowerContent
    refine le_iInf fun C ↦ le_iInf fun hC ↦ ?_
    let B : C.index → Set (ℕ → ℕ) := fun j ↦
      bowenBall (fun y j ↦ y (j + 1)) (C.order j) (C.center j) (dyadicRadius k) ∩
        finiteAlphabetSubsystem m
    have hcover : finiteAlphabetSubsystem m ⊆ ⋃ j, B j := by
      intro x hx
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hC.2 hx)
      exact Set.mem_iUnion.mpr ⟨j, hj, hx⟩
    calc
      (1 : ℝ≥0∞) = μ (finiteAlphabetSubsystem m) := hμ.symm
      _ ≤ μ (⋃ j, B j) := MeasureTheory.measure_mono hcover
      _ ≤ ∑' j, μ (B j) := MeasureTheory.measure_iUnion_le B
      _ ≤ bowenCoverCost (fun y j ↦ y (j + 1)) (fun _ ↦ -s) .centered
          t (dyadicRadius k) C := by
        unfold bowenCoverCost
        apply ENNReal.tsum_le_tsum
        intro j
        have hmass :=
          outerMeasure_bowenBall_inter_le
            hd m μ hcyl (C.center j) (C.order j) k (by simpa using hC.1 j)
        have hcost :=
          inv_alphabet_pow_le_pressure_cost
            m hm s t (C.order j) k ht
        simpa only [pressureBallWeight,
          birkhoffSum_const] using hmass.trans hcost
  have hlimit : (1 : ℝ≥0∞) ≤
      lowerContentLimit (fun y j ↦ y (j + 1)) (fun _ ↦ -s) .centered
        (finiteAlphabetSubsystem m) t (dyadicRadius k) :=
    le_iSup_of_le 1 (le_iSup_of_le (le_refl 1) hcontent)
  exact lt_of_lt_of_le zero_lt_one hlimit

/-- Extending all words of length `n + k` by zeros gives a Bowen cover of order `n`
with cost at most `m^(n + k) * 2^(-(t + s) * n)`. -/
private lemma exists_bowenCover_finiteAlphabetSubsystem
    [MetricSpace (ℕ → ℕ)]
    (hd : ∀ x y : ℕ → ℕ, x ≠ y → dist x y = (1 / 2 : ℝ) ^ PiNat.firstDiff x y)
    (m : ℕ) (s t : ℝ) (k N n : ℕ) (hn : max 1 N ≤ n) :
    ∃ C : BowenCoverFamily (ℕ → ℕ),
      IsBowenCover (fun y j ↦ y (j + 1)) (finiteAlphabetSubsystem m) (dyadicRadius k) N C ∧
      bowenCoverCost (fun y j ↦ y (j + 1)) (fun _ ↦ -s) .centered t (dyadicRadius k) C ≤
        ((m : ℝ≥0∞) ^ (n + k) * (2 : ℝ≥0∞) ^ (-(t + s) * (n : ℝ))) := by
  have hn1 : 1 ≤ n := le_trans (le_max_left _ _) hn
  obtain ⟨f⟩ : Nonempty (Fin (m ^ (n + k)) ≃ (Fin (n + k) → Fin m)) :=
    ⟨finFunctionFinEquiv.symm⟩
  let c : Fin (m ^ (n + k)) → (ℕ → ℕ) :=
    fun i j ↦ if hj : j < n + k then (f i ⟨j, hj⟩ : ℕ) else 0
  let S : Set ℕ := {idx | idx < m ^ (n + k)}
  let C_fam : BowenCoverFamily (ℕ → ℕ) :=
    { index := S
      center := fun idx ↦ c ⟨idx.val, idx.property⟩
      order := fun _ ↦ n }
  refine ⟨C_fam, ?_, ?_⟩
  · unfold IsBowenCover
    refine ⟨fun _ ↦ hn, ?_⟩
    intro y hy
    let y_pref : Fin (n + k) → Fin m := fun j ↦ ⟨y j.val, hy j.val⟩
    let i : Fin (m ^ (n + k)) := f.symm y_pref
    refine Set.mem_iUnion.mpr ⟨⟨i.val, i.isLt⟩, ?_⟩
    dsimp only [C_fam]
    rw [bowenBall_shift_eq_cylinder hd _ n k hn1]
    intro j hj
    have h_f : f i = y_pref := Equiv.apply_symm_apply f y_pref
    simp [c, hj, h_f, y_pref]
  · have hcost : bowenCoverCost (fun y j ↦ y (j + 1)) (fun _ ↦ -s) .centered
        t (dyadicRadius k) C_fam =
        ∑' _ : C_fam.index, (2 : ℝ≥0∞) ^ (-(t + s) * (n : ℝ)) := by
      unfold bowenCoverCost
      refine tsum_congr fun j ↦ ?_
      have h_ord : C_fam.order j = n := rfl
      simp only [pressureBallWeight, birkhoffSum_const, h_ord]
      rw [← ENNReal.rpow_add _ _ (by norm_num) (by norm_num)]
      congr 1; ring
    have H_S : C_fam.index ≃ Fin (m ^ (n + k)) := (Fin.equivSubtype).symm
    refine le_of_eq ?_
    rw [hcost]
    rw [Equiv.tsum_eq H_S (fun _ ↦ (2 : ℝ≥0∞) ^ (-(t + s) * (n : ℝ)))]
    rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [Nat.cast_pow]

open Filter Topology MeasureTheory
open scoped Topology

/-- Above the alphabet logarithm, the costs of equal-order cylinder covers tend to zero. -/
private lemma tendsto_cylinder_cover_cost_zero
    (m : ℕ) (hm : 2 ≤ m) (s t : ℝ) (k : ℕ) (ht : Real.logb 2 m < t + s) :
    Filter.Tendsto (fun n : ℕ ↦ ((m : ℝ≥0∞) ^ (n + k) * (2 : ℝ≥0∞) ^ (-(t + s) * (n : ℝ))))
      Filter.atTop (𝓝 0) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hmE : (2 : ℝ≥0∞) ^ Real.logb 2 m = m := by
    rw [← ENNReal.ofReal_ofNat (n := 2), ENNReal.ofReal_rpow_of_pos (by norm_num),
      Real.rpow_logb (by norm_num) (by norm_num) hmpos, ENNReal.ofReal_natCast]
  have hbase : (m : ℝ≥0∞) * (2 : ℝ≥0∞) ^ (-(t + s)) < 1 := by
    rw [← hmE, ← ENNReal.rpow_add _ _ (by norm_num) (by norm_num),
      ← ENNReal.rpow_zero (x := 2)]
    exact ENNReal.rpow_lt_rpow_of_exponent_lt (by norm_num) ENNReal.coe_ne_top
      (by linarith)
  have hlim := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hbase
  have hmul := ENNReal.Tendsto.const_mul hlim
    (Or.inr (ENNReal.pow_ne_top (ENNReal.natCast_ne_top m)) :
      (0 : ℝ≥0∞) ≠ 0 ∨ (m : ℝ≥0∞) ^ k ≠ ⊤)
  convert hmul using 1
  · ext n
    rw [pow_add, mul_pow, ← ENNReal.rpow_natCast (x := (2 : ℝ≥0∞) ^ (-(t + s))),
      ← ENNReal.rpow_mul]
    ring
  · rw [mul_zero]

/-- Above the alphabet logarithm, arbitrarily long cylinder covers make the limiting
lower content vanish. -/
private lemma lowerContentLimit_finiteAlphabetSubsystem_eq_zero [MetricSpace (ℕ → ℕ)]
    (hd : ∀ x y : ℕ → ℕ, x ≠ y → dist x y = (1 / 2 : ℝ) ^ PiNat.firstDiff x y)
    (m : ℕ) (hm : 2 ≤ m) (s t : ℝ) (k : ℕ) (ht : Real.logb 2 m < t + s) :
    lowerContentLimit (fun y j ↦ y (j + 1)) (fun _ ↦ -s) .centered
      (finiteAlphabetSubsystem m) t (dyadicRadius k) = 0 := by
  apply le_antisymm ?_ bot_le
  refine iSup_le fun N ↦ iSup_le fun _ ↦ ?_
  have hlim := tendsto_cylinder_cover_cost_zero m hm s t k ht
  apply ge_of_tendsto hlim
  filter_upwards [eventually_ge_atTop (max 1 N)] with n hn
  obtain ⟨C, hcover, hcost⟩ :=
    exists_bowenCover_finiteAlphabetSubsystem hd m s t k N n hn
  exact (iInf_le_of_le C (iInf_le_of_le hcover le_rfl)).trans hcost

/-- At every dyadic radius, lower pressure is the alphabet logarithm minus `s`. -/
private lemma lowerPressureAt_finiteAlphabetSubsystem [MetricSpace (ℕ → ℕ)]
    (hd : ∀ x y : ℕ → ℕ, x ≠ y → dist x y = (1 / 2 : ℝ) ^ PiNat.firstDiff x y)
    (m : ℕ) (hm : 2 ≤ m) (s : ℝ) (p : ℕ) :
    lowerPressureAt (fun y j ↦ y (j + 1)) (fun _ ↦ -s) .centered
      (finiteAlphabetSubsystem m) (dyadicRadius p) = ((Real.logb 2 m - s : ℝ) : EReal) := by
  unfold lowerPressureAt
  apply le_antisymm
  · apply EReal.le_of_forall_lt_iff_le.mp
    intro t ht
    have ht' : Real.logb 2 m - s < t :=
      EReal.coe_lt_coe_iff.mp ht
    have hz :=
      lowerContentLimit_finiteAlphabetSubsystem_eq_zero
        hd m hm s t p (by linarith)
    exact iInf_le_of_le t (iInf_le_of_le hz le_rfl)
  · refine le_iInf fun t ↦ le_iInf fun hz ↦ ?_
    apply EReal.coe_le_coe_iff.mpr
    by_contra h
    have ht : t + s < Real.logb 2 m := by
      have hlt : t < Real.logb 2 m - s := lt_of_not_ge h
      linarith
    have hpos :=
      lowerContentLimit_finiteAlphabetSubsystem_pos
        hd m hm s t p ht
    rw [hz] at hpos
    exact (lt_irrefl (0 : ℝ≥0∞)) hpos

/-- The lower pressure of the finite-alphabet subsystem for potential `-s` is `logb 2 m - s`,
using ambient Baire-space centers.
Blueprint node `geometry:finite-alphabet-pressure`. -/
theorem finiteAlphabetSubsystemPressure [MetricSpace (ℕ → ℕ)]
    (hd : ∀ x y : ℕ → ℕ, x ≠ y → dist x y = (1 / 2 : ℝ) ^ PiNat.firstDiff x y)
    (m : ℕ) (hm : 2 ≤ m) (s : ℝ) :
    lowerPressure (fun y j => y (j + 1)) (fun _ => -s) 0 (finiteAlphabetSubsystem m) =
      ((Real.logb 2 m - s : ℝ) : EReal) := by
  simp only [lowerPressure, lowerPressureAt_finiteAlphabetSubsystem hd m hm s,
    iSup_const, iSup_pos, Nat.zero_le]

section

open Filter MeasureTheory
open scoped Topology

/-- Every countable cover of a set of mass one contains a piece whose intersection
with that set has positive outer measure. -/
private lemma exists_pos_outerMeasure_inter_of_cover
    (m : ℕ) (μ : OuterMeasure (ℕ → ℕ))
    (hμ : μ (finiteAlphabetSubsystem m) = 1)
    (E : ℕ → Set (ℕ → ℕ)) (hE : finiteAlphabetSubsystem m ⊆ ⋃ i, E i) :
    ∃ i, 0 < μ (E i ∩ finiteAlphabetSubsystem m) := by
  by_contra h
  have hz : ∀ i, μ (E i ∩ finiteAlphabetSubsystem m) = 0 := by
    simpa only [not_exists, not_lt, nonpos_iff_eq_zero] using h
  have hcover : finiteAlphabetSubsystem m ⊆ ⋃ i, E i ∩ finiteAlphabetSubsystem m := by
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hE hx)
    exact Set.mem_iUnion.mpr ⟨i, hi, hx⟩
  have hle := (measure_mono (μ := μ) hcover).trans
    (measure_iUnion_le (μ := μ) (fun i ↦ E i ∩ finiteAlphabetSubsystem m))
  simp [hμ, hz] at hle

/-- A positive finite mass factor and a fixed cylinder-length offset leave the
normalized logarithmic growth rate equal to `logb 2 m - s`. -/
private lemma tendsto_pressureRate_cylinder_cost
    (m : ℕ) (hm : 2 ≤ m) (s : ℝ) (p : ℕ)
    (a : ℝ≥0∞) (ha : a ≠ 0) (ha' : a ≠ ⊤) :
    Tendsto (pressureRate (fun n ↦ a * (m : ℝ≥0∞) ^ (n + p) *
      (2 : ℝ≥0∞) ^ (-s * (n : ℝ)))) atTop
      (𝓝 (((Real.logb 2 m - s : ℝ) : EReal))) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hl2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hlogm : ENNReal.log (m : ℝ≥0∞) = ((Real.log m : ℝ) : EReal) := by
    rw [← ENNReal.ofReal_natCast, ENNReal.log_ofReal_of_pos hmpos]
  have hlog2 : ENNReal.log (2 : ℝ≥0∞) = ((Real.log 2 : ℝ) : EReal) := by
    simpa using ENNReal.log_ofReal_of_pos (by norm_num : (0 : ℝ) < 2)
  have hformula (n : ℕ) (hn : n ≠ 0) :
      pressureRate (fun n ↦ a * (m : ℝ≥0∞) ^ (n + p) *
          (2 : ℝ≥0∞) ^ (-s * (n : ℝ))) n =
        ((Real.logb 2 m - s +
          (Real.logb 2 a.toReal + (p : ℝ) * Real.logb 2 m) / (n : ℝ) : ℝ) : EReal) := by
    rw [pressureRate, ite_eq_right hn, pressureLog,
      ENNReal.log_mul_add, ENNReal.log_mul_add, ENNReal.log_pow, ENNReal.log_rpow,
      ENNReal.log_pos_real ha ha', hlogm, hlog2]
    simp only [← EReal.coe_natCast, ← EReal.coe_mul, ← EReal.coe_add]
    congr 1
    simp only [Real.logb, Nat.cast_add]
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    field_simp
    ring
  have hlim : Tendsto (fun n : ℕ ↦ Real.logb 2 m - s +
      (Real.logb 2 a.toReal + (p : ℝ) * Real.logb 2 m) / (n : ℝ))
      atTop (𝓝 (Real.logb 2 m - s)) := by
    simpa only [add_zero] using tendsto_const_nhds.add
      (Tendsto.const_div_atTop tendsto_natCast_atTop_atTop
        (Real.logb 2 a.toReal + (p : ℝ) * Real.logb 2 m))
  apply (continuous_coe_real_ereal.tendsto _ |>.comp hlim).congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (hformula n (by omega)).symm

/-- The cylinder mass bound gives a lower bound on the fixed-order partition sum of
any ambient subset in terms of its mass inside the subsystem. -/
private lemma outerMeasure_mul_le_partitionSum
    [MetricSpace (ℕ → ℕ)]
    (hd : ∀ x y : ℕ → ℕ, x ≠ y → dist x y = (1 / 2 : ℝ) ^ PiNat.firstDiff x y)
    (m : ℕ) (hm : 2 ≤ m) (s : ℝ) (p : ℕ)
    (μ : OuterMeasure (ℕ → ℕ))
    (hcyl : ∀ (x : ℕ → ℕ) (L : ℕ),
      μ (PiNat.cylinder x L ∩ finiteAlphabetSubsystem m) ≤ ((m : ℝ≥0∞) ^ L)⁻¹)
    (E : Set (ℕ → ℕ)) (n : ℕ) (hn : 1 ≤ n) :
    μ (E ∩ finiteAlphabetSubsystem m) * (m : ℝ≥0∞) ^ (n + p) *
        (2 : ℝ≥0∞) ^ (-s * (n : ℝ)) ≤
      partitionSum (fun y j ↦ y (j + 1)) (fun _ ↦ -s) .centered E n (dyadicRadius p) := by
  classical
  unfold partitionSum
  refine le_iInf fun F ↦ le_iInf fun hF ↦ ?_
  let B : (ℕ → ℕ) → Set (ℕ → ℕ) := fun y ↦
    bowenBall (fun (z : ℕ → ℕ) (j : ℕ) ↦ z (j + 1)) n y (dyadicRadius p) ∩
      finiteAlphabetSubsystem m
  have hcov : E ∩ finiteAlphabetSubsystem m ⊆ ⋃ y ∈ F, B y := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hF.2 hx.1)
    exact Set.mem_iUnion₂.mpr ⟨y, hy, hxy, hx.2⟩
  have hmass : μ (E ∩ finiteAlphabetSubsystem m) ≤ ∑' y : F, μ (B y.val) :=
    (measure_mono (μ := μ) hcov).trans (measure_biUnion_le μ hF.1 B)
  have hm0 : (m : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hpow0 : (m : ℝ≥0∞) ^ (n + p) ≠ 0 := pow_ne_zero _ hm0
  have hpowtop : (m : ℝ≥0∞) ^ (n + p) ≠ ⊤ := by finiteness
  calc
    _ ≤ (∑' y : F, μ (B y.val)) * (m : ℝ≥0∞) ^ (n + p) *
        (2 : ℝ≥0∞) ^ (-s * (n : ℝ)) :=
      mul_le_mul_left (mul_le_mul_left hmass _) _
    _ = ∑' y : F, μ (B y.val) * (m : ℝ≥0∞) ^ (n + p) *
        (2 : ℝ≥0∞) ^ (-s * (n : ℝ)) := by
      rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_right]
    _ ≤ partitionCoverCost (fun y j ↦ y (j + 1)) (fun _ ↦ -s) .centered F n
        (dyadicRadius p) := by
      unfold partitionCoverCost
      apply ENNReal.tsum_le_tsum
      intro y
      have hbound : μ (B y.val) ≤ ((m : ℝ≥0∞) ^ (n + p))⁻¹ := by
        dsimp only [B]
        rw [bowenBall_shift_eq_cylinder hd y.val n p hn]
        exact hcyl y.val (n + p)
      calc
        _ ≤ ((m : ℝ≥0∞) ^ (n + p))⁻¹ * (m : ℝ≥0∞) ^ (n + p) *
            (2 : ℝ≥0∞) ^ (-s * (n : ℝ)) :=
          mul_le_mul_left (mul_le_mul_left hbound _) _
        _ = _ := by
          rw [ENNReal.inv_mul_cancel hpow0 hpowtop, one_mul]
          simp [pressureBallWeight, birkhoffSum, mul_comm]

/-- The zero extensions of all words of length `n + p` give a partition cover with
cost at most `m^(n + p) * 2^(-s * n)`. -/
private lemma partitionSum_finiteAlphabetSubsystem_le
    [MetricSpace (ℕ → ℕ)]
    (hd : ∀ x y : ℕ → ℕ, x ≠ y → dist x y = (1 / 2 : ℝ) ^ PiNat.firstDiff x y)
    (m : ℕ) (s : ℝ) (n p : ℕ) (hn : 1 ≤ n) :
    partitionSum (fun y j ↦ y (j + 1)) (fun _ ↦ -s) .centered
        (finiteAlphabetSubsystem m) n (dyadicRadius p) ≤
      (m : ℝ≥0∞) ^ (n + p) * (2 : ℝ≥0∞) ^ (-s * (n : ℝ)) := by
  classical
  let c : (Fin (n + p) → Fin m) → (ℕ → ℕ) :=
    fun w j ↦ if hj : j < n + p then (w ⟨j, hj⟩).val else 0
  have hF : (Set.range c).Countable ∧ finiteAlphabetSubsystem m ⊆
      ⋃ y ∈ Set.range c, bowenBall (fun y j ↦ y (j + 1)) n y (dyadicRadius p) := by
    refine ⟨(Set.finite_range c).countable, ?_⟩
    intro x hx
    let w : Fin (n + p) → Fin m := fun j ↦ ⟨x j, hx j⟩
    apply Set.mem_iUnion₂.mpr
    refine ⟨c w, ⟨w, rfl⟩, ?_⟩
    rw [bowenBall_shift_eq_cylinder hd (c w) n p hn]
    intro j hj
    simp [c, w, hj]
  unfold partitionSum
  apply iInf_le_of_le (Set.range c)
  apply iInf_le_of_le hF
  unfold partitionCoverCost
  have hsurj : Function.Surjective (fun w : Fin (n + p) → Fin m ↦
      (⟨c w, Set.mem_range_self w⟩ : Set.range c)) := by
    rintro ⟨y, w, rfl⟩
    exact ⟨w, rfl⟩
  apply (ENNReal.tsum_le_tsum_comp_of_surjective hsurj _).trans
  simp [pressureBallWeight, birkhoffSum, tsum_fintype, mul_comm]

/-- A set of positive mass inside the subsystem has upper capacity at least
`logb 2 m - s`. -/
private lemma logb_sub_le_upperCapacity_of_pos
    [MetricSpace (ℕ → ℕ)]
    (hd : ∀ x y : ℕ → ℕ, x ≠ y → dist x y = (1 / 2 : ℝ) ^ PiNat.firstDiff x y)
    (m : ℕ) (hm : 2 ≤ m) (s : ℝ) (p : ℕ)
    (μ : OuterMeasure (ℕ → ℕ)) (hμ : μ (finiteAlphabetSubsystem m) = 1)
    (hcyl : ∀ (x : ℕ → ℕ) (L : ℕ),
      μ (PiNat.cylinder x L ∩ finiteAlphabetSubsystem m) ≤ ((m : ℝ≥0∞) ^ L)⁻¹)
    (E : Set (ℕ → ℕ)) (hE : 0 < μ (E ∩ finiteAlphabetSubsystem m)) :
    ((Real.logb 2 m - s : ℝ) : EReal) ≤
      upperCapacity (fun y j ↦ y (j + 1)) (fun _ ↦ -s) .centered E (dyadicRadius p) := by
  have hfinite : μ (E ∩ finiteAlphabetSubsystem m) ≠ ⊤ := by
    apply ne_of_lt
    calc
      _ ≤ μ (finiteAlphabetSubsystem m) := measure_mono Set.inter_subset_right
      _ = 1 := hμ
      _ < ⊤ := by norm_num
  have hlim := tendsto_pressureRate_cylinder_cost m hm s p
    (μ (E ∩ finiteAlphabetSubsystem m)) hE.ne' hfinite
  rw [upperCapacity, ← hlim.limsup_eq]
  apply Filter.limsup_le_limsup
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact pressureRate_le_of_le _ _ n
      (outerMeasure_mul_le_partitionSum hd m hm s p μ hcyl E n hn)
  · isBoundedDefault
  · isBoundedDefault

/-- Finite cylinder covers bound the upper capacity of the subsystem by `logb 2 m - s`. -/
private lemma upperCapacity_finiteAlphabetSubsystem_le
    [MetricSpace (ℕ → ℕ)]
    (hd : ∀ x y : ℕ → ℕ, x ≠ y → dist x y = (1 / 2 : ℝ) ^ PiNat.firstDiff x y)
    (m : ℕ) (hm : 2 ≤ m) (s : ℝ) (p : ℕ) :
    upperCapacity (fun y j ↦ y (j + 1)) (fun _ ↦ -s) .centered
      (finiteAlphabetSubsystem m) (dyadicRadius p) ≤ ((Real.logb 2 m - s : ℝ) : EReal) := by
  have hlim := tendsto_pressureRate_cylinder_cost m hm s p
    1 (by norm_num) (by norm_num)
  rw [upperCapacity, ← hlim.limsup_eq]
  apply Filter.limsup_le_limsup
  · filter_upwards [eventually_ge_atTop 1] with n hn
    apply pressureRate_le_of_le
    simpa only [one_mul] using
      partitionSum_finiteAlphabetSubsystem_le hd m s n p hn
  · isBoundedDefault
  · isBoundedDefault

/-- Every countable cover has a positive-mass piece, so countable modification
preserves the lower bound `logb 2 m - s`. -/
private lemma logb_sub_le_modifiedUpperPressure
    [MetricSpace (ℕ → ℕ)]
    (hd : ∀ x y : ℕ → ℕ, x ≠ y → dist x y = (1 / 2 : ℝ) ^ PiNat.firstDiff x y)
    (m : ℕ) (hm : 2 ≤ m) (s : ℝ) (p : ℕ) :
    ((Real.logb 2 m - s : ℝ) : EReal) ≤
      modifiedUpperPressure (fun y j ↦ y (j + 1)) (fun _ ↦ -s) .centered
        (finiteAlphabetSubsystem m) (dyadicRadius p) := by
  obtain ⟨μ, hμ, hcyl⟩ := exists_outerMeasure_finiteAlphabetSubsystem m hm
  unfold modifiedUpperPressure
  refine le_iInf fun E ↦ le_iInf fun hE ↦ ?_
  obtain ⟨i, hi⟩ := exists_pos_outerMeasure_inter_of_cover m μ hμ E hE
  exact le_iSup_of_le i
    (logb_sub_le_upperCapacity_of_pos hd m hm s p μ hμ hcyl (E i) hi)

end

/-- The upper pressure of the finite-alphabet subsystem for potential `-s` is `logb 2 m - s`,
including countable modification of upper capacity.
Blueprint node `geometry:finite-alphabet-pressure`. -/
theorem finiteAlphabetSubsystemPressure_upper [MetricSpace (ℕ → ℕ)]
    (hd : ∀ x y : ℕ → ℕ, x ≠ y → dist x y = (1 / 2 : ℝ) ^ PiNat.firstDiff x y)
    (m : ℕ) (hm : 2 ≤ m) (s : ℝ) :
    upperPressure (fun y j => y (j + 1)) (fun _ => -s) 0 (finiteAlphabetSubsystem m) =
      ((Real.logb 2 m - s : ℝ) : EReal) := by
  unfold upperPressure
  apply le_antisymm
  · refine iSup_le fun p ↦ iSup_le fun _ ↦ ?_
    apply le_trans ?_ (upperCapacity_finiteAlphabetSubsystem_le hd m hm s p)
    unfold modifiedUpperPressure
    refine iInf_le_of_le (fun _ ↦ finiteAlphabetSubsystem m) ?_
    refine iInf_le_of_le ?_ ?_
    · intro x hx
      exact Set.mem_iUnion.mpr ⟨0, hx⟩
    · exact iSup_le fun _ ↦ le_rfl
  · exact le_iSup_of_le 0 (le_iSup_of_le (le_refl 0)
      (logb_sub_le_modifiedUpperPressure hd m hm s 0))

/-- A cylinder of length `L` has extended diameter at most `2⁻ᴸ` inside the subsystem. -/
private lemma ediam_cylinder_inter_finiteAlphabetSubsystem_le [MetricSpace (ℕ → ℕ)]
    (hd : ∀ x y : ℕ → ℕ, x ≠ y → dist x y = (1 / 2 : ℝ) ^ PiNat.firstDiff x y)
    (m : ℕ)
    (x : ℕ → ℕ) (L : ℕ) :
    Metric.ediam (PiNat.cylinder x L ∩ finiteAlphabetSubsystem m) ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ L) := by
  refine Metric.ediam_le_of_forall_dist_le ?_
  intro y hy z hz
  by_cases h : y = z
  · rw [h, dist_self]
    positivity
  · have hy_cyl : y ∈ PiNat.cylinder x L := hy.1
    have hz_cyl : z ∈ PiNat.cylinder x L := hz.1
    rw [PiNat.mem_cylinder_iff] at hy_cyl hz_cyl
    have h_diff : L ≤ PiNat.firstDiff y z := by
      by_contra! h_lt
      have heq_y := hy_cyl _ h_lt
      have heq_z := hz_cyl _ h_lt
      have h_neq := PiNat.apply_firstDiff_ne h
      rw [heq_y, heq_z] at h_neq
      exact h_neq rfl
    calc
      dist y z = (1 / 2 : ℝ) ^ PiNat.firstDiff y z := hd y z h
      _ ≤ (1 / 2 : ℝ) ^ L :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) h_diff

/-- The subsystem admits a cover by `m^L` sets of diameter at most `2⁻ᴸ`, whose
`logb 2 m` powers sum to at most one. This supplies the Hausdorff dimension upper bound. -/
lemma exists_finite_cover_ediam_sum_le_one [MetricSpace (ℕ → ℕ)]
    (hd : ∀ x y : ℕ → ℕ, x ≠ y → dist x y = (1 / 2 : ℝ) ^ PiNat.firstDiff x y)
    (m : ℕ) (hm : 2 ≤ m)
    (L : ℕ) :
    ∃ C : Fin (m ^ L) → Set (ℕ → ℕ),
      (finiteAlphabetSubsystem m ⊆ ⋃ i, C i) ∧
      (∀ i, Metric.ediam (C i) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ L)) ∧
      (∑ i, Metric.ediam (C i) ^ Real.logb 2 m) ≤ 1 := by
  let f : Fin (m ^ L) → (Fin L → Fin m) := finFunctionFinEquiv.symm
  let C : Fin (m ^ L) → Set (ℕ → ℕ) := fun i ↦
    PiNat.cylinder (fun j ↦ if hj : j < L then (f i ⟨j, hj⟩ : ℕ) else 0) L ∩
      finiteAlphabetSubsystem m
  use C
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    simp only [Set.mem_iUnion]
    let y : Fin L → Fin m := fun j ↦ ⟨x j.val, hx j.val⟩
    let i := finFunctionFinEquiv y
    use i
    have H : f i = y := Equiv.symm_apply_apply _ _
    simp only [C]
    refine ⟨?_, hx⟩
    intro j hj
    simp only [hj, dite_true]
    have H2 : (f i ⟨j, hj⟩ : ℕ) = (y ⟨j, hj⟩ : ℕ) := by
      rw [H]
    rw [H2]
  · intro i
    apply ediam_cylinder_inter_finiteAlphabetSubsystem_le hd m
  · have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    have hlog : 0 ≤ Real.logb 2 m :=
      Real.logb_nonneg (by norm_num) (by exact_mod_cast (show 1 ≤ m by omega))
    have hbase : (1 / 2 : ℝ) ^ Real.logb 2 m = (m : ℝ)⁻¹ := by
      rw [one_div, Real.inv_rpow (by norm_num),
        Real.rpow_logb (by norm_num) (by norm_num) hmpos]
    have hpow : ENNReal.ofReal ((1 / 2 : ℝ) ^ L) ^ Real.logb 2 m =
        ((m : ℝ≥0∞) ^ L)⁻¹ := by
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hlog,
        ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm,
        Real.rpow_mul (by norm_num), Real.rpow_natCast, hbase,
        ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_inv_of_pos hmpos,
        ENNReal.ofReal_natCast, ENNReal.inv_pow]
    calc
      (∑ i, Metric.ediam (C i) ^ Real.logb 2 m) ≤
          ∑ _ : Fin (m ^ L), ENNReal.ofReal ((1 / 2 : ℝ) ^ L) ^ Real.logb 2 m := by
        apply Finset.sum_le_sum
        intro i _
        exact ENNReal.rpow_le_rpow
          (ediam_cylinder_inter_finiteAlphabetSubsystem_le hd m _ L) hlog
      _ = 1 := by
        rw [hpow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, Nat.cast_pow, ENNReal.mul_inv_cancel]
        · exact pow_ne_zero _ (by exact_mod_cast hmpos.ne')
        · exact ENNReal.pow_ne_top (ENNReal.natCast_ne_top m)

end Kolmogorov.PointToSet
