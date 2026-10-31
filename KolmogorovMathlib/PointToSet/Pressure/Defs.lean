/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.Dynamics
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
import Mathlib.Topology.EMetricSpace.Diam

/-!
# Pressure contents, discrete witnesses and nonnegative entropies

All pressures are `EReal`, and all masses and entropies are `ENNReal`. Lower covers are
indexed by subsets of `ℕ`, allowing empty families and repeated balls. Fixed-order
partition sums instead use countable sets of centers. The presentation is fixed before
the oracle. Pointwise pressure is the existing definition in `PointToSet.Dynamics`.

Definitions are total at arbitrary radii; comparison theorems impose positive radii and
finite oscillation. Scale-zero pressures explicitly use the chosen tail `p ≥ p₀`.
-/

namespace Kolmogorov.PointToSet

open Filter
open scoped Topology ENNReal Computability

variable {X : Type*} [MetricSpace X]

/-- Fixed presentation, continuous dynamics and potential with a classical small-scale
oscillation bound. The bound is chosen before any oracle. Blueprint node `pressure:data`. -/
structure PressureData (X : Type*) [MetricSpace X] where
  /-- The single complete dense presentation used for every oracle. -/
  presentation : Presentation X
  /-- The dynamics, with times counted from zero. -/
  T : X → X
  /-- Continuity of the dynamics. -/
  continuous_T : Continuous T
  /-- The real potential. -/
  φ : X → ℝ
  /-- Uniform continuity, without an effective modulus. -/
  uniformContinuous_φ : UniformContinuous φ
  /-- The first scale at which the oscillation bounds apply. -/
  p₀ : ℕ
  /-- Strictly positive analytical errors on the small-scale tail. -/
  ω : ℕ → ℝ
  /-- Positivity is required only on the chosen tail. -/
  ω_pos : ∀ p ≥ p₀, 0 < ω p
  /-- The errors vanish as precision increases. -/
  ω_tendsto : Tendsto ω atTop (𝓝 0)
  /-- The potential oscillates by at most the given error on each valid scale. -/
  oscillation : ∀ p ≥ p₀, ∀ x y, dist x y < dyadicRadius p → |φ x - φ y| ≤ ω p

/-- The extended base-two logarithm sends zero to `⊥` and infinity to `⊤`, using
Mathlib's extended natural logarithm. Blueprint node `pressure:data`. -/
noncomputable def pressureLog (q : ℝ≥0∞) : EReal :=
  ENNReal.log q * ((Real.log 2)⁻¹ : ℝ)

/-- The logarithmic rate at a positive order; the unused order-zero value is `⊥`.
Blueprint node `pressure:upper-content`. -/
noncomputable def pressureRate (q : ℕ → ℝ≥0∞) (n : ℕ) : EReal :=
  if n = 0 then ⊥ else pressureLog (q n) * ((n : ℝ)⁻¹ : ℝ)

/-- At a positive order, `pressureRate` is the extended logarithm scaled by
`(log 2)⁻¹ n⁻¹`. -/
theorem pressureRate_eq_log_mul (q : ℕ → ℝ≥0∞) {n : ℕ} (hn : n ≠ 0) :
    pressureRate q n =
      ENNReal.log (q n) * ((((Real.log 2)⁻¹ * (n : ℝ)⁻¹ : ℝ)) : EReal) := by
  simp only [pressureRate, ite_eq_right hn, pressureLog, mul_assoc, ← EReal.coe_mul]

/-- The normalized extended logarithm `pressureRate` is monotone: a pointwise inequality
`f n ≤ g n` gives `pressureRate f n ≤ pressureRate g n`. -/
lemma pressureRate_le_of_le (f g : ℕ → ℝ≥0∞) (n : ℕ) (h : f n ≤ g n) :
    pressureRate f n ≤ pressureRate g n := by
  unfold pressureRate
  split_ifs
  · exact le_rfl
  · unfold pressureLog
    apply mul_le_mul_of_nonneg_right
    · apply mul_le_mul_of_nonneg_right (ENNReal.log_le_log h)
      exact EReal.coe_nonneg.mpr (inv_nonneg.mpr (Real.log_nonneg (by norm_num)))
    · exact EReal.coe_nonneg.mpr (inv_nonneg.mpr (Nat.cast_nonneg n))

/-- The rate of the zero sequence is `⊥` at every order. -/
theorem pressureRate_zero (n : ℕ) : pressureRate (fun _ ↦ 0) n = ⊥ := by
  unfold pressureRate
  split_ifs with hn
  · rfl
  · unfold pressureLog
    rw [ENNReal.log_zero,
      EReal.bot_mul_of_pos (EReal.coe_pos.mpr (inv_pos.mpr (Real.log_pos (by norm_num)))),
      EReal.bot_mul_of_pos (EReal.coe_pos.mpr
        (inv_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))))]

/-- A rate bounded by a real number at a positive order comes from a finite value. -/
theorem lt_top_of_pressureRate_le {q : ℕ → ℝ≥0∞} {n : ℕ} (hn : 1 ≤ n) {b : ℝ}
    (h : pressureRate q n ≤ (b : EReal)) : q n < ⊤ := by
  by_contra hq
  have hqtop : q n = ⊤ := top_unique (not_lt.mp hq)
  rw [pressureRate, ite_eq_right (by omega : n ≠ 0), pressureLog, hqtop, ENNReal.log_top,
    EReal.top_mul_of_pos (EReal.coe_pos.mpr (inv_pos.mpr (Real.log_pos one_lt_two))),
    EReal.top_mul_of_pos (EReal.coe_pos.mpr (inv_pos.mpr (Nat.cast_pos.mpr hn)))] at h
  exact EReal.coe_ne_top b (top_le_iff.mp h)

/-- Multiplying a value by `2 ^ (n c)` raises its rate at order `n ≥ 1` by at most `c`. -/
theorem pressureRate_le_add_of_le_mul (f g : ℕ → ℝ≥0∞) (c : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (h : g n ≤ f n * (2 : ℝ≥0∞) ^ ((n : ℝ) * c)) :
    pressureRate g n ≤ pressureRate f n + (c : EReal) := by
  have hn0 : n ≠ 0 := by omega
  have hlpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let k : ℝ := (Real.log 2)⁻¹ * (n : ℝ)⁻¹
  have hk : 0 ≤ (k : EReal) := EReal.coe_nonneg.mpr
    (mul_nonneg (inv_nonneg.mpr hlpos.le) (inv_nonneg.mpr (Nat.cast_nonneg n)))
  rw [pressureRate_eq_log_mul _ hn0, pressureRate_eq_log_mul _ hn0]
  have hlogtwo : ENNReal.log 2 = ((Real.log 2 : ℝ) : EReal) := by
    simpa using ENNReal.log_ofReal_of_pos (by norm_num : (0 : ℝ) < 2)
  have hm := mul_le_mul_of_nonneg_right (ENNReal.log_le_log h) hk
  rw [ENNReal.log_mul_add, ENNReal.log_rpow, hlogtwo,
    EReal.right_distrib_of_nonneg_of_ne_top hk (EReal.coe_ne_top k)] at hm
  have hc : (((n : ℝ) * c : ℝ) : EReal) * (Real.log 2 : EReal) * (k : EReal) =
      (c : EReal) := by
    rw [← EReal.coe_mul, ← EReal.coe_mul]
    congr 1
    dsimp [k]
    field_simp
  rwa [hc] at hm

/-- A value at most `2 ^ c` has rate at most `c / n` at order `n ≥ 1`. -/
theorem pressureRate_le_of_le_rpow {q : ℕ → ℝ≥0∞} {c : ℝ} {n : ℕ} (hn : 1 ≤ n)
    (h : q n ≤ (2 : ℝ≥0∞) ^ c) : pressureRate q n ≤ ((c / n : ℝ) : EReal) := by
  have hn0 : n ≠ 0 := by omega
  have hlog2 : ENNReal.log 2 = ((Real.log 2 : ℝ) : EReal) := by
    simpa using ENNReal.log_ofReal_of_pos (by norm_num : (0 : ℝ) < 2)
  have hlog : ENNReal.log (q n) ≤ ((c * Real.log 2 : ℝ) : EReal) := by
    refine (ENNReal.log_le_log h).trans_eq ?_
    rw [ENNReal.log_rpow, hlog2, ← EReal.coe_mul]
  have hnonneg : (0 : ℝ) ≤ (Real.log 2)⁻¹ * (n : ℝ)⁻¹ :=
    mul_nonneg (inv_nonneg.2 (Real.log_nonneg (by norm_num))) (inv_nonneg.2 n.cast_nonneg)
  have hl : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn0
  calc
    pressureRate q n = ENNReal.log (q n) * (((Real.log 2)⁻¹ * (n : ℝ)⁻¹ : ℝ) : EReal) :=
      pressureRate_eq_log_mul q hn0
    _ ≤ ((c * Real.log 2 : ℝ) : EReal) * (((Real.log 2)⁻¹ * (n : ℝ)⁻¹ : ℝ) : EReal) :=
      mul_le_mul_of_nonneg_right hlog (EReal.coe_nonneg.2 hnonneg)
    _ = ((c / n : ℝ) : EReal) := by
      rw [← EReal.coe_mul]
      congr 1
      field_simp

/-- The two weight conventions in the blueprint. Blueprint node `pressure:lower-content`. -/
inductive PressureWeight where
  /-- Evaluate the potential sum at the center. -/
  | centered
  /-- Take the supremum of potential sums on the Bowen ball. -/
  | supremum

/-- The extended supremum of Birkhoff sums on a Bowen ball, finite on valid small scales.
Blueprint node `pressure:recenter`. -/
noncomputable def bowenPotentialSup (T : X → X) (φ : X → ℝ) (n : ℕ) (y : X)
    (r : ℝ) : EReal :=
  ⨆ z ∈ bowenBall T n y r, ((birkhoffSum T φ n z : ℝ) : EReal)

/-- Exponentiated centered or supremum potential. Taking the supremum after exponentiation
also defines the weight at unbounded scales. Blueprint node `pressure:lower-content`. -/
noncomputable def pressureBallWeight (T : X → X) (φ : X → ℝ) (w : PressureWeight)
    (n : ℕ) (y : X) (r : ℝ) : ℝ≥0∞ :=
  match w with
  | .centered => (2 : ℝ≥0∞) ^ birkhoffSum T φ n y
  | .supremum => ⨆ z ∈ bowenBall T n y r, (2 : ℝ≥0∞) ^ birkhoffSum T φ n z

/-- A countable indexed family, including the empty family; centers may repeat.
Blueprint node `pressure:lower-content`. -/
structure BowenCoverFamily (X : Type*) where
  /-- The active indices, permitting finite and empty families. -/
  index : Set ℕ
  /-- The center at each active index. -/
  center : index → X
  /-- The order at each active index. -/
  order : index → ℕ

/-- A family covers the set at the specified radius with orders above the positive cutoff.
Blueprint node `pressure:lower-content`. -/
def IsBowenCover (T : X → X) (Z : Set X) (r : ℝ) (N : ℕ)
    (C : BowenCoverFamily X) : Prop :=
  (∀ j, max 1 N ≤ C.order j) ∧ Z ⊆ ⋃ j, bowenBall T (C.order j) (C.center j) r

/-- Total pressure cost, counting the indices of a covering family with multiplicity.
Blueprint node `pressure:lower-content`. -/
noncomputable def bowenCoverCost (T : X → X) (φ : X → ℝ) (w : PressureWeight)
    (s r : ℝ) (C : BowenCoverFamily X) : ℝ≥0∞ :=
  ∑' j, (2 : ℝ≥0∞) ^ (-s * C.order j) *
    pressureBallWeight T φ w (C.order j) (C.center j) r

/-- The order-cutoff lower content is an infimum over countable indexed covers.
Blueprint node `pressure:lower-content`. -/
noncomputable def lowerContent (T : X → X) (φ : X → ℝ) (w : PressureWeight)
    (Z : Set X) (s r : ℝ) (N : ℕ) : ℝ≥0∞ :=
  ⨅ C : BowenCoverFamily X, ⨅ (_ : IsBowenCover T Z r N C), bowenCoverCost T φ w s r C

/-- The lower content after taking the supremum over positive order cutoffs.
Blueprint node `pressure:lower-content`. -/
noncomputable def lowerContentLimit (T : X → X) (φ : X → ℝ) (w : PressureWeight)
    (Z : Set X) (s r : ℝ) : ℝ≥0∞ :=
  ⨆ N : ℕ, ⨆ (_ : 1 ≤ N), lowerContent T φ w Z s r N

/-- The signed critical infimum of real exponents with vanishing lower content.
Blueprint node `pressure:lower-content`. -/
noncomputable def lowerPressureAt (T : X → X) (φ : X → ℝ) (w : PressureWeight)
    (Z : Set X) (r : ℝ) : EReal :=
  ⨅ s : ℝ, ⨅ (_ : lowerContentLimit T φ w Z s r = 0), (s : EReal)

/-- Scale-zero lower pressure uses the monotone centered critical values on a small-scale
tail. Blueprint node `pressure:lower-scale`. -/
noncomputable def lowerPressure (T : X → X) (φ : X → ℝ) (p₀ : ℕ) (Z : Set X) : EReal :=
  ⨆ p : ℕ, ⨆ (_ : p₀ ≤ p), lowerPressureAt T φ .centered Z (dyadicRadius p)

/-- The weight of a set of centers at one order, without enumeration multiplicity.
Blueprint node `pressure:upper-content`. -/
noncomputable def partitionCoverCost (T : X → X) (φ : X → ℝ) (w : PressureWeight)
    (F : Set X) (n : ℕ) (r : ℝ) : ℝ≥0∞ :=
  ∑' y : F, pressureBallWeight T φ w n y r

/-- The fixed-order partition infimum over countable sets of covering centers.
Blueprint node `pressure:upper-content`. -/
noncomputable def partitionSum (T : X → X) (φ : X → ℝ) (w : PressureWeight)
    (Z : Set X) (n : ℕ) (r : ℝ) : ℝ≥0∞ :=
  ⨅ F : Set X, ⨅ (_ : F.Countable ∧ Z ⊆ ⋃ y ∈ F, bowenBall T n y r),
    partitionCoverCost T φ w F n r

/-- Upper capacity is the upper time limit of extended logarithmic partition rates.
Blueprint node `pressure:upper-content`. -/
noncomputable def upperCapacity (T : X → X) (φ : X → ℝ) (w : PressureWeight)
    (Z : Set X) (r : ℝ) : EReal :=
  limsup (pressureRate (fun n => partitionSum T φ w Z n r)) atTop

/-- Partition sums are monotone in the covered set. -/
theorem partitionSum_mono_set (T : X → X) (φ : X → ℝ) (w : PressureWeight) {Y Z : Set X}
    (h : Y ⊆ Z) (n : ℕ) (r : ℝ) : partitionSum T φ w Y n r ≤ partitionSum T φ w Z n r :=
  iInf_mono fun _ ↦ iInf_mono' fun hF ↦ ⟨⟨hF.1, h.trans hF.2⟩, le_rfl⟩

/-- Upper capacities are monotone in the covered set. -/
theorem upperCapacity_mono_set (T : X → X) (φ : X → ℝ) (w : PressureWeight) {Y Z : Set X}
    (h : Y ⊆ Z) (r : ℝ) : upperCapacity T φ w Y r ≤ upperCapacity T φ w Z r :=
  limsup_le_limsup (Eventually.of_forall fun n ↦
    pressureRate_le_of_le _ _ n (partitionSum_mono_set T φ w h n r))
    (isCoboundedUnder_le_of_le atTop fun _ ↦ bot_le) (isBoundedUnder_of ⟨⊤, fun _ ↦ le_top⟩)

/-- At a positive radius, centered partition sums are bounded by supremum-weight ones. -/
theorem partitionSum_centered_le_supremum (T : X → X) (φ : X → ℝ) (Z : Set X) (n : ℕ)
    {r : ℝ} (hr : 0 < r) :
    partitionSum T φ .centered Z n r ≤ partitionSum T φ .supremum Z n r := by
  unfold partitionSum
  refine iInf_mono fun F ↦ iInf_mono fun _ ↦ ?_
  unfold partitionCoverCost
  refine ENNReal.tsum_le_tsum fun y ↦ ?_
  dsimp [pressureBallWeight]
  exact le_iSup₂_of_le (f := fun z (_ : z ∈ bowenBall T n y r) ↦
    (2 : ℝ≥0∞) ^ birkhoffSum T φ n z) (y : X) (self_mem_bowenBall T n y r hr) le_rfl

/-- At a positive radius, centered lower contents are bounded by supremum-weight ones. -/
theorem lowerContentLimit_centered_le_supremum (T : X → X) (φ : X → ℝ) (Z : Set X)
    (s r : ℝ) (hr : 0 < r) :
    lowerContentLimit T φ .centered Z s r ≤ lowerContentLimit T φ .supremum Z s r := by
  unfold lowerContentLimit lowerContent
  refine iSup_mono fun N ↦ iSup_mono fun _ ↦ iInf_mono fun C ↦ iInf_mono fun _ ↦ ?_
  unfold bowenCoverCost
  refine ENNReal.tsum_le_tsum fun j ↦ mul_le_mul' le_rfl ?_
  exact le_iSup₂_of_le (C.center j) (self_mem_bowenBall T (C.order j) (C.center j) r hr)
    le_rfl

/-- The countable modification allows arbitrary covering subsets, without measurability.
Blueprint node `pressure:upper-content`. -/
noncomputable def modifiedUpperPressure (T : X → X) (φ : X → ℝ) (w : PressureWeight)
    (Z : Set X) (r : ℝ) : EReal :=
  ⨅ Y : ℕ → Set X, ⨅ (_ : Z ⊆ ⋃ k, Y k), ⨆ k, upperCapacity T φ w (Y k) r

/-- Scale-zero upper pressure is the small-scale supremum of centered modifications.
Blueprint node `pressure:upper-content`. -/
noncomputable def upperPressure (T : X → X) (φ : X → ℝ) (p₀ : ℕ) (Z : Set X) : EReal :=
  ⨆ p : ℕ, ⨆ (_ : p₀ ≤ p), modifiedUpperPressure T φ .centered Z (dyadicRadius p)

/-- Total mass of distinct triples in a discrete pressure cover.
Blueprint node `pressure:null-cover`. -/
noncomputable def nullPressureMass (P : Presentation X) (T : X → X) (φ : X → ℝ)
    (s : ℝ) (E : Set (ℕ × ℕ × ℕ)) : ℝ≥0∞ :=
  ∑' t : E, (2 : ℝ≥0∞) ^ (-s * t.val.2.1 + birkhoffSum T φ t.val.2.1 (P.ι t.val.1))

/-- A finite-mass set of valid triples covers at every scale and arbitrarily large orders.
Blueprint node `pressure:null-cover`. -/
def IsNullPressureCover (P : Presentation X) (T : X → X) (φ : X → ℝ) (p₀ : ℕ)
    (Z : Set X) (s : ℝ) (E : Set (ℕ × ℕ × ℕ)) : Prop :=
  (∀ t ∈ E, 1 ≤ t.2.1 ∧ p₀ ≤ t.2.2) ∧ nullPressureMass P T φ s E < ⊤ ∧
    ∀ p ≥ p₀, ∀ N ≥ 1, ∀ x ∈ Z, ∃ i n, N ≤ n ∧ (i, n, p) ∈ E ∧
      x ∈ bowenBall T n (P.ι i) (dyadicRadius p)

/-- Effective lower pressure restricts null-cover witnesses to relatively enumerable sets.
Blueprint node `pressure:effective-lower`. -/
noncomputable def effectiveLowerPressure (P : Presentation X) (T : X → X) (φ : X → ℝ)
    (p₀ : ℕ) (A : Set ℕ) (Z : Set X) : EReal :=
  ⨅ s : ℝ, ⨅ E : Set (ℕ × ℕ × ℕ),
    ⨅ (_ : IsNullPressureCover P T φ p₀ Z s E ∧ IsREIn A E), (s : EReal)

/-- The weighted sum of distinct ideal indices in one uniform-net slice.
Blueprint node `pressure:uniform-net`. -/
noncomputable def uniformPressureSum (P : Presentation X) (T : X → X) (φ : X → ℝ)
    (E : Set (ℕ × ℕ × ℕ × ℕ)) (n p k : ℕ) : ℝ≥0∞ :=
  ∑' i : {i : ℕ | (i, n, p, k) ∈ E}, (2 : ℝ≥0∞) ^ birkhoffSum T φ n (P.ι i)

/-- A uniform net bounds every slice rate; for each point and scale one slice parameter
works at every positive order. Blueprint node `pressure:uniform-net`. -/
def IsUniformPressureNet (P : Presentation X) (T : X → X) (φ : X → ℝ) (p₀ : ℕ)
    (Z : Set X) (s : ℝ) (E : Set (ℕ × ℕ × ℕ × ℕ)) : Prop :=
  (∀ t ∈ E, 1 ≤ t.2.1 ∧ p₀ ≤ t.2.2.1) ∧
    (∀ p ≥ p₀, ∀ k,
      limsup (pressureRate (fun n => uniformPressureSum P T φ E n p k)) atTop ≤ (s : EReal)) ∧
    ∀ p ≥ p₀, ∀ x ∈ Z, ∃ k, ∀ n ≥ 1, ∃ i, (i, n, p, k) ∈ E ∧
      x ∈ bowenBall T n (P.ι i) (dyadicRadius p)

/-- Effective upper pressure is the infimum of exponents of relatively enumerable nets.
Blueprint node `pressure:effective-upper`. -/
noncomputable def effectiveUpperPressure (P : Presentation X) (T : X → X) (φ : X → ℝ)
    (p₀ : ℕ) (A : Set ℕ) (Z : Set X) : EReal :=
  ⨅ s : ℝ, ⨅ E : Set (ℕ × ℕ × ℕ × ℕ),
    ⨅ (_ : IsUniformPressureNet P T φ p₀ Z s E ∧ IsREIn A E), (s : EReal)

/-- The lower threshold uses the existing prefix complexity and nested pair encoding.
The domain explicitly excludes order zero and coarse scales.
Blueprint node `pressure:lower-threshold`. -/
def lowerPressureThreshold (P : Presentation X) (T : X → X) (φ : X → ℝ) (p₀ : ℕ)
    (A : Set ℕ) (s : ℚ) : Set (ℕ × ℕ × ℕ) :=
  {t | 1 ≤ t.2.1 ∧ p₀ ≤ t.2.2 ∧
    (oracleComplexity A (pairCode (natBits t.1)
      (pairCode (natBits t.2.1) (natBits t.2.2))) : ℝ) <
        (s : ℝ) * t.2.1 - birkhoffSum T φ t.2.1 (P.ι t.1)}

/-- The upper threshold adds one natural slice allowance to the real cost threshold.
Blueprint node `pressure:upper-threshold`. -/
def upperPressureThreshold (P : Presentation X) (T : X → X) (φ : X → ℝ) (p₀ : ℕ)
    (A : Set ℕ) (s : ℚ) : Set (ℕ × ℕ × ℕ × ℕ) :=
  {t | 1 ≤ t.2.1 ∧ p₀ ≤ t.2.2.1 ∧ (oracleNatComplexity A t.1 : ℝ) <
    (s : ℝ) * t.2.1 - birkhoffSum T φ t.2.1 (P.ι t.1) + t.2.2.2}

/-- Classical lower entropy uses only nonnegative real critical parameters at zero
potential. Blueprint node `pressure:entropy-definitions`. -/
noncomputable def lowerEntropy (T : X → X) (Z : Set X) : ℝ≥0∞ :=
  ⨆ p : ℕ, ⨅ s : ℝ, ⨅ (_ : 0 ≤ s),
    ⨅ (_ : lowerContentLimit T (fun _ => 0) .centered Z s (dyadicRadius p) = 0),
      ENNReal.ofReal s

/-- Classical upper entropy is the nonnegative critical infimum of zero-potential nets.
Blueprint node `pressure:entropy-definitions`. -/
noncomputable def upperEntropy (P : Presentation X) (T : X → X) (Z : Set X) : ℝ≥0∞ :=
  ⨅ s : ℝ, ⨅ (_ : 0 ≤ s), ⨅ E : Set (ℕ × ℕ × ℕ × ℕ),
    ⨅ (_ : IsUniformPressureNet P T (fun _ => 0) 0 Z s E), ENNReal.ofReal s

/-- Effective lower entropy is defined for every oracle, without geometric algorithms.
Blueprint node `pressure:entropy-definitions`. -/
noncomputable def effectiveLowerEntropy (P : Presentation X) (T : X → X) (A : Set ℕ)
    (Z : Set X) : ℝ≥0∞ :=
  ⨅ s : ℝ, ⨅ (_ : 0 ≤ s), ⨅ E : Set (ℕ × ℕ × ℕ),
    ⨅ (_ : IsNullPressureCover P T (fun _ => 0) 0 Z s E ∧ IsREIn A E), ENNReal.ofReal s

/-- Effective upper entropy likewise requires only enumeration of the net's encoded set.
Blueprint node `pressure:entropy-definitions`. -/
noncomputable def effectiveUpperEntropy (P : Presentation X) (T : X → X) (A : Set ℕ)
    (Z : Set X) : ℝ≥0∞ :=
  ⨅ s : ℝ, ⨅ (_ : 0 ≤ s), ⨅ E : Set (ℕ × ℕ × ℕ × ℕ),
    ⨅ (_ : IsUniformPressureNet P T (fun _ => 0) 0 Z s E ∧ IsREIn A E), ENNReal.ofReal s

/-- Orbit complexity is an `ENat` infimum, retaining infinity on an empty candidate set.
Blueprint node `pressure:entropy-definitions`. -/
noncomputable def orbitComplexity (P : Presentation X) (T : X → X) (A : Set ℕ)
    (x : X) (n : ℕ) (r : ℝ) : ENat :=
  ⨅ i : ℕ, ⨅ (_ : P.ι i ∈ bowenBall T n x r), (oracleNatComplexity A i : ENat)

/-- The natural shadow of orbit complexity, used at positive radii where it is attained.
Blueprint node `pressure:entropy-definitions`. -/
noncomputable def orbitComplexityNat (P : Presentation X) (T : X → X) (A : Set ℕ)
    (x : X) (n : ℕ) (r : ℝ) : ℕ :=
  (orbitComplexity P T A x n r).toNat

/-- Nonnegative lower and upper orbit rates reuse the frozen pointwise BS formula with
constant denominator potential one, whose positive-order Birkhoff sum is exactly `n`.
Blueprint node `pressure:entropy-definitions`. -/
noncomputable def orbitComplexities (P : Presentation X) (T : X → X) (A : Set ℕ)
    (x : X) : ℝ≥0∞ × ℝ≥0∞ :=
  pointwiseBSDimension P T (fun _ => 1) A x

/-- The two classical entropies, two effective entropies and pointwise orbit rates, grouped
in that order; all six quantities have nonnegative extended values.
Blueprint node `pressure:entropy-definitions`. -/
noncomputable def entropiesAndOrbitComplexities (P : Presentation X) (T : X → X)
    (A : Set ℕ) (Z : Set X) :
    (ℝ≥0∞ × ℝ≥0∞) × (ℝ≥0∞ × ℝ≥0∞) × (X → ℝ≥0∞ × ℝ≥0∞) :=
  ((lowerEntropy T Z, upperEntropy P T Z),
    (effectiveLowerEntropy P T A Z, effectiveUpperEntropy P T A Z), orbitComplexities P T A)

/-- Residence time is the supremum of finite orders with all preceding image diameters
at most the prescribed radius. Extended diameter also handles unbounded open sets.
Blueprint node `pressure:entropy-content`. -/
noncomputable def residenceTime (T : X → X) (r : ℝ) (U : Set X) : ENat :=
  ⨆ n : ℕ, ⨆ (_ : ∀ j < n, Metric.ediam (T^[j] '' U) ≤ ENNReal.ofReal r), (n : ENat)

/-- The size of an open set is two to the negative residence time, with size zero for
infinite residence. Blueprint node `pressure:entropy-content`. -/
noncomputable def residenceSize (T : X → X) (r : ℝ) (U : Set X) : ℝ≥0∞ :=
  if residenceTime T r U = ⊤ then 0 else (2 : ℝ≥0∞) ^ (-(residenceTime T r U).toNat : ℝ)

open Classical in
/-- Residence content uses countable open covers with a size cutoff. At exponent zero
each active set costs one, explicitly specifying the endpoint convention.
Blueprint node `pressure:entropy-content`. -/
noncomputable def residenceContent (T : X → X) (Z : Set X) (s r : ℝ)
    (δ : ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ J : Set ℕ, ⨅ U : J → Set X,
    ⨅ (_ : (∀ j, IsOpen (U j) ∧ residenceSize T r (U j) ≤ δ) ∧ Z ⊆ ⋃ j, U j),
      ∑' j, if s = 0 then 1 else residenceSize T r (U j) ^ s

/-- Residence-time entropy is the scale-zero supremum of nonnegative critical exponents
after the size cutoff tends to zero. Blueprint node `pressure:entropy-content`. -/
noncomputable def residenceEntropy (T : X → X) (Z : Set X) : ℝ≥0∞ :=
  ⨆ p : ℕ, ⨅ s : ℝ, ⨅ (_ : 0 ≤ s),
    ⨅ (_ : (⨆ δ : ℝ≥0∞, ⨆ (_ : 0 < δ),
      residenceContent T Z s (dyadicRadius p) δ) = 0), ENNReal.ofReal s

end Kolmogorov.PointToSet
