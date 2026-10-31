/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.BSDimension.Upper.OracleAttainment

/-!
# The point-to-set principle for Barreira-Schmeling dimensions

This module proves Main B (blueprint node `bs:point-to-set`): for a set `Z` on which the lower
Birkhoff average of `u` is positive, the lower (resp. modified upper) Barreira-Schmeling
dimension of `Z` equals the infimum over all oracles `A` of the supremum over `x ∈ Z` of the
`A`-relative pointwise dimension (`bsPointToSet`, `bsPointToSet_upper`).  The inequality `≤`
is the classical-versus-effective comparison, the inequality `≥` uses the oracle attaining the
dimension from `OracleAttainment` together with the effective characterization of the dimension
as a supremum of pointwise dimensions.

It also records that a single upper cone of oracles realises both minima simultaneously
(`bsPointToSet_cone`; oracle strengthening only decreases the pointwise dimensions by
`bsPointToSet_mono_oracle` from `OracleAttainment`), and that the classical and effective
dimensions of the empty set vanish (`bsPointToSet_empty`, `effectiveBSDimensions_empty`).
These statements are the final input of `KolmogorovMathlib.PointToSet.BSDimension.Upper`,
which re-exports them.
-/

namespace Kolmogorov.PointToSet
open Filter
open scoped Topology ENNReal Computability
variable {X : Type*} [MetricSpace X]

/-- Main B: lower BS dimension is the infimum over every oracle of pointwise suprema.
Blueprint node `bs:point-to-set`. -/
theorem bsPointToSet (P : Presentation X) (T : X → X) (hT : Continuous T)
    (u : X → ℝ) (hu : UniformContinuous u) (Z : Set X)
    (hZ : ∀ x ∈ Z, 0 < lowerBirkhoffAverage T u x) :
    lowerBSDimension T u Z = ⨅ A : Set ℕ, ⨆ x ∈ Z, (pointwiseBSDimension P T u A x).1 := by
  apply le_antisymm
  · apply le_iInf
    intro A
    exact bsPointToSet_all_oracles P T hT u hu Z hZ A LimitSide.lower
  · have h_attainment := bsOracleAttainment P T hT u hu Z hZ
    rcases h_attainment with ⟨A₀, hA₀, hB_attainment⟩
    apply iInf_le_of_le A₀
    have hA₀_refl : TuringReducible (charOracle A₀) (charOracle A₀) := TuringReducible.refl _
    have hB := hB_attainment A₀ hA₀_refl
    have hB_adm := hB.1
    have hB_eq := hB.2
    have h_effective := effectiveLowerBSEqSup P T u hu A₀ hB_adm Z hZ
    rw [← hB_eq]
    rw [h_effective]

/-- Main B: modified upper BS dimension has the analogous all-oracle infimum.
Blueprint node `bs:point-to-set`. -/
theorem bsPointToSet_upper (P : Presentation X) (T : X → X) (hT : Continuous T)
    (u : X → ℝ) (hu : UniformContinuous u) (Z : Set X)
    (hZ : ∀ x ∈ Z, 0 < lowerBirkhoffAverage T u x) :
    upperBSDimension T u Z = ⨅ A : Set ℕ, ⨆ x ∈ Z, (pointwiseBSDimension P T u A x).2 := by
  apply le_antisymm
  · apply le_iInf
    intro A
    exact bsPointToSet_all_oracles P T hT u hu Z hZ A LimitSide.upper
  · have ⟨A₀, hA₀, h_eq⟩ := bsOracleAttainment_upper P T hT u hu Z hZ
    have h_cone := h_eq A₀ (TuringReducible.refl (charOracle A₀))
    rw [← h_cone.2, effectiveUpperBSEqSup P T hT u hu A₀ h_cone.1 Z hZ]
    apply iInf_le _ A₀

/-- One admissible upper cone realizes both point-to-set minima simultaneously.
Blueprint node `bs:point-to-set`. -/
theorem bsPointToSet_cone (P : Presentation X) (T : X → X) (hT : Continuous T)
    (u : X → ℝ) (hu : UniformContinuous u) (Z : Set X)
    (hZ : ∀ x ∈ Z, 0 < lowerBirkhoffAverage T u x) :
    ∃ A₀ : Set ℕ, ∀ A : Set ℕ, charOracle A₀ ≤ᵀ charOracle A →
      IsAdmissible P T (fun _ : Fin 1 => u) A ∧ ∀ σ : LimitSide,
        σ.choose (lowerBSDimension T u Z, upperBSDimension T u Z) =
          ⨆ x ∈ Z, σ.choose (pointwiseBSDimension P T u A x) := by
  have ⟨A_L, _, hA_L⟩ := bsOracleAttainment P T hT u hu Z hZ
  have ⟨A_U, _, hA_U⟩ := bsOracleAttainment_upper P T hT u hu Z hZ
  use oracleJoin A_L A_U
  intro A hA
  have hA_L_A : charOracle A_L ≤ᵀ charOracle A :=
    TuringReducible.trans (oracle_joins A_L A_U) hA
  have hA_U_A : charOracle A_U ≤ᵀ charOracle A :=
    TuringReducible.trans (oracle_joins_right A_L A_U) hA
  have hA_L_res := hA_L A hA_L_A
  have hA_U_res := hA_U A hA_U_A
  refine ⟨hA_L_res.1, ?_⟩
  intro σ
  cases σ
  · dsimp [LimitSide.choose]
    have eq1 : effectiveLowerBSDimension P T u A Z = lowerBSDimension T u Z := hA_L_res.2
    rw [← eq1]
    exact effectiveLowerBSEqSup P T u hu A hA_L_res.1 Z hZ
  · dsimp [LimitSide.choose]
    have eq1 : effectiveUpperBSDimension P T u A Z = upperBSDimension T u Z := hA_U_res.2
    rw [← eq1]
    exact effectiveUpperBSEqSup P T hT u hu A hA_U_res.1 Z hZ

/-- Both classical BS dimensions of the empty set are zero.
Blueprint node `bs:point-to-set`. -/
theorem bsPointToSet_empty (T : X → X) (u : X → ℝ) (σ : LimitSide) :
    σ.choose (lowerBSDimension T u ∅, upperBSDimension T u ∅) = 0 := by
  cases σ
  · change lowerBSDimension T u ∅ = 0
    have hmass (r : ℝ) (N : ℕ) : lowerBSMass T u ∅ 0 r N = 0 := by
      let C : BowenCoverFamily X :=
        { index := ∅, center := fun j => False.elim j.property, order := fun _ => N }
      have hC : IsBowenCover T ∅ r N C :=
        ⟨fun j => False.elim j.property, Set.empty_subset _⟩
      apply le_antisymm _ bot_le
      unfold lowerBSMass
      refine iInf_le_of_le C (iInf_le_of_le hC ?_)
      simp [bsCoverCost, C]
    have hlimit (r : ℝ) : lowerBSMassLimit T u ∅ 0 r = 0 := by
      simp [lowerBSMassLimit, hmass]
    apply le_antisymm _ bot_le
    unfold lowerBSDimension
    refine iSup_le fun p => ?_
    unfold lowerBSDimensionAt
    exact iInf_le_of_le 0 (iInf_le_of_le le_rfl
      (iInf_le_of_le (hlimit _) (by simp)))
  · change upperBSDimension T u ∅ = 0
    have hsum (r : ℝ) (n : ℕ) : bsPartitionSum T u ∅ 0 r n = 0 := by
      apply le_antisymm _ bot_le
      unfold bsPartitionSum
      refine iInf_le_of_le ∅ (iInf_le_of_le
        ⟨Set.countable_empty, Set.empty_subset _⟩ ?_)
      simp [bsPartitionCoverCost]
    apply le_antisymm _ bot_le
    unfold upperBSDimension
    refine iSup_le fun p => ?_
    unfold modifiedUpperBSDimension
    refine iInf_le_of_le (fun _ => ∅) (iInf_le_of_le
      ⟨fun _ => Set.Subset.rfl, Set.empty_subset _⟩ ?_)
    refine iSup_le fun k => ?_
    unfold upperBSCapacityAt
    have hfinite : limsup (bsPartitionSum T u ∅ 0 (dyadicRadius p)) atTop < ⊤ := by
      have hz : bsPartitionSum T u ∅ 0 (dyadicRadius p) = fun _ => 0 :=
        funext (hsum (dyadicRadius p))
      rw [hz]
      simp
    exact iInf_le_of_le 0 (iInf_le_of_le le_rfl (iInf_le_of_le hfinite (by simp)))

private lemma nullPressureMass_empty (P : Presentation X) (T : X → X) (φ : X → ℝ) (s : ℝ) :
    nullPressureMass P T φ s ∅ = 0 := by
  dsimp [nullPressureMass]
  exact tsum_empty

private lemma nullBSMass_empty (P : Presentation X) (T : X → X) (u : X → ℝ) (s : ℝ) :
    nullBSMass P T u s ∅ = 0 := by
  dsimp [nullBSMass]
  exact nullPressureMass_empty P T (fun y => -s * u y) 0

private lemma isNullBSCover_empty (P : Presentation X) (T : X → X) (u : X → ℝ) (s : ℝ) :
    IsNullBSCover P T u ∅ s ∅ := by
  dsimp [IsNullBSCover]
  constructor
  · rw [nullBSMass_empty]
    exact ENNReal.zero_lt_top
  · rintro p k x hx
    exfalso
    exact hx

private lemma uniformPressureSum_empty (P : Presentation X) (T : X → X) (φ : X → ℝ)
    (n p k : ℕ) : uniformPressureSum P T φ ∅ n p k = 0 := by
  unfold uniformPressureSum
  have hidx : {i : ℕ | (i, n, p, k) ∈ (∅ : Set (ℕ × ℕ × ℕ × ℕ))} = ∅ := by
    ext i
    simp
  rw [hidx, tsum_empty]

private lemma uniformBSSum_empty (P : Presentation X) (T : X → X) (u : X → ℝ) (s : ℝ)
    (n p k : ℕ) : uniformBSSum P T u s ∅ n p k = 0 := by
  dsimp [uniformBSSum]
  exact uniformPressureSum_empty P T (fun y => -s * u y) n p k

private lemma isUniformBSNet_empty (P : Presentation X) (T : X → X) (u : X → ℝ) (s : ℝ) :
    IsUniformBSNet P T u ∅ s ∅ := by
  dsimp [IsUniformBSNet]
  constructor
  · rintro p k
    have h_zero : (fun (n : ℕ) => uniformBSSum P T u s ∅ n p k) = (fun _ => 0) := by
      ext n
      exact uniformBSSum_empty P T u s n p k
    rw [h_zero]
    simp
  · rintro p x hx
    exfalso
    exact hx

private lemma effectiveLowerBSDimension_empty (P : Presentation X) (T : X → X) (u : X → ℝ)
    (A : Set ℕ) : effectiveLowerBSDimension P T u A ∅ = 0 := by
  dsimp [effectiveLowerBSDimension]
  apply le_antisymm
  · refine iInf_le_of_le 0 ?_
    refine iInf_le_of_le le_rfl ?_
    refine iInf_le_of_le ∅ ?_
    have h_RE : IsREIn A (∅ : Set (ℕ × ℕ × ℕ)) := isREIn_empty A
    have h_cov : IsNullBSCover P T u ∅ 0 ∅ := isNullBSCover_empty P T u 0
    refine iInf_le_of_le ⟨h_cov, h_RE⟩ ?_
    simp
  · exact bot_le

private lemma effectiveUpperBSDimension_empty (P : Presentation X) (T : X → X) (u : X → ℝ)
    (A : Set ℕ) : effectiveUpperBSDimension P T u A ∅ = 0 := by
  dsimp [effectiveUpperBSDimension]
  apply le_antisymm
  · refine iInf_le_of_le 0 ?_
    refine iInf_le_of_le le_rfl ?_
    refine iInf_le_of_le ∅ ?_
    have h_RE : IsREIn A (∅ : Set (ℕ × ℕ × ℕ × ℕ)) := isREIn_empty A
    have h_net : IsUniformBSNet P T u ∅ 0 ∅ := isUniformBSNet_empty P T u 0
    refine iInf_le_of_le ⟨h_net, h_RE⟩ ?_
    simp
  · exact bot_le

/-- Both effective dimensions of the empty set are zero for every oracle.
Blueprint node `bs:effective`. -/
theorem effectiveBSDimensions_empty (P : Presentation X) (T : X → X) (u : X → ℝ)
    (A : Set ℕ) (σ : LimitSide) :
    σ.choose (effectiveBSDimensions P T u A ∅) = 0 := by
  dsimp [effectiveBSDimensions]
  cases σ
  · dsimp [LimitSide.choose]
    exact effectiveLowerBSDimension_empty P T u A
  · dsimp [LimitSide.choose]
    exact effectiveUpperBSDimension_empty P T u A

end Kolmogorov.PointToSet
