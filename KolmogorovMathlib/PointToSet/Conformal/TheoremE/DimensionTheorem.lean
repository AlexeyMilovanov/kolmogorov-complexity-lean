/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.BowenEquation
import KolmogorovMathlib.PointToSet.Conformal.Classical
import KolmogorovMathlib.PointToSet.Conformal.Distortion
import KolmogorovMathlib.PointToSet.PackingEquivalences.BSDimension
import KolmogorovMathlib.PointToSet.Conformal.TheoremE.BallComparison
import KolmogorovMathlib.PointToSet.Conformal.TheoremE.FactorialUltrametric

/-!
# Conformal dimension and Bowen equations

Theorem E identifies Hausdorff and specified-radius packing dimension with the lower and
upper Barreira–Schmeling dimensions on the conformal locus (`conf:theorem-e`). The proof
compares the classical and dynamical point-to-set formulas through their pointwise identities.
The corrected pressure cut and root characterizations then transfer to classical dimension
(`conf:bowen`), with the uniform average and finiteness assumptions required for root existence.
These results are re-exported by `Conformal.TheoremE`.
-/

namespace Kolmogorov.PointToSet

open Filter
open scoped Topology ENNReal Computability

variable {X : Type*} [MetricSpace X]

/-- Theorem E identifies Hausdorff dimension with the existing lower covering BS dimension.
Completeness and the fixed dense sequence are supplied by the presentation.
Blueprint node `conf:theorem-e`. -/
theorem dimensionTheorem (P : Presentation X) (C : UniformConformalData X)
    (Z : Set X) (hZ : Z ⊆ conformalLocus C) :
    _root_.dimH Z = lowerBSDimension C.T C.potential Z := by
  rw [classicalPointToSet P Z]
  rw [bsPointToSet P C.T C.uniformContinuous_T.continuous C.potential
    (distortionModuli C) Z (fun x hx ↦ (hZ hx).1.1.1)]
  apply iInf_congr
  intro A
  apply iSup_congr
  intro x
  apply iSup_congr
  intro hx
  exact pointwiseDimensionEqBS P C A x (hZ hx)

/-- Theorem E identifies specified-radius packing dimension with modified upper BS dimension.
Blueprint node `conf:theorem-e`. -/
theorem dimensionTheorem_upper (P : Presentation X) (C : UniformConformalData X)
    (Z : Set X) (hZ : Z ⊆ conformalLocus C) :
    metricPackingDimension Z = upperBSDimension C.T C.potential Z := by
  rw [classicalPointToSet_upper P Z]
  rw [bsPointToSet_upper P C.T C.uniformContinuous_T.continuous C.potential
    (distortionModuli C) Z (fun x hx ↦ (hZ hx).1.1.1)]
  apply iInf_congr
  intro A
  apply iSup_congr
  intro x
  apply iSup_congr
  intro hx
  exact pointwiseDimensionEqBS_upper P C A x (hZ hx)

/-- The same packing dimension agrees with the decorated Bowen packing dimension.
Blueprint node `conf:theorem-e`. -/
theorem dimensionTheorem_packing (P : Presentation X) (C : UniformConformalData X)
    (Z : Set X) (hZ : Z ⊆ conformalLocus C) :
    metricPackingDimension Z = packingBSDimension C.T C.potential Z := by
  let _ : TopologicalSpace.SeparableSpace X :=
    TopologicalSpace.SeparableSpace.of_denseRange P.ι P.dense
  rw [dimensionTheorem_upper P C Z hZ]
  exact (bsEquivalence_upper C.T C.uniformContinuous_T.continuous C.potential
    (distortionModuli C) Z (by
      intro x hx
      exact (hZ hx).1.1.1)).symm

section ConformalSets

variable (P : Presentation X) (C : UniformConformalData X) (Z : Set X)
  (hZ : Z ⊆ conformalLocus C)

include P hZ

/-- Both classical dimensions have the corresponding positive-pressure cut characterization.
Blueprint node `conf:bowen`. -/
theorem bowenEquation (σ : LimitSide) :
    σ.choose (_root_.dimH Z, metricPackingDimension Z) =
      positivePressureThreshold (fun s =>
        σ.choose (lowerPressure C.T (fun y => -s * C.potential y) 0 Z,
          upperPressure C.T (fun y => -s * C.potential y) 0 Z)) := by
  rw [dimensionTheorem P C Z hZ, dimensionTheorem_upper P C Z hZ]
  exact setBowenCriticalValue P C.T C.uniformContinuous_T.continuous C.potential
    (distortionModuli C) Z (fun x hx ↦ ⟨(hZ hx).1.1.1, (hZ hx).1.1.2.2⟩) σ

/-- The nonpositive-pressure cut gives the same classical dimension, including empty sets.
Blueprint node `conf:bowen`. -/
theorem bowenEquation_nonpositive (σ : LimitSide) :
    σ.choose (_root_.dimH Z, metricPackingDimension Z) =
      nonpositivePressureThreshold (fun s =>
        σ.choose (lowerPressure C.T (fun y => -s * C.potential y) 0 Z,
          upperPressure C.T (fun y => -s * C.potential y) 0 Z)) := by
  rw [dimensionTheorem P C Z hZ, dimensionTheorem_upper P C Z hZ]
  exact setBowenCriticalValue_nonpositive P C.T C.uniformContinuous_T.continuous C.potential
    (distortionModuli C) Z (fun x hx ↦ ⟨(hZ hx).1.1.1, (hZ hx).1.1.2.2⟩) σ

/-- The positive cut also equals the infimum of its pointwise-pressure oracle counterparts.
Blueprint node `conf:bowen`. -/
theorem bowenEquation_oracles (σ : LimitSide) :
    σ.choose (_root_.dimH Z, metricPackingDimension Z) =
      ⨅ A : Set ℕ, positivePressureThreshold (fun s =>
        ⨆ x ∈ Z, σ.choose (pointwisePressure P C.T (fun y => -s * C.potential y) A x)) := by
  rw [dimensionTheorem P C Z hZ, dimensionTheorem_upper P C Z hZ]
  exact setBowenCriticalValue_oracles P C.T C.uniformContinuous_T.continuous C.potential
    (distortionModuli C) Z (fun x hx ↦ ⟨(hZ hx).1.1.1, (hZ hx).1.1.2.2⟩) σ

/-- The nonpositive cut has the same all-oracle characterization.
Blueprint node `conf:bowen`. -/
theorem bowenEquation_oracles_nonpositive (σ : LimitSide) :
    σ.choose (_root_.dimH Z, metricPackingDimension Z) =
      ⨅ A : Set ℕ, nonpositivePressureThreshold (fun s =>
        ⨆ x ∈ Z, σ.choose (pointwisePressure P C.T (fun y => -s * C.potential y) A x)) := by
  rw [dimensionTheorem P C Z hZ, dimensionTheorem_upper P C Z hZ]
  exact setBowenCriticalValue_oracles_nonpositive P C.T C.uniformContinuous_T.continuous C.potential
    (distortionModuli C) Z (fun x hx ↦ ⟨(hZ hx).1.1.1, (hZ hx).1.1.2.2⟩) σ

/-- One admissible oracle cone attains both cut characterizations for both classical dimensions.
Blueprint node `conf:bowen`. -/
theorem bowenEquation_cone :
    ∃ A₀ : Set ℕ, ∀ A : Set ℕ, charOracle A₀ ≤ᵀ charOracle A →
      IsAdmissible P C.T (fun _ : Fin 1 => C.potential) A ∧ ∀ σ : LimitSide,
        let d := σ.choose (_root_.dimH Z, metricPackingDimension Z)
        let f := fun s : ℝ =>
          ⨆ x ∈ Z, σ.choose (pointwisePressure P C.T (fun y => -s * C.potential y) A x)
        d = positivePressureThreshold f ∧ d = nonpositivePressureThreshold f := by
  rw [dimensionTheorem P C Z hZ, dimensionTheorem_upper P C Z hZ]
  exact setBowenCriticalValue_cone P C.T C.uniformContinuous_T.continuous C.potential
    (distortionModuli C) Z (fun x hx ↦ ⟨(hZ hx).1.1.1, (hZ hx).1.1.2.2⟩)

/-- A finite classical dimension and a uniform finite upper average give the repaired root.
Blueprint node `conf:bowen`. -/
theorem bowenEquation_root (hne : Z.Nonempty) (β : ℝ)
    (hupper : ∀ x ∈ Z, upperBirkhoffAverage C.T C.potential x ≤ (β : EReal))
    (σ : LimitSide)
    (hfinite : σ.choose (_root_.dimH Z, metricPackingDimension Z) < ⊤) :
    let d := (σ.choose (_root_.dimH Z, metricPackingDimension Z)).toReal
    σ.choose (lowerPressure C.T (fun y => -d * C.potential y) 0 Z,
      upperPressure C.T (fun y => -d * C.potential y) 0 Z) = 0 := by
  rw [dimensionTheorem P C Z hZ, dimensionTheorem_upper P C Z hZ] at hfinite ⊢
  exact setBowenRootOfFiniteBSDimension P C.T C.uniformContinuous_T.continuous C.potential
    (distortionModuli C) Z hne β (fun x hx ↦ ⟨(hZ hx).1.1.1, hupper x hx⟩) σ hfinite

section UniformLower

variable (hne : Z.Nonempty) (α : ℝ) (hα : 0 < α)
  (hlower : ∀ x ∈ Z, (α : EReal) ≤ lowerBirkhoffAverage C.T C.potential x)
  (σ : LimitSide) (hfinite : σ.choose (lowerEntropy C.T Z, upperEntropy P C.T Z) < ⊤)

include hne hα hlower hfinite

/-- A uniform positive lower average and finite relevant entropy give at most one real root.
Blueprint node `conf:bowen`. -/
theorem bowenEquation_unique (s t : ℝ)
    (hs : σ.choose (lowerPressure C.T (fun y => -s * C.potential y) 0 Z,
      upperPressure C.T (fun y => -s * C.potential y) 0 Z) = 0)
    (ht : σ.choose (lowerPressure C.T (fun y => -t * C.potential y) 0 Z,
      upperPressure C.T (fun y => -t * C.potential y) 0 Z) = 0) : s = t := by
  exact setBowenRootUniqueness P C.T C.uniformContinuous_T.continuous C.potential
    (distortionModuli C) Z hne α hα (fun x hx ↦ ⟨hlower x hx, (hZ hx).1.1.2.2⟩) σ hfinite s t hs ht

/-- Under these hypotheses the corresponding pressure is finite on nonnegative parameters.
Blueprint node `conf:bowen`. -/
theorem bowenEquation_real (s : ℝ) (hs : 0 ≤ s) :
    ∃ v : ℝ, σ.choose (lowerPressure C.T (fun y => -s * C.potential y) 0 Z,
      upperPressure C.T (fun y => -s * C.potential y) 0 Z) = (v : EReal) := by
  exact setBowenRootUniqueness_real P C.T C.uniformContinuous_T.continuous C.potential
    (distortionModuli C) Z hne α hα (fun x hx ↦ ⟨hlower x hx, (hZ hx).1.1.2.2⟩) σ hfinite s hs

/-- Strict decrease is asserted on nonnegative parameters, where the pressure is finite.
Blueprint node `conf:bowen`. -/
theorem bowenEquation_strict :
    StrictAntiOn (fun s : ℝ =>
      σ.choose (lowerPressure C.T (fun y => -s * C.potential y) 0 Z,
        upperPressure C.T (fun y => -s * C.potential y) 0 Z)) (Set.Ici 0) := by
  exact setBowenRootUniqueness_strict P C.T C.uniformContinuous_T.continuous C.potential
    (distortionModuli C) Z hne α hα (fun x hx ↦ ⟨hlower x hx, (hZ hx).1.1.2.2⟩) σ hfinite

/-- The corresponding entropy divided by the common lower average bounds classical dimension.
Blueprint node `conf:bowen`. -/
theorem bowenEquation_dimension_le :
    σ.choose (_root_.dimH Z, metricPackingDimension Z) ≤
      σ.choose (lowerEntropy C.T Z, upperEntropy P C.T Z) / ENNReal.ofReal α := by
  rw [dimensionTheorem P C Z hZ, dimensionTheorem_upper P C Z hZ]
  exact setBowenRootUniqueness_dimension_le P C.T C.uniformContinuous_T.continuous C.potential
    (distortionModuli C) Z hne α hα (fun x hx ↦ ⟨hlower x hx, (hZ hx).1.1.2.2⟩) σ hfinite

/-- Finite entropy and the uniform positive lower average imply finite classical dimension.
Blueprint node `conf:bowen`. -/
theorem bowenEquation_dimension_finite :
    σ.choose (_root_.dimH Z, metricPackingDimension Z) < ⊤ := by
  exact (bowenEquation_dimension_le P C Z hZ hne α hα hlower σ hfinite).trans_lt
    (ENNReal.div_lt_top hfinite.ne (ne_of_gt (ENNReal.ofReal_pos.mpr hα)))

/-- Adding a common finite upper average gives the unique real root at classical dimension.
The root is finite and nonnegative; no potential is evaluated at an infinite parameter.
Blueprint node `conf:bowen`. -/
theorem bowenEquation_exists (β : ℝ)
    (hupper : ∀ x ∈ Z, upperBirkhoffAverage C.T C.potential x ≤ (β : EReal)) :
    ∃ d : ℝ, 0 ≤ d ∧
      ENNReal.ofReal d = σ.choose (_root_.dimH Z, metricPackingDimension Z) ∧
      ∀ s : ℝ, σ.choose (lowerPressure C.T (fun y => -s * C.potential y) 0 Z,
        upperPressure C.T (fun y => -s * C.potential y) 0 Z) = 0 ↔ s = d := by
  rw [dimensionTheorem P C Z hZ, dimensionTheorem_upper P C Z hZ]
  exact setBowenRootUniqueness_exists P C.T C.uniformContinuous_T.continuous C.potential
    (distortionModuli C) Z hne α hα (fun x hx ↦ ⟨hlower x hx, (hZ hx).1.1.2.2⟩) σ hfinite β hupper

end UniformLower
end ConformalSets

end Kolmogorov.PointToSet
