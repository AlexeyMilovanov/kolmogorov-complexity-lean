/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.BSDimension.Defs
import KolmogorovMathlib.PointToSet.PackingEquivalences.Defs
import KolmogorovMathlib.PointToSet.Pressure.Defs

/-!
# Uniform conformal data and classical metric contents

The logarithmic distance ratio lives on a neighborhood of the diagonal. Its exact
distance identity excludes local collisions without taking the logarithm of zero.
Average and increment limits reuse the existing Birkhoff sums and extended averages.

Classical packing uses decorated center/radius pairs and specified-radius weights.
The actual-diameter variant is separate and is used only by the regression theorem.
Box dimension reuses the open-ball covering infimum at order one and zero potential.
-/

namespace Kolmogorov.PointToSet

open Filter
open scoped Topology ENNReal

variable {X : Type*} [MetricSpace X]

/-- Uniform local conformality with a specified logarithmic distance ratio.
Blueprint node `conf:data`. -/
structure UniformConformalData (X : Type*) [MetricSpace X] where
  /-- The radius of the neighborhood on which the distance law holds. -/
  r₀ : ℝ
  /-- The neighborhood has positive radius. -/
  r₀_pos : 0 < r₀
  /-- The dynamics. -/
  T : X → X
  /-- Uniform continuity of the dynamics. -/
  uniformContinuous_T : UniformContinuous T
  /-- The real logarithmic distance ratio, defined only near the diagonal. -/
  ζ : {p : X × X // dist p.1 p.2 < r₀} → ℝ
  /-- Uniform continuity for the induced product uniformity. -/
  uniformContinuous_ζ : UniformContinuous ζ
  /-- The exact local distance identity, including coincident points. -/
  distance_eq : ∀ (x y : X) (h : dist x y < r₀),
    dist (T x) (T y) = (2 : ℝ) ^ ζ ⟨(x, y), h⟩ * dist x y

/-- The diagonal potential of the specified conformal data. Blueprint node `conf:data`. -/
def UniformConformalData.potential (C : UniformConformalData X) (x : X) : ℝ :=
  C.ζ ⟨(x, x), by simpa using C.r₀_pos⟩

/-- The positive finite lower/upper average locus, using the frozen extended averages.
Blueprint node `conf:data`. -/
def positiveFiniteAverageLocus (T : X → X) (u : X → ℝ) : Set X :=
  {x | 0 < lowerBirkhoffAverage T u x ∧
    lowerBirkhoffAverage T u x ≤ upperBirkhoffAverage T u x ∧
    upperBirkhoffAverage T u x < ⊤}

/-- Tempered contraction allows a finite lower bound for every strictly positive slack.
The constant precedes both time indices. Blueprint node `conf:data`. -/
def HasTemperedContraction (T : X → X) (u : X → ℝ) (x : X) : Prop :=
  ∀ τ : ℝ, 0 < τ → ∃ c : ℝ, ∀ n k : ℕ, k ≤ n →
    c ≤ birkhoffSum T u n x - birkhoffSum T u k x + n * τ

/-- Sublinear potential increments along the orbit; the initial term does not affect the limit.
Blueprint node `conf:data`. -/
def HasSublinearOrbitGrowth (T : X → X) (u : X → ℝ) (x : X) : Prop :=
  Tendsto (fun n : ℕ => u (T^[n] x) / n) atTop (𝓝 0)

/-- The intersection of the three loci in the conformal dimension theorem.
Blueprint node `conf:data`. -/
def conformalLocus (C : UniformConformalData X) : Set X :=
  positiveFiniteAverageLocus C.T C.potential ∩
    {x | HasTemperedContraction C.T C.potential x} ∩
    {x | HasSublinearOrbitGrowth C.T C.potential x}

/-- Nonnegative ratio-to-diagonal distortion, with empty supremum zero.
Only pairs in the domain of the ratio are used; comparisons assume a radius below `r₀`.
Blueprint node `conf:moduli`. -/
noncomputable def conformalDistortion (C : UniformConformalData X) (δ : ℝ) : ℝ≥0∞ :=
  ⨆ p : {p : X × X // dist p.1 p.2 < C.r₀},
    ⨆ (_ : 0 < dist p.val.1 p.val.2 ∧ dist p.val.1 p.val.2 ≤ δ),
      ENNReal.ofReal |C.ζ p - C.potential p.val.1|

/-- The one-step distortion estimate with half of the final positive error.
Blueprint node `conf:moduli`. -/
def HasConformalDistortionBound (C : UniformConformalData X) (τ δ₀ : ℝ) : Prop :=
  ∀ x y : X, dist x y < δ₀ →
    (2 : ℝ) ^ (C.potential x - τ / 2) * dist x y ≤ dist (C.T x) (C.T y) ∧
    dist (C.T x) (C.T y) ≤ (2 : ℝ) ^ (C.potential x + τ / 2) * dist x y

/-- Inner and outer orbit radii, selected respectively by the lower and upper side.
Blueprint node `conf:denominators`. -/
noncomputable def conformalOrbitRadius (C : UniformConformalData X) (σ : LimitSide)
    (x : X) (η δ τ : ℝ) (n : ℕ) : ℝ :=
  σ.choose (η * δ * (2 : ℝ) ^ (-birkhoffSum C.T C.potential n x - n * τ),
    δ * (2 : ℝ) ^ (-birkhoffSum C.T C.potential n x + n * τ))

/-- Base-two logarithmic precision of the corresponding orbit radius.
Blueprint node `conf:denominators`. -/
noncomputable def conformalOrbitPrecision (C : UniformConformalData X) (σ : LimitSide)
    (x : X) (η δ τ : ℝ) (n : ℕ) : ℝ :=
  -Real.logb 2 (conformalOrbitRadius C σ x η δ τ n)

/-- An ideal-centered dyadic cover with a prescribed minimum precision.
Blueprint node `conf:hausdorff-interface`. -/
def IsIdealDyadicCover (P : Presentation X) (Z : Set X) (M : ℕ)
    (E : Set (ℕ × ℕ)) : Prop :=
  (∀ a ∈ E, M ≤ a.2) ∧ Z ⊆ ⋃ a ∈ E, Metric.ball (P.ι a.1) (dyadicRadius a.2)

/-- Power-gauge cost of the distinct ideal-index/precision pairs of a dyadic cover.
Blueprint node `conf:hausdorff-interface`. -/
noncomputable def idealDyadicCoverCost (s : ℝ) (E : Set (ℕ × ℕ)) : ℝ≥0∞ :=
  ∑' a : E, (2 : ℝ≥0∞) ^ (-s * a.val.2)

/-- A countable decorated family of disjoint open balls centered in the target.
Positive radii and disjointness forbid repeated copies of a nonempty ball.
Blueprint node `conf:packing-box-interface`. -/
def IsDisjointMetricBallFamily (Z : Set X) (F : Set (X × ℝ)) : Prop :=
  F.Countable ∧ (∀ a ∈ F, a.1 ∈ Z ∧ 0 < a.2) ∧
    F.Pairwise fun a b => Disjoint (Metric.ball a.1 a.2) (Metric.ball b.1 b.2)

/-- A classical metric packing bounds the specified radii by the cutoff.
Blueprint node `conf:packing-box-interface`. -/
def IsMetricPacking (Z : Set X) (δ : ℝ) (F : Set (X × ℝ)) : Prop :=
  IsDisjointMetricBallFamily Z F ∧ ∀ a ∈ F, a.2 ≤ δ

/-- Specified-radius power-gauge mass; no actual ball diameter occurs in this weight.
Blueprint node `conf:packing-box-interface`. -/
noncomputable def metricPackingSum (s : ℝ) (F : Set (X × ℝ)) : ℝ≥0∞ :=
  ∑' a : F, ENNReal.ofReal (2 * a.val.2) ^ s

/-- The supremum of specified-radius packing masses at a positive cutoff.
Blueprint node `conf:packing-box-interface`. -/
noncomputable def metricPackingContent (Z : Set X) (s δ : ℝ) : ℝ≥0∞ :=
  ⨆ F : Set (X × ℝ), ⨆ (_ : IsMetricPacking Z δ F), metricPackingSum s F

/-- The small-radius packing premeasure, before countable outer regularization.
Blueprint node `conf:packing-box-interface`. -/
noncomputable def metricPackingPremeasure (Z : Set X) (s : ℝ) : ℝ≥0∞ :=
  ⨅ δ : ℝ, ⨅ (_ : 0 < δ), metricPackingContent Z s δ

/-- Countable outer regularization of the specified-radius packing premeasure.
Blueprint node `conf:packing-box-interface`. -/
noncomputable def metricPackingOuterMeasure (Z : Set X) (s : ℝ) : ℝ≥0∞ :=
  ⨅ Y : ℕ → Set X, ⨅ (_ : Z ⊆ ⋃ j, Y j), ∑' j, metricPackingPremeasure (Y j) s

/-- Classical packing dimension for the specified-radius convention, including zero on empty sets.
Blueprint node `conf:packing-box-interface`. -/
noncomputable def metricPackingDimension (Z : Set X) : ℝ≥0∞ :=
  ⨅ s : ℝ, ⨅ (_ : 0 ≤ s), ⨅ (_ : metricPackingOuterMeasure Z s = 0), ENNReal.ofReal s

/-- Upper box dimension from radius-`2⁻ⁿ` covering numbers, allowing infinity.
At order one with zero potential the existing partition sum counts covering centers.
The nonnegative projection sends the empty-set logarithm to zero.
Blueprint node `conf:packing-box-interface`. -/
noncomputable def upperBoxDimension (Z : Set X) : ℝ≥0∞ :=
  limsup (fun n => (pressureRate
    (fun k => partitionSum id (fun _ : X => 0) .centered Z 1 (dyadicRadius k)) n).toENNReal)
    atTop

/-- Countable modification of upper box dimension, with arbitrary covering pieces.
Blueprint node `conf:packing-box-interface`. -/
noncomputable def modifiedUpperBoxDimension (Z : Set X) : ℝ≥0∞ :=
  ⨅ Y : ℕ → Set X, ⨅ (_ : Z ⊆ ⋃ j, Y j), ⨆ j, upperBoxDimension (Y j)

/-- Actual-diameter packing content, used only to state the alternative-convention regression.
Here both the cutoff and the weight use the actual extended diameter of the open ball.
Blueprint node `conf:packing-diameter-counterexample`. -/
noncomputable def actualDiameterPackingContent (Z : Set X) (s δ : ℝ) : ℝ≥0∞ :=
  ⨆ F : Set (X × ℝ),
    ⨆ (_ : IsDisjointMetricBallFamily Z F ∧
      ∀ a ∈ F, Metric.ediam (Metric.ball a.1 a.2) ≤ ENNReal.ofReal δ),
      ∑' a : F, Metric.ediam (Metric.ball a.val.1 a.val.2) ^ s

/-- Small-diameter premeasure for the explicitly separate actual-diameter convention.
Blueprint node `conf:packing-diameter-counterexample`. -/
noncomputable def actualDiameterPackingPremeasure (Z : Set X) (s : ℝ) : ℝ≥0∞ :=
  ⨅ δ : ℝ, ⨅ (_ : 0 < δ), actualDiameterPackingContent Z s δ

/-- Countable outer regularization of actual-diameter packing premeasure.
Blueprint node `conf:packing-diameter-counterexample`. -/
noncomputable def actualDiameterPackingOuterMeasure (Z : Set X) (s : ℝ) : ℝ≥0∞ :=
  ⨅ Y : ℕ → Set X, ⨅ (_ : Z ⊆ ⋃ j, Y j),
    ∑' j, actualDiameterPackingPremeasure (Y j) s

/-- Critical dimension of the alternative actual-diameter convention.
Blueprint node `conf:packing-diameter-counterexample`. -/
noncomputable def actualDiameterPackingDimension (Z : Set X) : ℝ≥0∞ :=
  ⨅ s : ℝ, ⨅ (_ : 0 ≤ s),
    ⨅ (_ : actualDiameterPackingOuterMeasure Z s = 0), ENNReal.ofReal s

end Kolmogorov.PointToSet
