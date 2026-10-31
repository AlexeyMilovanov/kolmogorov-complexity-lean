/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.Dynamics
import KolmogorovMathlib.PointToSet.Pressure.Defs

/-!
# BS covering masses, capacity dimensions and discrete witnesses

Dimensions and masses take values in `ENNReal`. Critical exponents are nonnegative reals.
The sup-weight is the negative power of the existing exponentiated potential supremum;
this retains the extended value at coarse scales. Countable lower covers reuse
`BowenCoverFamily`, including empty families and repeated balls.

The pointwise definitions are the frozen `finiteScaleBSCost` and `pointwiseBSDimension`
from `Dynamics`. All effective definitions fix the presentation before the oracle.
-/

namespace Kolmogorov.PointToSet

open Filter
open scoped Topology ENNReal Computability

variable {X : Type*} [MetricSpace X]

/-- The upper Birkhoff average, with infinite values retained in `EReal`.
Blueprint node `bs:realizer-bounds`. -/
noncomputable def upperBirkhoffAverage (T : X → X) (u : X → ℝ) (x : X) : EReal :=
  limsup (fun n => ((birkhoffSum T u n x / n : ℝ) : EReal)) atTop

/-- A uniform positive-average piece of a set, with rational slope and order cutoff.
Blueprint node `bs:exhaustion`. -/
def positiveAveragePiece (T : X → X) (u : X → ℝ) (Z : Set X) (N : ℕ) (ρ : ℚ) : Set X :=
  {x ∈ Z | ∀ n ≥ N, (ρ : ℝ) * n ≤ birkhoffSum T u n x}

/-- The two time asymptotics used in the Bowen equation. Blueprint node `bs:affine-slope`. -/
inductive LimitSide where
  /-- Lower time limits and lower covering dimensions. -/
  | lower
  /-- Upper time limits and modified upper dimensions. -/
  | upper

/-- Select the lower or upper entry of an existing pair of asymptotic quantities.
Blueprint node `bs:affine-slope`. -/
def LimitSide.choose {α : Type*} (σ : LimitSide) (v : α × α) : α :=
  match σ with
  | .lower => v.1
  | .upper => v.2

/-- Take the indicated extended lower or upper time limit.
Blueprint node `bs:affine-slope`. -/
noncomputable def LimitSide.timeLimit {α : Type*} [CompleteLattice α]
    (σ : LimitSide) (v : ℕ → α) : α :=
  σ.choose (liminf v atTop, limsup v atTop)

/-- Both time limits are monotone under eventual inequality. -/
theorem LimitSide.timeLimit_mono {α : Type*} [CompleteLattice α] (σ : LimitSide)
    {f g : ℕ → α} (h : ∀ᶠ n in atTop, f n ≤ g n) : σ.timeLimit f ≤ σ.timeLimit g := by
  cases σ
  · exact liminf_le_liminf h
  · exact limsup_le_limsup h

/-- The BS weight is `2 ^ (-s * W)` at every finite supremum `W`.
Negative powers of the extended exponential also define it at unbounded scales.
Blueprint node `bs:lower-mass`. -/
noncomputable def bsBallWeight (T : X → X) (u : X → ℝ) (s : ℝ) (n : ℕ)
    (y : X) (r : ℝ) : ℝ≥0∞ :=
  pressureBallWeight T u .supremum n y r ^ (-s)

/-- Total sup-weight BS cost of a countably indexed family, including multiplicities.
Blueprint node `bs:lower-mass`. -/
noncomputable def bsCoverCost (T : X → X) (u : X → ℝ) (s r : ℝ)
    (C : BowenCoverFamily X) : ℝ≥0∞ :=
  ∑' j, bsBallWeight T u s (C.order j) (C.center j) r

/-- Lower BS mass with a positive order cutoff, defined by a covering infimum.
Blueprint node `bs:lower-mass`. -/
noncomputable def lowerBSMass (T : X → X) (u : X → ℝ) (Z : Set X)
    (s r : ℝ) (N : ℕ) : ℝ≥0∞ :=
  ⨅ C : BowenCoverFamily X, ⨅ (_ : IsBowenCover T Z r N C), bsCoverCost T u s r C

/-- Lower BS mass after the order cutoff tends to infinity.
Blueprint node `bs:lower-mass`. -/
noncomputable def lowerBSMassLimit (T : X → X) (u : X → ℝ) (Z : Set X)
    (s r : ℝ) : ℝ≥0∞ :=
  ⨆ N : ℕ, ⨆ (_ : 1 ≤ N), lowerBSMass T u Z s r N

/-- The nonnegative critical infimum of vanishing lower mass at one radius.
Blueprint node `bs:lower-mass`. -/
noncomputable def lowerBSDimensionAt (T : X → X) (u : X → ℝ) (Z : Set X)
    (r : ℝ) : ℝ≥0∞ :=
  ⨅ s : ℝ, ⨅ (_ : 0 ≤ s), ⨅ (_ : lowerBSMassLimit T u Z s r = 0), ENNReal.ofReal s

/-- The lower BS dimension is the increasing scale supremum along dyadic radii.
Blueprint node `bs:lower-mass`. -/
noncomputable def lowerBSDimension (T : X → X) (u : X → ℝ) (Z : Set X) : ℝ≥0∞ :=
  ⨆ p : ℕ, lowerBSDimensionAt T u Z (dyadicRadius p)

/-- Fixed-order BS cost of a set of centers, without enumeration multiplicity.
Blueprint node `bs:upper-capacity`. -/
noncomputable def bsPartitionCoverCost (T : X → X) (u : X → ℝ) (s r : ℝ)
    (n : ℕ) (F : Set X) : ℝ≥0∞ :=
  ∑' y : F, bsBallWeight T u s n y r

/-- The fixed-order covering infimum used for BS capacity.
Blueprint node `bs:upper-capacity`. -/
noncomputable def bsPartitionSum (T : X → X) (u : X → ℝ) (Z : Set X)
    (s r : ℝ) (n : ℕ) : ℝ≥0∞ :=
  ⨅ F : Set X, ⨅ (_ : F.Countable ∧ Z ⊆ ⋃ y ∈ F, bowenBall T n y r),
    bsPartitionCoverCost T u s r n F

/-- Upper BS capacity uses finiteness, rather than vanishing, of the upper mass limit.
Blueprint node `bs:upper-capacity`. -/
noncomputable def upperBSCapacityAt (T : X → X) (u : X → ℝ) (Z : Set X)
    (r : ℝ) : ℝ≥0∞ :=
  ⨅ s : ℝ, ⨅ (_ : 0 ≤ s),
    ⨅ (_ : limsup (bsPartitionSum T u Z s r) atTop < ⊤), ENNReal.ofReal s

/-- Countable modification restricts every covering piece to the original set.
Blueprint node `bs:upper-capacity`. -/
noncomputable def modifiedUpperBSDimension (T : X → X) (u : X → ℝ) (Z : Set X)
    (r : ℝ) : ℝ≥0∞ :=
  ⨅ Y : ℕ → Set X, ⨅ (_ : (∀ k, Y k ⊆ Z) ∧ Z ⊆ ⋃ k, Y k),
    ⨆ k, upperBSCapacityAt T u (Y k) r

/-- The modified upper BS dimension is the increasing scale supremum.
Blueprint node `bs:upper-capacity`. -/
noncomputable def upperBSDimension (T : X → X) (u : X → ℝ) (Z : Set X) : ℝ≥0∞ :=
  ⨆ p : ℕ, modifiedUpperBSDimension T u Z (dyadicRadius p)

/-- The zero threshold used only after refining into positive-average pieces.
Blueprint node `bs:upper-refinement`. -/
noncomputable def upperBSZeroCapacityAt (T : X → X) (u : X → ℝ) (Z : Set X)
    (r : ℝ) : ℝ≥0∞ :=
  ⨅ s : ℝ, ⨅ (_ : 0 ≤ s),
    ⨅ (_ : limsup (bsPartitionSum T u Z s r) atTop = 0), ENNReal.ofReal s

/-- Countable modification of the zero capacity threshold, with pieces inside the set.
Blueprint node `bs:upper-refinement`. -/
noncomputable def modifiedUpperBSZeroDimension (T : X → X) (u : X → ℝ) (Z : Set X)
    (r : ℝ) : ℝ≥0∞ :=
  ⨅ Y : ℕ → Set X, ⨅ (_ : (∀ k, Y k ⊆ Z) ∧ Z ⊆ ⋃ k, Y k),
    ⨆ k, upperBSZeroCapacityAt T u (Y k) r

/-- Total center-weight mass of distinct encoded triples; negative sums are permitted.
Blueprint node `bs:discrete`. -/
noncomputable def nullBSMass (P : Presentation X) (T : X → X) (u : X → ℝ)
    (s : ℝ) (E : Set (ℕ × ℕ × ℕ)) : ℝ≥0∞ :=
  nullPressureMass P T (fun y => -s * u y) 0 E

/-- A finite-mass null cover covers every scale at arbitrarily large positive orders.
Blueprint node `bs:discrete`. -/
def IsNullBSCover (P : Presentation X) (T : X → X) (u : X → ℝ) (Z : Set X)
    (s : ℝ) (E : Set (ℕ × ℕ × ℕ)) : Prop :=
  nullBSMass P T u s E < ⊤ ∧ ∀ p k, ∀ x ∈ Z, ∃ i n,
    max 1 k ≤ n ∧ (i, n, p) ∈ E ∧ x ∈ bowenBall T n (P.ι i) (dyadicRadius p)

/-- The center-weight mass of one uniform BS slice, counting each ideal index once.
Blueprint node `bs:discrete`. -/
noncomputable def uniformBSSum (P : Presentation X) (T : X → X) (u : X → ℝ)
    (s : ℝ) (E : Set (ℕ × ℕ × ℕ × ℕ)) (n p k : ℕ) : ℝ≥0∞ :=
  uniformPressureSum P T (fun y => -s * u y) E n p k

/-- A uniform net has finite upper slice mass limits and one slice parameter per point
and scale that covers every positive order. Blueprint node `bs:discrete`. -/
def IsUniformBSNet (P : Presentation X) (T : X → X) (u : X → ℝ) (Z : Set X)
    (s : ℝ) (E : Set (ℕ × ℕ × ℕ × ℕ)) : Prop :=
  (∀ p k, limsup (fun n => uniformBSSum P T u s E n p k) atTop < ⊤) ∧
    ∀ p, ∀ x ∈ Z, ∃ k, ∀ n ≥ 1, ∃ i, (i, n, p, k) ∈ E ∧
      x ∈ bowenBall T n (P.ι i) (dyadicRadius p)

/-- The two discrete witness predicates, with the null cover first and the net second.
Blueprint node `bs:discrete`. -/
def bsDiscreteWitnesses (P : Presentation X) (T : X → X) (u : X → ℝ) (Z : Set X)
    (s : ℝ) : (Set (ℕ × ℕ × ℕ) → Prop) × (Set (ℕ × ℕ × ℕ × ℕ) → Prop) :=
  (IsNullBSCover P T u Z s, IsUniformBSNet P T u Z s)

/-- Effective lower BS dimension restricts the nonnegative witness infimum to
relatively enumerable null covers; exponents need not be computable.
Blueprint node `bs:effective`. -/
noncomputable def effectiveLowerBSDimension (P : Presentation X) (T : X → X)
    (u : X → ℝ) (A : Set ℕ) (Z : Set X) : ℝ≥0∞ :=
  ⨅ s : ℝ, ⨅ (_ : 0 ≤ s), ⨅ E : Set (ℕ × ℕ × ℕ),
    ⨅ (_ : IsNullBSCover P T u Z s E ∧ IsREIn A E), ENNReal.ofReal s

/-- Effective upper BS dimension uses relatively enumerable uniform nets.
Blueprint node `bs:effective`. -/
noncomputable def effectiveUpperBSDimension (P : Presentation X) (T : X → X)
    (u : X → ℝ) (A : Set ℕ) (Z : Set X) : ℝ≥0∞ :=
  ⨅ s : ℝ, ⨅ (_ : 0 ≤ s), ⨅ E : Set (ℕ × ℕ × ℕ × ℕ),
    ⨅ (_ : IsUniformBSNet P T u Z s E ∧ IsREIn A E), ENNReal.ofReal s

/-- The pair of effective lower and upper BS dimensions, total for every oracle.
Blueprint node `bs:effective`. -/
noncomputable def effectiveBSDimensions (P : Presentation X) (T : X → X) (u : X → ℝ)
    (A : Set ℕ) (Z : Set X) : ℝ≥0∞ × ℝ≥0∞ :=
  (effectiveLowerBSDimension P T u A Z, effectiveUpperBSDimension P T u A Z)

/-- The nonnegative supremum of parameters where a signed pressure is positive.
Blueprint node `bs:dense-threshold`. -/
noncomputable def positivePressureThreshold (f : ℝ → EReal) : ℝ≥0∞ :=
  ⨆ s : ℝ, ⨆ (_ : 0 ≤ s), ⨆ (_ : 0 < f s), ENNReal.ofReal s

/-- The nonnegative infimum of parameters where a signed pressure is nonpositive.
Blueprint node `bs:dense-threshold`. -/
noncomputable def nonpositivePressureThreshold (f : ℝ → EReal) : ℝ≥0∞ :=
  ⨅ s : ℝ, ⨅ (_ : 0 ≤ s), ⨅ (_ : f s ≤ 0), ENNReal.ofReal s

end Kolmogorov.PointToSet
