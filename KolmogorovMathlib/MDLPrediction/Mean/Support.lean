/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.MDLPrediction.Core.Model

/-!
# Common positive support and first exits

A string remains in the first-exit support when every strict prefix is positive under
both source measures. A first one-zero child retains its incoming mean mass.
Blueprint nodes: `exp:mean-support`.
-/

namespace Kolmogorov.MDLPrediction

open MeasureTheory
open scoped ENNReal

/-- Every strict prefix has positive mass under both sources.
Blueprint node `exp:mean-support`. -/
def CommonPositivePrefixes (P Q : Measure CantorSeq) (x : BitString) : Prop :=
  ∀ i : ℕ, i < x.length →
    0 < cantorMass P (x.take i) ∧ 0 < cantorMass Q (x.take i)

/-- Cylinder mass decreases when a bit string is extended. -/
private lemma cantorMass_antitone_prefix (μ : Measure CantorSeq) {x y : BitString} (h : x <+: y) :
    cantorMass μ y ≤ cantorMass μ x := by
  unfold cantorMass
  apply measure_mono
  exact cantorCylinder_subset_of_prefix h

/-- Positive endpoint masses give common positive strict prefixes.
Blueprint node `exp:mean-support`. -/
theorem exp_mean_support (P Q : Measure CantorSeq) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (x : BitString)
    (hP : 0 < cantorMass P x) (hQ : 0 < cantorMass Q x) :
    CommonPositivePrefixes P Q x := by
  intro i hi
  constructor
  · apply lt_of_lt_of_le hP
    apply cantorMass_antitone_prefix
    exact List.take_prefix i x
  · apply lt_of_lt_of_le hQ
    apply cantorMass_antitone_prefix
    exact List.take_prefix i x

/-- A zero-mass prefix kills the common-positive status of all strict descendants.
Blueprint node `exp:mean-support`. -/
theorem exp_mean_support_exit (P Q : Measure CantorSeq) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (x y : BitString)
    (hzero : (cantorMass P x = 0 ∧ 0 < cantorMass Q x) ∨
      (0 < cantorMass P x ∧ cantorMass Q x = 0))
    (hprefix : x <+: y) (hlen : x.length < y.length) :
    ¬ CommonPositivePrefixes P Q y := by
  intro hy
  have hyx := hy x.length hlen
  have eq1 : y.take x.length = x := (List.prefix_iff_eq_take.mp hprefix).symm
  rw [eq1] at hyx
  rcases hzero with ⟨hP, _⟩ | ⟨_, hQ⟩
  · have : cantorMass P x ≠ 0 := ne_of_gt hyx.1
    exact this hP
  · have : cantorMass Q x ≠ 0 := ne_of_gt hyx.2
    exact this hQ

end Kolmogorov.MDLPrediction
