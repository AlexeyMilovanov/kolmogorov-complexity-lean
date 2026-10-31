/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.Dynamics

/-!
# Separated sets and decorated Bowen packings

Separation uses the existing Bowen distance. A packing is a countable set of
center/order pairs, and disjointness is tested on distinct pairs, not on distinct
underlying balls. The radius is a parameter of the family, never an actual diameter.
Potential variation is extended nonnegative; finite-scale real error terms require
an explicit finiteness hypothesis before using its real value.
-/

namespace Kolmogorov.PointToSet

open scoped ENNReal

variable {X : Type*} [MetricSpace X]

/-- Distinct centers have Bowen distance at least the specified radius.
Blueprint node `pack:countable-net`. -/
def IsBowenSeparated (T : X → X) (n : ℕ) (r : ℝ) (F : Set X) : Prop :=
  F.Pairwise fun x y => r ≤ bowenDist T n x y

/-- The extended oscillation on pairs at distance at most the specified radius.
Blueprint node `pack:supweight`. -/
noncomputable def potentialVariation (f : X → ℝ) (r : ℝ) : ℝ≥0∞ :=
  ⨆ x : X, ⨆ y : X, ⨆ (_ : dist x y ≤ r), ENNReal.ofReal |f x - f y|

/-- The potential variation of a uniformly continuous function is eventually at most any
positive bound as the radius tends to zero from above. -/
theorem eventually_potentialVariation_le_ofReal {f : X → ℝ} (hf : UniformContinuous f)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℝ in nhdsWithin 0 (Set.Ioi 0), potentialVariation f r ≤ ENNReal.ofReal ε := by
  obtain ⟨δ, hδ, hfδ⟩ := Metric.uniformContinuous_iff.mp hf ε hε
  filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
  exact iSup₂_le fun x y ↦ iSup_le fun hxy ↦
    ENNReal.ofReal_le_ofReal (hfδ (hxy.trans_lt hr.2)).le

/-- The potential variation of a uniformly continuous function is eventually finite as the
radius tends to zero from above. -/
theorem eventually_potentialVariation_lt_top {f : X → ℝ} (hf : UniformContinuous f) :
    ∀ᶠ r : ℝ in nhdsWithin 0 (Set.Ioi 0), potentialVariation f r < ⊤ :=
  (eventually_potentialVariation_le_ofReal hf one_pos).mono fun _ h ↦
    h.trans_lt ENNReal.ofReal_lt_top

/-- The real potential variation of a uniformly continuous function tends to zero with the
radius. -/
theorem tendsto_potentialVariation_toReal {f : X → ℝ} (hf : UniformContinuous f) :
    Filter.Tendsto (fun r : ℝ ↦ ((potentialVariation f r).toReal : EReal))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  rw [show (0 : EReal) = ((0 : ℝ) : EReal) from rfl, EReal.tendsto_coe]
  refine Metric.tendsto_nhds.mpr fun ε hε ↦ ?_
  filter_upwards [eventually_potentialVariation_le_ofReal hf (half_pos hε)] with r hr
  rw [Real.dist_eq, sub_zero, abs_of_nonneg ENNReal.toReal_nonneg]
  calc (potentialVariation f r).toReal ≤ ε / 2 := by
        simpa [ENNReal.toReal_ofReal (half_pos hε).le] using
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hr
    _ < ε := half_lt_self hε

/-- A finite or countable decorated packing with centers in the set and positive orders.
Distinct center/order pairs must give disjoint balls, even if their underlying sets agree.
Blueprint node `pack:outer`. -/
def IsBowenPacking (T : X → X) (Z : Set X) (r : ℝ) (N : ℕ)
    (F : Set (X × ℕ)) : Prop :=
  F.Countable ∧ (∀ a ∈ F, a.1 ∈ Z ∧ max 1 N ≤ a.2) ∧
    F.Pairwise fun a b => Disjoint (bowenBall T a.2 a.1 r) (bowenBall T b.2 b.1 r)

end Kolmogorov.PointToSet
