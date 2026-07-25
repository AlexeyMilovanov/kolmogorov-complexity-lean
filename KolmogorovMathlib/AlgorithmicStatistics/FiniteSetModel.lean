import KolmogorovMathlib.AlgorithmicStatistics.Stochasticity

/-!
# Coded Finite-Set Models and Level Sets

This module is the coded replacement for the old finite-set model layer.  A
level-set model is now `codedUniformOn` the level set, so its code is determined
by the finite rational distribution data rather than an arbitrary label.
-/

namespace Kolmogorov

open scoped ENNReal

/-- The level set of a coded finite distribution `P` at threshold `2^{-k}`. -/
noncomputable def levelSet (P : CodedFiniteDistribution) (k : Nat) : Finset BitString :=
  P.support.filter (fun y => (2 : ENNReal)⁻¹ ^ k <= P.mass y)

/-- If `x` is in the support and has mass at least `2^{-k}`, then it is in the level set. -/
theorem mem_levelSet {P : CodedFiniteDistribution} {k : Nat} {x : BitString}
    (hx_support : x ∈ P.support)
    (hx : (2 : ENNReal)⁻¹ ^ k <= P.mass x) : x ∈ levelSet P k := by
  rw [levelSet, Finset.mem_filter]
  exact ⟨hx_support, hx⟩

/-
Cardinality bound for coded probability level sets.  The proof obligation is
the same counting argument as before, now parameterized by `P.IsProbability`.
-/
theorem levelSet_card_le (P : CodedFiniteDistribution) (k : Nat)
    (hprob : P.IsProbability) :
    ((levelSet P k).card : ENNReal) <= (2 : ENNReal) ^ k := by
  -- Each element in the level set has a mass of at least 2^-k.
  have h_mass_ge : ∀ y ∈ levelSet P k, P.mass y ≥ (2 : ENNReal)⁻¹ ^ k := by
    exact fun y hy => Finset.mem_filter.mp hy |>.2;
  -- The sum of the masses of the elements in the level set is at most 1.
  have h_sum_mass_le : ∑ y ∈ levelSet P k, P.mass y ≤ 1 := by
    exact hprob ▸ Finset.sum_le_sum_of_subset ( Finset.filter_subset _ _ );
  contrapose! h_sum_mass_le;
  refine lt_of_lt_of_le ?_ ( Finset.sum_le_sum h_mass_ge ) ; norm_num;
  rw [ ← ENNReal.toReal_lt_toReal ] at * <;> norm_num at *;
  · convert mul_lt_mul_of_pos_right h_sum_mass_le
      (by positivity : 0 < (1 / 2 : ℝ) ^ k) using 1
    norm_num [← mul_pow]
  · exact ENNReal.mul_ne_top ( by norm_num ) ( by norm_num )

/-- The coded uniform distribution over a nonempty level set. -/
noncomputable def levelSetModel (P : CodedFiniteDistribution) (k : Nat)
    (h_nonempty : (levelSet P k).Nonempty) : CodedFiniteDistribution :=
  codedUniformOn (levelSet P k) h_nonempty

theorem levelSetModel_isProbability (P : CodedFiniteDistribution) (k : Nat)
    (h_nonempty : (levelSet P k).Nonempty) :
    (levelSetModel P k h_nonempty).IsProbability :=
  codedUniformOn_isProbability _ _

/-
If `x` belongs to the `k`-th level set, its coded level-set model mass is at
least `2^{-k}`.
-/
theorem levelSetModel_mass_ge (P : CodedFiniteDistribution) (k : Nat)
    (hprob : P.IsProbability) (h_nonempty : (levelSet P k).Nonempty)
    (x : BitString) (hx : x ∈ levelSet P k) :
    (2 : ENNReal)⁻¹ ^ k <= (levelSetModel P k h_nonempty).mass x := by
  have h_card : (levelSet P k).card ≤ 2 ^ k := by
    convert levelSet_card_le P k hprob using 1;
    norm_cast;
  unfold levelSetModel
  rw [codedUniformOn_mass_of_mem (levelSet P k) h_nonempty x hx]
  rw [← ENNReal.inv_pow]
  apply ENNReal.inv_le_inv.mpr
  exact_mod_cast h_card

/-
Deficiency under a coded level-set model, using its canonical code.
-/
theorem deficiencyLe_levelSetModel (U : Map) (P : CodedFiniteDistribution) (k : Nat)
    (h_nonempty : (levelSet P k).Nonempty)
    (x : BitString) (hx : x ∈ levelSet P k)
    (beta : Nat)
    (h_weight :
      complexityWeight (KP U x (levelSetModel P k h_nonempty).code) <=
        (2 : ENNReal) ^ beta * ((levelSet P k).card : ENNReal)⁻¹) :
    DeficiencyLe U (levelSetModel P k h_nonempty) x beta := by
  -- By definition of `DeficiencyLe`, the complexity weight is at most
  -- `2^beta` times the mass.
  unfold DeficiencyLe;
  convert h_weight using 1;
  unfold CodedFiniteDistribution.DeficiencyLe;
  convert Iff.rfl;
  convert ( codedUniformOn_mass_of_mem ( levelSet P k ) h_nonempty x hx ) |> Eq.symm

/-- A coded level-set model can witness stochasticity when its canonical model
complexity and deficiency bounds are available. -/
theorem isStochastic_levelSetModel_of_model (U : Map) (P : CodedFiniteDistribution) (k : Nat)
    (h_nonempty : (levelSet P k).Nonempty)
    (x : BitString) (hx : x ∈ levelSet P k)
    (alpha beta : Nat)
    (h_comp : (levelSetModel P k h_nonempty).complexity U <= (alpha : ENat))
    (h_weight :
      complexityWeight (KP U x (levelSetModel P k h_nonempty).code) <=
        (2 : ENNReal) ^ beta * ((levelSet P k).card : ENNReal)⁻¹) :
    IsStochastic U x alpha beta := by
  apply isStochastic_of_model U x (levelSetModel P k h_nonempty) alpha beta
  · exact levelSetModel_isProbability P k h_nonempty
  · exact h_comp
  · exact deficiencyLe_levelSetModel U P k h_nonempty x hx beta h_weight
end Kolmogorov
