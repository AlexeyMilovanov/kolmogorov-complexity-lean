import KolmogorovMathlib.AlgorithmicStatistics.CodedFiniteDistribution
import KolmogorovMathlib.Prefix.Symmetry

/-!
# Randomness Deficiency

This module defines the randomness deficiency $d(x \mid P)$ of a string $x$ with
respect to a finite probability model $P$. Instead of a fragile literal `-log`
definition, we define the relation $d(x \mid P) \le \beta$ as a stable
multiplicative inequality:

`2^{-K(x | P.code)} \le 2^\beta \cdot P(x)`

This avoids logarithms and negative infinities.
-/

namespace Kolmogorov

open scoped ENNReal

/-- `DeficiencyLe U P x beta` asserts that the randomness deficiency of `x` with
respect to the model `P` is bounded by `beta`.
In standard notation, this is `-log P(x) - KP(x | P) \le \beta`, which we write
as `2^{-KP(x | P.code)} \le 2^\beta \cdot P(x)`. -/
noncomputable def DeficiencyLe (U : Map) (P : CodedFiniteDistribution)
    (x : BitString) (beta : ℕ) : Prop :=
  P.DeficiencyLe U x beta

/-- Monotonicity in `beta`: if deficiency is bounded by `beta`, it is bounded by any larger `beta'`. -/
theorem DeficiencyLe.mono_beta {U : Map} {P : CodedFiniteDistribution} {x : BitString}
    {beta beta' : ℕ} (h : beta ≤ beta') (hdef : DeficiencyLe U P x beta) :
    DeficiencyLe U P x beta' := by
  calc
    complexityWeight (KP U x P.code) ≤ (2 : ℝ≥0∞) ^ beta * P.mass x := hdef
    _ ≤ (2 : ℝ≥0∞) ^ beta' * P.mass x := by
      exact mul_le_mul (pow_two_mono h) (le_refl _) (zero_le _) (zero_le _)

/-- If a model assigns probability 1 to a string, its deficiency is trivially bounded by 0. -/
theorem deficiencyLe_zero_of_mass_one (U : Map) (P : CodedFiniteDistribution) (x : BitString)
    (hmass : P.mass x = 1) : DeficiencyLe U P x 0 := by
  dsimp [DeficiencyLe]
  dsimp [CodedFiniteDistribution.DeficiencyLe, CodedFiniteDistribution.complexity]
  rw [hmass, pow_two_zero, mul_one]
  exact complexityWeight_KP_le_one U x P.code

/-- If `DeficiencyLe U P x beta`, then `P.mass x` cannot be zero unless the complexity is `⊤`.
Since `KP U x P.code` is `⊤` iff the string is unreachable, for an optimal machine this only happens if `x` is impossible. -/
theorem mass_pos_of_deficiencyLe_of_KP_ne_top {U : Map} {P : CodedFiniteDistribution} {x : BitString}
    {beta : ℕ} (hdef : DeficiencyLe U P x beta) (hKP : KP U x P.code ≠ ⊤) :
    0 < P.mass x := by
  by_contra hzero
  push_neg at hzero
  have hz : P.mass x = 0 := le_bot_iff.mp hzero
  unfold DeficiencyLe at hdef
  unfold CodedFiniteDistribution.DeficiencyLe at hdef
  rw [hz, mul_zero] at hdef
  have hpos : 0 < complexityWeight (KP U x P.code) := (complexityWeight_pos_iff _).mpr hKP
  exact not_le.mpr hpos hdef

/-- High-deficiency predicate: strings `x` whose deficiency exceeds `beta`. -/
def HighDeficiency (U : Map) (P : CodedFiniteDistribution) (beta : ℕ) (x : BitString) : Prop :=
  ¬ DeficiencyLe U P x beta

end Kolmogorov
