import KolmogorovMathlib.AlgorithmicProbability.UniversalMixture
import KolmogorovMathlib.AlgorithmicProbability.UniversalSemimeasure
import KolmogorovMathlib.MonotoneComplexity.TreeSemimeasure
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitinCore
import KolmogorovMathlib.Core.Basic
import KolmogorovMathlib.Foundation.NatEncoding

/-!
# Mixing continuous tree semimeasures

`continuousTreeMixture b = ∑ i, 2 ^ (-i-1) * b i` combines a family of continuous tree
semimeasures into one. The root normalisation and the child inequality both pass to the mixture
(`continuousTreeMixture_nil`, `continuousTreeMixture_children_le`,
`continuousTreeMixture_isContinuousTreeSemimeasure`), the mixture dominates each component with
that component's dyadic weight (`continuousTreeMixture_dominates_component`), and lower
semicomputability is preserved
(`continuousTreeMixture_dyadicWeight_isLowerSemicomputableContinuousSemimeasure`). Applied to the
standard enumeration this is how a maximal semimeasure is obtained.
-/

namespace Kolmogorov
open scoped ENNReal
open ENNReal

/-- The mixture `∑ 2 ^ (-i-1) b i` of a family of continuous tree semimeasures. -/
noncomputable def continuousTreeMixture (b : ℕ → BitString → ℝ≥0∞) : BitString → ℝ≥0∞ :=
  fun x => ∑' i, dyadicWeight i * b i x

/-- A mixture of families normalised at the root is itself normalised at the root. -/
lemma continuousTreeMixture_nil (b : ℕ → BitString → ℝ≥0∞)
    (hb : ∀ i, b i ([] : BitString) = 1) :
    continuousTreeMixture b ([] : BitString) = 1 := by
  simp_rw [continuousTreeMixture, hb, mul_one]
  exact tsum_dyadicWeight

/-- A mixture of families satisfying the child inequality satisfies it too. -/
lemma continuousTreeMixture_children_le (b : ℕ → BitString → ℝ≥0∞)
    (hb : ∀ i x, b i (x ++ [false]) + b i (x ++ [true]) ≤ b i x) (x : BitString) :
    continuousTreeMixture b (x ++ [false]) + continuousTreeMixture b (x ++ [true])
      ≤ continuousTreeMixture b x := by
  dsimp [continuousTreeMixture]
  rw [← ENNReal.tsum_add]
  · apply ENNReal.tsum_le_tsum
    intro i
    rw [← mul_add]
    gcongr
    apply hb

/-- A mixture of continuous tree semimeasures is a continuous tree semimeasure. -/
theorem continuousTreeMixture_isContinuousTreeSemimeasure
    (b : ℕ → BitString → ℝ≥0∞) (hb : ∀ i, IsContinuousTreeSemimeasure (b i)) :
    IsContinuousTreeSemimeasure (continuousTreeMixture b) := by
  constructor
  · exact continuousTreeMixture_nil b (fun i => (hb i).1)
  · intro x
    exact continuousTreeMixture_children_le b (fun i y => (hb i).2 y) x

/-- The mixture dominates each component with the component's own dyadic weight. -/
theorem continuousTreeMixture_dominates_component (b : ℕ → BitString → ℝ≥0∞) (i : ℕ)
    (x : BitString) :
    dyadicWeight i * b i x ≤ continuousTreeMixture b x := by
  apply ENNReal.le_tsum

/-- A mixture of continuous tree semimeasures with a uniformly computable monotone approximation is
lower semicomputable. -/
theorem continuousTreeMixture_dyadicWeight_isLowerSemicomputableContinuousSemimeasure
    {a : ℕ → ℕ → BitString → BitString → ℕ}
    (b : ℕ → BitString → ℝ≥0∞)
    (hmono : ∀ i s out ctx, dyadicValue (a i s out ctx) s ≤
      dyadicValue (a i (s + 1) out ctx) (s + 1))
    (hsup : ∀ i out ctx, ⨆ s, dyadicValue (a i s out ctx) s = b i out)
    (hb_cont : ∀ i, IsContinuousTreeSemimeasure (b i))
    (h_comp : Computable (fun p : ℕ × ℕ × BitString × BitString =>
      a p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    IsLowerSemicomputableContinuousSemimeasure (continuousTreeMixture b) := by
  constructor
  · apply continuousTreeMixture_isContinuousTreeSemimeasure b hb_cont
  · let μ : ℕ → BitString → BitString → ℝ≥0∞ := fun i out _ => b i out
    have hsup' : ∀ i out ctx, ⨆ s, dyadicValue (a i s out ctx) s = μ i out ctx := hsup
    apply isLSC_unaryMixture_dyadicWeight_of_uniform (μ := μ) (a := a) hmono hsup' h_comp

end Kolmogorov
