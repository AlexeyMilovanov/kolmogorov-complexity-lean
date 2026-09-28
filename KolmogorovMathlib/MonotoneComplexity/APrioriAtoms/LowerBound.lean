import KolmogorovMathlib.AlgorithmicProbability.UniversalSemimeasure
import KolmogorovMathlib.MonotoneComplexity.APrioriAtoms.Basic
import KolmogorovMathlib.MonotoneComplexity.APrioriAtoms.Mixture

/-!
# The discrete a priori probability is below the atom masses

Modify a probabilistic algorithm that prints a finite string `x` with probability `m x` so
that, after printing `x`, it prints a zero and then ones forever.  The result is the mixture
`discreteAtomMixture m = branchMixture m atomSeq`: a lower semicomputable continuous
semimeasure whose mass at the branch `x01^∞` is at least `m x`.  Maximality of the a priori
probability on the tree then gives one constant `c` with `c * m x ≤ atomMass x` for every `x`,
i.e. `m x ≤ C * atomMass x` — the first half of the note.

Only lower semicomputability of `m` is used; universality enters just to name `m`.

Source: the note `apriori-atoms.md`, section "Почему m(x) ≤ C f(x)"; SUV Chapter 5, §5.2.
-/

open scoped ENNReal

namespace Kolmogorov

/-- The continuous semimeasure that puts the discrete weight `m x` on the branch `x01^∞`.

Source: the note `apriori-atoms.md`, section "Почему m(x) ≤ C f(x)"; SUV Chapter 5, §5.2. -/
noncomputable def discreteAtomMixture (m : BitString → ℝ≥0∞) : BitString → ℝ≥0∞ :=
  branchMixture m atomSeq

/-- The mixture of the atoms of a semimeasure carries at most mass one at the root. -/
theorem discreteAtomMixture_root_le_one {m : BitString → ℝ≥0∞} (hm : IsSemimeasure m) :
    discreteAtomMixture m [] ≤ 1 := by
  rw [discreteAtomMixture, branchMixture_root]
  exact hm

/-- The mixture of the atoms of a semimeasure satisfies the child inequality. -/
theorem discreteAtomMixture_child_le (m : BitString → ℝ≥0∞) (u : BitString) :
    discreteAtomMixture m (u ++ [false]) + discreteAtomMixture m (u ++ [true]) ≤
      discreteAtomMixture m u :=
  branchMixture_child_le m atomSeq u

/-- The weights of the atom mixture, read through the index decoding, are lower
semicomputable: the decoding is computable and the weights themselves are lower
semicomputable.

Source: the note `apriori-atoms.md`, section "Почему m(x) ≤ C f(x)"; SUV Chapter 5, §5.2. -/
theorem indexWeight_isLSC {m : BitString → ℝ≥0∞} (hm : IsLSC fun x _ => m x) :
    IsLSC fun (x : BitString) (_ : BitString) => indexWeight m x :=
  isLSC_option_elim hm (computable_decodeIndex BitString)

/-- The mixture of the atoms of a lower semicomputable semimeasure is lower semicomputable:
the weights are enumerated from below and the branches are computable uniformly in `x`. -/
theorem discreteAtomMixture_isLSC {m : BitString → ℝ≥0∞} (hm : IsLSC fun x _ => m x) :
    IsLSC fun u _ => discreteAtomMixture m u :=
  branchMixture_isLSC m atomSeq (indexWeight_isLSC hm) computable_atomSeq

/-- Every string of the branch of `x` carries at least the discrete weight of `x`.

Source: the note `apriori-atoms.md`, section "Почему m(x) ≤ C f(x)"; SUV Chapter 5, §5.2. -/
theorem le_discreteAtomMixture_tailOnes (m : BitString → ℝ≥0∞) (x : BitString) (k : ℕ) :
    m x ≤ discreteAtomMixture m (tailOnes x k) := by
  refine le_branchMixture m atomSeq x ?_
  rw [length_tailOnes]
  exact cantorPrefix_atomSeq x k

/-- **The atom mass dominates a lower semicomputable semimeasure.**  There is one positive
finite constant `c` with `c * m x ≤ atomMass x` for every string `x`.

Source: the note `apriori-atoms.md`, section "Почему m(x) ≤ C f(x)"; SUV Chapter 5, §5.2. -/
theorem exists_const_mul_le_atomMass {m : BitString → ℝ≥0∞}
    (hm : IsLowerSemicomputableSemimeasure m) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ x, c * m x ≤ atomMass x := by
  obtain ⟨c, hc0, hctop, hc⟩ := exists_const_le_universalContinuousSemimeasure
    (discreteAtomMixture_root_le_one hm.1) (discreteAtomMixture_child_le m)
    (discreteAtomMixture_isLSC hm.2)
  refine ⟨c, hc0, hctop, fun x => ?_⟩
  refine le_atomMass fun k => ?_
  refine le_trans ?_ (hc (tailOnes x k))
  gcongr
  exact le_discreteAtomMixture_tailOnes m x k

/-- **`m x ≤ C · f(x)`.**  The universal discrete semimeasure of a string is, up to one
constant factor, below the mass of the atom of the branch `x01^∞`.

Source: the note `apriori-atoms.md`, section "Почему m(x) ≤ C f(x)"; SUV Chapter 5, §5.2. -/
theorem exists_const_universalSemimeasure_le_atomMass (m : BitString → ℝ≥0∞)
    (hm : IsUniversalSemimeasure m) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ x, m x ≤ C * atomMass x := by
  obtain ⟨c, hc0, hctop, hc⟩ := exists_const_mul_le_atomMass hm.1
  refine ⟨c⁻¹, ENNReal.inv_ne_top.mpr hc0, fun x => ?_⟩
  calc m x = c⁻¹ * (c * m x) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 hctop, one_mul]
    _ ≤ c⁻¹ * atomMass x := by gcongr; exact hc x

end Kolmogorov
