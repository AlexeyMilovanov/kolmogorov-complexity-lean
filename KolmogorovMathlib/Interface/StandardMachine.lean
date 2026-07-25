/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/

import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.PaperTheorems
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.CurveRealization
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.ProfileRealization

/-!
# The standard machine bundle

Leaf lemmas throughout the library are stated against minimal hypotheses
(`(U : Map) (hU : IsOptimalPrefixConditional U)`, plus per-theorem gates such
as `SingletonSetComplexityGate`). As the paper-facing layer grows, threading
this tuple by hand through every statement stops scaling.

`StandardMachine` bundles the machine together with its optimality proof; the
standard gates are *derived* (they are theorems of optimality, see
`CurveRealization.singletonSetComplexityGate` / `fullSetComplexityGate`), so a
bundle needs no extra fields. The paper-facing results are re-exported below
as dot-notation wrappers, with all gate hypotheses discharged.

Convention going forward: **new leaf lemmas keep minimal hypotheses; new
paper-facing statements are added here as `StandardMachine` wrappers.**
-/

namespace Kolmogorov

/-- An optimal prefix-conditional decompressor, bundled with its optimality
proof. Paper-facing theorems are stated against this bundle. -/
structure StandardMachine where
  U : Map
  optimal : IsOptimalPrefixConditional U

/-- The canonical standard machine, obtained from the existence theorem. -/
noncomputable def StandardMachine.default : StandardMachine :=
  ⟨Classical.choose exists_isOptimalPrefixConditional,
   Classical.choose_spec exists_isOptimalPrefixConditional⟩

namespace StandardMachine

variable (M : StandardMachine)

/-! ### Derived gates -/

/-- Gate B1, discharged: singleton set complexity is bounded by plain prefix
complexity up to logarithmic slack. -/
theorem singletonGate : SingletonSetComplexityGate M.U :=
  singletonSetComplexityGate M.U M.optimal

/-- Gate B2, discharged: the full length-`n` cube has set complexity `O(log n)`. -/
theorem fullGate : FullSetComplexityGate M.U :=
  fullSetComplexityGate M.U M.optimal

/-! ### Symmetry of information -/

/-- Staged symmetry of information for pairs:
`K(x,y) = K(x) + K(y | x, K(x)) + O(1)`. -/
theorem symmetryOfInformation :
    ∃ cUpper : Nat, ∃ cLower : Nat,
      ∀ x y : BitString, ∀ kx : Nat,
        HasPrefixComplexityValue M.U x kx →
          KPPair M.U x y
              ≤ KPPlain M.U x + KP M.U y (prefixComplexityContext x kx) + (cUpper : ENat) ∧
          KPPlain M.U x + KP M.U y (prefixComplexityContext x kx)
              ≤ KPPair M.U x y + (cLower : ENat) :=
  KPPair_symmetryOfInformation_staged M.U M.optimal

/-- Conditional staged symmetry of information:
`K(x,y | z) = K(x | z) + K(y | z, x, K(x|z)) + O(1)`. -/
theorem condSymmetryOfInformation :
    ∃ cUpper : Nat, ∃ cLower : Nat,
      ∀ x y z : BitString, ∀ kx : Nat,
        HasCondPrefixComplexityValue M.U x z kx →
          KPCondPair M.U x y z
              ≤ KP M.U x z + KP M.U y (prefixCondComplexityContext z x kx) + (cUpper : ENat) ∧
          KP M.U x z + KP M.U y (prefixCondComplexityContext z x kx)
              ≤ KPCondPair M.U x y z + (cLower : ENat) :=
  KPCondPair_symmetryOfInformation_staged M.U M.optimal

/-! ### Section-3 paper theorems -/

/-- Two-part code upper bound: an `(i,j)`-description gives
`K(x) ≤ i + j + O(log(n+i+j))`. -/
theorem twoPart_upper :
    ∃ c : ℕ, ∀ (x : BitString) (n i j : ℕ),
      x.length = n →
      InDescriptionProfile M.U x i j →
      KPPlain M.U x ≤ (i + j + logSlack c (n + i + j) : ENat) :=
  KPPlain_le_of_inDescriptionProfile M.U M.optimal

/-- Improving Descriptions, complexity half: `≥ 2^k` many `(i,j)`-descriptions
yield an `(i−k, j)`-description up to `O(log)` slack. -/
theorem improvingDescriptions_complexity :
    ∃ c : ℕ, ∀ x n i j k,
      x.length = n →
      ManyIJDescriptions M.U x i j k →
      k ≤ i →
      InDescriptionProfile M.U x (i - k + logSlack c (n + i + j)) (j + logSlack c (n + i + j)) :=
  improving_descriptions_complexity_thm M.U M.optimal

/-- Improving Descriptions, size half: `≥ 2^k` many `(i,j)`-descriptions yield
an `(i, j−k)`-description up to `O(log)` slack. -/
theorem improvingDescriptions_size :
    ∃ c : ℕ, ∀ x n i j k,
      x.length = n →
      ManyIJDescriptions M.U x i j k →
      k ≤ j →
      InDescriptionProfile M.U x (i + logSlack c (n + i + j)) (j - k + logSlack c (n + i + j)) :=
  improving_descriptions_size_thm M.U M.optimal

/-- The Deficiencies Theorem (tight version). -/
theorem deficiencies_tight :
    ∃ c : ℕ, ∀ (A : Finset BitString) (hA : A.Nonempty) (x : BitString)
        (n delta d i j kx c_soi : ℕ),
      x.length = n →
      RealizedSetOptimalityGap M.U A hA x delta i j kx →
      CodedFiniteDistribution.DeficiencyLe M.U (codedUniformOn A hA) x d →
      d ≤ delta + c_soi →
      ∃ (B : Finset BitString) (hB : B.Nonempty), x ∈ B ∧
        setComplexity M.U B hB + (delta - d : ℕ) ≤
          setComplexity M.U A hA + (logSlack c (n + delta + d) : ENat) ∧
        SetOptimalityDeficiencyLe M.U B hB x (d + logSlack c (n + delta + d)) :=
  deficiencies_theorem_tight_thm M.U M.optimal

/-- Optimal set stochasticity yields an explicit description profile point. -/
theorem optimalStochastic_imp_profile :
    ∃ c : ℕ, ∀ (x : BitString) (alpha beta j : ℕ),
      IsOptimalSetStochastic M.U x alpha beta →
      KPPlain M.U x + beta ≤ (alpha : ENat) + j →
      InDescriptionProfile M.U x (alpha + logSlack c (alpha + beta + j)) (j + 1) :=
  optimal_stochasticity_imp_profile_thm M.U M.optimal

/-- Theorem 3 direction: any stochasticity witness converts into an optimal
uniform-set witness up to `O(log)` slack. -/
theorem stochastic_to_optimalSet :
    ∃ c : ℕ, ∀ x : BitString, ∀ n alpha beta : ℕ,
      x.length = n →
      IsStochastic M.U x alpha beta →
      IsOptimalSetStochastic M.U x (alpha + logSlack c (n + alpha + beta))
        (beta + logSlack c (n + alpha + beta)) :=
  stochasticity_to_optimal_set_thm M.U M.optimal

/-! ### Structure function -/

/-- Corrected Section-3 admissibility of the structure function, with both
set-complexity gates discharged from optimality. -/
theorem structureFunction_admissible :
    ∃ c : ℕ, ∀ (x : BitString) (n kx : ℕ), x.length = n → KPPlain M.U x = (kx : ENat) →
      Antitone (structureFunction M.U x) ∧
      structureFunction M.U x (logSlack c n) ≤ (n : ℕ∞) ∧
      structureFunction M.U x (kx + logSlack c n) = 0 ∧
      (∀ i j : ℕ, structureFunction M.U x i ≤ (j : ℕ∞) →
        kx ≤ i + j + logSlack c (n + i + j)) :=
  _root_.Kolmogorov.structureFunction_admissible M.U M.optimal M.singletonGate M.fullGate

/-- Profile realization (`stat-any-curve`): every admissible `ProfileCurve` is
realized by a length-`n` string up to `O(log n)` slack, in both halves. -/
theorem realize_curve :
    ∃ c_real : ℕ, ∀ (c n kx m : ℕ) (h : ℕ → ℕ), ProfileCurve M.U c n kx m h →
      ∃ x : BitString, x.length = n ∧
        (∀ i, InDescriptionProfile M.U x (i + m + logSlack c_real n) (h i + logSlack c_real n)) ∧
        (∀ i, ¬ InDescriptionProfile M.U x i (h i - (m + logSlack c_real n)) ∨
          h i ≤ m + logSlack c_real n) :=
  exists_string_with_profile M.U M.optimal

end StandardMachine

end Kolmogorov
