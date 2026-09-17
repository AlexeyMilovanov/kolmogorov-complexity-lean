/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Foundation.EffectiveNotions
import KolmogorovMathlib.Interface.Dovetailing
import KolmogorovMathlib.Foundation.PrimrecExtras
import Mathlib.Data.Nat.Dist
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Computability.Reduce
import KolmogorovMathlib.Complexity.Uncomputability
import KolmogorovMathlib.AlgorithmicStatistics.Selector
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.ModelsToSets2
import KolmogorovMathlib.CommonInformation.Counting
import KolmogorovMathlib.Complexity.Properties
import Mathlib.Computability.PartrecCode
import KolmogorovMathlib.Complexity.Incompressibility
import KolmogorovMathlib.Foundation.FixedPointFree.ArslanovCompleteness
import KolmogorovMathlib.Foundation.FixedPointFree

/-!
# Arslanov's completeness criterion, complexity form

`arslanov_solvesHighComplexity_iff_halting` states the criterion in the form used in this
development: an enumerable oracle solves the task "given `n`, produce an object of plain
complexity at least `n`" exactly when it computes the halting problem. The two directions are
supplied by the fixed-point-free material this module gathers.

Source: SUV, Exercise 15.
-/

namespace Kolmogorov
open Nat.Partrec (Code)
open Kolmogorov.CodedFiniteDistribution
open Nat.Partrec (Code)

/-- **Exercise 15 (Arslanov completeness criterion).** An enumerable oracle solves
the high-complexity task if and only if it solves the halting problem. -/
theorem arslanov_solvesHighComplexity_iff_halting (U : Map) (hU : isOptimalConditional U)
    (A : Set ℕ) (hA : IsEnumerableSet A) :
    (∃ g : ℕ → ℕ, SolvesHighComplexity U g ∧
        RecursiveIn {charOracle A} (totalOracle g)) ↔
      RecursiveIn {charOracle A}
        (charOracle {e | ((Denumerable.ofNat Code e).eval e).Dom}) := by
  constructor
  · rintro ⟨g, hg, hgA⟩
    obtain ⟨h, hh, hhg⟩ := solvesDiagonal_of_solvesHighComplexity U hU g hg
    refine arslanov_completeness A hA h hh
      (recursiveIn_of_forall_oracle_recursiveIn hhg ?_)
    rintro f hf
    rw [Set.mem_singleton_iff] at hf
    subst hf
    exact hgA
  · intro hK
    obtain ⟨g, hg, hgK⟩ := solvesHighComplexity_recursiveIn_halting U hU
    refine ⟨g, hg, recursiveIn_of_forall_oracle_recursiveIn hgK ?_⟩
    rintro f hf
    rw [Set.mem_singleton_iff] at hf
    subst hf
    exact hK

end Kolmogorov
