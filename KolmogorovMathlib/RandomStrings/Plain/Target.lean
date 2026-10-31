/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.HaltingLanguage
import KolmogorovMathlib.RandomStrings.Plain.Main

/-!
# Final separation targets for C-random strings

This module states the final results of the formalization of the separation theorems:
there exists an optimal conditional plain decompressor that separates the halting problem
from its polynomial-time cumulative oracle class (blueprint node `thm:target`) and its
polynomial-time plain-random oracle class (blueprint node `cor:random-target`). It also
records that a single conditional machine witnesses both separations simultaneously
(blueprint node `native:joint`). These statements are fully concrete: the halting language,
the oracle access mechanism (query encoding), the optimality predicate, and the polynomial-time
classes are all explicit.

The theorems here are the top-level results of the formalization. They are fully proved, and
they depend only on the standard axioms `propext`, `Classical.choice` and `Quot.sound`. Each
simply instantiates the existence claim with the native separating machine
`nativeSeparatingMachine`, which is constructed in the imported `Main` module and shown there
to be optimal and to defeat every polynomial-time reduction of the halting language to its
cumulative or plain-random oracle.
-/

namespace Kolmogorov.Milovanov

/-- Some optimal conditional plain machine separates halting from its cumulative oracle class.
Blueprint node `thm:target`. This is definitionally `FormalizationTarget HBin encF`. -/
theorem exists_optimal_halting_not_poly_time_cumulative :
    ∃ U : Map, isOptimalConditional U ∧
      HBin ∉ RandomStrings.PolyTimeOracle (CumulativeOracle encF U) :=
  ⟨nativeSeparatingMachine, native_separating_machine_spec.1,
    native_halting_not_poly_time_cumulative⟩

/-- Some optimal conditional plain machine separates halting from its plain-random oracle class.
Blueprint node `cor:random-target`. -/
theorem exists_optimal_halting_not_poly_time_random :
    ∃ U : Map, isOptimalConditional U ∧
      HBin ∉ RandomStrings.PolyTimeOracle (PlainRandomOracle U) :=
  ⟨nativeSeparatingMachine, native_separating_machine_spec.1,
    native_halting_not_poly_time_random⟩

/-- One optimal conditional plain machine witnesses both oracle-class separations.
Blueprint node `native:joint`. -/
theorem exists_optimal_native_halting_oracle_separation :
    ∃ U : Map, isOptimalConditional U ∧
      HBin ∉ RandomStrings.PolyTimeOracle (CumulativeOracle encF U) ∧
      HBin ∉ RandomStrings.PolyTimeOracle (PlainRandomOracle U) :=
  ⟨nativeSeparatingMachine, native_separating_machine_spec.1,
    native_halting_not_poly_time_cumulative, native_halting_not_poly_time_random⟩

end Kolmogorov.Milovanov
