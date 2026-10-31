/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Construction.Accounting.TargetRange
import KolmogorovMathlib.RandomStrings.Plain.Construction.Accounting.DummyHistory
import KolmogorovMathlib.RandomStrings.Plain.Construction.Accounting.DummyIdentities
import KolmogorovMathlib.RandomStrings.Plain.Construction.Accounting.FuelHistory
import KolmogorovMathlib.RandomStrings.Plain.Construction.Accounting.PhaseCountBounds
import KolmogorovMathlib.RandomStrings.Plain.Construction.Accounting.LevelRanges
import KolmogorovMathlib.RandomStrings.Plain.Construction.Accounting.EarlierTargets
import KolmogorovMathlib.RandomStrings.Plain.Construction.Accounting.CapacityFailure
import KolmogorovMathlib.RandomStrings.Plain.Construction.Accounting.OutputSet
import KolmogorovMathlib.RandomStrings.Plain.Construction.Accounting.UniformRank

/-!
# Accounting for the fighter construction

This aggregator imports the `Construction/Accounting/` directory, which counts what the
effective fighter family (`Construction.Effective`) does. The diagonal argument needs two
kinds of bounds: the construction must issue few directives (so that the constructed
decompressor is optimal and its sets of short outputs are small), and the targets reserved
for different levels and different kinds of directive must not collide.

* `TargetRange`, `PhaseCountBounds`, `FuelHistory`: the number of phases started at each
  level and the fuel they receive (blueprint nodes `constr:intervals`, `constr:phasecount`).
* `DummyHistory`, `DummyIdentities`: provenance, uniqueness and preservation of the dummy
  allocations.
* `LevelRanges`, `EarlierTargets`: disjointness of the target ranges of different levels and
  the saturation of the input pools of earlier levels.
* `CapacityFailure`, `OutputSet`: counting allocations at a failed target, and the description
  capacity of the payoff directives.
* `UniformRank`: exponentially bounded output sets of the constructed machine
  (`constructed_machine_exponential_output_bound`) and their uniform rank codes
  (`constructed_machine_uniform_rank_code`), which give the description bounds used when the
  padding constant is chosen in `Construction.Stability`.

These bounds concern all candidates. In particular the sparse-output and rank-code
statements concern the entire guarded family, without assuming that allocation never
fails. No theorem here assumes true-marker realization or later priority stability.
-/
