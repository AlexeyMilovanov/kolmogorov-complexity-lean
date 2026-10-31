/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Construction.Effective.StateMachine
import KolmogorovMathlib.RandomStrings.Plain.Construction.Effective.ConstructionTransitions
import KolmogorovMathlib.RandomStrings.Plain.Construction.Effective.GameTransitions
import KolmogorovMathlib.RandomStrings.Plain.Construction.Effective.Allocations
import KolmogorovMathlib.RandomStrings.Plain.Construction.Effective.EventActions
import KolmogorovMathlib.RandomStrings.Plain.Construction.Effective.LiveInvariantSteps
import KolmogorovMathlib.RandomStrings.Plain.Construction.Effective.LiveInvariants

/-!
# The uniformly effective guarded decompressor family

This aggregator imports the `Construction/Effective/` directory, which shows that the
guarded fighter construction (`Construction.State`, `Construction.Actions`,
`Construction.Conditional`) is a computable object, so that the machine `fighterU` built
from it is a partial computable conditional decompressor.

* `StateMachine`: the fighter state machine with its primitive recursive toolbox.
* `ConstructionTransitions`, `CounterGameOperations`, `GameTransitions`: computability of the
  construction operations, of the operations on encoded counter games, and of the game
  transitions (using the solver of `FiniteGame`).
* `Allocations`, `EventActions`: effective allocation and the completeness of the event
  actions along the enumeration of `Plain.Enumeration`.
* `LiveInvariantSteps`, `LiveInvariants`: the live invariant relating the official and the
  live counters of every active phase, and its preservation along the whole run.

Finite states follow the frozen master ticks. The partial directive function searches
for its first successful allocation, and the conditional machine uses the
simulation/directive split. Semantic phase limits below expose the eventual virtual
oracle to the diagonal argument; the executable event process never evaluates those limits.
The live invariant is consumed by `Construction.Stability` and `Construction.Diagonal`.
-/
