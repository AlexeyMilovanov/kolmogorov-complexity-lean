/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.FiniteGame.Rules
import KolmogorovMathlib.RandomStrings.Plain.FiniteGame.LegalMoves
import KolmogorovMathlib.RandomStrings.Plain.FiniteGame.BoundedSolver
import KolmogorovMathlib.RandomStrings.Plain.FiniteGame.RoleExchange

/-!
# The effective finite counter game

This aggregator imports `FiniteGame/Rules.lean` (the rules and the winning positions of the
finite counter game), `FiniteGame/LegalMoves.lean` (computability of the rules),
`FiniteGame/BoundedSolver.lean` (a computable bounded solver) and `FiniteGame/RoleExchange.lean`
(determinacy and the exchange of the two roles). In the construction, the controlled player of
each phase plays this game against the opponent, which is how the constructed decompressor
forces the cumulative count to differ from the referee's answer; the solver makes the
strategy effective, so `Construction.Effective` can run it inside the machine.

Finite lists represent coordinate vectors and tables. Coordinates are deduplicated
before indexing; missing table entries mean zero and surplus entries are ignored.
The solver enumerates the finite box of move vectors and recurses on the sum of
remaining budgets. All data, positions, winners, and moves have explicit codes in
existing primitive types. No strategy is selected by classical choice.
-/
