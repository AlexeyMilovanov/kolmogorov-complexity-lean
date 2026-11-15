/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.PartialRules.MisesChurchDaley
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.PartialRules.ComplexityLowerBound
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.PartialRules.PartialMartingales

/-!
# Partial selection rules (SUV Section 9.11, pp. 287-290)

A *Church-Daley admissible* rule is `S_r` for a partial computable `r : Σ →. {0, 1}`, with the
hanging semantics of `partialRuleSet`: the set `R` of such a rule is in general not decidable, so
these rules are strictly more general than the Church-admissible ones, and the class of random
sequences is strictly smaller (Theorems 173 and 188).

*Partial martingales* are partial computable rational functions; the fairness equation is required
only where all three values are defined, and winning requires definedness on all prefixes.
-/
