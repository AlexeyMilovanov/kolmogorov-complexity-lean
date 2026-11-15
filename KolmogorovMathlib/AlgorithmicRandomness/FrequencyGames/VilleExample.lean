/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.VilleExample.CountableFamilies
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.VilleExample.MisesChurchExample
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.VilleExample.LogarithmicComplexity
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.VilleExample.EffectivelyNullSet

/-!
# Ville's example (SUV Section 9.4, pp. 267-270)

The Wald-Ville-Loveland construction of a sequence that is finite-or-balanced under a given
countable family of rules, with every prefix having at least as many zeros as ones.  The stages of
the construction are stated separately (one rule, `m` rules, countably many rules), since each is
used later.  Applied to all decidable sets it gives Theorem 172; run with advice it gives the
logarithmic prefix complexity of Theorem 173, and hence Theorem 174.
-/
