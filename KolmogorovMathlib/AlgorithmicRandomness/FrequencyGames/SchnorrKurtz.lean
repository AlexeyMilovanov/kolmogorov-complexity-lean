/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.SchnorrKurtz.Defs
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.SchnorrKurtz.SchnorrSeries
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.SchnorrKurtz.GrowthMartingales
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.SchnorrKurtz.SchnorrMartingaleGrowth
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.SchnorrKurtz.SchnorrNotComputable
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.SchnorrKurtz.KurtzMartingales
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.SchnorrKurtz.RandomnessHierarchy

/-!
# Martingales and Schnorr randomness (SUV Section 9.9, pp. 282-284)

The library has no other Schnorr or Kurtz randomness definitions, so the notions of Section 3.4
that Section 9.9 uses are defined here.  These definitions have been checked against Section 3.4,
printed pp. 69-70 (author's PDF pp. 83-84), as well as Chapter 9:

* `IsSchnorrNull`: covers with sum of masses at most `2^{-n}`, enumerated uniformly in `n`, with
  that sum a computable real uniformly in `n`.  The proof of Theorem 183 builds exactly such
  covers, and Problem 90 of Section 3.4, used there, is `not_isSchnorrRandom_iff_exists_series`.
* `IsKurtzNull`: covers by *finite* lists of intervals, computed uniformly in `n`, with the sum
  of their masses bounded by `2^{-n}` (Section 3.4 and the hint to Problem 272).

Dyadic non-strict bounds are equivalent to the book's strict bounds for every positive rational
`ε`: choose a dyadic bound strictly below `ε`.  Missing intervals in a Schnorr cover are encoded
by `none`.  For finite Kurtz covers, a bound on the measure of the union gives the same notion:
one can computably remove duplicates and intervals contained in other intervals.

The distinction between Theorem 183 and `IsComputablyRandom` is the growth condition: Schnorr's
criterion asks for a computable lower bound on the growth infinitely often, not merely for
unboundedness.
-/
