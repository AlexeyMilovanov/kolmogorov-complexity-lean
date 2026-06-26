/-
Copyright (c) 2024 Alexey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey
-/
import KolmogorovMathlib.Prefix.Kraft
import KolmogorovMathlib.AlgorithmicProbability.Normalization

/-!
# Countable Kraft Inequality and A Priori Semimeasure Normalization

This module performs the final lift in the prefix-machine normalization chain. Two
earlier slots prepared the ground:

* `Prefix/Kraft.lean` proved the **finite** Kraft inequality
  `finset_kraft_progWeight_le_one`: the total `progWeight` of any prefix-free
  *finite* set of bitstrings is at most `1`.
* `AlgorithmicProbability/Normalization.lean` reduced the semimeasure normalization
  goal `∑_x m_M(x | y) ≤ 1` to the single domain-weight bound
  `domainWeight M y ≤ 1`, packaged as
  `tsum_aprioriMeasure_le_one_of_domainWeight_le_one`.

Here we close the gap. The domain weight is a `tsum` of an indicator series; by
`ENNReal.tsum_eq_iSup_sum` it is the supremum of its finite partial sums. Each
finite partial sum ranges over an *arbitrary* finite set `s`, which need not be
prefix-free — but only the programs in `s` that actually halt contribute, and the
halting domain is prefix-free for a prefix machine. Filtering `s` down to that
sub-collection (`IsPrefixFree.mono`) and applying the finite Kraft bound gives a
uniform `≤ 1` on every partial sum, hence on the supremum. Feeding the resulting
`domainWeight M y ≤ 1` into the normalization reduction yields the headline
theorem `tsum_aprioriMeasure_le_one`.

Everything stays in `ℝ≥0∞`: no logarithms, no real numbers beyond the finite Kraft
bridge, and the conclusion is an inequality `≤ 1`, never an equality.
-/

namespace Kolmogorov

open scoped ENNReal

open Classical in
/-- **Finite partial sums of the domain-weight series are bounded by `1`.** For a
prefix machine `M`, any finite partial sum of the indicator series defining
`domainWeight M y` is at most `1`. The arbitrary finite set `s` is filtered down to
the programs in `s` that halt in context `y`; that filtered set is a finite subset
of the prefix-free halting domain (`IsPrefixFree.mono`), so the finite Kraft
inequality `finset_kraft_progWeight_le_one` applies. The non-halting terms of the
original sum are `0`, so the filter does not change the value. -/
theorem domainWeight_finset_sum_le_one (M : Map) (y : BitString)
    (hM : IsPrefixMachine M) (s : Finset BitString) :
    ∑ p ∈ s, (if p ∈ domainAt M y then progWeight p else 0) ≤ 1 := by
  classical
  -- Drop the indicator: only the halting programs in `s` contribute.
  have hsum :
      ∑ p ∈ s, (if p ∈ domainAt M y then progWeight p else 0)
        = ∑ p ∈ s.filter (fun p => p ∈ domainAt M y), progWeight p := by
    rw [Finset.sum_filter]
  rw [hsum]
  -- The filtered finset is a finite subset of the prefix-free halting domain.
  have hsub : (↑(s.filter (fun p => p ∈ domainAt M y)) : Set BitString)
      ⊆ domainAt M y := by
    intro p hp
    rw [Finset.coe_filter, Set.mem_setOf_eq] at hp
    exact hp.2
  have hPF : IsPrefixFree (↑(s.filter (fun p => p ∈ domainAt M y)) : Set BitString) :=
    (hM y).mono hsub
  exact finset_kraft_progWeight_le_one _ hPF

/-- **Countable Kraft inequality.** For a prefix machine `M`, the total weight of
its halting domain in any context `y` is at most `1`. This is the lift of the finite
Kraft inequality to the countable `tsum`: `domainWeight` is the supremum of its
finite partial sums (`ENNReal.tsum_eq_iSup_sum`), and every partial sum is bounded
by `1` via `domainWeight_finset_sum_le_one`. -/
theorem domainWeight_le_one (M : Map) (y : BitString) (hM : IsPrefixMachine M) :
    domainWeight M y ≤ 1 := by
  rw [domainWeight, ENNReal.tsum_eq_iSup_sum]
  exact iSup_le fun s => domainWeight_finset_sum_le_one M y hM s

/-- **A priori semimeasure normalization.** For a prefix machine `M`, the conditional
a priori semimeasure is normalized: the total mass over all outputs `x` is at most
`1`. This is the headline milestone of the prefix-machine layer; it follows in one
step by feeding the countable Kraft bound `domainWeight_le_one` into the
normalization reduction `tsum_aprioriMeasure_le_one_of_domainWeight_le_one`. -/
theorem tsum_aprioriMeasure_le_one (M : Map) (y : BitString)
    (hM : IsPrefixMachine M) :
    (∑' x : BitString, aprioriMeasure M x y) ≤ 1 :=
  tsum_aprioriMeasure_le_one_of_domainWeight_le_one M y (domainWeight_le_one M y hM)

end Kolmogorov
