/-
Copyright (c) 2026 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Restricted.FamilyCurve
import KolmogorovMathlib.Restricted.Examples.HammingBalls

/-!
# Curve realization for Hamming balls

The restricted-profile curve realization theorem (VS40 §6, `prop_family_curve`)
instantiated at the concrete Hamming-ball description family: every admissible
strictly decreasing curve `t` on `[0, k]` is realized, within square-root
slack, by the Hamming-ball restricted profile of some word of length
`n + O(log n)` and plain complexity `≤ k + O(√(n log n))`.
-/

namespace Kolmogorov

/-- Curve realization for the Hamming-ball description family. -/
theorem prop_hamming_curve (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c_curve : ℕ, ∀ (n k : ℕ) (t : ℕ → ℕ),
      k ≤ n →
      t 0 ≤ n →
      t k = 0 →
      (∀ i : ℕ, i < k → t (i + 1) < t i) →
      ∃ x : BitString, ∃ n' : ℕ,
        x.length = n' ∧
        n ≤ n' ∧ n' ≤ n + logSlack c_curve n ∧
        KPPlain U x ≤ (k + sqrtSlack c_curve n : ENat) ∧
        RestrictedProfileWithinCurve hammingFamily U x k t
          (sqrtSlack c_curve n) :=
  prop_family_curve U hU hammingFamily hammingFamily_hasPolynomialOverhead

end Kolmogorov
