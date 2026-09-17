/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.MonotoneComplexity.Dimension.UniversalAlphaTest
import KolmogorovMathlib.MonotoneComplexity.Omega.Basic.Part01
import KolmogorovMathlib.MonotoneComplexity.Omega.BusyBeaverInfra

/-!
# The coding theorem on `ℕ`, and elementary a priori facts

Facts that SUV Sections 5.7.5–5.7.7 use silently and that are not themselves part of
Section 5.7.  All of them are **proved**.

* `KPNat_ne_top` — relative to an optimal prefix-free machine every natural number *has*
  a description (SUV Section 4.1), so `K(n) ≠ ∞`.  This is what makes the passage
  between `K(n)` and the dyadic weight `2^{-K(n)}` reversible.
* `exists_const_KPNat_aprioriNat_equiv` — **the coding theorem** `K(i) = −log m(i) + O(1)`
  (SUV Theorem 60, recalled on p. 165) in the `ℕ`-indexed form used by Section 5.7.
  It is proved here as the transport along the canonical computable bijection
  `natBitStringEquiv` of the Chapter-4 owner `universalSemimeasure_equiv_prefixComplexity`
  (`AlgorithmicProbability/UniversalSemimeasure.lean`, proved), exactly as
  `exists_isUniversalSemimeasureNat` is the transport of `exists_universalSemimeasure`.
  `Omega/Basic.lean` states the same fact as
  `exists_const_KPNat_aprioriNat_equiv`; the two are interchangeable.
* `apriori_ne_top`, `apriori_pos` — the discrete a priori probability is finite and
  strictly positive (SUV p. 157), the two domain facts every ratio `rᵢ/m(i)` needs.
* `inv_two_pow_antitone`, `ofReal_rat_inv_two_pow` — the dyadic bookkeeping that lets the
  rational series `2^{-f(n)}` of Theorem 113 be compared with `ℝ≥0∞`-valued weights.
-/

namespace Kolmogorov

open scoped ENNReal

/-! ### Finiteness of prefix complexity -/

/-- **SUV Section 4.1, used silently on p. 165.** Relative to an optimal prefix-free
machine every natural number has a description, so its prefix complexity is finite. -/
theorem KPNat_ne_top {U : Map} (hU : IsOptimalPrefixConditional U) (n : ℕ) :
    KPNat U n ≠ ⊤ := by
  obtain ⟨c, hc⟩ := KPPlain_le_two_mul_length U hU
  refine ne_top_of_le_natCast (n := 2 * (natToBitString n).length + c) ?_
  calc KPNat U n = KPPlain U (natToBitString n) := KPNat_def U n
    _ ≤ 2 * ((natToBitString n).length : ENat) + (c : ENat) := hc _
    _ = ((2 * (natToBitString n).length + c : ℕ) : ENat) := by push_cast; ring

/-! ### Dyadic bookkeeping -/

/-- The rational dyadic weight `2^{-k}` read in `ℝ≥0∞`.  This is the bridge between the
rational series `rₙ = 2^{-f(n)}` of SUV Theorem 113 and the `ℝ≥0∞`-valued weights in
which the a priori probability is compared with it. -/
theorem ofReal_rat_inv_two_pow (k : ℕ) :
    ENNReal.ofReal ((((2 : ℚ)⁻¹ ^ k : ℚ) : ℝ)) = (2 : ℝ≥0∞)⁻¹ ^ k := by
  have h : (((2 : ℚ)⁻¹ ^ k : ℚ) : ℝ) = ((2 : ℝ)⁻¹) ^ k := by push_cast; ring
  rw [h, ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_inv_of_pos (by norm_num)]
  norm_num

/-! ### The coding theorem in the `ℕ`-indexed form of SUV Section 5.7 -/

/-! ### The discrete a priori probability is finite and positive -/

/-- The a priori probability of a natural number is finite: it is bounded by the total
mass, which is at most `1`. -/
theorem apriori_ne_top {m : ℕ → ℝ≥0∞} (hm : IsUniversalSemimeasureNat m) (n : ℕ) :
    m n ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (le_trans (ENNReal.le_tsum n) hm.tsum_le_one)

/-- **SUV p. 157.** The a priori probability of a natural number is strictly positive:
by the coding theorem it dominates `2^{-K(n)}`, and `K(n)` is finite. -/
theorem apriori_pos {m : ℕ → ℝ≥0∞} (hm : IsUniversalSemimeasureNat m)
    {U : Map} (hU : IsOptimalPrefixConditional U) (n : ℕ) : 0 < m n := by
  obtain ⟨c₁, c₂, h₁, h₂, hA, hB⟩ := exists_const_KPNat_aprioriNat_equiv hm hU
  refine lt_of_lt_of_le ?_ (hB n)
  exact ENNReal.mul_pos h₂.ne' ((complexityWeight_pos_iff _).2 (KPNat_ne_top hU n)).ne'

end Kolmogorov
