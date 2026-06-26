/-
Copyright (c) 2024 Alexey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey
-/
import KolmogorovMathlib.AlgorithmicProbability.UniversalSemimeasure.Enumeration.Computability

namespace Kolmogorov

open scoped ENNReal

/-! ### The Hard Theorem -/

/-! #### Canonical dyadic weights

The weights used in the universal mixture are the canonical strictly-positive
dyadic weights `dyadicWeight i = 2^{-(i+1)}` (defined in `UniversalMixture`),
whose total mass is exactly `1`. These weights supply the geometric-series algebra
(`tsum_dyadicWeight`, `dyadicWeight_pos`) used to assemble the universal mixture
from the dovetailed enumeration `approxEnum`. -/

/-- **The hard SUV enumeration/sanitization core (family only).**
...
-/
theorem exists_lsc_semimeasure_family :
    ∃ μ : ℕ → BitString → ℝ≥0∞,
      (∀ i, IsSemimeasure (μ i)) ∧
      IsLowerSemicomputableSemimeasure (unaryMixture dyadicWeight μ) ∧
      ∀ m' : BitString → ℝ≥0∞, IsLowerSemicomputableSemimeasure m' →
        ∃ (i : ℕ) (c : ℝ≥0∞), 0 < c ∧ DominatesUnary (μ i) m' c := by
  refine ⟨fun i x => lscEnum i x [], ?_, ?_, ?_⟩
  · intro i; exact lscEnum_isSemimeasure i
  · exact unaryMixture_dyadicWeight_lscEnum_isLowerSemicomputable
  · intro m' hm'
    obtain ⟨hm'_semi, hm'_lsc⟩ := hm'
    obtain ⟨approx, hmono, hsup, hcomp⟩ := hm'_lsc
    obtain ⟨i, hi⟩ := exists_approxEnum approx hcomp
    refine ⟨i, 1, by norm_num, fun x => ?_⟩
    rw [one_mul]
    have hmono_i : ∀ s out ctx, dyadicValue (makeMono (approxEnum i) s out ctx) s
        ≤ dyadicValue (makeMono (approxEnum i) (s + 1) out ctx) (s + 1) :=
      makeMono_mono (approxEnum i)
    have hsup_i : ∀ out ctx, ⨆ s, dyadicValue (makeMono (approxEnum i) s out ctx) s =
        (⨆ s, dyadicValue (makeMono (approxEnum i) s out ctx) s) := fun _ _ => rfl
    have hle_i : (∑' out, ⨆ s, dyadicValue (makeMono (approxEnum i) s out []) s) ≤ (2 : ℝ≥0∞) ^ 0 := by
      rw [pow_zero]
      calc
        (∑' out, ⨆ s, dyadicValue (makeMono (approxEnum i) s out []) s)
          = ∑' out, ⨆ s, dyadicValue (approxEnum i s out []) s := by
            congr 1
            ext out
            exact iSup_makeMono_eq_iSup (approxEnum i) out []
        _ = ∑' out, ⨆ s, dyadicValue (approx s out []) s := by
            congr 1
            ext out
            exact hi out []
        _ = ∑' out, m' out := by
            congr 1
            ext out
            exact hsup out []
        _ ≤ 1 := hm'_semi
    have h_trunc := truncG_eq_f_of_le (approx := makeMono (approxEnum i)) (f := fun out ctx => ⨆ s, dyadicValue (makeMono (approxEnum i) s out ctx) s) hmono_i hsup_i 0 [] hle_i x
    have h_lsc : lscEnum i x [] = truncG (makeMono (approxEnum i)) 0 x [] := rfl
    change m' x ≤ lscEnum i x []
    rw [h_lsc, h_trunc, iSup_makeMono_eq_iSup, hi x []]
    exact (hsup x []).symm.le

/-- Existence of the canonically-weighted sanitized enumeration. The weights are
the canonical dyadic weights `dyadicWeight`, whose positivity and subnormalization
are proved (`dyadicWeight_pos`, `tsum_dyadicWeight_le_one`); the family is the one
from `exists_lsc_semimeasure_family`. -/
theorem exists_lsc_semimeasure_enumeration :
    ∃ (w : ℕ → ℝ≥0∞) (μ : ℕ → BitString → ℝ≥0∞),
      (∑' i, w i) ≤ 1 ∧ (∀ i, 0 < w i) ∧ (∀ i, IsSemimeasure (μ i)) ∧
      IsLowerSemicomputableSemimeasure (unaryMixture w μ) ∧
      ∀ m' : BitString → ℝ≥0∞, IsLowerSemicomputableSemimeasure m' →
        ∃ (i : ℕ) (c : ℝ≥0∞), 0 < c ∧ DominatesUnary (μ i) m' c := by
  obtain ⟨μ, hsemi, hlsc, hdom⟩ := exists_lsc_semimeasure_family
  exact ⟨dyadicWeight, μ, tsum_dyadicWeight.le, dyadicWeight_pos, hsemi, hlsc, hdom⟩

/-- Existence of a universal lower-semicomputable semimeasure.

The maximal semimeasure is the dyadically weighted mixture of the sanitized
enumeration provided by `exists_lsc_semimeasure_enumeration`. Universality is then
pure mixture algebra: the mixture dominates each component `μ i` by its weight
`w i`, each component dominates an arbitrary l.s.c. semimeasure by a positive
constant, and unary domination composes transitively. -/
theorem exists_universalSemimeasure :
    ∃ m : BitString → ℝ≥0∞, IsUniversalSemimeasure m := by
  obtain ⟨w, μ, _hw_sum, hw_pos, _hμ, hlsc, hdom⟩ := exists_lsc_semimeasure_enumeration
  refine ⟨unaryMixture w μ, hlsc, fun m' hm' => ?_⟩
  obtain ⟨i, c, hc_pos, hci⟩ := hdom m' hm'
  refine ⟨w i * c, ENNReal.mul_pos (hw_pos i).ne' hc_pos.ne', ?_⟩
  exact (unaryMixture_dominates_component w μ i).trans hci

end Kolmogorov
