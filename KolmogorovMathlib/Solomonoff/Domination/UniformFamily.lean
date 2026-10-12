import KolmogorovMathlib.Solomonoff.Domination

/-!
# Domination of uniform prefix-free families

`exists_const_two_pow_KPNat_mul_le_universal_of_uniform_prefixFree`: let `ν e` be tree masses,
lower semicomputable uniformly in the index `e`, each of mass at most one on every finite
prefix-free set of strings. Then one constant `C`, fixed before the index, gives
`2^{-(K(e)+C)} · ν e x ≤ M(x)` for every index `e` and every string `x`, where `K(e) = KPNat U e`
for the optimal prefix decompressor `U` and `M = universalContinuousSemimeasure`.

The members of the family need not be continuous tree semimeasures: the hypothesis bounds only
their mass on finite prefix-free sets, with no root normalization and no tree inequality. This is
the generic form of `exists_const_two_pow_KPNat_mul_cantorMass_le_universal`, whose components
are the cylinder masses of computable probability measures.

### Proof

The mixture `R(x) = ∑' e, 2^{-K(e)} · ν e x` is lower semicomputable: the weights `2^{-K(e)}`
form a uniform family (`isUniformlyLSC_complexityWeight_KPNat`), products of uniform families are
uniform (`IsUniformlyLowerSemicomputableTreeFamily.mul`), and countable sums of uniform families
are lower semicomputable (`isLSC_tsum_of_uniform`). Its mass on a finite prefix-free set is at
most the Kraft sum `∑' e, 2^{-K(e)} ≤ 1` (`sum_tsum_complexityWeight_KPNat_mul_le_one`). The
prefix-free envelope `exists_lsc_continuousTreeSemimeasure_dominating_prefixFree` dominates `R`
by a lower semicomputable continuous semimeasure `ξ`, and maximality of `M`, applied once to `ξ`,
yields the constant (`exists_const_of_KPNat_weighted_continuousSemimeasure`).
-/

namespace Kolmogorov

open scoped ENNReal

/-- **The prefix-free budget survives the complexity-weighted mixture.** If every member of the
family `ν` has mass at most one on each finite prefix-free set of strings, then so has the
mixture `x ↦ ∑' e, 2^{-K(e)} · ν e x`, where `K(e) = KPNat U e`, by Kraft's inequality
`∑' e, 2^{-K(e)} ≤ 1` (`tsum_complexityWeight_KPNat_le_one`). -/
theorem sum_tsum_complexityWeight_KPNat_mul_le_one (U : Map) (hU : IsOptimalPrefixConditional U)
    {ν : ℕ → BitString → ℝ≥0∞}
    (hfree : ∀ (e : ℕ) (S : Finset BitString), IsPrefixFree (S : Set BitString) →
      ∑ x ∈ S, ν e x ≤ 1)
    (S : Finset BitString) (hS : IsPrefixFree (S : Set BitString)) :
    ∑ x ∈ S, ∑' e, complexityWeight (KPNat U e) * ν e x ≤ 1 := by
  calc
    ∑ x ∈ S, ∑' e, complexityWeight (KPNat U e) * ν e x
        = ∑' e, ∑ x ∈ S, complexityWeight (KPNat U e) * ν e x :=
      (Summable.tsum_finsetSum fun _ _ => ENNReal.summable).symm
    _ = ∑' e, complexityWeight (KPNat U e) * ∑ x ∈ S, ν e x := by
      simp_rw [Finset.mul_sum]
    _ ≤ ∑' e, complexityWeight (KPNat U e) :=
      ENNReal.tsum_le_tsum fun e => mul_le_of_le_one_right' (hfree e S hS)
    _ ≤ 1 := tsum_complexityWeight_KPNat_le_one U hU

/-- **Domination of a uniform prefix-free family through its index.** Let `ν e` be tree masses,
lower semicomputable uniformly in the index `e`, each of mass at most one on every finite
prefix-free set of strings. There is a constant `C`, quantified before the index, such that
`2^{-(K(e)+C)} · ν e x ≤ M(x)` for every index `e` and every string `x`, where `K(e) = KPNat U e`
and `M = universalContinuousSemimeasure`. -/
theorem exists_const_two_pow_KPNat_mul_le_universal_of_uniform_prefixFree (U : Map)
    (hU : IsOptimalPrefixConditional U) (ν : ℕ → BitString → ℝ≥0∞)
    (hν : IsUniformlyLowerSemicomputableTreeFamily ν)
    (hfree : ∀ (e : ℕ) (S : Finset BitString), IsPrefixFree (S : Set BitString) →
      ∑ x ∈ S, ν e x ≤ 1) :
    ∃ C : ℕ, ∀ (e : ℕ) (x : BitString),
      (2 : ℝ≥0∞)⁻¹ ^ ((KPNat U e).toNat + C) * ν e x ≤ universalContinuousSemimeasure x := by
  obtain ⟨ξ, hξ, hRξ⟩ := exists_lsc_continuousTreeSemimeasure_dominating_prefixFree
    (fun x => ∑' e, complexityWeight (KPNat U e) * ν e x)
    (isLSC_tsum_of_uniform ((isUniformlyLSC_complexityWeight_KPNat U hU).mul hν))
    (sum_tsum_complexityWeight_KPNat_mul_le_one U hU hfree)
  exact exists_const_of_KPNat_weighted_continuousSemimeasure U hU ν ξ hξ fun e x =>
    (ENNReal.le_tsum (f := fun e => complexityWeight (KPNat U e) * ν e x) e).trans (hRξ x)

end Kolmogorov
