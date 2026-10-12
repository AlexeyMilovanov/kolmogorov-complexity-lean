/-
Copyright (c) 2026 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.MonotoneComplexity.PlainMonotoneComparison
import KolmogorovMathlib.Solomonoff.SelectedBits.Assembly

/-!
# Solomonoff prediction of selected bits: the headline statements

The linear description-length bound for the normalized Solomonoff predictor at the forced
positions of a computable prefix tree, answering the question of slide 14 of
Bauwens–Kuznetsov, *Solomonoff induction of selected bits* (26 August 2026): for a fixed
exponent `γ > 1`, the γ-power loss over the forced positions of any branch of a tree decided
by a program of length `k` is `O(k)`, improving the exponential bound `O(2^{γ k} log^{2γ} k)`
of Kuznetsov's thesis to the polynomial, indeed linear, order.

* `square_loss_le_index_complexity`: for `γ = 2` the loss is at most `KPNat U e + C`, where
  `e` is any index deciding the tree and `U` the fixed optimal prefix machine.
* `power_loss_le_index_complexity`: for every real `γ > 1` the loss is at most
  `A (KPNat U e + C)`, with `A` and `C` fixed before the tree, the index and the branch.
* `power_loss_summable_le_index_complexity`: the series over all forced positions is summable
  with the same bound.
* `treeComplexity_ne_top` and `power_loss_le_treeComplexity`: the same bound in terms of the
  prefix complexity `treeComplexity U T` of a computable prefix tree.

The index `e` plays the role of the tree program: `KPNat U e` is the length of a shortest
self-delimiting description of `e`, and a program of `k` bits deciding `T` yields an index of
prefix complexity `k + O(log k)`.  Every constant is quantified after the optimal prefix
machine `U` and the exponent `γ`, and before all instance data.  The universal tree semimeasure
is the canonical `universalContinuousSemimeasure` of the library.
-/

namespace Kolmogorov.SelectedBits

open scoped ENNReal

/-- **Square loss.**  For the optimal prefix machine `U` there is a constant `C` such that for
every prefix tree `T` decided by the index `e`, every branch `ω` of `T` and every `n`, the sum
of the squared normalized errors at the forced positions `i < n` is at most
`KPNat U e + C`. -/
theorem square_loss_le_index_complexity (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ C : ℕ, ∀ (T : Set BitString) (e : ℕ) (ω : CantorSeq) (n : ℕ),
      DecidesTree e T → Branch T ω →
        partialPowerLoss universalContinuousSemimeasure T ω 2 n ≤
          ((KPNat U e).toNat : ℝ) + C := by
  obtain ⟨C, hC⟩ := kappa_mul_partialPowerLoss_le_index_complexity squareGainFamily U hU
  refine ⟨C, fun T e ω n hdec hω => ?_⟩
  have h := hC T e ω n hdec hω
  rw [squareGainFamily_kappa, squareGainFamily_beta] at h
  exact le_of_mul_le_mul_left h (Real.log_pos one_lt_two)

/-- **Linear bound for every exponent `γ > 1`.**  For the optimal prefix machine `U` and a real
`γ > 1` there are constants `A` and `C` such that for every prefix tree `T` decided by the
index `e`, every branch `ω` of `T` and every `n`, the γ-power loss at the forced positions
`i < n` is at most `A (KPNat U e + C)`. -/
theorem power_loss_le_index_complexity (U : Map) (hU : IsOptimalPrefixConditional U) (γ : ℝ)
    (hγ : 1 < γ) :
    ∃ A C : ℕ, ∀ (T : Set BitString) (e : ℕ) (ω : CantorSeq) (n : ℕ),
      DecidesTree e T → Branch T ω →
        partialPowerLoss universalContinuousSemimeasure T ω γ n ≤
          A * (((KPNat U e).toNat : ℝ) + C) := by
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.mpr hγ)
  obtain ⟨C, hC⟩ := staircase_partialPowerLoss_le U hU (k + 1) k.succ_pos
  refine ⟨2 ^ (k + 1 + 1), C, fun T e ω n hdec hω => ?_⟩
  have hβ : 1 + 1 / ((k + 1 : ℕ) : ℝ) ≤ γ := by
    push_cast
    linarith
  calc partialPowerLoss universalContinuousSemimeasure T ω γ n
      ≤ partialPowerLoss universalContinuousSemimeasure T ω (1 + 1 / ((k + 1 : ℕ) : ℝ)) n :=
        partialPowerLoss_le_of_le_exponent _ T ω (by positivity) hβ n
    _ ≤ 2 ^ (k + 1 + 1) * (((KPNat U e).toNat : ℝ) + C) := hC T e ω n hdec hω
    _ = ((2 ^ (k + 1 + 1) : ℕ) : ℝ) * (((KPNat U e).toNat : ℝ) + C) := by push_cast; rfl

/-- **The whole series.**  Under the hypotheses of `power_loss_le_index_complexity`, the series
of the γ-th powers of the normalized errors over all forced positions of the branch is summable,
with sum at most `A (KPNat U e + C)`. -/
theorem power_loss_summable_le_index_complexity (U : Map) (hU : IsOptimalPrefixConditional U)
    (γ : ℝ) (hγ : 1 < γ) :
    ∃ A C : ℕ, ∀ (T : Set BitString) (e : ℕ) (ω : CantorSeq),
      DecidesTree e T → Branch T ω →
        Summable (forcedErrorTerm universalContinuousSemimeasure T ω γ) ∧
        ∑' i : ℕ, forcedErrorTerm universalContinuousSemimeasure T ω γ i ≤
          A * (((KPNat U e).toNat : ℝ) + C) := by
  obtain ⟨A, C, h⟩ := power_loss_le_index_complexity U hU γ hγ
  exact ⟨A, C, fun T e ω hdec hω =>
    summable_forcedErrorTerm_and_tsum_le _ T ω γ _ fun n => h T e ω n hdec hω⟩

/-- A computable prefix tree has finite prefix complexity. -/
theorem treeComplexity_ne_top (U : Map) (hU : IsOptimalPrefixConditional U)
    (T : Set BitString) (hT : IsComputablePrefixTree T) :
    treeComplexity U T ≠ ⊤ := by
  obtain ⟨e, he⟩ := exists_decidesTree_of_isComputablePrefixTree hT
  refine ne_top_of_le_ne_top ?_ (treeComplexity_le_KPNat U he)
  rw [KPNat_def]
  exact KPPlain_ne_top_of_isOptimalPrefixConditional hU _

/-- **Linear bound in the prefix complexity of the tree.**  For the optimal prefix machine `U`
and a real `γ > 1` there are constants `A` and `C` such that for every computable prefix tree
`T`, every branch `ω` of `T` and every `n`, the γ-power loss at the forced positions `i < n` is
at most `A (treeComplexity U T + C)`. -/
theorem power_loss_le_treeComplexity (U : Map) (hU : IsOptimalPrefixConditional U) (γ : ℝ)
    (hγ : 1 < γ) :
    ∃ A C : ℕ, ∀ (T : Set BitString) (ω : CantorSeq) (n : ℕ),
      IsComputablePrefixTree T → Branch T ω →
        partialPowerLoss universalContinuousSemimeasure T ω γ n ≤
          A * (((treeComplexity U T).toNat : ℝ) + C) := by
  obtain ⟨A, C, h⟩ := power_loss_le_index_complexity U hU γ hγ
  refine ⟨A, C, fun T ω n hT hω => ?_⟩
  obtain ⟨e, he, hKe⟩ := exists_decidesTree_KPNat_eq_treeComplexity U hT
  rw [← hKe]
  exact h T e ω n he hω

end Kolmogorov.SelectedBits
