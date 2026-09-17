import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Spec

/-!
# The child rung's branching fits the parent's frozen base branch

The stage-`q` rung freezes the outer branching bound
`grayTailBaseBranch q L` with per-round budget `L`.  Its children are
stage-`(q−1)` rungs at budget `fp (q−1)`, planted at the block anchor `a'`
with exported depth `a' + graySpendSpan q`; their own ladder branching is
`ladderBranching (grayTailBaseBranch (q−1) (fp (q−1))) a' (a' + graySpendSpan q)`.
This file shows that the child branching is dominated by the parent's frozen
base branch as soon as the parent's budget dominates the child's footprint,
`fp (q−1) ≤ L`.  The proof is pure arithmetic: both the binomial term
`2 · 2^(graySpendSpan q)` and the child's own base branch sit below the
(deliberately roomy) parent bound.
-/

namespace Kolmogorov

/-- The footprint is positive at every stage. -/
lemma grayFootprint_pos : ∀ j : Nat, 1 <= grayFootprint j
  | 0 => by decide
  | 1 => by decide
  | 2 => by decide
  | j + 3 => by
    change 1 <= (256 * (j + 3) ^ 2 + 8) * grayFootprint (j + 2) + 256 * (j + 3) + 3
    omega

/-- The footprint is monotone across one stage. -/
lemma grayFootprint_pred_le : ∀ q : Nat, grayFootprint (q - 1) <= grayFootprint q
  | 0 => le_rfl
  | 1 => by decide
  | 2 => by decide
  | j + 3 => by
    change grayFootprint (j + 2) <=
      (256 * (j + 3) ^ 2 + 8) * grayFootprint (j + 2) + 256 * (j + 3) + 3
    have h1 : grayFootprint (j + 2) <= (256 * (j + 3) ^ 2 + 8) * grayFootprint (j + 2) :=
      Nat.le_mul_of_pos_left _ (by positivity)
    omega

/-- The child rung's ladder branching at the block anchor fits in the parent's frozen
base branch as soon as the parent's per-round budget dominates the child's footprint. -/
theorem grayChildBranching_le_baseBranch {q L a' : Nat}
    (hL : grayFootprint (q - 1) <= L) :
    ladderBranching (grayTailBaseBranch (q - 1) (grayFootprint (q - 1))) a'
        (a' + graySpendSpan q) <= grayTailBaseBranch q L := by
  -- the exponent of the child's binomial term
  have hspan : a' + graySpendSpan q - a' = 8 * grayFootprint (q - 1) + 3 := by
    rw [graySpendSpan, Nat.add_sub_cancel_left]
  -- `(q - 1) + 1 ≤ q + 1` uniformly, including `q = 0`
  have hm : q - 1 + 1 <= q + 1 := by omega
  -- the binomial term sits below the parent's exponential
  have hpow : 2 * 2 ^ (8 * grayFootprint (q - 1) + 3) <=
      256 * (q + 1) * 2 ^ (256 * (q + 1) ^ 2 * L + 256 * (q + 1)) := by
    apply Nat.mul_le_mul
    · omega
    · apply Nat.pow_le_pow_right (by norm_num)
      have hsq : 0 < (q + 1) ^ 2 := by positivity
      have h1 : 8 * grayFootprint (q - 1) <= 256 * (q + 1) ^ 2 * L :=
        calc 8 * grayFootprint (q - 1) <= 8 * L := Nat.mul_le_mul_left 8 hL
          _ <= 256 * (q + 1) ^ 2 * L := Nat.mul_le_mul_right L (by omega)
      omega
  have hpow' : 2 * 2 ^ (8 * grayFootprint (q - 1) + 3) <= grayTailBaseBranch q L := by
    unfold grayTailBaseBranch
    exact le_trans hpow (le_max_right _ _)
  -- the child's own base branch sits below the parent's
  have hbase : grayTailBaseBranch (q - 1) (grayFootprint (q - 1)) <=
      grayTailBaseBranch q L := by
    unfold grayTailBaseBranch
    refine max_le (le_max_left _ _) (le_trans ?_ (le_max_right _ _))
    refine Nat.mul_le_mul (Nat.mul_le_mul_left 256 hm) ?_
    refine Nat.pow_le_pow_right (by norm_num) (Nat.add_le_add ?_ (Nat.mul_le_mul_left 256 hm))
    exact Nat.mul_le_mul (Nat.mul_le_mul_left 256 (Nat.pow_le_pow_left hm 2)) hL
  unfold ladderBranching
  rw [hspan]
  exact max_le hpow' hbase

end Kolmogorov
