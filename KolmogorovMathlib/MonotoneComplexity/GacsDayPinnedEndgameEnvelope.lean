import KolmogorovMathlib.AlgorithmicRandomness.ProbabilityBounded
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailConstruction
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Schedule
import KolmogorovMathlib.MonotoneComplexity.Omega.NullRealApi

/-!
# The numeric envelope of the single-call pinned endgame

The single call of the stage-`k` pinned strategy branches by

```
ladderBranching (grayTailBaseBranch (k-1) (grayFootprint (k-1))) a
  (a + 8 * grayFootprint (k-1) + 3)
```

and `GacsDayGameStatement` asks for a branching below `2 ^ ((C * d) ^ (C * d))`.
This module closes that gap directly against `grayFootprint`, never against
`grayFamilyEnvelope`: the pinned branching is bounded by
`2 ^ (grayFootprint k + k + 8)` (`ladderBranching_pinned_le`), the footprint is
bounded by `(4 * j) ^ (4 * j)` (`grayFootprint_le_pow`), and at the endgame
stage `k = 32 * d` these compose into `2 ^ ((129 * d) ^ (129 * d))`
(`pinnedEndgame_branch_le`), which fixes the public constant at `C = 129`.

The recursion in play is `grayFootprint (j+1) = 8 * fp j + 3 +
grayTailNewLoss j (fp j)` for `j ≥ 2` (`grayFootprint_succ_newLoss`), with
`grayTailNewLoss q L = 256 * (q+1)^2 * L + 256 * (q+1)`.

## Main results

* `one_le_grayFootprint`
* `grayFootprint_le_pow` — the fp-envelope domination.
* `ladderBranching_pinned_le` — branching domination of the pinned rung.
* `pinnedEndgame_branch_le` — the `C = 129` leaf.
* `pinnedEndgame_height_le` — the height leaf (needs only `C ≥ 65`).
-/

namespace Kolmogorov

/-- The gray footprint is never zero. -/
theorem one_le_grayFootprint : ∀ j : ℕ, 1 ≤ grayFootprint j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    match j with
    | 0 => decide
    | 1 => decide
    | 2 => decide
    | (m + 3) =>
      have h := ih (m + 2) (by omega)
      change 1 ≤ (256 * (m + 3) ^ 2 + 8) * grayFootprint (m + 2) + 256 * (m + 3) + 3
      omega

/-- **fp-envelope domination.**  The gray footprint of stage `j ≥ 2` is
dominated by `(4 * j) ^ (4 * j)`. -/
theorem grayFootprint_le_pow : ∀ j : ℕ, 2 ≤ j → grayFootprint j ≤ (4 * j) ^ (4 * j) := by
  intro j
  induction j with
  | zero => intro h; omega
  | succ i ih =>
    intro _
    rcases Nat.lt_or_ge i 2 with hi | hi
    · interval_cases i
      · decide
      · decide
    · have hF := ih hi
      have hone := one_le_grayFootprint i
      have hstep : grayFootprint (i + 1)
          = (256 * (i + 1) ^ 2 + 8) * grayFootprint i + 256 * (i + 1) + 3 :=
        grayFootprint_succ hi
      have hmul : (256 * (i + 1) ^ 2 + 8) * grayFootprint i + 256 * (i + 1) + 3
          ≤ (4 * (i + 1)) ^ 4 * grayFootprint i := by
        have h4 : (4 * (i + 1)) ^ 4 = 256 * (i + 1) ^ 4 := by ring
        rw [h4]
        have hm : 3 ≤ i + 1 := by omega
        have hbig : (256 * (i + 1) ^ 2 + 8) + (256 * (i + 1) + 3) ≤ 256 * (i + 1) ^ 4 := by
          have h1 : (256 * (i + 1) ^ 2 + 8) + (256 * (i + 1) + 3) ≤ 768 * (i + 1) ^ 2 := by
            nlinarith [hm]
          have hm2 : 9 ≤ (i + 1) ^ 2 := by nlinarith [hm]
          have h2 : 768 * (i + 1) ^ 2 ≤ 256 * (i + 1) ^ 4 := by
            have h3 : 9 * (i + 1) ^ 2 ≤ (i + 1) ^ 2 * (i + 1) ^ 2 :=
              Nat.mul_le_mul_right _ hm2
            have h4' : (i + 1) ^ 2 * (i + 1) ^ 2 = (i + 1) ^ 4 := by ring
            omega
          omega
        calc (256 * (i + 1) ^ 2 + 8) * grayFootprint i + 256 * (i + 1) + 3
            ≤ (256 * (i + 1) ^ 2 + 8) * grayFootprint i
                + (256 * (i + 1) + 3) * grayFootprint i := by
              have := Nat.le_mul_of_pos_right (256 * (i + 1) + 3)
                (by omega : 0 < grayFootprint i)
              omega
          _ = ((256 * (i + 1) ^ 2 + 8) + (256 * (i + 1) + 3)) * grayFootprint i := by ring
          _ ≤ 256 * (i + 1) ^ 4 * grayFootprint i := Nat.mul_le_mul_right _ hbig
      have hpow1 : (4 * i) ^ (4 * i) ≤ (4 * (i + 1)) ^ (4 * i) :=
        Nat.pow_le_pow_left (by omega) _
      have hpow2 : (4 * (i + 1)) ^ 4 * grayFootprint i
          ≤ (4 * (i + 1)) ^ 4 * (4 * (i + 1)) ^ (4 * i) :=
        Nat.mul_le_mul_left _ (le_trans hF hpow1)
      have hcomb : (4 * (i + 1)) ^ 4 * (4 * (i + 1)) ^ (4 * i)
          = (4 * (i + 1)) ^ (4 * (i + 1)) := by
        rw [← pow_add]
        congr 1
        omega
      omega

/-- **Branching domination of the pinned rung.**  The stage-`k` pinned call
branches below `2 ^ (grayFootprint k + k + 8)`, uniformly in the anchor `a`. -/
theorem ladderBranching_pinned_le (k a : ℕ) (hk : 3 ≤ k) :
    ladderBranching (grayTailBaseBranch (k - 1) (grayFootprint (k - 1))) a
        (a + 8 * grayFootprint (k - 1) + 3)
      ≤ 2 ^ (grayFootprint k + k + 8) := by
  set L := grayFootprint (k - 1) with hL
  have hstep : grayFootprint k = 8 * L + 3 + grayTailNewLoss (k - 1) L := by
    have h := grayFootprint_succ_newLoss (j := k - 1) (by omega)
    rw [show k - 1 + 1 = k by omega] at h
    exact h
  have hnew : grayTailNewLoss (k - 1) L = 256 * k ^ 2 * L + 256 * k := by
    rw [grayTailNewLoss, show k - 1 + 1 = k by omega]
  have hsub : a + 8 * L + 3 - a = 8 * L + 3 := by omega
  rw [ladderBranching, hsub, grayTailBaseBranch, show k - 1 + 1 = k by omega]
  refine max_le ?_ (max_le ?_ ?_)
  · calc 2 * 2 ^ (8 * L + 3) = 2 ^ (8 * L + 4) := by ring
      _ ≤ 2 ^ (grayFootprint k + k + 8) := Nat.pow_le_pow_right (by omega) (by omega)
  · calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (grayFootprint k + k + 8) := Nat.pow_le_pow_right (by omega) (by omega)
  · have hfp : grayFootprint k = 8 * L + 3 + (256 * k ^ 2 * L + 256 * k) := by
      rw [hstep, hnew]
    have hexp : (k + 8) + (256 * k ^ 2 * L + 256 * k) ≤ grayFootprint k + k + 8 := by omega
    have hk2 : 256 * k ≤ 2 ^ (k + 8) := by
      calc 256 * k ≤ 256 * 2 ^ k := by
            have := k_le_two_pow_k k
            omega
        _ = 2 ^ (k + 8) := by rw [pow_add]; ring
    calc 256 * k * 2 ^ (256 * k ^ 2 * L + 256 * k)
        ≤ 2 ^ (k + 8) * 2 ^ (256 * k ^ 2 * L + 256 * k) :=
          Nat.mul_le_mul_right _ hk2
      _ = 2 ^ ((k + 8) + (256 * k ^ 2 * L + 256 * k)) := (pow_add 2 _ _).symm
      _ ≤ 2 ^ (grayFootprint k + k + 8) := Nat.pow_le_pow_right (by omega) hexp

/-- **The `C = 129` branching leaf.**  At the endgame stage `k = 32 * d` the
pinned branching sits below the frozen envelope `2 ^ ((129 * d) ^ (129 * d))`,
uniformly in the anchor `a`. -/
theorem pinnedEndgame_branch_le {d : ℕ} (hd : 1 ≤ d) (a : ℕ) :
    ladderBranching (grayTailBaseBranch (32 * d - 1) (grayFootprint (32 * d - 1))) a
        (a + 8 * grayFootprint (32 * d - 1) + 3)
      ≤ 2 ^ ((129 * d) ^ (129 * d)) := by
  have hbr := ladderBranching_pinned_le (32 * d) a (by omega)
  refine le_trans hbr (Nat.pow_le_pow_right (by omega) ?_)
  -- `grayFootprint (32 * d) + 32 * d + 8 ≤ (129 * d) ^ (129 * d)`
  have hfp : grayFootprint (32 * d) ≤ (128 * d) ^ (128 * d) := by
    have h := grayFootprint_le_pow (32 * d) (by omega)
    rwa [show 4 * (32 * d) = 128 * d by ring] at h
  have hXle : (128 * d) ^ (128 * d) ≤ (129 * d) ^ (128 * d) :=
    Nat.pow_le_pow_left (by omega) _
  have hXge : 129 * d ≤ (129 * d) ^ (128 * d) := Nat.le_self_pow (by omega) _
  have hd2 : 129 * d ≤ (129 * d) ^ d := Nat.le_self_pow (by omega) _
  have hsplit : (129 * d) ^ (129 * d) = (129 * d) ^ (128 * d) * (129 * d) ^ d := by
    rw [← pow_add]
    congr 1
    omega
  have hlow : (129 * d) ^ (128 * d) * 129 ≤ (129 * d) ^ (129 * d) := by
    rw [hsplit]
    exact Nat.mul_le_mul_left _ (by omega)
  omega

/-- The height leaf: the pinned height `2 * (32 * d)` plus the lift's extra
level fits under `C * d` already for `C = 65`, hence a fortiori for `C = 129`. -/
theorem pinnedEndgame_height_le {d : ℕ} (hd : 1 ≤ d) : 2 * (32 * d) + 1 ≤ 129 * d := by
  omega

end Kolmogorov
