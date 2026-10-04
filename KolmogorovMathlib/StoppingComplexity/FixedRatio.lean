import KolmogorovMathlib.StoppingComplexity.WordGame
import KolmogorovMathlib.StoppingComplexity.StrategyComputable

/-!
# The fixed-ratio (T3) schedule and its word family

Blueprint 02 §8 (recovering T3 Theorem A, LEM-T3-PARAM), 04 §7 (Lemmas fixed-budget-unroll,
fixed-initial-budget, fixed-threshold, Corollary fixed-game-bounds), the Interface GAME-FIXED of
04 §1, and the W1/W2 bridge of 04 §8.

For a tag `c` put `g = c + 2`, `R = 2^g`, `q = 2^{-g} = 1/R` and `C = 2^c = R/4`, and take the
schedule `E_j = δ_j = (j + 1)·g + 1`, `0 ≤ j ≤ R` (`fixedSchedule c`). Then `s_j = w_j`,
`L_j = 2^g`, the budget recurrence of PARAM-GAME is `B_R = 1`, `B_{j-1} = (1 - q)·B_j - 2^{-E_j}`,
and the sharp thresholds of COR-GAME-SHARP are the exact T3 thresholds `B_j - 2^{-E_{j-1}}`.
Finite rational arithmetic (geometric sums, Bernoulli's inequality) gives FB, `B_0 ≥ 2^{-E_0}`
(FB0) and `Ψ♯_R ≥ R/2 ≥ C` (FP), so the concrete strategy `localStrategy` wins in the palette
capacity `[0, 2^c)` (GAME-FIXED), with the exponent bound FE and the height bound FH. Through
LEM-SHADOW with `cap = c` this is the uniformly computable family `fixedWordFamily`, winning
`G_c` (reply bound `n + c`), and on word-reachable histories its requests obey FE and FH
(`fixedWordFamily_exp_le`, `fixedWordFamily_length_le`), which the T3 endpoints use for W1/W2.
-/

namespace Kolmogorov

/-! ### The fixed schedule (02 §8, 04 §7) -/

/-- The fixed T3 schedule of the tag `c`: `g = c + 2`, `R = 2^g` levels, and exponents equal to
depths, `E_j = δ_j = (j + 1)·g + 1` for `0 ≤ j ≤ R`. With `s_j = w_j` and `L_j = 2^g` the
budget recurrence of PARAM-GAME is `B_R = 1`, `B_{j-1} = (1 - 2^{-g})·B_j - 2^{-E_j}`.
Blueprint 02 §8 and 04 §7, fixed parameters (`02-8-T3-RECOVER`, `04-FIXED-PARAMS`). -/
def fixedSchedule (c : ℕ) : GameSchedule :=
  ⟨(List.range (2 ^ (c + 2) + 1)).map fun j => (j + 1) * (c + 2) + 1,
    (List.range (2 ^ (c + 2) + 1)).map fun j => (j + 1) * (c + 2) + 1⟩

/-- The fixed schedule is valid: the two lists have the same positive length `2^{c+2} + 1`, the
exponents and depths increase strictly, and `E_0 = c + 3 ≥ 1`.
Blueprint 02 §8 (the schedule of DEF-03 with `g ≥ 1`) (`02-8-T3-RECOVER`). -/
theorem fixedSchedule_isValid (c : ℕ) : (fixedSchedule c).IsValid := by
  have hmono : List.Pairwise (· < ·)
      ((List.range (2 ^ (c + 2) + 1)).map fun j => (j + 1) * (c + 2) + 1) := by
    rw [List.pairwise_map]
    exact List.pairwise_lt_range.imp fun hij => by nlinarith
  refine ⟨rfl, by simp [fixedSchedule], hmono, hmono, ?_⟩
  simp [fixedSchedule, GameSchedule.exp]

/-- FE: the top exponent of the fixed schedule is `E_R = (2^{c+2} + 1)·(c + 2) + 1`.
Blueprint 04 Corollary fixed-game-bounds, (FE) (`04-FIXED-GAME-BOUNDS`). -/
theorem fixedSchedule_exp_R (c : ℕ) :
    (fixedSchedule c).exp (fixedSchedule c).R = (2 ^ (c + 2) + 1) * (c + 2) + 1 := by
  simp [GameSchedule.exp, GameSchedule.R, fixedSchedule, List.getD_eq_getElem?_getD]

/-- The exact T3 thresholds: since `s_j = w_j`, every sharp threshold of the fixed schedule is
`t♯_j = B_j - 2^{-E_{j-1}}`, so `Ψ♯_j = Σ_{i=1}^j (B_i - 2^{-E_{i-1}})`.
Blueprint 02 §8 ("COR-GAME-SHARP gives the exact T3 thresholds") (`02-8-T3-RECOVER`). -/
theorem fixedSchedule_thresholdSharp_eq (c j : ℕ) :
    (fixedSchedule c).thresholdSharp j =
      (fixedSchedule c).budget j - (fixedSchedule c).weight (j - 1) := by
  have hs : ∀ i, (fixedSchedule c).fineLength i = (fixedSchedule c).weight i := fun _ => rfl
  have hw : (fixedSchedule c).weight j ≠ 0 := by
    unfold GameSchedule.weight requestWeight
    positivity
  rw [GameSchedule.thresholdSharp, hs, hs, div_self hw, mul_one]

/-- The top level of the fixed schedule is `R = 2^{c+2}`. Blueprint 04 §7 (`R = 2^g`). -/
private theorem fixedSchedule_R (c : ℕ) : (fixedSchedule c).R = 2 ^ (c + 2) := by
  simp [GameSchedule.R, fixedSchedule]

/-- The exponents (equal to the depths) of the fixed schedule in range:
`E_j = (j + 1)·(c + 2) + 1` for `j ≤ R`. Blueprint 04 §7. -/
private theorem fixedSchedule_exp_of_le (c : ℕ) {j : ℕ} (hj : j ≤ 2 ^ (c + 2)) :
    (fixedSchedule c).exp j = (j + 1) * (c + 2) + 1 := by
  simp [GameSchedule.exp, fixedSchedule, List.getD_eq_getElem?_getD, Nat.lt_succ_of_le hj]

/-- The weights of the fixed schedule in range: `w_j = 2^{-E_j} = q^{j+1}/2` with
`q = 2^{-(c+2)}`, for `j ≤ R`. Blueprint 02 LEM-T3-PARAM step 1 (`w_i = q^{i+1}/2`). -/
private theorem fixedSchedule_weight_of_le (c : ℕ) {j : ℕ} (hj : j ≤ 2 ^ (c + 2)) :
    (fixedSchedule c).weight j = ((1 / 2 : ℚ) ^ (c + 2)) ^ (j + 1) / 2 := by
  rw [GameSchedule.weight, requestWeight, fixedSchedule_exp_of_le c hj, pow_succ, ← pow_mul,
    mul_comm (c + 2)]
  ring

/-- The ratios of the fixed schedule: `L_{j+1} = 2^{δ_{j+1} - δ_j} = 2^{c+2}` for `j < R`.
Blueprint 02 §8 (`L = 2^g`). -/
private theorem fixedSchedule_ratio (c : ℕ) {j : ℕ} (hj : j < 2 ^ (c + 2)) :
    (fixedSchedule c).ratio (j + 1) = 2 ^ (c + 2) := by
  have h1 : (fixedSchedule c).depth (j + 1) = (j + 1 + 1) * (c + 2) + 1 :=
    fixedSchedule_exp_of_le c hj
  have h2 : (fixedSchedule c).depth j = (j + 1) * (c + 2) + 1 :=
    fixedSchedule_exp_of_le c hj.le
  rw [GameSchedule.ratio, Nat.add_sub_cancel, h1, h2]
  congr 1
  rw [show (j + 1 + 1) * (c + 2) + 1 = ((j + 1) * (c + 2) + 1) + (c + 2) by ring]
  omega

/-- Every budget of every schedule is at most one: `B_R = 1`, and each step of the downward
recursion multiplies by `1 - 1/L ∈ [0, 1]` and subtracts a positive weight (the backwards
induction of (B1)). Blueprint 04 Lemma fixed-budget-unroll, upper half of (FB). -/
private theorem budget_le_one (S : GameSchedule) (j : ℕ) : S.budget j ≤ 1 := by
  unfold GameSchedule.budget
  generalize S.R - j = k
  induction k with
  | zero => exact le_refl _
  | succ k ih =>
    rw [GameSchedule.budgetAux]
    have hL : (1 : ℚ) ≤ (S.ratio (S.R - k) : ℚ) := by
      unfold GameSchedule.ratio
      exact_mod_cast Nat.one_le_two_pow
    have h0 : 0 ≤ 1 / (S.ratio (S.R - k) : ℚ) := by positivity
    have h1 : 1 / (S.ratio (S.R - k) : ℚ) ≤ 1 := by
      rw [div_le_one (by linarith)]
      exact hL
    have hw : 0 < S.weight (S.R - k) := by
      unfold GameSchedule.weight requestWeight
      positivity
    nlinarith

/-- The marker count of every level `1 ≤ j ≤ R` of the fixed schedule is at most `2^{E_{j-1}}`:
since `B_j ≤ 1` and `w_j·2^{E_{j-1}} = 2^{-g}` lies strictly between `0` and `1`,
`M_j = ⌊(B_j - w_j)·2^{E_{j-1}}⌋ + 1 ≤ 2^{E_{j-1}}`.
Blueprint 02 §8 (`M_j ≤ 2^{E_{j-1}}`) (`02-8-T3-RECOVER`). -/
theorem fixedSchedule_markerBound_le (c : ℕ) {j : ℕ} (hj : 1 ≤ j)
    (hjR : j ≤ (fixedSchedule c).R) :
    (fixedSchedule c).markerBound j ≤ 2 ^ (fixedSchedule c).exp (j - 1) := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rw [fixedSchedule_R] at hjR
  have hB := budget_le_one (fixedSchedule c) (i + 1)
  have hw : 0 < (fixedSchedule c).weight (i + 1) := by
    unfold GameSchedule.weight requestWeight
    positivity
  have hLw : ((fixedSchedule c).ratio (i + 1) : ℚ) * (fixedSchedule c).weight (i + 1) =
      (1 / 2 : ℚ) ^ (fixedSchedule c).exp i := by
    rw [fixedSchedule_ratio c (by omega), GameSchedule.weight, requestWeight,
      fixedSchedule_exp_of_le c hjR, fixedSchedule_exp_of_le c (by omega),
      show (i + 1 + 1) * (c + 2) + 1 = ((i + 1) * (c + 2) + 1) + (c + 2) by ring,
      pow_add (1 / 2 : ℚ), Nat.cast_pow, Nat.cast_ofNat, mul_left_comm, ← mul_pow]
    norm_num
  unfold GameSchedule.markerBound markerCount
  rw [Nat.add_sub_cancel, Nat.add_one_le_iff, Nat.floor_lt' (by positivity), hLw,
    div_lt_iff₀ (by positivity)]
  push_cast
  rw [← mul_pow]
  norm_num
  linarith

/-- The height bound of the fixed schedule grows by at most `2^{g + 2E_{j-1}}` per level
`1 ≤ j ≤ R`: with `k = 2^{E_{j-1}} ≥ 2` and `L = 2^g ≥ 2` the phase height
`2M_j + (L - 1)·M_j(M_j - 1)/2` is at most `(L - 1)·k(k - 1)/2 + 2k ≤ L·k^2`.
Blueprint 02 §8 (`H_j ≤ H_{j-1} + 2^{g + 2E_{j-1}}`) (`02-8-T3-RECOVER`). -/
theorem fixedSchedule_heightBound_step (c : ℕ) {j : ℕ} (hj : 1 ≤ j)
    (hjR : j ≤ (fixedSchedule c).R) :
    (fixedSchedule c).heightBound j ≤
      (fixedSchedule c).heightBound (j - 1) + 2 ^ (c + 2 + 2 * (fixedSchedule c).exp (j - 1)) := by
  have hM := fixedSchedule_markerBound_le c hj hjR
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rw [fixedSchedule_R] at hjR
  rw [Nat.add_sub_cancel] at hM ⊢
  rw [GameSchedule.heightBound, fixedSchedule_ratio c (by omega)]
  set M := (fixedSchedule c).markerBound (i + 1)
  set k := 2 ^ (fixedSchedule c).exp i with hk
  have hk2 : 2 ≤ k := by
    rw [hk, fixedSchedule_exp_of_le c (by omega)]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hL : 1 ≤ 2 ^ (c + 2) := Nat.one_le_two_pow
  have hdiv : M * (M - 1) / 2 ≤ k * k :=
    (Nat.div_le_self _ _).trans (Nat.mul_le_mul hM ((Nat.sub_le _ _).trans hM))
  have hprod : (2 ^ (c + 2) - 1) * (M * (M - 1) / 2) ≤ (2 ^ (c + 2) - 1) * (k * k) :=
    Nat.mul_le_mul_left _ hdiv
  have hsplit : 2 ^ (c + 2) * (k * k) = (2 ^ (c + 2) - 1) * (k * k) + k * k := by
    rw [Nat.sub_mul, one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_left _ (by positivity))]
  have htwo : 2 * M ≤ k * k := by nlinarith
  have hpow : 2 ^ (c + 2 + 2 * (fixedSchedule c).exp i) = 2 ^ (c + 2) * (k * k) := by
    rw [hk]
    ring
  rw [hpow]
  omega

/-! ### Budgets and thresholds (04 §7, 02 LEM-T3-PARAM) -/

/-- The unrolled budget with its exact geometric tail: with `q = 2^{-(c+2)}`, for `i ≤ R`,
`B_{R-i} ≥ (1 - q)^i - q^{R-i+2}`. The recurrence `B_{R-i-1} = (1 - q)·B_{R-i} - q^{R-i+1}/2`
multiplies the bound by `1 - q ∈ [0, 1]` and subtracts the cost `q^{R-i+1}/2`, and
`q^{R-i+2} + q^{R-i+1}/2 ≤ q^{R-i+1}` since `q ≤ 1/2` (the finite geometric sum of the costs).
Blueprint 04 Lemma fixed-budget-unroll and 02 LEM-T3-PARAM step 2. -/
private theorem fixedSchedule_budget_ge_tail (c : ℕ) {i : ℕ} (hi : i ≤ (fixedSchedule c).R) :
    (1 - (1 / 2 : ℚ) ^ (c + 2)) ^ i - ((1 / 2 : ℚ) ^ (c + 2)) ^ ((fixedSchedule c).R - i + 2) ≤
      (fixedSchedule c).budget ((fixedSchedule c).R - i) := by
  rw [GameSchedule.budget, Nat.sub_sub_self hi]
  rw [fixedSchedule_R] at hi ⊢
  set q : ℚ := (1 / 2 : ℚ) ^ (c + 2) with hq
  have hq0 : 0 < q := by positivity
  have hq2 : q ≤ 1 / 2 := by
    rw [hq]
    calc (1 / 2 : ℚ) ^ (c + 2) ≤ (1 / 2) ^ 1 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 2 := by norm_num
  induction i with
  | zero =>
    have : 0 < q ^ (2 ^ (c + 2) - 0 + 2) := by positivity
    simp only [pow_zero, GameSchedule.budgetAux]
    linarith
  | succ i ih =>
    have ih := ih (by omega)
    obtain ⟨n, hn⟩ : ∃ n, 2 ^ (c + 2) - i = n + 1 := ⟨2 ^ (c + 2) - i - 1, by omega⟩
    have hL : (1 : ℚ) / ((fixedSchedule c).ratio ((fixedSchedule c).R - i) : ℚ) = q := by
      rw [fixedSchedule_R, hn, fixedSchedule_ratio c (by omega), hq, one_div_pow]
      push_cast
      rfl
    have hw : (fixedSchedule c).weight ((fixedSchedule c).R - i) = q ^ (n + 1 + 1) / 2 := by
      rw [fixedSchedule_R, hn, fixedSchedule_weight_of_le c (by omega)]
    rw [GameSchedule.budgetAux, hL, hw, show 2 ^ (c + 2) - (i + 1) + 2 = n + 1 + 1 by omega]
    rw [show 2 ^ (c + 2) - i + 2 = n + 1 + 1 + 1 by omega] at ih
    have h1q : 0 ≤ 1 - q := by linarith
    have key := mul_le_mul_of_nonneg_right ih h1q
    have hx : 0 < q ^ (n + 1 + 1) := by positivity
    rw [pow_succ q (n + 1 + 1)] at key
    rw [pow_succ]
    nlinarith [mul_nonneg hx.le (sub_nonneg.2 hq2), mul_nonneg (mul_nonneg hq0.le hq0.le) hx.le]

/-- fixed-budget-unroll (FB): with `q = 2^{-(c+2)}`, for every `0 ≤ i ≤ R`,
`(1 - q)^i - q^2 ≤ B_{R-i} ≤ 1`. Unrolling the recurrence leaves `(1 - q)^i` minus the costs
`2^{-E_j}` weighted by powers of `1 - q` in `[0, 1]`, and the finite geometric sum
`Σ_{j=1}^R 2^{-E_j}` is at most `q^2`; the upper bound is backwards induction.
Blueprint 04 Lemma fixed-budget-unroll, (FB) (`04-FB`). -/
theorem fixedSchedule_budget_unroll (c : ℕ) {i : ℕ} (hi : i ≤ (fixedSchedule c).R) :
    (1 - (1 / 2 : ℚ) ^ (c + 2)) ^ i - ((1 / 2 : ℚ) ^ (c + 2)) ^ 2 ≤
        (fixedSchedule c).budget ((fixedSchedule c).R - i) ∧
      (fixedSchedule c).budget ((fixedSchedule c).R - i) ≤ 1 := by
  have htail := fixedSchedule_budget_ge_tail c hi
  have hle : ((1 / 2 : ℚ) ^ (c + 2)) ^ ((fixedSchedule c).R - i + 2) ≤
      ((1 / 2 : ℚ) ^ (c + 2)) ^ 2 :=
    pow_le_pow_of_le_one (by positivity) (pow_le_one₀ (by norm_num) (by norm_num)) (by omega)
  exact ⟨by linarith, budget_le_one _ _⟩

/-- `(1 - q)^R ≥ 1/4` for `q = 2^{-(c+2)}` and `R = 2^{c+2}`: Bernoulli's inequality on the
block `R/4 = 2^c` gives `(1 - q)^{2^c} ≥ 1 - 2^c q = 3/4`, and `(3/4)^4 = 81/256 ≥ 1/4`.
Blueprint 04 Lemma fixed-initial-budget. -/
private theorem quarter_le_one_sub_pow (c : ℕ) :
    (1 / 4 : ℚ) ≤ (1 - (1 / 2 : ℚ) ^ (c + 2)) ^ 2 ^ (c + 2) := by
  have hq : (1 / 2 : ℚ) ^ (c + 2) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hb := one_add_mul_le_pow (a := -(1 / 2 : ℚ) ^ (c + 2)) (by linarith) (2 ^ c)
  have h34 : ((2 ^ c : ℕ) : ℚ) * (1 / 2) ^ (c + 2) = 1 / 4 := by
    push_cast
    rw [pow_add, ← mul_assoc, ← mul_pow]
    norm_num
  rw [← sub_eq_add_neg, mul_neg, h34] at hb
  rw [show 2 ^ (c + 2) = 2 ^ c * 4 by rw [pow_add]; norm_num, pow_mul]
  calc (1 / 4 : ℚ) ≤ (1 - 1 / 4) ^ 4 := by norm_num
    _ ≤ _ := pow_le_pow_left₀ (by norm_num) (by linarith) 4

/-- Every budget `B_j`, `j ≤ R`, of the fixed schedule is at least `3/16`: by the unrolled bound,
`B_j ≥ (1 - q)^{R-j} - q^{j+2} ≥ (1 - q)^R - q^2 ≥ 1/4 - 1/16`.
Blueprint 04 Lemma fixed-initial-budget (`B_0 ≥ 1/4 - q^2 ≥ 3/16`, and every budget is at least
`B_0`). -/
private theorem fixedSchedule_budget_ge (c : ℕ) {j : ℕ} (hj : j ≤ (fixedSchedule c).R) :
    (3 / 16 : ℚ) ≤ (fixedSchedule c).budget j := by
  have h := fixedSchedule_budget_ge_tail c (Nat.sub_le (fixedSchedule c).R j)
  rw [Nat.sub_sub_self hj] at h
  have hR := fixedSchedule_R c
  have hq : (1 / 2 : ℚ) ^ (c + 2) ≤ 1 / 4 := by
    calc (1 / 2 : ℚ) ^ (c + 2) ≤ (1 / 2) ^ 2 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 4 := by norm_num
  have hq0 : 0 ≤ (1 / 2 : ℚ) ^ (c + 2) := by positivity
  have h1 : (1 - (1 / 2 : ℚ) ^ (c + 2)) ^ (fixedSchedule c).R ≤
      (1 - (1 / 2 : ℚ) ^ (c + 2)) ^ ((fixedSchedule c).R - j) :=
    pow_le_pow_of_le_one (by linarith) (by linarith) (Nat.sub_le _ _)
  have h2 : ((1 / 2 : ℚ) ^ (c + 2)) ^ (j + 2) ≤ ((1 / 2 : ℚ) ^ (c + 2)) ^ 2 :=
    pow_le_pow_of_le_one hq0 (by linarith) (by omega)
  have h3 : ((1 / 2 : ℚ) ^ (c + 2)) ^ 2 ≤ (1 / 4) ^ 2 := pow_le_pow_left₀ hq0 hq 2
  have h4 := quarter_le_one_sub_pow c
  rw [← hR] at h4
  norm_num at h3
  linarith

/-- fixed-initial-budget (FB0): `B_0 ≥ 2^{-E_0} = q/2 = w_0`, and the budgets increase with the
level, `B_j ≤ B_{j+1}` for `j < R`. By FB with `i = R`, `B_0 ≥ (1 - q)^R - q^2`, where
`(1 - q)^{R/4} ≥ 3/4` (Bernoulli) gives `(1 - q)^R ≥ (3/4)^4 ≥ 1/4`, so
`B_0 ≥ 1/4 - q^2 ≥ 3/16 ≥ q/2`; the recurrence has a positive multiplier and a nonnegative
subtracted term, so once the budgets are positive they increase.
Blueprint 04 Lemma fixed-initial-budget, (FB0), and 02 LEM-T3-PARAM steps 3–4 (`04-FB0`). -/
theorem fixedSchedule_budget_zero_ge (c : ℕ) :
    (fixedSchedule c).weight 0 ≤ (fixedSchedule c).budget 0 ∧
      ∀ j, j < (fixedSchedule c).R →
        (fixedSchedule c).budget j ≤ (fixedSchedule c).budget (j + 1) := by
  refine ⟨?_, fun j hj => ?_⟩
  · have h0 := fixedSchedule_budget_ge c (Nat.zero_le _)
    have hw : (fixedSchedule c).weight 0 ≤ 1 / 8 := by
      rw [fixedSchedule_weight_of_le c (Nat.zero_le _), pow_one]
      have : (1 / 2 : ℚ) ^ (c + 2) ≤ (1 / 2) ^ 2 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      norm_num at this ⊢
      linarith
    linarith
  · have hrec := (fixedSchedule c).budget_eq_of_lt hj
    have hpos := fixedSchedule_budget_ge c (j := j + 1) (by omega)
    have hL : 0 ≤ 1 / ((fixedSchedule c).ratio (j + 1) : ℚ) := by positivity
    have hw : 0 < (fixedSchedule c).weight (j + 1) := by
      unfold GameSchedule.weight requestWeight
      positivity
    rw [hrec]
    nlinarith [mul_nonneg (by linarith : (0 : ℚ) ≤ (fixedSchedule c).budget (j + 1)) hL]

/-- The partial sharp potentials of the fixed schedule: for `j ≤ R`,
`Ψ♯_j ≥ q·j(j + 1)/2 - (1 - q^j)/2` with `q = 2^{-(c+2)}`. The increment is
`t♯_j = B_j - q^j/2`, where `B_j ≥ (1 - q)^{R-j} - q^{j+2} ≥ 1 - (R - j)q - q^{j+2} = jq - q^{j+2}`
(the unrolled bound, Bernoulli, `Rq = 1`), and the costs `q^{j+2} + q^j/2` are absorbed by
`(q^{j-1} - q^j)/2` since `q + q^3 ≤ 1/2`.
Blueprint 04 Lemma fixed-threshold and 02 LEM-T3-PARAM steps 5–7. -/
private theorem fixedSchedule_psiSharp_ge_partial (c : ℕ) {j : ℕ}
    (hj : j ≤ (fixedSchedule c).R) :
    (1 / 2 : ℚ) ^ (c + 2) * (j * (j + 1)) / 2 - (1 - ((1 / 2 : ℚ) ^ (c + 2)) ^ j) / 2 ≤
      (fixedSchedule c).psiSharp j := by
  induction j with
  | zero => simp [GameSchedule.psiSharp]
  | succ j ih =>
    have ih := ih (by omega)
    have htail := fixedSchedule_budget_ge_tail c (Nat.sub_le (fixedSchedule c).R (j + 1))
    rw [Nat.sub_sub_self hj] at htail
    rw [GameSchedule.psiSharp, Finset.sum_Icc_succ_top (by omega), ← GameSchedule.psiSharp,
      fixedSchedule_thresholdSharp_eq, Nat.add_sub_cancel,
      fixedSchedule_weight_of_le c (by rw [fixedSchedule_R] at hj; omega)]
    set q : ℚ := (1 / 2 : ℚ) ^ (c + 2) with hq
    have hq0 : 0 < q := by positivity
    have hq4 : q ≤ 1 / 4 := by
      rw [hq]
      calc (1 / 2 : ℚ) ^ (c + 2) ≤ (1 / 2) ^ 2 :=
            pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
        _ = 1 / 4 := by norm_num
    have hRq : ((fixedSchedule c).R : ℚ) * q = 1 := by
      rw [fixedSchedule_R, hq, Nat.cast_pow, Nat.cast_ofNat, ← mul_pow]
      norm_num
    have hbern := one_add_mul_le_pow (a := -q) (by linarith) ((fixedSchedule c).R - (j + 1))
    rw [← sub_eq_add_neg, Nat.cast_sub hj] at hbern
    have hx : 0 < q ^ j := by positivity
    rw [show j + 1 + 2 = j + 3 by omega, pow_add q j 3] at htail
    rw [pow_succ q j]
    have hq3 : q ^ 3 ≤ (1 / 4) ^ 3 := pow_le_pow_left₀ hq0.le hq4 3
    push_cast at hbern ⊢
    nlinarith [mul_nonneg hx.le (by linarith : (0 : ℚ) ≤ 1 / 2 - q - q ^ 3)]

/-- fixed-threshold (FP): the sharp potential at the top level is at least `R/2` (hence at
least `C = 2^c = R/4`): `Ψ♯_R = Σ_{j=1}^R (B_j - 2^{-E_{j-1}})`, where
`Σ_{j=1}^R B_j ≥ Σ_{k<R} (1 - q)^k - R q^2 ≥ (R + 1)/2 - q` by FB and Bernoulli,
`Σ_{j=1}^R 2^{-E_{j-1}} ≤ q`, and `2q ≤ 1/2`.
Blueprint 04 Lemma fixed-threshold, (FP), and 02 LEM-T3-PARAM steps 5–7 (`04-FP`). -/
theorem fixedSchedule_psiSharp_ge (c : ℕ) :
    ((fixedSchedule c).R : ℚ) / 2 ≤ (fixedSchedule c).psiSharp (fixedSchedule c).R := by
  have h := fixedSchedule_psiSharp_ge_partial c (le_refl (fixedSchedule c).R)
  have hRq : ((fixedSchedule c).R : ℚ) * (1 / 2 : ℚ) ^ (c + 2) = 1 := by
    rw [fixedSchedule_R, Nat.cast_pow, Nat.cast_ofNat, ← mul_pow]
    norm_num
  have hx : 0 ≤ ((1 / 2 : ℚ) ^ (c + 2)) ^ (fixedSchedule c).R := by positivity
  nlinarith

/-- The source threshold of the fixed schedule is the sharp one minus the weight:
`t_j = B_j - 2^{-E_j} - 2^{-E_{j-1}} = t♯_j - w_j` (since `s_j = w_j` and `h_j = w_{j-1}`).
Blueprint 02 LEM-T3-PARAM and 04 Lemma fixed-threshold (source-threshold form). -/
private theorem fixedSchedule_threshold_eq (c j : ℕ) :
    (fixedSchedule c).threshold j =
      (fixedSchedule c).thresholdSharp j - (fixedSchedule c).weight j := by
  have hs : ∀ i, (fixedSchedule c).fineLength i = (fixedSchedule c).weight i := fun _ => rfl
  have hw : (fixedSchedule c).weight j ≠ 0 := by
    unfold GameSchedule.weight requestWeight
    positivity
  rw [GameSchedule.threshold, GameSchedule.thresholdSharp, hs, hs, div_self hw, mul_one,
    mul_one]
  have hc : (fixedSchedule c).coarseLength j = (fixedSchedule c).weight (j - 1) := rfl
  rw [hc]
  ring

/-- The fixed schedule satisfies the hypotheses of COR-GAME-SHARP: it is admissible in the
sense of PARAM-GAME (valid, `w_0 ≤ B_0`, and every source threshold
`t_j = B_j - 2^{-E_j} - 2^{-E_{j-1}}` with `1 ≤ j ≤ R` is nonnegative), and every sharp threshold
`t♯_j = B_j - 2^{-E_{j-1}}` with `1 ≤ j ≤ R` is nonnegative (`B_j ≥ B_0 ≥ 3/16` while
`2^{-E_j} + 2^{-E_{j-1}} ≤ q^2/2 + q/2 ≤ 5/32`). Source admissibility is included because
`localStrategy_winning_sharp` takes `S.IsAdmissible`.
Blueprint 02 LEM-T3-PARAM ("`B_0 ≥ 2^{-E_0}` implies every threshold is nonnegative") and 04
Lemma fixed-threshold, last sentence (`02-LEM-T3-PARAM`). -/
theorem fixedSchedule_isAdmissibleSharp (c : ℕ) :
    (fixedSchedule c).IsAdmissible ∧
      ∀ j, 1 ≤ j → j ≤ (fixedSchedule c).R → 0 ≤ (fixedSchedule c).thresholdSharp j := by
  have hq : (1 / 2 : ℚ) ^ (c + 2) ≤ 1 / 4 := by
    calc (1 / 2 : ℚ) ^ (c + 2) ≤ (1 / 2) ^ 2 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 4 := by norm_num
  have hq0 : 0 ≤ (1 / 2 : ℚ) ^ (c + 2) := by positivity
  have hsharp : ∀ j, 1 ≤ j → j ≤ (fixedSchedule c).R →
      (fixedSchedule c).weight j ≤ 1 / 32 ∧ 1 / 16 ≤ (fixedSchedule c).thresholdSharp j := by
    intro j hj1 hjR
    have hB := fixedSchedule_budget_ge c hjR
    rw [fixedSchedule_R] at hjR
    rw [fixedSchedule_thresholdSharp_eq, fixedSchedule_weight_of_le c (j := j - 1) (by omega),
      fixedSchedule_weight_of_le c (j := j) hjR, Nat.sub_add_cancel hj1]
    have h1 : ((1 / 2 : ℚ) ^ (c + 2)) ^ j ≤ (1 / 2 : ℚ) ^ (c + 2) :=
      pow_le_of_le_one hq0 (by linarith) (by omega)
    have h2 : ((1 / 2 : ℚ) ^ (c + 2)) ^ (j + 1) ≤ ((1 / 2 : ℚ) ^ (c + 2)) ^ 2 :=
      pow_le_pow_of_le_one hq0 (by linarith) (by omega)
    have h3 : ((1 / 2 : ℚ) ^ (c + 2)) ^ 2 ≤ (1 / 4) ^ 2 := pow_le_pow_left₀ hq0 hq 2
    norm_num at h3
    constructor <;> linarith
  refine ⟨⟨fixedSchedule_isValid c, (fixedSchedule_budget_zero_ge c).1, fun j hj1 hjR => ?_⟩,
    fun j hj1 hjR => by linarith [(hsharp j hj1 hjR).2]⟩
  rw [fixedSchedule_threshold_eq]
  linarith [hsharp j hj1 hjR]

/-- The palette capacity `C = 2^c` is also below the source potential of the fixed schedule:
`2^c ≤ Ψ_R`, since `Ψ_R = Ψ♯_R - Σ_{j=1}^R 2^{-E_j} ≥ R/2 - q^2 ≥ R/4`. This puts the T3 game
under the hypotheses of THEOREM-GAME as well, which the height bound `localStrategy_length_le`
(LEM-EFF-01, stated under them) needs for W2.
Blueprint 04 Lemma fixed-threshold (source-threshold form) with 02 LEM-EFF-01
(`04-W1-W2-BRIDGE`). -/
theorem fixedSchedule_psi_ge (c : ℕ) :
    (2 ^ c : ℚ) ≤ (fixedSchedule c).psi (fixedSchedule c).R := by
  have hsum : (fixedSchedule c).psi (fixedSchedule c).R =
      (fixedSchedule c).psiSharp (fixedSchedule c).R -
        ∑ i ∈ Finset.Icc 1 (fixedSchedule c).R, (fixedSchedule c).weight i := by
    rw [GameSchedule.psi, GameSchedule.psiSharp, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => fixedSchedule_threshold_eq c i
  have hw : ∑ i ∈ Finset.Icc 1 (fixedSchedule c).R, (fixedSchedule c).weight i ≤
      ((fixedSchedule c).R : ℚ) / 4 := by
    have hle : ∀ i ∈ Finset.Icc 1 (fixedSchedule c).R, (fixedSchedule c).weight i ≤ 1 / 4 := by
      intro i hi
      have hiR := (Finset.mem_Icc.1 hi).2
      rw [fixedSchedule_R] at hiR
      rw [fixedSchedule_weight_of_le c hiR]
      have h1 : ((1 / 2 : ℚ) ^ (c + 2)) ^ (i + 1) ≤ (1 / 2 : ℚ) ^ (c + 2) :=
        pow_le_of_le_one (by positivity) (pow_le_one₀ (by norm_num) (by norm_num)) (by omega)
      have h2 : (1 / 2 : ℚ) ^ (c + 2) ≤ 1 / 2 := pow_le_of_le_one (by norm_num) (by norm_num)
        (by omega)
      linarith
    have := Finset.sum_le_card_nsmul _ _ _ hle
    rw [Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul] at this
    linarith
  have hC : (2 ^ c : ℚ) = ((fixedSchedule c).R : ℚ) / 4 := by
    rw [fixedSchedule_R, Nat.cast_pow, Nat.cast_ofNat, pow_add]
    norm_num
  have hFP := fixedSchedule_psiSharp_ge c
  rw [hsum]
  linarith

/-! ### The fixed game (GAME-FIXED, fixed-game-bounds) -/

/-- GAME-FIXED: the concrete strategy `localStrategy (fixedSchedule c) R (2^c)` wins the local
game of the fixed schedule at the top level `R` in the palette capacity `U = C = 2^c`: every
request is fresh and uses an exponent among `E_0, …, E_R`, every path load including the pending
request is at most `B_R = 1`, and no legal history answers `T_R` requests. By COR-GAME-SHARP
with `fixedSchedule_isAdmissibleSharp` and `C ≤ R/2 ≤ Ψ♯_R` (FP).
Blueprint 04 Interface GAME-FIXED and Corollary fixed-game-bounds ("Alice wins `G_c`")
(`04-GAME-FIXED`). -/
theorem fixedSchedule_wins (c : ℕ) :
    IsWinningLocalStrategy (fixedSchedule c) (fixedSchedule c).R (2 ^ c) 1
      ((fixedSchedule c).requestBound (fixedSchedule c).R)
      (localStrategy (fixedSchedule c) (fixedSchedule c).R (2 ^ c)) := by
  obtain ⟨hA, hsharp⟩ := fixedSchedule_isAdmissibleSharp c
  have hC : (2 ^ c : ℚ) ≤ ((fixedSchedule c).R : ℚ) / 2 := by
    rw [fixedSchedule_R, Nat.cast_pow, Nat.cast_ofNat, pow_add]
    have : (0 : ℚ) ≤ 2 ^ c := by positivity
    linarith
  have hwin := localStrategy_winning_sharp (fixedSchedule c) hA.1 hA.2.1 le_rfl hsharp
    (by positivity) ⟨2 ^ c * 2 ^ (fixedSchedule c).depth (fixedSchedule c).R, by push_cast; rfl⟩
    (hC.trans (fixedSchedule_psiSharp_ge c))
  rwa [GameSchedule.budget_R] at hwin

/-- The height bounds along the fixed schedule: `H_j ≤ 2^{(2j + 1)(c + 2) + 3}` for `j ≤ R`
(`H_0 = 0`, and the step `H_{j+1} ≤ H_j + 2^{(2j + 3)(c + 2) + 2}` at most doubles the larger
summand, `(2j + 1)(c + 2) + 3 ≤ (2j + 3)(c + 2) + 2`).
Blueprint 04 Corollary fixed-game-bounds, (FH). -/
private theorem fixedSchedule_heightBound_le_of_le (c : ℕ) {j : ℕ}
    (hj : j ≤ (fixedSchedule c).R) :
    (fixedSchedule c).heightBound j ≤ 2 ^ ((2 * j + 1) * (c + 2) + 3) := by
  induction j with
  | zero => simp [GameSchedule.heightBound]
  | succ j ih =>
    have hstep := fixedSchedule_heightBound_step c (j := j + 1) (by omega) hj
    have ih := ih (by omega)
    rw [fixedSchedule_R] at hj
    rw [Nat.add_sub_cancel, fixedSchedule_exp_of_le c (by omega),
      show c + 2 + 2 * ((j + 1) * (c + 2) + 1) = (2 * j + 1) * (c + 2) + 3 + (2 * c + 3) by ring]
      at hstep
    rw [show (2 * (j + 1) + 1) * (c + 2) + 3 = (2 * j + 1) * (c + 2) + 3 + (2 * c + 3) + 1 by ring,
      pow_succ]
    have hmono : 2 ^ ((2 * j + 1) * (c + 2) + 3) ≤ 2 ^ ((2 * j + 1) * (c + 2) + 3 + (2 * c + 3)) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

/-- FH: the game height of the fixed schedule is
`H_R ≤ Σ_{j=1}^R 2^{g + 2E_{j-1}} ≤ 2^{(2R+1)g + 3} = 2^{(2^{c+3} + 1)(c + 2) + 3}`; here
`g + 2E_{j-1} = (2j + 1)g + 2`, consecutive summands have ratio `2^{2g}`, so the finite sum is
at most twice its last term.
Blueprint 04 Corollary fixed-game-bounds, (FH) (`04-FIXED-GAME-BOUNDS`). -/
theorem fixedSchedule_heightBound_le (c : ℕ) :
    (fixedSchedule c).heightBound (fixedSchedule c).R ≤ 2 ^ ((2 ^ (c + 3) + 1) * (c + 2) + 3) := by
  have h := fixedSchedule_heightBound_le_of_le c (le_refl (fixedSchedule c).R)
  rw [fixedSchedule_R] at h ⊢
  rwa [show 2 * 2 ^ (c + 2) = 2 ^ (c + 3) by ring] at h

/-! ### The T3 word family and the W1/W2 bridge (02 §8, 04 §8) -/

/-- The T3 word family: for the tag `c`, the strategy `localStrategy (fixedSchedule c) R (2^c)`
played in the word game `G_c` through the palette translation of LEM-SHADOW with `cap = c` (a
reply padded with zeros to `n + c` bits addresses a depth-`n` cell of the board `[0, 2^c)`: its
first `c` bits select one of the `2^c` palettes).
Blueprint 02 §8 with LEM-SHADOW ("the exact quantitative finite-game input to the T3
diagonalization") (`02-T3-WORD-FAMILY`). -/
def fixedWordFamily (c : ℕ) : WordStrategy :=
  wordStrategyOfLocal c (fixedSchedule c).depthOfExp
    (localStrategy (fixedSchedule c) (fixedSchedule c).R (2 ^ c))

/-- On the exponents of the fixed schedule the prescribed Bob depth is the exponent itself: its
exponent and depth lists coincide (`E_j = δ_j`). Blueprint 02 §8 (`δ(n) = n` on the exponents). -/
private theorem depthOfExp_fixedSchedule_eq_self {c n : ℕ} (hn : n ∈ (fixedSchedule c).exps) :
    (fixedSchedule c).depthOfExp n = n := by
  have hd : (fixedSchedule c).depths = (fixedSchedule c).exps := rfl
  unfold GameSchedule.depthOfExp GameSchedule.depth
  rw [hd, List.getD_eq_getElem _ _ (List.idxOf_lt_length_iff.2 hn), List.getElem_idxOf]

/-- The T3 word family wins `G_c` uniformly in the tag: for every `c`, `fixedWordFamily c` is a
winning word strategy for the reply bound `b c n = n + c` within the request bound `T_R` of the
fixed schedule — every request has a positive exponent and a fresh vertex, every path load
including the pending request is at most one, and no legal history answers `T_R` requests.
From GAME-FIXED and LEM-SHADOW with `hS := fixedSchedule_isValid` (`δ(n) = n` on the exponents).
Blueprint 02 §8 and 04 Interface GAME-FIXED ("wins in `G_c` when `C = 2^c`")
(`02-T3-WORD-FAMILY`). -/
theorem fixedWordFamily_winning :
    IsWinningWordFamily (fun c n => n + c) fixedWordFamily fun c =>
      (fixedSchedule c).requestBound (fixedSchedule c).R := fun c =>
  wordStrategyOfLocal_winning (fixedSchedule_isValid c) (fixedSchedule_wins c)
    fun n hn => by rw [depthOfExp_fixedSchedule_eq_self hn]

/-- The fixed schedule is primitive recursive in the tag: both lists are the image of
`List.range (2^{c+2} + 1)` under the primitive recursive map `j ↦ (j + 1)·(c + 2) + 1`.
Blueprint 02 LEM-EFF-02 for the fixed schedules (`02-T3-WORD-FAMILY`). -/
private theorem primrec_fixedSchedule : Primrec fixedSchedule := by
  have hl : Primrec fun c : ℕ =>
      (List.range (2 ^ (c + 2) + 1)).map fun j => (j + 1) * (c + 2) + 1 :=
    Primrec.list_map (Primrec.list_range.comp (Primrec.succ.comp
      (nat_pow_primrec₂.comp (Primrec.const 2) (Primrec.nat_add.comp Primrec.id
        (Primrec.const 2)))))
      ((Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.succ.comp Primrec.snd)
        (Primrec.nat_add.comp Primrec.fst (Primrec.const 2)))).of_eq fun _ => rfl)
  exact ((Primrec.of_equiv_symm (e := GameSchedule.equivProd)).comp (hl.pair hl)).of_eq
    fun _ => rfl

/-- The T3 word family is computable uniformly in the tag and the history: one algorithm
computes `(c, h) ↦ fixedWordFamily c h` (the schedule is a primitive recursive list, the
strategy is computable by LEM-EFF-02, the palette translation is primitive recursive).
Blueprint 02 LEM-EFF-02 for the fixed schedules and 03 §6 item 1 (`02-T3-WORD-FAMILY`). -/
theorem fixedWordFamily_computable :
    Computable fun a : ℕ × WordHistory => fixedWordFamily a.1 a.2 := by
  have hR : Primrec fun c : ℕ => (fixedSchedule c).R :=
    (Primrec.nat_sub.comp (Primrec.list_length.comp
      ((Primrec.fst.comp (Primrec.of_equiv (e := GameSchedule.equivProd))).comp
        primrec_fixedSchedule)) (Primrec.const 1)).of_eq fun _ => rfl
  have hU : Computable fun c : ℕ => (2 ^ c : ℚ) :=
    (computable_nat_to_rat.comp comp_pow).of_eq fun _ => by push_cast; rfl
  exact (wordStrategyOfLocal_computable.comp (Computable.fst.pair
    ((primrec_fixedSchedule.to_comp.comp Computable.fst).pair
      ((hR.to_comp.comp Computable.fst).pair ((hU.comp Computable.fst).pair
        Computable.snd))))).of_eq fun _ => rfl

/-- The W1/W2 bridge for the T3 word family: a word-reachable history of `G_c` (reply bound
`n + c`), with its answers read as cells, is a reachable history of the fixed local strategy in
the palette capacity `2^c` (LEM-SHADOW bridge with GAME-FIXED). Blueprint 04 §8 (W1/W2). -/
private theorem reachable_localStrategy_of_fixedWordFamily {c : ℕ} {h : WordHistory}
    (hh : ReachableWordHistory (fun n => n + c) (fixedWordFamily c) h) :
    Reachable (fixedSchedule c) (2 ^ c)
      (localStrategy (fixedSchedule c) (fixedSchedule c).R (2 ^ c))
      (h.map fun e => (e.1, wordToCell c ((fixedSchedule c).depthOfExp e.1.2) e.2)) :=
  reachable_of_reachableWordHistory (fixedSchedule_isValid c) (fixedSchedule_wins c)
    (fun n hn => by rw [depthOfExp_fixedSchedule_eq_self hn]) hh

/-- W1 bridge: at every word-reachable history of `G_c` (reply bound `n + c`) the exponent
requested by the T3 word family is at most `E_R = (2^{c+2} + 1)·(c + 2) + 1`: the history is,
through `reachable_of_reachableWordHistory`, a reachable local history, so the request is allowed
at level `R` (`GameSchedule.le_exp_of_requestAllowed`), and FE.
Blueprint 04 §8, (W1) exponent bound from GAME-FIXED (`04-W1-W2-BRIDGE`). -/
theorem fixedWordFamily_exp_le {c : ℕ} {h : WordHistory}
    (hh : ReachableWordHistory (fun n => n + c) (fixedWordFamily c) h) :
    (fixedWordFamily c h).2 ≤ (2 ^ (c + 2) + 1) * (c + 2) + 1 := by
  have hle := GameSchedule.le_exp_of_requestAllowed (fixedSchedule_isValid c) le_rfl
    ((fixedSchedule_wins c) _ (reachable_localStrategy_of_fixedWordFamily hh)).2.1
  rw [fixedSchedule_exp_R] at hle
  exact hle

/-- W2 bridge: at every word-reachable history of `G_c` (reply bound `n + c`) the vertex
requested by the T3 word family has length at most `2^{(2^{c+3} + 1)(c + 2) + 3}`: the height
bound of LEM-EFF-01 (`localStrategy_length_le`, applicable by `fixedSchedule_psi_ge`) on the
local history given by `reachable_of_reachableWordHistory`, and FH. The tag length `c + 1` of
W2 is added by the diagonalization.
Blueprint 04 §8, (W2) height bound from GAME-FIXED (`04-W1-W2-BRIDGE`). -/
theorem fixedWordFamily_length_le {c : ℕ} {h : WordHistory}
    (hh : ReachableWordHistory (fun n => n + c) (fixedWordFamily c) h) :
    (fixedWordFamily c h).1.length ≤ 2 ^ ((2 ^ (c + 3) + 1) * (c + 2) + 3) := by
  have hlen := localStrategy_length_le (fixedSchedule c) (fixedSchedule_isAdmissibleSharp c).1
    le_rfl (by positivity)
    ⟨2 ^ c * 2 ^ (fixedSchedule c).depth (fixedSchedule c).R, by push_cast; rfl⟩
    (fixedSchedule_psi_ge c) _ (reachable_localStrategy_of_fixedWordFamily hh)
  exact hlen.trans (fixedSchedule_heightBound_le c)

end Kolmogorov
