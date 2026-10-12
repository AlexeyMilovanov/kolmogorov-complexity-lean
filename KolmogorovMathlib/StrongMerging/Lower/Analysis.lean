import KolmogorovMathlib.StrongMerging.Lower.Hypercontractivity
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# The sharp lower bound: entropy, binomial and distance-count estimates

Blueprint nodes L10 (`entropyAndBinomialBounds`), L12 (`binomialModeMass`) and L13
(`distanceCountFromSSE`) of the formalization of `sublinear-merging.tex` (main text
"Near-equator parameters and uniform entropy estimates", tex lines 1530-1570, and
`lem:ham-hypercontractive-distance`, lines 1852-1890; appendix lines 4477-4605).

* **L12.**  At `q = i / M` the integer `i` is a mode of `Binomial(M, q)`, and its mass is at
  least `1 / (M + 1)`.
* **L10.**  With binary entropy in bits `binEntropy2 = Real.binEntropy / log 2` (the library's
  `Real.binEntropy` uses natural logarithms): the one-sided entropy bounds
  `eq:ham-entropy-estimate`, the binomial-entropy bounds `eq:ham-binomial-estimate`,
  `(L / k)^k ≤ (L choose k)`, the equator entropy deficit `2 α² log e ≤ 1 - h(1/2 - α) ≤ 4 α²`,
  and the ball volume bound `log V(M, h - 1) ≤ h log(e M / h)`.
* **L13.**  The ordered distance-`i` count
  `#{(u, v) ∈ U² : dist(u, v) = i} ≤ |U| (M + 1) (M choose i) μ^(i/(M-i))` from small-set
  expansion (L11), and its consequence `eq:ham-hypercontractive-small-support`.
-/

namespace Kolmogorov.StrongMerging.Lower

open Finset

/-! ### L12: the binomial mode -/

/-- The binomial weight `P[Binomial(M, q) = k] = (M choose k) q^k (1 - q)^(M - k)`. -/
noncomputable def binomPmf (M k : ℕ) (q : ℝ) : ℝ :=
  M.choose k * q ^ k * (1 - q) ^ (M - k)

/-- **The binomial weights sum to one.**

Proof sketch: `add_pow` for `(q + (1 - q))^M = 1^M = 1`, `mul_comm` inside the sum.
Reference: tex 1543-1545; node L12.  [leaf: easy] -/
theorem sum_binomPmf (M : ℕ) (q : ℝ) : ∑ k ∈ range (M + 1), binomPmf M k q = 1 := by
  have h : (q + (1 - q)) ^ M = 1 := by rw [add_sub_cancel, one_pow]
  rw [add_pow] at h
  rw [← h]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [binomPmf]
  ring

/-- **Below the mode the binomial weights increase**: for `j < i ≤ M` and `q = i / M`,
`P[= j] ≤ P[= j + 1]`.

Proof sketch: if `i = M` then `q = 1` and `P[= j] = 0` (`zero_pow`, `M - j > 0`).  Otherwise
`0 < q < 1`; by `Nat.choose_succ_right_eq`, `(j + 1) (M choose (j+1)) = (M - j) (M choose j)`, so
the claim is `(j + 1) (1 - q) ≤ (M - j) q`, i.e. `(j + 1)(M - i) ≤ (M - j) i`, i.e.
`M (j + 1) ≤ i (M + 1)`, true since `j + 1 ≤ i`.
Reference: tex 1543-1545 ("k is a mode"), 4588-4590; node L12.  [leaf: medium] -/
theorem binomPmf_le_succ_of_lt (M i j : ℕ) (hi : i ≤ M) (hj : j < i) :
    binomPmf M j ((i : ℝ) / M) ≤ binomPmf M (j + 1) ((i : ℝ) / M) := by
  have hM : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hqM : (i : ℝ) / M * M = i := div_mul_cancel₀ _ hM.ne'
  have hq0 : (0 : ℝ) ≤ (i : ℝ) / M := by positivity
  have hq1 : (i : ℝ) / M ≤ 1 := div_le_one_of_le₀ (by exact_mod_cast hi) hM.le
  have hji : (j : ℝ) + 1 ≤ i := by exact_mod_cast hj
  have hrel : (M.choose (j + 1) : ℝ) * (j + 1) = M.choose j * ((M : ℝ) - j) := by
    rw [← Nat.cast_sub (by omega)]
    exact_mod_cast Nat.choose_succ_right_eq M j
  have hjM : M - j = M - (j + 1) + 1 := by omega
  unfold binomPmf
  rw [hjM, pow_succ, pow_succ]
  generalize (i : ℝ) / M = q at hqM hq0 hq1 ⊢
  have hlin : (1 - q) * (j + 1) ≤ ((M : ℝ) - j) * q := by linarith
  have hj1 : (0 : ℝ) < j + 1 := by positivity
  have hc0 : (0 : ℝ) ≤ M.choose j := Nat.cast_nonneg _
  have key : (M.choose j : ℝ) * (1 - q) ≤ M.choose (j + 1) * q := by
    refine le_of_mul_le_mul_right ?_ hj1
    calc (M.choose j : ℝ) * (1 - q) * (j + 1) = M.choose j * ((1 - q) * (j + 1)) := by ring
      _ ≤ M.choose j * (((M : ℝ) - j) * q) := mul_le_mul_of_nonneg_left hlin hc0
      _ = M.choose (j + 1) * q * (j + 1) := by rw [← mul_assoc, ← hrel]; ring
  have hp : 0 ≤ q ^ j * (1 - q) ^ (M - (j + 1)) :=
    mul_nonneg (pow_nonneg hq0 _) (pow_nonneg (sub_nonneg.2 hq1) _)
  linarith [mul_le_mul_of_nonneg_left key hp]

/-- **Above the mode the binomial weights decrease**: for `i ≤ j < M` and `q = i / M`,
`P[= j + 1] ≤ P[= j]`.

Proof sketch: if `i = 0` then `q = 0` and `P[= j + 1] = 0`.  Otherwise `0 < q < 1` and, as in
`binomPmf_le_succ_of_lt`, the claim is `(M - j) i ≤ (j + 1)(M - i)`, i.e.
`i (M + 1) ≤ M (j + 1)`, true since `i ≤ j` and `i ≤ M`.
Reference: tex 1543-1545, 4588-4590; node L12.  [leaf: medium] -/
theorem binomPmf_succ_le_of_le (M i j : ℕ) (hij : i ≤ j) (hj : j < M) :
    binomPmf M (j + 1) ((i : ℝ) / M) ≤ binomPmf M j ((i : ℝ) / M) := by
  have hM : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hqM : (i : ℝ) / M * M = i := div_mul_cancel₀ _ hM.ne'
  have hq0 : (0 : ℝ) ≤ (i : ℝ) / M := by positivity
  have hq1 : (i : ℝ) / M ≤ 1 := div_le_one_of_le₀ (by exact_mod_cast (by omega : i ≤ M)) hM.le
  have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij
  have hrel : (M.choose (j + 1) : ℝ) * (j + 1) = M.choose j * ((M : ℝ) - j) := by
    rw [← Nat.cast_sub (by omega)]
    exact_mod_cast Nat.choose_succ_right_eq M j
  have hjM : M - j = M - (j + 1) + 1 := by omega
  unfold binomPmf
  rw [hjM, pow_succ, pow_succ]
  generalize (i : ℝ) / M = q at hqM hq0 hq1 ⊢
  have hlin : ((M : ℝ) - j) * q ≤ (1 - q) * (j + 1) := by linarith
  have hj1 : (0 : ℝ) < j + 1 := by positivity
  have hc0 : (0 : ℝ) ≤ M.choose j := Nat.cast_nonneg _
  have key : (M.choose (j + 1) : ℝ) * q ≤ M.choose j * (1 - q) := by
    refine le_of_mul_le_mul_right ?_ hj1
    calc (M.choose (j + 1) : ℝ) * q * (j + 1) = M.choose (j + 1) * (j + 1) * q := by ring
      _ = M.choose j * (((M : ℝ) - j) * q) := by rw [hrel]; ring
      _ ≤ M.choose j * ((1 - q) * (j + 1)) := mul_le_mul_of_nonneg_left hlin hc0
      _ = M.choose j * (1 - q) * (j + 1) := by ring
  have hp : 0 ≤ q ^ j * (1 - q) ^ (M - (j + 1)) :=
    mul_nonneg (pow_nonneg hq0 _) (pow_nonneg (sub_nonneg.2 hq1) _)
  linarith [mul_le_mul_of_nonneg_left key hp]

/-- **`i` is a mode of `Binomial(M, i / M)`**: for `i ≤ M` and every `k ≤ M`,
`P[= k] ≤ P[= i]` at `q = i / M` (with `0⁰ = 1` at the endpoints). -/
theorem binomPmf_le_mode (M i k : ℕ) (hi : i ≤ M) (hk : k ≤ M) :
    binomPmf M k ((i : ℝ) / M) ≤ binomPmf M i ((i : ℝ) / M) := by
  rcases le_total k i with hki | hik
  · have up : ∀ j, k ≤ j → j ≤ i →
        binomPmf M k ((i : ℝ) / M) ≤ binomPmf M j ((i : ℝ) / M) := by
      intro j hkj
      induction j, hkj using Nat.le_induction with
      | base => exact fun _ => le_rfl
      | succ j hkj ih =>
        intro hj
        exact (ih (by omega)).trans (binomPmf_le_succ_of_lt M i j hi (by omega))
    exact up i hki le_rfl
  · have down : ∀ j, i ≤ j → j ≤ M →
        binomPmf M j ((i : ℝ) / M) ≤ binomPmf M i ((i : ℝ) / M) := by
      intro j hij
      induction j, hij using Nat.le_induction with
      | base => exact fun _ => le_rfl
      | succ j hij ih =>
        intro hj
        exact (binomPmf_succ_le_of_le M i j hij (by omega)).trans (ih (by omega))
    exact down k hik hk

/-- **Binomial mode mass** (blueprint node L12).  For `i ≤ M` and `q = i / M`: `i` is a mode of
`Binomial(M, q)`, and its mass is at least `1 / (M + 1)`. -/
theorem binomialModeMass (M i : ℕ) (hi : i ≤ M) :
    (∀ k ≤ M, binomPmf M k ((i : ℝ) / M) ≤ binomPmf M i ((i : ℝ) / M)) ∧
      1 / ((M : ℝ) + 1) ≤ binomPmf M i ((i : ℝ) / M) := by
  refine ⟨fun k hk => binomPmf_le_mode M i k hi hk, ?_⟩
  have hle : ∑ k ∈ range (M + 1), binomPmf M k ((i : ℝ) / M) ≤
      ∑ _k ∈ range (M + 1), binomPmf M i ((i : ℝ) / M) :=
    Finset.sum_le_sum fun k hk =>
      binomPmf_le_mode M i k hi (Nat.lt_succ_iff.mp (mem_range.mp hk))
  rw [sum_binomPmf, Finset.sum_const, card_range, nsmul_eq_mul] at hle
  rw [div_le_iff₀ (by positivity), mul_comm]
  exact_mod_cast hle

/-! ### L10: entropy and binomial estimates -/

/-- Binary entropy in bits, `h(z) = -z log₂ z - (1 - z) log₂ (1 - z)`, with `0 log 0 = 0`. -/
noncomputable def binEntropy2 (z : ℝ) : ℝ :=
  Real.binEntropy z / Real.log 2

/-- **Natural-log upper bound for the second entropy term**: `-(1 - z) ln(1 - z) ≤ z` on
`[0, 1]`.

Proof sketch: for `z < 1`, `Real.one_sub_inv_le_log_of_pos` gives
`ln(1 - z) ≥ 1 - 1/(1 - z) = -z/(1 - z)`; multiply by `1 - z > 0`.  At `z = 1` the left side
is `0` (`Real.log_zero`).
Reference: tex 1532-1540 (`eq:ham-entropy-estimate`); node L10.  [leaf: easy] -/
theorem neg_one_sub_mul_log_one_sub_le {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    -((1 - z) * Real.log (1 - z)) ≤ z := by
  rcases eq_or_lt_of_le hz1 with rfl | hz1'
  · simp
  · have hx : 0 < 1 - z := by linarith
    have h := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos hx) hx.le
    rw [mul_sub, mul_one, mul_inv_cancel₀ hx.ne'] at h
    linarith

/-- **Natural-log lower bound for the second entropy term**: `z - z² ≤ -(1 - z) ln(1 - z)` on
`[0, 1]`.

Proof sketch: `Real.log_le_sub_one_of_pos` gives `ln(1 - z) ≤ -z` for `z < 1`; multiply by
`-(1 - z) ≤ 0`.  At `z = 1` both sides are `0`.
Reference: tex 1532-1540; node L10.  [leaf: easy] -/
theorem le_neg_one_sub_mul_log_one_sub {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    z - z ^ 2 ≤ -((1 - z) * Real.log (1 - z)) := by
  rcases eq_or_lt_of_le hz1 with rfl | hz1'
  · simp
  · have hx : 0 < 1 - z := by linarith
    have h := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hx) hx.le
    nlinarith

/-- **Entropy in bits, split**: `h(z) = z log₂(1/z) + (-(1 - z) ln(1 - z)) log₂ e`.

Proof sketch: unfold `binEntropy2`, `Real.binEntropy`; `Real.logb`, `one_div`,
`Real.log_inv`, `Real.log_exp`; `field_simp`/`ring`.  Valid for all real `z`.
Reference: tex 1532-1540; node L10.  [leaf: easy] -/
theorem binEntropy2_eq (z : ℝ) :
    binEntropy2 z = z * Real.logb 2 (1 / z) +
      -((1 - z) * Real.log (1 - z)) * Real.logb 2 (Real.exp 1) := by
  rw [binEntropy2, Real.binEntropy, Real.logb, Real.logb, Real.log_exp, one_div]
  simp only [Real.log_inv]
  ring

/-- **One-sided entropy bounds** (`eq:ham-entropy-estimate`): for `0 ≤ z ≤ 1`,
`z log(1/z) + z log e - z² log e ≤ h(z) ≤ z log(1/z) + z log e` (logs base 2). -/
theorem binEntropy2_bounds {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    z * Real.logb 2 (1 / z) + z * Real.logb 2 (Real.exp 1) -
        z ^ 2 * Real.logb 2 (Real.exp 1) ≤ binEntropy2 z ∧
      binEntropy2 z ≤ z * Real.logb 2 (1 / z) + z * Real.logb 2 (Real.exp 1) := by
  have hexp : 1 < Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hc : 0 < Real.logb 2 (Real.exp 1) := Real.logb_pos one_lt_two hexp
  rw [binEntropy2_eq]
  have h1 := mul_le_mul_of_nonneg_right (neg_one_sub_mul_log_one_sub_le hz0 hz1) hc.le
  have h2 := mul_le_mul_of_nonneg_right (le_neg_one_sub_mul_log_one_sub hz0 hz1) hc.le
  constructor
  · nlinarith [h2]
  · nlinarith [h1]

/-- **The binomial weight at its mean in entropy form**: for `k ≤ L` and `p = k / L`,
`p^k (1 - p)^(L - k) = 2^(-L h(p))` (with `0⁰ = 1`; both sides are `1` when `k ∈ {0, L}`).

Proof sketch: if `k = 0` or `k = L` (including `L = 0`), `h(p) = 0` (`Real.binEntropy_zero`,
`Real.binEntropy_one`) and both sides are `1`.  Otherwise `0 < p < 1`; take `Real.logb 2` of
the left side: `k log₂ p + (L - k) log₂ (1 - p) = L (p log₂ p + (1 - p) log₂ (1 - p))`
(`Nat.cast_sub`, `k = L p`), then `Real.rpow_logb`/`Real.logb_rpow`.
Reference: tex 1541-1546 (`eq:ham-binomial-estimate`); node L10.  [leaf: medium] -/
theorem pow_mul_pow_eq_two_rpow (L k : ℕ) (hk : k ≤ L) :
    ((k : ℝ) / L) ^ k * (1 - (k : ℝ) / L) ^ (L - k) =
      (2 : ℝ) ^ (-((L : ℝ) * binEntropy2 ((k : ℝ) / L))) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp [binEntropy2]
  rcases eq_or_lt_of_le hk with hkL | hkL
  · subst hkL
    have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk0.ne'
    simp [div_self hk', binEntropy2]
  have hL : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hp0 : (0 : ℝ) < (k : ℝ) / L := by positivity
  have hp1 : (k : ℝ) / L < 1 := (div_lt_one hL).2 (by exact_mod_cast hkL)
  have hLp : (L : ℝ) * ((k : ℝ) / L) = k := mul_div_cancel₀ _ hL.ne'
  have hcast : ((L - k : ℕ) : ℝ) = L - k := Nat.cast_sub hk
  have hl2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  generalize (k : ℝ) / L = p at hp0 hp1 hLp ⊢
  have h1p : 0 < 1 - p := by linarith
  rw [← Real.exp_log (mul_pos (pow_pos hp0 k) (pow_pos h1p (L - k))),
    Real.rpow_def_of_pos two_pos, binEntropy2]
  congr 1
  have e2 : Real.log 2 * -(↑L * (Real.binEntropy p / Real.log 2)) =
      -(↑L * Real.binEntropy p) := by
    field_simp
  rw [e2, Real.log_mul (pow_pos hp0 k).ne' (pow_pos h1p (L - k)).ne', Real.log_pow,
    Real.log_pow, hcast, Real.binEntropy, Real.log_inv, Real.log_inv]
  linear_combination (Real.log (1 - p) - Real.log p) * hLp

/-- **A binomial weight is at most one**: `binomPmf L k q ≤ 1` for `0 ≤ q ≤ 1`.

Proof sketch: it is one nonnegative term of `sum_binomPmf` when `k ≤ L`
(`single_le_sum`), and `0` otherwise (`Nat.choose_eq_zero_of_lt`).
Reference: tex 1541-1546; node L10.  [leaf: easy] -/
theorem binomPmf_le_one (L k : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    binomPmf L k q ≤ 1 := by
  rcases le_or_gt k L with hk | hk
  · rw [← sum_binomPmf L q]
    exact Finset.single_le_sum (f := fun j => binomPmf L j q)
      (fun j _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hq0 _))
        (pow_nonneg (sub_nonneg.mpr hq1) _))
      (mem_range.mpr (Nat.lt_succ_of_le hk))
  · rw [binomPmf, Nat.choose_eq_zero_of_lt hk]
    simp

/-- **Binomial-entropy bounds** (`eq:ham-binomial-estimate`): for `k ≤ L`,
`L h(k/L) - log₂(L + 1) ≤ log₂ (L choose k) ≤ L h(k/L)`. -/
theorem log_choose_bounds (L k : ℕ) (hk : k ≤ L) :
    (L : ℝ) * binEntropy2 ((k : ℝ) / L) - Real.logb 2 ((L : ℝ) + 1) ≤
        Real.logb 2 (L.choose k) ∧
      Real.logb 2 (L.choose k) ≤ (L : ℝ) * binEntropy2 ((k : ℝ) / L) := by
  have hw := pow_mul_pow_eq_two_rpow L k hk
  have hpmf : binomPmf L k ((k : ℝ) / L) =
      L.choose k * (2 : ℝ) ^ (-((L : ℝ) * binEntropy2 ((k : ℝ) / L))) := by
    rw [binomPmf, mul_assoc, hw]
  have hC : (0 : ℝ) < L.choose k := by exact_mod_cast Nat.choose_pos hk
  have hq0 : (0 : ℝ) ≤ (k : ℝ) / L := by positivity
  have hq1 : (k : ℝ) / L ≤ 1 := div_le_one_of_le₀ (by exact_mod_cast hk) (by positivity)
  have hup := binomPmf_le_one L k hq0 hq1
  have hlow := (binomialModeMass L k hk).2
  rw [hpmf] at hup hlow
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ (-((L : ℝ) * binEntropy2 ((k : ℝ) / L))) := by positivity
  constructor
  · have h := Real.logb_le_logb_of_le one_lt_two (by positivity) hlow
    rw [Real.logb_mul hC.ne' h2pos.ne', Real.logb_rpow two_pos one_lt_two.ne', one_div,
      Real.logb_inv] at h
    linarith
  · have h := Real.logb_le_logb_of_le one_lt_two (mul_pos hC h2pos) hup
    rw [Real.logb_mul hC.ne' h2pos.ne', Real.logb_rpow two_pos one_lt_two.ne',
      Real.logb_one] at h
    linarith

/-- **Lower product estimate** `(L / k)^k ≤ (L choose k)` for `1 ≤ k ≤ L`.

Proof sketch: `(L choose k) = ∏_{j < k} (L - j) / (k - j)`
(`Nat.choose_eq_descFactorial_div_factorial`, `Nat.descFactorial`), and
`(L - j) / (k - j) ≥ L / k` for `j < k ≤ L`
(cross-multiply: `k (L - j) ≥ L (k - j)` iff `j (L - k) ≥ 0`); `Finset.prod_le_prod`.
Reference: tex 1546-1547; node L10.  [leaf: medium] -/
theorem pow_div_le_choose (L k : ℕ) (hk1 : 1 ≤ k) (hkL : k ≤ L) :
    ((L : ℝ) / k) ^ k ≤ L.choose k := by
  have hprod : ∀ m, m ≤ k → L ^ m * k.descFactorial m ≤ k ^ m * L.descFactorial m := by
    intro m hm
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Nat.descFactorial_succ, Nat.descFactorial_succ, pow_succ, pow_succ]
      have h2 : L * (k - m) ≤ k * (L - m) := by
        have hmk : m ≤ k := by omega
        have hmL : m ≤ L := by omega
        zify [hmk, hmL]
        nlinarith [mul_le_mul_of_nonneg_right (show (k : ℤ) ≤ L by exact_mod_cast hkL)
          (show (0 : ℤ) ≤ m by positivity)]
      calc L ^ m * L * ((k - m) * k.descFactorial m)
          = (L ^ m * k.descFactorial m) * (L * (k - m)) := by ring
        _ ≤ (k ^ m * L.descFactorial m) * (k * (L - m)) := Nat.mul_le_mul (ih (by omega)) h2
        _ = k ^ m * k * ((L - m) * L.descFactorial m) := by ring
  have hfin : L ^ k ≤ L.choose k * k ^ k := by
    have h := hprod k le_rfl
    rw [Nat.descFactorial_self, Nat.descFactorial_eq_factorial_mul_choose] at h
    refine Nat.le_of_mul_le_mul_right (c := k.factorial) ?_ (Nat.factorial_pos k)
    calc L ^ k * k.factorial ≤ k ^ k * (k.factorial * L.choose k) := h
      _ = L.choose k * k ^ k * k.factorial := by ring
  have hkpos : (0 : ℝ) < (k : ℝ) ^ k := pow_pos (Nat.cast_pos.2 (by omega)) k
  rw [div_pow, div_le_iff₀ hkpos]
  exact_mod_cast hfin

/-- The natural-log equator deficit `D(α) = ln 2 - H(1/2 - α)`, `H = Real.binEntropy`. -/
noncomputable def equatorDeficit (α : ℝ) : ℝ :=
  Real.log 2 - Real.binEntropy (1 / 2 - α)

/-- The equator deficit is continuous.

Proof sketch: `Real.binEntropy_continuous` composed with `α ↦ 1/2 - α` (`fun_prop`).
Reference: tex 1559-1567; node L10.  [leaf: easy] -/
theorem continuous_equatorDeficit : Continuous equatorDeficit := by
  unfold equatorDeficit
  fun_prop

/-- The derivative of the equator deficit: `D'(α) = ln(1/2 + α) - ln(1/2 - α)` for
`-1/2 < α < 1/2`.

Proof sketch: `Real.hasDerivAt_binEntropy` at `p = 1/2 - α ∉ {0, 1}` gives the derivative
`ln(1 - p) - ln p`; compose with `α ↦ 1/2 - α` (`HasDerivAt.comp`, `hasDerivAt_id`,
`HasDerivAt.const_sub`), negate and add the constant `ln 2`; `1 - (1/2 - α) = 1/2 + α` (`ring`).
Reference: tex 1559-1563 ("integrating its derivative"); node L10.  [leaf: easy] -/
theorem hasDerivAt_equatorDeficit {α : ℝ} (h0 : -(1 / 2) < α) (h1 : α < 1 / 2) :
    HasDerivAt equatorDeficit (Real.log (1 / 2 + α) - Real.log (1 / 2 - α)) α := by
  have hp0 : (1 / 2 - α) ≠ 0 := by linarith
  have hp1 : (1 / 2 - α) ≠ 1 := by linarith
  have h := ((Real.hasDerivAt_binEntropy hp0 hp1).comp_const_sub (1 / 2) α).const_sub
    (Real.log 2)
  rw [show (1 : ℝ) - (1 / 2 - α) = 1 / 2 + α by ring, neg_neg] at h
  exact h

/-- **Second-order lower bound for `log(1 + x)`**: `x - x²/2 ≤ ln(1 + x)` for `x ≥ 0`.

Proof sketch: `f(x) = ln(1 + x) - x + x²/2` has `f(0) = 0` and `f'(x) = x² / (1 + x) ≥ 0`
(`Real.hasDerivAt_log`, chain rule); apply `nonneg_of_hasDerivAt_nonneg` on `[0, x]`
(`Real.continuousOn_log` away from `0`).
Reference: tex 1559-1563; node L10.  [leaf: easy] -/
theorem sub_sq_div_two_le_log_one_add {x : ℝ} (hx : 0 ≤ x) :
    x - x ^ 2 / 2 ≤ Real.log (1 + x) := by
  have hd : ∀ y : ℝ, 0 ≤ y → HasDerivAt (fun a : ℝ => Real.log (1 + a) - (a - a ^ 2 / 2))
      (1 / (1 + y) - (1 - y)) y := by
    intro y hy
    have h := (((hasDerivAt_id' y).const_add 1).log (by linarith)).sub
      ((hasDerivAt_id' y).sub ((hasDerivAt_pow 2 y).div_const 2))
    convert h using 1
    norm_num
  have key : 0 ≤ Real.log (1 + x) - (x - x ^ 2 / 2) :=
    nonneg_of_hasDerivAt_nonneg (f := fun a => Real.log (1 + a) - (a - a ^ 2 / 2))
      (f' := fun y => 1 / (1 + y) - (1 - y)) (a := 0) (b := x)
      (fun y hy => (hd y hy.1).continuousAt.continuousWithinAt)
      (fun y hy => hd y hy.1.le)
      (fun y hy => by
        show 0 ≤ 1 / (1 + y) - (1 - y)
        have h1y : 0 < 1 + y := by linarith [hy.1]
        rw [sub_nonneg, le_div_iff₀ h1y]
        nlinarith [sq_nonneg y])
      (by simp) x ⟨hx, le_rfl⟩
  linarith

/-- **Second-order lower bound for `-log(1 - x)`**: `x + x²/2 ≤ -ln(1 - x)` for `0 ≤ x < 1`.

Proof sketch: `f(t) = -ln(1 - t) - t - t²/2` has `f(0) = 0` and `f'(t) = t² / (1 - t) ≥ 0` on
`[0, 1)`; apply `nonneg_of_hasDerivAt_nonneg` on `[0, x]`.
Reference: tex 1559-1563; node L10.  [leaf: easy] -/
theorem add_sq_div_two_le_neg_log_one_sub {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    x + x ^ 2 / 2 ≤ -Real.log (1 - x) := by
  have hd : ∀ y : ℝ, y < 1 → HasDerivAt (fun a : ℝ => -Real.log (1 - a) - (a + a ^ 2 / 2))
      (1 / (1 - y) - (1 + y)) y := by
    intro y hy
    have h := (((hasDerivAt_id' y).const_sub 1).log (by linarith)).neg.sub
      ((hasDerivAt_id' y).add ((hasDerivAt_pow 2 y).div_const 2))
    convert h using 1
    rw [neg_div, neg_neg]
    norm_num
  have key : 0 ≤ -Real.log (1 - x) - (x + x ^ 2 / 2) :=
    nonneg_of_hasDerivAt_nonneg (f := fun a => -Real.log (1 - a) - (a + a ^ 2 / 2))
      (f' := fun y => 1 / (1 - y) - (1 + y)) (a := 0) (b := x)
      (fun y hy => (hd y (by linarith [hy.2])).continuousAt.continuousWithinAt)
      (fun y hy => hd y (by linarith [hy.2]))
      (fun y hy => by
        show 0 ≤ 1 / (1 - y) - (1 + y)
        have h1y : 0 < 1 - y := by linarith [hy.2]
        rw [sub_nonneg, le_div_iff₀ h1y]
        nlinarith [sq_nonneg y])
      (by simp) x ⟨hx0, le_rfl⟩
  linarith

/-- **Lower bound for the derivative**: `4 α ≤ ln(1/2 + α) - ln(1/2 - α)` for
`0 ≤ α < 1/2`; with `x = 2α`, `ln(1 + x) - ln(1 - x) ≥ (x - x²/2) + (x + x²/2) = 2x`. -/
theorem four_mul_le_log_sub_log {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1 / 2) :
    4 * α ≤ Real.log (1 / 2 + α) - Real.log (1 / 2 - α) := by
  have hp : (1 : ℝ) / 2 + α = 1 / 2 * (1 + 2 * α) := by ring
  have hm : (1 : ℝ) / 2 - α = 1 / 2 * (1 - 2 * α) := by ring
  have h2p : (0 : ℝ) < 1 + 2 * α := by linarith
  have h2m : (0 : ℝ) < 1 - 2 * α := by linarith
  rw [hp, hm, Real.log_mul (by norm_num) h2p.ne', Real.log_mul (by norm_num) h2m.ne']
  have a1 := sub_sq_div_two_le_log_one_add (x := 2 * α) (by linarith)
  have a2 := add_sq_div_two_le_neg_log_one_sub (x := 2 * α) (by linarith) (by linarith)
  linarith

/-- **Third-order upper bound for `log(1 + x)`**: `ln(1 + x) ≤ x - x²/2 + x³/3` for `x ≥ 0`.

Proof sketch: `f(x) = x - x²/2 + x³/3 - ln(1 + x)` has `f(0) = 0` and
`f'(x) = x³ / (1 + x) ≥ 0`; apply `nonneg_of_hasDerivAt_nonneg` on `[0, x]`.
Reference: tex 1567-1569; node L10.  [leaf: easy] -/
theorem log_one_add_le_cubic {x : ℝ} (hx : 0 ≤ x) :
    Real.log (1 + x) ≤ x - x ^ 2 / 2 + x ^ 3 / 3 := by
  have hd : ∀ y : ℝ, 0 ≤ y → HasDerivAt
      (fun a : ℝ => a - a ^ 2 / 2 + a ^ 3 / 3 - Real.log (1 + a))
      (1 - y + y ^ 2 - 1 / (1 + y)) y := by
    intro y hy
    have h := (((hasDerivAt_id' y).sub ((hasDerivAt_pow 2 y).div_const 2)).add
      ((hasDerivAt_pow 3 y).div_const 3)).sub
      (((hasDerivAt_id' y).const_add 1).log (by linarith))
    convert h using 1
    norm_num
  have key : 0 ≤ x - x ^ 2 / 2 + x ^ 3 / 3 - Real.log (1 + x) :=
    nonneg_of_hasDerivAt_nonneg (f := fun a => a - a ^ 2 / 2 + a ^ 3 / 3 - Real.log (1 + a))
      (f' := fun y => 1 - y + y ^ 2 - 1 / (1 + y)) (a := 0) (b := x)
      (fun y hy => (hd y hy.1).continuousAt.continuousWithinAt)
      (fun y hy => hd y hy.1.le)
      (fun y hy => by
        show 0 ≤ 1 - y + y ^ 2 - 1 / (1 + y)
        have h1y : 0 < 1 + y := by linarith [hy.1]
        rw [sub_nonneg, div_le_iff₀ h1y]
        nlinarith [pow_nonneg hy.1.le 3])
      (by simp) x ⟨hx, le_rfl⟩
  linarith

/-- **Upper bound for `-log(1 - x)` near zero**: `-ln(1 - x) ≤ x + x²/2 + 2x³/3` for
`0 ≤ x ≤ 1/2`.

Proof sketch: `g(t) = t + t²/2 + 2t³/3 + ln(1 - t)` has `g(0) = 0` and
`g'(t) = t² (1 - 2t) / (1 - t) ≥ 0` on `[0, 1/2]`; apply `nonneg_of_hasDerivAt_nonneg`.
Reference: tex 1567-1569; node L10.  [leaf: easy] -/
theorem neg_log_one_sub_le_cubic {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    -Real.log (1 - x) ≤ x + x ^ 2 / 2 + 2 * x ^ 3 / 3 := by
  have hd : ∀ y : ℝ, y < 1 → HasDerivAt
      (fun a : ℝ => a + a ^ 2 / 2 + 2 * a ^ 3 / 3 + Real.log (1 - a))
      (1 + y + 2 * y ^ 2 - 1 / (1 - y)) y := by
    intro y hy
    have h := (((hasDerivAt_id' y).add ((hasDerivAt_pow 2 y).div_const 2)).add
      (((hasDerivAt_pow 3 y).const_mul 2).div_const 3)).add
      (((hasDerivAt_id' y).const_sub 1).log (by linarith))
    convert h using 1
    norm_num
    ring
  have key : 0 ≤ x + x ^ 2 / 2 + 2 * x ^ 3 / 3 + Real.log (1 - x) :=
    nonneg_of_hasDerivAt_nonneg
      (f := fun a => a + a ^ 2 / 2 + 2 * a ^ 3 / 3 + Real.log (1 - a))
      (f' := fun y => 1 + y + 2 * y ^ 2 - 1 / (1 - y)) (a := 0) (b := x)
      (fun y hy => (hd y (by linarith [hy.2])).continuousAt.continuousWithinAt)
      (fun y hy => hd y (by linarith [hy.2]))
      (fun y hy => by
        show 0 ≤ 1 + y + 2 * y ^ 2 - 1 / (1 - y)
        have h1y : 0 < 1 - y := by linarith [hy.2]
        rw [sub_nonneg, div_le_iff₀ h1y]
        nlinarith [mul_nonneg (sq_nonneg y) (by linarith [hy.2] : (0 : ℝ) ≤ 1 - 2 * y)])
      (by simp) x ⟨hx0, le_rfl⟩
  linarith

/-- **Upper bound for the derivative**: `ln(1/2 + α) - ln(1/2 - α) ≤ (16/3) α` for
`0 ≤ α ≤ 1/4`; with `x = 2α ≤ 1/2`, `ln(1 + x) - ln(1 - x) ≤ 2x + x³ ≤ 8x/3`. -/
theorem log_sub_log_le {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1 / 4) :
    Real.log (1 / 2 + α) - Real.log (1 / 2 - α) ≤ 16 / 3 * α := by
  have hp : (1 : ℝ) / 2 + α = 1 / 2 * (1 + 2 * α) := by ring
  have hm : (1 : ℝ) / 2 - α = 1 / 2 * (1 - 2 * α) := by ring
  have h2p : (0 : ℝ) < 1 + 2 * α := by linarith
  have h2m : (0 : ℝ) < 1 - 2 * α := by linarith
  rw [hp, hm, Real.log_mul (by norm_num) h2p.ne', Real.log_mul (by norm_num) h2m.ne']
  have a1 := log_one_add_le_cubic (x := 2 * α) (by linarith)
  have a2 := neg_log_one_sub_le_cubic (x := 2 * α) (by linarith) (by linarith)
  have hx2 : (2 * α) ^ 2 ≤ 1 / 4 := by nlinarith
  have hx3 : (2 * α) ^ 3 ≤ 2 * α / 4 := by
    have := mul_le_mul_of_nonneg_left hx2 (by linarith : (0 : ℝ) ≤ 2 * α)
    nlinarith [this]
  nlinarith [hx3]

/-- The equator deficit vanishes at the equator: `D(0) = 0`. -/
theorem equatorDeficit_zero : equatorDeficit 0 = 0 := by
  rw [equatorDeficit, sub_zero, one_div, Real.binEntropy_two_inv, sub_self]

/-- The function `a ↦ c a²` has derivative `2 c y` at `y`. -/
theorem hasDerivAt_const_mul_sq (c y : ℝ) :
    HasDerivAt (fun a : ℝ => c * a ^ 2) (2 * c * y) y := by
  have h := (hasDerivAt_pow 2 y).const_mul c
  convert h using 1
  norm_num
  ring

/-- **Equator deficit, lower bound, natural logs**: `2 α² ≤ ln 2 - H(1/2 - α)` for
`0 ≤ α ≤ 1/2`, by integrating `D'(α) ≥ 4 α`. -/
theorem two_mul_sq_le_log_two_sub_binEntropy {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1 / 2) :
    2 * α ^ 2 ≤ Real.log 2 - Real.binEntropy (1 / 2 - α) := by
  have key : 0 ≤ equatorDeficit α - 2 * α ^ 2 :=
    nonneg_of_hasDerivAt_nonneg (f := fun a => equatorDeficit a - 2 * a ^ 2)
      (f' := fun a => Real.log (1 / 2 + a) - Real.log (1 / 2 - a) - 2 * 2 * a)
      (a := 0) (b := 1 / 2)
      ((continuous_equatorDeficit.sub (continuous_const.mul (continuous_pow 2))).continuousOn)
      (fun y hy => (hasDerivAt_equatorDeficit (by linarith [hy.1]) hy.2).sub
        (hasDerivAt_const_mul_sq 2 y))
      (fun y hy => by
        show 0 ≤ Real.log (1 / 2 + y) - Real.log (1 / 2 - y) - 2 * 2 * y
        linarith [four_mul_le_log_sub_log hy.1.le hy.2])
      (by
        show equatorDeficit 0 - 2 * 0 ^ 2 = 0
        rw [equatorDeficit_zero]
        ring)
      α ⟨h0, h1⟩
  unfold equatorDeficit at key
  linarith

/-- **Equator deficit, upper bound, natural logs**: `ln 2 - H(1/2 - α) ≤ (8/3) α²` for
`0 ≤ α ≤ 1/4`, by integrating `D'(α) ≤ (16/3) α`. -/
theorem log_two_sub_binEntropy_le {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1 / 4) :
    Real.log 2 - Real.binEntropy (1 / 2 - α) ≤ 8 / 3 * α ^ 2 := by
  have key : 0 ≤ 8 / 3 * α ^ 2 - equatorDeficit α :=
    nonneg_of_hasDerivAt_nonneg (f := fun a => 8 / 3 * a ^ 2 - equatorDeficit a)
      (f' := fun a => 2 * (8 / 3) * a - (Real.log (1 / 2 + a) - Real.log (1 / 2 - a)))
      (a := 0) (b := 1 / 4)
      (((continuous_const.mul (continuous_pow 2)).sub continuous_equatorDeficit).continuousOn)
      (fun y hy => (hasDerivAt_const_mul_sq (8 / 3) y).sub
        (hasDerivAt_equatorDeficit (by linarith [hy.1]) (by linarith [hy.2])))
      (fun y hy => by
        show 0 ≤ 2 * (8 / 3) * y - (Real.log (1 / 2 + y) - Real.log (1 / 2 - y))
        linarith [log_sub_log_le hy.1.le hy.2.le])
      (by
        show 8 / 3 * 0 ^ 2 - equatorDeficit 0 = 0
        rw [equatorDeficit_zero]
        ring)
      α ⟨h0, h1⟩
  unfold equatorDeficit at key
  linarith

/-- **Equator entropy deficit, lower bound** (in bits): `2 α² log e ≤ 1 - h(1/2 - α)` for
`0 ≤ α ≤ 1/2`. -/
theorem equatorDeficit_lower {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1 / 2) :
    2 * α ^ 2 * Real.logb 2 (Real.exp 1) ≤ 1 - binEntropy2 (1 / 2 - α) := by
  have hl : 0 < Real.log 2 := Real.log_pos one_lt_two
  have h := two_mul_sq_le_log_two_sub_binEntropy h0 h1
  have he : Real.logb 2 (Real.exp 1) = 1 / Real.log 2 := by
    rw [Real.logb, Real.log_exp]
  rw [he, binEntropy2, show (1 : ℝ) - Real.binEntropy (1 / 2 - α) / Real.log 2 =
      (Real.log 2 - Real.binEntropy (1 / 2 - α)) / Real.log 2 by
    rw [sub_div, div_self hl.ne'], mul_one_div]
  exact div_le_div_of_nonneg_right h hl.le

/-- **Equator entropy deficit, upper bound** (in bits): `1 - h(1/2 - α) ≤ 4 α²` for
`0 ≤ α ≤ 1/4` (the constant `4 > (8/3) log₂ e`). -/
theorem equatorDeficit_upper {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1 / 4) :
    1 - binEntropy2 (1 / 2 - α) ≤ 4 * α ^ 2 := by
  have hl : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hl2 : 2 / 3 < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have h := log_two_sub_binEntropy_le h0 h1
  rw [binEntropy2, show (1 : ℝ) - Real.binEntropy (1 / 2 - α) / Real.log 2 =
      (Real.log 2 - Real.binEntropy (1 / 2 - α)) / Real.log 2 by
    rw [sub_div, div_self hl.ne'], div_le_iff₀ hl]
  nlinarith [mul_nonneg (sub_nonneg.2 hl2.le) (sq_nonneg α)]

/-- **Weighted ball volume**: for `0 ≤ t ≤ 1`, `t^j V(M, j) ≤ (1 + t)^M`.

Proof sketch: `t^j ≤ t^i` for `i ≤ j` (`pow_le_pow_of_le_one`), so
`t^j ∑_{i ≤ j} (M choose i) ≤ ∑_{i ≤ j} (M choose i) t^i ≤ ∑_{i ≤ M} (M choose i) t^i =
(1 + t)^M` (`add_pow`; the terms with `i > M` vanish by `Nat.choose_eq_zero_of_lt`, the others
are nonnegative: `Finset.sum_le_sum_of_subset_of_nonneg` after splitting at `min j M`).
Reference: tex 1603-1606; node L10.  [leaf: medium] -/
theorem pow_mul_hammingVol_le (M j : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t ^ j * hammingVol M j ≤ (1 + t) ^ M := by
  have hbin : (1 + t) ^ M = ∑ s ∈ range (M + 1), t ^ s * (M.choose s : ℝ) := by
    rw [add_comm, add_pow]
    simp only [one_pow, mul_one]
  have hext : ∑ s ∈ range (M + 1), t ^ s * (M.choose s : ℝ) =
      ∑ s ∈ range (j + M + 1), t ^ s * (M.choose s : ℝ) := by
    apply Finset.sum_subset
    · intro s hs
      simp only [Finset.mem_range] at hs ⊢
      omega
    · intro s _ hs'
      simp only [Finset.mem_range, not_lt] at hs'
      rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero]
  rw [hbin, hext, hammingVol, Nat.cast_sum, Finset.mul_sum]
  calc ∑ s ∈ range (j + 1), t ^ j * (M.choose s : ℝ)
      ≤ ∑ s ∈ range (j + 1), t ^ s * (M.choose s : ℝ) := by
        apply Finset.sum_le_sum
        intro s hs
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_of_le_one ht0 ht1 (Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)))
          (Nat.cast_nonneg _)
    _ ≤ ∑ s ∈ range (j + M + 1), t ^ s * (M.choose s : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro s hs
          simp only [Finset.mem_range] at hs ⊢
          omega
        · intro s _ _
          positivity

/-- `(1 + t)^M ≤ e^(t M)` for `t ≥ 0`.

Proof sketch: `Real.add_one_le_exp` gives `1 + t ≤ e^t`; raise to the `M`-th power
(`pow_le_pow_left₀`) and use `Real.exp_nat_mul` (`(e^t)^M = e^(M t)`), `mul_comm`.
Reference: tex 1603-1606; node L10.  [leaf: easy] -/
theorem one_add_pow_le_exp_mul (M : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (1 + t) ^ M ≤ Real.exp (t * M) := by
  have h : 1 + t ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
  calc (1 + t) ^ M ≤ Real.exp t ^ M := pow_le_pow_left₀ (by linarith) h M
    _ = Real.exp (t * M) := by rw [← Real.exp_nat_mul, mul_comm]

/-- **Hamming-ball volume**: `V(M, h - 1) ≤ (e M / h)^h` for `1 ≤ h ≤ M`; from
`pow_mul_hammingVol_le` at `t = h / M` and `(1 + t)^M ≤ e^(t M) = e^h`. -/
theorem hammingVol_le_exp_mul_pow (M h : ℕ) (hh : 1 ≤ h) (hhM : h ≤ M) :
    (hammingVol M (h - 1) : ℝ) ≤ (Real.exp 1 * M / h) ^ h := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hhpos : (0 : ℝ) < h := by exact_mod_cast (by omega : 0 < h)
  have ht0 : (0 : ℝ) < (h : ℝ) / M := div_pos hhpos hMpos
  have ht1 : (h : ℝ) / M ≤ 1 := div_le_one_of_le₀ (by exact_mod_cast hhM) hMpos.le
  have h1 : (hammingVol M (h - 1) : ℝ) ≤ hammingVol M h := by
    exact_mod_cast hammingVol_mono (by omega)
  have h2 := pow_mul_hammingVol_le M h ht0.le ht1
  have h3 := one_add_pow_le_exp_mul M ht0.le
  have h4 : Real.exp ((h : ℝ) / M * M) = Real.exp 1 ^ h := by
    rw [div_mul_cancel₀ _ hMpos.ne', ← Real.exp_nat_mul, mul_one]
  have hte : Real.exp 1 * M / h = Real.exp 1 / ((h : ℝ) / M) := by
    rw [div_div_eq_mul_div]
  rw [hte, div_pow, le_div_iff₀ (pow_pos ht0 h)]
  calc (hammingVol M (h - 1) : ℝ) * ((h : ℝ) / M) ^ h
      ≤ hammingVol M h * ((h : ℝ) / M) ^ h :=
        mul_le_mul_of_nonneg_right h1 (pow_nonneg ht0.le h)
    _ = ((h : ℝ) / M) ^ h * hammingVol M h := mul_comm _ _
    _ ≤ (1 + (h : ℝ) / M) ^ M := h2
    _ ≤ Real.exp ((h : ℝ) / M * M) := h3
    _ = Real.exp 1 ^ h := h4

/-- **Ball volume in bits**: `log₂ V(M, h - 1) ≤ h log₂(e M / h)` for `1 ≤ h ≤ M`. -/
theorem logb_hammingVol_le (M h : ℕ) (hh : 1 ≤ h) (hhM : h ≤ M) :
    Real.logb 2 (hammingVol M (h - 1)) ≤ h * Real.logb 2 (Real.exp 1 * M / h) := by
  have hV : (0 : ℝ) < hammingVol M (h - 1) := by exact_mod_cast hammingVol_pos M (h - 1)
  rw [← Real.logb_pow]
  exact Real.logb_le_logb_of_le one_lt_two hV (hammingVol_le_exp_mul_pow M h hh hhM)

/-- **Entropy and binomial bounds** (blueprint node L10), all logarithms base 2:
the one-sided entropy bounds `eq:ham-entropy-estimate` on `[0, 1]`; the binomial-entropy bounds
`eq:ham-binomial-estimate`; `(L/k)^k ≤ (L choose k)`; the equator deficit
`2 α² log e ≤ 1 - h(1/2 - α)` on `[0, 1/2]` and `1 - h(1/2 - α) ≤ 4 α²` on `[0, 1/4]`; and
`log V(M, h - 1) ≤ h log(e M / h)` for `1 ≤ h ≤ M`. -/
theorem entropyAndBinomialBounds :
    (∀ z : ℝ, 0 ≤ z → z ≤ 1 →
      z * Real.logb 2 (1 / z) + z * Real.logb 2 (Real.exp 1) -
          z ^ 2 * Real.logb 2 (Real.exp 1) ≤ binEntropy2 z ∧
        binEntropy2 z ≤ z * Real.logb 2 (1 / z) + z * Real.logb 2 (Real.exp 1)) ∧
      (∀ L k : ℕ, k ≤ L →
        (L : ℝ) * binEntropy2 ((k : ℝ) / L) - Real.logb 2 ((L : ℝ) + 1) ≤
            Real.logb 2 (L.choose k) ∧
          Real.logb 2 (L.choose k) ≤ (L : ℝ) * binEntropy2 ((k : ℝ) / L)) ∧
      (∀ L k : ℕ, 1 ≤ k → k ≤ L → ((L : ℝ) / k) ^ k ≤ L.choose k) ∧
      (∀ α : ℝ, 0 ≤ α → α ≤ 1 / 2 →
        2 * α ^ 2 * Real.logb 2 (Real.exp 1) ≤ 1 - binEntropy2 (1 / 2 - α)) ∧
      (∀ α : ℝ, 0 ≤ α → α ≤ 1 / 4 → 1 - binEntropy2 (1 / 2 - α) ≤ 4 * α ^ 2) ∧
      (∀ M h : ℕ, 1 ≤ h → h ≤ M →
        Real.logb 2 (hammingVol M (h - 1)) ≤ h * Real.logb 2 (Real.exp 1 * M / h)) :=
  ⟨fun _ h0 h1 => binEntropy2_bounds h0 h1, fun L k hk => log_choose_bounds L k hk,
    fun L k h1 h2 => pow_div_le_choose L k h1 h2, fun _ h0 h1 => equatorDeficit_lower h0 h1,
    fun _ h0 h1 => equatorDeficit_upper h0 h1, fun M h h1 h2 => logb_hammingVol_le M h h1 h2⟩

/-! ### L13: the ordered distance count from small-set expansion -/

/-- The ordered pairs of `U` at Hamming distance `i`. -/
def distancePairs (U : Finset BitString) (i : ℕ) : Finset (BitString × BitString) :=
  (U ×ˢ U).filter (fun p => hammingDist p.1 p.2 = i)

/-- **Keeping one nonnegative noise summand**: the distance-`i` pairs contribute
`a_i(U) q^i (1 - q)^(M - i)` to the noise correlation of `U`.

Proof sketch: `Finset.sum_product'` rewrites the double sum over `U ×ˢ U`;
`sum_le_sum_of_subset_of_nonneg` (filter ⊆ `U ×ˢ U`, terms `≥ 0` for `0 ≤ q ≤ 1`), and on the
filter every term equals `q^i (1 - q)^(M - i)` (`sum_const`, `nsmul_eq_mul`).
Reference: tex 1866-1873; node L13.  [leaf: easy] -/
theorem card_distancePairs_mul_le (M : ℕ) (U : Finset BitString) (i : ℕ) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ((distancePairs U i).card : ℝ) * (q ^ i * (1 - q) ^ (M - i)) ≤
      ∑ u ∈ U, ∑ v ∈ U, q ^ hammingDist u v * (1 - q) ^ (M - hammingDist u v) := by
  rw [← Finset.sum_product'
    (f := fun u v => q ^ hammingDist u v * (1 - q) ^ (M - hammingDist u v))]
  have hc : ∑ p ∈ distancePairs U i,
      q ^ hammingDist p.1 p.2 * (1 - q) ^ (M - hammingDist p.1 p.2) =
      ∑ _p ∈ distancePairs U i, q ^ i * (1 - q) ^ (M - i) :=
    Finset.sum_congr rfl fun p hp => by rw [(Finset.mem_filter.mp hp).2]
  rw [← nsmul_eq_mul, ← Finset.sum_const, ← hc]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun p _ _ =>
    mul_nonneg (pow_nonneg hq0 _) (pow_nonneg (sub_nonneg.mpr hq1) _)

/-- `(i/M) / (1 - i/M) = i / (M - i)` for `i < M`.

Proof sketch: `M > 0`, `field_simp`.  Reference: tex 1862-1863; node L13.  [leaf: easy] -/
theorem div_one_sub_div_eq (M i : ℕ) (hi : i < M) :
    ((i : ℝ) / M) / (1 - (i : ℝ) / M) = (i : ℝ) / ((M : ℝ) - i) := by
  have hM : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  rw [one_sub_div hM.ne', div_div_div_cancel_right₀ hM.ne']

/-- **The distance bound from small-set expansion** (`eq:ham-hypercontractive-distance`): for
nonempty `U` of strings of length `M` and `1 ≤ i ≤ M / 2`, the ordered distance-`i` pairs
satisfy `a_i(U) ≤ |U| (M + 1) (M choose i) μ^(i/(M-i))`, `μ = |U| / 2^M`. -/
theorem distanceCount_le (M : ℕ) (U : Finset BitString) (hUM : U ⊆ stringsOfLength M)
    (hU : U.Nonempty) (i : ℕ) (hi1 : 1 ≤ i) (hiM : 2 * i ≤ M) :
    ((distancePairs U i).card : ℝ) ≤
      U.card * (M + 1) * M.choose i * ((U.card : ℝ) / 2 ^ M) ^ ((i : ℝ) / ((M : ℝ) - i)) := by
  have hiM' : i < M := by omega
  have hM : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hq0 : (0 : ℝ) ≤ (i : ℝ) / M := by positivity
  have hq1 : (i : ℝ) / M ≤ 1 / 2 := by
    rw [div_le_iff₀ hM]
    have : (2 * i : ℝ) ≤ M := by exact_mod_cast hiM
    linarith
  have hsse := cubeSmallSetExpansion M U hUM hU hq0 hq1
  rw [div_one_sub_div_eq M i hiM'] at hsse
  have hcount := card_distancePairs_mul_le M U i hq0 (by linarith)
  have hmode := (binomialModeMass M i hiM'.le).2
  rw [binomPmf, div_le_iff₀ (by positivity)] at hmode
  have hw : 1 ≤ ((M : ℝ) + 1) * M.choose i *
      (((i : ℝ) / M) ^ i * (1 - (i : ℝ) / M) ^ (M - i)) := by
    calc (1 : ℝ) ≤ _ := hmode
      _ = _ := by ring
  have hcnt0 : (0 : ℝ) ≤ (distancePairs U i).card := Nat.cast_nonneg _
  calc ((distancePairs U i).card : ℝ) = (distancePairs U i).card * 1 := (mul_one _).symm
    _ ≤ (distancePairs U i).card * (((M : ℝ) + 1) * M.choose i *
          (((i : ℝ) / M) ^ i * (1 - (i : ℝ) / M) ^ (M - i))) :=
        mul_le_mul_of_nonneg_left hw hcnt0
    _ = ((distancePairs U i).card * (((i : ℝ) / M) ^ i * (1 - (i : ℝ) / M) ^ (M - i))) *
          (((M : ℝ) + 1) * M.choose i) := by ring
    _ ≤ (U.card * ((U.card : ℝ) / 2 ^ M) ^ ((i : ℝ) / ((M : ℝ) - i))) *
          (((M : ℝ) + 1) * M.choose i) :=
        mul_le_mul_of_nonneg_right (hcount.trans hsse) (by positivity)
    _ = _ := by ring

/-- **Small support density**: if `c ≤ 2^(M/4)` then `c / 2^M ≤ 2^(-3M/4)`.

Proof sketch: `div_le_div_of_nonneg_right`, then `2^(M/4) / 2^M = 2^(M/4 - M)`
(`Real.rpow_natCast`, `← Real.rpow_sub two_pos`) and `M/4 - M = -(3M/4)` (`ring_nf`).
Reference: tex 1874-1880 ("`log μ ≤ -3M/4`"); node L13.  [leaf: easy] -/
theorem div_two_pow_le_rpow {M : ℕ} {c : ℝ} (hsmall : c ≤ (2 : ℝ) ^ ((M : ℝ) / 4)) :
    c / 2 ^ M ≤ (2 : ℝ) ^ (-(3 * (M : ℝ) / 4)) := by
  calc c / 2 ^ M ≤ (2 : ℝ) ^ ((M : ℝ) / 4) / 2 ^ M :=
        div_le_div_of_nonneg_right hsmall (by positivity)
    _ = (2 : ℝ) ^ ((M : ℝ) / 4 - M) := by rw [Real.rpow_sub two_pos, Real.rpow_natCast]
    _ = (2 : ℝ) ^ (-(3 * (M : ℝ) / 4)) := by congr 1; ring

/-- **Exponent comparison**: for `1 ≤ r` and `4 r ≤ M`,
`3r/2 ≤ (3M/4) · (2r / (M - 2r))`.

Proof sketch: `M - 2r > 0`; `le_div_iff₀`/`div_le_iff₀` and `nlinarith`: the claim is
`(3r/2)(M - 2r) ≤ (3M/4)(2r)`, i.e. `-3r² ≤ 0`.
Reference: tex 1876-1880; node L13.  [leaf: easy] -/
theorem exponent_comparison {M r : ℕ} (hr : 1 ≤ r) (hrM : 4 * r ≤ M) :
    3 * (r : ℝ) / 2 ≤ 3 * (M : ℝ) / 4 * (((2 * r : ℕ) : ℝ) / ((M : ℝ) - ((2 * r : ℕ) : ℝ))) := by
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hrM' : 4 * (r : ℝ) ≤ M := by exact_mod_cast hrM
  have hden : 0 < (M : ℝ) - 2 * r := by linarith
  push_cast
  rw [mul_div_assoc', le_div_iff₀ hden]
  nlinarith

/-- **Small support exponent**: if `0 < c ≤ 2^(M/4)`, `1 ≤ r` and `4 r ≤ M`, then
`(c / 2^M)^(2r / (M - 2r)) ≤ 2^(-3r/2)`. -/
theorem small_support_rpow_le {M r : ℕ} {c : ℝ} (hc : 0 < c) (hr : 1 ≤ r) (hrM : 4 * r ≤ M)
    (hsmall : c ≤ (2 : ℝ) ^ ((M : ℝ) / 4)) :
    (c / 2 ^ M) ^ (((2 * r : ℕ) : ℝ) / ((M : ℝ) - ((2 * r : ℕ) : ℝ))) ≤
      (2 : ℝ) ^ (-(3 * (r : ℝ) / 2)) := by
  have hden : (0 : ℝ) < (M : ℝ) - ((2 * r : ℕ) : ℝ) := by
    have : ((2 * r : ℕ) : ℝ) < M := by exact_mod_cast (by omega : 2 * r < M)
    linarith
  have he : 0 ≤ ((2 * r : ℕ) : ℝ) / ((M : ℝ) - ((2 * r : ℕ) : ℝ)) :=
    div_nonneg (Nat.cast_nonneg _) hden.le
  calc (c / 2 ^ M) ^ (((2 * r : ℕ) : ℝ) / ((M : ℝ) - ((2 * r : ℕ) : ℝ)))
      ≤ ((2 : ℝ) ^ (-(3 * (M : ℝ) / 4))) ^
          (((2 * r : ℕ) : ℝ) / ((M : ℝ) - ((2 * r : ℕ) : ℝ))) :=
        Real.rpow_le_rpow (div_pos hc (by positivity)).le (div_two_pow_le_rpow hsmall) he
    _ = (2 : ℝ) ^ (-(3 * (M : ℝ) / 4 *
          (((2 * r : ℕ) : ℝ) / ((M : ℝ) - ((2 * r : ℕ) : ℝ))))) := by
        rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), neg_mul]
    _ ≤ (2 : ℝ) ^ (-(3 * (r : ℝ) / 2)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (neg_le_neg (exponent_comparison hr hrM))

/-- **Ordered distance count from small-set expansion** (blueprint node L13,
`lem:ham-hypercontractive-distance`).  For a nonempty set `U` of strings of length `M`, with
`μ = |U| / 2^M`: for `1 ≤ i ≤ M / 2`, `a_i(U) ≤ |U| (M + 1) (M choose i) μ^(i/(M-i))`; and if
moreover `|U| ≤ 2^(M/4)`, `i = 2r` with `1 ≤ r` and `4 r ≤ M`, then
`a_{2r}(U) ≤ |U| (M + 1) (M choose 2r) 2^(-3r/2)`, a gain of `3r/2` bits. -/
theorem distanceCountFromSSE (M : ℕ) (U : Finset BitString) (hUM : U ⊆ stringsOfLength M)
    (hU : U.Nonempty) :
    (∀ i : ℕ, 1 ≤ i → 2 * i ≤ M →
      ((distancePairs U i).card : ℝ) ≤
        U.card * (M + 1) * M.choose i * ((U.card : ℝ) / 2 ^ M) ^ ((i : ℝ) / ((M : ℝ) - i))) ∧
      (∀ r : ℕ, 1 ≤ r → 4 * r ≤ M → (U.card : ℝ) ≤ (2 : ℝ) ^ ((M : ℝ) / 4) →
        ((distancePairs U (2 * r)).card : ℝ) ≤
          U.card * (M + 1) * M.choose (2 * r) * (2 : ℝ) ^ (-(3 * (r : ℝ) / 2))) := by
  refine ⟨fun i hi1 hiM => distanceCount_le M U hUM hU i hi1 hiM, fun r hr hrM hsmall => ?_⟩
  have h := distanceCount_le M U hUM hU (2 * r) (by omega) (by omega)
  have hc : (0 : ℝ) < U.card := by exact_mod_cast hU.card_pos
  calc _ ≤ _ := h
    _ ≤ _ := mul_le_mul_of_nonneg_left (small_support_rpow_le hc hr hrM hsmall) (by positivity)

end Kolmogorov.StrongMerging.Lower
