import KolmogorovMathlib.StrongMerging.Lower.CenterCode
import KolmogorovMathlib.StrongMerging.Lower.Analysis

/-!
# Numerical helpers of the near-equator calibration

The real-valued sharp quantities, generic numerical helpers and the entropy forms of
binomial logarithms used by the calibration L24 and the sharp game hypotheses L25.

Part of `KolmogorovMathlib.StrongMerging.Lower.Calibration`, which imports it.
-/

namespace Kolmogorov.StrongMerging.Lower

open Finset

/-! ### Real-valued sharp quantities -/

/-- The equator deficit `Δ = M - log₂ N` of the sharp sphere, `N = (M choose R)`. -/
noncomputable def sharpDeficit (M E : ℕ) : ℝ :=
  M - Real.logb 2 (sharpSphereCard M E)

/-- The ambient star exponent `a = log₂ D_a`, `D_a = (M choose 2r)`. -/
noncomputable def sharpLogAmbient (M E : ℕ) : ℝ :=
  Real.logb 2 (sharpAmbientDegree M E)

/-- The relative equator shift `α = w / M`, so that `R / M = 1/2 - α` (`sharp_rho_eq`). -/
noncomputable def sharpAlpha (M E : ℕ) : ℝ :=
  sharpShift M E / M

/-! ### Generic numerical helpers -/

/-- `log₂ e` lies in `(1.44, 1.5)`: `log₂ e = 1 / ln 2` and `0.693 < ln 2 < 0.6932`. -/
theorem logb_two_exp_bounds :
    (144 / 100 : ℝ) < Real.logb 2 (Real.exp 1) ∧ Real.logb 2 (Real.exp 1) < 3 / 2 := by
  have h : Real.logb 2 (Real.exp 1) = 1 / Real.log 2 := by
    rw [Real.logb, Real.log_exp]
  have h1 := Real.log_two_gt_d9
  have h2 := Real.log_two_lt_d9
  have hpos : 0 < Real.log 2 := by linarith
  rw [h]
  constructor
  · rw [lt_div_iff₀ hpos]
    norm_num at h1 h2 ⊢
    linarith
  · rw [div_lt_iff₀ hpos]
    norm_num at h1 h2 ⊢
    linarith

/-- **Integer square root from below**: `√n / 2 ≤ ⌊√n⌋` for `n ≥ 1`.

Proof sketch: put `s = Nat.sqrt n ≥ 1` (`Nat.le_sqrt`); `n < (s + 1)²` (`Nat.lt_succ_sqrt'`), so
`√n < s + 1 ≤ 2 s` (`Real.sqrt_lt'`).
Reference: tex 1550-1556 (`r ≥ √(ME)/2`, `w ≥ √(Mr)/2`); node L24. -/
theorem half_sqrt_le_natSqrt {n : ℕ} (hn : 1 ≤ n) : Real.sqrt n / 2 ≤ Nat.sqrt n := by
  have hs : 1 ≤ Nat.sqrt n := Nat.le_sqrt.2 (by omega)
  have hlt : n < (Nat.sqrt n + 1) ^ 2 := Nat.lt_succ_sqrt' n
  have hlt' : (n : ℝ) < ((Nat.sqrt n : ℝ) + 1) ^ 2 := by exact_mod_cast hlt
  have hsqrt : Real.sqrt n < (Nat.sqrt n : ℝ) + 1 := by
    rw [Real.sqrt_lt' (by positivity)]
    exact hlt'
  have hs' : (1 : ℝ) ≤ Nat.sqrt n := by exact_mod_cast hs
  linarith

/-- **Exponential beats linear, explicitly**: `(2j + 3) 2⁴⁰ ≤ 2^j` for `j ≥ 50`.

Proof sketch: induction from `j = 50` (`103 · 2⁴⁰ ≤ 2⁵⁰ = 1024 · 2⁴⁰`, `norm_num`); the step adds
`2 · 2⁴⁰ = 2⁴¹ ≤ 2^j` to the left side and doubles the right side (`Nat.le_induction`, `pow_succ`).
Reference: tex 1550-1556 (`r / m → ∞`); node L24. -/
theorem linear_mul_le_two_pow (j : ℕ) (hj : 50 ≤ j) : (2 * j + 3) * 2 ^ 40 ≤ 2 ^ j := by
  induction j, hj using Nat.le_induction with
  | base => norm_num
  | succ j hj ih =>
    have h41 : 2 ^ 41 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [pow_succ 2 j]
    have e : (2 * (j + 1) + 3) * 2 ^ 40 = (2 * j + 3) * 2 ^ 40 + 2 ^ 41 := by ring
    rw [e]
    linarith

/-- `2^⌊⌊log₂ M⌋ / 2⌋ ≤ ⌊√M⌋` for `M ≠ 0`. -/
theorem two_pow_half_log_le_sqrt {M : ℕ} (hM : M ≠ 0) : 2 ^ (Nat.log 2 M / 2) ≤ Nat.sqrt M := by
  rw [Nat.le_sqrt, ← pow_add]
  exact le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) (Nat.pow_log_le_self 2 hM)

/-- **The logarithm is negligible against the square root**: `(⌊log₂ M⌋ + 2) 2⁴⁰ ≤ ⌊√M⌋` for
`M ≥ 2¹⁰⁰`, from `2^⌊k/2⌋ ≤ ⌊√M⌋` with `k = ⌊log₂ M⌋ ≥ 100` and `linear_mul_le_two_pow`. -/
theorem natLog_mul_le_sqrt {M : ℕ} (hM : 2 ^ 100 ≤ M) :
    (Nat.log 2 M + 2) * 2 ^ 40 ≤ Nat.sqrt M := by
  have hM0 : M ≠ 0 := (lt_of_lt_of_le (by positivity) hM).ne'
  have hk : 100 ≤ Nat.log 2 M := Nat.le_log_of_pow_le one_lt_two hM
  have hj := linear_mul_le_two_pow (Nat.log 2 M / 2) (by omega)
  calc (Nat.log 2 M + 2) * 2 ^ 40 ≤ (2 * (Nat.log 2 M / 2) + 3) * 2 ^ 40 :=
        Nat.mul_le_mul_right _ (by omega)
    _ ≤ 2 ^ (Nat.log 2 M / 2) := hj
    _ ≤ Nat.sqrt M := two_pow_half_log_le_sqrt hM0

/-- **Real versus floor logarithm**: `log₂ x < ⌊log₂ x⌋ + 1` for a natural `x ≠ 0`.

Proof sketch: `x < 2^(⌊log₂ x⌋ + 1)` (`Nat.lt_pow_succ_log_self`); take `Real.logb 2`
(`Real.logb_lt_iff_lt_rpow`, `Real.rpow_natCast`).
Reference: tex 1512-1519 (`b = ⌊log N⌋`, `d = ⌊log D_i⌋`); node L24. -/
theorem logb_lt_natLog_add_one {x : ℕ} (hx : x ≠ 0) :
    Real.logb 2 x < Nat.log 2 x + 1 := by
  have h : x < 2 ^ (Nat.log 2 x + 1) := Nat.lt_pow_succ_log_self one_lt_two x
  have hx' : (0 : ℝ) < x := by exact_mod_cast Nat.pos_of_ne_zero hx
  rw [Real.logb_lt_iff_lt_rpow one_lt_two hx']
  have e : ((Nat.log 2 x : ℝ) + 1) = ((Nat.log 2 x + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [e, Real.rpow_natCast]
  exact_mod_cast h

/-- **Logarithm of a successor**: `log₂ (M + 1) ≤ ⌊log₂ M⌋ + 2` for every natural `M`.

Proof sketch: `M + 1 ≤ 2^(⌊log₂ M⌋ + 1)` (`Nat.lt_pow_succ_log_self`), so
`log₂ (M + 1) ≤ ⌊log₂ M⌋ + 1` (`Real.logb_le_logb_of_le`, `Real.logb_rpow`).
Reference: tex 1567-1569 (`Δ = O(r + m)`); node L24. -/
theorem logb_succ_le_natLog_add_two (M : ℕ) :
    Real.logb 2 ((M : ℝ) + 1) ≤ Nat.log 2 M + 2 := by
  have h : M < 2 ^ (Nat.log 2 M + 1) := Nat.lt_pow_succ_log_self one_lt_two M
  have h' : ((M : ℝ) + 1) ≤ (2 : ℝ) ^ ((Nat.log 2 M + 1 : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]
    exact_mod_cast (h : M + 1 ≤ 2 ^ (Nat.log 2 M + 1))
  have h2 := Real.logb_le_logb_of_le one_lt_two (by positivity) h'
  rw [Real.logb_rpow two_pos one_lt_two.ne'] at h2
  push_cast at h2
  linarith

/-- **Logarithm against the header length**: `log₂ (n + 1) ≤ ⌈log₂ (M + 2)⌉` for `n ≤ M`.

Proof sketch: `n + 1 ≤ M + 2 ≤ 2^⌈log₂ (M + 2)⌉` (`Nat.le_pow_clog`); `Real.logb_le_logb_of_le`
and `Real.logb_rpow` (or `Real.logb_le_iff_le_rpow`).
Reference: tex 1655-1662 (`2 log(M + 1) ≤ 2m`); node L24. -/
theorem logb_add_one_le_headerLog {n M : ℕ} (h : n ≤ M) :
    Real.logb 2 ((n : ℝ) + 1) ≤ headerLog M := by
  have hpow : M + 2 ≤ 2 ^ headerLog M := Nat.le_pow_clog one_lt_two _
  have h' : ((n : ℝ) + 1) ≤ (2 : ℝ) ^ ((headerLog M : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]
    exact_mod_cast (by omega : n + 1 ≤ 2 ^ headerLog M)
  have h2 := Real.logb_le_logb_of_le one_lt_two (by positivity) h'
  rwa [Real.logb_rpow two_pos one_lt_two.ne'] at h2

/-- **Header length against the floor logarithm**: `⌈log₂ (M + 2)⌉ ≤ ⌊log₂ M⌋ + 2`.

Proof sketch: `M + 2 ≤ 2^(⌊log₂ M⌋ + 2)` since `M + 1 ≤ 2^(⌊log₂ M⌋ + 1)`
(`Nat.lt_pow_succ_log_self`; for `M = 0` both sides are small); conclude with
`Nat.clog_le_iff_le_pow`.
Reference: blueprint L24 ("uniform form of `m / r → 0`"); node L24. -/
theorem headerLog_le_natLog_add_two (M : ℕ) : headerLog M ≤ Nat.log 2 M + 2 := by
  unfold headerLog
  rw [Nat.clog_le_iff_le_pow one_lt_two]
  have h : M < 2 ^ (Nat.log 2 M + 1) := Nat.lt_pow_succ_log_self one_lt_two M
  have e : 2 ^ (Nat.log 2 M + 2) = 2 * 2 ^ (Nat.log 2 M + 1) := by ring
  have h1 : 1 ≤ 2 ^ (Nat.log 2 M + 1) := Nat.one_le_two_pow
  omega

/-- **Exponential beats any linear function**: for every `A` there is `j₀` with
`A (2j + 3) ≤ 2^j` for all `j ≥ j₀`.

Proof sketch: take `j₀ = 2A + 10` (or use `Nat.lt_two_pow`); show `A (2j + 3) ≤ 2^j` at `j₀`
and propagate by `Nat.le_induction` (the left side grows by `2A ≤ 2^j` per step).
Reference: blueprint L24 ("derive an upper bound depending only on `M` ... then prove that it
tends to zero"); node L24. -/
theorem exists_linear_le_two_pow (A : ℕ) : ∃ j₀ : ℕ, ∀ j : ℕ, j₀ ≤ j → A * (2 * j + 3) ≤ 2 ^ j := by
  have hsq : ∀ j : ℕ, 4 ≤ j → j * j ≤ 2 ^ j := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => norm_num
    | succ j hj ih =>
      rw [pow_succ]
      nlinarith
  refine ⟨2 * A + 4, fun j hj => ?_⟩
  have h1 := hsq j (by omega)
  nlinarith [Nat.mul_le_mul_right j hj]

/-- **Choose from below by a power**: `a^k ≤ (L choose k)` whenever `1 ≤ k` and `a k ≤ L`, from
`(L / k)^k ≤ (L choose k)` (node L10, `pow_div_le_choose`). -/
theorem pow_le_choose_of_mul_le {L k a : ℕ} (hk : 1 ≤ k) (h : a * k ≤ L) : a ^ k ≤ L.choose k := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · rw [zero_pow (by omega)]
    exact Nat.zero_le _
  have hkL : k ≤ L := le_trans (Nat.le_mul_of_pos_left k ha) h
  have h1 := pow_div_le_choose L k hk hkL
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have h2 : (a : ℝ) ≤ (L : ℝ) / k := by
    rw [le_div_iff₀ hk']
    exact_mod_cast h
  have h3 : (a : ℝ) ^ k ≤ ((L : ℝ) / k) ^ k := pow_le_pow_left₀ (Nat.cast_nonneg a) h2 k
  exact_mod_cast h3.trans h1

/-! ### Entropy forms of binomial logarithms -/

/-- **Binomial logarithm, upper entropy form**: for `k ≤ L`, `0 < L`,
`log₂ (L choose k) ≤ k log₂ (L / k) + k log₂ e`.

Proof sketch: `log_choose_bounds` (upper) gives `log₂ (L choose k) ≤ L h(k/L)`; the upper entropy
bound `binEntropy2_bounds` at `z = k / L ∈ [0, 1]` gives
`L h(z) ≤ L z log₂ (1/z) + L z log₂ e = k log₂ (L/k) + k log₂ e` (`L z = k` as `L ≠ 0`;
`1 / (k / L) = L / k`, `one_div_div`).
Reference: tex 1641-1655 (`eq:ham-gap-raw`, ambient term); node L24 (uses L10). -/
theorem logb_choose_le_entropyForm (L k : ℕ) (hk : k ≤ L) (hL : 0 < L) :
    Real.logb 2 (L.choose k) ≤ k * Real.logb 2 ((L : ℝ) / k) + k * Real.logb 2 (Real.exp 1) := by
  have h1 := (log_choose_bounds L k hk).2
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hLne : (L : ℝ) ≠ 0 := hL'.ne'
  have hz0 : (0 : ℝ) ≤ (k : ℝ) / L := by positivity
  have hz1 : (k : ℝ) / L ≤ 1 := div_le_one_of_le₀ (by exact_mod_cast hk) hL'.le
  have h2 := (binEntropy2_bounds hz0 hz1).2
  have h3 := mul_le_mul_of_nonneg_left h2 hL'.le
  have e : (L : ℝ) * ((k : ℝ) / L * Real.logb 2 (1 / ((k : ℝ) / L)) +
      (k : ℝ) / L * Real.logb 2 (Real.exp 1)) =
      k * Real.logb 2 ((L : ℝ) / k) + k * Real.logb 2 (Real.exp 1) := by
    rw [one_div_div]
    field_simp
  rw [e] at h3
  linarith

/-- **Binomial logarithm, lower entropy form**: for `1 ≤ k ≤ L`,
`k log₂ (L / k) + k log₂ e - (k² / L) log₂ e - log₂ (L + 1) ≤ log₂ (L choose k)`.

Proof sketch: `log_choose_bounds` (lower) gives `L h(k/L) - log₂ (L + 1) ≤ log₂ (L choose k)`;
the lower entropy bound `binEntropy2_bounds` at `z = k / L` gives
`L h(z) ≥ L z log₂ (1/z) + L z log₂ e - L z² log₂ e = k log₂ (L/k) + k log₂ e - (k²/L) log₂ e`.
Reference: tex 1641-1655 (`eq:ham-gap-raw`, internal terms); node L24 (uses L10). -/
theorem logb_choose_ge_entropyForm (L k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ L) :
    (k : ℝ) * Real.logb 2 ((L : ℝ) / k) + k * Real.logb 2 (Real.exp 1) -
        (k : ℝ) ^ 2 / L * Real.logb 2 (Real.exp 1) - Real.logb 2 ((L : ℝ) + 1) ≤
      Real.logb 2 (L.choose k) := by
  have hL : 0 < L := by omega
  have h1 := (log_choose_bounds L k hk).1
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hLne : (L : ℝ) ≠ 0 := hL'.ne'
  have hz0 : (0 : ℝ) ≤ (k : ℝ) / L := by positivity
  have hz1 : (k : ℝ) / L ≤ 1 := div_le_one_of_le₀ (by exact_mod_cast hk) hL'.le
  have h2 := (binEntropy2_bounds hz0 hz1).1
  have h3 := mul_le_mul_of_nonneg_left h2 hL'.le
  have e : (L : ℝ) * ((k : ℝ) / L * Real.logb 2 (1 / ((k : ℝ) / L)) +
      (k : ℝ) / L * Real.logb 2 (Real.exp 1) -
        ((k : ℝ) / L) ^ 2 * Real.logb 2 (Real.exp 1)) =
      (k : ℝ) * Real.logb 2 ((L : ℝ) / k) + k * Real.logb 2 (Real.exp 1) -
        (k : ℝ) ^ 2 / L * Real.logb 2 (Real.exp 1) := by
    rw [one_div_div]
    field_simp
  rw [e] at h3
  linarith

/-- **Recombination of the three entropy logarithms**: for `M, R, M - R, r > 0`,
`2r log₂ (M / 2r) - r log₂ (R / r) - r log₂ ((M - R) / r) = r log₂ (M² / (4 R (M - R)))`.

Proof sketch: expand every `Real.logb` of a quotient or product (`Real.logb_div`,
`Real.logb_mul`, `Real.logb_pow`, all arguments nonzero) and compare (`ring`); the `log₂ r` terms
cancel and `log₂ 4 = 2 log₂ 2`.
Reference: tex 1655 (`r log (1 / (4 ρ (1 - ρ)))`); node L24. -/
theorem log_recombine {M R r : ℝ} (hM : 0 < M) (hR : 0 < R) (hMR : 0 < M - R) (hr : 0 < r) :
    2 * r * Real.logb 2 (M / (2 * r)) - r * Real.logb 2 (R / r) -
        r * Real.logb 2 ((M - R) / r) =
      r * Real.logb 2 (M ^ 2 / (4 * R * (M - R))) := by
  have h4R : (4 : ℝ) * R ≠ 0 := by positivity
  rw [Real.logb_div (x := M) (y := 2 * r) hM.ne' (by positivity),
    Real.logb_div (x := R) (y := r) hR.ne' hr.ne',
    Real.logb_div (x := M - R) (y := r) hMR.ne' hr.ne',
    Real.logb_div (x := M ^ 2) (y := 4 * R * (M - R)) (by positivity)
      (mul_ne_zero h4R hMR.ne'),
    Real.logb_mul (x := 2) (y := r) two_ne_zero hr.ne',
    Real.logb_mul (x := 4 * R) (y := M - R) h4R hMR.ne',
    Real.logb_mul (x := 4) (y := R) four_ne_zero hR.ne', Real.logb_pow]
  have h4 : Real.logb 2 (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.logb_pow, Real.logb_self_eq_one one_lt_two]
    norm_num
  rw [h4, Real.logb_self_eq_one one_lt_two]
  push_cast
  ring

/-- **The `α`-term of the score gap**: if `8 w² ≤ M²`, `w² ≤ M r`, `r ≥ 0` and `r² ≤ M E`, then
`r log₂ (M² / (M² - 4 w²)) ≤ 8 E log₂ e`.

Proof sketch: `x = M² / (M² - 4w²) > 0` and `log₂ x ≤ (x - 1) log₂ e` (`Real.log_le_sub_one_of_pos`,
`Real.logb = log / log 2`); `x - 1 = 4w² / (M² - 4w²) ≤ 8 w² / M²` as `M² - 4 w² ≥ M² / 2`; then
`r · 8 w² / M² ≤ 8 r² / M ≤ 8 E` (`w² ≤ M r`, `r² ≤ M E`).
Reference: tex 1657-1662 (`-log(1 - 4α²) ≤ 8 α² log e`, `α² ≤ r/M`, `r²/M ≤ E`); node L24. -/
theorem sqrt_gap_log_bound {M w r E : ℝ} (hM : 0 < M) (h8 : 8 * w ^ 2 ≤ M ^ 2)
    (hwr : w ^ 2 ≤ M * r) (hr : 0 ≤ r) (hrE : r ^ 2 ≤ M * E) :
    r * Real.logb 2 (M ^ 2 / (M ^ 2 - 4 * w ^ 2)) ≤ 8 * E * Real.logb 2 (Real.exp 1) := by
  have hM2 : 0 < M ^ 2 := by positivity
  have hdpos : 0 < M ^ 2 - 4 * w ^ 2 := by nlinarith [sq_nonneg w]
  have hle : Real.logb 2 (Real.exp 1) = 1 / Real.log 2 := by rw [Real.logb, Real.log_exp]
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hxpos : 0 < M ^ 2 / (M ^ 2 - 4 * w ^ 2) := div_pos hM2 hdpos
  have hlogx : Real.logb 2 (M ^ 2 / (M ^ 2 - 4 * w ^ 2)) ≤
      (M ^ 2 / (M ^ 2 - 4 * w ^ 2) - 1) * Real.logb 2 (Real.exp 1) := by
    rw [hle, show Real.logb 2 (M ^ 2 / (M ^ 2 - 4 * w ^ 2)) =
      Real.log (M ^ 2 / (M ^ 2 - 4 * w ^ 2)) / Real.log 2 from rfl, mul_one_div,
      div_le_div_iff_of_pos_right hlog2]
    exact Real.log_le_sub_one_of_pos hxpos
  have hx1 : M ^ 2 / (M ^ 2 - 4 * w ^ 2) - 1 ≤ 8 * w ^ 2 / M ^ 2 := by
    rw [div_sub_one hdpos.ne', div_le_div_iff₀ hdpos hM2]
    nlinarith [mul_nonneg (sq_nonneg w) (sub_nonneg.2 h8)]
  have hr8 : r * (8 * w ^ 2 / M ^ 2) ≤ 8 * E := by
    rw [mul_div_assoc', div_le_iff₀ hM2]
    nlinarith [mul_le_mul_of_nonneg_left hwr hr, mul_le_mul_of_nonneg_left hrE hM.le]
  have hlepos : 0 ≤ Real.logb 2 (Real.exp 1) := by rw [hle]; positivity
  calc r * Real.logb 2 (M ^ 2 / (M ^ 2 - 4 * w ^ 2))
      ≤ r * ((M ^ 2 / (M ^ 2 - 4 * w ^ 2) - 1) * Real.logb 2 (Real.exp 1)) :=
        mul_le_mul_of_nonneg_left hlogx hr
    _ = (r * (M ^ 2 / (M ^ 2 - 4 * w ^ 2) - 1 + (1 - 1) * r)) *
          Real.logb 2 (Real.exp 1) := by ring
    _ ≤ (r * (8 * w ^ 2 / M ^ 2)) * Real.logb 2 (Real.exp 1) := by
        apply mul_le_mul_of_nonneg_right _ hlepos
        have := mul_le_mul_of_nonneg_left hx1 hr
        linarith
    _ ≤ 8 * E * Real.logb 2 (Real.exp 1) := mul_le_mul_of_nonneg_right hr8 hlepos

/-- **The `ρ`-term of the score gap**: if `M / 4 ≤ R ≤ M / 2` and `r² ≤ M E`, then
`r² / R + r² / (M - R) ≤ (16/3) E`.

Proof sketch: `1/R + 1/(M - R) = M / (R (M - R))` and `R (M - R) ≥ 3 M² / 16` on
`[M/4, M/2]` (`nlinarith`: `(R - M/4)(3M/4 - R) ≥ 0`); so the sum is at most
`16 r² / (3 M) ≤ 16 E / 3` (`div_le_iff₀`).
Reference: tex 1657-1662 (`1/ρ + 1/(1 - ρ) ≤ 16/3`); node L24. -/
theorem inv_sum_bound {M R r E : ℝ} (hM : 0 < M) (hR1 : M / 4 ≤ R) (hR2 : R ≤ M / 2)
    (hrE : r ^ 2 ≤ M * E) : r ^ 2 / R + r ^ 2 / (M - R) ≤ 16 / 3 * E := by
  have hR : 0 < R := by linarith
  have hMR : 0 < M - R := by linarith
  have hprod : 3 * M ^ 2 / 16 ≤ R * (M - R) := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ R - M / 4)
      (by linarith : (0 : ℝ) ≤ 3 * M / 4 - R)]
  have hE : 0 ≤ E := by
    by_contra h
    have := mul_neg_of_pos_of_neg hM (lt_of_not_ge h)
    nlinarith [sq_nonneg r]
  rw [div_add_div _ _ hR.ne' hMR.ne', div_le_iff₀ (mul_pos hR hMR)]
  nlinarith [mul_le_mul_of_nonneg_left hprod hE, mul_le_mul_of_nonneg_left hrE hM.le]

end Kolmogorov.StrongMerging.Lower
