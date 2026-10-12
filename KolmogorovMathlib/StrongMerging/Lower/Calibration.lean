import KolmogorovMathlib.StrongMerging.Lower.Calibration.Numerics

/-!
# The sharp lower bound: near-equator calibration and the sharp game hypotheses

Blueprint nodes L24 (`nearEquatorCalibration`) and L25 (`sharpGameHypotheses`) of the
formalization of `sublinear-merging.tex` (paper: "Near-equator parameters and uniform entropy
estimates", lines ~1506-1576, and "Verifying the reservoir inequalities", lines ~1577-1611;
blueprint: "Uniform parameter calibration and the incompressible edge", lines ~4806-4847).

All parameters are those of `sharpParameters M E` (node L05): `r = ⌊√(M E)⌋`, `w = ⌊√(M r)⌋`,
`R = M/2 - w`, `N = (M choose R)`, `b = ⌊log₂ N⌋`, `K = ⌊(M + b)/2⌋`, `D_a = (M choose 2r)`,
`D_i = (R choose r)((M - R) choose r)`, `d = ⌊log₂ D_i⌋`, `T = ⌊r/10⁶⌋`, `S = 3T`, `τ = 6T`,
`ℓ = M/8`, `h = M/1024`, `δ = ⌊r/10⁴⌋`, `m = ⌈log₂ (M + 2)⌉`; the real quantities are
`Δ = M - log₂ N` (`sharpDeficit`), `a = log₂ D_a` (`sharpLogAmbient`) and `α = w / M`
(`sharpAlpha`).

* **L24.**  On the valid domain `SharpValid M E` (`2048 ∣ M`, `1 ≤ E`, `2¹⁰⁰ E ≤ M`, which forces
  `M ≥ 2¹⁰⁰`) every estimate is an exact inequality with rational constants and no cutoff:
  `r ≥ √(M E)/2`, `2⁵⁰ E ≤ r` (so `E / r ≤ 2⁻⁵⁰`; it does not tend to zero), `w² ≤ M r`,
  `w ≥ √(M r)/2`, `0.72 r ≤ Δ ≤ 5 r`, `Δ/2 ≤ M - K ≤ Δ/2 + 1`, `M - K > 0.35 r`,
  `K - log₂ N > 0.35 r`, `a - d ≤ (8 + 16/3) E log₂ e + 2m + 1 < 20 E + 2m + 1`, `97 r ≤ d ≤ M`.
  The uniform growth of `T / m` (hence of `r / m`) is `sharp_growth`: for every constant `C`
  there is a cutoff `M₀`, depending only on `C`, with `C m ≤ T` for all `M ≥ M₀` and all `E ≥ 1`.
  The only quantitative input beyond the entropy bounds of node L10 is `sharp_log_small`:
  `(⌊log₂ M⌋ + 2) 2⁴⁰ ≤ r`, so `log M` is negligible against `r` on the whole valid domain.
* **L25.**  The four inequalities `ReservoirInequalities` of the generic game hold at the sharp
  parameters for all valid `M, E` (the cutoff is `M₀ = 0`): density, charge and arrivals are
  integer statements reduced to exponent comparisons (`density_of_exponent`,
  `charge_of_exponent`, `arrivals_of_exponent`); the real heavy inequality is split into the
  near-pair term `2^(S+1+δ) V(M, h-1) 2^(-ℓ) ≤ 1/512` (`log₂ V(M, h-1) ≤ M/64`) and the collision
  term `2^(S+1+δ) β^h ≤ 1/512` (`β ≤ exp(-2α²)`, so `β^h ≤ exp(-r/2048)`).

The first part of the development is in
`KolmogorovMathlib.StrongMerging.Lower.Calibration.Numerics`, imported here.
-/

namespace Kolmogorov.StrongMerging.Lower

open Finset

/-! ### Elementary facts on the sharp parameters -/

/-- **Large `M` and a large radius**: `2¹⁰⁰ ≤ M` and `2⁵⁰ ≤ r` on the valid domain. -/
theorem sharp_big {M E : ℕ} (hv : SharpValid M E) :
    2 ^ 100 ≤ M ∧ 2 ^ 50 ≤ sharpRootRadius M E := by
  obtain ⟨-, hE, hEM⟩ := hv
  have hM : 2 ^ 100 ≤ M := le_trans (Nat.le_mul_of_pos_right _ hE) hEM
  refine ⟨hM, ?_⟩
  rw [sharpRootRadius, Nat.le_sqrt]
  calc 2 ^ 50 * 2 ^ 50 = 2 ^ 100 * 1 := by norm_num
    _ ≤ M * E := Nat.mul_le_mul hM hE

/-- **The logarithm is negligible against the radius**: `(⌊log₂ M⌋ + 2) 2⁴⁰ ≤ r` on the valid
domain (`r = ⌊√(M E)⌋ ≥ ⌊√M⌋` and `natLog_mul_le_sqrt`). -/
theorem sharp_log_small {M E : ℕ} (hv : SharpValid M E) :
    (Nat.log 2 M + 2) * 2 ^ 40 ≤ sharpRootRadius M E := by
  exact (natLog_mul_le_sqrt (sharp_big hv).1).trans
    (Nat.sqrt_le_sqrt (Nat.le_mul_of_pos_right M hv.2.1))

/-- `log₂ (M + 1) ≤ r` on the valid domain. -/
theorem sharp_logb_succ_le_root {M E : ℕ} (hv : SharpValid M E) :
    Real.logb 2 ((M : ℝ) + 1) ≤ sharpRootRadius M E := by
  have h1 := logb_succ_le_natLog_add_two M
  have h2 := sharp_log_small hv
  have h3 : Nat.log 2 M + 2 ≤ sharpRootRadius M E :=
    le_trans (Nat.le_mul_of_pos_right _ (by positivity)) h2
  have h4 : ((Nat.log 2 M + 2 : ℕ) : ℝ) ≤ sharpRootRadius M E := by exact_mod_cast h3
  push_cast at h4
  linarith

/-- **The relative sphere radius**: `R / M = 1/2 - α` on the valid domain.

Proof sketch: `R + w = M / 2` and `M = 2 (M / 2)` (`sharpParameters_valid`), so `(R : ℝ) = M/2 - w`
after casting (`Nat.cast_add`, `Nat.cast_mul`); divide by `M > 0` (`field_simp`, `sharpAlpha`).
Reference: tex 1548-1550 (`ρ = R/M = 1/2 - α`); node L24. -/
theorem sharp_rho_eq {M E : ℕ} (hv : SharpValid M E) :
    (sharpSphereRadius M E : ℝ) / M = 1 / 2 - sharpAlpha M E := by
  obtain ⟨-, -, -, -, -, hRw, -, -, -, -, -, -, hM2, -⟩ := sharpParameters_valid hv
  have hM : (0 : ℝ) < M := by exact_mod_cast lt_of_lt_of_le (by positivity) (sharp_big hv).1
  have h : 2 * (sharpSphereRadius M E + sharpShift M E) = M := by omega
  have h' : (2 : ℝ) * ((sharpSphereRadius M E : ℝ) + sharpShift M E) = M := by exact_mod_cast h
  rw [sharpAlpha, eq_sub_iff_add_eq, ← add_div, div_eq_iff hM.ne']
  linarith

/-- **The relative shift is small**: `0 ≤ α ≤ 1/4` (indeed `α ≤ 2⁻²⁵`). -/
theorem sharp_alpha_bounds {M E : ℕ} (hv : SharpValid M E) :
    0 ≤ sharpAlpha M E ∧ sharpAlpha M E ≤ 1 / 4 := by
  obtain ⟨-, -, -, hw25, -⟩ := sharpParameters_valid hv
  have hM : (0 : ℝ) < M := by exact_mod_cast lt_of_lt_of_le (by positivity) (sharp_big hv).1
  refine ⟨div_nonneg (Nat.cast_nonneg _) hM.le, ?_⟩
  rw [sharpAlpha, div_le_iff₀ hM]
  have h : (2 ^ 25 * sharpShift M E : ℕ) ≤ M := hw25
  have h' : (2 : ℝ) ^ 25 * sharpShift M E ≤ M := by exact_mod_cast h
  have hw : (0 : ℝ) ≤ sharpShift M E := Nat.cast_nonneg _
  nlinarith

/-- **The sphere radius between the quarter and the half**: `M/4 ≤ R ≤ M/2` (reals). -/
theorem sharp_R_bounds {M E : ℕ} (hv : SharpValid M E) :
    (M : ℝ) / 4 ≤ sharpSphereRadius M E ∧ (sharpSphereRadius M E : ℝ) ≤ M / 2 := by
  obtain ⟨-, -, -, hw25, -, hRw, -, hRM, -, -, -, -, hM2, -⟩ := sharpParameters_valid hv
  have h1 : M ≤ 4 * sharpSphereRadius M E := by norm_num at hw25; omega
  have h1' : (M : ℝ) ≤ 4 * sharpSphereRadius M E := by exact_mod_cast h1
  have h2' : (2 * sharpSphereRadius M E : ℝ) ≤ M := by exact_mod_cast hRM.le
  constructor <;> linarith

/-- **The product `4 R (M - R)`**: `4 R (M - R) = M² - 4 w²` (reals), from `R + w = M/2`. -/
theorem sharp_four_R_MR {M E : ℕ} (hv : SharpValid M E) :
    4 * (sharpSphereRadius M E : ℝ) * ((M : ℝ) - sharpSphereRadius M E) =
      (M : ℝ) ^ 2 - 4 * (sharpShift M E : ℝ) ^ 2 := by
  obtain ⟨-, -, -, -, -, hRw, -, -, -, -, -, -, hM2, -⟩ := sharpParameters_valid hv
  have h : 2 * (sharpSphereRadius M E + sharpShift M E) = M := by omega
  have h' : (M : ℝ) = 2 * ((sharpSphereRadius M E : ℝ) + sharpShift M E) := by
    exact_mod_cast h.symm
  rw [h']
  ring

/-- `log₂ N ≤ M h(1/2 - α)` (upper binomial entropy bound, node L10). -/
theorem sharp_logN_le_entropy {M E : ℕ} (hv : SharpValid M E) :
    Real.logb 2 (sharpSphereCard M E) ≤ M * binEntropy2 (1 / 2 - sharpAlpha M E) := by
  obtain ⟨-, -, -, -, -, -, -, hRM, -⟩ := sharpParameters_valid hv
  have h := (log_choose_bounds M (sharpSphereRadius M E) (by omega)).2
  rw [sharp_rho_eq hv] at h
  exact h

/-- `M h(1/2 - α) - log₂ (M + 1) ≤ log₂ N` (lower binomial entropy bound, node L10). -/
theorem sharp_logN_ge_entropy {M E : ℕ} (hv : SharpValid M E) :
    M * binEntropy2 (1 / 2 - sharpAlpha M E) - Real.logb 2 ((M : ℝ) + 1) ≤
      Real.logb 2 (sharpSphereCard M E) := by
  obtain ⟨-, -, -, -, -, -, -, hRM, -⟩ := sharpParameters_valid hv
  have h := (log_choose_bounds M (sharpSphereRadius M E) (by omega)).1
  rw [sharp_rho_eq hv] at h
  exact h

/-! ### L24: the near-equator calibration -/

/-- **Root radius from below**: `r = ⌊√(M E)⌋ ≥ √(M E) / 2`. -/
theorem sharp_root_lower {M E : ℕ} (hv : SharpValid M E) :
    Real.sqrt ((M : ℝ) * E) / 2 ≤ sharpRootRadius M E := by
  have hM := (sharp_big hv).1
  have hn : 1 ≤ M * E := Nat.one_le_iff_ne_zero.2
    (Nat.mul_ne_zero (by positivity) (by have := hv.2.1; omega))
  have h := half_sqrt_le_natSqrt hn
  push_cast at h
  exact h

/-- **The tolerance is a tiny fraction of the radius**: `2⁵⁰ E ≤ r` (so `E / r ≤ 2⁻⁵⁰`). -/
theorem sharp_tolerance_le {M E : ℕ} (hv : SharpValid M E) :
    2 ^ 50 * E ≤ sharpRootRadius M E := by
  obtain ⟨-, -, hEM⟩ := hv
  rw [sharpRootRadius, Nat.le_sqrt]
  calc 2 ^ 50 * E * (2 ^ 50 * E) = 2 ^ 100 * E * E := by ring
    _ ≤ M * E := Nat.mul_le_mul_right _ hEM

/-- **Shift squared**: `w² ≤ M r` (so `α² = (w/M)² ≤ r / M`). -/
theorem sharp_shift_sq_le (M E : ℕ) :
    sharpShift M E * sharpShift M E ≤ M * sharpRootRadius M E := by
  have h := Nat.sqrt_le' (M * sharpRootRadius M E)
  rw [sq] at h
  exact h

/-- **Shift from below**: `w = ⌊√(M r)⌋ ≥ √(M r) / 2`. -/
theorem sharp_shift_lower {M E : ℕ} (hv : SharpValid M E) :
    Real.sqrt ((M : ℝ) * sharpRootRadius M E) / 2 ≤ sharpShift M E := by
  have hM := (sharp_big hv).1
  have hr := (sharp_big hv).2
  have hn : 1 ≤ M * sharpRootRadius M E := Nat.one_le_iff_ne_zero.2
    (Nat.mul_ne_zero (by positivity) (by positivity))
  have h := half_sqrt_le_natSqrt hn
  push_cast at h
  exact h

/-- `r / 4 ≤ M α²` (from `w ≥ √(M r)/2`). -/
theorem sharp_alpha_sq_lower {M E : ℕ} (hv : SharpValid M E) :
    (sharpRootRadius M E : ℝ) / 4 ≤ M * sharpAlpha M E ^ 2 := by
  have hw := sharp_shift_lower hv
  have hM : (0 : ℝ) < M := by exact_mod_cast lt_of_lt_of_le (by positivity) (sharp_big hv).1
  have hr : (0 : ℝ) ≤ sharpRootRadius M E := Nat.cast_nonneg _
  have hsq : Real.sqrt ((M : ℝ) * sharpRootRadius M E) ^ 2 = M * sharpRootRadius M E :=
    Real.sq_sqrt (by positivity)
  have h0 : 0 ≤ Real.sqrt ((M : ℝ) * sharpRootRadius M E) / 2 := by positivity
  have hw2 := pow_le_pow_left₀ h0 hw 2
  rw [div_pow, hsq] at hw2
  have he : (M : ℝ) * sharpAlpha M E ^ 2 = (sharpShift M E : ℝ) ^ 2 / M := by
    rw [sharpAlpha]
    field_simp
  rw [he, le_div_iff₀ hM]
  nlinarith

/-- `M α² ≤ r` (from `w² ≤ M r`). -/
theorem sharp_alpha_sq_upper {M E : ℕ} (hv : SharpValid M E) :
    M * sharpAlpha M E ^ 2 ≤ sharpRootRadius M E := by
  have hM : (0 : ℝ) < M := by exact_mod_cast lt_of_lt_of_le (by positivity) (sharp_big hv).1
  have h := sharp_shift_sq_le M E
  have h' : (sharpShift M E : ℝ) * sharpShift M E ≤ M * sharpRootRadius M E := by
    exact_mod_cast h
  have he : (M : ℝ) * sharpAlpha M E ^ 2 = (sharpShift M E : ℝ) ^ 2 / M := by
    rw [sharpAlpha]
    field_simp
  rw [he, div_le_iff₀ hM]
  nlinarith

/-- **Equator deficit from below**: `Δ = M - log₂ N ≥ 0.72 r`. -/
theorem sharp_deficit_lower {M E : ℕ} (hv : SharpValid M E) :
    72 / 100 * (sharpRootRadius M E : ℝ) ≤ sharpDeficit M E := by
  obtain ⟨hα0, hα1⟩ := sharp_alpha_bounds hv
  have h1 := sharp_logN_le_entropy hv
  have h2 := equatorDeficit_lower hα0 (by linarith : sharpAlpha M E ≤ 1 / 2)
  have h3 := sharp_alpha_sq_lower hv
  have h4 := logb_two_exp_bounds.1
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hr : (0 : ℝ) ≤ sharpRootRadius M E := Nat.cast_nonneg _
  have hle : (0 : ℝ) ≤ Real.logb 2 (Real.exp 1) := by linarith
  have h5 := mul_le_mul_of_nonneg_left h2 hM
  have h6 := mul_le_mul_of_nonneg_left h3 hle
  have h7 := mul_le_mul_of_nonneg_right h4.le hr
  unfold sharpDeficit
  nlinarith

/-- **Equator deficit from above**: `Δ = M - log₂ N ≤ 5 r` (`Δ = Θ(r)` with `c_Δ = 5`). -/
theorem sharp_deficit_upper {M E : ℕ} (hv : SharpValid M E) :
    sharpDeficit M E ≤ 5 * (sharpRootRadius M E : ℝ) := by
  obtain ⟨hα0, hα1⟩ := sharp_alpha_bounds hv
  have h1 := sharp_logN_ge_entropy hv
  have h2 := equatorDeficit_upper hα0 hα1
  have h3 := sharp_alpha_sq_upper hv
  have h4 := sharp_logb_succ_le_root hv
  have h5 := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg (α := ℝ) M)
  unfold sharpDeficit
  nlinarith

/-- **The threshold is halfway**: `Δ/2 ≤ M - K ≤ Δ/2 + 1`. -/
theorem sharp_threshold_deficit {M E : ℕ} (hv : SharpValid M E) :
    sharpDeficit M E / 2 ≤ (M : ℝ) - sharpThreshold M E ∧
      (M : ℝ) - sharpThreshold M E ≤ sharpDeficit M E / 2 + 1 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hN0, -⟩ := sharpParameters_valid hv
  have hb1 : (sharpLogSphereCard M E : ℝ) ≤ Real.logb 2 (sharpSphereCard M E) :=
    natLog_le_logb _
  have hb2 : Real.logb 2 (sharpSphereCard M E) < (sharpLogSphereCard M E : ℝ) + 1 :=
    logb_lt_natLog_add_one hN0.ne'
  have hK1 : 2 * sharpThreshold M E ≤ M + sharpLogSphereCard M E := by
    unfold sharpThreshold
    omega
  have hK2 : M + sharpLogSphereCard M E ≤ 2 * sharpThreshold M E + 1 := by
    unfold sharpThreshold
    omega
  have hK1' : (2 * sharpThreshold M E : ℝ) ≤ M + sharpLogSphereCard M E := by exact_mod_cast hK1
  have hK2' : (M + sharpLogSphereCard M E : ℝ) ≤ 2 * sharpThreshold M E + 1 := by
    exact_mod_cast hK2
  unfold sharpDeficit
  constructor <;> linarith

/-- **Game margins** (`eq:ham-game-margins`): `M - K > 0.35 r` and `K - log₂ N > 0.35 r`. -/
theorem sharp_game_margins {M E : ℕ} (hv : SharpValid M E) :
    35 / 100 * (sharpRootRadius M E : ℝ) < (M : ℝ) - sharpThreshold M E ∧
      35 / 100 * (sharpRootRadius M E : ℝ) <
        (sharpThreshold M E : ℝ) - Real.logb 2 (sharpSphereCard M E) := by
  obtain ⟨h1, h2⟩ := sharp_threshold_deficit hv
  have h3 := sharp_deficit_lower hv
  have hr : (2 : ℝ) ^ 50 ≤ sharpRootRadius M E := by exact_mod_cast (sharp_big hv).2
  unfold sharpDeficit at h1 h2 h3
  constructor <;> linarith

/-- `log₂ D_a ≤ 2r log₂ (M / 2r) + 2r log₂ e` (ambient star, upper entropy form). -/
theorem sharp_logAmbient_le {M E : ℕ} (hv : SharpValid M E) :
    sharpLogAmbient M E ≤
      2 * (sharpRootRadius M E : ℝ) * Real.logb 2 ((M : ℝ) / (2 * sharpRootRadius M E)) +
        2 * (sharpRootRadius M E : ℝ) * Real.logb 2 (Real.exp 1) := by
  obtain ⟨-, -, -, -, -, -, -, hRM, hrR, -⟩ := sharpParameters_valid hv
  have h := logb_choose_le_entropyForm M (2 * sharpRootRadius M E) (by omega) (by omega)
  push_cast at h
  exact h

/-- `log₂ D_i` from below, in entropy form:
`r log₂ (R/r) + r log₂ ((M-R)/r) + 2r log₂ e - (r²/R + r²/(M-R)) log₂ e - 2m ≤ log₂ D_i`. -/
theorem sharp_logInternal_ge {M E : ℕ} (hv : SharpValid M E) :
    (sharpRootRadius M E : ℝ) *
          Real.logb 2 ((sharpSphereRadius M E : ℝ) / sharpRootRadius M E) +
        (sharpRootRadius M E : ℝ) *
          Real.logb 2 (((M : ℝ) - sharpSphereRadius M E) / sharpRootRadius M E) +
        2 * (sharpRootRadius M E : ℝ) * Real.logb 2 (Real.exp 1) -
        ((sharpRootRadius M E : ℝ) ^ 2 / sharpSphereRadius M E +
            (sharpRootRadius M E : ℝ) ^ 2 / ((M : ℝ) - sharpSphereRadius M E)) *
          Real.logb 2 (Real.exp 1) -
        2 * headerLog M ≤
      Real.logb 2 (sharpInternalDegree M E) := by
  obtain ⟨hr0, -, -, -, -, -, hR0, hRM, hrR, -⟩ := sharpParameters_valid hv
  have hRle : sharpSphereRadius M E ≤ M := by omega
  have h1 := logb_choose_ge_entropyForm (sharpSphereRadius M E) (sharpRootRadius M E) hr0
    (by omega)
  have h2 := logb_choose_ge_entropyForm (M - sharpSphereRadius M E) (sharpRootRadius M E) hr0
    (by omega)
  have h3 := logb_add_one_le_headerLog hRle
  have h4 := logb_add_one_le_headerLog (Nat.sub_le M (sharpSphereRadius M E))
  have hc1 : (0 : ℝ) < ((sharpSphereRadius M E).choose (sharpRootRadius M E) : ℕ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  have hc2 : (0 : ℝ) < ((M - sharpSphereRadius M E).choose (sharpRootRadius M E) : ℕ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  have hmul : Real.logb 2 (sharpInternalDegree M E) =
      Real.logb 2 ((sharpSphereRadius M E).choose (sharpRootRadius M E) : ℕ) +
        Real.logb 2 ((M - sharpSphereRadius M E).choose (sharpRootRadius M E) : ℕ) := by
    rw [sharpInternalDegree, Nat.cast_mul, Real.logb_mul hc1.ne' hc2.ne']
  rw [Nat.cast_sub hRle] at h2 h4
  rw [hmul]
  linarith

/-- The recombined logarithms are at most `8 E log₂ e`. -/
theorem sharp_recombined {M E : ℕ} (hv : SharpValid M E) :
    2 * (sharpRootRadius M E : ℝ) * Real.logb 2 ((M : ℝ) / (2 * sharpRootRadius M E)) -
        (sharpRootRadius M E : ℝ) *
          Real.logb 2 ((sharpSphereRadius M E : ℝ) / sharpRootRadius M E) -
        (sharpRootRadius M E : ℝ) *
          Real.logb 2 (((M : ℝ) - sharpSphereRadius M E) / sharpRootRadius M E) ≤
      8 * E * Real.logb 2 (Real.exp 1) := by
  obtain ⟨hr0, -, -, hw25, -, -, hR0, hRM, -⟩ := sharpParameters_valid hv
  have hM : (0 : ℝ) < M := by exact_mod_cast lt_of_lt_of_le (by positivity) (sharp_big hv).1
  have hR : (0 : ℝ) < sharpSphereRadius M E := by exact_mod_cast hR0
  have hMR : (0 : ℝ) < (M : ℝ) - sharpSphereRadius M E := by
    have : (2 * sharpSphereRadius M E : ℝ) < M := by exact_mod_cast hRM
    linarith
  have hr : (0 : ℝ) < sharpRootRadius M E := by exact_mod_cast hr0
  rw [log_recombine hM hR hMR hr, sharp_four_R_MR hv]
  have h8 : 8 * (sharpShift M E : ℝ) ^ 2 ≤ (M : ℝ) ^ 2 := by
    have h : (2 ^ 25 * sharpShift M E : ℕ) ≤ M := hw25
    have h' : (2 : ℝ) ^ 25 * sharpShift M E ≤ M := by exact_mod_cast h
    have hw : (0 : ℝ) ≤ sharpShift M E := Nat.cast_nonneg _
    nlinarith
  have hwr : (sharpShift M E : ℝ) ^ 2 ≤ M * sharpRootRadius M E := by
    have h := sharp_shift_sq_le M E
    rw [sq]
    exact_mod_cast h
  have hrE : (sharpRootRadius M E : ℝ) ^ 2 ≤ M * E := by
    have h := Nat.sqrt_le' (M * E)
    exact_mod_cast h
  exact sqrt_gap_log_bound hM h8 hwr hr.le hrE

/-- `r²/R + r²/(M - R) ≤ (16/3) E`. -/
theorem sharp_inv_terms {M E : ℕ} (hv : SharpValid M E) :
    (sharpRootRadius M E : ℝ) ^ 2 / sharpSphereRadius M E +
        (sharpRootRadius M E : ℝ) ^ 2 / ((M : ℝ) - sharpSphereRadius M E) ≤
      16 / 3 * E := by
  have hM : (0 : ℝ) < M := by exact_mod_cast lt_of_lt_of_le (by positivity) (sharp_big hv).1
  obtain ⟨h1, h2⟩ := sharp_R_bounds hv
  have hrE : (sharpRootRadius M E : ℝ) ^ 2 ≤ M * E := by
    have h := Nat.sqrt_le' (M * E)
    exact_mod_cast h
  exact inv_sum_bound hM h1 h2 hrE

/-- **Score gap, exact form** (`eq:ham-gap`):
`a - d ≤ (8 + 16/3) E log₂ e + 2m + 1`, with `a = log₂ D_a`, `d = ⌊log₂ D_i⌋`. -/
theorem sharp_gap_le {M E : ℕ} (hv : SharpValid M E) :
    sharpLogAmbient M E - sharpLogInternalDegree M E ≤
      (8 + 16 / 3) * E * Real.logb 2 (Real.exp 1) + 2 * headerLog M + 1 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hDi0, -⟩ := sharpParameters_valid hv
  have hA := sharp_logAmbient_le hv
  have hI := sharp_logInternal_ge hv
  have hd : Real.logb 2 (sharpInternalDegree M E) < (sharpLogInternalDegree M E : ℝ) + 1 :=
    logb_lt_natLog_add_one hDi0.ne'
  have hrec := sharp_recombined hv
  have hle : (0 : ℝ) ≤ Real.logb 2 (Real.exp 1) := by linarith [logb_two_exp_bounds.1]
  have hX := mul_le_mul_of_nonneg_right (sharp_inv_terms hv) hle
  linarith

/-- **Score gap** (`eq:ham-gap`): `a - d < 20 E + 2m + 1`. -/
theorem sharp_gap_lt {M E : ℕ} (hv : SharpValid M E) :
    sharpLogAmbient M E - sharpLogInternalDegree M E < 20 * E + 2 * headerLog M + 1 := by
  have h1 := sharp_gap_le hv
  have h2 := logb_two_exp_bounds.2
  have hE : (1 : ℝ) ≤ E := by exact_mod_cast hv.2.1
  have h3 := mul_lt_mul_of_pos_left h2 (by linarith : (0 : ℝ) < (8 + 16 / 3) * E)
  linarith

/-- **Internal degree exponent from below**: `97 r ≤ d` (the blueprint's `d ≥ 97 r - 1`):
`R ≥ 2⁴⁸ r` and `M - R ≥ 2⁴⁹ r`, so `D_i ≥ (2⁴⁸)^r (2⁴⁹)^r = 2^(97 r)`. -/
theorem sharp_logDegree_lower {M E : ℕ} (hv : SharpValid M E) :
    97 * sharpRootRadius M E ≤ sharpLogInternalDegree M E := by
  obtain ⟨hr0, hr50, -, hw25, -, hRw, -, hRM, -, -, -, -, hM2, -⟩ := sharpParameters_valid hv
  have hR48 : 2 ^ 48 * sharpRootRadius M E ≤ sharpSphereRadius M E := by
    norm_num at hr50 hw25 ⊢
    omega
  have hMR49 : 2 ^ 49 * sharpRootRadius M E ≤ M - sharpSphereRadius M E := by
    norm_num at hr50 hw25 ⊢
    omega
  have h1 := pow_le_choose_of_mul_le hr0 hR48
  have h2 := pow_le_choose_of_mul_le hr0 hMR49
  apply Nat.le_log_of_pow_le one_lt_two
  calc 2 ^ (97 * sharpRootRadius M E) =
        (2 ^ 48) ^ sharpRootRadius M E * (2 ^ 49) ^ sharpRootRadius M E := by
        rw [← pow_mul, ← pow_mul, ← pow_add]
        ring_nf
    _ ≤ sharpInternalDegree M E := Nat.mul_le_mul h1 h2

/-- **Internal degree exponent from above**: `d ≤ M`. -/
theorem sharp_logDegree_le_M {M E : ℕ} (hv : SharpValid M E) :
    sharpLogInternalDegree M E ≤ M := by
  obtain ⟨-, -, -, -, -, -, -, hRM, -⟩ := sharpParameters_valid hv
  have h : sharpInternalDegree M E ≤ 2 ^ M := by
    unfold sharpInternalDegree
    calc _ ≤ 2 ^ sharpSphereRadius M E * 2 ^ (M - sharpSphereRadius M E) :=
          Nat.mul_le_mul (Nat.choose_le_two_pow _ _) (Nat.choose_le_two_pow _ _)
      _ = 2 ^ M := by rw [← pow_add, Nat.add_sub_of_le (by omega)]
  calc sharpLogInternalDegree M E ≤ Nat.log 2 (2 ^ M) := Nat.log_mono_right h
    _ = M := Nat.log_pow one_lt_two M

/-- **Uniform growth of `T / m`**: for every constant `C` there is a cutoff `M₀`, depending only
on `C`, such that `C ⌈log₂ (M + 2)⌉ ≤ T = ⌊⌊√(M E)⌋ / 10⁶⌋` for all `M ≥ M₀` and all `E ≥ 1`. -/
theorem sharp_growth (C : ℕ) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ E : ℕ, 1 ≤ E → C * headerLog M ≤ mergerBudget M E := by
  obtain ⟨j₀, hj₀⟩ := exists_linear_le_two_pow (10 ^ 6 * C)
  refine ⟨2 ^ (2 * j₀) + 1, fun M hM E hE => ?_⟩
  have hpos : 0 < 2 ^ (2 * j₀) := by positivity
  have hM0 : M ≠ 0 := by omega
  have hk : 2 * j₀ ≤ Nat.log 2 M := Nat.le_log_of_pow_le one_lt_two (by omega)
  have hj := hj₀ (Nat.log 2 M / 2) (by omega)
  have hH := headerLog_le_natLog_add_two M
  have hME : Nat.sqrt M ≤ Nat.sqrt (M * E) := Nat.sqrt_le_sqrt (Nat.le_mul_of_pos_right M hE)
  rw [mergerBudget, Nat.le_div_iff_mul_le (by norm_num)]
  calc C * headerLog M * 10 ^ 6 = 10 ^ 6 * C * headerLog M := by ring
    _ ≤ 10 ^ 6 * C * (2 * (Nat.log 2 M / 2) + 3) := Nat.mul_le_mul_left _ (by omega)
    _ ≤ 2 ^ (Nat.log 2 M / 2) := hj
    _ ≤ Nat.sqrt M := two_pow_half_log_le_sqrt hM0
    _ ≤ Nat.sqrt (M * E) := hME

/-- **Near-equator calibration** (blueprint node L24): the bundle of the uniform radius, entropy
and degree estimates.  For valid `M, E` (no cutoff): `r ≥ √(M E)/2`, `2⁵⁰ E ≤ r`, `w² ≤ M r`,
`w ≥ √(M r)/2`, `0.72 r ≤ Δ ≤ 5 r`, `M - K > 0.35 r`, `K - log₂ N > 0.35 r`,
`a - d < 20 E + 2m + 1`, `97 r ≤ d ≤ M`; and the uniform growth `C m ≤ T` beyond a cutoff
depending only on `C`. -/
theorem nearEquatorCalibration :
    (∀ M E : ℕ, SharpValid M E →
      Real.sqrt ((M : ℝ) * E) / 2 ≤ sharpRootRadius M E ∧
      2 ^ 50 * E ≤ sharpRootRadius M E ∧
      sharpShift M E * sharpShift M E ≤ M * sharpRootRadius M E ∧
      Real.sqrt ((M : ℝ) * sharpRootRadius M E) / 2 ≤ sharpShift M E ∧
      72 / 100 * (sharpRootRadius M E : ℝ) ≤ sharpDeficit M E ∧
      sharpDeficit M E ≤ 5 * (sharpRootRadius M E : ℝ) ∧
      35 / 100 * (sharpRootRadius M E : ℝ) < (M : ℝ) - sharpThreshold M E ∧
      35 / 100 * (sharpRootRadius M E : ℝ) <
        (sharpThreshold M E : ℝ) - Real.logb 2 (sharpSphereCard M E) ∧
      sharpLogAmbient M E - sharpLogInternalDegree M E < 20 * E + 2 * headerLog M + 1 ∧
      97 * sharpRootRadius M E ≤ sharpLogInternalDegree M E ∧
      sharpLogInternalDegree M E ≤ M) ∧
    ∀ C : ℕ, ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ E : ℕ, 1 ≤ E →
      C * headerLog M ≤ mergerBudget M E :=
  ⟨fun _ _ hv => ⟨sharp_root_lower hv, sharp_tolerance_le hv, sharp_shift_sq_le _ _,
    sharp_shift_lower hv, sharp_deficit_lower hv, sharp_deficit_upper hv,
    (sharp_game_margins hv).1, (sharp_game_margins hv).2, sharp_gap_lt hv,
    sharp_logDegree_lower hv, sharp_logDegree_le_M hv⟩, sharp_growth⟩

/-! ### L25: the sharp game hypotheses -/

/-- **Density from an exponent comparison**: if `K + τ + 2 ≤ 2^(L+2)` and `K + τ + L + 10 ≤ M`
then `256 (2^K + (K+τ+1) 2^(K+τ)) ≤ 2^M`.

Proof sketch: `2^K ≤ 2^(K+τ)` (`Nat.pow_le_pow_right`), so the left side is at most
`2⁸ (K+τ+2) 2^(K+τ) ≤ 2⁸ 2^(L+2) 2^(K+τ) = 2^(K+τ+L+10) ≤ 2^M` (`pow_add`).
Reference: tex 1579-1582 (`eq:ham-game-density`); node L25. -/
theorem density_of_exponent {K τ M L : ℕ} (h1 : K + τ + 2 ≤ 2 ^ (L + 2))
    (h2 : K + τ + L + 10 ≤ M) : 256 * (2 ^ K + (K + τ + 1) * 2 ^ (K + τ)) ≤ 2 ^ M := by
  have hK : 2 ^ K ≤ 2 ^ (K + τ) := Nat.pow_le_pow_right (by norm_num) (by omega)
  calc 256 * (2 ^ K + (K + τ + 1) * 2 ^ (K + τ))
      ≤ 2 ^ 8 * ((K + τ + 2) * 2 ^ (K + τ)) := by nlinarith
    _ ≤ 2 ^ 8 * (2 ^ (L + 2) * 2 ^ (K + τ)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h1)
    _ = 2 ^ (8 + (L + 2 + (K + τ))) := by rw [← pow_add, ← pow_add]
    _ ≤ 2 ^ M := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- **Charge from an exponent comparison**: if `K + τ + 1 ≤ 2^(L+2)` and `τ + L + 2 ≤ δ` then
`(K+τ+1) 2^(K+τ) ≤ 2^(K+δ)`.

Proof sketch: `(K+τ+1) 2^(K+τ) ≤ 2^(L+2) 2^(K+τ) = 2^(K+τ+L+2) ≤ 2^(K+δ)`
(`Nat.mul_le_mul_right`, `pow_add`, `Nat.pow_le_pow_right`).
Reference: tex 1583-1584 (`δ - τ ≥ 0.000094 r - 1`); node L25. -/
theorem charge_of_exponent {K τ δ L : ℕ} (h1 : K + τ + 1 ≤ 2 ^ (L + 2))
    (h2 : τ + L + 2 ≤ δ) : (K + τ + 1) * 2 ^ (K + τ) ≤ 2 ^ (K + δ) := by
  calc (K + τ + 1) * 2 ^ (K + τ) ≤ 2 ^ (L + 2) * 2 ^ (K + τ) := Nat.mul_le_mul_right _ h1
    _ = 2 ^ (L + 2 + (K + τ)) := (pow_add _ _ _).symm
    _ ≤ 2 ^ (K + δ) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- **Arrivals from an exponent comparison**: if `N < 2^(b+1)` and `b + S + 2 ≤ K` then
`N 2^(S+1) ≤ 2^K`.

Proof sketch: `N 2^(S+1) ≤ 2^(b+1) 2^(S+1) = 2^(b+S+2) ≤ 2^K`.
Reference: tex 1582-1583 (`eq:ham-game-arrivals` from the margin); node L25. -/
theorem arrivals_of_exponent {N b S K : ℕ} (hN : N < 2 ^ (b + 1)) (h : b + S + 2 ≤ K) :
    N * 2 ^ (S + 1) ≤ 2 ^ K := by
  calc N * 2 ^ (S + 1) ≤ 2 ^ (b + 1) * 2 ^ (S + 1) := Nat.mul_le_mul_right _ hN.le
    _ = 2 ^ (b + 1 + (S + 1)) := (pow_add _ _ _).symm
    _ ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- **Near-pair volume**: `V(M, M/1024 - 1) ≤ 2^(M/64)` for `1024 ∣ M`, `M > 0`.

Proof sketch: with `h = M/1024 ≥ 1`, `logb_hammingVol_le` gives
`log₂ V(M, h - 1) ≤ h log₂ (e M / h) = h log₂ (1024 e) ≤ 16 h = M / 64` (`M / h = 1024`,
`1024 e < 2¹⁶`, `Real.exp_one_lt_d9`); then `Real.logb_le_iff_le_rpow` and a cast.
Reference: tex 1603-1606 (`log V(M, h-1) ≤ h log(eM/h) < 0.012 M`); node L25 (uses L10). -/
theorem hammingVol_le_two_pow_div64 {M : ℕ} (hM : 1024 ∣ M) (hM0 : 0 < M) :
    hammingVol M (M / 1024 - 1) ≤ 2 ^ (M / 64) := by
  obtain ⟨t, rfl⟩ := hM
  have ht : 1 ≤ t := by omega
  have hdiv : 1024 * t / 1024 = t := by omega
  have hdiv64 : 1024 * t / 64 = 16 * t := by omega
  rw [hdiv, hdiv64]
  have h := logb_hammingVol_le (1024 * t) t ht (by omega)
  have ht' : (t : ℝ) ≠ 0 := by exact_mod_cast (by omega : t ≠ 0)
  have he : Real.exp 1 * ((1024 * t : ℕ) : ℝ) / t = 1024 * Real.exp 1 := by
    push_cast
    field_simp
  rw [he] at h
  have h1024 : Real.logb 2 (1024 * Real.exp 1) ≤ 16 := by
    rw [Real.logb_le_iff_le_rpow one_lt_two (by positivity),
      show (16 : ℝ) = ((16 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have := Real.exp_one_lt_d9
    norm_num at this ⊢
    linarith
  have hV : (0 : ℝ) < hammingVol (1024 * t) (t - 1) := by exact_mod_cast hammingVol_pos _ _
  have h2 : Real.logb 2 (hammingVol (1024 * t) (t - 1)) ≤ ((16 * t : ℕ) : ℝ) := by
    push_cast
    have := mul_le_mul_of_nonneg_left h1024 (Nat.cast_nonneg (α := ℝ) t)
    linarith
  rw [Real.logb_le_iff_le_rpow one_lt_two hV, Real.rpow_natCast] at h2
  exact_mod_cast h2

/-- **The near-pair term**: if `V ≤ 2^k` and `a + k + 9 ≤ ℓ` then `2^a V / 2^ℓ ≤ 1/512`.

Proof sketch: in `ℕ`, `512 · 2^a V ≤ 2^(a+k+9) ≤ 2^ℓ`; cast and divide by `2^ℓ > 0`
(`div_le_iff₀`, `pow_add`).
Reference: tex 1603-1609; node L25. -/
theorem two_pow_mul_vol_le {a ℓ k V : ℕ} (hV : V ≤ 2 ^ k) (h : a + k + 9 ≤ ℓ) :
    (2 : ℝ) ^ a * ((V : ℝ) / 2 ^ ℓ) ≤ 1 / 512 := by
  have hnat : 512 * (2 ^ a * V) ≤ 2 ^ ℓ := by
    calc 512 * (2 ^ a * V) ≤ 2 ^ 9 * (2 ^ a * 2 ^ k) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hV)
      _ = 2 ^ (9 + (a + k)) := by rw [← pow_add, ← pow_add]
      _ ≤ 2 ^ ℓ := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hreal : (512 : ℝ) * (2 ^ a * V) ≤ 2 ^ ℓ := by exact_mod_cast hnat
  have hpos : (0 : ℝ) < 2 ^ ℓ := by positivity
  rw [mul_div_assoc', div_le_iff₀ hpos]
  linarith

/-- **The collision factor**: `β = 2 √(ρ (1 - ρ)) ≤ exp(-2 α²)` at the sharp radius.

Proof sketch: `ρ = 1/2 - α` (`sharp_rho_eq`), so `4 ρ (1 - ρ) = 1 - 4 α²` and
`β = √(4 ρ (1 - ρ))` (`Real.sqrt_mul_self`, `Real.sqrt_mul`); `1 - 4α² ≤ exp(-4α²)`
(`Real.add_one_le_exp`) and `√(exp(-4α²)) = exp(-2α²)` (`Real.sqrt_eq_iff`, `Real.exp_add`).
Reference: tex 1591-1596 (`β = √(1 - 4α²)`, `-log β ≥ 2 α² log e`); node L25. -/
theorem sharp_beta_le_exp {M E : ℕ} (hv : SharpValid M E) :
    collisionBeta M (sharpSphereRadius M E) ≤ Real.exp (-2 * sharpAlpha M E ^ 2) := by
  obtain ⟨hα0, hα1⟩ := sharp_alpha_bounds hv
  rw [collisionBeta, sharp_rho_eq hv]
  have hx : (1 / 2 - sharpAlpha M E) * (1 - (1 / 2 - sharpAlpha M E)) =
      (1 - 4 * sharpAlpha M E ^ 2) / 4 := by ring
  rw [hx]
  have h2 : 1 - 4 * sharpAlpha M E ^ 2 ≤ Real.exp (-4 * sharpAlpha M E ^ 2) := by
    have := Real.add_one_le_exp (-4 * sharpAlpha M E ^ 2)
    linarith
  have he : Real.exp (-2 * sharpAlpha M E ^ 2) ^ 2 = Real.exp (-4 * sharpAlpha M E ^ 2) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hepos := Real.exp_pos (-2 * sharpAlpha M E ^ 2)
  have h3 : (1 - 4 * sharpAlpha M E ^ 2) / 4 ≤ (Real.exp (-2 * sharpAlpha M E ^ 2) / 2) ^ 2 := by
    rw [div_pow, he]
    linarith
  have h4 := Real.sqrt_le_sqrt h3
  rw [Real.sqrt_sq (by positivity)] at h4
  linarith

/-- **Decay of the collision term**: `β^h ≤ exp(-r/2048)` with `h = M/1024`, since
`β ≤ exp(-2α²)` and `2 α² h = (M α²)/512 ≥ r/2048` (`sharp_alpha_sq_lower`). -/
theorem sharp_beta_pow_le {M E : ℕ} (hv : SharpValid M E) :
    collisionBeta M (sharpSphereRadius M E) ^ (M / 1024) ≤
      Real.exp (-((sharpRootRadius M E : ℝ) / 2048)) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hM1024, -⟩ := sharpParameters_valid hv
  have hβ0 := (collisionBeta_nonneg_le_one M (sharpSphereRadius M E)).1
  have hβ := sharp_beta_le_exp hv
  have h3 := sharp_alpha_sq_lower hv
  have hpow : collisionBeta M (sharpSphereRadius M E) ^ (M / 1024) ≤
      Real.exp (-2 * sharpAlpha M E ^ 2) ^ (M / 1024) := pow_le_pow_left₀ hβ0 hβ _
  rw [← Real.exp_nat_mul] at hpow
  refine hpow.trans (Real.exp_le_exp.2 ?_)
  have hcast : ((M / 1024 : ℕ) : ℝ) = (M : ℝ) / 1024 := by
    have h : (M : ℝ) = 1024 * ((M / 1024 : ℕ) : ℝ) := by exact_mod_cast hM1024
    rw [h]
    ring
  rw [hcast]
  nlinarith

/-- **The collision term**: if `1420 (a + 9) ≤ r` then `2^a exp(-r/2048) ≤ 1/512`.

Proof sketch: `2^(a+9) = exp((a + 9) ln 2)` and `(a + 9) ln 2 ≤ 1420 (a + 9) / 2048 ≤ r / 2048`
(`Real.log_two_lt_d9`: `2048 ln 2 < 1420`); so `2^a exp(-r/2048) ≤ 2^a 2^(-(a+9)) = 1/512`
(`Real.exp_le_exp`, `Real.rpow_natCast`, `Real.exp_log`).
Reference: tex 1597-1601 (`-h log β > 0.0007 r` against `S + δ + 1 ≤ 0.000103 r + 1`);
node L25. -/
theorem two_pow_mul_exp_le {a r : ℕ} (h : 1420 * (a + 9) ≤ r) :
    (2 : ℝ) ^ a * Real.exp (-((r : ℝ) / 2048)) ≤ 1 / 512 := by
  have hl := Real.log_two_lt_d9
  norm_num at hl
  have h2 : (2 : ℝ) ^ (a + 9) = Real.exp (((a + 9 : ℕ) : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  have hr : ((a + 9 : ℕ) : ℝ) * Real.log 2 ≤ (r : ℝ) / 2048 := by
    have h' : (1420 : ℝ) * ((a + 9 : ℕ) : ℝ) ≤ r := by exact_mod_cast h
    have hpos : (0 : ℝ) ≤ ((a + 9 : ℕ) : ℝ) := Nat.cast_nonneg _
    have := mul_le_mul_of_nonneg_left hl.le hpos
    linarith
  have h3 : (2 : ℝ) ^ (a + 9) ≤ Real.exp ((r : ℝ) / 2048) := by
    rw [h2]
    exact Real.exp_le_exp.2 hr
  have hpos : 0 < Real.exp ((r : ℝ) / 2048) := Real.exp_pos _
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ hpos]
  have e : (2 : ℝ) ^ (a + 9) = 2 ^ a * 512 := by
    rw [pow_add]
    norm_num
  linarith

/-- The sharp threshold is at most `M` (`b = ⌊log₂ N⌋ ≤ M` as `N ≤ 2^M`). -/
theorem sharp_threshold_le (M E : ℕ) : sharpThreshold M E ≤ M := by
  have hb : sharpLogSphereCard M E ≤ M := by
    calc sharpLogSphereCard M E ≤ Nat.log 2 (2 ^ M) :=
          Nat.log_mono_right (Nat.choose_le_two_pow _ _)
      _ = M := Nat.log_pow one_lt_two M
  unfold sharpThreshold
  omega

/-- **Integer margins**: `35 r < 100 (M - K)` and `35 r < 100 (K - b)`, `b = ⌊log₂ N⌋`. -/
theorem sharp_margins_nat {M E : ℕ} (hv : SharpValid M E) :
    35 * sharpRootRadius M E < 100 * (M - sharpThreshold M E) ∧
      35 * sharpRootRadius M E < 100 * (sharpThreshold M E - sharpLogSphereCard M E) := by
  obtain ⟨h1, h2⟩ := sharp_game_margins hv
  have hb1 : (sharpLogSphereCard M E : ℝ) ≤ Real.logb 2 (sharpSphereCard M E) :=
    natLog_le_logb _
  have hKM := sharp_threshold_le M E
  have hbK : sharpLogSphereCard M E ≤ sharpThreshold M E := by
    have : (sharpLogSphereCard M E : ℝ) < sharpThreshold M E := by
      have hr : (0 : ℝ) ≤ sharpRootRadius M E := Nat.cast_nonneg _
      linarith
    exact_mod_cast this.le
  constructor
  · have h : (35 * sharpRootRadius M E : ℝ) < 100 * ((M : ℝ) - sharpThreshold M E) := by
      linarith
    rw [← Nat.cast_sub hKM] at h
    exact_mod_cast h
  · have h : (35 * sharpRootRadius M E : ℝ) <
        100 * ((sharpThreshold M E : ℝ) - sharpLogSphereCard M E) := by
      linarith
    rw [← Nat.cast_sub hbK] at h
    exact_mod_cast h

/-- **Density inequality at the sharp parameters**. -/
theorem sharp_density {M E : ℕ} (hv : SharpValid M E) :
    256 * (2 ^ sharpThreshold M E + (sharpThreshold M E + 6 * mergerBudget M E + 1) *
      2 ^ (sharpThreshold M E + 6 * mergerBudget M E)) ≤ 2 ^ M := by
  obtain ⟨-, hr50, -⟩ := sharpParameters_valid hv
  obtain ⟨hM, hr⟩ := sharp_big hv
  have hlog := sharp_log_small hv
  have hmar := (sharp_margins_nat hv).1
  have hKM := sharp_threshold_le M E
  have hMlt : M < 2 ^ (Nat.log 2 M + 1) := Nat.lt_pow_succ_log_self one_lt_two M
  have hT : mergerBudget M E = sharpRootRadius M E / 1000000 := rfl
  rw [hT]
  apply density_of_exponent (L := Nat.log 2 M)
  · have h2 : 2 ^ (Nat.log 2 M + 2) = 2 * 2 ^ (Nat.log 2 M + 1) := by ring
    norm_num at hr50 hM hr hlog
    omega
  · norm_num at hr50 hM hr hlog
    omega

/-- **Charge inequality at the sharp parameters**. -/
theorem sharp_charge {M E : ℕ} (hv : SharpValid M E) :
    (sharpThreshold M E + 6 * mergerBudget M E + 1) *
        2 ^ (sharpThreshold M E + 6 * mergerBudget M E) ≤
      2 ^ (sharpThreshold M E + sharpRootRadius M E / 10000) := by
  obtain ⟨-, hr50, -⟩ := sharpParameters_valid hv
  obtain ⟨hM, hr⟩ := sharp_big hv
  have hlog := sharp_log_small hv
  have hKM := sharp_threshold_le M E
  have hMlt : M < 2 ^ (Nat.log 2 M + 1) := Nat.lt_pow_succ_log_self one_lt_two M
  have hT : mergerBudget M E = sharpRootRadius M E / 1000000 := rfl
  rw [hT]
  apply charge_of_exponent (L := Nat.log 2 M)
  · have h2 : 2 ^ (Nat.log 2 M + 2) = 2 * 2 ^ (Nat.log 2 M + 1) := by ring
    norm_num at hr50 hM hr hlog
    omega
  · norm_num at hr50 hM hr hlog
    omega

/-- **Arrival inequality at the sharp parameters**. -/
theorem sharp_arrivals {M E : ℕ} (hv : SharpValid M E) :
    M.choose (sharpSphereRadius M E) * 2 ^ (3 * mergerBudget M E + 1) ≤
      2 ^ sharpThreshold M E := by
  obtain ⟨hM, hr⟩ := sharp_big hv
  have hmar := (sharp_margins_nat hv).2
  have hT : mergerBudget M E = sharpRootRadius M E / 1000000 := rfl
  rw [hT]
  apply arrivals_of_exponent (b := sharpLogSphereCard M E)
  · exact Nat.lt_pow_succ_log_self one_lt_two _
  · norm_num at hr
    omega

/-- **Heavy inequality at the sharp parameters**: `2^(S+1) θ ≤ 1/256`, split into the
near-pair term and the collision term, each at most `1/512`. -/
theorem sharp_heavy {M E : ℕ} (hv : SharpValid M E) :
    (2 : ℝ) ^ (3 * mergerBudget M E + 1) *
        heavyTheta M (sharpSphereRadius M E) (M / 8) (sharpRootRadius M E / 10000) (M / 1024) ≤
      1 / 256 := by
  obtain ⟨-, hr50, -, -, -, -, -, -, -, -, -, -, -, -, hM1024, -⟩ := sharpParameters_valid hv
  obtain ⟨hM, hr⟩ := sharp_big hv
  have hT : mergerBudget M E = sharpRootRadius M E / 1000000 := rfl
  have hV := hammingVol_le_two_pow_div64 (M := M) (Nat.dvd_of_mod_eq_zero (by omega))
    (lt_of_lt_of_le (by positivity) hM)
  have hVterm := two_pow_mul_vol_le
    (a := 3 * (sharpRootRadius M E / 1000000) + 1 + sharpRootRadius M E / 10000)
    (ℓ := M / 8) hV (by norm_num at hr50 hM hr; omega)
  have hβ := sharp_beta_pow_le hv
  have hexp := two_pow_mul_exp_le
    (a := 3 * (sharpRootRadius M E / 1000000) + 1 + sharpRootRadius M E / 10000)
    (r := sharpRootRadius M E) (by norm_num at hr; omega)
  have hβterm : (2 : ℝ) ^ (3 * (sharpRootRadius M E / 1000000) + 1 +
        sharpRootRadius M E / 10000) * collisionBeta M (sharpSphereRadius M E) ^ (M / 1024) ≤
      1 / 512 := le_trans (mul_le_mul_of_nonneg_left hβ (by positivity)) hexp
  rw [hT, heavyTheta]
  have e : (2 : ℝ) ^ (3 * (sharpRootRadius M E / 1000000) + 1) *
      (2 ^ (sharpRootRadius M E / 10000) *
        ((hammingVol M (M / 1024 - 1) : ℝ) / 2 ^ (M / 8) +
          collisionBeta M (sharpSphereRadius M E) ^ (M / 1024))) =
      (2 : ℝ) ^ (3 * (sharpRootRadius M E / 1000000) + 1 + sharpRootRadius M E / 10000) *
          ((hammingVol M (M / 1024 - 1) : ℝ) / 2 ^ (M / 8)) +
        (2 : ℝ) ^ (3 * (sharpRootRadius M E / 1000000) + 1 + sharpRootRadius M E / 10000) *
          collisionBeta M (sharpSphereRadius M E) ^ (M / 1024) := by
    rw [pow_add (2 : ℝ) (3 * (sharpRootRadius M E / 1000000) + 1)]
    ring
  rw [e]
  linarith

/-- **The sharp game hypotheses** (blueprint node L25): beyond one cutoff `M₀`, for every valid
`M, E` the four game inequalities `ReservoirInequalities` hold at the sharp parameters
`R, K, S = 3T, τ = 6T, ℓ = M/8, δ = ⌊r/10⁴⌋, h = M/1024`.  (The cutoff is `M₀ = 0`: the valid
domain already forces `M ≥ 2¹⁰⁰`.) -/
theorem sharpGameHypotheses :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ E : ℕ, SharpValid M E →
      ReservoirInequalities M (sharpSphereRadius M E) (sharpThreshold M E)
        (3 * mergerBudget M E) (6 * mergerBudget M E) (M / 8) (sharpRootRadius M E / 10000)
        (M / 1024) :=
  ⟨0, fun _ _ _ hv => ⟨sharp_density hv, sharp_heavy hv, sharp_charge hv, sharp_arrivals hv⟩⟩

end Kolmogorov.StrongMerging.Lower
