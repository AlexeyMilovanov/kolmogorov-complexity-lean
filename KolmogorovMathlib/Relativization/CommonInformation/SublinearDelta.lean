/-
Copyright (c) 2026 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Relativization.CommonInformation.MutualInformationBounds

/-!
# Sublinear Delta

This module proves sublinear growth estimates used to construct round schedules and error budgets
for the relativized common-information arguments. It formalizes the budget and iteration steps of
Theorem 2 in Muchnik and Romashchenko's paper on stability under relativization.
-/

namespace Kolmogorov.Relativization
open Filter Asymptotics

/-- The logarithmic slack is sublinear as a function of its argument. -/
private theorem theorem2_choose_rounds_logSlack_sublinear
    (c : ℕ) :
    (fun N : ℕ => (logSlack c N : ℝ)) =o[atTop] fun N : ℕ => (N : ℝ) := by
  have hLogShift :
      (fun N : ℕ => Real.log ((N : ℝ) + 1)) =o[atTop]
        fun N : ℕ => (N : ℝ) + 1 :=
    Real.isLittleO_log_id_atTop.comp_tendsto
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hPlus :
      (fun N : ℕ => (N : ℝ) + 1) =O[atTop] fun N : ℕ => (N : ℝ) := by
    apply Asymptotics.isBigO_iff.mpr
    refine ⟨2, ?_⟩
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    have hNReal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hbound : (N : ℝ) + 1 ≤ 2 * (N : ℝ) := by linarith
    have hnormL : ‖(N : ℝ) + 1‖ = (N : ℝ) + 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hnormR : ‖(N : ℝ)‖ = (N : ℝ) := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by exact_mod_cast (Nat.zero_le N))]
    rw [hnormL, hnormR]
    linarith
  have hLogNat :
      (fun N : ℕ => Real.log ((N : ℝ) + 1)) =o[atTop]
        fun N : ℕ => (N : ℝ) := hLogShift.trans_isBigO hPlus
  have hLogb :
      (fun N : ℕ => Real.logb 2 ((N : ℝ) + 1)) =o[atTop]
        fun N : ℕ => (N : ℝ) := by
    have heq : (fun N : ℕ => Real.logb 2 ((N : ℝ) + 1)) =
        fun N : ℕ => (1 / Real.log 2) * Real.log ((N : ℝ) + 1) := by
      funext N
      rw [Real.logb]
      ring
    rw [heq]
    exact Asymptotics.IsLittleO.const_mul_left hLogNat (1 / Real.log 2)
  have hLogbPlus :
      (fun N : ℕ => Real.logb 2 ((N : ℝ) + 1) + 1) =o[atTop]
        fun N : ℕ => (N : ℝ) := by
    have hConstOne : (fun _ : ℕ => (1 : ℝ)) =o[atTop]
        fun N : ℕ => (N : ℝ) :=
      (Asymptotics.isLittleO_const_id_atTop (1 : ℝ)).comp_tendsto
        tendsto_natCast_atTop_atTop
    exact Asymptotics.IsLittleO.add hLogb hConstOne
  have hBits :
      (fun N : ℕ => ((Nat.bits (N + 1)).length : ℝ)) =o[atTop]
        fun N : ℕ => (N : ℝ) := by
    have hBound :
        (fun N : ℕ => ((Nat.bits (N + 1)).length : ℝ)) =O[atTop]
          fun N : ℕ => Real.logb 2 ((N : ℝ) + 1) + 1 := by
      apply Asymptotics.isBigO_iff.mpr
      refine ⟨1, ?_⟩
      filter_upwards [] with N
      have hLength := length_natBits_le_log (N + 1)
      have hLog := Real.natLog_le_logb (N + 1) 2
      have hLog' : (Nat.log 2 (N + 1) : ℝ) ≤
          Real.logb 2 ((N : ℝ) + 1) := by simpa using hLog
      have hLength' : ((Nat.bits (N + 1)).length : ℝ) ≤
          (Nat.log 2 (N + 1) : ℝ) + 1 := by exact_mod_cast hLength
      have hArg : (1 : ℝ) ≤ (N : ℝ) + 1 := by
        exact_mod_cast (show 1 ≤ N + 1 by omega)
      have hLogNonneg : 0 ≤ Real.logb 2 ((N : ℝ) + 1) :=
        Real.logb_nonneg (by norm_num) hArg
      have hFinal : ((Nat.bits (N + 1)).length : ℝ) ≤
          Real.logb 2 ((N : ℝ) + 1) + 1 := by linarith
      have hNormL : ‖((Nat.bits (N + 1)).length : ℝ)‖ =
          ((Nat.bits (N + 1)).length : ℝ) := by
        rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
      have hNormR : ‖Real.logb 2 ((N : ℝ) + 1) + 1‖ =
          Real.logb 2 ((N : ℝ) + 1) + 1 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      rw [hNormL, hNormR]
      simpa using hFinal
    exact hBound.trans_isLittleO hLogbPlus
  have hShift :
      (fun N : ℕ => (logSlack c (N + 1) : ℝ)) =o[atTop]
        fun N : ℕ => (N : ℝ) := by
    have heq : (fun N : ℕ => (logSlack c (N + 1) : ℝ)) =
        fun N : ℕ => (c : ℝ) * ((Nat.bits (N + 1)).length : ℝ) + c := by
      funext N
      simp [logSlack]
    rw [heq]
    have hConst : (fun _ : ℕ => (c : ℝ)) =o[atTop]
        fun N : ℕ => (N : ℝ) :=
      (Asymptotics.isLittleO_const_id_atTop (c : ℝ)).comp_tendsto
        tendsto_natCast_atTop_atTop
    exact Asymptotics.IsLittleO.add
      (Asymptotics.IsLittleO.const_mul_left hBits (c : ℝ)) hConst
  have hMono : ∀ N, (logSlack c N : ℝ) ≤ logSlack c (N + 1) := by
    intro N
    exact_mod_cast logSlack_mono_right c (Nat.le_succ N)
  rw [Asymptotics.isLittleO_iff] at hShift ⊢
  intro ε hε
  filter_upwards [hShift hε] with N hN
  have hNormMono : ‖(logSlack c N : ℝ)‖ ≤ ‖(logSlack c (N + 1) : ℝ)‖ := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (Nat.cast_nonneg _)]
    exact hMono N
  exact hNormMono.trans hN

/-- A growing round schedule whose exponential growth cost is sublinear, with each round bounded
by the input's bit length beyond a finite cutoff.
-/
private theorem theorem2_choose_rounds
    (f : ℕ → ℕ)
    (hf : (fun N : ℕ => (f N : ℝ)) =o[atTop] fun N : ℕ => (N : ℝ))
    (B : ℕ) :
    ∃ rounds : ℕ → ℕ, ∃ N₁ : ℕ,
      Tendsto rounds atTop atTop ∧
      (∀ N ≥ N₁, rounds N ≤ (Nat.bits N).length) ∧
      ((fun N : ℕ =>
        ((8 * 3 ^ (rounds N) * (f N + logSlack B N) : ℕ) : ℝ)) =o[atTop]
        fun N : ℕ => (N : ℝ)) := by
  have hSlack :
      (fun N : ℕ => (logSlack B N : ℝ)) =o[atTop] fun N : ℕ => (N : ℝ) :=
    theorem2_choose_rounds_logSlack_sublinear B
  let g : ℕ → ℕ := fun N => f N + logSlack B N
  let gPlus : ℕ → ℕ := fun N => g N + 1
  have hG : (fun N : ℕ => (g N : ℝ)) =o[atTop] fun N : ℕ => (N : ℝ) := by
    simpa [g, Nat.cast_add] using Asymptotics.IsLittleO.add hf hSlack
  have hOne : (fun _ : ℕ => (1 : ℝ)) =o[atTop] fun N : ℕ => (N : ℝ) :=
    (Asymptotics.isLittleO_const_id_atTop (1 : ℝ)).comp_tendsto
      tendsto_natCast_atTop_atTop
  have hGPlus : (fun N : ℕ => (gPlus N : ℝ)) =o[atTop] fun N : ℕ => (N : ℝ) := by
    simpa [gPlus, Nat.cast_add] using Asymptotics.IsLittleO.add hG hOne
  let rounds : ℕ → ℕ := fun N => Nat.log 9 (N / gPlus N)
  have hKey : ∀ k : ℕ, ∀ᶠ N : ℕ in atTop, 9 ^ k * gPlus N ≤ N := by
    intro k
    have hε : (0 : ℝ) < 1 / (2 * (9 : ℝ) ^ k) := by positivity
    have hsmall := (Asymptotics.isLittleO_iff.mp hGPlus) hε
    filter_upwards [hsmall] with N hsmall
    have hsmall' : (gPlus N : ℝ) ≤
        (1 / (2 * (9 : ℝ) ^ k)) * (N : ℝ) := by
      simpa [Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ (gPlus N : ℝ)),
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ))] using hsmall
    have hreal : ((9 ^ k * gPlus N : ℕ) : ℝ) ≤ (N : ℝ) := by
      have hk : 0 < (9 : ℝ) ^ k := by positivity
      have hmul := mul_le_mul_of_nonneg_left hsmall' hk.le
      have hhalf : (1 / 2 : ℝ) * (N : ℝ) ≤ (N : ℝ) := by
        nlinarith [show 0 ≤ (N : ℝ) from Nat.cast_nonneg N]
      calc
        ((9 ^ k * gPlus N : ℕ) : ℝ) =
            (9 : ℝ) ^ k * (gPlus N : ℝ) := by push_cast; rfl
        _ ≤
            (9 : ℝ) ^ k * ((1 / (2 * (9 : ℝ) ^ k)) * (N : ℝ)) := hmul
        _ = (1 / 2 : ℝ) * (N : ℝ) := by field_simp
        _ ≤ (N : ℝ) := hhalf
    exact_mod_cast hreal
  have hRounds : Tendsto rounds atTop atTop := by
    rw [tendsto_atTop]
    intro k
    filter_upwards [hKey k] with N hN
    dsimp [rounds]
    apply Nat.le_log_of_pow_le (by norm_num : 1 < 9)
    exact (Nat.le_div_iff_mul_le (by positivity : 0 < gPlus N)).2 hN
  have hCost : ∀ᶠ N : ℕ in atTop, 9 ^ rounds N * gPlus N ≤ N := by
    have hHalf := (Asymptotics.isLittleO_iff.mp hGPlus) (by norm_num : (0 : ℝ) < 1 / 2)
    filter_upwards [hHalf, Filter.eventually_ge_atTop 1] with N hHalf hN
    have hsmall : (gPlus N : ℝ) ≤ (1 / 2 : ℝ) * (N : ℝ) := by
      simpa [Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ (gPlus N : ℝ)),
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ))] using hHalf
    have hNreal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hgNreal : (gPlus N : ℝ) ≤ (N : ℝ) := by nlinarith [hsmall]
    have hgN : gPlus N ≤ N := by exact_mod_cast hgNreal
    have hqpos : 0 < N / gPlus N := Nat.div_pos hgN (by positivity)
    have hpow : 9 ^ rounds N ≤ N / gPlus N := by
      dsimp [rounds]
      exact Nat.pow_log_le_self 9 hqpos.ne'
    exact (Nat.le_div_iff_mul_le (by positivity : 0 < gPlus N)).1 hpow
  have hRoundsLe : ∀ N ≥ 1, rounds N ≤ (Nat.bits N).length := by
    intro N hN
    have hq : N / gPlus N ≤ N := Nat.div_le_self _ _
    have hpow9 : 9 ^ rounds N ≤ N := by
      by_cases hqpos : N / gPlus N = 0
      · simp [rounds, hqpos]
        omega
      · calc
          9 ^ rounds N ≤ N / gPlus N := by
            dsimp [rounds]
            exact Nat.pow_log_le_self 9 hqpos
          _ ≤ N := hq
    have hpow2 : 2 ^ rounds N ≤ N :=
      (Nat.pow_le_pow_left (by norm_num : 2 ≤ 9) _).trans hpow9
    exact (Nat.le_log_of_pow_le (by norm_num : 1 < 2) hpow2).trans
      (commonInfo_le_mutualInfo_natLog_le_bits N)
  have hGrowth :
      (fun N : ℕ => ((8 * 3 ^ rounds N * g N : ℕ) : ℝ)) =o[atTop]
        fun N : ℕ => (N : ℝ) := by
    rw [Asymptotics.isLittleO_iff]
    intro ε hε
    have hsmall := (Asymptotics.isLittleO_iff.mp hGPlus)
      (div_pos (sq_pos_of_pos hε) (by norm_num : (0 : ℝ) < 128))
    filter_upwards [hsmall, hCost] with N hsmall hCost
    let n : ℝ := (N : ℝ)
    let u : ℝ := (g N : ℝ)
    let H : ℝ := ((8 * 3 ^ rounds N * g N : ℕ) : ℝ)
    have hsmall' : u + 1 ≤ (ε ^ 2 / 128) * n := by
      have h' : (gPlus N : ℝ) ≤ (ε ^ 2 / 128) * (N : ℝ) := by
        simpa [Real.norm_eq_abs,
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ (gPlus N : ℝ)),
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ))] using hsmall
      simpa [u, n, gPlus, g, Nat.cast_add] using h'
    have hcost' : (9 : ℝ) ^ rounds N * (u + 1) ≤ n := by
      have hcast : ((9 ^ rounds N * gPlus N : ℕ) : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast hCost
      simpa [u, n, gPlus, g, Nat.cast_add] using hcast
    have hpow : ((3 : ℝ) ^ rounds N) ^ 2 = (9 : ℝ) ^ rounds N := by
      rw [← pow_mul, Nat.mul_comm (rounds N) 2, pow_mul]
      norm_num
    have hbase : (((3 : ℝ) ^ rounds N) * u) ^ 2 ≤ n * (u + 1) := by
      have hcostmul := mul_le_mul_of_nonneg_right hcost' (by positivity : 0 ≤ u + 1)
      have hu0 : 0 ≤ u := by positivity
      have hu : u ^ 2 ≤ (u + 1) ^ 2 := by nlinarith
      calc
        (((3 : ℝ) ^ rounds N) * u) ^ 2 =
            (9 : ℝ) ^ rounds N * u ^ 2 := by rw [mul_pow, hpow]
        _ ≤ (9 : ℝ) ^ rounds N * (u + 1) ^ 2 :=
            mul_le_mul_of_nonneg_left hu (by positivity)
        _ = ((9 : ℝ) ^ rounds N * (u + 1)) * (u + 1) := by ring
        _ ≤ n * (u + 1) := hcostmul
    have hHdef : H = 8 * ((3 : ℝ) ^ rounds N) * u := by
      dsimp [H, u]
      push_cast
      ring
    have hHsq : H ^ 2 ≤ 64 * n * (u + 1) := by
      rw [hHdef]
      calc
        (8 * ((3 : ℝ) ^ rounds N) * u) ^ 2 =
            64 * (((3 : ℝ) ^ rounds N) * u) ^ 2 := by ring
        _ ≤ 64 * (n * (u + 1)) :=
            mul_le_mul_of_nonneg_left hbase (by norm_num)
        _ = 64 * n * (u + 1) := by ring
    have hbudget : 64 * n * (u + 1) ≤ (ε * n) ^ 2 := by
      have hmul := mul_le_mul_of_nonneg_left hsmall' (by positivity : 0 ≤ 64 * n)
      nlinarith [hmul]
    have htarget : H ≤ ε * n := by
      by_contra hnot
      have hlt : ε * n < H := lt_of_not_ge hnot
      have hεn : 0 ≤ ε * n := mul_nonneg hε.le (by positivity)
      have hsum : 0 < H + ε * n := by linarith
      have hprod : 0 < (H - ε * n) * (H + ε * n) :=
        mul_pos (sub_pos.mpr hlt) hsum
      nlinarith [hHsq.trans hbudget, hprod]
    have hnorm : ‖H‖ ≤ ε * ‖n‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ H),
        Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ n)]
      exact htarget
    simpa [H, n] using hnorm
  exact ⟨rounds, 1, hRounds, hRoundsLe, by simpa [g] using hGrowth⟩

/-- The logarithmic slack term grows sublinearly in the input size. -/
private theorem theorem2_choose_delta_logSlack_sublinear
    (A : ℕ) :
    (fun N : ℕ => (logSlack A N : ℝ)) =o[atTop] fun N : ℕ => (N : ℝ) := by
  have hLogShift :
      (fun N : ℕ => Real.log ((N : ℝ) + 1)) =o[atTop]
        fun N : ℕ => (N : ℝ) + 1 :=
    Real.isLittleO_log_id_atTop.comp_tendsto
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hPlus :
      (fun N : ℕ => (N : ℝ) + 1) =O[atTop] fun N : ℕ => (N : ℝ) := by
    apply Asymptotics.isBigO_iff.mpr
    refine ⟨2, ?_⟩
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    have hNReal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hbound : (N : ℝ) + 1 ≤ 2 * (N : ℝ) := by linarith
    have hnormL : ‖(N : ℝ) + 1‖ = (N : ℝ) + 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hnormR : ‖(N : ℝ)‖ = (N : ℝ) := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by exact_mod_cast (Nat.zero_le N))]
    rw [hnormL, hnormR]
    linarith
  have hLogNat :
      (fun N : ℕ => Real.log ((N : ℝ) + 1)) =o[atTop]
        fun N : ℕ => (N : ℝ) := hLogShift.trans_isBigO hPlus
  have hLogb :
      (fun N : ℕ => Real.logb 2 ((N : ℝ) + 1)) =o[atTop]
        fun N : ℕ => (N : ℝ) := by
    have heq : (fun N : ℕ => Real.logb 2 ((N : ℝ) + 1)) =
        fun N : ℕ => (1 / Real.log 2) * Real.log ((N : ℝ) + 1) := by
      funext N
      rw [Real.logb]
      ring
    rw [heq]
    exact Asymptotics.IsLittleO.const_mul_left hLogNat (1 / Real.log 2)
  have hLogbPlus :
      (fun N : ℕ => Real.logb 2 ((N : ℝ) + 1) + 1) =o[atTop]
        fun N : ℕ => (N : ℝ) := by
    have hConstOne : (fun _ : ℕ => (1 : ℝ)) =o[atTop]
        fun N : ℕ => (N : ℝ) :=
      (Asymptotics.isLittleO_const_id_atTop (1 : ℝ)).comp_tendsto
        tendsto_natCast_atTop_atTop
    exact Asymptotics.IsLittleO.add hLogb hConstOne
  have hBits :
      (fun N : ℕ => ((Nat.bits (N + 1)).length : ℝ)) =o[atTop]
        fun N : ℕ => (N : ℝ) := by
    have hBound :
        (fun N : ℕ => ((Nat.bits (N + 1)).length : ℝ)) =O[atTop]
          fun N : ℕ => Real.logb 2 ((N : ℝ) + 1) + 1 := by
      apply Asymptotics.isBigO_iff.mpr
      refine ⟨1, ?_⟩
      filter_upwards [] with N
      have hLength := length_natBits_le_log (N + 1)
      have hLog := Real.natLog_le_logb (N + 1) 2
      have hLog' : (Nat.log 2 (N + 1) : ℝ) ≤
          Real.logb 2 ((N : ℝ) + 1) := by simpa using hLog
      have hLength' : ((Nat.bits (N + 1)).length : ℝ) ≤
          (Nat.log 2 (N + 1) : ℝ) + 1 := by exact_mod_cast hLength
      have hArg : (1 : ℝ) ≤ (N : ℝ) + 1 := by
        exact_mod_cast (show 1 ≤ N + 1 by omega)
      have hLogNonneg : 0 ≤ Real.logb 2 ((N : ℝ) + 1) :=
        Real.logb_nonneg (by norm_num) hArg
      have hFinal : ((Nat.bits (N + 1)).length : ℝ) ≤
          Real.logb 2 ((N : ℝ) + 1) + 1 := by linarith
      have hnormL : ‖((Nat.bits (N + 1)).length : ℝ)‖ =
          ((Nat.bits (N + 1)).length : ℝ) := by
        rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
      have hnormR : ‖Real.logb 2 ((N : ℝ) + 1) + 1‖ =
          Real.logb 2 ((N : ℝ) + 1) + 1 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      rw [hnormL, hnormR]
      simpa using hFinal
    exact hBound.trans_isLittleO hLogbPlus
  have hLogSlackShift :
      (fun N : ℕ => (logSlack A (N + 1) : ℝ)) =o[atTop]
        fun N : ℕ => (N : ℝ) := by
    have heq : (fun N : ℕ => (logSlack A (N + 1) : ℝ)) =
        fun N : ℕ => (A : ℝ) * ((Nat.bits (N + 1)).length : ℝ) + A := by
      funext N
      simp [logSlack]
    rw [heq]
    have hConst : (fun _ : ℕ => (A : ℝ)) =o[atTop]
        fun N : ℕ => (N : ℝ) :=
      (Asymptotics.isLittleO_const_id_atTop (A : ℝ)).comp_tendsto
        tendsto_natCast_atTop_atTop
    exact Asymptotics.IsLittleO.add
      (Asymptotics.IsLittleO.const_mul_left hBits (A : ℝ)) hConst
  have hBound :
      (fun N : ℕ => (logSlack A N : ℝ)) =O[atTop]
        fun N : ℕ => (logSlack A (N + 1) : ℝ) := by
    apply Asymptotics.isBigO_iff.mpr
    refine ⟨1, ?_⟩
    filter_upwards [] with N
    have h := logSlack_mono_right A (Nat.le_succ N)
    have hreal : (logSlack A N : ℝ) ≤ logSlack A (N + 1) := by
      exact_mod_cast h
    have hnormL : ‖(logSlack A N : ℝ)‖ = (logSlack A N : ℝ) := by
      rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    have hnormR : ‖(logSlack A (N + 1) : ℝ)‖ =
        (logSlack A (N + 1) : ℝ) := by
      rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    rw [hnormL, hnormR]
    simpa using hreal
  exact hBound.trans_isLittleO hLogSlackShift

/-- Dividing a linear budget by a diverging round count gives a sublinear budget. -/
private theorem theorem2_choose_delta_round_quotient_sublinear
    (rounds : ℕ → ℕ) (hRounds : Tendsto rounds atTop atTop) (A : ℕ) :
    (fun N : ℕ =>
      (((8 * N + 2 * logSlack A N) / max 1 (rounds N) : ℕ) : ℝ)) =o[atTop]
        fun N : ℕ => (N : ℝ) := by
  let numerator : ℕ → ℕ := fun N => 8 * N + 2 * logSlack A N
  let denominator : ℕ → ℕ := fun N => max 1 (rounds N)
  let quotient : ℕ → ℕ := fun N => numerator N / denominator N
  have hRoundsReal : Tendsto (fun N : ℕ => (rounds N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hRounds
  have hRoundsPos : ∀ᶠ N : ℕ in atTop, 1 ≤ rounds N :=
    hRounds.eventually_ge_atTop 1
  have hDenEq : (fun N : ℕ => (denominator N : ℝ)) =ᶠ[atTop]
      fun N : ℕ => (rounds N : ℝ) := by
    filter_upwards [hRoundsPos] with N hN
    simp [denominator, max_eq_right hN]
  have hDenTendsto : Tendsto (fun N : ℕ => (denominator N : ℝ)) atTop atTop :=
    Tendsto.congr' hDenEq.symm hRoundsReal
  have hUpper : Tendsto
      (fun N : ℕ => ((8 + 4 * A : ℕ) : ℝ) / (denominator N : ℝ))
      atTop (nhds 0) := hDenTendsto.const_div_atTop ((8 + 4 * A : ℕ) : ℝ)
  have hRatio : Tendsto
      (fun N : ℕ => (quotient N : ℝ) / (N : ℝ)) atTop (nhds 0) := by
    apply tendsto_order.2
    constructor
    · intro a ha
      filter_upwards [] with N
      have hnonneg : 0 ≤ (quotient N : ℝ) / (N : ℝ) :=
        div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      linarith
    · intro a ha
      filter_upwards [hUpper.eventually (Iio_mem_nhds ha),
        Filter.eventually_ge_atTop 1] with N hUpperN hN
      have hbits := length_natBits_le N
      have hlog : logSlack A N ≤ A * N + A := by
        unfold logSlack
        have hbitsA := Nat.mul_le_mul_left A hbits
        omega
      have hAN : A ≤ A * N := by
        calc
          A = A * 1 := by omega
          _ ≤ A * N := Nat.mul_le_mul_left A hN
      have hlog' : logSlack A N ≤ 2 * (A * N) := by omega
      have hnum : numerator N ≤ 8 * N + 4 * (A * N) := by
        dsimp [numerator]
        omega
      have hnumReal : (numerator N : ℝ) ≤
          ((8 + 4 * A : ℕ) : ℝ) * (N : ℝ) := by
        calc
          (numerator N : ℝ) ≤ (8 * N + 4 * (A * N) : ℕ) := by exact_mod_cast hnum
          _ = ((8 + 4 * A : ℕ) : ℝ) * (N : ℝ) := by push_cast; ring
      have hdiv : (quotient N : ℝ) ≤
          (numerator N : ℝ) / (denominator N : ℝ) := by
        exact Nat.cast_div_le
      have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
      have hDpos : (0 : ℝ) < (denominator N : ℝ) := by
        have : 1 ≤ denominator N := by simp [denominator]
        exact_mod_cast (by omega : 0 < denominator N)
      have hquotBound : (quotient N : ℝ) / (N : ℝ) ≤
          ((8 + 4 * A : ℕ) : ℝ) / (denominator N : ℝ) := by
        calc
          (quotient N : ℝ) / (N : ℝ) ≤
              ((numerator N : ℝ) / (denominator N : ℝ)) / (N : ℝ) :=
            div_le_div_of_nonneg_right hdiv (by positivity)
          _ = (numerator N : ℝ) / ((denominator N : ℝ) * (N : ℝ)) := by ring
          _ ≤ (((8 + 4 * A : ℕ) : ℝ) * (N : ℝ)) /
                ((denominator N : ℝ) * (N : ℝ)) :=
            div_le_div_of_nonneg_right hnumReal (by positivity)
          _ = ((8 + 4 * A : ℕ) : ℝ) / (denominator N : ℝ) := by
            field_simp
      linarith
  have hgf : ∀ᶠ N : ℕ in atTop, (N : ℝ) = 0 → (quotient N : ℝ) = 0 := by
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN hz
    have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (by omega : 0 < N))
    exact False.elim (hNne hz)
  have hQuotient : (fun N : ℕ => (quotient N : ℝ)) =o[atTop]
      fun N : ℕ => (N : ℝ) :=
    (Asymptotics.isLittleO_iff_tendsto' hgf).2 hRatio
  simpa [numerator, denominator, quotient] using hQuotient

/-- A sublinear delta that pays for the iteration progress and growth cost of a growing round
schedule.
-/
private theorem theorem2_choose_delta
    (rounds growth : ℕ → ℕ)
    (hRounds : Tendsto rounds atTop atTop)
    (hGrowth : (fun N : ℕ => (growth N : ℝ)) =o[atTop] fun N : ℕ => (N : ℝ))
    (A : ℕ) :
    ∃ delta : ℕ → ℕ, ∃ N₂ : ℕ,
      ((fun N : ℕ => ((4 * delta N + logSlack A N : ℕ) : ℝ)) =o[atTop]
        fun N : ℕ => (N : ℝ)) ∧
      (∀ N ≥ N₂,
        2 ≤ N ∧
        delta N ≤ N ∧
        logSlack A N ≤ N ∧
        8 * N + 2 * logSlack A N ≤ rounds N * (delta N / 2) ∧
        growth N ≤ delta N) := by
  let quotient : ℕ → ℕ := fun N =>
    (8 * N + 2 * logSlack A N) / max 1 (rounds N)
  let delta : ℕ → ℕ := fun N => growth N + 2 * (quotient N + 1)
  have hLogSlack :=
    theorem2_choose_delta_logSlack_sublinear A
  have hQuotient :=
    theorem2_choose_delta_round_quotient_sublinear
      rounds hRounds A
  have hConst : (fun _ : ℕ => (1 : ℝ)) =o[atTop]
      fun N : ℕ => (N : ℝ) :=
    (Asymptotics.isLittleO_const_id_atTop (1 : ℝ)).comp_tendsto
      tendsto_natCast_atTop_atTop
  have hQuotientPlus : (fun N : ℕ => ((quotient N + 1 : ℕ) : ℝ)) =o[atTop]
      fun N : ℕ => (N : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using Asymptotics.IsLittleO.add hQuotient hConst
  have hDelta : (fun N : ℕ => (delta N : ℝ)) =o[atTop]
      fun N : ℕ => (N : ℝ) := by
    have h := Asymptotics.IsLittleO.add hGrowth
      (Asymptotics.IsLittleO.const_mul_left hQuotientPlus (2 : ℝ))
    simpa [delta] using h
  have hError : (fun N : ℕ => ((4 * delta N + logSlack A N : ℕ) : ℝ)) =o[atTop]
      fun N : ℕ => (N : ℝ) := by
    simpa using
      Asymptotics.IsLittleO.add
        (Asymptotics.IsLittleO.const_mul_left hDelta (4 : ℝ)) hLogSlack
  have hErrBound := hError.eventuallyLE
  obtain ⟨Nerr, hErrBound⟩ := Filter.eventually_atTop.mp hErrBound
  have hRoundsPos : ∀ᶠ N : ℕ in atTop, 1 ≤ rounds N :=
    hRounds.eventually_ge_atTop 1
  obtain ⟨Nr, hNr⟩ := Filter.eventually_atTop.mp hRoundsPos
  let N₂ := max 2 (max Nerr Nr)
  refine ⟨delta, N₂, hError, ?_⟩
  intro N hN
  have hCutInner : max Nerr Nr ≤ N :=
    (Nat.le_max_right 2 (max Nerr Nr)).trans hN
  have hNerr : N ≥ Nerr := (Nat.le_max_left Nerr Nr).trans hCutInner
  have hNrN : N ≥ Nr := (Nat.le_max_right Nerr Nr).trans hCutInner
  have hTwo : 2 ≤ N := (Nat.le_max_left 2 (max Nerr Nr)).trans hN
  have hErrReal := hErrBound N hNerr
  have hErrNat : 4 * delta N + logSlack A N ≤ N := by
    have hErrNonneg : (0 : ℝ) ≤ ((4 * delta N + logSlack A N : ℕ) : ℝ) := by positivity
    have hNNonneg : (0 : ℝ) ≤ (N : ℝ) := by positivity
    have hErrAbs : |((4 * delta N + logSlack A N : ℕ) : ℝ)| ≤ |(N : ℝ)| := by
      simpa [Real.norm_eq_abs] using hErrReal
    have hreal : ((4 * delta N + logSlack A N : ℕ) : ℝ) ≤ (N : ℝ) := by
      rw [abs_of_nonneg hErrNonneg, abs_of_nonneg hNNonneg] at hErrAbs
      exact hErrAbs
    exact_mod_cast hreal
  have hDeltaN : delta N ≤ N := by omega
  have hLogN : logSlack A N ≤ N := by omega
  have hRoundN : 1 ≤ rounds N := hNr N hNrN
  have hMax : max 1 (rounds N) = rounds N := max_eq_right hRoundN
  have hQuotientRound : 8 * N + 2 * logSlack A N ≤
      rounds N * (quotient N + 1) := by
    have hMod : (8 * N + 2 * logSlack A N) % rounds N < rounds N :=
      Nat.mod_lt _ (by omega)
    have hDecomp : (8 * N + 2 * logSlack A N) % rounds N +
        rounds N * quotient N = 8 * N + 2 * logSlack A N := by
      simpa [quotient, hMax] using
        (Nat.mod_add_div (8 * N + 2 * logSlack A N) (rounds N))
    have hSmall : 8 * N + 2 * logSlack A N ≤ rounds N * quotient N + rounds N := by
      omega
    calc
      8 * N + 2 * logSlack A N ≤ rounds N * quotient N + rounds N := hSmall
      _ = rounds N * (quotient N + 1) := by simp [Nat.mul_add]
  have hFloor : quotient N + 1 ≤ delta N / 2 := by
    dsimp [delta]
    omega
  have hProgress : 8 * N + 2 * logSlack A N ≤ rounds N * (delta N / 2) := by
    exact hQuotientRound.trans (Nat.mul_le_mul_left (rounds N) hFloor)
  have hGrowthN : growth N ≤ delta N := by
    dsimp [delta]
    omega
  exact ⟨hTwo, hDeltaN, hLogN, hProgress, hGrowthN⟩

/-- Choose a sublinear error budget and a number of replacement rounds. Beyond a finite cutoff,
the round budget is large
enough to force termination, while the threshold recurrence stays below the error budget.  The
error functions are also enlarged on the finite initial segment for the small-input fallback. -/
theorem theorem2_choose_budgets
    (f : ℕ → ℕ)
    (hf : (fun N : ℕ => (f N : ℝ)) =o[atTop] fun N : ℕ => (N : ℝ))
    (a b A B : ℕ) :
    ∃ loss threshold rounds delta : ℕ → ℕ, ∃ N₀ : ℕ,
      ((fun N : ℕ => (loss N : ℝ)) =o[atTop] fun N : ℕ => (N : ℝ)) ∧
      ((fun N : ℕ => (threshold N : ℝ)) =o[atTop] fun N : ℕ => (N : ℝ)) ∧
      (∀ N < N₀,
        a * (N + f N + logSlack a (N + f N + 1)) + a ≤ loss N ∧
        b ≤ threshold N) ∧
      (∀ N ≥ N₀,
        2 ≤ N ∧
        rounds N ≤ (Nat.bits N).length ∧
        delta N ≤ N ∧
        logSlack A N ≤ N ∧
        8 * N + 2 * logSlack A N ≤ rounds N * (delta N / 2) ∧
        8 * 3 ^ (rounds N) * (f N + logSlack B N) ≤ delta N ∧
        4 * delta N + logSlack A N ≤ loss N ∧
        4 * delta N + logSlack A N ≤ threshold N) := by
  obtain ⟨rounds, N₁, hRounds, hRoundsLe, hGrowth⟩ :=
    theorem2_choose_rounds f hf B
  let growth : ℕ → ℕ := fun N => 8 * 3 ^ (rounds N) * (f N + logSlack B N)
  have hGrowth' : (fun N : ℕ => (growth N : ℝ)) =o[atTop] fun N : ℕ => (N : ℝ) := by
    simpa [growth] using hGrowth
  obtain ⟨delta, N₂, hError, hDelta⟩ :=
    theorem2_choose_delta
      rounds growth hRounds hGrowth' A
  let N₀ := max N₁ N₂
  let loss : ℕ → ℕ := fun N =>
    if N < N₀ then a * (N + f N + logSlack a (N + f N + 1)) + a
    else 4 * delta N + logSlack A N
  let threshold : ℕ → ℕ := fun N =>
    if N < N₀ then b else 4 * delta N + logSlack A N
  have hErrorEqLoss :
      (fun N : ℕ => ((4 * delta N + logSlack A N : ℕ) : ℝ)) =ᶠ[atTop]
        fun N : ℕ => (loss N : ℝ) := by
    filter_upwards [Filter.eventually_ge_atTop N₀] with N hN
    simp [loss, Nat.not_lt.mpr hN]
  have hErrorEqThreshold :
      (fun N : ℕ => ((4 * delta N + logSlack A N : ℕ) : ℝ)) =ᶠ[atTop]
        fun N : ℕ => (threshold N : ℝ) := by
    filter_upwards [Filter.eventually_ge_atTop N₀] with N hN
    simp [threshold, Nat.not_lt.mpr hN]
  refine ⟨loss, threshold, rounds, delta, N₀, ?_, ?_, ?_, ?_⟩
  · exact hError.congr' hErrorEqLoss Filter.EventuallyEq.rfl
  · exact hError.congr' hErrorEqThreshold Filter.EventuallyEq.rfl
  · intro N hN
    constructor <;> simp [loss, threshold, hN]
  · intro N hN
    have hN₁ : N ≥ N₁ := (Nat.le_max_left N₁ N₂).trans hN
    have hN₂ : N ≥ N₂ := (Nat.le_max_right N₁ N₂).trans hN
    obtain ⟨hTwo, hDeltaN, hLogN, hProgress, hGrowthN⟩ := hDelta N hN₂
    have hRoundsN := hRoundsLe N hN₁
    have hLarge :
        2 ≤ N ∧
        rounds N ≤ (Nat.bits N).length ∧
        delta N ≤ N ∧
        logSlack A N ≤ N ∧
        8 * N + 2 * logSlack A N ≤ rounds N * (delta N / 2) ∧
        8 * 3 ^ (rounds N) * (f N + logSlack B N) ≤ delta N := by
      exact ⟨hTwo, hRoundsN, hDeltaN, hLogN, hProgress, by simpa [growth] using hGrowthN⟩
    simpa [loss, threshold, Nat.not_lt.mpr hN] using hLarge

/- Internal state used to record a single round of the finite iteration. -/

end Kolmogorov.Relativization
