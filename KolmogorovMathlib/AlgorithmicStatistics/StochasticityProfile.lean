/-
Copyright (c) 2026 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Interface.Dovetailing
import KolmogorovMathlib.Interface.StandardMachine
import KolmogorovMathlib.Restricted.HammingGap
import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.TailProfile
import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.NonStochasticFinal
import KolmogorovMathlib.AlgorithmicStatistics.Selector
import KolmogorovMathlib.Core.Invariance
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.CurveRealization
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.UpwardConditional
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.BudgetedStochasticity
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.CubeStochasticity
import KolmogorovMathlib.Prefix.NumericalValues
import KolmogorovMathlib.AlgorithmicProbability.CompatibleGraphs
import KolmogorovMathlib.AlgorithmicProbability.HaltingProbabilityApproximation
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitinApplications.Part01
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitinApplications.Part02
import KolmogorovMathlib.Interface.ComputableReals.LowerSemicomputableReals
import KolmogorovMathlib.MonotoneComplexity.Omega.SolovayInverse
import KolmogorovMathlib.Prefix.BlockingReadMachines
import KolmogorovMathlib.Prefix.ExtensionTheorem
import KolmogorovMathlib.Prefix.PairComplexity
import KolmogorovMathlib.Prefix.SelfDelimitingMachines
import KolmogorovMathlib.Prefix.StableDecompressors
import KolmogorovMathlib.Restricted.DeficiencyEquiv
import KolmogorovMathlib.MonotoneComplexity.Dimension.ChangeOfMeasure
import KolmogorovMathlib.AlgorithmicStatistics.DeficiencyValue
import KolmogorovMathlib.AlgorithmicStatistics.NonStochasticMassWeak

/-!
# Non-stochastic strings and the shape of the stochasticity profile

Existence of non-stochastic strings under a weak gap hypothesis, the
non-stochasticity of a string whose description profile is extreme, the
properties of the stochasticity profile, and the enumeration machinery behind
them: codes that enumerate a list or a list of groups (`EnumeratesList`,
`EnumeratesGroups`), simple codes (`IsSimpleCode`), the four properties of the
list characterisation of the description profile, the tail-strings selector and
the computable bijection transport used for the invariance statements.

SUV Chapter 14 (algorithmic statistics), Sections 14.2-14.3.
-/

namespace Kolmogorov
open scoped ENNReal
open Nat.Partrec (Code)
open CodedFiniteDistribution

/-- **Exercise 363.** Non-stochastic strings of length `n` already exist under the
weaker hypothesis `alpha + beta < n - O(log n)`. -/
theorem exists_isNonStochastic_weak (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (n alpha beta : ℕ), alpha + beta + logSlack c n < n →
      ∃ x : BitString, x.length = n ∧ IsNonStochastic U x alpha beta := by
  obtain ⟨c_anti, h_anti⟩ := exists_antistochastic U hU
  obtain ⟨c_opt, h_opt⟩ := stochasticity_to_optimal_set_thm U hU
  obtain ⟨c_prof, h_prof⟩ := isOptimalSetStochastic_imp_profile U hU
  obtain ⟨C_opt, hC_opt⟩ := logSlack_linear_bound c_opt 3 0
  obtain ⟨C_prof, hC_prof⟩ := logSlack_linear_bound c_prof (3 + 6 * C_opt + 10) 0
  set c := 2 * C_opt + 2 * C_prof + 3 * c_anti + 10 with hc
  refine ⟨c, fun n alpha beta hgap => ?_⟩
  set s_opt := logSlack c_opt (n + alpha + beta)
  set A1 := alpha + s_opt
  set B1 := beta + s_opt
  set s_anti := logSlack c_anti n
  set s_prof := logSlack c_prof (A1 + B1 + (n + B1))
  set k := A1 + s_prof + s_anti + 1
  have hn_pos : 0 < n := by omega
  have h_s_opt : s_opt ≤ logSlack C_opt n := by
    have h1 : n + alpha + beta ≤ 3 * n := by omega
    exact (logSlack_mono_right c_opt h1).trans (hC_opt n)
  have h_s_prof : s_prof ≤ logSlack C_prof n := by
    have h1 : A1 + B1 + (n + B1) ≤ (3 + 6 * C_opt + 10) * n := by
      dsimp [A1, B1]
      have hs : s_opt ≤ C_opt * n.bits.length + C_opt := h_s_opt
      have hbits : n.bits.length ≤ n := length_natBits_le n
      nlinarith [Nat.zero_le C_opt]
    exact (logSlack_mono_right c_prof h1).trans (hC_prof n)
  have hkn : k ≤ n := by
    have hL1 : 1 ≤ (Nat.bits n).length := by
      have h0 : 0 < Nat.size n := Nat.size_pos.mpr hn_pos
      rw [Nat.size_eq_bits_len]; exact h0
    have h_s_opt_val : s_opt ≤ C_opt * n.bits.length + C_opt := h_s_opt
    have h_s_prof_val : s_prof ≤ C_prof * n.bits.length + C_prof := h_s_prof
    have h_k_le : k ≤ alpha + beta + logSlack c n := by
      dsimp [k, A1, s_anti, logSlack]
      dsimp [c]
      nlinarith [h_s_opt_val, h_s_prof_val, Nat.zero_le C_opt,
        Nat.zero_le C_prof, Nat.zero_le c_anti]
    omega
  obtain ⟨x, hx_len, hx_kp_ub, hx_kp_lb, hx_anti⟩ := h_anti n k hkn
  refine ⟨x, hx_len, fun hstoch => ?_⟩
  have hopt : IsOptimalSetStochastic U x A1 B1 := h_opt x n alpha beta hx_len hstoch
  have hx_ne : KPPlain U x ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top _) hx_kp_ub
  obtain ⟨p, hp⟩ : ∃ p : ℕ, KPPlain U x = (p : ENat) :=
    ⟨(KPPlain U x).toNat, (ENat.natCast_toNat hx_ne).symm⟩
  have hp_le_k : p ≤ k + s_anti := by
    rw [hp] at hx_kp_ub
    exact_mod_cast hx_kp_ub
  have hA1_le_p : A1 ≤ p := by
    have h_p_lb : k ≤ p + s_anti := by
      rw [hp] at hx_kp_lb
      exact_mod_cast hx_kp_lb
    dsimp [k] at h_p_lb
    omega
  set j := (p + B1) - A1
  have harith : KPPlain U x + (B1 : ENat) ≤ (A1 : ENat) + (j : ENat) := by
    have hnat : p + B1 ≤ A1 + j := by dsimp [j]; omega
    calc KPPlain U x + (B1 : ENat)
        = ((p + B1 : ℕ) : ENat) := by rw [hp]; push_cast; rfl
      _ ≤ ((A1 + j : ℕ) : ENat) := by exact_mod_cast hnat
      _ = (A1 : ENat) + (j : ENat) := by push_cast; rfl
  have hprof : InDescriptionProfile U x (A1 + logSlack c_prof (A1 + B1 + j)) (j + 1) :=
    h_prof x A1 B1 j hopt harith
  set i_prof := A1 + logSlack c_prof (A1 + B1 + j)
  have hs_less_n : s_prof + 2 * s_anti + 1 ≤ n := by
    have hL1 : 1 ≤ (Nat.bits n).length := by
      have h0 : 0 < Nat.size n := Nat.size_pos.mpr hn_pos
      rw [Nat.size_eq_bits_len]; exact h0
    have h_s_prof_val : s_prof ≤ C_prof * n.bits.length + C_prof := h_s_prof
    dsimp [logSlack, s_anti] at hgap ⊢
    dsimp [c] at hgap
    nlinarith [h_s_prof_val, Nat.zero_le C_opt, Nat.zero_le C_prof, Nat.zero_le c_anti]
  have hj_bound : A1 + B1 + j ≤ A1 + B1 + (n + B1) := by
    dsimp [j, k, A1] at hp_le_k ⊢
    omega
  have hi_prof_le : i_prof ≤ A1 + s_prof := by
    dsimp [i_prof, s_prof]
    exact Nat.add_le_add_left (logSlack_mono_right c_prof hj_bound) A1
  have hi_prof_s_anti : i_prof + s_anti < k := by
    dsimp [k]
    omega
  have h_anti_applied := hx_anti i_prof (j + 1) hi_prof_s_anti hprof
  have h_i_prof_j : i_prof + (j + 1) + s_anti ≤ p + beta + s_opt + s_prof + 1 + s_anti := by
    have h1 : logSlack c_prof (A1 + B1 + j) ≤ s_prof := by
      have h2 := hi_prof_le
      dsimp [i_prof, A1] at h2
      omega
    dsimp [i_prof, j, A1, B1] at h1 ⊢
    omega
  have h_p_bound : p + beta + s_opt + s_prof + 1 + s_anti ≤
      alpha + beta + 2 * s_opt + 2 * s_prof + 3 * s_anti + 2 := by
    dsimp [k, A1] at hp_le_k
    omega
  have h_slack_bound : 2 * s_opt + 2 * s_prof + 3 * s_anti + 2 ≤ logSlack c n := by
    have hL1 : 1 ≤ (Nat.bits n).length := by
      have h0 : 0 < Nat.size n := Nat.size_pos.mpr hn_pos
      rw [Nat.size_eq_bits_len]; exact h0
    have h_s_opt_val : s_opt ≤ C_opt * n.bits.length + C_opt := h_s_opt
    have h_s_prof_val : s_prof ≤ C_prof * n.bits.length + C_prof := h_s_prof
    dsimp [logSlack, s_anti]
    dsimp [c]
    nlinarith [h_s_opt_val, h_s_prof_val, Nat.zero_le C_opt,
      Nat.zero_le C_prof, Nat.zero_le c_anti]
  have h_sum_le : i_prof + (j + 1) + s_anti ≤ alpha + beta + logSlack c n := by
    omega
  omega

/-- The slack constant splits additively: `logSlack (c + c') n` is the sum of the
two slacks. -/
theorem logSlack_add_left (c c' n : ℕ) :
    logSlack (c + c') n = logSlack c n + logSlack c' n :=
  logSlack_add_constants c c' n

/-- The binary length of `n` is at most `n + 1`. -/
theorem bits_length_le_succ (n : ℕ) : (Nat.bits n).length ≤ n + 1 := by
  have h : n < 2 ^ n := Nat.lt_two_pow_self
  have h2 : Nat.size n ≤ n := Nat.size_le.mpr h
  have h3 : (Nat.bits n).length = Nat.size n := Nat.size_eq_bits_len n
  omega

/-- `logSlack c n` grows at most linearly in `n`. -/
theorem logSlack_le_mul_add_two_mul (c n : ℕ) : logSlack c n ≤ c * n + 2 * c := by
  have h := bits_length_le_succ n
  have : c * (Nat.bits n).length ≤ c * (n + 1) := Nat.mul_le_mul_left c h
  unfold logSlack
  nlinarith [Nat.zero_le c, Nat.zero_le n]

/-- **Exercise 350, general form.** For every profile-slack constant `c_prof`
there is a constant `c` such that a string of length `n` and prefix complexity
`kx` whose description profile stays on the slope `-1` line `i + j = n` for all
complexity coordinates below `kx` (with precision `logSlack c_prof n`) is not
`(alpha, beta)`-stochastic once `alpha + logSlack c n < kx` and
`beta + 2 kx + logSlack c n < n`. -/
theorem isNonStochastic_of_extreme_profile_general (U : Map)
    (hU : IsOptimalPrefixConditional U) (c_prof : ℕ) :
    ∃ c : ℕ, ∀ (x : BitString) (n kx alpha beta : ℕ), x.length = n →
      KPPlain U x = (kx : ℕ∞) →
      (∀ i j : ℕ, i + logSlack c_prof n < kx → InDescriptionProfile U x i j →
        n ≤ i + j + logSlack c_prof n) →
      alpha + logSlack c n < kx →
      beta + 2 * kx + logSlack c n < n →
      IsNonStochastic U x alpha beta := by
  obtain ⟨c_opt, h_opt⟩ := stochasticity_to_optimal_set_thm U hU
  obtain ⟨c_prf, h_prf⟩ := isOptimalSetStochastic_imp_profile U hU
  obtain ⟨C0, hC0⟩ := logSlack_linear_bound c_opt 3 0
  obtain ⟨C2, hC2⟩ := logSlack_linear_bound c_prf (4 + 3 * C0) (6 * C0)
  refine ⟨C0 + C2 + c_prof + 1, ?_⟩
  intro x n kx alpha beta hxlen hkx hprof halpha hbeta hst
  -- Notation for the three slacks involved.
  set A := logSlack C0 n with hA
  set B := logSlack C2 n with hB
  set P := logSlack c_prof n with hP
  have hSc : logSlack (C0 + C2 + c_prof + 1) n = A + B + P + logSlack 1 n := by
    rw [logSlack_add_left, logSlack_add_left, logSlack_add_left]
  have hone : 1 ≤ logSlack 1 n := by unfold logSlack; omega
  -- Elementary consequences of the two gap hypotheses.
  have halpha_lt : alpha < kx := by omega
  have hkx_lt : 2 * kx < n := by omega
  -- The optimal-set witness produced by an assumed stochasticity witness.
  have hopt := h_opt x n alpha beta hxlen hst
  set s_opt := logSlack c_opt (n + alpha + beta) with hs_opt
  have hs_optA : s_opt ≤ A := by
    have h1 : n + alpha + beta ≤ 3 * n + 0 := by omega
    exact le_trans (logSlack_mono h1) (hC0 n)
  set alpha' := alpha + s_opt with halpha'
  set beta' := beta + s_opt with hbeta'
  set j := kx + beta' - alpha' with hj
  have harith : KPPlain U x + (beta' : ℕ∞) ≤ (alpha' : ℕ∞) + (j : ℕ∞) := by
    rw [hkx]
    have hnat : kx + beta' ≤ alpha' + j := by omega
    exact_mod_cast hnat
  have hprof_pt := h_prf x alpha' beta' j hopt harith
  set s2 := logSlack c_prf (alpha' + beta' + j) with hs2
  -- The second slack is also logarithmic in `n`.
  have hs2B : s2 ≤ B := by
    have hAlin : A ≤ C0 * n + 2 * C0 := by
      rw [hA]; exact logSlack_le_mul_add_two_mul C0 n
    have hlin : s_opt ≤ C0 * n + 2 * C0 := le_trans hs_optA hAlin
    have hstep : alpha' + beta' + j ≤ 4 * n + 3 * s_opt := by omega
    have hstep2 : 4 * n + 3 * s_opt ≤ 4 * n + 3 * (C0 * n + 2 * C0) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left 3 hlin) _
    have hstep3 : 4 * n + 3 * (C0 * n + 2 * C0) = (4 + 3 * C0) * n + 6 * C0 := by ring
    have hfin : alpha' + beta' + j ≤ (4 + 3 * C0) * n + 6 * C0 :=
      le_trans hstep (le_trans hstep2 (le_of_eq hstep3))
    exact le_trans (logSlack_mono hfin) (hC2 n)
  -- Case analysis on whether the profile point lies below the complexity coordinate.
  by_cases hcase : (alpha' + s2) + P < kx
  · have hline := hprof (alpha' + s2) (j + 1) hcase hprof_pt
    omega
  · omega

/-- **Exercise 350.** A string whose description profile follows the slope `-1`
line `i + j = n` up to the complexity coordinate is not `(alpha, beta)`-stochastic
for `alpha < K(x)` and `beta < n - 2 K(x)`. -/
theorem isNonStochastic_of_extreme_profile (U : Map)
    (hU : IsOptimalPrefixConditional U) :
    ∃ c_prof c : ℕ, ∀ (x : BitString) (n kx alpha beta : ℕ), x.length = n →
      KPPlain U x = (kx : ℕ∞) →
      (∀ i j : ℕ, i + logSlack c_prof n < kx → InDescriptionProfile U x i j →
        n ≤ i + j + logSlack c_prof n) →
      alpha + logSlack c n < kx →
      beta + 2 * kx + logSlack c n < n →
      IsNonStochastic U x alpha beta := by
  obtain ⟨c, hc⟩ := isNonStochastic_of_extreme_profile_general U hU 1
  exact ⟨1, c, hc⟩

/-! ### The stochasticity profile `Q_x` -/

/-- **Exercise 366, structural half.** The stochasticity profile `Q_x` of an
`n`-bit string of complexity `k` is upward closed and contains the two extreme
points `(O(log n), n - k + O(log n))` and `(k + O(1), 0)`. -/
theorem stochasticityProfile_properties (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (n kx : ℕ), x.length = n → KPPlain U x = (kx : ℕ∞) →
      (∀ alpha alpha' beta beta' : ℕ, alpha ≤ alpha' → beta ≤ beta' →
          IsStochastic U x alpha beta → IsStochastic U x alpha' beta') ∧
        IsStochastic U x (logSlack c n) (n - kx + logSlack c n) ∧
        IsStochastic U x (kx + c) 0 := by
  obtain ⟨c_sub, hc_sub⟩ := KPPlain_le_KPPlain_add_KP U hU
  obtain ⟨c_map, hc_map⟩ := KPPlain_map_le U hU lengthUniformCode lengthUniformCode_computable
  obtain ⟨cNat, hc_nat⟩ := KPPlain_natCode_le_log U hU
  obtain ⟨c_log, hc_log⟩ := isStochastic_lengthUniform_log U hU
  obtain ⟨c_dir, hc_dir⟩ := setComplexity_singleton_le_KPPlain_add_const U hU
  set C_sum := cNat + c_map + c_sub
  set c := c_log + C_sum + c_dir + 2
  refine ⟨c, fun x n kx hlen hkx =>
    ⟨fun a a' b b' ha hb hst => isStochastic_mono ha hb hst, ?_, ?_⟩⟩
  · have h_code_comp : KPPlain U (codedLengthUniform n).code ≤
        ((2 * (Nat.bits n).length + cNat + c_map : ℕ) : ENat) := by
      have h1 := hc_map (natCode n)
      rw [lengthUniformCode_eq] at h1
      have hnat := hc_nat n
      calc KPPlain U (codedLengthUniform n).code
          ≤ KPPlain U (natCode n) + (c_map : ENat) := h1
        _ ≤ (2 * ((Nat.bits n).length : ENat) + (cNat : ENat)) + (c_map : ENat) :=
            add_le_add hnat le_rfl
        _ = ((2 * (Nat.bits n).length + cNat + c_map : ℕ) : ENat) := by push_cast; ring
    have h_sub : (kx : ENat) ≤
        KP U x (codedLengthUniform n).code + ((2 * (Nat.bits n).length + C_sum : ℕ) : ENat) := by
      have h2 := hc_sub x (codedLengthUniform n).code
      rw [hkx] at h2
      have h_comb : KPPlain U (codedLengthUniform n).code + KP U x (codedLengthUniform n).code
        + (c_sub : ENat) ≤
          ((2 * (Nat.bits n).length + cNat + c_map : ℕ) : ENat)
            + KP U x (codedLengthUniform n).code + (c_sub : ENat) :=
        add_le_add (add_le_add h_code_comp le_rfl) le_rfl
      have h_eq : ((2 * (Nat.bits n).length + cNat + c_map : ℕ) : ENat)
        + KP U x (codedLengthUniform n).code + (c_sub : ENat) =
          KP U x (codedLengthUniform n).code + ((2 * (Nat.bits n).length + C_sum : ℕ) : ENat) := by
        dsimp [C_sum]; push_cast; ring
      exact h2.trans (h_comb.trans (by rw [h_eq]))
    have h_n_le : (n : ENat) ≤ KP U x (codedLengthUniform n).code +
        ((n - kx + 2 * (Nat.bits n).length + C_sum : ℕ) : ENat) := by
      have hK := h_sub
      generalize h_kp : KP U x (codedLengthUniform n).code = Kcond
      rw [h_kp] at hK
      cases Kcond with
      | top => rw [top_add]; exact le_top
      | coe Kcond_nat =>
        push_cast at hK ⊢
        have h_nat_sub : kx ≤ Kcond_nat + (2 * (Nat.bits n).length + C_sum) := by exact_mod_cast hK
        have h_nat_n : n ≤ Kcond_nat + (n - kx + 2 * (Nat.bits n).length + C_sum) := by omega
        exact_mod_cast h_nat_n
    have h_def : DeficiencyLe U (codedLengthUniform n) x
        (n - kx + 2 * (Nat.bits n).length + C_sum) := by
      exact deficiencyLe_codedLengthUniform_of_length_le U x n
        (n - kx + 2 * (Nat.bits n).length + C_sum) hlen h_n_le
    have h_stoch_raw := hc_log x (n - kx + 2 * (Nat.bits n).length + C_sum)
      (by rw [hlen]; exact h_def)
    have h_slack_bound (k : ℕ) (hk : k ≤ c) : 2 * (Nat.bits n).length + k ≤ logSlack c n := by
      unfold logSlack
      have hc2 : 2 ≤ c := by omega
      have h1 : 2 * (Nat.bits n).length ≤ c * (Nat.bits n).length := Nat.mul_le_mul_right _ hc2
      omega
    have ha_le : 2 * (Nat.bits n).length + c_log ≤ logSlack c n := h_slack_bound c_log (by omega)
    have hb_le : n - kx + 2 * (Nat.bits n).length + C_sum ≤ n - kx + logSlack c n := by
      have h1 := h_slack_bound C_sum (by omega)
      omega
    rw [hlen] at h_stoch_raw
    exact isStochastic_mono ha_le hb_le h_stoch_raw
  · have h_sing_comp : setComplexity U {x} (Finset.singleton_nonempty x) ≤
        ((kx + c : ℕ) : ENat) := by
      have h1 := hc_dir x
      rw [hkx] at h1
      refine h1.trans ?_
      have hdir : c_dir ≤ c := by
        change c_dir ≤ c_log + C_sum + c_dir + 2
        omega
      have : kx + c_dir ≤ kx + c := by omega
      exact_mod_cast this
    have h_stoch := isStochastic_of_model U x (codedUniformOn {x} (Finset.singleton_nonempty x))
      (kx + c) 0 (codedUniformOn_isProbability _ _) h_sing_comp ?_
    · exact h_stoch
    · refine deficiencyLe_zero_of_mass_one U _ x ?_
      rw [codedUniformOn_mass_of_mem _ _ _ (Finset.mem_singleton_self x)]
      simp

-- `exercise366_profile_realization` (ch14-exercise-366) is archived; see
-- `docs/ARCHIVED_TARGETS.md`.

/-! ### Theorem 254: four equivalent descriptions of the two-dimensional strata

In the book an *enumerated list* is an **algorithm** that emits strings one at a
time; the length of the list is the number of emissions, and the list is
*simple* when the algorithm — not the finished list — has small complexity.
That distinction carries the whole content of part (d): the algorithm that
enumerates all strings of complexity at most `m` is simple (it only has to know
`m`), whereas the finished list of those strings has complexity at least
`m - O(1)`, because the first string missing from it is computable from it and
must have complexity above `m`.  Modelling an enumerated list by the finished
`List` and calling it simple when *that* has small complexity therefore makes
(d) vacuous as soon as `m ≥ s + O(1)`, and turns the last implication into a
false statement (a counting argument then produces an `n`-bit `x` violating the
conclusion (b)).

Here an enumerated list is a code `e` whose `k`-th run outputs the `k`-th emitted
string and diverges once the list has ended, so that no computation can detect
the end of the list.  Distance to the end is the library's `tailAfter`. -/

/-- The code `e` *enumerates the list* `L`: for `k < L.length` its `k`-th run
outputs `L[k]`, and for `k ≥ L.length` it diverges. -/
def EnumeratesList (e : ℕ) (L : List BitString) : Prop :=
  (∀ k : ℕ, (h : k < L.length) →
      Encodable.encode (L[k]'h) ∈ (Denumerable.ofNat Code e).eval k) ∧
    ∀ k : ℕ, L.length ≤ k → ¬ ((Denumerable.ofNat Code e).eval k).Dom

/-- The code `e` *enumerates the groups* `G`: its `k`-th run outputs the `k`-th
group of strings emitted, and it diverges once the last group has been emitted.
-/
def EnumeratesGroups (e : ℕ) (G : List (List BitString)) : Prop :=
  (∀ k : ℕ, (h : k < G.length) →
      Encodable.encode (G[k]'h) ∈ (Denumerable.ofNat Code e).eval k) ∧
    ∀ k : ℕ, G.length ≤ k → ¬ ((Denumerable.ofNat Code e).eval k).Dom

/-- An algorithm is `s`-simple when its code has prefix complexity at most `s`.
-/
def IsSimpleCode (U : Map) (s : ℕ) (e : ℕ) : Prop :=
  kNat U e ≤ (s : ℕ∞)

/-- `x` has an `(i, j)`-description: the pair `(i, j)` lies in the description profile of `x`,
that is, some set of log-cardinality at most `j` containing `x` has complexity at most `i`. -/
noncomputable def HasIJDescription (U : Map) (x : BitString) (i j : ℕ) : Prop :=
  InDescriptionProfile U x i j

/-- Property (b) of Theorem 254: some `s`-simple algorithm enumerates a list of
size at most `2 ^ (i + j)` in which `x` appears at least `2 ^ j` steps before the
end. -/
def HasSimpleEnumeratedList (U : Map) (x : BitString) (s i j : ℕ) : Prop :=
  ∃ (e : ℕ) (L : List BitString), EnumeratesList e L ∧ IsSimpleCode U s e ∧
    L.length ≤ 2 ^ (i + j) ∧ 2 ^ j ≤ tailAfter L x

/-- Property (c) of Theorem 254: some `s`-simple algorithm enumerates, in at most
`2 ^ i` groups, a list of size at most `2 ^ (i + j)` that contains `x`. -/
def HasSimpleGroupedEnumeration (U : Map) (x : BitString) (s i j : ℕ) : Prop :=
  ∃ (e : ℕ) (G : List (List BitString)), EnumeratesGroups e G ∧ IsSimpleCode U s e ∧
    G.length ≤ 2 ^ i ∧ G.flatten.length ≤ 2 ^ (i + j) ∧ x ∈ G.flatten

/-- Property (d) of Theorem 254: in *every* list enumerated by an `s`-simple
algorithm and containing all strings of plain complexity at most `m`, the string
`x` appears at least `2 ^ j` steps before the end. -/
noncomputable def TailInEverySimpleEnumeration (V U : Map) (x : BitString) (s m j : ℕ) : Prop :=
  ∀ (e : ℕ) (L : List BitString), EnumeratesList e L → IsSimpleCode U s e →
    (∀ y : BitString, plainK V y ≤ (m : ℕ∞) → y ∈ L) → 2 ^ j ≤ tailAfter L x

-- `theorem254_equivalences` (ch14-theorem-254) is archived; see `docs/ARCHIVED_TARGETS.md`.

/-! ### Exercises 351–354 -/

-- `exercise351_curve_complexity_needed` (ch14-exercise-351) is archived; see
-- `docs/ARCHIVED_TARGETS.md`.

-- `exercise352_boundary_not_computable` (ch14-exercise-352) is archived; see
-- `docs/ARCHIVED_TARGETS.md`.

/-- The counting fold returns the length of the list in its first component. -/
theorem foldr_length_step (zs : List BitString) (y : BitString) :
    (zs.foldr (fun y' acc => (acc.1 + 1, cond (y' == y) acc.1 acc.2)) (0, 0)).1 = zs.length := by
  induction zs with
  | nil => rfl
  | cons w ws ih_w =>
    rw [List.foldr_cons]
    dsimp
    exact congrArg Nat.succ ih_w

/-- The number of entries after the first occurrence of `y` is computed by the
counting fold. -/
theorem tailAfter_eq_foldr (L : List BitString) (y : BitString) :
    tailAfter L y =
      (L.foldr (fun y' acc => (acc.1 + 1, cond (y' == y) acc.1 acc.2)) (0, 0)).2 := by
  induction L with
  | nil => rfl
  | cons z zs ih =>
    unfold tailAfter
    rw [List.foldr_cons]
    rw [foldr_length_step zs y, ih]
    by_cases hzy : z = y
    · rw [if_pos hzy, hzy]
      have : (y == y) = true := beq_self_eq_true y
      rw [this]; rfl
    · rw [if_neg hzy]
      have hbeq : (z == y) = false := beq_eq_false_iff_ne.mpr hzy
      rw [hbeq]; rfl

/-- The tail count is primitive recursive in the list and the element. -/
theorem tailAfter_primrec : Primrec (fun q : List BitString × BitString => tailAfter q.1 q.2) := by
  have heq : (fun q : List BitString × BitString => tailAfter q.1 q.2) =
      (fun q => (q.1.foldr (fun y' acc =>
        (acc.1 + 1, cond (y' == q.2) acc.1 acc.2)) (0, 0)).2) := by
    funext q
    exact tailAfter_eq_foldr q.1 q.2
  rw [heq]
  have hstep : Primrec₂ (fun (q : List BitString × BitString) (p : BitString × (ℕ × ℕ)) =>
      (p.2.1 + 1, cond (p.1 == q.2) p.2.1 p.2.2)) := by
    have h1 : Primrec (fun (z : (List BitString × BitString) × (BitString × (ℕ × ℕ))) =>
        z.2.2.1 + 1) :=
      Primrec.succ.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
    have hcond : Primrec (fun (z : (List BitString × BitString) × (BitString × (ℕ × ℕ))) =>
        z.2.1 == z.1.2) := by
      have h1 : (fun (z : (List BitString × BitString) × (BitString × (ℕ × ℕ))) =>
          z.2.1 == z.1.2) = (fun z => decide (z.2.1 = z.1.2)) := by
        funext z
        by_cases h : z.2.1 = z.1.2 <;> simp [h]
      rw [h1]
      exact PrimrecPred.decide
        (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.fst))
    have hthen : Primrec (fun (z : (List BitString × BitString) × (BitString × (ℕ × ℕ))) =>
        z.2.2.1) :=
      Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
    have helse : Primrec (fun (z : (List BitString × BitString) × (BitString × (ℕ × ℕ))) =>
        z.2.2.2) :=
      Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
    have h2 : Primrec (fun (z : (List BitString × BitString) × (BitString × (ℕ × ℕ))) =>
        cond (z.2.1 == z.1.2) z.2.2.1 z.2.2.2) :=
      Primrec.cond hcond hthen helse
    exact (Primrec.pair h1 h2).to₂
  have hfold : Primrec (fun q : List BitString × BitString =>
      q.1.foldr (fun y' acc => (acc.1 + 1, cond (y' == q.2) acc.1 acc.2)) (0, 0)) :=
    Primrec.list_foldr Primrec.fst (Primrec.const (0, 0)) hstep
  exact Primrec.snd.comp hfold

/-- Given `y` and the parameters `(n, k_x, k_y)`, wait for the stage at which `y`
has appeared with tail count at least `k_y`, and return the entry `k_y - k_x`
positions before `y`. -/
noncomputable def tailStringsSelector (cd : Code) : BitString → BitString →. BitString := fun y p =>
  let n := bitsToNat (decodeFirst p)
  let k_x := bitsToNat (decodeFirst (decodeSecond p))
  let k_y := bitsToNat (decodeSecond (decodeSecond p))
  (Nat.rfind (fun t => Part.some
    (decide (y ∈ boundedOutputStage cd n t) &&
      decide (k_y ≤ tailAfter (boundedOutputStage cd n t) y)))).bind
    (fun t =>
      let L := boundedOutputStage cd n t
      let idx_y := L.findIdx (· == y)
      let idx_x := idx_y + k_y - k_x
      Part.ofOption (L[idx_x]?)
    )

/-- The tail selector unfolded on an assembled parameter string. -/
theorem tailStringsSelector_eval (cd : Code) (n k_x k_y : ℕ) (y : BitString) :
    tailStringsSelector cd y (pairCode (Nat.bits n) (pairCode (Nat.bits k_x) (Nat.bits k_y))) =
      (Nat.rfind (fun t => Part.some (decide
        (y ∈ boundedOutputStage cd n t ∧ k_y ≤ tailAfter (boundedOutputStage cd n t) y)))).bind
        (fun t =>
          let L := boundedOutputStage cd n t
          let idx_y := L.findIdx (· == y)
          let idx_x := idx_y + k_y - k_x
          Part.ofOption (L[idx_x]?)
        ) := by
  dsimp [tailStringsSelector]
  rw [decodeFirst_pairCode, decodeSecond_pairCode, decodeFirst_pairCode, decodeSecond_pairCode]
  rw [bitsToNat_bits, bitsToNat_bits, bitsToNat_bits]
  congr 2
  ext t
  by_cases h1 : y ∈ boundedOutputStage cd n t
  · by_cases h2 : k_y ≤ tailAfter (boundedOutputStage cd n t) y
    · simp [h1, h2]
    · simp [h1, h2]
  · simp [h1]

/-- The tail selector is partial recursive in its two arguments. -/
theorem tailStringsSelector_partrec (cd : Code) :
    Partrec (fun q : BitString × BitString => tailStringsSelector cd q.1 q.2) := by
  have hn : Primrec (fun q : BitString × BitString => bitsToNat (decodeFirst q.2)) :=
    bitsToNat_primrec.comp (decodeFirst_primrec.comp Primrec.snd)
  have hkx : Primrec (fun q : BitString × BitString =>
      bitsToNat (decodeFirst (decodeSecond q.2))) :=
    bitsToNat_primrec.comp (decodeFirst_primrec.comp (decodeSecond_primrec.comp Primrec.snd))
  have hky : Primrec (fun q : BitString × BitString =>
      bitsToNat (decodeSecond (decodeSecond q.2))) :=
    bitsToNat_primrec.comp (decodeSecond_primrec.comp (decodeSecond_primrec.comp Primrec.snd))
  have hy : Primrec (fun q : BitString × BitString => q.1) := Primrec.fst
  have hL : Primrec (fun p : (BitString × BitString) × ℕ =>
      boundedOutputStage cd (bitsToNat (decodeFirst p.1.2)) p.2) :=
    (boundedOutputStage_primrec cd).comp
      (Primrec.pair (hn.comp Primrec.fst) Primrec.snd)
  have hy' : Primrec (fun p : (BitString × BitString) × ℕ => p.1.1) :=
    hy.comp Primrec.fst
  have hmem : Primrec (fun p : (BitString × BitString) × ℕ =>
      decide (p.1.1 ∈ boundedOutputStage cd (bitsToNat (decodeFirst p.1.2)) p.2)) :=
    bitString_mem_primrec.comp hy' hL
  have htail : Primrec (fun p : (BitString × BitString) × ℕ =>
      tailAfter (boundedOutputStage cd (bitsToNat (decodeFirst p.1.2)) p.2) p.1.1) :=
    tailAfter_primrec.comp (Primrec.pair hL hy')
  have hky' : Primrec (fun p : (BitString × BitString) × ℕ =>
      bitsToNat (decodeSecond (decodeSecond p.1.2))) :=
    hky.comp Primrec.fst
  have hle : Primrec (fun p : (BitString × BitString) × ℕ =>
      decide (bitsToNat (decodeSecond (decodeSecond p.1.2)) ≤
        tailAfter (boundedOutputStage cd (bitsToNat (decodeFirst p.1.2)) p.2) p.1.1)) :=
    PrimrecPred.decide ((Primrec.nat_le : PrimrecRel (fun a b : ℕ => a ≤ b)).comp hky' htail)
  have hcond : Computable₂ (fun (q : BitString × BitString) (t : ℕ) =>
      decide (q.1 ∈ boundedOutputStage cd (bitsToNat (decodeFirst q.2)) t) &&
        decide (bitsToNat (decodeSecond (decodeSecond q.2)) ≤
          tailAfter (boundedOutputStage cd (bitsToNat (decodeFirst q.2)) t) q.1)) :=
    (Primrec₂.comp Primrec.and hmem hle).to_comp.to₂
  have hsearch : Partrec (fun q : BitString × BitString =>
      Nat.rfind (fun t => Part.some (decide (q.1 ∈ boundedOutputStage cd
        (bitsToNat (decodeFirst q.2)) t) && decide (bitsToNat (decodeSecond
        (decodeSecond q.2)) ≤ tailAfter (boundedOutputStage cd
        (bitsToNat (decodeFirst q.2)) t) q.1)))) :=
    Partrec.rfind hcond.partrec₂
  have hpred : Primrec₂ (fun (p : (BitString × BitString) × ℕ) (x : BitString) => x == p.1.1) := by
    have h1 : (fun (p : (BitString × BitString) × ℕ) (x : BitString) => x == p.1.1) =
        (fun p x => decide (x = p.1.1)) := by
      funext p x
      by_cases h : x = p.1.1 <;> simp [h]
    rw [h1]
    exact (PrimrecPred.decide (Primrec.eq.comp Primrec.snd (hy'.comp Primrec.fst))).to₂
  have hidx_y : Primrec (fun p : (BitString × BitString) × ℕ =>
      (boundedOutputStage cd (bitsToNat (decodeFirst p.1.2)) p.2).findIdx (· == p.1.1)) :=
    Primrec.list_findIdx hL hpred
  have hkx' : Primrec (fun p : (BitString × BitString) × ℕ =>
      bitsToNat (decodeFirst (decodeSecond p.1.2))) :=
    hkx.comp Primrec.fst
  have hidx_x : Primrec (fun p : (BitString × BitString) × ℕ =>
      (boundedOutputStage cd (bitsToNat (decodeFirst p.1.2)) p.2).findIdx (· == p.1.1) +
        bitsToNat (decodeSecond (decodeSecond p.1.2)) -
          bitsToNat (decodeFirst (decodeSecond p.1.2))) :=
    Primrec.nat_sub.comp (Primrec.nat_add.comp hidx_y hky') hkx'
  have hget : Primrec (fun p : (BitString × BitString) × ℕ =>
      (boundedOutputStage cd (bitsToNat (decodeFirst p.1.2)) p.2)[
        (boundedOutputStage cd (bitsToNat (decodeFirst p.1.2)) p.2).findIdx (· == p.1.1) +
          bitsToNat (decodeSecond (decodeSecond p.1.2)) -
            bitsToNat (decodeFirst (decodeSecond p.1.2))]?) :=
    Primrec.list_getElem?.comp hL hidx_x
  have hget_comp : Partrec₂ (fun (q : BitString × BitString) (t : ℕ) =>
      Part.ofOption ((boundedOutputStage cd (bitsToNat (decodeFirst q.2)) t)[
        (boundedOutputStage cd (bitsToNat (decodeFirst q.2)) t).findIdx (· == q.1) +
          bitsToNat (decodeSecond (decodeSecond q.2)) -
            bitsToNat (decodeFirst (decodeSecond q.2))]?)) :=
    (Computable.ofOption hget.to_comp).to₂
  unfold tailStringsSelector
  exact Partrec.bind hsearch hget_comp

/-- **Exercise 353.** All the strings at the very end of the enumerated list of
strings of complexity at most `n` — those followed by at most polynomially many
further strings — are mutually simple: the conditional complexity of one given
another is `O(log n)`. -/
theorem tail_strings_mutually_simple (V U : Map) (hV : isOptimalConditional V)
    (_hU : IsOptimalPrefixConditional U) (cd : Code) (_hc : IsCodeFor cd V) (d : ℕ) :
    ∃ C : ℕ, ∀ (n : ℕ) (x y : BitString),
      x ∈ completedBoundedOutput cd n → y ∈ completedBoundedOutput cd n →
      tailAfter (completedBoundedOutput cd n) x ≤ (n + 1) ^ d →
      tailAfter (completedBoundedOutput cd n) y ≤ (n + 1) ^ d →
      condK V x y ≤ ((logSlack C n : ℕ) : ℕ∞) := by
  obtain ⟨C_sel, hC_sel⟩ :=
    condK_partrec_cond_map_le V hV (tailStringsSelector cd) (tailStringsSelector_partrec cd)
  refine ⟨3 * d + 5 + C_sel, fun n x y hx hy hx_tail hy_tail => ?_⟩
  set k_x := tailAfter (completedBoundedOutput cd n) x
  set k_y := tailAfter (completedBoundedOutput cd n) y
  set p := pairCode (Nat.bits n) (pairCode (Nat.bits k_x) (Nat.bits k_y))
  have h_p_sel : x ∈ tailStringsSelector cd y p := by
    rw [tailStringsSelector_eval]
    let t_max := maxHaltingStage cd n
    have h_t_max_mem : y ∈ boundedOutputStage cd n t_max := hy
    have h_t_max_tail : k_y ≤ tailAfter (boundedOutputStage cd n t_max) y := le_refl _
    have hrdom : (Nat.rfind (fun t => Part.some (decide
        (y ∈ boundedOutputStage cd n t ∧ k_y ≤ tailAfter (boundedOutputStage cd n t) y)))).Dom := by
      exact Nat.rfind_dom.mpr
        ⟨t_max, by simp [h_t_max_mem, h_t_max_tail], fun {m} _ => Part.some_dom _⟩
    obtain ⟨t_0, ht_0⟩ := Part.dom_iff_mem.mp hrdom
    rw [Part.mem_bind_iff]
    use t_0
    refine ⟨ht_0, ?_⟩
    have ht_0_spec := (Nat.mem_rfind.mp ht_0).1
    have hy_t0_bool : (decide (y ∈ boundedOutputStage cd n t_0 ∧
        k_y ≤ tailAfter (boundedOutputStage cd n t_0) y)) = true := by
      simpa using ht_0_spec
    let L_0 := boundedOutputStage cd n t_0
    let L_comp := completedBoundedOutput cd n
    have hy_t0 : y ∈ L_0 ∧ k_y ≤ tailAfter L_0 y :=
      of_decide_eq_true hy_t0_bool
    obtain ⟨hy_in_L0, htail_t0⟩ := hy_t0
    have h_prefix : L_0 <+: L_comp := boundedOutputStage_prefix_completed cd n t_0
    obtain ⟨R, h_comp_eq⟩ := h_prefix
    have h_tail_comp : tailAfter L_comp y = tailAfter L_0 y + R.length := by
      have h1 := suffixCountIncluding_append_of_mem hy_in_L0 (R := R)
      rw [h_comp_eq] at h1
      have h2 := suffixCountIncluding_eq_tailAfter_add_one hy
      have h3 := suffixCountIncluding_eq_tailAfter_add_one hy_in_L0
      dsimp [L_comp, L_0] at h1 h2 h3 ⊢
      omega
    have h_tail_eq : tailAfter L_0 y = k_y ∧ R.length = 0 := by
      have h1 : tailAfter L_comp y ≤ tailAfter L_0 y := htail_t0
      have h2 : tailAfter L_comp y = tailAfter L_0 y + R.length := h_tail_comp
      dsimp [k_y, L_comp, L_0] at h1 h2 ⊢
      omega
    have hL0_eq : L_0 = L_comp := by
      have hR_nil : R = [] := List.length_eq_zero_iff.mp h_tail_eq.2
      rw [← h_comp_eq, hR_nil, List.append_nil]
    have hnodup : L_comp.Nodup := boundedOutputStage_nodup cd n (maxHaltingStage cd n)
    have h_idx_y : L_comp.findIdx (· == y) + k_y + 1 = L_comp.length := by
      have h_sum := findIdx_add_suffixCountIncluding_eq_length L_comp y hy
      rw [suffixCountIncluding_eq_tailAfter_add_one hy] at h_sum
      exact h_sum
    have h_idx_x : L_comp.findIdx (· == x) + k_x + 1 = L_comp.length := by
      have h_sum := findIdx_add_suffixCountIncluding_eq_length L_comp x hx
      rw [suffixCountIncluding_eq_tailAfter_add_one hx] at h_sum
      exact h_sum
    have h_idx_eq : L_comp.findIdx (· == x) = L_comp.findIdx (· == y) + k_y - k_x := by
      omega
    have h_get_x : L_comp[L_comp.findIdx (· == x)]? = some x := by
      have h_lt : L_comp.findIdx (· == x) < L_comp.length := by
        rw [List.findIdx_lt_length]
        exact ⟨x, hx, by simp⟩
      rw [List.getElem?_eq_getElem h_lt]
      exact congrArg Option.some (eq_of_beq (List.findIdx_getElem (xs := L_comp) (p := (· == x))))
    change x ∈ Part.ofOption (L_0[L_0.findIdx (· == y) + k_y - k_x]?)
    rw [hL0_eq, ← h_idx_eq, h_get_x]
    exact Part.mem_some x
  have h_condK := hC_sel y p x h_p_sel
  refine h_condK.trans ?_
  set L_n := (Nat.bits n).length
  have h_pow_n : n < 2 ^ L_n := lt_two_pow_length_natBits n
  have h_np1_pow : (n + 1) < 2 ^ (L_n + 1) := by
    calc n + 1 ≤ 2 ^ L_n := h_pow_n
      _ < 2 ^ (L_n + 1) := Nat.pow_lt_pow_right one_lt_two (Nat.lt_succ_self L_n)
  have h_bound_k (k : ℕ) (hk : k ≤ (n + 1) ^ d) : (Nat.bits k).length ≤ d * L_n + d + 1 := by
    have h_np1 : n + 1 ≤ 2 ^ (L_n + 1) := by
      have := lt_two_pow_length_natBits n
      calc n + 1 ≤ 2 ^ L_n := by omega
        _ ≤ 2 ^ (L_n + 1) := Nat.pow_le_pow_right two_pos (by omega)
    have h_pow_d : (n + 1) ^ d ≤ (2 ^ (L_n + 1)) ^ d := Nat.pow_le_pow_left h_np1 d
    have h_pow_eq : (2 ^ (L_n + 1)) ^ d = 2 ^ (d * L_n + d) := by
      rw [← Nat.pow_mul]
      congr 1
      ring
    have h_lt : k < 2 ^ (d * L_n + d + 1) := by
      calc k ≤ (n + 1) ^ d := hk
        _ ≤ (2 ^ (L_n + 1)) ^ d := h_pow_d
        _ = 2 ^ (d * L_n + d) := h_pow_eq
        _ < 2 ^ (d * L_n + d + 1) := Nat.pow_lt_pow_right one_lt_two (by omega)
    exact length_natBits_lt_pow h_lt
  have h_kx_len := h_bound_k k_x hx_tail
  have h_ky_len := h_bound_k k_y hy_tail
  have h_p_len : p.length = 2 * L_n + 2 * (Nat.bits k_x).length + (Nat.bits k_y).length + 2 := by
    dsimp [p]
    rw [length_pairCode, length_pairCode]
    ring
  have h_p_len_bound : p.length + C_sel ≤ (3 * d + 5 + C_sel) * L_n + (3 * d + 5 + C_sel) := by
    dsimp [p] at h_p_len
    have h_p1 : p.length = 2 * L_n + 2 * (Nat.bits k_x).length + (Nat.bits k_y).length + 2 :=
      h_p_len
    have h_kx1 : (Nat.bits k_x).length ≤ d * L_n + d + 1 := h_kx_len
    have h_ky1 : (Nat.bits k_y).length ≤ d * L_n + d + 1 := h_ky_len
    calc p.length + C_sel
      _ = 2 * L_n + 2 * (Nat.bits k_x).length + (Nat.bits k_y).length + 2 + C_sel := by rw [h_p1]
      _ ≤ 2 * L_n + 2 * (d * L_n + d + 1) + (d * L_n + d + 1) + 2 + C_sel := by omega
      _ = (3 * d + 2) * L_n + 3 * d + 5 + C_sel := by ring
      _ ≤ (3 * d + 5 + C_sel) * L_n + (3 * d + 5 + C_sel) := by
        have : (3 * d + 2) * L_n ≤ (3 * d + 5 + C_sel) * L_n := Nat.mul_le_mul_right L_n (by omega)
        omega
  unfold logSlack
  exact_mod_cast h_p_len_bound

open Kolmogorov.CodedFiniteDistribution

/-- Construct uniform set model code directly from a list of points. -/
noncomputable def codeFromList (pts : List BitString) : BitString :=
  canonicalUniformCodeOfList (canonicalFinsetList pts.toFinset)

/-- Building the uniform model code of a list of points is primitive recursive. -/
theorem codeFromList_primrec : Primrec codeFromList :=
  canonicalUniformCodeOfList_primrec.comp canonicalFinsetList_toFinset_primrec

/-- On a list with nonempty underlying set, the code built from the list is the
canonical uniform code of that set. -/
theorem codeFromList_eq (pts : List BitString) (hne : pts.toFinset.Nonempty) :
    codeFromList pts = (codedUniformOn pts.toFinset hne).code :=
  canonicalUniformCodeOfList_canonicalFinsetList pts.toFinset hne

/-- Check if fuel is sufficient to evaluate `e` on all points in `pts`. -/
def bijectionEvalFuel (e : ℕ) (pts : List BitString) (fuel : ℕ) : Bool :=
  pts.all (fun w =>
    (Nat.Partrec.Code.evaln fuel (Denumerable.ofNat Code e) (Encodable.encode w)).isSome)

/-- Map the code `e` over `pts` with step budget `fuel`, decoding each output as a bit string
and returning the empty string where `e` has not halted within the budget. -/
def bijectionRun (e : ℕ) (fuel : ℕ) (pts : List BitString) : List BitString :=
  pts.map (fun w =>
    match Nat.Partrec.Code.evaln fuel (Denumerable.ofNat Code e) (Encodable.encode w) with
    | some r => (Encodable.decode r : Option BitString).getD []
    | none => [])

/-- Whether the given fuel suffices to evaluate the coded machine on every point of
the coded model. -/
def bijectionCheck (p : BitString × ℕ) : Bool :=
  let c_S := decodeFirst p.1
  let e_bits := decodeSecond p.1
  let e := decodeBits e_bits
  let entries := decodeDistributionData c_S
  let pts := entries.map CodedDistributionEntry.point
  bijectionEvalFuel e pts p.2

/-- The uniform model code of the image of the coded model under the coded machine,
run with the given fuel. -/
noncomputable def bijectionPost (p : BitString × ℕ) : BitString :=
  let c_S := decodeFirst p.1
  let e_bits := decodeSecond p.1
  let e := decodeBits e_bits
  let entries := decodeDistributionData c_S
  let pts := entries.map CodedDistributionEntry.point
  codeFromList (bijectionRun e p.2 pts)

attribute [local irreducible] bijectionCheck bijectionPost

/-- The fuel check is partial recursive. -/
theorem bijectionCheck_partrec :
    Partrec (fun p : BitString × ℕ => Part.some (bijectionCheck p)) := by
  have h_code : Primrec (fun p : BitString × ℕ =>
      Denumerable.ofNat Code (decodeBits (decodeSecond p.1))) :=
    (Primrec.ofNat Code).comp (primrec_decodeBits.comp (decodeSecond_primrec.comp Primrec.fst))
  have h_pts : Primrec (fun p : BitString × ℕ =>
      (decodeDistributionData (decodeFirst p.1)).map CodedDistributionEntry.point) :=
    Primrec.list_map (decodeDistributionData_primrec.comp (decodeFirst_primrec.comp Primrec.fst))
      (entry_point_primrec.comp Primrec.snd).to₂
  have h_evaln : Primrec (fun (p : (BitString × ℕ) × BitString) =>
      (Nat.Partrec.Code.evaln p.1.2 (Denumerable.ofNat Code (decodeBits (decodeSecond p.1.1)))
        (Encodable.encode p.2)).isSome) := by
    have h_fuel : Primrec (fun p : (BitString × ℕ) × BitString => p.1.2) :=
      Primrec.snd.comp Primrec.fst
    have h_c : Primrec (fun p : (BitString × ℕ) × BitString =>
        Denumerable.ofNat Code (decodeBits (decodeSecond p.1.1))) :=
      h_code.comp Primrec.fst
    have h_enc : Primrec (fun p : (BitString × ℕ) × BitString => Encodable.encode p.2) :=
      Primrec.encode.comp Primrec.snd
    have h_evaln_opt := Nat.Partrec.Code.primrec_evaln.comp ((h_fuel.pair h_c).pair h_enc)
    exact Primrec.option_isSome.comp h_evaln_opt
  have h_check : Primrec bijectionCheck := by
    unfold bijectionCheck bijectionEvalFuel
    exact list_all_primrec h_pts h_evaln.to₂
  exact h_check.to_comp.partrec

/-- The image-model construction is partial recursive. -/
theorem bijectionPost_partrec : Partrec (fun p : BitString × ℕ => Part.some (bijectionPost p)) := by
  have h_code : Primrec (fun p : BitString × ℕ =>
      Denumerable.ofNat Code (decodeBits (decodeSecond p.1))) :=
    (Primrec.ofNat Code).comp (primrec_decodeBits.comp (decodeSecond_primrec.comp Primrec.fst))
  have h_pts : Primrec (fun p : BitString × ℕ =>
      (decodeDistributionData (decodeFirst p.1)).map CodedDistributionEntry.point) :=
    Primrec.list_map (decodeDistributionData_primrec.comp (decodeFirst_primrec.comp Primrec.fst))
      (entry_point_primrec.comp Primrec.snd).to₂
  have h_evaln_opt : Primrec (fun (p : (BitString × ℕ) × BitString) =>
      Nat.Partrec.Code.evaln p.1.2 (Denumerable.ofNat Code (decodeBits (decodeSecond p.1.1)))
        (Encodable.encode p.2)) := by
    have h_fuel : Primrec (fun p : (BitString × ℕ) × BitString => p.1.2) :=
      Primrec.snd.comp Primrec.fst
    have h_c : Primrec (fun p : (BitString × ℕ) × BitString =>
        Denumerable.ofNat Code (decodeBits (decodeSecond p.1.1))) :=
      h_code.comp Primrec.fst
    have h_enc : Primrec (fun p : (BitString × ℕ) × BitString => Encodable.encode p.2) :=
      Primrec.encode.comp Primrec.snd
    exact Nat.Partrec.Code.primrec_evaln.comp ((h_fuel.pair h_c).pair h_enc)
  have h_getD : Primrec₂ (fun (p : (BitString × ℕ) × BitString) (r : ℕ) =>
      (Encodable.decode r : Option BitString).getD []) :=
    primrecDecodeGetD.comp₂ Primrec₂.right
  have h_cases : Primrec (fun (p : (BitString × ℕ) × BitString) =>
      match Nat.Partrec.Code.evaln p.1.2
        (Denumerable.ofNat Code (decodeBits (decodeSecond p.1.1)))
        (Encodable.encode p.2) with
      | some r => (Encodable.decode r : Option BitString).getD []
      | none => []) :=
    (Primrec.option_casesOn h_evaln_opt (Primrec.const []) h_getD).of_eq (fun p => by
      cases Nat.Partrec.Code.evaln p.1.2 (Denumerable.ofNat Code (decodeBits (decodeSecond p.1.1)))
        (Encodable.encode p.2) <;> rfl)
  have h_run : Primrec (fun p : BitString × ℕ => bijectionRun (decodeBits (decodeSecond p.1)) p.2
      ((decodeDistributionData (decodeFirst p.1)).map CodedDistributionEntry.point)) :=
    Primrec.list_map h_pts h_cases.to₂
  have h_post : Primrec bijectionPost := by
    unfold bijectionPost
    exact codeFromList_primrec.comp h_run
  exact h_post.to_comp.partrec

/-- Partial recursive map evaluating simple bijection `e` on the uniform set model. -/
noncomputable def bijectionImageMap (input : BitString) : Part BitString :=
  (Nat.rfind (fun fuel => Part.some (bijectionCheck (input, fuel)))).map (fun fuel =>
    bijectionPost (input, fuel))

/-- The map sending a coded model and a machine code to the code of the image model
is partial recursive. -/
theorem bijectionImageMap_partrec : Partrec bijectionImageMap := by
  have h_rf : Partrec (fun input =>
      Nat.rfind (fun fuel => Part.some (bijectionCheck (input, fuel)))) := by
    refine Partrec.rfind ?_
    exact bijectionCheck_partrec.to₂
  exact Partrec.map h_rf bijectionPost_partrec.to₂

/-- If the fuel suffices on every point, the run returns the pointwise image of the
list under the computed function. -/
theorem bijectionRun_eq (e : ℕ) (fuel : ℕ) (pts : List BitString) (pi : BitString → BitString)
    (he : ∀ w ∈ pts, ∃ r,
      Nat.Partrec.Code.evaln fuel (Denumerable.ofNat Code e) (Encodable.encode w) = some r ∧
      (Encodable.decode r : Option BitString).getD [] = pi w) :
    bijectionRun e fuel pts = pts.map pi := by
  unfold bijectionRun
  induction pts with
  | nil => rfl
  | cons w pts ih =>
    simp only [List.map_cons]
    have hw : ∃ r,
        Nat.Partrec.Code.evaln fuel (Denumerable.ofNat Code e) (Encodable.encode w) = some r ∧
        (Encodable.decode r : Option BitString).getD [] = pi w :=
      he w List.mem_cons_self
    obtain ⟨r, hr1, hr2⟩ := hw
    have ih_res := ih (fun v hv => he v (List.mem_cons_of_mem w hv))
    simp [hr1, hr2, ih_res]

end Kolmogorov
