/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Interface.Dovetailing
import KolmogorovMathlib.AlgorithmicProbability.CompatibleGraphs
import KolmogorovMathlib.AlgorithmicProbability.HaltingProbabilityApproximation
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitinApplications.Part01
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitinApplications.Part02
import KolmogorovMathlib.Interface.ComputableReals.LowerSemicomputableReals
import KolmogorovMathlib.MonotoneComplexity.Omega.SolovayInverse
import KolmogorovMathlib.Prefix.BlockingReadMachines
import KolmogorovMathlib.Prefix.ExtensionTheorem
import KolmogorovMathlib.Prefix.NumericalValues
import KolmogorovMathlib.Prefix.PairComplexity
import KolmogorovMathlib.Prefix.SelfDelimitingMachines
import KolmogorovMathlib.Prefix.StableDecompressors
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
import KolmogorovMathlib.Restricted.DeficiencyEquiv
import KolmogorovMathlib.MonotoneComplexity.Dimension.ChangeOfMeasure
import KolmogorovMathlib.Restricted.DescriptionProfileGap.SlackArithmetic
import KolmogorovMathlib.Restricted.DescriptionProfileGap

/-!
# The structure function against the randomness deficiency

The lower bound `K(x) + d <= i + h_x(i) + O(log)` relating the structure
function `structureFunction` of `x` to the deficiency of `x` in a minimising
model, kept as the proved half of an item whose remaining half is archived in
`docs/ARCHIVED_TARGETS.md`.

SUV Exercise 367, p. 505.
-/

namespace Kolmogorov
open scoped ENNReal
open Nat.Partrec (Code)
open CodedFiniteDistribution
open Kolmogorov.CodedFiniteDistribution
open ENat

/-- The two standing bounds of the deficiency estimate for `U`: a string in the
description profile `(i, j)` has prefix complexity at most `i + j` up to the
logarithmic slack of `c_prof`, and a set-optimality deficiency bound becomes a
deficiency bound at the cost of the constant `c_opt`. -/
private def DeficiencyProfileBounds (U : Map) (c_prof c_opt : ℕ) : Prop :=
  (∀ (x : BitString) (n i j : ℕ), x.length = n → InDescriptionProfile U x i j →
      KPPlain U x ≤ (i + j + logSlack c_prof (n + i + j) : ℕ∞)) ∧
    ∀ (P : CodedFiniteDistribution) (x : BitString) (beta : ℕ),
      OptimalityDeficiencyLe U P x beta → DeficiencyLe U P x (beta + c_opt)

/-- Deficiency in a minimal set is bounded by profile parameters and complexity slack. -/
private theorem deficiency_le_profile_slack (U : Map) (c_prof c_opt : ℕ)
    (hbounds : DeficiencyProfileBounds U c_prof c_opt)
    {x : BitString} {kx alpha d idx s_idx : ℕ}
    (hkx : KPPlain U x = (kx : ENat)) (hidx : idx ≤ alpha)
    (h_prof : InDescriptionProfile U x idx s_idx)
    (hminA : ∀ (B : Finset BitString) (hB : B.Nonempty), x ∈ B →
      setComplexity U B hB ≤ (alpha : ℕ∞) → (d : ℕ∞) ≤ deficiencyValue U B hB x) :
    kx + d ≤ idx + s_idx + (logSlack c_prof (x.length + idx + s_idx) + c_opt) := by
  obtain ⟨hc_prof, hc_opt⟩ := hbounds
  obtain ⟨B, hB, hxB, hcompB, hsizeB⟩ := h_prof
  have h_comp_finite : setComplexity U B hB ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.natCast_ne_top idx) hcompB
  set i_B := (setComplexity U B hB).toNat
  have hi_B_eq : setComplexity U B hB = (i_B : ENat) := (ENat.natCast_toNat h_comp_finite).symm
  have hi_B_le_idx : i_B ≤ idx := by
    have : (i_B : ENat) ≤ (idx : ENat) := hi_B_eq ▸ hcompB
    exact_mod_cast this
  have hi_B_le_alpha : (i_B : ENat) ≤ (alpha : ENat) := by exact_mod_cast (hi_B_le_idx.trans hidx)
  have hcompB_le : setComplexity U B hB ≤ (alpha : ℕ∞) := hi_B_eq.symm ▸ hi_B_le_alpha
  have hdef_B := hminA B hB hxB hcompB_le
  have hkx_prof : (kx : ENat) ≤
      ((idx + s_idx + logSlack c_prof (x.length + idx + s_idx) : ℕ) : ENat) := by
    have h0 := hc_prof x x.length idx s_idx rfl ⟨B, hB, hxB, hcompB, hsizeB⟩
    rwa [← hkx]
  have hkx_prof_nat : kx ≤ idx + s_idx + logSlack c_prof (x.length + idx + s_idx) := by
    exact_mod_cast hkx_prof
  set S1 := logSlack c_prof (x.length + idx + s_idx)
  set beta_0 := idx + s_idx + S1 - kx
  have h_arith : (i_B : ENat) + (s_idx : ENat) ≤ KPPlain U x + (beta_0 : ENat) := by
    rw [hkx]
    exact_mod_cast (by omega)
  have h_opt_B : SetOptimalityDeficiencyLe U B hB x beta_0 :=
    setOptimalityDeficiencyLe_of_profile hxB hi_B_eq.le hsizeB h_arith
  have h_def_B : DeficiencyLe U (codedUniformOn B hB) x (beta_0 + c_opt) :=
    hc_opt (codedUniformOn B hB) x beta_0 h_opt_B
  have h_val_le : deficiencyValue U B hB x ≤ (beta_0 + c_opt : ℕ∞) :=
    sInf_le ⟨beta_0 + c_opt, rfl, h_def_B⟩
  have h_d_le : (d : ℕ∞) ≤ (beta_0 + c_opt : ℕ∞) := hdef_B.trans h_val_le
  have h_d_le_nat : d ≤ beta_0 + c_opt := by exact_mod_cast h_d_le
  dsimp [beta_0] at h_d_le_nat
  omega

private theorem structureFunction_deficiency_lower_bound (U : Map)
    (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (alpha d : ℕ) (A : Finset BitString) (hA : A.Nonempty),
      x ∈ A →
      setComplexity U A hA ≤ (alpha : ℕ∞) →
      deficiencyValue U A hA x = (d : ℕ∞) →
      (∀ (B : Finset BitString) (hB : B.Nonempty), x ∈ B →
        setComplexity U B hB ≤ (alpha : ℕ∞) → (d : ℕ∞) ≤ deficiencyValue U B hB x) →
      ∀ idx ≤ alpha,
        KPPlain U x + (d : ℕ∞) ≤ (idx : ℕ∞) + structureFunction U x idx + (logSlack c (x.length
          + alpha + d) : ℕ∞) := by
  obtain ⟨c_prof, hc_prof⟩ := KPPlain_le_of_inDescriptionProfile U hU
  obtain ⟨c_opt, hc_opt⟩ := randomness_optimality U hU
  obtain ⟨c_len, hc_len⟩ := KPPlain_le_length_add_log U hU
  obtain ⟨c_plain, hc_plain⟩ := KP_le_KPPlain U hU
  obtain ⟨C_fold, hC_fold⟩ := logSlack_linear_bound c_prof 10 (c_len + c_plain + 100)
  set c := C_fold + c_opt + 10
  use c
  intro x alpha d A hA hxA hcompA hdefA hminA idx hidx
  by_cases h_top : structureFunction U x idx = ⊤
  · rw [h_top]; exact le_top
  · set s_idx := (structureFunction U x idx).toNat
    have h_sf_eq : structureFunction U x idx = (s_idx : ℕ∞) := (ENat.natCast_toNat h_top).symm
    have h_prof_idx_spec : InDescriptionProfile U x idx s_idx :=
      (inDescriptionProfile_iff_structureFunction_le U x idx s_idx).mpr h_sf_eq.le
    have h_prof_idx : InDescriptionProfile U x idx s_idx := h_prof_idx_spec
    have hkx_ne_top : KPPlain U x ≠ ⊤ := KPPlain_ne_top_of_optimal U hU x
    set kx := (KPPlain U x).toNat
    have hkx_eq : KPPlain U x = (kx : ENat) := (ENat.natCast_toNat hkx_ne_top).symm
    set n := x.length
    by_cases h_easy : kx + d ≤ idx
    · calc KPPlain U x + (d : ℕ∞)
          = ((kx + d : ℕ) : ℕ∞) := by rw [hkx_eq]; push_cast; rfl
        _ ≤ ((idx + s_idx : ℕ) : ℕ∞) := by exact_mod_cast (by omega)
        _ = (idx : ℕ∞) + structureFunction U x idx := by rw [h_sf_eq]; push_cast; rfl
        _ ≤ (idx : ℕ∞) + structureFunction U x idx + (logSlack c (n + alpha + d) : ℕ∞) :=
            self_le_add_right _ _
    · push Not at h_easy
      have h_sum_le : kx + d ≤ idx + s_idx + (logSlack c_prof (n + idx + s_idx) + c_opt) :=
        deficiency_le_profile_slack U c_prof c_opt ⟨hc_prof, hc_opt⟩ hkx_eq hidx
          h_prof_idx hminA
      set S1 := logSlack c_prof (n + idx + s_idx)
      set M := n + alpha + d
      have h_kx_bound : kx ≤ 3 * n + c_len := by
        have h_len := hc_len x
        rw [hkx_eq] at h_len
        have h_bits : (Nat.bits n).length ≤ n := length_natBits_le n
        exact kx_le_3n_add_clen h_bits (by exact_mod_cast h_len)
      have hM : M = n + alpha + d := rfl
      by_cases h_s_idx_le : s_idx ≤ 3 * M + (c_len + c_plain + 100)
      · have h_arg_le : n + idx + s_idx ≤ 10 * M + (c_len + c_plain + 100) := by omega
        have h_S1_bound : S1 ≤ logSlack C_fold M :=
          (logSlack_mono_right c_prof h_arg_le).trans (hC_fold M)
        have h_slack : S1 + c_opt ≤ logSlack c M := by
          have h1 : S1 + c_opt ≤ logSlack C_fold M + c_opt := by omega
          have h2 : logSlack C_fold M + c_opt ≤ logSlack (C_fold + c_opt) M :=
            logSlack_add_const_le C_fold c_opt M
          have h3 : C_fold + c_opt ≤ c := by
            change C_fold + c_opt ≤ C_fold + c_opt + 10
            omega
          exact h1.trans (h2.trans (logSlack_mono_left h3 M))
        calc KPPlain U x + (d : ℕ∞)
            = (kx : ℕ∞) + (d : ℕ∞) := by rw [hkx_eq]
          _ = ((kx + d : ℕ) : ℕ∞) := by push_cast; rfl
          _ ≤ ((idx + s_idx + (S1 + c_opt) : ℕ) : ℕ∞) := by exact_mod_cast h_sum_le
          _ = (idx : ℕ∞) + (s_idx : ℕ∞) + ((S1 + c_opt : ℕ) : ℕ∞) := by push_cast; ring
          _ ≤ (idx : ℕ∞) + (s_idx : ℕ∞) + (logSlack c M : ℕ∞) := by gcongr
          _ = (idx : ℕ∞) + structureFunction U x idx + (logSlack c (x.length + alpha + d) : ℕ∞) :=
            by
              rw [← h_sf_eq]
      · push Not at h_s_idx_le
        have hM' : M = n + alpha + d := rfl
        have hgoal : kx + d ≤ idx + s_idx := by omega
        calc KPPlain U x + (d : ℕ∞)
            = ((kx + d : ℕ) : ℕ∞) := by rw [hkx_eq]; push_cast; rfl
          _ ≤ ((idx + s_idx : ℕ) : ℕ∞) := by exact_mod_cast hgoal
          _ = (idx : ℕ∞) + structureFunction U x idx := by rw [h_sf_eq]; push_cast; rfl
          _ ≤ (idx : ℕ∞) + structureFunction U x idx + (logSlack c (x.length + alpha + d) : ℕ∞) :=
              self_le_add_right _ _

-- `exercise367_slope_minus_one_segment` (ch14-exercise-367) is archived; see
-- `docs/ARCHIVED_TARGETS.md`.

end Kolmogorov


