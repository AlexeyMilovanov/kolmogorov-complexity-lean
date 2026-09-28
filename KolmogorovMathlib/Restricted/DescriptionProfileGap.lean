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
import KolmogorovMathlib.AlgorithmicStatistics.DeficiencyValue
import KolmogorovMathlib.AlgorithmicStatistics.StochasticityProfile
import KolmogorovMathlib.AlgorithmicStatistics.DescriptionProfileInvariance
import KolmogorovMathlib.Restricted.MinimalRestrictedDescriptions

/-!
# The Hamming gap between the restricted and the unrestricted profile

The Hamming-ball family of descriptions: a string of length `n` whose profile
restricted to that family has a gap against its unrestricted profile
(`hammingGap_restricted_profile`), together with the approximation complexity
`approxComplexity` and the profile minimum `hammingBallProfileMin` of the
Hamming balls.

SUV Chapter 14, Section 14.5 (restricted descriptions).
-/

namespace Kolmogorov
open scoped ENNReal
open Nat.Partrec (Code)
open CodedFiniteDistribution
open Kolmogorov.CodedFiniteDistribution

/-! ### Exercises 359 and 361: Hamming balls -/

/-- If the Hamming volume is at least `2 ^ v`, the list-decoding parameter `2 ^ n / vol` is at
most `2 ^ (n - v)`. -/
lemma bits_length_bound_of_div (n v : ℕ) (hv : 2 ^ v ≤ hammingVol n (n / 64)) :
    (2 ^ n / hammingVol n (n / 64)) ≤ 2 ^ (n - v) := by
  have hV_pos : 0 < hammingVol n (n / 64) := hammingVol_pos n (n / 64)
  by_cases hvn : v ≤ n
  · have h1 : 2 ^ n / hammingVol n (n / 64) * 2 ^ v ≤
        2 ^ n / hammingVol n (n / 64) * hammingVol n (n / 64) :=
      Nat.mul_le_mul_left _ hv
    have h2 : 2 ^ n / hammingVol n (n / 64) * hammingVol n (n / 64) ≤ 2 ^ n :=
      Nat.div_mul_le_self (2 ^ n) (hammingVol n (n / 64))
    have h3 : 2 ^ n / hammingVol n (n / 64) * 2 ^ v ≤ 2 ^ n := h1.trans h2
    have h4 : 2 ^ n / hammingVol n (n / 64) * 2 ^ v ≤ 2 ^ (n - v) * 2 ^ v := by
      calc 2 ^ n / hammingVol n (n / 64) * 2 ^ v ≤ 2 ^ n := h3
        _ = 2 ^ (n - v) * 2 ^ v := by rw [← pow_add, Nat.sub_add_cancel hvn]
    exact Nat.le_of_mul_le_mul_right h4 (by positivity)
  · have hnv : n - v = 0 := Nat.sub_eq_zero_of_le (by omega)
    rw [hnv, pow_zero]
    have h2n : 2 ^ n < 2 ^ v := Nat.pow_lt_pow_right (by decide) (by omega)
    have hV : 2 ^ n < hammingVol n (n / 64) := lt_of_lt_of_le h2n hv
    have hdiv : 2 ^ n / hammingVol n (n / 64) = 0 := Nat.div_eq_of_lt hV
    rw [hdiv]
    exact Nat.zero_le 1

/-- Two-part description of a point in an intersection: the point's prefix complexity is at
most the two set complexities plus the index inside the intersection, so a lower bound on the
complexity of the point bounds the size of the ambient set. -/
private lemma sub_le_logSlack_add_of_intersection {U : Map} {x : BitString}
    {E B : Finset BitString} {hE_ne : E.Nonempty} {hB_ne : B.Nonempty}
    {n v_0 i c_E c_x c_int Bud : ℕ}
    (hE_K : setComplexity U E hE_ne ≤ (logSlack c_E n : ENat))
    (hB_comp : setComplexity U B hB_ne ≤ (i : ENat))
    (hbits : (Nat.bits (E ∩ B).card).length ≤ Bud)
    (hKP_le : KPPlain U x ≤ setComplexity U E hE_ne + setComplexity U B hB_ne +
      (Nat.bits (E ∩ B).card).length + (c_int : ENat))
    (hlow : ((n - v_0 - 1 : ℕ) : ENat) ≤ KPPlain U x + (c_x : ENat)) :
    n - v_0 - 1 ≤ logSlack c_E n + i + Bud + c_int + c_x := by
  have h_bits_cast : ((Nat.bits (E ∩ B).card).length : ENat) ≤ (Bud : ENat) := by
    exact_mod_cast hbits
  have h1 : KPPlain U x ≤
      (logSlack c_E n : ENat) + (i : ENat) + (Bud : ENat) + (c_int : ENat) :=
    hKP_le.trans (add_le_add (add_le_add (add_le_add hE_K hB_comp) h_bits_cast)
      (le_refl (c_int : ENat)))
  have h4 : ((n - v_0 - 1 : ℕ) : ENat) ≤
      (logSlack c_E n : ENat) + (i : ENat) + (Bud : ENat) + (c_int : ENat) + (c_x : ENat) := by
    calc ((n - v_0 - 1 : ℕ) : ENat) ≤ KPPlain U x + (c_x : ENat) := hlow
      _ ≤ (logSlack c_E n : ENat) + (i : ENat) + (Bud : ENat) + (c_int : ENat) +
          (c_x : ENat) := by gcongr
  exact_mod_cast h4

/-- If the Hamming volume is below `2 ^ (v + 1)`, the parameter `2 ^ n / vol` is at least
`2 ^ (n - v - 1)`. -/
lemma bits_length_lower_bound_of_div (n v : ℕ)
    (hV_lt : hammingVol n (n / 64) < 2 ^ (v + 1)) :
    2 ^ (n - v - 1) ≤ 2 ^ n / hammingVol n (n / 64) := by
  have hV_pos : 0 < hammingVol n (n / 64) := hammingVol_pos n (n / 64)
  by_cases hvn : v + 1 ≤ n
  · have hmul : 2 ^ (n - v - 1) * hammingVol n (n / 64) ≤ 2 ^ n := by
      have h1 : 2 ^ (n - v - 1) * hammingVol n (n / 64) < 2 ^ (n - v - 1) * 2 ^ (v + 1) :=
        Nat.mul_lt_mul_of_pos_left hV_lt (by positivity)
      rw [← pow_add, show (n - v - 1) + (v + 1) = n by omega] at h1
      exact h1.le
    exact (Nat.le_div_iff_mul_le hV_pos).mpr hmul
  · have hnv : n - v - 1 = 0 := by omega
    rw [hnv, pow_zero]
    have hV_le : hammingVol n (n / 64) ≤ 2 ^ n := hammingVol_le_two_pow n (n / 64)
    exact Nat.div_pos hV_le hV_pos

private lemma hammingSet_inDescriptionProfile (U : Map) (n v_0 N c_E c0 : ℕ)
    (E : Finset BitString) (hE_ne : E.Nonempty) (hE_is : IsHammingListDecodingSet n (n / 64) N E)
    (hE_K : setComplexity U E hE_ne ≤ (logSlack c_E n : ENat))
    (x : BitString) (hx_in : x ∈ E) (hN_le : N ≤ 2 ^ (n - v_0))
    (hc_E_le : c_E ≤ c0) :
    InDescriptionProfile U x (logSlack c0 n) (n - v_0) := by
  have hslack_E : logSlack c_E n ≤ logSlack c0 n := logSlack_mono_left hc_E_le n
  refine ⟨E, hE_ne, hx_in, ?_, by rw [hE_is.2.1]; exact hN_le⟩
  calc setComplexity U E hE_ne ≤ (logSlack c_E n : ENat) := hE_K
    _ ≤ (logSlack c0 n : ENat) := by exact_mod_cast hslack_E

private lemma hammingGap_profile_exclusion (U : Map) (_hU : IsOptimalPrefixConditional U)
    (n v_0 N c_E c_x c_int c_bits1 c_bits8 c0 : ℕ)
    (E : Finset BitString) (hE_ne : E.Nonempty) (hE_is : IsHammingListDecodingSet n (n / 64) N E)
    (hE_K : setComplexity U E hE_ne ≤ (logSlack c_E n : ENat))
    (x : BitString) (hx_in : x ∈ E) (_hx_len : x.length = n)
    (hx_K : ((Nat.bits E.card).length : ENat) ≤ KPPlain U x + (c_x : ENat))
    (hv_le : 2 ^ v_0 ≤ hammingVol n (n / 64))
    (hN_ge : 2 ^ (n - v_0 - 1) ≤ N)
    (hc_int : ∀ (E B : Finset BitString) (hE : E.Nonempty) (hB : B.Nonempty) (x : BitString),
      x ∈ E ∩ B → KPPlain U x ≤ setComplexity U E hE + setComplexity U B hB +
        (Nat.bits (E ∩ B).card).length + (c_int : ENat))
    (hc_bits1 : ∀ n, (Nat.bits (1 * (n + 1) ^ 1)).length ≤ logSlack c_bits1 n)
    (hc_bits8 : ∀ n, (Nat.bits (8 * (n + 1) ^ 1)).length ≤ logSlack c_bits8 n)
    (hc0_1 : c_E + c_bits1 + c_int + c_x + 1 ≤ c0)
    (hc0_8 : c_E + 8 * c_bits8 + c_int + c_x + 2 ≤ c0) :
    ∀ i j : ℕ, i + max j v_0 + logSlack c0 n < n →
      ¬ InDescriptionProfileIn hammingFamily U x i j := by
  intro i j hij hprof
  obtain ⟨B, hB_ne, hB_mem, hxB, hB_comp, hB_card⟩ := hprof
  have hB_mem' : ∃ z r', z.length = n ∧ B = hammingBall n z r' := by
    rcases hB_mem with ⟨n_b, z, r', hzlen, hB_eq⟩
    have hxB' := hxB
    rw [hB_eq, hammingBall, Finset.mem_filter] at hxB'
    have hx_m := (mem_stringsOfLength n_b x).mp hxB'.1
    have hn_b : n_b = n := by omega
    subst hn_b
    exact ⟨z, r', hzlen, hB_eq⟩
  obtain ⟨z, r', hz_len, rfl⟩ := hB_mem'
  have hxB_ball : x ∈ hammingBall n z r' := hxB
  have hxB_ne' : (hammingBall n z r').Nonempty := hB_ne
  have hxB_comp' : setComplexity U (hammingBall n z r') hxB_ne' ≤ (i : ENat) := hB_comp
  have hxB_card' : (hammingBall n z r').card ≤ 2 ^ j := hB_card
  have hx_inter : x ∈ E ∩ hammingBall n z r' := Finset.mem_inter.mpr ⟨hx_in, hxB_ball⟩
  have hKP_le := hc_int E (hammingBall n z r') hE_ne hxB_ne' x hx_inter
  have hx_K_lower : (Nat.bits N).length ≤ KPPlain U x + (c_x : ENat) := by
    have := hx_K
    rw [hE_is.2.1] at this
    exact_mod_cast this
  have hN_bits_lower : n - v_0 - 1 ≤ (Nat.bits N).length := by
    have h_not_lt : ¬ N < 2 ^ (n - v_0 - 1) := not_lt.mpr hN_ge
    have h_not_le : ¬ Nat.size N ≤ n - v_0 - 1 := fun h => h_not_lt (Nat.size_le.mp h)
    have h_sz : n - v_0 - 1 < Nat.size N := by omega
    rw [← Nat.size_eq_bits_len] at h_sz
    exact h_sz.le
  by_cases hj_le : j ≤ v_0
  · have hB_vol : (hammingBall n z r').card ≤ hammingVol n (n / 64) := by
      calc (hammingBall n z r').card ≤ 2 ^ j := hxB_card'
        _ ≤ 2 ^ v_0 := Nat.pow_le_pow_right (by decide) hj_le
        _ ≤ hammingVol n (n / 64) := hv_le
    have hB_family : hammingFamilyMem (hammingBall n z r') := ⟨n, z, r', hz_len, rfl⟩
    have hinter_card : (hammingBall n z r' ∩ E).card ≤ n := hE_is.2.2 _ hB_family hB_vol
    have hinter_card' : (E ∩ hammingBall n z r').card ≤ n := by
      rwa [Finset.inter_comm] at hinter_card
    have hbits_inter : (Nat.bits (E ∩ hammingBall n z r').card).length ≤ (Nat.bits n).length :=
      length_natBits_mono hinter_card'
    have hbits_n_slack : (Nat.bits (1 * (n + 1) ^ 1)).length ≤ logSlack c_bits1 n := hc_bits1 n
    have hbits_n_slack' : (Nat.bits n).length ≤ logSlack c_bits1 n := by
      have h_eq1 : 1 * (n + 1) ^ 1 = n + 1 := by ring
      have h_bits_le : (Nat.bits n).length ≤ (Nat.bits (n + 1)).length :=
        length_natBits_mono (by omega)
      rw [h_eq1] at hbits_n_slack
      exact h_bits_le.trans hbits_n_slack
    have hcontra : n ≤ i + max j v_0 + logSlack c0 n := by
      have hmax : max j v_0 = v_0 := max_eq_right hj_le
      rw [hmax]
      have h2 : ((n - v_0 - 1 : ℕ) : ENat) ≤ KPPlain U x + (c_x : ENat) := by
        calc ((n - v_0 - 1 : ℕ) : ENat)
            ≤ ((Nat.bits N).length : ENat) := by exact_mod_cast hN_bits_lower
          _ ≤ KPPlain U x + (c_x : ENat) := hx_K_lower
      have h3 : n - v_0 - 1 ≤ logSlack c_E n + i + logSlack c_bits1 n + c_int + c_x :=
        sub_le_logSlack_add_of_intersection hE_K hxB_comp'
          (hbits_inter.trans hbits_n_slack') hKP_le h2
      have hslack_bound : logSlack (c_E + c_bits1) n + (c_int + c_x + 1) ≤ logSlack c0 n := by
        have h_add := logSlack_add_nat_le (c_E + c_bits1) (c_int + c_x + 1) n
        have hc0_1' : c_E + c_bits1 + (c_int + c_x + 1) ≤ c0 := by omega
        have h_mono := logSlack_mono_left hc0_1' n
        exact h_add.trans h_mono
      have h5 : n ≤ i + v_0 + logSlack c0 n := by
        have hle1 : n ≤ (logSlack c_E n + i + logSlack c_bits1 n + c_int + c_x) + v_0 + 1 := by
          omega
        have hle2 : logSlack c_E n + i + logSlack c_bits1 n + c_int + c_x + v_0 + 1 ≤
            i + v_0 + logSlack c0 n := by
          have h_sum : logSlack c_E n + i + logSlack c_bits1 n + c_int + c_x + v_0 + 1
              = i + v_0 + (logSlack (c_E + c_bits1) n + (c_int + c_x + 1)) := by
            dsimp [logSlack]; ring
          rw [h_sum]
          exact Nat.add_le_add_left hslack_bound (i + v_0)
        exact hle1.trans hle2
      exact h5
    omega
  · push_neg at hj_le
    have hmax : max j v_0 = j := max_eq_left (by omega)
    have hW : (E ∩ hammingBall n z r').card ≤
        n * ((n + 1) ^ 7 * (hammingBall n z r').card / hammingVol n (n / 64) + 1) :=
      hamming_list_decoding_intersection n (n / 64) N r' E z hE_is hz_len
    have hbits_bound := bits_intersection_bound n (hammingBall n z r').card (hammingVol n (n / 64))
      (E ∩ hammingBall n z r').card j v_0 hv_le hxB_card' hW
    have hbits_8_slack : (Nat.bits (8 * (n + 1) ^ 1)).length ≤ logSlack c_bits8 n := hc_bits8 n
    have hbits_8 : 8 * (Nat.bits (n + 1)).length ≤ logSlack (8 * c_bits8) n := by
      have h_le : (Nat.bits (n + 1)).length ≤ logSlack c_bits8 n := by
        have : n + 1 ≤ 8 * (n + 1) ^ 1 := by nlinarith
        have h_len_le := length_natBits_mono this
        exact h_len_le.trans hbits_8_slack
      calc 8 * (Nat.bits (n + 1)).length
          ≤ 8 * logSlack c_bits8 n := Nat.mul_le_mul_left 8 h_le
        _ = logSlack (8 * c_bits8) n := logSlack_nsmul 8 c_bits8 n
    have hcontra : n ≤ i + max j v_0 + logSlack c0 n := by
      rw [hmax]
      have h2 : ((n - v_0 - 1 : ℕ) : ENat) ≤ KPPlain U x + (c_x : ENat) := by
        calc ((n - v_0 - 1 : ℕ) : ENat)
            ≤ ((Nat.bits N).length : ENat) := by exact_mod_cast hN_bits_lower
          _ ≤ KPPlain U x + (c_x : ENat) := hx_K_lower
      have hbits : (Nat.bits (E ∩ hammingBall n z r').card).length ≤
          logSlack (8 * c_bits8) n + (j - v_0) + 1 :=
        hbits_bound.trans (Nat.add_le_add_right (Nat.add_le_add_right hbits_8 _) _)
      have h3 : n - v_0 - 1 ≤ logSlack c_E n + i +
          (logSlack (8 * c_bits8) n + (j - v_0) + 1) + c_int + c_x :=
        sub_le_logSlack_add_of_intersection hE_K hxB_comp' hbits hKP_le h2
      have hslack_bound : logSlack (c_E + 8 * c_bits8) n + (c_int + c_x + 2) ≤
          logSlack c0 n := by
        have h_add := logSlack_add_nat_le (c_E + 8 * c_bits8) (c_int + c_x + 2) n
        have hc0_8' : c_E + 8 * c_bits8 + (c_int + c_x + 2) ≤ c0 := by omega
        have h_mono := logSlack_mono_left hc0_8' n
        exact h_add.trans h_mono
      have h5 : n ≤ i + j + logSlack c0 n := by
        have hle1 : n ≤ (logSlack c_E n + i + (logSlack (8 * c_bits8) n + (j - v_0) + 1) +
            c_int + c_x) + v_0 + 1 := by omega
        have hle2 : logSlack c_E n + i + (logSlack (8 * c_bits8) n + (j - v_0) + 1) +
            c_int + c_x + v_0 + 1 ≤ i + j + logSlack c0 n := by
          have h_sum : logSlack c_E n + i + (logSlack (8 * c_bits8) n + (j - v_0) + 1) +
              c_int + c_x + v_0 + 1 = i + j + (logSlack (c_E + 8 * c_bits8) n +
              (c_int + c_x + 2)) := by
            dsimp [logSlack]
            rw [add_mul]
            omega
          rw [h_sum]
          exact Nat.add_le_add_left hslack_bound (i + j)
        exact hle1.trans hle2
      exact h5
    omega

/-- The logarithmic slack accumulated by the shift is again logarithmic in `n`, with the
constants made explicit. -/
lemma logSlack_shift_total_bound (c_shift c_shift_bound c_bits7 n j L : ℕ)
    (hn0 : 0 < n) (_hj : j < n)
    (hL : (Nat.bits n).length = L)
    (hc_bits7 : (Nat.bits (1 * (n + 1) ^ 7)).length ≤ logSlack c_bits7 n)
    (hc_shift_bound : ∀ M, logSlack c_shift (2 * M + 2) ≤ logSlack c_shift_bound M) :
    logSlack c_shift (n + (n - j) + (n + 1) ^ 7) ≤
      (c_shift_bound * c_bits7 + c_shift_bound) * L +
        c_shift_bound * c_bits7 + c_shift_bound := by
  have h_pow2_7 : (n + 1) ^ 2 ≤ (n + 1) ^ 7 := Nat.pow_le_pow_right (by omega) (by decide)
  have h2n : 2 * n ≤ (n + 1) ^ 7 := by
    calc 2 * n ≤ 2 * (n + 1) := by omega
      _ ≤ (n + 1) * (n + 1) := by nlinarith [hn0]
      _ = (n + 1) ^ 2 := by ring
      _ ≤ (n + 1) ^ 7 := h_pow2_7
  have h_nj : n + (n - j) ≤ 2 * n := by omega
  have hM : n + (n - j) + (n + 1) ^ 7 ≤ 2 * (n + 1) ^ 7 + 2 := by linarith [h_nj, h2n]
  have h_shift1 : logSlack c_shift (n + (n - j) + (n + 1) ^ 7) ≤
      logSlack c_shift_bound ((n + 1) ^ 7) :=
    (logSlack_mono hM).trans (hc_shift_bound ((n + 1) ^ 7))
  have h_bits7 : (Nat.bits ((n + 1) ^ 7)).length ≤ c_bits7 * L + c_bits7 := by
    have h_spec := hc_bits7
    have h1 : 1 * (n + 1) ^ 7 = (n + 1) ^ 7 := by ring
    rw [h1] at h_spec
    dsimp [logSlack] at h_spec
    rwa [hL] at h_spec
  have h_shift2 : logSlack c_shift_bound ((n + 1) ^ 7) ≤
      (c_shift_bound * c_bits7 + c_shift_bound) * L + c_shift_bound * c_bits7 + c_shift_bound := by
    dsimp [logSlack]
    nlinarith [h_bits7]
  exact h_shift1.trans h_shift2

/-- The `O(log)` facts about the full cube and about shifting a description down that the
Hamming-gap profile argument uses in the low-index regime: every string of length `n` has a
cube description of log-size `n` at complexity `logSlack c_cube n`; a description can be
shrunk by `k` at the cost of `k` plus a `logSlack c_shift` term; and the two slack terms
involved are bounded by `logSlack c_bits7` and `logSlack c_shift_bound`. -/
structure HammingShiftConstants (U : Map) (c_cube c_shift c_bits7 c_shift_bound : ℕ) : Prop where
  /-- The full cube is a description of log-size `n` at complexity `logSlack c_cube n`. -/
  cube : ∀ (𝒜 : DescriptionFamily) (x : BitString) (n : ℕ),
    x.length = n → InDescriptionProfileIn 𝒜 U x (logSlack c_cube n) n
  /-- A Hamming description can be shifted down by `k`. -/
  shift : ∀ (x : BitString) (n i j k : ℕ),
    x.length = n → k ≤ j → InDescriptionProfileIn hammingFamily U x i j →
      InDescriptionProfileIn hammingFamily U x
        (i + k + logSlack c_shift (n + k + hammingFamily.overhead n)) (j - k)
  /-- The overhead of `hammingFamily` costs at most `logSlack c_bits7` bits to name. -/
  bits7 : ∀ n, (Nat.bits (1 * (n + 1) ^ 7)).length ≤ logSlack c_bits7 n
  /-- The shift slack at doubled length is absorbed by `logSlack c_shift_bound`. -/
  shift_bound : ∀ M, logSlack c_shift (2 * M + 2) ≤ logSlack c_shift_bound M

/-- The explicit constant collecting all logarithmic slack terms of the Hamming-gap profile
argument. -/
def hammingGapProfileConst (c_E c_x c_cube c_shift c_sing c_int c_index c_add c_bits1 c_bits7
    c_bits8
    c_shift_bound : ℕ) : ℕ :=
  c_E + c_x + 2 * c_cube + c_shift + c_sing + c_int + c_index + c_add + c_bits1 + c_bits7 +
    8 * c_bits8 + c_shift_bound * c_bits7 + c_shift_bound + 100

/-- The three `O(1)` coding facts about the optimal prefix machine `U` that the Hamming-gap
profile argument uses: a singleton set costs the complexity of its element plus `O(log n)`;
an element of a uniformly coded set costs the index of the set plus a constant; and plain
prefix complexity is subadditive along a description, up to a constant. -/
structure PrefixCodingConstants (U : Map) (c_sing c_index c_add : ℕ) : Prop where
  /-- A singleton costs the complexity of its element plus `logSlack c_sing`. -/
  singleton_le : ∀ (x : BitString) (n kx : ℕ),
    x.length = n → KPPlain U x = (kx : ENat) →
      setComplexity U {x} (Finset.singleton_nonempty x) ≤ (kx + logSlack c_sing n : ENat)
  /-- An element of a uniformly coded set costs its index plus `c_index`. -/
  index_le : ∀ (S : Finset BitString) (hS : S.Nonempty) (x : BitString),
    x ∈ S → KP U x (codedUniformOn S hS).code ≤ (Nat.bits S.card).length + (c_index : ENat)
  /-- Prefix complexity is subadditive along a description, up to `c_add`. -/
  add_le : ∀ (x y : BitString), KPPlain U x ≤ KPPlain U y + KP U x y + (c_add : ENat)

/-- The witness set of the Hamming-gap construction: a nonempty Hamming list-decoding set `E`
for radius `n / 64` with at most `N` codewords, of set complexity at most `logSlack c_E n`,
containing the string `x`. -/
structure HammingGapWitnessSet (U : Map) (n N c_E : ℕ) (E : Finset BitString)
    (x : BitString) : Prop where
  /-- The set is nonempty. -/
  nonempty : E.Nonempty
  /-- It is a Hamming list-decoding set at radius `n / 64` with at most `N` codewords. -/
  is_list_decoding : IsHammingListDecodingSet n (n / 64) N E
  /-- Its set complexity is `O(log n)`. -/
  complexity_le : setComplexity U E nonempty ≤ (logSlack c_E n : ENat)
  /-- The string `x` belongs to it. -/
  mem : x ∈ E

/-- Profile inclusion for `hammingFamily` in the high complexity index regime (`n - v_0 ≤ i`),
where the singleton description `{x}` provides the required bound. -/
private lemma hammingGap_profile_inclusion_high_i (U : Map) (hU : IsOptimalPrefixConditional U)
    (n v_0 N c_E c_sing c_index c_add c0 : ℕ)
    (E : Finset BitString) (x : BitString)
    (hE : HammingGapWitnessSet U n N c_E E x)
    (hx_len : x.length = n) (hN_le : N ≤ 2 ^ (n - v_0))
    (hconst : PrefixCodingConstants U c_sing c_index c_add)
    (hc_sing_le : c_E + c_index + c_add + 1 + c_sing ≤ c0)
    (i j : ℕ) (hi_ge : n - v_0 ≤ i) :
    InDescriptionProfileIn hammingFamily U x (i + logSlack c0 n) (j + logSlack c0 n) := by
  obtain ⟨hE_ne, hE_is, hE_K, hx_in⟩ := hE
  obtain ⟨hc_sing, hc_index, hc_add⟩ := hconst
  have hx_sing : x ∈ ({x} : Finset BitString) := Finset.mem_singleton_self x
  have hne : ({x} : Finset BitString).Nonempty := Finset.singleton_nonempty x
  refine ⟨{x}, hne, hammingFamily.singleton_mem x, hx_sing, ?_, ?_⟩
  · have hN_bits : (Nat.bits N).length ≤ n - v_0 + 1 := by
      have hN_lt : N < 2 ^ (n - v_0 + 1) := by
        calc N ≤ 2 ^ (n - v_0) := hN_le
          _ < 2 ^ (n - v_0 + 1) := Nat.pow_lt_pow_right (by decide) (by omega)
      exact length_natBits_lt_pow hN_lt
    have hne_top : KPPlain U x ≠ ⊤ := KPPlain_ne_top_of_optimal U hU x
    have hKP_eq : KPPlain U x = ((KPPlain U x).toNat : ENat) :=
      (ENat.coe_toNat hne_top).symm
    have hset_sing := hc_sing x n (KPPlain U x).toNat hx_len hKP_eq
    have h_comp1 : KP U x (codedUniformOn E hE_ne).code ≤
        ((n - v_0 + 1 + c_index : ℕ) : ENat) := by
      have h_add_index := add_le_add
        (by exact_mod_cast hN_bits : ((Nat.bits N).length : ENat) ≤ ((n - v_0 + 1 : ℕ) : ENat))
        (le_refl (c_index : ENat))
      calc KP U x (codedUniformOn E hE_ne).code
          ≤ ((Nat.bits E.card).length : ENat) + (c_index : ENat) := hc_index E hE_ne x hx_in
        _ = ((Nat.bits N).length : ENat) + (c_index : ENat) := by rw [hE_is.2.1]
        _ ≤ ((n - v_0 + 1 : ℕ) : ENat) + (c_index : ENat) := h_add_index
    have h_comp2 : KPPlain U x ≤
        ((n - v_0) + logSlack (c_E + c_index + c_add + 1) n : ENat) := by
      have h_slack_le : logSlack c_E n + (n - v_0 + 1 + c_index) + c_add ≤
          (n - v_0) + logSlack (c_E + c_index + c_add + 1) n := by
        dsimp [logSlack]
        nlinarith
      have h_add1 := add_le_add hE_K h_comp1
      have h_add2 := add_le_add h_add1 (le_refl (c_add : ENat))
      calc KPPlain U x
          ≤ setComplexity U E hE_ne + KP U x (codedUniformOn E hE_ne).code + (c_add : ENat) :=
            hc_add x (codedUniformOn E hE_ne).code
        _ ≤ (logSlack c_E n : ENat) + ((n - v_0 + 1 + c_index : ℕ) : ENat) +
            (c_add : ENat) := h_add2
        _ = ((logSlack c_E n + (n - v_0 + 1 + c_index) + c_add : ℕ) : ENat) := by
            push_cast; ring
        _ ≤ ((n - v_0) + logSlack (c_E + c_index + c_add + 1) n : ENat) := by
            exact_mod_cast h_slack_le
    have h_comp3 : setComplexity U {x} hne ≤
        ((n - v_0) + logSlack (c_E + c_index + c_add + 1 + c_sing) n : ENat) := by
      have h_slack_eq : logSlack (c_E + c_index + c_add + 1) n + logSlack c_sing n =
          logSlack (c_E + c_index + c_add + 1 + c_sing) n :=
        logSlack_add_const (c_E + c_index + c_add + 1) c_sing n
      have h_add_slack : (n - v_0) + logSlack (c_E + c_index + c_add + 1) n +
          logSlack c_sing n = (n - v_0) + logSlack (c_E + c_index + c_add + 1 + c_sing) n := by
        rw [add_assoc, h_slack_eq]
      calc setComplexity U {x} hne
          ≤ ((KPPlain U x).toNat + logSlack c_sing n : ENat) := hset_sing
        _ = KPPlain U x + (logSlack c_sing n : ENat) := by rw [← hKP_eq]
        _ ≤ ((n - v_0) + logSlack (c_E + c_index + c_add + 1) n : ENat) +
            (logSlack c_sing n : ENat) :=
          add_le_add h_comp2 (le_refl (logSlack c_sing n : ENat))
        _ = (((n - v_0) + logSlack (c_E + c_index + c_add + 1) n +
            logSlack c_sing n : ℕ) : ENat) := by
            push_cast; rfl
        _ = (((n - v_0) + logSlack (c_E + c_index + c_add + 1 + c_sing) n :
            ℕ) : ENat) := by
            rw [h_add_slack]
        _ = (n - v_0 : ENat) + (logSlack (c_E + c_index + c_add + 1 + c_sing) n : ENat) := by
            push_cast; rfl
    calc setComplexity U {x} hne
        ≤ ((n - v_0) + logSlack (c_E + c_index + c_add + 1 + c_sing) n : ENat) := h_comp3
      _ ≤ i + (logSlack c0 n : ENat) := by
          have h_le2 : logSlack (c_E + c_index + c_add + 1 + c_sing) n ≤ logSlack c0 n :=
            logSlack_mono_left hc_sing_le n
          have h_le_sum : (n - v_0) + logSlack (c_E + c_index + c_add + 1 + c_sing) n ≤
              i + logSlack c0 n := Nat.add_le_add hi_ge h_le2
          exact_mod_cast h_le_sum
  · calc ({x} : Finset BitString).card = 1 := Finset.card_singleton x
      _ ≤ 2 ^ (j + logSlack c0 n) := Nat.one_le_pow _ _ (by decide)

/-- Profile inclusion for `hammingFamily` in the low complexity index regime (`i < n - v_0`),
where the description is obtained by shifting the full cube down to size `2 ^ j`. -/
private lemma hammingGap_profile_inclusion_low_i (U : Map)
    (n j i c_cube c_shift c_bits7 c_shift_bound c0 : ℕ) (hn0 : 0 < n)
    (x : BitString) (hx_len : x.length = n)
    (hconst : HammingShiftConstants U c_cube c_shift c_bits7 c_shift_bound)
    (hc_shift_le : c_cube + c_shift_bound * c_bits7 + c_shift_bound + c_cube ≤ c0)
    (hj_ge : j < n) (h_inj : n - j ≤ i) :
    InDescriptionProfileIn hammingFamily U x (i + logSlack c0 n) (j + logSlack c0 n) := by
  obtain ⟨hc_cube, hc_shift, hc_bits7, hc_shift_bound⟩ := hconst
  generalize hL : (Nat.bits n).length = L
  have hk_le : n - j ≤ n := by omega
  obtain ⟨S, hS, hmemS, hxS, hcompS, hcardS⟩ :=
    hc_shift x n (logSlack c_cube n) n (n - j) hx_len hk_le
      (hc_cube hammingFamily x n hx_len)
  have hsub_j : n - (n - j) = j := by omega
  rw [hsub_j] at hcardS
  have hoverhead : hammingFamily.overhead n = (n + 1) ^ 7 := rfl
  set K := logSlack c_shift (n + (n - j) + hammingFamily.overhead n)
  have hK : logSlack c_shift (n + (n - j) + hammingFamily.overhead n) = K := rfl
  have h_shift_tot : K ≤ (c_shift_bound * c_bits7 + c_shift_bound) * L +
      c_shift_bound * c_bits7 + c_shift_bound := by
    rw [← hK, hoverhead]
    exact logSlack_shift_total_bound c_shift c_shift_bound c_bits7 n j L
      hn0 hj_ge hL (hc_bits7 n) hc_shift_bound
  have hn_bits_pos : 1 ≤ L := by rw [← hL]; exact length_natBits_mono hn0
  have hslack_bound_L : c_cube * L + c_cube + (n - j) + K ≤ i + (c0 * L + c0) := by
    nlinarith [h_inj, h_shift_tot, hc_shift_le, hn_bits_pos]
  have h_final : setComplexity U S hS ≤ (i : ENat) + (logSlack c0 n : ENat) := by
    have h_cast : ((logSlack c_cube n + (n - j) + K : ℕ) : ENat) ≤
        ((i + logSlack c0 n : ℕ) : ENat) := by
      dsimp only [logSlack]
      rw [hL]
      exact Nat.cast_le.mpr hslack_bound_L
    refine hcompS.trans (h_cast.trans ?_)
    push_cast
    rfl
  refine ⟨S, hS, hmemS, hxS, h_final, ?_⟩
  · calc S.card ≤ 2 ^ j := hcardS
      _ ≤ 2 ^ (j + logSlack c0 n) := Nat.pow_le_pow_right (by decide) (by omega)

/-- Every profile point `(i, j)` with `n ≤ i + max j v_0` lies in the description profile
of `x` for `hammingFamily`, with the single slack constant `c0`.

The hypotheses `hc_cube`, `hc_shift`, `hc_sing`, `hc_index`, `hc_add`, `hc_bits7` and
`hc_shift_bound` are interface assumptions about an arbitrary optimal conditional prefix
machine `U`: each is one machine-invariance estimate carrying its own named constant. -/
private lemma hammingGap_profile_inclusion (U : Map) (hU : IsOptimalPrefixConditional U)
    (n v_0 N c_E _c_x c_cube c_shift c_sing c_index c_add c_bits7 c_shift_bound c0 : ℕ)
    (hn0 : 0 < n)
    (E : Finset BitString) (hE_ne : E.Nonempty) (hE_is : IsHammingListDecodingSet n (n / 64) N E)
    (hE_K : setComplexity U E hE_ne ≤ (logSlack c_E n : ENat))
    (x : BitString) (hx_in : x ∈ E) (hx_len : x.length = n)
    (hN_le : N ≤ 2 ^ (n - v_0))
    (hc_cube : ∀ (𝒜 : DescriptionFamily) (x : BitString) (n : ℕ),
      x.length = n → InDescriptionProfileIn 𝒜 U x (logSlack c_cube n) n)
    (hc_shift : ∀ (x : BitString) (n i j k : ℕ),
      x.length = n → k ≤ j → InDescriptionProfileIn hammingFamily U x i j →
        InDescriptionProfileIn hammingFamily U x
          (i + k + logSlack c_shift (n + k + hammingFamily.overhead n)) (j - k))
    (hc_sing : ∀ (x : BitString) (n kx : ℕ),
      x.length = n → KPPlain U x = (kx : ENat) →
        setComplexity U {x} (Finset.singleton_nonempty x) ≤ (kx + logSlack c_sing n : ENat))
    (hc_index : ∀ (S : Finset BitString) (hS : S.Nonempty) (x : BitString),
      x ∈ S → KP U x (codedUniformOn S hS).code ≤ (Nat.bits S.card).length + (c_index : ENat))
    (hc_add : ∀ (x y : BitString), KPPlain U x ≤ KPPlain U y + KP U x y + (c_add : ENat))
    (hc_bits7 : ∀ n, (Nat.bits (1 * (n + 1) ^ 7)).length ≤ logSlack c_bits7 n)
    (hc_shift_bound : ∀ M, logSlack c_shift (2 * M + 2) ≤ logSlack c_shift_bound M)
    (hc_cube_le : c_cube ≤ c0)
    (hc_sing_le : c_E + c_index + c_add + 1 + c_sing ≤ c0)
    (hc_shift_le : c_cube + c_shift_bound * c_bits7 + c_shift_bound + c_cube ≤ c0) :
    ∀ i j : ℕ, n ≤ i + max j v_0 →
      InDescriptionProfileIn hammingFamily U x (i + logSlack c0 n) (j + logSlack c0 n) := by
  intro i j hij
  by_cases hj_ge : n ≤ j
  · obtain ⟨S_cube, hS_cube_ne, hS_cube_mem, hx_cube, hS_cube_comp, hS_cube_card⟩ :=
      hc_cube hammingFamily x n hx_len
    refine ⟨S_cube, hS_cube_ne, hS_cube_mem, hx_cube, ?_, ?_⟩
    · calc setComplexity U S_cube hS_cube_ne
          ≤ (logSlack c_cube n : ENat) := hS_cube_comp
        _ = ((c_cube * (Nat.bits n).length + c_cube : ℕ) : ENat) := rfl
        _ ≤ ((c0 * (Nat.bits n).length + c0 : ℕ) : ENat) := by
            exact_mod_cast Nat.add_le_add (Nat.mul_le_mul_right _ hc_cube_le) hc_cube_le
        _ = (logSlack c0 n : ENat) := rfl
        _ ≤ (i : ENat) + (logSlack c0 n : ENat) := self_le_add_left (logSlack c0 n : ENat) i
    · calc S_cube.card ≤ 2 ^ n := hS_cube_card
        _ ≤ 2 ^ (j + logSlack c0 n) := Nat.pow_le_pow_right (by decide) (by omega)
  · push_neg at hj_ge
    by_cases hi_ge : n - v_0 ≤ i
    · exact hammingGap_profile_inclusion_high_i U hU n v_0 N c_E c_sing c_index c_add c0
        E x ⟨hE_ne, hE_is, hE_K, hx_in⟩ hx_len hN_le ⟨hc_sing, hc_index, hc_add⟩
        hc_sing_le i j hi_ge
    · push_neg at hi_ge
      have hmax : max j v_0 = j := by
        by_cases hjv : j ≤ v_0
        · have h_max_v : max j v_0 = v_0 := max_eq_right hjv
          have h_sum : n ≤ i + v_0 := by rw [h_max_v] at hij; exact hij
          omega
        · exact max_eq_left (by omega)
      have h_inj : n - j ≤ i := by
        have h_sum : n ≤ i + j := by rw [hmax] at hij; exact hij
        omega
      exact hammingGap_profile_inclusion_low_i U n j i c_cube c_shift c_bits7 c_shift_bound c0
        hn0 x hx_len ⟨hc_cube, hc_shift, hc_bits7, hc_shift_bound⟩ hc_shift_le hj_ge h_inj

/-- **Exercise 359.** The restricted profile `P_x^𝒜` of the string produced by
the Hamming-ball gap construction (Exercise 358, `prop_hamming_gap`): its
boundary consists of the vertical segment at complexity `n - log V` below
log-size `log V`, and of the slope `-1` segment `i + j = n` above it.  The last
clause records that `x` does have an unrestricted `(O(log n), n - log V)`
description, which is what makes the restricted profile strictly smaller. -/
theorem hammingGap_restricted_profile (U : Map)
    (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ n ≥ c, ∃ x : BitString, x.length = n ∧
      (∀ i j : ℕ, n ≤ i + max j (Nat.log 2 (hammingVol n (n / 64))) →
        InDescriptionProfileIn hammingFamily U x (i + logSlack c n) (j + logSlack c n)) ∧
      (∀ i j : ℕ, i + max j (Nat.log 2 (hammingVol n (n / 64))) + logSlack c n < n →
        ¬ InDescriptionProfileIn hammingFamily U x i j) ∧
      InDescriptionProfile U x (logSlack c n) (n - Nat.log 2 (hammingVol n (n / 64))) := by
  obtain ⟨c_E, hc_E⟩ := exists_list_decoding_set_low_complexity U hU
  obtain ⟨c_x, hc_x⟩ := exists_high_complexity_element_in_finset U hU
  obtain ⟨c_cube, hc_cube⟩ := inDescriptionProfileIn_fullCube_of_optimal U hU
  obtain ⟨c_shift, hc_shift⟩ := inDescriptionProfileIn_cover_shift U hU hammingFamily
  obtain ⟨c_sing, hc_sing⟩ := singletonSetComplexityGate U hU
  obtain ⟨c_int, hc_int⟩ := KPPlain_le_intersection U hU
  obtain ⟨c_index, hc_index⟩ := KP_le_log_card_given_setCode U hU
  obtain ⟨c_add, hc_add⟩ := KPPlain_le_KPPlain_add_KP U hU
  obtain ⟨c_bits1, hc_bits1⟩ := polynomialOverhead_bits_le_logSlack 1 1 (by norm_num)
  obtain ⟨c_bits7, hc_bits7⟩ := polynomialOverhead_bits_le_logSlack 1 7 (by norm_num)
  obtain ⟨c_bits8, hc_bits8⟩ := polynomialOverhead_bits_le_logSlack 8 1 (by norm_num)
  obtain ⟨c_shift_bound, hc_shift_bound⟩ := logSlack_linear_bound c_shift 2 2
  set c0 := hammingGapProfileConst c_E c_x c_cube c_shift c_sing c_int c_index c_add c_bits1
    c_bits7 c_bits8
    c_shift_bound
  have hc0_1 : c_E + c_bits1 + c_int + c_x + 1 ≤ c0 := by dsimp [c0, hammingGapProfileConst]; omega
  have hc0_8 : c_E + 8 * c_bits8 + c_int + c_x + 2 ≤ c0 := by
    dsimp [c0, hammingGapProfileConst]; omega
  have hc_E_le : c_E ≤ c0 := by dsimp [c0, hammingGapProfileConst]; omega
  have hc_cube_le : c_cube ≤ c0 := by dsimp [c0, hammingGapProfileConst]; omega
  have hc_sing_le : c_E + c_index + c_add + 1 + c_sing ≤ c0 := by
    dsimp [c0, hammingGapProfileConst]; omega
  have hc_shift_le : c_cube + c_shift_bound * c_bits7 + c_shift_bound + c_cube ≤ c0 := by
    dsimp [c0, hammingGapProfileConst]; omega
  refine ⟨c0, fun n hn => ?_⟩
  set r := n / 64
  set V := hammingVol n r
  set v_0 := Nat.log 2 V
  set N := 2 ^ n / V
  have hn_pos : 0 < n := by omega
  have hV_pos : 0 < V := hammingVol_pos n r
  have hN_eq : N = 2 ^ n / hammingVol n r := rfl
  have hr_eq : r = n / 64 := rfl
  have hE_exists := exists_list_decoding_set n r N hn_pos hN_eq
  obtain ⟨E, hE_ne, hE_is, hE_K⟩ := hc_E n r N hr_eq hN_eq hE_exists
  obtain ⟨x, hx_in, hx_K⟩ := hc_x E hE_ne
  have hx_len : x.length = n := hE_is.1 x hx_in
  have hv_le : 2 ^ v_0 ≤ V := Nat.pow_log_le_self 2 hV_pos.ne'
  have hv_lt : V < 2 ^ (v_0 + 1) := Nat.lt_pow_succ_log_self (by decide) V
  have hN_le : N ≤ 2 ^ (n - v_0) := bits_length_bound_of_div n v_0 hv_le
  have hN_ge : 2 ^ (n - v_0 - 1) ≤ N := bits_length_lower_bound_of_div n v_0 hv_lt
  refine ⟨x, hx_len, ?_, ?_, ?_⟩
  · exact hammingGap_profile_inclusion U hU n v_0 N c_E c_x c_cube c_shift c_sing c_index c_add
      c_bits7 c_shift_bound c0 hn_pos E hE_ne hE_is hE_K x hx_in hx_len hN_le hc_cube hc_shift
      hc_sing hc_index hc_add hc_bits7 hc_shift_bound hc_cube_le hc_sing_le hc_shift_le
  · exact hammingGap_profile_exclusion U hU n v_0 N c_E c_x c_int c_bits1 c_bits8 c0 E hE_ne
      hE_is hE_K x hx_in hx_len hx_K hv_le hN_ge hc_int hc_bits1 hc_bits8 hc0_1 hc0_8
  · exact hammingSet_inDescriptionProfile U n v_0 N c_E c0 E hE_ne hE_is hE_K x hx_in hN_le hc_E_le

/-- `C_r(x)`: the minimal plain complexity of a string of the same length that
differs from `x` in at most `r` positions. -/
noncomputable def approxComplexity (V : Map) (x : BitString) (r : ℕ) : ℕ∞ :=
  ⨅ y ∈ {y : BitString | y.length = x.length ∧ hammingDist x y ≤ r}, plainK V y

/-- The minimal complexity coordinate `i` for which `x` has an
`(i * log V(r))`-description that is a Hamming ball. -/
noncomputable def hammingBallProfileMin (U : Map) (x : BitString) (n r : ℕ) : ℕ∞ :=
  ⨅ i ∈ {i : ℕ | InDescriptionProfileIn hammingFamily U x i
      (Nat.log 2 (hammingVol n r))}, (i : ℕ∞)

-- `exercise361_approxComplexity_eq_hammingBallProfileMin` (ch14-exercise-361) is archived; see
-- `docs/ARCHIVED_TARGETS.md`.

-- `exercise361_approxComplexity_shape` (ch14-exercise-361) is archived; see
-- `docs/ARCHIVED_TARGETS.md`.

-- `exercise361_approxComplexity_realization` (ch14-exercise-361) is archived; see
-- `docs/ARCHIVED_TARGETS.md`.

end Kolmogorov
