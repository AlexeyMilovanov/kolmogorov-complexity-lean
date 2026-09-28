import KolmogorovMathlib.Interface.ComputableReals
import KolmogorovMathlib.Interface.Dovetailing
import KolmogorovMathlib.Complexity.PairComplexity
import KolmogorovMathlib.Complexity.ConditionalComplexity
import KolmogorovMathlib.Complexity.KolmogorovLevin
import KolmogorovMathlib.Complexity.RandomConditions
import KolmogorovMathlib.Complexity.SelfComplexity
import KolmogorovMathlib.Complexity.InfiniteSequences
import KolmogorovMathlib.Complexity.IncompressibleStrings
import KolmogorovMathlib.Complexity.Information
import KolmogorovMathlib.Complexity.Incompressibility
import KolmogorovMathlib.AlgorithmicProbability.UniversalSemimeasure
import KolmogorovMathlib.AlgorithmicProbability.PairProjection
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitinAllocator
import KolmogorovMathlib.Prefix.ConditionalSymmetry
import KolmogorovMathlib.Prefix.TotalCountingBound
import KolmogorovMathlib.Prefix.KPPairSwap
import KolmogorovMathlib.Prefix.TwoStage
import KolmogorovMathlib.Prefix.CondTwoStage
import KolmogorovMathlib.Foundation.PrimrecExtras
import KolmogorovMathlib.Prefix.Properties
import KolmogorovMathlib.AlgorithmicStatistics.Selector
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Rat.Denumerable
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Partrec
import Mathlib.Computability.Halting
import KolmogorovMathlib.MonotoneComplexity.Omega.SolovayInverse.Inequality

/-!
# Solovay's inequality, plain against prefix complexity

The inequality `C(x) ≤ K(x) - K(K(x))` up to an additive constant
(`solovay_plain_le_prefix_sub_prefix_prefix`), the converse direction of Solovay's theorem
proved in `MonotoneComplexity.Omega.SolovayInverse.Core`.

SUV Theorem 72, p. 148.
-/

namespace Kolmogorov
open scoped ENNReal
open Nat.Partrec (Code)
open Kolmogorov.ComputableReals

/-- `3 * m < 2 ^ (m - 1)` for `m ≥ 5`. -/
private lemma three_mul_lt_two_pow_sub_one (m : ℕ) (hm : 5 ≤ m) : 3 * m < 2 ^ (m - 1) := by
  induction m with
  | zero => omega
  | succ m ih =>
    by_cases hm5 : m < 5
    · have : m = 4 := by omega
      subst this
      decide
    · have hm' : 5 ≤ m := by omega
      have h_prev := ih hm'
      have h_eq : m + 1 - 1 = m := by omega
      have h_eq2 : m - 1 + 1 = m := by omega
      rw [h_eq, ← h_eq2, pow_succ]
      omega

/-- Bound on `kn` when `n < kn` and `kn ≤ 2 * (natBits n).length + c_two`. -/
private lemma kVal_le_three_mul_add_of_lt (n kn c_two : ℕ)
    (h_kn_le : (kn : ENat) ≤ 2 * (natBits n).length + (c_two : ENat))
    (h_lt : n < kn) : kn ≤ 3 * c_two + 8 := by
  have h_kn_le' : kn ≤ 2 * (natBits n).length + c_two := by exact_mod_cast h_kn_le
  have h_bits_len : (natBits n).length = (Nat.bits n).length := rfl
  rw [h_bits_len] at h_kn_le'
  have h_bound_n : n < 2 * (Nat.bits n).length + c_two := Nat.lt_of_lt_of_le h_lt h_kn_le'
  have h_bits_lt : (Nat.bits n).length ≤ c_two + 4 := by
    by_contra hc
    have hc' : c_two + 4 < (Nat.bits n).length := Nat.lt_of_not_ge hc
    set L := (Nat.bits n).length
    have hL_ge : 5 ≤ L := by omega
    have h_pow_L := three_mul_lt_two_pow_sub_one L hL_ge
    have hL_size : L = Nat.size n := Nat.size_eq_bits_len n
    have h_pow_lower : 2 ^ (L - 1) ≤ n := Nat.lt_size.mp (by rw [← hL_size]; omega)
    omega
  omega

/-- Membership of `x` in `solovayMap cU c₆₄ (v ++ u, [])` when `v` produces `natBits kn`
and `u` encodes index `k` in the snapshot codes. -/
private lemma mem_solovayMap_of_snapshot (U : Map) (hU : IsOptimalPrefixConditional U)
    (cU : Code) (hcU : IsCodeFor cU U) (c₆₄ : ℕ)
    (v u : BitString) (T_max kn n k : ℕ) (x : BitString)
    (hv_prod : produces U v [] (natBits kn))
    (hv_eval_max : runOut cU T_max v = some (natBits kn))
    (hle : kn ≤ n)
    (hu_len : u.length = n - kn + c₆₄)
    (hu_nat : bitsToNat u = k)
    (hk_lt_len : k < (cumSnapshotCodes cU (n, T_max)).length)
    (hx_getD : (cumSnapshotCodes cU (n, T_max)).getD k [] = x) :
    x ∈ solovayMap cU c₆₄ (v ++ u, []) := by
  set w := v ++ u
  have hcheck_max : (solovayCheck cU c₆₄ w (Nat.pair v.length T_max)).isSome = true :=
    solovayCheck_max_isSome cU c₆₄ v u T_max kn n k hv_eval_max hle hu_len hu_nat hk_lt_len
  have hrfind_dom :
      (Nat.rfind (fun m => Part.some (solovayCheck cU c₆₄ w m).isSome)).Dom :=
    ⟨Nat.pair v.length T_max, Part.mem_some_iff.mpr hcheck_max.symm, fun _ _ => Part.some_dom _⟩
  obtain ⟨m_found, hm_found_mem⟩ := Part.dom_iff_mem.mp hrfind_dom
  have hcheck_found : (solovayCheck cU c₆₄ w m_found).isSome = true :=
    (Part.mem_some_iff.mp (Nat.mem_rfind.mp hm_found_mem).1).symm
  have hcond_found : solovayCond cU c₆₄ w m_found = true := by
    by_cases hc : solovayCond cU c₆₄ w m_found = true
    · exact hc
    · unfold solovayCheck at hcheck_found
      rw [Bool.not_eq_true] at hc
      rw [hc] at hcheck_found
      contradiction
  have hout_found : (solovayOut cU w m_found).isSome = true := by
    by_cases ho : (solovayOut cU w m_found).isSome = true
    · exact ho
    · unfold solovayCond at hcond_found
      rw [Bool.not_eq_true] at ho
      rw [ho] at hcond_found
      contradiction
  have hrun_found : ∃ y, runOut cU m_found.unpair.2 (w.take m_found.unpair.1) = some y :=
    Option.isSome_iff_exists.mp hout_found
  obtain ⟨y_found, hy_run_found⟩ := hrun_found
  have hprod_found := runOut_sound hcU hy_run_found
  have hpref_found : w.take m_found.unpair.1 <+: w := List.take_prefix _ _
  have hpref_v : v <+: w := ⟨u, rfl⟩
  have h_prefix_or : (w.take m_found.unpair.1) <+: v ∨ v <+: (w.take m_found.unpair.1) :=
    List.prefix_or_prefix_of_prefix hpref_found hpref_v
  have h_eq_v : w.take m_found.unpair.1 = v := by
    cases h_prefix_or with
    | inl hp1 => exact IsPrefixMachine.eq_of_prefix hU.1.2 hprod_found hv_prod hp1
    | inr hp2 => exact (IsPrefixMachine.eq_of_prefix hU.1.2 hv_prod hprod_found hp2).symm
  have h_drop_u : w.drop m_found.unpair.1 = u := by
    have h_app1 : w = (w.take m_found.unpair.1) ++ (w.drop m_found.unpair.1) :=
      (List.take_append_drop _ _).symm
    rw [h_eq_v] at h_app1
    have h_app2 : w = v ++ u := rfl
    rw [h_app1] at h_app2
    exact List.append_cancel_left h_app2
  have hdrop_len : (w.drop m_found.unpair.1).length = n - kn + c₆₄ := by
    rw [h_drop_u, hu_len]
  have h_u_nat : bitsToNat (w.drop m_found.unpair.1) = k := by
    rw [h_drop_u, hu_nat]
  have h_y_eq : y_found = natBits kn := by
    have hy1 : runOut cU m_found.unpair.2 v = some y_found := by
      rwa [h_eq_v] at hy_run_found
    set T_both := max m_found.unpair.2 T_max
    have hy_both : runOut cU T_both v = some y_found :=
      runOut_mono (le_max_left _ _) hy1
    have hkn_both : runOut cU T_both v = some (natBits kn) :=
      runOut_mono (le_max_right _ _) hv_eval_max
    rw [hy_both] at hkn_both
    exact Option.some_inj.mp hkn_both
  have hkn_eq : solovayKN cU (w, m_found) = kn := by
    dsimp [solovayKN, solovayOutStr, solovayOut]
    rw [h_eq_v]
    have hy1 : runOut cU m_found.unpair.2 v = some y_found := by
      rwa [h_eq_v] at hy_run_found
    rw [hy1]
    dsimp
    rw [h_y_eq]
    exact decodeBits_natBits kn
  have h_sol_N : solovayN cU c₆₄ (w, m_found) = n := by
    dsimp [solovayN]
    rw [hdrop_len, hkn_eq]
    omega
  have h_sol_codes : solovayCodes cU c₆₄ (w, m_found) =
      cumSnapshotCodes cU (n, m_found.unpair.2) := by
    dsimp [solovayCodes]
    rw [h_sol_N]
  have h_sol_val : solovayVal cU c₆₄ w m_found = x := by
    change (solovayCodes cU c₆₄ (w, m_found)).getD (bitsToNat (w.drop m_found.unpair.1)) [] = x
    rw [h_sol_codes, h_u_nat]
    have h_prefix_cum :
        cumSnapshotCodes cU (n, T_max) <+: cumSnapshotCodes cU (n, m_found.unpair.2) ∨
        cumSnapshotCodes cU (n, m_found.unpair.2) <+: cumSnapshotCodes cU (n, T_max) := by
      by_cases hT : T_max ≤ m_found.unpair.2
      · left; exact cumSnapshotCodes_prefix_of_le cU n hT
      · right; exact cumSnapshotCodes_prefix_of_le cU n (le_of_not_ge hT)
    cases h_prefix_cum with
    | inl hp1_pref =>
      have h_lt_cum : k < (cumSnapshotCodes cU (n, m_found.unpair.2)).length :=
        hk_lt_len.trans_le hp1_pref.length_le
      rw [← getD_eq_of_prefix_common hp1_pref (List.prefix_refl _) hk_lt_len h_lt_cum]
      exact hx_getD
    | inr hp2_pref =>
      have h_lt_cum : k < (cumSnapshotCodes cU (n, m_found.unpair.2)).length := by
        have h_lt_codes := solovayCond_lt_length cU c₆₄ w m_found hcond_found hout_found
        rwa [h_sol_codes, h_u_nat] at h_lt_codes
      rw [getD_eq_of_prefix_common hp2_pref (List.prefix_refl _) h_lt_cum hk_lt_len]
      exact hx_getD
  have h_sol_check : solovayCheck cU c₆₄ w m_found = some x := by
    unfold solovayCheck
    rw [hcond_found, h_sol_val]
    rfl
  unfold solovayMap
  rw [Part.mem_bind_iff]
  refine ⟨m_found, hm_found_mem, ?_⟩
  rw [Part.mem_ofOption, h_sol_check]
  rfl

/-- **Exercise 117.** The direct form of the Solovay inequality
`C(x) ≤ K(x) - K(K(x)) + K⁽³⁾(x) + O(1)`. -/
theorem solovay_plain_le_prefix_sub_prefix_prefix (U V : Map)
    (hU : IsOptimalPrefixConditional U) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ x : BitString,
      (cVal V x : ℤ) ≤ (kVal U x : ℤ) - (kNatVal U (kVal U x) : ℤ)
        + (kNatVal U (kNatVal U (kVal U x)) : ℤ) + (c : ℤ) := by
  obtain ⟨cU, hcU⟩ : ∃ cU : Code, IsCodeFor cU U :=
    Nat.Partrec.Code.exists_code.mp hU.isDecompressor
  obtain ⟨c₆₄, hc₆₄⟩ := card_KPPlain_le_upper_bound U hU
  have hsol_decomp : isDecompressor (solovayMap cU c₆₄) := solovayMap_isDecompressor cU c₆₄
  obtain ⟨cV, hcV⟩ := hV.2 (solovayMap cU c₆₄) hsol_decomp
  obtain ⟨c_plain, hc_plain⟩ := plain_le_prefix V U hV hU.isPrefixDecompressor
  obtain ⟨c_two, hc_two⟩ := KPPlain_le_two_mul_length U hU
  refine ⟨c₆₄ + cV + c_plain + 3 * c_two + 12, fun x => ?_⟩
  set n := kVal U x
  set kn := kNatVal U n
  set kkn := kNatVal U kn
  have htop_x : KPPlain U x ≠ ⊤ := KPPlain_ne_top_of_optimal U hU x
  have htop_n : KPPlain U (natBits n) ≠ ⊤ := KPPlain_ne_top_of_optimal U hU (natBits n)
  have htop_kn : KPPlain U (natBits kn) ≠ ⊤ := KPPlain_ne_top_of_optimal U hU (natBits kn)
  obtain ⟨v, hv_prod, hv_len⟩ :=
    exists_program_of_KP_ne_top (M := U) (x := natBits kn) (y := []) htop_kn
  have hv_len_eq : v.length = kkn := by
    dsimp [kkn, kNatVal, kNat, programLength] at hv_len ⊢
    have h_toNat := congr_arg ENat.toNat hv_len
    rwa [ENat.toNat_coe] at h_toNat
  obtain ⟨Tv, hTv_eval⟩ := (produces_iff_evaln cU hcU v (natBits kn) []).mp hv_prod
  have hTv_runOut : runOut cU Tv v = some (natBits kn) := by
    unfold runOut
    rw [hTv_eval]
    dsimp
    exact Encodable.encodek (natBits kn)
  obtain ⟨px, hpx_prod, hpx_len⟩ :=
    exists_program_of_KP_ne_top (M := U) (x := x) (y := []) htop_x
  have hpx_len_eq : px.length = n := by
    dsimp [n, kVal, programLength] at hpx_len ⊢
    have h_toNat := congr_arg ENat.toNat hpx_len
    rwa [ENat.toNat_coe] at h_toNat
  obtain ⟨Tx, hTx_eval⟩ := (produces_iff_evaln cU hcU px x []).mp hpx_prod
  have hTx_runOut : runOut cU Tx px = some x := by
    unfold runOut
    rw [hTx_eval]
    dsimp
    exact Encodable.encodek x
  set T_max := max Tv Tx
  have hv_eval_max : runOut cU T_max v = some (natBits kn) :=
    runOut_mono (le_max_left Tv Tx) hTv_runOut
  have hpx_eval_max : runOut cU T_max px = some x :=
    runOut_mono (le_max_right Tv Tx) hTx_runOut
  have hpx_mem_bounded : px ∈ boundedPrograms n := by
    rw [mem_boundedPrograms_iff, hpx_len_eq]
  have hx_mem_snap : x ∈ snapshotCodes cU n T_max := by
    unfold snapshotCodes
    rw [List.mem_filterMap]
    refine ⟨px, hpx_mem_bounded, hpx_eval_max⟩
  have hx_mem_cum : x ∈ cumSnapshotCodes cU (n, T_max) := by
    dsimp [cumSnapshotCodes]
    rw [mem_eraseDups_bitString, List.mem_flatMap]
    exact ⟨T_max, List.mem_range.mpr (Nat.lt_succ_self T_max), hx_mem_snap⟩
  set A := (cumSnapshotCodes cU (n, T_max)).toFinset
  have hx_in_A : x ∈ A := List.mem_toFinset.mpr hx_mem_cum
  set k := (cumSnapshotCodes cU (n, T_max)).idxOf x
  have hk_lt_len : k < (cumSnapshotCodes cU (n, T_max)).length :=
    List.idxOf_lt_length_of_mem hx_mem_cum
  have hx_getD : (cumSnapshotCodes cU (n, T_max)).getD k [] = x := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_idxOf hx_mem_cum, Option.getD_some]
  have hA_sub : ∀ y ∈ A, KPPlain U y ≤ (n : ENat) := by
    intro y hy
    rw [List.mem_toFinset] at hy
    exact KPPlain_le_of_mem_cumSnapshotCodes hcU hy
  have hkn_val : HasPrefixComplexityValue U n.bits kn := kNatVal_hasPrefixComplexityValue U hU n
  have hbound := hc₆₄ n kn hkn_val A hA_sub
  have hA_card_le := card_le_of_ennreal_bound hbound
  have hk_lt_pow : k < 2 ^ (n - kn + c₆₄) := by
    have h1 : k < A.card := by
      have h_nodup : (cumSnapshotCodes cU (n, T_max)).Nodup :=
        nodup_eraseDups_bitString _
      rw [List.toFinset_card_of_nodup h_nodup]
      exact hk_lt_len
    exact h1.trans_le hA_card_le
  by_cases hle : kn ≤ n
  · set u := ShortDescriptions.padBits k (n - kn + c₆₄)
    have hu_bits_len : (Nat.bits k).length ≤ n - kn + c₆₄ :=
      length_natBits_lt_pow hk_lt_pow
    have hu_len : u.length = n - kn + c₆₄ := length_padBits hu_bits_len
    have hu_nat : bitsToNat u = k := bitsToNat_padBits hu_bits_len
    set w := v ++ u
    have h_sol_map_mem : x ∈ solovayMap cU c₆₄ (w, []) :=
      mem_solovayMap_of_snapshot U hU cU hcU c₆₄ v u T_max kn n k x
        hv_prod hv_eval_max hle hu_len hu_nat hk_lt_len hx_getD
    have hcondK_sol : condK (solovayMap cU c₆₄) x [] ≤ (w.length : ENat) :=
      KP_le_programLength_of_produces h_sol_map_mem
    have hplainK_V : plainK V x ≤ (w.length : ENat) + (cV : ENat) :=
      le_trans (hcV x []) (add_le_add hcondK_sol le_rfl)
    have hw_len : w.length = kkn + n - kn + c₆₄ := by
      dsimp [w]
      rw [List.length_append, hv_len_eq, hu_len]
      omega
    have hcVal_le : cVal V x ≤ kkn + n - kn + c₆₄ + cV := by
      dsimp [cVal]
      have h1 : plainK V x ≤ ((kkn + n - kn + c₆₄ + cV : ℕ) : ENat) := by
        rw [hw_len] at hplainK_V
        exact hplainK_V
      have h2 := ENat.toNat_le_toNat h1 (ENat.coe_ne_top _)
      rwa [ENat.toNat_coe] at h2
    zify at hcVal_le ⊢
    omega
  · have hcVal_le : cVal V x ≤ n + c_plain := by
      dsimp [cVal]
      have h_plain := hc_plain x
      have h_KPPlain_eq : KPPlain U x = (n : ENat) := (kVal_eq_coe U hU x).symm
      have h1 : plainK V x ≤ ((n + c_plain : ℕ) : ENat) := by
        have h_sum : (n : ENat) + (c_plain : ENat) = ((n + c_plain : ℕ) : ENat) := by push_cast; rfl
        rw [← h_sum, ← h_KPPlain_eq]
        exact h_plain
      have h2 := ENat.toNat_le_toNat h1 (ENat.coe_ne_top _)
      rwa [ENat.toNat_coe] at h2
    have h_two := hc_two (natBits n)
    have h_kn_eq : (kn : ENat) = KPPlain U (natBits n) := hkn_val
    have h_two_nat : (kn : ENat) ≤ 2 * (natBits n).length + (c_two : ENat) := h_kn_eq.symm ▸ h_two
    have h_not_le : n < kn := Nat.lt_of_not_ge hle
    have h_kn_small := kVal_le_three_mul_add_of_lt n kn c_two h_two_nat h_not_le
    zify at hcVal_le ⊢
    linarith

end Kolmogorov
