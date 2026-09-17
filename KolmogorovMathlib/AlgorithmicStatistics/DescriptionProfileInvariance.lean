/-
Copyright (c) 2026 Alexey Milovanov. All rights reserved.
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
import KolmogorovMathlib.AlgorithmicStatistics.DeficiencyValue
import KolmogorovMathlib.AlgorithmicStatistics.NonStochasticMassWeak
import KolmogorovMathlib.AlgorithmicStatistics.StochasticityProfile

/-!
# Invariance of the description profile under a simple bijection

If `x` and `y` correspond under a bijection computed by a program of complexity
at most `t`, their description profiles agree up to an `O(t)` shift of the
complexity coordinate.

SUV Exercise 354, p. 495.
-/

namespace Kolmogorov
open scoped ENNReal
open Nat.Partrec (Code)
open CodedFiniteDistribution
open Kolmogorov.CodedFiniteDistribution

/-- There exists a common fuel value for `bijectionEvalFuel` given a list of strings whose
evaluations under code `e` terminate with output `pi w`. -/
private theorem bijection_eval_fuel_exists (e : ℕ) (pi : BitString → BitString)
    (L : List BitString)
    (h_eval : ∀ w ∈ L,
      ∃ k_w : ℕ, Nat.Partrec.Code.evaln k_w (Denumerable.ofNat Code e) (Encodable.encode w) =
        some (Encodable.encode (pi w))) :
    ∃ fuel : ℕ, bijectionEvalFuel e L fuel = true := by
  induction L with
  | nil => exact ⟨0, rfl⟩
  | cons w ws ih =>
    obtain ⟨kw, hkw⟩ := h_eval w List.mem_cons_self
    have h_ws : ∀ v ∈ ws, ∃ kv : ℕ,
        Nat.Partrec.Code.evaln kv (Denumerable.ofNat Code e) (Encodable.encode v) =
          some (Encodable.encode (pi v)) :=
      fun v hv => h_eval v (List.mem_cons_of_mem w hv)
    obtain ⟨f_ws, hf_ws⟩ := ih h_ws
    use max kw f_ws
    unfold bijectionEvalFuel
    rw [List.all_eq_true]
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv_ws
    · rw [Nat.Partrec.Code.evaln_mono (le_max_left kw f_ws) hkw]
      rfl
    · unfold bijectionEvalFuel at hf_ws
      rw [List.all_eq_true] at hf_ws
      have h_v_some := hf_ws v hv_ws
      obtain ⟨r_v, hr_v⟩ := Option.isSome_iff_exists.mp h_v_some
      rw [Nat.Partrec.Code.evaln_mono (le_max_right kw f_ws) hr_v]
      rfl

/-- The code of the uniform distribution on `S.image pi` belongs to the range of
`bijectionImageMap` for the paired code of `S` and program `e`. -/
private theorem codedUniformOn_image_mem_bijectionImageMap (S : Finset BitString)
    (hS : S.Nonempty) (pi : BitString → BitString) (e : ℕ)
    (he_eval : ∀ w : BitString,
      Encodable.encode (pi w) ∈ (Denumerable.ofNat Code e).eval (Encodable.encode w))
    (hS' : (S.image pi).Nonempty) :
    (codedUniformOn (S.image pi) hS').code ∈
      bijectionImageMap (pairCode (codedUniformOn S hS).code (natBits e)) := by
  set c_S := (codedUniformOn S hS).code
  set e_bits := natBits e
  set p := pairCode c_S e_bits
  have h_eval_all : ∀ w ∈ canonicalFinsetList S,
      ∃ k_w : ℕ, Nat.Partrec.Code.evaln k_w (Denumerable.ofNat Code e) (Encodable.encode w) =
        some (Encodable.encode (pi w)) := by
    intro w _
    exact Nat.Partrec.Code.evaln_complete.mp (he_eval w)
  obtain ⟨fuel, hfuel⟩ := bijection_eval_fuel_exists e pi (canonicalFinsetList S) h_eval_all
  have h_check_ex : ∃ fuel : ℕ, bijectionCheck (p, fuel) = true := by
    use fuel
    unfold bijectionCheck
    have h_p1 : decodeFirst p = c_S := decodeFirst_pairCode _ _
    have h_p2 : decodeSecond p = e_bits := decodeSecond_pairCode _ _
    have h_eb : decodeBits e_bits = e := decodeBits_natBits e
    have h_data : (decodeDistributionData c_S).map CodedDistributionEntry.point =
        canonicalFinsetList S :=
      dataPoints_codedUniformOn S hS
    simp only [h_p1, h_p2, h_eb, h_data]
    exact hfuel
  have h_rfind_dom : (Nat.rfind (fun fuel => Part.some (bijectionCheck (p, fuel)))).Dom := by
    obtain ⟨f, hf⟩ := h_check_ex
    exact Nat.rfind_dom.mpr ⟨f, by simp [hf]⟩
  set fuel_found := (Nat.rfind (fun fuel => Part.some (bijectionCheck (p, fuel)))).get h_rfind_dom
  have h_rfind_mem : fuel_found ∈ Nat.rfind (fun fuel => Part.some (bijectionCheck (p, fuel))) :=
    Part.get_mem h_rfind_dom
  have h_check_spec : bijectionCheck (p, fuel_found) = true := by
    have h_mem := Part.get_mem h_rfind_dom
    replace h_mem := Nat.mem_rfind.mp h_mem
    simpa using h_mem.1
  have h_fuel_spec : bijectionEvalFuel e (canonicalFinsetList S) fuel_found = true := by
    unfold bijectionCheck at h_check_spec
    have h_p1 : decodeFirst p = c_S := decodeFirst_pairCode _ _
    have h_p2 : decodeSecond p = e_bits := decodeSecond_pairCode _ _
    have h_eb : decodeBits e_bits = e := decodeBits_natBits e
    have h_data : (decodeDistributionData c_S).map CodedDistributionEntry.point =
        canonicalFinsetList S :=
      dataPoints_codedUniformOn S hS
    simpa only [h_p1, h_p2, h_eb, h_data] using h_check_spec
  have h_run_eq : bijectionRun e fuel_found (canonicalFinsetList S) =
      (canonicalFinsetList S).map pi := by
    apply bijectionRun_eq
    intro w hw
    unfold bijectionEvalFuel at h_fuel_spec
    rw [List.all_eq_true] at h_fuel_spec
    have h_some := h_fuel_spec w hw
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp h_some
    have hr_mem : r ∈ (Denumerable.ofNat Code e).eval (Encodable.encode w) :=
      Nat.Partrec.Code.evaln_sound hr
    have hpi_mem : Encodable.encode (pi w) ∈ (Denumerable.ofNat Code e).eval (Encodable.encode w) :=
      he_eval w
    have hr_eq : r = Encodable.encode (pi w) := Part.mem_unique hr_mem hpi_mem
    subst hr_eq
    refine ⟨Encodable.encode (pi w), hr, ?_⟩
    simp
  have h_finset_eq : (bijectionRun e fuel_found (canonicalFinsetList S)).toFinset =
      S.image pi := by
    rw [h_run_eq]
    ext y
    constructor
    · intro hy
      rw [List.mem_toFinset, List.mem_map] at hy
      obtain ⟨a, ha1, ha2⟩ := hy
      subst ha2
      exact Finset.mem_image_of_mem pi (mem_canonicalFinsetList.mp ha1)
    · intro hy
      rw [Finset.mem_image] at hy
      obtain ⟨a, ha1, ha2⟩ := hy
      subst ha2
      rw [List.mem_toFinset, List.mem_map]
      exact ⟨a, mem_canonicalFinsetList.mpr ha1, rfl⟩
  unfold bijectionImageMap
  rw [Part.mem_map_iff]
  refine ⟨fuel_found, h_rfind_mem, ?_⟩
  unfold bijectionPost
  have h_p1 : decodeFirst p = c_S := decodeFirst_pairCode _ _
  have h_p2 : decodeSecond p = e_bits := decodeSecond_pairCode _ _
  have h_eb : decodeBits e_bits = e := decodeBits_natBits e
  have h_data : (decodeDistributionData c_S).map CodedDistributionEntry.point =
      canonicalFinsetList S :=
    dataPoints_codedUniformOn S hS
  simp only [h_p1, h_p2, h_eb, h_data]
  have h_code_eq := codeFromList_eq (bijectionRun e fuel_found (canonicalFinsetList S))
    (by rw [h_finset_eq]; exact hS')
  have h_congr := codedUniformOn_code_congr (by rw [h_finset_eq]; exact hS') hS' h_finset_eq
  rw [h_congr] at h_code_eq
  exact h_code_eq

/-- Arithmetic bound shifting the description profile complexity coordinate under a simple
bijection. -/
private theorem simple_bijection_complexity_bound (i t c_pair c_f : ℕ) :
    i + t + c_pair + c_f ≤ i + (c_f + c_pair + 1) * (t + 1) := by
  calc i + t + c_pair + c_f
    _ = i + t + (c_pair + c_f) := by ring
    _ ≤ i + (c_f + c_pair + 1) * t + (c_f + c_pair + 1) := by
      have h1 : t ≤ (c_f + c_pair + 1) * t := Nat.le_mul_of_pos_left t (by omega)
      omega
    _ = i + (c_f + c_pair + 1) * (t + 1) := by ring

/-- **Exercise 354.** If `x` and `y` correspond to each other under a bijection
computed by a program of complexity at most `t`, then the description profile is
preserved up to an `O(t)` shift of the complexity coordinate. -/
theorem descriptionProfile_invariant_of_simple_bijection (U : Map)
    (hU : IsOptimalPrefixConditional U) :
    ∃ C : ℕ, ∀ (pi : BitString → BitString) (e t : ℕ),
      Function.Bijective pi →
      (∀ w : BitString,
        Encodable.encode (pi w) ∈ (Denumerable.ofNat Code e).eval (Encodable.encode w)) →
      kNat U e ≤ (t : ℕ∞) →
      ∀ (x : BitString) (i j : ℕ), InDescriptionProfile U x i j →
        InDescriptionProfile U (pi x) (i + C * (t + 1)) j := by
  obtain ⟨c_f, hc_f⟩ := KPPlain_partrec_map_le U hU bijectionImageMap bijectionImageMap_partrec
  obtain ⟨c_pair, hc_pair⟩ := KPPair_le_KPPlain_add_KPPlain U hU
  refine ⟨c_f + c_pair + 1, fun pi e t hbij he_eval he_kNat x i j hprof => ?_⟩
  rcases hprof with ⟨S, hS, hx_mem, hcomp_S, hcard_S⟩
  set S' := S.image pi
  have hS' : S'.Nonempty := ⟨pi x, Finset.mem_image_of_mem pi hx_mem⟩
  have hx' : pi x ∈ S' := Finset.mem_image_of_mem pi hx_mem
  have hcard' : S'.card ≤ 2 ^ j := by
    rw [Finset.card_image_of_injective S hbij.1]
    exact hcard_S
  refine ⟨S', hS', hx', ?_, hcard'⟩
  set c_S := (codedUniformOn S hS).code
  set e_bits := natBits e
  set p := pairCode c_S e_bits
  have h_image_mem : (codedUniformOn S' hS').code ∈ bijectionImageMap p :=
    codedUniformOn_image_mem_bijectionImageMap S hS pi e he_eval hS'
  have h_comp_image : KPPlain U (codedUniformOn S' hS').code ≤ KPPlain U p + (c_f : ENat) :=
    hc_f p _ h_image_mem
  have h_comp_pair : KPPlain U p ≤ KPPlain U c_S + KPPlain U e_bits + (c_pair : ENat) :=
    hc_pair c_S e_bits
  have h_e_bits : KPPlain U e_bits = kNat U e := rfl
  have h_cS : KPPlain U c_S = setComplexity U S hS := rfl
  unfold setComplexity
  have h_le1 : KPPlain U (codedUniformOn S' hS').code ≤
      (i : ENat) + (t : ENat) + (c_pair : ENat) + (c_f : ENat) := by
    calc KPPlain U (codedUniformOn S' hS').code
      _ ≤ KPPlain U p + (c_f : ENat) := h_comp_image
      _ ≤ (KPPlain U c_S + KPPlain U e_bits + (c_pair : ENat)) + (c_f : ENat) := by gcongr
      _ ≤ (i : ENat) + (t : ENat) + (c_pair : ENat) + (c_f : ENat) := by
        rw [h_e_bits, h_cS]
        gcongr
  have h_nat_le := simple_bijection_complexity_bound i t c_pair c_f
  have h_cast : ((i + t + c_pair + c_f : ℕ) : ENat) ≤
      ((i + (c_f + c_pair + 1) * (t + 1) : ℕ) : ENat) := by exact_mod_cast h_nat_le
  have h_group : (i : ENat) + (t : ENat) + (c_pair : ENat) + (c_f : ENat) =
      ((i + t + c_pair + c_f : ℕ) : ENat) := by
    push_cast
    ring
  rw [h_group] at h_le1
  exact h_le1.trans h_cast

/-- Adding `B` to `A` costs at most `B` extra binary digits: `(A + B).size ≤ A.size + B`. -/
theorem size_add_le (A B : ℕ) : (A + B).size ≤ A.size + B := by
  have hA : A < 2 ^ A.size := Nat.lt_size_self A
  have h_add : A + B < 2 ^ (A.size + B) := by
    by_cases hA0 : A.size = 0
    · have hA_eq : A = 0 := Nat.size_eq_zero.mp hA0
      subst hA_eq
      rw [zero_add, Nat.size_zero, zero_add]
      exact Nat.lt_pow_self (by decide : 1 < 2)
    · by_cases hB0 : B = 0
      · subst hB0
        rw [add_zero, add_zero]
        exact hA
      · have h1 : 2 ≤ 2 ^ A.size :=
          Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.pos_of_ne_zero hA0)
        have h2 : 2 ≤ 2 ^ B :=
          Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.pos_of_ne_zero hB0)
        calc A + B < 2 ^ A.size + 2 ^ B := by
               have hB : B < 2 ^ B := Nat.lt_pow_self (by decide : 1 < 2)
               omega
             _ ≤ 2 ^ A.size * 2 ^ B := by nlinarith
             _ = 2 ^ (A.size + B) := by rw [pow_add]
  exact Nat.size_le.mpr h_add

end Kolmogorov
