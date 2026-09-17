/-
Copyright (c) 2026 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Interface.Dovetailing
import KolmogorovMathlib.Complexity.Incompressibility
import KolmogorovMathlib.AlgorithmicProbability.PairProjection
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitinAllocator
import KolmogorovMathlib.Prefix.ConditionalSymmetry
import KolmogorovMathlib.Prefix.TwoStage
import KolmogorovMathlib.Prefix.CondTwoStage
import KolmogorovMathlib.Foundation.PrimrecExtras
import KolmogorovMathlib.Prefix.Properties
import KolmogorovMathlib.AlgorithmicStatistics.Selector
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Partrec
import Mathlib.Computability.Halting
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.PaperTheorems
import KolmogorovMathlib.Complexity.PairComplexity.Basic
import KolmogorovMathlib.Interface.ComputableReals
import KolmogorovMathlib.Complexity.PairComplexity
import KolmogorovMathlib.Complexity.ConditionalComplexity
import KolmogorovMathlib.Complexity.KolmogorovLevin
import KolmogorovMathlib.Complexity.RandomConditions
import KolmogorovMathlib.Complexity.SelfComplexity
import KolmogorovMathlib.Complexity.InfiniteSequences
import KolmogorovMathlib.Complexity.IncompressibleStrings
import KolmogorovMathlib.Complexity.Information
import KolmogorovMathlib.AlgorithmicProbability.UniversalSemimeasure
import KolmogorovMathlib.Prefix.TotalCountingBound
import KolmogorovMathlib.Prefix.KPPairSwap
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitinApplications.Part01
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitinApplications.Part02
import Mathlib.Data.Rat.Denumerable

/-!
# Numerical values of plain and prefix complexity

The `ℕ`-valued forms `kVal`, `kCondVal`, `kNat`, `kNatVal`, `cNatVal` of prefix and plain
complexity, the triple complexity `KPTriple`, the program complexity
`prefixProgramComplexity`, and the difference decompressor `natDiffDecompressor` used to
compare the complexity of a number with the complexity of its neighbours.

SUV Chapter 4, pp. 100-150.
-/

namespace Kolmogorov
open scoped ENNReal
open Nat.Partrec (Code)
open Kolmogorov.ComputableReals

/-! ### Numerical values of prefix and plain complexity -/

/-- The natural-number value of the prefix complexity `K(x)`. -/
noncomputable def kVal (U : Map) (x : BitString) : ℕ := (KPPlain U x).toNat

/-- The natural-number value of the conditional prefix complexity `K(x | y)`. -/
noncomputable def kCondVal (U : Map) (x y : BitString) : ℕ := (KP U x y).toNat

/-- The prefix complexity of a natural number, `K(n)`. -/
noncomputable def kNat (U : Map) (n : ℕ) : ℕ∞ := KPPlain U (natBits n)

/-- The natural-number value of `K(n)`. -/
noncomputable def kNatVal (U : Map) (n : ℕ) : ℕ := (kNat U n).toNat

/-- The plain complexity of a natural number, as a natural number. -/
noncomputable def cNatVal (U : Map) (n : ℕ) : ℕ := cVal U (natBits n)

/-- Prefix complexity of a triple. -/
noncomputable def KPTriple (U : Map) (x y z : BitString) : ℕ∞ := KP U (listCode [x, y, z]) []

/-- The minimal prefix complexity of a program mapping `y` to `x`. -/
noncomputable def prefixProgramComplexity (U : Map) (x y : BitString) : ℕ∞ :=
  sInf {v : ℕ∞ | ∃ e : ℕ,
    Encodable.encode x ∈ (Denumerable.ofNat Code e).eval (Encodable.encode y) ∧
      kNat U e = v}

/-! ### Prefix complexity: the remaining book statements -/

/-- Program `q` in context `ctx = prefixComplexityContext x kx` is interpreted as `natCode d`,
where `d = q.length - 1`. `decodeSecond ctx` is `natCode kx`,
so `kx = (decodeSecond ctx).length - 1`. The machine outputs `natBits (kx + d)`. -/
def natDiffDecompressorOpt (pr : BitString × BitString) : Option BitString :=
  bif decide (pr.1 = natCode (pr.1.length - 1)) then
    some (natBits ((decodeSecond pr.2).length - 1 + (pr.1.length - 1)))
  else
    none

/-- The machine that reads a natural `d` and a condition carrying a complexity value `k`, and
outputs the binary representation of `k + d`. -/
def natDiffDecompressor : Map := fun pr =>
  Part.ofOption (natDiffDecompressorOpt pr)

/-- That machine is a decompressor. -/
lemma natDiffDecompressor_computable : isDecompressor natDiffDecompressor := by
  have h_opt : Computable natDiffDecompressorOpt := by
    have h1 : Computable (fun pr : BitString × BitString => pr.1) := Computable.fst
    have h_len : Computable (fun pr : BitString × BitString => pr.1.length) :=
      Computable.list_length.comp Computable.fst
    have h_sub1 : Computable (fun p : ℕ => p - 1) := Primrec.pred.to_comp
    have h_d : Computable (fun pr : BitString × BitString => pr.1.length - 1) :=
      h_sub1.comp h_len
    have h_natcode : Computable (fun pr : BitString × BitString => natCode (pr.1.length - 1)) :=
      natCode_computable.comp h_d
    have h_beq : Computable (fun pr : BitString × BitString =>
        decide (pr.1 = natCode (pr.1.length - 1))) := by
      have h_eq : Computable (fun p : BitString × BitString => decide (p.1 = p.2)) := by
        have h_eq_prim : Primrec (fun p : BitString × BitString => decide (p.1 = p.2)) := by
          exact PrimrecPred.decide Primrec.eq
        exact h_eq_prim.to_comp
      exact h_eq.comp (h1.pair h_natcode)
    have h_len2 : Computable (fun pr : BitString × BitString => (decodeSecond pr.2).length) :=
      Computable.list_length.comp (decodeSecond_computable.comp Computable.snd)
    have h_kx : Computable (fun pr : BitString × BitString => (decodeSecond pr.2).length - 1) :=
      h_sub1.comp h_len2
    have h_u : Computable (fun pr : BitString × BitString =>
        (decodeSecond pr.2).length - 1 + (pr.1.length - 1)) := by
      have h_add : Computable (fun p : ℕ × ℕ => p.1 + p.2) := Primrec.nat_add.to_comp
      exact h_add.comp (h_kx.pair h_d)
    have h_out : Computable (fun pr : BitString × BitString =>
        natBits ((decodeSecond pr.2).length - 1 + (pr.1.length - 1))) :=
      natBits_computable.comp h_u
    have h_then : Computable (fun pr : BitString × BitString =>
        some (natBits ((decodeSecond pr.2).length - 1 + (pr.1.length - 1)))) :=
      Computable.option_some.comp h_out
    have h_none : Computable (fun (_ : BitString × BitString) => (none : Option BitString)) :=
      Computable.const none
    exact (Computable.cond h_beq h_then h_none).of_eq (fun pr => by
      unfold natDiffDecompressorOpt
      cases h : decide (pr.1 = natCode (pr.1.length - 1)) <;> rfl)
  exact Computable.ofOption h_opt

/-- That machine is a prefix machine. -/
lemma natDiffDecompressor_isPrefixMachine : IsPrefixMachine natDiffDecompressor := by
  intro y p hp q hq hpre
  unfold natDiffDecompressor natDiffDecompressorOpt at hp hq
  have hp' : natDiffDecompressorOpt (p, y) ≠ none := by
    intro h
    change (Part.ofOption (natDiffDecompressorOpt (p, y))).Dom at hp
    rw [h] at hp; exact hp
  have hq' : natDiffDecompressorOpt (q, y) ≠ none := by
    intro h
    change (Part.ofOption (natDiffDecompressorOpt (q, y))).Dom at hq
    rw [h] at hq; exact hq
  unfold natDiffDecompressorOpt at hp' hq'
  cases hp_eq : decide (p = natCode (p.length - 1)) <;> rw [hp_eq] at hp'
  · contradiction
  cases hq_eq : decide (q = natCode (q.length - 1)) <;> rw [hq_eq] at hq'
  · contradiction
  have hp_code : p = natCode (p.length - 1) := decide_eq_true_iff.mp hp_eq
  have hq_code : q = natCode (q.length - 1) := decide_eq_true_iff.mp hq_eq
  rw [hp_code, hq_code] at hpre ⊢
  exact natCode_prefix_iff.mp hpre ▸ rfl

/-- That machine is a prefix decompressor. -/
lemma natDiffDecompressor_isPrefixDecompressor : IsPrefixDecompressor natDiffDecompressor :=
  ⟨natDiffDecompressor_computable, natDiffDecompressor_isPrefixMachine⟩

/-- On the code of `d` with the complexity context of `x` at value `kx`, the machine outputs the
binary representation of `kx + d`. -/
lemma natDiffDecompressor_produces (x : BitString) (kx d : ℕ) :
    produces natDiffDecompressor (natCode d) (prefixComplexityContext x kx)
      (natBits (kx + d)) := by
  unfold produces natDiffDecompressor natDiffDecompressorOpt prefixComplexityContext
  rw [decodeSecond_pairCode, length_natCode, Nat.add_sub_cancel_right,
      length_natCode, Nat.add_sub_cancel_right]
  have : decide (natCode d = natCode d) = true := decide_eq_true_iff.mpr rfl
  rw [this]
  exact ⟨trivial, rfl⟩

/-- **Exercise 105.** If `K(x) ≤ u`, then `K(x, u) ≤ u + O(1)`. -/
theorem KP_pair_bound_le (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (u : ℕ), KPPlain U x ≤ (u : ℕ∞) →
      KPPair U x (natBits u) ≤ ((u + c : ℕ) : ℕ∞) := by
  have hctx : Computable (fun p : BitString × ℕ => prefixComplexityContext p.1 p.2) :=
    prefixComplexityContext_computable
  have hM_stage : IsPrefixDecompressor (twoStagePairBuilder U prefixComplexityContext) :=
    twoStagePairBuilder_isPrefixDecompressor hU.isDecompressor hU.isPrefixMachine hctx
  obtain ⟨c_stage, hc_stage⟩ := hU.invariance hM_stage
  obtain ⟨c_diff, hc_diff⟩ := hU.invariance natDiffDecompressor_isPrefixDecompressor
  refine ⟨c_stage + c_diff + 1, ?_⟩
  intro x u hx
  by_cases hKx_top : KPPlain U x = ⊤
  · rw [hKx_top] at hx
    contradiction
  · obtain ⟨p, hp, hplen⟩ := exists_program_of_KP_ne_top (M := U) (x := x) (y := []) hKx_top
    have hp_le : (p.length : ℕ∞) ≤ (u : ℕ∞) := by
      rw [hplen]
      exact hx
    have hplen_nat : p.length ≤ u := by
      exact_mod_cast hp_le
    let kx := p.length
    let d := u - kx
    have hd_add : kx + d = u := Nat.add_sub_of_le hplen_nat
    have hprod_diff : produces natDiffDecompressor (natCode d)
        (prefixComplexityContext x kx) (natBits u) := by
      have := natDiffDecompressor_produces x kx d
      rw [hd_add] at this
      exact this
    have hKP_diff : KP U (natBits u) (prefixComplexityContext x kx) ≠ ⊤ := by
      have h_le : KP U (natBits u) (prefixComplexityContext x kx) ≤
          KP natDiffDecompressor (natBits u) (prefixComplexityContext x kx)
            + (c_diff : ℕ∞) :=
        hc_diff (natBits u) (prefixComplexityContext x kx)
      have h_prog : KP natDiffDecompressor (natBits u)
          (prefixComplexityContext x kx) ≤ ((natCode d).length : ℕ∞) :=
        KP_le_programLength_of_produces hprod_diff
      have h_fin : ((natCode d).length : ℕ∞) + (c_diff : ℕ∞) ≠ ⊤ := ENat.natCast_ne_top _
      have h_sum : KP natDiffDecompressor (natBits u) (prefixComplexityContext x kx)
          + (c_diff : ℕ∞) ≤ ((natCode d).length : ℕ∞) + (c_diff : ℕ∞) :=
        add_le_add_left h_prog (c_diff : ℕ∞)
      exact ne_top_of_le_ne_top h_fin (h_le.trans h_sum)
    obtain ⟨q, hq, hqlen⟩ := exists_program_of_KP_ne_top (M := U) (x := natBits u)
      (y := prefixComplexityContext x kx) hKP_diff
    have hq_len_le : (q.length : ℕ∞) ≤ ((d + 1 + c_diff : ℕ) : ℕ∞) := by
      rw [hqlen]
      calc
        KP U (natBits u) (prefixComplexityContext x kx)
            ≤ KP natDiffDecompressor (natBits u) (prefixComplexityContext x kx)
              + (c_diff : ℕ∞) :=
          hc_diff (natBits u) (prefixComplexityContext x kx)
        _ ≤ ((natCode d).length : ℕ∞) + (c_diff : ℕ∞) :=
          add_le_add_left (KP_le_programLength_of_produces hprod_diff) (c_diff : ℕ∞)
        _ = ((d + 1 + c_diff : ℕ) : ℕ∞) := by
          rw [length_natCode]
          push_cast
          rfl
    have hq_len_nat : q.length ≤ d + 1 + c_diff := by
      exact_mod_cast hq_len_le
    have hbound := KP_twoStagePairBuilder_le_of_produces
      (U := U) (ctx := prefixComplexityContext) hU.isPrefixMachine hp hq
    calc
      KPPair U x (natBits u) = KP U (pairCode x (natBits u)) [] := rfl
      _ ≤ KP (twoStagePairBuilder U prefixComplexityContext)
            (pairCode x (natBits u)) [] + (c_stage : ℕ∞) :=
        hc_stage (pairCode x (natBits u)) []
      _ ≤ ((p.length + q.length : ℕ) : ℕ∞) + (c_stage : ℕ∞) :=
        add_le_add_left hbound (c_stage : ℕ∞)
      _ ≤ ((kx + (d + 1 + c_diff) + c_stage : ℕ) : ℕ∞) := by
        have h_add : p.length + q.length + c_stage ≤ kx + (d + 1 + c_diff) + c_stage := by
          omega
        exact_mod_cast h_add
      _ = ((u + (c_stage + c_diff + 1) : ℕ) : ℕ∞) := by
        have : kx + (d + 1 + c_diff) + c_stage = u + (c_stage + c_diff + 1) := by
          omega
        rw [this]

/-- The `ℕ`-valued shadow of the prefix complexity of a natural is a genuine complexity value of
its binary representation. -/
theorem kNatVal_hasPrefixComplexityValue (U : Map) (hU : IsOptimalPrefixConditional U) (n : ℕ) :
    HasPrefixComplexityValue U n.bits (kNatVal U n) := by
  dsimp [HasPrefixComplexityValue, kNatVal, kNat, natBits]
  have htop := KPPlain_ne_top_of_optimal U hU n.bits
  exact ENat.natCast_toNat htop

/-- The weight of the prefix complexity of `x` is `2^{-K(x)}` in terms of the `ℕ`-valued shadow. -/
theorem complexityWeight_KPPlain (U : Map) (hU : IsOptimalPrefixConditional U) (x : BitString) :
    complexityWeight (KPPlain U x) = (2 : ℝ≥0∞)⁻¹ ^ (kVal U x) := by
  have htop := KPPlain_ne_top_of_optimal U hU x
  have h_eq : KPPlain U x = (kVal U x : ℕ∞) := (ENat.natCast_toNat htop).symm
  rw [h_eq]
  exact complexityWeight_coe (kVal U x)

/-- **Exercise 106.** The average prefix complexity of the strings of length `n`
is `n + K(n) + O(1)`. -/
theorem average_KP_eq_length_add_KP (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ n : ℕ,
      |(((allStrings n).map (fun x => (kVal U x : ℝ))).sum) / (2 : ℝ) ^ n
          - ((n : ℝ) + (kNatVal U n : ℝ))| ≤ (c : ℝ) := by
  obtain ⟨c_up, hc_up⟩ := KPPlain_le_length_add_KPPlain_length U hU
  obtain ⟨c_marg, hc_marg⟩ := sum_complexityWeight_stringsOfLength_le U hU
  use 2 ^ (c_up + c_marg)
  intro n
  set kn := kNatVal U n
  have hkn_val : HasPrefixComplexityValue U n.bits kn := kNatVal_hasPrefixComplexityValue U hU n
  have h_sum_list : (((allStrings n).map (fun x => (kVal U x : ℝ))).sum) =
      ∑ x ∈ stringsOfLength n, (kVal U x : ℝ) := by
    change ((allStrings n).map (fun x => (kVal U x : ℝ))).sum =
      ∑ x ∈ (allStrings n).toFinset, (kVal U x : ℝ)
    rw [← List.sum_toFinset _ (allStrings_nodup n)]
  rw [h_sum_list]
  have h_le_up : ∀ x ∈ stringsOfLength n, kVal U x ≤ n + kn + c_up := by
    intro x hx
    have hxlen : x.length = n := (mem_allStrings n x).mp (List.mem_toFinset.mp hx)
    have hle := hc_up x
    rw [hxlen] at hle
    have hkn_eq : KPPlain U n.bits = (kn : ENat) := hkn_val.symm
    rw [hkn_eq] at hle
    have htop : KPPlain U x ≠ ⊤ := KPPlain_ne_top_of_optimal U hU x
    rw [← ENat.natCast_toNat htop] at hle
    exact_mod_cast hle
  have h_marg_enn : (∑ x ∈ stringsOfLength n, (2 : ℝ≥0∞)⁻¹ ^ (kVal U x)) ≤
      (2 : ℝ≥0∞) ^ c_marg * (2 : ℝ≥0∞)⁻¹ ^ kn := by
    have h := hc_marg n kn hkn_val
    have h_eq : (∑ x ∈ stringsOfLength n, complexityWeight (KPPlain U x)) =
        ∑ x ∈ stringsOfLength n, (2 : ℝ≥0∞)⁻¹ ^ (kVal U x) := by
      refine Finset.sum_congr rfl (fun x _ => complexityWeight_KPPlain U hU x)
    rwa [h_eq] at h
  have h_marg_real : (∑ x ∈ stringsOfLength n, (2 : ℝ)⁻¹ ^ (kVal U x)) ≤
      (2 : ℝ) ^ c_marg * (2 : ℝ)⁻¹ ^ kn := by
    have h_ne_top : (2 : ℝ≥0∞) ^ c_marg * (2 : ℝ≥0∞)⁻¹ ^ kn ≠ ⊤ := by
      apply ENNReal.mul_ne_top (ENNReal.pow_ne_top (by norm_num))
      exact ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr (by norm_num))
    have h_sum_ne_top : (∑ x ∈ stringsOfLength n, (2 : ℝ≥0∞)⁻¹ ^ (kVal U x)) ≠ ⊤ :=
      ne_top_of_le_ne_top h_ne_top h_marg_enn
    have h_toReal := ENNReal.toReal_le_toReal h_sum_ne_top h_ne_top |>.mpr h_marg_enn
    rw [ENNReal.toReal_sum
      (fun _ _ => ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr (by norm_num)))] at h_toReal
    simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv,
      ENNReal.toReal_ofNat] at h_toReal
    exact h_toReal
  set S := stringsOfLength n
  set M := n + kn + c_up
  set avg := (∑ x ∈ S, (kVal U x : ℝ)) / (2 : ℝ) ^ n
  have h_pow_pos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have h_pow_ne : (2 : ℝ) ^ n ≠ 0 := h_pow_pos.ne'
  have h_card : (S.card : ℝ) = (2 : ℝ) ^ n := by
    simp only [S, card_stringsOfLength, Nat.cast_pow, Nat.cast_ofNat]
  have h_sum_m : ∑ x ∈ S, ((M - kVal U x : ℕ) : ℝ) =
      (2 : ℝ) ^ n * (M : ℝ) - ∑ x ∈ S, (kVal U x : ℝ) := by
    have h_split : ∀ x ∈ S, ((M - kVal U x : ℕ) : ℝ) = (M : ℝ) - (kVal U x : ℝ) := by
      intro x hx
      exact Nat.cast_sub (h_le_up x hx)
    rw [Finset.sum_congr rfl h_split, Finset.sum_sub_distrib, Finset.sum_const,
      nsmul_eq_mul, h_card]
  have h_m_le_pow : ∀ x ∈ S, ((M - kVal U x : ℕ) : ℝ) ≤ (2 : ℝ) ^ (M - kVal U x) := by
    intro x _
    exact_mod_cast (Nat.lt_two_pow_self : M - kVal U x < 2 ^ (M - kVal U x)).le
  have h_pow_eq : ∀ x ∈ S, (2 : ℝ) ^ (M - kVal U x) =
      (2 : ℝ) ^ (n + kn + c_up) * (2 : ℝ)⁻¹ ^ (kVal U x) := by
    intro x hx
    have h_sub : M - kVal U x + kVal U x = n + kn + c_up := Nat.sub_add_cancel (h_le_up x hx)
    have h1 : (2 : ℝ) ^ (M - kVal U x) * (2 : ℝ) ^ (kVal U x) = (2 : ℝ) ^ (n + kn + c_up) := by
      rw [← pow_add, h_sub]
    calc
      (2 : ℝ) ^ (M - kVal U x) = (2 : ℝ) ^ (M - kVal U x) * (2 : ℝ) ^ (kVal U x) *
          (2 : ℝ)⁻¹ ^ (kVal U x) := by
        rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ (by norm_num), one_pow, mul_one]
      _ = (2 : ℝ) ^ (n + kn + c_up) * (2 : ℝ)⁻¹ ^ (kVal U x) := by rw [h1]
  have h_sum_m_le : ∑ x ∈ S, ((M - kVal U x : ℕ) : ℝ) ≤
      (2 : ℝ) ^ (c_up + c_marg) * (2 : ℝ) ^ n := by
    calc
      ∑ x ∈ S, ((M - kVal U x : ℕ) : ℝ) ≤ ∑ x ∈ S, (2 : ℝ) ^ (M - kVal U x) :=
        Finset.sum_le_sum h_m_le_pow
      _ = ∑ x ∈ S, ((2 : ℝ) ^ (n + kn + c_up) * (2 : ℝ)⁻¹ ^ (kVal U x)) :=
        Finset.sum_congr rfl h_pow_eq
      _ = (2 : ℝ) ^ (n + kn + c_up) * ∑ x ∈ S, (2 : ℝ)⁻¹ ^ (kVal U x) := by
        rw [Finset.mul_sum]
      _ ≤ (2 : ℝ) ^ (n + kn + c_up) * ((2 : ℝ) ^ c_marg * (2 : ℝ)⁻¹ ^ kn) := by gcongr
      _ = (2 : ℝ) ^ (c_up + c_marg) * (2 : ℝ) ^ n := by
        have h_pow_split : (2 : ℝ) ^ (n + kn + c_up) =
            (2 : ℝ) ^ n * (2 : ℝ) ^ kn * (2 : ℝ) ^ c_up := by rw [pow_add, pow_add]
        rw [h_pow_split]
        have h_cancel : (2 : ℝ) ^ kn * (2 : ℝ)⁻¹ ^ kn = 1 := by
          rw [← mul_pow, mul_inv_cancel₀ (by norm_num), one_pow]
        calc
          (2 : ℝ) ^ n * (2 : ℝ) ^ kn * (2 : ℝ) ^ c_up * ((2 : ℝ) ^ c_marg * (2 : ℝ)⁻¹ ^ kn)
              = (2 : ℝ) ^ c_up * (2 : ℝ) ^ c_marg *
                ((2 : ℝ) ^ kn * (2 : ℝ)⁻¹ ^ kn) * (2 : ℝ) ^ n := by ring
          _ = (2 : ℝ) ^ (c_up + c_marg) * 1 * (2 : ℝ) ^ n := by rw [← pow_add, h_cancel]
          _ = (2 : ℝ) ^ (c_up + c_marg) * (2 : ℝ) ^ n := by ring
  have hM_cast : (M : ℝ) = (n : ℝ) + (kn : ℝ) + (c_up : ℝ) := by dsimp [M]; push_cast; rfl
  have h_lower : (n : ℝ) + (kn : ℝ) - avg ≤ (2 : ℝ) ^ (c_up + c_marg) := by
    have h_div : (∑ x ∈ S, ((M - kVal U x : ℕ) : ℝ)) / (2 : ℝ) ^ n ≤
        (2 : ℝ) ^ (c_up + c_marg) := by
      rw [div_le_iff₀ h_pow_pos]
      exact h_sum_m_le
    rw [h_sum_m, sub_div, mul_div_cancel_left₀ _ h_pow_ne] at h_div
    change (M : ℝ) - avg ≤ (2 : ℝ) ^ (c_up + c_marg) at h_div
    rw [hM_cast] at h_div
    linarith
  have hc_up_le : (c_up : ℝ) ≤ (2 : ℝ) ^ (c_up + c_marg) := by
    have h_nat : c_up ≤ 2 ^ (c_up + c_marg) :=
      le_trans (Nat.le_add_right c_up c_marg)
        (Nat.lt_two_pow_self : c_up + c_marg < 2 ^ (c_up + c_marg)).le
    exact_mod_cast h_nat
  have h_upper : avg - ((n : ℝ) + (kn : ℝ)) ≤ (2 : ℝ) ^ (c_up + c_marg) := by
    have h_avg_le : avg ≤ (M : ℝ) := by
      dsimp [avg]
      rw [div_le_iff₀ h_pow_pos]
      calc
        ∑ x ∈ S, (kVal U x : ℝ) ≤ ∑ _x ∈ S, (M : ℝ) :=
          Finset.sum_le_sum (fun x hx => by exact_mod_cast h_le_up x hx)
        _ = (2 : ℝ) ^ n * (M : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, h_card]
        _ = (M : ℝ) * (2 : ℝ) ^ n := by rw [mul_comm]
    rw [hM_cast] at h_avg_le
    linarith [h_avg_le, hc_up_le]
  have h_abs : |avg - ((n : ℝ) + (kn : ℝ))| ≤ (2 : ℝ) ^ (c_up + c_marg) := by
    rw [abs_le]
    constructor <;> linarith
  exact_mod_cast h_abs

namespace PlainPrefixTwoStage

open Nat.Partrec (Code)

/-- The first stage of the two-stage machine: the output of the plain machine on the input read so
far. -/
def plainPrefixTwoStageS1 (cU : Code) (w : BitString) (n : ℕ) : Option BitString :=
  (Code.evaln n.unpair.2 cU (Encodable.encode (w.take n.unpair.1, ([] : BitString)))).bind
    (fun e => (Encodable.decode e : Option BitString))

/-- The second stage: the output of the prefix machine applied to the first stage's result. -/
def plainPrefixTwoStageS2 (cU cV : Code) (w : BitString) (n : ℕ) : Option BitString :=
  (plainPrefixTwoStageS1 cU w n).bind (fun x =>
    (Code.evaln n.unpair.2 cV (Encodable.encode (w.drop n.unpair.1, x))).bind
      (fun e => (Encodable.decode e : Option BitString)))

/-- The output of the two-stage machine at a given stage. -/
def plainPrefixTwoStageOut (cU cV : Code) (w : BitString) (n : ℕ) : Option BitString :=
  (plainPrefixTwoStageS1 cU w n).bind (fun x =>
    (plainPrefixTwoStageS2 cU cV w n).map (fun y => pairCode x y))

/-- The admissibility check of the two-stage machine at a given stage. -/
def plainPrefixTwoStageCheck (cU cV : Code) (w : BitString) (n : ℕ) : Bool :=
  decide (n.unpair.1 ≤ w.length) && (plainPrefixTwoStageOut cU cV w n).isSome

/-- The two-stage machine: it runs the plain machine and feeds its output to the prefix machine. -/
def plainPrefixTwoStageMap (cU cV : Code) : Map := fun pr =>
  (Nat.rfind (fun n => Part.some (plainPrefixTwoStageCheck cU cV pr.1 n))).bind
    (fun n => (↑(plainPrefixTwoStageOut cU cV pr.1 n) : Part BitString))

/-- The first stage is computable. -/
theorem plainPrefixTwoStageS1_computable (cU : Code) :
    Computable (fun p : BitString × ℕ => plainPrefixTwoStageS1 cU p.1 p.2) := by
  have h_evaln_computable : Computable₂ (fun (n : ℕ) (m : ℕ) => Code.evaln n cU m) :=
    evaln_fixed_computable cU
  have h_take_computable : Computable₂ (fun (w : BitString) (n : ℕ) => w.take n) :=
    (Primrec.list_take.comp Primrec.snd Primrec.fst).to_comp
  have h_time : Computable (fun p : BitString × ℕ => p.2.unpair.2) :=
    Computable.snd.comp (Computable.unpair.comp Computable.snd)
  have h_take : Computable (fun p : BitString × ℕ => p.1.take p.2.unpair.1) :=
    h_take_computable.comp Computable.fst
      (Computable.fst.comp (Computable.unpair.comp Computable.snd))
  have h_arg : Computable (fun p : BitString × ℕ =>
      Encodable.encode (p.1.take p.2.unpair.1, ([] : BitString))) :=
    Computable.encode.comp (h_take.pair (Computable.const ([] : BitString)))
  have h_eval : Computable (fun p : BitString × ℕ =>
      Code.evaln p.2.unpair.2 cU
        (Encodable.encode (p.1.take p.2.unpair.1, ([] : BitString)))) :=
    h_evaln_computable.comp h_time h_arg
  have h_dec : Computable₂ (fun (_ : BitString × ℕ) (e : ℕ) =>
      (Encodable.decode e : Option BitString)) :=
    Computable.decode.comp Computable.snd
  exact (Computable.option_bind h_eval h_dec).of_eq fun _ => rfl

/-- The second stage is computable. -/
theorem plainPrefixTwoStageS2_computable (cU cV : Code) :
    Computable (fun p : BitString × ℕ => plainPrefixTwoStageS2 cU cV p.1 p.2) := by
  have h_comp : Computable (fun p : BitString × ℕ => plainPrefixTwoStageS1 cU p.1 p.2) ∧
    Computable (fun p : BitString × ℕ => p.1.drop p.2.unpair.1) ∧
      Computable (fun p : BitString × ℕ => p.2.unpair.1 : BitString × ℕ → ℕ) ∧
        Computable (fun p : BitString × ℕ => p.2.unpair.2 : BitString × ℕ → ℕ) := by
    refine ⟨ plainPrefixTwoStageS1_computable cU, ?_, ?_, ?_ ⟩;
    · convert Primrec.to_comp ( Primrec.list_drop.comp ( Primrec.fst.comp (
        Primrec.unpair.comp ( Primrec.snd ) ) ) ( Primrec.fst ) ) using 1;
    · exact Computable.fst.comp ( Computable.unpair.comp ( Computable.snd ) );
    · exact Computable.snd.comp ( Computable.unpair.comp ( Computable.snd ) );
  have h_comp2 : Computable (fun p : BitString × ℕ =>
    (plainPrefixTwoStageS1 cU p.1 p.2).bind (fun x =>
      (Code.evaln p.2.unpair.2 cV (Encodable.encode (p.1.drop p.2.unpair.1,
        x))).bind (fun e => (Encodable.decode e : Option BitString)))) := by
    apply Computable.option_bind h_comp.1;
    apply Computable.option_bind;
    · convert evaln_fixed_computable cV |> Computable.comp <| Computable.pair (
        h_comp.2.2.2.comp <| Computable.fst ) ( Computable.encode.comp <| Computable.pair (
            h_comp.2.1.comp <| Computable.fst ) ( Computable.snd ) ) using 1;
    · exact Computable.decode.comp ( Computable.snd );
  exact h_comp2

/-- The stagewise output of the two-stage machine is computable. -/
theorem plainPrefixTwoStageOut_computable (cU cV : Code) :
    Computable (fun p : BitString × ℕ => plainPrefixTwoStageOut cU cV p.1 p.2) := by
  have h_twoStageS2_computable :
      Computable (fun p : BitString × ℕ => plainPrefixTwoStageS2 cU cV p.1 p.2) :=
    plainPrefixTwoStageS2_computable cU cV
  have h_twoStageS1_computable :
      Computable (fun p : BitString × ℕ => plainPrefixTwoStageS1 cU p.1 p.2) :=
    plainPrefixTwoStageS1_computable cU
  have h_pairCode_computable : Computable₂ (fun (x y : BitString) => pairCode x y) :=
    pairCode_computable
  have h_s2 : Computable (fun q : (BitString × ℕ) × BitString =>
      plainPrefixTwoStageS2 cU cV q.1.1 q.1.2) :=
    h_twoStageS2_computable.comp Computable.fst
  have h_map : Computable₂ (fun (q : (BitString × ℕ) × BitString) (y : BitString) =>
      pairCode q.2 y) :=
    h_pairCode_computable.comp (Computable.snd.comp Computable.fst) Computable.snd
  have h_inner : Computable₂ (fun (p : BitString × ℕ) (x : BitString) =>
      (plainPrefixTwoStageS2 cU cV p.1 p.2).map (fun y => pairCode x y)) :=
    Computable.option_map h_s2 h_map
  exact (Computable.option_bind h_twoStageS1_computable h_inner).of_eq fun _ => rfl

/-- The stagewise check of the two-stage machine is computable. -/
theorem plainPrefixTwoStageCheck_computable (cU cV : Code) :
    Computable (fun p : BitString × ℕ => plainPrefixTwoStageCheck cU cV p.1 p.2) := by
  have h1 : Computable (fun p : BitString × ℕ => decide (p.2.unpair.1 ≤ p.1.length)) := by
    have h1 : Computable (fun p : ℕ × ℕ => decide (p.1 ≤ p.2)) := by
      obtain ⟨_, h⟩ := Primrec.nat_le
      exact Computable.of_eq h.to_comp (fun p => by congr)
    convert h1.comp ( Computable.fst.comp ( Computable.unpair.comp (
        Computable.snd ) ) |> Computable.pair <| Computable.list_length.comp (
            Computable.fst ) ) using 1;
  have h2 : Computable (fun p : BitString × ℕ =>
      (plainPrefixTwoStageOut cU cV p.1 p.2).isSome) := by
    convert Primrec.to_comp ( Primrec.option_isSome )
        |> Computable.comp <| plainPrefixTwoStageOut_computable cU cV using 1;
  convert Computable.cond h1 h2 ( Computable.const false ) using 1;
  exact funext fun p => by
    unfold plainPrefixTwoStageCheck
    cases decide (p.2.unpair.1 ≤ p.1.length) <;> rfl

/-- The two-stage machine is partial computable. -/
theorem plainPrefixTwoStageMap_partrec (cU cV : Code) :
    Partrec (plainPrefixTwoStageMap cU cV) := by
  exact
    (Partrec.bind
      (Partrec.rfind (Computable.to₂ (plainPrefixTwoStageCheck_computable cU cV)).partrec₂)
      (Computable.ofOption (plainPrefixTwoStageOut_computable cU cV)).to₂).comp
        Computable.fst

/-- The two-stage machine produces on the composed input what the two machines produce in
succession. -/
lemma plainPrefixTwoStageMap_produces {U V : Map} {cU cV : Code}
    (hU : IsPrefixMachine U)
    (hcU : cU.eval = fun n =>
      (Part.ofOption (Encodable.decode (α := BitString × BitString) n)).bind
        (fun a => Part.map Encodable.encode (U a)))
    (hcV : cV.eval = fun n =>
      (Part.ofOption (Encodable.decode (α := BitString × BitString) n)).bind
        (fun a => Part.map Encodable.encode (V a)))
    {p q x y : BitString}
    (hp : produces U p [] x)
    (hq : produces V q x y) :
    produces (plainPrefixTwoStageMap cU cV) (p ++ q) [] (pairCode x y) := by
  have h1mem : Encodable.encode x ∈ cU.eval (Encodable.encode (p, ([] : BitString))) := by
    rw [hcU]; simp only [Part.mem_bind_iff]
    exact ⟨(p, ([] : BitString)), by simp [Encodable.encodek], Part.mem_map Encodable.encode hp⟩
  obtain ⟨t1, ht1⟩ :
      ∃ t1, Code.evaln t1 cU (Encodable.encode (p, ([] : BitString))) =
        some (Encodable.encode x) := by
    obtain ⟨k, hk⟩ := Nat.Partrec.Code.evaln_complete.mp h1mem
    exact ⟨k, Option.mem_def.mp hk⟩
  have h2mem : Encodable.encode y ∈ cV.eval (Encodable.encode (q, x)) := by
    rw [hcV]; simp only [Part.mem_bind_iff]
    exact ⟨(q, x), by simp [Encodable.encodek], Part.mem_map Encodable.encode hq⟩
  obtain ⟨t2, ht2⟩ :
      ∃ t2, Code.evaln t2 cV (Encodable.encode (q, x)) = some (Encodable.encode y) := by
    obtain ⟨k, hk⟩ := Nat.Partrec.Code.evaln_complete.mp h2mem
    exact ⟨k, Option.mem_def.mp hk⟩
  have ht1' : Code.evaln (max t1 t2) cU (Encodable.encode (p, ([] : BitString))) =
      some (Encodable.encode x) :=
    Nat.Partrec.Code.evaln_mono (le_max_left t1 t2) ht1
  have ht2' : Code.evaln (max t1 t2) cV (Encodable.encode (q, x)) =
      some (Encodable.encode y) :=
    Nat.Partrec.Code.evaln_mono (le_max_right t1 t2) ht2
  have hs1 : plainPrefixTwoStageS1 cU (p ++ q) (Nat.pair p.length (max t1 t2)) = some x := by
    unfold plainPrefixTwoStageS1
    simp only [Nat.unpair_pair, List.take_left, ht1', Option.bind_some, Encodable.encodek]
  have hs2 : plainPrefixTwoStageS2 cU cV (p ++ q) (Nat.pair p.length (max t1 t2)) = some y := by
    unfold plainPrefixTwoStageS2
    simp only [hs1, Option.bind_some, Nat.unpair_pair, List.drop_left, ht2', Encodable.encodek]
  have hout : plainPrefixTwoStageOut cU cV (p ++ q) (Nat.pair p.length (max t1 t2)) =
      some (pairCode x y) := by
    unfold plainPrefixTwoStageOut
    simp only [hs1, hs2, Option.bind_some, Option.map_some]
  have hcheck : plainPrefixTwoStageCheck cU cV (p ++ q) (Nat.pair p.length (max t1 t2)) = true := by
    unfold plainPrefixTwoStageCheck
    simp only [Nat.unpair_pair, List.length_append, hout, Option.isSome_some, Bool.and_true,
      decide_eq_true_eq]
    omega
  have hrdom :
      (Nat.rfind (fun m => Part.some (plainPrefixTwoStageCheck cU cV (p ++ q) m))).Dom := by
    exact Nat.rfind_dom.mpr ⟨Nat.pair p.length (max t1 t2),
      by rw [Part.mem_some_iff, hcheck], fun {m} _ => Part.some_dom _⟩
  set n' := (Nat.rfind (fun m => Part.some (plainPrefixTwoStageCheck cU cV (p ++ q) m))).get hrdom
  have hn'mem : n' ∈ Nat.rfind (fun m => Part.some (plainPrefixTwoStageCheck cU cV (p ++ q) m)) :=
    Part.get_mem hrdom
  have hn'spec := (Nat.mem_rfind.mp hn'mem).1
  rw [Part.mem_some_iff, eq_comm] at hn'spec
  unfold plainPrefixTwoStageCheck at hn'spec
  rw [Bool.and_eq_true, decide_eq_true_eq] at hn'spec
  obtain ⟨hlen_le, hsome⟩ := hn'spec
  obtain ⟨z, hz⟩ := Option.isSome_iff_exists.mp hsome
  unfold plainPrefixTwoStageOut at hz
  rw [Option.bind_eq_some_iff] at hz
  obtain ⟨x', hx', hy'⟩ := hz
  rw [Option.map_eq_some_iff] at hy'
  obtain ⟨y', hy', rfl⟩ := hy'
  unfold plainPrefixTwoStageS1 at hx'
  rw [Option.bind_eq_some_iff] at hx'
  obtain ⟨a1, ha1, ha1_dec⟩ := hx'
  have h_eval1 := Nat.Partrec.Code.evaln_sound ha1
  rw [hcU, Part.mem_bind_iff] at h_eval1
  obtain ⟨⟨p', r1⟩, hr1, hx_map⟩ := h_eval1
  rw [Part.mem_ofOption] at hr1
  have hr1_eq : (p', r1) = ((p ++ q).take n'.unpair.1, []) := by
    apply Option.some.inj; rw [← hr1, Encodable.encodek]
  injection hr1_eq with hp'_eq hr1_eq'
  subst hp'_eq; subst hr1_eq'
  rw [Part.mem_map_iff] at hx_map
  obtain ⟨x'', hx'', hencode1⟩ := hx_map
  have hx''_eq : x'' = x' := by
    apply Option.some.inj; rw [← ha1_dec, ← hencode1, Encodable.encodek]
  have hpre1 : (p ++ q).take n'.unpair.1 <+: p ++ q := List.take_prefix _ _
  have hpre2 : p <+: p ++ q := List.prefix_append p q
  have hp_eq : (p ++ q).take n'.unpair.1 = p := by
    rcases List.prefix_or_prefix_of_prefix hpre1 hpre2 with hpre | hpre
    · exact IsPrefixMachine.eq_of_prefix hU hx'' hp hpre
    · exact (IsPrefixMachine.eq_of_prefix hU hp hx'' hpre).symm
  have hlen_eq : n'.unpair.1 = p.length := by
    have h1 := congr_arg List.length hp_eq
    rw [List.length_take] at h1
    omega
  rw [hp_eq] at hx''
  have hx_eq : x'' = x := Part.mem_unique hx'' hp
  subst hx_eq
  subst hx''_eq
  unfold plainPrefixTwoStageS2 at hy'
  have hx1 : plainPrefixTwoStageS1 cU (p ++ q) n' = some x'' := by
    unfold plainPrefixTwoStageS1
    rw [ha1, Option.bind_some, ha1_dec]
  rw [hx1, Option.bind_some, Option.bind_eq_some_iff] at hy'
  obtain ⟨a2, ha2, ha2_dec⟩ := hy'
  have h_eval2 := Nat.Partrec.Code.evaln_sound ha2
  rw [hcV, Part.mem_bind_iff] at h_eval2
  obtain ⟨⟨q', x_cond⟩, hq_cond, hy_map⟩ := h_eval2
  rw [Part.mem_ofOption] at hq_cond
  have hq_cond_eq : (q', x_cond) = ((p ++ q).drop n'.unpair.1, x'') := by
    apply Option.some.inj; rw [← hq_cond, Encodable.encodek]
  injection hq_cond_eq with hq'_eq hx_cond_eq
  subst hq'_eq; subst hx_cond_eq
  rw [Part.mem_map_iff] at hy_map
  obtain ⟨y'', hy'', hencode2⟩ := hy_map
  have hy''_eq : y'' = y' := by
    apply Option.some.inj; rw [← ha2_dec, ← hencode2, Encodable.encodek]
  subst hy''_eq
  have hq_eq : (p ++ q).drop n'.unpair.1 = q := by
    rw [hlen_eq, List.drop_left]
  rw [hq_eq] at hy''
  have h2 : plainPrefixTwoStageS2 cU cV (p ++ q) n' = some y'' := by
    unfold plainPrefixTwoStageS2
    rw [hx1, Option.bind_some, Option.bind_eq_some_iff]
    exact ⟨a2, ha2, ha2_dec⟩
  have hy_eq : y'' = y := Part.mem_unique hy'' hq
  unfold plainPrefixTwoStageMap produces
  rw [Part.mem_bind_iff]
  refine ⟨n', hn'mem, ?_⟩
  rw [Part.mem_coe]
  unfold plainPrefixTwoStageOut
  rw [hx1, Option.bind_some, h2, Option.map_some, hy_eq]
  rfl

end PlainPrefixTwoStage

/-- **Exercise 110.** `C(x, y) ≤ K(x) + C(y | x) + O(1)`. -/
theorem plainK_pair_le_KP_add_condK (U V : Map)
    (hU : IsOptimalPrefixConditional U) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ x y : BitString,
      cPair V x y ≤ KPPlain U x + condK V y x + (c : ℕ∞) := by
  obtain ⟨cU, hcU⟩ := Nat.Partrec.Code.exists_code.mp hU.isDecompressor
  obtain ⟨cV, hcV⟩ := Nat.Partrec.Code.exists_code.mp hV.1
  have hD : isDecompressor (PlainPrefixTwoStage.plainPrefixTwoStageMap cU cV) :=
    PlainPrefixTwoStage.plainPrefixTwoStageMap_partrec cU cV
  obtain ⟨c, hc⟩ := hV.2 (PlainPrefixTwoStage.plainPrefixTwoStageMap cU cV) hD
  refine ⟨c, fun x y => ?_⟩
  by_cases hx : KPPlain U x = ⊤
  · rw [hx, top_add]; exact le_top
  by_cases hy : condK V y x = ⊤
  · rw [hy, add_top]; exact le_top
  obtain ⟨p, hp, hplen⟩ := exists_program_of_KP_ne_top (M := U) (x := x) (y := [])
    (by rwa [KPPlain_eq_KP] at hx)
  obtain ⟨q, hq, hqlen⟩ := exists_program_of_KP_ne_top (M := V) (x := y) (y := x) hy
  have hprod := PlainPrefixTwoStage.plainPrefixTwoStageMap_produces hU.isPrefixMachine hcU hcV hp hq
  have hbound : KP (PlainPrefixTwoStage.plainPrefixTwoStageMap cU cV) (pairCode x y) [] ≤
      ((p.length + q.length : ℕ) : ENat) := by
    have h1 := KP_le_programLength_of_produces hprod
    simpa [programLength, List.length_append] using h1
  have hV_bound := hc (pairCode x y) []
  have hsum : ((p.length + q.length : ℕ) : ENat) = KPPlain U x + condK V y x := by
    rw [Nat.cast_add, hplen, hqlen, KPPlain_eq_KP, KP_eq_condK V y x]
  have hENat : condK V (pairCode x y) [] ≤ KPPlain U x + condK V y x + (c : ENat) := by
    calc condK V (pairCode x y) []
      _ ≤ condK (PlainPrefixTwoStage.plainPrefixTwoStageMap cU cV) (pairCode x y) [] + (c : ENat) :=
        hV_bound
      _ ≤ ((p.length + q.length : ℕ) : ENat) + (c : ENat) := by
        gcongr
        rw [← KP_eq_condK]
        exact hbound
      _ = KPPlain U x + condK V y x + (c : ENat) := by rw [hsum]
  exact hENat

/-- **Exercise 107.** `C(x, y) ≤ K(x) + C(y) + O(1)`. -/
theorem plainK_pair_le_KP_add_plainK (U V : Map)
    (hU : IsOptimalPrefixConditional U) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ x y : BitString,
      cPair V x y ≤ KPPlain U x + plainK V y + (c : ℕ∞) := by
  obtain ⟨c110, hc110⟩ := plainK_pair_le_KP_add_condK U V hU hV
  let D_ignore : Map := fun pr => V (pr.1, [])
  have hD : isDecompressor D_ignore :=
    Partrec.comp hV.1 (Computable.fst.pair (Computable.const []))
  obtain ⟨c_ignore, hc_ignore⟩ := hV.2 D_ignore hD
  refine ⟨c110 + c_ignore, fun x y => ?_⟩
  calc
    cPair V x y ≤ KPPlain U x + condK V y x + (c110 : ℕ∞) := hc110 x y
    _ ≤ KPPlain U x + (plainK V y + (c_ignore : ℕ∞)) + (c110 : ℕ∞) := by
      gcongr
      exact hc_ignore y x
    _ = KPPlain U x + plainK V y + ((c110 + c_ignore : ℕ) : ℕ∞) := by
      push_cast
      ring

/-- Decoding a pair of binary representations and returning the binary representation of the
truncated difference of the two numbers. -/
def subPairBits (z : BitString) : BitString :=
  natBits (bitsToNat (decodeFirst z) - bitsToNat (decodeSecond z))

/-- That decoder is computable. -/
lemma subPairBits_computable : Computable subPairBits := by
  have h1 : Primrec (fun z => decodeFirst z) := CodedFiniteDistribution.decodeFirst_primrec
  have h2 : Primrec (fun z => decodeSecond z) := CodedFiniteDistribution.decodeSecond_primrec
  have hu : Primrec (fun z => bitsToNat (decodeFirst z)) := bitsToNat_primrec.comp h1
  have hv : Primrec (fun z => bitsToNat (decodeSecond z)) := bitsToNat_primrec.comp h2
  have hsub : Primrec (fun z => bitsToNat (decodeFirst z) - bitsToNat (decodeSecond z)) :=
    Primrec.nat_sub.comp hu hv
  have hbits :
      Primrec (fun z => natBits (bitsToNat (decodeFirst z) - bitsToNat (decodeSecond z))) :=
    primrec_natBits.comp hsub
  exact hbits.to_comp

/-- On the pair code of the representations of `n` and `k'` the decoder returns the representation
of `n - k'`. -/
lemma subPairBits_eval (n k' : ℕ) :
    subPairBits (pairCode (natBits n) (natBits k')) = natBits (n - k') := by
  dsimp [subPairBits, natBits]
  rw [decodeFirst_pairCode, decodeSecond_pairCode, bitsToNat_bits, bitsToNat_bits]

/-- The binary representation of `x` is at most `log₂ (x + 2) + 1` bits long. -/
lemma bits_len_le_log2_add_two (x : ℕ) :
    (Nat.bits x).length ≤ Nat.log 2 (x + 2) + 1 := by
  have hsz : (Nat.bits x).length = Nat.size x := Nat.size_eq_bits_len x
  rw [hsz]
  have hpow : x < 2 ^ (Nat.log 2 (x + 2) + 1) := by
    have h1 : x + 2 < 2 ^ (Nat.log 2 (x + 2) + 1) := Nat.lt_pow_succ_log_self (by decide) (x + 2)
    omega
  exact Nat.size_le.mpr hpow

/-- `2k ≤ 2^k` for every natural `k`. -/
lemma two_mul_le_two_pow (k : ℕ) : 2 * k ≤ 2 ^ k := by
  induction k with
  | zero => decide
  | succ k' ih =>
    rcases k' with _ | k''
    · decide
    · calc 2 * (k'' + 2) = 2 * (k'' + 1) + 2 := by ring
        _ ≤ 2 ^ (k'' + 1) + 2 := by omega
        _ ≤ 2 ^ (k'' + 1) + 2 ^ (k'' + 1) := by
          have : 1 ≤ 2 ^ k'' := Nat.one_le_two_pow
          omega
        _ = 2 ^ (k'' + 2) := by ring

/-- `2 · log₂ (m + 2) ≤ m + 2` for every natural `m`. -/
lemma two_mul_log2_le (m : ℕ) : 2 * Nat.log 2 (m + 2) ≤ m + 2 := by
  have h1 := two_mul_le_two_pow (Nat.log 2 (m + 2))
  have h2 := Nat.pow_log_le_self 2 (by omega : m + 2 ≠ 0)
  omega

/-- A positive number below `2^K` has binary logarithm below `K`. -/
lemma log2_lt_of_lt_pow {x K : ℕ} (hx_pos : 0 < x) (hx : x < 2 ^ K) : Nat.log 2 x < K := by
  by_contra h
  push Not at h
  have h1 : 2 ^ K ≤ 2 ^ Nat.log 2 x := Nat.pow_le_pow_right (by decide) h
  have h2 : 2 ^ Nat.log 2 x ≤ x := Nat.pow_log_le_self 2 (ne_of_gt hx_pos)
  have h_le : 2 ^ K ≤ x := h1.trans h2
  omega

/-- The logarithm of a sum is at most the sum of the logarithms, up to one extra bit. -/
lemma log2_add_two_add_le (d m : ℕ) :
    Nat.log 2 (d + m + 2) ≤ Nat.log 2 (d + 2) + Nat.log 2 (m + 2) + 1 := by
  have hd : d + 2 < 2 ^ (Nat.log 2 (d + 2) + 1) := Nat.lt_pow_succ_log_self (by decide) (d + 2)
  have hm : m + 2 < 2 ^ (Nat.log 2 (m + 2) + 1) := Nat.lt_pow_succ_log_self (by decide) (m + 2)
  have hprod : d + m + 2 < 2 ^ (Nat.log 2 (d + 2) + Nat.log 2 (m + 2) + 2) := by
    have h_prod1 : d + m + 2 < (d + 2) * (m + 2) := by nlinarith
    have h_pow : (d + 2) * (m + 2) < 2 ^ (Nat.log 2 (d + 2) + Nat.log 2 (m + 2) + 2) := by
      have h_exp : Nat.log 2 (d + 2) + 1 + (Nat.log 2 (m + 2) + 1) =
          Nat.log 2 (d + 2) + Nat.log 2 (m + 2) + 2 := by omega
      rw [← h_exp, pow_add]
      nlinarith
    exact h_prod1.trans h_pow
  have hlt := log2_lt_of_lt_pow (by omega) hprod
  omega

/-- **Exercise 108.** A string of length `n` with `C(x) ≤ n - d` has prefix
complexity at most `n + K(n) - d + O(log d)`. -/
theorem KP_le_of_plainK_le_sub (U V : Map)
    (hU : IsOptimalPrefixConditional U) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ (n d : ℕ) (x : BitString), x.length = n →
      (cVal V x : ℤ) ≤ (n : ℤ) - (d : ℤ) →
      (kVal U x : ℤ) ≤ (n : ℤ) + (kNatVal U n : ℤ) - (d : ℤ)
        + (c : ℤ) * ((Nat.log 2 (d + 2) : ℤ) + 1) := by
  obtain ⟨c65, hc65⟩ := KPPlain_le_plainK_add_KPPlain_plainK U V hU hV
  obtain ⟨c_map, hc_map⟩ := KPPlain_map_le U hU subPairBits subPairBits_computable
  obtain ⟨c_pair, hc_pair⟩ := KPPair_le_KPPlain_add_KPPlain U hU
  obtain ⟨c_bits, hc_bits⟩ := KPPlain_le_two_mul_length U hU
  set c := c65 + c_map + c_pair + c_bits + 12
  refine ⟨c, ?_⟩
  intro n d x hx hC
  by_cases hdn : n < d
  · have : (n : ℤ) - (d : ℤ) < 0 := by omega
    have : (cVal V x : ℤ) ≥ 0 := by positivity
    omega
  · push Not at hdn
    set k := cVal V x
    have hk_le : k ≤ n - d := by omega
    set m := n - d - k
    set k' := d + m
    have hk'_eq : k' = n - k := by omega
    have hk_sub : n - k' = k := by omega
    have hplain : plainK V x = (k : ENat) := by
      dsimp [k, cVal]
      obtain ⟨c_len, hc_len⟩ := plainK_le_length V hV
      have htop : plainK V x ≠ ⊤ := by
        have h_bound := hc_len x
        have h_top_ne : ((x.length + c_len : ℕ) : ENat) ≠ ⊤ := ENat.natCast_ne_top _
        exact ne_top_of_le_ne_top h_top_ne h_bound
      exact (ENat.natCast_toNat htop).symm
    have h_65 := hc65 x k hplain
    have h_sub_eval := subPairBits_eval n k'
    have h_map := hc_map (pairCode (natBits n) (natBits k'))
    rw [h_sub_eval, hk_sub] at h_map
    have h_pair := hc_pair (natBits n) (natBits k')
    have h_bits : KPPlain U (natBits k') ≤ ((2 * (Nat.bits k').length + c_bits : ℕ) : ENat) :=
      hc_bits (natBits k')
    have h_4 : KPPlain U (natBits n) = (kNatVal U n : ENat) := by
      dsimp [kNatVal, kNat]
      have htop : KPPlain U (natBits n) ≠ ⊤ :=
        KPPlain_ne_top_of_optimal U hU (natBits n)
      exact (ENat.natCast_toNat htop).symm
    have h_step1 : KPPlain U (natBits k) ≤
        KPPlain U (natBits n) + KPPlain U (natBits k') + (c_pair : ENat) + (c_map : ENat) := by
      have h_pair' := hc_pair (natBits n) (natBits k')
      change KPPlain U (pairCode (natBits n) (natBits k')) ≤
        KPPlain U (natBits n) + KPPlain U (natBits k') + (c_pair : ENat) at h_pair'
      have h_pair_add : KPPlain U (pairCode (natBits n) (natBits k')) + (c_map : ENat) ≤
          (KPPlain U (natBits n) + KPPlain U (natBits k') + (c_pair : ENat)) +
          (c_map : ENat) := by
        gcongr
      exact h_map.trans h_pair_add
    have h_step2 : KPPlain U (natBits n) + KPPlain U (natBits k') + (c_pair : ENat) +
        (c_map : ENat) ≤ (kNatVal U n : ENat) + ((2 * (Nat.bits k').length + c_bits : ℕ) : ENat) +
        (c_pair : ENat) + (c_map : ENat) := by
      rw [h_4]
      gcongr
    have h_k_bits : KPPlain U (natBits k) ≤ (kNatVal U n : ENat) +
        ((2 * (Nat.bits k').length + c_bits + c_pair + c_map : ℕ) : ENat) := by
      calc KPPlain U (natBits k)
          ≤ KPPlain U (natBits n) + KPPlain U (natBits k') + (c_pair : ENat) +
            (c_map : ENat) := h_step1
        _ ≤ (kNatVal U n : ENat) + ((2 * (Nat.bits k').length + c_bits : ℕ) : ENat) +
            (c_pair : ENat) + (c_map : ENat) := h_step2
        _ = (kNatVal U n : ENat) +
            ((2 * (Nat.bits k').length + c_bits + c_pair + c_map : ℕ) : ENat) := by
            push_cast; abel
    have h_nat_k : (natBits k) = k.bits := rfl
    have h_65' : KPPlain U x ≤ (k : ENat) + KPPlain U (natBits k) + (c65 : ENat) := by
      rw [h_nat_k]
      exact h_65
    have h_kx_enat : KPPlain U x ≤ (k : ENat) + (kNatVal U n : ENat) +
        ((2 * (Nat.bits k').length + c_bits + c_pair + c_map + c65 : ℕ) : ENat) := by
      calc KPPlain U x
          ≤ (k : ENat) + KPPlain U (natBits k) + (c65 : ENat) := h_65'
        _ ≤ (k : ENat) + ((kNatVal U n : ENat) +
            ((2 * (Nat.bits k').length + c_bits + c_pair + c_map : ℕ) : ENat)) + (c65 : ENat) := by
            gcongr
        _ = (k : ENat) + (kNatVal U n : ENat) +
            ((2 * (Nat.bits k').length + c_bits + c_pair + c_map + c65 : ℕ) : ENat) := by
            push_cast; abel
    have htop_x : KPPlain U x ≠ ⊤ := KPPlain_ne_top_of_optimal U hU x
    have h1_x : KPPlain U x = (kVal U x : ENat) := (ENat.natCast_toNat htop_x).symm
    have h_kx_nat : kVal U x ≤ k + kNatVal U n +
        (2 * (Nat.bits k').length + c_bits + c_pair + c_map + c65) := by
      have h2 : KPPlain U x ≤ ((k + kNatVal U n +
          (2 * (Nat.bits k').length + c_bits + c_pair + c_map + c65) : ℕ) : ENat) := by
        push_cast
        exact h_kx_enat
      rw [h1_x] at h2
      exact WithTop.coe_le_coe.mp h2
    have h_bits_len := bits_len_le_log2_add_two k'
    have h_log_add := log2_add_two_add_le d m
    have h_m_log := two_mul_log2_le m
    have h_two_bits : 2 * (Nat.bits k').length ≤ 2 * Nat.log 2 (d + 2) + m + 6 := by
      dsimp [k'] at h_bits_len h_log_add ⊢
      omega
    have hk_add_m : k + m = n - d := by dsimp [k, m]; omega
    have h_sum_nat : kVal U x ≤ (n - d) + kNatVal U n + 2 * Nat.log 2 (d + 2) +
        (c_bits + c_pair + c_map + c65 + 6) := by omega
    have h_kx_z : (kVal U x : ℤ) ≤ (n : ℤ) - (d : ℤ) + (kNatVal U n : ℤ) +
        2 * (Nat.log 2 (d + 2) : ℤ) + (c_bits + c_pair + c_map + c65 + 6 : ℤ) := by
      zify at h_sum_nat hdn
      omega
    have h_c_bound : (c_bits + c_pair + c_map + c65 + 6 : ℤ) + 2 * (Nat.log 2 (d + 2) : ℤ) ≤
        (c : ℤ) * ((Nat.log 2 (d + 2) : ℤ) + 1) := by
      dsimp [c]
      have h_pos : 0 ≤ (Nat.log 2 (d + 2) : ℤ) := by positivity
      nlinarith
    linarith

end Kolmogorov
