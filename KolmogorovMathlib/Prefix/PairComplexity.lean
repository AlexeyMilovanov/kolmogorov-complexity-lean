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
import KolmogorovMathlib.Prefix.NumericalValues

/-!
# Prefix complexity of pairs

Complexity of pairs and of nested pairs: the pair codes
`tripleCodeOfNestedPair` and `tripleCodeOfSwappedPair` and the bounds proved from them, and
the minimal-restriction witness `minimalRestrictWitnessFun`.

SUV Exercises 98 and 114, pp. 110 and 149.
-/

namespace Kolmogorov
open scoped ENNReal
open Nat.Partrec (Code)
open Kolmogorov.ComputableReals

/-- Auxiliary decompressor mapping `x` to `y` via a program code `e` produced by `U`. -/
noncomputable def evalProgDecompressor (U : Map) : Map := fun pr =>
  (U (pr.1, [])).bind (fun p_out =>
    let e := decodeBits p_out
    Part.map (fun (code_out : ℕ) => (Encodable.decode code_out : Option BitString).getD [])
      ((Denumerable.ofNat Nat.Partrec.Code e).eval (Encodable.encode (pr.2))))

/-- `evalProgDecompressor U` is a decompressor whenever `U` is: it is the composition
of the partial recursive `U` with the universal evaluation of the decoded machine
code, hence partial recursive. -/
lemma evalProgDecompressor_isDecompressor (U : Map) (hU : isDecompressor U) :
    isDecompressor (evalProgDecompressor U) := by
  dsimp [evalProgDecompressor, isDecompressor]
  apply Partrec.bind
  · exact Partrec.comp hU (Computable.fst.pair (Computable.const []))
  · apply Partrec.map
    · apply Partrec₂.comp Nat.Partrec.Code.eval_part
      · have h_dec : Computable (fun (p : (BitString × BitString) × BitString) =>
            (Encodable.decode (decodeBits p.2) : Option Nat.Partrec.Code)) :=
          Computable.decode.comp (decodeBits_computable.comp Computable.snd)
        exact (Computable.ofOption h_dec).of_eq (fun p => by
          rw [Denumerable.decode_eq_ofNat Nat.Partrec.Code, Part.coe_some]
          rfl)
      · exact Computable.encode.comp (Computable.snd.comp Computable.fst)
    · have h_getD : Primrec (fun (code_out : ℕ) =>
          (Encodable.decode code_out : Option BitString).getD []) :=
        Primrec.option_getD.comp Primrec.decode (Primrec.const [])
      exact Primrec.to_comp (h_getD.comp Primrec.snd)

/-- `evalProgDecompressor U` has a prefix-free halting set in each context, because a
program halts for it exactly when it halts for `U` in the empty context. -/
lemma evalProgDecompressor_isPrefixMachine (U : Map) (hU : IsPrefixMachine U) :
    IsPrefixMachine (evalProgDecompressor U) := by
  intro y p hp q hq hpre
  dsimp [domainAt, Set.mem_setOf_eq, evalProgDecompressor] at hp hq
  have hp' : p ∈ domainAt U [] := by
    dsimp [domainAt, Set.mem_setOf_eq]
    rcases Part.dom_iff_mem.mp hp with ⟨out_p, hp_mem⟩
    rcases Part.mem_bind_iff.mp hp_mem with ⟨p_out_p, hp_U, _⟩
    exact Part.dom_iff_mem.mpr ⟨p_out_p, hp_U⟩
  have hq' : q ∈ domainAt U [] := by
    dsimp [domainAt, Set.mem_setOf_eq]
    rcases Part.dom_iff_mem.mp hq with ⟨out_q, hq_mem⟩
    rcases Part.mem_bind_iff.mp hq_mem with ⟨p_out_q, hq_U, _⟩
    exact Part.dom_iff_mem.mpr ⟨p_out_q, hq_U⟩
  exact hU [] hp' hq' hpre

/-- For an optimal conditional prefix machine `U`, the auxiliary machine
`evalProgDecompressor U` is a prefix decompressor. -/
lemma evalProgDecompressor_isPrefixDecompressor (U : Map) (hU : IsOptimalPrefixConditional U) :
    IsPrefixDecompressor (evalProgDecompressor U) :=
  ⟨evalProgDecompressor_isDecompressor U hU.isDecompressor,
   evalProgDecompressor_isPrefixMachine U hU.isPrefixMachine⟩

/-- If the program `p` makes `U` output the code `e` of a machine that maps `x` to
`y`, then `p` makes `evalProgDecompressor U` output `y` on input `x`. -/
lemma evalProgDecompressor_produces {U : Map} {p x y : BitString} {e : ℕ}
    (hp : produces U p [] (natBits e))
    (he : Encodable.encode y ∈ (Denumerable.ofNat Nat.Partrec.Code e).eval (Encodable.encode x)) :
    produces (evalProgDecompressor U) p x y := by
  dsimp [produces, evalProgDecompressor]
  rw [Part.mem_bind_iff]
  refine ⟨natBits e, hp, ?_⟩
  dsimp [natBits]
  rw [decodeBits_natBits]
  rw [Part.mem_map_iff]
  refine ⟨Encodable.encode y, he, ?_⟩
  rw [Encodable.encodek, Option.getD_some]

/-- **Exercise 109, positive part.** `K(y | x)` does not exceed the minimal prefix
complexity of a program mapping `x` to `y`. -/
theorem condKP_le_program_KP (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x y : BitString,
      KP U y x ≤ prefixProgramComplexity U y x + (c : ℕ∞) := by
  obtain ⟨c, hc⟩ := hU.invariance (evalProgDecompressor_isPrefixDecompressor U hU)
  refine ⟨c, fun x y => ?_⟩
  unfold prefixProgramComplexity
  have h_le : ∀ v ∈ {v : ℕ∞ | ∃ e : ℕ,
      Encodable.encode y ∈ (Denumerable.ofNat Nat.Partrec.Code e).eval (Encodable.encode x) ∧
        kNat U e = v},
      KP U y x ≤ v + (c : ℕ∞) := by
    rintro v ⟨e, he, rfl⟩
    unfold kNat natBits KPPlain
    by_cases htop : KP U (Nat.bits e) [] = ⊤
    · rw [htop, top_add]
      exact le_top
    · obtain ⟨p, hp_prod, hp_len⟩ := exists_program_of_KP_ne_top htop
      have hprod_eval := evalProgDecompressor_produces hp_prod he
      have hKP_eval := KP_le_programLength_of_produces hprod_eval
      have hU_bound := hc y x
      calc KP U y x
        _ ≤ KP (evalProgDecompressor U) y x + (c : ℕ∞) := hU_bound
        _ ≤ (programLength p : ℕ∞) + (c : ℕ∞) := by gcongr
        _ = KP U (Nat.bits e) [] + (c : ℕ∞) := by rw [hp_len]
  by_cases h_emp : {v : ℕ∞ | ∃ e : ℕ,
      Encodable.encode y ∈ (Denumerable.ofNat Nat.Partrec.Code e).eval (Encodable.encode x) ∧
        kNat U e = v} = ∅
  · rw [h_emp, sInf_empty, top_add]
    exact le_top
  · obtain ⟨v₀, hv₀⟩ := Set.nonempty_iff_ne_empty.mpr h_emp
    by_cases h_top_all : ∀ v ∈ {v : ℕ∞ | ∃ e : ℕ,
      Encodable.encode y ∈ (Denumerable.ofNat Nat.Partrec.Code e).eval (Encodable.encode x) ∧
        kNat U e = v}, v = ⊤
    · have h_sInf : sInf {v : ℕ∞ | ∃ e : ℕ,
          Encodable.encode y ∈ (Denumerable.ofNat Nat.Partrec.Code e).eval (Encodable.encode x) ∧
            kNat U e = v} = ⊤ := by
        apply top_unique
        rw [le_sInf_iff]
        intro b hb
        rw [h_top_all b hb]
      rw [h_sInf, top_add]
      exact le_top
    · push_neg at h_top_all
      obtain ⟨v1, hv1_mem, hv1_ne_top⟩ := h_top_all
      have h_mem := csInf_mem (s := {v : ℕ∞ | ∃ e : ℕ,
        Encodable.encode y ∈ (Denumerable.ofNat Nat.Partrec.Code e).eval (Encodable.encode x) ∧
          kNat U e = v}) ⟨v1, hv1_mem⟩
      exact h_le _ h_mem

/-- The binary encoding `natBits` is injective on natural numbers. -/
lemma natToBits_inj {a b : ℕ} (h : natBits a = natBits b) : a = b := by
  dsimp [natBits] at h
  have h1 : decodeBits (Nat.bits a) = decodeBits (Nat.bits b) := by rw [h]
  simpa [decodeBits_natBits] using h1

/-- Abel summation for the dyadic series `∑ s n · 2⁻ⁿ` in terms of the partial sums
`A n = s 0 + ⋯ + s n`: the sum over `range (M + 1)` equals `A M · 2⁻ᴹ` plus
`∑_{n < M} A n · 2^{-(n+1)}`. -/
lemma sum_s_real_eq (s A : ℕ → ℕ) (hA0 : A 0 = s 0)
    (hA : ∀ n, A (n + 1) = A n + s (n + 1)) (M : ℕ) :
    (∑ n ∈ Finset.range (M + 1), (s n : ℝ) * (1 / 2) ^ n) =
      (A M : ℝ) * (1 / 2) ^ M +
        ∑ n ∈ Finset.range M, (A n : ℝ) * (1 / 2) ^ (n + 1) := by
  induction M with
  | zero =>
    simp [hA0]
  | succ M ih =>
    rw [Finset.sum_range_succ]
    rw [ih]
    rw [Finset.sum_range_succ]
    have hA_next : (A (M + 1) : ℝ) = (A M : ℝ) + (s (M + 1) : ℝ) := by
      exact_mod_cast hA M
    rw [hA_next]
    ring

/-- If the partial sums satisfy `2 ^ n ≤ A n` for every `n`, the dyadic series
`∑_{n ≤ M} s n · 2⁻ⁿ` is at least `(M + 2) / 2`; so the series diverges. -/
lemma real_sum_lower_bound (s A : ℕ → ℕ) (hA0 : A 0 = s 0)
    (hA : ∀ n, A (n + 1) = A n + s (n + 1))
    (h_ge : ∀ n, (2 ^ n : ℝ) ≤ (A n : ℝ)) (M : ℕ) :
    ((M : ℝ) + 2) / 2 ≤ ∑ n ∈ Finset.range (M + 1), (s n : ℝ) * (1 / 2) ^ n := by
  rw [sum_s_real_eq s A hA0 hA M]
  have h1 : 1 ≤ (A M : ℝ) * (1 / 2) ^ M := by
    calc (1 : ℝ) = (2 ^ M : ℝ) * (1 / 2) ^ M := by
          rw [← mul_pow]; norm_num
      _ ≤ (A M : ℝ) * (1 / 2) ^ M := by gcongr; exact h_ge M
  have h2 : (M : ℝ) / 2 ≤ ∑ n ∈ Finset.range M, (A n : ℝ) * (1 / 2) ^ (n + 1) := by
    have h_each : ∀ n ∈ Finset.range M, (1 / 2 : ℝ) ≤ (A n : ℝ) * (1 / 2) ^ (n + 1) := by
      intro n _
      calc (1 / 2 : ℝ) = (2 ^ n : ℝ) * (1 / 2) ^ (n + 1) := by
            rw [pow_add, pow_one, ← mul_assoc, ← mul_pow]; norm_num
        _ ≤ (A n : ℝ) * (1 / 2) ^ (n + 1) := by gcongr; exact h_ge n
    calc (M : ℝ) / 2 = ∑ n ∈ Finset.range M, (1 / 2 : ℝ) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
      _ ≤ ∑ n ∈ Finset.range M, (A n : ℝ) * (1 / 2) ^ (n + 1) := by
          gcongr with n hn
          exact h_each n hn
  linarith

/-- `ENNReal.ofReal (1 / 2) = 2⁻¹`. -/
lemma ofReal_half : ENNReal.ofReal (1 / 2 : ℝ) = (2 : ENNReal)⁻¹ := by
  have : (1 / 2 : ℝ) = 2⁻¹ := by norm_num
  rw [this, ENNReal.ofReal_inv_of_pos (by norm_num)]
  norm_num

/-- `ENNReal.ofReal 2 = 2`. -/
lemma ofReal_two : ENNReal.ofReal (2 : ℝ) = 2 := by norm_num

/-- The `ℝ≥0∞`-valued form of `real_sum_lower_bound`: partial sums bounded below by
`2 ^ n` force `∑_{n ≤ M} s n · 2⁻ⁿ` to be at least `(M + 2) / 2`. -/
lemma ennreal_sum_lower_bound (s A : ℕ → ℕ) (hA0 : A 0 = s 0)
    (hA : ∀ n, A (n + 1) = A n + s (n + 1))
    (h_ge : ∀ n, 2 ^ n ≤ A n) (M : ℕ) :
    ((M + 2 : ℕ) : ENNReal) / 2 ≤
      ∑ n ∈ Finset.range (M + 1), (s n : ENNReal) * (2 : ENNReal)⁻¹ ^ n := by
  have h_ge_real : ∀ n, (2 ^ n : ℝ) ≤ (A n : ℝ) := by
    intro n
    exact_mod_cast h_ge n
  have h_real := real_sum_lower_bound s A hA0 hA h_ge_real M
  have h_ofReal := ENNReal.ofReal_le_ofReal h_real
  have h_lhs : ENNReal.ofReal (((M : ℝ) + 2) / 2) = ((M + 2 : ℕ) : ENNReal) / 2 := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    have hM : ENNReal.ofReal ((M : ℝ) + 2) = ((M + 2 : ℕ) : ENNReal) := by
      have hM_eq : ((M : ℝ) + 2) = ((M + 2 : ℕ) : ℝ) := by push_cast; rfl
      rw [hM_eq, ENNReal.ofReal_natCast]
    rw [hM, ofReal_two]
  have h_rhs : ENNReal.ofReal (∑ n ∈ Finset.range (M + 1), (s n : ℝ) * (1 / 2) ^ n) =
      ∑ n ∈ Finset.range (M + 1), (s n : ENNReal) * (2 : ENNReal)⁻¹ ^ n := by
    rw [ENNReal.ofReal_sum_of_nonneg]
    · congr 1; ext n
      rw [ENNReal.ofReal_mul (by positivity)]
      rw [ENNReal.ofReal_natCast]
      have : ENNReal.ofReal ((1 / 2 : ℝ) ^ n) = (2 : ENNReal)⁻¹ ^ n := by
        rw [ENNReal.ofReal_pow (by norm_num), ofReal_half]
      rw [this]
    · intro n _
      positivity
  rw [h_lhs, h_rhs] at h_ofReal
  exact h_ofReal

/-- The `n`-th layer of the greedy sieve of a family of finite sets: the members of `E n`
that none of `E 0, …, E (n-1)` already contains. -/
private def sieveLayer (E : ℕ → Finset ℕ) (n : ℕ) : Finset ℕ :=
  E n \ ((List.range n).map E).toFinset.biUnion id

/-- Each sieve layer is contained in the set it was carved out of. -/
private lemma sieveLayer_subset (E : ℕ → Finset ℕ) (n : ℕ) : sieveLayer E n ⊆ E n :=
  Finset.sdiff_subset

/-- The first `n + 1` sieve layers cover exactly the union of the first `n + 1` sets. -/
private lemma sieveLayer_biUnion (E : ℕ → Finset ℕ) (n : ℕ) :
    ((List.range (n + 1)).map (sieveLayer E)).toFinset.biUnion id =
      ((List.range (n + 1)).map E).toFinset.biUnion id := by
  induction n with
  | zero =>
    ext x
    dsimp [sieveLayer]
    simp
  | succ n ih =>
    have h_range : List.range (n + 1 + 1) = List.range (n + 1) ++ [n + 1] := List.range_succ
    rw [h_range, List.map_append, List.map_singleton, List.toFinset_append, Finset.union_biUnion]
    rw [ih]
    dsimp [sieveLayer]
    ext x
    simp only [List.toFinset_cons, List.toFinset_nil, insert_empty_eq, Finset.singleton_biUnion,
      id_eq, Finset.union_sdiff_self_eq_union, Finset.mem_union, Finset.mem_biUnion,
      List.mem_toFinset, List.mem_map, List.mem_range, Order.lt_add_one_iff,
      exists_exists_and_eq_and, List.map_append, List.map_cons, List.map_nil,
      List.toFinset_append, Finset.union_singleton, Finset.biUnion_insert]
    exact or_comm

/-- The number of elements covered by the first `n + 1` sieve layers. -/
private def sieveCount (E : ℕ → Finset ℕ) (n : ℕ) : ℕ :=
  (((List.range (n + 1)).map (sieveLayer E)).toFinset.biUnion id).card

/-- At stage `0` the sieve has covered exactly the first layer. -/
private lemma sieveCount_zero (E : ℕ → Finset ℕ) :
    sieveCount E 0 = (sieveLayer E 0).card := by
  simp [sieveCount]

/-- Each stage of the sieve adds exactly the cardinality of the new layer. -/
private lemma sieveCount_succ (E : ℕ → Finset ℕ) (n : ℕ) :
    sieveCount E (n + 1) = sieveCount E n + (sieveLayer E (n + 1)).card := by
  dsimp [sieveCount]
  have h_split : ((List.range (n + 2)).map (sieveLayer E)).toFinset =
      ((List.range (n + 1)).map (sieveLayer E)).toFinset ∪ {sieveLayer E (n + 1)} := by
    rw [List.range_succ, List.map_append, List.map_singleton, List.toFinset_append]
    rfl
  have h_bi : (((List.range (n + 2)).map (sieveLayer E)).toFinset.biUnion id) =
      ((List.range (n + 1)).map (sieveLayer E)).toFinset.biUnion id ∪ (sieveLayer E (n + 1)) := by
    rw [h_split, Finset.union_biUnion, Finset.singleton_biUnion, id_eq]
  rw [h_bi]
  have h_disj : Disjoint (((List.range (n + 1)).map (sieveLayer E)).toFinset.biUnion id)
      (sieveLayer E (n + 1)) := by
    rw [Finset.disjoint_left]
    rintro x hx_union hx_S
    dsimp [sieveLayer] at hx_S
    rw [Finset.mem_sdiff] at hx_S
    have h_in_u : x ∈ ((List.range (n + 1)).map E).toFinset.biUnion id := by
      rw [← sieveLayer_biUnion E n]
      exact hx_union
    exact hx_S.2 h_in_u
  rw [Finset.card_union_of_disjoint h_disj]

/-- The sieve has covered at least the whole of `E n` by stage `n`. -/
private lemma card_le_sieveCount (E : ℕ → Finset ℕ) (n : ℕ) : (E n).card ≤ sieveCount E n := by
  dsimp [sieveCount]
  rw [sieveLayer_biUnion E n]
  refine Finset.card_le_card ?_
  intro x hx
  rw [Finset.mem_biUnion]
  refine ⟨E n, ?_, hx⟩
  rw [List.mem_toFinset, List.mem_map]
  exact ⟨n, List.mem_range.mpr (Nat.lt_succ_self n), rfl⟩

/-- A sum over the union of the first `k` sieve layers splits as a sum of sums over the
layers, which are pairwise disjoint. -/
private lemma sum_biUnion_sieveLayer {M : Type*} [AddCommMonoid M] (E : ℕ → Finset ℕ)
    (f : ℕ → M) (k : ℕ) :
    ∑ e ∈ ((List.range k).map (sieveLayer E)).toFinset.biUnion id, f e =
      ∑ n ∈ Finset.range k, ∑ e ∈ sieveLayer E n, f e := by
  induction k with
  | zero => simp [List.range_zero]
  | succ k ih =>
    have h_split : ((List.range (k + 1)).map (sieveLayer E)).toFinset =
        ((List.range k).map (sieveLayer E)).toFinset ∪ {sieveLayer E k} := by
      rw [List.range_succ, List.map_append, List.map_singleton, List.toFinset_append]
      rfl
    have h_bi : (((List.range (k + 1)).map (sieveLayer E)).toFinset.biUnion id) =
        ((List.map (sieveLayer E) (List.range k)).toFinset.biUnion id) ∪ (sieveLayer E k) := by
      rw [h_split, Finset.union_biUnion, Finset.singleton_biUnion, id_eq]
    have h_disj : Disjoint ((List.map (sieveLayer E) (List.range k)).toFinset.biUnion id)
        (sieveLayer E k) := by
      rw [Finset.disjoint_left]
      rintro x hx_union hx_S
      dsimp [sieveLayer] at hx_S
      rw [Finset.mem_sdiff] at hx_S
      have h_in_u : x ∈ ((List.range k).map E).toFinset.biUnion id := by
        cases k with
        | zero => simp [List.range_zero] at hx_union
        | succ k' =>
          rw [← sieveLayer_biUnion E k']
          exact hx_union
      exact hx_S.2 h_in_u
    rw [h_bi, Finset.sum_range_succ, ← ih, Finset.sum_union h_disj]

/-- A bound on the program complexity by a natural number is realised by an actual program of
at most that complexity. -/
private lemma exists_program_kNat_le_of_prefixProgramComplexity_le {U : Map} {y v : BitString}
    {b : ℕ} (h3 : prefixProgramComplexity U y v ≤ ((b : ℕ) : ℕ∞)) :
    ∃ e : ℕ, Encodable.encode y ∈
      (Denumerable.ofNat Nat.Partrec.Code e).eval (Encodable.encode v) ∧
      kNat U e ≤ ((b : ℕ) : ℕ∞) := by
  unfold prefixProgramComplexity at h3
  by_cases h_emp : {w : ℕ∞ | ∃ e : ℕ,
      Encodable.encode y ∈
        (Denumerable.ofNat Nat.Partrec.Code e).eval (Encodable.encode v) ∧
        kNat U e = w} = ∅
  · rw [h_emp, sInf_empty] at h3
    contradiction
  · have h_mem := csInf_mem (s := {w : ℕ∞ | ∃ e : ℕ,
        Encodable.encode y ∈
          (Denumerable.ofNat Nat.Partrec.Code e).eval (Encodable.encode v) ∧
          kNat U e = w}) (Set.nonempty_iff_ne_empty.mpr h_emp)
    rcases h_mem with ⟨e, he, he_eq⟩
    refine ⟨e, he, ?_⟩
    rw [he_eq]
    exact h3

/-- A program of complexity at most `m` carries complexity weight at least `2⁻¹ ^ m`. -/
private lemma inv_two_pow_le_complexityWeight_of_kNat_le {U : Map} {e m : ℕ}
    (h_le : kNat U e ≤ ((m : ℕ) : ℕ∞)) :
    (2 : ENNReal)⁻¹ ^ m ≤ complexityWeight (kNat U e) := by
  unfold kNat KPPlain natBits at h_le ⊢
  by_cases htop : KP U (Nat.bits e) [] = ⊤
  · rw [htop] at h_le
    contradiction
  · obtain ⟨k_val, hk_val⟩ := WithTop.ne_top_iff_exists.mp htop
    rw [← hk_val] at h_le ⊢
    have hk_le : k_val ≤ m := WithTop.coe_le_coe.mp h_le
    unfold complexityWeight
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hk_le
    rw [hd]
    have h1 : (2 : ENNReal)⁻¹ ^ (k_val + d) =
      (2 : ENNReal)⁻¹ ^ k_val * (2 : ENNReal)⁻¹ ^ d := pow_add _ _ _
    rw [h1]
    have h2 : (2 : ENNReal)⁻¹ ^ d ≤ 1 := pow_le_one' (ENNReal.inv_le_one.mpr one_le_two) d
    calc (2 : ENNReal)⁻¹ ^ k_val * (2 : ENNReal)⁻¹ ^ d
      _ ≤ (2 : ENNReal)⁻¹ ^ k_val * 1 := by gcongr
      _ = (2 : ENNReal)⁻¹ ^ k_val := mul_one _

/-- Multiplying a weight at level `n + C` by `2 ^ C` shifts it to level `n`. -/
private lemma two_pow_mul_mul_inv_two_pow_add (C n : ℕ) (x : ENNReal) :
    (2 : ENNReal) ^ C * (x * (2 : ENNReal)⁻¹ ^ (n + C)) = x * (2 : ENNReal)⁻¹ ^ n := by
  have h_cancel : (2 : ENNReal) ^ C * (2 : ENNReal)⁻¹ ^ C = 1 := by
    rw [← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow]
  rw [pow_add]
  calc (2 : ENNReal) ^ C * (x * ((2 : ENNReal)⁻¹ ^ n * (2 : ENNReal)⁻¹ ^ C))
    _ = ((2 : ENNReal) ^ C * (2 : ENNReal)⁻¹ ^ C) * (x * (2 : ENNReal)⁻¹ ^ n) := by ring
    _ = x * (2 : ENNReal)⁻¹ ^ n := by rw [h_cancel, one_mul]

/-- **Exercise 109, converse part.** The converse inequality fails. -/
theorem not_program_KP_le_condKP (U : Map) (hU : IsOptimalPrefixConditional U) :
    ¬ ∃ c : ℕ, ∀ x y : BitString,
      prefixProgramComplexity U y x ≤ KP U y x + (c : ℕ∞) := by
  intro ⟨c_conv, h_conv⟩
  obtain ⟨c_len, h_len⟩ := KP_le_length_given_natBits_length U hU
  set C := c_len + c_conv
  have h_bound : ∀ (n : ℕ) (y : BitString), y.length = n →
      ∃ e : ℕ, Encodable.encode y ∈
        (Denumerable.ofNat Nat.Partrec.Code e).eval (Encodable.encode (natBits n)) ∧
        kNat U e ≤ ((n + C : ℕ) : ℕ∞) := by
    intro n y hy
    have h1 : KP U y (natBits n) ≤ (n : ℕ∞) + (c_len : ℕ∞) := by
      rw [← hy]
      exact h_len y
    have h2 : prefixProgramComplexity U y (natBits n) ≤ KP U y (natBits n) + (c_conv : ℕ∞) :=
      h_conv (natBits n) y
    have h3 : prefixProgramComplexity U y (natBits n) ≤ ((n + C : ℕ) : ℕ∞) := by
      calc prefixProgramComplexity U y (natBits n)
        _ ≤ KP U y (natBits n) + (c_conv : ℕ∞) := h2
        _ ≤ (n : ℕ∞) + (c_len : ℕ∞) + (c_conv : ℕ∞) := by gcongr
        _ = ((n + C : ℕ) : ℕ∞) := by
          have h_add : n + c_len + c_conv = n + (c_len + c_conv) := by rw [add_assoc]
          exact_mod_cast h_add
    exact exists_program_kNat_le_of_prefixProgramComplexity_le h3
  have h_find : ∀ (n : ℕ) (y : BitString) (hy : y.length = n),
      ∃ e : ℕ, Encodable.encode y ∈
        (Denumerable.ofNat Nat.Partrec.Code e).eval (Encodable.encode (natBits n)) ∧
        kNat U e ≤ ((n + C : ℕ) : ℕ∞) := fun n y hy => h_bound n y hy
  choose e_fn he_fn using h_find
  have h_inj : ∀ (n : ℕ) (y1 y2 : BitString) (h1 : y1.length = n) (h2 : y2.length = n),
      e_fn n y1 h1 = e_fn n y2 h2 → y1 = y2 := by
    intro n y1 y2 h1 h2 heq
    have hy1 := (he_fn n y1 h1).1
    have hy2 := (he_fn n y2 h2).1
    rw [heq] at hy1
    have h_det : ∀ (e : Nat.Partrec.Code) (w : ℕ) (a b : ℕ),
        a ∈ e.eval w → b ∈ e.eval w → a = b := by
      intro e w a b ha hb
      exact Part.mem_unique ha hb
    have h_enc_eq := h_det (Denumerable.ofNat Nat.Partrec.Code (e_fn n y2 h2))
      (Encodable.encode (natBits n)) (Encodable.encode y1) (Encodable.encode y2) hy1 hy2
    exact Encodable.encode_injective h_enc_eq
  have h_weight (n : ℕ) (y : BitString) (hy : y.length = n) :
      (2 : ENNReal)⁻¹ ^ (n + C) ≤ complexityWeight (kNat U (e_fn n y hy)) :=
    inv_two_pow_le_complexityWeight_of_kNat_le (he_fn n y hy).2
  have h_mem_len (n : ℕ) (y : BitString) (hy : y ∈ (allStrings n).toFinset) : y.length = n := by
    rw [List.mem_toFinset, mem_allStrings] at hy
    exact hy
  let E_set (n : ℕ) : Finset ℕ :=
    (allStrings n).toFinset.attach.image (fun ⟨y, hy⟩ => e_fn n y (h_mem_len n y hy))
  have h_E_card (n : ℕ) : (E_set n).card = 2 ^ n := by
    dsimp [E_set]
    rw [Finset.card_image_of_injOn]
    · rw [Finset.card_attach, List.toFinset_card_of_nodup (allStrings_nodup n), length_allStrings]
    · rintro ⟨y1, hy1⟩ _ ⟨y2, hy2⟩ _ heq
      dsimp at heq
      have hy_eq := h_inj n y1 y2 (h_mem_len n y1 hy1) (h_mem_len n y2 hy2) heq
      exact Subtype.ext hy_eq
  let S_seq : ℕ → Finset ℕ := sieveLayer E_set
  let A_seq : ℕ → ℕ := sieveCount E_set
  have h_S_sub (n : ℕ) : S_seq n ⊆ E_set n := sieveLayer_subset E_set n
  have h_A_union (n : ℕ) :
      ((List.range (n + 1)).map S_seq).toFinset.biUnion id =
        ((List.range (n + 1)).map E_set).toFinset.biUnion id := sieveLayer_biUnion E_set n
  have h_A0 : A_seq 0 = (S_seq 0).card := sieveCount_zero E_set
  have h_A_step (n : ℕ) : A_seq (n + 1) = A_seq n + (S_seq (n + 1)).card :=
    sieveCount_succ E_set n
  have h_A_ge (n : ℕ) : 2 ^ n ≤ A_seq n := by
    have h := card_le_sieveCount E_set n
    rwa [h_E_card n] at h
  have h_S_weight (n : ℕ) (e : ℕ) (he : e ∈ S_seq n) :
      (2 : ENNReal)⁻¹ ^ (n + C) ≤ complexityWeight (KPPlain U (natBits e)) := by
    have he_E : e ∈ E_set n := h_S_sub n he
    dsimp [E_set] at he_E
    rw [Finset.mem_image] at he_E
    rcases he_E with ⟨⟨y, hy⟩, _, rfl⟩
    exact h_weight n y (h_mem_len n y hy)
  have h_S_sum (n : ℕ) :
      ((S_seq n).card : ENNReal) * (2 : ENNReal)⁻¹ ^ (n + C) ≤
        ∑ e ∈ S_seq n, complexityWeight (KPPlain U (natBits e)) := by
    calc ((S_seq n).card : ENNReal) * (2 : ENNReal)⁻¹ ^ (n + C)
      _ = ∑ e ∈ S_seq n, (2 : ENNReal)⁻¹ ^ (n + C) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ e ∈ S_seq n, complexityWeight (KPPlain U (natBits e)) := by
        gcongr with e he
        exact h_S_weight n e he
  set M := 2 * 2 ^ C
  have h_enn_bound :=
    ennreal_sum_lower_bound (fun n => (S_seq n).card) A_seq h_A0 h_A_step h_A_ge M
  have h_pow (n : ℕ) :
      (2 : ENNReal) ^ C * (((S_seq n).card : ENNReal) * (2 : ENNReal)⁻¹ ^ (n + C)) =
      ((S_seq n).card : ENNReal) * (2 : ENNReal)⁻¹ ^ n :=
    two_pow_mul_mul_inv_two_pow_add C n _
  have h_biUnion_sum (k : ℕ) :
      ∑ e ∈ ((List.range k).map S_seq).toFinset.biUnion id,
          complexityWeight (KPPlain U (natBits e)) =
        ∑ n ∈ Finset.range k, ∑ e ∈ S_seq n, complexityWeight (KPPlain U (natBits e)) :=
    sum_biUnion_sieveLayer E_set (fun e => complexityWeight (KPPlain U (natBits e))) k
  have h_sum_S_union :
      ∑ n ∈ Finset.range (M + 1), ((S_seq n).card : ENNReal) * (2 : ENNReal)⁻¹ ^ n ≤
        (2 : ENNReal) ^ C * ∑ e ∈ ((List.range (M + 1)).map S_seq).toFinset.biUnion id,
          complexityWeight (KPPlain U (natBits e)) := by
    rw [h_biUnion_sum (M + 1), Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n _
    rw [← h_pow n]
    gcongr
    exact h_S_sum n
  have h_inj_bits : Function.Injective (fun e : ℕ => natBits e) := by
    intro a b hab
    exact natToBits_inj hab
  have h_union_kraft :
      ∑ e ∈ ((List.range (M + 1)).map S_seq).toFinset.biUnion id,
        complexityWeight (KPPlain U (natBits e)) ≤
        ∑' x : BitString, complexityWeight (KPPlain U x) := by
    rw [← Finset.sum_image (f := fun x => complexityWeight (KPPlain U x)) (g := natBits)
      (by intro a _ b _ hab; exact h_inj_bits hab)]
    exact ENNReal.sum_le_tsum _
  have h_kraft := KPPlain_kraft_sum_le_one U hU.isPrefixDecompressor
  have h_total_bound :
      ((M + 2 : ℕ) : ENNReal) / 2 ≤ (2 : ENNReal) ^ C * 1 := by
    calc ((M + 2 : ℕ) : ENNReal) / 2
      _ ≤ ∑ n ∈ Finset.range (M + 1), ((S_seq n).card : ENNReal) * (2 : ENNReal)⁻¹ ^ n :=
          h_enn_bound
      _ ≤ (2 : ENNReal) ^ C * ∑ e ∈ ((List.range (M + 1)).map S_seq).toFinset.biUnion id,
          complexityWeight (KPPlain U (natBits e)) := h_sum_S_union
      _ ≤ (2 : ENNReal) ^ C * ∑' x : BitString, complexityWeight (KPPlain U x) := by gcongr
      _ ≤ (2 : ENNReal) ^ C * 1 := by gcongr
  dsimp [M] at h_total_bound
  have h_div : (((2 * 2 ^ C + 2 : ℕ) : ENNReal)) / 2 = (2 : ENNReal) ^ C + 1 := by
    have h2 : (2 : ENNReal) ≠ 0 := by norm_num
    have h2_top : (2 : ENNReal) ≠ ⊤ := by norm_num
    calc (((2 * 2 ^ C + 2 : ℕ) : ENNReal)) / 2
      _ = (2 * (2 : ENNReal) ^ C + 2) / 2 := by push_cast; rfl
      _ = ((2 : ENNReal) ^ C + 1) * 2 / 2 := by ring_nf
      _ = (2 : ENNReal) ^ C + 1 := by rw [ENNReal.mul_div_cancel_right h2 h2_top]
  rw [h_div] at h_total_bound
  rw [mul_one] at h_total_bound
  have h_gt : (2 : ENNReal) ^ C < (2 : ENNReal) ^ C + 1 := by
    have h2C_ne_top : (2 : ENNReal) ^ C ≠ ⊤ := by norm_num
    exact ENNReal.lt_add_right h2C_ne_top (by norm_num)
  exact lt_irrefl ((2 : ENNReal) ^ C + 1) (lt_of_le_of_lt h_total_bound h_gt)

/-- **Exercise 111.** The triangle inequality for conditional prefix
complexity. -/
theorem condKP_triangle (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x y z : BitString, KP U x z ≤ KP U x y + KP U y z + (c : ℕ∞) := by
  let ctx : BitString → BitString → Nat → BitString := fun _ y _ => y
  have hctx : Computable (fun p : (BitString × BitString) × ℕ => ctx p.1.1 p.1.2 p.2) :=
    Computable.snd.comp Computable.fst
  have hD_decomp := condTwoStagePairBuilder_isDecompressor hU.isDecompressor hU.isPrefixMachine hctx
  have hD_prefix := condTwoStagePairBuilder_isPrefixMachine (ctx := ctx) hU.isPrefixMachine
  let D := condTwoStagePairBuilder U ctx
  have hD : IsPrefixDecompressor D := ⟨hD_decomp, hD_prefix⟩
  obtain ⟨c_inv, hc_inv⟩ := hU.invariance hD
  obtain ⟨c_map, hc_map⟩ := KP_map_le U hU decodeSecond decodeSecond_computable
  use c_inv + c_map
  intro x y z
  by_cases hxy : KP U x y = ⊤
  · rw [hxy, top_add, top_add]; exact le_top
  by_cases hyz : KP U y z = ⊤
  · rw [hyz, add_top, top_add]; exact le_top
  obtain ⟨p, hp, hplen⟩ := exists_program_of_KP_ne_top (M := U) (x := x) (y := y) hxy
  obtain ⟨q, hq, hqlen⟩ := exists_program_of_KP_ne_top (M := U) (x := y) (y := z) hyz
  have hq' : produces U p (ctx z y q.length) x := hp
  have hbound := KP_condTwoStagePairBuilder_le_of_produces
    (U := U) (ctx := ctx) hU.isPrefixMachine hq hq'
  have hD_le : KP D (pairCode y x) z ≤ KP U x y + KP U y z := by
    calc
      KP D (pairCode y x) z ≤ ((q.length + p.length : ℕ) : ENat) := hbound
      _ = (q.length : ENat) + (p.length : ENat) := by norm_cast
      _ = KP U y z + KP U x y := by rw [hqlen, hplen]
      _ = KP U x y + KP U y z := add_comm _ _
  calc
    KP U x z = KP U (decodeSecond (pairCode y x)) z := by rw [decodeSecond_pairCode]
    _ ≤ KP U (pairCode y x) z + (c_map : ENat) := hc_map (pairCode y x) z
    _ ≤ (KP D (pairCode y x) z + (c_inv : ENat)) + (c_map : ENat) := by
      gcongr
      exact hc_inv (pairCode y x) z
    _ ≤ (KP U x y + KP U y z) + (c_inv : ENat) + (c_map : ENat) := by
      gcongr
    _ = KP U x y + KP U y z + ((c_inv + c_map : ℕ) : ENat) := by
      rw [Nat.cast_add]
      ac_rfl

/-- Reassociation of a nested pair code: `⟨x, ⟨y, z⟩⟩` is turned into the triple code
`⟨x, ⟨y, ⟨z, []⟩⟩⟩`. -/
def tripleCodeOfNestedPair (w : BitString) : BitString :=
  pairCode (decodeFirst w)
    (pairCode (decodeFirst (decodeSecond w))
      (pairCode (decodeSecond (decodeSecond w)) []))

private lemma tripleCodeOfNestedPair_computable : Computable tripleCodeOfNestedPair := by
  apply Computable.of_eq
    (pairCode_computable.comp
      (decodeFirst_computable.pair
        (pairCode_computable.comp
          ((decodeFirst_computable.comp decodeSecond_computable).pair
            (pairCode_computable.comp
              ((decodeSecond_computable.comp decodeSecond_computable).pair
                (Computable.const [])))))))
  intro w
  rfl

/-- Reassociation with a swap: `⟨⟨x, y⟩, z⟩` is turned into the triple code
`⟨z, ⟨x, ⟨y, []⟩⟩⟩`. -/
def tripleCodeOfSwappedPair (w : BitString) : BitString :=
  pairCode (decodeSecond w)
    (pairCode (decodeFirst (decodeFirst w))
      (pairCode (decodeSecond (decodeFirst w)) []))

private lemma tripleCodeOfSwappedPair_computable : Computable tripleCodeOfSwappedPair := by
  apply Computable.of_eq
    (pairCode_computable.comp
      (decodeSecond_computable.pair
        (pairCode_computable.comp
          ((decodeFirst_computable.comp decodeFirst_computable).pair
            (pairCode_computable.comp
              ((decodeSecond_computable.comp decodeFirst_computable).pair
                (Computable.const [])))))))
  intro w
  rfl

/-- **Exercise 114.** The prefix version of the basic triple inequality:
`2 K(x, y, z) ≤ K(x, y) + K(x, z) + K(y, z) + O(1)`. -/
theorem two_mul_KP_triple_le (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x y z : BitString,
      2 * KPTriple U x y z ≤ KPPair U x y + KPPair U x z + KPPair U y z + (c : ℕ∞) := by
  obtain ⟨c_map_A, h_map_A⟩ :=
    KPPlain_map_le U hU tripleCodeOfNestedPair tripleCodeOfNestedPair_computable
  obtain ⟨c_map_B, h_map_B⟩ :=
    KPPlain_map_le U hU tripleCodeOfSwappedPair tripleCodeOfSwappedPair_computable
  obtain ⟨c_chain_upper, h_chain_upper⟩ := KPPair_chain_upper U hU
  obtain ⟨c_chain_w, h_chain_w⟩ := KPPair_chain_upper_weak U hU
  obtain ⟨c_upper_cond, h_upper_cond⟩ := KPCondPair_chain_upper U hU
  obtain ⟨c_drop_r, h_drop_r⟩ := KP_cond_drop_right_le U hU
  obtain ⟨c_lower_plain, h_lower_plain⟩ := KPPair_chain_lower U hU
  obtain ⟨c_drop, h_drop⟩ := KP_le_KPPlain U hU
  let C1 := 2 * c_lower_plain + c_upper_cond + c_drop_r + c_chain_upper + c_map_A
  let C2 := c_map_B + c_chain_w + c_drop
  let C := C1 + C2
  have h_C_cast : (C1 : ℕ∞) + (C2 : ℕ∞) = (C : ℕ∞) := by
    dsimp [C]
    push_cast
    rfl
  refine ⟨C, fun x y z => ?_⟩
  have h_kx : KPPlain U x ≠ ⊤ := KPPlain_ne_top_of_optimal U hU x
  set kx := (KPPlain U x).toNat
  have hkx : HasPrefixComplexityValue U x kx := ENat.coe_toNat h_kx
  set w := prefixComplexityContext x kx
  by_cases h_ky : KP U y w = ⊤
  · have h_xy : KPPair U x y = ⊤ := by
      have h1 := h_lower_plain x y kx hkx
      rw [h_ky, add_top] at h1
      have h2 : (KPPair U x y + (c_lower_plain : ℕ∞)) = ⊤ := top_unique h1
      cases h_xy_eq : KPPair U x y with
      | top => rfl
      | coe n =>
        rw [h_xy_eq] at h2
        have h_fin : (n : ℕ∞) + (c_lower_plain : ℕ∞) ≠ ⊤ := ENat.coe_ne_top _
        exact False.elim (h_fin h2)
    rw [h_xy]
    simp
  · set ky := (KP U y w).toNat
    have hky : HasCondPrefixComplexityValue U y w ky := ENat.coe_toNat h_ky
    have hA : KPPlain U x + KPTriple U x y z ≤ KPPair U x y + KPPair U x z + (C1 : ℕ∞) := by
      have hfA : tripleCodeOfNestedPair (pairCode x (pairCode y z)) = listCode [x, y, z] := by
        dsimp [tripleCodeOfNestedPair, listCode]
        simp [decodeFirst_pairCode, decodeSecond_pairCode]
      have s1 : KPTriple U x y z ≤ KPPair U x (pairCode y z) + (c_map_A : ℕ∞) := by
        rw [KPTriple, ← hfA]
        exact h_map_A (pairCode x (pairCode y z))
      have s2 : KPPair U x (pairCode y z) ≤
          KPPlain U x + KPCondPair U y z w + (c_chain_upper : ℕ∞) :=
        h_chain_upper x (pairCode y z) kx hkx
      have s3 : KPCondPair U y z w ≤
          KP U y w + KP U z (prefixCondComplexityContext w y ky) + (c_upper_cond : ℕ∞) :=
        h_upper_cond y z w ky hky
      have s4 : KP U z (prefixCondComplexityContext w y ky) ≤ KP U z w + (c_drop_r : ℕ∞) :=
        h_drop_r z w (pairCode y (natCode ky))
      have s_xy : KPPlain U x + KP U y w ≤ KPPair U x y + (c_lower_plain : ℕ∞) :=
        h_lower_plain x y kx hkx
      have s_xz : KPPlain U x + KP U z w ≤ KPPair U x z + (c_lower_plain : ℕ∞) :=
        h_lower_plain x z kx hkx
      calc KPPlain U x + KPTriple U x y z
          ≤ KPPlain U x + (KPPair U x (pairCode y z) + (c_map_A : ℕ∞)) :=
            add_le_add (le_refl _) s1
        _ ≤ KPPlain U x + ((KPPlain U x + KPCondPair U y z w + (c_chain_upper : ℕ∞)) +
            (c_map_A : ℕ∞)) := by gcongr
        _ ≤ KPPlain U x + ((KPPlain U x + (KP U y w + KP U z (prefixCondComplexityContext w y ky) +
            (c_upper_cond : ℕ∞)) + (c_chain_upper : ℕ∞)) + (c_map_A : ℕ∞)) := by gcongr
        _ ≤ KPPlain U x + ((KPPlain U x + (KP U y w + (KP U z w + (c_drop_r : ℕ∞)) +
            (c_upper_cond : ℕ∞)) + (c_chain_upper : ℕ∞)) + (c_map_A : ℕ∞)) := by gcongr
        _ = (KPPlain U x + KP U y w) + (KPPlain U x + KP U z w) +
            ((c_upper_cond + c_drop_r + c_chain_upper + c_map_A : ℕ) : ℕ∞) := by
            push_cast; ring_nf
        _ ≤ (KPPair U x y + (c_lower_plain : ℕ∞)) + (KPPair U x z + (c_lower_plain : ℕ∞)) +
            ((c_upper_cond + c_drop_r + c_chain_upper + c_map_A : ℕ) : ℕ∞) := by gcongr
        _ = KPPair U x y + KPPair U x z + (C1 : ℕ∞) := by
            dsimp [C1]
            push_cast; ring_nf
    have hB : KPTriple U x y z ≤ KPPair U y z + KPPlain U x + (C2 : ℕ∞) := by
      have hfB : tripleCodeOfSwappedPair (pairCode (pairCode y z) x) = listCode [x, y, z] := by
        dsimp [tripleCodeOfSwappedPair, listCode]
        simp [decodeFirst_pairCode, decodeSecond_pairCode]
      have s1 : KPTriple U x y z ≤ KPPair U (pairCode y z) x + (c_map_B : ℕ∞) := by
        rw [KPTriple, ← hfB]
        exact h_map_B (pairCode (pairCode y z) x)
      have s2 : KPPair U (pairCode y z) x ≤ KPPair U y z + KP U x (pairCode y z) +
          (c_chain_w : ℕ∞) :=
        h_chain_w (pairCode y z) x
      have s3 : KP U x (pairCode y z) ≤ KPPlain U x + (c_drop : ℕ∞) :=
        h_drop x (pairCode y z)
      calc KPTriple U x y z
          ≤ KPPair U (pairCode y z) x + (c_map_B : ℕ∞) := s1
        _ ≤ (KPPair U y z + KP U x (pairCode y z) + (c_chain_w : ℕ∞)) + (c_map_B : ℕ∞) :=
            add_le_add s2 (le_refl (c_map_B : ℕ∞))
        _ ≤ (KPPair U y z + (KPPlain U x + (c_drop : ℕ∞)) + (c_chain_w : ℕ∞)) + (c_map_B : ℕ∞) := by
            gcongr
        _ = KPPair U y z + KPPlain U x + (C2 : ℕ∞) := by
            dsimp [C2]
            push_cast; ring_nf
    have h_two : 2 * KPTriple U x y z = KPTriple U x y z + KPTriple U x y z := two_mul _
    have h_sum : KPPlain U x + 2 * KPTriple U x y z ≤
        KPPlain U x + (KPPair U x y + KPPair U x z + KPPair U y z + (C : ℕ∞)) := by
      calc KPPlain U x + 2 * KPTriple U x y z
          = (KPPlain U x + KPTriple U x y z) + KPTriple U x y z := by rw [h_two]; ring
        _ ≤ (KPPair U x y + KPPair U x z + (C1 : ℕ∞)) + (KPPair U y z + KPPlain U x + (C2 : ℕ∞)) :=
            add_le_add hA hB
        _ = KPPlain U x + (KPPair U x y + KPPair U x z + KPPair U y z + (C : ℕ∞)) := by
            rw [← h_C_cast]
            ring
    exact WithTop.add_le_add_iff_left h_kx |>.mp h_sum

/-- **Exercise 115.** For every `x` and `n` there is a string `y` of length `n`
with `K(x, y) ≥ K(x) + n - O(1)`. -/
theorem exists_extension_KP_pair_ge (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (n : ℕ), ∃ y : BitString, y.length = n ∧
      KPPlain U x + (n : ℕ∞) ≤ KPPair U x y + (c : ℕ∞) := by
  obtain ⟨c, hc⟩ := KPPair_chain_lower U hU
  obtain ⟨c_left, h_left⟩ := KPPlain_left_le_KPPair U hU
  refine ⟨c + c_left, fun x n => ?_⟩
  by_cases hKx : KPPlain U x = ⊤
  · refine ⟨List.replicate n false, by simp, ?_⟩
    have h_top := h_left x (List.replicate n false)
    rw [hKx] at h_top
    rw [hKx, top_add]
    exact h_top.trans (by gcongr; exact Nat.le_add_left _ _)
  · have hkx : HasPrefixComplexityValue U x (KPPlain U x).toNat :=
      ENat.coe_toNat hKx
    let ctx := prefixComplexityContext x (KPPlain U x).toNat
    have h_ex : ∃ y ∈ stringsOfLength n, (n : ℕ∞) ≤ KP U y ctx := by
      by_contra h_all
      push_neg at h_all
      by_cases hn : n = 0
      · subst hn
        have h_nil : [] ∈ stringsOfLength 0 := by simp [mem_stringsOfLength]
        have h0 := h_all [] h_nil
        exact not_lt_bot h0
      · have h_sum_le : ∑ y ∈ stringsOfLength n, complexityWeight (KP U y ctx) ≤ 1 := by
          calc ∑ y ∈ stringsOfLength n, complexityWeight (KP U y ctx)
            _ ≤ ∑' y : BitString, complexityWeight (KP U y ctx) :=
                ENNReal.sum_le_tsum _
            _ ≤ ∑' y : BitString, aprioriMeasure U y ctx :=
                ENNReal.tsum_le_tsum (fun y => complexityWeight_KP_le_aprioriMeasure U y ctx)
            _ ≤ 1 := tsum_aprioriMeasure_le_one U ctx hU.isPrefixMachine
        have h_elem : ∀ y ∈ stringsOfLength n,
            (2 : ℝ≥0∞)⁻¹ ^ (n - 1) ≤ complexityWeight (KP U y ctx) := by
          intro y hy
          have h_lt := h_all y hy
          have h_le : KP U y ctx ≤ ((n - 1 : ℕ) : ℕ∞) := by
            obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_lt h_lt)
            have h_lt' : k < n := by exact_mod_cast (hk ▸ h_lt)
            have h_le' : k ≤ n - 1 := Nat.le_pred_of_lt h_lt'
            exact hk ▸ (Nat.cast_le.mpr h_le')
          have h_cw := complexityWeight_le_of_le h_le
          rw [complexityWeight_coe] at h_cw
          exact h_cw
        have h_sum_ge : (2 : ℝ≥0∞) ^ n * (2 : ℝ≥0∞)⁻¹ ^ (n - 1) ≤
            ∑ y ∈ stringsOfLength n, complexityWeight (KP U y ctx) := by
          have h_sum := Finset.sum_le_sum h_elem
          rw [Finset.sum_const, card_stringsOfLength, nsmul_eq_mul] at h_sum
          rw [Nat.cast_pow, Nat.cast_ofNat] at h_sum
          exact h_sum
        have h_two : (2 : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ n * (2 : ℝ≥0∞)⁻¹ ^ (n - 1) := by
          have hn_pos : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn)
          have h_eq : n = (n - 1) + 1 := (Nat.sub_add_cancel hn_pos).symm
          have h_mul : (2 : ℝ≥0∞) ^ (n - 1) * (2 : ℝ≥0∞)⁻¹ ^ (n - 1) = 1 := by
            rw [← mul_pow, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow]
          have h_step : (2 : ℝ≥0∞) = (2 : ℝ≥0∞) ^ n * (2 : ℝ≥0∞)⁻¹ ^ (n - 1) := by
            calc (2 : ℝ≥0∞)
              _ = (2 : ℝ≥0∞) ^ 1 * 1 := by rw [pow_one, mul_one]
              _ = (2 : ℝ≥0∞) ^ 1 * ((2 : ℝ≥0∞) ^ (n - 1) * (2 : ℝ≥0∞)⁻¹ ^ (n - 1)) := by rw [h_mul]
              _ = ((2 : ℝ≥0∞) ^ (n - 1) * (2 : ℝ≥0∞) ^ 1) * (2 : ℝ≥0∞)⁻¹ ^ (n - 1) := by ring
              _ = (2 : ℝ≥0∞) ^ n * (2 : ℝ≥0∞)⁻¹ ^ (n - 1) := by rw [← pow_add, ← h_eq]
          exact h_step.le
        have h_contra : (2 : ℝ≥0∞) ≤ 1 := h_two.trans (h_sum_ge.trans h_sum_le)
        exact absurd h_contra (by norm_num)
    obtain ⟨y, hy_mem, hy_ge⟩ := h_ex
    have hy_len : y.length = n := (mem_stringsOfLength n y).mp hy_mem
    refine ⟨y, hy_len, ?_⟩
    have h_lower := hc x y (KPPlain U x).toNat hkx
    calc KPPlain U x + (n : ℕ∞)
      _ ≤ KPPlain U x + KP U y ctx := by gcongr
      _ ≤ KPPair U x y + (c : ℕ∞) := h_lower
      _ ≤ KPPair U x y + ((c + c_left : ℕ) : ℕ∞) := by gcongr; exact Nat.le_add_right _ _

end Kolmogorov
