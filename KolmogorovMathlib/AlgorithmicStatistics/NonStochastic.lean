/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/

import KolmogorovMathlib.AlgorithmicProbability.PairProjection
import KolmogorovMathlib.AlgorithmicStatistics.FiniteSetModel
import KolmogorovMathlib.AlgorithmicStatistics.Stochasticity
import KolmogorovMathlib.Foundation.RecursivelyEnumerable
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
/-!
# Non-Stochastic Skeleton

This module defines abstract level-set cover lemmas and non-stochastic existence.
The numerical gap follows the SUV/arXiv finite-set route:
`2 * alpha + beta + O(log n) < n`.
-/

namespace Kolmogorov

open scoped ENNReal

theorem length_exactLengthPrograms (n : Nat) : (exactLengthPrograms n).length = 2 ^ n := by
  induction n with
  | zero => simp [exactLengthPrograms]
  | succ n ih => simp [exactLengthPrograms, ih, Nat.pow_succ, Nat.mul_comm]

theorem boundedPrograms_succ (n : Nat) :
    boundedPrograms (n + 1) = boundedPrograms n ++ exactLengthPrograms (n + 1) := by
  unfold boundedPrograms
  rw [List.range_succ]
  simp [List.flatMap_append]

theorem length_boundedPrograms_le (n : Nat) : (boundedPrograms n).length ≤ 2 ^ (n + 1) := by
  induction n with
  | zero => simp [boundedPrograms, length_exactLengthPrograms]
  | succ n ih =>
      rw [boundedPrograms_succ, List.length_append, length_exactLengthPrograms]
      calc
        (boundedPrograms n).length + 2 ^ (n + 1)
            ≤ 2 ^ (n + 1) + 2 ^ (n + 1) := Nat.add_le_add_right ih _
        _ = 2 ^ (n + 1 + 1) := by
            rw [Nat.pow_succ]
            omega

/-- The output of a program, with a fixed dummy value for non-halting programs.
This is only used inside finite images of bounded program lists. -/
noncomputable def modelCodeOfProgram (U : Map) (p : BitString) : BitString := by
  classical
  exact if h : (U (p, [])).Dom then (U (p, [])).get h else []

/-- Finite enumeration of model codes produced by programs of length `<= alpha`. -/
noncomputable def modelsWithComplexityLe (U : Map) (alpha : ℕ) : Finset BitString := by
  classical
  exact (boundedPrograms alpha).toFinset.image (modelCodeOfProgram U)

/-- The number of model codes of complexity `<= alpha` is bounded. -/
theorem card_modelsWithComplexityLe (U : Map) (alpha : ℕ) :
    (modelsWithComplexityLe U alpha).card ≤ 2 ^ (alpha + 1) := by
  unfold modelsWithComplexityLe
  refine le_trans Finset.card_image_le ?_
  rw [List.toFinset_card_of_nodup (boundedPrograms_nodup alpha)]
  exact length_boundedPrograms_le alpha

/-- The code of any model of complexity `≤ alpha` appears in the finite
enumeration `modelsWithComplexityLe`. -/
theorem code_mem_modelsWithComplexityLe (U : Map) (P : CodedFiniteDistribution)
    (alpha : ℕ) (hcomp : P.complexity U ≤ (alpha : ENat)) :
    P.code ∈ modelsWithComplexityLe U alpha := by
  classical
  have hne : KP U P.code [] ≠ ⊤ := by
    intro htop
    rw [CodedFiniteDistribution.complexity, KPPlain_eq_KP, htop] at hcomp
    exact (not_le.mpr (by exact_mod_cast ENat.coe_lt_top alpha)) hcomp
  obtain ⟨p, hp_prod, hp_len⟩ := exists_program_of_KP_ne_top hne
  have hlen : p.length ≤ alpha := by
    have : (programLength p : ENat) ≤ (alpha : ENat) := by
      rw [hp_len]; rw [CodedFiniteDistribution.complexity, KPPlain_eq_KP] at hcomp; exact hcomp
    have := (Nat.cast_le (α := ENat)).mp this
    simpa [programLength] using this
  have hmem : p ∈ boundedPrograms alpha := (mem_boundedPrograms_iff p alpha).mpr hlen
  have hcode : modelCodeOfProgram U p = P.code := by
    have hdom : (U (p, [])).Dom := hp_prod.1
    unfold modelCodeOfProgram
    rw [dif_pos hdom]
    exact hp_prod.2
  unfold modelsWithComplexityLe
  rw [Finset.mem_image]
  exact ⟨p, List.mem_toFinset.mpr hmem, hcode⟩

/-- A chosen probability model carrying a given code, defaulting to a Dirac model
when no probability model has that code. -/
noncomputable def probModelOfCode (c : BitString) : CodedFiniteDistribution := by
  classical
  exact if h : ∃ P : CodedFiniteDistribution, P.code = c ∧ P.IsProbability then h.choose
    else codedDirac []

theorem probModelOfCode_isProbability (c : BitString) :
    (probModelOfCode c).IsProbability := by
  classical
  unfold probModelOfCode
  split
  · rename_i h; exact h.choose_spec.2
  · exact codedDirac_isProbability []

theorem probModelOfCode_eq {P : CodedFiniteDistribution} (hP : P.IsProbability) :
    probModelOfCode P.code = P := by
  classical
  unfold probModelOfCode
  rw [dif_pos ⟨P, rfl, hP⟩]
  exact CodedFiniteDistribution.code_injective
    (Exists.choose_spec (⟨P, rfl, hP⟩ : ∃ Q, Q.code = P.code ∧ Q.IsProbability)).1

/-
**Counting / existence step.** If the total budget for level sets of simple
probability models is smaller than the number of `n`-bit strings, then some
`n`-bit string lies outside every level set of every simple probability model.
-/
theorem exists_uncovered_nbit_string (U : Map) (n alpha max_k : ℕ)
    (h : 2 ^ (alpha + 1) * (max_k + 1) * 2 ^ max_k < 2 ^ n) :
    ∃ x : BitString, x.length = n ∧
      ∀ P : CodedFiniteDistribution, P.IsProbability →
        P.complexity U ≤ (alpha : ENat) →
        ∀ k ≤ max_k, x ∉ levelSet P k := by
  -- By definition of `stringsOfLength`, there exists an `x` in `stringsOfLength n`.
  obtain ⟨x, hx⟩ : ∃ x : BitString, x ∈ stringsOfLength n ∧
      x ∉ (modelsWithComplexityLe U alpha).biUnion (fun c ↦
        (Finset.range (max_k + 1)).biUnion (fun k ↦ levelSet (probModelOfCode c) k)) := by
    contrapose! h
    calc 2 ^ n = (stringsOfLength n).card := (Kolmogorov.cardStringsOfLength n).symm
      _ ≤ _ := Finset.card_le_card h
      _ ≤ ∑ c ∈ _, ((Finset.range (max_k + 1)).biUnion
            (fun k ↦ levelSet (probModelOfCode c) k)).card := Finset.card_biUnion_le
      _ ≤ ∑ c ∈ modelsWithComplexityLe U alpha, (max_k + 1) * 2 ^ max_k := by
          apply Finset.sum_le_sum
          intro c _
          refine le_trans Finset.card_biUnion_le ?_
          have h2 := Finset.sum_le_card_nsmul (Finset.range (max_k + 1))
            (fun k ↦ (levelSet (probModelOfCode c) k).card) (2 ^ max_k) ?_
          · refine h2.trans_eq ?_
            rw [Finset.card_range]
            exact_mod_cast rfl
          · intro y hy
            have h1 := levelSet_card_le (probModelOfCode c) y (probModelOfCode_isProbability c)
            exact_mod_cast h1.trans (pow_le_pow_right₀ (by norm_num)
              (Finset.mem_range_succ_iff.mp hy))
      _ = (modelsWithComplexityLe U alpha).card * ((max_k + 1) * 2 ^ max_k) := by
          simp [Finset.sum_const]
      _ ≤ 2 ^ (alpha + 1) * ((max_k + 1) * 2 ^ max_k) := by
          gcongr
          exact card_modelsWithComplexityLe U alpha
      _ = 2 ^ (alpha + 1) * (max_k + 1) * 2 ^ max_k := by ring
  refine ⟨ x, ?_, ?_ ⟩
  · simp_all +decide only [levelSet, Finset.mem_biUnion, Finset.mem_range, Order.lt_add_one_iff,
      Finset.mem_filter, not_exists, not_and, not_le]
    grind +suggestions
  · simp_all +decide only [levelSet, Finset.mem_biUnion, Finset.mem_range, Order.lt_add_one_iff,
      Finset.mem_filter, not_exists, not_and, not_le]
    intro P hP hcomp k hk hxP
    specialize hx
    have hcover := hx.2 P.code (code_mem_modelsWithComplexityLe U P alpha hcomp) k hk
    simp_all +decide [probModelOfCode_eq]

/-- **Partial-recursive coding bound.** If `w` is produced from `x` by a partial
recursive function `f`, then the plain prefix complexity of `w` is no more than
that of `x` plus a constant. This is the partial-function analogue of
`KPPlain_map_le`; the auxiliary decompressor `fun pr ↦ (U pr).bind f` has a
domain contained in that of `U`, hence is prefix-free. -/
theorem KPPlain_partrec_map_le (U : Map) (hU : IsOptimalPrefixConditional U)
    (f : BitString →. BitString) (hf : Partrec f) :
    ∃ c : ℕ, ∀ x w : BitString, w ∈ f x → KPPlain U w ≤ KPPlain U x + (c : ENat) := by
  classical
  -- The auxiliary decompressor: run `U`, then apply `f` to the output.
  set D : Map := fun pr ↦ (U pr).bind (fun z ↦ f z) with hDdef
  have hD_decomp : isDecompressor D := by
    have : Partrec (fun pr : BitString × BitString ↦ (U pr).bind (fun z ↦ f z)) :=
      Partrec.bind hU.isDecompressor (hf.comp Computable.snd)
    exact this
  have hD_sub : ∀ y, domainAt D y ⊆ domainAt U y := by
    intro y p hp
    simp only [domainAt, Set.mem_setOf_eq, hDdef] at hp ⊢
    exact hp.fst
  have hD_prefix : IsPrefixMachine D := fun y ↦
    (hU.isPrefixMachine y).mono (hD_sub y)
  have hD_pd : IsPrefixDecompressor D := ⟨hD_decomp, hD_prefix⟩
  obtain ⟨c, hc⟩ := hU.invariance hD_pd
  refine ⟨c, fun x w hw ↦ ?_⟩
  by_cases hx : KPPlain U x = ⊤
  · rw [hx, top_add]; exact le_top
  · obtain ⟨p, hp_prod, hp_len⟩ := exists_program_of_KP_ne_top (by rwa [KPPlain_eq_KP] at hx)
    have hprodD : produces D p [] w := by
      simp only [produces, hDdef]
      exact Part.mem_bind_iff.mpr ⟨x, hp_prod, hw⟩
    have hKPD : KP D w [] ≤ (programLength p : ENat) := KP_le_programLength_of_produces hprodD
    calc
      KPPlain U w = KP U w [] := rfl
      _ ≤ KP D w [] + (c : ENat) := hc w []
      _ ≤ (programLength p : ENat) + (c : ENat) := by gcongr
      _ = KPPlain U x + (c : ENat) := by rw [hp_len, KPPlain_eq_KP]

/-- The finite-set enumeration/counting step (SUV Theorem 248, algorithmic core).

If the union of the level sets of all *probability* models of prefix complexity
`≤ alpha` at thresholds `k ≤ max_k` is smaller than the space of `n`-bit strings,
then there is an `n`-bit string outside that union whose plain prefix complexity
is `alpha + O(log n)`.

The two halves of the argument are already available in this file:
* the pure counting/existence half is `exists_uncovered_nbit_string`, which uses
  `card_modelsWithComplexityLe`, `levelSet_card_le`, and `probModelOfCode`;
* the coding half is `KPPlain_partrec_map_le`, the partial-recursive analogue of
  `KPPlain_map_le`, which bounds the complexity of any value produced from a
  short input by a partial-recursive map.

What remains is the *constructive* bridge: a single partial-recursive selector
that, fed the canonical encoding of `(n, alpha, max_k)` together with the count
`h` of length-`≤ alpha` programs that halt under `U`, dovetails `U` until exactly
`h` of them halt (so that every model of complexity `≤ alpha` has been seen),
builds the finite cover with a computable rational-mass level-set test, and
returns the first uncovered `n`-bit string.  Its output is then an uncovered
string whose complexity is bounded via `KPPlain_partrec_map_le` by the
complexity of the input encoding, namely `alpha + O(log n)` (the `alpha` term is
the cost of `h`, encoded in `Nat.bits h` of length `≤ alpha + O(1)`, and the
`O(log n)` term is the cost of `(n, alpha, max_k)`).  This selector, its
`Partrec` proof, and the computable-cover correctness are the remaining work. -/
def pack4 (a b c d : BitString) : BitString :=
  pairCode a (pairCode b (pairCode c d))

/-- Encodes the selector input parameters `(n, alpha, max_k, h)` into a single bitstring. -/
def selectorInput (n alpha max_k h : ℕ) : BitString :=
  pack4 (Nat.bits n) (Nat.bits alpha) (Nat.bits max_k) (Nat.bits h)

/-- If `k < 2 ^ m` then the binary expansion `Nat.bits k` has length at most `m`.
(Equivalently `(Nat.bits k).length = Nat.size k` and `Nat.size_le`.) -/
theorem length_natBits_lt_pow {k m : ℕ} (h : k < 2 ^ m) :
    (Nat.bits k).length ≤ m := by
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.mpr h

/-- Every `n` is strictly below `2` raised to the length of its binary expansion. -/
theorem lt_two_pow_length_natBits (n : ℕ) : n < 2 ^ (Nat.bits n).length := by
  rw [Nat.size_eq_bits_len]
  exact Nat.lt_size_self n

/-
**Length/coding half of SUV Theorem 248.**

The canonical selector input `selectorInput n alpha max_k h` has plain prefix
complexity `alpha + O(log n)`, with the downstream partial-recursive map constant
`c_partrec` absorbed.  The `alpha` term is the cost of the halting count `h`,
whose binary expansion has length `≤ alpha + 1` (using `h < 2 ^ (alpha + 1)`); the
`O(log n)` term is the cost of `(n, alpha, max_k)`, all of which are `< n` by the
covering hypothesis, hence have bit-length `≤ (Nat.bits n).length`.

Proof outline (does not use `KPPlain_uncovered_string`):
* From the covering hypothesis, `alpha < n` and `max_k < n` (drop the positive
  factors), and `n ≥ 1`.
* Write `a := (Nat.bits n).length`.  Then `n < 2 ^ a` (`lt_two_pow_length_natBits`),
  so `alpha, max_k < 2 ^ a` and thus `(Nat.bits alpha).length, (Nat.bits max_k).length ≤ a`
  (`length_natBits_lt_pow`); also `(Nat.bits h).length ≤ alpha + 1`.
* `length_pairCode` gives `(selectorInput n alpha max_k h).length ≤ 6 * a + alpha + 4`.
* `KPPlain_le_length_add_log` bounds `KPPlain U s ≤ s.length + 2 * (Nat.bits s.length).length + c₀`.
  Since `s.length ≤ 6a + alpha + 4 < 2 ^ (a + 3)`, `(Nat.bits s.length).length ≤ a + 3`.
* Collecting terms, `KPPlain U s + c_partrec ≤ alpha + (20 + c₀ + c_partrec) * a`,
  so `c := 20 + c₀ + c_partrec` works (using `a ≥ 1`).
-/
theorem KPPlain_selectorInput_le (U : Map) (hU : IsOptimalPrefixConditional U) (c_partrec : ℕ) :
    ∃ c : ℕ, ∀ n alpha max_k h : ℕ,
      h < 2 ^ (alpha + 1) →
      2 ^ (alpha + 1) * (max_k + 1) * 2 ^ max_k < 2 ^ n →
      KPPlain U (selectorInput n alpha max_k h) + (c_partrec : ENat)
        ≤ (alpha : ENat) + (c : ENat) * (Nat.bits n).length :=
  by
    by_contra h_contra;
    obtain ⟨c₀, hc₀⟩ := KPPlain_le_length_add_log U hU;
    refine h_contra ⟨ 18 + c₀ + c_partrec, fun n alpha max_k h hh h_cov ↦ ?_ ⟩;
    -- Let `a := (Nat.bits n).length`.
    -- Obtain `c0` from `KPPlain_le_length_add_log U hU`. Use `c := 18 + c0 + c_partrec`.
    set a := (Nat.bits n).length with ha
    have h_alpha : alpha < n := by
      contrapose! h_cov;
      exact le_trans (pow_le_pow_right₀ (by decide) (by linarith))
        (Nat.le_of_dvd (by positivity) (dvd_mul_of_dvd_left (dvd_mul_right _ _) _))
    have h_max_k : max_k < n := by
      contrapose! h_cov;
      exact le_trans (pow_le_pow_right₀ (by decide) h_cov)
        (Nat.le_of_dvd (by positivity) (dvd_mul_left _ _))
    have h_n : n < 2 ^ a := by
      convert lt_two_pow_length_natBits n using 1
    have h_alpha_lt : (Nat.bits alpha).length ≤ a := by
      exact length_natBits_lt_pow ( by linarith )
    have h_max_k_lt : (Nat.bits max_k).length ≤ a := by
      exact length_natBits_lt_pow ( by linarith )
    have h_h_lt : (Nat.bits h).length ≤ alpha + 1 := by
      convert length_natBits_lt_pow hh using 1
    have h_a_ge_1 : 1 ≤ a := by
      lia;
    -- Using `hslen` and the bound from Step 3, in ℕ:
    have h_bound : (selectorInput n alpha max_k h).length +
        2 * (Nat.bits (selectorInput n alpha max_k h).length).length +
        c₀ + c_partrec ≤ alpha + (18 + c₀ + c_partrec) * a := by
      have h_bound : (selectorInput n alpha max_k h).length ≤ 6 * a + alpha + 4 := by
        unfold selectorInput
        simp +arith +decide [pack4, pairCode]
        linarith
      have h_bound : (Nat.bits (selectorInput n alpha max_k h).length).length ≤ a + 3 := by
        apply length_natBits_lt_pow;
        have h_bound : 6 * a + alpha + 4 < 2 ^ (a + 3) := by
          have h_exp : 2 ^ a ≥ a + 1 := by
            exact Nat.recOn a (by norm_num) fun n ihn ↦ by
              rw [pow_succ']
              linarith
          rw [pow_add]
          nlinarith only [h_exp, h_alpha, h_n]
        linarith
      nlinarith only [
        h_bound,
        ‹List.length (selectorInput n alpha max_k h) ≤ 6 * a + alpha + 4›,
        h_a_ge_1]
    exact add_le_add (hc₀ _) le_rfl |> le_trans <| by norm_cast

/-
The distribution-to-finite-set bridge used by the contradiction.

If `x` is `(alpha,beta)`-stochastic and has plain prefix complexity bounded by
`kxBound`, then the witnessing distribution has a level set containing `x` with
threshold at most `kxBound + beta + O(1)`.  This packages the arXiv/SUV
level-set construction: from `DeficiencyLe U P x beta`, use
`KP U x P.code ≤ KPPlain U x + O(1)` and take
`A = {y | 2^-k ≤ P(y)}`.  No cardinality bound on all deficient strings is used.
-/
theorem stochastic_mem_levelSet_of_KPPlain_bound
    (U : Map) (_hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x : BitString, ∀ alpha beta kxBound max_k : ℕ,
      IsStochastic U x alpha beta →
      KPPlain U x ≤ (kxBound : ENat) →
      kxBound + beta + c ≤ max_k →
      ∃ P : CodedFiniteDistribution, P.IsProbability ∧
        P.complexity U ≤ (alpha : ENat) ∧
        ∃ k ≤ max_k, x ∈ levelSet P k := by
  obtain ⟨ c, hc ⟩ := KP_le_KPPlain U _hU; use c
  intros x alpha beta kxBound max_k hstoch hKPx hthr
  obtain ⟨ P, hprob, hcomp, hdef ⟩ := hstoch
  refine ⟨P, hprob, hcomp, ?_⟩
  simp_all +decide only [KPPlain_eq_KP, levelSet, Finset.mem_filter]
  refine ⟨ KP U x P.code |> ENat.toNat |> (· + beta), ?_, ?_, ?_ ⟩;
  · have hKP_le : KP U x P.code ≤ (kxBound + c : ENat) := by
      exact le_trans ( hc _ _ ) ( by gcongr );
    cases h : KP U x P.code <;> simp_all +arith +decide;
    · norm_cast at hKP_le;
    · norm_cast at *; linarith;
  · contrapose! hdef; simp_all +decide only [DeficiencyLe];
    simp_all +decide only [CodedFiniteDistribution.DeficiencyLe, not_false_eq_true,
      CodedFiniteDistribution.mass_eq_zero_of_not_mem_support, mul_zero, nonpos_iff_eq_zero];
    cases h : KP U x P.code <;>
      simp_all +decide only [complexityWeight, pow_eq_zero_iff', ENNReal.inv_eq_zero, ne_eq,
        false_and, not_false_eq_true];
    have h_not_top : KP U x [] ≠ ⊤ := by intro h_top; rw [h_top] at hKPx; cases hKPx
    have h_lt := lt_of_le_of_lt (hc x P.code)
      (WithTop.add_lt_top.mpr ⟨lt_top_iff_ne_top.mpr h_not_top, WithTop.coe_lt_top c⟩)
    exact absurd h (ne_of_lt h_lt);
  · have h_bound : complexityWeight (KP U x P.code) ≤ (2 : ENNReal) ^ beta * P.mass x := by
      exact hdef;
    cases h : KP U x P.code <;>
      simp_all +decide only [complexityWeight_top, complexityWeight_coe, zero_le, ENat.toNat_top,
        ENat.toNat_coe, zero_add, pow_add, ge_iff_le];
    · have := hc x P.code; simp_all +decide;
      cases h : KP U x [] <;> simp_all +decide;
      cases this;
    · calc
        _ ≤ ((2 : ENNReal) ^ beta * P.mass x) * (2 : ENNReal)⁻¹ ^ beta := by gcongr
        _ = P.mass x := by
          rw [mul_right_comm, ← mul_pow,
            ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow, one_mul]

/-
The arithmetic bridge: if `2*alpha + beta + c*log n < n`, then we can choose `max_k` such that
the total size is `< 2^n`, and `max_k` is large enough to cover the required threshold.
-/
theorem nonstochastic_arithmetic_bridge (n alpha beta c_1 c_2 c : ℕ)
    (hc : c_1 + c_2 + 4 ≤ c)
    (h_gap : 2 * alpha + beta + c * (Nat.bits n).length < n) :
    let max_k := alpha + beta + c_1 * (Nat.bits n).length + c_2;
    2 ^ (alpha + 1) * (max_k + 1) * 2 ^ max_k < 2 ^ n := by
      -- Set max_k := alpha + beta + c_1 * n.bits.length + c_2, and note the goal LHS
      -- equals (max_k + 1) * 2 ^ E where E := 2*alpha + beta + c_1 * n.bits.length + c_2 + 1.
      set max_k := alpha + beta + c_1 * n.bits.length + c_2
      have h_max_k : max_k + 1 < 2 ^ (n.bits.length) := by
        have h_max_k : max_k + 1 ≤ n := by
          by_cases h_bits : n.bits.length = 0;
          · cases n <;> simp_all +arith +decide [ Nat.bits ];
            rw [ Nat.binaryRec ] at h_bits; aesop;
          · norm_num +zetaDelta at *;
            nlinarith [ Nat.pos_of_ne_zero ( show n.bits.length ≠ 0 from by aesop ) ];
        refine lt_of_le_of_lt h_max_k ?_;
        have hnsize : n < 2 ^ n.bits.length := by
          have h1 := Nat.lt_size_self n
          rwa [← Nat.size_eq_bits_len] at h1
        exact hnsize
      -- From hc, c ≥ c_1 + c_2 + 4, so c*L ≥ (c_1+c_2+4)*L = c_1*L + c_2*L + 4*L.
      -- Since L ≥ 1, c_2*L ≥ c_2. Hence c*L ≥ c_1*L + c_2 + 4*L.
      have h_cL : c * n.bits.length ≥ c_1 * n.bits.length + c_2 + 4 * n.bits.length := by
        nlinarith [ show n.bits.length > 0 from Nat.pos_of_ne_zero ( by aesop ) ];
      have h1 : 2 ^ (alpha + 1) * (max_k + 1) * 2 ^ max_k =
          (max_k + 1) * 2 ^ (2 * alpha + beta + c_1 * n.bits.length + c_2 + 1) := by
        calc 2 ^ (alpha + 1) * (max_k + 1) * 2 ^ max_k
          _ = (max_k + 1) * (2 ^ (alpha + 1) * 2 ^ max_k) := by ring
          _ = (max_k + 1) * 2 ^ (alpha + 1 + max_k) := by rw [← pow_add]
          _ = (max_k + 1) * 2 ^ (2 * alpha + beta + c_1 * n.bits.length + c_2 + 1) := by
            congr 2
            omega
      have h2 : (max_k + 1) * 2 ^ (2 * alpha + beta + c_1 * n.bits.length + c_2 + 1) <
          2 ^ n.bits.length * 2 ^ (2 * alpha + beta + c_1 * n.bits.length + c_2 + 1) := by
        apply Nat.mul_lt_mul_of_pos_right h_max_k
        exact pow_pos (by decide) _
      have h3 : 2 ^ n.bits.length * 2 ^ (2 * alpha + beta + c_1 * n.bits.length + c_2 + 1) ≤
          2 ^ n := by
        rw [← pow_add]
        apply Nat.pow_le_pow_right (by decide)
        omega
      change 2 ^ (alpha + 1) * (max_k + 1) * 2 ^ max_k < 2 ^ n
      rw [h1]
      exact h2.trans_le h3

end Kolmogorov
