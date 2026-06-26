/-
Copyright (c) 2024 Alexey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey
-/
import Mathlib
import KolmogorovMathlib.AlgorithmicProbability.Coding
import KolmogorovMathlib.Prefix.Optimal
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitinAllocator
import KolmogorovMathlib.AlgorithmicProbability.Computability.Tuple

import KolmogorovMathlib.AlgorithmicProbability.LSC.Defs
import KolmogorovMathlib.AlgorithmicProbability.LSC.Truncate
import KolmogorovMathlib.AlgorithmicProbability.LSC.Computability

import KolmogorovMathlib.AlgorithmicProbability.KraftChaitin.Machine
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitin.Geometric

namespace Kolmogorov

open scoped ENNReal
open Computability
/-- **Realization bound from a matched allocator (geometric form).** If a request
stream is realized by a prefix machine `M'` (each requested `(out, l)` gets an
allocated code of length `l` that `M'` maps back to `out`), and each output's mass
`f out` is within a factor `2^K` of its *largest single* request weight, then `M'`
achieves the multiplicative coding bound `2^{-K} · f(out|ctx) ≤ 2^{-KP_{M'}(out|ctx)}`.

This replaces the previous false form (which used the exact identity
`∑ requests = f` and is unprovable: with many equal-length requests `f out` can be
arbitrarily larger than the single largest request weight `= 2^{-KP}`). -/
lemma realization_bound_of_machine (f : BitString → BitString → ℝ≥0∞)
    (req : BitString → ℕ → Option (BitString × ℕ))
    (alloc : BitString → ℕ → Option BitString)
    (M' : Map) (K : ℕ)
    (hmatch : ∀ ctx n o l, req ctx n = some (o, l) → ∃ c, alloc ctx n = some c ∧ c.length = l)
    (hmachine : ∀ ctx n o l c, req ctx n = some (o, l) → alloc ctx n = some c → M' (c, ctx) = Part.some o)
    (hgeo : ∀ ctx out : BitString, f out ctx ≤ (2 : ℝ≥0∞) ^ K *
      (⨆ n, match req ctx n with | some (o, l) => if o = out then (2 : ℝ≥0∞)⁻¹ ^ l else 0 | none => 0)) :
    ∃ c₀ : ℕ, ∀ out ctx : BitString, (2 : ℝ≥0∞)⁻¹ ^ c₀ * f out ctx ≤ complexityWeight (KP M' out ctx) := by
  -- The supremum of the per-request weights for `out` is `≤ 2^{-KP M' out ctx}`,
  -- since every realized request gives a code of its length producing `out`.
  have hS : ∀ ctx out : BitString,
      (⨆ n, match req ctx n with
        | some (o, l) => if o = out then (2 : ℝ≥0∞)⁻¹ ^ l else 0 | none => 0)
        ≤ complexityWeight (KP M' out ctx) := by
    intro ctx out
    apply iSup_le
    intro n
    rcases h : req ctx n with _ | ⟨o, l⟩
    · simp
    · by_cases ho : o = out
      · subst ho
        obtain ⟨c, hc₁, hc₂⟩ := hmatch ctx n o l h
        have hprod : produces M' c ctx o := by
          have := hmachine ctx n o l c h hc₁
          simp [produces, this]
        have hKP : KP M' o ctx ≤ (programLength c : ENat) :=
          KP_le_programLength_of_produces hprod
        simpa [complexityWeight_programLength, progWeight, programLength, hc₂]
          using complexityWeight_le_of_le hKP
      · simp [ho]
  refine ⟨K, fun out ctx => ?_⟩
  calc (2 : ℝ≥0∞)⁻¹ ^ K * f out ctx
      ≤ (2 : ℝ≥0∞)⁻¹ ^ K * ((2 : ℝ≥0∞) ^ K *
          (⨆ n, match req ctx n with
            | some (o, l) => if o = out then (2 : ℝ≥0∞)⁻¹ ^ l else 0 | none => 0)) := by
        gcongr
        exact hgeo ctx out
    _ = (⨆ n, match req ctx n with
            | some (o, l) => if o = out then (2 : ℝ≥0∞)⁻¹ ^ l else 0 | none => 0) := by
        rw [← mul_assoc, ← mul_pow,
          ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow, one_mul]
    _ ≤ complexityWeight (KP M' out ctx) := hS ctx out

/-- **The abstract Kraft–Chaitin realization engine, unit-mass interface.**

This is the genuinely hard online prefix-free allocator, stated at the *unit mass*
level: a lower-semicomputable `f` whose per-context total mass is `≤ 1` is realized
by a genuine prefix decompressor up to an additive coding constant.

This is strictly more specific than the previous `2^d`-mass obligation: the
down-scaling reduction (`IsLSC.div_two_pow` plus the `ℝ≥0∞` exponent algebra) is
*proved* in `kraftChaitin_realization_bound` below, so the only remaining missing
content is the online leftmost-free-dyadic-interval allocator at mass `≤ 1`
(`exists_online_prefixFree_of_kraft_le_one`, to be built in a separate
`KraftChaitinOnline.lean`). -/
theorem kraftChaitin_realization_bound_unit {f : BitString → BitString → ℝ≥0∞}
    (hlsc : IsLSC f)
    (h_sum : ∀ ctx : BitString, (∑' out : BitString, f out ctx) ≤ 1) :
    ∃ M' : Map, IsPrefixDecompressor M' ∧ ∃ c₀ : ℕ, ∀ out ctx : BitString,
      (2 : ℝ≥0∞)⁻¹ ^ c₀ * f out ctx ≤ complexityWeight (KP M' out ctx) := by
  -- The genuinely hard online allocator (leftmost-free-dyadic-interval) at mass ≤ 1:
  -- 1. Extract the dyadic increments from `hlsc` as a computable request stream.
  obtain ⟨req, K, hreq_comp, hreq_wt, hgeo⟩ := extract_request_stream_geometric hlsc h_sum
  -- 2 & 3. Allocate prefix-free programs of the requested lengths online.
  obtain ⟨alloc, halloc_comp, halloc_match, halloc_pref⟩ := exists_online_prefixFree_family req hreq_comp hreq_wt
  -- 4. Construct `M'` via `Partrec` combinators from the resulting computable allocator.
  obtain ⟨M', hM', hM_match⟩ := construct_prefix_machine req alloc hreq_comp halloc_comp halloc_match halloc_pref
  obtain ⟨c₀, hc₀⟩ := realization_bound_of_machine f req alloc M' K halloc_match hM_match hgeo
  exact ⟨M', hM', c₀, hc₀⟩

theorem kraftChaitin_realization_bound {f : BitString → BitString → ℝ≥0∞}
    (hlsc : IsLSC f) (d : ℕ)
    (h_sum : ∀ ctx : BitString, (∑' out : BitString, f out ctx) ≤ (2 : ℝ≥0∞) ^ d) :
    ∃ M' : Map, IsPrefixDecompressor M' ∧ ∃ c₀ : ℕ, ∀ out ctx : BitString,
      (2 : ℝ≥0∞)⁻¹ ^ c₀ * f out ctx ≤ complexityWeight (KP M' out ctx) := by
  -- Reduce the `2^d`-mass case to the unit-mass interface by dividing `f` by `2^d`.
  have hg_lsc : IsLSC (fun out ctx => f out ctx / (2 : ℝ≥0∞) ^ d) := hlsc.div_two_pow d
  have hg_sum : ∀ ctx : BitString,
      (∑' out : BitString, f out ctx / (2 : ℝ≥0∞) ^ d) ≤ 1 := by
    intro ctx
    simp_rw [ENNReal.div_eq_inv_mul]
    rw [ENNReal.tsum_mul_left]
    rw [ENNReal.inv_mul_le_iff (by positivity) (by simp), mul_one]
    exact h_sum ctx
  obtain ⟨M', hM', c₀, hc₀⟩ := kraftChaitin_realization_bound_unit hg_lsc hg_sum
  refine ⟨M', hM', c₀ + d, fun out ctx => ?_⟩
  have hkey := hc₀ out ctx
  have hrw : (2 : ℝ≥0∞)⁻¹ ^ (c₀ + d) * f out ctx
      = (2 : ℝ≥0∞)⁻¹ ^ c₀ * (f out ctx / (2 : ℝ≥0∞) ^ d) := by
    rw [pow_add, div_eq_mul_inv]
    simp only [← ENNReal.inv_pow]
    ring
  rw [hrw]
  exact hkey
end Kolmogorov
