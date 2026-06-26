/-
Copyright (c) 2024 Alexey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey
-/
import Mathlib
import KolmogorovMathlib.Core.Basic

/-!
# The abstract Kraft–Chaitin realization engine

This module isolates the genuinely hard Chapter-4 (SUV §4.x) coding engine — the
**online Kraft–Chaitin allocator** — into a single, abstract, reusable obligation
`kraftChaitin_realization_bound`, decoupled from every particular semimeasure.

The engine consumes a *lower-semicomputable* conditional function
`f : output → context → ℝ≥0∞` (interface `IsLSC`: a computable, monotone, dyadic
approximation converging to `f`) that is globally `2^{d}`-subnormalized
(`∀ ctx, ∑_out f out ctx ≤ 2^{d}`), and produces a genuine prefix decompressor
`M'` realizing `f` up to an additive coding constant `c₀`:
`2^{-c₀} · f(out | ctx) ≤ 2^{-KP_{M'}(out | ctx)}`.

This is the canonical textbook statement of the Kraft–Chaitin coding theorem
(hard direction): it is `≤×`, with no logarithm and no equality, and the constant
`c₀` is genuine positive coding overhead (it absorbs the `2^{-d}` down-scaling the
truncated allocator hardcodes).

Both of the project's remaining coding sorries reduce to this single engine:

* `aprioriMeasure_prefix_realization` (in `KraftChaitin`) applies it to
  `aprioriMeasure M` at level `d = 0`, using `aprioriMeasure_isLSC` and
  `tsum_aprioriMeasure_le_one`;
* `conditional_coding_section_realization` (in `ConditionalCoding`) applies it to a
  dynamically *truncated* scaled section at level `d`.

The `IsLSC` interface deliberately keeps the approximation **concrete** (a
`ℕ`-valued numerator over the dyadic denominator `2^{s}`, with `Computable`
witnessing computability) rather than introducing a generic typeclass: this avoids
universe/computability-class friction and keeps the engine's hypotheses exactly
the data an allocator consumes.
-/

namespace Kolmogorov

open scoped ENNReal
open Computability

/-! ## Lower-Semicomputable Bounds -/

/-- The **dyadic value** `n / 2^s` of a stage-`s` numerator `n`, in `ℝ≥0∞`. This is
the value carried by one stage of a lower-semicomputable approximation. -/
noncomputable def dyadicValue (n s : ℕ) : ℝ≥0∞ := (n : ℝ≥0∞) / (2 : ℝ≥0∞) ^ s

/-- **Lower-semicomputable conditional function** interface.

`IsLSC f` says the conditional function `f : output → context → ℝ≥0∞` has a
*computable, monotone, dyadic* approximation: a `ℕ`-valued numerator
`approx s out ctx`, whose dyadic value `approx s out ctx / 2^s` increases in the
stage `s` and converges (as a supremum) to `f out ctx`, and which is `Computable`
as a function of `(s, out, ctx)`.

This is exactly the data the Kraft–Chaitin allocator enumerates: at each stage it
reads finitely many dyadic increments of `f` and emits prefix codes for them. The
numerators are `ℕ` (not `ℝ≥0∞`) precisely so the approximation is genuinely
computable; the conversion to `ℝ≥0∞` happens only in the monotonicity/supremum
clauses. -/
def IsLSC (f : BitString → BitString → ℝ≥0∞) : Prop :=
  ∃ approx : ℕ → BitString → BitString → ℕ,
    (∀ s out ctx, dyadicValue (approx s out ctx) s
        ≤ dyadicValue (approx (s + 1) out ctx) (s + 1)) ∧
    (∀ out ctx, ⨆ s, dyadicValue (approx s out ctx) s = f out ctx) ∧
    Computable (fun p : ℕ × BitString × BitString => approx p.1 p.2.1 p.2.2)

/-! ### The abstract Kraft–Chaitin realization engine (coding theorem, hard direction)

Every lower-semicomputable conditional function `f` that is globally
`2^{d}`-subnormalized (`∀ ctx, ∑_out f out ctx ≤ 2^{d}`) is *realized* by a genuine
prefix decompressor `M'` up to an additive coding constant `c₀`:
`2^{-c₀} · f(out | ctx) ≤ 2^{-KP_{M'}(out | ctx)}`.

This is the online Kraft–Chaitin allocator: scale `f` down by `2^{-d}` to a
subprobability (mass `≤ 1`), enumerate its dyadic increments via the `IsLSC`
approximation, and assign each increment a prefix-free program of length
`⌈-log(f/2^d)⌉ + O(1)`; the resulting `Partrec` map is a prefix decompressor whose
program lengths realize `-log f` up to `c₀ = d + O(1)`.

Discharging this requires the Kraft–Chaitin enumeration/allocation machinery
(prefix-free online code assignment from a computable request stream): convert the
`IsLSC` dyadic increments of `f / 2^d` into a computable request stream whose
per-context Kraft weight is `≤ 1` (from `h_sum`), allocate prefix-free programs of
the requested lengths online, and read off the `KP` bound. The agreed home for this
engine is a *to-be-built* separate streaming allocator (an online
`exists_online_prefixFree_of_kraft_le_one` in a new `KraftChaitinOnline.lean`,
leftmost-free-dyadic-interval, genuinely `Computable`, and actually consumed here),
*not* the finite offline Kraft converse. The realization bound is stated in the
*true* `≤×` direction (no logarithm, no equality); the constant `c₀` is genuine
coding overhead. -/

/-
**`IsLSC` is closed under dividing by a fixed power of two.**

Dividing a lower-semicomputable conditional function by the constant `2^d`
preserves lower semicomputability: shift the dyadic approximation stage by `d`
(`approxG S = approx (S - d)` for `S ≥ d`, and `0` below `d`), which keeps the
numerators integral and computable, monotone in the stage, and converging to
`f / 2^d` (multiplication by the constant `(2⁻¹)^d` commutes with the supremum).

This is pure approximation bookkeeping (no allocator content) and lets the general
`2^d`-mass realization bound reduce to the unit-mass interface
`kraftChaitin_realization_bound_unit` below.

Supremum of the stage-shifted dyadic approximation equals the original
supremum scaled by `2^{-d}`. The shifted approximation is `0` for stages `< d` and
`approx (S - d)` for `S ≥ d`; reindexing `S = k + d` and pulling the constant
`(2⁻¹)^d` through the supremum gives the result.
-/
lemma iSup_dyadicValue_shift (approx : ℕ → BitString → BitString → ℕ) (d : ℕ)
    (out ctx : BitString) :
    (⨆ S, dyadicValue (if S < d then 0 else approx (S - d) out ctx) S)
      = (⨆ s, dyadicValue (approx s out ctx) s) / (2 : ℝ≥0∞) ^ d := by
  rw [ ENNReal.div_eq_inv_mul ];
  rw [ ENNReal.mul_iSup ];
  refine le_antisymm ( iSup_le ?_ ) ( iSup_le ?_ );
  · intro i; split_ifs <;> simp_all +decide [ dyadicValue ] ;
    refine le_trans ?_ ( le_iSup _ ( i - d ) );
    rw [ show ( 2 : ℝ≥0∞ ) ^ i = ( 2 : ℝ≥0∞ ) ^ d * ( 2 : ℝ≥0∞ ) ^ ( i - d ) by rw [ ← pow_add, Nat.add_sub_of_le ‹d ≤ i› ] ] ; ring_nf;
    rw [ ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul ] ; ring_nf;
    rw [ ENNReal.mul_inv ] ; ring_nf ; norm_num;
    · exact Or.inl <| by norm_num;
    · exact Or.inl <| ENNReal.pow_ne_top <| by norm_num;
  · intro i; refine le_trans ?_ ( le_iSup _ ( i + d ) ) ; simp +decide [ dyadicValue ] ; ring_nf;
    rw [ ENNReal.div_eq_inv_mul ] ; ring_nf;
    rw [ ENNReal.div_eq_inv_mul ] ; ring_nf;
    rw [ mul_comm ] ; gcongr ; norm_num [ ENNReal.mul_inv ]

/-
Computability of the stage-shifted approximation, from computability of the
original approximation.
-/
lemma computable_dyadicValue_shift (approx : ℕ → BitString → BitString → ℕ) (d : ℕ)
    (hcomp : Computable (fun p : ℕ × BitString × BitString => approx p.1 p.2.1 p.2.2)) :
    Computable (fun p : ℕ × BitString × BitString =>
      if p.1 < d then 0 else approx (p.1 - d) p.2.1 p.2.2) := by
  have hsub : Computable (fun p : ℕ × BitString × BitString => p.1 - d) :=
    (Primrec.nat_sub.comp Primrec.fst (Primrec.const d)).to_comp
  have hbranch : Computable (fun p : ℕ × BitString × BitString =>
      approx (p.1 - d) p.2.1 p.2.2) :=
    hcomp.comp (hsub.pair Computable.snd)
  obtain ⟨_, hP⟩ := (Primrec.nat_lt.comp Primrec.fst (Primrec.const d) :
      PrimrecPred (fun p : ℕ × BitString × BitString => p.1 < d))
  have hpred : Computable (fun p : ℕ × BitString × BitString => decide (p.1 < d)) :=
    hP.to_comp
  refine (Computable.cond hpred (Computable.const 0) hbranch).of_eq (fun p => ?_)
  by_cases h : p.1 < d <;> simp [h]

theorem IsLSC.div_two_pow {f : BitString → BitString → ℝ≥0∞}
    (hf : IsLSC f) (d : ℕ) :
    IsLSC (fun out ctx => f out ctx / (2 : ℝ≥0∞) ^ d) := by
  obtain ⟨approx, hmono, hsup, hcomp⟩ := hf
  refine ⟨fun S out ctx => if S < d then 0 else approx (S - d) out ctx, ?_, ?_, ?_⟩
  · -- monotonicity of the shifted approximation
    intro s out ctx; by_cases hs : s < d <;> simp +decide [ hs ] ;
    · unfold dyadicValue; aesop;
    · convert mul_le_mul_left ( hmono ( s - d ) out ctx ) ( 2⁻¹ ^ d ) using 1 <;> ring_nf;
      · unfold dyadicValue; rw [ show s = s - d + d by rw [ Nat.sub_add_cancel ( le_of_not_gt hs ) ] ] ; ring_nf;
        simp +decide [ div_eq_mul_inv, mul_comm, mul_left_comm ];
        norm_num [ ENNReal.mul_inv, ENNReal.inv_pow ];
      · rw [ if_neg ( by linarith ) ] ; rw [ show 1 + s = 1 + ( s - d ) + d by linarith [ Nat.sub_add_cancel ( by linarith : d ≤ s ) ] ] ; simp +decide [ pow_add, dyadicValue ] ; ring_nf;
        simp +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, ENNReal.mul_inv ];
        norm_num [ ENNReal.inv_pow ]
  · -- supremum equals `f / 2^d`
    intro out ctx
    rw [iSup_dyadicValue_shift approx d out ctx, hsup out ctx]
  · -- computability of the shifted approximation
    exact computable_dyadicValue_shift approx d hcomp


end Kolmogorov
