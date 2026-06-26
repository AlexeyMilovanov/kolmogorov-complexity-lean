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
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitin.Request
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





/-- **Dynamic truncation of a lower-semicomputable function to a global mass bound.**

Given a lower-semicomputable `f` and a level `d`, there is a lower-semicomputable
`g` that is *globally* `2^{d}`-subnormalized (`∀ ctx, ∑_out g out ctx ≤ 2^{d}`) and
agrees with `f` on every context whose own `f`-mass already respects the bound
(`∑_out f out ctx ≤ 2^{d} → g = f` on that context).

This is the online "cap the running mass at `2^{d}`" operator: enumerate the dyadic
increments of `f` (via its `IsLSC` approximation) and accept each only while the
accumulated per-context mass stays `≤ 2^{d}`. The accepted stream is itself
lower-semicomputable and globally bounded; where `f`'s total mass never exceeds the
cap, no increment is ever dropped, so `g = f` there.

This packages the dynamic-truncation half of the *conditional* Kraft–Chaitin
construction (SUV §4.5): it converts the merely per-context-guarded scaled section
into a globally-bounded l.s.c. function the abstract allocator
`kraftChaitin_realization_bound` can consume directly.

The construction is the take-while online truncation `truncG`: enumerate all dyadic
increments of `f` as a single `ℕ`-indexed stream (output decoded via
`Encodable.decode₂`, stage from `Nat.unpair`), accept an increment iff the running
cumulative mass stays `≤ 2^{d}`, and read off the accepted mass per output as the
supremum of exact dyadic numerators over `2^{S}`. It is now fully proved: see the
`truncG*`/`ev*`/`cumNum`/`incNum` lemmas above for lower
semicomputability (`truncGapprox_mono`, `truncGapprox_computable`), the global
`2^{d}` bound (`tsum_truncG_le`), and agreement (`truncG_eq_f_of_le`). -/
theorem IsLSC.truncate {f : BitString → BitString → ℝ≥0∞} (hf : IsLSC f) (d : ℕ) :
    ∃ g : BitString → BitString → ℝ≥0∞, IsLSC g ∧
      (∀ ctx : BitString, (∑' out : BitString, g out ctx) ≤ (2 : ℝ≥0∞) ^ d) ∧
      (∀ ctx : BitString, (∑' out : BitString, f out ctx) ≤ (2 : ℝ≥0∞) ^ d →
        ∀ out : BitString, g out ctx = f out ctx) := by
  obtain ⟨approx, hmono, hsup, hcomp⟩ := hf
  refine ⟨truncG approx d, ⟨truncGapprox approx d, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro S out ctx; exact truncGapprox_mono d S out ctx
  · intro out ctx; rfl
  · exact truncGapprox_computable hcomp d
  · intro ctx; exact tsum_truncG_le d ctx
  · intro ctx hle out; exact truncG_eq_f_of_le hmono hsup d ctx hle out



end Kolmogorov
