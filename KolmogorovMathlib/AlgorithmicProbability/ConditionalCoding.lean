/-
Copyright (c) 2024 Alexey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey
-/
import KolmogorovMathlib.AlgorithmicProbability.ConditionalCoding.Basic
import KolmogorovMathlib.AlgorithmicProbability.ConditionalCoding.Computability
import KolmogorovMathlib.AlgorithmicProbability.ConditionalCoding.Bounds

/-!
# Conditional Coding for the Pair-Section Semimeasure

This module isolates the genuinely hard Chapter-4 (SUV §4.5) content of the
*lower* direction of prefix symmetry of information into precise coding
obligations, and proves all of the connecting algebra around them.

The reduction theorem `KPPair_chain_lower_of_conditional_coding`
(`KolmogorovMathlib.Prefix.Symmetry`) shows that the whole counting content of
the Levin–Gács lower direction collapses to a single conditional coding bound
`hcode`: at `k = K(x)`, the conditional weight `2^{-K(y | x, k)}` dominates the
scaled section mass `2^{-c₁} · m_U(⟨x,y⟩) · 2^{k}`. This file assembles exactly
that bound (`section_coding_bound`) from two independent obligations:

* `pairMarginal_coding_bound` — the **marginal coding bound** at `k = K(x)`: the
  coding theorem applied to the lower-semicomputable pair marginal
  `x ↦ pairMarginal U x` (whose normalization `∑_x pairMarginal U x ≤ 1` is
  already proved in `PairMarginal`). It is stated in the *true* direction, with
  the constant on the side that makes it provable: `pairMarginal U x · 2^{k} ≤ 2^{c₂}`
  at `k = K(x)`. The constant-free form `pairMarginal U x ≤ 2^{-K(x)}` (i.e.
  section mass `≤ 1`) is **false** — the coding theorem only gives
  `pairMarginal U x ≤ 2^{c₂} · 2^{-K(x)}` with a genuine positive overhead `c₂`.

* `conditional_coding_section_realization` — the **conditional Kraft–Chaitin
  realization** of the scaled section family `y ↦ m_U(⟨x,y⟩) · 2^{k}`. Because the
  section is only *constant*-subnormalized (mass `≤ 2^{d}`, not `≤ 1`), the
  realization is stated uniformly in the subnormalization level `d`: for each `d`
  there is a prefix decompressor `M` and loss `c₀` realizing every section of
  mass `≤ 2^{d}` (per-context guard `∑_y m_U(⟨x,y⟩) · 2^{k} ≤ 2^{d}`) up to `c₀`.
  The guard keeps the statement honest: a truncated Kraft–Chaitin machine
  (down-scaling by the fixed `2^{-d}` it hardcodes) realizes the section only
  where its running mass stays `≤ 2^{d}`. The loss `c₀` absorbs the `d`-level
  overhead. No false lower-semicomputability claim about a `K(x)`-guarded object
  is made — the raw section is l.s.c.; the guard restricts where the bound holds.

The glue (`section_coding_bound`) is pure `ℝ≥0∞`/exponent algebra: the marginal
bound puts the section mass at `≤ 2^{c₂}` at `k = K(x)` (via `pairSection_tsum`),
which discharges the realization guard at level `d = c₂`; `M`'s realization is
transferred to the optimal `U` by `optimalPrefix_complexityWeight_bound`, and the
constants combine with `pow_add`. The guard is never instantiated at `k ≠ K(x)`,
so the false unguarded `∀ k` coding bound never appears.
-/
