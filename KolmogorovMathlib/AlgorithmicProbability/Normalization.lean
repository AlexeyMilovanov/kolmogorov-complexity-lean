/-
Copyright (c) 2024 Alexey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey
-/
import KolmogorovMathlib.AlgorithmicProbability.Semimeasure

/-!
# Reducing A Priori Semimeasure Normalization to a Domain-Weight Bound

This module performs the *shape-fixing* reduction that precedes the (later, harder)
Kraft inequality. The normalization statement we ultimately want is

```
∑_x m_M(x | y) ≤ 1,
```

a sum over **outputs** `x`. The structurally clean object, however, is the total
weight of the **halting domain** in context `y`:

```
domainWeight M y = ∑_{p ∈ domainAt M y} 2^{-|p|}.
```

The headline lemma `tsum_aprioriMeasure_eq_domainWeight` shows these two sums are
*equal* for **every** map `M` — no prefix-freeness required. The single ingredient
is that a `Part` computation is single-valued (`Part.mem_unique`): a program `p`
either halts on a unique output (contributing its weight once) or never halts
(contributing nothing). Swapping the order of summation with `ENNReal.tsum_comm`
collapses the output sum to one indicator term per program.

This isolates the *entire* remaining difficulty into the one bound
`domainWeight M y ≤ 1`, which is exactly the Kraft inequality for the prefix-free
domain of a prefix machine. That bound is **not** proved here; it is the target of
a subsequent `Prefix/Kraft.lean` slot. We package the conditional consequence
`tsum_aprioriMeasure_le_one_of_domainWeight_le_one` so the Kraft slot can drop in
without touching this file.

No prefix hypothesis, no logarithms, no real numbers: everything stays in `ℝ≥0∞`.
-/

namespace Kolmogorov

open scoped ENNReal

open Classical in
/-- The total **domain weight** of a map `M` in context `y`: the sum of the
weights `2^{-|p|}` over every program `p` that halts in context `y`. Realized as a
`tsum` over all of `BitString` with an indicator summand, matching the shape of
`aprioriMeasure`. This is the object the Kraft inequality will bound by `1`. -/
noncomputable def domainWeight (M : Map) (y : BitString) : ℝ≥0∞ :=
  ∑' p : BitString, if p ∈ domainAt M y then progWeight p else 0

/-- **Empty-domain collapse.** If *no* program halts in context `y`, then the
total domain weight is `0`: every indicator summand vanishes. By the reduction
`tsum_aprioriMeasure_eq_domainWeight`, this is the degenerate case in which the a
priori semimeasure carries no mass at all. -/
theorem domainWeight_eq_zero_of_forall_not_mem_domainAt {M : Map} {y : BitString}
    (h : ∀ p, p ∉ domainAt M y) : domainWeight M y = 0 := by
  classical
  rw [domainWeight]
  refine (tsum_congr (fun p => ?_)).trans tsum_zero
  rw [if_neg (h p)]

open Classical in
/-- **Single-program collapse.** Summing the contribution of a *fixed* program `p`
over all possible outputs `x` yields just its weight if `p` halts in context `y`,
and `0` otherwise. The proof uses only that `M (p, y)` is single-valued
(`Part.mem_unique`): in the halting case there is a unique output `x₀`, so the
output sum reduces to a single term. -/
theorem tsum_produces_eq (M : Map) (p y : BitString) :
    (∑' x : BitString, if produces M p y x then progWeight p else 0)
      = if p ∈ domainAt M y then progWeight p else 0 := by
  classical
  by_cases hp : p ∈ domainAt M y
  · rw [if_pos hp]
    obtain ⟨x₀, hx₀⟩ := Part.dom_iff_mem.mp hp
    have hcongr : ∀ x : BitString,
        (if produces M p y x then progWeight p else 0)
          = if x = x₀ then progWeight p else 0 := by
      intro x
      have hiff : produces M p y x ↔ x = x₀ :=
        ⟨fun hx => Part.mem_unique hx hx₀, fun hx => hx ▸ hx₀⟩
      simp only [hiff]
    rw [tsum_congr hcongr, tsum_eq_single x₀ (fun b hb => if_neg hb), if_pos rfl]
  · rw [if_neg hp]
    have hzero : ∀ x : BitString,
        (if produces M p y x then progWeight p else 0) = 0 := by
      intro x
      rw [if_neg]
      intro hx
      exact hp (produces_mem_domainAt hx)
    rw [tsum_congr hzero, tsum_zero]

/-- **The reduction.** The total a priori semimeasure mass over all outputs equals
the total domain weight, for an arbitrary map `M`. This fixes the shape of the
normalization goal: bounding `∑_x m_M(x | y)` is the *same* as bounding
`domainWeight M y`. -/
theorem tsum_aprioriMeasure_eq_domainWeight (M : Map) (y : BitString) :
    (∑' x : BitString, aprioriMeasure M x y) = domainWeight M y := by
  classical
  simp only [aprioriMeasure]
  rw [ENNReal.tsum_comm]
  simp only [domainWeight]
  exact tsum_congr (fun p => tsum_produces_eq M p y)

/-- **Conditional normalization.** If the domain weight in context `y` is at most
`1` — which is exactly the Kraft inequality for a prefix machine's halting domain —
then the a priori semimeasure is normalized: `∑_x m_M(x | y) ≤ 1`. The Kraft bound
hypothesis is supplied by a later slot; this packaging lets that slot conclude
normalization in one line. -/
theorem tsum_aprioriMeasure_le_one_of_domainWeight_le_one (M : Map) (y : BitString)
    (h : domainWeight M y ≤ 1) : (∑' x : BitString, aprioriMeasure M x y) ≤ 1 := by
  rw [tsum_aprioriMeasure_eq_domainWeight]
  exact h

end Kolmogorov
