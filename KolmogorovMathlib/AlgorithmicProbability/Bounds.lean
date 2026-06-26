/-
Copyright (c) 2024 Alexey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey
-/
import KolmogorovMathlib.Prefix.CountableKraft

/-!
# Pointwise Bounds and Non-Vacuity of the A Priori Semimeasure

The earlier slots established the *total* mass bound `∑_x m_M(x | y) ≤ 1` for a
prefix machine (`tsum_aprioriMeasure_le_one`). This module closes the remaining
"genuine semimeasure" obligations:

* a **pointwise** bound `m_M(x | y) ≤ domainWeight M y` for an arbitrary map, and
  hence `m_M(x | y) ≤ 1` and finiteness `m_M(x | y) ≠ ⊤` for a prefix machine;
* a reusable predicate `IsConditionalSemimeasure` packaging "every conditional
  total mass is `≤ 1`", satisfied by `aprioriMeasure M` for a prefix machine;
* a concrete **witness** `fun _ => Part.none` of `IsPrefixMachine`, so the whole
  prefix-machine theory is demonstrably non-vacuous (its semimeasure is `0`).

Everything stays in `ℝ≥0∞`: only elementary inequalities, no logarithms, no real
numbers, no computability, and no equality claims. The slot is purely additive
and builds on `tsum_aprioriMeasure_eq_domainWeight`, `domainWeight_le_one`, and
`tsum_aprioriMeasure_le_one`.
-/

namespace Kolmogorov

open scoped ENNReal

/-! ### Pointwise bounds -/

/-- **Pointwise bound by the domain weight.** Each output's mass is at most the
total domain weight, for an *arbitrary* map `M`: it is a single term in the
output-indexed sum, which equals `domainWeight M y`
(`tsum_aprioriMeasure_eq_domainWeight`). No prefix hypothesis is needed. -/
theorem aprioriMeasure_le_domainWeight (M : Map) (x y : BitString) :
    aprioriMeasure M x y ≤ domainWeight M y := by
  rw [← tsum_aprioriMeasure_eq_domainWeight]
  exact ENNReal.le_tsum x

/-- **Pointwise bound by `1`.** For a prefix machine, every value of the a priori
semimeasure is at most `1`. Combines the pointwise domain-weight bound with the
countable Kraft inequality `domainWeight_le_one`. -/
theorem aprioriMeasure_le_one (M : Map) (x y : BitString) (hM : IsPrefixMachine M) :
    aprioriMeasure M x y ≤ 1 :=
  (aprioriMeasure_le_domainWeight M x y).trans (domainWeight_le_one M y hM)

/-- **Finiteness.** For a prefix machine, every value of the a priori semimeasure
is finite (`≠ ⊤`), being bounded above by `1`. -/
theorem aprioriMeasure_ne_top (M : Map) (x y : BitString) (hM : IsPrefixMachine M) :
    aprioriMeasure M x y ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (aprioriMeasure_le_one M x y hM)

/-! ### The conditional-semimeasure interface -/

/-- A family `μ x y` is a **conditional semimeasure** when, for every context `y`,
its total mass over outputs is at most `1`. This is the reusable interface the
later universal/domination theory will quantify over. -/
def IsConditionalSemimeasure (μ : BitString → BitString → ℝ≥0∞) : Prop :=
  ∀ y, (∑' x : BitString, μ x y) ≤ 1

/-- The a priori semimeasure of a prefix machine satisfies the conditional
semimeasure interface — this is exactly the normalization milestone
`tsum_aprioriMeasure_le_one`, repackaged through the predicate. -/
theorem aprioriMeasure_isConditionalSemimeasure (M : Map) (hM : IsPrefixMachine M) :
    IsConditionalSemimeasure (aprioriMeasure M) :=
  fun y => tsum_aprioriMeasure_le_one M y hM

/-! ### Non-vacuity: the empty prefix machine -/

/-- The empty (never-halting) map has empty halting domain in every context. -/
theorem domainAt_const_none (y : BitString) :
    domainAt (fun _ => Part.none) y = (∅ : Set BitString) := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro p hp
  exact hp.elim

/-- **Non-vacuity.** The never-halting map is a prefix machine: its halting domain
is empty in every context, and the empty set is prefix-free. This exhibits a
concrete inhabitant of `IsPrefixMachine`, so every prefix-machine theorem above is
non-vacuous. -/
theorem isPrefixMachine_const_none : IsPrefixMachine (fun _ => Part.none) := by
  intro y
  rw [domainAt_const_none]
  exact isPrefixFree_empty

/-- **Sanity check.** The a priori semimeasure of the never-halting map is
identically `0`: no program produces any output, so every summand vanishes. -/
theorem aprioriMeasure_const_none (x y : BitString) :
    aprioriMeasure (fun _ => Part.none) x y = 0 := by
  classical
  rw [aprioriMeasure]
  have hzero : ∀ p : BitString,
      (if produces (fun _ => Part.none) p y x then progWeight p else 0) = 0 := by
    intro p
    rw [if_neg]
    exact Part.notMem_none x
  rw [tsum_congr hzero, tsum_zero]

end Kolmogorov
