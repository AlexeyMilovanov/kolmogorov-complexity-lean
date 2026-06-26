/-
Copyright (c) 2024 Alexey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey
-/
import KolmogorovMathlib.Prefix.Machine

/-!
# Optimal Prefix Decompressors

This module adds the *prefix* analogue of the plain optimality interface
(`isOptimalConditional` in `KolmogorovMathlib.Core.Basic`). It is deliberately a
thin interface layer: definitions plus projection/unfolding lemmas, parallel to
the plain case but quantifying only over *prefix* decompressors.

A **prefix decompressor** is a `Map` that is simultaneously a decompressor
(`isDecompressor`, i.e. partial recursive) and a prefix machine
(`IsPrefixMachine`, i.e. its halting domain is prefix-free in every context).
An **optimal prefix decompressor** dominates every other prefix decompressor on
conditional prefix complexity `KP`, up to an additive constant.

We make no existence claims here: constructing a universal prefix machine, or
proving that an optimal prefix decompressor exists, is intentionally deferred.
This file only fixes the vocabulary and records the easy projections, including
the `KP = condK` bridge that lets the invariance bound be restated for `condK`.
-/

namespace Kolmogorov

/-! ### Prefix decompressors -/

/-- A **prefix decompressor** is a decompressor whose halting domain is
prefix-free in every context. The two conditions are orthogonal: computability
(`isDecompressor`) says nothing about prefix-freeness (`IsPrefixMachine`), and
vice versa, so we bundle them explicitly. -/
def IsPrefixDecompressor (M : Map) : Prop :=
  isDecompressor M ∧ IsPrefixMachine M

/-- A prefix decompressor is, in particular, a decompressor. -/
theorem IsPrefixDecompressor.isDecompressor {M : Map}
    (h : IsPrefixDecompressor M) : isDecompressor M :=
  h.1

/-- A prefix decompressor is, in particular, a prefix machine. -/
theorem IsPrefixDecompressor.isPrefixMachine {M : Map}
    (h : IsPrefixDecompressor M) : IsPrefixMachine M :=
  h.2

/-! ### Optimal prefix decompressors -/

/-- A map `U` is an **optimal prefix decompressor** if it is itself a prefix
decompressor and it simulates every other prefix decompressor `M` with at most a
constant additive overhead in conditional prefix complexity `KP`.

This mirrors `isOptimalConditional` but quantifies *only* over prefix
decompressors, which is the correct universe for prefix complexity. -/
def IsOptimalPrefixConditional (U : Map) : Prop :=
  IsPrefixDecompressor U ∧
    ∀ M, IsPrefixDecompressor M →
      ∃ c : ℕ, ∀ x y, KP U x y ≤ KP M x y + (c : ENat)

/-- An optimal prefix decompressor is a prefix decompressor. -/
theorem IsOptimalPrefixConditional.isPrefixDecompressor {U : Map}
    (h : IsOptimalPrefixConditional U) : IsPrefixDecompressor U :=
  h.1

/-- An optimal prefix decompressor is, in particular, a decompressor. -/
theorem IsOptimalPrefixConditional.isDecompressor {U : Map}
    (h : IsOptimalPrefixConditional U) : isDecompressor U :=
  h.1.1

/-- An optimal prefix decompressor is, in particular, a prefix machine. -/
theorem IsOptimalPrefixConditional.isPrefixMachine {U : Map}
    (h : IsOptimalPrefixConditional U) : IsPrefixMachine U :=
  h.1.2

/-- **Invariance for prefix complexity.** An optimal prefix decompressor `U`
dominates any prefix decompressor `M` on conditional prefix complexity up to an
additive constant. -/
theorem IsOptimalPrefixConditional.invariance {U M : Map}
    (hU : IsOptimalPrefixConditional U) (hM : IsPrefixDecompressor M) :
    ∃ c : ℕ, ∀ x y, KP U x y ≤ KP M x y + (c : ENat) :=
  hU.2 M hM

/-- The invariance bound restated for `condK`, using the `KP = condK` bridge.
Since `KP` is definitionally `condK`, this is the same statement with the prefix
notation unfolded. -/
theorem IsOptimalPrefixConditional.invariance_condK {U M : Map}
    (hU : IsOptimalPrefixConditional U) (hM : IsPrefixDecompressor M) :
    ∃ c : ℕ, ∀ x y, condK U x y ≤ condK M x y + (c : ENat) := by
  simpa only [KP_eq_condK] using hU.invariance hM

end Kolmogorov
