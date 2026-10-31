/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Oracle.Universal.Enumeration
import KolmogorovMathlib.Oracle.Universal.Optimal

/-!
# Bounded oracle enumeration and optimal prefix machines

This directory builds the oracle-relative prefix machine on which every oracle statement of the
point-to-set principles rests. For a set `A ⊆ ℕ` used as a characteristic oracle, it produces a
conditional prefix decompressor that is recursive in `A` and optimal among all such machines up
to an additive constant (blueprint node `oracle:universal`). Prefix optimality is a predicate of
its own, separate from the plain `IsOptimalConditionalIn`.

* `Universal.Enumeration`: a bounded evaluator for functions recursive in the oracle, which
  dovetails the finite part of the oracle that is consulted with the running time, and the
  resulting relative enumerations.
* `Universal.Optimal`: the optimal oracle prefix machine, obtained by filtering each indexed
  evaluator to a prefix-free machine and taking the tagged union of the filters.

The optimal machine defines the oracle prefix complexity `K^A` in
`KolmogorovMathlib.Oracle.PrefixComplexity`. That complexity is the cost function in the
effective pressure and the effective Barreira–Schmeling dimension, so the machine underlies the
oracle minima in the point-to-set principles for pressure (Main A), for Barreira–Schmeling
dimension (Main B), and for the classical dimensions in the conformal setting (Main E).
-/
