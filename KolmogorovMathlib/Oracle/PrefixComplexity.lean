/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Oracle.PrefixComplexity.Basic
import KolmogorovMathlib.Oracle.PrefixComplexity.MonotonicityThreshold

/-!
# Canonical relative prefix complexity

This directory defines the oracle-relative prefix complexity `K^A` from the optimal machine of
`KolmogorovMathlib.Oracle.Universal` and proves the properties the point-to-set principles
need (blueprint nodes `oracle:complexity`, `oracle:kraft`, `oracle:monotone`, `oracle:tuple`).
Machine complexities take values in `ENat`; their natural-number versions are introduced only
after the finiteness statement. Natural numbers and pairs are fed to the machines through the
injective encodings `natBits` and `pairCode`.

* `PrefixComplexity.Basic`: the complexity functions on bit strings, naturals, pairs and sets
  of strings; the Kraft inequality, hence finiteness of complexity sublevel sets; tuple and
  composition bounds; and the invariance of complexity, up to a constant, under strengthening
  of the oracle.
* `PrefixComplexity.MonotonicityThreshold`: for a uniformly `A`-lower-semicomputable function
  `g`, the set `{w | K^A(w) < g w}` is `A`-computably enumerable. This is the form of the
  monotonicity of complexity that is used to build covers from coding arguments.

These facts feed the oracle Kraft–Chaitin coding, in which finite lists of covering centers are
packed into a single oracle, and the comparison of effective quantities with their classical
counterparts in the pressure, Barreira–Schmeling and conformal parts of the proof.
-/
