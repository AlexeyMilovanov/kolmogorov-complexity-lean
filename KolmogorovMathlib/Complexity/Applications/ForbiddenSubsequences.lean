/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Complexity.Applications.ForbiddenSubsequences.RestrictionBounds
import KolmogorovMathlib.Complexity.Applications.ForbiddenSubsequences.ValidAssignments

/-!
# Forbidden subsequences (SUV Sections 8.5.3-8.5.4, pp. 247-250)

A *restriction* `(F, X)` is a finite set of indices with a string of the same length; it forbids the
sequences `ω` with `ω(F) = X`, where `ω(F)` lists the `ω_i`, `i ∈ F`, in the order of increasing
`i`.

The bound of Theorem 161 is on the number of restrictions of a given size that cover a given
position.  These are required to be finitely many, with at most `2^{αn}` of them: `Set.ncard` of an
infinite set is `0`, so a bound through `ncard` alone would say nothing about infinite families.
-/
