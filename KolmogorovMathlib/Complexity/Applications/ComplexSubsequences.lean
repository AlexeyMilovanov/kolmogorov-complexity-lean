/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Complexity.Applications.ComplexSubsequences.SetPairComplexity
import KolmogorovMathlib.Complexity.Applications.ComplexSubsequences.MartinLofRandomFailure

/-!
# Complex subsequences (SUV Section 8.5.5, p. 251)

Theorem 162 is the complexity reformulation of Theorem 161.  A finite set of positions is coded by
the increasing list of its elements in binary, and a pair by `pairCode`, so the complexity of
`(F, ω(F))` given `t` is a definite quantity for the decompressor `V`.

The statement cannot be strengthened to a bound for the subsequence alone, since an arbitrary
subsequence can be all zeros: the complexity of `F` has to be taken into account.  This is the point
of p. 251.
-/
