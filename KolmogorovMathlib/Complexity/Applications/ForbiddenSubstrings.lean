/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Complexity.Applications.ForbiddenSubstrings.BiinfiniteSequences
import KolmogorovMathlib.Complexity.Applications.ForbiddenSubstrings.ComputableAvoidance
import KolmogorovMathlib.Complexity.Applications.ForbiddenSubstrings.EmergencyLevel

/-!
# Forbidden substrings: the combinatorial statements (SUV Section 8.5.1, pp. 241-244)

Sequences are `ℕ → Bool` and strings are `List Bool`, which are the library's `CantorSeq` and
`BitString`.  This module does not mention complexity, and imports only Mathlib.

**Occurrences.**  `OccursIn u ω` says that `u` is a substring of `ω`, of consecutive bits, at some
position: `ω_i ω_{i+1} … ω_{i+|u|-1} = u`.

**Budgets.**  `IsAtMostForbidden α F` is the hypothesis of Theorem 157: at most `2^{αn}` forbidden
strings of length `n`, for every `n`.  Since there are finitely many strings of a given length the
cardinal `Set.ncard` is meaningful (`finite_length_eq`).  `IsLessForbidden` is the strict version of
Theorem 159.

**Emergency levels.**  `emergency c F x` is Miller's `w_c(x)`, in `ℝ≥0∞` since `F` may be infinite.
The identity of p. 244 is `emergency_append_add`; it holds in `ℝ≥0∞` whether or not the sum is
finite.
-/
