/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Complexity.Applications.ComplexSubstrings.LevinLemma
import KolmogorovMathlib.Complexity.Applications.ComplexSubstrings.ComplexityProfile

/-!
# Sequences without simple substrings (SUV Section 8.5.1, pp. 241-242)

Levin's lemma, Theorem 158.  The proof goes through Theorem 71, which is the library's
`exists_extension_KP_ge`, and the subadditivity of prefix complexity.

**The budget in Theorem 158.**  The book presents Theorem 158 as an instance of Theorem 157 with the
strings of length `n` and complexity less than `αn` as forbidden.  That is not literally an
instance: the number of such strings is only known to be below `2^{αn + 1}`, as `ncard_plainK_lt_lt`
states.  This is absorbed by a small change of `α`, which the statement
`exists_forall_substring_le_plainK` reflects by holding for all `α < 1`.
-/
