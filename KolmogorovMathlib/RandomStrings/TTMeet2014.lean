/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.TTMeet2014.Main
import KolmogorovMathlib.RandomStrings.TTMeet2014.Effectivity.GameTable
import KolmogorovMathlib.RandomStrings.TTMeet2014.Effectivity.StateTwin
import KolmogorovMathlib.RandomStrings.TTMeet2014.ParityExample

/-!
# Cai, Downey, Epstein, Lempp, Miller (2014), Theorem 4.1

A formalization of Theorem 4.1 of *Random strings and truth-table degrees of Turing complete
C.E. sets* (LMCS 10(3:15), 2014): the only sets tt-reducible to `R_U` for every optimal prefix
machine `U` are the computable sets (`theorem_4_1`, `ttMeet_iff_computable` in `Main.lean`).
See `docs/random_strings_tt_meet_2014.md` for the relation to the paper, the source map, the
module map, and a gap found in the printed proof of Lemma 4.3 together with its repair.
-/
