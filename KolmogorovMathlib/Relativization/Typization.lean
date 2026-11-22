/-
Copyright (c) 2026 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Relativization.Typization.TypizationSize
import KolmogorovMathlib.Relativization.Typization.CloneMajority
import KolmogorovMathlib.Relativization.Typization.OracleStability

/-!
# Typization: Lemmas 1–3 of Muchnik–Romashchenko

Section 3.2 of the paper; the proofs are in its Appendix.  `lemma3_relativized` is the form of
Lemma 3 with an oracle on either side, for arbitrary tuples; it contains both parts of Lemma 3
and the variant used at the end of the proof of Theorem 5.
-/
