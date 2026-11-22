/-
Copyright (c) 2026 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Relativization.Bunches.FiniteStageSelection
import KolmogorovMathlib.Relativization.Bunches.BunchCovers

/-!
# The method of bunches: Lemmas 5 and 6 of Muchnik–Romashchenko

Section 3.4 of the paper.  Lemma 5 is quoted there from Romashchenko's papers on extracting the
mutual information of a triple of strings; Lemma 6 is proved in the Appendix, and the same
greedy selection proves Lemma 5, every bunch being a semi-bunch.
-/
