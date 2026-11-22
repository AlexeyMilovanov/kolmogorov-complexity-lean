/-
Copyright (c) 2026 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Relativization.CommonInformation.MutualInformationBounds
import KolmogorovMathlib.Relativization.CommonInformation.CloneCoordinateChains
import KolmogorovMathlib.Relativization.CommonInformation.ExtractionIndexBounds
import KolmogorovMathlib.Relativization.CommonInformation.PairCloneBounds
import KolmogorovMathlib.Relativization.CommonInformation.PairPaddingBounds
import KolmogorovMathlib.Relativization.CommonInformation.SublinearDelta
import KolmogorovMathlib.Relativization.CommonInformation.FiniteIteration
import KolmogorovMathlib.Relativization.CommonInformation.CommonInformationTheorem
import KolmogorovMathlib.Relativization.CommonInformation.ConjectureReduction

/-!
# Extracting common information: Theorem 2 of Muchnik–Romashchenko

Section 1 of the paper (the bound on extractable common information, Conjecture 2, Theorem 2)
and Section 6 (the proof of Theorem 2), together with the remark of Section 2 that Conjecture 2
is a special case of Conjecture 3.  The conjectures themselves are the propositions
`Conjecture2` and `Conjecture3`; they are open and are not asserted.
-/
