/-
Copyright (c) 2026 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Relativization.Existential.ProfileRelativization
import KolmogorovMathlib.Relativization.Existential.StochasticProfiles

/-!
# Existential formulae: Theorems 4 and 5 of Muchnik–Romashchenko

Section 2 of the paper; the proofs are in Section 4.  Both proofs establish the closeness of the
*extended* complexity profiles (`theorem4_extended`, `theorem5_extended`), which is stronger
than the closeness of the profiles asserted in the statements (`theorem4`, `theorem5`).
-/
