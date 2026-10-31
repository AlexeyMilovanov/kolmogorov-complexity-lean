/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Encoding
import Mathlib.Computability.PartrecCode

/-!
# The fixed binary halting language

The code numbering is literally `Denumerable.ofNat Nat.Partrec.Code`. Inputs are
the canonical binary words fixed in `Encoding`, with data before code index. This
freezes the language used by the final statements without selecting a different
acceptable numbering or claiming a polynomial compiler between numberings.
-/

namespace Kolmogorov.Milovanov

/-- The native binary halting language: canonical `haltWord e y` with code `e` halting on `y`.
Blueprint node `native:halting-language`. Malformed words have no such representation. -/
def HBin : Set BitString :=
  {w | ∃ e y : ℕ, haltWord e y = w ∧
    ((Denumerable.ofNat Nat.Partrec.Code e).eval y).Dom}

end Kolmogorov.Milovanov
