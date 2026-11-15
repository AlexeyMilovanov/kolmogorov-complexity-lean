/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Complexity.Applications.Primes
import KolmogorovMathlib.Complexity.Applications.TapeMachine
import KolmogorovMathlib.Complexity.Applications.CrossingSequences
import KolmogorovMathlib.Complexity.Applications.MultiheadAutomata
import KolmogorovMathlib.Complexity.Applications.LawsOfLargeNumbers
import KolmogorovMathlib.Complexity.Applications.ForbiddenSubstrings
import KolmogorovMathlib.Complexity.Applications.ComplexSubstrings
import KolmogorovMathlib.Complexity.Applications.LovaszLocalLemma
import KolmogorovMathlib.Complexity.Applications.ForbiddenSubsequences
import KolmogorovMathlib.Complexity.Applications.ComplexSubsequences
import KolmogorovMathlib.Complexity.Applications.MoserTardos
import KolmogorovMathlib.Complexity.Applications.LoomisWhitney
import KolmogorovMathlib.Complexity.Applications.BesicovitchDistance
import KolmogorovMathlib.Complexity.Applications.LipschitzBesicovitch

/-!
# Some applications of Kolmogorov complexity (SUV Chapter 8, printed pp. 233-260)

The theorems and problems of Chapter 8, with proofs; see `docs/suv_chapters_08_09.md` for the
map from book items to declarations.

* Section 8.1: `Primes`;
* Section 8.2: `TapeMachine`, `CrossingSequences`;
* Section 8.3: `MultiheadAutomata`;
* Section 8.4: `LawsOfLargeNumbers`;
* Section 8.5: `ForbiddenSubstrings`, `ComplexSubstrings`, `LovaszLocalLemma`,
  `ForbiddenSubsequences`, `ComplexSubsequences`, `MoserTardos`;
* Section 8.6: `LoomisWhitney`;
* Section 8.7: `BesicovitchDistance`, `LipschitzBesicovitch`.
-/
