/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Complexity.GeneralScheme.Regular
import KolmogorovMathlib.Complexity.GeneralScheme.Decision
import KolmogorovMathlib.Complexity.GeneralScheme.DecisionBasic
import KolmogorovMathlib.Complexity.GeneralScheme.DecisionMinimality
import KolmogorovMathlib.Complexity.GeneralScheme.DecisionVariants
import KolmogorovMathlib.Complexity.GeneralScheme.Comparing
import KolmogorovMathlib.Complexity.GeneralScheme.Pairs
import KolmogorovMathlib.Complexity.GeneralScheme.Conditional
import KolmogorovMathlib.Complexity.GeneralScheme.Numberings
import KolmogorovMathlib.Complexity.GeneralScheme.OracleDefs
import KolmogorovMathlib.Complexity.GeneralScheme.Relativized
import KolmogorovMathlib.Complexity.GeneralScheme.SetConditions
import KolmogorovMathlib.Complexity.GeneralScheme.LargeConditionsPlain
import KolmogorovMathlib.Complexity.GeneralScheme.LargeConditionsPrefix
import KolmogorovMathlib.Complexity.GeneralScheme.Enumeration
import KolmogorovMathlib.Complexity.GeneralScheme.Frequencies

/-!
# SUV Chapter 6: General scheme for complexities

Aggregator for the formalization of Shen–Uspensky–Vereshchagin, Chapter 6. The map from
book items to declarations is `docs/suv_chapter_06.md`.

* `Regular`: α-β and `(α, β) | γ` description modes (Sections 6.2, 6.3).
* `Decision`, `DecisionBasic`, `DecisionMinimality`, `DecisionVariants`: decision complexity
  `KR`, Theorem 127, Problems 192–196 (Section 6.1).
* `Comparing`, `Pairs`: Problem 197, Theorem 128, Problems 198–199, the pentagon bounds
  (Section 6.2).
* `Conditional`, `Numberings`: Theorem 129, Problems 200–203, Theorem 130 (Section 6.3).
* `OracleDefs`, `Relativized`: relativized complexities, Problems 204–205 (Section 6.4.1).
* `SetConditions`, `LargeConditionsPlain`, `LargeConditionsPrefix`, `Enumeration`:
  `C(x ‖ A)`, Problem 206, Theorems 131–134, Problems 208–209 (Section 6.4.2).
* `Frequencies`: Theorems 135–136, Problems 210–213 (Section 6.4.3).
-/
