/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.InformationLogic.Problems
import KolmogorovMathlib.InformationLogic.Bridges
import KolmogorovMathlib.InformationLogic.Formulas
import KolmogorovMathlib.InformationLogic.Kripke
import KolmogorovMathlib.InformationLogic.OperationsComplexity
import KolmogorovMathlib.InformationLogic.OperationsProblems
import KolmogorovMathlib.InformationLogic.IntuitionisticBounds
import KolmogorovMathlib.InformationLogic.SingletonFormulas
import KolmogorovMathlib.InformationLogic.DiagonalLowerBounds
import KolmogorovMathlib.InformationLogic.MedvedevReduction
import KolmogorovMathlib.InformationLogic.KripkeComplexity
import KolmogorovMathlib.InformationLogic.NonTupleComplexity
import KolmogorovMathlib.InformationLogic.NonTupleLemmas

/-!
# Information and logic (SUV Chapter 13)

Shen, Uspensky, Vereshchagin, *Kolmogorov Complexity and Algorithmic Randomness*, Chapter 13:
problems as sets of strings, their complexity, the operations `∧`, `∨`, `∨~`, `→`, and the
relation between provability in intuitionistic propositional calculus and the complexity of
problems obtained from formulas.  See `docs/suv_chapter_13.md` for the item map.
-/
