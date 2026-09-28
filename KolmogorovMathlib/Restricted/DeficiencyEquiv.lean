import KolmogorovMathlib.Restricted.DeficiencyEquiv.ProgrammedFamilies
import KolmogorovMathlib.Restricted.DeficiencyEquiv.MarkedCodeSelectors
import KolmogorovMathlib.Restricted.DeficiencyEquiv.Part02
import KolmogorovMathlib.Restricted.Improving
import KolmogorovMathlib.Restricted.GapCountingIn
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Deficiencies
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.PaperTheorems

/-!
# Deficiency, optimality gap and description count in a restricted family

Group of the equivalence between the ways a model of a fixed enumerable family can be bad for a
string. `ProgrammedFamilies` presents families through the programs that enumerate them,
`MarkedCodeSelectors` runs the marked-code selection from such a program and makes it uniform,
and `Part02` proves the equivalence itself, together with the restricted forms of the deficiency
and improving-descriptions theorems. The two-part and gap-counting modules imported alongside
supply the unrestricted statements they refine.
-/
