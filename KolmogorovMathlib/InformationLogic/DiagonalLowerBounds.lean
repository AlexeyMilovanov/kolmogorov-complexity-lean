import KolmogorovMathlib.InformationLogic.DiagonalLowerBounds.ImplicationUpperBound
import KolmogorovMathlib.InformationLogic.DiagonalLowerBounds.CriticalImplications

/-!
# Lower bounds via diagonal functions (SUV §13.4, Theorems 242-244)

The formula `((x → y) → y) → (x ∨ y)` (Theorem 242) and its generalizations, the critical
implications on singletons (Theorems 243, 244).  The lower bounds use a computable diagonal
function (for Theorem 242: a pair of computably inseparable enumerable sets, i.e. a Boolean
diagonal function).
-/
