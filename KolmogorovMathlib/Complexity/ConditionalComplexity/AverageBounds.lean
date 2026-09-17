import KolmogorovMathlib.Complexity.ConditionalComplexity.AverageBounds.Tail
import KolmogorovMathlib.Complexity.ConditionalComplexity.AverageBounds.Expectation

/-!
# Average conditional complexity

How `C(x | y)` behaves as `y` ranges over the strings of one length.  `AverageBounds.Tail`
proves the tail bound of SUV Exercise 42 — few conditions make `x` much simpler than the
length alone does — and `AverageBounds.Expectation` the corresponding bound in expectation.
-/
