import KolmogorovMathlib.Complexity.RandomConditions.Bound.StageComputability
import KolmogorovMathlib.Complexity.RandomConditions.Bound.HeavyStringsEnumeration

/-!
# A random condition does not help: the group

Conditioning on a random string of length `n` lowers the complexity of `x` by only a bounded
amount.  `Bound.HeavyStringsEnumeration` enumerates the strings that many conditions do make
simple and counts them; `Bound.StageComputability` provides the effectiveness of that
enumeration.
-/
