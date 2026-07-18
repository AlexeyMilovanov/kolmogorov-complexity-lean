import KolmogorovMathlib.Restricted.BasicProfile
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.SlackArith

namespace Kolmogorov
open scoped ENNReal

/-!
## Retired independent good-set interface

The former `good_set_sequence` declaration admitted a constant sequence
`stringsOfLength 0`; it did not connect the sets to the ambient length,
surviving candidates, or the target curve.  Although that weak statement was
inhabited, it could not support M7 and made the old bad-set interface visibly
false.

The replacement must construct good sets inside the coupled finite process:
when new bad descriptions delete survivors, a suffix of sampled grid levels is
rebuilt using maximum-intersection cover members.  This module deliberately
exports no independent sequence theorem.
-/

end Kolmogorov
