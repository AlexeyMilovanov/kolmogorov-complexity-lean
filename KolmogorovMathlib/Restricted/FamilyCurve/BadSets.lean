import KolmogorovMathlib.Restricted.BasicProfile
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.SlackArith

namespace Kolmogorov
open scoped ENNReal

/-!
## Retired independent bad-set interface

The former `restricted_bad_sets_volume` declaration was false.  For positive
`ambientLength`, take every proposed good set to be `stringsOfLength 0`.  Its
family, size, and complexity hypotheses can all hold, but the conclusion would
require a nonempty candidate pool whose elements both have positive length and
belong to `stringsOfLength 0`.

The VV proof instead couples bad-description enumeration to survivor-preserving
rebuilds of the good sets.  This module deliberately exports no theorem until
that process is represented by the M7 grid/rebuild/process interfaces.
-/

end Kolmogorov
