/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/

import KolmogorovMathlib.Restricted.BasicProfile
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.SlackArith

/-!
## Good sets in the coupled construction

The M7 good sets belong to the coupled finite process: when new bad
descriptions delete survivors, a suffix of sampled grid levels is rebuilt
using maximum-intersection cover members.  Their ambient length, surviving
candidates, and target-curve bounds are therefore supplied by the coupled-run
invariants rather than by an independent sequence interface.  This module
deliberately exports no separate good-set theorem.
-/

namespace Kolmogorov
open scoped ENNReal

end Kolmogorov
