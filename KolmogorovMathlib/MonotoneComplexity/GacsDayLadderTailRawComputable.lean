import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailRawComputable.Basic
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailRawComputable.Step
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailRaw
import KolmogorovMathlib.MonotoneComplexity.GacsDayGraftComputable
import KolmogorovMathlib.MonotoneComplexity.GacsDayRobustGrayComputable
import KolmogorovMathlib.MonotoneComplexity.GacsDayTailReserveComputable
import KolmogorovMathlib.MonotoneComplexity.GacsDayStageTwoComputable

/-!
# Computability of the index-erased tail controller

Every construction of `GacsDayLadderTailRaw.lean` lives on plain tuples of
naturals, rationals, Booleans and lists, so each is computable.  The three
statements consumed by the oracle assembly are

* `computable_rawQuery`     -- the single subcall input of a state,
* `computable_rawStepWith`  -- one controller transition, with the answer of
  the recursive call supplied as an ordinary argument,
* `computable_rawOutput`    -- the displayed move.

The remaining declarations are the intermediate steps.
-/
