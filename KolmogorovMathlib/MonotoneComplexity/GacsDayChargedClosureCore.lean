import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedClosureCore.TailStep
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedClosureCore.FinalReplay
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedClosureCore.ExitWidth
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedReplay
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailFrontierDefs
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderCode
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedTailGlobalProgress

/-!
# Source-grounded closure leaves for the charged Gacs-Day tail

This file is the replacement frontier for the false positive-root branch of
the old hereditary/subfamily proof.  Its leaves talk only about the executable
`grayChargedStrategy`, its certified replay, and Gacs's designated charge.
They are ordered so that every global conclusion consumes the preceding local
interfaces; no arbitrary rational array or weak-to-robust shortcut appears.
-/
