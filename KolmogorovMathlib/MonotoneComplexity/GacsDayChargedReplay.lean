import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedReplay.SourceInvariant
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedReplay.Certification
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedReplay.CertifiedStates
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedSpendArithmetic
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailPointwise

/-!
# Replay certificate for the complete charged Gacs-Day controller

The advantage controller used the grandson coordinate as a round number.  Day's
spend phase instead uses four disjoint slices of the non-source two-level slots.
This file records that real layout directly and removes the obsolete coordinate
equality from the replay interface.
-/
