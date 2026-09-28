import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedClosureSupport.SourceLedger
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedClosureSupport.Reserves
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedClosureSupport.FrozenCells
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedClosureCore
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedResolutionExact
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailOwnerIndex

/-!
# Source ledger and late-horizon support for the charged closure leaves

This file collects the accounting layer used by the charged final charge
transport: the two disjoint classes of resolved sources and their exact
cardinality, the displayed request at a threshold-raised source, one common
late service horizon backed by genuine tail family reserves, and the scalar
aggregate arithmetic behind the final mass bounds.
-/
