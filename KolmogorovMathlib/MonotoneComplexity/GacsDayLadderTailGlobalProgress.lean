import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailGlobalProgress.Part01
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailGlobalProgress.Part02
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailRound

/-!
# Global progress of a tail run

Group of the two-part argument that a tail run cannot go on forever: `Part01` sets up the sums
that measure the total request of a run — over entries, over frozen rounds and over source son
bases — and shows a per-round gain accumulates in them; `Part02` bounds the open slots and the
frozen son bases by the service threshold and concludes that the run has no open slots left once
its round budget is spent. The round-level facts they rest on come from the tail round module
imported alongside.
-/
