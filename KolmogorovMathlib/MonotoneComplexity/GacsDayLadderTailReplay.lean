import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailReplay.Invariants
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailReplay.StateAt
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailReplay.Part02
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailController

/-!
# Replay facts for Day's bounded gray-ladder controller

This file relates the executable fold to the mathematical sequence of parallel
recursive calls.  The elementary slot facts are kept separate because they are
also used by the legality and computability proofs.
-/
