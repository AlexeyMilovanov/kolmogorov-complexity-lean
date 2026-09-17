import KolmogorovMathlib.MonotoneComplexity.GacsDayEmbedding.Part01
import KolmogorovMathlib.MonotoneComplexity.GacsDayEmbedding.Part02
import KolmogorovMathlib.MonotoneComplexity.GacsDayReplay
import KolmogorovMathlib.MonotoneComplexity.GacsDayGame
import KolmogorovMathlib.MonotoneComplexity.GacsDayBinaryEncoding
import KolmogorovMathlib.MonotoneComplexity.GacsDayBlockCode
import KolmogorovMathlib.AlgorithmicRandomness.RatComputable

/-!
# Embedding the Gács–Day game into a binary tree

Group of the reduction that replaces the wide request tree of the Gács–Day game by a binary one:
each branch index is written in a fixed-width binary block, so a strategy for the binary game
yields one for the original. `Part01` supplies the extension machinery and the coherence and
finite realisation of the intermediate request assignment; `Part02` assembles the reduction
itself (`serverPlayLegal_baseServerMove`, `exists_intermediateClientMove`,
`isWinningStrategyUnserved_binary_of_base`) and records what the frozen game interface still
leaves open. The block coding and the game itself come from the modules imported alongside.
-/
