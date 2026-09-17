import KolmogorovMathlib.Complexity.SelfComplexity.TokenGame.BoardMachinery
import KolmogorovMathlib.Complexity.SelfComplexity.TokenGame.LowerBound

/-!
# The token game: the group

The combinatorial game behind the self-complexity bound — tokens are placed on a board and the
opponent must respond, the score bounding how well a machine can know its own complexity.
`TokenGame.BoardMachinery` sets up the board and the strategies, `TokenGame.LowerBound` proves
the bound the game yields.
-/
