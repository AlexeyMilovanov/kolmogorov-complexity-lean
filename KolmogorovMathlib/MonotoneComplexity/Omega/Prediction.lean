import KolmogorovMathlib.MonotoneComplexity.Omega.Prediction.Part01
import KolmogorovMathlib.MonotoneComplexity.Omega.Prediction.REFamilyCriterion
import KolmogorovMathlib.MonotoneComplexity.Omega.Solovay
import KolmogorovMathlib.MonotoneComplexity.Omega.PredictCover
import KolmogorovMathlib.MonotoneComplexity.Omega.PaintEnum
import KolmogorovMathlib.MonotoneComplexity.Omega.DisjointCover
import KolmogorovMathlib.MonotoneComplexity.Omega.MultiCover

/-!
# Randomness and the prediction game

Group of §5.7.3: the observer's prediction game against a computable non-decreasing sequence of
rationals, and the randomness criteria it yields. `Part01` states the game
(`PredictionStrategy`, `ObserverWins`) and proves that the observer has a computable winning
strategy exactly when the limit is not random, with the game-free reformulation;
`REFamilyCriterion` recasts that as a covering condition by uniformly enumerable families and
deduces that non-randomness of lower semicomputable reals is preserved by sums. The covering and
enumeration modules imported alongside build the families used.

Source: SUV §5.7.3, pp. 161–164.
-/
