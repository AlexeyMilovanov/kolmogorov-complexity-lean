import KolmogorovMathlib.MonotoneComplexity.Omega.SolovayFunctions.SolovayProperty
import KolmogorovMathlib.MonotoneComplexity.Omega.SolovayFunctions.Existence
import KolmogorovMathlib.MonotoneComplexity.Omega.SolovayFunctions.BusyBeavers
import KolmogorovMathlib.MonotoneComplexity.Omega.SolovayFunctions.BusyBeaverOmega
import KolmogorovMathlib.MonotoneComplexity.Omega.Prediction
import KolmogorovMathlib.MonotoneComplexity.Omega.BusyBeaverInfra
import KolmogorovMathlib.MonotoneComplexity.Omega.SolovayFunctionComputable
import KolmogorovMathlib.MonotoneComplexity.Omega.NullRealCantor
import KolmogorovMathlib.MonotoneComplexity.Omega.NullRealKraft
import KolmogorovMathlib.MonotoneComplexity.Omega.AntitoneSplit
import KolmogorovMathlib.MonotoneComplexity.Omega.ModulusRandom
import KolmogorovMathlib.MonotoneComplexity.Omega.CappedScaling
import KolmogorovMathlib.MonotoneComplexity.Omega.IntervalCover
import KolmogorovMathlib.MonotoneComplexity.Omega.NeighbourhoodCover
import KolmogorovMathlib.MonotoneComplexity.Omega.BusyBeaverSearch
import KolmogorovMathlib.MonotoneComplexity.Omega.OmegaBitsFromApprox
import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.BusyBeaver
import KolmogorovMathlib.Complexity.NatComplexity
import KolmogorovMathlib.Prefix.UpperSemicomputableBound

/-!
# Solovay functions, busy beavers and `Ω`

Group of §5.7.5 to §5.7.7. `SolovayProperty` defines what it means for a computable `f` with
convergent `∑ₙ 2 ^ (-f n)` to be a Solovay function, `Existence` constructs such functions and
shows the property depends only on the value of the sum, `BusyBeavers` introduces the busy-beaver
functions of prefix and plain complexity with the theorems relating them to Solovay functions and
convergence moduli, and `BusyBeaverOmega` proves that prefixes of `Ω` and values of the busy
beaver compute each other, with the total forms of those statements refuted. The remaining
imports supply the covering, search and approximation machinery the proofs run on.

Source: SUV §5.7.5–5.7.7, pp. 166–170.
-/
