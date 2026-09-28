import KolmogorovMathlib.MonotoneComplexity.Dimension.ChangeOfMeasure.Part01
import KolmogorovMathlib.MonotoneComplexity.Dimension.ChangeOfMeasure.DigressionP183
import KolmogorovMathlib.MonotoneComplexity.Dimension.Basic
import KolmogorovMathlib.MonotoneComplexity.Dimension.AbsolutelyNonRandom
import KolmogorovMathlib.MonotoneComplexity.Dimension.ImageMeasure
import KolmogorovMathlib.MonotoneComplexity.Dimension.EffectiveNullDiff
import KolmogorovMathlib.MonotoneComplexity.Dimension.DeficiencySemimeasure
import KolmogorovMathlib.MonotoneComplexity.Dimension.DyadicEndpoint
import KolmogorovMathlib.MonotoneComplexity.Dimension.ArithMeasurePreserving
import KolmogorovMathlib.MonotoneComplexity.LevinSchnorr.Infra
import KolmogorovMathlib.MonotoneComplexity.LevinSchnorr.Basic
import KolmogorovMathlib.MonotoneComplexity.LevinSchnorr.Criteria
import KolmogorovMathlib.MonotoneComplexity.GeneratorComposition
import KolmogorovMathlib.MonotoneComplexity.SemimeasureRealization
import KolmogorovMathlib.MonotoneComplexity.APrioriComplexity
import KolmogorovMathlib.MonotoneComplexity.ContinuousStreamMap
import KolmogorovMathlib.AlgorithmicRandomness.ExpectationBounded
import KolmogorovMathlib.MonotoneComplexity.ExpectationBoundedDeficiency
import Mathlib.Data.EReal.Basic
import Mathlib.Data.EReal.Operations

/-!
# Randomness with respect to different measures

Group of §5.9 of the source: how randomness and randomness deficiency behave when the measure is
changed. `Part01` carries §5.9.1 to §5.9.3 — the interval maps between a computable measure and
the uniform one (Theorem 121), the bridges between the `EReal` deficiency and the multiplicative
form, and the image-randomness theorem — and `DigressionP183` the almost-monotonicity of the
randomness deficiency (Theorem 124), which the source proves inside the argument for Theorem
123(b) and which is therefore placed before it. The dimension, deficiency and Levin–Schnorr
modules imported alongside supply the machinery both parts use.

Source: SUV §5.9, pp. 176–185.
-/
