import KolmogorovMathlib.MonotoneComplexity.Dimension.DyadicEndpoint.GapCover
import KolmogorovMathlib.MonotoneComplexity.Dimension.DyadicEndpoint.MapTotality
import KolmogorovMathlib.MonotoneComplexity.Dimension.DyadicEndpoint.MutualInversion
import KolmogorovMathlib.MonotoneComplexity.Dimension.ArithmeticStreamMap
import KolmogorovMathlib.MonotoneComplexity.LevinSchnorr.Basic

/-!
# Transfer of randomness along the interval maps

Group of the dyadic-endpoint argument behind Theorem 121: `GapCover` proves that a random
sequence never denotes a dyadic rational, `MapTotality` deduces that the interval maps are total
on random sequences and computes the reverse map as a binary expansion, and `MutualInversion`
shows the two maps invert each other. The arithmetic stream maps themselves and the
Levin–Schnorr criterion they are used with come from the modules imported alongside.

Source: SUV §5.9.1, pp. 176–177.
-/
