import KolmogorovMathlib.Restricted.FamilyCurve.Basic.Part01
import KolmogorovMathlib.Restricted.FamilyCurve.Basic.FiniteBadDescriptionCounting
import KolmogorovMathlib.Restricted.BasicProfile
import KolmogorovMathlib.Restricted.FamilyCurve.SampledRun
import KolmogorovMathlib.Restricted.FamilyCurve.Selector
import KolmogorovMathlib.Encoding.Tuples

/-!
# Basic estimates for restricted profile curves

This module collects the finite-grid construction and the counting estimates for bad
descriptions used in the restricted-family curve theorem. `Basic.Part01` builds and encodes the
grid, introduces scale states and proves the rebuild-density estimates.
`Basic.FiniteBadDescriptionCounting` bounds the descriptions that can spoil a candidate.

The later effective run combines these ingredients to select a model at every sampled scale.
-/
