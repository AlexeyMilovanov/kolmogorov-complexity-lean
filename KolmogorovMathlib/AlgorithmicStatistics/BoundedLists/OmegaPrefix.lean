import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.OmegaPrefix.Part01
import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.OmegaPrefix.Conditional
import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.EnumerationTail

/-!
# VS40 Section 4, Milestone B4: finite Omega equivalence (`prop:omega-equivalence`)

The source considers `Ω_m` as a bit string (of length `m + O(1)`), and its first
`k` bits `(Ω_m)_k`.  With the high-bit-first fixed-width encoding
`omegaFixedCode c m = fixedWidthNatCode (omegaCount c m) (m + 1)`, the "first `k`
bits" are literally `(omegaFixedCode c m).take k`.

This file develops the *exact* arithmetic bridge between a high-bit prefix and
the underlying number: taking the top `k` bits of a width-`width` code and
decoding yields exactly `n / 2 ^ (width - k)`, i.e. the number `n` truncated to
its high `k` bits.  Consequently the prefix pins `n` down to an interval of
width `2 ^ (width - k)`.  This is precisely the quantitative content the
`prop:omega-equivalence` reconstructions rely on (knowing `(Ω_m)_k` determines
`Ω_m` with error `< 2 ^ (m + 1 - k)`).
-/
