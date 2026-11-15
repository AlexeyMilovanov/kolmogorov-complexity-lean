import KolmogorovMathlib.Complexity.GeneralScheme.Frequencies.LowerFrequency
import KolmogorovMathlib.Complexity.GeneralScheme.Frequencies.MaximalFrequency
import KolmogorovMathlib.Complexity.GeneralScheme.Frequencies.ExactFrequencies
import KolmogorovMathlib.Complexity.GeneralScheme.Frequencies.PartialSequences

/-!
# Limit frequencies and `0'`-a priori probability (SUV Section 6.4.3)

SUV Theorems 135 and 136 and Problems 210–213 (printed pp. 209–211). Let `f` be a computable
sequence of naturals. The *lower frequency* of `k` in `f` is
`liminf_n #{i < n | f i = k} / n`. These frequencies form a `0'`-lower-semicomputable
semimeasure, and an appropriate computable `f` realizes the maximal one, i.e. the `0'`-a priori
probability.

`0'`-lower semicomputability is the library's `PointToSet.IsLowerSemicomputableIn jumpSet`: the
set of pairs `(k, r)` with `r < q k` is `0'`-enumerable. A real number `x` is treated as the
function `fun _ : Unit => x`. The book's "`∑ qᵢ ≤ 1`" for non-negative `q` is written with
finite partial sums.
-/
