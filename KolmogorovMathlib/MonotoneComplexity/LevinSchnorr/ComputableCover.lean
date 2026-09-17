import KolmogorovMathlib.MonotoneComplexity.LevinSchnorr.ComputableCover.PaddedCover
import KolmogorovMathlib.MonotoneComplexity.LevinSchnorr.ComputableCover.Decompressor

/-!
# A computable summable function certifying randomness

Group of the construction behind Theorem 96: a total computable `f` with `∑ₙ 2 ^ (-f n) < ∞`
such that any sequence whose prefixes satisfy `C((ω)ₙ | n) ≥ n - f n - c` is Martin-Löf random
for the uniform measure. `PaddedCover` builds the padded cover from which `f` is read off —
every interval of a cover of the largest effectively null set is replaced by all its extensions
of one common length — and `Decompressor` turns that cover into a conditional decompressor,
proving the convergence of the series and the complexity bound it forces.

Source: SUV Theorem 96, pp. 152–154.
-/
