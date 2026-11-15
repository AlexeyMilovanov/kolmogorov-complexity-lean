import KolmogorovMathlib.InformationLogic.SingletonFormulas.PeirceLogBound
import KolmogorovMathlib.InformationLogic.SingletonFormulas.PeirceComplexity
import KolmogorovMathlib.InformationLogic.SingletonFormulas.DisjunctionFormulas

/-!
# Some formulas and their complexity (SUV §13.3)

Peirce's law on singletons (Theorem 239, Problem 341), the formula `(x → y) → y` (Theorem 240)
and `(x → y) → z` (Theorem 241).  As in the book, a string `x` stands for the singleton `{x}`.

The common tool (SUV printed p. 405): `S` is the set of strings of length at most `n`; for every
total `τ : S → S` a program `l_τ` computing `τ` is found effectively from the table of `τ`
(Gödel property); a tuple is *compatible* with a solution `p` if `[p](l_τ)` has the prescribed
value for all `τ` with the prescribed value at a point.  Compatible tuples are enumerable from
`p` and `n`, and two of them coincide in the coordinates the argument needs.  The resulting
algorithms take `n` and one advice bit, so `problemK_le_of_partrec_advice` gives `O(log n)`.
-/
