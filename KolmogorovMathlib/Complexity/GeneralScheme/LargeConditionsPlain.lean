import KolmogorovMathlib.Complexity.GeneralScheme.LargeConditionsPlain.PlainJumpLimit
import KolmogorovMathlib.Complexity.GeneralScheme.LargeConditionsPlain.LimsupJump

/-!
# Large numbers as conditions: plain complexity (SUV Section 6.4.2)

SUV Theorems 131 and 132 (printed pp. 204–205). The limit of `C(x ‖ ≥ n)` and the `limsup` of
`C(x | n)` are both the `0'`-relativized complexity `C^{0'}(x)` up to `O(1)`. `C^{0'}` is
`plainK V` for an optimal `haltingOracle`-decompressor `V`.
-/
