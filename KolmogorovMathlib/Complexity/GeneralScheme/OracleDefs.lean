import KolmogorovMathlib.Complexity.GeneralScheme.OracleDefs.MonotoneDecompressors
import KolmogorovMathlib.Complexity.GeneralScheme.OracleDefs.MaximalSemimeasure

/-!
# Relativized complexities: definitions (SUV Section 6.4.1)

SUV Section 6.4.1 (printed p. 202) relativizes every complexity to an oracle `A ⊆ ℕ`: replace
"computable" or "enumerable" by "computable or enumerable relative to `A`". The library already
has:

* plain: `IsOptimalConditionalIn (charOracle A) U`;
* prefix: `PointToSet.IsOptimalOraclePrefix A U`, with existence `exists_optimalOraclePrefix`;
* relative enumerability: `PointToSet.IsREIn A`;
* relative lower semicomputability of reals: `PointToSet.IsLowerSemicomputableIn A`.

Here we add relativized decision, monotone and a priori complexity, the halting set `0'`
(`jumpSet`, with `charOracle jumpSet = haltingOracle`), and characteristic sequences.
-/
