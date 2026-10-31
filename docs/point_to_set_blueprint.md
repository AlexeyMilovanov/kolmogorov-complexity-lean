# Point-to-set blueprint and its Lean formalization

This file maps the 149 nodes of the blueprint of the point-to-set formalization (Emma
Dinowitz, *Point-to-set principles in dynamical systems*, arXiv:2607.21976, following the
corrected blueprint) to the Lean declarations that formalize them.  The Lean docstrings carry
the same references (search for `Blueprint node` in `KolmogorovMathlib/PointToSet` and
`KolmogorovMathlib/Oracle`).

## Conventions

* Every file path is relative to the repository root and lives under `KolmogorovMathlib/`;
  `PointToSet/...` means `KolmogorovMathlib/PointToSet/...` and `Oracle/...` means
  `KolmogorovMathlib/Oracle/...`.
* Every declaration lives in the namespace `Kolmogorov.PointToSet`; the blueprint's chapter
  prefixes `Conformal.`, `Packing.` and `Geometry.` are *not* Lean namespaces.  The first
  declaration of a node is written with its fully qualified name; companions are written
  without the prefix `Kolmogorov.PointToSet.` (the only other namespace is the auxiliary
  `NonuniformCounterexample` section of `PointToSet/BowenEquation/NonuniformCounterexample.lean`).
  A companion written `_bar` abbreviates `foo_bar`, where `foo` is the primary declaration
  of the same node (`Kolmogorov.PointToSet.foo`).
* Marks: **⚠** the paper's claim is false as printed and the Lean development proves a
  counterexample instead; **✎** the statement is corrected or repaired (hypotheses, indexing
  or scope changed with respect to the printed claim); **◇** the node is realized by a
  supporting definition, a bundled statement or under another name than the blueprint's.
* `σ : LimitSide` (lower/upper selector, `PointToSet/BSDimension/Defs.lean`) is how one
  Lean statement covers the blueprint's paired "lower / upper" claims.  Pointwise quantities
  are `ENNReal`/`EReal` pairs `(lower, upper)`, selected by `.1` / `.2`.
* Chapters: 1 foundations (oracles, order, computable metric), 2 pressure, 3 BS dimension and
  Bowen equations, 4 packing appendix, 5 conformal appendix, 6 geometry addenda, 7 symbolic
  sets and examples, 8 corrections and differently realized nodes.

## Main theorems

* **A**, lower pressure (`pressure:lower-pts`): `Kolmogorov.PointToSet.lowerPressure_pointToSet`
  (`PointToSet/Pressure/Lower/PointToSetPrinciple.lean`).
* **A**, upper pressure (`pressure:upper-pts`): `Kolmogorov.PointToSet.upperPressure_pointToSet`
  (`PointToSet/Pressure/Upper/PointToSetPrinciple.lean`).
* **B**, BS dimensions (`bs:point-to-set`): `Kolmogorov.PointToSet.bsPointToSet`
  (`PointToSet/BSDimension/Upper/PointToSetPrinciple.lean`).
* **C**, pointwise Bowen equation (`bs:pointwise-root`):
  `Kolmogorov.PointToSet.pointwiseBowenEquation`
  (`PointToSet/BowenEquation/PointwiseCriticalValue.lean`).
* **D**, critical-value part (`bs:set-critical`): `Kolmogorov.PointToSet.setBowenCriticalValue`
  (`PointToSet/BowenEquation/SetCriticalValue.lean`); repaired root (`bs:set-root-repaired`):
  `Kolmogorov.PointToSet.setBowenRootOfFiniteBSDimension`
  (`PointToSet/BowenEquation/SetRoot.lean`); counterexample to the printed root claim
  (`bs:counterexample-existence`): `Kolmogorov.PointToSet.counterexampleNonuniformBowenExistence`
  (`PointToSet/BowenEquation/NonuniformCounterexample.lean`).
* **E**, conformal dimension theorem (`conf:theorem-e`): `Kolmogorov.PointToSet.dimensionTheorem`
  and Bowen equation (`conf:bowen`): `Kolmogorov.PointToSet.bowenEquation`
  (`PointToSet/Conformal/TheoremE/DimensionTheorem.lean`).

## 1. Foundations

### 1.1 Relative computability and oracle prefix complexity (`Oracle/`)

* **`oracle:ce`** — Relative enumerability: a predicate is `A`-c.e. when it is the domain of an
  `O_A`-partial-recursive function, and an enumeration is a total `A`-computable
  `ℕ → Option α`.
  `Kolmogorov.PointToSet.IsREIn`, `IsEnumerationIn` (`Oracle/Basic.lean`).
* **`oracle:closure`** — The relative closure toolkit: pairing, composition, binding, mapping,
  natural recursion, unbounded search, optional search, conditionals and substitution.
  `Kolmogorov.PointToSet.relative_closure` (`Oracle/Basic.lean`); same file:
  `relative_closure_pair`, `_comp`, `_bind`, `_map`, `_nat_rec`, `_rfind`, `_rfindOpt`,
  `_cond`, `_subst` (written `relative_closure_*`).
* **`oracle:joins`** — Binary and countable joins: `A ⊕ B` is a least upper bound under
  Turing reducibility, and countable families of sets and tables are coded in one oracle.
  `Kolmogorov.PointToSet.oracle_joins` (`Oracle/Joins.lean`); same file: `oracleJoin`,
  `oracleCountableJoin`, `oracle_joins_right`, `_least`, `_countable`, `_tables`.
* **`oracle:operator`** — Exact finite-prefix representation: a function recursive in a
  total oracle is an ordinary partial computable operator on finite oracle prefixes, monotone
  under extension.
  `Kolmogorov.PointToSet.exists_exact_string_operator` (`Oracle/FinitePrefix.lean`).
* **`oracle:bounded`** — A bounded oracle enumeration: an `A`-computable total stage
  evaluator with persistent outputs that enumerates every `O_A`-recursive function.
  `Kolmogorov.PointToSet.oracleStage` (`Oracle/Universal/Enumeration.lean`); same file:
  `oracleEval`, `oracleStage_computable`, `_persistent`, `_universal`, `_evaluator`.
* **`oracle:enumeration`** — Oracle enumerations and strict thresholds: relative domains have
  total optional enumerations, there is a duplicate-free one, and `g < q` is `A`-c.e. for
  an upper-semicomputable `g`.  ◇ the duplicate-free enumeration is a separate statement.
  `Kolmogorov.PointToSet.relative_enumeration` (`Oracle/Universal/Enumeration.lean`);
  same file: `relative_enumeration_injective` (duplicate-free), `relative_enumeration_threshold`;
  `IsUpperSemicomputableOnIn` (`Oracle/Basic.lean`).
* **`oracle:universal`** — Optimal oracle prefix machines: for every `A` there is an
  `O_A`-recursive conditional prefix decompressor dominating all others up to a constant,
  chosen once and for all.  ◇ choice is the definition `optimalOraclePrefix`.
  `Kolmogorov.PointToSet.exists_optimalOraclePrefix` (`Oracle/Universal/Optimal.lean`);
  same file: `optimalOraclePrefix`, `exists_optimalOraclePrefix_spec`, `_finite`;
  `IsOptimalOraclePrefix` (`Oracle/Universal/Enumeration.lean`).
* **`oracle:complexity`** — Canonical oracle complexities `K^A(x | y)`, `K^A(x)`, the
  natural-number, pair and set versions, with `ℕ` values only after finiteness is proved.
  `Kolmogorov.PointToSet.oraclePrefixComplexity` (`Oracle/PrefixComplexity/Basic.lean`);
  same file: `oraclePrefixComplexityNat`, `oracleComplexity`, `oracleNatComplexity`,
  `oraclePairComplexity`, `oracleSetComplexity`, `oraclePrefixComplexity_coe`.
* **`oracle:kraft`** — Kraft inequality and finite sublevels: `∑ 2^{-K^A(i)} ≤ 1` and
  `{i : K^A(i) ≤ b}` is finite.
  `Kolmogorov.PointToSet.oracle_kraft` (`Oracle/PrefixComplexity/Basic.lean`); same file:
  `oracle_kraft_finite_sublevels`.
* **`oracle:tuple`** — Projection, tuple overhead and effective composition:
  `K^A(i) ≤ K^A(i,n) + c`, `K^A(i,n) ≤ K^A(i) + 2 log₂(n+1) + c`, and composition of
  partial computable operations costs a constant.
  `Kolmogorov.PointToSet.oracle_tuple_bounds` (`Oracle/PrefixComplexity/Basic.lean`); same
  file: `oracle_tuple_bounds_overhead`, `_composition`.
* **`oracle:monotone`** — Threshold sets and oracle monotonicity: `{w : K^A(w) < g(w)}` is
  `A`-c.e. for lower-semicomputable `g`, and `A ≤_T B` gives `K^B ≤ K^A + c`.
  `Kolmogorov.PointToSet.oracle_monotonicity` (`Oracle/PrefixComplexity/Basic.lean`);
  `oracle_monotonicity_threshold` (`Oracle/PrefixComplexity/MonotonicityThreshold.lean`);
  `IsLowerSemicomputableIn` (`Oracle/Basic.lean`).
* **`oracle:kc`** — Relative Kraft–Chaitin realization: an `A`-c.e. request sequence with
  total weight at most one is realized by an `A`-recursive prefix machine.
  `Kolmogorov.PointToSet.oracle_kraftChaitin` (`Oracle/KraftChaitin.lean`); same file:
  `oracleRequestMass`, `oracle_kraftChaitin_bound`.
* **`oracle:coding`** — Coding a summable upper-semicomputable cost: a finite mass
  `∑ 2^{-g(w)}` over an `A`-c.e. set gives `K^A(w) ≤ g(w) + c`.
  `Kolmogorov.PointToSet.oracle_coding_finite_mass` (`Oracle/KraftChaitin.lean`).

### 1.2 Order theory of oracles (`PointToSet/Order/`)

* **`order:attainment`** — Attained oracle minimization: an antitone oracle functional that
  is almost achieved above a base oracle is attained, and stays attained on the upper cone.
  `Kolmogorov.PointToSet.exists_achieving_oracle` (`PointToSet/Order/AchievingOracles.lean`);
  same file: `exists_achieving_oracle_stable`, `_all`, `_cone`, `_ennreal`, `_ennreal_stable`,
  `_ennreal_all`, `_ennreal_cone` (`EReal` and `ENNReal` versions).
* **`order:slack`** — A uniform additive cost disappears after division by a linearly growing
  quantity; hence oracle monotonicity passes to pointwise pressures and BS dimensions.
  `Kolmogorov.PointToSet.normalized_additive_slack` (`PointToSet/Order/NormalizedSlack.lean`);
  same file: `normalized_additive_slack_log`, `_logSlack`, `_pressure`, `_pressure_upper`,
  `_bs`, `_bs_upper`.

### 1.3 Computable metric presentations and dynamics

Files: `PointToSet/ComputableMetric/` and `PointToSet/Dynamics/`.

* **`metric:presentation`** — Fixed presentations: a complete separable metric space with one
  dense sequence `ι` chosen before quantifying over oracles, and dyadic radii.
  `Kolmogorov.PointToSet.Presentation` (`PointToSet/ComputableMetric/Presentation.lean`);
  same file: `dyadicRadius`.
* **`metric:names`** — Cauchy names, an `A`-computable metric table and represented maps.
  `Kolmogorov.PointToSet.ComputablePresentationIn`
  (`PointToSet/ComputableMetric/Presentation.lean`); same file: `IsCauchyName`,
  `IsRepresentedMapIn`, `basicBall`, `realPresentation`; `IsComputableRealFamilyIn`
  (`Oracle/Basic.lean`).
* **`metric:evaluation`** — A represented map sends computable input names to computable
  output names, uniformly, and composes effectively.
  `Kolmogorov.PointToSet.eval_computable_names` (`PointToSet/ComputableMetric/Presentation.lean`);
  same file: `eval_computable_names_uniform`, `_comp`.
* **`metric:admissible`** — An admissible upper cone exists: one oracle computes the metric
  table, `T` and the potentials, and every oracle above it is admissible.
  `Kolmogorov.PointToSet.exists_admissible_base`
  (`PointToSet/ComputableMetric/StaticDimensions.lean`);
  `IsAdmissible` (`PointToSet/ComputableMetric/Presentation.lean`).
* **`metric:bowen`** — Bowen topology: `d_n` is a metric for the original topology, Bowen balls
  are open, nonempty, contain an ideal point, and decrease in `n`.
  `Kolmogorov.PointToSet.bowen_ball_dense` (`PointToSet/Dynamics/BowenBalls.lean`); same file:
  `bowen_ball_dense_triangle`, `_open`, `_iff`, `_metric`, `_nonempty`, `_succ`, `_zero`;
  `bowenBall` (`PointToSet/Dynamics/BirkhoffComputability.lean`); `mem_bowenBall_iff`,
  `bowenBall_subset_of_le` (`PointToSet/Dynamics/BowenBalls.lean`).
* **`metric:birkhoff`** — Birkhoff values `S_nφ(ι i)` and orbit distances `d_n(ι i, ι j)` are
  `A`-computable uniformly in `(i, j, n, p)` for admissible `A`.
  `Kolmogorov.PointToSet.birkhoff_computableIn` (`PointToSet/Dynamics/BirkhoffComputability.lean`);
  same file: `bowenDist`, `birkhoff_computableIn_dist`; `birkhoff_computableIn_lt`, `_gt`
  (`PointToSet/Dynamics/BowenBalls.lean`).
* **`metric:oscillation`** — Positive small-scale oscillation bounds `ω_p → 0`, and the
  resulting `|S_nv(y) − S_nv(x)| ≤ nω_p` on Bowen balls of radius `2^{-p}`.
  `Kolmogorov.PointToSet.small_scale_oscillation` (`PointToSet/Dynamics/BowenBalls.lean`);
  same file: `small_scale_oscillation_birkhoff`.
* **`metric:min`** — Attainment of the finite-scale minimization of `K^A(i) + S_nφ(ι i)`
  (and of the ratio version) over the ideal points of a Bowen ball.
  `Kolmogorov.PointToSet.finite_scale_min_attained` (`PointToSet/Dynamics/BowenBalls.lean`);
  same file: `finite_scale_min_attained_ratio`, `finiteScalePressureCost`, `finiteScaleBSCost`.
* **`metric:static-dimension`** — Static point dimensions `dim^A(x)`, `Dim^A(x)` from the
  precision cost `K^A_δ(x)`, a finite attained minimum by density.
  `Kolmogorov.PointToSet.staticPointDimensions`
  (`PointToSet/ComputableMetric/StaticDimensions.lean`); same file:
  `staticPointDimensions_attained`, `_antitone`, `precisionComplexity`,
  `precisionComplexityNat`, `normalizedPrecisionComplexity`.
* **`metric:sampling`** — Sampling need not be monotone ✎: both normalized dimensions are
  computed along any scale sequence `δ_m → 0` with `log δ_{m+1}/log δ_m → 1`.
  `Kolmogorov.PointToSet.dimension_along_scales`
  (`PointToSet/ComputableMetric/DimensionAlongScales.lean`); same file:
  `dimension_along_scales_upper`.
* **`metric:change`** — Changing a presentation: above an oracle computing both presentations
  and mixed distances, effective dimensions, pressures and BS quantities do not depend on
  the dense sequence.  ◇ the node is spread over one statement per quantity.
  `Kolmogorov.PointToSet.presentation_change` (`PointToSet/ComputableMetric/StaticDimensions.lean`);
  `presentation_change_packing` (`PointToSet/ComputableMetric/DimensionAlongScales.lean`);
  `presentation_change_bs`, `_bs_upper` (`PointToSet/Dynamics/PresentationChangeBS.lean`);
  `presentation_change_pressure`, `_pressure_upper`, `DynamicalComparisonIn`,
  `finiteScalePressureRate`, `pointwisePressure`, `pointwiseBSDimension`, `lowerBirkhoffAverage`
  (`PointToSet/Dynamics/PointwiseQuantities.lean`).

## 2. Pressure (`PointToSet/Pressure/`)

The files are `PointToSet/Pressure/Defs.lean` (definitions), `Lower/*.lean` and `Upper/*.lean`.

### 2.1 Standing data, covers and scale-zero limits

* **`pressure:data`** — Standing data: a separable metric space, a continuous `T`, the dense
  sequence `ι`, a uniformly continuous potential `φ` with its oscillation moduli `ω_p`,
  `p ≥ p₀`.  ◇ bundled in one structure.
  `Kolmogorov.PointToSet.PressureData` (`PointToSet/Pressure/Defs.lean`); same file:
  `pressureLog`.
* **`pressure:bowen`** — Bowen geometry: `d_n` is a metric with the original topology, balls are
  open, membership is symmetric, `B_n(x, b) ⊂ B_n(y, a+b)` when `d_n(x,y) < a`, and `ι` is
  dense for every `d_n`.
  `Kolmogorov.PointToSet.bowen_geometry` (`PointToSet/Pressure/Lower/BowenGeometry.lean`);
  same file: `bowen_geometry_open`, `_symm`, `_subset`, `_dense`.
* **`pressure:recenter`** — Recentring and bounded distortion: balls can be recentered on
  ideal points at doubled radius, and `S_nφ(y) ≤ W_p(y,n) ≤ S_nφ(y) + nω_p`.
  `Kolmogorov.PointToSet.recenter_bowen_cover` (`PointToSet/Pressure/Lower/BowenGeometry.lean`);
  same file: `recenter_bowen_cover_distortion`, `_sup_bounds`, `_sup_finite`;
  `bowenPotentialSup` (`PointToSet/Pressure/Defs.lean`).
* **`pressure:lower-content`** — Centered and supremum-weight lower contents `m_N`, `m`
  over countable Bowen covers.  ◇ the two weights are the constructors of `PressureWeight`.
  `Kolmogorov.PointToSet.lowerContent` (`PointToSet/Pressure/Defs.lean`); same file:
  `BowenCoverFamily`, `IsBowenCover`, `PressureWeight`, `bowenCoverCost`, `lowerContentLimit`,
  `lowerPressureAt`, `pressureBallWeight`.
* **`pressure:critical`** — Critical-value calculus: `m_N` is monotone in `N`, antitone in
  `s`, decays by `2^{-(t-s)N}`, and is `0` above and `+∞` below the critical value.
  `Kolmogorov.PointToSet.lowerContent_critical` (`PointToSet/Pressure/Lower/BowenGeometry.lean`);
  same file: `lowerContent_critical_mono_cutoff`, `_antitone`, `_zero`, `_top`, `_cover`.
* **`pressure:lower-scale`** — Correct scale-zero lower pressure ✎: the supremum-weight
  small-scale limit exists and equals the centered `lowerPressure`; fixed-scale
  supremum-weight pressure need not be monotone in the radius.
  `Kolmogorov.PointToSet.lowerPressure_eq_centered`
  (`PointToSet/Pressure/Lower/BowenGeometry.lean`); same file: `_radius`, `_bounds`;
  `_limit`, `_nonmonotone` (`PointToSet/Pressure/Lower/CenteredContents.lean`); the
  definition `lowerPressure` is in `PointToSet/Pressure/Defs.lean`.
* **`pressure:upper-content`** — Upper capacity from fixed-order partition infima and its
  countable modification.  ◇ the printed `M^c_r` is `modifiedUpperPressure`.
  `Kolmogorov.PointToSet.modifiedUpperPressure` (`PointToSet/Pressure/Defs.lean`); same file:
  `partitionCoverCost`, `partitionSum`, `pressureRate`, `upperCapacity`, `upperPressure`.
* **`pressure:upper-scale`** — Correct scale-zero upper pressure and countable stability ✎:
  centered and supremum-weight capacities differ by at most `ω_p`, the scale-zero limit
  exists and equals `upperPressure`, and countable unions are stable.
  `Kolmogorov.PointToSet.upperPressure_scale_comparison`
  (`PointToSet/Pressure/Upper/ScaleComparison.lean`); same file: `_modified`,
  `_capacity_radius`, `_modified_radius`, `_centered_limit`, `_limit`, `_countable`,
  `_countable_limit` (each prefixed `upperPressure_scale_comparison`).
* **`pressure:partition-approx`** — Near-optimal fixed-order covers: partition infima are
  positive, admit covers of cost below twice the infimum, and a rate bound is achieved at
  every order.
  `Kolmogorov.PointToSet.exists_partitionSum_approximation`
  (`PointToSet/Pressure/Upper/ScaleComparison.lean`); same file:
  `exists_partitionSum_approximation_pos`, `_rate`.
* **`pressure:null-cover`** — Discrete null covers: a set of triples `(i, n, p)` with finite
  weight whose tails cover `Z` at every scale and cutoff.
  `Kolmogorov.PointToSet.IsNullPressureCover` (`PointToSet/Pressure/Defs.lean`); same file:
  `nullPressureMass`.
* **`pressure:uniform-net`** — Uniform pressure nets: families `E_{n,p,k}` with controlled
  exponential growth rate of `∑ 2^{S_nφ(ι i)}` covering `Z` uniformly in `n`.
  `Kolmogorov.PointToSet.IsUniformPressureNet` (`PointToSet/Pressure/Defs.lean`); same file:
  `uniformPressureSum`.
* **`pressure:pointwise`** — Pointwise pressure `P̲^A(x)`, `P̄^A(x)` from the infima
  `a^A_{n,p}(x)` of `(K^A(i) + S_nφ(ι i))/n` over ideal points in a Bowen ball; tail,
  good-radius and attainment lemmas.
  `Kolmogorov.PointToSet.pointwisePressure` (`PointToSet/Dynamics/PointwiseQuantities.lean`);
  `pointwisePressure_eq_tail`, `_eq_tail_upper`, `_attained`
  (`PointToSet/Pressure/Lower/PointwiseTails.lean`).
* **`pressure:pointwise-monotone`** — Scale and oracle monotonicity: `L^A_p`, `H^A_p` are
  nondecreasing in `p`, and pointwise pressures decrease when the oracle is strengthened.
  `Kolmogorov.PointToSet.pointwisePressure_mono_oracle`
  (`PointToSet/Pressure/Lower/PointwiseTails.lean`); same file:
  `pointwisePressure_mono_oracle_upper`, `_scale`, `_scale_upper`.

### 2.2 Discretization, effective pressure and the point-to-set principle

* **`pressure:lower-threshold`** — The lower-complexity threshold cover: for admissible `A`
  and rational `s`, `{(i,n,p) : K^A(i,n,p) < sn − S_nφ(ι i)}` is a null `s`-cover of
  `{x : P̲^A(x) < s}`.
  `Kolmogorov.PointToSet.lowerThreshold_isNullCover`
  (`PointToSet/Pressure/Lower/PointwiseTails.lean`); same file:
  `lowerThreshold_isNullCover_re`; `lowerPressureThreshold` (`PointToSet/Pressure/Defs.lean`).
* **`pressure:lower-to-null`** — Small classical covers produce a null cover: every real
  `s > P̲(Z)` admits a null `s`-cover.
  `Kolmogorov.PointToSet.exists_nullCover_of_lowerPressure_lt`
  (`PointToSet/Pressure/Lower/NullCovers.lean`).
* **`pressure:null-to-lower`** — A null `s`-cover gives `P̲(Z) ≤ s`.
  `Kolmogorov.PointToSet.lowerPressure_le_of_nullCover`
  (`PointToSet/Pressure/Lower/NullCovers.lean`); same file:
  `lowerContentLimit_centered_eq_zero_of_nullCover`.
* **`pressure:lower-discrete`** — Discretization of lower pressure: `P̲(Z)` is the infimum
  of the real `s` for which `Z` has a null `s`-cover.
  `Kolmogorov.PointToSet.lowerPressure_eq_iInf_nullCover`
  (`PointToSet/Pressure/Lower/NullCovers.lean`).
* **`pressure:upper-threshold`** — The upper-complexity threshold net:
  `{(i,n,p,k) : K^A(i) < sn − S_nφ(ι i) + k}` is an `A`-effective uniform `s`-net of
  `{x : P̄^A(x) < s}`.
  `Kolmogorov.PointToSet.upperThreshold_isUniformNet`
  (`PointToSet/Pressure/Upper/UniformNets.lean`); `upperThreshold_isUniformNet_re`
  (`PointToSet/Pressure/Upper/EffectiveEqSup.lean`); `upperPressureThreshold`
  (`PointToSet/Pressure/Defs.lean`).
* **`pressure:upper-to-net`** — Classical upper pressure gives uniform nets: every real
  `s > P̄(Z)` yields a uniform `s`-net.
  `Kolmogorov.PointToSet.exists_uniformNet_of_upperPressure_lt`
  (`PointToSet/Pressure/Upper/UniformNets.lean`).
* **`pressure:net-to-upper`** — A uniform `s`-net gives `P̄(Z) ≤ s`.
  `Kolmogorov.PointToSet.upperPressure_le_of_uniformNet`
  (`PointToSet/Pressure/Upper/UniformNets.lean`).
* **`pressure:upper-discrete`** — Discretization of upper pressure: `P̄(Z)` is the infimum
  of the real `s` for which `Z` has a uniform `s`-net.
  `Kolmogorov.PointToSet.upperPressure_eq_iInf_uniformNet`
  (`PointToSet/Pressure/Upper/UniformNets.lean`).
* **`pressure:effective-lower`** — Effective lower pressure: the infimum of the exponents of
  `A`-c.e. null covers; it bounds `P̲(Z)` from above, is monotone in `Z` and decreases when
  `A` is strengthened.
  `Kolmogorov.PointToSet.effectiveLowerPressure` (`PointToSet/Pressure/Defs.lean`);
  `effectiveLowerPressure_ge`, `_mono`, `_mono_oracle`, `_exists_cover`
  (`PointToSet/Pressure/Lower/NullCovers.lean`).
* **`pressure:effective-upper`** — Effective upper pressure, the same with `A`-c.e. uniform
  nets.
  `Kolmogorov.PointToSet.effectiveUpperPressure` (`PointToSet/Pressure/Defs.lean`);
  `effectiveUpperPressure_ge`, `_mono`, `_mono_oracle`, `_exists_net`
  (`PointToSet/Pressure/Upper/UniformNets.lean`).
* **`pressure:code-null`** — Coding an effective null cover: an `A`-effective null `s`-cover
  with rational `s` and admissible `A` gives `P̲^A(x) ≤ s` for all `x ∈ Z`.
  `Kolmogorov.PointToSet.pointwiseLower_le_of_effectiveNullCover`
  (`PointToSet/Pressure/Lower/PointToSetPrinciple.lean`).
* **`pressure:net-tail`** — Summable tails from a uniform exponential rate: in an effective
  uniform `s`-net, `K^A(i) + S_nφ(ι i) ≤ tn + c` for `t > s` rational and `n` large.
  `Kolmogorov.PointToSet.uniformNet_tail_weight_summable`
  (`PointToSet/Pressure/Upper/EffectiveEqSup.lean`); same file:
  `uniformNet_tail_weight_summable_mass`.
* **`pressure:code-net`** — An effective uniform `s`-net bounds pointwise upper pressure:
  `P̄^A(x) ≤ s` for all `x ∈ Z`.
  `Kolmogorov.PointToSet.pointwiseUpper_le_of_effectiveUniformNet`
  (`PointToSet/Pressure/Upper/EffectiveEqSup.lean`).
* **`pressure:effective-lower-equality`** — For admissible `A`, the effective lower pressure
  of `Z` is the supremum of the pointwise lower pressures.
  `Kolmogorov.PointToSet.effectiveLowerPressure_eq_iSup_pointwise`
  (`PointToSet/Pressure/Lower/PointToSetPrinciple.lean`).
* **`pressure:effective-upper-equality`** — The same for effective upper pressure.
  `Kolmogorov.PointToSet.effectiveUpperPressure_eq_iSup_pointwise`
  (`PointToSet/Pressure/Upper/EffectiveEqSup.lean`).
* **`pressure:lower-attainment`** — Some admissible oracle `B` satisfies
  `P̲^B_eff(Z) = P̲(Z)`, as does every oracle above it.
  `Kolmogorov.PointToSet.exists_oracle_effectiveLower_eq`
  (`PointToSet/Pressure/Lower/PointToSetPrinciple.lean`); same file: `_cone`.
* **`pressure:upper-attainment`** — The same for upper pressure.
  `Kolmogorov.PointToSet.exists_oracle_effectiveUpper_eq`
  (`PointToSet/Pressure/Upper/PointToSetPrinciple.lean`); same file: `_cone`.
* **`pressure:lower-pts`** — Main A, lower pressure: `P̲(Z) = min_A sup_{x∈Z} P̲^A(x)`,
  attained on an upper cone, for all oracles.
  `Kolmogorov.PointToSet.lowerPressure_pointToSet`
  (`PointToSet/Pressure/Lower/PointToSetPrinciple.lean`); same file: `_all_oracles`
  (every oracle bounds the pressure from above), `_cone`.
* **`pressure:upper-pts`** — Main A, upper pressure: `P̄(Z) = min_A sup_{x∈Z} P̄^A(x)`.
  `Kolmogorov.PointToSet.upperPressure_pointToSet`
  (`PointToSet/Pressure/Upper/PointToSetPrinciple.lean`); same file: `_all_oracles`, `_cone`.

### 2.3 Entropy

* **`pressure:entropy-definitions`** — Nonnegative entropies `h̲`, `h̄`, effective entropies
  and the orbit-complexity rates, valued in `ℝ≥0∞`.  ◇ one bundled statement collects the
  rate and attainment facts.
  `Kolmogorov.PointToSet.entropiesAndOrbitComplexities` (`PointToSet/Pressure/Defs.lean`);
  same file: `lowerEntropy`, `upperEntropy`, `effectiveLowerEntropy`, `effectiveUpperEntropy`,
  `orbitComplexity`, `orbitComplexityNat`, `orbitComplexities`;
  `entropiesAndOrbitComplexities_attained`, `_rate`, `_lower_rate`, `_upper_rate`, `_empty`,
  `_empty_upper`, `_empty_effective_lower`, `_empty_effective_upper`
  (`PointToSet/Pressure/Lower/PointToSetPrinciple.lean`).
* **`pressure:entropy-nonnegative`** — Zero-potential comparisons: for nonempty `Z` the
  classical and effective zero-potential pressures are nonnegative and equal the entropies.
  `Kolmogorov.PointToSet.entropy_eq_zeroPotentialPressure_of_nonempty`
  (`PointToSet/Pressure/Lower/EntropyZeroPotential.lean`); same file: `_upper`;
  the effective and inequality variants `_effective`, `_effective_upper`, `_nonneg`,
  `_nonneg_upper`, `_nonneg_effective`, `_nonneg_effective_upper`, `_le_effective`,
  `_upper_le_effective` are in `PointToSet/Pressure/Lower/EntropyZeroPotentialVariants.lean`.
* **`pressure:entropy-content`** — Residence-time entropy comparison: the paper's entropy from
  the sizes `2^{-n_r(U)}` of open sets equals `P̲(Z, T, 0)` after the scale-zero limit.
  `Kolmogorov.PointToSet.bowenEntropy_eq_lowerPressure_zero`
  (`PointToSet/Pressure/Lower/EntropyCharacterization.lean`); same file: `_nonempty`;
  `residenceTime`, `residenceSize`, `residenceContent`, `residenceEntropy`
  (`PointToSet/Pressure/Defs.lean`).
* **`pressure:entropy-pts`** — Effective entropy for every oracle, with no admissibility
  hypothesis, and the lower entropy point-to-set principle with an upper cone of oracles.
  `Kolmogorov.PointToSet.entropy_effectiveCharacterization_allOracles`
  (`PointToSet/Pressure/Lower/EntropyCharacterization.lean`); `_upper`, `_cone`, `_pointToSet`
  (`PointToSet/Pressure/Lower/EntropyPointToSet.lean`).
* **`pressure:upper-entropy`** — Upper entropy point-to-set principle and simultaneous
  oracle minimization of lower and upper entropy and pressure.
  `Kolmogorov.PointToSet.upperEntropy_pointToSet`
  (`PointToSet/Pressure/Upper/PointToSetPrinciple.lean`); same file: `_effective`, `_cone`,
  `_simultaneous`.

## 3. Barreira–Schmeling dimension and Bowen equations

Files: `PointToSet/BSDimension/` (definitions, `Lower/`, `Upper/`) and
`PointToSet/BowenEquation/`.

### 3.1 Definitions and the positive-average locus

* **`bs:pointwise`** — Total pointwise BS dimensions `d^A(x)`, `D^A(x)` from the ratios
  `K^A(i)/U_n(x_i)` over ideal points in a Bowen ball with positive denominator; empty
  infimum is `+∞`, order `0` is `+∞`.  ✎ ◇ the definition sits in the dynamics layer.
  `Kolmogorov.PointToSet.pointwiseBSDimension` (`PointToSet/Dynamics/PointwiseQuantities.lean`);
  `pointwiseBSDimension_antitone_radius` (`PointToSet/Dynamics/BowenBalls.lean`);
  `pointwiseBSDimension_eq_tail`, `_eq_good_radii`, `_eq_unfiltered_tail`
  (`PointToSet/BSDimension/Lower/Realizers.lean`).
* **`bs:realizer-bounds`** — Tail bounds on ideal realizers: if `0 < ℓ(x) ≤ b(x) < ∞`, then
  `ℓ − η ≤ U_n(x_i)/n ≤ b + η` for small radii and large `n`; with only `ℓ > 0` there is a
  uniform lower bound `ρn`.
  `Kolmogorov.PointToSet.birkhoffRealizerBounds` (`PointToSet/BSDimension/Lower/Realizers.lean`);
  same file: `birkhoffRealizerBounds_positive`, `abs_birkhoffSum_sub_le_of_mem_bowenBall`,
  `birkhoffSum_le_add_of_mem_bowenBall`; `upperBirkhoffAverage`
  (`PointToSet/BSDimension/Defs.lean`).
* **`bs:exhaustion`** — Positive-average exhaustion ✎: if `ℓ > 0` on `Z`, the countable sets
  `C_{N,ρ}` cover `Z`; no common positive lower bound is asserted.
  `Kolmogorov.PointToSet.positiveAverageExhaustion`
  (`PointToSet/BSDimension/Lower/Realizers.lean`); `positiveAveragePiece`
  (`PointToSet/BSDimension/Defs.lean`).
* **`bs:lower-mass`** — Lower covering mass `m_N(Z,s,r)`, `m(Z,s,r)` over countable families of
  Bowen balls, the exponent `d_r(Z)` and `d(Z) = sup_r d_r(Z)`; monotone in cutoff and
  radius.
  `Kolmogorov.PointToSet.lowerBSMass` (`PointToSet/BSDimension/Defs.lean`); same file:
  `bsBallWeight`, `bsCoverCost`, `lowerBSMassLimit`, `lowerBSDimensionAt`, `lowerBSDimension`;
  `lowerBSMass_weight`, `_mono_cutoff`, `_antitone_radius`, `_antitone_radius_limit`,
  `_antitone_radius_dimension`, `_cutoff_limit` (`PointToSet/BSDimension/Lower/Realizers.lean`);
  `lowerBSMass_scale_limit` (`PointToSet/BSDimension/Lower/MassDichotomy.lean`).
* **`bs:upper-capacity`** — Upper capacity `c_r(Z)` and the modified upper BS dimension
  `D(Z) = lim_r D_r(Z)` over countable decompositions, with restriction of pieces to `Z`.
  `Kolmogorov.PointToSet.upperBSDimension` (`PointToSet/BSDimension/Defs.lean`); same file:
  `bsPartitionCoverCost`, `bsPartitionSum`, `upperBSCapacityAt`, `modifiedUpperBSDimension`;
  `upperBSDimension_mono_capacity`, `_restrict_pieces`, `_mono`, `_antitone_capacity_radius`,
  `_antitone_radius`, `_scale_limit`, `_radius_limit`
  (`PointToSet/BSDimension/Upper/ScaleLimits.lean`).
* **`bs:upper-refinement`** — Positive refinement of upper capacity covers ✎: on a piece of
  `C_{N₀,ρ}`, `H_n(C,t,r) ≤ 2^{-(t-s)ρn} H_n(C,s,r)`, so the finiteness threshold can be
  replaced by the zero threshold after refinement.
  `Kolmogorov.PointToSet.upperCapacityPositiveRefinement`
  (`PointToSet/BSDimension/Upper/ScaleLimits.lean`); same file: `_tendsto`, `_modified`;
  `upperBSZeroCapacityAt`, `modifiedUpperBSZeroDimension` (`PointToSet/BSDimension/Defs.lean`).
* **`bs:discrete`** — Discrete null covers and uniform nets in `ℕ³`, `ℕ⁴`: a null `s`-cover has
  finite weight `∑ 2^{-sU_n(x_i)}` and covers at every scale and cutoff; a uniform net has
  bounded `limsup` slice weights.  ◇ `bsDiscreteWitnesses` packages the two witness kinds.
  `Kolmogorov.PointToSet.bsDiscreteWitnesses` (`PointToSet/BSDimension/Defs.lean`); same file:
  `IsNullBSCover`, `IsUniformBSNet`, `nullBSMass`, `uniformBSSum`.
* **`bs:effective`** — Effective BS dimensions `d^A_eff(Z)`, `D^A_eff(Z)`: infima of exponents
  of `A`-c.e. null covers and uniform nets, always above the classical ones.
  `Kolmogorov.PointToSet.effectiveBSDimensions` (`PointToSet/BSDimension/Defs.lean`); same
  file: `effectiveLowerBSDimension`, `effectiveUpperBSDimension`;
  `effectiveBSDimensions_ge`, `_null_upward` (`PointToSet/BSDimension/Lower/NullCovers.lean`);
  `effectiveBSDimensions_ge_upper` (`PointToSet/BSDimension/Upper/UniformNets.lean`);
  `effectiveBSDimensions_empty` (`PointToSet/BSDimension/Upper/PointToSetPrinciple.lean`).

### 3.2 Classical characterizations by covers and nets

* **`bs:recenter`** — Ideal recentering near a supremum: if `W_n(y,r)` is finite there is an
  ideal `x_i ∈ B_n(y,r)` with `U_n(x_i) > W_n(y,r) − a` and `B_n(y,r) ⊂ B_n(x_i,2r)`.
  `Kolmogorov.PointToSet.recenterNearBirkhoffSupremum`
  (`PointToSet/BSDimension/Lower/MassDichotomy.lean`).
* **`bs:subadditivity`** — Countable subadditivity of `m_N` and of `m` in the set argument.
  `Kolmogorov.PointToSet.lowerBSMassCountableSubadditive`
  (`PointToSet/BSDimension/Lower/MassDichotomy.lean`); same file: `_limit`.
* **`bs:lower-dichotomy`** — Exponent gap and lower dichotomy: finite mass at `s` gives zero
  mass at every `t > s`; hence mass is `∞` below `d_r(Z)` and `0` above.
  `Kolmogorov.PointToSet.lowerBSDichotomy` (`PointToSet/BSDimension/Lower/MassDichotomy.lean`);
  same file: `lowerBSDichotomy_top`, `lowerBSDichotomy_zero`.
* **`bs:null-lower`** — A null `s`-cover bounds the lower BS dimension: `d(Z) ≤ s`.
  `Kolmogorov.PointToSet.nullCoverBoundsLowerBS` (`PointToSet/BSDimension/Lower/NullCovers.lean`).
* **`bs:null-construction`** — Construction of a classical null witness: `d(Z)` is the infimum
  of exponents of null covers.
  `Kolmogorov.PointToSet.lowerBSNullCoverCharacterization`
  (`PointToSet/BSDimension/Lower/NullCovers.lean`); same file: `_iInf`.
* **`bs:net-lower`** — A uniform `s`-net bounds the upper BS dimension: `D(Z) ≤ s`.
  `Kolmogorov.PointToSet.uniformNetBoundsUpperBS`
  (`PointToSet/BSDimension/Upper/ScaleLimits.lean`).
* **`bs:net-construction`** — Construction of a classical uniform net: `D(Z)` is the infimum
  of exponents of uniform nets.
  `Kolmogorov.PointToSet.upperBSUniformNetCharacterization`
  (`PointToSet/BSDimension/Upper/UniformNets.lean`); same file: `_iInf`.

### 3.3 Effective dimensions and Main B

* **`bs:effective-lower-lower`** — Coding an effective null cover: an `A`-c.e. null `s`-cover
  gives `d^A(x) ≤ s` for all `x ∈ Z`, hence `sup_x d^A(x) ≤ d^A_eff(Z)`.
  `Kolmogorov.PointToSet.pointwiseLowerBSLeEffective`
  (`PointToSet/BSDimension/Lower/EffectiveEqSup.lean`); same file: `_iSup`.
* **`bs:effective-lower-upper`** — Kraft null-cover construction: `d^A_eff(Z) ≤ sup_x d^A(x)`.
  `Kolmogorov.PointToSet.effectiveLowerBSLeSup`
  (`PointToSet/BSDimension/Lower/NullCovers.lean`).
* **`bs:effective-lower-equality`** — Effective lower characterization:
  `d^A_eff(Z) = sup_{x∈Z} d^A(x)` for admissible `A`.
  `Kolmogorov.PointToSet.effectiveLowerBSEqSup`
  (`PointToSet/BSDimension/Lower/EffectiveEqSup.lean`).
* **`bs:effective-upper-lower`** — Coding truncated uniform slices: an `A`-c.e. uniform
  `s`-net gives `D^A(x) ≤ s` for all `x ∈ Z`.
  `Kolmogorov.PointToSet.pointwiseUpperBSLeEffective`
  (`PointToSet/BSDimension/Upper/OracleAttainment.lean`).
* **`bs:effective-upper-upper`** — Kraft uniform-net construction: `D^A_eff(Z) ≤ sup_x D^A(x)`.
  `Kolmogorov.PointToSet.effectiveUpperBSLeSup`
  (`PointToSet/BSDimension/Upper/UniformNets.lean`).
* **`bs:effective-upper-equality`** — Effective upper characterization:
  `D^A_eff(Z) = sup_{x∈Z} D^A(x)` for admissible `A`.
  `Kolmogorov.PointToSet.effectiveUpperBSEqSup`
  (`PointToSet/BSDimension/Upper/OracleAttainment.lean`).
* **`bs:oracle-attainment`** — Achieving BS oracles and upward preservation: an admissible
  `A₀` makes the effective dimension equal the classical one for every `B ≥_T A₀`.
  `Kolmogorov.PointToSet.bsOracleAttainment`
  (`PointToSet/BSDimension/Upper/OracleAttainment.lean`); same file: `_upper`.
* **`bs:point-to-set`** — Main B: `d(Z) = min_A sup_x d^A(x)` and `D(Z) = min_A sup_x D^A(x)`
  for `ℓ > 0` on `Z`, over all oracles, attained on an upper cone.
  `Kolmogorov.PointToSet.bsPointToSet` (`PointToSet/BSDimension/Upper/PointToSetPrinciple.lean`);
  same file: `bsPointToSet_upper`, `_mono_oracle`, `_cone`, `_empty`;
  `bsPointToSet_all_oracles` (`PointToSet/BSDimension/Upper/OracleAttainment.lean`).

### 3.4 Bowen equations

* **`bs:attainment`** — Attainment is a derived fact: the infimum defining the ratio `q^A_n`
  is attained on the good tail, and so is the affine one `(K^A(i) − sU_n(x_i))/n`.
  `Kolmogorov.PointToSet.idealRealizerInfimumAttained`
  (`PointToSet/BSDimension/Lower/Realizers.lean`); same file: `_affine`.
* **`bs:affine-slope`** — Two-sided affine slope bounds for `R_n(s)` and the pointwise
  pressure in the exponent `s`, in finite order, after liminf/limsup, and at scale zero.
  ◇ the lower/upper pair is the selector `LimitSide`.
  `Kolmogorov.PointToSet.pointwisePressureSlopeBounds`
  (`PointToSet/BowenEquation/SlopeBounds.lean`); same file: `_time`;
  `pointwisePressureSlopeBounds_scale`, `_strict` (`PointToSet/BowenEquation/Pointwise.lean`);
  `LimitSide`, `LimitSide.choose`, `LimitSide.timeLimit` (`PointToSet/BSDimension/Defs.lean`).
* **`bs:signed-comparison`** — Signed ratio–pressure comparison: `R_n(s)` and
  `Q_n = inf K^A(i)/U_n(x_i) − s` have the same sign and are sandwiched by `aQ_n`, `bQ_n`;
  consequences for the limits.
  `Kolmogorov.PointToSet.ratioPressureSignedComparison`
  (`PointToSet/BowenEquation/SlopeBounds.lean`); same file: `_finite`, `_positive`, `_zero`,
  `_negative`, `_limit_positive`, `_limit_negative`.
* **`bs:finite-scale-root`** — Finite-scale Bowen equation: with eventual bounds and finite
  orbit complexity, `d` is finite, the unique real zero of the pressure, with a two-sided
  sandwich.
  `Kolmogorov.PointToSet.finiteScalePointwiseBowenEquation`
  (`PointToSet/BowenEquation/SlopeBounds.lean`); same file: `_finite`;
  `finiteScalePointwiseBowenEquation_unique`, `_sandwich`
  (`PointToSet/BowenEquation/Pointwise.lean`).
* **`bs:pointwise-root`** — Main C, scale-zero pointwise Bowen equation: for
  `0 < ℓ(x) ≤ b(x) < ∞` and finite `k^A_σ(x)`, `d^A_σ(x)` is finite and the unique real
  zero of `s ↦ P^A_σ(x,s)`, with the `min/max` sandwich.
  `Kolmogorov.PointToSet.pointwiseBowenEquation`
  (`PointToSet/BowenEquation/PointwiseCriticalValue.lean`); same file: `_sandwich`, `_unique`;
  `pointwiseBowenEquation_finite` (`PointToSet/BowenEquation/Pointwise.lean`).
* **`bs:pointwise-critical`** — Infinite complexity and critical values: infinite complexity
  forces `d^A_σ(x) = ∞`, and in all cases `d^A_σ(x) = sup{s : P > 0} = inf{s : P ≤ 0}`.
  `Kolmogorov.PointToSet.pointwiseBowenCriticalValue`
  (`PointToSet/BowenEquation/PointwiseCriticalValue.lean`); same file: `_infinite`,
  `_infinite_pressure`, `_nonpositive`, `_positive_iff`;
  `pointwiseBowenCriticalValue_nonpositive_iff` (`PointToSet/BowenEquation/SetCriticalValue.lean`).
* **`bs:supremum-critical`** — Supremum critical value: `sup_{x∈Z} d^A_σ(x)` is both the
  positive-set supremum and the nonpositive-set infimum of the supremum pressure `F^A_σ`.
  `Kolmogorov.PointToSet.supPointwiseBSDimensionCriticalValue`
  (`PointToSet/BowenEquation/SetCriticalValue.lean`); same file: `_nonpositive`,
  `_at_dimension`.
* **`bs:dense-threshold`** — Dense agreement preserves sign thresholds: nonincreasing functions
  that agree on the nonnegative rationals have the same positive-set supremum and
  nonpositive-set infimum.  ◇ the thresholds are the definitions below.
  `Kolmogorov.PointToSet.monotoneDenseAgreementCriticalValue`
  (`PointToSet/BowenEquation/SetCriticalValue.lean`); `_nonpositive`
  (`PointToSet/BowenEquation/SetRoot.lean`); `positivePressureThreshold`,
  `nonpositivePressureThreshold` (`PointToSet/BSDimension/Defs.lean`).
* **`bs:set-slope-join`** — Set slope inequality and countable simultaneous attainment: the
  set pressure decreases in `s` (strictly, at rate `α`, for uniform `ℓ ≥ α`), and one oracle
  attains both BS minima and both pressure minima at all rational parameters.
  `Kolmogorov.PointToSet.setPressureSlopeAndRationalAttainment`
  (`PointToSet/BowenEquation/SetCriticalValue.lean`); same file: `_slope`, `_attainment`,
  `setPressure_eq_iInf_iSup_pointwisePressure`.
* **`bs:set-critical`** — Main D, valid critical-value part ✎: for `0 < ℓ ≤ b < ∞`,
  `d(Z)` and `D(Z)` are the positive-set suprema and nonpositive-set infima of the lower and
  upper set pressures `P^Z_∓(s)`, also as minima over oracle counterparts on an upper cone.
  `Kolmogorov.PointToSet.setBowenCriticalValue`
  (`PointToSet/BowenEquation/SetCriticalValue.lean`); same file: `_nonpositive`, `_cone`,
  `_oracles`, `_oracles_nonpositive`.
* **`bs:set-root-repaired`** — Repaired set-level existence theorem ✎: for nonempty `Z` with
  `0 < ℓ ≤ b ≤ β < ∞` and *finite BS dimension*, `P^Z_σ(d_σ(Z)) = 0`.  Finite entropy alone
  does not suffice (`bs:counterexample-existence`).
  `Kolmogorov.PointToSet.setBowenRootOfFiniteBSDimension`
  (`PointToSet/BowenEquation/SetRoot.lean`).
* **`bs:set-root-unique`** — Uniform lower bound ✎: with `0 < α ≤ ℓ`, finite entropy gives a
  real-valued, strictly decreasing set pressure with at most one zero and
  `d_σ(Z) ≤ h_σ(Z)/α`; with a common upper bound `β` the zero exists and equals `d_σ(Z)`.
  `Kolmogorov.PointToSet.setBowenRootUniqueness` (`PointToSet/BowenEquation/SetRoot.lean`;
  the formal uniqueness statement needs neither finite entropy nor `Z ≠ ∅`);
  same file: `_real`, `_strict`, `_dimension_le`, `_dimension_finite`;
  `setBowenRootUniqueness_exists` (`PointToSet/BowenEquation/NonuniformCounterexample.lean`).
* **`bs:counterexample-existence`** — ⚠ Counterexample to the uncorrected existence claim:
  finite entropy and bounded positive averages on a nonempty complete separable system do not
  give a real Bowen root; the witness has both entropies one, infinite BS dimensions and no
  real pressure zero.
  `Kolmogorov.PointToSet.counterexampleNonuniformBowenExistence`
  (`PointToSet/BowenEquation/NonuniformCounterexample.lean`).
* **`bs:constant-exponent`** — Constant asymptotic exponent: if `ℓ = b = α > 0` on `Z`, then
  `d(Z) = h_-(Z)/α` and `D(Z) = h_+(Z)/α` in `ℝ≥0∞`, including infinite entropy.
  `Kolmogorov.PointToSet.bsDimensionConstantExponent`
  (`PointToSet/BowenEquation/ConstantExponent.lean`); same file: `_upper`.

## 4. Packing appendix (`PointToSet/PackingEquivalences/`)

The pressure side lives in `PointToSet/PackingEquivalences/Pressure/` and the BS side in
`PointToSet/PackingEquivalences/BSDimension/`; shared definitions are in
`PointToSet/PackingEquivalences/Defs.lean`.  Below, `PSD` abbreviates the file
`PointToSet/PackingEquivalences/Pressure/PackingSeparatedDefs.lean`, `SD` abbreviates
`PointToSet/PackingEquivalences/Pressure/ScaleDichotomy.lean`, `MS` abbreviates
`PointToSet/PackingEquivalences/Pressure/ModifiedSeparated.lean`, `BPSD` abbreviates
`PointToSet/PackingEquivalences/BSDimension/PackingSeparatedDefs.lean`, `BRC` abbreviates
`PointToSet/PackingEquivalences/BSDimension/RadiusComparison.lean` and `BCC` abbreviates
`PointToSet/PackingEquivalences/BSDimension/CoveringComparison.lean`.

### 4.1 Packing, separated and covering pressure

* **`pack:supweight`** — Sup-weight estimates: at a radius with finite variation
  `S_nf ≤ W_f ≤ S_nf + nω_f(r)`, and Birkhoff sums differ by at most `nω_f(r)` on a ball.
  `Kolmogorov.PointToSet.supWeightBounds` (`PSD`); same file: `supWeightBounds_upper`, `_finite`,
  `_birkhoff`, `abs_birkhoffSum_sub_le_mul_variation`; `potentialVariation`
  (`PointToSet/PackingEquivalences/Defs.lean`).
* **`pack:countable-net`** — Countable maximal separated nets: a Bowen-separated set in a
  separable space is countable, and every `Z` has a maximal one whose balls cover `Z`.
  `Kolmogorov.PointToSet.countableSeparatedMaximalNet` (`PSD`); same file: `_countable`;
  `IsBowenSeparated` (`PointToSet/PackingEquivalences/Defs.lean`).
* **`pack:span-sep`** — Pressure spanning–separated comparison: `N_f(Z,n,2r) ≤ Q_f(Z,n,2r) ≤
  2^{nω_f(2r)} N_f(Z,n,r)`.
  `Kolmogorov.PointToSet.pressureSpanSep` (`PSD`); same file: `pressureSpanSep_upper`,
  `pressureBallWeight_le_mul_of_mem_bowenBall`, `separatedPressureSum`.
* **`pack:outer`** — Packing outer envelope: `𝒫_N`, `𝒫_0`, `𝒫` over disjointly decorated Bowen
  packings, the cutoff limit and the packing pressure at scale `r`.  ◇ the blueprint's
  `\lean` anchor is truncated; the central definition is `pressureOuterEnvelope`.
  `Kolmogorov.PointToSet.pressureOuterEnvelope` (`PSD`); same file: `packingPressureSum`,
  `packingPressureContent`, `packingPressurePrecontent`, `packingPressureAt`,
  `pressureOuterEnvelope_antitone_cutoff`, `_mono_content`, `_empty_content`, `_mono`,
  `_subadditive`, `_countable_zero`, `_empty`; `IsBowenPacking`
  (`PointToSet/PackingEquivalences/Defs.lean`).
* **`pack:pressure-dichotomy`** — Pressure dichotomy and scale limit: finite packing content at
  `s` is zero above `s`, and `P_pack(Z,f,r') ≥ P_pack(Z,f,r) − ω_f(r)`, so the scale-zero
  packing pressure exists.
  `Kolmogorov.PointToSet.pressureDichotomyScaleLimit` (`PSD`); `_threshold`, `_radius`,
  `_limit` (`SD`); `packingPressure` (`PSD`).
* **`pack:order-extraction`** — Mixed-order extraction: if `∑_{k≥N} 2^{-(s-t)k} b_k ≥ a` then
  some `k ≥ N` has `b_k ≥ (1 − 2^{-(s-t)}) a`.
  `Kolmogorov.PointToSet.extractOrder` (`SD`).
* **`pack:pack-to-sep`** — Packing bounds modified separated pressure:
  `P^sep_mUC(Z,f,2r) ≤ P_pack(Z,f,r) + ω_f(2r)`.
  `Kolmogorov.PointToSet.packBoundsModifiedSeparatedPressure` (`SD`); definitions
  `separatedUpperPressureAt`, `modifiedSeparatedPressureAt` (`PSD`).
* **`pack:sep-to-pack`** — Separated modification bounds packing: `P_pack(Z,f,r) ≤
  P^sep_mUC(Z,f,r)`.
  `Kolmogorov.PointToSet.modifiedSeparatedBoundsPackPressure` (`MS`).
* **`pack:pressure-equivalence`** — All three upper pressure definitions agree:
  `P_pack = P^sep_mUC = P^cov_mUC`.
  `Kolmogorov.PointToSet.pressureEquivalence`
  (`PointToSet/PackingEquivalences/Pressure/Equivalence.lean`); same file: `_covering`,
  `_upper`, `_separated_limit`, `_covering_limit`; `_capacity_lower`, `_capacity_upper`,
  `_restrict_pieces`, `_modified_lower`, `_modified_upper` (`MS`); definition
  `modifiedSeparatedPressure` (`PSD`).

### 4.2 Packing and separated BS dimension

* **`pack:bs-definitions`** — BS packing and separated capacity: replace the pressure weight by
  `2^{-aW_u}` to define the packing BS threshold `D_BSP`, the separated capacity `Q^u_n` and
  the countable modification `D^sep_mUC`, with dichotomy, threshold, radius and scale-limit
  comparison lemmas.  ◇ the bundle is `bsPackingSeparatedDefinitions`.
  `Kolmogorov.PointToSet.bsPackingSeparatedDefinitions` (`BPSD`); same file: `bsPackingSum`,
  `bsPackingContent`, `bsPackingPrecontent`, `bsPackingOuterEnvelope`, `packingBSDimensionAt`,
  `packingBSDimension`, `separatedBSSum`, `separatedBSZeroCapacityAt`,
  `modifiedSeparatedBSDimension`, `separatedBSDimension`, `_dichotomy`, `_threshold`; and
  in `BRC`: `_content_radius`, `_radius`, `_sum_radius`, `_separated_radius`, `_scale_limit`,
  `_separated_scale_limit`, `_negative`, `_empty`, `_empty_separated` (each prefixed
  `bsPackingSeparatedDefinitions`).
* **`pack:positive-pieces`** — Uniform-positive-average pieces: if `u̲ > 0` on `Z`, then `Z` is
  the union of the pieces `C(Z,N,ρ)`, and balls meeting or centered on a piece have
  `W_u ≥ ρn`.
  `Kolmogorov.PointToSet.uniformPositivePieces` (`BPSD`); same file: `_meeting`, `_centered`.
* **`pack:bs-finite-zero`** — Finite equals zero on uniform-positive pieces: finite `limsup` of
  separated or covering sums at `a` gives zero at every `b > a`.
  `Kolmogorov.PointToSet.bsFiniteZeroUniformPiece` (`BRC`); same file: `_covering`,
  `_separated_threshold`; `bsFiniteZeroUniformPiece_covering_threshold` (`BCC`);
  `separatedBSFiniteCapacityAt` (`BPSD`).
* **`pack:lower-bs-subadditive`** — Lower BS countable subadditivity of covering contents, before
  and after the cutoff limit.
  `Kolmogorov.PointToSet.lowerBSCountableSubadditive` (`BPSD`); same file: `_limit`.
* **`pack:lower-bs-dichotomy`** — Lower BS dichotomy for `u̲ > 0`: finite limiting lower BS
  content at `a` gives zero content at every `b > a`.  ◇ named with a `packing` suffix because
  `lowerBSDichotomy` is the node `bs:lower-dichotomy`.
  `Kolmogorov.PointToSet.lowerBSDichotomy_packing` (`BPSD`); same file:
  `lowerBSDichotomy_threshold`.
* **`pack:bs-span-sep`** — BS spanning–separated comparison: `M^u_n(Z,a,2r) ≤ Q^u_n(Z,a,2r) ≤
  M^u_n(Z,a,r)`, and the induced comparison of the countably modified dimensions.
  `Kolmogorov.PointToSet.bsSpanSepModified` (`BCC`); same file: `_upper`, `_finite_lower`,
  `_finite_upper`, `_refinement`, `_modified_lower`, `_modified_upper`.
* **`pack:bs-pack-to-sep`** — Packing BS bounds the separated modification:
  `D^sep_mUC ≤ D_BSP`.
  `Kolmogorov.PointToSet.bsPackBoundsSeparated` (`BCC`).
* **`pack:bs-sep-to-pack`** — The separated modification bounds packing BS: `D_BSP ≤ D^sep_mUC`.
  `Kolmogorov.PointToSet.bsSeparatedBoundsPack` (`BCC`).
* **`pack:bs-equivalence`** — Upper BS definitions agree:
  `D_BSP = D^sep_mUC = D^cov_mUC = Dim_BS` for `u̲ > 0`.
  `Kolmogorov.PointToSet.bsEquivalence` (`BCC`); same file: `_covering`, `_upper`,
  `_covering_limit`.
* **`pack:raw-threshold-counterexample`** — ⚠ Raw-threshold regression example: pointwise
  positive averages tending to one do not make the finite and zero raw BS capacity thresholds
  agree (finite thresholds are zero, zero thresholds are infinite), while the countable
  modification is zero.  Witness: binary shift, first-bit potential, sequences `0^j 1^∞`.
  `Kolmogorov.PointToSet.rawThresholdCounterexample`
  (`PointToSet/PackingEquivalences/BSDimension/RawThresholdCounterexample.lean`).

## 5. Conformal appendix (`PointToSet/Conformal/`)

Definitions are in `PointToSet/Conformal/Defs.lean`; the distortion estimates in
`PointToSet/Conformal/Distortion/`, the classical point-to-set principles in
`PointToSet/Conformal/Classical/` and Theorem E with its counterexamples in
`PointToSet/Conformal/TheoremE/`.  Below, `CD` abbreviates
`PointToSet/Conformal/Distortion/DistortionModuli.lean` and `DT` abbreviates
`PointToSet/Conformal/TheoremE/DimensionTheorem.lean`.

### 5.1 Conformal data and distortion

* **`conf:data`** — Uniform conformal data: a uniformly continuous `T` and potential `ζ` with
  `d(Tx,Ty) = 2^{ζ(x,y)} d(x,y)` below radius `r₀`; the positive finite average locus, the
  tempered-contraction and sublinear-orbit-growth predicates and their intersection.
  `Kolmogorov.PointToSet.UniformConformalData` (`PointToSet/Conformal/Defs.lean`); same file:
  `UniformConformalData.potential`, `positiveFiniteAverageLocus`, `HasTemperedContraction`,
  `HasSublinearOrbitGrowth`, `conformalLocus`.
* **`conf:moduli`** — Two distortion moduli: `u` is uniformly continuous, the multiplicative
  distortion `2^{u(x) ± τ/2}` holds below `δ₀`, and the potential modulus is at most twice the
  ratio-distortion modulus.
  `Kolmogorov.PointToSet.distortionModuli` (`CD`); same file: `_distance`, `_finite`,
  `_tendsto`, `_potential`, `_birkhoff`; `conformalDistortion`, `HasConformalDistortionBound`
  (`PointToSet/Conformal/Defs.lean`).
* **`conf:tempered-constant`** — Tempered constant with positive slack ✎: for `x ∈ ℬ` and
  `τ > 0` there is `0 < η ≤ 1` with `log₂ η ≤ S_nu(x) − S_ku(x) + nτ/2`.
  `Kolmogorov.PointToSet.temperedConstant` (`CD`).
* **`conf:iterate-distance`** — Finite-orbit estimates: `d(x,y) ≤ d(T^nx,T^ny) 2^{-S_nu(x)+nτ/2}`
  when the orbit stays `δ`-close, and a small initial distance forces closeness.
  `Kolmogorov.PointToSet.iterateDistance` (`CD`); same file: `_small_initial`.
* **`conf:ball-inclusion`** — Correctly indexed ball comparison ✎: Bowen balls of order `n+1`
  sit between metric balls of radii `ηδ2^{-S_nu(x)-nτ}` and `δ2^{-S_nu(x)+nτ}`.
  `Kolmogorov.PointToSet.ballInclusion` (`CD`).
* **`conf:nonmonotone-scales`** — Nonmonotone scale sampling ✎: liminf and limsup of `F(t)/t`
  for nondecreasing `F` equal those along any `t_n → ∞` with `t_{n+1}/t_n → 1`.
  `Kolmogorov.PointToSet.nonmonotoneScaleSampling` (`CD`); same file: `_upper`.
* **`conf:denominators`** — Orbit scales and BS denominators: for the radii `r_n^±` the scales
  `t_n^± → ∞` with ratio tending to one, and the BS denominators `S_{n+1}u(y)` on a Bowen ball
  are controlled by `S_nu(x)`.
  `Kolmogorov.PointToSet.orbitScaleDenominators` (`CD`); same file: `_ratio`, `_variation`;
  `orbitScaleDenominators_bounds` (`PointToSet/Conformal/Distortion/PointwiseDimension.lean`);
  `conformalOrbitRadius`, `conformalOrbitPrecision` (`PointToSet/Conformal/Defs.lean`).
* **`conf:pointwise`** — Pointwise conformal comparison: for every oracle,
  `dim^A(x) = dim^A_BS(x,T,u)` and `Dim^A(x) = Dim^A_BS(x,T,u)` on
  `𝒜(0,∞) ∩ ℬ ∩ 𝒞`.
  `Kolmogorov.PointToSet.pointwiseDimensionEqBS`
  (`PointToSet/Conformal/Distortion/PointwiseDimension.lean`); same file: `_upper`,
  `_order_shift`.

### 5.2 Classical dimensions and their point-to-set principles

* **`conf:hausdorff-interface`** — Hausdorff dimension via ideal dyadic balls: covers by
  ideal-centered dyadic balls with small `∑ 2^{-sr_j}` exist above `dim_H Z`, and conversely.
  `Kolmogorov.PointToSet.hausdorffDyadicIdealCover`
  (`PointToSet/Conformal/Classical/HausdorffCovers.lean`); same file: `_converse`;
  `IsIdealDyadicCover`, `idealDyadicCoverCost` (`PointToSet/Conformal/Defs.lean`).
* **`conf:hausdorff-any-oracle`** — `dim_H Z ≤ sup_{x∈Z} dim^A(x)` for every oracle `A`.
  `Kolmogorov.PointToSet.hausdorffLeSupPointDimension`
  (`PointToSet/Conformal/Classical/HausdorffPointToSet.lean`).
* **`conf:hausdorff-achieving`** — An oracle `A_H`, and every oracle above it, satisfies
  `sup_x dim^{A_H}(x) ≤ dim_H Z`.
  `Kolmogorov.PointToSet.hausdorffAchievingOracle`
  (`PointToSet/Conformal/Classical/HausdorffPointToSet.lean`); same file: `_stable`.
* **`conf:packing-box-interface`** — Packing equals modified upper box dimension: specified-radius
  metric packing dimension (weights `(2r)^s`, disjoint open balls) equals the countably
  modified upper box dimension on separable metric spaces.
  `Kolmogorov.PointToSet.packingEqModifiedUpperBox`
  (`PointToSet/Conformal/Classical/PackingModifiedBox.lean`);
  `packingEqModifiedUpperBox_open_covering`, `_coveringNumber`
  (`PointToSet/Conformal/Classical/PackingPointDimension.lean`);
  definitions `IsDisjointMetricBallFamily`, `IsMetricPacking`, `metricPackingSum`,
  `metricPackingContent`, `metricPackingPremeasure`, `metricPackingOuterMeasure`,
  `metricPackingDimension`, `upperBoxDimension`, `modifiedUpperBoxDimension`
  (`PointToSet/Conformal/Defs.lean`).
* **`conf:packing-any-oracle`** — `dim_P Z ≤ sup_{x∈Z} Dim^A(x)` for every oracle `A`.
  `Kolmogorov.PointToSet.packingLeSupPointDimension`
  (`PointToSet/Conformal/Classical/PackingPointDimension.lean`).
* **`conf:packing-achieving`** — An oracle `A_P`, and every oracle above it, satisfies
  `sup_x Dim^{A_P}(x) ≤ dim_P Z`.
  `Kolmogorov.PointToSet.packingAchievingOracle`
  (`PointToSet/Conformal/Classical/PointToSetPrinciple.lean`); same file: `_stable`.
* **`conf:classical-pts`** — Classical metric point-to-set interfaces:
  `dim_H Z = min_A sup_x dim^A(x)` and `dim_P Z = min_A sup_x Dim^A(x)`, with the minima
  restrictable to an upper cone.
  `Kolmogorov.PointToSet.classicalPointToSet`
  (`PointToSet/Conformal/Classical/PointToSetPrinciple.lean`); same file: `_upper`, `_cone`,
  `_cone_upper`, `_attained`.

### 5.3 Theorem E and the conformal Bowen equation

* **`conf:theorem-e`** — Theorem E: on `Z ⊆ 𝒜(0,∞) ∩ ℬ ∩ 𝒞` of a complete separable
  uniformly conformal system, `dim_H Z = dim_BS(Z,T,u)` (`dimH Z = lowerBSDimension …`) and
  `dim_P Z = Dim_BS(Z,T,u)`.  ◇ the packing half is stated for `metricPackingDimension` and
  separately for the decorated Bowen packing dimension.
  `Kolmogorov.PointToSet.dimensionTheorem` (`DT`); same file: `_upper`, `_packing`.
* **`conf:bowen`** — Scoped conformal Bowen consequence ✎: the corrected cut and root
  characterizations of the BS dimensions transfer to Hausdorff and packing dimension, and
  under uniform bounds `0 < α ≤ u̲ ≤ ū ≤ β` with finite entropy the pressure equation has its
  unique root at the classical dimension.
  `Kolmogorov.PointToSet.bowenEquation` (`DT`); same file: `_nonpositive`, `_oracles`,
  `_oracles_nonpositive`, `_cone`, `_root`, `_unique`, `_real`, `_strict`, `_dimension_le`,
  `_dimension_finite`, `_exists`.
* **`conf:ball-counterexamples`** — ⚠ Ball-comparison regression tests: the printed exact ball
  comparison fails with its stated Bowen indexing (a doubling map has an order-`n` ball of
  radius `δ2^{-(n-1)}`), and the tempered constant needs slack (a square-root coboundary has
  unbounded suffix sums at zero slack).
  `Kolmogorov.PointToSet.ballComparisonRegression`
  (`PointToSet/Conformal/TheoremE/BallComparison.lean`); same file: `_tempered`.
* **`conf:packing-diameter-counterexample`** — ⚠ Actual-diameter packing is a different
  convention: on a compact separable ultrametric space (the factorial product) packing
  weights `diam(B(x,r))^s` give dimension zero while the specified-radius weights `(2r)^s`
  give one.
  `Kolmogorov.PointToSet.actualDiameterPackingCounterexample`
  (`PointToSet/Conformal/TheoremE/ActualDiameterCounterexample.lean`); definitions
  `actualDiameterPackingContent`, `actualDiameterPackingPremeasure`,
  `actualDiameterPackingOuterMeasure`, `actualDiameterPackingDimension`
  (`PointToSet/Conformal/Defs.lean`).  The witness space and its estimates are built in the
  node-free modules `FactorialUltrametric.lean`, `FactorialPackingGeometry.lean`,
  `FactorialBoxBounds.lean` and `ActualDiameterBounds.lean` of the same directory.

## 6. Geometry addenda (`PointToSet/Geometry/`)

The center-independence results live in `PointToSet/Geometry/CoverCenters/` and the
infinite-entropy example in `PointToSet/Geometry/InfiniteEntropy/`.

* **`geometry:center-policies`** — Two policies for covering centers: ambient (centers in `X`)
  and self (centers in `E`), with the corresponding lower contents, fixed-order partition
  sums, upper capacities, modified pressures and BS analogues.
  `Kolmogorov.PointToSet.CoverCenterPolicy`
  (`PointToSet/Geometry/CoverCenters/CenterPolicies.lean`); same file: `lowerContentWithCenters`,
  `lowerContentLimitWithCenters`, `lowerPressureAtWithCenters`, `partitionSumWithCenters`,
  `upperCapacityWithCenters`, `modifiedUpperPressureWithCenters`,
  `modifiedUpperPressureWithCenters_ambient`, `unrestrictedSelfUpperPressure`,
  `coverCenterPressure`, `lowerBSMassWithCenters`, `lowerBSMassLimitWithCenters`,
  `lowerBSDimensionAtWithCenters`, `bsPartitionSumWithCenters`, `upperBSCapacityAtWithCenters`,
  `modifiedUpperBSDimensionWithCenters`, `unrestrictedSelfUpperBSDimension`,
  `coverCenterBSDimension`.
* **`geometry:center-relocation`** — Relocating a useful ball: a ball meeting `E` can be
  recentered at a point of `E` at doubled radius with controlled sup-weights.
  `Kolmogorov.PointToSet.relocateCoverBall`
  (`PointToSet/Geometry/CoverCenters/CenterPolicies.lean`); same file: `_sup`, `_pressure`,
  `_bs`, `lowerPressureAt_self_bounds`.
* **`geometry:pressure-centers`** — Lower and modified upper pressure do not depend on the
  center policy: `P^X(E,f,2r) ≤ P^self(E,f,2r) ≤ P^X(E,f,r) + ω_f(2r)`, and scale-zero values
  agree.
  `Kolmogorov.PointToSet.pressureIndependentOfCoverCenters`
  (`PointToSet/Geometry/CoverCenters/PressureIndependence.lean`); same file: `_content`,
  `_partition`, `_lower`, `_capacity`, `_modified`, `_limit`, `_unrestricted_sandwich`;
  `pressureIndependentOfCoverCenters_unrestricted`
  (`PointToSet/Geometry/CoverCenters/BSDimensionIndependence.lean`).
* **`geometry:bs-centers`** — The same for the lower and the modified upper BS dimension, for
  uniformly continuous `u` with `u̲ > 0` on `E`.
  `Kolmogorov.PointToSet.bsDimensionIndependentOfCoverCenters`
  (`PointToSet/Geometry/CoverCenters/BSDimensionIndependence.lean`); same file: `_content`,
  `_partition`, `_lower`, `_capacity`, `_modified`, `_limit`, `_unrestricted_sandwich`,
  `_unrestricted`.
* **`geometry:finite-alphabet-pressure`** — Finite-alphabet subsystem calculation: on the Baire
  space with `u = 1`, `P̲(Y_m,σ,−su) = P̄(Y_m,σ,−su) = log₂ m − s` and `dim_H Y_m = log₂ m`.
  `Kolmogorov.PointToSet.finiteAlphabetSubsystemPressure`
  (`PointToSet/Geometry/InfiniteEntropy/FiniteAlphabetSubsystems.lean`); same file:
  `finiteAlphabetSubsystem`, `finiteAlphabetSubsystemPressure_upper`;
  `finiteAlphabetSubsystemPressure_hausdorff`
  (`PointToSet/Geometry/InfiniteEntropy/NoBowenRoot.lean`).
* **`geometry:infinite-entropy-conformal`** — ⚠ Infinite entropy refutes the root clause of the
  introductory Theorem E: the Baire shift with `u = 1` is uniformly conformal, has a point in
  all three conformal loci with both averages one, yet all pressures, entropies and classical
  dimensions are `+∞` and no real Bowen root exists.
  `Kolmogorov.PointToSet.infiniteEntropyConformalNoBowenRoot`
  (`PointToSet/Geometry/InfiniteEntropy/NoBowenRoot.lean`).

## 7. Symbolic sets and examples

* **`pressure:symbolic`** — Symbolic-dynamics radius bookkeeping: for the shift on a finite or
  countable alphabet, `B_n(x, β^k) = B(x, β^{n+k-1})`, so lower and upper orbit complexities
  are `(−log₂ β)` times `dim^A(x)` and `Dim^A(x)`.
  `Kolmogorov.PointToSet.symbolic_orbitComplexity`
  (`PointToSet/Pressure/Lower/SymbolicOrbitComplexity.lean`); same file: `_lower`, `_upper`.
* **`pressure:isometry`** — Isometries: if `T` is an isometry and `X` is nonempty,
  `h̲(X,T) = 0`.
  `Kolmogorov.PointToSet.lowerEntropy_isometry`
  (`PointToSet/Pressure/Lower/SymbolicOrbitComplexity.lean`).
* **`pressure:symbolic-set`** — Hausdorff and packing dimensions of symbolic subsets: for
  `Z ⊆ 𝒜^ℕ` with the standard metric `β^{ℓ(x,y)}`, `dim_H Z = h̲(Z,σ)/c` and
  `dim_P Z = h̄(Z,σ)/c` with `c = −log₂ β`.
  `Kolmogorov.PointToSet.symbolic_setDimensions_eq_entropies` (`PointToSet/SymbolicSet.lean`);
  same file: `_upper_entropy`, `_upper`.
* **`example:digits`** — Complex digit sequences without a randomness detour: for every
  oracle `A` there is a binary `ξ` and a constant `c` with `K^A(ξ↾n) ≥ n − c`.
  `Kolmogorov.PointToSet.exists_complex_digit_sequence`
  (`PointToSet/Examples/MiddleThirds.lean`).
* **`example:cantor`** — The middle-thirds Cantor example: with the canonical computable dense
  presentation, both classical dimensions of the Cantor set are `log 2 / log 3`.  ◇ lower,
  upper and pointwise statements are in separate modules.
  `Kolmogorov.PointToSet.middleThirds_dimensions` (`PointToSet/Examples/MiddleThirds.lean`);
  same file: `middleThirdsPresentation`, `middleThirds_dimensions_computable`;
  `middleThirds_dimensions_pointwise` (`PointToSet/Examples/MiddleThirdsPointwise.lean`);
  `middleThirds_dimensions_upper` (`PointToSet/Examples/MiddleThirdsUpper.lean`).

## 8. Corrections and differently realized nodes

### 8.1 Claims false as printed (⚠) and their counterexamples

All five declarations are in `Kolmogorov.PointToSet`; the files are in the node entries above.

* `bs:counterexample-existence`: finite entropy does not give a Bowen root;
  `counterexampleNonuniformBowenExistence`.
* `conf:ball-counterexamples`: the exact ball comparison with the printed indexing and no
  slack fails; `ballComparisonRegression`, `ballComparisonRegression_tempered`.
* `conf:packing-diameter-counterexample`: actual-diameter packing differs from the standard
  specified-radius packing; `actualDiameterPackingCounterexample`.
* `pack:raw-threshold-counterexample`: finite and zero raw BS thresholds need not agree under
  pointwise positive averages; `rawThresholdCounterexample`.
* `geometry:infinite-entropy-conformal`: the root clause of Theorem E fails at infinite
  entropy; `infiniteEntropyConformalNoBowenRoot`.

### 8.2 Corrected or repaired statements (✎)

* `bs:set-root-repaired`, `bs:set-root-unique`, `bs:set-critical`: set-level Bowen equation
  needs finite BS dimension (not finite entropy), a uniform lower average bound for
  uniqueness, and only the critical-value part of Main D holds unconditionally.
* `conf:bowen`, `conf:ball-inclusion`, `conf:tempered-constant`: Bowen balls of order `n+1`,
  positive slack in the tempered constant, root clause only under uniform bounds and finite
  entropy.
* `pressure:lower-scale`, `pressure:upper-scale`: the scale-zero limit is taken for centered
  contents; fixed-scale supremum-weight pressure need not be monotone in the radius.
* `bs:exhaustion`, `bs:upper-refinement`, `bs:pointwise`, `metric:sampling`,
  `conf:nonmonotone-scales`: positive-average locus without a common bound, total pointwise
  definitions, and sampling along non-monotone scale sequences.

### 8.3 Nodes realized differently (◇)

* Namespaces: the blueprint's `Conformal.`, `Packing.` and `Geometry.` names (for example
  `Conformal.dimensionTheorem`, `Packing.bsEquivalence`, `Geometry.relocateCoverBall`) are all
  in the flat namespace `Kolmogorov.PointToSet`.
* Paired lower/upper statements are one statement with `LimitSide`, or a base theorem plus a
  `_upper` companion (`bsPointToSet`/`bsPointToSet_upper`, `pointwiseDimensionEqBS`/`_upper`).
* Definitions anchoring a node are supporting declarations: `bsDiscreteWitnesses`
  (`bs:discrete`), `effectiveBSDimensions` (`bs:effective`), `PressureData`
  (`pressure:data`), `PressureWeight` (`pressure:lower-content`),
  `entropiesAndOrbitComplexities` (`pressure:entropy-definitions`),
  `bsPackingSeparatedDefinitions` (`pack:bs-definitions`), `pressureOuterEnvelope`
  (`pack:outer`), `positivePressureThreshold` (`bs:dense-threshold`).
* `pack:lower-bs-dichotomy` is `lowerBSDichotomy_packing` (the name `lowerBSDichotomy` is
  `bs:lower-dichotomy`); `bs:set-root-unique` has its existence half
  `setBowenRootUniqueness_exists` in the counterexample file.
* `pressure:isometry` and `pressure:symbolic` live in the orbit-complexity file, and
  `pointwisePressure`, `pointwiseBSDimension` (nodes `pressure:pointwise`, `bs:pointwise`)
  are defined in `PointToSet/Dynamics/PointwiseQuantities.lean`, labelled `metric:change`.
* Nodes realized by a family of statements: `oracle:closure` (one lemma per closure
  operation), `metric:change` (one statement per quantity) and `order:slack` (one per
  consumer).
* The four factorial-product modules under `PointToSet/Conformal/TheoremE/` carry no node of
  their own; they support `conf:packing-diameter-counterexample`.

