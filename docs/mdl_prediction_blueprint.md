# Prediction and MDL for infinite sequences: blueprint and Lean map

Alexey Milovanov's [*Prediction and MDL for infinite sequences*](https://doi.org/10.1007/s00224-024-10180-0)
(*Theory of Computing Systems*, 2024; [arXiv:2005.03467](https://arxiv.org/abs/2005.03467),
whose preprint has a different title) selects, at each observed binary prefix, a computable
probability measure minimizing a complexity-penalized description score and uses its conditional
probability to predict the next bit. The Lean development in `KolmogorovMathlib/MDLPrediction/`
formalizes the global and effective-class predictors, their convergence and squared-error bounds,
the finite-block machinery behind the class bounds, and a counterexample to a measure-uniform
claim in the printed proof. All declarations in the map below belong to
`Kolmogorov.MDLPrediction`; the four source-audit remarks are documented in the blueprint and
the module prose without separate Lean declarations.

## Main theorems

- **Theorem 4:** `predictor_merges_on_random` — every global minimizer choice eventually
  predicts the same bit probabilities as a computable source on each of its Martin-Löf random paths.
- **Theorem 7:** `pathwise_sq_bound` — a finite randomness budget gives a finite, explicit
  squared-error sum for the global predictor along a path.
- **Theorem 3:** `expected_sq_bound` — the global predictor has a finite expected squared-error
  sum, bounded in terms of the source's description complexity.
- **Theorem 9:** `class_pathwise_sq_polynomial` — for an effective finite-mixture class, the
  class predictor's pathwise squared-error sum has a polynomial bound.
- **Theorem 10:** `class_expected_sq_polynomial` — under the same class conditions, the
  expected squared-error sum has a polynomial bound.
- **Counterexample to uniform Lemma 5:** `uniformPrefixDropFalse` — no one constant gives
  the printed logarithmic prefix-deficiency drop bound for all computable source measures.

## Corrections to the printed paper

Line numbers below refer to `main.tex` of the arXiv v3 source of the paper. The listed Lean
results use proper computable measures
as source models.

- **Measure scope (106–123).** The paper defines its source distributions as proper measures
  and its universal `M` as a semimeasure; a purported remark extending every result to
  semimeasures is absent. A semimeasure's two bit conditionals need separate treatment. Lean
  proves the prediction results for proper computable measures and uses a semimeasure only as
  the intermediate domination object (`Model`, `meanTree_uniform_domination`).
- **Global versus class minimization (150–166, 192–194, 444–464).** The global score ranges
  over all computable proper measures and defines an ideal, generally uncomputable predictor;
  Section 4 changes both the domain and complexity to an effective class. A minimizer at a
  zero-mass prefix need not exist. Lean separates `score` and `classScore`, makes the positive
  mass condition explicit, and proves the results for every classical minimizer choice.
- **Theorem 7 indexing (307–312, 318–381, 411, 420).** The displayed sums omit the
  empty-prefix prediction, while the product argument controls positions before a positive
  prefix. Lean's `pairwise_prefix_sq_bound` counts positions `0 ≤ i < n`, and
  `pathwise_sq_bound` charges the selected time separately.
- **Pairwise intermediate object (328–334).** The paper calls the pointwise mean-conditional
  process a computable measure. Deciding a cylinder has zero mass is not available from the
  repository's two-sided dyadic measure approximation interface. Lean constructs a lower
  semicomputable continuous tree semimeasure (`meanTree_uniform_domination`) with the required
  common-positive product values.
- **Deficiency convention (208–224, 239–243, 429–441).** The paper rounds `-log₂ M(x)`
  upward and writes a finite-path deficiency at line 440 using infinite-path notation.
  Lean uses unrounded `KA` and natural multiplicative `PathBudget` layers, with the
  corresponding additive rounding slack and no finite bound claimed for nonrandom paths.
- **Lemma 4 counting route (491–499).** The printed proof groups distinct computable
  distributions by complexity and has a score-sign typo at line 493. Equality of computable
  distributions is not generally decidable, so Lean enumerates numeric indices and builds
  complete blocks (`enum_indices_ce`, `enum_blocks`) instead.
- **Uniform Lemma 5 (503–534; use at 565–574).** The printed proof treats the constant in
  the prefix-deficiency drop bound as independent of `Q`, though constructing its auxiliary
  semimeasure must encode `Q` and costs `K(Q)`. Lean proves `uniformPrefixDropFalse`: atomic
  measures `Q_z` give a deficiency drop linear in `|z|`, beyond any uniform logarithmic loss.
  A fixed-measure version needs a constant depending on that measure; it cannot justify the
  printed varying-measure counting step.
- **Theorems 9–10 counting (560–574).** The printed multiplicative deficiency buckets omit
  nonpositive deficiencies; its mass comparison loses a factor exponential in the bucket
  parameter, and line 573 drops an `O(log a)` term. The resulting count is not polynomial.
  Lean proves `everWinners_layer_polynomial` by score comparison with complete-block mixtures,
  then derives `class_pathwise_sq_polynomial` and `class_expected_sq_polynomial` without those
  buckets or uniform Lemma 5.
- **Theorem 10 and class notation (454–457, 477–483, 560–563, 585–587, 592).** The printed
  display drops the bit argument from `H_A`, uses `H` where the proof needs `H_A`, mixes global
  and relative complexities, and describes the last result as exponential in the final
  question. Lean uses `classPredictor` with its bit argument and class complexity in the
  class theorems; Theorem 10 is polynomial, while the exponential scope belongs to the
  unrestricted Theorem 3.

<!-- BEGIN GENERATED MDL MAP -->
## Module index

Each line names one Lean module under `KolmogorovMathlib/MDLPrediction/`.

- `Analysis/LogGap.lean` — Elementary logarithmic and binary mean gaps.
- `Analysis/Products.lean` — Product inequalities for conditional discrepancies.
- `Analysis/Series.lean` — A geometric deficit moment.
- `Class/BlockCode.lean` — Prefix descriptions and mixture bounds for complete blocks.
- `Class/Charge.lean` — Polynomial winner count and one-winner path charge.
- `Class/Compiler.lean` — Uniform class-to-measure index compiler.
- `Class/Enumeration.lean` — Duplicate-free discovery of short-program outputs.
- `Class/Exclusion.lean` — Exclusion of full-block indices and polynomial ever-winner count.
- `Class/Expectation.lean` — Expected squared error for an effective class.
- `Class/Mixture.lean` — Cylinder mass of a finite class mixture.
- `Class/Path.lean` — Polynomial pathwise error for effective mixture classes.
- `Class/Presentation.lean` — Effective indexed classes of computable measures.
- `Class/Relative.lean` — Relative complexity, class score, and minimizers.
- `Class/Replay.lean` — Partial replay of complete discovery blocks.
- `Class/Winner.lean` — Bounds on a class minimizer along a budgeted path.
- `Core/Argmin.lean` — Global score minimizers and their predictors.
- `Core/ArgminGeneric.lean` — Minimum of a score with finite complexity sublevels.
- `Core/Budget.lean` — A priori path budgets.
- `Core/FinitePrograms.lean` — Finite prefix-complexity sublevels.
- `Core/Index.lean` — Indices and attained complexity of computable models.
- `Core/Model.lean` — Computable probability models and MDL scores.
- `Core/TwoPart.lean` — Uniform two-part code bound.
- `Core/UniformModel.lean` — Uniform computable competitor.
- `Core/Winner.lean` — Bounds for a winner on a budgeted path.
- `Counterexample/Atomic.lean` — Incompressible branch words and an atomic rational witness.
- `Counterexample/Deficiency.lean` — Deficiency drop along the atomic branch.
- `Counterexample/Main.lean` — Failure of a measure-uniform prefix-deficiency drop.
- `Expectation/Layers.lean` — Least natural path budgets and geometric layers.
- `Expectation/Level.lean` — One-level cylinder expectation.
- `Expectation/Main.lean` — Expected squared error for the global MDL predictor.
- `Expectation/Tail.lean` — A priori budget-failure tail.
- `Expectation/Tonelli.lean` — Nonnegative Tonelli and length reindexing.
- `Mean/Brackets.lean` — Dyadic brackets for indexed cylinder masses.
- `Mean/Compiler.lean` — Pair-index complexity compiler.
- `Mean/Domination.lean` — Uniform domination of the first-exit mean tree.
- `Mean/Enumeration.lean` — Lower requests for the first-exit mean tree.
- `Mean/Quotients.lean` — Certified conditional quotients.
- `Mean/Sanitizer.lean` — Prefix-free sanitation of pair-code requests.
- `Mean/Support.lean` — Common positive support and first exits.
- `Mean/Tree.lean` — The first-exit mean tree.
- `Pairwise/Bound.lean` — Pairwise squared discrepancy on a positive cylinder.
- `Pairwise/Product.lean` — Product comparison for two proper measures.
- `Path/Charge.lean` — Charge at selected times for one model.
- `Path/Main.lean` — Pathwise squared-error bound for the global predictor.
- `Path/Winners.lean` — Finite family of winners on a budgeted path.
- `Random/BadCandidate.lean` — Finite winners and eventual exclusion of nonrandom candidates.
- `Random/Criteria.lean` — Random paths and a priori deficiency.
- `Random/Main.lean` — Global MDL predictor merging on a random path.
- `Random/Vovk.lean` — Merging on paths random for two computable measures.

## Blueprint nodes

Rows follow `formalization-order.md`; locations are repository-relative Lean
declaration lines. The four audit remarks are documentation-only nodes.

| Node | Lean declaration(s) | File:line |
| --- | --- | --- |
| `base:model` | `Kolmogorov.MDLPrediction.Model`<br>`Kolmogorov.MDLPrediction.Model.k`<br>`Kolmogorov.MDLPrediction.Model.conditional`<br>`Kolmogorov.MDLPrediction.Model.conditional_bounds`<br>`Kolmogorov.MDLPrediction.Model.ext` | `KolmogorovMathlib/MDLPrediction/Core/Model.lean:35`<br>`KolmogorovMathlib/MDLPrediction/Core/Model.lean:42`<br>`KolmogorovMathlib/MDLPrediction/Core/Model.lean:47`<br>`KolmogorovMathlib/MDLPrediction/Core/Model.lean:53`<br>`KolmogorovMathlib/MDLPrediction/Core/Model.lean:74` |
| `base:index-bridge` | `Kolmogorov.MDLPrediction.base_index_bridge` | `KolmogorovMathlib/MDLPrediction/Core/Index.lean:23` |
| `base:complexity-attained` | `Kolmogorov.MDLPrediction.base_complexity_attained` | `KolmogorovMathlib/MDLPrediction/Core/Index.lean:29` |
| `base:program-count` | `Kolmogorov.MDLPrediction.base_program_count` | `KolmogorovMathlib/MDLPrediction/Core/FinitePrograms.lean:26` |
| `base:finite` | `Kolmogorov.MDLPrediction.finite_models_complexity_le`<br>`Kolmogorov.MDLPrediction.finite_model_indices_complexity_le` | `KolmogorovMathlib/MDLPrediction/Core/FinitePrograms.lean:51`<br>`KolmogorovMathlib/MDLPrediction/Core/FinitePrograms.lean:102` |
| `base:score` | `Kolmogorov.MDLPrediction.score`<br>`Kolmogorov.MDLPrediction.score_ge_complexity`<br>`Kolmogorov.MDLPrediction.score_nonneg`<br>`Kolmogorov.MDLPrediction.IsGlobalWinner` | `KolmogorovMathlib/MDLPrediction/Core/Model.lean:85`<br>`KolmogorovMathlib/MDLPrediction/Core/Model.lean:93`<br>`KolmogorovMathlib/MDLPrediction/Core/Model.lean:115`<br>`KolmogorovMathlib/MDLPrediction/Core/Model.lean:148` |
| `base:uniform-positive` | `Kolmogorov.MDLPrediction.base_uniform_positive` | `KolmogorovMathlib/MDLPrediction/Core/UniformModel.lean:25` |
| `base:argmin-generic` | `Kolmogorov.MDLPrediction.base_argmin_generic` | `KolmogorovMathlib/MDLPrediction/Core/ArgminGeneric.lean:22` |
| `base:argmin` | `Kolmogorov.MDLPrediction.exists_argmin` | `KolmogorovMathlib/MDLPrediction/Core/Argmin.lean:98` |
| `base:predictor` | `Kolmogorov.MDLPrediction.predictor`<br>`Kolmogorov.MDLPrediction.IsGlobalChoice`<br>`Kolmogorov.MDLPrediction.globalChoice`<br>`Kolmogorov.MDLPrediction.globalChoice_spec`<br>`Kolmogorov.MDLPrediction.predictor_add_eq_one` | `KolmogorovMathlib/MDLPrediction/Core/Argmin.lean:129`<br>`KolmogorovMathlib/MDLPrediction/Core/Argmin.lean:110`<br>`KolmogorovMathlib/MDLPrediction/Core/Argmin.lean:116`<br>`KolmogorovMathlib/MDLPrediction/Core/Argmin.lean:122`<br>`KolmogorovMathlib/MDLPrediction/Core/Argmin.lean:135` |
| `base:budget` | `Kolmogorov.MDLPrediction.PathBudget` | `KolmogorovMathlib/MDLPrediction/Core/Budget.lean:27` |
| `base:budget-positive` | `Kolmogorov.MDLPrediction.base_budget_positive` | `KolmogorovMathlib/MDLPrediction/Core/Budget.lean:33` |
| `base:budget-log` | `Kolmogorov.MDLPrediction.base_budget_log` | `KolmogorovMathlib/MDLPrediction/Core/Budget.lean:46` |
| `base:two-part` | `Kolmogorov.MDLPrediction.KA_le_measure_code` | `KolmogorovMathlib/MDLPrediction/Core/TwoPart.lean:24` |
| `base:winner` | `Kolmogorov.MDLPrediction.winner_bounds`<br>`Kolmogorov.MDLPrediction.winner_bounds_complexity`<br>`Kolmogorov.MDLPrediction.winner_bounds_mass` | `KolmogorovMathlib/MDLPrediction/Core/Winner.lean:57`<br>`KolmogorovMathlib/MDLPrediction/Core/Winner.lean:138`<br>`KolmogorovMathlib/MDLPrediction/Core/Winner.lean:167` |
| `rand:levin` | `Kolmogorov.MDLPrediction.random_iff_exists_budget`<br>`Kolmogorov.MDLPrediction.random_prefix_mass_pos` | `KolmogorovMathlib/MDLPrediction/Random/Criteria.lean:25`<br>`KolmogorovMathlib/MDLPrediction/Random/Criteria.lean:33` |
| `rand:diverges` | `Kolmogorov.MDLPrediction.apriori_deficiency_tendsto_of_not_random`<br>`Kolmogorov.MDLPrediction.zero_mass_persists` | `KolmogorovMathlib/MDLPrediction/Random/Criteria.lean:42`<br>`KolmogorovMathlib/MDLPrediction/Random/Criteria.lean:78` |
| `rand:finite-candidates` | `Kolmogorov.MDLPrediction.rand_finite_candidates` | `KolmogorovMathlib/MDLPrediction/Random/BadCandidate.lean:26` |
| `rand:bad-one` | `Kolmogorov.MDLPrediction.rand_bad_one` | `KolmogorovMathlib/MDLPrediction/Random/BadCandidate.lean:54` |
| `rand:bad` | `Kolmogorov.MDLPrediction.eventually_no_bad_winner` | `KolmogorovMathlib/MDLPrediction/Random/BadCandidate.lean:113` |
| `exp:mean-support` | `Kolmogorov.MDLPrediction.exp_mean_support`<br>`Kolmogorov.MDLPrediction.CommonPositivePrefixes`<br>`Kolmogorov.MDLPrediction.exp_mean_support_exit` | `KolmogorovMathlib/MDLPrediction/Mean/Support.lean:36`<br>`KolmogorovMathlib/MDLPrediction/Mean/Support.lean:23`<br>`KolmogorovMathlib/MDLPrediction/Mean/Support.lean:51` |
| `exp:dyadic-bracket` | `Kolmogorov.MDLPrediction.exp_dyadic_bracket`<br>`Kolmogorov.MDLPrediction.measureIndexRequest`<br>`Kolmogorov.MDLPrediction.massLower`<br>`Kolmogorov.MDLPrediction.massUpper`<br>`Kolmogorov.MDLPrediction.exp_dyadic_bracket_gap` | `KolmogorovMathlib/MDLPrediction/Mean/Brackets.lean:267`<br>`KolmogorovMathlib/MDLPrediction/Mean/Brackets.lean:26`<br>`KolmogorovMathlib/MDLPrediction/Mean/Brackets.lean:31`<br>`KolmogorovMathlib/MDLPrediction/Mean/Brackets.lean:38`<br>`KolmogorovMathlib/MDLPrediction/Mean/Brackets.lean:287` |
| `exp:quotient-lower` | `Kolmogorov.MDLPrediction.exp_quotient_lower`<br>`Kolmogorov.MDLPrediction.conditionalLower`<br>`Kolmogorov.MDLPrediction.conditionalLower_zero`<br>`Kolmogorov.MDLPrediction.exp_quotient_upper_pos` | `KolmogorovMathlib/MDLPrediction/Mean/Quotients.lean:30`<br>`KolmogorovMathlib/MDLPrediction/Mean/Quotients.lean:23`<br>`KolmogorovMathlib/MDLPrediction/Mean/Quotients.lean:107`<br>`KolmogorovMathlib/MDLPrediction/Mean/Quotients.lean:125` |
| `exp:mean-tree` | `Kolmogorov.MDLPrediction.exp_mean_tree`<br>`Kolmogorov.MDLPrediction.meanFactor`<br>`Kolmogorov.MDLPrediction.meanTree`<br>`Kolmogorov.MDLPrediction.meanTree_product`<br>`Kolmogorov.MDLPrediction.meanTree_killed` | `KolmogorovMathlib/MDLPrediction/Mean/Tree.lean:37`<br>`KolmogorovMathlib/MDLPrediction/Mean/Tree.lean:26`<br>`KolmogorovMathlib/MDLPrediction/Mean/Tree.lean:32`<br>`KolmogorovMathlib/MDLPrediction/Mean/Tree.lean:68`<br>`KolmogorovMathlib/MDLPrediction/Mean/Tree.lean:83` |
| `exp:mean-lsc` | `Kolmogorov.MDLPrediction.exp_mean_lsc`<br>`Kolmogorov.MDLPrediction.meanStageFactor`<br>`Kolmogorov.MDLPrediction.meanStageProduct`<br>`Kolmogorov.MDLPrediction.meanStageRounded` | `KolmogorovMathlib/MDLPrediction/Mean/Enumeration.lean:341`<br>`KolmogorovMathlib/MDLPrediction/Mean/Enumeration.lean:26`<br>`KolmogorovMathlib/MDLPrediction/Mean/Enumeration.lean:32`<br>`KolmogorovMathlib/MDLPrediction/Mean/Enumeration.lean:38` |
| `exp:mean-sanitize` | `Kolmogorov.MDLPrediction.exp_mean_sanitize` | `KolmogorovMathlib/MDLPrediction/Mean/Sanitizer.lean:517` |
| `exp:mean-compiler` | `Kolmogorov.MDLPrediction.exp_mean_compiler` | `KolmogorovMathlib/MDLPrediction/Mean/Compiler.lean:94` |
| `exp:mean` | `Kolmogorov.MDLPrediction.meanTree_uniform_domination`<br>`Kolmogorov.MDLPrediction.meanTree_prefixFree_budget` | `KolmogorovMathlib/MDLPrediction/Mean/Domination.lean:23`<br>`KolmogorovMathlib/MDLPrediction/Mean/Domination.lean:82` |
| `exp:log-nonneg` | `Kolmogorov.MDLPrediction.exp_log_nonneg` | `KolmogorovMathlib/MDLPrediction/Analysis/LogGap.lean:22` |
| `exp:convex` | `Kolmogorov.MDLPrediction.log_mean_gap_ge_sq` | `KolmogorovMathlib/MDLPrediction/Analysis/LogGap.lean:30` |
| `exp:product-logs` | `Kolmogorov.MDLPrediction.exp_product_logs` | `KolmogorovMathlib/MDLPrediction/Analysis/Products.lean:24` |
| `exp:product` | `Kolmogorov.MDLPrediction.sum_sq_le_of_mean_product` | `KolmogorovMathlib/MDLPrediction/Analysis/Products.lean:96` |
| `exp:pair-product` | `Kolmogorov.MDLPrediction.exp_pair_product` | `KolmogorovMathlib/MDLPrediction/Pairwise/Product.lean:125` |
| `exp:zero-one` | `Kolmogorov.MDLPrediction.exp_zero_one` | `KolmogorovMathlib/MDLPrediction/Pairwise/Product.lean:161` |
| `exp:pairwise` | `Kolmogorov.MDLPrediction.pairwise_prefix_sq_bound`<br>`Kolmogorov.MDLPrediction.pairwiseError`<br>`Kolmogorov.MDLPrediction.pairwise_realized_sq_bound` | `KolmogorovMathlib/MDLPrediction/Pairwise/Bound.lean:82`<br>`KolmogorovMathlib/MDLPrediction/Pairwise/Bound.lean:26`<br>`KolmogorovMathlib/MDLPrediction/Pairwise/Bound.lean:169` |
| `rand:vovk` | `Kolmogorov.MDLPrediction.vovk_merging`<br>`Kolmogorov.MDLPrediction.vovk_merging_bound`<br>`Kolmogorov.MDLPrediction.vovk_merging_summable`<br>`Kolmogorov.MDLPrediction.vovk_merging_true` | `KolmogorovMathlib/MDLPrediction/Random/Vovk.lean:130`<br>`KolmogorovMathlib/MDLPrediction/Random/Vovk.lean:46`<br>`KolmogorovMathlib/MDLPrediction/Random/Vovk.lean:116`<br>`KolmogorovMathlib/MDLPrediction/Random/Vovk.lean:152` |
| `rand:theorem4` | `Kolmogorov.MDLPrediction.predictor_merges_on_random`<br>`Kolmogorov.MDLPrediction.predictor_merges_on_random_true` | `KolmogorovMathlib/MDLPrediction/Random/Main.lean:112`<br>`KolmogorovMathlib/MDLPrediction/Random/Main.lean:128` |
| `exp:charge-finite` | `Kolmogorov.MDLPrediction.exp_charge_finite`<br>`Kolmogorov.MDLPrediction.selectedError` | `KolmogorovMathlib/MDLPrediction/Path/Charge.lean:178`<br>`KolmogorovMathlib/MDLPrediction/Path/Charge.lean:28` |
| `exp:charge` | `Kolmogorov.MDLPrediction.charge_selected_measure`<br>`Kolmogorov.MDLPrediction.selectedCharge` | `KolmogorovMathlib/MDLPrediction/Path/Charge.lean:258`<br>`KolmogorovMathlib/MDLPrediction/Path/Charge.lean:35` |
| `exp:finite-winner-count` | `Kolmogorov.MDLPrediction.exp_finite_winner_count` | `KolmogorovMathlib/MDLPrediction/Path/Winners.lean:24` |
| `exp:theorem7` | `Kolmogorov.MDLPrediction.pathwise_sq_bound` | `KolmogorovMathlib/MDLPrediction/Path/Main.lean:54` |
| `exp:tail` | `Kolmogorov.MDLPrediction.measure_budget_failure_le`<br>`Kolmogorov.MDLPrediction.budgetFailure`<br>`Kolmogorov.MDLPrediction.measure_no_budget_eq_zero` | `KolmogorovMathlib/MDLPrediction/Expectation/Tail.lean:32`<br>`KolmogorovMathlib/MDLPrediction/Expectation/Tail.lean:26`<br>`KolmogorovMathlib/MDLPrediction/Expectation/Tail.lean:58` |
| `exp:level-integral` | `Kolmogorov.MDLPrediction.exp_level_integral` | `KolmogorovMathlib/MDLPrediction/Expectation/Level.lean:26` |
| `exp:tonelli-sum` | `Kolmogorov.MDLPrediction.exp_tonelli_sum`<br>`Kolmogorov.MDLPrediction.exp_tonelli_sum_reindex` | `KolmogorovMathlib/MDLPrediction/Expectation/Tonelli.lean:28`<br>`KolmogorovMathlib/MDLPrediction/Expectation/Tonelli.lean:50` |
| `exp:tonelli` | `Kolmogorov.MDLPrediction.integral_path_error_eq_tsum` | `KolmogorovMathlib/MDLPrediction/Expectation/Tonelli.lean:66` |
| `exp:budget-layers` | `Kolmogorov.MDLPrediction.exp_budget_layers`<br>`Kolmogorov.MDLPrediction.leastBudget`<br>`Kolmogorov.MDLPrediction.ae_exists_budget`<br>`Kolmogorov.MDLPrediction.exp_budget_zero_layer` | `KolmogorovMathlib/MDLPrediction/Expectation/Layers.lean:38`<br>`KolmogorovMathlib/MDLPrediction/Expectation/Layers.lean:24`<br>`KolmogorovMathlib/MDLPrediction/Expectation/Layers.lean:31`<br>`KolmogorovMathlib/MDLPrediction/Expectation/Layers.lean:63` |
| `exp:geometric` | `Kolmogorov.MDLPrediction.exp_geometric` | `KolmogorovMathlib/MDLPrediction/Analysis/Series.lean:21` |
| `exp:theorem3` | `Kolmogorov.MDLPrediction.expected_sq_bound`<br>`Kolmogorov.MDLPrediction.expected_sq_bound_true` | `KolmogorovMathlib/MDLPrediction/Expectation/Main.lean:254`<br>`KolmogorovMathlib/MDLPrediction/Expectation/Main.lean:286` |
| `enum:class` | `Kolmogorov.MDLPrediction.EffectiveMixtureClass`<br>`Kolmogorov.MDLPrediction.EffectiveMixtureClass.model`<br>`Kolmogorov.MDLPrediction.EffectiveMixtureClass.carrier` | `KolmogorovMathlib/MDLPrediction/Class/Presentation.lean:25`<br>`KolmogorovMathlib/MDLPrediction/Class/Presentation.lean:37`<br>`KolmogorovMathlib/MDLPrediction/Class/Presentation.lean:42` |
| `enum:relative-attained` | `Kolmogorov.MDLPrediction.enum_relative_attained` | `KolmogorovMathlib/MDLPrediction/Class/Relative.lean:42` |
| `enum:relative-finite` | `Kolmogorov.MDLPrediction.enum_relative_finite` | `KolmogorovMathlib/MDLPrediction/Class/Relative.lean:60` |
| `enum:score` | `Kolmogorov.MDLPrediction.classScore`<br>`Kolmogorov.MDLPrediction.classComplexityENat`<br>`Kolmogorov.MDLPrediction.classComplexity`<br>`Kolmogorov.MDLPrediction.classScore_ge_complexity`<br>`Kolmogorov.MDLPrediction.classScore_nonneg` | `KolmogorovMathlib/MDLPrediction/Class/Relative.lean:96`<br>`KolmogorovMathlib/MDLPrediction/Class/Relative.lean:30`<br>`KolmogorovMathlib/MDLPrediction/Class/Relative.lean:36`<br>`KolmogorovMathlib/MDLPrediction/Class/Relative.lean:104`<br>`KolmogorovMathlib/MDLPrediction/Class/Relative.lean:134` |
| `enum:argmin` | `Kolmogorov.MDLPrediction.enum_argmin`<br>`Kolmogorov.MDLPrediction.IsClassWinner`<br>`Kolmogorov.MDLPrediction.IsClassChoice`<br>`Kolmogorov.MDLPrediction.classChoice`<br>`Kolmogorov.MDLPrediction.classChoice_spec`<br>`Kolmogorov.MDLPrediction.classPredictor`<br>`Kolmogorov.MDLPrediction.classPredictor_default` | `KolmogorovMathlib/MDLPrediction/Class/Relative.lean:168`<br>`KolmogorovMathlib/MDLPrediction/Class/Relative.lean:160`<br>`KolmogorovMathlib/MDLPrediction/Class/Relative.lean:224`<br>`KolmogorovMathlib/MDLPrediction/Class/Relative.lean:231`<br>`KolmogorovMathlib/MDLPrediction/Class/Relative.lean:240`<br>`KolmogorovMathlib/MDLPrediction/Class/Relative.lean:249`<br>`KolmogorovMathlib/MDLPrediction/Class/Relative.lean:259` |
| `enum:compiler` | `Kolmogorov.MDLPrediction.enum_compiler` | `KolmogorovMathlib/MDLPrediction/Class/Compiler.lean:23` |
| `enum:bridge` | `Kolmogorov.MDLPrediction.measureComplexity_le_classComplexity` | `KolmogorovMathlib/MDLPrediction/Class/Compiler.lean:55` |
| `enum:indices-ce` | `Kolmogorov.MDLPrediction.enum_indices_ce`<br>`Kolmogorov.MDLPrediction.IsDiscoveryStream`<br>`Kolmogorov.MDLPrediction.discoveryStream` | `KolmogorovMathlib/MDLPrediction/Class/Enumeration.lean:79`<br>`KolmogorovMathlib/MDLPrediction/Class/Enumeration.lean:72`<br>`KolmogorovMathlib/MDLPrediction/Class/Enumeration.lean:105` |
| `enum:blocks` | `Kolmogorov.MDLPrediction.enum_blocks`<br>`Kolmogorov.MDLPrediction.ordinalBlock`<br>`Kolmogorov.MDLPrediction.IsCompleteBlock`<br>`Kolmogorov.MDLPrediction.discoveryStream_complete_at_stage` | `KolmogorovMathlib/MDLPrediction/Class/Enumeration.lean:229`<br>`KolmogorovMathlib/MDLPrediction/Class/Enumeration.lean:113`<br>`KolmogorovMathlib/MDLPrediction/Class/Enumeration.lean:118`<br>`KolmogorovMathlib/MDLPrediction/Class/Enumeration.lean:125` |
| `enum:layer` | `Kolmogorov.MDLPrediction.enumerate_low_complexity_indices` | `KolmogorovMathlib/MDLPrediction/Class/Enumeration.lean:258` |
| `enum:mix-mass` | `Kolmogorov.MDLPrediction.enum_mix_mass` | `KolmogorovMathlib/MDLPrediction/Class/Mixture.lean:22` |
| `enum:block-replay` | `Kolmogorov.MDLPrediction.enum_block_replay`<br>`Kolmogorov.MDLPrediction.blockReplay` | `KolmogorovMathlib/MDLPrediction/Class/Replay.lean:136`<br>`KolmogorovMathlib/MDLPrediction/Class/Replay.lean:22` |
| `enum:block-prefixcode` | `Kolmogorov.MDLPrediction.enum_block_prefixcode`<br>`Kolmogorov.MDLPrediction.levelLog` | `KolmogorovMathlib/MDLPrediction/Class/BlockCode.lean:199`<br>`KolmogorovMathlib/MDLPrediction/Class/BlockCode.lean:26` |
| `enum:block-code` | `Kolmogorov.MDLPrediction.blockMixture_complexity_le` | `KolmogorovMathlib/MDLPrediction/Class/BlockCode.lean:270` |
| `enum:block-exclusion` | `Kolmogorov.MDLPrediction.enum_block_exclusion`<br>`Kolmogorov.MDLPrediction.blockRadius` | `KolmogorovMathlib/MDLPrediction/Class/Exclusion.lean:137`<br>`KolmogorovMathlib/MDLPrediction/Class/Exclusion.lean:30` |
| `enum:low-layers` | `Kolmogorov.MDLPrediction.enum_low_layers` | `KolmogorovMathlib/MDLPrediction/Class/Exclusion.lean:170` |
| `enum:dominate` | `Kolmogorov.MDLPrediction.everWinners_layer_polynomial` | `KolmogorovMathlib/MDLPrediction/Class/Exclusion.lean:322` |
| `enum:winner` | `Kolmogorov.MDLPrediction.class_winner_bounds` | `KolmogorovMathlib/MDLPrediction/Class/Winner.lean:107` |
| `enum:ever-count` | `Kolmogorov.MDLPrediction.enum_ever_count` | `KolmogorovMathlib/MDLPrediction/Class/Charge.lean:27` |
| `enum:class-charge` | `Kolmogorov.MDLPrediction.enum_class_charge` | `KolmogorovMathlib/MDLPrediction/Class/Charge.lean:94` |
| `enum:theorem9` | `Kolmogorov.MDLPrediction.class_pathwise_sq_polynomial`<br>`Kolmogorov.MDLPrediction.classPathError`<br>`Kolmogorov.MDLPrediction.class_pathwise_sq_polynomial_true` | `KolmogorovMathlib/MDLPrediction/Class/Path.lean:148`<br>`KolmogorovMathlib/MDLPrediction/Class/Path.lean:22`<br>`KolmogorovMathlib/MDLPrediction/Class/Path.lean:238` |
| `enum:class-layers` | `Kolmogorov.MDLPrediction.enum_class_layers`<br>`Kolmogorov.MDLPrediction.classBudgetLayer`<br>`Kolmogorov.MDLPrediction.classBudgetLayer_eq_leastBudget` | `KolmogorovMathlib/MDLPrediction/Class/Expectation.lean:69`<br>`KolmogorovMathlib/MDLPrediction/Class/Expectation.lean:29`<br>`KolmogorovMathlib/MDLPrediction/Class/Expectation.lean:34` |
| `enum:poly-moment` | `Kolmogorov.MDLPrediction.enum_poly_moment` | `KolmogorovMathlib/MDLPrediction/Analysis/Series.lean:137` |
| `enum:theorem10` | `Kolmogorov.MDLPrediction.class_expected_sq_polynomial` | `KolmogorovMathlib/MDLPrediction/Class/Expectation.lean:114` |
| `audit:incompressible` | `Kolmogorov.MDLPrediction.audit_incompressible` | `KolmogorovMathlib/MDLPrediction/Counterexample/Atomic.lean:109` |
| `audit:atomic` | `Kolmogorov.MDLPrediction.audit_atomic`<br>`Kolmogorov.MDLPrediction.atomicWitness` | `KolmogorovMathlib/MDLPrediction/Counterexample/Atomic.lean:287`<br>`KolmogorovMathlib/MDLPrediction/Counterexample/Atomic.lean:127` |
| `audit:drop` | `Kolmogorov.MDLPrediction.audit_drop`<br>`Kolmogorov.MDLPrediction.positiveDeficiency` | `KolmogorovMathlib/MDLPrediction/Counterexample/Deficiency.lean:30`<br>`KolmogorovMathlib/MDLPrediction/Counterexample/Deficiency.lean:24` |
| `audit:notation` | Documentation only | see *Corrections to the printed paper* above |
| `audit:scope` | Documentation only | see *Corrections to the printed paper* above |
| `audit:pair` | Documentation only | see *Corrections to the printed paper* above |
| `audit:deficiency` | Documentation only | see *Corrections to the printed paper* above |
| `audit:lemma5` | `Kolmogorov.MDLPrediction.uniformPrefixDropFalse` | `KolmogorovMathlib/MDLPrediction/Counterexample/Main.lean:79` |
<!-- END GENERATED MDL MAP -->
