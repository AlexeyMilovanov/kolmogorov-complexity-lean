# Formalized Algorithmic Information Theory in Lean 4

This repository contains a Lean 4 formalization of algorithmic information theory: Kolmogorov complexity, prefix complexity, universal machines, algorithmic probability, and algorithmic statistics for finite binary strings, including profiles restricted to structured families of finite-set descriptions, together with Shannon entropy and its relation to complexity, information inequalities, multisource algorithmic information theory, Solomonoff induction, and stopping complexity. The main background reference is Alexander Shen, Vladimir A. Uspensky, and Nikolai Vereshchagin, [*Kolmogorov Complexity and Algorithmic Randomness*](https://www.lirmm.fr/~ashen/kolmbook-eng-scan.pdf). The algorithmic-statistics layer is developed with Nikolai Vereshchagin and Alexander Shen, [*Algorithmic statistics: forty years later*](https://arxiv.org/abs/1607.08077), as a central guide.

The development is based on Mathlib's computability infrastructure. Decompressors are represented as partial functions, finite objects are represented by bitstrings, and most theorem statements are phrased up to the additive or logarithmic slack terms natural in Kolmogorov-complexity arguments.

## What Is Formalized

The core library formalizes plain conditional Kolmogorov complexity for bitstrings, universal decompressors, invariance up to an additive constant, basic complexity inequalities, incompressibility, uncomputability results for natural-number complexity, and Chaitin-style [incompleteness interfaces](https://arxiv.org/abs/1011.4974). The [second-incompleteness files](https://arxiv.org/abs/1011.4974) use abstract formal-system interfaces in a Kritchman-Raz style rather than formalizing a concrete arithmetic system.

The prefix-complexity part develops prefix-free codes and machines, optimal prefix decompressors, conditional prefix complexity, Kraft inequalities and converse constructions, two-stage and pair-coding infrastructure, and symmetry-of-information lemmas including conditional variants.

The algorithmic-probability part formalizes semimeasure infrastructure, a priori machine semimeasures, lower-semicomputable semimeasure interfaces, mixtures, domination lemmas, universal semimeasure constructions, conditional universal semimeasures, and Kraft-Chaitin style coding infrastructure. It also includes the coding-theorem equivalence between conditional prefix complexity and universal conditional a priori semimeasures, corresponding to `K(x | z) = -log m(x | z) + O(1)` and formalized through multiplicative `ENNReal` domination bounds.

The monotone-complexity part builds SUV Chapter 5 on continuous semimeasures and
monotone machines. `Kolmogorov.universalContinuousSemimeasure_isMaximal`
(`KolmogorovMathlib.MonotoneComplexity.APrioriComplexity`) constructs the a priori
probability on the binary tree as a lower semicomputable continuous semimeasure that
dominates every other one, and `Kolmogorov.KA_isMinimal_upperSemicomputableComplexity`
(`KolmogorovMathlib.MonotoneComplexity.APrioriMinimality`) characterizes the derived
complexity `KA` as the least complexity whose Kraft weight is lower semicomputable.
`Kolmogorov.exists_optimalMonotoneDecompressor`
(`KolmogorovMathlib.MonotoneComplexity.MonotoneOptimality`) gives the optimal monotone
decompressor behind `KMOf`, and `Kolmogorov.KMStreamOf_infinite_eq_iSup_prefixes`
(`KolmogorovMathlib.MonotoneComplexity.MonotoneInfinite`) extends monotone complexity to
infinite sequences as the supremum over prefixes. The comparison with plain complexity is
two-sided: `Kolmogorov.exists_const_abs_plainK_sub_KMOf_le_log`
(`KolmogorovMathlib.MonotoneComplexity.PlainMonotoneComparison`) bounds `|C(x) - KM(x)|` by
`2 log(l(x) + 1) + O(1)`, and `Kolmogorov.plainK_KMOf_log_gap_both_signs`
(`KolmogorovMathlib.MonotoneComplexity.PlainMonotoneSeparation`) shows that the gap is
attained with both signs. The separation of `KM` from `KA` is the Gacs-Day theorem:
`Kolmogorov.gacsDay_game` and `Kolmogorov.gacsDay_separation`
(`KolmogorovMathlib.MonotoneComplexity.GacsDayTheorems`) prove the request game and, for
every optimal monotone decompressor, the unbounded `KM - KA` gap of SUV Theorems 88 and 87.

The randomness part formalizes Martin-Lof randomness for computable measures on Cantor
space together with the effective measure theory it needs.
`Kolmogorov.exists_universal_martinLof_test`
(`KolmogorovMathlib.AlgorithmicRandomness.MartinLof`) constructs a universal test, and
`Kolmogorov.not_isMartinLofRandom_iff_solovay_test` in the same module gives the
Solovay-test characterization of non-randomness. The effective strong law of large numbers,
`Kolmogorov.tendsto_freqOne_of_isMartinLofRandom_uniform` and
`Kolmogorov.tendsto_freqOne_of_isMartinLofRandom_bernoulli`
(`KolmogorovMathlib.AlgorithmicRandomness.EffectiveLaws`), settles what a random sequence
must look like; randomness is preserved by measure-preserving cylinder maps
(`Kolmogorov.isMartinLofRandom_of_cylinderPullback`), a `0'`-computable random sequence is
constructed in `Kolmogorov.exists_isMartinLofRandom_uniform_computableInJump`
(`KolmogorovMathlib.AlgorithmicRandomness.JumpRandom`), and the supremum, monotone-limit and
sum presentations of a lower semicomputable function on Cantor space are shown equivalent by
`Kolmogorov.lowerSemicomputableFun_characterizations`
(`KolmogorovMathlib.AlgorithmicRandomness.LSCCharacterizations.Characterization`).

The complexity criteria for randomness are proved in both directions.
`Kolmogorov.isMartinLofRandom_uniform_iff_KA_KMOf_eq_length` and
`Kolmogorov.isMartinLofRandom_iff_boundedPrefixDeficiency`
(`KolmogorovMathlib.MonotoneComplexity.LevinSchnorr.Criteria`) are the endpoints of the
Levin-Schnorr criterion, with the ample-excess form
`Kolmogorov.tsum_two_pow_mul_ne_top_of_isMartinLofRandom_uniform`
(`KolmogorovMathlib.MonotoneComplexity.LevinSchnorr.AmpleExcess`). For Chaitin's number,
`Kolmogorov.omega_binary_isMartinLofRandom`
(`KolmogorovMathlib.MonotoneComplexity.Omega.Basic.DiracSemimeasure`) proves the binary
expansion of `Omega` Martin-Lof random, and
`Kolmogorov.isSolovayComplete_iff_isMartinLofRandomReal`
(`KolmogorovMathlib.MonotoneComplexity.Omega.Solovay.CompletenessRandomness`) identifies the
Solovay complete lower semicomputable reals with the random ones. Solovay functions and busy
beavers follow, in `Kolmogorov.isMartinLofRandomReal_iff_hasSolovayProperty` and in the
two-way translation `Kolmogorov.omegaPrefix_of_busyBeaver` and
`Kolmogorov.busyBeaver_of_omegaPrefix`
(`KolmogorovMathlib.MonotoneComplexity.Omega.SolovayFunctions.BusyBeaverOmega`), whose total
forms are refuted in the same module. Effective Hausdorff dimension is developed in
`KolmogorovMathlib.MonotoneComplexity.Dimension.Hausdorff`, where
`Kolmogorov.effectiveHausdorffDim_eq_sSup_image` reduces the dimension of a set to that of
its singletons and `Kolmogorov.effectiveHausdorffDim_singleton_eq_liminf` identifies the
dimension of a singleton with the lower limit of `C(x_1 ... x_n) / n`; change of measure is
in `KolmogorovMathlib.MonotoneComplexity.Dimension.ChangeOfMeasure`, with
`Kolmogorov.image_isMartinLofRandom_of_isMartinLofRandom`.

The Solomonoff part proves that the universal predictor `M(b | x) = M(xb) / M(x)` of the a
priori probability on the tree learns every computable probability measure `mu` on Cantor
space. `Kolmogorov.exists_const_two_pow_complexity_mul_cantorMass_le_universal`
(`KolmogorovMathlib.Solomonoff.Domination`) is the domination step: one constant `C`,
quantified before the measure, gives `2^-(K(mu) + C) mu(x) <= M(x)` for every computable `mu`.
`Kolmogorov.solomonoff_tsum_predictionError_le_complexity`
(`KolmogorovMathlib.Solomonoff.Main`) is Solomonoff's theorem: the total expected squared
prediction error is at most `(ln 2 / 2) (K(mu) + C)`, with the bound on the summed one-step
Kullback-Leibler divergences `Kolmogorov.solomonoff_tsum_stepKL_le_complexity` behind it, and
`Kolmogorov.solomonoff_ae_tendsto` in the same module shows that the predictions converge to
the true conditional probabilities `mu`-almost surely.

The stopping-complexity part, `KolmogorovMathlib/StoppingComplexity/`, originates from the
public `lean-4.28-stopping` branch. It formalizes randomized stopping machines, which read an
input and fair random bits and may halt, the monotone stopping complexity `K_stop`
(`Kolmogorov.univStopComplexity`) and the a priori stopping probability `M_stop`
(`Kolmogorov.univStopProb`) of a fixed universal machine, and lower bounds on the gap
`g(z) = K_stop(z) - m(z)` with `m(z) = -log M_stop(z)`. The endpoints are unconditional
theorems about the universal machine. For every admissible discount `f`,
`Kolmogorov.raw_inequality` (`KolmogorovMathlib.StoppingComplexity.GeneralCriterion`) gives
strings with `K_stop(z) > n + f(n) + c` and `M_stop(z) >= 2^-(n + a)`, and
`Kolmogorov.stoppingGap_exceeds_admissibleDiscount` in the same module turns this into
`g(z) > f(ceil m(z)) + c` at arbitrarily large mass depth;
`Kolmogorov.stoppingGap_iteratedLog_lowerBound`
(`KolmogorovMathlib.StoppingComplexity.MainTheorem`) specializes this to
`g(z) > log m(z) + log log log m(z) + c`; and `Kolmogorov.stoppingGap_logMass_lowerBound` and
`Kolmogorov.stoppingGap_logLength_lowerBound`
(`KolmogorovMathlib.StoppingComplexity.LengthBounds`) give the bounds
`log m - log log m - O(1)` in the mass depth and `log log l - log log log l - O(1)` in the
length `l`. The witnesses are infinitely many strings, not all long strings.

The foundational layer carries two results of its own besides the encodings.
`Kolmogorov.arslanov_completeness`
(`KolmogorovMathlib.Foundation.FixedPointFree.ArslanovCompleteness`) proves Arslanov's
completeness criterion, that an enumerable oracle computing a fixed-point-free function
computes the halting problem, through a parametrized form of Kleene's recursion theorem, and
`Kolmogorov.arslanov_solvesHighComplexity_iff_halting`
(`KolmogorovMathlib.Foundation.Arslanov`) states it in complexity form: an enumerable oracle
produces from `n` an object of plain complexity at least `n` exactly when it computes the
halting problem. `KolmogorovMathlib.Foundation.RSeparability` decides `r`-separability for the
sets attached to plain complexity and shows that the property is not automatic.

The algorithmic-statistics part formalizes finite-set and finite-distribution models, randomness deficiency, stochasticity predicates, non-stochastic strings, selectors, two-part descriptions, optimality deficiency, description shifting, gap-counting and improving-description arguments. The `TwoPart` profile-realization layer carries the Section 3 machinery of the Vereshchagin-Shen survey: stochasticity profiles, admissible/profile curves, realization of profile curves by strings, antistochastic examples, and non-stochastic corollaries.

The bounded-complexity-list layer formalizes Section 4 of the Vereshchagin-Shen survey: the
list of all strings of plain complexity at most `m` in enumeration order, its counter, the
busy-beaver completion times, the equivalence between a high-bit prefix of `Omega_m` and the
list, and the non-stochastic objects it produces. `Kolmogorov.tail_characterization`
(`KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.TailProfile.Uniform`) bridges the layer
to the Section 3 description profile in both directions, and the section's conclusions
`Kolmogorov.prop_dilemma`, `Kolmogorov.prop_information_rare` and
`Kolmogorov.prop_nonstochastic_counting_improved` are in
`KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.NonStochasticFinal.Part02`.

The strong-models layer formalizes Section 7 of the Vereshchagin-Shen survey: total
conditional complexity and its optimal machine, total-information equivalence, strong
statistics and simple finite partitions, strong profiles and normal versus strange strings,
hereditary and step-wise properties, separation of strong natural models from strong standard
descriptions, strong sufficient statistics, and bounds on the number of strings with a
prescribed profile. Its endpoints are `Kolmogorov.prop_add_noise`,
`Kolmogorov.thm_separation`, `Kolmogorov.thm_card`, `Kolmogorov.thm_uppest`,
`Kolmogorov.lemma_lch`, `Kolmogorov.t1_strange_string` and `Kolmogorov.prop_upward`, in
`KolmogorovMathlib.AlgorithmicStatistics.StrongModels`.

The restricted-description layer formalizes the framework of Section 6 of the
Vereshchagin-Shen survey. A `DescriptionFamily` packages an effective
enumeration, the presence of every full binary cube, and a quantitative
covering property; the main realization theorem assumes that its overhead is
polynomial. The development proves family-relative profile
endpoints, effective covering and selection results, improving-description
theorems, and restricted analogues of the comparison between randomness and
optimality deficiencies. Its main theorem, `prop_family_curve`, realizes every
strictly decreasing boundary curve, up to `O(sqrt(n log n))` profile error, by a
string of length `n + O(log n)` and plain complexity
`k + O(sqrt(n log n))`. Concrete families include the full family, cylinders,
masks, and Hamming balls. For Hamming balls, `prop_hamming_curve` specializes
the general realization theorem, while `prop_hamming_gap` proves an
asymptotically linear separation between the unrestricted and restricted
profiles.

The entropy part formalizes Chapter 7 of Shen-Uspensky-Vereshchagin, on Shannon entropy and
its relation to Kolmogorov complexity. Codes over a finite alphabet come first:
`Kolmogorov.Code.kraftSum_le_one_of_isUniquelyDecodable`
(`KolmogorovMathlib.Entropy.Codes.Kraft`, Theorem 140) is the Kraft-McMillan inequality for
uniquely decodable codes, `Kolmogorov.isOptimalPrefixCode_of_isHuffmanCode`
(`KolmogorovMathlib.Entropy.Codes.Huffman`) proves that Huffman's algorithm produces an optimal
prefix code, and `Kolmogorov.entropyDist_le_avgLength_of_isPrefixFree` and
`Kolmogorov.exists_isPrefixFree_avgLength_lt_entropyDist_add_one`
(`KolmogorovMathlib.Entropy.Coding`, Theorem 138) place the average length of an optimal prefix
code between `H` and `H + 1`. Conditional entropy and mutual information are developed in
`KolmogorovMathlib.Entropy.Inequalities.Basic` and
`KolmogorovMathlib.Entropy.Inequalities.Independence`, with the chain rule
`Kolmogorov.entropy_pairRV_eq_add_condEntropy` (Theorem 142) and the nonnegativity of
conditional mutual information `Kolmogorov.condMutualInfo_nonneg` (Theorem 145). On the
complexity side, `Kolmogorov.card_typeClass_le_rpow_entropy`
(`KolmogorovMathlib.Entropy.Complexity.Frequencies`) is the multinomial bound behind the
complexity of a word with given frequencies (Theorem 146);
`Kolmogorov.mul_entropyDist_le_expect_KP` and `Kolmogorov.exists_expect_KP_le_mul_entropyDist`
(`KolmogorovMathlib.Entropy.Complexity.Expected.Basic`, Theorem 147) compare the expected
prefix complexity of `N` independent letters with `N H`;
`Kolmogorov.tendsto_plainK_cantorPrefix_div`
(`KolmogorovMathlib.Entropy.Complexity.RandomSequences`, Theorem 148, binary case) shows that
`C(x_1 ... x_N) / N` tends to the entropy along a sequence random for a Bernoulli measure, and
`Kolmogorov.exists_const_prob_plainK_near_mul_entropyDist` in the same module that the
complexity of an i.i.d. word concentrates around `N H` at scale `sqrt N` (Theorem 149).
Shannon's coding theorem is `Kolmogorov.exists_code_error_le_iff_exists_card_le` and
`Kolmogorov.exists_const_code_error_le`
(`KolmogorovMathlib.Entropy.Complexity.ShannonCoding.Basic`, Theorems 150 and 151).

The information-inequalities part formalizes Chapter 10 of Shen-Uspensky-Vereshchagin: linear
inequalities for entropies, complexities, sizes of finite sets, subgroups and subspaces.
`Kolmogorov.holdsForEntropies_iff_holdsForComplexitiesCplx`
(`KolmogorovMathlib.InformationInequalities.Typization.Romashchenko`, Theorem 212) is
Romashchenko's theorem that a linear inequality holds for the entropies of all tuples of
random variables exactly when it holds, with `O(log N)` precision, for the complexities of all
tuples of strings; its proof goes through the typization of
`Kolmogorov.exists_cUniform_typization`
(`KolmogorovMathlib.InformationInequalities.Typization.Uniform`, Theorem 211) and the
almost-uniform sets of `KolmogorovMathlib.InformationInequalities.AlmostUniform` (Theorem 210).
`Kolmogorov.holdsForEntropies_iff_holdsForGroups`
(`KolmogorovMathlib.InformationInequalities.ChanYeung`, Theorem 209) is the Chan-Yeung
equivalence with inequalities for the indices of subgroups of finite groups, and
`Kolmogorov.cover_iff_complexity_inequality`
(`KolmogorovMathlib.InformationInequalities.Combinatorial.Cover`, Theorem 213) the
combinatorial interpretation of complexity inequalities by covers of finite sets. Ingleton's
inequality for subspaces is `Kolmogorov.ingleton_finrank`, and
`Kolmogorov.holdsForSubspaces_of_holdsForEntropies` transfers every entropy inequality to
dimensions of subspaces over a finite field
(`KolmogorovMathlib.InformationInequalities.Ingleton`, Theorems 215 and 216); a non-Shannon
inequality for entropies is
`Kolmogorov.holdsForEntropies_nonShannonForm`
(`KolmogorovMathlib.InformationInequalities.NonShannonTheorems`, Theorem 218).

The common-information layer formalizes Chapter 11 of Shen-Uspensky-Vereshchagin: common
information of pairs, rectangle covers and incidence-geometry bounds over concrete finite
fields, no-four-cycle density arguments, conditional-independence chains, and Muchnik-style
effective selectors used for worst-case counting. `Kolmogorov.muchnik_nonextractability`
(`KolmogorovMathlib.CommonInformation.WorstCase`) is Muchnik's non-extractability theorem and
`Kolmogorov.muchnik_worst_case_region` (`KolmogorovMathlib.CommonInformation.WorstCaseRegion`)
the worst-case region theorem; a point-line incidence relation over a finite field supplies a
concrete pair of strings with no cheap common witness,
`Kolmogorov.incidence_nonextractability_large_z`
(`KolmogorovMathlib.CommonInformation.IncidenceConsequences`).

The multisource part formalizes Chapter 12 of Shen-Uspensky-Vereshchagin, on information
transmission requests with several sources and conditions. Muchnik's theorem on conditional
codes, `Kolmogorov.exists_muchnikCode` (`KolmogorovMathlib.Multisource.Muchnik`, Theorem 229),
gives for `A` and `B` of complexity at most `n` a string `X` of length `C(A|B) + O(log n)` that
is simple given `A` and restores `A` together with `B`; its combinatorial form is the game
`Kolmogorov.exists_muchnikGame_winningStrategy` (`KolmogorovMathlib.Multisource.MuchnikGame`,
Theorem 230). The criterion `Kolmogorov.conditionalEncoding_criterion`
(`KolmogorovMathlib.Multisource.ConditionalEncoding`, Problem 318) settles conditional
encoding, `Kolmogorov.exists_informationDistanceCode`
(`KolmogorovMathlib.Multisource.InformationDistance.Part02`, Theorem 232) gives one code that
transforms two strings into each other, and `Kolmogorov.exists_twoConditionCode`
(`KolmogorovMathlib.Multisource.TwoConditions`, Theorem 234) one code that restores a string
under either of two conditions. Algorithmic network coding is
`Kolmogorov.exists_networkCoding_of_cutConditions`
(`KolmogorovMathlib.Multisource.NetworkCoding`, Theorem 236): a single-source request on a
fixed graph is fulfillable with logarithmic precision when every cut has enough capacity, here
with capacities exceeded by `O(log n)` bits, which is weaker than the printed statement. For
minimal sufficient statistics, `Kolmogorov.exists_pair_with_minimal_profile`
(`KolmogorovMathlib.Multisource.MinimalSufficientStatistics`, Theorem 237) shows that the
profile of a pair is not determined by the complexities of its components.

`KolmogorovCounterexamples` is a second, independent library root: it holds machine-checked
refutations of readings of the source material that turned out to be false, and nothing in
`KolmogorovMathlib` depends on a refuted notion. `Kolmogorov.AdmissibleCurve_unsatisfiable`
shows that packaging the Section 3 admissibility conditions as five exact fields on a curve is
self-contradictory, the provable replacement being `Kolmogorov.structureFunction_admissible`;
`Kolmogorov.not_forall_exists_isFloorComputableMeasure_of_exact` refutes the dyadic
floor-selector reading of computability of a measure, under which the representation theorem
for computable measures becomes false; and
`Kolmogorov.information_conservation_Cn_only_exponent_false` refutes the exponent
`-l + O(C(n))` in Problem 59, the book's own `-l + O(C(n) + C(l))` being proved as
`Kolmogorov.levin_information_conservation`.

Which theorem covers which item of the book is tabulated in `docs/SUV_COVERAGE.md`, generated
from the tree: of 342 items, 305 are proved here, 5 were already available, 30 are archived
with their statements preserved in `docs/ARCHIVED_TARGETS.md`, and 2 are partly archived.

## Build

Install Lean through `elan`, then fetch the Mathlib cache and build the exported library target:

```bash
lake exe cache get
lake build KolmogorovMathlib
```

For the default package build — the library together with the counterexample
library — run:

```bash
lake build
```

`bash scripts/audit.sh` is the completion gate (forbidden constructs, `sorry` scan,
build, warning gate, co-import smoke test, axiom sweep, tactic smoke tests).

The conventions and the contribution rules are in `CONTRIBUTING.md`; the map
from book items to theorems is `docs/SUV_COVERAGE.md`, regenerated by
`scripts/gen_suv_coverage.py`.

The HTML documentation is built from the side package `docbuild/`, which is the
only place `doc-gen4` is required, at a revision pinned to this repository's
Lean release:

```bash
cd docbuild
lake update doc-gen4
lake build KolmogorovMathlib:docs KolmogorovCounterexamples:docs   # writes .lake/build/doc
```

`.github/workflows/ci.yml` runs the build, the audit, the test scripts under
`scripts/tests/` and the documentation build; `scripts/ci_local.sh` runs the
same steps locally, and the workflow calls that script so the two cannot drift
apart.

The library has a single build root, `KolmogorovMathlib`, which imports every module
of the library, directly or through other modules: the root imports the maximal modules
of the topic directories itself, and `KolmogorovMathlib/Extras.lean`, which the root also
imports, collects the side modules outside the main development line (alternative
developments, spare interfaces and side results), so that they stay in the build.
`KolmogorovCounterexamples` is a
second root, deliberately not imported by the library, and the release check builds
it too.

This branch is pinned to Lean `v4.34.1` and the matching Mathlib ecosystem.

## Branches

`main` is the development branch and is pinned to Lean `v4.34.1` together with
the matching Mathlib ecosystem; the historical `lean-4.28-aristotle` and
`codex/lean28-polish` branches keep the last Lean `v4.28.0` state of the library.

## Project Layout

```text
KolmogorovMathlib/
├── Foundation/                  # Search operators, recursively enumerable relations, Nat/bitstring encodings,
│                                #   fixed-point-free functions and Arslanov's criterion, r-separability
├── Core/                        # Partial decompressors, plain complexity, universal decompressor, invariance
├── Complexity/                  # Bounds, incompressibility, uncomputability, incompleteness interfaces,
│                                #   enumerable families, canonical objects, pairs, information, the busy beaver
├── Encoding/                    # Codes for tuples and lists of bit strings
├── Entropy/                     # Shannon entropy of finite random variables, codes over a finite
│                                #   alphabet, and the entropy side of Chapter 7
├── InformationInequalities/     # Linear inequalities for entropies, complexities and set sizes
├── Multisource/                 # Information transmission requests and multisource results
├── Combinatorics/               # Bipartite graphs, matchings, hash families and network flows
├── Interface/                   # Standard machines, dovetailing, computable and semicomputable reals
├── Prefix/                      # Prefix machines, Kraft theory, prefix complexity, symmetry of information
├── MonotoneComplexity/          # A priori probability, monotone complexity, the Gacs-Day separation,
│                                #   Levin-Schnorr, Omega and Solovay functions, effective dimension
├── AlgorithmicProbability/      # Semimeasures, mixtures, domination, universal semimeasures, coding tools
├── AlgorithmicRandomness/       # Martin-Löf randomness and lower-semicomputable characterisations
├── AlgorithmicStatistics/       # Stochasticity, deficiencies, models, non-stochasticity, two-part profiles
│   ├── TwoPart/                 # Descriptions, gap counting, profiles, curve realization, paper-facing theorems
│   ├── BoundedLists/            # Lists of strings of bounded complexity, Section 4 of the survey
│   └── StrongModels/            # Total conditional complexity and strong models, Section 7 of the survey
├── CommonInformation/           # Common information, extraction obstructions, incidence regions
├── Restricted/                  # Description families and restricted profiles from Section 6
│   ├── FamilyCurve/             # Effective multiscale construction and general curve realization
│   └── Examples/                # Cylinders, masks, and Hamming-ball families
├── Solomonoff/                  # The universal predictor, domination and Solomonoff's convergence theorem
├── StoppingComplexity/          # Randomized stopping machines and the gap K_stop - (-log M_stop)
├── Deprecated/                  # `@[deprecated] alias`es for the old names, generated from the rename table
└── Extras.lean                  # Imports side modules outside the main development line, keeping them in the build

KolmogorovCounterexamples/       # Refutations of superseded readings of the source
└── Deprecated/                  # `@[deprecated] alias`es for the old names of that library
```

There is no directory organised by book chapter: a proved exercise is a
statement about its topic and lives with the rest of that topic.  The map from
book items to declarations is `docs/SUV_COVERAGE.md`.

The top-level module `KolmogorovMathlib.lean` imports the library development.
`KolmogorovCounterexamples.lean` is a second, independent library root: it
collects the machine-checked refutations of readings of the source material
that turned out to be false, and is deliberately not imported by
`KolmogorovMathlib`.

## Lake Metadata

The Lake package is named `kolmogorov_complexity`; the Lean library targets are
`KolmogorovMathlib` and `KolmogorovCounterexamples`. The Mathlib dependency is pinned in `lakefile.toml` and
`lake-manifest.json` to the Lean `v4.34.1` ecosystem.

## Attribution

This branch includes proofs edited by
[Aristotle](https://aristotle.harmonic.fun). To cite Aristotle, tag
`@Aristotle-Harmonic` on GitHub pull requests or issues, or use:

```text
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```
