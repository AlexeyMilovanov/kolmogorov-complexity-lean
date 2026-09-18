# Formalized Algorithmic Information Theory in Lean 4

This repository contains a Lean 4 formalization of algorithmic information theory: Kolmogorov complexity, prefix complexity, universal machines, algorithmic probability, and algorithmic statistics for finite binary strings, including profiles restricted to structured families of finite-set descriptions. The main background reference is Alexander Shen, Vladimir A. Uspensky, and Nikolai Vereshchagin, [*Kolmogorov Complexity and Algorithmic Randomness*](https://www.lirmm.fr/~ashen/kolmbook-eng-scan.pdf). The algorithmic-statistics layer is developed with Nikolai Vereshchagin and Alexander Shen, [*Algorithmic statistics: forty years later*](https://arxiv.org/abs/1607.08077), as a central guide.

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
from the tree: of 136 items, 108 are proved here, 5 were already available, 21 are archived
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

The library has a single build root, `KolmogorovMathlib`; the side modules that no
other module imports are collected by `KolmogorovMathlib/Extras.lean`, which the
root imports, so that they stay in the build. `KolmogorovCounterexamples` is a
second root, deliberately not imported by the library, and the release check builds
it too.

This branch is pinned to Lean `v4.33.1` and the matching Mathlib ecosystem.

## Branches

`main` is the development branch and is pinned to Lean `v4.33.1` together with
the matching Mathlib ecosystem; the historical `lean-4.28-aristotle` branch
keeps an earlier Lean `v4.28.0` state of the library.

## Project Layout

```text
KolmogorovMathlib/
├── Foundation/                  # Search operators, recursively enumerable relations, Nat/bitstring encodings,
│                                #   fixed-point-free functions and Arslanov's criterion, r-separability
├── Core/                        # Partial decompressors, plain complexity, universal decompressor, invariance
├── Complexity/                  # Bounds, incompressibility, uncomputability, incompleteness interfaces,
│                                #   enumerable families, canonical objects, pairs, information, the busy beaver
├── Encoding/                    # Codes for tuples and lists of bit strings
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
├── Deprecated/                  # `@[deprecated] alias`es for the old names, generated from the rename table
└── Extras.lean                  # Imports the modules no other module imports, keeping them in the build

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
`lake-manifest.json` to the Lean `v4.33.1` ecosystem.

