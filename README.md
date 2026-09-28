# Formalized Algorithmic Information Theory in Lean 4

This repository contains a Lean 4 formalization of algorithmic information theory: Kolmogorov complexity, prefix complexity, universal machines, algorithmic probability, and algorithmic statistics for finite binary strings, including profiles restricted to structured families of finite-set descriptions. The main background reference is Alexander Shen, Vladimir A. Uspensky, and Nikolai Vereshchagin, [*Kolmogorov Complexity and Algorithmic Randomness*](https://www.lirmm.fr/~ashen/kolmbook-eng-scan.pdf). The algorithmic-statistics layer is developed with Nikolai Vereshchagin and Alexander Shen, [*Algorithmic statistics: forty years later*](https://arxiv.org/abs/1607.08077), as a central guide.

The development is based on Mathlib's computability infrastructure. Decompressors are represented as partial functions, finite objects are represented by bitstrings, and most theorem statements are phrased up to the additive or logarithmic slack terms natural in Kolmogorov-complexity arguments.

## What Is Formalized

The core library formalizes plain conditional Kolmogorov complexity for bitstrings, universal decompressors, invariance up to an additive constant, basic complexity inequalities, incompressibility, uncomputability results for natural-number complexity, and Chaitin-style [incompleteness interfaces](https://arxiv.org/abs/1011.4974). The [second-incompleteness files](https://arxiv.org/abs/1011.4974) use abstract formal-system interfaces in a Kritchman-Raz style rather than formalizing a concrete arithmetic system.

The prefix-complexity part develops prefix-free codes and machines, optimal prefix decompressors, conditional prefix complexity, Kraft inequalities and converse constructions, two-stage and pair-coding infrastructure, and symmetry-of-information lemmas including conditional variants.

The algorithmic-probability part formalizes semimeasure infrastructure, a priori machine semimeasures, lower-semicomputable semimeasure interfaces, mixtures, domination lemmas, universal semimeasure constructions, conditional universal semimeasures, and Kraft-Chaitin style coding infrastructure. It also includes the coding-theorem equivalence between conditional prefix complexity and universal conditional a priori semimeasures, corresponding to `K(x | z) = -log m(x | z) + O(1)` and formalized through multiplicative `ENNReal` domination bounds.

The algorithmic-statistics part formalizes finite-set and finite-distribution models, randomness deficiency, stochasticity predicates, non-stochastic strings, selectors, two-part descriptions, optimality deficiency, description shifting, gap-counting and improving-description arguments. The `TwoPart` profile-realization layer includes the current formalization of the main Section 3 machinery from the Vereshchagin-Shen survey: stochasticity profiles, admissible/profile curves, realization of profile curves by strings, antistochastic examples, and non-stochastic corollaries.

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

## Stopping complexity: the gap K_stop − (−log M_stop)

`KolmogorovMathlib/StoppingComplexity/` formalizes quantitative lower bounds on
the gap between two measures of a finite binary string under randomized stopping
machines: the monotone stopping complexity `K_stop` and the negative logarithm of
the a priori stopping probability `M_stop`.

**The machine model.** A randomized stopping machine has an input tape and a tape
of fair random bits, and it may halt. It is formalized operationally (`Machine`):
a machine is a *controller*, a partial recursive function that, given the input
prefix and the random prefix consumed so far, asks for the next input bit or the
next random bit, or halts. A halting run consumes *exactly* an input `z` and a
random prefix `p`. The controllers are enumerated computably, and the fixed
universal machine `univStopping` (`Universal`) reads a unary tag `1^e 0` from the
random tape and then runs the `e`-th controller on the rest of the random tape and
on the input. For a string `z`:

* `M(z)` (`univStopProb z`) is the probability that the universal machine halts
  after consuming exactly the input `z`, that is, the fair-coin measure of the
  random tapes on which it does (`StopProbability`);
* `K_s(z)` (`univStopComplexity z`) is the length of the shortest random prefix
  `p`, tag included, with which the universal machine halts after consuming
  exactly `(z, p)`; it is finite, and `M(z)` is positive, for every `z`;
* `m(z) = −log₂ M(z)` (`massDepth z`) is the mass depth of `z`, and
  `g(z) = K_s(z) − m(z)` (`stoppingGap z`) its stopping gap (`MassDepth`);
  `0 ≤ m(z) ≤ K_s(z)`, so the gap is nonnegative.

**The endpoint theorems.** All six are unconditional theorems about the fixed
universal machine.

| Target | Lean name | Statement |
| --- | --- | --- |
| RAW | `raw_inequality` | For every admissible discount `f` there is one constant `a` such that for every `c` some string `z` beginning with the tag `1^c 0`, and some `n`, satisfy `K_s(z) > n + f(n) + c` and `M(z) ≥ 2^−(n+a)`. |
| THEOREM-GAME | `localStrategy_winning` | In the finite stopping-allocation game with an admissible schedule, the explicit strategy of every level `j ≤ R` wins the local game of every capacity `0 ≤ U ≤ Ψ_j` on the level's fine grid: each request is fresh and uses only the exponents `E_0, …, E_j`, every path load is at most the level's budget `B_j`, and no legal history answers `T_j` requests. |
| GENERAL | `stoppingGap_exceeds_admissibleDiscount` | For every admissible discount `f`, every natural `c` and every real `T` there is `z` with `m(z) ≥ max(16, T)` and `g(z) > f(⌈m(z)⌉) + c`. |
| MAIN | `stoppingGap_iteratedLog_lowerBound` | For every natural `c` and every real `T` there is `z` with `m(z) ≥ max(16, T)` and `g(z) > log₂ m(z) + log₂ log₂ log₂ m(z) + c`. |
| T3-M | `stoppingGap_logMass_lowerBound` | There is a natural constant `C` such that for every real `T` some `z` has `m(z) ≥ max(16, T)` and `g(z) ≥ log₂ m(z) − log₂ log₂ m(z) − C`. |
| T3-LENGTH | `stoppingGap_logLength_lowerBound` | There is a natural constant `C` such that for every natural `N` some `z` has length `\|z\| ≥ max(16, N)` and `g(z) ≥ log₂ log₂ \|z\| − log₂ log₂ log₂ \|z\| − C`. |

An admissible discount (`IsAdmissibleDiscount`) is a total computable,
nondecreasing `f : ℕ → ℕ` that satisfies the schedule inequality R1, has bounded
shifts (`f(n + a) − f(n)` is bounded for each `a`), and makes the sums
`Σ 2^−f(E_i)` along the common schedule `E_i` unbounded. MAIN follows from GENERAL
for the discount `discountF`, `F(n) = L(n′) + L(L(L(n′)))` with `n′ = max(16, n)` and `L`
the ceiling of `log₂`, whose divergence condition is proved in `Divergence`.
MAIN says that the excess of the gap over `log₂ m + log₂ log₂ log₂ m` is unbounded
and is attained at arbitrarily large mass depths, hence by infinitely many
strings; it does not say that the inequality holds for every long string. The
only upper bound formalized here is the level-colouring bound
`g(z) ≤ 2⌈m(z)⌉ + 3 + C₀` (`stoppingGap_le_massDepth`), which is what forces the
witnesses above to have large mass depth.

Every theorem of the development depends only on the axioms `propext`,
`Classical.choice` and `Quot.sound`; the axiom sweep of `scripts/audit.sh`
checks this for each of them.

**Module map.** The 31 modules of `KolmogorovMathlib/StoppingComplexity/`, in
dependency order:

| Module | Contents |
| --- | --- |
| `Words` | Binary words, prefix order, cylinders and fixed-length codes |
| `DyadicCells` | Dyadic cells |
| `RatComputableExtras` | Primitive recursive floor and ceiling of rationals |
| `CeilLog` | Computable ceiling logarithms and the discount `F` |
| `PathBudget` | Requests, path loads and budgets |
| `Game` | The generalized finite stopping-allocation game |
| `CellCounting` | Counting dyadic cells for the marker round |
| `LegalHistory` | Legal local histories: disjoint answers and path loads |
| `Schedule` | The common increasing schedule and its exact budget estimates |
| `Repacking` | Clean regions and exact repacking |
| `MarkerRound` | One round of the game: markers, chains and the residual space |
| `Strategy` | The finite-state strategy for the recursive game and its termination bounds (THEOREM-GAME) |
| `StrategyComputable` | Computability of the strategy |
| `WordGame` | The word-answer game and the shadow of a local strategy |
| `Machine` | Operational randomized stopping machines |
| `TimeSemimeasure` | Time semimeasures and request streams |
| `StopProbability` | The stopping probability of a machine |
| `Universal` | The fixed universal stopping machine, `M_stop` and `K_stop` |
| `Allocator` | Effective seed allocation on a finite grid |
| `AllocatorLimit` | Limiting seed events of the allocator |
| `Realization` | Realization of an effective time semimeasure by a stopping machine |
| `Diagonalization` | The global enumerator and the generic diagonalization theorem |
| `MassDepth` | The mass depth `m` and the stopping gap `g` |
| `FixedRatio` | The fixed-ratio (T3) schedule and its word family |
| `AdmissibleDiscount` | Admissible discounts and the variable-discount word family |
| `Divergence` | A discrete divergence proof for the discount `F` |
| `UpperBoundStreams` | Effective approximations behind the level-colouring upper bound |
| `UpperBound` | Level colouring and the upper bound on the stopping gap |
| `GeneralCriterion` | RAW and GENERAL: the gap exceeds every admissible discount |
| `MainTheorem` | MAIN: the gap exceeds `log m + log log log m` by any constant, infinitely often |
| `LengthBounds` | T3-M and T3-LENGTH: explicit bounds in the mass depth and in the string length |

**Source.** The machine model, the universal machine, the realization of time
semimeasures by stopping machines, the reduction of the separation to a game and
the level-colouring upper bound follow Mikhail Mironov, Aram Ebtekar and Cole
Wyeth,
[*Failure of the coding theorem for randomized stopping machines*](https://www.lesswrong.com/posts/wJzhoe4hB8Xc8Fbvw/failure-of-the-coding-theorem-for-randomized-stopping)
(LessWrong, 2026-09-19). That post proves that the gap is unbounded (for every `c`
some `z` has `K_stop(z) > −log M_stop(z) + c`) and that
`K_stop(z) ≤ −log M_stop(z) + K(⌈−log M_stop(z)⌉) + O(1)`, with `K` the prefix
complexity, and leaves open whether this upper bound is sharp. The quantitative
lower bounds formalized here, T3 (the targets T3-M and T3-LENGTH) and its
strengthening T3c (MAIN, with the general criterion GENERAL), are due to the
author of this repository (proof blueprint of 2026-09-27); the docstrings cite
that blueprint by chapter and section and use its target names. The exact second-order term of the gap
remains open.

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

This branch is pinned to Lean `v4.28.0` and the matching Mathlib ecosystem.

## Branches

This branch, `lean-4.28-stopping`, is the Lean `v4.28.0` line of the library: it is
pinned to Lean `v4.28.0` together with the matching Mathlib ecosystem, and it
carries the stopping-complexity formalization described above.  `main` is the
development branch and is pinned to Lean `v4.33.1`; it does not contain the
stopping-complexity development.  The historical `lean-4.28-aristotle` branch
keeps the August 2026 snapshot of the Lean `v4.28.0` state of the library.

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
├── MonotoneComplexity/          # Monotone complexity, effective dimension, Omega and Solovay functions
├── AlgorithmicProbability/      # Semimeasures, mixtures, domination, universal semimeasures, coding tools
├── AlgorithmicRandomness/       # Martin-Löf randomness and lower-semicomputable characterisations
├── AlgorithmicStatistics/       # Stochasticity, deficiencies, models, non-stochasticity, two-part profiles
│   └── TwoPart/                 # Descriptions, gap counting, profiles, curve realization, paper-facing theorems
├── CommonInformation/           # Common information, extraction obstructions, incidence regions
├── Restricted/                  # Description families and restricted profiles from Section 6
│   ├── FamilyCurve/             # Effective multiscale construction and general curve realization
│   └── Examples/                # Cylinders, masks, and Hamming-ball families
├── StoppingComplexity/          # Randomized stopping machines, K_stop and M_stop, and the
│                                #   lower bounds on the gap between them
└── Deprecated/                  # `@[deprecated] alias`es for the old names, generated from the rename table

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
`lake-manifest.json` to the Lean `v4.28.0` ecosystem.

