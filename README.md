# Formalized Algorithmic Information Theory in Lean 4

This repository contains a Lean 4 formalization of algorithmic information theory,
built on Mathlib.

The main references are Alexander Shen, Vladimir A. Uspensky, and Nikolai Vereshchagin,
[*Kolmogorov Complexity and Algorithmic Randomness*](https://www.lirmm.fr/~ashen/kolmbook-eng-scan.pdf)
(SUV), and Nikolai Vereshchagin and Alexander Shen,
[*Algorithmic statistics: forty years later*](https://arxiv.org/abs/1607.08077).

The development is based on Mathlib's computability infrastructure. Decompressors are represented as partial functions, finite objects are represented by bitstrings, and most theorem statements are phrased up to the additive or logarithmic slack terms natural in Kolmogorov-complexity arguments.

## What Is Formalized

- **The SUV book:** essentially the whole book, Chapters 1-14: plain, conditional, prefix
  and monotone complexity, a priori probability, Martin-Löf randomness, the general scheme
  for complexities, Shannon entropy, applications of complexity, frequency and game
  approaches to randomness, information inequalities, common information, multisource
  information theory, information and logic, and algorithmic statistics. Nearly all numbered
  theorems and most of the problems are formalized;
  [`docs/SUV_STATUS.md`](docs/SUV_STATUS.md) gives the state of every item.
- **Algorithmic statistics:** finite-set and distribution models, stochasticity
  profiles, restricted descriptions and strong sufficient statistics, following
  the Vereshchagin-Shen survey.
- **Incompleteness:** Chaitin-style and
  [Kritchman-Raz-style results](https://arxiv.org/abs/1011.4974), using abstract
  formal-system interfaces rather than a concrete arithmetic system.
- **Further developments:** Solomonoff induction, Solomonoff prediction of selected
  bits, the negative answer to Shen's question on the a priori probability of a prefix,
  stopping complexity, and the exact realisation of `min(K, F)` for an entropy function `F`
  by a prefix machine (Allender-Friedman-Gasarch, Claim 1), and the Allender-Friedman-Gasarch
  theorem that a decidable set polynomial-time reducible to the `K_U`-random strings for
  every optimal prefix machine `U` lies in `EXPSPACE` (resource-bounded machines, complexity
  classes and the game construction in `KolmogorovMathlib/RandomStrings/`).
- **C-random strings:** the theorem of Milovanov, *Limit on the Computational Power
  of C-Random Strings* (FOCS 2026), that some optimal plain decompressor `U` has a
  cumulative complexity oracle and a set of `C_U`-random strings neither of which computes
  the halting language in polynomial time
  (`Kolmogorov.Milovanov.exists_optimal_native_halting_oracle_separation` in
  `KolmogorovMathlib/RandomStrings/Plain/`).
- **Point-to-set principles in dynamical systems:** Dinowitz's characterizations of
  topological pressure, Barreira-Schmeling dimension and, for conformal systems, Hausdorff
  and packing dimension as minima over oracles of suprema of pointwise Kolmogorov-complexity
  quantities, and the Bowen equations, following a corrected blueprint with counterexamples
  to the printed claims that fail (`Kolmogorov.PointToSet.lowerPressure_pointToSet`,
  `bsPointToSet`, `dimensionTheorem` in `KolmogorovMathlib/PointToSet/`, built on the oracle
  prefix complexity of `KolmogorovMathlib/Oracle/`).
- **Prediction and MDL for infinite sequences:** Milovanov's theorems (*Theory of Computing
  Systems*, 2024) that the predictor which selects, at each observed prefix `x`, a computable
  measure `Q` of minimal two-part score `3·K(Q) − log₂ Q(x)` merges with every computable
  source on its random paths and has finite pathwise and expected squared-error sums, the
  corrected polynomial bounds for effective classes closed under finite mixtures, and a
  counterexample to the measure-uniform Lemma 5 of the printed proof
  (`Kolmogorov.MDLPrediction.predictor_merges_on_random`, `pathwise_sq_bound`,
  `expected_sq_bound`, `class_pathwise_sq_polynomial`, `class_expected_sq_polynomial`,
  `uniformPrefixDropFalse` in `KolmogorovMathlib/MDLPrediction/`).
- **Truth-table reductions to the random strings:** the theorem of Cai, Downey, Epstein,
  Lempp and Miller (*Logical Methods in Computer Science*, 2014, Theorem 4.1) that for every
  noncomputable set `X` there is an optimal prefix machine `U` such that `X` is not
  truth-table reducible to the set of `K_U`-random strings, so that the sets tt-reducible to
  the random strings of every optimal prefix machine are exactly the computable sets; the
  construction is modified where the printed proof of Lemma 4.3 appears to have a gap (a
  reading not confirmed with the authors, see the notes)
  (`Kolmogorov.RandomStrings.TTMeet.theorem_4_1`, `theorem_4_1_unconditional`,
  `ttMeet_iff_computable` in `KolmogorovMathlib/RandomStrings/TTMeet2014/`).
- **New strong-merging results:** the square-root merger of two strong sufficient
  statistics, its matching obstruction and the questions of survey Section 7.9.

The [detailed overview](docs/RESULTS.md) lists the main theorems and their modules.
The [SUV status](docs/SUV_STATUS.md) counts the book items by chapter and lists
those that are not formalized in full; the [SUV coverage table](docs/SUV_COVERAGE.md)
records which declaration covers which item.

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

The [SUV coverage table](docs/SUV_COVERAGE.md) maps book items to theorems and
is regenerated by `scripts/gen_suv_coverage.py`.

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

This branch is pinned to Lean `v4.35.0` and the matching Mathlib ecosystem.

## Branches

`main` is the development branch and is pinned to Lean `v4.35.0` together with
the matching Mathlib ecosystem. Historical branches preserve earlier Lean releases.

## Project Layout

The [module tree and project layout](docs/RESULTS.md#project-layout) are included
with the detailed overview.

## Lake Metadata

The Lake package is named `kolmogorov_complexity`; the Lean library targets are
`KolmogorovMathlib` and `KolmogorovCounterexamples`. The Mathlib dependency is pinned in `lakefile.toml` and
`lake-manifest.json` to the Lean `v4.35.0` ecosystem.
