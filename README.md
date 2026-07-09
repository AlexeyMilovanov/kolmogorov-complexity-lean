# Formalized Algorithmic Information Theory in Lean 4

This repository contains a Lean 4 formalization of algorithmic information theory: Kolmogorov complexity, prefix complexity, universal machines, algorithmic probability, and algorithmic statistics for finite binary strings. The main background reference is Alexander Shen, Vladimir A. Uspensky, and Nikolai Vereshchagin, [*Kolmogorov Complexity and Algorithmic Randomness*](https://www.lirmm.fr/~ashen/kolmbook-eng-scan.pdf). The algorithmic-statistics layer is developed with Nikolai Vereshchagin and Alexander Shen, [*Algorithmic statistics: forty years later*](https://arxiv.org/abs/1607.08077), as a central guide.

The development is based on Mathlib's computability infrastructure. Decompressors are represented as partial functions, finite objects are represented by bitstrings, and most theorem statements are phrased up to the additive or logarithmic slack terms natural in Kolmogorov-complexity arguments.

## What Is Formalized

The core library formalizes plain conditional Kolmogorov complexity for bitstrings, universal decompressors, invariance up to an additive constant, basic complexity inequalities, incompressibility, uncomputability results for natural-number complexity, and Chaitin-style [incompleteness interfaces](https://arxiv.org/abs/1011.4974). The [second-incompleteness files](https://arxiv.org/abs/1011.4974) use abstract formal-system interfaces in a Kritchman-Raz style rather than formalizing a concrete arithmetic system.

The prefix-complexity part develops prefix-free codes and machines, optimal prefix decompressors, conditional prefix complexity, Kraft inequalities and converse constructions, two-stage and pair-coding infrastructure, and symmetry-of-information lemmas including conditional variants.

The algorithmic-probability part formalizes semimeasure infrastructure, a priori machine semimeasures, lower-semicomputable semimeasure interfaces, mixtures, domination lemmas, universal semimeasure constructions, conditional universal semimeasures, and Kraft-Chaitin style coding infrastructure. It also includes the coding-theorem equivalence between conditional prefix complexity and universal conditional a priori semimeasures, corresponding to `K(x | z) = -log m(x | z) + O(1)` and formalized through multiplicative `ENNReal` domination bounds.

The algorithmic-statistics part formalizes finite-set and finite-distribution models, randomness deficiency, stochasticity predicates, non-stochastic strings, selectors, two-part descriptions, optimality deficiency, description shifting, gap-counting and improving-description arguments. The `TwoPart` profile-realization layer includes the current formalization of the main Section 3 machinery from the Vereshchagin-Shen survey: stochasticity profiles, admissible/profile curves, realization of profile curves by strings, antistochastic examples, and non-stochastic corollaries.

## Build

Install Lean through `elan`, then fetch the Mathlib cache and build the exported library target:

```bash
lake exe cache get
lake build KolmogorovMathlib
```

For the default package build, run:

```bash
lake build
```

The project is currently pinned to Lean `v4.31.0` and the matching Mathlib ecosystem.

## Branches

The `main` branch contains the current Lean `v4.31.0` version. A Lean `v4.28` version is preserved on the [`lean-4.28-aristotle`](https://github.com/AlexeyMilovanov/kolmogorov-complexity-lean/tree/lean-4.28-aristotle) branch as a stable reference point for the earlier Mathlib ecosystem and for comparison with the Lean 4.31 migration.

## Project Layout

```text
KolmogorovMathlib/
├── Foundation/                  # Search operators, recursively enumerable relations, Nat/bitstring encodings
├── Core/                        # Partial decompressors, plain complexity, universal decompressor, invariance
├── Complexity/                  # Bounds, incompressibility, uncomputability, incompleteness interfaces
├── Prefix/                      # Prefix machines, Kraft theory, prefix complexity, symmetry of information
├── AlgorithmicProbability/      # Semimeasures, mixtures, domination, universal semimeasures, coding tools
└── AlgorithmicStatistics/       # Stochasticity, deficiencies, models, non-stochasticity, two-part profiles
    └── TwoPart/                 # Descriptions, gap counting, profiles, curve realization, paper-facing theorems
```

The top-level module `KolmogorovMathlib.lean` imports the library development.

## Lake Metadata

The Lake package is named `kolmogorov_complexity`; the Lean library target is `KolmogorovMathlib`. The Mathlib dependency is pinned in `lakefile.toml` and `lake-manifest.json` to the Lean `v4.31.0` ecosystem.
