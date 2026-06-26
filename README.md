# Formalization of Algorithmic Information Theory in Lean 4

This repository contains a Lean 4 formalization of parts of algorithmic
information theory, centered on Kolmogorov complexity.  The development uses
Mathlib's computability infrastructure and represents decompressors as partial
functions (`Part`).

The project is currently pinned to Lean `v4.31.0` and Mathlib `v4.31.0`.

## Build

Install Lean through `elan`, then run:

```bash
lake exe cache get
lake build
```

For a smaller check of the exported library target, run:

```bash
lake build KolmogorovMathlib
```

## Scope

The original core development formalizes plain conditional complexity for
bitstrings, a universal decompressor, invariance up to an additive constant,
basic complexity inequalities, incompressibility, uncomputability of natural
number complexity, and Chaitin-style incompleteness results.  The
second-incompleteness files use abstract formal-system interfaces in a
Kritchman-Raz style rather than formalizing a concrete arithmetic system.

Recent modules add a prefix-complexity and algorithmic-probability layer.  This
includes prefix-free codes, prefix machines, conditional prefix complexity,
optimal prefix decompressors, Kraft inequalities and converse constructions,
two-stage and pair-coding infrastructure, a priori machine semimeasures,
lower-semicomputable semimeasure interfaces, mixture and domination lemmas, and
Kraft-Chaitin style coding infrastructure.

The prefix and semimeasure material contains substantial theorem statements and
checked infrastructure, but it should be read as an actively developed
formalization layer.  In particular, the repository avoids claiming a finished
textbook equivalence theory with exact logarithmic coding-theorem equalities.
Many results are stated in additive-complexity or multiplicative semimeasure
forms over `ENat` and `ENNReal`.

## Project Layout

```text
KolmogorovMathlib/
├── Foundation/             # Search operators, recursively enumerable relations, Nat.bits encoding
├── Core/                   # Maps, conditional/plain complexity, universal decompressor, invariance
├── Complexity/             # Bounds, incompressibility, uncomputability, incompleteness interfaces
├── Prefix/                 # Prefix-free codes, prefix machines, prefix complexity, Kraft results
└── AlgorithmicProbability/ # A priori semimeasures, LSC semimeasures, mixtures, coding infrastructure
```

The top-level module `KolmogorovMathlib.lean` imports the library development.

## Lake Metadata

The Lake package is named `kolmogorov_complexity`; the Lean library target is
`KolmogorovMathlib`.  The Mathlib dependency is pinned in `lakefile.toml` and
`lake-manifest.json` to the Lean `v4.31.0` ecosystem.

## Development Notes

Some computationally heavy Kraft-Chaitin proofs use local
`set_option maxHeartbeats` overrides.  These are intentionally local to the
affected declarations.

The repository should remain free of `sorry`, `admit`, `axiom`, `unsafe`, and
`set_option profiler true` in Lean sources.
