# Kolmogorov Complexity in Lean 4 ? Aristotle-Compatible Branch

This branch is pinned to Lean `v4.28.0` and Mathlib `v4.28.0`, matching the
version currently supported by Aristotle. The main GitHub branch tracks the
modern Lean/Mathlib line (`v4.31.0`).

Build:

```bash
lake exe cache get
lake build KolmogorovMathlib
```

The development formalizes parts of algorithmic information theory and
algorithmic statistics, including plain and prefix Kolmogorov complexity,
algorithmic probability infrastructure, finite rational probability models,
non-stochastic strings, and the Section 3 two-part description machinery used
in the algorithmic statistics development.

This branch is intended as the stable Aristotle working line. After a section is
formalized and polished here, it can be migrated to `main`.
