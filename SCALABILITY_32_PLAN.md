# Lean 4.32.1 Scalability and Validation Plan

The Lean 4.32.1 tree is intended to grow by one or two orders of magnitude. Its
normal development workflow therefore needs fast local feedback without
weakening final acceptance.

## Validation Layers

1. `scripts/check_affected.py --direct-only <files>` strictly elaborates every
   touched Lean source with the project style linters enabled. This is the
   mandatory ordinary merge check for edited modules.
2. `scripts/check_affected.py <files>` computes the transitive reverse-import
   closure and builds its maximal modules. It is the default developer feedback
   command for changes whose downstream compatibility matters.
3. `scripts/audit.sh` checks repository hygiene, all discovered build roots,
   warnings, the external tactic smoke test, and the strict sweep once
   project-wide suppressions are gone.
4. `scripts/audit.sh --release` always requires the complete strict sweep and
   rejects every project linter suppression.

The import graph is discovered from source rather than encoded as a fixed list.
The current project has 118 modules and four maximal build roots:
`KolmogorovMathlib`,
`KolmogorovMathlib.AlgorithmicProbability.KraftChaitinOnline`,
`KolmogorovMathlib.AlgorithmicStatistics.FiniteDistribution`, and
`KolmogorovMathlib.Prefix.KPPairSwap`. The latter three include standalone
modules not imported by `KolmogorovMathlib.lean`. New modules and new maximal
roots must therefore enter validation automatically.

## Growth Constraints

- Keep foundational modules low in the import graph small, stable, and free of
  domain-specific dependencies. A change there has the largest rebuild radius.
- Give each major mathematical layer a clear aggregate module and keep imports
  directed from foundations toward applications.
- Avoid convenience imports that collapse layer boundaries. Import the
  narrowest stable module that owns the needed API.
- Split a module when it has distinct ownership or creates a material
  elaboration/rebuild bottleneck, not merely to reduce line count.
- Keep reusable definitions and lemmas public and named; do not inline
  substantial interfaces merely to shorten a proof.
- Prefer focused regression and smoke files outside the library import graph
  for tactics or APIs that have no in-tree call site.
- Measure build or elaboration bottlenecks before adding performance-specific
  options. Project `maxHeartbeats`, profiler directives, and linter
  suppressions are not accepted substitutes for structural fixes.

## Release Baseline

The Lean 4.32.1 migration is complete only when:

- all final Lean 4.31 mathematics and public interfaces are represented;
- every module is strictly warning-free without project suppressions;
- the dependency-aware build covers every maximal root;
- validation scripts remain checked in and usable for future changes;
- no known architectural or proof-style debt is deferred merely because the
  current project still builds quickly.

This baseline is deliberately reusable for the later Lean 4.32.1 to newer stable
Lean migration.
