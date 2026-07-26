# Migration Status

The original file-porting phase and protected validation repair are complete.
The deterministic final release gate is the only remaining step.

## Verified State

- Final Lean 4.28 source: immutable snapshot and commit recorded in
  `proof_loop/migration_source.json`.
- Coverage authority: `COVERAGE.md` is restored from the final Lean 4.28
  snapshot, with only its Primrec toolkit row reconciled to the documented
  Lean 4.31 list-first wrappers and Mathlib-owned `Primrec.list_takeWhile`.
- Module paths: 118 / 118 in both source and target; no source-only or
  target-only paths.
- Initially absent Lean 4.28 files ported to Lean 4.31: 39 / 39.
- Common files that differ textually: 117 / 118.
- Public declaration fidelity: all 2,473 namespace-qualified names / 2,477
  declaration occurrences from final Lean 4.28 are represented, including the
  restored source-named theorem `countP_lt_of_witness`.
- Intentional Lean 4.31 API adaptations: 18, recorded with target evidence in
  `proof_loop/migration_compatibility.json`.
- Sorries and forbidden escape hatches in the current target: none known.
- Strict validation: all 118 modules pass direct elaboration without project
  linter suppressions.
- Dependency-aware build: successful across the four maximal roots
  `KolmogorovMathlib`,
  `KolmogorovMathlib.AlgorithmicProbability.KraftChaitinOnline`,
  `KolmogorovMathlib.AlgorithmicStatistics.FiniteDistribution`, and
  `KolmogorovMathlib.Prefix.KPPairSwap`.
- Release audit: `scripts/audit.sh --release` passed with `AUDIT OK` after the
  protected validator repair.

The 18 compatibility mappings, including the list-first Primrec wrappers, are
enumerated in `MIGRATION_28_TO_31.md`.

## Remaining Release Step

- The full-fidelity release gate has not yet run to completion and
  `proof_loop/MIGRATION_COMPLETE.json` does not yet exist.

## Validation Contract

- `scripts/check_migration_fidelity.py` checks module equality,
  namespace-qualified declaration multiplicity, declaration kinds, source
  attributes, exact structural compatibility-ledger assertions,
  `COVERAGE.md`, and required validation infrastructure.
- `scripts/test_migration_fidelity.py` regression-tests attributes, namespaces,
  multiplicity, comment rejection, compatibility assertions, and coverage
  normalization.
- `scripts/check_affected.py` provides dependency-aware fast feedback and
  strict direct checking for touched modules.
- `scripts/audit.sh` is the ordinary merge gate.
- `scripts/audit.sh --release` additionally requires all project linter
  suppressions, including smoke-file suppressions, to be gone and runs the
  complete uncached strict sweep.
- `scripts/final_release_gate.py` performs the deterministic release audit,
  obtains an independent read-only review, repeats the audit, and records
  completion only if the source tree did not change during review.

The migration runner uses Gemini for implementation and Codex for review,
repair, and continuation. Strategy iterations are 1, 6, 11, and so on.
Strategy output can request a release decision, but only the final release gate
can finish the migration.
