# Migration Status

The original file-porting phase is complete, but the full-fidelity migration is
not yet release-ready.

## Verified State

- Final Lean 4.28 source: immutable snapshot and commit recorded in
  `proof_loop/migration_source.json`.
- Module paths: 118 / 118 in both source and target; no source-only or
  target-only paths.
- Initially absent Lean 4.28 files ported to Lean 4.31: 39 / 39.
- Common files that differ textually: 117 / 118.
- Intentional Lean 4.31 API adaptations: 18, recorded with target evidence in
  `proof_loop/migration_compatibility.json`.
- Sorries and forbidden escape hatches in the current target: none known.
- Existing ordinary Lean 4.31 build: successful.

## Open Release Blockers

- `countP_lt_of_witness` from the final Lean 4.28 public surface is not currently
  present under its source name and is not an approved compatibility mapping.
  The equivalent argument appears to have been inlined locally in Lean 4.31;
  restore the reusable theorem or supply a justified, machine-checked API
  adaptation.
- `lakefile.toml` still disables the project `longLine`, `multiGoal`, and
  `flexible` linters. Zero warnings under those suppressions is not a clean
  release.
- All 118 shared module paths still need strict per-file validation under the
  final linter configuration. The old status covered the 39 newly ported files,
  not the entire migrated codebase.
- The full-fidelity release gate has not passed and
  `proof_loop/MIGRATION_COMPLETE.json` does not yet exist.

## Validation Contract

- `scripts/check_migration_fidelity.py` checks module equality, public
  declaration coverage, the compatibility ledger, and required validation
  infrastructure.
- `scripts/check_affected.py` provides dependency-aware fast feedback and
  strict direct checking for touched modules.
- `scripts/audit.sh` is the ordinary merge gate.
- `scripts/audit.sh --release` additionally requires all project linter
  suppressions to be gone and runs the complete uncached strict sweep.
- `scripts/final_release_gate.py` performs the deterministic release audit,
  obtains an independent read-only review, repeats the audit, and records
  completion only if the source tree did not change during review.

The migration runner uses Gemini for implementation and Codex for review,
repair, and continuation. Strategy iterations are 1, 6, 11, and so on.
Strategy output can request a release decision, but only the final release gate
can finish the migration.
