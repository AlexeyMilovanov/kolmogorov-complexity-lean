# Full-Fidelity Lean 4.28 to 4.31 Migration

## Objective

Produce a Lean 4.31 development that contains every mathematical result and
public interface from the final polished Lean 4.28 snapshot, preserves the
intentional Lean 4.31 API adaptations, and reaches at least the same cleanliness
and Mathlib-style standard as the source.

The immutable source of truth is recorded in
`proof_loop/migration_source.json`. The migration concerns all 118 project
modules, not only the 39 modules that were initially absent from Lean 4.31.
Shared files also require result, interface, warning, proof-style, and
maintainability review. Textual identity is not required where Lean 4.31 or
Mathlib APIs changed; mathematical and interface fidelity is required.

The order of completion is strict:

1. restore complete mathematical and public-API coverage;
2. make every touched module pass strict direct elaboration;
3. remove all project linter suppressions and remaining style debt;
4. retain scalable validation and dependency-aware build tooling;
5. pass the deterministic release audit and an independent final review.

## Current Inventory

The source and target contain the same 118 module paths: 117 files under
`KolmogorovMathlib/` plus `KolmogorovMathlib.lean`. Only one common file is
currently byte-identical, so path presence alone is not evidence of a complete
migration.

The original 39 missing files have been ported. Eighteen source declaration
names are represented by intentional Lean 4.31 API adaptations recorded in
`proof_loop/migration_compatibility.json`. Every other public declaration must
remain available under its source name. The fidelity checker currently exposes
any omission instead of allowing prose status files to hide it.

## Migration Work

1. Run `scripts/check_migration_fidelity.py` and close every unaccounted
   declaration gap. Preserve stronger source statements; document and
   machine-check unavoidable 4.31 renamings or equivalent replacements.
2. Review changed modules in dependency-aware batches. For every edited Lean
   file run `scripts/check_affected.py --direct-only <files>` before the merge
   gate. A touched file is accepted only when strict `flexible`, `longLine`,
   `multiGoal`, and `openClassical` checking is silent.
3. Remove the three temporary project suppressions in `lakefile.toml`. Do this
   only after their complete warning classes have been repaired, never by
   moving, renaming, or locally suppressing warnings.
4. Preserve or improve the final 4.28 proof quality: no proof golf that obscures
   mathematics, no duplicated compatibility layer, no unnecessary imports,
   stale comments, brittle generated proof terms, or avoidable architectural
   coupling.
5. Treat expected 10x-100x growth as a design constraint. Keep module
   ownership, import direction, local feedback time, and release validation
   sustainable as described in `SCALABILITY_31_PLAN.md`.

## Acceptance Gates

- Exact equality of source and target module-path inventories.
- Complete public declaration coverage, except for machine-readable,
  evidence-checked entries in the compatibility ledger.
- No `sorry`, `sorryAx`, `admit`, custom axiom, `unsafe`, `implemented_by`,
  theorem weakening, hidden result loss, or other escape hatch.
- No warning, broad `import Mathlib`, project `set_option maxHeartbeats`,
  project linter suppression, profiler directive, build artifact, or temporary
  proof scaffold in the release tree.
- Silent strict direct elaboration of all 118 modules, including modules not
  reachable from the aggregate root.
- Successful dependency-aware full build and external `primrec_auto` smoke
  test.
- A final `scripts/audit.sh --release` before and after an independent
  read-only Codex review.

The loop may stop only when `scripts/final_release_gate.py` records
`proof_loop/MIGRATION_COMPLETE.json`. A clean cached build, zero visible
warnings, completion of the original 39-file port, or an agent's unsupported
claim is not sufficient.
