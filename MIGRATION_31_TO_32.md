# Full-Fidelity Lean 4.31 to 4.32.1 Migration

## Objective

Produce a Lean 4.32.1 development that preserves every mathematical result,
public interface, proof-quality improvement, warning cleanup, and scalability
property of the final polished Lean 4.31 release.

The sole source authority is the immutable snapshot `/home/lesha/kolmogorov-complexity-lean-31-migration-source-final-20260726T154201Z` at commit
`f2bc405f4cea36deb0f65bd0f36a7a03fe7800d6`. All 118 project modules are in scope, including files that happen
to compile without edits. A successful build is necessary but does not replace
declaration-fidelity, strict-linter, release-audit, and independent-review gates.

## Initial State

The target starts as an exact copy of the final Lean 4.31 release with only the
Lean and Mathlib pins changed to 4.32.1. The 31-to-32 compatibility ledger is
initially empty. Add an entry only for a real, human-reviewed API adaptation;
never use the ledger to hide a lost theorem.

The isolated preflight found the first concrete incompatibility in
`AlgorithmicProbability/KraftChaitinCore.lean`: two computability proof terms
no longer elaborate under 4.32.1 and their downstream elaboration reaches the
default heartbeat limit. This is migration work, not a reason to weaken the
statement or add a project heartbeat override.

## Work Order

1. Restore strict direct elaboration of each failing module with narrow 4.32.1
   API adaptations and targeted checks.
2. Preserve exact module and public-declaration coverage against the immutable
   Lean 4.31 snapshot.
3. Run dependency-aware builds for all maximal roots and the external tactic
   smoke test.
4. Remove every warning, temporary compatibility scaffold, broad import,
   heartbeat override, linter suppression, and avoidable proof-style regression.
5. Pass `scripts/audit.sh --release` twice around an independent final review.

## Acceptance

The migration is complete only when `scripts/final_release_gate.py` writes
`proof_loop/MIGRATION_COMPLETE.json` with `status = release_complete` and a
`commit_32` release commit. Zero visible warnings or a cached aggregate build
alone is not sufficient.
