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
remain available under its namespace-qualified source name with its source
multiplicity, declaration kind, and public attributes. The fidelity checker
also requires exact structural agreement between the compatibility ledger and
the Lean smoke assertions.

The source-authoritative `COVERAGE.md` is restored. Its mathematical coverage
claims are unchanged; the Primrec toolkit row alone uses the documented Lean
4.31 names `Primrec.list_drop_listFirst`, `Primrec.list_take_listFirst`, and
Mathlib-owned `Primrec.list_takeWhile`.

All 118 modules pass strict direct elaboration without project linter
suppressions. The dependency-aware build has four maximal roots:
`KolmogorovMathlib`,
`KolmogorovMathlib.AlgorithmicProbability.KraftChaitinOnline`,
`KolmogorovMathlib.AlgorithmicStatistics.FiniteDistribution`, and
`KolmogorovMathlib.Prefix.KPPairSwap`. The protected validation repair is
complete: `COVERAGE.md` is mandatory, parser regression tests pass, all 18
ledger pairs are checked structurally and resolved by Lean, and smoke files are
included in the suppression scan. The release audit passes; only the
deterministic final gate and its independent review remain.

## Lean 4.31 API Adaptations

The 18 compatibility-ledger entries are:

| Final Lean 4.28 declaration | Lean 4.31 evidence |
|---|---|
| `List.dedup` | `List.localDedup` |
| `List.dedup_nodup` | `List.nodup_localDedup` |
| `mem_List.dedup` | `List.mem_localDedup` |
| `list_dedup_eq_root` | `List.localDedup_eq_dedup` |
| `list_dedup_eq_root_gen` | `List.localDedup_eq_dedup` |
| `list_dedup_gen_primrec` | `local_dedup_primrec` |
| `_root_.Primrec.list_drop` | `Primrec.list_drop_listFirst` |
| `_root_.Primrec.list_take` | `Primrec.list_take_listFirst` |
| `_root_.Primrec.list_takeWhile` | `Primrec.list_takeWhile` |
| `UniquelyDecodable` | `InformationTheory.UniquelyDecodable` |
| `emittedHalfRichChunks_fold_step` | `emittedHalfRichChunksFoldStep` |
| `emittedHalfRichChunks_fold_step_primrec` | `emittedHalfRichChunksFoldStep_primrec` |
| `emittedHalfRichChunks_step` | `emittedHalfRichChunksStep` |
| `emittedHalfRichChunks_step_primrec` | `emittedHalfRichChunksStep_primrec` |
| `ge_invPow2` | `RatMass.geInvPow2` |
| `logSlack_add_nat_le` | `logSlack_add_const_le` |
| `mem_eraseDups_bitString` | `List.mem_eraseDups` |
| `nodup_eraseDups_bitString` | `CodedFiniteDistribution.eraseDups_bitstring_nodup` |

## Migration Work

1. Run `scripts/check_migration_fidelity.py` and close every unaccounted
   declaration gap. Preserve stronger source statements; document and
   machine-check unavoidable 4.31 renamings or equivalent replacements.
2. Review changed modules in dependency-aware batches. For every edited Lean
   file run `scripts/check_affected.py --direct-only <files>` before the merge
   gate. A touched file is accepted only when strict `flexible`, `longLine`,
   `multiGoal`, and `openClassical` checking is silent.
3. The three temporary project suppressions in `lakefile.toml` have been
   removed after repairing their complete warning classes; no warning was
   moved, renamed, or locally suppressed.
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
- Successful dependency-aware full build, external `primrec_auto` smoke test,
  and exact 18-pair migration-compatibility smoke test.
- A final `scripts/audit.sh --release` before and after an independent
  read-only Codex review.

The loop may stop only when `scripts/final_release_gate.py` records
`proof_loop/MIGRATION_COMPLETE.json`. A clean cached build, zero visible
warnings, completion of the original 39-file port, or an agent's unsupported
claim is not sufficient.
