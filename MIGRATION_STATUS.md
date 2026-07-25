# Migration Status

All 39 source-only Lean 4.28 files are present in the Lean 4.31 tree and are
reachable from the root module. The remaining work is polishing, not porting.

## Gates

- Source-only files represented in Lean 4.31: 39 / 39
- Lean file count: 117 source, 117 target; no source-only or target-only paths
- Root reachability: 115 / 118 modules reachable from `KolmogorovMathlib.lean`;
  the 3 exceptions (`AlgorithmicProbability.KraftChaitinOnline`,
  `AlgorithmicStatistics.FiniteDistribution`, `Prefix.KPPairSwap`) are
  pre-existing standalone modules, also unreachable in 4.28, and are built
  explicitly
- Full Lean 4.31 build: passed (`2831/2831` jobs, root plus the 3 standalone
  modules)
- Errors: 0
- Warnings: 0 (each of the 39 migrated files was additionally elaborated
  individually so that build caching could not mask a warning)
- Sorries and forbidden escape hatches: 0
- Declaration coverage: every source declaration is represented; the 18 source
  names without same-named target declarations have Lean-checked equivalence
  witnesses
- Signature coverage: 0 signature differences inside the 39 migrated files
- Polishing phase: started; stale documentation and hard-tab cleanup completed

## Compatibility ledger

Shared 4.31 modules keep their deliberate signatures. Where 4.31 weakened a
4.28 interface, the 4.28 strength is restored by an additively added,
separately named companion, and each is machine-checked to imply the verbatim
4.28 statement:

| Lean 4.28 result | Lean 4.31 representation |
| --- | --- |
| `gap_lowerBound_conditional_setComplexity_tight` | `..._tight_of_le_add` |
| `manyIJDescriptions_of_realizedSetOptimalityGap` | `..._of_le_add` |
| `GapCountingBridge` | `GapCountingBridgeWithSOI` |
| `TightGapCountingBridge` | `TightGapCountingBridgeWithSOI` |
| `deficiencies_theorem` | `deficiencies_theorem_with_soi` |
| `deficiencies_theorem_tight` | `deficiencies_theorem_tight_with_soi` |
| `deficiencies_theorem_tight_of_optimal` | `deficiencies_theorem_tight_of_optimal_with_soi` |
| `logSlack_add_nat_le` | `logSlack_add_const_le` |
| `mem_eraseDups_bitString` | `List.mem_eraseDups` (Mathlib) |
| `nodup_eraseDups_bitString` | `CodedFiniteDistribution.eraseDups_bitstring_nodup` |
| `Primrec.list_drop` / `list_take` / `list_takeWhile` | native Mathlib 4.31; list-first order via `Primrec.list_drop_listFirst` / `list_take_listFirst` |
| `List.dedup` and its API | `List.localDedup` and its API |
| `list_dedup_gen_primrec` | `localDedup_gen_primrec` |
| `list_dedup_eq_root`, `list_dedup_eq_root_gen` | `List.localDedup_eq_dedup` |
| `ge_invPow2` | `geInvPow2` |
| `emittedHalfRichChunks_fold_step`, `..._step` and their `_primrec` lemmas | `emittedHalfRichChunksFoldStep`, `emittedHalfRichChunksStep` and their `_primrec` lemmas |
| `UniquelyDecodable` | Mathlib `InformationTheory.UniquelyDecodable` |

## Remaining cleanup

- Remove the migration scaffolding (`scripts/run_migration_loop.py`,
  `scripts/audit.sh`, `proof_loop/`, `MIGRATION_28_TO_31.md`, this file) once
  the migration loop finishes.
- `scripts/audit.sh` now builds the root target and the 3 pre-existing
  standalone modules explicitly; retain that coverage until the migration loop
  finishes.
- The six declarations whose explicit `@[simp]` attributes disappeared relative
  to 4.28 were checked against the 4.31 simplifier; all six source rewrite goals
  already close with the current simp set, so restoring redundant attributes is
  unnecessary.
- `primrec_auto` has no in-tree use sites but remains part of the preserved
  4.28 public API. Because nothing expands it, the library build could not
  detect that it was broken: its `apply_rules` list names `Primrec.to_comp`,
  which lives in `Mathlib.Computability.Partrec`, while `Foundation/PrimrecExtras`
  imported only `Mathlib.Computability.Primrec.List`. A tactic quotation
  resolves identifiers against its declaration site, so every expansion failed
  with `Unknown constant 'Primrec.to_comp'`. Lean 4.28 has the same import set,
  so this was a latent 4.28 defect rather than migration drift. Fixed by adding
  the `Partrec` import; `primrec_auto` now closes `Primrec` and `Computable`
  goals within its documented (non-higher-order) scope. Do not drop that import
  in an unused-import sweep — no declaration in the file mentions it.
