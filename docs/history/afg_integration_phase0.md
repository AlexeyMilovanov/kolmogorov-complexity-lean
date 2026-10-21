# AFG integration, phase 0 (2026-10-20)

The Allender–Friedman–Gasarch formalisation (the standalone `AFG` development, 29 modules, Lean 4.35) is imported as
`KolmogorovMathlib/RandomStrings/`. Phase 0 is a mechanical port; the cleanup is the next phase.

## What changed

* `AFG/X.lean` became `KolmogorovMathlib/RandomStrings/X.lean`; imports `AFG.X` became
  `KolmogorovMathlib.RandomStrings.X`; the namespace `RandomStrings` became
  `Kolmogorov.RandomStrings`; every file got the standard copyright header.
* `Str` was replaced by `Kolmogorov.BitString` and its abbrev deleted (`Basic.lean` now also
  imports `KolmogorovMathlib.Prefix.EntropyFunctions`).
* `AprioriComplexity` keeps its shape; its fields are now `kraft : IsKraftFun H` and
  `re : HasREOvergraph H`.
* `PFEntropy` and `PFEntropy.toApriori` were deleted; every use is now `Kolmogorov.IsEntropyFun`
  (Construction, General, PrefixForm, `Hmin_kraft`/`Hmin_re`/`HminApriori*`). `ov` is kept
  (used by `Flim_re` in Construction).
* `Apriori.lean`: removed `exists_reEnum` and the whole trim/mixture block (`memB` … `mixH_re`,
  about 560 lines). `exists_universal_apriori` (same statement) is now a 20-line proof:
  `K_U` for an optimal prefix decompressor `U` (`exists_isOptimalPrefixConditional`,
  `KPPlain_toNat_kraft`, `REPred_KPPlain_toNat_le`), and universality from
  `exists_isOptimalPrefixConditional_min_toNat` plus the optimality of `U`. `REPred.exists_stage`
  and `REPred_exists_nat` were kept (Construction uses them). `Hmin`, `HminApriori`,
  `HminApriori_universal` are unchanged apart from the renames.
* `PrefixForm.lean`: the `simpa [HasREOvergraph, ov]` conversion became unnecessary and was
  removed. `dec_inter_polyTime_RA_subset_EXPSPACE` (from the AFG project's `Solution.lean`, which
  lives outside the `AFG` library) was added here, so both forms of the main theorem are in the
  library.
* `KolmogorovMathlib.lean` imports the leaves `KeyInstances`, `PathDataSATree`, `PrefixForm`,
  `SAExpE`; README module tree has a `RandomStrings/` line.

## State

`lake build`: success, 0 errors, 948 warnings, all in `RandomStrings` (mathlib style linters:
longLine 641, show 229, flexible 41, maxHeartbeats-comment 21, emptyLine 13, multiGoal 2,
openClassical 1). `#print axioms` of `dec_inter_polyTime_prefixRandom_subset_EXPSPACE`,
`dec_inter_polyTime_RA_subset_EXPSPACE` and `exists_universal_apriori`: `propext`,
`Classical.choice`, `Quot.sound`.

Gates: `forbidden_scan --mode forbidden` fails on the 21 `maxHeartbeats` overrides in
`Expspace.lean` and nothing else; `--mode sorry` clean; `module_docs --check`, `import_hygiene`
OK; `check_dup_decls` 24 clashes, the same as on `main`; `docstring_coverage --check` OK
(RandomStrings is not in `COMPLETE`); `cut_quality` 53 unlisted, all in RandomStrings; `prose_scan`
11 hits in RandomStrings. No allowlist was edited.

## Dirt inventory

Columns: lines; `maxHeartbeats` overrides; proofs over 150 lines (`long_proofs.py --min 151`);
undocumented public declarations; lines over 100 characters; unlisted `cut_quality` findings;
`prose_scan` hits.

| file | lines | overrides | proofs >150 | undocumented | lines >100 | cut | prose |
|---|---|---|---|---|---|---|---|
| Apriori | 246 | 0 | 0 | 0 | 4 | 0 | 0 |
| Basic | 323 | 0 | 0 | 0 | 3 | 0 | 0 |
| Clocks | 144 | 0 | 0 | 2 | 3 | 0 | 0 |
| Construction | 6535 | 0 | 2 | 241 | 80 | 10 | 0 |
| Effective | 2840 | 0 | 0 | 191 | 37 | 0 | 0 |
| Expspace | 16514 | 21 | 15 | 297 | 302 | 20 | 0 |
| Family | 215 | 0 | 0 | 10 | 11 | 0 | 0 |
| Game | 628 | 0 | 0 | 8 | 3 | 1 | 0 |
| General | 119 | 0 | 0 | 1 | 0 | 0 | 0 |
| Instances | 85 | 0 | 0 | 0 | 2 | 0 | 0 |
| KeyCodes | 258 | 0 | 0 | 5 | 4 | 0 | 0 |
| KeyEval | 2385 | 0 | 0 | 47 | 54 | 12 | 0 |
| KeyInstances | 739 | 0 | 1 | 37 | 55 | 2 | 0 |
| KeyRoutines | 1328 | 0 | 0 | 53 | 17 | 4 | 0 |
| KeySlots | 191 | 0 | 0 | 10 | 3 | 0 | 0 |
| Machines | 255 | 0 | 0 | 5 | 0 | 0 | 0 |
| PathDataSA | 273 | 0 | 0 | 3 | 5 | 0 | 4 |
| PathDataSATree | 151 | 0 | 0 | 0 | 0 | 0 | 2 |
| PathGame | 905 | 0 | 0 | 29 | 10 | 0 | 0 |
| PrefixForm | 115 | 0 | 0 | 1 | 0 | 1 | 0 |
| Pspace | 728 | 0 | 1 | 0 | 4 | 0 | 0 |
| SAExp | 104 | 0 | 0 | 0 | 0 | 0 | 0 |
| SAExpE | 584 | 0 | 0 | 10 | 4 | 0 | 1 |
| StackTime | 872 | 0 | 0 | 4 | 6 | 1 | 0 |
| StepBudget | 736 | 0 | 0 | 24 | 4 | 0 | 0 |
| StmtTime | 2045 | 0 | 0 | 71 | 2 | 2 | 0 |
| SubAdaptive | 1595 | 0 | 0 | 57 | 17 | 0 | 4 |
| SwapAsk | 130 | 0 | 0 | 6 | 4 | 0 | 0 |
| TT | 391 | 0 | 0 | 19 | 7 | 0 | 0 |
| **total** | 41434 | 21 | 19 | 1131 of 2604 | 641 | 53 | 11 |

7 files have more than 1000 lines (Construction, Effective, Expspace, KeyEval, KeyRoutines,
StmtTime, SubAdaptive). Unlisted cut findings by kind: RFL-BINDER 39, LONG-STATEMENT 5,
THEOREM-HYP 4, WRAPPER 4, SINGLE-USE-TAIL 1.

## Phase 0.5: splitting the oversized files (2026-10-20)

The seven files over 1000 lines were split along their existing topical sections into
directories of leaf modules. The old module stays as a hub that imports its leaves and keeps the
final results, so every existing `import KolmogorovMathlib.RandomStrings.X` still works.
`KolmogorovMathlib.lean` is unchanged, since the leaves are reached through the hubs. Each leaf
has the standard header and a `/-! -/` module docstring, and it imports only the earlier leaves
that it uses (a DAG, not a chain). No declaration statement changed:
`check_headers.py --rev 7fb6be1 --by-name` reports 0 problems.

* `Expspace` (16514 lines) became the hub `Expspace` (89 lines: `exists_gameProg`,
  `gameValue_mem_EXPSPACE`) and 28 leaves. In dependency order: `StackProg`, `OneTapeSim`,
  `Stmt`, `Routines`, `CodedLists`, `SimOTM`, `RecSim`, `QEnumParts`, `QEnum`,
  `Evaluator`, then the depth-first search `DFSGame`, `DFSMachine`, `DFSRoot`,
  `DFSFrames`, `DFSTests`, `DFSMode1`, `DFSMode2`, `DFSMode3Tests`, `DFSMode3Reject`,
  `DFSMode3Accept`, `DFSMode4`, `DFSEnter`, `DFSInit`, `DFSAssembly`, then
  `GameStmt`, `Cost`, `Prep`, `Hardwire`. The DFS block (about 7.5k lines) has no
  `####` sub-headings of its own. It was cut at its sub-contract boundaries instead: the
  bit-vector game, the machine `mstep`, the root run, frame coding, the `costV`/`isSub`
  tests, one module per mode routine (mode 3 in three parts, at the two `/-!` notes that
  already split its commit phase), enter/post, initialisation, and assembly.
* `Construction` (6535 lines) became the hub (137 lines: `limit_game_foils`, `Flim_foils`,
  `exists_built`) and the leaves `Stages`, `Mirror`, `MirrorReply`, `MirrorPrimrec`,
  `MirrorBookkeeping`, `Claim3`, `Flips`, `Evolution`, `LiveGames`, `LiveInv`,
  `Claim2Stage`, `Changes`.
* `Effective` (2840 lines) became the hub (670 lines: deciding `SafeYes`/`SafeNo` at
  arbitrary finite states) and the leaves `Codes`, `Configs`, `GameValues`.
* Smaller files: each has a real seam, so each was split rather than allow-listed.
  * `KeyEval` (2385 lines): the hub (720 lines) has the budget test and the driver logic. Its
    leaves are `Table` (the table and its loops over bit strings) and `Plumbing`.
  * `StmtTime` (2045 lines; its sections are `####` headings): the hub (431 lines) has the
    polynomial time of the simulation and of the query enumeration. Its leaves are `ExecT`
    (the step-count framework) and `Budgets` (the generic pop-loop budgets).
  * `SubAdaptive` (1595 lines): the hub (785 lines) has the decision procedures and the
    boundary-free notion. Its leaf `Basic` holds the definitions, stage 1 and counting.
  * `KeyRoutines` (1328 lines): the hub (891 lines) has the inclusion, conditional-inclusion
    and duplicate-freeness tests. Its leaf `Decoder` holds the decoder and the run at a key.

Now no file in `RandomStrings` has more than 1000 lines (the largest is
`Expspace/Routines`, 969 lines). No `size_allow.tsv` row was needed and none was added.

Seven `private` declarations of `Expspace` are used by a leaf other than their own, so they
became public: `DFS.space_update_int` (it got a new docstring), `DFS.binVal_numBits_of_lt`,
`DFS.addBits_numBits`, `DFS.exists_costVStmt_except29`, `DFS.exists_costVStmt_except23`,
`DFS.exec_mode3Commit_notSub`, `DFS.exec_mode3Commit_overBudget`. The other 84 stay private.

State: `lake build` succeeds (10375 jobs) with 948 warnings, all in `RandomStrings`, the same
as in phase 0: longLine 641, show 229, flexible 41, maxHeartbeats-comment 21, emptyLine 13,
multiGoal 2, openClassical 1. The axioms of the three main theorems are unchanged: `propext`,
`Classical.choice`, `Quot.sound`. These gates pass: `module_docs --check`,
`import_hygiene`, `check_dup_decls` (24 clashes, as before), the size gate of `audit.sh` and
`check_headers --by-name` (0 problems).

### Dirt inventory after phase 0.5

Same columns as above.

| file | lines | overrides | proofs >150 | undocumented | lines >100 | cut | prose |
|---|---|---|---|---|---|---|---|
| Apriori | 246 | 0 | 0 | 0 | 4 | 0 | 0 |
| Basic | 323 | 0 | 0 | 0 | 3 | 0 | 0 |
| Clocks | 144 | 0 | 0 | 2 | 3 | 0 | 0 |
| Construction/Changes | 512 | 0 | 1 | 4 | 1 | 0 | 0 |
| Construction/Claim2Stage | 514 | 0 | 0 | 23 | 8 | 0 | 0 |
| Construction/Claim3 | 267 | 0 | 0 | 8 | 6 | 0 | 0 |
| Construction/Evolution | 186 | 0 | 0 | 7 | 7 | 0 | 0 |
| Construction/Flips | 910 | 0 | 0 | 36 | 8 | 8 | 0 |
| Construction/LiveGames | 473 | 0 | 0 | 19 | 5 | 1 | 0 |
| Construction/LiveInv | 610 | 0 | 0 | 26 | 6 | 0 | 0 |
| Construction/Mirror | 854 | 0 | 0 | 38 | 12 | 0 | 0 |
| Construction/MirrorBookkeeping | 514 | 0 | 1 | 15 | 5 | 0 | 0 |
| Construction/MirrorPrimrec | 741 | 0 | 0 | 34 | 10 | 0 | 0 |
| Construction/MirrorReply | 654 | 0 | 0 | 24 | 3 | 1 | 0 |
| Construction/Stages | 449 | 0 | 0 | 7 | 9 | 0 | 0 |
| Construction | 137 | 0 | 0 | 0 | 0 | 0 | 0 |
| Effective/Codes | 423 | 0 | 0 | 32 | 1 | 0 | 0 |
| Effective/Configs | 887 | 0 | 0 | 58 | 13 | 0 | 0 |
| Effective/GameValues | 927 | 0 | 0 | 62 | 13 | 0 | 0 |
| Effective | 670 | 0 | 0 | 39 | 10 | 0 | 0 |
| Expspace/CodedLists | 336 | 0 | 0 | 7 | 3 | 0 | 0 |
| Expspace/Cost | 898 | 1 | 0 | 15 | 54 | 1 | 0 |
| Expspace/DFSAssembly | 674 | 0 | 2 | 15 | 6 | 2 | 0 |
| Expspace/DFSEnter | 711 | 2 | 0 | 0 | 62 | 1 | 0 |
| Expspace/DFSFrames | 437 | 1 | 0 | 0 | 18 | 0 | 0 |
| Expspace/DFSGame | 315 | 0 | 0 | 6 | 9 | 0 | 0 |
| Expspace/DFSInit | 550 | 3 | 1 | 0 | 2 | 3 | 0 |
| Expspace/DFSMachine | 750 | 0 | 2 | 0 | 16 | 2 | 0 |
| Expspace/DFSMode1 | 882 | 2 | 3 | 0 | 4 | 0 | 0 |
| Expspace/DFSMode2 | 315 | 1 | 0 | 0 | 0 | 0 | 0 |
| Expspace/DFSMode3Accept | 773 | 3 | 2 | 0 | 0 | 2 | 0 |
| Expspace/DFSMode3Reject | 331 | 2 | 0 | 0 | 0 | 0 | 0 |
| Expspace/DFSMode3Tests | 483 | 2 | 1 | 0 | 1 | 0 | 0 |
| Expspace/DFSMode4 | 322 | 1 | 0 | 0 | 0 | 0 | 0 |
| Expspace/DFSRoot | 438 | 0 | 1 | 1 | 42 | 0 | 0 |
| Expspace/DFSTests | 887 | 0 | 1 | 0 | 14 | 0 | 0 |
| Expspace/Evaluator | 378 | 0 | 0 | 17 | 13 | 0 | 0 |
| Expspace/GameStmt | 888 | 1 | 1 | 19 | 9 | 0 | 0 |
| Expspace/Hardwire | 422 | 0 | 0 | 7 | 8 | 0 | 0 |
| Expspace/OneTapeSim | 876 | 0 | 0 | 45 | 6 | 1 | 0 |
| Expspace/Prep | 314 | 0 | 1 | 2 | 1 | 0 | 0 |
| Expspace/QEnum | 890 | 2 | 0 | 28 | 11 | 2 | 0 |
| Expspace/QEnumParts | 732 | 0 | 0 | 22 | 1 | 4 | 0 |
| Expspace/RecSim | 610 | 0 | 0 | 14 | 4 | 0 | 0 |
| Expspace/Routines | 969 | 0 | 0 | 28 | 2 | 0 | 0 |
| Expspace/SimOTM | 893 | 0 | 0 | 41 | 13 | 2 | 0 |
| Expspace/StackProg | 391 | 0 | 0 | 11 | 0 | 0 | 0 |
| Expspace/Stmt | 605 | 0 | 0 | 19 | 3 | 0 | 0 |
| Expspace | 89 | 0 | 0 | 0 | 0 | 0 | 0 |
| Family | 215 | 0 | 0 | 10 | 11 | 0 | 0 |
| Game | 628 | 0 | 0 | 8 | 3 | 1 | 0 |
| General | 119 | 0 | 0 | 1 | 0 | 0 | 0 |
| Instances | 85 | 0 | 0 | 0 | 2 | 0 | 0 |
| KeyCodes | 258 | 0 | 0 | 5 | 4 | 0 | 0 |
| KeyEval/Plumbing | 821 | 0 | 0 | 17 | 5 | 2 | 0 |
| KeyEval/Table | 897 | 0 | 0 | 23 | 11 | 6 | 0 |
| KeyEval | 720 | 0 | 0 | 7 | 38 | 4 | 0 |
| KeyInstances | 739 | 0 | 1 | 37 | 55 | 2 | 0 |
| KeyRoutines/Decoder | 468 | 0 | 0 | 29 | 6 | 0 | 0 |
| KeyRoutines | 891 | 0 | 0 | 24 | 11 | 4 | 0 |
| KeySlots | 191 | 0 | 0 | 10 | 3 | 0 | 0 |
| Machines | 255 | 0 | 0 | 5 | 0 | 0 | 0 |
| PathDataSA | 273 | 0 | 0 | 3 | 5 | 0 | 4 |
| PathDataSATree | 151 | 0 | 0 | 0 | 0 | 0 | 2 |
| PathGame | 905 | 0 | 0 | 29 | 10 | 0 | 0 |
| PrefixForm | 115 | 0 | 0 | 1 | 0 | 1 | 0 |
| Pspace | 728 | 0 | 1 | 0 | 4 | 0 | 0 |
| SAExp | 104 | 0 | 0 | 0 | 0 | 0 | 0 |
| SAExpE | 584 | 0 | 0 | 10 | 4 | 0 | 1 |
| StackTime | 872 | 0 | 0 | 4 | 6 | 1 | 0 |
| StepBudget | 736 | 0 | 0 | 24 | 4 | 0 | 0 |
| StmtTime/Budgets | 882 | 0 | 0 | 33 | 0 | 0 | 0 |
| StmtTime/ExecT | 779 | 0 | 0 | 16 | 1 | 2 | 0 |
| StmtTime | 431 | 0 | 0 | 22 | 1 | 0 | 0 |
| SubAdaptive/Basic | 834 | 0 | 0 | 27 | 10 | 0 | 4 |
| SubAdaptive | 785 | 0 | 0 | 30 | 7 | 0 | 0 |
| SwapAsk | 130 | 0 | 0 | 6 | 4 | 0 | 0 |
| TT | 391 | 0 | 0 | 19 | 7 | 0 | 0 |
| **total** | 42587 | 21 | 19 | 1131 | 641 | 53 | 11 |
