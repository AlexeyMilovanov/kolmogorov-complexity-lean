# Migration plan: final Lean 4.28 algstat state to Lean 4.31

Status: active migration plan.
Updated: `2026-07-09T05:41:20Z`.

Source 28 directory: `/home/lesha/kolmogorov-complexity-lean-28`
Source 28 commit: `e5bba7bbe59acd10df333643e28d778380e03319` (`e5bba7b`)
Target 31 worktree: `/home/lesha/kolmogorov-complexity-lean-31-port-current-28`
Target 31 baseline before this plan: `f4a0ca5e1cff1b71e85fd0adaf62556a0f6c319f` (`f4a0ca5`)
Target branch: `local/port-current-28-to-31` (local migration branch; do not push unless explicitly asked)

## Verified 31 Baseline

The target 31 worktree was checked before starting this migration:

- `lake build KolmogorovMathlib`: green
- build warnings: `0`
- build errors: `0`
- Lean source scan: `sorry = 0`, `admit = 0`, `axiom = 0`, `unsafe = 0`
- `set_option maxHeartbeats`: `0`
- broad imports `import Mathlib` / `import Mathlib.Tactic`: `0`
- linter suppressions: `0`
- root temporary logs/reports/patch artifacts: removed before launch

## Difference Summary

Comparing final 28 against the local 31 migration worktree:

- Lean files in 28: `79`
- Lean files in 31: `74`
- common Lean files: `74`
- literally identical common Lean files: `1`
- differing common Lean files: `73`
- Lean files only in 28: `5`
- Lean files only in 31: `0`

The large common-file diff is expected: the 31 tree already contains Lean/Mathlib 4.31 adaptations and polishing. Therefore the migration must not copy the whole 28 tree over 31.

## Core Principle

Use the current 31 tree as the base. Port the new mathematical content from final 28 into the already-adapted 31 code. Preserve 31-specific repairs, imports, style cleanup, and proof restructuring unless a specific 28 theorem/API delta is required.

Forbidden migration pattern: wholesale replacement of common 31 files with 28 versions.

Allowed migration pattern: small, reviewed API deltas copied or rederived from 28 into 31-adapted files, followed by targeted builds.

## Files Structurally Missing From 31

Port these five Section 3 files in dependency order:

1. `KolmogorovMathlib/AlgorithmicStatistics/TwoPart/GreedyWindow.lean`
2. `KolmogorovMathlib/AlgorithmicStatistics/TwoPart/Profile.lean`
3. `KolmogorovMathlib/AlgorithmicStatistics/TwoPart/CurveRealization.lean`
4. `KolmogorovMathlib/AlgorithmicStatistics/TwoPart/ProfileRealization.lean`
5. `KolmogorovMathlib/AlgorithmicStatistics/TwoPart/PaperTheorems.lean`

Update `KolmogorovMathlib.lean` only incrementally, after the imported module or slice is buildable enough to expose useful downstream errors.

## Likely Shared API Delta Files

Before or while adding the missing files, compare 28 and 31 versions of these shared dependencies and port only the needed theorem/API deltas:

- `KolmogorovMathlib/AlgorithmicStatistics/TwoPart/SlackArith.lean`
- `KolmogorovMathlib/AlgorithmicStatistics/TwoPart/DescriptionSnapshot.lean`
- `KolmogorovMathlib/AlgorithmicStatistics/TwoPart/GapCounting.lean`
- `KolmogorovMathlib/AlgorithmicStatistics/TwoPart/Deficiencies.lean`
- `KolmogorovMathlib/AlgorithmicStatistics/Selector.lean`
- `KolmogorovMathlib/AlgorithmicStatistics/NonStochastic.lean`
- `KolmogorovMathlib/Prefix/ConditionalSymmetry.lean`
- if required: `Prefix/Properties.lean`, `Prefix/TotalCountingBound.lean`, `Complexity/NatComplexity.lean`, `Complexity/Incompressibility.lean`

Do not replace these files wholesale unless Codex explicitly verifies that the 31-specific adaptation is preserved.

## Build Strategy

Prefer targeted checks while editing:

- `lake build KolmogorovMathlib.AlgorithmicStatistics.TwoPart.GreedyWindow`
- `lake build KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Profile`
- `lake build KolmogorovMathlib.AlgorithmicStatistics.TwoPart.CurveRealization`
- `lake build KolmogorovMathlib.AlgorithmicStatistics.TwoPart.ProfileRealization`
- `lake build KolmogorovMathlib.AlgorithmicStatistics.TwoPart.PaperTheorems`

Run `lake build KolmogorovMathlib` as the final gate for an accepted green step. Do not run `lake clean` or `lake update`.

## Acceptance Criteria

A final accepted 31 migration state must have:

- all final 28 mathematical results present in 31;
- `lake build KolmogorovMathlib` green;
- warnings `0`;
- no `sorry`, `admit`, `axiom`, `unsafe`, `implemented_by`, `native_decide`, `sorryAx`, or `opaque`;
- no `set_option maxHeartbeats`;
- no broad `import Mathlib` / `import Mathlib.Tactic`;
- no temporary logs, scratch files, generated patches, or agent reports in the repository tree.

## Automation Policy

Run an indefinite `Gemini -> Codex` loop.

- Iterations `1, 6, 11, ...` are strategic: Gemini proposes/refines the next four work slices, Codex reviews and writes the active plan.
- Other iterations are implementation iterations: Gemini edits one coherent slice, Codex reviews, repairs, runs checks, and writes `decision.json`.
- Codex may choose `continue_wip` when the full build is still broken but the diff is coherent and moves the migration frontier forward.
- Codex must choose `reject` for hallucinated imports/lemmas, theorem weakening, broad churn, scratch pollution, or any forbidden construct.
- A green accepted step is committed locally by the runner. Broken but coherent WIP may be kept for the next iteration; rejected work is stashed with a diff saved in the iteration directory.
