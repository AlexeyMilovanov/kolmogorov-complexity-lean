# Lean 4.28 Strict Polishing Plan

## Objective

Finish the Lean 4.28 branch as a genuinely strict Mathlib-style development.
The mathematical API is complete and frozen. Only proof terms, imports,
private dead code, comments, formatting, and audit infrastructure may improve.

## 10x-100x Scalability Objective

This branch is the architectural baseline for a library expected to grow by at
least 10x and plausibly 100x. Zero warnings and clean local proofs are necessary
but not sufficient. Strategic rounds must also measure and improve:

- import-graph fan-out and subsystem boundaries;
- oversized or slow-to-elaborate modules;
- the cost of validating a local change;
- the separation between fast affected checks and the final full audit;
- proof and definition placement that minimizes unnecessary downstream rebuilds.

Do not split files, add umbrella modules, or introduce build tooling merely for
appearance. Every architectural change needs a measured bottleneck, a targeted
acceptance test, and a rollback criterion. The root audit remains authoritative.

## Mandatory Final Gates

1. Delete all project-level `linter.* = false` settings from `lakefile.toml`.
2. Pass `scripts/strict_lint_sweep.sh` with empty output over every Lean file.
3. Pass the root target and the three standalone-module builds with no warning.
4. Keep zero `sorry`, forbidden escape hatches, heartbeat/recursion overrides,
   broad imports, source-level linter suppressions, and measurement scaffolding.
5. Preserve theorem statements, assumptions, public names, executable
   definition bodies, encodings, enumeration order, and quantitative constants.

## Iteration Protocol

Iterations 1, 6, 11, ... are read-only strategy rounds for Gemini, Codex,
Opus, Codex, and Aristotle. Each strategy round measures the current warning
inventory, import and reverse-dependency graph, module sizes, elaboration/build
hotspots, and local-change validation cost. It then assigns exclusive
dependency-aware proof, architecture, or build-infrastructure batches to the
next four ordinary iterations.

Ordinary iterations use:

`Gemini -> Codex -> Opus -> Codex -> Aristotle`

Every touched file must pass direct elaboration with `flexible`, `longLine`,
`multiGoal`, and `openClassical` enabled. The final Codex runs the project
audit; Aristotle receives only exact remaining proof/style leaves. Rejected
batches stay in the isolated worktree and never dirty the accepted branch.

Ordinary iterations may add a sound affected-build layer for fast feedback, but
must continue to run the complete audit before acceptance. Import cleanup,
module extraction, and umbrella-module changes are accepted only when measured
fan-out or elaboration cost improves without API drift.

## Authoritative Recovery Baseline (2026-07-21)

Iteration 5 integrated an unchanged Aristotle submission copy over files that
had been polished in earlier iterations. The accepted pre-iteration-5 versions
of 29 non-Restricted files were recovered from the merge-gate backup, while the
newer improvements in 12 Restricted files were retained. The runner now kills
complete agent process groups on timeout, integrates only Aristotle's actual
changes relative to the submitted package, and checkpoints accepted root state
as the worktree's new Git `HEAD` after every merge decision.

The recovered tree passed the full 2,843-job audit and an uncached direct sweep
of all 118 Lean files. This is the authoritative starting point for iteration 7:

- elaboration errors: 0;
- strict linter warnings: 1,667 total;
- original iteration-1 baseline: 2,744 total;
- `sorry`, forbidden constructs, resource overrides, and ordinary build warnings: 0.

Later agents must not use the stale 2,420-warning measurement from strategy
iteration 6 as the current total. They should remeasure their owned files before
editing and preserve every recovered change outside the current file batch.

## Style Policy

Occurrences of `simp_all`, `aesop`, `grind`, and `nlinarith` are candidates for
review, not automatic defects. Replace them only when a shorter, clearer, and
no-slower structural proof is verified. Prefer explicit rewrites, focused
`simp only`, named intermediate facts, stable case splits, narrow imports, and
standard Mathlib naming/layout. Do not create churn merely to reduce line count.
At 10x-100x scale, prefer stable module boundaries and cheap local validation
over cosmetic proof shortening.
