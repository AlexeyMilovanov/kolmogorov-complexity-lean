# Lean 4.28 Strict Polishing Plan

## Objective

Finish the Lean 4.28 branch as a genuinely strict Mathlib-style development.
The mathematical API is complete and frozen. Only proof terms, imports,
private dead code, comments, formatting, and audit infrastructure may improve.

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
inventory and assigns exclusive dependency-aware file batches to the next four
ordinary iterations.

Ordinary iterations use:

`Gemini -> Codex -> Opus -> Codex -> Aristotle`

Every touched file must pass direct elaboration with `flexible`, `longLine`,
`multiGoal`, and `openClassical` enabled. The final Codex runs the project
audit; Aristotle receives only exact remaining proof/style leaves. Rejected
batches stay in the isolated worktree and never dirty the accepted branch.

## Style Policy

Occurrences of `simp_all`, `aesop`, `grind`, and `nlinarith` are candidates for
review, not automatic defects. Replace them only when a shorter, clearer, and
no-slower structural proof is verified. Prefer explicit rewrites, focused
`simp only`, named intermediate facts, stable case splits, narrow imports, and
standard Mathlib naming/layout. Do not create churn merely to reduce line count.
