# Lean 4.28 to 4.31 Migration

## Objective

Move every theorem and definition from the final Lean 4.28 development into
the existing Lean 4.31 project. The Lean 4.31 tree is authoritative for files
that already exist there; the 4.28 snapshot is read-only reference material.

The order of completion is strict:

1. complete result coverage;
2. error-free `lake build KolmogorovMathlib`;
3. warning-free and debt-free cleanup;
4. measured Mathlib-style polishing in Lean 4.31.

## Initial Inventory

The final 4.28 tree has 117 Lean files and the initial 4.31 tree has 78. The
following 39 files are absent by path from 4.31:

- `KolmogorovMathlib/Encoding/Tuples.lean`
- `KolmogorovMathlib/Encoding/TuplesComplexity.lean`
- `KolmogorovMathlib/Foundation/PrimrecExtras.lean`
- `KolmogorovMathlib/Foundation/EnumerationComplexity.lean`
- `KolmogorovMathlib/Interface/StandardMachine.lean`
- all 34 files under `KolmogorovMathlib/Restricted/`

All 78 shared Lean files differ textually between versions. They must not be
replaced wholesale. Existing 4.31 APIs and proofs are preserved, with only
small compatibility additions when a migrated result genuinely requires one.

## Dependency Order

1. Port and build the five support files above in import order. Prefer existing
   4.31 encodings and computability APIs over recreating their 4.28 forms.
2. Port the restricted-family foundation: `Family`, `BasicProfile`, selection,
   enumeration, cover-search, greedy-cover, improvement, gap, and deficiency
   modules.
3. Port examples in dependency order: cylinders, masks, Hamming balls, Hamming
   gap, and Hamming curve.
4. Port `FamilyCurve/` bottom-up from its import graph, then the aggregate
   `FamilyCurve.lean` and root imports.
5. Compare public declaration coverage against the source snapshot, run the
   full audit, and only then begin 4.31-specific polishing.

## Acceptance Gates

- No `sorry`, `sorryAx`, forbidden escape hatch, theorem weakening, or hidden
  source result loss.
- Every accepted ordinary iteration passes `scripts/audit.sh`; rejected batches
  remain only in the persistent worktree for the next agents to repair.
- No new warning, `set_option maxHeartbeats`, broad `import Mathlib`, linter
  suppression, test file, build log, or measurement directive is accepted.
- Public statement changes required by Lean 4.31 must be documented and shown
  equivalent to the 4.28 result.
- Once every source-only file is represented and the full build is clean,
  strategy agents switch the ordinary iterations to warning cleanup and
  measured proof polishing.
