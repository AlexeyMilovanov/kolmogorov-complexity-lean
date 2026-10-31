/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Markers.LastProgram
import KolmogorovMathlib.RandomStrings.Plain.Markers.StagePrefix

/-!
# Last-program markers and tails of the emitted enumeration

This aggregator imports `Markers/LastProgram.lean` (the marker and its basic properties) and
`Markers/StagePrefix.lean` (the stage prefix complexity and the post-marker tail). The marker
singles out, for each scale `n`, the last short program emitted by the canonical enumeration
of `Plain.Enumeration`. It is incompressible, the enumeration is final on short outputs at
the marker tick, and the number of simple strings still to come afterwards is exponentially
small (`exponential_tail_budget`). The fighter construction starts the phase of a level at
its marker, and the tail budget is one of the constants chosen in `Plain.Main`.

`lastProgram B n` is a program, not an output. Its timestamp is the maximum emission
tick of a halting program of length at most `n`. Below the first nonempty scale the
timestamp and event position default to zero and the program defaults to `[]`.
The marker is classical; algorithms consume a validated `Candidate` instead.

Every asymptotic statement explicitly quantifies a threshold at least 32. A common
threshold for the fixed-machine marker assertions is exported at the end; it is chosen
before any future padding parameter. Strict half-length bounds are written `2*l < n`
to avoid rounding an odd natural `n` down before the comparison.
-/
