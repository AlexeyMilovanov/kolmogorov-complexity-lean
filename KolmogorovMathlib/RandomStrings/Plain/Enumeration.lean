/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Enumeration.Schedule
import KolmogorovMathlib.RandomStrings.Plain.Enumeration.CanonicalSpec

/-!
# One synchronized enumeration of plain and prefix computations

This aggregator imports `Enumeration/Schedule.lean`, which defines the canonical schedule of
the halting events of the plain machine `V` and the observations of the prefix machine `D`,
and `Enumeration/CanonicalSpec.lean`, which proves that the schedule is correct: every
halting computation is emitted exactly once, at a determined tick and position. The
fighter construction (`Construction.Effective`) reads this schedule tick by tick, and the
markers of `Plain.Markers` are defined from its emission times.

Tick zero has empty tables. At tick `t+1`, decode input indices below `t+1` and
run each interpreter with `Code.evaln` fuel `t+1`. Remove repeated inputs, append
new V halts to a FIFO queue in increasing input-code order, and emit at most its
head. Append new D observations on this same tick. Each tick performs explicitly
bounded work; these are logical ticks, not OTM running-time bounds.

The state consists entirely of lists of products of encodable data. V history records
`(tick, zero-based event position, program, output)`. Distinct-output tables are derived
only from emitted events, including when several programs produce the same output.
No classical choice or machine-level halting test occurs in the finite computations.
-/
