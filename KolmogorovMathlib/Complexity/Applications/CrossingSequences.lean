/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Complexity.Applications.CrossingSequences.CrossingSequenceBound
import KolmogorovMathlib.Complexity.Applications.CrossingSequences.DuplicationLowerBound

/-!
# Moving information along the tape (SUV Section 8.2, pp. 233-235)

The zones of Theorem 152 on a tape of `TuringMachine`: the left zone `L` is the cells `≤ a`,
arbitrary; the buffer is the `b` cells `a + 1, …, a + b`; the right zone `R` is the cells after
`a + b`.  Initially the buffer and `R` are blank.

The head starts in the left zone.  The book does not say this in the statement, but it uses it in
the proof ("otherwise `R(t)` is empty since the head never visited `R`"), and the statement is false
without it: a head starting at a distance `d` to the right of the buffer can only write at that
distance, and the content of `R`, with its `d` leading blanks, has complexity about `C(d)`, which is
unrelated to `t`.

The content `R(t)` is a word over the tape alphabet.  Its complexity is that of its binary code
`wordBits` (Section 7.3), the library's fixed encoding of words over a finite alphabet.
-/
