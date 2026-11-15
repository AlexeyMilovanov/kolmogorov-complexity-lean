/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Complexity.Applications.MoserTardos.Algorithm
import KolmogorovMathlib.Complexity.Applications.MoserTardos.SuccessProbability

/-!
# The effective proof of the local lemma (SUV Section 8.5.6, pp. 251-255)

A CNF with `n` variables and `N` clauses of exactly `m` variables each.  A clause forbids one
combination of values of its variables.  Two clauses are *neighbours* if they share a variable, so
that a clause is its own neighbour: this is the convention that the book's proof needs (p. 253).

**The algorithm.**  The book's recursive procedure

```
for all clauses d: if d is false: Fix(d)
Fix(d): resample all variables of d using fresh random bits;
        for all clauses d' that are neighbours of d: if d' is false: Fix(d')
```

is an explicit machine with a call stack.  One step of `step` is one clause test, together with the
resampling if the clause is false, or a return from a call.  So the number of steps measures the
time up to a factor polynomial in `n + N`, as a step handles at most `m ≤ n` variables, and the
convention for "time" is this count.

**Probability.**  The random bits are given in advance, as the book says on p. 253.  The probability
space is the set of `L`-bit tapes, with `L` large enough for the number of calls considered, so a
probability is an exact count of tapes.  `tapeOf` reads a finite tape as a function; the bits beyond
its end are `false`, and they are never read during the calls that the bound `L` allows.
-/
