/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Complexity.Applications.MultiheadAutomata.AutomatonDefs
import KolmogorovMathlib.Complexity.Applications.MultiheadAutomata.HeadHierarchy

/-!
# Finite automata with several heads (SUV Section 8.3, pp. 236-238)

The model follows p. 236 literally.

* A `k`-head automaton has finitely many states and `k` one-way read-only heads.  Initially all
  heads observe the leftmost character.
* The input is followed by an end marker, which is what `observe` returns as `none`.
* At each step the behaviour is determined by the state and the `k` observed symbols: the automaton
  changes the state and instructs some heads to move right.  A head that sees the marker does not
  move, and at least one head moves as long as not all heads see the marker (`moves_nonempty`).
* The automaton terminates when all heads observe the marker, and it accepts when it is then in an
  accepting state.

A language is `IsRecognizedBy k L` when some `k`-head automaton accepts exactly the words of `L`.

The hard part of Theorem 154 is `not_isRecognizedBy_palindromeBlocks`.  The book proves it with
incompressible blocks; this statement does not mention complexity, and its proof may also be
translated into counting.
-/
