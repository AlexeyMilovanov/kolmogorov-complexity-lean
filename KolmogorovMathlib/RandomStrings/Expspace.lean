/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Expspace.StackProg
import KolmogorovMathlib.RandomStrings.Expspace.OneTapeSim
import KolmogorovMathlib.RandomStrings.Expspace.Stmt
import KolmogorovMathlib.RandomStrings.Expspace.Routines
import KolmogorovMathlib.RandomStrings.Expspace.CodedLists
import KolmogorovMathlib.RandomStrings.Expspace.SimOTM
import KolmogorovMathlib.RandomStrings.Expspace.RecSim
import KolmogorovMathlib.RandomStrings.Expspace.QEnumParts
import KolmogorovMathlib.RandomStrings.Expspace.QEnum
import KolmogorovMathlib.RandomStrings.Expspace.Evaluator
import KolmogorovMathlib.RandomStrings.Expspace.DFSGame
import KolmogorovMathlib.RandomStrings.Expspace.DFSMachine
import KolmogorovMathlib.RandomStrings.Expspace.DFSRoot
import KolmogorovMathlib.RandomStrings.Expspace.DFSFrames
import KolmogorovMathlib.RandomStrings.Expspace.DFSTests
import KolmogorovMathlib.RandomStrings.Expspace.DFSMode1
import KolmogorovMathlib.RandomStrings.Expspace.DFSMode2
import KolmogorovMathlib.RandomStrings.Expspace.DFSMode3Tests
import KolmogorovMathlib.RandomStrings.Expspace.DFSMode3Reject
import KolmogorovMathlib.RandomStrings.Expspace.DFSMode3Accept
import KolmogorovMathlib.RandomStrings.Expspace.DFSMode4
import KolmogorovMathlib.RandomStrings.Expspace.DFSEnter
import KolmogorovMathlib.RandomStrings.Expspace.DFSInit
import KolmogorovMathlib.RandomStrings.Expspace.DFSAssembly
import KolmogorovMathlib.RandomStrings.Expspace.GameStmt
import KolmogorovMathlib.RandomStrings.Expspace.Cost
import KolmogorovMathlib.RandomStrings.Expspace.Prep
import KolmogorovMathlib.RandomStrings.Expspace.Hardwire

/-!
# Game values are computable in exponential space (Claim 4 of the paper, P-case)

For a fixed clocked machine `(c, e)` and finitely much hardwired information (the current
values `h` differ from the initial values `2|z| + 6` only on a finite table; the sets `X_{e'}`
of the higher-priority requirements are finite), the map `x ↦ val (G_{e,x})` is computable in
space `2 ^ poly(|x|)`: the query set has at most `2 ^ clock` elements of length `≤ clock`, a game
state is described by `2^{O(clock)}` bits, and the alternating evaluation of `YesWins` with turn
budget `2|X| + 2` uses a stack of that depth.

The development lives in the modules `KolmogorovMathlib.RandomStrings.Expspace.*`, in dependency
order: stack programs and their one-tape simulation (`StackProg`, `OneTapeSim`), the structured
layer (`Stmt`) and its routines (`Routines`, `CodedLists`), the simulation of the clocked machine
(`SimOTM`, `RecSim`), the enumeration of the query set (`QEnumParts`, `QEnum`), the game evaluator
(`Evaluator`), the depth-first search (`DFSGame` … `DFSAssembly`), the game statement and the cost
procedure (`GameStmt`, `Cost`, `Prep`), and hardwiring (`Hardwire`).  This module states the final
results `exists_gameProg` and `gameValue_mem_EXPSPACE`.
-/

namespace Kolmogorov.RandomStrings

/-- The concrete game-evaluation program: on input `x` it enumerates the query set of the clocked
machine, computes the flip costs and the budget as fixed-point numbers at the precision `gameN`,
and decides `SafeYes` by depth-first search over the positions `S ⊆ X` with the two scores
(`exists_evalStmt`); it runs in space `2 ^ poly(|x|)`.  Its output is `val` by
`gameValB_gameOf` (the finite recursion `safeYesB` computes `SafeYes` / `YesWinsInit`). -/
theorem exists_gameProg (c : OTMCode) (e : ℕ) (T : Table) (m : ℕ) (Y : Finset BitString) :
    ∃ (P : Prog) (p : Polynomial ℕ), P.SpaceBounded p ∧
      ∀ x : BitString, x ∈ P.Lang ↔ val (gameOf c e x T.fn ((2 : ℝ)⁻¹ ^ m)
        (querySet c.toOTM x (clock e x.length) \ Y)) = true := by
  obtain ⟨k, s, out, C, hs⟩ := exists_evalStmt c e T m Y
  refine Stmt.exists_prog s out
    (Polynomial.C C * (Polynomial.X ^ e + Polynomial.C e + Polynomial.X + 1)) _ fun x => ?_
  obtain ⟨σ', hσ', hout⟩ := hs x
  refine ⟨σ', ?_, ?_⟩
  · have hp : (Polynomial.C C * (Polynomial.X ^ e + Polynomial.C e + Polynomial.X + 1)).eval
        x.length = C * (clock e x.length + x.length + 1) := by
      simp [clock]
    rw [hp]; exact hσ'
  · rw [hout, gameValB_gameOf]

/-- Claim 4, machine part: for every clocked machine, hardwired table, budget `2^{-m}`, and
finite set `Y` of strings to exclude from the game, the set of inputs on which the YES player
wins is in `EXPSPACE`. -/
theorem gameValue_mem_EXPSPACE (c : OTMCode) (e : ℕ) (T : Table) (m : ℕ) (Y : Finset BitString) :
    {x : BitString | val (gameOf c e x T.fn ((2 : ℝ)⁻¹ ^ m)
      (querySet c.toOTM x (clock e x.length) \ Y)) = true} ∈ EXPSPACE := by
  obtain ⟨P, p, hP, hacc⟩ := exists_gameProg c e T m Y
  have h := Prog.lang_mem_EXPSPACE P p hP
  have hset : P.Lang = {x : BitString | val (gameOf c e x T.fn ((2 : ℝ)⁻¹ ^ m)
      (querySet c.toOTM x (clock e x.length) \ Y)) = true} := Set.ext fun x => hacc x
  rw [← hset]
  exact h

end Kolmogorov.RandomStrings
