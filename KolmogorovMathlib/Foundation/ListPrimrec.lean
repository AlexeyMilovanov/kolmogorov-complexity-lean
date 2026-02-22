import Mathlib.Computability.Partrec
import Mathlib.Data.List.Basic

/-!
# Primitive Recursive Functions on Lists

This module provides structural-recursive implementations of basic list operations
(`prefixLen` and `listDrop`) and proves their primitive recursiveness (`Primrec`).
These low-level primitives are required to build the Universal Turing Machine
without relying on the non-computable or complex equation lemmas of standard
library list functions.
-/

namespace Kolmogorov

-- ==========================================================
-- PHASE 1: List Computability Primitives
-- Custom Turing-friendly functions for List Bool
-- ==========================================================

/-- Computes the number of consecutive `true`s at the start of a boolean list.
    Defined using strict `List.recOn` to perfectly match `Primrec.list_rec`. -/
def prefixLen (l : List Bool) : ℕ :=
  List.recOn l 0 (fun head _ IH => cond head (IH + 1) 0)

/-- Proves that `prefixLen` is Primitive Recursive. -/
lemma Primrec.prefixLen : Primrec prefixLen := by
  have h_f : Primrec (fun (l : List Bool) => l) := Primrec.id
  have h_base : Primrec (fun (_ : List Bool) => (0 : ℕ)) := Primrec.const 0
  have h_step : Primrec₂ (fun (_ : List Bool) (p : Bool × List Bool × ℕ) =>
      cond p.1 (p.2.2 + 1) 0) :=
    Primrec.cond (Primrec.fst.comp Primrec.snd)
      (Primrec.succ.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.const 0)
  exact Primrec.list_rec h_f h_base h_step

/-- Drops `n` elements from a list.
    Defined as a function of two arguments to perfectly match `Primrec₂`.
    Uses strict `Nat.rec` so the combinator recognizes it instantly. -/
def listDrop (l : List Bool) (n : ℕ) : List Bool :=
  Nat.rec l (fun _ r => r.tail) n

/-- Proves that `listDrop` is a computable function of two arguments. -/
lemma Primrec₂.listDrop : Primrec₂ listDrop := by
  have h_base : Primrec (fun (l : List Bool) => l) := Primrec.id
  have h_step : Primrec₂ (fun (_ : List Bool) (p : ℕ × List Bool) => p.2.tail) :=
    Primrec.list_tail.comp (Primrec.snd.comp Primrec.snd)
  exact Primrec.nat_rec h_base h_step

end Kolmogorov
