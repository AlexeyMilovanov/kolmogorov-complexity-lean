/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/

import Mathlib.Computability.Partrec
import Mathlib.Computability.Primrec.List

/-!
# Primitive-recursion toolkit

This file extends Mathlib's `Primrec` API with generic list and iteration
lemmas used throughout the development. It also provides list-first wrappers
for Mathlib's number-first `Primrec.list_drop` and `Primrec.list_take` results.

Provided: `Primrec.list_drop_listFirst`, `Primrec.list_take_listFirst`,
`Primrec.list_replicate`, `Primrec.nat_iterate'`, and the best-effort tactic
macro `primrec_auto`. Mathlib provides `Primrec.list_takeWhile` directly.

`Mathlib.Computability.Partrec` is imported for `Primrec.to_comp`, which
`primrec_auto` uses to reduce a `Computable` goal to a `Primrec` one. No
declaration in this file mentions it, but a tactic quotation resolves its
identifiers against the macro's declaration site, so dropping the import
would make every `primrec_auto` expansion fail.
-/

namespace Kolmogorov

open Primrec

variable {α : Type*} [Primcodable α]

/-- List-first compatibility form of Mathlib's number-first `Primrec.list_drop`. -/
theorem _root_.Primrec.list_drop_listFirst :
    Primrec₂ (fun (l : List α) (n : ℕ) => l.drop n) := by
  exact (Primrec.list_drop (α := α)).comp Primrec.snd Primrec.fst

/-- List-first compatibility form of Mathlib's number-first `Primrec.list_take`. -/
theorem _root_.Primrec.list_take_listFirst :
    Primrec₂ (fun (l : List α) (n : ℕ) => l.take n) := by
  exact (Primrec.list_take (α := α)).comp Primrec.snd Primrec.fst

/-- `List.replicate` is primitive recursive in both arguments. -/
theorem _root_.Primrec.list_replicate :
    Primrec₂ (fun (n : ℕ) (a : α) => List.replicate n a) := by
  have h : ∀ (n : ℕ) (a : α),
      List.replicate n a = Nat.rec [] (fun _ ih => a :: ih) n := by
    intro n a
    induction n with
    | zero => rfl
    | succ n ih => rw [List.replicate_succ, ih]
  have hp : Primrec (fun q : ℕ × α =>
      (Nat.rec [] (fun _ ih => q.2 :: ih) q.1 : List α)) :=
    Primrec.nat_rec' Primrec.fst (Primrec.const [])
      ((Primrec.list_cons.comp (Primrec.snd.comp Primrec.fst)
        (Primrec.snd.comp Primrec.snd)).to₂)
  exact hp.of_eq (fun q => (h q.1 q.2).symm)

/-- Iterating a primitive recursive function a variable number of times is
primitive recursive: `(a, n) ↦ f^[n] a`. -/
theorem _root_.Primrec.nat_iterate' {f : α → α} (hf : Primrec f) :
    Primrec₂ (fun (a : α) (n : ℕ) => f^[n] a) := by
  have h : ∀ (a : α) (n : ℕ), f^[n] a = Nat.rec a (fun _ ih => f ih) n := by
    intro a n
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', ih]
  have hp : Primrec (fun q : α × ℕ =>
      (Nat.rec q.1 (fun _ ih => f ih) q.2 : α)) :=
    Primrec.nat_rec' Primrec.snd Primrec.fst
      ((hf.comp (Primrec.snd.comp Primrec.snd)).to₂)
  exact hp.of_eq (fun q => (h q.1 q.2).symm)

/-- Best-effort automation for `Primrec`/`Computable` goals: `apply_rules`
over the standard combinators and the list toolkit. Works for goals whose
composition structure is forced by the expected type; for higher-order
splits (choosing how to factor `fun a => f (g a)`) fall back to manual
`.comp` chains. -/
macro "primrec_auto" : tactic =>
  `(tactic| apply_rules [Primrec.id, Primrec.fst, Primrec.snd, Primrec.const,
      Primrec.pair, Primrec.succ, Primrec.pred, Primrec.nat_add,
      Primrec.nat_sub, Primrec.nat_mul, Primrec.list_cons, Primrec.list_append,
      Primrec.list_reverse, Primrec.list_length, Primrec.list_tail,
      Primrec.list_drop, Primrec.list_take, Primrec.list_drop_listFirst,
      Primrec.list_take_listFirst, Primrec.list_replicate,
      Primrec.to_comp, Primrec.to₂])

end Kolmogorov
