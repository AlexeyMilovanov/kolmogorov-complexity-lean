import Mathlib.Computability.Partrec
import Mathlib.Computability.Primrec.List

/-!
# Primitive-recursion toolkit

Mathlib's `Primrec` API misses several list/iteration lemmas that this
development needs constantly; before this file they were re-derived locally
(specialised to `BitString` or `List BitString`) in `Prefix/TwoStage.lean`,
`TwoPart/DescriptionShift.lean`, `NormalizedCodedFiniteDistribution.lean`, and
`Encoding/Tuples.lean`. This file is the single home for such lemmas, stated
generically. **Add new general-purpose `Primrec` lemmas here, not next to
their first use.**

Provided: `Primrec.list_drop`, `Primrec.list_take`, `Primrec.list_takeWhile`,
`Primrec.list_replicate`, `Primrec.nat_iterate'`, and the best-effort tactic
macro `primrec_auto`.

`Mathlib.Computability.Partrec` provides `Primrec.to_comp`, which is used by
the `primrec_auto` quotation and must therefore be available at the macro's
declaration site.
-/

namespace Kolmogorov

open Primrec

variable {α : Type*} [Primcodable α]


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
      Primrec.list_drop, Primrec.list_take, Primrec.list_replicate,
      Primrec.to_comp, Primrec.to₂])

end Kolmogorov
