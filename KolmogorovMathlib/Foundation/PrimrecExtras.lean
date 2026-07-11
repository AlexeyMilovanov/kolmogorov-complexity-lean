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
-/

namespace Kolmogorov

open Primrec

variable {α : Type*} [Primcodable α]

/-- `List.drop` is primitive recursive in both arguments. -/
theorem _root_.Primrec.list_drop :
    Primrec₂ (fun (l : List α) (n : ℕ) => l.drop n) := by
  have h : (fun (l : List α) (n : ℕ) => l.drop n)
      = fun l n => Nat.rec l (fun _ ih => ih.tail) n := by
    funext l n
    induction n with
    | zero => rfl
    | succ n ih => rw [← List.tail_drop, ih]
  rw [h]
  exact Primrec.nat_rec' Primrec.snd Primrec.fst
    (Primrec.list_tail.comp (Primrec.snd.comp Primrec.snd)).to₂

/-- `List.take` is primitive recursive in both arguments (via
`take n l = (l.reverse.drop (l.length − n)).reverse`). -/
theorem _root_.Primrec.list_take :
    Primrec₂ (fun (l : List α) (n : ℕ) => l.take n) := by
  have h_take_eq : ∀ (l : List α) (n : ℕ),
      l.take n = (l.reverse.drop (l.length - n)).reverse := by
    grind +suggestions
  have h : Primrec (fun p : List α × ℕ =>
      (p.1.reverse.drop (p.1.length - p.2)).reverse) :=
    Primrec.list_reverse.comp
      (Primrec.list_drop.comp (Primrec.list_reverse.comp Primrec.fst)
        (Primrec.nat_sub.comp (Primrec.list_length.comp Primrec.fst) Primrec.snd))
  exact h.of_eq (fun p => (h_take_eq p.1 p.2).symm)

/-- `List.takeWhile` with a primitive recursive predicate is primitive
recursive (via the fold identity
`takeWhile p = foldr (fun a acc => bif p a then a :: acc else []) []`). -/
theorem _root_.Primrec.list_takeWhile {p : α → Bool} (hp : Primrec p) :
    Primrec (fun l : List α => l.takeWhile p) := by
  have hid : ∀ l : List α, l.takeWhile p
      = l.foldr (fun a acc => bif p a then a :: acc else []) [] := by
    intro l
    induction l with
    | nil => rfl
    | cons a t ih => cases hpa : p a <;> simp [hpa, ih]
  have h : Primrec (fun l : List α =>
      l.foldr (fun a acc => bif p a then a :: acc else []) []) :=
    Primrec.list_foldr Primrec.id (Primrec.const [])
      ((Primrec.cond (hp.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
          (Primrec.snd.comp Primrec.snd))
        (Primrec.const [])).to₂)
  exact h.of_eq (fun l => (hid l).symm)

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
