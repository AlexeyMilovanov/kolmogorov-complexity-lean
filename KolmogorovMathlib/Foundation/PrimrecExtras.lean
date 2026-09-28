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
`Primrec.list_replicate`, `Primrec.nat_iterate'`, the lattice operations
`Kolmogorov.primrec₂_max_of_le` and `Kolmogorov.primrec₂_min_of_le`, and the
best-effort tactic macro `primrec_auto`.

`Mathlib.Computability.Partrec` provides `Primrec.to_comp`, which is used by
the `primrec_auto` quotation and must therefore be available at the macro's
declaration site.
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
    intro l n
    induction l generalizing n with
    | nil => simp
    | cons a l ih =>
      cases n with
      | zero => simp
      | succ n =>
        simp only [List.take_succ_cons, List.reverse_cons, List.length_cons,
          Nat.succ_sub_succ_eq_sub]
        rw [List.drop_append_of_le_length (l₁ := l.reverse) (l₂ := [a])
          (i := l.length - n) (by simp), List.reverse_append]
        simp [ih]
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

/-- `List.all` with a primitive recursive predicate is primitive recursive. -/
theorem _root_.Primrec.list_all {α : Type*} [Primcodable α] {p : α → Bool} (hp : Primrec p) :
    Primrec (fun l : List α => l.all p) := by
  have hid : ∀ l : List α, l.all p = l.foldr (fun a acc => p a && acc) true := by
    intro l
    induction l with
    | nil => rfl
    | cons a t ih => simp [ih]
  have hp_fold : Primrec (fun l : List α => l.foldr (fun a acc => p a && acc) true) :=
    Primrec.list_foldr Primrec.id (Primrec.const true)
      ((Primrec.dom_bool₂ (fun b c : Bool => b && c)).comp
        (hp.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.snd)).to₂
  exact hp_fold.of_eq (fun l => (hid l).symm)

/-- Filtering a primitive recursive list by a primitive recursive predicate is
primitive recursive. -/
theorem _root_.Primrec.list_filter {α β : Type*} [Primcodable α] [Primcodable β]
    {l : α → List β} {p : α → β → Bool} (hl : Primrec l) (hp : Primrec₂ p) :
    Primrec (fun a => (l a).filter (p a)) := by
  have hid : ∀ a,
    (l a).filter (p a) = (l a).foldr (fun b s => bif p a b then b :: s else s) [] := by
    intro a
    induction l a with
    | nil => rfl
    | cons b t ih => cases hpa : p a b <;> simp [ih, hpa]
  have hh : Primrec₂ (fun (a : α) (p_1 : β × List β) =>
    bif p a p_1.1 then p_1.1 :: p_1.2 else p_1.2) :=
    Primrec.cond (hp.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
  have h_fold : Primrec (fun a => (l a).foldr (fun b s => bif p a b then b :: s else s) []) :=
    Primrec.list_foldr hl (Primrec.const []) hh
  exact h_fold.of_eq (fun a => (hid a).symm)

/-- Mapping a computable function over a computable list is computable. -/
theorem _root_.Computable.list_map {α β γ : Type*} [Primcodable α] [Primcodable β] [Primcodable γ]
    {l : α → List β} {f : α → β → γ} (hl : Computable l) (hf : Computable₂ f) :
    Computable (fun a => (l a).map (f a)) := by
  have h_len : Computable (fun a => (l a).length) :=
    Primrec.list_length.to_comp.comp hl
  have h_drop : Computable (fun p : α × ℕ => ((l p.1).drop p.2).head?) :=
    Primrec.list_head?.to_comp.comp (
      Computable₂.comp (f := fun l n =>
        List.drop n l) (Primrec.list_drop).to_comp (hl.comp Computable.fst) Computable.snd)
  have h_step : Computable₂ (fun (a : α) (p_1 : ℕ × List γ) =>
    p_1.2 ++ Option.casesOn (((l a).drop p_1.1).head?) [] (fun b => [f a b])) := by
    apply Computable₂.comp Computable.list_append (Computable.snd.comp Computable.snd)
    have ho : Computable (fun (p : α × (ℕ × List γ)) => ((l p.1).drop p.2.1).head?) :=
      h_drop.comp (Computable.pair Computable.fst (Computable.fst.comp Computable.snd))
    have hf_cases : Computable (fun (p : α × (ℕ × List γ)) => ([] : List γ)) :=
      Computable.const []
    have hg_cases : Computable₂ (fun (p : α × (ℕ × List γ)) (b : β) => [f p.1 b]) :=
      Computable₂.comp Computable.list_cons
        (hf.comp (Computable.fst.comp Computable.fst) Computable.snd)
        (Computable.const [])
    exact Computable.option_casesOn ho hf_cases hg_cases
  have h_rec : Computable (fun a => Nat.rec (motive := fun _ => List γ) [] (fun y (IH : List γ) =>
    IH ++ Option.casesOn (((l a).drop y).head?) ([] : List γ) (fun b => [f a b])) ((l a).length)) :=
    Computable.nat_rec h_len (Computable.const []) h_step
  have hid : ∀ a,
    (l a).map (f a) = Nat.rec (motive := fun _ => List γ) [] (fun y (IH : List γ) =>
    IH ++ Option.casesOn (((l a).drop y).head?) ([] : List γ) (fun b =>
    [f a b])) ((l a).length) := by
    intro a
    have H : ∀ n,
      n ≤ (l a).length → Nat.rec (motive := fun _ => List γ) [] (fun y (IH : List γ) =>
      IH ++ Option.casesOn (((l a).drop y).head?) ([] : List γ) (fun b =>
      [f a b])) n = ((l a).take n).map (f a) := by
      intro n
      induction n with
      | zero =>
        intro hn
        simp
      | succ n ih =>
        intro hn
        have hn_le : n ≤ (l a).length := Nat.le_of_succ_le hn
        change Nat.rec (motive := fun _ => List γ) [] (fun y (IH : List γ) =>
          IH ++ Option.casesOn (((l a).drop y).head?) ([] : List γ) (fun b =>
          [f a b])) n ++ Option.casesOn (((l a).drop n).head?) ([] : List γ) (fun b =>
          [f a b]) = ((l a).take (n + 1)).map (f a)
        rw [ih hn_le]
        have h1 : (l a).take (n + 1) = (l a).take n ++ ((l a)[n]?).toList := List.take_add_one
        rw [h1, List.map_append]
        congr
        have h2 : ((l a).drop n).head? = (l a)[n]? := by rw [List.head?_drop]
        rw [h2]
        cases (l a)[n]? with
        | none => rfl
        | some x => rfl
    have h_len2 : (l a).take (l a).length = l a := List.take_length
    have h_all := H ((l a).length) (Nat.le_refl _)
    rw [h_len2] at h_all
    exact h_all.symm
  exact h_rec.of_eq (fun a => (hid a).symm)

/-- `List.any` with a primrec list and primrec predicate is primrec. -/
theorem list_any_primrec {α β} [Primcodable α] [Primcodable β] {f : α → List β} {p : α → β → Bool}
    (hf : Primrec f) (hp : Primrec₂ p) : Primrec (fun a => (f a).any (p a)) := by
  have heq : (fun a => (f a).any (p a))
      = (fun a => (f a).foldr (fun b acc => p a b || acc) false) := by
    funext a; induction f a with
    | nil => rfl
    | cons b t ih => simp [List.any_cons, ih]
  rw [heq]
  have hstep : Primrec₂ (fun (a : α) (q : β × Bool) => p a q.1 || q.2) :=
    (Primrec.cond (hp.comp Primrec.fst (Primrec.fst.comp Primrec.snd)) (Primrec.const true)
      (Primrec.snd.comp Primrec.snd)).to₂
  exact Primrec.list_foldr hf (Primrec.const false) hstep

/-- `List.all` with a primrec list and primrec predicate is primrec. -/
theorem list_all_primrec {α β} [Primcodable α] [Primcodable β] {f : α → List β}
    {p : α → β → Bool} (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec (fun a => (f a).all (p a)) := by
  have heq : (fun a => (f a).all (p a))
      = (fun a => (f a).foldr (fun b acc => p a b && acc) true) := by
    funext a; induction f a with
    | nil => rfl
    | cons b t ih => simp [List.all_cons, ih]
  rw [heq]
  have hstep : Primrec₂ (fun (a : α) (q : β × Bool) => p a q.1 && q.2) :=
    (Primrec.and.comp (hp.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂
  exact Primrec.list_foldr hf (Primrec.const true) hstep

/-- `List.filter` with a primrec list and primrec predicate is primrec. -/
theorem list_filter_primrec {α β} [Primcodable α] [Primcodable β] {f : α → List β}
    {p : α → β → Bool} (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec (fun a => (f a).filter (p a)) := by
  exact Primrec.list_filter hf hp

/-! ### Lattice operations from a primitive recursive order -/

/-- **The maximum of a linear order is primitive recursive as soon as its order relation
is.** Deciding `a ≤ b` and selecting the corresponding argument computes `max a b`; every
concrete `max` in this development (on `ℕ`, on `ℚ`) is an instance of this lemma. -/
theorem primrec₂_max_of_le {α : Type*} [Primcodable α] [LinearOrder α]
    (hle : PrimrecRel ((· ≤ ·) : α → α → Prop)) : Primrec₂ (max : α → α → α) :=
  (Primrec.ite (PrimrecRel.comp hle Primrec.fst Primrec.snd)
    Primrec.snd Primrec.fst).of_eq
    (fun p => by
      by_cases h : p.1 ≤ p.2
      · rw [if_pos h, max_eq_right h]
      · rw [if_neg h, max_eq_left (not_le.mp h).le])

/-- **The minimum of a linear order is primitive recursive as soon as its order relation
is**, by the same selection as `Kolmogorov.primrec₂_max_of_le`. -/
theorem primrec₂_min_of_le {α : Type*} [Primcodable α] [LinearOrder α]
    (hle : PrimrecRel ((· ≤ ·) : α → α → Prop)) : Primrec₂ (min : α → α → α) :=
  (Primrec.ite (PrimrecRel.comp hle Primrec.fst Primrec.snd)
    Primrec.fst Primrec.snd).of_eq
    (fun p => by
      by_cases h : p.1 ≤ p.2
      · rw [if_pos h, min_eq_left h]
      · rw [if_neg h, min_eq_right (not_le.mp h).le])

end Kolmogorov

/-- A left fold with computable data and step function is computable. -/
theorem _root_.Computable.list_foldl {α β σ : Type*} [Primcodable α] [Primcodable β] [Primcodable σ]
    {l : α → List β} {g : α → σ} {h : α → σ × β
      → σ} (hl : Computable l) (hg : Computable g) (hh : Computable₂ h) :
    Computable (fun a => (l a).foldl (fun s b => h a (s, b)) (g a)) := by
  have h_len : Computable (fun a => (l a).length) :=
    Primrec.list_length.to_comp.comp hl
  have h_drop : Computable (fun p : α × ℕ => ((l p.1).drop p.2).head?) :=
    Primrec.list_head?.to_comp.comp (
      Computable₂.comp (f := fun list n =>
        List.drop n list) (Primrec.list_drop).to_comp (hl.comp Computable.fst) Computable.snd)
  have h_step : Computable₂ (fun (a : α) (p_1 : ℕ × σ) =>
    Option.casesOn (motive := fun _ => σ) (((l a).drop p_1.1).head?) p_1.2 (fun b =>
      h a (p_1.2, b))) := by
    have ho : Computable (fun (p : α × (ℕ × σ)) => ((l p.1).drop p.2.1).head?) :=
      h_drop.comp (Computable.pair Computable.fst (Computable.fst.comp Computable.snd))
    have hf_cases : Computable (fun (p : α × (ℕ × σ)) => p.2.2) :=
      Computable.snd.comp Computable.snd
    have hg_cases : Computable₂ (fun (p : α × (ℕ × σ)) (b : β) => h p.1 (p.2.2, b)) :=
      hh.comp (Computable.fst.comp Computable.fst) (Computable.pair (Computable.snd.comp
        (Computable.snd.comp Computable.fst)) Computable.snd)
    exact Computable.option_casesOn ho hf_cases hg_cases
  have h_rec : Computable (fun a => Nat.rec (motive := fun _ => σ) (g a) (fun y (IH : σ) =>
    Option.casesOn (motive := fun _ => σ) (((l a).drop y).head?) IH (fun b => h a (IH,
    b))) ((l a).length)) :=
    Computable.nat_rec h_len hg h_step
  have hid : ∀ a, (l a).foldl (fun s b => h a (s,
    b)) (g a) = Nat.rec (motive := fun _ => σ) (g a) (fun y (IH : σ) => Option.casesOn (motive :=
    fun _ => σ) (((l a).drop y).head?) IH (fun b => h a (IH, b))) ((l a).length) := by
    intro a
    have H : ∀ n,
      n ≤ (l a).length → Nat.rec (motive := fun _ => σ) (g a) (fun y (IH : σ) =>
      Option.casesOn (motive := fun _ => σ) (((l a).drop y).head?) IH (fun b => h a (IH,
      b))) n = ((l a).take n).foldl (fun s b => h a (s, b)) (g a) := by
      intro n
      induction n with
      | zero =>
        intro hn
        simp
      | succ n ih =>
        intro hn
        have hn_le : n ≤ (l a).length := Nat.le_of_succ_le hn
        change Option.casesOn (motive := fun _ =>
          σ) (((l a).drop n).head?) (Nat.rec (motive := fun _ => σ) (g a) (fun y (IH : σ) =>
          Option.casesOn (motive := fun _ => σ) (((l a).drop y).head?) IH (fun b => h a (IH,
          b))) n) (fun b => h a (Nat.rec (motive := fun _ => σ) (g a) (fun y (IH : σ) =>
          Option.casesOn (motive := fun _ => σ) (((l a).drop y).head?) IH (fun b => h a (IH, b))) n,
          b)) = ((l a).take (n + 1)).foldl (fun s b => h a (s, b)) (g a)
        rw [ih hn_le]
        have h1 : (l a).take (n + 1) = (l a).take n ++ ((l a)[n]?).toList := List.take_add_one
        rw [h1, List.foldl_append]
        have h2 : ((l a).drop n).head? = (l a)[n]? := by rw [List.head?_drop]
        rw [h2]
        cases (l a)[n]? with
        | none => rfl
        | some x => rfl
    have h_len2 : (l a).take (l a).length = l a := List.take_length
    have h_all := H ((l a).length) (Nat.le_refl _)
    rw [h_len2] at h_all
    exact h_all.symm
  exact h_rec.of_eq (fun a => (hid a).symm)

/-- A right fold with computable data and step function is computable. -/
theorem _root_.Computable.list_foldr {α β σ : Type*} [Primcodable α] [Primcodable β] [Primcodable σ]
    {l : α → List β} {g : α → σ} {h : α → β × σ
      → σ} (hl : Computable l) (hg : Computable g) (hh : Computable₂ h) :
    Computable (fun a => (l a).foldr (fun b s => h a (b, s)) (g a)) := by
  have hrev : Computable (fun a => (l a).reverse) := Primrec.list_reverse.to_comp.comp hl
  have hh_swap : Computable₂ (fun a (p : σ × β) => h a (p.2, p.1)) :=
    Computable₂.comp hh Computable.fst (Computable.pair (Computable.snd.comp Computable.snd)
      (Computable.fst.comp Computable.snd))
  have hfoldl : Computable (fun a => ((l a).reverse).foldl (fun s b => h a (b, s)) (g a)) :=
    Computable.list_foldl hrev hg hh_swap
  exact hfoldl.of_eq fun a => by simp [List.foldl_reverse]
