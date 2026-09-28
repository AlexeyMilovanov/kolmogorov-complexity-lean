import KolmogorovMathlib.AlgorithmicStatistics.Selector
import KolmogorovMathlib.MonotoneComplexity.NestedAllocation

/-!
# A computability toolkit for lists

Mathlib's `Primrec` API is closed under the usual list operations, but the corresponding
`Computable` statements are not available.  This file supplies the three that the a priori
sublevel cover needs — left folds, existential quantification and filtering along a computable
list with a computable step function or predicate — by realising the fold as a `Nat.rec`
iteration over a state consisting of the remaining list together with the accumulator.

It also records two `Primrec` facts (decidable equality and `List.any`) that are stated in a form
convenient for the same development.
-/

namespace Kolmogorov

open Primrec


variable {α β σ : Type*} [Primcodable α] [Primcodable β] [Inhabited β] [Primcodable σ]

/-- The state transformer used to realise a left fold as a `Nat.rec` iteration. -/
private def foldStep (H : σ × β → σ) : List β × σ → List β × σ :=
  fun p => (p.1.tail, H (p.2, p.1.headD default))

omit [Primcodable β] [Primcodable σ] in
private theorem foldStep_iterate (H : σ × β → σ) :
    ∀ (l : List β) (acc : σ),
      (foldStep H)^[l.length] (l, acc) = ([], l.foldl (fun s b => H (s, b)) acc) := by
  intro l
  induction l with
  | nil => intro acc; rfl
  | cons b t ih =>
    intro acc
    rw [List.length_cons, Function.iterate_succ_apply]
    simpa [foldStep] using ih (H (acc, b))

/-- Left folds along a computable list with a computable step function are computable. -/
theorem computable_list_foldl {f : α → List β} {g : α → σ} {h : α → σ × β → σ}
    (hf : Computable f) (hg : Computable g) (hh : Computable₂ h) :
    Computable (fun a => (f a).foldl (fun s b => h a (s, b)) (g a)) := by
  have hstep : Computable₂ (fun (a : α) (u : ℕ × (List β × σ)) => foldStep (h a) u.2) := by
    have h1 : Computable (fun v : α × (ℕ × (List β × σ)) => v.2.2.1.tail) :=
      (Primrec.list_tail.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))).to_comp
    have h2 : Computable (fun v : α × (ℕ × (List β × σ)) =>
        h v.1 (v.2.2.2, v.2.2.1.headD default)) :=
      hh.comp Computable.fst (Computable.pair
        (Computable.snd.comp (Computable.snd.comp Computable.snd))
        ((headD_primrec (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)) default).to_comp))
    exact (Computable.pair h1 h2).to₂
  have hrec := Computable.nat_rec (Primrec.list_length.to_comp.comp hf)
    (Computable.pair hf hg) hstep
  refine (Computable.snd.comp hrec).of_eq (fun a => ?_)
  rw [natRec_eq_iterate, foldStep_iterate]

omit [Primcodable α] [Primcodable β] [Inhabited β] [Primcodable σ] in
private theorem foldl_or_eq (p : β → Bool) : ∀ (l : List β) (acc : Bool),
    l.foldl (fun s b => s || p b) acc = (acc || l.any p) := by
  intro l
  induction l with
  | nil => intro acc; simp
  | cons b t ih => intro acc; simp [ih, Bool.or_assoc]

omit [Primcodable α] [Primcodable β] [Inhabited β] [Primcodable σ] in
private theorem foldl_filter_eq (p : β → Bool) : ∀ (l : List β) (acc : List β),
    l.foldl (fun s b => bif p b then s ++ [b] else s) acc = acc ++ l.filter p := by
  intro l
  induction l with
  | nil => intro acc; simp
  | cons b t ih =>
    intro acc
    cases hb : p b <;> simp [ih, hb]

/-- Existential quantification over a computable list with a computable predicate. -/
theorem computable_list_any {f : α → List β} {p : α → β → Bool}
    (hf : Computable f) (hp : Computable₂ p) : Computable (fun a => (f a).any (p a)) := by
  have hh : Computable₂ (fun (a : α) (u : Bool × β) => u.1 || p a u.2) :=
    (Primrec.or.to_comp.comp (Computable.fst.comp Computable.snd)
      (hp.comp Computable.fst (Computable.snd.comp Computable.snd))).to₂
  refine (computable_list_foldl hf (g := fun _ => false) (Computable.const false) hh).of_eq
    (fun a => ?_)
  rw [foldl_or_eq]
  simp

/-- Filtering a computable list by a computable predicate is computable. -/
theorem computable_list_filter {f : α → List β} {p : α → β → Bool}
    (hf : Computable f) (hp : Computable₂ p) : Computable (fun a => (f a).filter (p a)) := by
  have hh : Computable₂ (fun (a : α) (u : List β × β) =>
      bif p a u.2 then u.1 ++ [u.2] else u.1) :=
    (Computable.cond (hp.comp Computable.fst (Computable.snd.comp Computable.snd))
      (Primrec.list_append.to_comp.comp (Computable.fst.comp Computable.snd)
        (Computable.list_cons.comp (Computable.snd.comp Computable.snd)
          (Computable.const [])))
      (Computable.fst.comp Computable.snd)).to₂
  refine (computable_list_foldl hf (g := fun _ => ([] : List β)) (Computable.const []) hh).of_eq
    (fun a => ?_)
  rw [foldl_filter_eq]
  simp

omit [Inhabited β] in
/-- Deciding equality is primitive recursive. -/
theorem primrec_decideEq [DecidableEq β] : Primrec₂ (fun (a b : β) => decide (a = b)) := by
  obtain ⟨_, hp⟩ := (Primrec.eq : PrimrecRel (fun a b : β => a = b))
  exact hp.of_eq (fun w => Bool.eq_iff_iff.mpr (by simp))

end Kolmogorov
