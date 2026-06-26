/-
Copyright (c) 2024 Alexey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey
-/
import Mathlib
import KolmogorovMathlib.Prefix.Basic

/-!
# Computability Helpers for Tuples and Options

This module provides reusable computability lemmas for common shapes,
packed applications, and wrappers for `Option` and `Nat` combinators,
simplifying manual proofs.
-/

namespace Kolmogorov
namespace Computability

/-! ## Packed Application Combinators -/

lemma beta_pair {α β γ} (f : α → β → γ) (x : α) (y : β) :
  (fun p : α × β => f p.1 p.2) (x, y) = f x y := rfl

lemma beta_pair3 {α β γ δ} (f : α → β → γ → δ) (x : α) (y : β) (z : γ) :
  (fun p : α × β × γ => f p.1 p.2.1 p.2.2) (x, y, z) = f x y z := rfl

lemma beta_pair4 {α β γ δ ε} (f : α → β → γ → δ → ε) (x : α) (y : β) (z : γ) (w : δ) :
  (fun p : α × β × γ × δ => f p.1 p.2.1 p.2.2.1 p.2.2.2) (x, y, z, w) = f x y z w := rfl

/-! ## Generic Projection Computability Helpers -/

lemma comp_fst {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
    {f : α → β × γ} (hf : Computable f) : Computable (fun a => (f a).1) := Computable.fst.comp hf

lemma comp_snd {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
    {f : α → β × γ} (hf : Computable f) : Computable (fun a => (f a).2) := Computable.snd.comp hf

lemma comp_fst_fst {α β γ δ} [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable δ]
    {f : α → (β × γ) × δ} (hf : Computable f) : Computable (fun a => (f a).1.1) :=
  Computable.fst.comp (Computable.fst.comp hf)

lemma comp_fst_snd {α β γ δ} [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable δ]
    {f : α → (β × γ) × δ} (hf : Computable f) : Computable (fun a => (f a).1.2) :=
  Computable.snd.comp (Computable.fst.comp hf)

lemma comp_snd_fst {α β γ δ} [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable δ]
    {f : α → β × (γ × δ)} (hf : Computable f) : Computable (fun a => (f a).2.1) :=
  Computable.fst.comp (Computable.snd.comp hf)

lemma comp_snd_snd {α β γ δ} [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable δ]
    {f : α → β × (γ × δ)} (hf : Computable f) : Computable (fun a => (f a).2.2) :=
  Computable.snd.comp (Computable.snd.comp hf)

lemma comp_snd_snd_snd {α β γ δ ε} [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable δ] [Primcodable ε]
    {f : α → β × (γ × (δ × ε))} (hf : Computable f) : Computable (fun a => (f a).2.2.2) :=
  Computable.snd.comp (Computable.snd.comp (Computable.snd.comp hf))

lemma comp_snd_snd_fst {α β γ δ ε} [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable δ] [Primcodable ε]
    {f : α → β × (γ × (δ × ε))} (hf : Computable f) : Computable (fun a => (f a).2.2.1) :=
  Computable.fst.comp (Computable.snd.comp (Computable.snd.comp hf))

lemma comp_fst_fst_fst {α β γ δ ε} [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable δ] [Primcodable ε]
    {f : α → ((β × γ) × δ) × ε} (hf : Computable f) : Computable (fun a => (f a).1.1.1) :=
  Computable.fst.comp (Computable.fst.comp (Computable.fst.comp hf))

lemma comp_fst_snd_fst {α β γ δ ε} [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable δ] [Primcodable ε]
    {f : α → (β × (γ × δ)) × ε} (hf : Computable f) : Computable (fun a => (f a).1.2.1) :=
  Computable.fst.comp (Computable.snd.comp (Computable.fst.comp hf))

/-! ## Option Combinators -/

lemma comp_option_map {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
    {f : α → Option β} {g : α → β → γ}
    (hf : Computable f) (hg : Computable₂ g) :
    Computable (fun a => (f a).map (g a)) :=
  Computable.option_map hf hg

lemma comp_option_bind {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
    {f : α → Option β} {g : α → β → Option γ}
    (hf : Computable f) (hg : Computable₂ g) :
    Computable (fun a => (f a).bind (g a)) :=
  Computable.option_bind hf hg

lemma comp_option_getD {α β} [Primcodable α] [Primcodable β]
    {f : α → Option β} {g : α → β}
    (hf : Computable f) (hg : Computable g) :
    Computable (fun a => (f a).getD (g a)) :=
  Computable.option_getD hf hg

/-! ## Encodable Combinators -/

lemma comp_decode {α β} [Primcodable α] [Primcodable β]
    {f : α → ℕ} (hf : Computable f) :
    Computable (fun a => (Encodable.decode (f a) : Option β)) :=
  Computable.decode.comp hf

lemma comp_decode_getD {α β} [Primcodable α] [Primcodable β]
    {f : α → ℕ} {d : α → β}
    (hf : Computable f) (hd : Computable d) :
    Computable (fun a => (Encodable.decode (f a) : Option β).getD (d a)) :=
  Computable.option_getD (comp_decode hf) hd

/-! ## Nat Recursion Combinators -/

lemma comp_nat_rec {α β} [Primcodable α] [Primcodable β]
    {n : α → ℕ} {z : α → β} {s : α → ℕ → β → β}
    (hn : Computable n) (hz : Computable z)
    (hs : Computable₂ (fun a (p : ℕ × β) => s a p.1 p.2)) :
    Computable (fun a => Nat.rec (motive := fun _ => β) (z a) (fun k r => s a k r) (n a)) :=
  (Computable.nat_rec hn hz hs).of_eq (fun _ => rfl)

lemma comp_nat_casesOn {α β} [Primcodable α] [Primcodable β]
    {n : α → ℕ} {z : α → β} {s : α → ℕ → β}
    (hn : Computable n) (hz : Computable z)
    (hs : Computable₂ (fun a (k : ℕ) => s a k)) :
    Computable (fun a => Nat.casesOn (motive := fun _ => β) (n a) (z a) (s a)) :=
  (Computable.nat_casesOn hn hz hs).of_eq (fun _ => rfl)

/-
Computable finite sums over an initial segment whose bound is computable. A
reusable bridge: `Computable.nat_rec` builds `∑_{t<b a} g a t` as an accumulator.
-/
lemma computable_range_sum {α : Type*} [Primcodable α]
    (g : α → ℕ → ℕ) (hg : Computable₂ g) (b : α → ℕ) (hb : Computable b) :
    Computable (fun a => ∑ t ∈ Finset.range (b a), g a t) := by
  have h_sum_computable : ∀ (f : α → ℕ → ℕ), Computable₂ f → Computable (fun a => ∑ t ∈ Finset.range (b a), f a t) := by
    intro f hf;
    have h_sum_computable : ∃ F : α → ℕ × ℕ → ℕ, Computable₂ F ∧ ∀ a n, F a (n, ∑ t ∈ Finset.range n, f a t) = ∑ t ∈ Finset.range (n + 1), f a t := by
      refine ⟨ fun a p => p.2 + f a p.1, ?_, ?_ ⟩ <;> simp_all +decide [ Computable₂ ];
      · have h_sum_computable : Computable (fun p : α × ℕ × ℕ => p.2.2 + f p.1 p.2.1) := by
          have h_add : Computable (fun p : ℕ × ℕ => p.1 + p.2) := by
            -- The addition function is primitive recursive, hence computable.
            have h_add_primrec : Primrec (fun p : ℕ × ℕ => p.1 + p.2) := by
              exact Primrec.nat_add.comp ( Primrec.fst ) ( Primrec.snd );
            exact h_add_primrec.to_comp
          convert h_add.comp ( Computable.snd.comp ( Computable.snd ) |> Computable.pair <| hf.comp ( Computable.fst |> Computable.pair <| Computable.fst.comp ( Computable.snd ) ) ) using 1;
        exact h_sum_computable;
      · exact fun a n => by rw [ Finset.sum_range_succ ] ;
    obtain ⟨ F, hF₁, hF₂ ⟩ := h_sum_computable;
    convert Computable.nat_rec hb ( Computable.const 0 ) ( hF₁.comp ( Computable.fst ) ( Computable.snd ) ) using 1;
    ext a; exact (by
    induction b a with
    | zero => simp_all +decide [ Finset.sum_range_succ ]
    | succ n ih =>
      simp_all +decide [ Finset.sum_range_succ ]
      rw [ ← ih, hF₂ ]);
  exact h_sum_computable g hg

/-- `n ↦ 2^n` is primitive recursive. -/
lemma primrec_two_pow : Primrec (fun n : ℕ => 2 ^ n) := by
  have h : (fun n : ℕ => 2 ^ n) = (fun n => Nat.rec 1 (fun _ ih => 2 * ih) n) := by
    funext n; induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ, ih]; ring
  rw [h]
  exact Primrec.nat_rec' Primrec.id (Primrec.const 1)
    (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.snd.comp Primrec.snd)).to₂

lemma computable_two_mul : Computable (fun n : ℕ => 2 * n) := by
  exact (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id).to_comp

lemma comp_evaln {α} [Primcodable α]
    {s : α → ℕ} {c : α → Nat.Partrec.Code} {x : α → ℕ}
    (hs : Computable s) (hc : Computable c) (hx : Computable x) :
    Computable (fun a => Nat.Partrec.Code.evaln (s a) (c a) (x a)) :=
  (Nat.Partrec.Code.primrec_evaln.to_comp.comp ((hs.pair hc).pair hx)).of_eq (fun _ => rfl)

def evalnDecoded {β} [Encodable β] (s : ℕ) (c : ℕ) (x : β) : Option ℕ :=
  Nat.Partrec.Code.evaln s
    ((Encodable.decode (α := Nat.Partrec.Code) c).getD Nat.Partrec.Code.zero)
    (Encodable.encode x)

lemma comp_evaln_decoded {α β} [Primcodable α] [Primcodable β]
    {s : α → ℕ} {c : α → ℕ} {x : α → β}
    (hs : Computable s) (hc : Computable c) (hx : Computable x) :
    Computable (fun a => evalnDecoded (s a) (c a) (x a)) :=
  comp_evaln hs
    (comp_decode_getD hc (Computable.const Nat.Partrec.Code.zero))
    (Computable.encode.comp hx)

lemma exists_code_of_computable_nat {α} [Primcodable α] [Inhabited α]
    (f : α → ℕ) (hf : Computable f) :
    ∃ c : Nat.Partrec.Code, ∀ a : α,
      Nat.Partrec.Code.eval c (Encodable.encode a) = some (f a) := by
  have h_total : ∃ h : ℕ → ℕ, Computable h ∧ ∀ a : α, h (Encodable.encode a) = f a := by
    use fun n => f ((Encodable.decode (α := α) n).getD default)
    refine ⟨hf.comp (comp_decode_getD Computable.id (Computable.const default)), ?_⟩
    intro a
    simp [Encodable.encodek]
  obtain ⟨h, hh₁, hh₂⟩ := h_total
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp (by simpa [Computable, Partrec] using hh₁)
  exact ⟨c, fun a => by simp [← hh₂, hc]⟩

end Computability
end Kolmogorov
