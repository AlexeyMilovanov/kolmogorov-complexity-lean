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

end Computability
end Kolmogorov
