import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderGraft
import KolmogorovMathlib.Foundation.PrimrecExtras
import KolmogorovMathlib.MonotoneComplexity.ComputableListTools

/-!
# Computability of the two-level graft

`graftClientMove` and `graftTwoLevel` are defined through the structural
recursion `graftSubtreeAssoc`, which is not directly in the shape accepted by
the computability library.  The first lemma below rewrites it as a `flatMap`
over `(List.range n).reverse`, after which the standard primitive recursive
list combinators apply.

Nothing here is a new mathematical statement: the rewriting lemma is proved by
induction and everything else is bookkeeping.
-/

namespace Kolmogorov

open Encodable

/-- A `flatMap` of a computable family over a computable list is computable. -/
theorem computable_list_flatMap {α β σ : Type} [Primcodable α] [Primcodable β]
    [Primcodable σ] {l : α → List β} {f : α → β → List σ}
    (hl : Computable l) (hf : Computable₂ f) :
    Computable fun a => (l a).flatMap (f a) :=
  (Primrec.list_flatten.to_comp.comp (Computable.list_map hl hf)).of_eq fun a => by
    rw [List.flatMap_def]

/-- `graftSubtreeAssoc` as a `flatMap` over a range. -/
theorem graftSubtreeAssoc_eq_flatMap {β : Type} (n : ℕ)
    (f : ℕ → List (GacsDayNode × β)) :
    graftSubtreeAssoc n f =
      ((List.range n).reverse).flatMap fun c => liftSubtreeAssoc c (f c) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [graftSubtreeAssoc, ih, List.range_succ, List.reverse_append]
    simp

/-- `graftClientMove` as an explicit list expression. -/
theorem graftClientMove_eq_flatMap (root : ℚ) (b : ℕ) (f : ℕ → ClientMove) :
    graftClientMove root b f =
      ([], root) :: ((List.range b).reverse).flatMap
        fun c => liftSubtreeAssoc c (f c) := by
  rw [graftClientMove, graftSubtreeAssoc_eq_flatMap]

/-- `liftSubtreeAssoc` is primitive recursive, jointly in the index and the
association list. -/
theorem primrec₂_liftSubtreeAssoc :
    Primrec₂ (fun (i : ℕ) (l : ClientMove) => liftSubtreeAssoc i l) := by
  have h : Primrec fun z : ℕ × ClientMove => z.2.map (fun p => (z.1 :: p.1, p.2)) := by
    refine Primrec.list_map Primrec.snd ?_
    exact (Primrec.list_cons.comp (Primrec.fst.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd)).pair (Primrec.snd.comp Primrec.snd)
  exact h.of_eq fun _ => rfl

/-- Computability of `graftClientMove` with computable data. -/
theorem computable_graftClientMove {X : Type} [Primcodable X]
    {froot : X → ℚ} {fb : X → ℕ} {ff : X → ℕ → ClientMove}
    (hroot : Computable froot) (hb : Computable fb)
    (hf : Computable fun z : X × ℕ => ff z.1 z.2) :
    Computable fun x : X => graftClientMove (froot x) (fb x) (ff x) := by
  have hrange : Computable fun x : X => (List.range (fb x)).reverse :=
    (Primrec.list_reverse.comp Primrec.list_range).to_comp.comp hb
  have hbody : Computable₂ fun (x : X) (c : ℕ) => liftSubtreeAssoc c (ff x c) :=
    primrec₂_liftSubtreeAssoc.to_comp.comp Computable.snd hf
  have hflat : Computable fun x : X =>
      ((List.range (fb x)).reverse).flatMap fun c => liftSubtreeAssoc c (ff x c) :=
    computable_list_flatMap hrange hbody
  have hhead : Computable fun x : X => (([], froot x) : GacsDayNode × ℚ) :=
    (Computable.const []).pair hroot
  exact (Computable.list_cons.comp hhead hflat).of_eq fun x =>
    (graftClientMove_eq_flatMap (froot x) (fb x) (ff x)).symm

/-- Computability of the two-level graft with computable data. -/
theorem computable_graftTwoLevel {X : Type} [Primcodable X]
    {froot : X → ℚ} {fb : X → ℕ} {fson : X → ℕ → ℚ} {fg : X → ℕ → ℕ → ClientMove}
    (hroot : Computable froot) (hb : Computable fb)
    (hson : Computable fun z : X × ℕ => fson z.1 z.2)
    (hg : Computable fun z : (X × ℕ) × ℕ => fg z.1.1 z.1.2 z.2) :
    Computable fun x : X => graftTwoLevel (froot x) (fb x) (fson x) (fg x) := by
  have hinner : Computable fun z : X × ℕ =>
      graftClientMove (fson z.1 z.2) (fb z.1) (fg z.1 z.2) :=
    computable_graftClientMove hson (hb.comp Computable.fst) hg
  exact (computable_graftClientMove hroot hb hinner).of_eq fun x => rfl

end Kolmogorov
