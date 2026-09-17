import Mathlib.Computability.TuringDegree
import Mathlib.Computability.PartrecCode

/-!
# Oracle computability: typed layer and compositional API

Mathlib 4.33 ships the untyped inductive `Nat.RecursiveIn O : (ℕ →. ℕ) → Prop`
(`Mathlib/Computability/RecursiveIn.lean`) together with `TuringReducible`
(`f ≤ᵀ g`), the typed layer `RecursiveIn O (f : α →. σ)` over `Primcodable`
types, `ComputableIn`, and the basic compositional lemmas (`of_eq`, `subst`,
`mono`, `partrec_of_oracle`, ...).  Until Mathlib 4.33 this file backported that
layer from the `ComputabilityTheory` project (`Oracle/Basic.lean` and its
supporting mathlib-fork layer, Apache 2.0, authors Tanner Duve, Elan Roth,
Alexey Milovanov); the declarations Mathlib now provides are recorded as
deleted in `docs/history/phase24_recut.tsv`, and this file keeps the
compositional API that Mathlib still lacks.

Naming: the typed relation is called `PartrecIn` here; it is definitionally
Mathlib's typed `RecursiveIn` (the name under which the untyped inductive was
known in Mathlib 4.28).

* `PartrecIn O f`: a partial function `f : α →. σ` between `Primcodable`
  types is partial recursive with access to the oracles in `O`.
* `ComputableIn O f`: a total function is computable with access to `O`.
* Compositional API: `pair`, `comp`, `bind`, `map`, `nat_rec`, `rfind`,
  `rfindOpt`, and the conditional `PartrecIn.cond`.
* `haltingChi`: the characteristic partial function of the halting problem
  (the oracle `0′`), and `ComputableInJump` — the notion "computable with
  oracle `0′`" needed by SUV Theorem 37.
-/

open Encodable Part

variable {α β γ δ σ : Type*}

/- The declarations below predate mathlib's typed oracle-computability layer.
They remain visible in source history; the compatibility layer below now uses
mathlib's current implementation. -/

/-
namespace RecursiveIn

variable {O : Set (ℕ →. ℕ)} {f g : ℕ →. ℕ}

/-- Oracle recursiveness only depends on the values of the function. -/
theorem of_eq (hf : RecursiveIn O f) (H : ∀ n, f n = g n) : RecursiveIn O g :=
  (funext H : f = g) ▸ hf

/-- A total function whose values are those of an oracle-recursive partial function is
itself oracle-recursive. -/
theorem of_eq_tot {g : ℕ → ℕ} (hf : RecursiveIn O f) (H : ∀ n, g n ∈ f n) :
    RecursiveIn O (g : ℕ →. ℕ) :=
  of_eq hf fun n => eq_some_iff.2 (H n)

/-- If every element of `O` is `RecursiveIn O'`, then any function which is
`RecursiveIn O` is also `RecursiveIn O'`. -/
theorem subst {O O'} (hf : RecursiveIn O f)
    (hO : ∀ g ∈ O, RecursiveIn O' g) : RecursiveIn O' f := by
  induction hf with
  | zero | succ | left | right => constructor
  | oracle g hg => exact hO g hg
  | pair _ _ ihf ihg => exact .pair ihf ihg
  | comp _ _ ihf ihg => exact .comp ihf ihg
  | prec _ _ ihf ihg => exact .prec ihf ihg
  | rfind _ ihf => exact .rfind ihf

/-- Monotonicity of `RecursiveIn` with respect to oracle sets. -/
theorem mono {O₁ O₂} (hsub : O₁ ⊆ O₂) (hf : RecursiveIn O₁ f) :
    RecursiveIn O₂ f :=
  hf.subst fun g hg => .oracle g (hsub hg)

/-- If every function in `O` is partial recursive, then a function which is
`RecursiveIn O` is also partial recursive. -/
theorem partrec_of_oracle (hO : ∀ g ∈ O, Nat.Partrec g)
    (hf : RecursiveIn O f) : Nat.Partrec f := by
  induction hf with
  | zero | succ | left | right => constructor
  | oracle g hg => exact hO g hg
  | pair _ _ ih₁ ih₂ => exact .pair ih₁ ih₂
  | comp _ _ ih₁ ih₂ => exact .comp ih₁ ih₂
  | prec _ _ ih₁ ih₂ => exact .prec ih₁ ih₂
  | rfind _ ih => exact .rfind ih

end RecursiveIn

/-- Every partial recursive function is recursive in every oracle set. -/
theorem Nat.Partrec.recursiveIn {O : Set (ℕ →. ℕ)} {f : ℕ →. ℕ}
    (pF : Nat.Partrec f) : RecursiveIn O f := by
  induction pF with
  | zero | succ | left | right => constructor
  | pair _ _ ih₁ ih₂ => exact .pair ih₁ ih₂
  | comp _ _ ih₁ ih₂ => exact .comp ih₁ ih₂
  | prec _ _ ih₁ ih₂ => exact .prec ih₁ ih₂
  | rfind _ ih => exact .rfind ih

/-- Every primitive recursive function is recursive in any oracle. -/
theorem Nat.Primrec.recursiveIn {O : Set (ℕ →. ℕ)} {f : ℕ → ℕ}
    (hf : Nat.Primrec f) : RecursiveIn O (f : ℕ →. ℕ) :=
  (Nat.Partrec.of_primrec hf).recursiveIn

-/

/-- A partial function `f : α →. σ` between `Primcodable` types is partial
recursive in the oracle set `O` if its numeric encoding is `RecursiveIn O`. -/
def PartrecIn [Primcodable α] [Primcodable σ] (O : Set (ℕ →. ℕ))
    (f : α →. σ) : Prop :=
  RecursiveIn O f

/-- A binary partial function is `PartrecIn O` if the uncurried form is. -/
def PartrecIn₂ [Primcodable α] [Primcodable β] [Primcodable σ]
    (O : Set (ℕ →. ℕ)) (f : α → β →. σ) : Prop :=
  PartrecIn O fun p : α × β => f p.1 p.2

/-- For functions on the naturals, oracle partial recursiveness coincides with oracle
recursiveness. -/
lemma PartrecIn.iff_nat {O : Set (ℕ →. ℕ)} {f : ℕ →. ℕ} :
    PartrecIn O f ↔ Nat.RecursiveIn O f :=
  RecursiveIn.iff_nat

section Transfer

variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable σ]
variable {O : Set (ℕ →. ℕ)}

/-- Every partial recursive function is `PartrecIn` any oracle set. -/
lemma Partrec.partrecIn {f : α →. σ} (hf : Partrec f) : PartrecIn O f :=
  hf.recursiveIn


nonrec theorem Computable₂.computableIn₂ {f : α → β → σ} (hf : Computable₂ f) :
    ComputableIn₂ O f :=
  hf.computableIn


/-- A function computable in an oracle is partial recursive in it. -/
protected theorem ComputableIn.partrecIn {f : α → σ} (hf : ComputableIn O f) :
    PartrecIn O (f : α →. σ) := hf

/-- A binary function computable in an oracle is partial recursive in it. -/
protected theorem ComputableIn₂.partrecIn₂ {f : α → β → σ}
    (hf : ComputableIn₂ O f) : PartrecIn₂ O fun a => (f a : β →. σ) := hf

end Transfer

namespace PartrecIn

variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable σ]
variable {O : Set (ℕ →. ℕ)}

/-- Oracle partial recursiveness only depends on the values of the function. -/
lemma of_eq {f g : α →. σ} (hf : PartrecIn O f) (H : ∀ x, f x = g x) :
    PartrecIn O g :=
  (funext H : f = g) ▸ hf

/-- A total function whose values are those of an oracle partial recursive function is
itself partial recursive in the oracle. -/
lemma of_eq_tot {f : α →. σ} {g : α → σ} (hf : PartrecIn O f)
    (H : ∀ n, g n ∈ f n) : PartrecIn O (g : α →. σ) :=
  of_eq hf fun n => eq_some_iff.2 (H n)

/-- Each member of the oracle is partial recursive in it. -/
lemma oracle : ∀ g ∈ O, PartrecIn O g :=
  fun g hg => iff_nat.2 (.oracle g hg)

/-- The total function returning its argument is partial recursive in any oracle. -/
protected theorem some : PartrecIn O (@Part.some α) :=
  Partrec.some.partrecIn

/-- The nowhere-defined function is partial recursive in any oracle. -/
protected theorem none : PartrecIn O fun _ : α => (Part.none : Part σ) :=
  Partrec.none.partrecIn

end PartrecIn

namespace Nat.RecursiveIn

variable {O : Set (ℕ →. ℕ)}

/-- Primitive recursion on the value of an oracle-recursive function preserves oracle
recursiveness. -/
theorem prec' {f g h : ℕ →. ℕ} (hf : Nat.RecursiveIn O f) (hg : Nat.RecursiveIn O g)
    (hh : Nat.RecursiveIn O h) :
    Nat.RecursiveIn O fun a => (f a).bind fun n => Nat.rec (g a)
      (fun y IH => do let i ← IH; h (Nat.pair a (Nat.pair y i))) n :=
  ((hg.prec hh).comp ((Nat.Partrec.some.recursiveIn).pair hf)).of_eq fun a => by
    simp [Seq.seq]

end Nat.RecursiveIn

section API

variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable δ]
variable [Primcodable σ]
variable {O : Set (ℕ →. ℕ)}

namespace ComputableIn

/-- Oracle computability only depends on the values of the function. -/
theorem of_eq {f g : α → σ} (hf : ComputableIn O f) (H : ∀ n, f n = g n) :
    ComputableIn O g :=
  (funext H : f = g) ▸ hf

/-- A function of a pair that is computable in an oracle is computable in it as a binary
function. -/
theorem to₂ {f : α × β → σ} (hf : ComputableIn O f) :
    ComputableIn₂ O fun a b => f (a, b) :=
  hf.of_eq fun ⟨_, _⟩ => rfl

nonrec theorem pair {f : α → β} {g : α → γ} (hf : ComputableIn O f)
    (hg : ComputableIn O g) : ComputableIn O fun a => (f a, g a) :=
  (hf.pair hg).of_eq fun n => by cases e : decode (α := α) n <;> simp [Seq.seq]

/-
/-- Constant functions are computable in any oracle. -/
protected theorem const (s : σ) : ComputableIn O fun _ : α => s :=
  (Primrec.const s).computableIn

/-- The identity is computable in any oracle. -/
protected theorem id : ComputableIn O (@id α) :=
  Primrec.id.computableIn

/-- The first projection is computable in any oracle. -/
protected theorem fst : ComputableIn O (@Prod.fst α β) :=
  Primrec.fst.computableIn

/-- The second projection is computable in any oracle. -/
protected theorem snd : ComputableIn O (@Prod.snd α β) :=
  Primrec.snd.computableIn

-/
end ComputableIn

namespace PartrecIn

/-- A partial function of a pair that is partial recursive in an oracle is partial
recursive in it as a binary function. -/
theorem to₂ {f : α × β →. σ} (hf : PartrecIn O f) :
    PartrecIn₂ O fun a b => f (a, b) :=
  hf.of_eq fun ⟨_, _⟩ => rfl

/-- Oracle partial recursiveness is preserved by binding. -/
protected theorem bind {f : α →. β} {g : α → β →. σ} (hf : PartrecIn O f)
    (hg : PartrecIn₂ O g) : PartrecIn O fun a => (f a).bind (g a) :=
  (Nat.RecursiveIn.comp hg ((Nat.Partrec.some.recursiveIn).pair hf)).of_eq fun n => by
    cases e : decode (α := α) n
    · simp only [Seq.seq, Part.bind_eq_bind, Part.bind_none, Part.bind_some, Part.coe_none,
        Part.map_eq_map, Part.map_none, Part.map_some, decode_prod_val]
    · rename_i a
      simp only [Seq.seq, e, encodek, Nat.unpair_pair, Option.bind_some, Option.map_some,
        Part.bind_eq_bind, Part.bind_map, Part.bind_some, Part.coe_some, Part.map_eq_map,
        Part.map_some, decode_prod_val]
      exact (Part.map_bind (fun y => g a y) (f a) encode).symm

/-- Oracle partial recursiveness is preserved by postcomposition with an oracle-computable
function. -/
theorem map {f : α →. β} {g : α → β → σ} (hf : PartrecIn O f)
    (hg : ComputableIn₂ O g) : PartrecIn O fun a => (f a).map (g a) :=
  (PartrecIn.bind hf (ComputableIn₂.partrecIn₂ hg)).of_eq fun a => by
    have hcoe : (g a : β →. σ) = fun y => Part.some (g a y) :=
      funext fun y => PFun.coe_val _ _
    rw [hcoe]
    exact Part.bind_some_eq_map (g a) (f a)

nonrec theorem comp {f : β →. σ} {g : α → β} (hf : PartrecIn O f)
    (hg : ComputableIn O g) : PartrecIn O fun a => f (g a) :=
  (hf.comp hg).of_eq fun n => by cases e : decode (α := α) n <;> simp [encodek]

/-- Primitive recursion with an oracle-computable step preserves oracle partial
recursiveness. -/
theorem nat_rec {f : α → ℕ} {g : α →. σ} {h : α → ℕ × σ →. σ}
    (hf : ComputableIn O f) (hg : PartrecIn O g) (hh : PartrecIn₂ O h) :
    PartrecIn O fun a => Nat.rec (g a)
      (fun y IH => IH.bind fun i => h a (y, i)) (f a) :=
  (Nat.RecursiveIn.prec' hf hg hh).of_eq fun n => by
    cases e : decode (α := α) n <;> simp [e, Part.bind_none]
    induction f _ <;> simp_all

/-- Unbounded search over an oracle partial recursive predicate is partial recursive in the
oracle. -/
theorem rfind {p : α → ℕ →. Bool} (hp : PartrecIn₂ O p) :
    PartrecIn O fun a => Nat.rfind (p a) :=
  (Nat.RecursiveIn.rfind <|
        hp.map (((Primrec.dom_bool fun b => cond b 0 1).comp
          Primrec.snd).to₂.to_comp.computableIn₂ (O := O))).of_eq
    fun n => by
      cases e : decode (α := α) n
      · simp only [decode_prod_val, Nat.unpair_pair, decode_nat, Option.map_some, Part.map_eq_map,
        Part.coe_none, Part.bind_none, e, Option.bind_none, Part.map_none]
        exact Nat.rfind_zero_none _ rfl
      · simp only [decode_prod_val, decode_nat, Option.map_some, Nat.unpair_pair,
          map_eq_map, e, Option.bind_some, coe_some, bind_some]
        refine congrArg Nat.rfind (funext fun k => ?_)
        simp only [Part.map_map]
        exact Part.map_id' (fun b => by cases b <;> rfl) _

end PartrecIn

namespace PartrecIn₂

/-- Oracle partial recursiveness is preserved by composition with oracle-computable
arguments. -/
theorem comp {f : β → γ →. σ} {g : α → β} {h : α → γ} (hf : PartrecIn₂ O f)
    (hg : ComputableIn O g) (hh : ComputableIn O h) :
    PartrecIn O fun a => f (g a) (h a) := by
  have huncurried : PartrecIn O fun p : β × γ => f p.1 p.2 := hf
  exact huncurried.comp (hg.pair hh)

/-- Composition of a binary oracle partial recursive function with two oracle-computable
binary functions is partial recursive in the oracle. -/
theorem comp₂ {f : γ → δ →. σ} {g : α → β → γ} {h : α → β → δ}
    (hf : PartrecIn₂ O f) (hg : ComputableIn₂ O g) (hh : ComputableIn₂ O h) :
    PartrecIn₂ O fun a b => f (g a b) (h a b) := by
  have huncurried : PartrecIn O fun p : α × β => f (g p.1 p.2) (h p.1 p.2) :=
    comp hf hg hh
  exact huncurried

end PartrecIn₂

namespace ComputableIn

nonrec theorem comp {f : β → σ} {g : α → β} (hf : ComputableIn O f)
    (hg : ComputableIn O g) : ComputableIn O fun a => f (g a) :=
  (PartrecIn.comp hf.partrecIn hg).of_eq fun _ => rfl

/-- Composition of an oracle-computable function with an oracle-computable binary function
is computable in the oracle. -/
theorem comp₂ {f : γ → σ} {g : α → β → γ} (hf : ComputableIn O f)
    (hg : ComputableIn₂ O g) : ComputableIn₂ O fun a b => f (g a b) :=
  hf.comp hg

/-- Total primitive recursion preserves relative computability. -/
theorem nat_rec {f : α → ℕ} {g : α → σ} {h : α → ℕ × σ → σ}
    (hf : ComputableIn O f) (hg : ComputableIn O g) (hh : ComputableIn₂ O h) :
    ComputableIn O fun a =>
      @Nat.rec (fun _ => σ) (g a) (fun y ih => h a (y, ih)) (f a) := by
  refine PartrecIn.of_eq_tot
    (g := fun a => @Nat.rec (fun _ => σ) (g a) (fun y ih => h a (y, ih)) (f a))
    (PartrecIn.nat_rec hf hg.partrecIn hh.partrecIn₂) ?_
  intro a
  change
    @Nat.rec (fun _ => σ) (g a) (fun y ih => h a (y, ih)) (f a) ∈
    @Nat.rec (fun _ => Part σ) (Part.some (g a))
      (fun y IH => IH.bind fun i => Part.some (h a (y, i))) (f a)
  generalize hn : f a = n
  clear hn
  induction n with
  | zero => simp
  | succ n ih =>
    simp only
    rw [Part.mem_bind_iff]
    exact ⟨_, ih, by simp⟩

end ComputableIn

namespace ComputableIn₂

/-- A binary function is computable in an oracle as soon as its uncurried form is. -/
theorem mk {f : α → β → σ} (hf : ComputableIn O fun p : α × β => f p.1 p.2) :
    ComputableIn₂ O f := hf

nonrec theorem comp {f : β → γ → σ} {g : α → β} {h : α → γ}
    (hf : ComputableIn₂ O f) (hg : ComputableIn O g) (hh : ComputableIn O h) :
    ComputableIn O fun a => f (g a) (h a) :=
  hf.comp (hg.pair hh)

end ComputableIn₂

namespace PartrecIn

/-- Case distinction on a natural number with an oracle partial recursive successor branch
is partial recursive in the oracle. -/
theorem nat_casesOn_right {f : α → ℕ} {g : α → σ} {h : α → ℕ →. σ}
    (hf : ComputableIn O f) (hg : ComputableIn O g) (hh : PartrecIn₂ O h) :
    PartrecIn O fun a => Nat.casesOn (f a) (Part.some (g a)) (h a) :=
  (nat_rec hf hg (PartrecIn₂.comp hh ComputableIn.fst
      ((Computable.pred.computableIn).comp (hf.comp ComputableIn.fst))).to₂).of_eq
    fun a => by
      dsimp only
      rcases f a with - | n
      · simp
      · simp only [Nat.pred_succ]
        refine Part.ext fun b => ⟨fun H => ?_, fun H => ?_⟩
        · rcases Part.mem_bind_iff.1 H with ⟨_, _, h₂⟩
          exact h₂
        · have hD : ∀ m, (Nat.rec (motive := fun _ => Part σ)
              (Part.some (g a)) (fun _ IH => IH.bind fun _ => h a n) m).Dom := by
            intro m; induction m <;> simp [*, H.fst]
          exact ⟨⟨hD n, H.fst⟩, H.snd⟩

/-- The `Nat.rfind`-based decoder: searching for the encoding of the value of
`v` and decoding recovers `v` itself.  Correctness core of `PartrecIn.cond`. -/
private lemma rfind_encode_bind_decode (v : Part σ) :
    ((Nat.rfind (show ℕ →. Bool from fun k => v.map fun s => decide (encode s = k))).bind
      fun k => Part.ofOption (decode (α := σ) k)) = v := by
  rcases Part.eq_none_or_eq_some v with rfl | ⟨s, rfl⟩
  · rw [Nat.rfind_zero_none _ (by simp)]
    simp
  · refine Part.eq_some_iff.2 (Part.mem_bind_iff.2 ⟨encode s, ?_, ?_⟩)
    · exact Nat.mem_rfind.2 ⟨by simp, fun {m} hm => by simp [Nat.ne_of_gt hm]⟩
    · simp [encodek]

/-- Branch selection with a **total** default branch. -/
theorem cond_some {c : α → Bool} {f : α →. σ} {g : α → σ} (hc : ComputableIn O c)
    (hf : PartrecIn O f) (hg : ComputableIn O g) :
    PartrecIn O fun a => cond (c a) (f a) (Part.some (g a)) := by
  have hcasesOn := nat_casesOn_right (O := O) (f := fun a => encode (c a))
    (g := g) (h := fun a _ => f a)
    ((Computable.encode.computableIn).comp hc) hg ((hf.comp ComputableIn.fst).to₂)
  refine hcasesOn.of_eq fun a => ?_
  cases h : c a <;> simp [Encodable.encode_true, Encodable.encode_false]

/-- Relativized `Partrec.cond`: the conditional of two functions `PartrecIn O`,
with a computable-in-`O` guard, is `PartrecIn O`.  Proved by unbounded search
over the encoded result, avoiding relativized code evaluation. -/
protected theorem cond {c : α → Bool} {f g : α →. σ} (hc : ComputableIn O c)
    (hf : PartrecIn O f) (hg : PartrecIn O g) :
    PartrecIn O fun a => cond (c a) (f a) (g a) := by
  have heq : Computable₂ fun (p : α × ℕ) (s : σ) => if encode s = p.2 then (0 : ℕ) else 1 :=
    Primrec₂.to_comp <| Primrec.ite
      (PrimrecRel.comp Primrec.eq (Primrec.encode.comp Primrec.snd)
        (Primrec.snd.comp Primrec.fst))
      (Primrec.const 0) (Primrec.const 1)
  set t : α × ℕ →. ℕ := fun p =>
    cond (c p.1) ((f p.1).map fun s => if encode s = p.2 then 0 else 1) (Part.some 1)
    with ht_def
  set u : α × ℕ →. ℕ := fun p =>
    cond (!c p.1) ((g p.1).map fun s => if encode s = p.2 then 0 else 1) (Part.some 1)
    with hu_def
  have ht : PartrecIn O t :=
    cond_some (hc.comp ComputableIn.fst)
      ((hf.comp ComputableIn.fst).map heq.computableIn₂)
      ((Computable.const 1).computableIn)
  have hu : PartrecIn O u :=
    cond_some (((Primrec.not.to_comp).computableIn).comp (hc.comp ComputableIn.fst))
      ((hg.comp ComputableIn.fst).map heq.computableIn₂)
      ((Computable.const 1).computableIn)
  have hmul : ComputableIn₂ O fun (p : (α × ℕ) × ℕ) (y : ℕ) => p.2 * y :=
    Computable₂.computableIn₂ <| Primrec₂.to_comp <|
      Primrec.nat_mul.comp (Primrec.snd.comp Primrec.fst) Primrec.snd
  have hcmp : PartrecIn O fun p : α × ℕ => (t p).bind fun x => (u p).map fun y => x * y :=
    PartrecIn.bind ht ((hu.comp ComputableIn.fst).map hmul).to₂
  have hzero : ComputableIn₂ O fun (_ : α × ℕ) (x : ℕ) => decide (x = 0) :=
    Computable₂.computableIn₂ <| Primrec₂.to_comp <| Primrec.to₂ <|
      PrimrecPred.decide (PrimrecRel.comp Primrec.eq Primrec.snd (Primrec.const 0))
  have hres : PartrecIn O fun a =>
      (Nat.rfind fun k =>
        (((t (a, k)).bind fun x => (u (a, k)).map fun y => x * y).map
          fun x => decide (x = 0))).bind
        fun k => Part.ofOption (decode (α := σ) k) :=
    PartrecIn.bind (rfind (PartrecIn.map hcmp hzero).to₂)
      (((Computable.ofOption (Computable.decode.comp Computable.snd)).partrecIn).to₂
        (O := O))
  refine hres.of_eq fun a => ?_
  cases hca : c a
  · have harg : (fun k =>
        (((t (a, k)).bind fun x => (u (a, k)).map fun y => x * y).map
          fun x => decide (x = 0)) : ℕ →. Bool)
        = fun k => (g a).map fun s => decide (encode s = k) := by
      refine funext fun k => ?_
      simp only [ht_def, hu_def, hca, cond_false, Bool.not_false, cond_true,
        Part.bind_some, Part.map_map]
      refine Part.ext fun b => ?_
      simp only [Part.mem_map_iff, Function.comp_apply]
      constructor <;> rintro ⟨s, hs, rfl⟩ <;>
        exact ⟨s, hs, by by_cases h : encode s = k <;> simp [h]⟩
    rw [harg, rfind_encode_bind_decode]
    simp
  · have harg : (fun k =>
        (((t (a, k)).bind fun x => (u (a, k)).map fun y => x * y).map
          fun x => decide (x = 0)) : ℕ →. Bool)
        = fun k => (f a).map fun s => decide (encode s = k) := by
      refine funext fun k => ?_
      simp only [ht_def, hu_def, hca, cond_true, Bool.not_true, cond_false,
        Part.map_some, Part.bind_some_eq_map, Part.map_map]
      refine Part.ext fun b => ?_
      simp only [Part.mem_map_iff, Function.comp_apply]
      constructor <;> rintro ⟨s, hs, rfl⟩ <;>
        exact ⟨s, hs, by by_cases h : encode s = k <;> simp [h]⟩
    rw [harg, rfind_encode_bind_decode]
    simp

/-- Searching for the first defined value of an oracle-computable family of options is
partial recursive in the oracle. -/
theorem rfindOpt {f : α → ℕ → Option σ} (hf : ComputableIn₂ O f) :
    PartrecIn O fun a => Nat.rfindOpt (f a) :=
  ((rfind ((Primrec.option_isSome.to_comp.computableIn (O := O)).comp₂
      hf).partrecIn₂).bind
    (((Computable.ofOption Computable.id).partrecIn (O := O)).comp hf).to₂).of_eq
    fun _ => rfl

end PartrecIn

end API

/-! ## The halting oracle `0′` -/

namespace Kolmogorov

open scoped Computability

/-- The halting set `0′`: indices `n` such that the `n`-th partial recursive
function halts on input `n`. -/
def haltingSet (n : ℕ) : Prop :=
  ((Denumerable.ofNat Nat.Partrec.Code n).eval n).Dom

open Classical in
/-- The characteristic partial function of the halting set: the oracle `0′`.
It is total (defined via classical choice); it is of course not computable. -/
noncomputable def haltingChi : ℕ →. ℕ := fun n =>
  Part.some (if haltingSet n then 1 else 0)

/-- A total function is `0′`-computable if it is computable with the halting
oracle.  This is the interface required by SUV Theorem 37 (existence of a
`0′`-computable Martin-Löf random sequence). -/
def ComputableInJump [Primcodable α] [Primcodable σ] (f : α → σ) : Prop :=
  ComputableIn {haltingChi} f

/-- Plain computable functions are `0′`-computable. -/
theorem Computable.computableInJump [Primcodable α] [Primcodable σ]
    {f : α → σ} (hf : Computable f) : ComputableInJump f :=
  hf.computableIn

/-- The halting oracle itself is `0′`-computable (as a partial function). -/
theorem partrecIn_haltingChi : PartrecIn {haltingChi} haltingChi :=
  PartrecIn.oracle _ rfl

/-- `0′`-computability is closed under composition. -/
theorem ComputableInJump.comp [Primcodable α] [Primcodable β] [Primcodable σ]
    {f : β → σ} {g : α → β} (hf : ComputableInJump f) (hg : ComputableInJump g) :
    ComputableInJump fun a => f (g a) :=
  ComputableIn.comp hf hg

end Kolmogorov
