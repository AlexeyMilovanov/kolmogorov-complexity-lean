import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderCode

/-!
# A partial oracle and a genuine monadic partial fold

This file contains the two pieces of generic computability engineering needed
to run a controller whose single recursive call is answered by an arbitrary
`Nat.Partrec.Code`:

* `codeEvalPart` -- the *one* partial oracle.  It runs a code on the encoding
  of an input and decodes the returned value.  Nothing here turns a divergent
  or malformed evaluation into a successful answer: divergence stays
  divergence, and an undecodable value makes the whole call diverge.
* `pfoldl` -- a genuine *monadic* left fold over a finite list whose step is
  partial.  A total `List.foldl` cannot iterate a partial step, so this fold,
  its append equation, its total-agreement lemma, and its partial
  recursiveness (`partrec_pfoldl`, proved from `Partrec.nat_rec`) are the
  reusable substitute.

Both are stated for arbitrary primcodable types and mention no game semantics.
-/

namespace Kolmogorov

open Encodable

/-! ### The partial oracle -/

/-- Runs `code` on `Encodable.encode a` and decodes the answer, undefined when the run diverges or
the answer does not decode to `β`. -/
def codeEvalPart {α β : Type} [Primcodable α] [Primcodable β]
    (code : Nat.Partrec.Code) (a : α) : Part β :=
  (code.eval (encode a)).bind fun n => Part.ofOption (decode (α := β) n)

/-- The oracle is partial recursive jointly in the code and the input. -/
theorem partrec₂_codeEvalPart {α β : Type} [Primcodable α] [Primcodable β] :
    Partrec fun x : Nat.Partrec.Code × α => codeEvalPart (β := β) x.1 x.2 := by
  have heval : Partrec fun x : Nat.Partrec.Code × α => x.1.eval (encode x.2) :=
    Nat.Partrec.Code.eval_part.comp Computable.fst
      (Computable.encode.comp Computable.snd)
  have hdec : Partrec fun x : (Nat.Partrec.Code × α) × ℕ =>
      Part.ofOption (decode (α := β) x.2) :=
    Computable.ofOption (Computable.decode.comp Computable.snd)
  exact heval.bind hdec.to₂

/-- On a code that really computes `f`, the oracle converges to `f a`. -/
theorem codeEvalPart_of_codeComputes {α β : Type} [Primcodable α] [Primcodable β]
    {code : Nat.Partrec.Code} {f : α → β} (h : CodeComputes code f) (a : α) :
    codeEvalPart (β := β) code a = Part.some (f a) := by
  simp [codeEvalPart, h a, Encodable.encodek]

/-! ### The monadic partial fold -/

-- The fold itself and its equational lemmas are pure list recursion: the
-- `Primcodable` instances enter only with the computability statements below.
variable {α β σ : Type}

/-- A genuine monadic left fold: the recursion continues only after the partial
step has produced a value. -/
def pfoldl (F : α → σ → β →. σ) (a : α) : σ → List β → Part σ
  | s, [] => Part.some s
  | s, b :: l => (F a s b).bind fun s' => pfoldl F a s' l

/-- Folding a partial step over the empty list returns the starting state. -/
@[simp] theorem pfoldl_nil (F : α → σ → β →. σ) (a : α) (s : σ) :
    pfoldl F a s [] = Part.some s := rfl

/-- Folding a partial step over a cons list applies the step and then folds over the rest. -/
@[simp] theorem pfoldl_cons (F : α → σ → β →. σ) (a : α) (s : σ) (b : β)
    (l : List β) :
    pfoldl F a s (b :: l) = (F a s b).bind fun s' => pfoldl F a s' l := rfl

/-- Folding a partial step over a concatenation is folding over the parts in turn. -/
theorem pfoldl_append (F : α → σ → β →. σ) (a : α) (s : σ) (l₁ l₂ : List β) :
    pfoldl F a s (l₁ ++ l₂) =
      (pfoldl F a s l₁).bind fun s' => pfoldl F a s' l₂ := by
  induction l₁ generalizing s with
  | nil => simp
  | cons b t ih => simp [ih, Part.bind_assoc]

/-- If the partial step always converges to a total step, the partial fold
converges to the total fold. -/
theorem pfoldl_eq_some_foldl {F : α → σ → β →. σ} {a : α} {g : σ → β → σ}
    (h : ∀ s b, F a s b = Part.some (g s b)) (s : σ) (l : List β) :
    pfoldl F a s l = Part.some (l.foldl g s) := by
  induction l generalizing s with
  | nil => simp
  | cons b t ih => simp [h s b, ih]

/-- The `Nat.rec` shape in which `Partrec.nat_rec` delivers the fold. -/
private def pfoldlAux [Inhabited β] (F : α → σ → β →. σ) (a : α) (s : σ)
    (l : List β) : ℕ → Part (σ × List β)
  | 0 => Part.some (s, l)
  | k + 1 =>
      (pfoldlAux F a s l k).bind fun i =>
        (F a i.1 i.2.headI).map fun s' => (s', i.2.tail)

private theorem pfoldlAux_eq [Inhabited β] (F : α → σ → β →. σ) (a : α) :
    ∀ (k : ℕ) (s : σ) (l : List β), k ≤ l.length →
      pfoldlAux F a s l k =
        (pfoldl F a s (l.take k)).map fun s' => (s', l.drop k) := by
  intro k
  induction k with
  | zero => intro s l _; simp [pfoldlAux]
  | succ k ih =>
    intro s l hk
    have hk' : k ≤ l.length := Nat.le_of_succ_le hk
    have hklt : k < l.length := hk
    have hdrop : l.drop k = l[k] :: l.drop (k + 1) := by
      rw [List.drop_eq_getElem_cons hklt]
    have htake : l.take (k + 1) = l.take k ++ [l[k]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hklt]
      simp
    rw [pfoldlAux, ih s l hk', htake, pfoldl_append, Part.bind_map, Part.map_bind]
    congr 1
    funext s'
    rw [hdrop]
    simp only [List.headI_cons, List.tail_cons, pfoldl_cons, pfoldl_nil]
    simp

private theorem pfoldlAux_rec [Inhabited β] (F : α → σ → β →. σ) (x : α × σ × List β)
    (k : ℕ) :
    Nat.rec (motive := fun _ => Part (σ × List β)) (Part.some (x.2.1, x.2.2))
        (fun _ IH => IH.bind fun i => Part.map (fun s' => (s', i.2.tail)) (F x.1 i.1 i.2.headI))
        k =
      pfoldlAux F x.1 x.2.1 x.2.2 k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pfoldlAux, ← ih]

variable [Primcodable α] [Primcodable β] [Primcodable σ]

private theorem partrec_pfoldlAux [Inhabited β] {F : α → σ → β →. σ}
    (hF : Partrec fun x : α × σ × β => F x.1 x.2.1 x.2.2) :
    Partrec fun x : α × σ × List β =>
      pfoldlAux F x.1 x.2.1 x.2.2 x.2.2.length := by
  have hf : Computable fun x : α × σ × List β => x.2.2.length :=
    Computable.list_length.comp (Computable.snd.comp Computable.snd)
  have hg : Partrec fun x : α × σ × List β =>
      (Part.some (x.2.1, x.2.2) : Part (σ × List β)) :=
    Computable.partrec ((Computable.fst.comp Computable.snd).pair
      (Computable.snd.comp Computable.snd))
  have hh : Partrec fun z : (α × σ × List β) × ℕ × (σ × List β) =>
      (F z.1.1 z.2.2.1 z.2.2.2.headI).map fun s' => (s', z.2.2.2.tail) := by
    have harg : Computable fun z : (α × σ × List β) × ℕ × (σ × List β) =>
        ((z.1.1, z.2.2.1, z.2.2.2.headI) : α × σ × β) :=
      (Computable.fst.comp Computable.fst).pair
        ((Computable.fst.comp (Computable.snd.comp Computable.snd)).pair
          (Primrec.list_headI.to_comp.comp
            (Computable.snd.comp (Computable.snd.comp Computable.snd))))
    have hmap : Computable₂ fun (z : (α × σ × List β) × ℕ × (σ × List β)) (s' : σ) =>
        ((s', z.2.2.2.tail) : σ × List β) :=
      (Computable.snd.pair
        (Primrec.list_tail.to_comp.comp
          (Computable.snd.comp (Computable.snd.comp
            (Computable.snd.comp Computable.fst))))).to₂
    exact (hF.comp harg).map hmap
  have := Partrec.nat_rec (f := fun x : α × σ × List β => x.2.2.length)
    (g := fun x : α × σ × List β => (Part.some (x.2.1, x.2.2) : Part (σ × List β)))
    (h := fun (x : α × σ × List β) (p : ℕ × (σ × List β)) =>
      (F x.1 p.2.1 p.2.2.headI).map fun s' => (s', p.2.2.tail))
    hf hg hh.to₂
  exact this.of_eq fun x => pfoldlAux_rec F x x.2.2.length

/-- **The partial fold is partial recursive.** -/
theorem partrec_pfoldl [Inhabited β] {F : α → σ → β →. σ}
    (hF : Partrec fun x : α × σ × β => F x.1 x.2.1 x.2.2) :
    Partrec fun x : α × σ × List β => pfoldl F x.1 x.2.1 x.2.2 := by
  have hmain := partrec_pfoldlAux hF
  have hfst : Computable₂ fun (_ : α × σ × List β) (p : σ × List β) => p.1 :=
    (Computable.fst.comp Computable.snd).to₂
  have := hmain.map hfst
  refine this.of_eq fun x => ?_
  rw [pfoldlAux_eq F x.1 x.2.2.length x.2.1 x.2.2 le_rfl, List.take_length,
    Part.map_map]
  refine Part.map_id' ?_ _
  intro s
  rfl

end Kolmogorov
