import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderCode
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTail

/-!
# The code transformer of the ladder, from an oracle procedure (s-m-n)

`grayLadderStep_tail_components` (in `GacsDayLadderStepClosure`) asks, besides
the semantic transformer `F` of family strategy schemes, for a *computable
transformer of codes* `G` with

```
CodeComputesScheme code sigma → CodeComputesScheme (G k code) (F k sigma).
```

That is not the shape in which such a transformer is ever constructed. What one
constructs is a single partial recursive *procedure*

```
Phi : stage × code × scheme input →. ℕ
```

which, whenever the code it is handed computes `sigma`, computes the value of
`F k sigma` at the given input -- the procedure calls the code as a subroutine,
through the universal function `Nat.Partrec.Code.eval_part`.

This file closes the gap once and for all, by the s-m-n theorem
(`Nat.Partrec.Code.curry`): from such a procedure the code transformer `G` is
obtained by currying the stage and the code into a code, and currying is
primitive recursive, so `G` is computable.

The three results:

* `exists_codeTransformer_of_partrec` -- the general s-m-n statement, for an
  arbitrary primcodable input type;
* `exists_codeStep_of_partrec` -- its specialisation to family strategy
  schemes, producing exactly the code conjunct of the ladder leaf;
* `grayLadderStep_tail_components_of_partrec` -- the ladder leaf itself,
  reduced to: a transformer `F`, a partial recursive procedure for it, and the
  semantic rung step.

Nothing here presupposes the construction: the procedure is data that Day's
half-step has to produce, and its defining property mentions the *real* `F`.
-/

namespace Kolmogorov

open Encodable

/-- **s-m-n for code transformers.** A partial recursive procedure in a stage,
a code and an input yields a computable transformer of codes: currying the
stage and the code into the procedure's own code is primitive recursive
(`Nat.Partrec.Code.primrec₂_curry`). -/
theorem exists_codeTransformer_of_partrec {α : Type} [Primcodable α]
    {Phi : ℕ × Nat.Partrec.Code × α →. ℕ} (hPhi : Partrec Phi) :
    ∃ G : ℕ → Nat.Partrec.Code → Nat.Partrec.Code, Computable₂ G ∧
      ∀ (k : ℕ) (c : Nat.Partrec.Code) (a : α), (G k c).eval (encode a) = Phi (k, c, a) := by
  have hnat : Nat.Partrec fun n => Part.bind (decode (α := ℕ × Nat.Partrec.Code × α) n)
      fun x => (Phi x).map encode := hPhi
  obtain ⟨d, hd⟩ := Nat.Partrec.Code.exists_code.mp hnat
  refine ⟨fun k c => Nat.Partrec.Code.curry (Nat.Partrec.Code.curry d k) (encode c), ?_, ?_⟩
  · have hcurry : Computable₂ Nat.Partrec.Code.curry :=
      Primrec₂.to_comp Nat.Partrec.Code.primrec₂_curry
    exact hcurry.comp (hcurry.comp (Computable.const d) Computable.fst)
      (Computable.encode.comp Computable.snd)
  · intro k c a
    rw [Nat.Partrec.Code.eval_curry, Nat.Partrec.Code.eval_curry, show d.eval = _ from hd]
    have hpair : (encode (k, c, a)) = Nat.pair k (Nat.pair (encode c) (encode a)) := rfl
    rw [← hpair]
    simpa using Part.map_id' (f := (Encodable.encode : ℕ → ℕ)) (fun _ => rfl) (Phi (k, c, a))

/-- **The code conjunct of the ladder leaf, from an oracle procedure.** A
partial recursive procedure which, on any code for `sigma`, returns the values
of `F k sigma`, yields a computable code transformer tracking `F`. -/
theorem exists_codeStep_of_partrec
    (F : ℕ → FamilyStrategyScheme → FamilyStrategyScheme)
    {Phi : ℕ × Nat.Partrec.Code × SchemeInput →. ℕ} (hPhi : Partrec Phi)
    (hspec : ∀ (k : ℕ) (code : Nat.Partrec.Code) (sigma : FamilyStrategyScheme),
      CodeComputesScheme code sigma → ∀ p : SchemeInput,
        Phi (k, code, p) =
          Part.some (@encode FamilyClientMove Primcodable.toEncodable
            (F k sigma p.1.1 p.1.2 p.2.1 p.2.2.1 p.2.2.2))) :
    ∃ G : ℕ → Nat.Partrec.Code → Nat.Partrec.Code, Computable₂ G ∧
      ∀ (k : ℕ) (code : Nat.Partrec.Code) (sigma : FamilyStrategyScheme),
        CodeComputesScheme code sigma → CodeComputesScheme (G k code) (F k sigma) := by
  obtain ⟨G, hG, heval⟩ := exists_codeTransformer_of_partrec hPhi
  refine ⟨G, hG, fun k code sigma hcode p => ?_⟩
  simpa only [heval] using hspec k code sigma hcode p

/-- **The remaining ladder leaf, reduced to a procedure plus the rung step.**

`grayLadderStep_tail_components` is exactly this statement with the code
transformer replaced by the partial recursive procedure `Phi` that a half-step
construction actually produces. -/
theorem grayLadderStep_tail_components_of_partrec
    (F : ℕ → FamilyStrategyScheme → FamilyStrategyScheme)
    {Phi : ℕ × Nat.Partrec.Code × SchemeInput →. ℕ} (hPhi : Partrec Phi)
    (hspec : ∀ (k : ℕ) (code : Nat.Partrec.Code) (sigma : FamilyStrategyScheme),
      CodeComputesScheme code sigma → ∀ p : SchemeInput,
        Phi (k, code, p) =
          Part.some (@encode FamilyClientMove Primcodable.toEncodable
            (F k sigma p.1.1 p.1.2 p.2.1 p.2.2.1 p.2.2.2)))
    (c : ℕ) (hc : 3 ≤ c)
    (hRung : ∀ (k L B : ℕ) (sigma : FamilyStrategyScheme),
      B ≤ max 2 (c * (k + 3) * 2 ^ L) → GrayRung (k + 2) L B sigma →
      GrayRung (k + 3) (c * (k + 3) ^ 2 * L + c * (k + 3))
        (max 2 (c * (k + 3) *
          2 ^ (c * (k + 3) ^ 2 * L + c * (k + 3)))) (F (k + 2) sigma)) :
    ∃ (F' : ℕ → FamilyStrategyScheme → FamilyStrategyScheme)
      (G : ℕ → Nat.Partrec.Code → Nat.Partrec.Code) (c' : ℕ),
    3 ≤ c' ∧ Computable₂ G ∧
    (∀ (k : ℕ) (code : Nat.Partrec.Code) (sigma : FamilyStrategyScheme),
      CodeComputesScheme code sigma → CodeComputesScheme (G k code) (F' k sigma)) ∧
    (∀ (k L B : ℕ) (sigma : FamilyStrategyScheme),
      B ≤ max 2 (c' * (k + 3) * 2 ^ L) → GrayRung (k + 2) L B sigma →
      GrayRung (k + 3) (c' * (k + 3) ^ 2 * L + c' * (k + 3))
        (max 2 (c' * (k + 3) *
          2 ^ (c' * (k + 3) ^ 2 * L + c' * (k + 3)))) (F' (k + 2) sigma)) := by
  obtain ⟨G, hG, hGcode⟩ := exists_codeStep_of_partrec F hPhi hspec
  exact ⟨F, G, c, hc, hG, hGcode, hRung⟩

end Kolmogorov
