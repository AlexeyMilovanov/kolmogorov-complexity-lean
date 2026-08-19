import KolmogorovMathlib.Prefix.TwoStage
import KolmogorovMathlib.AlgorithmicProbability.PairProjection
import KolmogorovMathlib.AlgorithmicStatistics.NormalizedCodedFiniteDistribution

/-!
# Self-delimiting codes for lists of bitstrings

This is the shared encoding API for tuples and lists: every chapter that needs
to put several strings into one context (lists of bounded-complexity strings in
survey §4, tuples in SUV ch. 10) should build on `listCode` instead of nesting
`pairCode` by hand.

`listCode` folds `pairCode` from the right, so the code is self-delimiting: the
decoder `decodeListCode` peels one `pairCode` block per step, consuming the
input in at most `|w|` steps. The round-trip theorem
`decodeListCode_listCode` yields injectivity for free, and both directions are
primitive recursive.

Conventions:

* the empty list is coded by the empty string;
* `listCode (x :: l) = pairCode x (listCode l)` definitionally, so all
  `pairCode` lemmas (`decodeFirst_pairCode`, `decodeSecond_pairCode`, length,
  computability) apply to the head block;
* contexts carrying a list plus auxiliary data should be assembled as
  `pairCode (listCode l) aux`, matching the existing
  `prefixCondComplexityContext` style.
-/

namespace Kolmogorov

open CodedFiniteDistribution in
/-- Re-exported: the pair decoders are primitive recursive. -/
theorem decodeFirst_primrec' : Primrec decodeFirst := decodeFirst_primrec

open CodedFiniteDistribution in
theorem decodeSecond_primrec' : Primrec decodeSecond := decodeSecond_primrec

/-- Self-delimiting code of a list of bitstrings: right fold of `pairCode`. -/
def listCode (l : List BitString) : BitString := l.foldr pairCode []

@[simp] theorem listCode_nil : listCode [] = [] := rfl

@[simp] theorem listCode_cons (x : BitString) (l : List BitString) :
    listCode (x :: l) = pairCode x (listCode l) := rfl

theorem length_listCode_cons (x : BitString) (l : List BitString) :
    (listCode (x :: l)).length = 2 * x.length + 1 + (listCode l).length := by
  simp [listCode_cons, length_pairCode]
  omega

/-! ### The streaming decoder -/

/-- One parsing step: peel one `pairCode` block off the input, appending its
first component to the accumulator. The empty input is a fixed point. -/
def listStep (s : BitString × List BitString) : BitString × List BitString :=
  match s.1 with
  | [] => s
  | _ :: _ => (decodeSecond s.1, s.2 ++ [decodeFirst s.1])

@[simp] theorem listStep_nil (acc : List BitString) :
    listStep (([] : BitString), acc) = ([], acc) := rfl

/-- Decoder for `listCode`: iterate `listStep` for `|w|` steps (each step
consumes at least one input bit, so this fuel always suffices). -/
def decodeListCode (w : BitString) : List BitString :=
  (listStep^[w.length] (w, [])).2

/-- The parsing step consumes a whole `pairCode` block. -/
theorem listStep_pairCode (x r : BitString) (acc : List BitString) :
    listStep (pairCode x r, acc) = (r, acc ++ [x]) := by
  have hstep : listStep (pairCode x r, acc)
      = (decodeSecond (pairCode x r), acc ++ [decodeFirst (pairCode x r)]) := by
    cases hpc : pairCode x r with
    | nil =>
      exfalso
      have hlen := congrArg List.length hpc
      rw [length_pairCode] at hlen
      simp only [List.length_nil] at hlen
      omega
    | cons b w' => rfl
  rw [hstep, decodeFirst_pairCode, decodeSecond_pairCode]

/-- Iterating the parsing step on a coded list, with any sufficient fuel,
recovers the list (appended to the accumulator). -/
theorem listStep_iterate (l : List BitString) :
    ∀ (acc : List BitString) (fuel : ℕ), (listCode l).length ≤ fuel →
      listStep^[fuel] (listCode l, acc) = ([], acc ++ l) := by
  induction l with
  | nil =>
    intro acc fuel _
    have hfix : ∀ n, listStep^[n] (([] : BitString), acc) = ([], acc) := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => rw [Function.iterate_succ_apply, listStep_nil, ih]
    simpa using hfix fuel
  | cons x t ih =>
    intro acc fuel hfuel
    rw [length_listCode_cons] at hfuel
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    rw [Function.iterate_succ_apply, listCode_cons, listStep_pairCode,
      ih (acc ++ [x]) f (by omega)]
    simp

/-- Round trip: decoding inverts encoding. -/
@[simp] theorem decodeListCode_listCode (l : List BitString) :
    decodeListCode (listCode l) = l := by
  unfold decodeListCode
  rw [listStep_iterate l [] (listCode l).length le_rfl]
  simp

/-- The list code is injective. -/
theorem listCode_injective : Function.Injective listCode :=
  Function.LeftInverse.injective decodeListCode_listCode

/-! ### Computability -/

/-- The unary code `natCode` is primitive recursive (exported form of the
computation inside `natCode_computable`). -/
theorem natCode_primrec : Primrec natCode :=
  Primrec.list_append.comp
    (Primrec.list_replicate.comp Primrec.id (Primrec.const true))
    (Primrec.const [false])

/-- The pair code is primitive recursive in both components. -/
theorem pairCode_primrec : Primrec₂ pairCode := by
  have h : Primrec (fun p : BitString × BitString =>
      natCode p.1.length ++ p.1 ++ p.2) :=
    Primrec.list_append.comp
      (Primrec.list_append.comp
        (natCode_primrec.comp (Primrec.list_length.comp Primrec.fst))
        Primrec.fst)
      Primrec.snd
  exact h.of_eq (fun p => rfl)

/-- The list code is primitive recursive. -/
theorem listCode_primrec : Primrec listCode := by
  have h : Primrec (fun l : List BitString =>
      l.foldr (fun x r => pairCode x r) ([] : BitString)) :=
    Primrec.list_foldr Primrec.id (Primrec.const [])
      ((pairCode_primrec.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd)).to₂)
  exact h.of_eq (fun l => rfl)

theorem listCode_computable : Computable listCode :=
  listCode_primrec.to_comp

/-- The parsing step is primitive recursive. -/
theorem listStep_primrec : Primrec listStep := by
  have hcons : Primrec (fun s : BitString × List BitString =>
      ((decodeSecond s.1, s.2 ++ [decodeFirst s.1]) : BitString × List BitString)) :=
    (decodeSecond_primrec'.comp Primrec.fst).pair
      (Primrec.list_append.comp Primrec.snd
        (Primrec.list_cons.comp (decodeFirst_primrec'.comp Primrec.fst)
          (Primrec.const [])))
  have h : Primrec (fun s : BitString × List BitString =>
      (List.casesOn s.1 s
        (fun _ _ => (decodeSecond s.1, s.2 ++ [decodeFirst s.1])) :
        BitString × List BitString)) :=
    Primrec.list_casesOn Primrec.fst Primrec.id
      ((hcons.comp Primrec.fst).to₂)
  exact h.of_eq (fun s => by
    rcases s with ⟨w, acc⟩
    cases w <;> rfl)

/-- The list decoder is primitive recursive. -/
theorem decodeListCode_primrec : Primrec decodeListCode :=
  Primrec.snd.comp
    ((Primrec.nat_iterate' listStep_primrec).comp
      (Primrec.id.pair (Primrec.const [])) Primrec.list_length)

theorem decodeListCode_computable : Computable decodeListCode :=
  decodeListCode_primrec.to_comp

end Kolmogorov
