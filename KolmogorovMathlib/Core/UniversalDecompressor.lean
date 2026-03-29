import Mathlib.Computability.Partrec
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Encoding
import Mathlib.Data.List.Basic
import Mathlib.Data.ENat.Basic
import KolmogorovMathlib.Core.Basic

/-!
# Universal Decompressor Construction

This module defines the universal decompressor `universalDecompressor` and
proves its computability. It uses unary prefix coding to safely interleave
the program's code index with its actual input.
-/

namespace Kolmogorov

/-! ### Unary Prefixes -/

/-- Unary prefix coding: `n` is encoded as `n` ones followed by a zero. -/
def unaryPrefix (n : ℕ) : List Bool :=
  List.replicate n true ++ [false]

@[simp] lemma length_unaryPrefix (n : ℕ) : (unaryPrefix n).length = n + 1 := by simp [unaryPrefix]

@[simp] lemma takeWhile_unaryPrefix (n : ℕ) (p : List Bool) :
    ((unaryPrefix n ++ p).takeWhile id).length = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ((unaryPrefix n ++ p).takeWhile id).length + 1 = n + 1
    omega

@[simp] lemma drop_unaryPrefix (n : ℕ) (p : List Bool) :
    (unaryPrefix n ++ p).drop (n + 1) = p := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (unaryPrefix n ++ p).drop (n + 1) = p
    exact ih

/-! ### Universal Decompressor -/

/-- The Conditional Universal Decompressor. It parses the unary prefix to find
    the simulated machine's index, and then simulates it on the rest of the tape. -/
def universalDecompressor : Map := fun p =>
  let s := p.1
  let y := p.2
  let i := (s.takeWhile id).length
  match (Encodable.decode i : Option Nat.Partrec.Code) with
  | none => Part.none
  | some code =>
      (code.eval (Encodable.encode (s.drop (i + 1), y))).map
        (fun r => (Encodable.decode r : Option BitString).getD [])

/-- Simulation lemma: `U(prefix(i) ++ p, y) = Decompressor_i(p, y)`. -/
lemma universalSimulation (code : Nat.Partrec.Code) (p y : BitString) :
    universalDecompressor (unaryPrefix (Encodable.encode code) ++ p, y) =
    (code.eval (Encodable.encode (p, y))).map
      (fun r => (Encodable.decode r : Option BitString).getD []) := by
  simp [universalDecompressor]

/-! ### Computability of the Universal Decompressor -/

/-- A total function that parses the tape from a natural number. -/
def parseTapeNat (n : ℕ) : ℕ × ℕ :=
  Option.casesOn (Encodable.decode n : Option BitString)
    (0, 0)
    (fun s =>
      let i := (s.takeWhile id).length
      (i, Encodable.encode (s.drop (i + 1))))

/-- The tape parser is primitive recursive. -/
lemma primrecParseTapeNat : Primrec parseTapeNat := by
  unfold parseTapeNat
  have h_twl : Primrec (fun s : List Bool => (s.takeWhile id).length) :=
    Primrec.list_length.comp (Primrec.list_takeWhile Primrec.id)
  exact Primrec.option_casesOn Primrec.decode (Primrec.const (0, 0))
    (Primrec.pair (h_twl.comp Primrec.snd)
      (Primrec.encode.comp (Primrec₂.comp Primrec.list_drop
        (Primrec.succ.comp (h_twl.comp Primrec.snd)) Primrec.snd)))

/-- The core numerical universal decompressor. -/
def univNat (p : ℕ × ℕ) : Part ℕ :=
  let parsed := parseTapeNat p.1
  Part.bind (Part.ofOption (Encodable.decode parsed.1 : Option Nat.Partrec.Code))
    (fun code => code.eval (Nat.pair parsed.2 p.2))

/-- The core numerical map is partial recursive. -/
lemma partrecUnivNat : Partrec univNat := by
  unfold univNat
  have h_parsed : Primrec (fun p : ℕ × ℕ => parseTapeNat p.1) :=
    primrecParseTapeNat.comp Primrec.fst
  apply Partrec.bind
  · exact Computable.ofOption
      (Computable.decode.comp (Primrec.to_comp (Primrec.fst.comp h_parsed)))
  · apply Partrec₂.comp Nat.Partrec.Code.eval_part
    · exact Computable.snd
    · exact Primrec.to_comp
        (Primrec₂.natPair.comp
          (Primrec.snd.comp (h_parsed.comp Primrec.fst))
          (Primrec.snd.comp Primrec.fst))

/-- Decode-with-default is primitive recursive. -/
private lemma primrecDecodeGetD :
    Primrec (fun r : ℕ => (Encodable.decode r : Option BitString).getD []) := by
  have : (fun r : ℕ => (Encodable.decode r : Option BitString).getD []) =
      fun r => Option.casesOn (Encodable.decode r : Option BitString) ([] : BitString) id := by
    funext r; cases (Encodable.decode r : Option BitString) <;> rfl
  rw [this]
  exact Primrec.option_casesOn (Primrec.decode (α := BitString))
    (Primrec.const []) Primrec.snd

/-- `universalDecompressor` is a computable partial function. -/
lemma isDecompressorUniversalDecompressor : isDecompressor universalDecompressor := by
  have h_eq : universalDecompressor = fun p =>
      (univNat (Encodable.encode p.1, Encodable.encode p.2)).map
        (fun r => (Encodable.decode r : Option BitString).getD []) := by
    funext ⟨s, y⟩
    unfold universalDecompressor univNat parseTapeNat
    simp only [Encodable.encodek]
    cases (Encodable.decode (List.takeWhile id s).length : Option Nat.Partrec.Code) <;> simp
  rw [h_eq]
  exact Partrec.map
    (Partrec.comp partrecUnivNat (Primrec.to_comp
      (Primrec.pair (Primrec.encode.comp Primrec.fst) (Primrec.encode.comp Primrec.snd))))
    (primrecDecodeGetD.to_comp.comp Computable.snd)

end Kolmogorov
