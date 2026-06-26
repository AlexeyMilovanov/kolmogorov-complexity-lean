/-
Copyright (c) 2024 Alexey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey
-/
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

lemma drop_unaryPrefix (n : ℕ) (p : List Bool) :
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

/-- `List.drop` is primitive recursive in its arguments (proved by recursion on the
number of elements dropped, peeling one tail at a time). -/
lemma primrec_list_drop : Primrec₂ (fun (l : List Bool) (n : ℕ) => l.drop n) := by
  have h : (fun (l : List Bool) (n : ℕ) => l.drop n)
      = fun l n => Nat.rec l (fun _ ih => ih.tail) n := by
    funext l n
    induction n with
    | zero => rfl
    | succ n ih => rw [← List.tail_drop, ih]
  rw [h]
  exact Primrec.nat_rec' Primrec.snd Primrec.fst
    (Primrec.list_tail.comp (Primrec.snd.comp Primrec.snd)).to₂

/-- The length of the leading run of `true`s equals the index of the first `false`,
so the unary-prefix length is computed by `List.findIdx`. -/
lemma takeWhile_id_length_eq_findIdx (s : List Bool) :
    (s.takeWhile id).length = s.findIdx (fun b => !b) := by
  induction s with
  | nil => rfl
  | cons a as ih =>
    cases a with
    | false => simp [List.findIdx_cons]
    | true =>
      simp only [List.takeWhile_cons, id_eq, List.findIdx_cons]; simp [ih]

/-- The tape parser is primitive recursive. -/
lemma primrecParseTapeNat : Primrec parseTapeNat := by
  have hform : parseTapeNat = fun n =>
      Option.casesOn (Encodable.decode n : Option BitString) (0, 0)
        (fun s => (s.findIdx (fun b => !b),
            Encodable.encode (s.drop (s.findIdx (fun b => !b) + 1)))) := by
    funext n
    simp only [parseTapeNat]
    cases (Encodable.decode n : Option BitString) with
    | none => rfl
    | some s => simp [takeWhile_id_length_eq_findIdx]
  rw [hform]
  have hidx : Primrec (fun p : ℕ × BitString => p.2.findIdx (fun b => !b)) :=
    Primrec.list_findIdx Primrec.snd (Primrec.not.comp Primrec.snd).to₂
  have hdrop : Primrec (fun p : ℕ × BitString => p.2.drop (p.2.findIdx (fun b => !b) + 1)) :=
    primrec_list_drop.comp Primrec.snd (Primrec.succ.comp hidx)
  have hsome : Primrec₂ (fun (n : ℕ) (s : BitString) =>
      (s.findIdx (fun b => !b), Encodable.encode (s.drop (s.findIdx (fun b => !b) + 1)))) :=
    (hidx.pair (Primrec.encode.comp hdrop)).to₂
  exact Primrec.option_casesOn Primrec.decode (Primrec.const (0, 0)) hsome

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
  have heq : universalDecompressor = fun p : BitString × BitString =>
      (univNat (Encodable.encode p.1, Encodable.encode p.2)).map
        (fun r => (Encodable.decode r : Option BitString).getD []) := by
    funext p
    obtain ⟨s, y⟩ := p
    simp only [universalDecompressor, univNat, parseTapeNat, Encodable.encodek]
    cases (Encodable.decode ((s.takeWhile id).length) : Option Nat.Partrec.Code) with
    | none => simp
    | some code =>
      simp only [Part.ofOption, Part.bind_some]
      rw [Encodable.encode_prod_val]
  rw [heq]
  have hpre : Computable (fun p : BitString × BitString =>
      (Encodable.encode p.1, Encodable.encode p.2)) :=
    (Primrec.encode.comp Primrec.fst).to_comp.pair (Primrec.encode.comp Primrec.snd).to_comp
  have hcomp : Partrec (fun p : BitString × BitString =>
      univNat (Encodable.encode p.1, Encodable.encode p.2)) :=
    partrecUnivNat.comp hpre
  exact Partrec.map hcomp (primrecDecodeGetD.comp Primrec.snd).to_comp.to₂

end Kolmogorov
