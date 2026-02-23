import Mathlib.Computability.Partrec
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Encoding
import Mathlib.Data.List.Basic
import Mathlib.Data.ENat.Basic
import KolmogorovMathlib.Core.Basic
import KolmogorovMathlib.Foundation.ListPrimrec

/-!
# Universal Decompressor Construction

This module constructs the Conditional Universal Decompressor `U`.
It introduces unary prefix coding to multiplex multiple programs onto a single tape.
We define both a human-readable decompressor (`universalDecompressor`) and a combinator-based
equivalent (`universalDecompressorCombinator`), proving they are identical.
Finally, we formally prove that `U` is computable (`Partrec`).
-/

namespace Kolmogorov

-- ==========================================================
-- BLOCK 1: Unary Prefixes
-- ==========================================================

/-- Unary prefix coding: `n` is encoded as `n` ones followed by a zero. -/
def unaryPrefix (n : ℕ) : List Bool :=
  List.replicate n true ++ [false]

@[simp]
lemma length_unaryPrefix (n : ℕ) : (unaryPrefix n).length = n + 1 := by
  simp [unaryPrefix]

@[simp]
lemma takeWhile_unaryPrefix (n : ℕ) (p : List Bool) :
    ((unaryPrefix n ++ p).takeWhile id).length = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    calc
      ((unaryPrefix (n + 1) ++ p).takeWhile id).length
      _ = ((true :: (unaryPrefix n ++ p)).takeWhile id).length := rfl
      _ = ((unaryPrefix n ++ p).takeWhile id).length + 1       := rfl
      _ = n + 1                                                := by rw [ih]

@[simp]
lemma drop_unaryPrefix (n : ℕ) (p : List Bool) :
    (unaryPrefix n ++ p).drop (n + 1) = p := by
  induction n with
  | zero => rfl
  | succ n ih =>
    calc
      (unaryPrefix (n + 1) ++ p).drop (n + 1 + 1)
      _ = (true :: (unaryPrefix n ++ p)).drop (n + 2) := rfl
      _ = (unaryPrefix n ++ p).drop (n + 1)           := rfl
      _ = p                                           := by rw [ih]

-- ==========================================================
-- BLOCK 2: Universal Decompressor
-- ==========================================================

/-- A robust, human-readable definition of the Conditional Universal Decompressor. -/
def universalDecompressor : Map := fun p =>
  let s := p.1
  let y := p.2
  let i := (s.takeWhile id).length
  let code_opt : Option Nat.Partrec.Code := Encodable.decode i
  match code_opt with
  | none => Part.none
  | some code =>
      let p_bits := s.drop (i + 1)
      let input_nat := Encodable.encode (p_bits, y)
      (code.eval input_nat).map (fun res_nat =>
        (Encodable.decode res_nat : Option BitString).getD [])

/-- A strict, combinator-friendly version of universalDecompressor. -/
def universalDecompressorCombinator : Map := fun p =>
  let s := p.1
  let y := p.2
  let code_part : Part Nat.Partrec.Code :=
    Part.ofOption (Encodable.decode (prefixLen s) : Option Nat.Partrec.Code)
  code_part.bind fun code =>
    let p_bits := listDrop s (prefixLen s + 1)
    let input_nat := Encodable.encode (p_bits, y)
    (code.eval input_nat).map (fun res_nat =>
      (Encodable.decode res_nat : Option BitString).getD [])

-- ==========================================================
-- BLOCK 3: The Bridge Lemmas & Simulation
-- ==========================================================

lemma prefixLen_eq_takeWhile (s : List Bool) :
    prefixLen s = (s.takeWhile id).length := by
  induction s with
  | nil => rfl
  | cons hd _ ih =>
    cases hd
    · rfl
    · exact congrArg Nat.succ ih

lemma dropTail_eq_dropSucc (s : List Bool) (n : ℕ) :
    (s.drop n).tail = s.drop (n + 1) := by
  induction s generalizing n with
  | nil => cases n <;> rfl
  | cons _ _ ih =>
    cases n
    · rfl
    · exact ih _

lemma listDrop_eq_drop (s : List Bool) (n : ℕ) :
    listDrop s n = s.drop n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    calc
      listDrop s (n + 1) = (listDrop s n).tail := rfl
      _ = (s.drop n).tail                      := by rw [ih]
      _ = s.drop (n + 1)                       := dropTail_eq_dropSucc s n

/-- The Bridge Lemma: The human-readable and combinator maps are identical. -/
lemma universalDecompressor_eq_combinator (s y : BitString) :
    universalDecompressor (s, y) = universalDecompressorCombinator (s, y) := by
  unfold universalDecompressor universalDecompressorCombinator
  dsimp only
  rw [← prefixLen_eq_takeWhile, ← listDrop_eq_drop]
  cases (Encodable.decode (prefixLen s) : Option Nat.Partrec.Code) <;> simp

/-- Simulation lemma: U(prefix(i) ++ p, y) = Decompressor_i(p, y) -/
lemma universalSimulation (code : Nat.Partrec.Code) (p y : BitString) :
    universalDecompressor (unaryPrefix (Encodable.encode code) ++ p, y) =
    (code.eval (Encodable.encode (p, y))).map
      (fun r => (Encodable.decode r : Option BitString).getD []) := by
  unfold universalDecompressor
  dsimp only
  simp only [takeWhile_unaryPrefix, drop_unaryPrefix]
  rw [@Encodable.encodek Nat.Partrec.Code _ code]

-- ==========================================================
-- BLOCK 4: Computability of the Universal Decompressor
-- ==========================================================

/-- A total function that parses the tape from a natural number. -/
def parseTapeNat (n : ℕ) : ℕ × ℕ :=
  Option.casesOn (Encodable.decode n : Option BitString)
    (0, 0)
    (fun s => (prefixLen s, Encodable.encode (listDrop s (prefixLen s + 1))))

/-- Prove that our total parser is Primitive Recursive. -/
lemma parseTapeNat_primrec : Primrec parseTapeNat := by
  unfold parseTapeNat
  apply Primrec.option_casesOn Primrec.decode
  · exact Primrec.const (0, 0)
  · apply Primrec.pair
    · exact Primrec.prefixLen.comp Primrec.snd
    · apply Primrec.encode.comp
      apply Primrec₂.comp Primrec₂.listDrop
      · exact Primrec.snd
      · apply Primrec.succ.comp
        exact Primrec.prefixLen.comp Primrec.snd

/-- The core numerical universal decompressor taking a pair of (program_nat, context_nat). -/
def univNat (p : ℕ × ℕ) : Part ℕ :=
  let parsed := parseTapeNat p.1
  Part.bind (Part.ofOption (Encodable.decode parsed.1 : Option Nat.Partrec.Code))
    (fun code => code.eval (Nat.pair parsed.2 p.2))

/-- Prove that the core numerical map is partial recursive. -/
lemma univNat_partrec : Partrec univNat := by
  unfold univNat
  have h_parsed : Primrec (fun p : ℕ × ℕ => parseTapeNat p.1) :=
    parseTapeNat_primrec.comp Primrec.fst
  apply Partrec.bind
  · have h_dec : Computable (fun p : ℕ × ℕ =>
        (Encodable.decode (parseTapeNat p.1).1 : Option Nat.Partrec.Code)) :=
      Computable.comp Computable.decode (Primrec.to_comp (Primrec.fst.comp h_parsed))
    exact Computable.ofOption h_dec
  · apply Partrec₂.comp Nat.Partrec.Code.eval_part
    · exact Computable.snd
    · apply Primrec.to_comp
      have h_parsed_2 : Primrec (fun p : (ℕ × ℕ) × Nat.Partrec.Code =>
          (parseTapeNat p.1.1).2) :=
        Primrec.snd.comp (parseTapeNat_primrec.comp (Primrec.fst.comp Primrec.fst))
      have h_ny : Primrec (fun p : (ℕ × ℕ) × Nat.Partrec.Code => p.1.2) :=
        Primrec.snd.comp Primrec.fst
      exact Primrec₂.natPair.comp h_parsed_2 h_ny

/-- Final Lemma: universalDecompressorCombinator is a valid Decompressor. -/
lemma universalDecompressorCombinator_partrec : isDecompressor universalDecompressorCombinator := by
  have h_eq : universalDecompressorCombinator = fun p =>
      (univNat (Encodable.encode p.1, Encodable.encode p.2)).map
        (fun r => (Encodable.decode r : Option BitString).getD []) := by
    funext p
    unfold universalDecompressorCombinator univNat parseTapeNat
    dsimp only
    simp [Encodable.encodek]
  rw [h_eq]
  apply Partrec.map
  · have h_encode1 : Primrec (fun p : BitString × BitString => Encodable.encode p.1) :=
      Primrec.encode.comp Primrec.fst
    have h_encode2 : Primrec (fun p : BitString × BitString => Encodable.encode p.2) :=
      Primrec.encode.comp Primrec.snd
    have h_pair : Primrec (fun p : BitString × BitString =>
        (Encodable.encode p.1, Encodable.encode p.2)) :=
      Primrec.pair h_encode1 h_encode2
    exact Partrec.comp univNat_partrec (Primrec.to_comp h_pair)
  · have h_eq_getD : (fun (r : ℕ) => (Encodable.decode r : Option BitString).getD []) =
        (fun (r : ℕ) => Option.casesOn (Encodable.decode r : Option BitString)
          ((fun _ : ℕ => ([] : BitString)) r)
          (fun x => Prod.snd (r, x))) := by
      funext r
      cases (Encodable.decode r : Option BitString) <;> rfl
    have h_post_prim : Primrec (fun r : ℕ => (Encodable.decode r : Option BitString).getD []) := by
      rw [h_eq_getD]
      exact Primrec.option_casesOn (Primrec.decode (α := BitString))
        (Primrec.const ([] : BitString))
        (Primrec.snd : Primrec (fun p : ℕ × BitString => p.2))
    exact Computable.comp (Primrec.to_comp h_post_prim) Computable.snd

/-- UniversalDecompressor is a computable partial function. -/
lemma isDecompressor_universalDecompressor : isDecompressor universalDecompressor := by
  have h_eq : universalDecompressor = universalDecompressorCombinator := by
    funext p
    exact universalDecompressor_eq_combinator p.1 p.2
  rw [h_eq]
  exact universalDecompressorCombinator_partrec

end Kolmogorov
