/-
Copyright (c) 2024 Alexey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey
-/
import KolmogorovMathlib.Prefix.OptimalExistence.Filter
import Mathlib

namespace Kolmogorov

open Nat.Partrec (Code)


/-- Equality of two values is a primitive recursive predicate (as a `Bool`). -/
theorem primrec_decide_eq {α} [Primcodable α] [DecidableEq α] :
    Primrec (fun p : α × α => decide (p.1 = p.2)) := by
  obtain ⟨inst, h⟩ := (Primrec.eq : PrimrecRel (@Eq α))
  exact h.of_eq (fun p => by congr 1)

/-- Strict order on `ℕ` is a primitive recursive predicate (as a `Bool`). -/
theorem primrec_decide_lt :
    Primrec (fun p : ℕ × ℕ => decide (p.1 < p.2)) := by
  obtain ⟨inst, h⟩ := (Primrec.nat_lt : PrimrecRel (· < ·))
  exact h.of_eq (fun p => by congr 1)

/-- `a` is a prefix of `b` iff appending the dropped tail of `b` reconstructs `b`. -/
theorem prefix_iff_append_drop (a b : BitString) :
    a <+: b ↔ a ++ b.drop a.length = b := by
  constructor
  · rintro ⟨t, rfl⟩; simp
  · intro h; exact ⟨b.drop a.length, h⟩

/-- `List.drop` on bitstrings is primitive recursive in both arguments. -/
theorem primrec_bitString_drop :
    Primrec₂ (fun (l : BitString) (n : ℕ) => l.drop n) := by
  have h : (fun (l : BitString) (n : ℕ) => l.drop n)
      = fun l n => Nat.rec l (fun _ ih => ih.tail) n := by
    funext l n; induction n with | zero => rfl | succ n ih => rw [← List.tail_drop, ih]
  rw [h]
  exact Primrec.nat_rec' Primrec.snd Primrec.fst
    (Primrec.list_tail.comp (Primrec.snd.comp Primrec.snd)).to₂

/-- The prefix relation on bitstrings is a primitive recursive predicate. -/
theorem decide_prefix_primrec :
    Primrec (fun ab : BitString × BitString => decide (ab.1 <+: ab.2)) := by
  have happ : Primrec (fun ab : BitString × BitString =>
      ((ab.1 ++ ab.2.drop ab.1.length, ab.2) : BitString × BitString)) :=
    (Primrec.list_append.comp Primrec.fst
      (primrec_bitString_drop.comp Primrec.snd (Primrec.list_length.comp Primrec.fst))).pair
      Primrec.snd
  exact (primrec_decide_eq.comp happ).of_eq
    (fun ab => decide_eq_decide.mpr (prefix_iff_append_drop ab.1 ab.2).symm)

/-- Decoding a natural number to a bitstring (defaulting to `[]`). -/
def decodeGetD (r : ℕ) : BitString := (Encodable.decode r : Option BitString).getD []

theorem decodeGetD_computable : Computable decodeGetD := by
  have h : decodeGetD =
      fun r => Option.casesOn (Encodable.decode r : Option BitString) ([] : BitString) id := by
    funext r; unfold decodeGetD; cases (Encodable.decode r : Option BitString) <;> rfl
  rw [h]
  exact Computable.option_casesOn Computable.decode (Computable.const []) Computable.snd.to₂

/-- The local prefix-freeness test as an explicit boolean combination. -/
def goodBool (q p : BitString) : Bool :=
  !((!decide (q = p)) && (decide (q <+: p) || decide (p <+: q)))

theorem goodBool_eq (q p : BitString) :
    goodBool q p = decide ¬ (q ≠ p ∧ (q <+: p ∨ p <+: q)) := by
  unfold goodBool
  by_cases h1 : q = p <;> by_cases h2 : q <+: p <;> by_cases h3 : p <+: q <;> simp_all

theorem goodBool_primrec : Primrec₂ goodBool := by
  unfold goodBool
  have hdeq : Primrec (fun s : BitString × BitString => decide (s.1 = s.2)) := primrec_decide_eq
  have hdqp : Primrec (fun s : BitString × BitString => decide (s.1 <+: s.2)) :=
    decide_prefix_primrec
  have hdpq : Primrec (fun s : BitString × BitString => decide (s.2 <+: s.1)) :=
    decide_prefix_primrec.comp (Primrec.snd.pair Primrec.fst)
  have h1 : Primrec (fun s : BitString × BitString => !(decide (s.1 = s.2))) :=
    Primrec.not.comp hdeq
  have h2 : Primrec (fun s : BitString × BitString =>
      decide (s.1 <+: s.2) || decide (s.2 <+: s.1)) := Primrec.or.comp hdqp hdpq
  exact Primrec.not.comp (Primrec.and.comp h1 h2)

/-- `appearsAt` is uniformly primitive recursive in the code, context, and index. -/
theorem appearsAt_uniform_primrec :
    Primrec (fun t : Code × BitString × ℕ => appearsAt t.1 t.2.1 t.2.2) := by
  unfold appearsAt
  have hf : Primrec (fun t : Code × BitString × ℕ =>
      (Encodable.decode t.2.2.unpair.1 : Option BitString)) :=
    Primrec.decode.comp (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.snd)))
  have hevaln : Primrec (fun q : (Code × BitString × ℕ) × BitString =>
      Code.evaln (q.1.2.2.unpair.2 + 1) q.1.1 (Encodable.encode (q.2, q.1.2.1))) := by
    have hk : Primrec (fun q : (Code × BitString × ℕ) × BitString => q.1.2.2.unpair.2 + 1) :=
      Primrec.succ.comp (Primrec.snd.comp (Primrec.unpair.comp
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))
    have hc : Primrec (fun q : (Code × BitString × ℕ) × BitString => q.1.1) :=
      Primrec.fst.comp Primrec.fst
    have hi : Primrec (fun q : (Code × BitString × ℕ) × BitString =>
        Encodable.encode (q.2, q.1.2.1)) :=
      Primrec.encode.comp
        (Primrec.pair Primrec.snd (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
    exact Nat.Partrec.Code.primrec_evaln.comp ((hk.pair hc).pair hi)
  have hg : Primrec₂ (fun (t : Code × BitString × ℕ) (p : BitString) =>
      if (Code.evaln (t.2.2.unpair.2 + 1) t.1 (Encodable.encode (p, t.2.1))).isSome then
        some p else none) := by
    have hbool : Primrec (fun q : (Code × BitString × ℕ) × BitString =>
        (Code.evaln (q.1.2.2.unpair.2 + 1) q.1.1 (Encodable.encode (q.2, q.1.2.1))).isSome) :=
      Primrec.option_isSome.comp hevaln
    have hsome : Primrec (fun q : (Code × BitString × ℕ) × BitString =>
        (some q.2 : Option BitString)) := Primrec.option_some.comp Primrec.snd
    have hnone : Primrec (fun _ : (Code × BitString × ℕ) × BitString =>
        (none : Option BitString)) := Primrec.const none
    exact (Primrec.cond hbool hsome hnone).of_eq (fun q => cond_eq_ite _ _ _)
  exact Primrec.option_bind hf hg

/-- `goodAt` rewritten via `goodBool`, suitable for computability. -/
theorem goodAt_eq (c : Code) (y p : BitString) (n : ℕ) :
    goodAt c y p n = Option.casesOn (appearsAt c y n) true (fun q => goodBool q p) := by
  cases h : appearsAt c y n with
  | none => simp [goodAt, h]
  | some q => simp [goodAt, h, goodBool_eq]

/-- `goodAt` is uniformly primitive recursive. -/
theorem goodAt_uniform_primrec :
    Primrec (fun t : Code × BitString × BitString × ℕ =>
      goodAt t.1 t.2.1 t.2.2.1 t.2.2.2) := by
  have hmap : Primrec (fun t : Code × BitString × BitString × ℕ =>
      ((t.1, t.2.1, t.2.2.2) : Code × BitString × ℕ)) :=
    Primrec.fst.pair ((Primrec.fst.comp Primrec.snd).pair
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have happ : Primrec (fun t : Code × BitString × BitString × ℕ =>
      appearsAt t.1 t.2.1 t.2.2.2) :=
    (appearsAt_uniform_primrec.comp hmap).of_eq (fun t => rfl)
  have hgb : Primrec (fun p : BitString × BitString => goodBool p.1 p.2) := goodBool_primrec
  have hpair : Primrec (fun s : (Code × BitString × BitString × ℕ) × BitString =>
      ((s.2, s.1.2.2.1) : BitString × BitString)) :=
    Primrec.snd.pair (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
  have hg : Primrec₂ (fun (t : Code × BitString × BitString × ℕ) (q : BitString) =>
      goodBool q t.2.2.1) := (hgb.comp hpair).of_eq (fun s => rfl)
  have hcase := Primrec.option_casesOn happ (Primrec.const true) hg
  exact hcase.of_eq (fun t => (goodAt_eq t.1 t.2.1 t.2.2.1 t.2.2.2).symm)

/-- `acceptBefore` is uniformly primitive recursive. -/
theorem acceptBefore_uniform_primrec :
    Primrec (fun t : Code × BitString × BitString × ℕ =>
      acceptBefore t.1 t.2.1 t.2.2.1 t.2.2.2) := by
  unfold acceptBefore
  have hf : Primrec (fun t : Code × BitString × BitString × ℕ => List.range t.2.2.2) :=
    Primrec.list_range.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hgc : Primrec (fun _ : Code × BitString × BitString × ℕ => true) := Primrec.const true
  have hmap : Primrec (fun s : (Code × BitString × BitString × ℕ) × (ℕ × Bool) =>
      ((s.1.1, s.1.2.1, s.1.2.2.1, s.2.1) : Code × BitString × BitString × ℕ)) :=
    (Primrec.fst.comp Primrec.fst).pair
      ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair
        ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).pair
          (Primrec.fst.comp Primrec.snd)))
  have hgoodc : Primrec (fun s : (Code × BitString × BitString × ℕ) × (ℕ × Bool) =>
      goodAt s.1.1 s.1.2.1 s.1.2.2.1 s.2.1) :=
    (goodAt_uniform_primrec.comp hmap).of_eq (fun s => rfl)
  have hh : Primrec₂ (fun (t : Code × BitString × BitString × ℕ) (bs : ℕ × Bool) =>
      goodAt t.1 t.2.1 t.2.2.1 bs.1 && bs.2) :=
    (Primrec.and.comp hgoodc (Primrec.snd.comp Primrec.snd)).of_eq (fun s => rfl)
  exact Primrec.list_foldr hf hgc hh

/-- The filter is uniformly partial recursive in the code and input. -/
theorem prefixFiltered_uniform_partrec :
    Partrec (fun t : Code × BitString × BitString => prefixFiltered t.1 t.2) := by
  have hcheck : Computable₂ (fun (t : Code × BitString × BitString) (n : ℕ) =>
      decide (appearsAt t.1 t.2.2 n = some t.2.1)) := by
    have hmap : Computable (fun s : (Code × BitString × BitString) × ℕ =>
        ((s.1.1, s.1.2.2, s.2) : Code × BitString × ℕ)) :=
      (Computable.fst.comp Computable.fst).pair
        ((Computable.snd.comp (Computable.snd.comp Computable.fst)).pair Computable.snd)
    have happ : Computable (fun s : (Code × BitString × BitString) × ℕ =>
        appearsAt s.1.1 s.1.2.2 s.2) :=
      ((Primrec.to_comp appearsAt_uniform_primrec).comp hmap).of_eq (fun s => rfl)
    have hsome : Computable (fun s : (Code × BitString × BitString) × ℕ =>
        (some s.1.2.1 : Option BitString)) :=
      Computable.option_some.comp (Computable.fst.comp (Computable.snd.comp Computable.fst))
    exact ((Primrec.to_comp primrec_decide_eq).comp (happ.pair hsome)).of_eq (fun s => rfl)
  have hrfind : Partrec (fun t : Code × BitString × BitString =>
      Nat.rfind (fun n => Part.some (decide (appearsAt t.1 t.2.2 n = some t.2.1)))) :=
    Partrec.rfind hcheck.partrec₂
  have hbindfn : Partrec₂ (fun (t : Code × BitString × BitString) (N : ℕ) =>
      bif acceptBefore t.1 t.2.2 t.2.1 N then
        (t.1.eval (Encodable.encode t.2)).map decodeGetD else Part.none) := by
    have hacc : Computable (fun s : (Code × BitString × BitString) × ℕ =>
        acceptBefore s.1.1 s.1.2.2 s.1.2.1 s.2) := by
      have hmap : Computable (fun s : (Code × BitString × BitString) × ℕ =>
          ((s.1.1, s.1.2.2, s.1.2.1, s.2) : Code × BitString × BitString × ℕ)) :=
        (Computable.fst.comp Computable.fst).pair
          ((Computable.snd.comp (Computable.snd.comp Computable.fst)).pair
            ((Computable.fst.comp (Computable.snd.comp Computable.fst)).pair Computable.snd))
      exact ((Primrec.to_comp acceptBefore_uniform_primrec).comp hmap).of_eq (fun s => rfl)
    have heval : Partrec (fun s : (Code × BitString × BitString) × ℕ =>
        s.1.1.eval (Encodable.encode s.1.2)) :=
      Nat.Partrec.Code.eval_part.comp (Computable.fst.comp Computable.fst)
        (Computable.encode.comp (Computable.snd.comp Computable.fst))
    have hmapp : Partrec (fun s : (Code × BitString × BitString) × ℕ =>
        (s.1.1.eval (Encodable.encode s.1.2)).map decodeGetD) :=
      heval.map (decodeGetD_computable.comp Computable.snd).to₂
    exact Partrec.cond hacc hmapp Partrec.none
  exact hrfind.bind hbindfn

/-- The filtered machine is partial recursive. -/
theorem prefixFiltered_isDecompressor (c : Code) :
    isDecompressor (prefixFiltered c) := by
  have h := prefixFiltered_uniform_partrec.comp
    ((Computable.const c).pair Computable.id)
  exact h

/-- The filtered machine is always a prefix decompressor. -/
theorem prefixFiltered_isPrefixDecompressor (c : Code) :
    IsPrefixDecompressor (prefixFiltered c) :=
  ⟨prefixFiltered_isDecompressor c, prefixFiltered_isPrefixMachine c⟩


end Kolmogorov
