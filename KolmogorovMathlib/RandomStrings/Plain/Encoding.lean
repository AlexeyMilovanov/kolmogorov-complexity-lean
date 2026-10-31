/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Encoding.Tuples
import KolmogorovMathlib.Foundation.NatEncoding
import KolmogorovMathlib.Prefix.Properties
import KolmogorovMathlib.RandomStrings.Plain.Basic
import KolmogorovMathlib.StoppingComplexity.CeilLog

/-! # Binary literals, tuples, and oracle queries

Natural data use nonempty, most-significant-bit-first binary strings. The existing
`pairCode` is the blueprint's pair: its unary header encodes a string length, not a
natural data field. `triple` uses binary integers and extensions curry its entire result.
All parsers reject malformed input by checking reconstruction. `Option` parsers are total;
their `Part.ofOption` interpretations are the required partial projections.

This module formalizes the encoding of natural numbers and tuples as self-delimiting
binary strings (nodes `native:halting-language` and `FoundationPrefixLiteralBound`).
It provides explicit computable encoders and decoders to define the native halting
language and establish upper bounds on prefix complexity. It is used by subsequent
modules like `KolmogorovMathlib.RandomStrings.Plain.Target`,
`KolmogorovMathlib.RandomStrings.Plain.PrefixInterface`,
and `KolmogorovMathlib.RandomStrings.Plain.HaltingLanguage` to instantiate the halting separation.
-/

namespace Kolmogorov.Milovanov

/-- Canonical nonempty binary naturals, most significant bit first, with zero coded by `0`.
Blueprint node `native:halting-language`. -/
def bits (n : ℕ) : BitString :=
  if n = 0 then [false] else (Nat.bits n).reverse

/-- Partial inverse of canonical binary notation; noncanonical words are rejected.
Blueprint node `FoundationPrefixLiteralBound`. -/
def decodeNat (w : BitString) : Option ℕ :=
  let n := decodeBits w.reverse
  if bits n = w then some n else none

/-- A self-delimited string `1^{|s|} 0 s`, using the existing pair encoder.
Blueprint node `native:halting-language`. -/
def sd (s : BitString) : BitString := pairCode s []

/-- Parse a self-delimited first field and its remaining suffix, rejecting bad headers.
Blueprint node `FoundationPrefixLiteralBound`. -/
def parseSd (w : BitString) : Option (BitString × BitString) :=
  let p := (decodeFirst w, decodeSecond w)
  if pairCode p.1 p.2 = w then some p else none

/-- A self-delimiting natural literal, with a unary header for its binary length.
Blueprint node `FoundationPrefixLiteralBound`. -/
def integerCode (n : ℕ) : BitString := sd (bits n)

/-- A literal string preceded by the self-delimiting binary code of its length.
Blueprint node `FoundationPrefixLiteralBound`. -/
def literalCode (s : BitString) : BitString := integerCode s.length ++ s

/-- Decode a literal string and its unconsumed suffix, rejecting invalid lengths.
Blueprint node `FoundationPrefixLiteralBound`. -/
def parseLiteral (w : BitString) : Option (BitString × BitString) := do
  let (header, rest) ← parseSd w
  let n ← decodeNat header
  if n ≤ rest.length then some (rest.take n, rest.drop n) else none

/-- The fixed base tuple `(x,q,w)`, with binary `q` and existing pair codes.
Blueprint node `FoundationPrefixLiteralBound`. -/
def triple (x : BitString) (q : ℕ) (w : BitString) : BitString :=
  pairCode x (pairCode (bits q) w)

/-- Partial projections of the fixed base triple, including canonical decoding of `q`.
Blueprint node `FoundationPrefixLiteralBound`. -/
def decodeTriple (s : BitString) : Option (BitString × ℕ × BitString) := do
  let (x, rest) ← parseSd s
  let (q, w) ← parseSd rest
  let n ← decodeNat q
  some (x, n, w)

/-- An extension attaches its final coordinate to the already encoded base triple.
Blueprint node `FoundationPrefixLiteralBound`. This currying is definitional. -/
def extensionCode (x : BitString) (q : ℕ) (w s : BitString) : BitString :=
  pairCode (triple x q w) s

/-- The fixed cumulative query `sd x ++ bits k`.
Blueprint node `FoundationPrefixLiteralBound`. -/
def encF (p : BitString × ℕ) : BitString := pairCode p.1 (bits p.2)

/-- Partial inverse of the cumulative query encoder, rejecting malformed words.
Blueprint node `FoundationPrefixLiteralBound`. -/
def decodeQuery (w : BitString) : Option (BitString × ℕ) := do
  let (x, suffix) ← parseSd w
  let k ← decodeNat suffix
  some (x, k)

/-- A halting instance has a self-delimited binary data field and a binary code index.
Blueprint node `native:halting-language`. The argument order is index, then data. -/
def haltWord (e y : ℕ) : BitString := encF (bits y, e)

/-- Parse a halting word into its code index and input, rejecting malformed words.
Blueprint node `native:halting-language`. -/
def decodeHaltWord (w : BitString) : Option (ℕ × ℕ) := do
  let (data, e) ← decodeQuery w
  let y ← decodeNat data
  some (e, y)

/-- The computable literal upper bound used as the default in finite prefix computations.
Blueprint node `FoundationPrefixLiteralBound`. -/
def literalBound (B : Base) (a : BitString) : ℕ :=
  a.length + 2 * Nat.clog 2 (a.length + 2) + B.cD

/-- A natural literal complexity budget with an explicitly supplied interpreter overhead.
Blueprint node `FoundationPrefixLiteralBound`. -/
def integerLiteralBound (c t : ℕ) : ℕ := 2 * Nat.clog 2 (t + 2) + c

/-- Canonical decoding recovers every encoded natural.
Blueprint node `FoundationPrefixLiteralBound`. -/
theorem decodeNat_bits (n : ℕ) : decodeNat (bits n) = some n := by
  have h : decodeBits (bits n).reverse = n := by
    by_cases hn : n = 0
    · subst n
      rfl
    · simp [bits, hn]
  simp [decodeNat, h]

/-- Canonical binary notation is injective.
Blueprint node `FoundationPrefixLiteralBound`. -/
theorem bits_injective : Function.Injective bits := by
  intro m n h
  have := congrArg decodeNat h
  simpa only [decodeNat_bits, Option.some.injEq] using this

/-- A natural number is zero iff its little-endian `Nat.bits` list is empty. -/
private theorem eq_zero_iff_bits_eq_nil (n : ℕ) : n = 0 ↔ Nat.bits n = [] := by
  constructor
  · intro h; subst h; rfl
  · intro h
    cases n
    · rfl
    · rename_i n
      revert h
      have hk : ∀ (k : ℕ), Nat.bits (k + 1) ≠ [] := by
        intro k hc
        have eq1 : k + 1 = Nat.bit (Nat.bodd (k + 1)) ((k + 1) / 2) := by
          rw [Nat.bit_val]
          have h2 := Nat.bodd_add_div2 (k + 1)
          unfold Nat.div2 at h2
          omega
        have eq2 : Nat.bits (k + 1) = Nat.bodd (k + 1) :: Nat.bits ((k + 1) / 2) := by
          conv => lhs; rw [eq1]
          apply Nat.bits_append_bit
          intro h_div2
          have h3 : k + 1 = Nat.bit (Nat.bodd (k + 1)) 0 := by rw [h_div2] at eq1; exact eq1
          rw [Nat.bit_val] at h3
          cases hb : Nat.bodd (k + 1)
          · rw [hb] at h3
            change k + 1 = 0 + 2 * 0 at h3
            omega
          · rfl
        rw [eq2] at hc
        contradiction
      intro hc
      exact False.elim (hk n hc)

/-- The canonical binary string representation of a natural number is never empty. -/
theorem bits_nonempty (n : ℕ) : bits n ≠ [] := by
  unfold bits
  split_ifs with h
  · intro hc; contradiction
  · intro hc
    have hc2 := List.reverse_eq_nil_iff.mp hc
    have h1 := (eq_zero_iff_bits_eq_nil n).mpr hc2
    contradiction

/-- Positive canonical binary words start with one, so there are no leading zeroes.
Blueprint node `native:halting-language`. -/
theorem bits_head (n : ℕ) (hn : n ≠ 0) : (bits n).head? = some true := by
  unfold bits
  simp only [hn, ite_false, List.head?_reverse]
  induction n using Nat.binaryRec with
  | zero => contradiction
  | bit b n' ih =>
    by_cases h2 : n' = 0 ∧ b = false
    · exact False.elim (hn (Nat.bit_eq_zero_iff.mpr h2))
    · have h3 : n' = 0 → b = true := by
        intro hn'
        subst hn'
        simpa using h2
      rw [Nat.bits_append_bit _ _ h3]
      rcases eq_or_ne n' 0 with rfl | hn'
      · cases b <;> simp_all
      · cases h_bits : n'.bits with
        | nil =>
          have := ih hn'
          rw [h_bits] at this
          contradiction
        | cons hd tl =>
          have : (b :: hd :: tl).getLast? = (hd :: tl).getLast? := rfl
          rw [this, ← h_bits]
          exact ih hn'

/-- A binary integer word has at most `n+1` bits, including at zero.
Blueprint node `native:halting-language`. -/
theorem length_bits_le (n : ℕ) : (bits n).length ≤ n + 1 := by
  by_cases hn : n = 0
  · subst n
    decide
  · simpa [bits, hn] using (length_natBits_le n).trans (Nat.le_succ n)

/-- Integers below `2^(m+1)` fit in `m+1` bits, with the same convention at zero.
Blueprint node `native:halting-language`. -/
theorem length_bits_le_of_lt {n m : ℕ} (h : n < 2 ^ (m + 1)) :
    (bits n).length ≤ m + 1 := by
  by_cases hn : n = 0
  · subst n
    simp [bits]
  · simpa [bits, hn, Nat.size_eq_bits_len] using Nat.size_le.mpr h

/-- The exact length of the self-delimited string header.
Blueprint node `native:halting-language`. -/
theorem length_sd (s : BitString) : (sd s).length = 2 * s.length + 1 := by
  simp [sd]
  omega

/-- The self-delimiter has exactly the blueprint's unary-header spelling.
Blueprint node `native:halting-language`. -/
theorem sd_eq (s : BitString) : sd s = List.replicate s.length true ++ false :: s := by
  simp [sd, pairCode, natCode]

/-- The fixed pair has exact length `2|a|+1+|b|`.
Blueprint node `FoundationPrefixLiteralBound`. -/
theorem literal_and_tuple_code_interface_pair (a b : BitString) :
    (pairCode a b).length = 2 * a.length + 1 + b.length := by
  simp only [length_pairCode]
  omega

/-- The fixed base triple has an explicit length, including its binary natural field.
Blueprint node `FoundationPrefixLiteralBound`. -/
theorem literal_and_tuple_code_interface_triple (x w : BitString) (q : ℕ) :
    (triple x q w).length = 2 * x.length + 2 * (bits q).length + w.length + 2 := by
  simp only [triple, length_pairCode]
  omega

/-- The literal prefix code has the exact advertised length before optimality overhead.
Blueprint node `FoundationPrefixLiteralBound`. -/
theorem length_literalCode (s : BitString) :
    (literalCode s).length = s.length + 2 * (bits s.length).length + 1 := by
  simp only [literalCode, integerCode, List.length_append, length_sd]
  omega

/-- Binary self-delimiting integer codes have logarithmic length.
Blueprint node `FoundationPrefixLiteralBound`. -/
theorem length_integerCode_le (t : ℕ) :
    (integerCode t).length ≤ 2 * Nat.clog 2 (t + 2) + 1 := by
  have h_len : (integerCode t).length = 2 * (Kolmogorov.Milovanov.bits t).length + 1 := by
    dsimp [integerCode]
    rw [length_sd (Kolmogorov.Milovanov.bits t)]
  rw [h_len]
  apply Nat.add_le_add_right
  apply Nat.mul_le_mul_left
  have hc : t + 1 < 2 ^ (Nat.clog 2 (t + 2)) := by
    have hc2 : t + 2 ≤ 2 ^ (Nat.clog 2 (t + 2)) := Nat.le_pow_clog (by decide) (t + 2)
    omega
  have hc3 : t < 2 ^ (Nat.clog 2 (t + 2)) := by omega
  have h1 : 1 ≤ Nat.clog 2 (t + 2) := by
    apply Nat.succ_le_of_lt
    apply Nat.clog_pos (by decide)
    omega
  have hm : ∃ m, Nat.clog 2 (t + 2) = m + 1 := ⟨Nat.clog 2 (t + 2) - 1, by omega⟩
  rcases hm with ⟨m, hm_eq⟩
  rw [hm_eq]
  have hc4 : t < 2 ^ (m + 1) := by
    rwa [←hm_eq]
  have h_bound := length_bits_le_of_lt hc4
  exact h_bound

private theorem eq_and_prefix_of_integerCode_append_prefix {n m : ℕ} {a b : BitString}
    (h : integerCode n ++ a <+: integerCode m ++ b) : n = m ∧ a <+: b := by
  dsimp [integerCode, sd, pairCode] at h
  obtain ⟨t, ht⟩ := h
  have h1 : natCode (bits n).length ++ ((bits n) ++ a ++ t) =
      natCode (bits m).length ++ ((bits m) ++ b) := by
    calc natCode (bits n).length ++ (bits n ++ a ++ t) =
        natCode (bits n).length ++ bits n ++ [] ++ a ++ t := by
          simp only [List.append_nil]; rw [← List.append_assoc, ← List.append_assoc]
      _ = natCode (bits m).length ++ bits m ++ [] ++ b := ht
      _ = natCode (bits m).length ++ (bits m ++ b) := by
          simp only [List.append_nil]; rw [List.append_assoc]
  have ⟨hlen, hap⟩ := natCode_append_inj h1
  have hn : bits n = bits m := by
    have h2 : bits n ++ (a ++ t) = bits m ++ b := by
      calc bits n ++ (a ++ t) = bits n ++ a ++ t := by rw [List.append_assoc]
        _ = bits m ++ b := hap
    apply List.append_inj_left h2 hlen
  have hnm : n = m := bits_injective hn
  subst hnm
  have h3 : bits n ++ (a ++ t) = bits n ++ b := by
    calc bits n ++ (a ++ t) = bits n ++ a ++ t := by rw [List.append_assoc]
      _ = bits n ++ b := hap
  have h4 : a ++ t = b := by exact List.append_cancel_left h3
  exact ⟨rfl, ⟨t, h4⟩⟩

/-- Literal codes are prefix-free, making their boundaries recoverable.
Blueprint node `FoundationPrefixLiteralBound`. -/
theorem literalCode_prefix_free : IsPrefixFree (Set.range literalCode) := by
  rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩ hpre
  have hpre2 : integerCode s.length ++ s <+: integerCode t.length ++ t := hpre
  have ⟨_, h_s_pre_t⟩ := eq_and_prefix_of_integerCode_append_prefix hpre2
  obtain ⟨u, hu⟩ := h_s_pre_t
  have h_len_eq_u : s.length + u.length = t.length := by
    have : (s ++ u).length = t.length := by rw [hu]
    simp only [List.length_append] at this
    exact this
  have h_u_empty : u.length = 0 := by omega
  have hu2 : u = [] := List.length_eq_zero_iff.mp h_u_empty
  subst hu2
  simp only [List.append_nil] at hu
  subst hu
  rfl

/-- The validated streaming parser recovers the first field and the raw suffix.
Blueprint node `FoundationPrefixLiteralBound`. -/
theorem parseSd_pairCode (x y : BitString) : parseSd (pairCode x y) = some (x, y) := by
  simp [parseSd, decodeFirst_pairCode, decodeSecond_pairCode]

/-- A literal code can be parsed in front of an arbitrary raw suffix.
Blueprint node `FoundationPrefixLiteralBound`. -/
theorem parseLiteral_literalCode (x r : BitString) :
    parseLiteral (literalCode x ++ r) = some (x, r) := by
  dsimp [parseLiteral, literalCode, integerCode, sd]
  have h1 : pairCode (bits x.length) [] ++ (x ++ r) = pairCode (bits x.length) (x ++ r) := by
    dsimp [pairCode]
    simp
  have h2 : pairCode (bits x.length) [] ++ x ++ r = pairCode (bits x.length) [] ++ (x ++ r) := by
    exact List.append_assoc _ _ _
  rw [h2]
  rw [h1]
  rw [parseSd_pairCode]
  dsimp
  rw [decodeNat_bits]
  dsimp
  have hlen : x.length ≤ (x ++ r).length := by simp
  split_ifs
  · simp

/-- The triple's validated partial projections recover all components.
Blueprint node `FoundationPrefixLiteralBound`. -/
theorem decodeTriple_triple (x w : BitString) (q : ℕ) :
    decodeTriple (triple x q w) = some (x, q, w) := by
  simp [decodeTriple, triple, parseSd_pairCode, decodeNat_bits]

/-- The fixed triple representation is injective in all three fields.
Blueprint node `FoundationPrefixLiteralBound`. -/
theorem triple_injective :
    Function.Injective (fun p : BitString × ℕ × BitString => triple p.1 p.2.1 p.2.2) := by
  intro p q h
  have := congrArg decodeTriple h
  simpa only [decodeTriple_triple, Option.some.injEq] using this

/-- Extension tuples are injective in the base triple and the last coordinate together.
Blueprint node `FoundationPrefixLiteralBound`. -/
theorem extensionCode_injective :
    Function.Injective (fun p : (BitString × ℕ × BitString) × BitString =>
      extensionCode p.1.1 p.1.2.1 p.1.2.2 p.2) := by
  intro p q h
  have hp : (triple p.1.1 p.1.2.1 p.1.2.2, p.2) =
      (triple q.1.1 q.1.2.1 q.1.2.2, q.2) := by
    apply pairCode_injective
    exact h
  exact Prod.ext (triple_injective (congrArg Prod.fst hp))
    (congrArg (Prod.snd : BitString × BitString → BitString) hp)

/-- The curried extension has an exact length with every tuple header accounted for.
Blueprint node `FoundationPrefixLiteralBound`. -/
theorem length_extensionCode (x w s : BitString) (q : ℕ) :
    (extensionCode x q w s).length =
      4 * x.length + 4 * (bits q).length + 2 * w.length + s.length + 5 := by
  simp only [extensionCode, length_pairCode, literal_and_tuple_code_interface_triple]
  omega

/-- The query encoder has exactly the fixed concatenation required by the target.
Blueprint node `FoundationPrefixLiteralBound`. -/
theorem encF_eq (x : BitString) (k : ℕ) : encF (x, k) = sd x ++ bits k := by
  simp [encF, sd, pairCode]

/-- The cumulative query has exact length, including the nonempty threshold code.
Blueprint node `FoundationPrefixLiteralBound`. -/
theorem length_encF (x : BitString) (k : ℕ) :
    (encF (x, k)).length = 2 * x.length + 1 + (bits k).length := by
  rw [encF_eq, List.length_append, length_sd]

/-- A query's target string is no longer than the complete query word.
Blueprint node `FoundationPrefixLiteralBound`. -/
theorem target_length_le_encF (x : BitString) (k : ℕ) : x.length ≤ (encF (x, k)).length := by
  rw [length_encF]
  omega

/-- Query decoding is a left inverse of query encoding.
Blueprint node `FoundationPrefixLiteralBound`. -/
theorem decodeQuery_encF (p : BitString × ℕ) : decodeQuery (encF p) = some p := by
  rcases p with ⟨x, k⟩
  simp [decodeQuery, encF, parseSd_pairCode, decodeNat_bits]

/-- The cumulative query representation is injective.
Blueprint node `FoundationPrefixLiteralBound`. -/
theorem encF_injective : Function.Injective encF := by
  intro p q h
  have := congrArg decodeQuery h
  simpa only [decodeQuery_encF, Option.some.injEq] using this

/-- The partial query inverse accepts exactly valid canonical encodings.
Blueprint node `FoundationPrefixLiteralBound`. -/
theorem decodeQuery_eq_some_iff (s : BitString) (p : BitString × ℕ) :
    decodeQuery s = some p ↔ encF p = s := by
  constructor
  · intro h
    dsimp [decodeQuery] at h
    rcases p with ⟨x, k⟩
    cases h1 : parseSd s with
    | none => 
      rw [h1] at h
      dsimp [bind, Option.bind] at h
      contradiction
    | some pair1 =>
      rcases pair1 with ⟨x', suffix⟩
      rw [h1] at h
      dsimp [bind, Option.bind] at h
      cases h2 : Milovanov.decodeNat suffix with
      | none =>
        rw [h2] at h
        dsimp [bind, Option.bind] at h
        contradiction
      | some k' =>
        rw [h2] at h
        dsimp [bind, Option.bind] at h
        injection h with h_eq
        injection h_eq with hx hk
        subst hx hk
        dsimp [parseSd] at h1
        split_ifs at h1 with hp
        · injection h1 with h1_eq
          injection h1_eq with hx_eq hs_eq
          subst hx_eq hs_eq
          dsimp [Milovanov.decodeNat] at h2
          split_ifs at h2 with hkb
          · injection h2 with hk_eq
            subst hk_eq
            dsimp [encF]
            rw [hkb]
            exact hp
  · intro h
    rw [← h, decodeQuery_encF]

/-- Halting words parse to their literal code index and data.
Blueprint node `native:halting-language`. -/
theorem decodeHaltWord_haltWord (e y : ℕ) : decodeHaltWord (haltWord e y) = some (e, y) := by
  simp [decodeHaltWord, haltWord, decodeQuery_encF, decodeNat_bits]

/-- Halting words uniquely identify both their code index and their data.
Blueprint node `native:halting-language`. -/
theorem haltWord_injective : Function.Injective (fun p : ℕ × ℕ => haltWord p.1 p.2) := by
  intro p q h
  have := congrArg decodeHaltWord h
  simpa only [decodeHaltWord_haltWord, Option.some.injEq] using this

/-- Halting words have length twice the binary data length plus the index length and one.
Blueprint node `native:halting-language`. -/
theorem length_haltWord (e y : ℕ) :
    (haltWord e y).length = 2 * (bits y).length + 1 + (bits e).length :=
  length_encF (bits y) e

private lemma bits_fn_computable : Computable bits := by
  have H : bits = fun n => bif decide (n = 0) then [false] else (Nat.bits n).reverse := by
    ext n
    simp [bits]
  rw [H]
  have h1 : Computable (fun (n : ℕ) => (Nat.bits n).reverse) :=
    (Primrec.list_reverse.comp primrec_natBits).to_comp
  have h2 : Computable (fun (n : ℕ) => [false]) :=
    Computable.const [false]
  have h3 : Computable (fun (n : ℕ) => decide (n = 0)) :=
    (PrimrecRel.decide (Primrec.eq (α := ℕ))).to_comp.comp
      Computable.id (Computable.const 0)
  exact Computable.cond h3 h2 h1

private lemma decodeNat_fn_computable : Computable decodeNat := by
  have H : decodeNat = fun w => let n := decodeBits w.reverse;
      bif decide (bits n = w) then some n else none := by
    ext w
    dsimp [decodeNat]
    split_ifs <;> simp [*]
  rw [H]
  have hn : Computable (fun (w : BitString) => decodeBits w.reverse) :=
    (primrec_decodeBits.comp Primrec.list_reverse).to_comp
  have h_bits_n : Computable (fun (w : BitString) => bits (decodeBits w.reverse)) :=
    bits_fn_computable.comp hn
  have h_cond : Computable (fun (w : BitString) => decide (bits (decodeBits w.reverse) = w)) :=
    (PrimrecRel.decide (Primrec.eq (α := BitString))).to_comp.comp
      h_bits_n Computable.id
  have h_some : Computable (fun (w : BitString) => some (decodeBits w.reverse)) :=
    Computable.option_some.comp hn
  have h_none : Computable (fun (w : BitString) => (none : Option ℕ)) :=
    Computable.const none
  exact Computable.cond h_cond h_some h_none

/-- Canonical binary encoding and its validated partial inverse are computable.
Blueprint node `FoundationPrefixLiteralBound`. -/
theorem bits_computable : Computable bits ∧ Computable decodeNat := by
  exact ⟨bits_fn_computable, decodeNat_fn_computable⟩

private lemma parseLiteral_core_computable :
  Computable₂ (fun (p : BitString × BitString) (n : ℕ) =>
    bif decide (n ≤ p.2.length) then some (p.2.take n, p.2.drop n) else none) := by
  have h_take : Computable₂ (fun (p : BitString × BitString) (n : ℕ) => p.2.take n) :=
    (Primrec.list_take.comp Primrec.snd (Primrec.snd.comp Primrec.fst)).to_comp
  have h_drop : Computable₂ (fun (p : BitString × BitString) (n : ℕ) => p.2.drop n) :=
    (Primrec.list_drop.comp Primrec.snd (Primrec.snd.comp Primrec.fst)).to_comp
  have h_len : Computable₂ (fun (p : BitString × BitString) (n : ℕ) => p.2.length) :=
    (Primrec.list_length.comp (Primrec.snd.comp Primrec.fst)).to_comp
  have h_cond : Computable₂ (fun (p : BitString × BitString) (n : ℕ) => decide (n ≤ p.2.length)) :=
    (PrimrecRel.decide (Primrec.nat_le)).to_comp.comp Computable.snd h_len
  have h_some : Computable₂ (fun (p : BitString × BitString) (n : ℕ) =>
      some (p.2.take n, p.2.drop n)) :=
    Computable.option_some.comp (h_take.pair h_drop)
  have h_none : Computable₂ (fun (p : BitString × BitString) (n : ℕ) =>
      (none : Option (BitString × BitString))) :=
    Computable.const none
  exact Computable.cond h_cond h_some h_none

private lemma parseLiteral_bind_computable : Computable (fun (p : BitString × BitString) =>
  Option.bind (decodeNat p.1) (fun n =>
    bif decide (n ≤ p.2.length) then some (p.2.take n, p.2.drop n) else none)) := by
  have h_dec : Computable (fun p : BitString × BitString => decodeNat p.1) :=
    bits_computable.2.comp Computable.fst
  have h_inner : Computable₂ (fun (p : BitString × BitString) (n : ℕ) =>
    bif decide (n ≤ p.2.length) then some (p.2.take n, p.2.drop n) else none) :=
    parseLiteral_core_computable
  exact Computable.option_bind h_dec h_inner

private lemma parseSd_computable : Computable parseSd := by
  have H : parseSd = fun w => 
    let p := (decodeFirst w, decodeSecond w)
    bif decide (pairCode p.1 p.2 = w) then some p else none := by
    funext w
    dsimp [parseSd]
    by_cases h : pairCode (decodeFirst w) (decodeSecond w) = w <;> simp [h]
  rw [H]
  have h_fst : Computable (fun w : BitString => decodeFirst w) := decodeFirst_computable
  have h_snd : Computable (fun w : BitString => decodeSecond w) := decodeSecond_computable
  have h_p : Computable (fun w : BitString => (decodeFirst w, decodeSecond w)) := h_fst.pair h_snd
  have h_pairCode : Computable (fun w : BitString => pairCode (decodeFirst w) (decodeSecond w)) :=
    Computable₂.comp pairCode_computable h_fst h_snd
  have h_cond : Computable (fun w : BitString =>
      decide (pairCode (decodeFirst w) (decodeSecond w) = w)) :=
    (PrimrecRel.decide (Primrec.eq (α := BitString))).to_comp.comp h_pairCode Computable.id
  have h_some : Computable (fun w : BitString => some (decodeFirst w, decodeSecond w)) :=
    Computable.option_some.comp h_p
  have h_none : Computable (fun (w : BitString) => (none : Option (BitString × BitString))) :=
    Computable.const none
  exact Computable.cond h_cond h_some h_none

private lemma parseLiteral_fn_computable : Computable parseLiteral := by
  have H : parseLiteral = fun w => Option.bind (parseSd w) (fun p =>
    Option.bind (decodeNat p.1) (fun n =>
      bif decide (n ≤ p.2.length) then some (p.2.take n, p.2.drop n) else none)) := by
    funext w
    dsimp [parseLiteral, bind, Option.bind]
    cases hp : parseSd w with
    | none => rfl
    | some p =>
      dsimp [Option.bind]
      cases hn : decodeNat p.1 with
      | none => rfl
      | some n =>
        dsimp [Option.bind]
        by_cases h : n ≤ p.2.length <;> simp [h]
  rw [H]
  have h1 : Computable parseSd := parseSd_computable
  have h2 : Computable₂ (fun (w : BitString) (p : BitString × BitString) =>
    Option.bind (decodeNat p.1) (fun n =>
      bif decide (n ≤ p.2.length) then some (p.2.take n, p.2.drop n) else none)) :=
    parseLiteral_bind_computable.comp Computable.snd
  exact Computable.option_bind h1 h2

private lemma sd_computable : Computable sd := by
  have H : sd = fun s => pairCode s [] := rfl
  rw [H]
  exact Computable₂.comp pairCode_computable Computable.id (Computable.const [])

private lemma integerCode_computable : Computable integerCode := by
  have H : integerCode = fun n => sd (bits n) := rfl
  rw [H]
  exact sd_computable.comp bits_computable.1

private lemma literalCode_encoder_computable : Computable literalCode := by
  have H : literalCode = fun s => integerCode s.length ++ s := rfl
  rw [H]
  have hlen : Computable (fun s : BitString => s.length) := Primrec.list_length.to_comp
  have hfst : Computable (fun s : BitString => integerCode s.length) :=
    integerCode_computable.comp hlen
  exact Computable₂.comp Primrec.list_append.to_comp hfst Computable.id

/-- Literal construction and validated streaming parsing are computable.
Blueprint node `FoundationPrefixLiteralBound`. -/
theorem literalCode_computable :
    Computable sd ∧ Computable parseSd ∧ Computable integerCode ∧
    Computable literalCode ∧ Computable parseLiteral := by
  exact ⟨sd_computable, parseSd_computable, integerCode_computable,
         literalCode_encoder_computable, parseLiteral_fn_computable⟩

/-- The fixed base triple and its partial inverse are computable.
Blueprint node `FoundationPrefixLiteralBound`. -/
theorem triple_computable :
    Computable (fun p : BitString × ℕ × BitString => triple p.1 p.2.1 p.2.2) ∧
      Computable decodeTriple := by
  constructor
  · have hd : (fun p : BitString × ℕ × BitString => triple p.1 p.2.1 p.2.2) = 
              (fun p => pairCode p.1 (pairCode (bits p.2.1) p.2.2)) := rfl
    rw [hd]
    have hinner : Computable (fun p : BitString × ℕ × BitString =>
        pairCode (bits p.2.1) p.2.2) := by
      have hq : Computable (fun p : BitString × ℕ × BitString => bits p.2.1) :=
        bits_computable.1.comp (Computable.fst.comp Computable.snd)
      have hw : Computable (fun p : BitString × ℕ × BitString => p.2.2) :=
        Computable.snd.comp Computable.snd
      exact Computable₂.comp pairCode_computable hq hw
    exact Computable₂.comp pairCode_computable Computable.fst hinner
  · have hd : decodeTriple = fun s => Option.bind (parseSd s) (fun p =>
      Option.bind (parseSd p.2) (fun p2 =>
        Option.bind (Milovanov.decodeNat p2.1) (fun n => some (p.1, n, p2.2)))) := by
      ext s
      dsimp [decodeTriple]
      cases parseSd s
      · rfl
      · rename_i p1
        cases parseSd p1.2
        · rfl
        · rfl
    rw [hd]
    have h1 : Computable parseSd := literalCode_computable.2.1
    have h3 : Computable₂ (fun (p1 : BitString × BitString) (p2 : BitString × BitString) =>
        Option.bind (Milovanov.decodeNat p2.1) (fun n => some (p1.1, n, p2.2))) := by
      have h3a : Computable (fun p : (BitString × BitString) × (BitString × BitString) =>
          Milovanov.decodeNat p.2.1) :=
        bits_computable.2.comp (Computable.fst.comp Computable.snd)
      have h3b : Computable₂ (fun (p : (BitString × BitString) × (BitString × BitString)) (n : ℕ) =>
          some (p.1.1, n, p.2.2)) := by
        exact Computable.option_some.comp (Computable.pair
          (Computable.fst.comp (Computable.fst.comp Computable.fst))
          (Computable.pair Computable.snd
            (Computable.snd.comp (Computable.snd.comp Computable.fst))))
      exact Computable.option_bind h3a h3b
    have h2 : Computable₂ (fun (s : BitString) (p1 : BitString × BitString) =>
        Option.bind (parseSd p1.2) (fun p2 =>
          Option.bind (Milovanov.decodeNat p2.1) (fun n => some (p1.1, n, p2.2)))) := by
      have h2a : Computable (fun p : BitString × (BitString × BitString) => parseSd p.2.2) :=
        literalCode_computable.2.1.comp (Computable.snd.comp Computable.snd)
      have h2b : Computable₂ (fun (p : BitString × (BitString × BitString))
          (p2 : BitString × BitString) =>
        Option.bind (Milovanov.decodeNat p2.1) (fun n => some (p.2.1, n, p2.2))) := by
        exact h3.comp (Computable.snd.comp Computable.fst) Computable.snd
      exact Computable.option_bind h2a h2b
    exact Computable.option_bind h1 h2

private lemma encF_fn_computable : Computable encF := by
  have : encF = fun p => pairCode p.1 (bits p.2) := rfl
  rw [this]
  exact Computable₂.comp pairCode_computable Computable.fst (bits_computable.1.comp Computable.snd)

private lemma decodeQuery_fn_computable : Computable decodeQuery := by
  have : decodeQuery = fun w => Option.bind (parseSd w)
      (fun p => Option.bind (Milovanov.decodeNat p.2) (fun k => some (p.1, k))) := by
    ext w
    dsimp [decodeQuery, bind, Option.bind]
    cases parseSd w <;> simp
  rw [this]
  have h1 : Computable₂ (fun (p : BitString × BitString) (k : ℕ) => some (p.1, k)) :=
    Computable.option_some.comp
      ((Computable.fst.comp Computable.fst).pair Computable.snd)
  have h2 : Computable (fun (p : BitString × BitString) =>
      Option.bind (Milovanov.decodeNat p.2) (fun k => some (p.1, k))) :=
    Computable.option_bind
      (bits_computable.2.comp Computable.snd) h1
  have h3 : Computable₂ (fun (w : BitString) (p : BitString × BitString) =>
      Option.bind (Milovanov.decodeNat p.2) (fun k => some (p.1, k))) :=
    h2.comp Computable.snd
  exact Computable.option_bind literalCode_computable.2.1 h3

/-- Query construction and canonical decoding are computable, uniformly in both fields.
Blueprint node `FoundationPrefixLiteralBound`. -/
theorem encF_computable : Computable encF ∧ Computable decodeQuery := by
  exact ⟨encF_fn_computable, decodeQuery_fn_computable⟩

/-- Halting-instance construction and canonical decoding are computable.
Blueprint node `native:halting-language`. -/
theorem haltWord_computable : Computable₂ haltWord ∧ Computable decodeHaltWord := by
  constructor
  · exact encF_computable.1.comp₂ <|
      (bits_computable.1.comp Computable.snd).pair Computable.fst
  · unfold decodeHaltWord
    apply Computable.option_bind encF_computable.2
    have h2 : Computable (fun (p : List Bool × ℕ) => decodeNat p.1) :=
      bits_computable.2.comp Computable.fst
    have h3 : Computable₂ (fun (p : List Bool × ℕ) (y : ℕ) => some (p.2, y)) :=
      Computable.option_some_iff.2 (Computable.snd.comp Computable.fst |>.pair Computable.snd)
    exact Computable.option_bind h2 h3 |>.comp Computable.snd

/-- The explicit prefix literal bound is uniform in the condition.
Blueprint node `FoundationPrefixLiteralBound`. -/
theorem literal_and_tuple_code_interface (B : Base) (a b : BitString) :
    KP B.D a b ≤ (literalBound B a : ENat) := B.literal_bound a b

/-- Binary naturals have a computable logarithmic prefix budget with a fixed overhead.
Blueprint node `FoundationPrefixLiteralBound`. -/
theorem literal_and_tuple_code_interface_integer (B : Base) :
    ∃ c : ℕ, ∀ t : ℕ, KPPlain B.D (bits t) ≤ (integerLiteralBound c t : ENat) := by
  use B.cD + 4
  intro t
  have h1 : KP B.D (bits t) [] ≤ (literalBound B (bits t) : ENat) := B.literal_bound (bits t) []
  have h2 : literalBound B (bits t) ≤ integerLiteralBound (B.cD + 4) t := by
    dsimp [literalBound, integerLiteralBound]
    set C := Nat.clog 2 (t + 2)
    set l := (bits t).length
    have hlC : l ≤ C := by
      have h4 := length_integerCode_le t
      have h3 : 2 * l + 1 = (integerCode t).length := by
        dsimp [integerCode]
        rw [length_sd]
      omega
    have hlog : Nat.clog 2 (l + 2) ≤ Nat.clog 2 (C + 2) := Nat.clog_mono_right 2 (by omega)
    have hsmall : ∀ n : ℕ, 2 * Nat.clog 2 (n + 2) ≤ n + 4 := by
      intro n
      have hpow : n + 2 ≤ 2 ^ ((n + 4) / 2) := by
        induction n using Nat.strong_induction_on with
        | h n ih =>
        cases n with
        | zero => decide
        | succ n =>
          cases n with
          | zero => decide
          | succ n =>
            have ih2 := ih n (by omega)
            have h3 : 2 ≤ 2 ^ ((n + 4) / 2) := by
              have h4 : 1 ≤ (n + 4) / 2 := by omega
              calc
                2 = 2 ^ 1 := by ring
                _ ≤ 2 ^ ((n + 4) / 2) := Nat.pow_le_pow_right (by norm_num) h4
            calc
              n + 1 + 1 + 2 = (n + 2) + 2 := by omega
              _ ≤ 2 ^ ((n + 4) / 2) + 2 := Nat.add_le_add_right ih2 2
              _ ≤ 2 ^ ((n + 4) / 2) + 2 ^ ((n + 4) / 2) := Nat.add_le_add_left h3 _
              _ = 2 * 2 ^ ((n + 4) / 2) := by omega
              _ = 2 ^ ((n + 4) / 2 + 1) := by ring
              _ ≤ 2 ^ ((n + 2 + 4) / 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hlog : Nat.clog 2 (n + 2) ≤ (n + 4) / 2 :=
        (Nat.clog_le_iff_le_pow (by norm_num : 1 < 2)).2 hpow
      omega
    have hbound := hsmall C
    omega
  rw [KPPlain_eq_KP]
  exact le_trans h1 (by exact_mod_cast h2)

/-- The literal upper bound used by the stage algorithm is computable.
Blueprint node `FoundationPrefixLiteralBound`. -/
theorem literalBound_computable (B : Base) : Computable (literalBound B) := by
  have hlen : Primrec (fun a : BitString => a.length) := Primrec.list_length
  have hlog : Primrec (fun n : ℕ => Nat.clog 2 n) := Kolmogorov.primrec_clogTwo
  have h : Primrec (literalBound B) := by
    change Primrec (fun a : BitString =>
      a.length + 2 * Nat.clog 2 (a.length + 2) + B.cD)
    exact Primrec.nat_add.comp (Primrec.nat_add.comp hlen
      (Primrec.nat_mul.comp (Primrec.const 2)
        (hlog.comp (Primrec.nat_add.comp hlen (Primrec.const 2)))))
      (Primrec.const B.cD)
  exact h.to_comp

/-- A fixed computable output transformation costs a constant in conditional prefix complexity.
Blueprint node `FoundationPrefixLiteralBound`. -/
theorem literal_and_tuple_code_interface_prefix_map (B : Base)
    (f : BitString → BitString) (hf : Computable f) :
    ∃ c : ℕ, ∀ a b, KP B.D (f a) b ≤ KP B.D a b + c :=
  KP_map_le B.D B.optimalD f hf

/-- A fixed computable output transformation costs a constant in conditional plain complexity.
Blueprint node `FoundationPrefixLiteralBound`. -/
theorem literal_and_tuple_code_interface_plain_map (B : Base)
    (f : BitString → BitString) (hf : Computable f) :
    ∃ c : ℕ, ∀ a b, condK B.V (f a) b ≤ condK B.V a b + c :=
  condK_map_le B.V B.optimalV f hf

end Kolmogorov.Milovanov
