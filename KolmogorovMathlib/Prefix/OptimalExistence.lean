/-
Copyright (c) 2024 Alexey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey
-/
import KolmogorovMathlib.Prefix.Optimal
import KolmogorovMathlib.Prefix.Combinators
import KolmogorovMathlib.AlgorithmicProbability.SimulationComplexity
import KolmogorovMathlib.AlgorithmicProbability.TaggedUnionUniversal
import KolmogorovMathlib.Core.Invariance
import Mathlib

/-!
# Existence of an Optimal Prefix Conditional Decompressor

This module proves the final non-vacuity theorems for the prefix-complexity
interfaces: there exists a simulation-universal prefix decompressor, hence an
optimal prefix conditional decompressor.
The construction enumerates all partial recursive maps via `Nat.Partrec.Code`.
For each code `c`, `prefixFiltered c` is an *online prefix filter*: it accepts a
program `p` in context `y` only when accepting it preserves prefix-freeness among
the already-accepted programs. This always yields a prefix machine, and it leaves
an already-prefix-free machine unchanged. Tagging the resulting family with the
self-delimiting unary code (`taggedUnion`) gives a single universal prefix
machine.

## The online filter

Fix a code `c` and context `y`. We dovetail the halting computations of `c`: at
dovetail index `n`, the candidate program is `Encodable.decode n.unpair.1`, and it
"appears" if `c` halts on it within `n.unpair.2 + 1` steps (`appearsAt`). Each
program appears at a least index (its priority); distinct programs never share an
index because the index determines the decoded program.

A program `p` is *accepted* when it appears at some index `N` (its first
appearance) and **no** earlier-appearing program `q ≠ p` is comparable to `p`
under the prefix order (`acceptBefore`). Two distinct comparable accepted programs
would contradict this at whichever has the smaller first index, so the accepted
set is prefix-free. If `c`'s halting domain is already prefix-free, no program is
ever rejected, so the filter is the identity.
-/

namespace Kolmogorov

open Nat.Partrec (Code)

/-! ### The online prefix filter -/

/-- The candidate program (if any) "appearing" at dovetail index `n` in context
`y` for the fixed code `c`: decode `n.unpair.1` to a program `p`, and accept it
iff `c` halts on `(p, y)` within `n.unpair.2 + 1` steps. -/
def appearsAt (c : Code) (y : BitString) (n : ℕ) : Option BitString :=
  (Encodable.decode n.unpair.1 : Option BitString).bind fun p =>
    if (Code.evaln (n.unpair.2 + 1) c (Encodable.encode (p, y))).isSome then
      some p
    else
      none

/-- The local prefix-freeness test at index `n`: the program appearing at `n`
(if any) must not be a distinct prefix-comparable competitor of `p`. -/
def goodAt (c : Code) (y p : BitString) (n : ℕ) : Bool :=
  match appearsAt c y n with
  | none => true
  | some q => decide ¬ (q ≠ p ∧ (q <+: p ∨ p <+: q))

/-- The accumulated acceptance test over the first `N` dovetail indices: every
program appearing strictly before index `N` passes the local test against `p`. -/
def acceptBefore (c : Code) (y p : BitString) (N : ℕ) : Bool :=
  (List.range N).foldr (fun n acc => goodAt c y p n && acc) true

/-- The **prefix-filtered machine** of a code `c`. On `(p, y)` it searches for the
first index `N` at which `p` appears (diverging if `p` never halts), checks that no
earlier-appearing comparable competitor exists (`acceptBefore`), and if so returns
the decoded output of `c`; otherwise it diverges. -/
def prefixFiltered (c : Code) : Map := fun pr =>
  (Nat.rfind fun n => Part.some (decide (appearsAt c pr.2 n = some pr.1))).bind fun N =>
    bif acceptBefore c pr.2 pr.1 N then
      (c.eval (Encodable.encode pr)).map
        (fun r => (Encodable.decode r : Option BitString).getD [])
    else
      Part.none

/-! ### Elementary facts about `appearsAt` -/

/-- If a program appears at index `n`, it is exactly the decoding of `n.unpair.1`. -/
theorem appearsAt_eq_some_decode {c : Code} {y : BitString} {n : ℕ} {p : BitString}
    (h : appearsAt c y n = some p) :
    (Encodable.decode n.unpair.1 : Option BitString) = some p := by
  unfold appearsAt at h
  cases hd : (Encodable.decode n.unpair.1 : Option BitString) with
  | none => rw [hd] at h; simp at h
  | some p' => rw [hd] at h; simp only [Option.bind] at h; split at h <;> simp_all

/-- If a program appears at index `n`, then `c` halts on it within the recorded
step bound. -/
theorem appearsAt_isSome {c : Code} {y : BitString} {n : ℕ} {p : BitString}
    (h : appearsAt c y n = some p) :
    (Code.evaln (n.unpair.2 + 1) c (Encodable.encode (p, y))).isSome = true := by
  have hd := appearsAt_eq_some_decode h
  unfold appearsAt at h
  rw [hd] at h
  simp only [Option.bind] at h
  split at h
  · assumption
  · simp at h

/-- If a program appears at some index, then `c` halts on it. -/
theorem appearsAt_eval_dom {c : Code} {y : BitString} {n : ℕ} {p : BitString}
    (h : appearsAt c y n = some p) :
    (c.eval (Encodable.encode (p, y))).Dom := by
  have hs := appearsAt_isSome h
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hs
  exact Part.dom_iff_mem.mpr ⟨x, Nat.Partrec.Code.evaln_complete.mpr ⟨_, hx⟩⟩

/-- A program appears at some index iff `c` halts on it. -/
theorem exists_appearsAt_iff_eval_dom {c : Code} {y p : BitString} :
    (∃ n, appearsAt c y n = some p) ↔ (c.eval (Encodable.encode (p, y))).Dom := by
  constructor
  · rintro ⟨n, hn⟩; exact appearsAt_eval_dom hn
  · intro h
    obtain ⟨x, hx⟩ := Part.dom_iff_mem.mp h
    obtain ⟨k, hk⟩ := Nat.Partrec.Code.evaln_complete.mp hx
    refine ⟨Nat.pair (Encodable.encode p) k, ?_⟩
    unfold appearsAt
    simp only [Nat.unpair_pair, Encodable.encodek]
    have hh : (Code.evaln (k + 1) c (Encodable.encode (p, y))).isSome = true := by
      rw [Option.isSome_iff_exists]
      exact ⟨x, Nat.Partrec.Code.evaln_mono (Nat.le_succ k) hk⟩
    change (if (Code.evaln (k + 1) c (Encodable.encode (p, y))).isSome then some p else none)
        = some p
    rw [if_pos hh]

/-! ### Acceptance characterisation -/

/-- A conjunctive `foldr` over a list is `true` iff each entry is `true`. -/
private theorem foldr_and_true_iff (l : List ℕ) (f : ℕ → Bool) :
    (l.foldr (fun n acc => f n && acc) true) = true ↔ ∀ n ∈ l, f n = true := by
  induction l with
  | nil => simp
  | cons a t ih => simp [ih]

/-- `acceptBefore` holds iff every index below `N` passes the local test. -/
theorem acceptBefore_eq_true_iff {c : Code} {y p : BitString} {N : ℕ} :
    acceptBefore c y p N = true ↔ ∀ n < N, goodAt c y p n = true := by
  unfold acceptBefore
  rw [foldr_and_true_iff]
  simp [List.mem_range]

/-- The local test fails at `n` exactly when a distinct comparable competitor of
`p` appears at `n`. -/
theorem goodAt_eq_false_iff {c : Code} {y p : BitString} {n : ℕ} :
    goodAt c y p n = false ↔
      ∃ q, appearsAt c y n = some q ∧ q ≠ p ∧ (q <+: p ∨ p <+: q) := by
  unfold goodAt
  cases h : appearsAt c y n with
  | none => simp
  | some q =>
    constructor
    · intro hf
      refine ⟨q, rfl, ?_⟩
      simp only [decide_eq_false_iff_not, not_not] at hf
      exact hf
    · rintro ⟨q', hq', hne, hcomp⟩
      obtain rfl := Option.some.inj hq'
      simp only [decide_eq_false_iff_not, not_not]
      exact ⟨hne, hcomp⟩

/-! ### Membership characterisation of the filter -/

/-- Membership in `prefixFiltered c (p, y)`: there is a first appearance index `N`
of `p`, no earlier comparable competitor exists, and the output is the decoded
result of `c`. -/
theorem mem_prefixFiltered_iff {c : Code} {p y x : BitString} :
    x ∈ prefixFiltered c (p, y) ↔
      ∃ N, (appearsAt c y N = some p ∧ ∀ m < N, appearsAt c y m ≠ some p) ∧
        acceptBefore c y p N = true ∧
        x ∈ (c.eval (Encodable.encode (p, y))).map
              (fun r => (Encodable.decode r : Option BitString).getD []) := by
  unfold prefixFiltered
  simp only [Part.mem_bind_iff, Nat.mem_rfind, Part.mem_some_iff]
  constructor
  · rintro ⟨N, ⟨hN, hlt⟩, hmem⟩
    refine ⟨N, ⟨of_decide_eq_true hN.symm, ?_⟩, ?_⟩
    · intro m hm; exact of_decide_eq_false (hlt hm).symm
    · cases hb : acceptBefore c y p N with
      | true => rw [hb] at hmem; exact ⟨rfl, by simpa using hmem⟩
      | false => rw [hb] at hmem; simp at hmem
  · rintro ⟨N, ⟨hN, hlt⟩, hacc, hmem⟩
    refine ⟨N, ⟨?_, ?_⟩, ?_⟩
    · rw [hN]; exact (decide_eq_true rfl).symm
    · intro m hm; exact (decide_eq_false (hlt m hm)).symm
    · rw [hacc]; simpa using hmem

/-! ### The filter is a prefix machine -/

/-- The filtered machine has a prefix-free halting domain in every context. -/
theorem prefixFiltered_isPrefixMachine (c : Code) :
    IsPrefixMachine (prefixFiltered c) := by
  intro y p hp q hq hpre
  by_contra hne
  obtain ⟨xp, hxp⟩ := Part.dom_iff_mem.mp hp
  obtain ⟨Np, ⟨hNp, _⟩, haccp, _⟩ := mem_prefixFiltered_iff.mp hxp
  obtain ⟨xq, hxq⟩ := Part.dom_iff_mem.mp hq
  obtain ⟨Nq, ⟨hNq, _⟩, haccq, _⟩ := mem_prefixFiltered_iff.mp hxq
  have hNneq : Np ≠ Nq := by
    intro h; rw [h] at hNp; rw [hNp] at hNq; exact hne (Option.some.inj hNq)
  rcases lt_or_gt_of_ne hNneq with hlt | hgt
  · have hgood := (acceptBefore_eq_true_iff.mp haccq) Np hlt
    have hbad : goodAt c y q Np = false := by
      rw [goodAt_eq_false_iff]; exact ⟨p, hNp, hne, Or.inl hpre⟩
    rw [hbad] at hgood; simp at hgood
  · have hgood := (acceptBefore_eq_true_iff.mp haccp) Nq hgt
    have hbad : goodAt c y p Nq = false := by
      rw [goodAt_eq_false_iff]; exact ⟨q, hNq, fun h => hne h.symm, Or.inr hpre⟩
    rw [hbad] at hgood; simp at hgood

/-! ### The filter preserves existing prefix decompressors -/

/-- If `c` codes a map `M` whose halting domain is prefix-free, the filter is the
identity on `M`. -/
theorem prefixFiltered_eq_of_isPrefixDecompressor {M : Map} (c : Code)
    (hM : IsPrefixDecompressor M)
    (hc : ∀ p y,
      (c.eval (Encodable.encode (p, y))).map
        (fun r => (Encodable.decode r : Option BitString).getD []) = M (p, y)) :
    prefixFiltered c = M := by
  funext pr
  obtain ⟨p, y⟩ := pr
  apply Part.ext
  intro x
  rw [mem_prefixFiltered_iff, ← hc p y]
  constructor
  · rintro ⟨N, _, _, hmem⟩; exact hmem
  · intro hmem
    obtain ⟨a, ha, _⟩ := (Part.mem_map_iff _).mp hmem
    have hpdom : (c.eval (Encodable.encode (p, y))).Dom := Part.dom_iff_mem.mpr ⟨a, ha⟩
    have h_ex : ∃ n, appearsAt c y n = some p := exists_appearsAt_iff_eval_dom.mpr hpdom
    classical
    refine ⟨Nat.find h_ex, ⟨Nat.find_spec h_ex, fun m hm => Nat.find_min h_ex hm⟩, ?_, hmem⟩
    rw [acceptBefore_eq_true_iff]
    intro n hn
    by_contra hbad
    rw [Bool.not_eq_true] at hbad
    obtain ⟨q, hq_app, hqne, hcomp⟩ := goodAt_eq_false_iff.mp hbad
    have hqdom_eval : (c.eval (Encodable.encode (q, y))).Dom := appearsAt_eval_dom hq_app
    have hqdom : (M (q, y)).Dom := by
      rw [← hc q y]
      obtain ⟨v, hv⟩ := Part.dom_iff_mem.mp hqdom_eval
      exact Part.dom_iff_mem.mpr ⟨_, Part.mem_map _ hv⟩
    have hpdomM : (M (p, y)).Dom := by
      rw [← hc p y]
      obtain ⟨v, hv⟩ := Part.dom_iff_mem.mp hpdom
      exact Part.dom_iff_mem.mpr ⟨_, Part.mem_map _ hv⟩
    have hpref := hM.isPrefixMachine y
    have hqmem : q ∈ domainAt M y := hqdom
    have hpmem : p ∈ domainAt M y := hpdomM
    rcases hcomp with h1 | h2
    · exact hqne (hpref hqmem hpmem h1)
    · exact hqne (hpref hpmem hqmem h2).symm

/-! ### Uniform computability of the filter -/

/-- Equality of two values is a primitive recursive predicate (as a `Bool`). -/
private theorem primrec_decide_eq {α} [Primcodable α] [DecidableEq α] :
    Primrec (fun p : α × α => decide (p.1 = p.2)) := by
  obtain ⟨inst, h⟩ := (Primrec.eq : PrimrecRel (@Eq α))
  exact h.of_eq (fun p => by congr 1)

/-- Strict order on `ℕ` is a primitive recursive predicate (as a `Bool`). -/
private theorem primrec_decide_lt :
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
private theorem primrec_bitString_drop :
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

/-! ### Enumerated family of prefix decompressors -/

/-- Enumerated family of prefix decompressors. -/
def enumeratedPrefixMachine (i : ℕ) : Map :=
  match Encodable.decode i with
  | some c => prefixFiltered c
  | none => fun _ => Part.none

theorem enumeratedPrefixMachine_isPrefixDecompressor (i : ℕ) :
    IsPrefixDecompressor (enumeratedPrefixMachine i) := by
  unfold enumeratedPrefixMachine
  cases (Encodable.decode i : Option Code) with
  | none =>
    exact ⟨Partrec.none, by
      intro y p hp q hq hpre
      exact False.elim hp⟩
  | some c =>
    exact prefixFiltered_isPrefixDecompressor c

theorem exists_enumeratedPrefixMachine_eq {M : Map} (hM : IsPrefixDecompressor M) :
    ∃ i, enumeratedPrefixMachine i = M := by
  obtain ⟨c, hc⟩ := existsCodeOfIsDecompressor M hM.isDecompressor
  use Encodable.encode c
  unfold enumeratedPrefixMachine
  rw [Encodable.encodek]
  exact prefixFiltered_eq_of_isPrefixDecompressor c hM hc

/-- The enumerated family, rewritten as an option-bind on the decoded code. -/
theorem enumeratedPrefixMachine_eq_bind (i : ℕ) (z : BitString × BitString) :
    enumeratedPrefixMachine i z =
      (Part.ofOption (Encodable.decode i : Option Code)).bind
        (fun c => prefixFiltered c z) := by
  unfold enumeratedPrefixMachine
  cases (Encodable.decode i : Option Code) with
  | none => simp
  | some c => simp

/-- The enumerated family is uniformly partial recursive in the index and input. -/
theorem enumeratedPrefixMachine_uniform_partrec :
    Partrec (fun t : ℕ × BitString × BitString => enumeratedPrefixMachine t.1 t.2) := by
  have hrw : (fun t : ℕ × BitString × BitString => enumeratedPrefixMachine t.1 t.2)
      = fun t => (Part.ofOption (Encodable.decode t.1 : Option Code)).bind
          (fun c => prefixFiltered c t.2) :=
    funext fun t => enumeratedPrefixMachine_eq_bind t.1 t.2
  rw [hrw]
  apply Partrec.bind
  · exact Computable.ofOption (Computable.decode.comp Computable.fst)
  · have hmap : Computable (fun s : (ℕ × BitString × BitString) × Code =>
        ((s.2, s.1.2) : Code × BitString × BitString)) :=
      Computable.snd.pair (Computable.snd.comp Computable.fst)
    exact (prefixFiltered_uniform_partrec.comp hmap).of_eq (fun s => rfl)

/-! ### The universal prefix machine -/

/-- A tagged union of a uniformly partial-recursive family is partial recursive. -/
theorem taggedUnion_isDecompressor_of_uniform {M : ℕ → Map}
    (hM : Partrec (fun t : ℕ × BitString × BitString => M t.1 t.2)) :
    isDecompressor (taggedUnion M) := by
  have hidxP : Primrec (fun pr : BitString × BitString => (pr.1.takeWhile id).length) :=
    (Primrec.list_findIdx Primrec.fst (Primrec.not.comp Primrec.snd).to₂).of_eq
      (fun pr => (takeWhile_id_length_eq_findIdx pr.1).symm)
  have hdropP : Primrec (fun pr : BitString × BitString =>
      pr.1.drop ((pr.1.takeWhile id).length + 1)) :=
    primrec_bitString_drop.comp Primrec.fst (Primrec.succ.comp hidxP)
  have hguard : Computable (fun pr : BitString × BitString =>
      decide ((pr.1.takeWhile id).length < pr.1.length)) :=
    (Primrec.to_comp primrec_decide_lt).comp
      ((Primrec.to_comp hidxP).pair (Primrec.to_comp (Primrec.list_length.comp Primrec.fst)))
  have hcall : Partrec (fun pr : BitString × BitString =>
      M ((pr.1.takeWhile id).length) (pr.1.drop ((pr.1.takeWhile id).length + 1), pr.2)) := by
    have hmap : Computable (fun pr : BitString × BitString =>
        (((pr.1.takeWhile id).length, (pr.1.drop ((pr.1.takeWhile id).length + 1), pr.2)) :
          ℕ × BitString × BitString)) :=
      (Primrec.to_comp hidxP).pair ((Primrec.to_comp hdropP).pair Computable.snd)
    exact (hM.comp hmap).of_eq (fun pr => rfl)
  refine (Partrec.cond hguard hcall Partrec.none).of_eq (fun pr => ?_)
  simp only [taggedUnion]
  by_cases h : (pr.1.takeWhile id).length < pr.1.length <;> simp [h]

/-- The universal prefix machine. -/
def universalPrefixMachine : Map := taggedUnion enumeratedPrefixMachine

/-- The effective tagged union of the enumerated filtered machines is partial
recursive. -/
theorem universalPrefixMachine_isDecompressor :
    isDecompressor universalPrefixMachine :=
  taggedUnion_isDecompressor_of_uniform enumeratedPrefixMachine_uniform_partrec

theorem universalPrefixMachine_isPrefixDecompressor :
    IsPrefixDecompressor universalPrefixMachine := by
  exact ⟨universalPrefixMachine_isDecompressor,
    taggedUnion_isPrefixMachine
      (fun i => (enumeratedPrefixMachine_isPrefixDecompressor i).isPrefixMachine)⟩

/-! ### Universal machine simulation -/

theorem universalPrefixMachine_isSimulationUniversal :
    IsSimulationUniversal universalPrefixMachine := by
  refine ⟨universalPrefixMachine_isPrefixDecompressor, fun M hM => ?_⟩
  obtain ⟨i, hi⟩ := exists_enumeratedPrefixMachine_eq hM
  use i + 1
  have h_sim := taggedUnionSimulation enumeratedPrefixMachine i
  rw [hi] at h_sim
  exact ⟨h_sim⟩

/-! ### Final existence theorems -/

theorem exists_isSimulationUniversal : Exists fun U : Map => IsSimulationUniversal U :=
  ⟨universalPrefixMachine, universalPrefixMachine_isSimulationUniversal⟩

theorem exists_isOptimalPrefixConditional : Exists fun U : Map => IsOptimalPrefixConditional U := by
  obtain ⟨U, hU⟩ := exists_isSimulationUniversal
  exact ⟨U, hU.isOptimalPrefixConditional⟩

end Kolmogorov
