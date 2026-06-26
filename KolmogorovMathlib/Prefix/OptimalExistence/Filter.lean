/-
Copyright (c) 2024 Alexey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey
-/
import KolmogorovMathlib.Prefix.Optimal
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

end Kolmogorov
