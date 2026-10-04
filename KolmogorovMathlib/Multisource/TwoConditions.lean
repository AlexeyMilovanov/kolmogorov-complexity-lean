/-
Copyright (c) 2026 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Combinatorics.HashFamily
import KolmogorovMathlib.Multisource.FingerprintLadder
import KolmogorovMathlib.Multisource.Requests
import KolmogorovMathlib.AlgorithmicStatistics.Selector
import KolmogorovMathlib.CommonInformation.ConditionalCounting
import KolmogorovMathlib.Foundation.EnumerationComplexity
import KolmogorovMathlib.Interface.Dovetailing

/-!
# Conditional codes for two conditions

Muchnik's second theorem: one message `X` serves two decoders at once, one knowing `A` and the
other knowing `B`, both having to restore the same string `C`; and `X` itself is simple given
`C`.  Theorem 235 refines this when the two conditional complexities differ: the shorter
decoder only reads a prefix of `X`.  The proof replaces the expander of Section 12.3 by the
hash family of `exists_prefixHashFamily`.

The section closes with the impossibility of a *universal* fingerprint: no string of `n/2`
bits (and no fixed number of such strings) lets one restore an incompressible `A` from an
arbitrary `B` with `C(A|B) ≤ n/2`.

The requests of Figures 42 and 43 are `restoreFromEitherRequest` and
`restoreFromEitherInformedRequest`, with the cuts giving their conditions (part of
Problem 327).

Complexity is plain `C`.

SUV Section 12.7, pp. 379–383.
-/

namespace Kolmogorov

open CodedFiniteDistribution

private theorem sort_034 : ({0, 3, 4} : Finset (Fin 6)).sort (· ≤ ·) = [0, 3, 4] := by
  simpa using (List.toFinset_sort (r := (· ≤ ·)) (l := [0, 3, 4]) (by simp)).2 (by simp)

private theorem sort_135 : ({1, 3, 5} : Finset (Fin 6)).sort (· ≤ ·) = [1, 3, 5] := by
  simpa using (List.toFinset_sort (r := (· ≤ ·)) (l := [1, 3, 5]) (by simp)).2 (by simp)

/-- The request of SUV Figure 42 on six nodes: `0`, `1`, `2` hold `A`, `B`, `C`, the channel
`2 → 3` has capacity `k`, the relay `3` reaches both output nodes, and the output nodes `4`
and `5` — reached also from `0` and from `1` respectively — must produce `C`.  All other
channels are unlimited.

SUV Figure 42, p. 379. -/
def restoreFromEitherRequest (A B C : BitString) (k : ℕ) : InformationRequest (Fin 6) where
  edges := {(2, 3), (3, 4), (3, 5), (0, 4), (1, 5)}
  rank v := if v.val ≤ 2 then 0 else if v.val = 3 then 1 else 2
  rank_lt := by decide +kernel
  capacity e := if e = (2, 3) then (k : ℕ∞) else ⊤
  input v := if v = 0 then some A else if v = 1 then some B else if v = 2 then some C else none
  output v := if v = 4 ∨ v = 5 then some C else none

/-- The two cuts of SUV Figure 42.  The cut `{0, 3, 4}` (the node of `A`, the relay and the
left output) and the cut `{1, 3, 5}` are each entered only by the channel of capacity `k`;
their inputs are `A` and `B` and their outputs `C`, which gives the conditions `C(C|A) ≤ k` and
`C(C|B) ≤ k` of Theorem 234.

SUV Problem 327, p. 384. -/
theorem restoreFromEitherRequest_cuts (A B C : BitString) (k : ℕ) :
    ((restoreFromEitherRequest A B C k).cutCapacity {0, 3, 4} = (k : ℕ∞) ∧
      (restoreFromEitherRequest A B C k).cutInputs {0, 3, 4} = [A] ∧
      (restoreFromEitherRequest A B C k).cutOutputs {0, 3, 4} = [C]) ∧
    ((restoreFromEitherRequest A B C k).cutCapacity {1, 3, 5} = (k : ℕ∞) ∧
      (restoreFromEitherRequest A B C k).cutInputs {1, 3, 5} = [B] ∧
      (restoreFromEitherRequest A B C k).cutOutputs {1, 3, 5} = [C]) := by
  have hcut034 : (restoreFromEitherRequest A B C k).cutEdges {0, 3, 4} = {(2, 3)} := by
    change (({(2, 3), (3, 4), (3, 5), (0, 4), (1, 5)} : Finset (Fin 6 × Fin 6)).filter fun e =>
      e.1 ∉ ({0, 3, 4} : Finset (Fin 6)) ∧ e.2 ∈ ({0, 3, 4} : Finset (Fin 6))) = _
    decide +kernel
  have hcut135 : (restoreFromEitherRequest A B C k).cutEdges {1, 3, 5} = {(2, 3)} := by
    change (({(2, 3), (3, 4), (3, 5), (0, 4), (1, 5)} : Finset (Fin 6 × Fin 6)).filter fun e =>
      e.1 ∉ ({1, 3, 5} : Finset (Fin 6)) ∧ e.2 ∈ ({1, 3, 5} : Finset (Fin 6))) = _
    decide +kernel
  simp only [InformationRequest.cutCapacity, hcut034, hcut135, InformationRequest.cutInputs,
    InformationRequest.cutOutputs, sort_034, sort_135]
  simp [restoreFromEitherRequest]

/-- The request of SUV Figure 43: Figure 42 with two additional unlimited channels `0 → 2` and
`1 → 2`, so that the encoder of `C` also knows `A` and `B`.

SUV Figure 43, p. 380. -/
def restoreFromEitherInformedRequest (A B C : BitString) (k : ℕ) :
    InformationRequest (Fin 6) where
  edges := {(0, 2), (1, 2), (2, 3), (3, 4), (3, 5), (0, 4), (1, 5)}
  rank v := if v.val ≤ 1 then 0 else v.val - 1
  rank_lt := by decide +kernel
  capacity e := if e = (2, 3) then (k : ℕ∞) else ⊤
  input v := if v = 0 then some A else if v = 1 then some B else if v = 2 then some C else none
  output v := if v = 4 ∨ v = 5 then some C else none

/-- The two cuts of SUV Figure 43 are those of Figure 42: the additional channels leave the
cuts `{0, 3, 4}` and `{1, 3, 5}` instead of entering them, so the conditions are again
`C(C|A) ≤ k` and `C(C|B) ≤ k`.

SUV Problem 327, p. 384. -/
theorem restoreFromEitherInformedRequest_cuts (A B C : BitString) (k : ℕ) :
    ((restoreFromEitherInformedRequest A B C k).cutCapacity {0, 3, 4} = (k : ℕ∞) ∧
      (restoreFromEitherInformedRequest A B C k).cutInputs {0, 3, 4} = [A] ∧
      (restoreFromEitherInformedRequest A B C k).cutOutputs {0, 3, 4} = [C]) ∧
    ((restoreFromEitherInformedRequest A B C k).cutCapacity {1, 3, 5} = (k : ℕ∞) ∧
      (restoreFromEitherInformedRequest A B C k).cutInputs {1, 3, 5} = [B] ∧
      (restoreFromEitherInformedRequest A B C k).cutOutputs {1, 3, 5} = [C]) := by
  have hcut034 :
      (restoreFromEitherInformedRequest A B C k).cutEdges {0, 3, 4} = {(2, 3)} := by
    change (({(0, 2), (1, 2), (2, 3), (3, 4), (3, 5), (0, 4), (1, 5)} :
      Finset (Fin 6 × Fin 6)).filter fun e =>
        e.1 ∉ ({0, 3, 4} : Finset (Fin 6)) ∧ e.2 ∈ ({0, 3, 4} : Finset (Fin 6))) = _
    decide +kernel
  have hcut135 :
      (restoreFromEitherInformedRequest A B C k).cutEdges {1, 3, 5} = {(2, 3)} := by
    change (({(0, 2), (1, 2), (2, 3), (3, 4), (3, 5), (0, 4), (1, 5)} :
      Finset (Fin 6 × Fin 6)).filter fun e =>
        e.1 ∉ ({1, 3, 5} : Finset (Fin 6)) ∧ e.2 ∈ ({1, 3, 5} : Finset (Fin 6))) = _
    decide +kernel
  simp only [InformationRequest.cutCapacity, hcut034, hcut135, InformationRequest.cutInputs,
    InformationRequest.cutOutputs, sort_034, sort_135]
  simp [restoreFromEitherInformedRequest]

/-- The bad right vertices of the proof of Theorem 235: the `m`-bit fingerprint prefixes
`[χ_i(x)]_m` that are hit by more than `T` pairs `(i, x)` with `x ∈ S` — in the book, the
vertices of `𝔹^k` with more than `n^c` neighbours in `S_A` (multiple edges counted).

SUV Section 12.7, p. 382. -/
def richPrefixValues {N : ℕ} (χ : Fin N → BitString → BitString) (m : ℕ)
    (S : Finset BitString) (T : ℕ) : Finset BitString :=
  ((Finset.univ ×ˢ S).image fun p : Fin N × BitString => prefixBits m (χ p.1 p.2)).filter
    fun u => T < ((Finset.univ ×ˢ S).filter
      fun p : Fin N × BitString => prefixBits m (χ p.1 p.2) = u).card

/-- Counting the bad right vertices: the bipartite graph between `S` and the fingerprint
prefixes has `N · |S|` edges (one per pair `(i, x)`), a bad vertex carries more than `T` of
them, so there are fewer than `N · |S| / T` bad vertices.

SUV Section 12.7, p. 382 (the bound `2N · 2^k / n^c`). -/
theorem card_richPrefixValues_mul_le {N : ℕ} (χ : Fin N → BitString → BitString) (m : ℕ)
    (S : Finset BitString) (T : ℕ) :
    (richPrefixValues χ m S T).card * T ≤ N * S.card := by
  classical
  set E : Finset (Fin N × BitString) := Finset.univ ×ˢ S with hE
  set f : Fin N × BitString → BitString := fun p => prefixBits m (χ p.1 p.2) with hf
  have hsum : ∑ u ∈ richPrefixValues χ m S T, (E.filter fun p => f p = u).card ≤ E.card := by
    rw [← Finset.card_biUnion]
    · exact Finset.card_le_card (Finset.biUnion_subset.2 fun u _ => Finset.filter_subset _ _)
    · intro u _ v _ huv
      exact Finset.disjoint_filter.2 fun p _ hu hv => huv (hu.symm.trans hv)
  have hcard : (richPrefixValues χ m S T).card * T ≤
      ∑ u ∈ richPrefixValues χ m S T, (E.filter fun p => f p = u).card := by
    rw [← smul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun u hu => ?_
    have hu' := hu
    simp only [richPrefixValues, Finset.mem_filter] at hu'
    exact hu'.2.le
  calc (richPrefixValues χ m S T).card * T
      ≤ ∑ u ∈ richPrefixValues χ m S T, (E.filter fun p => f p = u).card := hcard
    _ ≤ E.card := hsum
    _ = N * S.card := by rw [hE, Finset.card_product, Finset.card_univ, Fintype.card_fin]

/-- Counting the bad left vertices: if the family has the prefix expansion property for `m`
(the conclusion of `exists_prefixHashFamily`), `S` has fewer than `2 · 2^m` strings and the
threshold satisfies `2N ≤ ε T`, then the bad right vertices are at most `ε 2^m`, so the
strings of length `n` at least half of whose `m`-bit fingerprint prefixes are bad are fewer
than the bad right vertices, hence at most `N · |S| / T` of them.

SUV Section 12.7, p. 382 (the bound `2N · 2^k / n^c` for the bad vertices of `S_A`). -/
theorem card_majorityPrefixHits_richPrefixValues_mul_le {N : ℕ}
    (χ : Fin N → BitString → BitString) (n m : ℕ) (ε : ℝ) (hlen : ∀ i x, (χ i x).length = n)
    (hm : m ≤ n) (hN : 0 < N)
    (hexp : ∀ U : Finset BitString, U.Nonempty → (∀ u ∈ U, u.length = m) →
      (U.card : ℝ) ≤ ε * 2 ^ m → (majorityPrefixHits χ n m U).card < U.card)
    (S : Finset BitString) (T : ℕ) (hS : S.card < 2 * 2 ^ m) (hT : (2 * N : ℝ) ≤ ε * T) :
    (majorityPrefixHits χ n m (richPrefixValues χ m S T)).card * T ≤ N * S.card := by
  classical
  have hUT := card_richPrefixValues_mul_le χ m S T
  rcases (richPrefixValues χ m S T).eq_empty_or_nonempty with hUe | hUne
  · have hemp : majorityPrefixHits χ n m ∅ = ∅ := by
      apply Finset.filter_eq_empty_iff.2
      intro x _
      simp only [Finset.notMem_empty, Finset.filter_false, Finset.card_empty, mul_zero]
      omega
    rw [hUe, hemp]
    simp
  · have hlenU : ∀ u ∈ richPrefixValues χ m S T, u.length = m := by
      intro u hu
      simp only [richPrefixValues, Finset.mem_filter] at hu
      obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hu.1
      simp [prefixBits, List.length_take, hlen, min_eq_left hm]
    have hT0 : 0 < T := by
      rcases Nat.eq_zero_or_pos T with h | h
      · subst h
        have : (0 : ℝ) < N := by exact_mod_cast hN
        simp at hT
        linarith
      · exact h
    have hTpos : (0 : ℝ) < T := by exact_mod_cast hT0
    have hpow : (0 : ℝ) ≤ 2 ^ m := by positivity
    have e1 : ((richPrefixValues χ m S T).card : ℝ) * T ≤ N * S.card := by exact_mod_cast hUT
    have e2 : (N : ℝ) * S.card ≤ N * (2 * 2 ^ m) := by
      gcongr
      exact_mod_cast hS.le
    have e3 : (N : ℝ) * (2 * 2 ^ m) ≤ ε * T * 2 ^ m := by
      have := mul_le_mul_of_nonneg_right hT hpow
      linarith
    have key : ((richPrefixValues χ m S T).card : ℝ) * T ≤ (ε * 2 ^ m) * T := by linarith
    have hUcard : ((richPrefixValues χ m S T).card : ℝ) ≤ ε * 2 ^ m :=
      le_of_mul_le_mul_right key hTpos
    have hlt := hexp _ hUne hlenU hUcard
    calc (majorityPrefixHits χ n m (richPrefixValues χ m S T)).card * T
        ≤ (richPrefixValues χ m S T).card * T := Nat.mul_le_mul_right _ hlt.le
      _ ≤ N * S.card := hUT

/-- A string that is good for both decoders has one fingerprint index good for both: if
fewer than half of its `k`-bit fingerprint prefixes lie in `U` (the bad vertices for the
decoder knowing `A`) and fewer than half of its `l`-bit prefixes lie in `V` (those for `B`),
then some index `i` avoids both, and `[χ_i(x)]_k` is the message `X` of Theorem 235.

SUV Section 12.7, p. 383. -/
theorem exists_index_prefixBits_notMem_of_lt_half {N : ℕ} (χ : Fin N → BitString → BitString)
    (k l : ℕ) (U V : Finset BitString) (x : BitString)
    (hU : 2 * (Finset.univ.filter fun i : Fin N => prefixBits k (χ i x) ∈ U).card < N)
    (hV : 2 * (Finset.univ.filter fun i : Fin N => prefixBits l (χ i x) ∈ V).card < N) :
    ∃ i : Fin N, prefixBits k (χ i x) ∉ U ∧ prefixBits l (χ i x) ∉ V := by
  classical
  by_contra h
  push Not at h
  have hcov : (Finset.univ : Finset (Fin N)) ⊆
      (Finset.univ.filter fun i : Fin N => prefixBits k (χ i x) ∈ U) ∪
        (Finset.univ.filter fun i : Fin N => prefixBits l (χ i x) ∈ V) := by
    intro i _
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    by_cases hk : prefixBits k (χ i x) ∈ U
    · exact Or.inl ⟨Finset.mem_univ _, hk⟩
    · exact Or.inr ⟨Finset.mem_univ _, h i hk⟩
  have := (Finset.card_le_card hcov).trans (Finset.card_union_le _ _)
  rw [Finset.card_univ, Fintype.card_fin] at this
  omega

/-- A good fingerprint leaves few candidates: if the `m`-bit prefix `[χ_i(x)]_m` of a string
`x ∈ S` is not a bad vertex, then at most `T` strings of `S` share it under `χ_i`, so the
decoder that enumerates `S` (the strings simple given `A`) finds `x` among at most `T`
candidates, which costs `log T` further bits.

SUV Section 12.7, p. 383. -/
theorem card_filter_prefixBits_eq_le_of_notMem_richPrefixValues {N : ℕ}
    (χ : Fin N → BitString → BitString) (m : ℕ) (S : Finset BitString) (T : ℕ) (i : Fin N)
    (x : BitString) (hx : x ∈ S) (hgood : prefixBits m (χ i x) ∉ richPrefixValues χ m S T) :
    (S.filter fun y => prefixBits m (χ i y) = prefixBits m (χ i x)).card ≤ T := by
  classical
  have hmem : prefixBits m (χ i x) ∈
      (Finset.univ ×ˢ S).image fun p : Fin N × BitString => prefixBits m (χ p.1 p.2) :=
    Finset.mem_image.2 ⟨(i, x), Finset.mem_product.2 ⟨Finset.mem_univ _, hx⟩, rfl⟩
  have hle : ((Finset.univ ×ˢ S).filter fun p : Fin N × BitString =>
      prefixBits m (χ p.1 p.2) = prefixBits m (χ i x)).card ≤ T := by
    by_contra hlt
    push Not at hlt
    exact hgood (Finset.mem_filter.2 ⟨hmem, hlt⟩)
  refine le_trans ?_ hle
  have hinj : Set.InjOn (fun y : BitString => ((i, y) : Fin N × BitString))
      ↑(S.filter fun y => prefixBits m (χ i y) = prefixBits m (χ i x)) :=
    fun a _ b _ hab => (Prod.mk.inj hab).2
  refine Finset.card_le_card_of_injOn (fun y => (i, y)) (fun y hy => ?_) hinj
  simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
    true_and] at hy ⊢
  exact hy

section TwoConditionCodes

open Nat.Partrec (Code)

private def stageRun (c : Code) (s : ℕ) (p y : BitString) : Option BitString :=
  (Code.evaln s c (Encodable.encode (p, y))).bind fun r => Encodable.decode r

private theorem stageRun_primrec (c : Code) :
    Primrec (fun a : ℕ × BitString × BitString => stageRun c a.1 a.2.1 a.2.2) :=
  Primrec.option_bind ((evaln_primrec c).comp Primrec.fst (Primrec.encode.comp Primrec.snd))
    (Primrec.decode.comp Primrec.snd).to₂

private theorem stageRun_sound {c : Code} {D : Map} (hc : IsCodeFor c D) {s : ℕ}
    {p y x : BitString} (h : stageRun c s p y = some x) : x ∈ D (p, y) := by
  unfold stageRun at h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨r, hr, hx⟩ := h
  have h2 := Nat.Partrec.Code.evaln_sound hr
  rw [hc] at h2
  simp only [Encodable.encodek, Part.ofOption, Part.bind_some, Part.mem_map_iff]
    at h2
  obtain ⟨x', hx', rfl⟩ := h2
  rw [Encodable.encodek] at hx
  cases hx
  exact hx'

private theorem stageRun_complete {c : Code} {D : Map} (hc : IsCodeFor c D)
    {p y x : BitString} (h : x ∈ D (p, y)) : ∃ s, stageRun c s p y = some x := by
  have h2 : Encodable.encode x ∈ c.eval (Encodable.encode (p, y)) := by
    rw [hc]
    simp only [Encodable.encodek, Part.ofOption, Part.bind_some]
    exact Part.mem_map _ h
  obtain ⟨s, hs⟩ := Nat.Partrec.Code.evaln_complete.mp h2
  refine ⟨s, ?_⟩
  unfold stageRun
  rw [Option.mem_def.mp hs]
  simp [Encodable.encodek]

private theorem stageRun_mono {c : Code} {s s' : ℕ} {p y x : BitString}
    (h : stageRun c s p y = some x) (hs : s ≤ s') : stageRun c s' p y = some x := by
  unfold stageRun at h ⊢
  rw [Option.bind_eq_some_iff] at h ⊢
  obtain ⟨r, hr, hx⟩ := h
  exact ⟨r, Nat.Partrec.Code.evaln_mono hs hr, hx⟩

private def codeHist (c : Code) (t s : ℕ) : List (BitString × BitString) :=
  (List.range (s + 1)).flatMap fun s' =>
    (exactLengthPrograms t).filterMap fun p => (stageRun c s' p []).map fun x => (p, x)

private def codeAt (c : Code) (t : ℕ) (C : BitString) (s : ℕ) : Option BitString :=
  ((codeHist c t s).find? fun q => decide (q.2 = C)).map Prod.fst

private theorem codeHist_primrec (c : Code) :
    Primrec (fun a : ℕ × ℕ => codeHist c a.1 a.2) := by
  unfold codeHist
  refine Primrec.list_flatMap (Primrec.list_range.comp (Primrec.succ.comp Primrec.snd)) ?_
  refine Primrec.listFilterMap (primrec_exactLengthPrograms.comp (Primrec.fst.comp Primrec.fst))
    ?_
  refine Primrec.option_map ((stageRun_primrec c).comp (Primrec.pair (Primrec.snd.comp
    Primrec.fst) (Primrec.pair Primrec.snd (Primrec.const [])))) ?_
  exact (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂

private theorem codeAt_primrec (c : Code) :
    Primrec (fun a : ℕ × BitString × ℕ => codeAt c a.1 a.2.1 a.2.2) := by
  unfold codeAt
  refine Primrec.option_map (list_find?_primrec ((codeHist_primrec c).comp
    (Primrec.pair Primrec.fst (Primrec.snd.comp Primrec.snd))) ?_)
    (Primrec.fst.comp Primrec.snd).to₂
  exact (PrimrecRel.decide Primrec.eq).comp (Primrec.snd.comp Primrec.snd)
    (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))

private theorem flatMap_range_prefix {α : Type*} (f : ℕ → List α) {s s' : ℕ} (h : s ≤ s') :
    (List.range (s + 1)).flatMap f <+: (List.range (s' + 1)).flatMap f := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  have e : List.range (s + d + 1) = List.range (s + 1) ++ (List.range d).map (s + 1 + ·) := by
    rw [show s + d + 1 = (s + 1) + d by omega]
    exact List.range_add
  rw [e, List.flatMap_append]
  exact List.prefix_append _ _

private theorem codeHist_prefix (c : Code) (t : ℕ) {s s' : ℕ} (h : s ≤ s') :
    codeHist c t s <+: codeHist c t s' :=
  flatMap_range_prefix _ h

private theorem mem_codeHist {c : Code} {t s : ℕ} {p x : BitString} :
    (p, x) ∈ codeHist c t s ↔
      p ∈ exactLengthPrograms t ∧ ∃ s' ≤ s, stageRun c s' p [] = some x := by
  unfold codeHist
  simp only [List.mem_flatMap, List.mem_range, List.mem_filterMap, Option.map_eq_some_iff,
    Prod.mk.injEq]
  constructor
  · rintro ⟨s', hs', p', hp', x', hx', rfl, rfl⟩
    exact ⟨hp', s', by omega, hx'⟩
  · rintro ⟨hp, s', hs', hx⟩
    exact ⟨s', by omega, p, hp, x, hx, rfl, rfl⟩

private theorem codeAt_mono {c : Code} {t : ℕ} {C : BitString} {s s' : ℕ} {p : BitString}
    (h : codeAt c t C s = some p) (hs : s ≤ s') : codeAt c t C s' = some p := by
  obtain ⟨l, hl⟩ := codeHist_prefix c t hs
  unfold codeAt at h ⊢
  rw [← hl, List.find?_append]
  rw [Option.map_eq_some_iff] at h ⊢
  obtain ⟨q, hq, rfl⟩ := h
  exact ⟨q, by rw [hq]; rfl, rfl⟩

private theorem codeAt_spec {c : Code} {D : Map} (hc : IsCodeFor c D) {t : ℕ} {C : BitString}
    {s : ℕ} {p : BitString} (h : codeAt c t C s = some p) : p.length = t ∧ C ∈ D (p, []) := by
  unfold codeAt at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨⟨p', x⟩, hq, rfl⟩ := h
  have hmem := List.mem_of_find?_eq_some hq
  have hx := List.find?_some hq
  simp only [decide_eq_true_eq] at hx
  subst hx
  obtain ⟨hp, s', -, hs'⟩ := mem_codeHist.1 hmem
  exact ⟨exactLengthPrograms_length_eq t _ hp, stageRun_sound hc hs'⟩

private theorem codeAt_exists {c : Code} {D : Map} (hc : IsCodeFor c D) {C p : BitString}
    (h : C ∈ D (p, [])) : ∃ s, (codeAt c p.length C s).isSome := by
  obtain ⟨s, hs⟩ := stageRun_complete hc h
  refine ⟨s, ?_⟩
  unfold codeAt
  rw [Option.isSome_map, List.find?_isSome]
  exact ⟨(p, C), mem_codeHist.2 ⟨mem_exactLengthPrograms_self p, s, le_rfl, hs⟩, by simp⟩

private theorem codeAt_unique {c : Code} {t : ℕ} {C : BitString} {s s' : ℕ} {p p' : BitString}
    (h : codeAt c t C s = some p) (h' : codeAt c t C s' = some p') : p = p' := by
  have h1 := codeAt_mono h (le_max_left s s')
  have h2 := codeAt_mono h' (le_max_right s s')
  rw [h1] at h2
  exact Option.some_injective _ h2

private def codeOf (c : Code) (t : ℕ) (C : BitString) : Part BitString :=
  (Nat.rfind fun s => Part.some (codeAt c t C s).isSome).bind fun s =>
    Part.ofOption (codeAt c t C s)

private theorem codeOf_partrec (c : Code) :
    Partrec (fun a : ℕ × BitString => codeOf c a.1 a.2) := by
  have h1 : Computable (fun a : (ℕ × BitString) × ℕ => codeAt c a.1.1 a.1.2 a.2) :=
    ((codeAt_primrec c).comp (Primrec.pair (Primrec.fst.comp Primrec.fst)
      (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd))).to_comp
  have h2 : Computable₂ (fun (a : ℕ × BitString) (s : ℕ) => (codeAt c a.1 a.2 s).isSome) :=
    Primrec.option_isSome.to_comp.comp h1
  exact Partrec.bind (Partrec.rfind h2.partrec₂) (Computable.ofOption h1).to₂

private theorem mem_codeOf {c : Code} {t : ℕ} {C : BitString} {s : ℕ} {p : BitString}
    (h : codeAt c t C s = some p) : p ∈ codeOf c t C := by
  have hex : ∃ s, (codeAt c t C s).isSome := ⟨s, by rw [h]; rfl⟩
  unfold codeOf
  rw [Part.mem_bind_iff]
  refine ⟨Nat.find hex, ?_, ?_⟩
  · change Nat.find hex ∈
      Nat.rfind (show ℕ →. Bool from fun s => Part.some (codeAt c t C s).isSome)
    refine Nat.mem_rfind.mpr ⟨?_, ?_⟩
    · exact Part.mem_some_iff.mpr (Nat.find_spec hex).symm
    · intro m hm
      exact Part.mem_some_iff.mpr (Bool.eq_false_of_ne_true (Nat.find_min hex hm)).symm
  · obtain ⟨p', hp'⟩ := Option.isSome_iff_exists.1 (Nat.find_spec hex)
    rw [hp', codeAt_unique hp' h]
    exact Part.mem_some _

private def codeStage (c : Code) (t k : ℕ) (Y : BitString) (s : ℕ) : List BitString :=
  (boundedPrograms k).filterMap fun q => (stageRun c s q Y).bind fun C' => codeAt c t C' s

private theorem codeStage_primrec (c : Code) :
    Primrec (fun a : (ℕ × ℕ) × BitString × ℕ => codeStage c a.1.1 a.1.2 a.2.1 a.2.2) := by
  unfold codeStage
  refine Primrec.listFilterMap (primrec_boundedPrograms.comp (Primrec.snd.comp Primrec.fst)) ?_
  refine Primrec.option_bind ((stageRun_primrec c).comp (Primrec.pair
    (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) (Primrec.pair Primrec.snd
    (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))))) ?_
  exact ((codeAt_primrec c).comp (Primrec.pair
    (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
    (Primrec.pair Primrec.snd
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))))).to₂

private theorem codeStage_mono {c : Code} {t k : ℕ} {Y x : BitString} {s s' : ℕ}
    (h : x ∈ codeStage c t k Y s) (hs : s ≤ s') : x ∈ codeStage c t k Y s' := by
  unfold codeStage at h ⊢
  rw [List.mem_filterMap] at h ⊢
  obtain ⟨q, hq, hx⟩ := h
  rw [Option.bind_eq_some_iff] at hx
  obtain ⟨C', hC', hx⟩ := hx
  exact ⟨q, hq, by rw [stageRun_mono hC' hs]; exact codeAt_mono hx hs⟩

private theorem codeStage_spec {c : Code} {D : Map} (hc : IsCodeFor c D) {t k : ℕ}
    {Y x : BitString} {s : ℕ} (h : x ∈ codeStage c t k Y s) :
    ∃ C', condK D C' Y ≤ (k : ℕ∞) ∧ codeAt c t C' s = some x := by
  unfold codeStage at h
  rw [List.mem_filterMap] at h
  obtain ⟨q, hq, hx⟩ := h
  rw [Option.bind_eq_some_iff] at hx
  obtain ⟨C', hC', hx⟩ := hx
  refine ⟨C', (condK_le_iff D _ _ _).2 ⟨q, ?_, stageRun_sound hc hC'⟩, hx⟩
  exact (mem_boundedPrograms_iff q k).1 hq

private theorem mem_codeStage_of {c : Code} {D : Map} (hc : IsCodeFor c D) {t k : ℕ}
    {Y C P : BitString} {s0 : ℕ} (hCY : condK D C Y ≤ (k : ℕ∞)) (hP : codeAt c t C s0 = some P) :
    ∃ s, P ∈ codeStage c t k Y s := by
  obtain ⟨q, hq, hqC⟩ := (condK_le_iff D _ _ _).1 hCY
  obtain ⟨s1, hs1⟩ := stageRun_complete hc hqC
  refine ⟨max s0 s1, ?_⟩
  unfold codeStage
  rw [List.mem_filterMap]
  refine ⟨q, (mem_boundedPrograms_iff q k).2 hq, ?_⟩
  rw [stageRun_mono hs1 (le_max_right s0 s1)]
  exact codeAt_mono hP (le_max_left s0 s1)

private theorem exists_stage_stable {f : ℕ → List BitString}
    (hmono : ∀ s s' x, s ≤ s' → x ∈ f s → x ∈ f s') {B : ℕ} (hB : ∀ s, (f s).length ≤ B) :
    ∃ s0, ∀ s, ∀ x ∈ f s, x ∈ f s0 := by
  classical
  let g : ℕ → ℕ := fun s => (f s).toFinset.card
  have hbdd : BddAbove (Set.range g) :=
    ⟨B, by rintro _ ⟨s, rfl⟩; exact (List.toFinset_card_le _).trans (hB s)⟩
  obtain ⟨s0, hs0⟩ := Nat.sSup_mem (Set.range_nonempty g) hbdd
  refine ⟨s0, fun s x hx => ?_⟩
  have hsub : (f s0).toFinset ⊆ (f (max s s0)).toFinset := fun y hy =>
    List.mem_toFinset.2 (hmono _ _ _ (le_max_right s s0) (List.mem_toFinset.1 hy))
  have hle : (f (max s s0)).toFinset.card ≤ (f s0).toFinset.card := by
    have := le_csSup hbdd ⟨max s s0, rfl⟩
    change g (max s s0) ≤ g s0
    rw [hs0]
    exact this
  have heq := Finset.eq_of_subset_of_card_le hsub hle
  have : x ∈ (f (max s s0)).toFinset :=
    List.mem_toFinset.2 (hmono _ _ _ (le_max_left s s0) hx)
  rw [← heq] at this
  exact List.mem_toFinset.1 this

private def tabFam (t : ℕ) (L : List (List BitString)) (i : ℕ) (x : BitString) : BitString :=
  (((L.getD i []).getD ((exactLengthPrograms t).findIdx fun y => decide (y = x)) []) ++
    List.replicate t false).take t

private theorem length_tabFam (t : ℕ) (L : List (List BitString)) (i : ℕ) (x : BitString) :
    (tabFam t L i x).length = t := by
  simp [tabFam]

private abbrev TabArg := (ℕ × List (List BitString)) × ℕ × BitString

private theorem tabFam_primrec :
    Primrec (fun a : TabArg => tabFam a.1.1 a.1.2 a.2.1 a.2.2) := by
  have h1 : Primrec (fun a : TabArg => a.1.2.getD a.2.1 []) :=
    (Primrec.list_getD []).comp (Primrec.snd.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)
  have h2 : Primrec (fun a : TabArg =>
      (exactLengthPrograms a.1.1).findIdx fun y => decide (y = a.2.2)) :=
    Primrec.list_findIdx (primrec_exactLengthPrograms.comp (Primrec.fst.comp Primrec.fst))
      ((PrimrecRel.decide Primrec.eq).comp Primrec.snd (Primrec.snd.comp (Primrec.snd.comp
        Primrec.fst)))
  have h3 : Primrec (fun a : TabArg =>
      (a.1.2.getD a.2.1 []).getD
        ((exactLengthPrograms a.1.1).findIdx fun y => decide (y = a.2.2)) []) :=
    (Primrec.list_getD []).comp h1 h2
  have h4 : Primrec (fun a : TabArg => List.replicate a.1.1 false) :=
    Primrec.list_replicate.comp (Primrec.fst.comp Primrec.fst) (Primrec.const false)
  exact Primrec.list_take.comp (Primrec.fst.comp Primrec.fst) (Primrec.list_append.comp h3 h4)

private def mhCount (t N m : ℕ) (L : List (List BitString)) (U : List BitString) : ℕ :=
  (exactLengthPrograms t).countP fun x =>
    decide (N ≤ 2 * (List.range N).countP fun i => decide ((tabFam t L i x).take m ∈ U))

private def hashBad (t N : ℕ) (L : List (List BitString)) : Bool :=
  (List.range (t + 1)).any fun m => decide (0 < m) && (exactLengthPrograms m).sublists.any
    fun U => decide (0 < U.length) && (decide (64 * U.length ≤ (exactLengthPrograms m).length)
      && decide (U.length ≤ mhCount t N m L U))

private abbrev MhArg := ((ℕ × ℕ) × ℕ) × List (List BitString) × List BitString

private theorem mhCount_primrec :
    Primrec (fun a : MhArg => mhCount a.1.1.1 a.1.1.2 a.1.2 a.2.1 a.2.2) := by
  have hT : Primrec₂ (fun (b : MhArg × BitString) (i : ℕ) =>
      decide ((tabFam b.1.1.1.1 b.1.2.1 i b.2).take b.1.1.2 ∈ b.1.2.2)) := by
    have e1 : Primrec (fun q : (MhArg × BitString) × ℕ =>
        tabFam q.1.1.1.1.1 q.1.1.2.1 q.2 q.1.2) := by
      have hp : Primrec (fun q : (MhArg × BitString) × ℕ =>
          (((q.1.1.1.1.1, q.1.1.2.1), q.2, q.1.2) : TabArg)) := by
        refine Primrec.pair (Primrec.pair ?_ ?_) (Primrec.pair Primrec.snd ?_)
        · exact Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp
            Primrec.fst)))
        · exact Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
        · exact Primrec.snd.comp Primrec.fst
      exact (tabFam_primrec.comp hp).of_eq fun q => rfl
    have e2 : Primrec (fun q : (MhArg × BitString) × ℕ =>
        (tabFam q.1.1.1.1.1 q.1.1.2.1 q.2 q.1.2).take q.1.1.1.2) :=
      Primrec.list_take.comp
        (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))) e1
    exact (bitString_mem_primrec.comp e2
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))).of_eq fun q => rfl
  have hC : Primrec (fun b : MhArg × BitString => (List.range b.1.1.1.2).countP fun i =>
      decide ((tabFam b.1.1.1.1 b.1.2.1 i b.2).take b.1.1.2 ∈ b.1.2.2)) :=
    list_countP_primrec (Primrec.list_range.comp
      (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))) hT
  have hP : Primrec₂ (fun (a : MhArg) (x : BitString) => decide (a.1.1.2 ≤ 2 *
      (List.range a.1.1.2).countP fun i =>
        decide ((tabFam a.1.1.1 a.2.1 i x).take a.1.2 ∈ a.2.2))) :=
    (PrimrecRel.decide Primrec.nat_le).comp
      (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.nat_mul.comp (Primrec.const 2) hC)
  exact list_countP_primrec (primrec_exactLengthPrograms.comp
    (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))) hP

private theorem sublists_primrec {α : Type*} [Primcodable α] :
    Primrec (List.sublists : List α → List (List α)) := by
  have hg : Primrec₂ (fun (_ : List α) (q : α × List (List α)) =>
      q.2.flatMap fun x => [x, q.1 :: x]) := by
    have e : Primrec₂ (fun (b : List α × α × List (List α)) (x : List α) => [x, b.2.1 :: x]) :=
      Primrec.list_cons.comp Primrec.snd (Primrec.list_cons.comp
        (Primrec.list_cons.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd)
        (Primrec.const []))
    exact Primrec.list_flatMap (Primrec.snd.comp Primrec.snd) e
  exact (Primrec.list_foldr Primrec.id (Primrec.const [[]]) hg).of_eq fun l => rfl

private theorem hashBad_primrec :
    Primrec (fun a : ℕ × List (List BitString) => hashBad a.1 (2 * a.1 + 2) a.2) := by
  have hmh : Primrec₂ (fun (b : (ℕ × List (List BitString)) × ℕ) (U : List BitString) =>
      mhCount b.1.1 (2 * b.1.1 + 2) b.2 b.1.2 U) := by
    have hp : Primrec (fun q : ((ℕ × List (List BitString)) × ℕ) × List BitString =>
        ((((q.1.1.1, 2 * q.1.1.1 + 2), q.1.2), q.1.1.2, q.2) : MhArg)) := by
      have ht : Primrec (fun q : ((ℕ × List (List BitString)) × ℕ) × List BitString =>
          q.1.1.1) := Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
      refine Primrec.pair (Primrec.pair (Primrec.pair ht ?_) (Primrec.snd.comp Primrec.fst))
        (Primrec.pair (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd)
      exact Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) ht) (Primrec.const 2)
    exact (mhCount_primrec.comp hp).of_eq fun q => rfl
  have hlenU : Primrec₂ (fun (_ : (ℕ × List (List BitString)) × ℕ) (U : List BitString) =>
      U.length) := Primrec.list_length.comp Primrec.snd
  have hin : Primrec₂ (fun (b : (ℕ × List (List BitString)) × ℕ) (U : List BitString) =>
      decide (0 < U.length) && (decide (64 * U.length ≤ (exactLengthPrograms b.2).length)
        && decide (U.length ≤ mhCount b.1.1 (2 * b.1.1 + 2) b.2 b.1.2 U))) := by
    refine Primrec.and.comp ((PrimrecRel.decide Primrec.nat_lt).comp (Primrec.const 0) hlenU)
      (Primrec.and.comp ?_ ((PrimrecRel.decide Primrec.nat_le).comp hlenU hmh))
    exact (PrimrecRel.decide Primrec.nat_le).comp (Primrec.nat_mul.comp (Primrec.const 64) hlenU)
      (Primrec.list_length.comp (primrec_exactLengthPrograms.comp
        (Primrec.snd.comp Primrec.fst)))
  have hany : Primrec₂ (fun (a : ℕ × List (List BitString)) (m : ℕ) =>
      decide (0 < m) && (exactLengthPrograms m).sublists.any fun U =>
        decide (0 < U.length) && (decide (64 * U.length ≤ (exactLengthPrograms m).length)
          && decide (U.length ≤ mhCount a.1 (2 * a.1 + 2) m a.2 U))) := by
    refine Primrec.and.comp ((PrimrecRel.decide Primrec.nat_lt).comp (Primrec.const 0)
      Primrec.snd) ?_
    exact (list_any_primrec (sublists_primrec.comp (primrec_exactLengthPrograms.comp
      Primrec.snd)) hin).of_eq fun q => rfl
  exact (list_any_primrec (Primrec.list_range.comp (Primrec.succ.comp Primrec.fst)) hany).of_eq
    fun a => by simp [hashBad]

private theorem card_filter_fin_eq_countP (N : ℕ) (p : ℕ → Prop) [DecidablePred p] :
    (Finset.univ.filter fun i : Fin N => p i.val).card =
      (List.range N).countP (fun i => decide (p i)) := by
  have e : (Finset.univ.filter fun i : Fin N => p i.val).map Fin.valEmbedding =
      (Finset.range N).filter p := by
    ext i
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
      Finset.mem_range]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨j.isLt, hj⟩
    · rintro ⟨hi, hp⟩
      exact ⟨⟨i, hi⟩, hp, rfl⟩
  rw [← Finset.card_map, e, List.countP_eq_length_filter]
  rfl

private theorem stringsOfLength_eq_toFinset (t : ℕ) :
    stringsOfLength t = (exactLengthPrograms t).toFinset := by
  ext x
  rw [mem_stringsOfLength, List.mem_toFinset]
  constructor
  · rintro rfl
    exact mem_exactLengthPrograms_self x
  · exact exactLengthPrograms_length_eq t x

private theorem mem_majorityPrefixHits_iff {N : ℕ} (χL : ℕ → BitString → BitString)
    (t m : ℕ) (U : Finset BitString) (x : BitString) :
    x ∈ majorityPrefixHits (fun i : Fin N => χL i) t m U ↔ x.length = t ∧
      N ≤ 2 * (List.range N).countP (fun i => decide (prefixBits m (χL i x) ∈ U)) := by
  unfold majorityPrefixHits
  rw [Finset.mem_filter, mem_stringsOfLength,
    card_filter_fin_eq_countP N (fun i => prefixBits m (χL i x) ∈ U)]

private theorem card_majorityPrefixHits_eq {N : ℕ} (χL : ℕ → BitString → BitString)
    (t m : ℕ) (U : Finset BitString) :
    (majorityPrefixHits (fun i : Fin N => χL i) t m U).card = (exactLengthPrograms t).countP
      (fun x => decide (N ≤ 2 * (List.range N).countP
        (fun i => decide (prefixBits m (χL i x) ∈ U)))) := by
  have e : majorityPrefixHits (fun i : Fin N => χL i) t m U = ((exactLengthPrograms t).filter
      (fun x => decide (N ≤ 2 * (List.range N).countP
        (fun i => decide (prefixBits m (χL i x) ∈ U))))).toFinset := by
    ext x
    rw [mem_majorityPrefixHits_iff, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro ⟨rfl, h⟩
      exact ⟨mem_exactLengthPrograms_self x, h⟩
    · rintro ⟨hx, h⟩
      exact ⟨exactLengthPrograms_length_eq t x hx, h⟩
  rw [e, List.toFinset_card_of_nodup ((exactLengthPrograms_nodup t).filter _),
    List.countP_eq_length_filter]

private theorem mhCount_eq_card {N t m : ℕ} (L : List (List BitString)) (Ul : List BitString)
    (U : Finset BitString) (hU : ∀ u, u ∈ Ul ↔ u ∈ U) :
    mhCount t N m L Ul = (majorityPrefixHits (fun i : Fin N => tabFam t L i) t m U).card := by
  rw [card_majorityPrefixHits_eq, mhCount]
  refine List.countP_congr fun x _ => ?_
  have : (List.range N).countP (fun i => decide ((tabFam t L i x).take m ∈ Ul)) =
      (List.range N).countP (fun i => decide (prefixBits m (tabFam t L i x) ∈ U)) :=
    List.countP_congr fun i _ => by
      constructor
      · intro hi
        exact decide_eq_true (hU _ |>.mp (of_decide_eq_true hi))
      · intro hi
        exact decide_eq_true (hU _ |>.mpr (of_decide_eq_true hi))
  simp [this]

private theorem hash_spec_of_hashBad_false {t N : ℕ} {L : List (List BitString)}
    (hb : hashBad t N L = false) (m : ℕ) (hm1 : 1 ≤ m) (hmt : m ≤ t) (U : Finset BitString)
    (hne : U.Nonempty) (hlen : ∀ u ∈ U, u.length = m) (hcard : (U.card : ℝ) ≤ 1 / 64 * 2 ^ m) :
    (majorityPrefixHits (fun i : Fin N => tabFam t L i) t m U).card < U.card := by
  classical
  set Ul := (exactLengthPrograms m).filter (fun u => decide (u ∈ U)) with hUl
  have hmem : ∀ u, u ∈ Ul ↔ u ∈ U := by
    intro u
    rw [hUl, List.mem_filter, decide_eq_true_eq]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨by rw [← hlen u h]; exact mem_exactLengthPrograms_self u, h⟩
  have hcardUl : Ul.length = U.card := by
    rw [← List.toFinset_card_of_nodup ((exactLengthPrograms_nodup m).filter _)]
    congr 1
    ext u
    rw [List.mem_toFinset, hmem]
  have hsub : Ul ∈ (exactLengthPrograms m).sublists :=
    List.mem_sublists.2 List.filter_sublist
  rw [hashBad, List.any_eq_false] at hb
  have hm := hb m (List.mem_range.2 (by omega))
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, not_and, not_exists] at hm
  have h1 := hm (by omega) Ul hsub
  rw [length_exactLengthPrograms, hcardUl, ← mhCount_eq_card L Ul U hmem] at *
  have hpos : 0 < U.card := Finset.card_pos.2 hne
  have h64 : 64 * U.card ≤ 2 ^ m := by
    have : (64 * U.card : ℝ) ≤ 2 ^ m := by linarith
    exact_mod_cast this
  by_contra hlt
  exact h1 hpos h64 (not_lt.1 hlt)

private def tableOf {N : ℕ} (t : ℕ) (χ : Fin N → BitString → BitString) :
    List (List BitString) :=
  (List.finRange N).map fun i => (exactLengthPrograms t).map (χ i)

private theorem tabFam_tableOf {N t : ℕ} (χ : Fin N → BitString → BitString)
    (hlen : ∀ i x, (χ i x).length = t) (i : Fin N) {x : BitString} (hx : x.length = t) :
    tabFam t (tableOf t χ) i x = χ i x := by
  have hxmem : x ∈ exactLengthPrograms t := hx ▸ mem_exactLengthPrograms_self x
  have hidx : ((exactLengthPrograms t).findIdx fun y => decide (y = x)) <
      (exactLengthPrograms t).length :=
    List.findIdx_lt_length_of_exists ⟨x, hxmem, by simp⟩
  have hget : (exactLengthPrograms t)[(exactLengthPrograms t).findIdx fun y => decide (y = x)]
      = x := by
    simpa using List.findIdx_getElem (w := hidx)
  unfold tabFam tableOf
  have h1 : ((List.finRange N).map fun i => (exactLengthPrograms t).map (χ i)).getD i [] =
      (exactLengthPrograms t).map (χ i) := by
    simp [List.getD_eq_getElem?_getD]
  rw [h1, List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hidx), List.getElem_map, hget,
    List.take_left' (hlen i x)]

private theorem hashBad_tableOf {N t : ℕ} (χ : Fin N → BitString → BitString)
    (hlen : ∀ i x, (χ i x).length = t)
    (hexp : ∀ m : ℕ, 1 ≤ m → m ≤ t → ∀ U : Finset BitString, U.Nonempty →
      (∀ u ∈ U, u.length = m) → (U.card : ℝ) ≤ 1 / 64 * 2 ^ m →
      (majorityPrefixHits χ t m U).card < U.card) :
    hashBad t N (tableOf t χ) = false := by
  classical
  have hMH : ∀ m U, majorityPrefixHits (fun i : Fin N => tabFam t (tableOf t χ) i) t m U =
      majorityPrefixHits χ t m U := by
    intro m U
    unfold majorityPrefixHits
    refine Finset.filter_congr fun x hx => ?_
    rw [mem_stringsOfLength] at hx
    simp only [tabFam_tableOf χ hlen _ hx]
  rw [hashBad, List.any_eq_false]
  intro m hm
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, not_and, not_exists]
  intro hm0 Ul hUl hpos h64 hle
  have hnd : Ul.Nodup := (List.mem_sublists.1 hUl).nodup (exactLengthPrograms_nodup m)
  have hcard : Ul.toFinset.card = Ul.length := List.toFinset_card_of_nodup hnd
  have hlt := hexp m hm0 (by have := List.mem_range.1 hm; omega) Ul.toFinset
    (by rw [← Finset.card_pos, hcard]; exact hpos)
    (fun u hu => exactLengthPrograms_length_eq m u
      ((List.mem_sublists.1 hUl).subset (List.mem_toFinset.1 hu)))
    (by
      rw [hcard]
      rw [length_exactLengthPrograms] at h64
      have : (64 * Ul.length : ℝ) ≤ 2 ^ m := by exact_mod_cast h64
      linarith)
  rw [← hMH, ← mhCount_eq_card (tableOf t χ) Ul Ul.toFinset (fun u => List.mem_toFinset.symm),
    hcard] at hlt
  omega

private theorem hashFamily_bound (t : ℕ) :
    (t : ℝ) * 2 ^ ((2 * t + 2) + 2 * t + 1) * (1 / 64 : ℝ) ^ (((2 * t + 2 : ℕ) : ℝ) / 2) < 1 := by
  have e : (((2 * t + 2 : ℕ) : ℝ) / 2) = ((t + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [e, Real.rpow_natCast]
  have h1 : (2 : ℝ) ^ ((2 * t + 2) + 2 * t + 1) * (1 / 64 : ℝ) ^ (t + 1) * 2 ^ (2 * t + 3) = 1 := by
    rw [show (1 / 64 : ℝ) = (1 / 2) ^ 6 by norm_num, ← pow_mul, mul_assoc, mul_comm _ (2 ^ _),
      ← mul_assoc, ← pow_add, one_div, inv_pow, ← div_eq_mul_inv]
    rw [div_eq_one_iff_eq (by positivity)]
    ring_nf
  have h2 : (t : ℝ) < 2 ^ (2 * t + 3) := by
    have : t < 2 ^ (2 * t + 3) := Nat.lt_two_pow_self.trans_le
      (Nat.pow_le_pow_right (by norm_num) (by omega))
    exact_mod_cast this
  have h3 : (0 : ℝ) < 2 ^ ((2 * t + 2) + 2 * t + 1) * (1 / 64 : ℝ) ^ (t + 1) := by positivity
  nlinarith

private def goodCode (t j : ℕ) : Bool :=
  ((Encodable.decode (α := List (List BitString)) j).map fun L => !hashBad t (2 * t + 2) L).getD
    false

private theorem exists_goodCode (t : ℕ) : ∃ j, goodCode t j = true := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · refine ⟨Encodable.encode ([] : List (List BitString)), ?_⟩
    simp [goodCode, hashBad]
  · obtain ⟨χ, hlen, hexp⟩ := exists_prefixHashFamily t (2 * t + 2) (1 / 64) ht (by omega)
      (by norm_num) (hashFamily_bound t)
    refine ⟨Encodable.encode (tableOf t χ), ?_⟩
    simp [goodCode, Encodable.encodek, hashBad_tableOf χ hlen hexp]

private def hashTab (t : ℕ) : List (List BitString) :=
  (Encodable.decode (α := List (List BitString)) (Nat.find (exists_goodCode t))).getD []

private theorem hashTab_computable : Computable hashTab := by
  have hg : Primrec (fun p : ℕ × ℕ => goodCode p.1 p.2) := by
    unfold goodCode
    refine Primrec.option_getD.comp (Primrec.option_map (Primrec.decode.comp Primrec.snd) ?_)
      (Primrec.const false)
    exact Primrec.not.comp (hashBad_primrec.comp (Primrec.pair
      (Primrec.fst.comp Primrec.fst) Primrec.snd))
  have hf := Computable.natFind (P := fun t j => goodCode t j = true)
    ((hg.to_comp).of_eq fun p => by simp) exists_goodCode
  exact (Primrec.option_getD.to_comp.comp (Primrec.decode.to_comp.comp hf)
    (Computable.const [])).of_eq fun t => rfl

private theorem hashBad_hashTab (t : ℕ) : hashBad t (2 * t + 2) (hashTab t) = false := by
  have h := Nat.find_spec (exists_goodCode t)
  have hspec {j : ℕ} (hj : goodCode t j = true) :
      ∃ L, Encodable.decode j = some L ∧ hashBad t (2 * t + 2) L = false := by
    unfold goodCode at hj
    cases hd : Encodable.decode (α := List (List BitString)) j with
    | none => simp only [hd, Option.map_none, Option.getD_none, Bool.false_eq_true] at hj
    | some L =>
        refine ⟨L, rfl, ?_⟩
        simp only [hd, Option.map_some, Option.getD_some] at hj
        exact Bool.eq_false_of_not_eq_true' hj
  obtain ⟨L, hd, hb⟩ := hspec h
  unfold hashTab
  rw [hd]
  exact hb

private theorem condK_le_of_enumeration (D : Map) (hD : isOptimalConditional D)
    (enum : BitString → ℕ → List BitString)
    (henum : Computable fun p : BitString × ℕ => enum p.1 p.2)
    (hmono : ∀ y s, enum y s <+: enum y (s + 1)) :
    ∃ cst : ℕ, ∀ (w y x out : BitString) (F : Finset BitString),
      (∃ s, x ∈ enum (pairCode w y) s) → (∀ s, ∀ v ∈ enum (pairCode w y) s, v ∈ F) →
      out ∈ D (x, []) →
      condK D out y ≤ ((2 * w.length + (Nat.bits F.card).length + cst : ℕ) : ℕ∞) := by
  let Dg : Map := fun pr =>
    (StagedEnumeration.condFFixedLength enum (pairCode (decodeFirst pr.1) pr.2)
      (decodeSecond pr.1)).bind fun x => D (x, [])
  have hDg : isDecompressor Dg := by
    have h1 : Partrec (fun pr : BitString × BitString =>
        StagedEnumeration.condFFixedLength enum (pairCode (decodeFirst pr.1) pr.2)
          (decodeSecond pr.1)) := by
      have hp : Computable (fun pr : BitString × BitString =>
          (decodeSecond pr.1, pairCode (decodeFirst pr.1) pr.2)) :=
        (Primrec.pair (decodeSecond_primrec.comp Primrec.fst)
          (pairCode_primrec.comp (decodeFirst_primrec.comp Primrec.fst) Primrec.snd)).to_comp
      exact ((StagedEnumeration.condFFixedLength_partrec enum henum).comp hp).of_eq
        fun _ => rfl
    exact h1.bind (hD.1.comp (Computable.pair Computable.snd (Computable.const []))).to₂
  obtain ⟨cst, hcst⟩ := hD.2 Dg hDg
  refine ⟨cst + 1, fun w y x out F ⟨s, hxs⟩ hF hout => ?_⟩
  set l := StagedEnumeration.condDistinctAt enum (pairCode w y) s with hl
  have hxl : x ∈ l := mem_eraseDups_iff.2 hxs
  set j := l.findIdx fun v => decide (v = x) with hj
  have hjlt : j < l.length := List.findIdx_lt_length_of_exists ⟨x, hxl, by simp⟩
  have hget : l.getD j [] = x := by
    rw [List.getD_eq_getElem _ _ hjlt]
    simpa using List.findIdx_getElem (w := hjlt)
  have hlF : l.length ≤ F.card := by
    have hnd : l.Nodup := nodup_eraseDups_list _
    rw [← List.toFinset_card_of_nodup hnd]
    exact Finset.card_le_card fun v hv =>
      hF s v (mem_eraseDups_iff.1 (List.mem_toFinset.1 hv))
  have hev := StagedEnumeration.condFFixedLength_eval enum hmono (pairCode w y) (Nat.bits j) s
    (by rw [bitsToNat_bits]; exact hjlt)
  rw [bitsToNat_bits, ← hl, hget] at hev
  have hmem : out ∈ Dg (pairCode w (Nat.bits j), y) := by
    simp only [Dg, decodeFirst_pairCode, decodeSecond_pairCode]
    exact Part.mem_bind_iff.2 ⟨x, hev, hout⟩
  have h1 : condK Dg out y ≤ ((pairCode w (Nat.bits j)).length : ℕ∞) :=
    (condK_le_iff Dg _ _ _).2 ⟨_, le_rfl, hmem⟩
  have hbits : (Nat.bits j).length ≤ (Nat.bits F.card).length := length_bits_mono (by omega)
  calc condK D out y ≤ condK Dg out y + (cst : ℕ∞) := hcst _ _
    _ ≤ ((pairCode w (Nat.bits j)).length : ℕ∞) + (cst : ℕ∞) := by gcongr
    _ ≤ ((2 * w.length + (Nat.bits F.card).length + (cst + 1) : ℕ) : ℕ∞) := by
      rw [length_pairCode]
      norm_cast
      omega

private def richCount (t m : ℕ) (L : List (List BitString)) (S : List BitString)
    (u : BitString) : ℕ :=
  (S.flatMap fun x => (List.range (2 * t + 2)).map fun i => (tabFam t L i x).take m).countP
    fun v => decide (v = u)

private def richList (t m τ : ℕ) (L : List (List BitString)) (S : List BitString) :
    List BitString :=
  (exactLengthPrograms m).filter fun u =>
    decide ((exactLengthPrograms τ).length < richCount t m L S u)

private def badStage (t m τ : ℕ) (L : List (List BitString)) (S : List BitString) :
    List BitString :=
  (exactLengthPrograms t).filter fun x => decide (2 * t + 2 ≤
    2 * (List.range (2 * t + 2)).countP fun i =>
      decide ((tabFam t L i x).take m ∈ richList t m τ L S))

private theorem richCount_eq_card {t m : ℕ} {L : List (List BitString)} {S : List BitString}
    (hS : S.Nodup) (u : BitString) :
    richCount t m L S u = ((Finset.univ ×ˢ S.toFinset).filter
      fun p : Fin (2 * t + 2) × BitString => prefixBits m (tabFam t L p.1 p.2) = u).card := by
  rw [Finset.card_filter, Finset.sum_product_right, List.sum_toFinset _ hS, richCount,
    List.countP_flatMap]
  congr 1
  refine List.map_congr_left fun x _ => ?_
  rw [Function.comp_apply, List.countP_map, ← Finset.card_filter,
    card_filter_fin_eq_countP (2 * t + 2) (fun i => prefixBits m (tabFam t L i x) = u)]
  rfl

private theorem mem_richList_iff {t m τ : ℕ} {L : List (List BitString)} {S : List BitString}
    (hS : S.Nodup) (hm : m ≤ t) (u : BitString) : u ∈ richList t m τ L S ↔
      u ∈ richPrefixValues (fun i : Fin (2 * t + 2) => tabFam t L i) m S.toFinset (2 ^ τ) := by
  rw [richList, List.mem_filter, decide_eq_true_eq, length_exactLengthPrograms,
    richCount_eq_card hS, richPrefixValues, Finset.mem_filter]
  constructor
  · rintro ⟨-, hlt⟩
    refine ⟨?_, hlt⟩
    obtain ⟨p, hp⟩ := Finset.card_pos.1 (lt_of_le_of_lt (Nat.zero_le _) hlt)
    rw [Finset.mem_filter] at hp
    exact Finset.mem_image.2 ⟨p, hp.1, hp.2⟩
  · rintro ⟨himg, hlt⟩
    refine ⟨?_, hlt⟩
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 himg
    have : (prefixBits m (tabFam t L p.1 p.2)).length = m := by
      simp [prefixBits, length_tabFam, hm]
    have h := mem_exactLengthPrograms_self (prefixBits m (tabFam t L p.1 p.2))
    rwa [this] at h

private theorem mem_badStage_iff {t m τ : ℕ} {L : List (List BitString)} {S : List BitString}
    (hS : S.Nodup) (hm : m ≤ t) (x : BitString) : x ∈ badStage t m τ L S ↔
      x ∈ majorityPrefixHits (fun i : Fin (2 * t + 2) => tabFam t L i) t m
        (richPrefixValues (fun i : Fin (2 * t + 2) => tabFam t L i) m S.toFinset (2 ^ τ)) := by
  rw [mem_majorityPrefixHits_iff, badStage, List.mem_filter, decide_eq_true_eq]
  have e : (List.range (2 * t + 2)).countP (fun i => decide ((tabFam t L i x).take m ∈
      richList t m τ L S)) = (List.range (2 * t + 2)).countP (fun i => decide (prefixBits m
        (tabFam t L i x) ∈ richPrefixValues (fun i : Fin (2 * t + 2) => tabFam t L i) m
          S.toFinset (2 ^ τ))) :=
    List.countP_congr fun i _ => by
      simp only [decide_eq_true_eq]
      exact mem_richList_iff hS hm _
  rw [e]
  constructor
  · rintro ⟨hx, h⟩
    exact ⟨exactLengthPrograms_length_eq t x hx, h⟩
  · rintro ⟨hx, h⟩
    exact ⟨hx ▸ mem_exactLengthPrograms_self x, h⟩

private abbrev RArg := ((ℕ × ℕ) × List (List BitString)) × List BitString × BitString

private theorem richCount_primrec :
    Primrec (fun r : RArg => richCount r.1.1.1 r.1.1.2 r.1.2 r.2.1 r.2.2) := by
  have hin : Primrec₂ (fun (b : RArg × BitString) (i : ℕ) =>
      (tabFam b.1.1.1.1 b.1.1.2 i b.2).take b.1.1.1.2) := by
    have hp : Primrec (fun q : (RArg × BitString) × ℕ =>
        (((q.1.1.1.1.1, q.1.1.1.2), q.2, q.1.2) : TabArg)) :=
      Primrec.pair (Primrec.pair
        (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
        (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
        (Primrec.pair Primrec.snd (Primrec.snd.comp Primrec.fst))
    exact (Primrec.list_take.comp
      (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
      (tabFam_primrec.comp hp)).of_eq fun _ => rfl
  have hN : Primrec (fun b : RArg × BitString => 2 * b.1.1.1.1 + 2) :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2)
      (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))) (Primrec.const 2)
  have hmap : Primrec₂ (fun (r : RArg) (x : BitString) =>
      (List.range (2 * r.1.1.1 + 2)).map fun i => (tabFam r.1.1.1 r.1.2 i x).take r.1.1.2) :=
    (Primrec.list_map (Primrec.list_range.comp hN) hin).of_eq fun _ => rfl
  have hfl : Primrec (fun r : RArg => r.2.1.flatMap fun x =>
      (List.range (2 * r.1.1.1 + 2)).map fun i => (tabFam r.1.1.1 r.1.2 i x).take r.1.1.2) :=
    Primrec.list_flatMap (Primrec.fst.comp Primrec.snd) hmap
  have heq : Primrec₂ (fun (r : RArg) (v : BitString) => decide (v = r.2.2)) :=
    (PrimrecRel.decide Primrec.eq).comp Primrec.snd
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  exact (list_countP_primrec hfl heq).of_eq fun _ => rfl

private abbrev BArg := ((ℕ × ℕ × ℕ) × List (List BitString)) × List BitString

private theorem richList_primrec :
    Primrec (fun b : BArg => richList b.1.1.1 b.1.1.2.1 b.1.1.2.2 b.1.2 b.2) := by
  have hc : Primrec₂ (fun (b : BArg) (u : BitString) =>
      richCount b.1.1.1 b.1.1.2.1 b.1.2 b.2 u) := by
    have hp : Primrec (fun q : BArg × BitString =>
        ((((q.1.1.1.1, q.1.1.1.2.1), q.1.1.2), q.1.2, q.2) : RArg)) :=
      Primrec.pair (Primrec.pair (Primrec.pair
        (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))))
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
        (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd)
    exact (richCount_primrec.comp hp).of_eq fun _ => rfl
  have hT : Primrec₂ (fun (b : BArg) (_ : BitString) => (exactLengthPrograms b.1.1.2.2).length) :=
    Primrec.list_length.comp (primrec_exactLengthPrograms.comp
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))))
  have hpr : Primrec₂ (fun (b : BArg) (u : BitString) => decide
      ((exactLengthPrograms b.1.1.2.2).length < richCount b.1.1.1 b.1.1.2.1 b.1.2 b.2 u)) :=
    (PrimrecRel.decide Primrec.nat_lt).comp hT hc
  have hl : Primrec (fun b : BArg => exactLengthPrograms b.1.1.2.1) :=
    primrec_exactLengthPrograms.comp (Primrec.fst.comp (Primrec.snd.comp
      (Primrec.fst.comp Primrec.fst)))
  exact (Primrec.list_filter hl hpr).of_eq fun _ => rfl

private theorem badStage_primrec :
    Primrec (fun b : BArg => badStage b.1.1.1 b.1.1.2.1 b.1.1.2.2 b.1.2 b.2) := by
  have hmem : Primrec₂ (fun (q : BArg × BitString) (i : ℕ) =>
      decide ((tabFam q.1.1.1.1 q.1.1.2 i q.2).take q.1.1.1.2.1 ∈
        richList q.1.1.1.1 q.1.1.1.2.1 q.1.1.1.2.2 q.1.1.2 q.1.2)) := by
    have hp : Primrec (fun r : (BArg × BitString) × ℕ =>
        (((r.1.1.1.1.1, r.1.1.1.2), r.2, r.1.2) : TabArg)) :=
      Primrec.pair (Primrec.pair
        (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
        (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
        (Primrec.pair Primrec.snd (Primrec.snd.comp Primrec.fst))
    have htk : Primrec (fun r : (BArg × BitString) × ℕ =>
        (tabFam r.1.1.1.1.1 r.1.1.1.2 r.2 r.1.2).take r.1.1.1.1.2.1) :=
      (Primrec.list_take.comp (Primrec.fst.comp (Primrec.snd.comp
        (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))))
        (tabFam_primrec.comp hp)).of_eq
        fun _ => rfl
    have hrl : Primrec (fun r : (BArg × BitString) × ℕ =>
        richList r.1.1.1.1.1 r.1.1.1.1.2.1 r.1.1.1.1.2.2 r.1.1.1.2 r.1.1.2) :=
      (richList_primrec.comp (Primrec.fst.comp Primrec.fst)).of_eq fun _ => rfl
    exact (bitString_mem_primrec.comp htk hrl).of_eq fun _ => rfl
  have hN : Primrec (fun q : BArg × BitString => 2 * q.1.1.1.1 + 2) :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2)
      (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))) (Primrec.const 2)
  have hcnt : Primrec (fun q : BArg × BitString => (List.range (2 * q.1.1.1.1 + 2)).countP
      fun i => decide ((tabFam q.1.1.1.1 q.1.1.2 i q.2).take q.1.1.1.2.1 ∈
        richList q.1.1.1.1 q.1.1.1.2.1 q.1.1.1.2.2 q.1.1.2 q.1.2)) :=
    list_countP_primrec (Primrec.list_range.comp hN) hmem
  have hp2 : Primrec₂ (fun (b : BArg) (x : BitString) => decide (2 * b.1.1.1 + 2 ≤
      2 * (List.range (2 * b.1.1.1 + 2)).countP fun i =>
        decide ((tabFam b.1.1.1 b.1.2 i x).take b.1.1.2.1 ∈
          richList b.1.1.1 b.1.1.2.1 b.1.1.2.2 b.1.2 b.2))) :=
    ((PrimrecRel.decide Primrec.nat_le).comp hN
      (Primrec.nat_mul.comp (Primrec.const 2) hcnt)).of_eq fun _ => rfl
  exact (Primrec.list_filter (primrec_exactLengthPrograms.comp
    (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))) hp2).of_eq fun _ => rfl

private theorem badStage_primrec' {α : Type*} [Primcodable α] {ft fm fτ : α → ℕ}
    {fL : α → List (List BitString)} {fS : α → List BitString} (ht : Primrec ft)
    (hm : Primrec fm) (hτ : Primrec fτ) (hL : Primrec fL) (hS : Primrec fS) :
    Primrec (fun a => badStage (ft a) (fm a) (fτ a) (fL a) (fS a)) :=
  (badStage_primrec.comp (Primrec.pair (Primrec.pair (Primrec.pair ht (Primrec.pair hm hτ)) hL)
    hS)).of_eq fun _ => rfl

private theorem richPrefixValues_mono {N : ℕ} (χ : Fin N → BitString → BitString) (m : ℕ)
    {S S' : Finset BitString} (h : S ⊆ S') (T : ℕ) :
    richPrefixValues χ m S T ⊆ richPrefixValues χ m S' T := by
  intro u hu
  rw [richPrefixValues, Finset.mem_filter] at hu ⊢
  have hsub : (Finset.univ : Finset (Fin N)) ×ˢ S ⊆ Finset.univ ×ˢ S' :=
    Finset.product_subset_product (Finset.Subset.refl _) h
  exact ⟨Finset.image_subset_image hsub hu.1,
    lt_of_lt_of_le hu.2 (Finset.card_le_card (Finset.filter_subset_filter _ hsub))⟩

private theorem majorityPrefixHits_mono {N : ℕ} (χ : Fin N → BitString → BitString) (n m : ℕ)
    {U U' : Finset BitString} (h : U ⊆ U') :
    majorityPrefixHits χ n m U ⊆ majorityPrefixHits χ n m U' := by
  intro x hx
  rw [majorityPrefixHits, Finset.mem_filter] at hx ⊢
  refine ⟨hx.1, hx.2.trans ?_⟩
  gcongr

private def encParams : List ℕ → BitString
  | [] => []
  | a :: l => pairCode (Nat.bits a) (encParams l)

private def prm : ℕ → BitString → ℕ
  | 0, w => bitsToNat (decodeFirst w)
  | k + 1, w => prm k (decodeSecond w)

private theorem prm_primrec : ∀ k, Primrec (prm k)
  | 0 => (bitsToNat_primrec.comp decodeFirst_primrec).of_eq fun _ => rfl
  | k + 1 => ((prm_primrec k).comp decodeSecond_primrec).of_eq fun _ => rfl

private theorem prm_encParams :
    ∀ (l : List ℕ) (k : ℕ), k < l.length → prm k (encParams l) = l.getD k 0
  | [], k, h => absurd h (by simp)
  | a :: l, 0, _ => by simp [prm, encParams, decodeFirst_pairCode, bitsToNat_bits]
  | a :: l, k + 1, h => by
    simp only [prm, encParams, decodeSecond_pairCode, List.getD_cons_succ]
    exact prm_encParams l k (by simpa using h)

private theorem length_encParams :
    ∀ l : List ℕ, (encParams l).length = (l.map fun a => 2 * (Nat.bits a).length + 1).sum
  | [] => rfl
  | a :: l => by
    simp only [encParams, length_pairCode, List.map_cons, List.sum_cons, length_encParams l]
    ring

private abbrev EArg := List (List BitString) × BitString × ℕ

private def enumBadCore (c : Code) (a : EArg) : List BitString :=
  (List.range (a.2.2 + 1)).flatMap fun s' =>
    badStage (prm 0 (decodeFirst a.2.1)) (prm 2 (decodeFirst a.2.1)) (prm 3 (decodeFirst a.2.1))
      a.1 (codeStage c (prm 0 (decodeFirst a.2.1)) (prm 1 (decodeFirst a.2.1))
        (decodeSecond a.2.1) s').eraseDups

private def enumBad (c : Code) (ctx : BitString) (s : ℕ) : List BitString :=
  enumBadCore c (hashTab (prm 0 (decodeFirst ctx)), ctx, s)

private theorem enumBadCore_primrec (c : Code) : Primrec (enumBadCore c) := by
  have hw : Primrec (fun q : EArg × ℕ => decodeFirst q.1.2.1) :=
    decodeFirst_primrec.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
  have hS : Primrec (fun q : EArg × ℕ => (codeStage c (prm 0 (decodeFirst q.1.2.1))
      (prm 1 (decodeFirst q.1.2.1)) (decodeSecond q.1.2.1) q.2).eraseDups) := by
    have hp : Primrec (fun q : EArg × ℕ => ((prm 0 (decodeFirst q.1.2.1),
        prm 1 (decodeFirst q.1.2.1)), decodeSecond q.1.2.1, q.2)) :=
      Primrec.pair (Primrec.pair ((prm_primrec 0).comp hw) ((prm_primrec 1).comp hw))
        (Primrec.pair (decodeSecond_primrec.comp (Primrec.fst.comp (Primrec.snd.comp
          Primrec.fst))) Primrec.snd)
    exact (eraseDups_bitstring_primrec.comp ((codeStage_primrec c).comp hp)).of_eq
      fun _ => rfl
  have hg : Primrec₂ (fun (a : EArg) (s' : ℕ) =>
      badStage (prm 0 (decodeFirst a.2.1)) (prm 2 (decodeFirst a.2.1)) (prm 3 (decodeFirst a.2.1))
        a.1 (codeStage c (prm 0 (decodeFirst a.2.1)) (prm 1 (decodeFirst a.2.1))
          (decodeSecond a.2.1) s').eraseDups) :=
    badStage_primrec' ((prm_primrec 0).comp hw) ((prm_primrec 2).comp hw)
      ((prm_primrec 3).comp hw) (Primrec.fst.comp Primrec.fst) hS
  exact (Primrec.list_flatMap (Primrec.list_range.comp (Primrec.succ.comp
    (Primrec.snd.comp Primrec.snd))) hg).of_eq fun _ => rfl

private theorem enumBad_computable (c : Code) :
    Computable fun p : BitString × ℕ => enumBad c p.1 p.2 := by
  have hp : Computable (fun p : BitString × ℕ =>
      ((hashTab (prm 0 (decodeFirst p.1)), p.1, p.2) : EArg)) :=
    Computable.pair (hashTab_computable.comp ((prm_primrec 0).comp
      (decodeFirst_primrec.comp Primrec.fst)).to_comp) Computable.id
  exact ((enumBadCore_primrec c).to_comp.comp hp).of_eq fun _ => rfl

private theorem enumBad_mono (c : Code) (y : BitString) (s : ℕ) :
    enumBad c y s <+: enumBad c y (s + 1) :=
  flatMap_range_prefix _ (Nat.le_succ s)

private def enumDecCore (c : Code) (a : EArg) : List BitString :=
  (List.range (a.2.2 + 1)).flatMap fun s' =>
    (codeStage c (prm 0 (decodeFirst a.2.1)) (prm 1 (decodeFirst a.2.1))
      (decodeFirst (decodeSecond a.2.1)) s').filter fun x =>
        decide ((tabFam (prm 0 (decodeFirst a.2.1)) a.1 (prm 2 (decodeFirst a.2.1)) x).take
          (decodeSecond (decodeSecond a.2.1)).length = decodeSecond (decodeSecond a.2.1))

private def enumDec (c : Code) (ctx : BitString) (s : ℕ) : List BitString :=
  enumDecCore c (hashTab (prm 0 (decodeFirst ctx)), ctx, s)

private theorem enumDecCore_primrec (c : Code) : Primrec (enumDecCore c) := by
  have hw : Primrec (fun q : EArg × ℕ => decodeFirst q.1.2.1) :=
    decodeFirst_primrec.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
  have hy : Primrec (fun q : EArg × ℕ => decodeSecond q.1.2.1) :=
    decodeSecond_primrec.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
  have hS : Primrec (fun q : EArg × ℕ => codeStage c (prm 0 (decodeFirst q.1.2.1))
      (prm 1 (decodeFirst q.1.2.1)) (decodeFirst (decodeSecond q.1.2.1)) q.2) := by
    have hp : Primrec (fun q : EArg × ℕ => ((prm 0 (decodeFirst q.1.2.1),
        prm 1 (decodeFirst q.1.2.1)), decodeFirst (decodeSecond q.1.2.1), q.2)) :=
      Primrec.pair (Primrec.pair ((prm_primrec 0).comp hw) ((prm_primrec 1).comp hw))
        (Primrec.pair (decodeFirst_primrec.comp hy) Primrec.snd)
    exact ((codeStage_primrec c).comp hp).of_eq fun _ => rfl
  have hf : Primrec₂ (fun (q : EArg × ℕ) (x : BitString) =>
      decide ((tabFam (prm 0 (decodeFirst q.1.2.1)) q.1.1 (prm 2 (decodeFirst q.1.2.1)) x).take
        (decodeSecond (decodeSecond q.1.2.1)).length = decodeSecond (decodeSecond q.1.2.1))) := by
    have hw' : Primrec (fun r : (EArg × ℕ) × BitString => decodeFirst r.1.1.2.1) :=
      hw.comp Primrec.fst
    have hX : Primrec (fun r : (EArg × ℕ) × BitString => decodeSecond (decodeSecond r.1.1.2.1)) :=
      decodeSecond_primrec.comp (hy.comp Primrec.fst)
    have hp : Primrec (fun r : (EArg × ℕ) × BitString =>
        (((prm 0 (decodeFirst r.1.1.2.1), r.1.1.1), prm 2 (decodeFirst r.1.1.2.1), r.2) :
          TabArg)) :=
      Primrec.pair (Primrec.pair ((prm_primrec 0).comp hw')
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
        (Primrec.pair ((prm_primrec 2).comp hw') Primrec.snd)
    have htk : Primrec (fun r : (EArg × ℕ) × BitString =>
        (tabFam (prm 0 (decodeFirst r.1.1.2.1)) r.1.1.1 (prm 2 (decodeFirst r.1.1.2.1)) r.2).take
          (decodeSecond (decodeSecond r.1.1.2.1)).length) :=
      (Primrec.list_take.comp (Primrec.list_length.comp hX) (tabFam_primrec.comp hp)).of_eq
        fun _ => rfl
    exact ((PrimrecRel.decide Primrec.eq).comp htk hX).of_eq fun _ => rfl
  have hg : Primrec₂ (fun (a : EArg) (s' : ℕ) =>
      (codeStage c (prm 0 (decodeFirst a.2.1)) (prm 1 (decodeFirst a.2.1))
        (decodeFirst (decodeSecond a.2.1)) s').filter fun x =>
          decide ((tabFam (prm 0 (decodeFirst a.2.1)) a.1 (prm 2 (decodeFirst a.2.1)) x).take
            (decodeSecond (decodeSecond a.2.1)).length = decodeSecond (decodeSecond a.2.1))) :=
    (Primrec.list_filter hS hf).of_eq fun _ => rfl
  exact (Primrec.list_flatMap (Primrec.list_range.comp (Primrec.succ.comp
    (Primrec.snd.comp Primrec.snd))) hg).of_eq fun _ => rfl

private theorem enumDec_computable (c : Code) :
    Computable fun p : BitString × ℕ => enumDec c p.1 p.2 := by
  have hp : Computable (fun p : BitString × ℕ =>
      ((hashTab (prm 0 (decodeFirst p.1)), p.1, p.2) : EArg)) :=
    Computable.pair (hashTab_computable.comp ((prm_primrec 0).comp
      (decodeFirst_primrec.comp Primrec.fst)).to_comp) Computable.id
  exact ((enumDecCore_primrec c).to_comp.comp hp).of_eq fun _ => rfl

private theorem enumDec_mono (c : Code) (y : BitString) (s : ℕ) :
    enumDec c y s <+: enumDec c y (s + 1) :=
  flatMap_range_prefix _ (Nat.le_succ s)

private theorem card_codeStage_toFinset_lt {c : Code} {t k : ℕ} {Y : BitString} {s : ℕ} :
    (codeStage c t k Y s).toFinset.card < 2 ^ (k + 1) :=
  lt_of_le_of_lt ((List.toFinset_card_le _).trans (List.length_filterMap_le _ _))
    (length_boundedPrograms_lt k)

private theorem card_codeStage_toFinset_le {c : Code} {D : Map} (hc : IsCodeFor c D) {t k : ℕ}
    {Y : BitString} {s : ℕ} : (codeStage c t k Y s).toFinset.card ≤ 2 ^ t := by
  rw [← card_stringsOfLength t]
  refine Finset.card_le_card fun x hx => ?_
  obtain ⟨C', -, hC'⟩ := codeStage_spec hc (List.mem_toFinset.1 hx)
  exact (mem_stringsOfLength t x).2 (codeAt_spec hc hC').1

private theorem two_pow_size_pred_le {n : ℕ} (hn : 0 < n) : 2 ^ (Nat.size n - 1) ≤ n := by
  by_contra h
  push Not at h
  have h1 := Nat.size_le.2 h
  have h2 := Nat.size_pos.2 hn
  omega

private theorem not_majority_bad (D : Map) {c : Code} (hc : IsCodeFor c D) {cBad : ℕ}
    (hBad : ∀ (w y x out : BitString) (F : Finset BitString),
      (∃ s, x ∈ enumBad c (pairCode w y) s) → (∀ s, ∀ v ∈ enumBad c (pairCode w y) s, v ∈ F) →
      out ∈ D (x, []) →
      condK D out y ≤ ((2 * w.length + (Nat.bits F.card).length + cBad : ℕ) : ℕ∞))
    {t kY m τ s0 sY : ℕ} {Y C P : BitString} (hP : codeAt c t C s0 = some P)
    (hkY : condK D C Y = kY) (hm1 : 1 ≤ m) (hmt : m ≤ t) (hmk : kY ≤ m ∨ m = t)
    (hT : 128 * (2 * t + 2) ≤ 2 ^ τ)
    (hτ : 2 * (encParams [t, kY, m, τ]).length + Nat.size (2 * t + 2) + 1 + cBad < τ)
    (hstab : ∀ s, ∀ x ∈ codeStage c t kY Y s, x ∈ codeStage c t kY Y sY) :
    2 * (Finset.univ.filter fun i : Fin (2 * t + 2) => prefixBits m (tabFam t (hashTab t) i P) ∈
      richPrefixValues (fun i : Fin (2 * t + 2) => tabFam t (hashTab t) i) m
        (codeStage c t kY Y sY).toFinset (2 ^ τ)).card < 2 * t + 2 := by
  classical
  set χ : Fin (2 * t + 2) → BitString → BitString := fun i => tabFam t (hashTab t) i with hχ
  set SY := (codeStage c t kY Y sY).toFinset with hSY
  set W := majorityPrefixHits χ t m (richPrefixValues χ m SY (2 ^ τ)) with hW
  by_contra hge
  push Not at hge
  obtain ⟨hPlen, hCP⟩ := codeAt_spec hc hP
  have hPW : P ∈ W := by
    rw [hW, majorityPrefixHits, Finset.mem_filter, mem_stringsOfLength]
    exact ⟨hPlen, hge⟩
  have hS2 : SY.card < 2 * 2 ^ m := by
    rcases hmk with h | h
    · calc SY.card < 2 ^ (kY + 1) := card_codeStage_toFinset_lt
        _ ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 2 * 2 ^ m := by ring
    · calc SY.card ≤ 2 ^ t := card_codeStage_toFinset_le hc
        _ < 2 * 2 ^ m := by rw [h]; have := Nat.one_le_two_pow (n := t); omega
  have hWT : W.card * 2 ^ τ ≤ (2 * t + 2) * SY.card := by
    have htN : 0 < 2 * t + 2 := by omega
    refine card_majorityPrefixHits_richPrefixValues_mul_le χ t m (1 / 64)
      (fun i x => length_tabFam _ _ _ _) hmt htN
      (hash_spec_of_hashBad_false (hashBad_hashTab t) m hm1 hmt) SY (2 ^ τ) hS2 ?_
    have : ((128 * (2 * t + 2) : ℕ) : ℝ) ≤ ((2 ^ τ : ℕ) : ℝ) := by exact_mod_cast hT
    push_cast at this ⊢
    linarith
  have hwv : ∀ k (hk : k < 4), prm k (encParams [t, kY, m, τ]) = [t, kY, m, τ].getD k 0 :=
    fun k hk => prm_encParams _ k (by simpa using hk)
  have hin : ∃ s, P ∈ enumBad c (pairCode (encParams [t, kY, m, τ]) Y) s := by
    refine ⟨sY, ?_⟩
    simp only [enumBad, enumBadCore, decodeFirst_pairCode, decodeSecond_pairCode,
      hwv 0 (by norm_num), hwv 1 (by norm_num), hwv 2 (by norm_num), hwv 3 (by norm_num),
      List.getD_cons_zero, List.getD_cons_succ, List.mem_flatMap, List.mem_range]
    refine ⟨sY, by omega, (mem_badStage_iff (nodup_eraseDups_list _) hmt P).2 ?_⟩
    have e : (codeStage c t kY Y sY).eraseDups.toFinset = SY := by
      ext v
      simp only [List.mem_toFinset, hSY]
      exact mem_eraseDups_iff
    rw [e]
    exact hPW
  have hall : ∀ s, ∀ v ∈ enumBad c (pairCode (encParams [t, kY, m, τ]) Y) s, v ∈ W := by
    intro s v hv
    simp only [enumBad, enumBadCore, decodeFirst_pairCode, decodeSecond_pairCode,
      hwv 0 (by norm_num), hwv 1 (by norm_num), hwv 2 (by norm_num), hwv 3 (by norm_num),
      List.getD_cons_zero, List.getD_cons_succ, List.mem_flatMap, List.mem_range] at hv
    obtain ⟨s', -, hv⟩ := hv
    rw [mem_badStage_iff (nodup_eraseDups_list _) hmt v] at hv
    refine majorityPrefixHits_mono χ t m (richPrefixValues_mono χ m ?_ (2 ^ τ)) hv
    intro x hx
    rw [List.mem_toFinset, mem_eraseDups_iff] at hx
    exact List.mem_toFinset.2 (hstab s' x hx)
  have hK := hBad _ Y P C W hin hall hCP
  rw [hkY, Nat.size_eq_bits_len] at hK
  have hK' : kY ≤ 2 * (encParams [t, kY, m, τ]).length + Nat.size W.card + cBad := by
    exact_mod_cast hK
  have hWpos : 0 < W.card := Finset.card_pos.2 ⟨P, hPW⟩
  have h1 := two_pow_size_pred_le hWpos
  have h2 : (2 * t + 2) < 2 ^ Nat.size (2 * t + 2) := Nat.lt_size_self _
  have h3 : 2 ^ (Nat.size W.card - 1) * 2 ^ τ < 2 ^ Nat.size (2 * t + 2) * 2 ^ (kY + 1) :=
    calc 2 ^ (Nat.size W.card - 1) * 2 ^ τ ≤ W.card * 2 ^ τ := Nat.mul_le_mul_right _ h1
      _ ≤ (2 * t + 2) * SY.card := hWT
      _ < (2 * t + 2) * 2 ^ (kY + 1) :=
        (Nat.mul_lt_mul_left (by omega)).2 card_codeStage_toFinset_lt
      _ ≤ 2 ^ Nat.size (2 * t + 2) * 2 ^ (kY + 1) := Nat.mul_le_mul_right _ h2.le
  rw [← pow_add, ← pow_add] at h3
  have h4 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 h3
  have h5 := Nat.size_pos.2 hWpos
  omega

private theorem condK_decoder_le (D : Map) {c : Code} (hc : IsCodeFor c D) {cDec : ℕ}
    (hDec : ∀ (w y x out : BitString) (F : Finset BitString),
      (∃ s, x ∈ enumDec c (pairCode w y) s) → (∀ s, ∀ v ∈ enumDec c (pairCode w y) s, v ∈ F) →
      out ∈ D (x, []) →
      condK D out y ≤ ((2 * w.length + (Nat.bits F.card).length + cDec : ℕ) : ℕ∞))
    {t kY m τ i s0 sY : ℕ} {Y C P : BitString} (hP : codeAt c t C s0 = some P)
    (hCY : condK D C Y ≤ (kY : ℕ∞)) (hmt : m ≤ t) (hi : i < 2 * t + 2)
    (hstab : ∀ s, ∀ x ∈ codeStage c t kY Y s, x ∈ codeStage c t kY Y sY)
    (hgood : prefixBits m (tabFam t (hashTab t) i P) ∉
      richPrefixValues (fun i : Fin (2 * t + 2) => tabFam t (hashTab t) i) m
        (codeStage c t kY Y sY).toFinset (2 ^ τ)) :
    condK D C (pairCode Y (prefixBits m (tabFam t (hashTab t) i P))) ≤
      ((2 * (encParams [t, kY, i]).length + (τ + 1) + cDec : ℕ) : ℕ∞) := by
  classical
  set X := prefixBits m (tabFam t (hashTab t) i P) with hX
  set SY := (codeStage c t kY Y sY).toFinset with hSY
  have hXlen : X.length = m := by simp [hX, prefixBits, length_tabFam, hmt]
  obtain ⟨hPlen, hCP⟩ := codeAt_spec hc hP
  obtain ⟨s1, hs1⟩ := mem_codeStage_of hc hCY hP
  have hPSY : P ∈ SY := List.mem_toFinset.2 (hstab s1 P hs1)
  set F := SY.filter fun y => prefixBits m (tabFam t (hashTab t) i y) = X with hF
  have hFcard : F.card ≤ 2 ^ τ :=
    card_filter_prefixBits_eq_le_of_notMem_richPrefixValues
      (fun i : Fin (2 * t + 2) => tabFam t (hashTab t) i) m SY (2 ^ τ) ⟨i, hi⟩ P hPSY hgood
  have hwv : ∀ k (hk : k < 3), prm k (encParams [t, kY, i]) = [t, kY, i].getD k 0 :=
    fun k hk => prm_encParams _ k (by simpa using hk)
  have hunf : ∀ s v, v ∈ enumDec c (pairCode (encParams [t, kY, i]) (pairCode Y X)) s ↔
      ∃ s' < s + 1, v ∈ codeStage c t kY Y s' ∧ (tabFam t (hashTab t) i v).take m = X := by
    intro s v
    simp only [enumDec, enumDecCore, decodeFirst_pairCode, decodeSecond_pairCode,
      hwv 0 (by norm_num), hwv 1 (by norm_num), hwv 2 (by norm_num), List.getD_cons_zero,
      List.getD_cons_succ, List.mem_flatMap, List.mem_range, List.mem_filter, decide_eq_true_eq,
      hXlen]
  have hin : ∃ s, P ∈ enumDec c (pairCode (encParams [t, kY, i]) (pairCode Y X)) s :=
    ⟨s1, (hunf s1 P).2 ⟨s1, by omega, hs1, rfl⟩⟩
  have hall : ∀ s, ∀ v ∈ enumDec c (pairCode (encParams [t, kY, i]) (pairCode Y X)) s,
      v ∈ F := by
    intro s v hv
    obtain ⟨s', -, hv1, hv2⟩ := (hunf s v).1 hv
    exact Finset.mem_filter.2 ⟨List.mem_toFinset.2 (hstab s' v hv1), hv2⟩
  have hK := hDec _ _ P C F hin hall hCP
  have hbits : (Nat.bits F.card).length ≤ τ + 1 := by
    rw [Nat.size_eq_bits_len, Nat.size_le]
    calc F.card ≤ 2 ^ τ := hFcard
      _ < 2 ^ (τ + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  refine hK.trans ?_
  exact_mod_cast (by omega)

private theorem tabFam_computable' {α : Type*} [Primcodable α] {ft fi : α → ℕ}
    {fL : α → List (List BitString)} {fx : α → BitString} (ht : Computable ft)
    (hL : Computable fL) (hi : Computable fi) (hx : Computable fx) :
    Computable (fun a => tabFam (ft a) (fL a) (fi a) (fx a)) :=
  (tabFam_primrec.to_comp.comp (Computable.pair (Computable.pair ht hL)
    (Computable.pair hi hx))).of_eq fun _ => rfl

private theorem condK_hashPrefix_le (D : Map) (hD : isOptimalConditional D) (c : Code) :
    ∃ cX : ℕ, ∀ (t a i : ℕ) (C P : BitString), P ∈ codeOf c t C →
      condK D ((tabFam t (hashTab t) i P).take a) C ≤
        (((encParams [t, a, i]).length + cX : ℕ) : ℕ∞) := by
  let DX : Map := fun pr => (codeOf c (prm 0 pr.1) pr.2).map fun P =>
    (tabFam (prm 0 pr.1) (hashTab (prm 0 pr.1)) (prm 2 pr.1) P).take (prm 1 pr.1)
  have hDX : isDecompressor DX := by
    have h0 : Computable (fun pr : BitString × BitString => prm 0 pr.1) :=
      ((prm_primrec 0).comp Primrec.fst).to_comp
    have hcode : Partrec (fun pr : BitString × BitString => codeOf c (prm 0 pr.1) pr.2) :=
      ((codeOf_partrec c).comp (Computable.pair h0 Computable.snd)).of_eq fun _ => rfl
    have hg : Computable₂ (fun (pr : BitString × BitString) (P : BitString) =>
        (tabFam (prm 0 pr.1) (hashTab (prm 0 pr.1)) (prm 2 pr.1) P).take (prm 1 pr.1)) := by
      have h0' : Computable (fun q : (BitString × BitString) × BitString => prm 0 q.1.1) :=
        h0.comp Computable.fst
      have htab : Computable (fun q : (BitString × BitString) × BitString =>
          tabFam (prm 0 q.1.1) (hashTab (prm 0 q.1.1)) (prm 2 q.1.1) q.2) :=
        tabFam_computable' h0' (hashTab_computable.comp h0')
          (((prm_primrec 2).comp (Primrec.fst.comp Primrec.fst)).to_comp) Computable.snd
      exact (Primrec.list_take.to_comp.comp
        (((prm_primrec 1).comp (Primrec.fst.comp Primrec.fst)).to_comp) htab).of_eq fun _ => rfl
    exact hcode.map hg
  obtain ⟨cX, hcX⟩ := hD.2 DX hDX
  refine ⟨cX, fun t a i C P hP => ?_⟩
  have hwv : ∀ k (hk : k < 3), prm k (encParams [t, a, i]) = [t, a, i].getD k 0 :=
    fun k hk => prm_encParams _ k (by simpa using hk)
  have hmem : (tabFam t (hashTab t) i P).take a ∈ DX (encParams [t, a, i], C) := by
    simp only [DX, hwv 0 (by norm_num), hwv 1 (by norm_num), hwv 2 (by norm_num),
      List.getD_cons_zero, List.getD_cons_succ]
    exact Part.mem_map _ hP
  have h1 : condK DX ((tabFam t (hashTab t) i P).take a) C ≤
      ((encParams [t, a, i]).length : ℕ∞) := (condK_le_iff DX _ _ _).2 ⟨_, le_rfl, hmem⟩
  calc condK D ((tabFam t (hashTab t) i P).take a) C
      ≤ condK DX ((tabFam t (hashTab t) i P).take a) C + (cX : ℕ∞) := hcX _ _
    _ ≤ ((encParams [t, a, i]).length : ℕ∞) + (cX : ℕ∞) := by gcongr
    _ = (((encParams [t, a, i]).length + cX : ℕ) : ℕ∞) := by push_cast; rfl

private theorem size_add_le' (a b : ℕ) : Nat.size (a + b) ≤ Nat.size a + Nat.size b + 1 := by
  rw [Nat.size_le]
  have ha := Nat.lt_size_self a
  have hb := Nat.lt_size_self b
  have h1 : 2 ^ Nat.size a ≤ 2 ^ (Nat.size a + Nat.size b) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 2 ^ Nat.size b ≤ 2 ^ (Nat.size a + Nat.size b) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [pow_succ]
  omega

private theorem size_mul_le' (a b : ℕ) : Nat.size (a * b) ≤ Nat.size a + Nat.size b := by
  rw [Nat.size_le, pow_add]
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp
  exact lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self a) hb)
    (Nat.mul_le_mul_left _ (Nat.lt_size_self b).le)

private theorem size_le_self' (a : ℕ) : Nat.size a ≤ a :=
  Nat.size_le.2 Nat.lt_two_pow_self

private theorem length_encParams_le (l : List ℕ) (B : ℕ) (h : ∀ a ∈ l, Nat.size a ≤ B) :
    (encParams l).length ≤ l.length * (2 * B + 1) := by
  induction l with
  | nil => simp [encParams]
  | cons a l ih =>
    simp only [encParams, length_pairCode, List.length_cons]
    have h1 := h a List.mem_cons_self
    have h2 := ih fun b hb => h b (List.mem_cons_of_mem _ hb)
    rw [Nat.size_eq_bits_len]
    nlinarith

end TwoConditionCodes

/-- Muchnik's theorem for two conditions with different capacities: with `C(C|A) ≤ k`,
`C(C|B) ≤ l` and `l ≤ k`, a string `X` of length at most `k`, simple given `C`, serves the
decoder that knows `A`, and its `l`-bit prefix already serves the decoder that knows `B`.

The book prints "a string `X` of length `k`"; the statement says "length at most `k`", which is
what the proof gives (it first decreases `k` and `l` to the conditional complexities). Exact
length `k` would be false: `k` is not bounded in terms of `n`, and only finitely many strings
have `C(X|C) = O(log n)` for fixed `n` and `C`, so they cannot have every length `k`.

SUV Theorem 235, p. 380. -/
theorem exists_twoConditionCode_prefix (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ (n k l : ℕ) (A B C : BitString),
      plainK D A ≤ (n : ℕ∞) → plainK D B ≤ (n : ℕ∞) → plainK D C ≤ (n : ℕ∞) → 0 < l → l ≤ k →
      condK D C A ≤ (k : ℕ∞) → condK D C B ≤ (l : ℕ∞) →
      ∃ X : BitString, X.length ≤ k ∧
        condK D X C ≤ (logSlack c n : ℕ∞) ∧
        condK D C (pairCode A X) ≤ (logSlack c n : ℕ∞) ∧
        condK D C (pairCode B (X.take l)) ≤ (logSlack c n : ℕ∞) := by
  classical
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hD.1
  obtain ⟨c0, hc0⟩ := condK_le_plainK D hD
  obtain ⟨cl, hcl⟩ := plainK_le_length D hD
  obtain ⟨cBad, hBad⟩ := condK_le_of_enumeration D hD (enumBad c) (enumBad_computable c)
    (enumBad_mono c)
  obtain ⟨cDec, hDec⟩ := condK_le_of_enumeration D hD (enumDec c) (enumDec_computable c)
    (enumDec_mono c)
  obtain ⟨cX, hcX⟩ := condK_hashPrefix_le D hD c
  obtain ⟨K, hK⟩ : ∃ K, K = 16 * Nat.size c0 + cBad + 200 := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, d = 2 ^ (K + 5) := ⟨_, rfl⟩
  have hsd : Nat.size d = K + 6 := hd ▸ Nat.size_pow
  have hKd : 32 * (K + 1) ≤ d := by
    have h1 : K < 2 ^ K := Nat.lt_two_pow_self
    have h2 : d = 2 ^ K * 32 := by rw [hd, pow_add]; norm_num
    omega
  refine ⟨d + 12 * Nat.size c0 + 12 * Nat.size d + cDec + cX + cl + c0 + 100,
    fun n k l A B C hA hB hC hl hlk hCA hCB => ?_⟩
  obtain ⟨cF, hcF⟩ : ∃ cF, cF = d + 12 * Nat.size c0 + 12 * Nat.size d + cDec + cX + cl + c0 +
    100 := ⟨_, rfl⟩
  rw [← hcF]
  obtain ⟨L, hL⟩ : ∃ L, L = Nat.size n := ⟨_, rfl⟩
  have hfin : ∀ (N : ℕ) (x y : BitString), N ≤ cF * L + cF → condK D x y ≤ (N : ℕ∞) →
      condK D x y ≤ (logSlack cF n : ℕ∞) := fun N x y hN h =>
    h.trans (by rw [logSlack, Nat.size_eq_bits_len, ← hL]; exact_mod_cast hN)
  obtain ⟨P0, hP0len, hP0⟩ := (condK_le_iff D C [] n).1 hC
  rcases Nat.eq_zero_or_pos P0.length with ht0 | ht0
  · have hCt : plainK D C ≤ ((0 : ℕ) : ℕ∞) := (condK_le_iff D C [] 0).2 ⟨P0, ht0.le, hP0⟩
    have hC0 : ∀ y, condK D C y ≤ ((c0 : ℕ) : ℕ∞) := fun y =>
      (hc0 C y).trans (by simpa using add_le_add hCt (le_refl (c0 : ℕ∞)))
    refine ⟨[], by simp, hfin (cl + c0) _ _ (by nlinarith) ?_,
      hfin c0 _ _ (by nlinarith) (hC0 _), hfin c0 _ _ (by nlinarith) (hC0 _)⟩
    refine (hc0 _ _).trans ?_
    have := add_le_add_right (hcl []) (c0 : ℕ∞)
    simpa using this
  obtain ⟨t, ht⟩ : ∃ t, t = P0.length := ⟨_, rfl⟩
  have htn : t ≤ n := ht ▸ hP0len
  obtain ⟨s0, hs0⟩ := codeAt_exists hc hP0
  rw [← ht] at hs0 ht0
  obtain ⟨P, hP⟩ := Option.isSome_iff_exists.1 hs0
  obtain ⟨hPlen, hCP⟩ := codeAt_spec hc hP
  have hCt : plainK D C ≤ (t : ℕ∞) := (condK_le_iff D C [] t).2 ⟨P, hPlen.le, hCP⟩
  have hkY : ∀ (Y : BitString) (m : ℕ), condK D C Y ≤ (m : ℕ∞) →
      ∃ kY : ℕ, condK D C Y = kY ∧ kY ≤ m ∧ kY ≤ t + c0 := by
    intro Y m hY
    have h1 := (hc0 C Y).trans (add_le_add hCt (le_refl (c0 : ℕ∞)))
    obtain ⟨kY, hkY⟩ := ENat.ne_top_iff_exists.1
      (ne_top_of_le_ne_top (ENat.natCast_ne_top m) hY)
    rw [← hkY] at hY h1 ⊢
    exact ⟨kY, rfl, by exact_mod_cast hY, by exact_mod_cast h1⟩
  obtain ⟨kA, hkA, hkAk, hkAt⟩ := hkY A k hCA
  obtain ⟨kB, hkB, hkBl, hkBt⟩ := hkY B l hCB
  obtain ⟨Bs, hBs⟩ : ∃ Bs, Bs = L + Nat.size c0 + Nat.size d + 4 := ⟨_, rfl⟩
  have hsize : ∀ x, x ≤ 4 * n + c0 → Nat.size x ≤ Bs := by
    intro x hx
    have h1 := Nat.size_le_size hx
    have h2 := size_add_le' (4 * n) c0
    have h3 := size_mul_le' 4 n
    have h4 : Nat.size 4 = 3 := Nat.size_pow (n := 2)
    omega
  obtain ⟨τ, hτ⟩ : ∃ τ, τ = d * (L + 1) := ⟨_, rfl⟩
  have hsτ : Nat.size τ ≤ Bs := by
    have h1 := size_mul_le' d (L + 1)
    have h2 := size_le_self' (L + 1)
    rw [hτ]
    omega
  have hT : 128 * (2 * t + 2) ≤ 2 ^ τ := by
    have hnL : n < 2 ^ L := hL ▸ Nat.lt_size_self n
    have h1 : 2 ^ (L + 8) = 2 ^ L * 256 := by rw [pow_add]; norm_num
    have h2 : L + 8 ≤ τ := by rw [hτ]; nlinarith
    calc 128 * (2 * t + 2) ≤ 2 ^ (L + 8) := by omega
      _ ≤ 2 ^ τ := Nat.pow_le_pow_right (by norm_num) h2
  have hdL : 32 * L ≤ d * L := Nat.mul_le_mul_right _ (by omega)
  have hτ' : τ = d * L + d := by rw [hτ, mul_add, mul_one]
  have henc4 : ∀ x y, x ≤ 4 * n + c0 → y ≤ 4 * n + c0 →
      (encParams [t, x, y, τ]).length ≤ 4 * (2 * Bs + 1) := by
    intro x y hx hy
    refine length_encParams_le _ Bs fun z hz => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    exacts [hsize _ (by omega), hsize _ hx, hsize _ hy, hsτ]
  have henc3 : ∀ x y, x ≤ 4 * n + c0 → y ≤ 4 * n + c0 →
      (encParams [t, x, y]).length ≤ 3 * (2 * Bs + 1) := by
    intro x y hx hy
    refine length_encParams_le _ Bs fun z hz => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl
    exacts [hsize _ (by omega), hsize _ hx, hsize _ hy]
  have hs2 := hsize (2 * t + 2) (by omega)
  have hτbad : ∀ x y, x ≤ 4 * n + c0 → y ≤ 4 * n + c0 →
      2 * (encParams [t, x, y, τ]).length + Nat.size (2 * t + 2) + 1 + cBad < τ := by
    intro x y hx hy
    have := henc4 x y hx hy
    omega
  obtain ⟨a, ha⟩ : ∃ a, a = min k t := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = min l t := ⟨_, rfl⟩
  obtain ⟨sA, hsA⟩ := exists_stage_stable (f := codeStage c t kA A)
    (fun s s' x h hx => codeStage_mono hx h) (fun s => List.length_filterMap_le _ _)
  obtain ⟨sB, hsB⟩ := exists_stage_stable (f := codeStage c t kB B)
    (fun s s' x h hx => codeStage_mono hx h) (fun s => List.length_filterMap_le _ _)
  have ha1 : 1 ≤ a := by omega
  have hat : a ≤ t := by omega
  have hka : kA ≤ a ∨ a = t := by omega
  have hbadA := not_majority_bad D hc hBad hP hkA ha1 hat hka hT
    (hτbad kA a (by omega) (by omega)) hsA
  have hb1 : 1 ≤ b := by omega
  have hbt : b ≤ t := by omega
  have hkb : kB ≤ b ∨ b = t := by omega
  have hbadB := not_majority_bad D hc hBad hP hkB hb1 hbt hkb hT
    (hτbad kB b (by omega) (by omega)) hsB
  obtain ⟨i, hiA, hiB⟩ := exists_index_prefixBits_notMem_of_lt_half _ a b _ _ P hbadA hbadB
  have hi := i.isLt
  have hcFL : d * L + 12 * L ≤ cF * L := by
    rw [← add_mul]
    exact Nat.mul_le_mul_right _ (by omega)
  refine ⟨prefixBits a (tabFam t (hashTab t) i P), ?_, ?_, ?_, ?_⟩
  · simp only [prefixBits, List.length_take, length_tabFam]
    omega
  · refine hfin _ _ _ ?_ (hcX t a i C P (mem_codeOf hP))
    have := henc3 a i (by omega) (by omega)
    omega
  · have hat : a ≤ t := by omega
    refine hfin _ _ _ ?_ (condK_decoder_le D hc hDec hP hkA.le hat hi hsA hiA)
    have := henc3 kA i (by omega) (by omega)
    omega
  · have hab : (prefixBits a (tabFam t (hashTab t) i P)).take l =
        prefixBits b (tabFam t (hashTab t) i P) := by
      simp only [prefixBits, List.take_take]
      congr 1
      omega
    rw [hab]
    have hbt : b ≤ t := by omega
    refine hfin _ _ _ ?_ (condK_decoder_le D hc hDec hP hkB.le hbt hi hsB hiB)
    have := henc3 kB i (by omega) (by omega)
    omega

/-- Muchnik's theorem for two conditions: if `C(C|A) ≤ k` and `C(C|B) ≤ k` for strings of
complexity at most `n`, then one string `X` of length at most `k + O(log n)`, simple given
`C`, lets both decoders restore `C`.

SUV Theorem 234, p. 379. -/
theorem exists_twoConditionCode (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ (n k : ℕ) (A B C : BitString),
      plainK D A ≤ (n : ℕ∞) → plainK D B ≤ (n : ℕ∞) → plainK D C ≤ (n : ℕ∞) → 0 < k →
      condK D C A ≤ (k : ℕ∞) → condK D C B ≤ (k : ℕ∞) →
      ∃ X : BitString, X.length ≤ k + logSlack c n ∧
        condK D X C ≤ (logSlack c n : ℕ∞) ∧
        condK D C (pairCode A X) ≤ (logSlack c n : ℕ∞) ∧
        condK D C (pairCode B X) ≤ (logSlack c n : ℕ∞) := by
  obtain ⟨c, hc⟩ := exists_twoConditionCode_prefix D hD
  refine ⟨c, fun n k A B C hA hB hC hk hCA hCB => ?_⟩
  obtain ⟨X, hXlen, hXC, hXA, hXB⟩ := hc n k k A B C hA hB hC hk le_rfl hCA hCB
  rw [List.take_of_length_le hXlen] at hXB
  exact ⟨X, hXlen.trans (Nat.le_add_right _ _), hXC, hXA, hXB⟩

/-- The request of SUV Problem 324 for Theorem 235: the input node `0` holds `C` and sends its
message in two pieces — a prefix of capacity `l` through the relay `5` and a remainder of
capacity `k - l` — while `1` and `2` hold `A` and `B`.  The output node `3` reads `A`, the
relay and the remainder; the output node `4` reads only `B` and the relay; both must produce
`C`.

SUV Problem 324, p. 380. -/
def twoConditionsRequest (A B C : BitString) (k l : ℕ) : InformationRequest (Fin 6) where
  edges := {(0, 5), (5, 3), (5, 4), (0, 3), (1, 3), (2, 4)}
  rank v := if v.val = 5 then 1 else if v.val ≤ 2 then 0 else 2
  rank_lt := by decide +kernel
  capacity e := if e = (0, 5) then (l : ℕ∞) else if e = (0, 3) then ((k - l : ℕ) : ℕ∞) else ⊤
  input v := if v = 0 then some C else if v = 1 then some A else if v = 2 then some B else none
  output v := if v = 3 ∨ v = 4 then some C else none

/-- Replacing the condition by a computable image of it costs a constant (a local copy of
`condK_cond_map_le`, whose module is not imported here). -/
private theorem condK_cond_comp_le (D : Map) (hD : isOptimalConditional D)
    (s : BitString → BitString) (hs : Computable s) :
    ∃ c : ℕ, ∀ x y : BitString, condK D x y ≤ condK D x (s y) + (c : ℕ∞) := by
  let D' : Map := fun pr => D (pr.1, s pr.2)
  have hD' : isDecompressor D' :=
    hD.1.comp (Computable.pair Computable.fst (hs.comp Computable.snd))
  obtain ⟨c, hc⟩ := hD.2 D' hD'
  refine ⟨c, fun x y => (hc x y).trans ?_⟩
  gcongr
  apply sInf_le_sInf
  rintro n ⟨p, hp, rfl⟩
  exact ⟨p, hp, rfl⟩

/-- Cutting a string at a point `m` (any primitive recursive `op X m`, such as `take` or
`drop`) costs `O(log m)` bits of conditional complexity: the cut point is sent in binary. -/
private theorem condK_cut_le_add_logSlack (D : Map) (hD : isOptimalConditional D)
    (op : BitString → ℕ → BitString) (hop : Primrec₂ op) :
    ∃ c : ℕ, ∀ (X C : BitString) (m : ℕ),
      condK D (op X m) C ≤ condK D X C + (logSlack c m : ℕ∞) := by
  let D' : Map := fun pr =>
    (D (decodeSecond pr.1, pr.2)).map fun w => op w (bitsToNat (decodeFirst pr.1))
  have hD' : isDecompressor D' := by
    refine Partrec.map (hD.1.comp (Computable.pair
      (decodeSecond_computable.comp Computable.fst) Computable.snd)) ?_
    exact (hop.comp Primrec.snd (bitsToNat_primrec.comp
      (decodeFirst_primrec.comp (Primrec.fst.comp Primrec.fst)))).to_comp
  obtain ⟨c, hc⟩ := hD.2 D' hD'
  refine ⟨c + 2, fun X C m => ?_⟩
  rcases eq_or_ne (condK D X C) ⊤ with htop | htop
  · rw [htop, top_add]
    exact le_top
  obtain ⟨r, hr, hrlen⟩ := exists_program_of_KP_ne_top (M := D) (x := X) (y := C) htop
  have hrlen' : (programLength r : ℕ∞) = condK D X C := hrlen
  have hmem : op X m ∈ D' (pairCode (Nat.bits m) r, C) := by
    simp only [D', decodeFirst_pairCode, decodeSecond_pairCode, bitsToNat_bits]
    exact Part.mem_map _ hr
  have h1 : condK D' (op X m) C ≤ ((pairCode (Nat.bits m) r).length : ℕ∞) :=
    (condK_le_iff D' _ _ _).2 ⟨_, le_rfl, hmem⟩
  rw [← hrlen']
  calc condK D (op X m) C ≤ condK D' (op X m) C + (c : ℕ∞) := hc _ _
    _ ≤ ((pairCode (Nat.bits m) r).length : ℕ∞) + (c : ℕ∞) := by gcongr
    _ ≤ (programLength r : ℕ∞) + (logSlack (c + 2) m : ℕ∞) := by
      rw [length_pairCode]
      simp only [logSlack, programLength]
      norm_cast
      nlinarith [Nat.zero_le (Nat.bits m).length]

private theorem inNeighbors_twoConditionsRequest (A B C : BitString) (k l : ℕ) (v : Fin 6) :
    (twoConditionsRequest A B C k l).inNeighbors v =
      if v = 3 then {0, 1, 5} else if v = 4 then {2, 5} else if v = 5 then {0} else ∅ := by
  change (({(0, 5), (5, 3), (5, 4), (0, 3), (1, 3), (2, 4)} : Finset (Fin 6 × Fin 6)).filter
    fun e => e.2 = v).image Prod.fst = _
  revert v
  decide +kernel

private theorem outNeighbors_twoConditionsRequest (A B C : BitString) (k l : ℕ) (v : Fin 6) :
    (twoConditionsRequest A B C k l).outNeighbors v =
      if v = 0 then {3, 5} else if v = 1 then {3} else if v = 2 then {4}
      else if v = 5 then {3, 4} else ∅ := by
  change (({(0, 5), (5, 3), (5, 4), (0, 3), (1, 3), (2, 4)} : Finset (Fin 6 × Fin 6)).filter
    fun e => e.1 = v).image Prod.snd = _
  revert v
  decide +kernel

private theorem sort_015 : ({0, 1, 5} : Finset (Fin 6)).sort (· ≤ ·) = [0, 1, 5] := by
  simpa using (List.toFinset_sort (r := (· ≤ ·)) (l := [0, 1, 5]) (by simp)).2 (by simp)

private theorem sort_25 : ({2, 5} : Finset (Fin 6)).sort (· ≤ ·) = [2, 5] := by
  simpa using (List.toFinset_sort (r := (· ≤ ·)) (l := [2, 5]) (by simp)).2 (by simp)

private theorem sort_35 : ({3, 5} : Finset (Fin 6)).sort (· ≤ ·) = [3, 5] := by
  simpa using (List.toFinset_sort (r := (· ≤ ·)) (l := [3, 5]) (by simp)).2 (by simp)

private theorem sort_34 : ({3, 4} : Finset (Fin 6)).sort (· ≤ ·) = [3, 4] := by
  simpa using (List.toFinset_sort (r := (· ≤ ·)) (l := [3, 4]) (by simp)).2 (by simp)

/-- The transmission fulfilling `twoConditionsRequest`: the `l`-bit prefix of `X` goes through
the relay `5` to both output nodes, the remainder goes to `3` directly, and `A`, `B` are
forwarded to their output nodes. -/
private def twoConditionsTransmission (A B X : BitString) (l : ℕ) :
    Fin 6 × Fin 6 → BitString := fun e =>
  if e = (0, 5) ∨ e = (5, 3) ∨ e = (5, 4) then X.take l
  else if e = (0, 3) then X.drop l else if e = (1, 3) then A else if e = (2, 4) then B else []

private theorem twoConditionsRequest_fulfilled_nodes (D : Map) (k l : ℕ) (A B C X : BitString)
    (l' : ℕ) (t : Fin 6 × Fin 6 → BitString)
    (e05 : t (0, 5) = X.take l') (e53 : t (5, 3) = X.take l') (e54 : t (5, 4) = X.take l')
    (e03 : t (0, 3) = X.drop l') (e13 : t (1, 3) = A) (e24 : t (2, 4) = B)
    (ε : ℕ) (hnode0T : condK D (X.take l') (listCode [C]) ≤ (ε : ℕ∞))
    (hnode0D : condK D (X.drop l') (listCode [C]) ≤ (ε : ℕ∞))
    (hnode3 : condK D C (listCode [X.drop l', A, X.take l']) ≤ (ε : ℕ∞))
    (hnode4 : condK D C (listCode [B, X.take l']) ≤ (ε : ℕ∞))
    (hself : ∀ Y : BitString, condK D Y (listCode [Y]) ≤ (ε : ℕ∞))
    (v : Fin 6) (x : BitString)
    (hx : x ∈ InformationRequest.outgoing (twoConditionsRequest A B C k l) t v) :
    condK D x (listCode (InformationRequest.incoming (twoConditionsRequest A B C k l) t v)) ≤
      (ε : ℕ∞) := by
  rw [InformationRequest.outgoing, outNeighbors_twoConditionsRequest] at hx
  rw [InformationRequest.incoming, inNeighbors_twoConditionsRequest]
  rcases eq_or_ne v 0 with rfl | h0
  · simp only [Fin.isValue, ↓reduceIte, sort_35, List.map_cons, e03, e05, List.map_nil,
      twoConditionsRequest, ENat.natCast_sub, Fin.reduceEq, or_self, Option.toList_none,
      List.append_nil, List.mem_cons, List.not_mem_nil, or_false, Finset.sort_empty,
      Option.toList_some, List.nil_append, listCode_cons, listCode_nil] at hx ⊢
    rcases hx with rfl | rfl
    · exact hnode0D
    · exact hnode0T
  rcases eq_or_ne v 1 with rfl | h1
  · simp only [Fin.isValue, one_ne_zero, ↓reduceIte, Finset.sort_singleton, List.map_cons, e13,
      List.map_nil, twoConditionsRequest, ENat.natCast_sub, Fin.reduceEq, or_self,
      Option.toList_none,
      List.append_nil, List.mem_cons, List.not_mem_nil, or_false, Finset.sort_empty,
      Option.toList_some, List.nil_append, listCode_cons, listCode_nil] at hx ⊢
    rw [hx]; exact hself A
  rcases eq_or_ne v 2 with rfl | h2
  · simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte, Finset.sort_singleton, List.map_cons, e24,
      List.map_nil, twoConditionsRequest, ENat.natCast_sub, or_self, Option.toList_none,
      List.append_nil, List.mem_cons, List.not_mem_nil, or_false, Finset.sort_empty,
      Option.toList_some, List.nil_append, listCode_cons, listCode_nil] at hx ⊢
    rw [hx]; exact hself B
  rcases eq_or_ne v 3 with rfl | h3
  · simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte, Finset.sort_empty, List.map_nil,
      twoConditionsRequest, ENat.natCast_sub, or_false, Option.toList_some, List.nil_append,
      List.mem_cons, List.not_mem_nil, sort_015, List.map_cons, e03, e13, e53, Option.toList_none,
      List.append_nil, listCode_cons, listCode_nil] at hx ⊢
    rw [hx]; exact hnode3
  rcases eq_or_ne v 4 with rfl | h4
  · simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte, Finset.sort_empty, List.map_nil,
      twoConditionsRequest, ENat.natCast_sub, or_true, Option.toList_some, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false, sort_25, List.map_cons, e24, e54,
      Option.toList_none, List.append_nil, listCode_cons, listCode_nil] at hx ⊢
    rw [hx]; exact hnode4
  rcases eq_or_ne v 5 with rfl | h5
  · simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte, sort_34, List.map_cons, e53, e54,
      List.map_nil, twoConditionsRequest, ENat.natCast_sub, or_self, Option.toList_none,
      List.append_nil, List.mem_cons, List.not_mem_nil, or_false, Finset.sort_singleton, e05,
      listCode_cons, listCode_nil] at hx ⊢
    rw [hx]
    exact hself _
  exfalso
  clear hx
  omega

/-- Theorem 235 in the language of information transmission requests: under its hypotheses the
request `twoConditionsRequest` is fulfillable with logarithmic precision.

SUV Problem 324, p. 380. -/
theorem twoConditionsRequest_fulfilled (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ (n k l : ℕ) (A B C : BitString),
      plainK D A ≤ (n : ℕ∞) → plainK D B ≤ (n : ℕ∞) → plainK D C ≤ (n : ℕ∞) → 0 < l → l ≤ k →
      condK D C A ≤ (k : ℕ∞) → condK D C B ≤ (l : ℕ∞) →
      ∃ t : Fin 6 × Fin 6 → BitString,
        IsFulfilled D (twoConditionsRequest A B C k l) t (logSlack c n) := by
  obtain ⟨cP, hP⟩ := exists_twoConditionCode_prefix D hD
  obtain ⟨c₀, hc₀⟩ := condK_le_plainK D hD
  obtain ⟨cTake, hTake⟩ :=
    condK_cut_le_add_logSlack D hD (fun w m => w.take m) Primrec.list_take.swap
  obtain ⟨cDrop, hDrop⟩ :=
    condK_cut_le_add_logSlack D hD (fun w m => w.drop m) Primrec.list_drop.swap
  obtain ⟨cOne, hOne⟩ := condK_cond_comp_le D hD decodeFirst decodeFirst_computable
  obtain ⟨cSelf, hSelf⟩ := condK_comp D hD decodeFirst decodeFirst_computable
  obtain ⟨cThree, hThree⟩ := condK_cond_comp_le D hD (fun w =>
      pairCode (decodeFirst (decodeSecond w))
        (decodeFirst (decodeSecond (decodeSecond w)) ++ decodeFirst w))
    (pairCode_primrec.comp (decodeFirst_primrec.comp decodeSecond_primrec)
      (Primrec.list_append.comp
        (decodeFirst_primrec.comp (decodeSecond_primrec.comp decodeSecond_primrec))
        decodeFirst_primrec)).to_comp
  obtain ⟨cTwo, hTwo⟩ := condK_cond_comp_le D hD
    (fun w => pairCode (decodeFirst w) (decodeFirst (decodeSecond w)))
    (pairCode_primrec.comp decodeFirst_primrec
      (decodeFirst_primrec.comp decodeSecond_primrec)).to_comp
  set K := logSlack cTake (c₀ + 1) + logSlack cDrop (c₀ + 1) + cOne + cSelf + cThree + cTwo
    with hK
  refine ⟨cP + cTake + cDrop + K, fun n k l A B C hA hB hC hl hlk hCA hCB => ?_⟩
  set M := n + (c₀ + 1) with hM
  have hCM : ∀ Y, condK D C Y ≤ (M : ℕ∞) := fun Y => (hc₀ C Y).trans (by
    calc plainK D C + (c₀ : ℕ∞) ≤ (n : ℕ∞) + (c₀ : ℕ∞) := by gcongr
      _ ≤ (M : ℕ∞) := by rw [hM]; norm_cast; omega)
  have hmin : ∀ (Y : BitString) (j : ℕ), condK D C Y ≤ (j : ℕ∞) →
      condK D C Y ≤ ((min j M : ℕ) : ℕ∞) := by
    intro Y j hj
    rcases le_total j M with h | h
    · rw [min_eq_left h]; exact hj
    · rw [min_eq_right h]; exact hCM Y
  obtain ⟨X, hXlen, hXC, hXA, hXB⟩ := hP n (min k M) (min l M) A B C hA hB hC
    (by omega) (by omega) (hmin A k hCA) (hmin B l hCB)
  set l' := min l M with hl'
  set t := twoConditionsTransmission A B X l' with ht
  have e05 : t (0, 5) = X.take l' := by simp [ht, twoConditionsTransmission]
  have e53 : t (5, 3) = X.take l' := by simp [ht, twoConditionsTransmission]
  have e54 : t (5, 4) = X.take l' := by simp [ht, twoConditionsTransmission]
  have e03 : t (0, 3) = X.drop l' := by simp [ht, twoConditionsTransmission]
  have e13 : t (1, 3) = A := by simp [ht, twoConditionsTransmission]
  have e24 : t (2, 4) = B := by simp [ht, twoConditionsTransmission]
  refine ⟨t, ?_, ?_⟩
  · intro e he
    simp only [twoConditionsRequest, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [twoConditionsRequest, e05, e53, e54, e03, e13, e24] <;> norm_cast <;> omega
  · -- the arithmetic of the slacks
    set ε := logSlack (cP + cTake + cDrop + K) n with hε
    have hbits : ∀ c, logSlack c M ≤ logSlack c n + logSlack c (c₀ + 1) := fun c =>
      logSlack_add_le c n (c₀ + 1)
    have hslackT : logSlack cP n + logSlack cTake l' + cOne ≤ ε := by
      have h1 := hbits cTake
      have h2 : logSlack cTake l' ≤ logSlack cTake M :=
        logSlack_mono_right cTake (min_le_right l M)
      simp only [logSlack] at h1 h2 hK hε ⊢
      linarith [Nat.zero_le ((Nat.bits n).length * cDrop), Nat.zero_le ((Nat.bits n).length * K),
        Nat.zero_le ((Nat.bits n).length * cTake), Nat.zero_le ((Nat.bits (c₀ + 1)).length * cDrop)]
    have hslackD : logSlack cP n + logSlack cDrop l' + cOne ≤ ε := by
      have h1 := hbits cDrop
      have h2 : logSlack cDrop l' ≤ logSlack cDrop M :=
        logSlack_mono_right cDrop (min_le_right l M)
      simp only [logSlack] at h1 h2 hK hε ⊢
      linarith [Nat.zero_le ((Nat.bits n).length * cDrop), Nat.zero_le ((Nat.bits n).length * K),
        Nat.zero_le ((Nat.bits n).length * cTake), Nat.zero_le ((Nat.bits (c₀ + 1)).length * cTake)]
    have hslackS : cSelf ≤ ε := by
      simp only [logSlack] at hK hε ⊢
      linarith [Nat.zero_le ((Nat.bits n).length * cDrop), Nat.zero_le ((Nat.bits n).length * K),
        Nat.zero_le ((Nat.bits n).length * cTake), Nat.zero_le ((Nat.bits n).length * cP),
        Nat.zero_le ((Nat.bits (c₀ + 1)).length * cTake),
        Nat.zero_le ((Nat.bits (c₀ + 1)).length * cDrop)]
    have hslack3 : logSlack cP n + cThree ≤ ε := by
      simp only [logSlack] at hK hε ⊢
      linarith [Nat.zero_le ((Nat.bits n).length * cDrop), Nat.zero_le ((Nat.bits n).length * K),
        Nat.zero_le ((Nat.bits n).length * cTake),
        Nat.zero_le ((Nat.bits (c₀ + 1)).length * cTake),
        Nat.zero_le ((Nat.bits (c₀ + 1)).length * cDrop)]
    have hslack2 : logSlack cP n + cTwo ≤ ε := by
      simp only [logSlack] at hK hε ⊢
      linarith [Nat.zero_le ((Nat.bits n).length * cDrop), Nat.zero_le ((Nat.bits n).length * K),
        Nat.zero_le ((Nat.bits n).length * cTake),
        Nat.zero_le ((Nat.bits (c₀ + 1)).length * cTake),
        Nat.zero_le ((Nat.bits (c₀ + 1)).length * cDrop)]
    -- the individual bounds
    have hfirst : ∀ Y : BitString, decodeFirst (listCode [Y]) = Y := fun Y =>
      decodeFirst_pairCode Y []
    have hself : ∀ Y : BitString, condK D Y (listCode [Y]) ≤ (ε : ℕ∞) := fun Y => by
      have := hSelf (listCode [Y])
      rw [hfirst] at this
      exact this.trans (by exact_mod_cast hslackS)
    have hone : ∀ Y : BitString, condK D Y (listCode [C]) ≤ condK D Y C + (cOne : ℕ∞) :=
      fun Y => by
        have := hOne Y (listCode [C])
        rwa [hfirst] at this
    have hnode0T : condK D (X.take l') (listCode [C]) ≤ (ε : ℕ∞) := by
      calc condK D (X.take l') (listCode [C]) ≤ condK D (X.take l') C + (cOne : ℕ∞) := hone _
        _ ≤ condK D X C + (logSlack cTake l' : ℕ∞) + (cOne : ℕ∞) := by gcongr; exact hTake X C l'
        _ ≤ (logSlack cP n : ℕ∞) + (logSlack cTake l' : ℕ∞) + (cOne : ℕ∞) := by gcongr
        _ ≤ (ε : ℕ∞) := by exact_mod_cast hslackT
    have hnode0D : condK D (X.drop l') (listCode [C]) ≤ (ε : ℕ∞) := by
      calc condK D (X.drop l') (listCode [C]) ≤ condK D (X.drop l') C + (cOne : ℕ∞) := hone _
        _ ≤ condK D X C + (logSlack cDrop l' : ℕ∞) + (cOne : ℕ∞) := by gcongr; exact hDrop X C l'
        _ ≤ (logSlack cP n : ℕ∞) + (logSlack cDrop l' : ℕ∞) + (cOne : ℕ∞) := by gcongr
        _ ≤ (ε : ℕ∞) := by exact_mod_cast hslackD
    have hnode3 : condK D C (listCode [X.drop l', A, X.take l']) ≤ (ε : ℕ∞) := by
      calc condK D C (listCode [X.drop l', A, X.take l'])
          ≤ condK D C (pairCode A (X.take l' ++ X.drop l')) + (cThree : ℕ∞) := by
            simpa [listCode, decodeFirst_pairCode, decodeSecond_pairCode] using
              hThree C (listCode [X.drop l', A, X.take l'])
        _ = condK D C (pairCode A X) + (cThree : ℕ∞) := by rw [List.take_append_drop]
        _ ≤ (logSlack cP n : ℕ∞) + (cThree : ℕ∞) := by gcongr
        _ ≤ (ε : ℕ∞) := by exact_mod_cast hslack3
    have hnode4 : condK D C (listCode [B, X.take l']) ≤ (ε : ℕ∞) := by
      calc condK D C (listCode [B, X.take l'])
          ≤ condK D C (pairCode B (X.take l')) + (cTwo : ℕ∞) := by
            simpa [listCode, decodeFirst_pairCode, decodeSecond_pairCode] using
              hTwo C (listCode [B, X.take l'])
        _ ≤ (logSlack cP n : ℕ∞) + (cTwo : ℕ∞) := by gcongr
        _ ≤ (ε : ℕ∞) := by exact_mod_cast hslack2
    intro v x hx
    exact twoConditionsRequest_fulfilled_nodes D k l A B C X l' t e05 e53 e54 e03 e13 e24 ε
      hnode0T hnode0D hnode3 hnode4 hself v x hx

section ManyConditionsTable

open Finset

private theorem card_piFinset_ite {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    (T : Finset α) (B : Finset β) :
    (Fintype.piFinset fun x => if x ∈ T then B else (univ : Finset β)).card =
      B.card ^ T.card * Fintype.card β ^ (Fintype.card α - T.card) := by
  classical
  rw [Fintype.card_piFinset]
  simp only [apply_ite Finset.card]
  rw [prod_ite, prod_const, prod_const, filter_mem_eq_inter,
    univ_inter, card_univ]
  congr 2
  rw [filter_not, card_sdiff_of_subset (by simp), filter_mem_eq_inter, univ_inter, card_univ]

private theorem card_majorityColumns_le (N r W : ℕ) (U : Finset (Fin W)) :
    ((univ : Finset (Fin N → Fin W)).filter fun v =>
      r ≤ (univ.filter fun i => v i ∈ U).card).card ≤
      N.choose r * (U.card ^ r * W ^ (N - r)) := by
  classical
  have hsub : ((univ : Finset (Fin N → Fin W)).filter fun v =>
      r ≤ (univ.filter fun i => v i ∈ U).card) ⊆
      (powersetCard r (univ : Finset (Fin N))).biUnion fun I =>
        Fintype.piFinset fun i => if i ∈ I then U else univ := by
    intro v hv
    rw [mem_filter] at hv
    obtain ⟨I, hI, hIc⟩ := exists_subset_card_eq hv.2
    refine mem_biUnion.2 ⟨I, mem_powersetCard.2 ⟨subset_univ _, hIc⟩, ?_⟩
    rw [Fintype.mem_piFinset]
    intro i
    split_ifs with hi
    · exact (mem_filter.1 (hI hi)).2
    · exact mem_univ _
  refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
  have hI : ∀ I ∈ powersetCard r (univ : Finset (Fin N)),
      (Fintype.piFinset fun i => if i ∈ I then U else (univ : Finset (Fin W))).card =
        U.card ^ r * W ^ (N - r) := by
    intro I hI
    rw [card_piFinset_ite, (mem_powersetCard.1 hI).2, Fintype.card_fin, Fintype.card_fin]
  rw [sum_congr rfl hI, sum_const, card_powersetCard, card_univ, Fintype.card_fin, smul_eq_mul]

private theorem sum_Icc_lt_of_mul_two_pow_le (a : ℕ → ℕ) (Z L : ℕ) (hZ : 0 < Z)
    (ha : ∀ t, 1 ≤ t → a t * 2 ^ t ≤ Z) : ∑ t ∈ Icc 1 L, a t < Z := by
  have key : ∀ L, 2 ^ L * ∑ t ∈ Icc 1 L, a t + Z ≤ 2 ^ L * Z := by
    intro L
    induction L with
    | zero => simp
    | succ L ih =>
      rw [sum_Icc_succ_top (by omega), pow_succ]
      have := ha (L + 1) (by omega)
      rw [pow_succ] at this
      nlinarith
  have h1 := key L
  have h2 : 0 < 2 ^ L := by positivity
  by_contra h
  push Not at h
  nlinarith

private theorem choose_mul_columns_le (d m n t : ℕ) (hd : 0 < d) (ht : t * 2 ^ (d + 1) ≤ 2 ^ m) :
    (2 ^ m).choose t * ((2 ^ (n + 1)).choose t *
      ((d * (m + n + 2)).choose (m + n + 2) * (t ^ (m + n + 2) *
        (2 ^ m) ^ (d * (m + n + 2) - (m + n + 2)))) ^ t *
      ((2 ^ m) ^ (d * (m + n + 2))) ^ (2 ^ (n + 1) - t)) * 2 ^ t
      ≤ ((2 ^ m) ^ (d * (m + n + 2))) ^ 2 ^ (n + 1) := by
  set r := m + n + 2 with hr
  set N := d * r with hN
  set W := 2 ^ m with hW
  set M := 2 ^ (n + 1) with hM
  rcases lt_or_ge M t with htM | htM
  · rw [Nat.choose_eq_zero_of_lt htM]; simp
  have hrN : r ≤ N := by rw [hN]; exact Nat.le_mul_of_pos_left r hd
  set A := N.choose r * (t ^ r * W ^ (N - r)) with hA
  have hi : A * 2 ^ ((d + 1) * r) ≤ 2 ^ N * W ^ N := by
    have h1 : t ^ r * 2 ^ ((d + 1) * r) ≤ W ^ r := by
      rw [pow_mul, ← mul_pow]
      exact Nat.pow_le_pow_left ht r
    have h2 : W ^ r * W ^ (N - r) = W ^ N := by rw [← pow_add, Nat.add_sub_cancel' hrN]
    calc A * 2 ^ ((d + 1) * r) = N.choose r * (t ^ r * 2 ^ ((d + 1) * r) * W ^ (N - r)) := by
          rw [hA]; ring
      _ ≤ 2 ^ N * (W ^ r * W ^ (N - r)) := by
          gcongr
          exact Nat.choose_le_two_pow N r
      _ = 2 ^ N * W ^ N := by rw [h2]
  have hii : A ^ t * 2 ^ ((d + 1) * r * t) ≤ (2 ^ N * W ^ N) ^ t := by
    rw [pow_mul, ← mul_pow]
    exact Nat.pow_le_pow_left hi t
  have hWM : W * M * 2 * 2 ^ N = 2 ^ ((d + 1) * r) := by
    rw [hW, hM, hN, hr, ← pow_add, ← pow_succ, ← pow_add]
    congr 1
    ring
  have hpos : 0 < 2 ^ ((d + 1) * r * t) := by positivity
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc W.choose t * (M.choose t * A ^ t * (W ^ N) ^ (M - t)) * 2 ^ t * 2 ^ ((d + 1) * r * t)
      ≤ W ^ t * (M ^ t * A ^ t * (W ^ N) ^ (M - t)) * 2 ^ t * 2 ^ ((d + 1) * r * t) := by
        gcongr
        · exact Nat.choose_le_pow W t
        · exact Nat.choose_le_pow M t
    _ = (W * M * 2) ^ t * (A ^ t * 2 ^ ((d + 1) * r * t)) * (W ^ N) ^ (M - t) := by ring_nf
    _ ≤ (W * M * 2) ^ t * (2 ^ N * W ^ N) ^ t * (W ^ N) ^ (M - t) := by gcongr
    _ = (W * M * 2 * 2 ^ N) ^ t * ((W ^ N) ^ t * (W ^ N) ^ (M - t)) := by ring
    _ = (W ^ N) ^ M * 2 ^ ((d + 1) * r * t) := by
        rw [← pow_add (W ^ N) t (M - t), Nat.add_sub_cancel' htM, hWM, ← pow_mul]; ring

private theorem exists_goodColumns (d m n : ℕ) (hd : 0 < d) :
    ∃ f : Fin (2 ^ (n + 1)) → Fin (d * (m + n + 2)) → Fin (2 ^ m),
      ∀ U : Finset (Fin (2 ^ m)), 0 < U.card → U.card * 2 ^ (d + 1) ≤ 2 ^ m →
        (univ.filter fun x => m + n + 2 ≤ (univ.filter fun i => f x i ∈ U).card).card <
          U.card := by
  classical
  set r := m + n + 2 with hr
  set N := d * r with hN
  set W := 2 ^ m with hW
  set M := 2 ^ (n + 1) with hM
  set B : Finset (Fin W) → Finset (Fin N → Fin W) := fun U =>
    univ.filter fun v => r ≤ (univ.filter fun i => v i ∈ U).card with hB
  set Us := (univ : Finset (Finset (Fin W))).filter
    fun U => 0 < U.card ∧ U.card * 2 ^ (d + 1) ≤ W with hUs
  set g : ℕ → ℕ := fun t =>
    M.choose t * ((N.choose r * (t ^ r * W ^ (N - r))) ^ t * (W ^ N) ^ (M - t)) with hg
  by_contra hcon
  push Not at hcon
  have hcover : (univ : Finset (Fin M → Fin N → Fin W)) ⊆
      Us.biUnion fun U => (powersetCard U.card (univ : Finset (Fin M))).biUnion fun T =>
        Fintype.piFinset fun x => if x ∈ T then B U else univ := by
    intro f _
    obtain ⟨U, hU0, hUW, hle⟩ := hcon f
    obtain ⟨T, hT, hTc⟩ := exists_subset_card_eq hle
    refine mem_biUnion.2 ⟨U, mem_filter.2 ⟨mem_univ _, hU0, hUW⟩, mem_biUnion.2
      ⟨T, mem_powersetCard.2 ⟨subset_univ _, hTc⟩, ?_⟩⟩
    rw [Fintype.mem_piFinset]
    intro x
    split_ifs with hx
    · exact mem_filter.2 ⟨mem_univ _, (mem_filter.1 (hT hx)).2⟩
    · exact mem_univ _
  have hcard := card_le_card hcover
  rw [card_univ, Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
    Fintype.card_fin] at hcard
  have hU : ∀ U ∈ Us, ((powersetCard U.card (univ : Finset (Fin M))).biUnion fun T =>
      Fintype.piFinset fun x => if x ∈ T then B U else univ).card ≤ g U.card := by
    intro U _
    refine card_biUnion_le.trans ?_
    have hT : ∀ T ∈ powersetCard U.card (univ : Finset (Fin M)),
        (Fintype.piFinset fun x => if x ∈ T then B U else univ).card ≤
          (N.choose r * (U.card ^ r * W ^ (N - r))) ^ U.card * (W ^ N) ^ (M - U.card) := by
      intro T hT
      rw [card_piFinset_ite, (mem_powersetCard.1 hT).2, Fintype.card_fun, Fintype.card_fin,
        Fintype.card_fin, Fintype.card_fin]
      gcongr
      exact card_majorityColumns_le N r W U
    refine (sum_le_sum hT).trans ?_
    rw [sum_const, card_powersetCard, card_univ, Fintype.card_fin, smul_eq_mul]
  have hsum : (Us.biUnion fun U => (powersetCard U.card (univ : Finset (Fin M))).biUnion
      fun T => Fintype.piFinset fun x => if x ∈ T then B U else univ).card ≤
      ∑ t ∈ Icc 1 W, (if t * 2 ^ (d + 1) ≤ W then W.choose t * g t else 0) := by
    refine card_biUnion_le.trans ((sum_le_sum hU).trans ?_)
    rw [← sum_fiberwise_of_maps_to (s := Us) (t := Icc 1 W) (g := Finset.card)
      (fun U hU => by
        have h := (mem_filter.1 hU).2
        refine mem_Icc.2 ⟨h.1, ?_⟩
        have := card_le_univ U
        rwa [Fintype.card_fin] at this)]
    refine sum_le_sum fun t _ => ?_
    have hfib : ∑ U ∈ Us with U.card = t, g U.card =
        (Us.filter fun U => U.card = t).card * g t := by
      rw [sum_congr rfl fun U hU => by rw [(mem_filter.1 hU).2], sum_const, smul_eq_mul]
    rw [hfib]
    split_ifs with ht
    · gcongr
      refine (card_le_card fun U hU => ?_).trans_eq (by rw [card_powersetCard, card_univ,
        Fintype.card_fin])
      exact mem_powersetCard.2 ⟨subset_univ _, (mem_filter.1 hU).2⟩
    · rw [card_eq_zero.2, zero_mul]
      refine filter_eq_empty_iff.2 fun U hU hUt => ht ?_
      rw [← hUt]
      exact ((mem_filter.1 hU).2).2
  have hlt : ∑ t ∈ Icc 1 W, (if t * 2 ^ (d + 1) ≤ W then W.choose t * g t else 0) <
      (W ^ N) ^ M := by
    refine sum_Icc_lt_of_mul_two_pow_le _ _ _ (by positivity) fun t _ => ?_
    split_ifs with ht
    · have hmain := choose_mul_columns_le d m n t hd ht
      rw [← hr, ← hN, ← hW, ← hM] at hmain
      refine le_trans (le_of_eq ?_) hmain
      simp only [hg]
      ring
    · simp
  omega

/-- The entry `χ_i(j)` of a hash table stored as a list of columns (`0` if absent). -/
private def mcTabEntry (tab : List (List ℕ)) (i j : ℕ) : ℕ := (tab.getD j []).getD i 0

/-- All sublists of a list, enumerated by a primitive recursive fold. -/
private def mcSublists (l : List ℕ) : List (List ℕ) :=
  l.foldr (fun a acc => acc ++ acc.map (List.cons a)) [[]]

private theorem mem_mcSublists {l U : List ℕ} : U ∈ mcSublists l ↔ U.Sublist l := by
  induction l generalizing U with
  | nil => simp [mcSublists]
  | cons a l ih =>
    simp only [mcSublists, List.foldr_cons] at ih ⊢
    rw [List.mem_append, List.mem_map, List.sublist_cons_iff, ih]
    constructor
    · rintro (h | ⟨V, hV, rfl⟩)
      · exact Or.inl h
      · exact Or.inr ⟨V, rfl, ih.1 hV⟩
    · rintro (h | ⟨V, rfl, hV⟩)
      · exact Or.inl h
      · exact Or.inr ⟨V, ih.2 hV, rfl⟩

/-- The number of columns `j < M` of which at least `r` of the `N` entries (reduced modulo
`W`) fall into the set `U`. -/
private def mcBadCount (M N r W : ℕ) (tab : List (List ℕ)) (U : List ℕ) : ℕ :=
  (List.range M).countP fun j =>
    decide (r ≤ (List.range N).countP fun i => U.any fun u => decide (u = mcTabEntry tab i j % W))

/-- A hash table is good when every nonempty set `U` of at most `2^m / 2^(d+1)` hash values
has fewer bad columns than elements (the finite, decidable form of the expansion property). -/
private def mcTabGood (d n m : ℕ) (tab : List (List ℕ)) : Bool :=
  (mcSublists (List.range (2 ^ m))).all fun U =>
    decide (U.length = 0) || decide (2 ^ m < U.length * 2 ^ (d + 1)) ||
      decide (mcBadCount (2 ^ (n + 1)) (d * (m + n + 2)) (m + n + 2) (2 ^ m) tab U < U.length)

private theorem mcTabGood_spec {d n m : ℕ} {tab : List (List ℕ)} (h : mcTabGood d n m tab = true)
    {U : List ℕ} (hU : U.Sublist (List.range (2 ^ m))) (hne : U ≠ [])
    (hsize : U.length * 2 ^ (d + 1) ≤ 2 ^ m) :
    mcBadCount (2 ^ (n + 1)) (d * (m + n + 2)) (m + n + 2) (2 ^ m) tab U < U.length := by
  have := List.all_eq_true.1 h U (mem_mcSublists.2 hU)
  simp only [Bool.or_eq_true, decide_eq_true_eq] at this
  rcases this with (h1 | h1) | h1
  · exact absurd (List.length_eq_zero_iff.1 h1) hne
  · omega
  · exact h1

private theorem countP_range_eq_card (M : ℕ) (p : ℕ → Bool) :
    (List.range M).countP p = (univ.filter fun x : Fin M => p x = true).card := by
  induction M generalizing p with
  | zero => simp
  | succ M ih =>
    rw [List.range_succ_eq_map, List.countP_cons, List.countP_map, Fin.card_filter_univ_succ']
    rw [ih (p ∘ Nat.succ)]
    simp only [Function.comp_apply, Fin.val_zero, Fin.val_succ]
    split_ifs with h
    · simp only [h, ite_eq_left, Nat.succ_eq_add_one, add_comm]
    · have hp : p 0 = false := Bool.eq_false_of_ne_true h
      simp only [hp, Bool.false_eq_true, ite_false, Nat.succ_eq_add_one, add_comm]

private theorem exists_mcTabGood (d n m : ℕ) : ∃ tab, mcTabGood d n m tab = true := by
  classical
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · refine ⟨[], List.all_eq_true.2 fun U _ => ?_⟩
    rcases U with _ | ⟨u, U⟩
    · simp
    · simp [mcBadCount]
  obtain ⟨f, hf⟩ := exists_goodColumns d m n hd
  refine ⟨List.ofFn fun x : Fin (2 ^ (n + 1)) =>
      List.ofFn fun i : Fin (d * (m + n + 2)) => (f x i : ℕ),
    List.all_eq_true.2 fun U hU => ?_⟩
  have hsub := mem_mcSublists.1 hU
  have hnd : U.Nodup := hsub.nodup List.nodup_range
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  by_cases hne : U = []
  · exact Or.inl (Or.inl (by simp [hne]))
  by_cases hsz : 2 ^ m < U.length * 2 ^ (d + 1)
  · exact Or.inl (Or.inr hsz)
  right
  set U' : Finset (Fin (2 ^ m)) := univ.filter fun u => (u : ℕ) ∈ U with hU'
  have hcard : U'.card = U.length := by
    have hmap : U'.map Fin.valEmbedding = U.toFinset := by
      ext v
      simp only [mem_map, hU', mem_filter, mem_univ, true_and, Fin.valEmbedding_apply,
        List.mem_toFinset]
      constructor
      · rintro ⟨u, hu, rfl⟩; exact hu
      · intro hv
        exact ⟨⟨v, List.mem_range.1 (hsub.subset hv)⟩, hv, rfl⟩
    rw [← card_map Fin.valEmbedding, hmap, List.toFinset_card_of_nodup hnd]
  have hentry : ∀ (x : Fin (2 ^ (n + 1))) (i : Fin (d * (m + n + 2))),
      mcTabEntry (List.ofFn fun x : Fin (2 ^ (n + 1)) =>
        List.ofFn fun i : Fin (d * (m + n + 2)) => (f x i : ℕ)) i x =
        f x i := by
    intro x i
    simp [mcTabEntry]
  have hbad : mcBadCount (2 ^ (n + 1)) (d * (m + n + 2)) (m + n + 2) (2 ^ m)
      (List.ofFn fun x : Fin (2 ^ (n + 1)) =>
        List.ofFn fun i : Fin (d * (m + n + 2)) => (f x i : ℕ)) U =
      (univ.filter fun x => m + n + 2 ≤ (univ.filter fun i => f x i ∈ U').card).card := by
    rw [mcBadCount, countP_range_eq_card]
    refine congrArg Finset.card (filter_congr fun x _ => ?_)
    rw [countP_range_eq_card, decide_eq_true_iff]
    have : (univ.filter fun i : Fin (d * (m + n + 2)) => (U.any fun u =>
        decide (u = mcTabEntry (List.ofFn fun x : Fin (2 ^ (n + 1)) =>
          List.ofFn fun i : Fin (d * (m + n + 2)) => (f x i : ℕ))
          i x % 2 ^ m)) = true) = univ.filter fun i => f x i ∈ U' := by
      refine filter_congr fun i _ => ?_
      rw [hentry, Nat.mod_eq_of_lt (f x i).isLt]
      simp [hU']
    rw [this]
  rw [hbad, ← hcard]
  exact hf U' (by rw [hcard]; exact List.length_pos_of_ne_nil hne) (by rw [hcard]; omega)

private theorem mc_nat_pow_primrec₂ : Primrec₂ (fun (a b : ℕ) => a ^ b) :=
  Primrec.nat_iff.mpr Nat.Primrec.pow

private theorem mcTabEntry_primrec :
    Primrec (fun p : List (List ℕ) × ℕ × ℕ => mcTabEntry p.1 p.2.1 p.2.2) :=
  (Primrec.list_getD 0).comp ((Primrec.list_getD []).comp Primrec.fst
    (Primrec.snd.comp Primrec.snd)) (Primrec.fst.comp Primrec.snd)

private theorem mcSublists_primrec : Primrec mcSublists := by
  unfold mcSublists
  have hstep : Primrec₂ (fun (_ : List ℕ) (q : ℕ × List (List ℕ)) =>
      q.2 ++ q.2.map (List.cons q.1)) :=
    (Primrec.list_append.comp (Primrec.snd.comp Primrec.snd)
      (Primrec.list_map (Primrec.snd.comp Primrec.snd)
        (Primrec.list_cons.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
          Primrec.snd).to₂)).to₂
  exact Primrec.list_foldr Primrec.id (Primrec.const [[]]) hstep

local notation "MCArg" => (ℕ × ℕ × ℕ × ℕ) × List (List ℕ) × List ℕ

private theorem mcBadCount_primrec :
    Primrec (fun p : MCArg => mcBadCount p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2 p.2.1 p.2.2) := by
  have h1 := (Primrec.fst (α := List (List ℕ)) (β := List ℕ)).comp
    ((Primrec.snd (α := ℕ × ℕ × ℕ × ℕ) (β := List (List ℕ) × List ℕ)).comp
    ((Primrec.fst (α := MCArg) (β := ℕ)).comp
    ((Primrec.fst (α := MCArg × ℕ) (β := ℕ)).comp (Primrec.fst (α := (MCArg × ℕ) × ℕ) (β := ℕ)))))
  have h2 := (Primrec.snd (α := MCArg × ℕ) (β := ℕ)).comp
    (Primrec.fst (α := (MCArg × ℕ) × ℕ) (β := ℕ))
  have h3 := (Primrec.snd (α := MCArg) (β := ℕ)).comp
    ((Primrec.fst (α := MCArg × ℕ) (β := ℕ)).comp (Primrec.fst (α := (MCArg × ℕ) × ℕ) (β := ℕ)))
  have hW : Primrec (fun a : MCArg => a.1.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have h4 := hW.comp ((Primrec.fst (α := MCArg) (β := ℕ)).comp
    ((Primrec.fst (α := MCArg × ℕ) (β := ℕ)).comp (Primrec.fst (α := (MCArg × ℕ) × ℕ) (β := ℕ))))
  have h5 := mcTabEntry_primrec.comp (h1.pair (h2.pair h3))
  have hent := (PrimrecRel.decide (Primrec.eq (α := ℕ))).comp
    (Primrec.snd (α := (MCArg × ℕ) × ℕ) (β := ℕ)) (Primrec.nat_mod.comp h5 h4)
  have hU : Primrec (fun r : (MCArg × ℕ) × ℕ => r.1.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have hent' : Primrec₂ (fun (r : (MCArg × ℕ) × ℕ) (u : ℕ) =>
      decide (u = mcTabEntry r.1.1.2.1 r.2 r.1.2 % r.1.1.1.2.2.2)) := hent
  have hany := list_any_primrec hU hent'
  have hN : Primrec (fun q : MCArg × ℕ => List.range q.1.1.2.1) :=
    Primrec.list_range.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
  have hany' : Primrec₂ (fun (q : MCArg × ℕ) (i : ℕ) =>
      q.1.2.2.any fun u => decide (u = mcTabEntry q.1.2.1 i q.2 % q.1.1.2.2.2)) := hany
  have hcnt := list_countP_primrec hN hany'
  have hr : Primrec (fun q : MCArg × ℕ => q.1.1.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
  have hinner := (PrimrecRel.decide Primrec.nat_le).comp hr hcnt
  have hM : Primrec (fun a : MCArg => List.range a.1.1) :=
    Primrec.list_range.comp (Primrec.fst.comp Primrec.fst)
  have hinner' : Primrec₂ (fun (a : MCArg) (j : ℕ) =>
      decide (a.1.2.2.1 ≤ (List.range a.1.2.1).countP fun i =>
        a.2.2.any fun u => decide (u = mcTabEntry a.2.1 i j % a.1.2.2.2))) := hinner
  have := list_countP_primrec hM hinner'
  exact this

private theorem mcTabGood_primrec (d : ℕ) :
    Primrec (fun a : (ℕ × ℕ) × List (List ℕ) => mcTabGood d a.1.1 a.1.2 a.2) := by
  have hpow := mc_nat_pow_primrec₂
  -- components as functions of `q = (a, U)`
  have hn : Primrec (fun q : ((ℕ × ℕ) × List (List ℕ)) × List ℕ => q.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hm : Primrec (fun q : ((ℕ × ℕ) × List (List ℕ)) × List ℕ => q.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have htab : Primrec (fun q : ((ℕ × ℕ) × List (List ℕ)) × List ℕ => q.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hU : Primrec (fun q : ((ℕ × ℕ) × List (List ℕ)) × List ℕ => q.2) := Primrec.snd
  have hW := hpow.comp (Primrec.const 2) hm
  have hM := hpow.comp (Primrec.const 2) (Primrec.succ.comp hn)
  have hr := Primrec.nat_add.comp (Primrec.nat_add.comp hm hn) (Primrec.const 2)
  have hN := Primrec.nat_mul.comp (Primrec.const d) hr
  have hlen := Primrec.list_length.comp hU
  have hbad := mcBadCount_primrec.comp ((hM.pair (hN.pair (hr.pair hW))).pair (htab.pair hU))
  have h1 := (PrimrecRel.decide (Primrec.eq (α := ℕ))).comp hlen (Primrec.const 0)
  have h2 := (PrimrecRel.decide Primrec.nat_lt).comp hW
    (Primrec.nat_mul.comp hlen (hpow.comp (Primrec.const 2) (Primrec.const (d + 1))))
  have h3 := (PrimrecRel.decide Primrec.nat_lt).comp hbad hlen
  have hor := Primrec.or.comp (Primrec.or.comp h1 h2) h3
  have hor' : Primrec₂ (fun (a : (ℕ × ℕ) × List (List ℕ)) (U : List ℕ) =>
      decide (U.length = 0) || decide (2 ^ a.1.2 < U.length * 2 ^ (d + 1)) ||
        decide (mcBadCount (2 ^ (a.1.1 + 1)) (d * (a.1.2 + a.1.1 + 2)) (a.1.2 + a.1.1 + 2)
          (2 ^ a.1.2) a.2 U < U.length)) := hor
  have hsub := mcSublists_primrec.comp (Primrec.list_range.comp
    (hpow.comp (Primrec.const 2) (Primrec.snd.comp (Primrec.fst (α := ℕ × ℕ)
      (β := List (List ℕ))))))
  have := list_all_primrec hsub hor'
  exact this

private theorem exists_mcTabGood_code (d n m : ℕ) :
    ∃ e, mcTabGood d n m ((Encodable.decode (α := List (List ℕ)) e).getD []) = true := by
  obtain ⟨tab, h⟩ := exists_mcTabGood d n m
  exact ⟨Encodable.encode tab, by rw [Encodable.encodek]; exact h⟩

/-- The first good hash table in a computable enumeration of all tables. -/
private def mcTable (d n m : ℕ) : List (List ℕ) :=
  (Encodable.decode (α := List (List ℕ)) (Nat.find (exists_mcTabGood_code d n m))).getD []

private theorem mcTable_good (d n m : ℕ) : mcTabGood d n m (mcTable d n m) = true :=
  Nat.find_spec (exists_mcTabGood_code d n m)

private theorem mcTable_computable (d : ℕ) : Computable (fun p : ℕ × ℕ => mcTable d p.1 p.2) := by
  have hdec := (Primrec.option_getD (α := List (List ℕ))).comp
    (Primrec.decode (α := List (List ℕ))) (Primrec.const (α := ℕ) ([] : List (List ℕ)))
  have h1 := (mcTabGood_primrec d).comp ((Primrec.fst (α := ℕ × ℕ) (β := ℕ)).pair
      (hdec.comp (Primrec.snd (α := ℕ × ℕ) (β := ℕ))))
  have hP : Computable (fun q : (ℕ × ℕ) × ℕ =>
      decide (mcTabGood d q.1.1 q.1.2 ((Encodable.decode (α := List (List ℕ)) q.2).getD [])
        = true)) := h1.to_comp.of_eq fun _ => Bool.decide_eq_true.symm
  have hex : ∀ p : ℕ × ℕ, ∃ e, mcTabGood d p.1 p.2
      ((Encodable.decode (α := List (List ℕ)) e).getD []) = true :=
    fun p => exists_mcTabGood_code d p.1 p.2
  have hfind := Computable.natFind (α := ℕ × ℕ)
    (P := fun p e => mcTabGood d p.1 p.2 ((Encodable.decode (α := List (List ℕ)) e).getD [])
      = true) hP hex
  have h2 := hdec.to_comp.comp hfind
  unfold mcTable
  exact h2

end ManyConditionsTable

section ManyConditionsCode

open Nat.Partrec (Code)

/-- The concatenation of the stage lists `L y 0, …, L y t`: a prefix-monotone enumeration. -/
private def mcCum (L : BitString → ℕ → List BitString) (y : BitString) (t : ℕ) : List BitString :=
  Nat.rec (L y 0) (fun s acc => acc ++ L y (s + 1)) t

private theorem mcCum_succ (L : BitString → ℕ → List BitString) (y : BitString) (t : ℕ) :
    mcCum L y (t + 1) = mcCum L y t ++ L y (t + 1) := rfl

private theorem mem_mcCum_of_mem (L : BitString → ℕ → List BitString) (y x : BitString) (t : ℕ)
    (h : x ∈ L y t) : x ∈ mcCum L y t := by
  cases t with
  | zero => exact h
  | succ t => rw [mcCum_succ]; exact List.mem_append_right _ h

private theorem exists_of_mem_mcCum (L : BitString → ℕ → List BitString) (y x : BitString) (t : ℕ)
    (h : x ∈ mcCum L y t) : ∃ t', x ∈ L y t' := by
  induction t with
  | zero => exact ⟨0, h⟩
  | succ t ih =>
    rw [mcCum_succ, List.mem_append] at h
    rcases h with h | h
    · exact ih h
    · exact ⟨_, h⟩

private theorem mcCum_computable (L : BitString → ℕ → List BitString)
    (hL : Computable (fun p : BitString × ℕ => L p.1 p.2)) :
    Computable (fun p : BitString × ℕ => mcCum L p.1 p.2) := by
  have hg : Computable (fun p : BitString × ℕ => L p.1 0) :=
    hL.comp (Computable.pair Computable.fst (Computable.const 0))
  have hh : Computable₂ (fun (p : BitString × ℕ) (q : ℕ × List BitString) =>
      q.2 ++ L p.1 (q.1 + 1)) :=
    Computable.list_append.comp (Computable.snd.comp Computable.snd)
      (hL.comp (Computable.pair (Computable.fst.comp Computable.fst)
        (Computable.succ.comp (Computable.fst.comp Computable.snd))))
  exact Computable.nat_rec Computable.snd hg hh

private theorem condK_le_of_mem_stageList (D : Map) (hD : isOptimalConditional D)
    (L : BitString → ℕ → List BitString)
    (hL : Computable (fun p : BitString × ℕ => L p.1 p.2)) :
    ∃ c₀ : ℕ, ∀ (y x : BitString) (t B : ℕ), x ∈ L y t →
      (∀ s : Finset BitString, (∀ z ∈ s, ∃ t', z ∈ L y t') → s.card ≤ B) →
      condK D x y ≤ (((Nat.bits B).length + c₀ : ℕ) : ℕ∞) := by
  classical
  let enum := mcCum L
  have hmono : ∀ y t, enum y t <+: enum y (t + 1) := fun y t => by
    change mcCum L y t <+: mcCum L y (t + 1)
    rw [mcCum_succ]
    exact List.prefix_append _ _
  let D' : Map := fun p => StagedEnumeration.condFFixedLength enum p.2 p.1
  have hD' : isDecompressor D' :=
    StagedEnumeration.condFFixedLength_partrec enum (mcCum_computable L hL)
  obtain ⟨c₁, hc₁⟩ := hD.2 D' hD'
  refine ⟨c₁, fun y x t B hx hB => ?_⟩
  have hxe : x ∈ StagedEnumeration.condDistinctAt enum y t := by
    unfold StagedEnumeration.condDistinctAt
    exact mem_eraseDups_bitString.2 (mem_mcCum_of_mem L y x t hx)
  obtain ⟨j, hj, hjx⟩ := List.getElem_of_mem hxe
  have hlen : (StagedEnumeration.condDistinctAt enum y t).length ≤ B := by
    have hnd : (StagedEnumeration.condDistinctAt enum y t).Nodup :=
      nodup_eraseDups_bitString _
    rw [← List.toFinset_card_of_nodup hnd]
    refine hB _ fun z hz => ?_
    rw [List.mem_toFinset] at hz
    unfold StagedEnumeration.condDistinctAt at hz
    exact exists_of_mem_mcCum L y z t (mem_eraseDups_bitString.1 hz)
  have hj' : bitsToNat (Nat.bits j) < (StagedEnumeration.condDistinctAt enum y t).length := by
    rw [bitsToNat_bits]; exact hj
  have hev := StagedEnumeration.condFFixedLength_eval enum hmono y (Nat.bits j) t hj'
  rw [bitsToNat_bits, List.getD_eq_getElem _ _ hj, hjx] at hev
  have h1 : condK D' x y ≤ ((Nat.bits j).length : ℕ∞) :=
    (condK_le_iff D' _ _ _).2 ⟨_, le_rfl, hev⟩
  have h2 : (Nat.bits j).length ≤ (Nat.bits B).length := length_bits_mono (by omega)
  calc condK D x y ≤ condK D' x y + (c₁ : ℕ∞) := hc₁ _ _
    _ ≤ ((Nat.bits j).length : ℕ∞) + (c₁ : ℕ∞) := by gcongr
    _ ≤ (((Nat.bits B).length + c₁ : ℕ) : ℕ∞) := by
      push_cast; gcongr

/-- The position of `x` in the stage-`t` enumeration of the strings of complexity `≤ n`. -/
private def mcIdx (c : Code) (n t : ℕ) (x : BitString) : ℕ :=
  (boundedOutputStage c n t).findIdx fun z => decide (z = x)

/-- The `i`-th fingerprint of `x` at stage `t`: the table entry of its index, modulo `2^m`. -/
private def mcHash (c : Code) (tab : List (List ℕ)) (n m t i : ℕ) (x : BitString) : ℕ :=
  mcTabEntry tab i (mcIdx c n t x) % 2 ^ m

/-- The stage-`t` approximation of `S_A`: outputs of programs of length `≤ k` given `A` that
already appear among the strings of complexity `≤ n`. -/
private def mcS (c : Code) (A : BitString) (k n t : ℕ) : List BitString :=
  (conditionalOutputSnapshot c A k t).filter fun x => decide (x ∈ boundedOutputStage c n t)

/-- The number of pairs `(i, x)` with `x ∈ S_A` (at stage `t`) whose fingerprint is `u`. -/
private def mcCount (c : Code) (d : ℕ) (tab : List (List ℕ)) (n m k t : ℕ) (A : BitString) (u : ℕ) :
    ℕ :=
  ((mcS c A k n t).eraseDups.flatMap fun x =>
    (List.range (d * (m + n + 2))).map fun i => mcHash c tab n m t i x).countP
      fun h => decide (h = u)

/-- A fingerprint value is rich at stage `t` when more than `N · 2^(d+2+e)` pairs hit it. -/
private def mcRich (c : Code) (d : ℕ) (tab : List (List ℕ)) (n m k e t : ℕ) (A : BitString)
    (u : ℕ) :
    Bool :=
  decide (d * (m + n + 2) * 2 ^ (d + 2 + e) < mcCount c d tab n m k t A u)

/-- The bad strings at stage `t`: those at least `r = m + n + 2` of whose `N` fingerprints are
rich. -/
private def mcBad (c : Code) (d : ℕ) (tab : List (List ℕ)) (n m k e t : ℕ) (A : BitString) :
    List BitString :=
  (boundedOutputStage c n t).filter fun x =>
    decide (m + n + 2 ≤ (List.range (d * (m + n + 2))).countP fun i =>
      mcRich c d tab n m k e t A (mcHash c tab n m t i x))

/-- The candidates of the decoder knowing `A`: strings of `S_A` with fingerprint `v` under the
`i`-th hash. -/
private def mcMatch (c : Code) (tab : List (List ℕ)) (n m k t : ℕ) (A : BitString) (i v : ℕ) :
    List BitString :=
  (mcS c A k n t).filter fun x => decide (mcHash c tab n m t i x = v)

/-- The encoder's stage list: the fingerprint of `C`, once `C` has been enumerated. -/
private def mcEnc (c : Code) (tab : List (List ℕ)) (n m t i : ℕ) (C : BitString) : List BitString :=
  ((boundedOutputStage c n t).filter fun x => decide (x = C)).map fun x =>
    Nat.bits (mcHash c tab n m t i x)

local notation "MZ" => (List (List ℕ) × ℕ × ℕ × ℕ × ℕ × ℕ) × BitString × ℕ

section Primrec

variable (c : Code) (d : ℕ)

private theorem mz_tab : Primrec (fun z : MZ => z.1.1) := Primrec.fst.comp Primrec.fst
private theorem mz_n : Primrec (fun z : MZ => z.1.2.1) :=
  Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
private theorem mz_m : Primrec (fun z : MZ => z.1.2.2.1) :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
private theorem mz_k : Primrec (fun z : MZ => z.1.2.2.2.1) :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
private theorem mz_e : Primrec (fun z : MZ => z.1.2.2.2.2.1) :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
    (Primrec.snd.comp Primrec.fst))))
private theorem mz_i : Primrec (fun z : MZ => z.1.2.2.2.2.2) :=
  Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
    (Primrec.snd.comp Primrec.fst))))
private theorem mz_A : Primrec (fun z : MZ => z.2.1) := Primrec.fst.comp Primrec.snd
private theorem mz_t : Primrec (fun z : MZ => z.2.2) := Primrec.snd.comp Primrec.snd

private theorem mz_omega_primrec : Primrec (fun z : MZ => boundedOutputStage c z.1.2.1 z.2.2) := by
  have := (boundedOutputStage_primrec c).comp (mz_n.pair mz_t)
  exact this

private theorem mcHash_primrec : Primrec (fun a : (MZ × BitString) × ℕ =>
    mcHash c a.1.1.1.1 a.1.1.1.2.1 a.1.1.1.2.2.1 a.1.1.2.2 a.2 a.1.2) := by
  have hq : Primrec (fun a : (MZ × BitString) × ℕ => a.1.1) := Primrec.fst.comp Primrec.fst
  have hx : Primrec (fun a : (MZ × BitString) × ℕ => a.1.2) := Primrec.snd.comp Primrec.fst
  have hi : Primrec (fun a : (MZ × BitString) × ℕ => a.2) := Primrec.snd
  have hom := (mz_omega_primrec c).comp hq
  have heq : Primrec₂ (fun (a : (MZ × BitString) × ℕ) (z : BitString) => decide (z = a.1.2)) :=
    (PrimrecRel.decide Primrec.eq).comp Primrec.snd (hx.comp Primrec.fst)
  have hidx := Primrec.list_findIdx hom heq
  have hent := mcTabEntry_primrec.comp ((mz_tab.comp hq).pair (hi.pair hidx))
  have hpow := mc_nat_pow_primrec₂.comp (Primrec.const 2) (mz_m.comp hq)
  have := Primrec.nat_mod.comp hent hpow
  unfold mcHash mcIdx
  exact this

private theorem mcS_primrec : Primrec (fun z : MZ => mcS c z.2.1 z.1.2.2.2.1 z.1.2.1 z.2.2) := by
  have hsnap := (conditionalOutputSnapshot_primrec c).comp ((mz_A.pair mz_k).pair mz_t)
  have hp : Primrec₂ (fun (z : MZ) (x : BitString) =>
      decide (x ∈ boundedOutputStage c z.1.2.1 z.2.2)) :=
    bitString_mem_primrec.comp Primrec.snd ((mz_omega_primrec c).comp Primrec.fst)
  have := Primrec.list_filter hsnap hp
  unfold mcS
  exact this

private theorem mcHash_primrec' : Primrec₂ (fun (p : MZ × BitString) (i : ℕ) =>
    mcHash c p.1.1.1 p.1.1.2.1 p.1.1.2.2.1 p.1.2.2 i p.2) := mcHash_primrec c

private theorem mcCount_primrec : Primrec (fun a : MZ × ℕ =>
    mcCount c d a.1.1.1 a.1.1.2.1 a.1.1.2.2.1 a.1.1.2.2.2.1 a.1.2.2 a.1.2.1 a.2) := by
  have hS := (mcS_primrec c).comp (Primrec.fst (α := MZ) (β := ℕ))
  have hED := eraseDups_bitstring_primrec.comp hS
  have hN : Primrec (fun p : (MZ × ℕ) × BitString =>
      List.range (d * (p.1.1.1.2.2.1 + p.1.1.1.2.1 + 2))) := by
    have h1 := (mz_m.comp (Primrec.fst.comp (Primrec.fst (α := MZ × ℕ) (β := BitString))))
    have h2 := (mz_n.comp (Primrec.fst.comp (Primrec.fst (α := MZ × ℕ) (β := BitString))))
    have h3 := Primrec.nat_add.comp (Primrec.nat_add.comp h1 h2) (Primrec.const 2)
    have h4 := Primrec.list_range.comp (Primrec.nat_mul.comp (Primrec.const d) h3)
    exact h4
  have hH : Primrec₂ (fun (p : (MZ × ℕ) × BitString) (i : ℕ) =>
      mcHash c p.1.1.1.1 p.1.1.1.2.1 p.1.1.1.2.2.1 p.1.1.2.2 i p.2) := by
    have := (mcHash_primrec c).comp (((Primrec.fst.comp (Primrec.fst.comp
      (Primrec.fst (α := (MZ × ℕ) × BitString) (β := ℕ)))).pair
      (Primrec.snd.comp Primrec.fst)).pair Primrec.snd)
    exact this
  have hmap := Primrec.list_map hN hH
  have hmap' : Primrec₂ (fun (a : MZ × ℕ) (x : BitString) =>
      (List.range (d * (a.1.1.2.2.1 + a.1.1.2.1 + 2))).map fun i =>
        mcHash c a.1.1.1 a.1.1.2.1 a.1.1.2.2.1 a.1.2.2 i x) := hmap
  have hfl := Primrec.list_flatMap hED hmap'
  have hp : Primrec₂ (fun (a : MZ × ℕ) (h : ℕ) => decide (h = a.2)) :=
    (PrimrecRel.decide Primrec.eq).comp Primrec.snd (Primrec.snd.comp Primrec.fst)
  have := list_countP_primrec hfl hp
  unfold mcCount
  exact this

private theorem mcRich_primrec : Primrec (fun a : MZ × ℕ =>
    mcRich c d a.1.1.1 a.1.1.2.1 a.1.1.2.2.1 a.1.1.2.2.2.1 a.1.1.2.2.2.2.1 a.1.2.2 a.1.2.1
      a.2) := by
  have hz := Primrec.fst (α := MZ) (β := ℕ)
  have h1 := mz_m.comp hz
  have h2 := mz_n.comp hz
  have h3 := Primrec.nat_mul.comp (Primrec.const d)
    (Primrec.nat_add.comp (Primrec.nat_add.comp h1 h2) (Primrec.const 2))
  have h4 := mc_nat_pow_primrec₂.comp (Primrec.const 2)
    (Primrec.nat_add.comp (Primrec.const (d + 2)) (mz_e.comp hz))
  have h5 := Primrec.nat_mul.comp h3 h4
  have := (PrimrecRel.decide Primrec.nat_lt).comp h5 (mcCount_primrec c d)
  unfold mcRich
  exact this

private theorem mcBad_primrec : Primrec (fun z : MZ =>
    mcBad c d z.1.1 z.1.2.1 z.1.2.2.1 z.1.2.2.2.1 z.1.2.2.2.2.1 z.2.2 z.2.1) := by
  have hN : Primrec (fun p : MZ × BitString =>
      List.range (d * (p.1.1.2.2.1 + p.1.1.2.1 + 2))) := by
    have h1 := (mz_m.comp (Primrec.fst (α := MZ) (β := BitString)))
    have h2 := (mz_n.comp (Primrec.fst (α := MZ) (β := BitString)))
    have h3 := Primrec.nat_add.comp (Primrec.nat_add.comp h1 h2) (Primrec.const 2)
    have h4 := Primrec.list_range.comp (Primrec.nat_mul.comp (Primrec.const d) h3)
    exact h4
  have hH := (mcHash_primrec c)
  have hR : Primrec₂ (fun (p : MZ × BitString) (i : ℕ) =>
      mcRich c d p.1.1.1 p.1.1.2.1 p.1.1.2.2.1 p.1.1.2.2.2.1 p.1.1.2.2.2.2.1 p.1.2.2 p.1.2.1
        (mcHash c p.1.1.1 p.1.1.2.1 p.1.1.2.2.1 p.1.2.2 i p.2)) := by
    have := (mcRich_primrec c d).comp
      ((Primrec.fst.comp (Primrec.fst (α := MZ × BitString) (β := ℕ))).pair hH)
    exact this
  have hcnt := list_countP_primrec hN hR
  have hr : Primrec (fun p : MZ × BitString => p.1.1.2.2.1 + p.1.1.2.1 + 2) := by
    have h1 := (mz_m.comp (Primrec.fst (α := MZ) (β := BitString)))
    have h2 := (mz_n.comp (Primrec.fst (α := MZ) (β := BitString)))
    have h3 := Primrec.nat_add.comp (Primrec.nat_add.comp h1 h2) (Primrec.const 2)
    exact h3
  have hle := (PrimrecRel.decide Primrec.nat_le).comp hr hcnt
  have hle' : Primrec₂ (fun (z : MZ) (x : BitString) =>
      decide (z.1.2.2.1 + z.1.2.1 + 2 ≤ (List.range (d * (z.1.2.2.1 + z.1.2.1 + 2))).countP
        fun i => mcRich c d z.1.1 z.1.2.1 z.1.2.2.1 z.1.2.2.2.1 z.1.2.2.2.2.1 z.2.2 z.2.1
          (mcHash c z.1.1 z.1.2.1 z.1.2.2.1 z.2.2 i x))) := hle
  have := Primrec.list_filter (mz_omega_primrec c) hle'
  unfold mcBad
  exact this

private theorem mcMatch_primrec : Primrec (fun a : MZ × ℕ =>
    mcMatch c a.1.1.1 a.1.1.2.1 a.1.1.2.2.1 a.1.1.2.2.2.1 a.1.2.2 a.1.2.1 a.1.1.2.2.2.2.2 a.2) := by
  have hS := (mcS_primrec c).comp (Primrec.fst (α := MZ) (β := ℕ))
  have hH : Primrec (fun p : (MZ × ℕ) × BitString =>
      mcHash c p.1.1.1.1 p.1.1.1.2.1 p.1.1.1.2.2.1 p.1.1.2.2 p.1.1.1.2.2.2.2.2 p.2) := by
    have hz := Primrec.fst.comp (Primrec.fst (α := MZ × ℕ) (β := BitString))
    have := (mcHash_primrec c).comp ((hz.pair Primrec.snd).pair (mz_i.comp hz))
    exact this
  have hv := Primrec.snd.comp (Primrec.fst (α := MZ × ℕ) (β := BitString))
  have hp := (PrimrecRel.decide Primrec.eq).comp hH hv
  have hp' : Primrec₂ (fun (a : MZ × ℕ) (x : BitString) =>
      decide (mcHash c a.1.1.1 a.1.1.2.1 a.1.1.2.2.1 a.1.2.2 a.1.1.2.2.2.2.2 x = a.2)) := hp
  have := Primrec.list_filter hS hp'
  unfold mcMatch
  exact this

private theorem mcEnc_primrec : Primrec (fun z : MZ =>
    mcEnc c z.1.1 z.1.2.1 z.1.2.2.1 z.2.2 z.1.2.2.2.2.2 z.2.1) := by
  have hp : Primrec₂ (fun (z : MZ) (x : BitString) => decide (x = z.2.1)) :=
    (PrimrecRel.decide Primrec.eq).comp Primrec.snd (mz_A.comp Primrec.fst)
  have hf := Primrec.list_filter (mz_omega_primrec c) hp
  have hH : Primrec (fun p : MZ × BitString =>
      Nat.bits (mcHash c p.1.1.1 p.1.1.2.1 p.1.1.2.2.1 p.1.2.2 p.1.1.2.2.2.2.2 p.2)) := by
    have hz := Primrec.fst (α := MZ) (β := BitString)
    have := primrec_natBits.comp
      ((mcHash_primrec c).comp ((hz.pair Primrec.snd).pair (mz_i.comp hz)))
    exact this
  have hH' : Primrec₂ (fun (z : MZ) (x : BitString) =>
      Nat.bits (mcHash c z.1.1 z.1.2.1 z.1.2.2.1 z.2.2 z.1.2.2.2.2.2 x)) := hH
  have := Primrec.list_map hf hH'
  unfold mcEnc
  exact this

/-- The parameters `(n, m, k, e, i)` packed into one self-delimiting string. -/
private def mcW (n m k e i : ℕ) : BitString :=
  pairCode (Nat.bits n) (pairCode (Nat.bits m) (pairCode (Nat.bits k)
    (pairCode (Nat.bits e) (Nat.bits i))))

/-- Decoding of `mcW`. -/
private def mcPar (w : BitString) : ℕ × ℕ × ℕ × ℕ × ℕ :=
  (bitsToNat (decodeFirst w), bitsToNat (decodeFirst (decodeSecond w)),
    bitsToNat (decodeFirst (decodeSecond (decodeSecond w))),
    bitsToNat (decodeFirst (decodeSecond (decodeSecond (decodeSecond w)))),
    bitsToNat (decodeSecond (decodeSecond (decodeSecond (decodeSecond w)))))

private theorem mcPar_mcW (n m k e i : ℕ) : mcPar (mcW n m k e i) = (n, m, k, e, i) := by
  simp [mcPar, mcW, decodeFirst_pairCode, decodeSecond_pairCode, bitsToNat_bits]

private theorem mcPar_primrec : Primrec mcPar := by
  have h1 := decodeSecond_primrec
  have h2 := decodeSecond_primrec.comp h1
  have h3 := decodeSecond_primrec.comp h2
  have h4 := decodeSecond_primrec.comp h3
  have := (bitsToNat_primrec.comp decodeFirst_primrec).pair
    ((bitsToNat_primrec.comp (decodeFirst_primrec.comp h1)).pair
    ((bitsToNat_primrec.comp (decodeFirst_primrec.comp h2)).pair
    ((bitsToNat_primrec.comp (decodeFirst_primrec.comp h3)).pair
    (bitsToNat_primrec.comp h4))))
  unfold mcPar
  exact this

/-- The hash table together with the parameters, condition and stage, read off a parameter
word. -/
private def mcZof (d : ℕ) (w A : BitString) (t : ℕ) : MZ :=
  ((mcTable d (mcPar w).1 (mcPar w).2.1, mcPar w), A, t)

private theorem mcZof_computable (d : ℕ) :
    Computable (fun p : (BitString × BitString) × ℕ => mcZof d p.1.1 p.1.2 p.2) := by
  have hP := mcPar_primrec.to_comp.comp (Computable.fst.comp (Computable.fst
    (α := BitString × BitString) (β := ℕ)))
  have hT := (mcTable_computable d).comp
    (Computable.pair (Computable.fst.comp hP) (Computable.fst.comp (Computable.snd.comp hP)))
  have := Computable.pair (Computable.pair hT hP)
    (Computable.pair (Computable.snd.comp Computable.fst) Computable.snd)
  unfold mcZof
  exact this

/-- The bad list at stage `t`, with parameters and condition read from the context. -/
private def mcLbad (c : Code) (d : ℕ) (y : BitString) (t : ℕ) : List BitString :=
  mcBad c d (mcTable d (mcPar (decodeFirst y)).1 (mcPar (decodeFirst y)).2.1)
    (mcPar (decodeFirst y)).1 (mcPar (decodeFirst y)).2.1 (mcPar (decodeFirst y)).2.2.1
    (mcPar (decodeFirst y)).2.2.2.1 t (decodeSecond y)

/-- The candidate list at stage `t`, with parameters, condition and fingerprint read from
the context. -/
private def mcLmatch (c : Code) (d : ℕ) (y : BitString) (t : ℕ) : List BitString :=
  mcMatch c (mcTable d (mcPar (decodeFirst y)).1 (mcPar (decodeFirst y)).2.1)
    (mcPar (decodeFirst y)).1 (mcPar (decodeFirst y)).2.1 (mcPar (decodeFirst y)).2.2.1 t
    (decodeFirst (decodeSecond y)) (mcPar (decodeFirst y)).2.2.2.2
    (bitsToNat (decodeSecond (decodeSecond y)))

/-- The encoder's list at stage `t`, with parameters and `C` read from the context. -/
private def mcLenc (c : Code) (d : ℕ) (y : BitString) (t : ℕ) : List BitString :=
  mcEnc c (mcTable d (mcPar (decodeFirst y)).1 (mcPar (decodeFirst y)).2.1)
    (mcPar (decodeFirst y)).1 (mcPar (decodeFirst y)).2.1 t (mcPar (decodeFirst y)).2.2.2.2
    (decodeSecond y)

private theorem mcLbad_computable : Computable (fun p : BitString × ℕ => mcLbad c d p.1 p.2) := by
  have hy := Computable.fst (α := BitString) (β := ℕ)
  have hz := (mcZof_computable d).comp (Computable.pair (Computable.pair
    (decodeFirst_primrec.to_comp.comp hy)
    (decodeSecond_primrec.to_comp.comp hy)) Computable.snd)
  have := (mcBad_primrec c d).to_comp.comp hz
  unfold mcLbad
  exact this

private theorem mcLmatch_computable :
    Computable (fun p : BitString × ℕ => mcLmatch c d p.1 p.2) := by
  have hy := Computable.fst (α := BitString) (β := ℕ)
  have hz := (mcZof_computable d).comp (Computable.pair (Computable.pair
    (decodeFirst_primrec.to_comp.comp hy)
    (decodeFirst_primrec.to_comp.comp (decodeSecond_primrec.to_comp.comp hy))) Computable.snd)
  have hv := bitsToNat_primrec.to_comp.comp (decodeSecond_primrec.to_comp.comp
    (decodeSecond_primrec.to_comp.comp hy))
  have := (mcMatch_primrec c).to_comp.comp (Computable.pair hz hv)
  unfold mcLmatch
  exact this

private theorem mcLenc_computable : Computable (fun p : BitString × ℕ => mcLenc c d p.1 p.2) := by
  have hy := Computable.fst (α := BitString) (β := ℕ)
  have hz := (mcZof_computable d).comp (Computable.pair (Computable.pair
    (decodeFirst_primrec.to_comp.comp hy)
    (decodeSecond_primrec.to_comp.comp hy)) Computable.snd)
  have := (mcEnc_primrec c).to_comp.comp hz
  unfold mcLenc
  exact this

end Primrec

private theorem findIdx_eq_of_prefix {l l' : List BitString} (h : l <+: l') {x : BitString}
    (hx : x ∈ l) : l'.findIdx (fun z => decide (z = x)) = l.findIdx (fun z => decide (z = x)) := by
  obtain ⟨r, rfl⟩ := h
  rw [List.findIdx_append, ite_eq_left]
  exact List.findIdx_lt_length_of_exists ⟨x, hx, by simp⟩

private theorem mcIdx_stable (c : Code) (n : ℕ) {t t' : ℕ} (h : t ≤ t') {x : BitString}
    (hx : x ∈ boundedOutputStage c n t) : mcIdx c n t' x = mcIdx c n t x :=
  findIdx_eq_of_prefix (boundedOutputStage_prefix_of_le c n h) hx

private theorem mcHash_stable (c : Code) (tab : List (List ℕ)) (n m i : ℕ) {t t' : ℕ} (h : t ≤ t')
    {x : BitString} (hx : x ∈ boundedOutputStage c n t) :
    mcHash c tab n m t' i x = mcHash c tab n m t i x := by
  unfold mcHash; rw [mcIdx_stable c n h hx]

private theorem mcIdx_lt (c : Code) (n t : ℕ) {x : BitString} (hx : x ∈ boundedOutputStage c n t) :
    mcIdx c n t x < (boundedOutputStage c n t).length :=
  List.findIdx_lt_length_of_exists ⟨x, hx, by simp⟩

private theorem mcIdx_getElem (c : Code) (n t : ℕ) {x : BitString}
    (hx : x ∈ boundedOutputStage c n t) :
    (boundedOutputStage c n t)[mcIdx c n t x]'(mcIdx_lt c n t hx) = x := by
  unfold mcIdx
  have := List.findIdx_getElem (xs := boundedOutputStage c n t)
    (p := fun z => decide (z = x)) (w := mcIdx_lt c n t hx)
  simpa using this

private theorem mcIdx_inj (c : Code) (n t : ℕ) {x x' : BitString}
    (hx : x ∈ boundedOutputStage c n t)
    (hx' : x' ∈ boundedOutputStage c n t) (h : mcIdx c n t x = mcIdx c n t x') : x = x' := by
  rw [← mcIdx_getElem c n t hx, ← mcIdx_getElem c n t hx']
  simp only [h]

private theorem length_eraseDups_le (l : List BitString) : l.eraseDups.length ≤ l.length := by
  classical
  rw [← List.toFinset_card_of_nodup (nodup_eraseDups_bitString l)]
  have : l.eraseDups.toFinset = l.toFinset := by
    ext x; simp
  rw [this]
  exact List.toFinset_card_le l

private theorem length_boundedOutputStage_lt (c : Code) (n t : ℕ) :
    (boundedOutputStage c n t).length < 2 ^ (n + 1) := by
  classical
  rw [← List.toFinset_card_of_nodup (boundedOutputStage_nodup c n t),
    boundedOutputStage_toFinset_eq_snapshotCodes]
  refine lt_of_le_of_lt (List.toFinset_card_le _) (lt_of_le_of_lt ?_ (length_boundedPrograms_lt n))
  exact List.length_filterMap_le _ _

private theorem mem_conditionalOutputSnapshot_mono {c : Code} {A : BitString} {k t t' : ℕ}
    (h : t ≤ t') {x : BitString} (hx : x ∈ conditionalOutputSnapshot c A k t) :
    x ∈ conditionalOutputSnapshot c A k t' := by
  unfold conditionalOutputSnapshot at hx ⊢
  rw [List.mem_filterMap] at hx ⊢
  obtain ⟨p, hp, hr⟩ := hx
  exact ⟨p, hp, conditionalRunOut_mono c h hr⟩

private theorem mem_mcS_mono {c : Code} {A : BitString} {k n t t' : ℕ} (h : t ≤ t') {x : BitString}
    (hx : x ∈ mcS c A k n t) : x ∈ mcS c A k n t' := by
  unfold mcS at hx ⊢
  simp only [List.mem_filter, decide_eq_true_eq] at hx ⊢
  exact ⟨mem_conditionalOutputSnapshot_mono h hx.1,
    (boundedOutputStage_prefix_of_le c n h).subset hx.2⟩

private theorem mem_omega_of_mem_mcS {c : Code} {A : BitString} {k n t : ℕ} {x : BitString}
    (hx : x ∈ mcS c A k n t) : x ∈ boundedOutputStage c n t := by
  unfold mcS at hx
  simp only [List.mem_filter, decide_eq_true_eq] at hx
  exact hx.2

private theorem length_mcS_eraseDups_lt (c : Code) (A : BitString) (k n t : ℕ) :
    (mcS c A k n t).eraseDups.length < 2 ^ (k + 1) := by
  refine lt_of_le_of_lt (length_eraseDups_le _) (lt_of_le_of_lt ?_ (length_boundedPrograms_lt k))
  unfold mcS conditionalOutputSnapshot
  exact (List.length_filter_le _ _).trans (List.length_filterMap_le _ _)

private theorem mcCount_eq_sum (c : Code) (d : ℕ) (tab : List (List ℕ)) (n m k t : ℕ)
    (A : BitString)
    (u : ℕ) : mcCount c d tab n m k t A u = ∑ x ∈ (mcS c A k n t).toFinset,
      (List.range (d * (m + n + 2))).countP (fun i => decide (mcHash c tab n m t i x = u)) := by
  classical
  have hts : (mcS c A k n t).toFinset = (mcS c A k n t).eraseDups.toFinset := by
    ext x; simp
  rw [hts, List.sum_toFinset _ (nodup_eraseDups_bitString _), mcCount, List.countP_flatMap]
  congr 1
  refine List.map_congr_left fun x _ => ?_
  simp only [Function.comp_apply, List.countP_map]
  rfl

private theorem mcCount_mono (c : Code) (d : ℕ) (tab : List (List ℕ)) (n m k : ℕ) (A : BitString)
    (u : ℕ) {t t' : ℕ} (h : t ≤ t') :
    mcCount c d tab n m k t A u ≤ mcCount c d tab n m k t' A u := by
  classical
  rw [mcCount_eq_sum, mcCount_eq_sum]
  calc _ = ∑ x ∈ (mcS c A k n t).toFinset,
        (List.range (d * (m + n + 2))).countP (fun i => decide (mcHash c tab n m t' i x = u)) := by
        refine Finset.sum_congr rfl fun x hx => ?_
        rw [List.mem_toFinset] at hx
        simp only [mcHash_stable c tab n m _ h (mem_omega_of_mem_mcS hx)]
    _ ≤ _ := by
        refine Finset.sum_le_sum_of_subset fun x hx => ?_
        rw [List.mem_toFinset] at hx ⊢
        exact mem_mcS_mono h hx

private theorem mcRich_mono (c : Code) (d : ℕ) (tab : List (List ℕ)) (n m k e : ℕ) (A : BitString)
    (u : ℕ) {t t' : ℕ} (h : t ≤ t') (hr : mcRich c d tab n m k e t A u = true) :
    mcRich c d tab n m k e t' A u = true := by
  unfold mcRich at hr ⊢
  rw [decide_eq_true_eq] at hr ⊢
  exact lt_of_lt_of_le hr (mcCount_mono c d tab n m k A u h)

private theorem mem_mcBad_iff (c : Code) (d : ℕ) (tab : List (List ℕ)) (n m k e t : ℕ)
    (A x : BitString) :
    x ∈ mcBad c d tab n m k e t A ↔ x ∈ boundedOutputStage c n t ∧
      m + n + 2 ≤ (List.range (d * (m + n + 2))).countP fun i =>
        mcRich c d tab n m k e t A (mcHash c tab n m t i x) := by
  unfold mcBad
  simp only [List.mem_filter, decide_eq_true_eq]

private theorem mem_mcBad_mono (c : Code) (d : ℕ) (tab : List (List ℕ)) (n m k e : ℕ)
    (A : BitString)
    {t t' : ℕ} (h : t ≤ t') {x : BitString} (hx : x ∈ mcBad c d tab n m k e t A) :
    x ∈ mcBad c d tab n m k e t' A := by
  rw [mem_mcBad_iff] at hx ⊢
  refine ⟨(boundedOutputStage_prefix_of_le c n h).subset hx.1, le_trans hx.2 ?_⟩
  refine List.countP_mono_left fun i _ hi => ?_
  rw [mcHash_stable c tab n m i h hx.1]
  exact mcRich_mono c d tab n m k e A _ h hi

private theorem sum_ite_eq_le_one (a : ℕ) {U : List ℕ} (hU : U.Nodup) :
    (U.map fun u => if a = u then 1 else 0).sum ≤ 1 := by
  induction U with
  | nil => simp
  | cons u U ih =>
    rw [List.nodup_cons] at hU
    rw [List.map_cons, List.sum_cons]
    by_cases h : a = u
    · subst h
      have : (U.map fun u => if a = u then 1 else 0) = U.map fun _ => 0 :=
        List.map_congr_left fun u hu => ite_eq_right fun (h : a = u) => hU.1 (h ▸ hu)
      rw [this]
      simp
    · rw [ite_eq_right h, zero_add]
      exact ih hU.2

private theorem sum_countP_eq_le_length {U : List ℕ} (hU : U.Nodup) (L : List ℕ) :
    (U.map fun u => L.countP fun h => decide (h = u)).sum ≤ L.length := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have hsum : (U.map fun u => (a :: L).countP fun h => decide (h = u)).sum =
        (U.map fun u => L.countP fun h => decide (h = u)).sum +
          (U.map fun u => if a = u then 1 else 0).sum := by
      rw [← List.sum_map_add]
      congr 1
      refine List.map_congr_left fun u _ => ?_
      simp [List.countP_cons]
    have hone := sum_ite_eq_le_one a hU
    rw [hsum, List.length_cons]
    omega

/-- The rich fingerprint values below `2^m` at stage `t`. -/
private def mcRichList (c : Code) (d : ℕ) (tab : List (List ℕ)) (n m k e t : ℕ) (A : BitString) :
    List ℕ :=
  (List.range (2 ^ m)).filter (mcRich c d tab n m k e t A)

private theorem mcRichList_bound (c : Code) (d : ℕ) (tab : List (List ℕ)) (n m k e t : ℕ)
    (A : BitString) (hd : 0 < d) (hne : mcRichList c d tab n m k e t A ≠ []) :
    (mcRichList c d tab n m k e t A).length * 2 ^ (d + 2 + e) < 2 ^ (k + 1) := by
  set U := mcRichList c d tab n m k e t A with hUdef
  set N := d * (m + n + 2) with hN
  have hNpos : 0 < N := Nat.mul_pos hd (by omega)
  set Lh := (mcS c A k n t).eraseDups.flatMap fun x =>
    (List.range N).map fun i => mcHash c tab n m t i x with hLh
  have hcount : ∀ u, mcCount c d tab n m k t A u = Lh.countP fun h => decide (h = u) :=
    fun u => rfl
  have hUnd : U.Nodup := List.nodup_range.filter _
  have hlen : Lh.length = (mcS c A k n t).eraseDups.length * N := by
    rw [hLh, List.length_flatMap]
    simp [List.map_const', List.sum_replicate]
  have h1 := sum_countP_eq_le_length hUnd Lh
  have h2 : (U.map fun _ => N * 2 ^ (d + 2 + e) + 1).sum ≤
      (U.map fun u => Lh.countP fun h => decide (h = u)).sum := by
    refine List.sum_le_sum fun u hu => ?_
    rw [← hcount]
    have hu' := hu
    rw [hUdef, mcRichList, List.mem_filter] at hu'
    have := hu'.2
    unfold mcRich at this
    rw [decide_eq_true_eq] at this
    have h' : N * 2 ^ (d + 2 + e) < mcCount c d tab n m k t A u := this
    omega
  have h3 : (U.map fun _ => N * 2 ^ (d + 2 + e) + 1).sum =
      U.length * (N * 2 ^ (d + 2 + e) + 1) := by
    simp [List.map_const', List.sum_replicate]
  have hS := length_mcS_eraseDups_lt c A k n t
  have hUpos : 0 < U.length := List.length_pos_of_ne_nil hne
  have h4 : U.length * (N * 2 ^ (d + 2 + e)) < (mcS c A k n t).eraseDups.length * N + 1 := by
    have := h2.trans h1
    rw [h3, hlen] at this
    nlinarith
  have h5 : N * (U.length * 2 ^ (d + 2 + e)) < N * 2 ^ (k + 1) := by
    have : (mcS c A k n t).eraseDups.length * N + 1 ≤ 2 ^ (k + 1) * N := by nlinarith
    nlinarith
  exact Nat.lt_of_mul_lt_mul_left h5

private theorem length_mcBad_le_badCount (c : Code) (d : ℕ) (tab : List (List ℕ)) (n m k e t : ℕ)
    (A : BitString) : (mcBad c d tab n m k e t A).length ≤
      mcBadCount (2 ^ (n + 1)) (d * (m + n + 2)) (m + n + 2) (2 ^ m) tab
        (mcRichList c d tab n m k e t A) := by
  set B := mcBad c d tab n m k e t A with hB
  set U := mcRichList c d tab n m k e t A with hU
  have hBnd : B.Nodup := (boundedOutputStage_nodup c n t).filter _
  have hmemB : ∀ x ∈ B, x ∈ boundedOutputStage c n t := fun x hx =>
    ((mem_mcBad_iff c d tab n m k e t A x).1 hx).1
  have hmapnd : (B.map (mcIdx c n t)).Nodup :=
    hBnd.map_on fun x hx y hy h => mcIdx_inj c n t (hmemB x hx) (hmemB y hy) h
  have hany : ∀ (x : BitString) (i : ℕ), (U.any fun u => decide (u = mcTabEntry tab i
      (mcIdx c n t x) % 2 ^ m)) = mcRich c d tab n m k e t A (mcHash c tab n m t i x) := by
    intro x i
    have hlt : mcHash c tab n m t i x < 2 ^ m := Nat.mod_lt _ (by positivity)
    rw [Bool.eq_iff_iff, List.any_eq_true]
    simp only [decide_eq_true_eq, exists_eq_right, hU, mcRichList, List.mem_filter,
      List.mem_range]
    exact ⟨fun h => h.2, fun h => ⟨hlt, h⟩⟩
  have hsub : B.map (mcIdx c n t) ⊆ (List.range (2 ^ (n + 1))).filter fun j =>
      decide (m + n + 2 ≤ (List.range (d * (m + n + 2))).countP fun i =>
        U.any fun u => decide (u = mcTabEntry tab i j % 2 ^ m)) := by
    intro j hj
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hj
    rw [List.mem_filter, List.mem_range, decide_eq_true_eq]
    refine ⟨lt_of_lt_of_le (mcIdx_lt c n t (hmemB x hx))
      (length_boundedOutputStage_lt c n t).le, ?_⟩
    simp only [hany]
    exact ((mem_mcBad_iff c d tab n m k e t A x).1 hx).2
  have := (List.subperm_of_subset hmapnd hsub).length_le
  rw [List.length_map] at this
  unfold mcBadCount
  rw [List.countP_eq_length_filter]
  exact this

private theorem mcBad_bound (c : Code) (d : ℕ) (tab : List (List ℕ)) (n m k e t : ℕ) (A : BitString)
    (hgood : mcTabGood d n m tab = true) (hd : 0 < d) (hkm : k ≤ m) :
    (mcBad c d tab n m k e t A).length ≤ 2 ^ (k - e) ∧
      (mcBad c d tab n m k e t A ≠ [] → e < k) := by
  have hle := length_mcBad_le_badCount c d tab n m k e t A
  by_cases hU : mcRichList c d tab n m k e t A = []
  · rw [hU] at hle
    have h0 : mcBadCount (2 ^ (n + 1)) (d * (m + n + 2)) (m + n + 2) (2 ^ m) tab [] = 0 := by
      unfold mcBadCount
      rw [List.countP_eq_zero]
      intro j _
      simp
    rw [h0, Nat.le_zero, List.length_eq_zero_iff] at hle
    rw [hle]
    exact ⟨by simp, fun h => absurd rfl h⟩
  · have hb := mcRichList_bound c d tab n m k e t A hd hU
    have hUpos : 0 < (mcRichList c d tab n m k e t A).length := List.length_pos_of_ne_nil hU
    have hek : d + 2 + e < k + 1 := by
      have : 2 ^ (d + 2 + e) < 2 ^ (k + 1) := lt_of_le_of_lt (Nat.le_mul_of_pos_left _ hUpos) hb
      exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 this
    have hsplit1 : 2 ^ (k + 1) = 2 ^ (k - e) * 2 ^ (e + 1) := by
      rw [← pow_add]; congr 1; omega
    have hsplit2 : 2 ^ (d + 2 + e) = 2 ^ (d + 1) * 2 ^ (e + 1) := by
      rw [← pow_add]; congr 1; omega
    have hsz : (mcRichList c d tab n m k e t A).length * 2 ^ (d + 1) < 2 ^ (k - e) := by
      rw [hsplit1, hsplit2, ← mul_assoc] at hb
      exact Nat.lt_of_mul_lt_mul_right hb
    have hkm' : 2 ^ (k - e) ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hgood' : mcBadCount (2 ^ (n + 1)) (d * (m + n + 2)) (m + n + 2) (2 ^ m) tab
        (mcRichList c d tab n m k e t A) < (mcRichList c d tab n m k e t A).length :=
      mcTabGood_spec hgood (List.filter_sublist) hU
      (le_of_lt (lt_of_lt_of_le hsz hkm'))
    have h2 : (mcRichList c d tab n m k e t A).length ≤
        (mcRichList c d tab n m k e t A).length * 2 ^ (d + 1) :=
      Nat.le_mul_of_pos_right _ (by positivity)
    exact ⟨by omega, fun _ => by omega⟩

private theorem card_le_of_mono_family (L : ℕ → List BitString)
    (hmono : ∀ t t', t ≤ t' → ∀ x ∈ L t, x ∈ L t') (B : ℕ)
    (hB : ∀ t, (L t).toFinset.card ≤ B) (s : Finset BitString)
    (hs : ∀ z ∈ s, ∃ t, z ∈ L t) : s.card ≤ B := by
  classical
  choose! tz htz using hs
  refine le_trans (Finset.card_le_card fun z hz => ?_) (hB (s.sup tz))
  rw [List.mem_toFinset]
  exact hmono _ _ (Finset.le_sup hz) z (htz z hz)

private theorem mem_mcMatch_iff (c : Code) (tab : List (List ℕ)) (n m k t : ℕ) (A : BitString)
    (i v : ℕ) (x : BitString) :
    x ∈ mcMatch c tab n m k t A i v ↔ x ∈ mcS c A k n t ∧ mcHash c tab n m t i x = v := by
  unfold mcMatch
  simp only [List.mem_filter, decide_eq_true_eq]

private theorem mem_mcMatch_mono (c : Code) (tab : List (List ℕ)) (n m k : ℕ) (A : BitString)
    (i v : ℕ) {t t' : ℕ} (h : t ≤ t') {x : BitString} (hx : x ∈ mcMatch c tab n m k t A i v) :
    x ∈ mcMatch c tab n m k t' A i v := by
  rw [mem_mcMatch_iff] at hx ⊢
  rw [mcHash_stable c tab n m i h (mem_omega_of_mem_mcS hx.1)]
  exact ⟨mem_mcS_mono h hx.1, hx.2⟩

private theorem card_mcMatch_le (c : Code) (d : ℕ) (tab : List (List ℕ)) (n m k t : ℕ)
    (A : BitString)
    {i : ℕ} (hi : i < d * (m + n + 2)) (v : ℕ) :
    (mcMatch c tab n m k t A i v).toFinset.card ≤ mcCount c d tab n m k t A v := by
  classical
  rw [mcCount_eq_sum]
  have hsub : (mcMatch c tab n m k t A i v).toFinset ⊆ (mcS c A k n t).toFinset := by
    intro x hx
    rw [List.mem_toFinset, mem_mcMatch_iff] at hx
    rw [List.mem_toFinset]; exact hx.1
  calc (mcMatch c tab n m k t A i v).toFinset.card
      = ∑ x ∈ (mcMatch c tab n m k t A i v).toFinset, 1 := by simp
    _ ≤ ∑ x ∈ (mcMatch c tab n m k t A i v).toFinset,
        (List.range (d * (m + n + 2))).countP (fun i => decide (mcHash c tab n m t i x = v)) := by
        refine Finset.sum_le_sum fun x hx => ?_
        rw [List.mem_toFinset, mem_mcMatch_iff] at hx
        refine List.countP_pos_iff.2 ⟨i, List.mem_range.2 hi, ?_⟩
        simpa using hx.2
    _ ≤ _ := Finset.sum_le_sum_of_subset hsub

private theorem mem_mcEnc_iff (c : Code) (tab : List (List ℕ)) (n m t i : ℕ) (C z : BitString) :
    z ∈ mcEnc c tab n m t i C ↔ C ∈ boundedOutputStage c n t ∧
      z = Nat.bits (mcHash c tab n m t i C) := by
  unfold mcEnc
  simp only [List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨x, ⟨hx, rfl⟩, rfl⟩; exact ⟨hx, rfl⟩
  · rintro ⟨hx, rfl⟩; exact ⟨C, ⟨hx, rfl⟩, rfl⟩

open Classical in
private theorem card_badIndices_lt (c : Code) (d : ℕ) (tab : List (List ℕ)) (n m k e : ℕ)
    (A C : BitString) {tC : ℕ} (hC : C ∈ boundedOutputStage c n tC)
    (hgood : ∀ t, C ∉ mcBad c d tab n m k e t A) :
    ((Finset.range (d * (m + n + 2))).filter fun i => ∃ t, C ∈ boundedOutputStage c n t ∧
      mcRich c d tab n m k e t A (mcHash c tab n m t i C) = true).card < m + n + 2 := by
  classical
  set I := (Finset.range (d * (m + n + 2))).filter fun i => ∃ t, C ∈ boundedOutputStage c n t ∧
      mcRich c d tab n m k e t A (mcHash c tab n m t i C) = true with hI
  have hex : ∀ i ∈ I, ∃ t, C ∈ boundedOutputStage c n t ∧
      mcRich c d tab n m k e t A (mcHash c tab n m t i C) = true := fun i hi =>
    (Finset.mem_filter.1 hi).2
  choose! ti hti using hex
  set ts := max tC (I.sup ti) with hts
  have hsub : I ⊆ (Finset.range (d * (m + n + 2))).filter fun i =>
      mcRich c d tab n m k e ts A (mcHash c tab n m ts i C) = true := by
    intro i hi
    have hle : ti i ≤ ts := le_trans (Finset.le_sup hi) (le_max_right _ _)
    refine Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hi).1, ?_⟩
    rw [mcHash_stable c tab n m i hle (hti i hi).1]
    exact mcRich_mono c d tab n m k e A _ hle (hti i hi).2
  have hCts : C ∈ boundedOutputStage c n ts :=
    (boundedOutputStage_prefix_of_le c n (le_max_left _ _)).subset hC
  have hnot := hgood ts
  rw [mem_mcBad_iff] at hnot
  have hlt : (List.range (d * (m + n + 2))).countP (fun i =>
      mcRich c d tab n m k e ts A (mcHash c tab n m ts i C)) < m + n + 2 := by
    by_contra h
    exact hnot ⟨hCts, by omega⟩
  have hcard : ((Finset.range (d * (m + n + 2))).filter fun i =>
      mcRich c d tab n m k e ts A (mcHash c tab n m ts i C) = true).card =
      (List.range (d * (m + n + 2))).countP (fun i =>
        mcRich c d tab n m k e ts A (mcHash c tab n m ts i C)) := by
    rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup
      (List.nodup_range.filter _), List.toFinset_filter, List.toFinset_range]
  exact lt_of_le_of_lt (Finset.card_le_card hsub) (hcard ▸ hlt)

private theorem exists_common_good_index (c : Code) (d : ℕ) (tab : List (List ℕ)) (n m e : ℕ)
    (ks : Fin d → ℕ) (As : Fin d → BitString) (C : BitString) {tC : ℕ}
    (hC : C ∈ boundedOutputStage c n tC)
    (hgood : ∀ j t, C ∉ mcBad c d tab n m (ks j) e t (As j)) (hd : 0 < d) :
    ∃ i < d * (m + n + 2), ∀ j t, mcCount c d tab n m (ks j) t (As j)
      (mcHash c tab n m tC i C) ≤ d * (m + n + 2) * 2 ^ (d + 2 + e) := by
  classical
  set N := d * (m + n + 2) with hN
  let I : Fin d → Finset ℕ := fun j => (Finset.range N).filter fun i =>
    ∃ t, C ∈ boundedOutputStage c n t ∧
      mcRich c d tab n m (ks j) e t (As j) (mcHash c tab n m t i C) = true
  have hI : ∀ j, (I j).card < m + n + 2 := fun j =>
    card_badIndices_lt c d tab n m (ks j) e (As j) C hC (hgood j)
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hU : (Finset.univ.biUnion I).card < (Finset.range N).card := by
    rw [Finset.card_range]
    calc (Finset.univ.biUnion I).card ≤ ∑ j, (I j).card := Finset.card_biUnion_le
      _ < ∑ _j : Fin d, (m + n + 2) :=
          Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun j _ => hI j
      _ = N := by simp [hN]
  obtain ⟨i, hiN, hiU⟩ := Finset.exists_mem_notMem_of_card_lt_card hU
  refine ⟨i, Finset.mem_range.1 hiN, fun j t => ?_⟩
  by_contra hlt
  push Not at hlt
  apply hiU
  refine Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, Finset.mem_filter.2 ⟨hiN, ?_⟩⟩
  have hle : tC ≤ max t tC := le_max_right _ _
  refine ⟨max t tC, (boundedOutputStage_prefix_of_le c n hle).subset hC, ?_⟩
  rw [mcHash_stable c tab n m i hle hC]
  unfold mcRich
  rw [decide_eq_true_eq]
  exact lt_of_lt_of_le hlt (mcCount_mono c d tab n m (ks j) (As j) _ (le_max_left _ _))

private theorem length_bits_two_pow (j : ℕ) : (Nat.bits (2 ^ j)).length = j + 1 := by
  rw [Nat.size_eq_bits_len, Nat.size_pow]

private theorem condK_le_of_mem_mcBad (D : Map) (hD : isOptimalConditional D) (c : Code) (d : ℕ)
    (hd : 0 < d) : ∃ c₀ : ℕ, ∀ (n m k e t : ℕ) (A C : BitString), k ≤ m →
      C ∈ mcBad c d (mcTable d n m) n m k e t A →
      e < k ∧ condK D C (pairCode (mcW n m k e 0) A) ≤ ((k - e + 1 + c₀ : ℕ) : ℕ∞) := by
  obtain ⟨c₀, hc₀⟩ := condK_le_of_mem_stageList D hD (mcLbad c d) (mcLbad_computable c d)
  refine ⟨c₀, fun n m k e t A C hkm hC => ?_⟩
  have hL : ∀ t', mcLbad c d (pairCode (mcW n m k e 0) A) t' =
      mcBad c d (mcTable d n m) n m k e t' A := fun t' => by
    simp only [mcLbad, decodeFirst_pairCode, decodeSecond_pairCode, mcPar_mcW]
  have hbd := mcBad_bound c d (mcTable d n m) n m k e t A (mcTable_good d n m) hd hkm
  refine ⟨hbd.2 (List.ne_nil_of_mem hC), ?_⟩
  have h := hc₀ (pairCode (mcW n m k e 0) A) C t (2 ^ (k - e)) (by rw [hL]; exact hC)
    (fun s hs => by
      refine card_le_of_mono_family (fun t' => mcBad c d (mcTable d n m) n m k e t' A)
        (fun t₁ t₂ h x hx => mem_mcBad_mono c d _ n m k e A h hx) _ (fun t' => ?_) s
        (fun z hz => by simpa only [hL] using hs z hz)
      exact (List.toFinset_card_le _).trans
        (mcBad_bound c d (mcTable d n m) n m k e t' A (mcTable_good d n m) hd hkm).1)
  rw [length_bits_two_pow] at h
  exact h

private theorem condK_le_of_mem_mcMatch (D : Map) (hD : isOptimalConditional D) (c : Code) (d : ℕ) :
    ∃ c₀ : ℕ, ∀ (n m k e i t v : ℕ) (A C : BitString), i < d * (m + n + 2) →
      C ∈ mcMatch c (mcTable d n m) n m k t A i v →
      (∀ t', mcCount c d (mcTable d n m) n m k t' A v ≤ d * (m + n + 2) * 2 ^ (d + 2 + e)) →
      condK D C (pairCode (mcW n m k e i) (pairCode A (Nat.bits v))) ≤
        (((Nat.bits (d * (m + n + 2) * 2 ^ (d + 2 + e))).length + c₀ : ℕ) : ℕ∞) := by
  obtain ⟨c₀, hc₀⟩ := condK_le_of_mem_stageList D hD (mcLmatch c d) (mcLmatch_computable c d)
  refine ⟨c₀, fun n m k e i t v A C hi hC hcnt => ?_⟩
  have hL : ∀ t', mcLmatch c d (pairCode (mcW n m k e i) (pairCode A (Nat.bits v))) t' =
      mcMatch c (mcTable d n m) n m k t' A i v := fun t' => by
    simp only [mcLmatch, decodeFirst_pairCode, decodeSecond_pairCode, mcPar_mcW, bitsToNat_bits]
  exact hc₀ _ C t _ (by rw [hL]; exact hC) fun s hs => by
    refine card_le_of_mono_family (fun t' => mcMatch c (mcTable d n m) n m k t' A i v)
      (fun t₁ t₂ h x hx => mem_mcMatch_mono c _ n m k A i v h hx) _ (fun t' => ?_) s
      (fun z hz => by simpa only [hL] using hs z hz)
    exact (card_mcMatch_le c d _ n m k t' A hi v).trans (hcnt t')

private theorem condK_le_of_mcEnc (D : Map) (hD : isOptimalConditional D) (c : Code) (d : ℕ) :
    ∃ c₀ : ℕ, ∀ (n m i t : ℕ) (C : BitString), C ∈ boundedOutputStage c n t →
      condK D (Nat.bits (mcHash c (mcTable d n m) n m t i C)) (pairCode (mcW n m 0 0 i) C) ≤
        (c₀ : ℕ∞) := by
  obtain ⟨c₀, hc₀⟩ := condK_le_of_mem_stageList D hD (mcLenc c d) (mcLenc_computable c d)
  refine ⟨1 + c₀, fun n m i t C hC => ?_⟩
  have hL : ∀ t', mcLenc c d (pairCode (mcW n m 0 0 i) C) t' =
      mcEnc c (mcTable d n m) n m t' i C := fun t' => by
    simp only [mcLenc, decodeFirst_pairCode, decodeSecond_pairCode, mcPar_mcW]
  have h := hc₀ (pairCode (mcW n m 0 0 i) C) _ t 1
    (by rw [hL, mem_mcEnc_iff]; exact ⟨hC, rfl⟩) fun s hs => by
      refine Finset.card_le_one.2 fun a ha b hb => ?_
      obtain ⟨ta, hta⟩ := hs a ha
      obtain ⟨tb, htb⟩ := hs b hb
      rw [hL, mem_mcEnc_iff] at hta htb
      have key : ∀ t', C ∈ boundedOutputStage c n t' →
          mcHash c (mcTable d n m) n m t' i C = mcHash c (mcTable d n m) n m t i C := by
        intro t' ht'
        rcases le_total t t' with h | h
        · exact mcHash_stable c _ n m i h hC
        · exact (mcHash_stable c _ n m i h ht').symm
      rw [hta.2, htb.2, key ta hta.1, key tb htb.1]
  simpa using h

private theorem length_bits_le_iff (a j : ℕ) : (Nat.bits a).length ≤ j ↔ a < 2 ^ j := by
  rw [Nat.size_eq_bits_len, Nat.size_le]

private theorem length_bits_lt_two_pow (a : ℕ) : a < 2 ^ (Nat.bits a).length := by
  rw [Nat.size_eq_bits_len]; exact Nat.lt_size_self a

private theorem length_bits_le_self_succ (a : ℕ) : (Nat.bits a).length ≤ a + 1 := by
  rw [length_bits_le_iff]
  calc a < a + 1 := by omega
    _ < 2 ^ (a + 1) := Nat.lt_two_pow_self

private theorem length_bits_add_le (a b : ℕ) :
    (Nat.bits (a + b)).length ≤ (Nat.bits a).length + b := by
  rw [length_bits_le_iff, pow_add]
  have h1 := length_bits_lt_two_pow a
  have h2 : b + 1 ≤ 2 ^ b := Nat.lt_two_pow_self
  have h3 : 1 ≤ 2 ^ (Nat.bits a).length := Nat.one_le_two_pow
  nlinarith

private theorem length_bits_mul_le (a b : ℕ) :
    (Nat.bits (a * b)).length ≤ (Nat.bits a).length + (Nat.bits b).length := by
  rw [length_bits_le_iff, pow_add]
  exact Nat.mul_lt_mul'' (length_bits_lt_two_pow a) (length_bits_lt_two_pow b)

private theorem length_mcW (n m k e i : ℕ) : (mcW n m k e i).length = 2 * (Nat.bits n).length +
    2 * (Nat.bits m).length + 2 * (Nat.bits k).length + 2 * (Nat.bits e).length +
    (Nat.bits i).length + 4 := by
  simp only [mcW, length_pairCode]
  omega

private theorem length_bits_N_le (d n m c₀ : ℕ) (hm : m ≤ n + c₀) :
    (Nat.bits (d * (m + n + 2))).length ≤ (Nat.bits d).length + (Nat.bits n).length + c₀ + 4 := by
  have h1 := length_bits_mul_le d (m + n + 2)
  have h2 : (Nat.bits (m + n + 2)).length ≤ (Nat.bits (2 * n)).length + (c₀ + 2) :=
    le_trans (length_bits_mono (by omega)) (length_bits_add_le (2 * n) (c₀ + 2))
  have h3 := length_bits_mul_le 2 n
  have h4 : (Nat.bits 2).length = 2 := by decide
  omega

private theorem length_mcW_le (d n m k e i c₀ : ℕ) (hm : m ≤ n + c₀) (hk : k ≤ m)
    (hi : i < d * (m + n + 2)) : (mcW n m k e i).length ≤
      7 * (Nat.bits n).length + 5 * c₀ + (Nat.bits d).length + 8 + 2 * (Nat.bits e).length := by
  rw [length_mcW]
  have h1 : (Nat.bits m).length ≤ (Nat.bits n).length + c₀ :=
    le_trans (length_bits_mono hm) (length_bits_add_le n c₀)
  have h2 : (Nat.bits k).length ≤ (Nat.bits m).length := length_bits_mono hk
  have h3 : (Nat.bits i).length ≤ (Nat.bits (d * (m + n + 2))).length := length_bits_mono hi.le
  have h4 := length_bits_N_le d n m c₀ hm
  omega

private theorem exists_large_E (a b : ℕ) : ∃ E : ℕ, a + b * (Nat.bits E).length ≤ E := by
  refine ⟨(a + 3 * b + 1) ^ 2, ?_⟩
  have h := bits_length_le_sqrt_add_two ((a + 3 * b + 1) ^ 2)
  rw [Nat.sqrt_eq'] at h
  have : b * (Nat.bits ((a + 3 * b + 1) ^ 2)).length ≤ b * (a + 3 * b + 1 + 2) :=
    Nat.mul_le_mul_left _ h
  nlinarith

private theorem logSlack_le_mul (c w : ℕ) : logSlack c w ≤ c * (w + 1) + c := by
  unfold logSlack
  have := length_bits_le_self_succ w
  have := Nat.mul_le_mul_left c this
  omega

private theorem length_bits_e_le (E n : ℕ) : (Nat.bits (E * ((Nat.bits n).length + 1))).length ≤
    (Nat.bits E).length + (Nat.bits n).length + 2 :=
  le_trans (length_bits_mul_le _ _)
    (by have := length_bits_le_self_succ ((Nat.bits n).length + 1); omega)

private theorem mcSlack_contra (k e cB W S c₁ L β B E : ℕ) (hnat : k ≤ k - e + 1 + cB + W + S)
    (hek : e < k) (hls : S ≤ c₁ * (W + 1) + c₁) (hw : W ≤ 9 * L + β + 2 * B)
    (hE : (c₁ + 1) * (9 + β) + cB + 2 * c₁ + 2 + 2 * (c₁ + 1) * B ≤ E)
    (he : e = E * (L + 1)) : False := by
  have h1 : e ≤ 1 + cB + W + S := by omega
  have hmul : (c₁ + 1) * W ≤ (c₁ + 1) * (9 * L + β + 2 * B) := Nat.mul_le_mul_left _ hw
  have hE9 : 9 * (c₁ + 1) ≤ E := by nlinarith
  have hEL : 9 * (c₁ + 1) * L ≤ E * L := Nat.mul_le_mul_right _ hE9
  subst he
  nlinarith

private theorem exists_E_not_mem_mcBad (D : Map) (hD : isOptimalConditional D) (c : Code) (d : ℕ)
    (hd : 0 < d) (c₀ : ℕ) : ∃ E : ℕ, ∀ (n m k t : ℕ) (A C : BitString), m ≤ n + c₀ → k ≤ m →
      condK D C A = (k : ℕ∞) →
      C ∉ mcBad c d (mcTable d n m) n m k (E * ((Nat.bits n).length + 1)) t A := by
  obtain ⟨cB, hcB⟩ := condK_le_of_mem_mcBad D hD c d hd
  obtain ⟨c₁, hc₁⟩ := condK_le_condK_cond_map_add_length D hD pairCode pairCode_primrec
  set β := 5 * c₀ + (Nat.bits d).length + 12 with hβ
  obtain ⟨E, hE⟩ := exists_large_E ((c₁ + 1) * (9 + β) + cB + 2 * c₁ + 2) (2 * (c₁ + 1))
  refine ⟨E, fun n m k t A C hm hk hCA hbad => ?_⟩
  set L := (Nat.bits n).length with hL
  set e := E * (L + 1) with he
  obtain ⟨hek, hK⟩ := hcB n m k e t A C hk hbad
  set w := mcW n m k e 0 with hw
  have h1 := hc₁ C A w
  have hlen := length_mcW_le d n m k e 0 c₀ hm hk (Nat.mul_pos hd (by omega))
  rw [← hw] at hlen
  have hbe : (Nat.bits e).length ≤ (Nat.bits E).length + L + 2 := length_bits_e_le E n
  have hls := logSlack_le_mul c₁ w.length
  have hnat : k ≤ (k - e + 1 + cB) + w.length + logSlack c₁ w.length := by
    have h2 : (k : ℕ∞) ≤ (((k - e + 1 + cB) + w.length + logSlack c₁ w.length : ℕ) : ℕ∞) := by
      rw [← hCA]
      refine h1.trans ?_
      push_cast
      gcongr
      exact_mod_cast hK
    exact_mod_cast h2
  exact mcSlack_contra k e cB w.length (logSlack c₁ w.length) c₁ L β (Nat.bits E).length E
    hnat hek hls (by omega) hE rfl

private theorem condK_nil_le_const (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ C : BitString, condK D [] C ≤ (c : ℕ∞) := by
  let D' : Map := fun _ => Part.some []
  have hD' : isDecompressor D' := (Computable.const ([] : BitString)).partrec
  obtain ⟨c, hc⟩ := hD.2 D' hD'
  refine ⟨c, fun C => (hc [] C).trans ?_⟩
  have h0 : condK D' [] C ≤ ((0 : ℕ) : ℕ∞) :=
    (condK_le_iff D' [] C 0).2 ⟨[], le_rfl, Part.mem_some _⟩
  simpa using add_le_add_left h0 (c : ℕ∞)

private theorem exists_stage_mem_mcS {D : Map} {c : Code} (hc : IsCodeFor c D) {A C : BitString}
    {k n tC : ℕ} (hk : condK D C A ≤ (k : ℕ∞)) (htC : C ∈ boundedOutputStage c n tC) :
    ∃ t, tC ≤ t ∧ C ∈ mcS c A k n t := by
  obtain ⟨p, hp, hprod⟩ := (condK_le_iff D C A k).1 hk
  obtain ⟨t₁, ht₁⟩ := conditionalRunOut_complete hc hprod
  have hsnap := mem_conditionalOutputSnapshot_of_run hp ht₁
  refine ⟨max t₁ tC, le_max_right _ _, ?_⟩
  unfold mcS
  simp only [List.mem_filter, decide_eq_true_eq]
  exact ⟨mem_conditionalOutputSnapshot_mono (le_max_left _ _) hsnap,
    (boundedOutputStage_prefix_of_le c n (le_max_right _ _)).subset htC⟩

private theorem condK_le_of_pairCode_context {D : Map} {c₁ : ℕ}
    (hc₁ : ∀ x y w : BitString,
      condK D x y ≤ condK D x (pairCode w y) + (w.length : ℕ∞) + (logSlack c₁ w.length : ℕ∞))
    {x y w : BitString} {a : ℕ} (h : condK D x (pairCode w y) ≤ (a : ℕ∞)) :
    condK D x y ≤ ((a + w.length + logSlack c₁ w.length : ℕ) : ℕ∞) := by
  refine (hc₁ x y w).trans ?_
  push_cast
  gcongr

private theorem mcSlack_enc (cE W S c₁ L β cF : ℕ) (hS : S ≤ c₁ * (W + 1) + c₁) (hW : W ≤ 9 * L + β)
    (hcF : cE + (c₁ + 1) * (9 + β) + 2 * c₁ ≤ cF) : cE + W + S ≤ cF * L + cF := by
  have hmul : (c₁ + 1) * W ≤ (c₁ + 1) * (9 * L + β) := Nat.mul_le_mul_left _ hW
  have h9 : 9 * (c₁ + 1) ≤ cF := by nlinarith
  have h9L : 9 * (c₁ + 1) * L ≤ cF * L := Nat.mul_le_mul_right _ h9
  nlinarith

private theorem mcSlack_dec (cM BT W S c₁ L β B E d cF : ℕ) (hS : S ≤ c₁ * (W + 1) + c₁)
    (hW : W ≤ 9 * L + β + 2 * B) (hT : BT ≤ β + L + d + 3 + E * (L + 1))
    (hcF : cM + β + d + 4 + E + (c₁ + 1) * (9 + β + 2 * B) + 2 * c₁ ≤ cF) :
    BT + cM + W + S ≤ cF * L + cF := by
  have hmul : (c₁ + 1) * W ≤ (c₁ + 1) * (9 * L + β + 2 * B) := Nat.mul_le_mul_left _ hW
  have h9 : E + 1 + 9 * (c₁ + 1) ≤ cF := by nlinarith
  have h9L : (E + 1 + 9 * (c₁ + 1)) * L ≤ cF * L := Nat.mul_le_mul_right _ h9
  nlinarith

private theorem exists_manyConditionCode_pos (D : Map) (hD : isOptimalConditional D) (d : ℕ)
    (hd : 0 < d) :
    ∃ c : ℕ, ∀ (n k : ℕ) (A : Fin d → BitString) (C : BitString),
      plainK D C ≤ (n : ℕ∞) → (∀ i, condK D C (A i) ≤ (k : ℕ∞)) →
      ∃ X : BitString, X.length ≤ k + logSlack c n ∧
        condK D X C ≤ (logSlack c n : ℕ∞) ∧
        ∀ i, condK D C (pairCode (A i) X) ≤ (logSlack c n : ℕ∞) := by
  obtain ⟨c, hc⟩ := Dovetailing.exists_isCodeFor hD
  obtain ⟨c₀, hc₀⟩ := condK_le_plainK D hD
  obtain ⟨E, hE⟩ := exists_E_not_mem_mcBad D hD c d hd c₀
  obtain ⟨cM, hcM⟩ := condK_le_of_mem_mcMatch D hD c d
  obtain ⟨cE, hcE⟩ := condK_le_of_mcEnc D hD c d
  obtain ⟨c₁, hc₁⟩ := condK_le_condK_cond_map_add_length D hD pairCode pairCode_primrec
  set β := 5 * c₀ + (Nat.bits d).length + 12 with hβ
  set B := (Nat.bits E).length with hB
  refine ⟨cE + cM + β + d + 4 + E + (c₁ + 1) * (9 + β + 2 * B) + 2 * c₁,
    fun n k A C hC hCA => ?_⟩
  set L := (Nat.bits n).length with hL
  set e := E * (L + 1) with he
  set m := min k (n + c₀) with hmdef
  have hm : m ≤ n + c₀ := min_le_right _ _
  have hmk : m ≤ k := min_le_left _ _
  have hfin : ∀ j, condK D C (A j) ≠ ⊤ := fun j =>
    ne_top_of_le_ne_top (ENat.natCast_ne_top k) (hCA j)
  set kj : Fin d → ℕ := fun j => (condK D C (A j)).toNat with hkjdef
  have hkj : ∀ j, condK D C (A j) = (kj j : ℕ∞) := fun j =>
    (ENat.natCast_toNat (hfin j)).symm
  have hkjm : ∀ j, kj j ≤ m := by
    intro j
    refine le_min ?_ ?_
    · have := hCA j
      rw [hkj j] at this
      exact_mod_cast this
    · have := (hc₀ C (A j)).trans (add_le_add_left hC _)
      rw [hkj j] at this
      exact_mod_cast this
  obtain ⟨tC, htC⟩ := (Dovetailing.exists_stage_mem_iff_plainK_le hc n C).2 hC
  have hgood : ∀ j t, C ∉ mcBad c d (mcTable d n m) n m (kj j) e t (A j) := fun j t =>
    hE n m (kj j) t (A j) C hm (hkjm j) (hkj j)
  obtain ⟨i, hi, hcnt⟩ := exists_common_good_index c d (mcTable d n m) n m e kj A C htC hgood hd
  set v := mcHash c (mcTable d n m) n m tC i C with hv
  refine ⟨Nat.bits v, ?_, ?_, fun j => ?_⟩
  · have : (Nat.bits v).length ≤ m := (length_bits_le_iff _ _).2 (Nat.mod_lt _ (by positivity))
    omega
  · have h1 := condK_le_of_pairCode_context hc₁ (hcE n m i tC C htC)
    have hlen := length_mcW_le d n m 0 0 i c₀ hm (Nat.zero_le _) hi
    have h0 : (Nat.bits 0).length = 0 := rfl
    refine h1.trans ?_
    unfold logSlack
    have hwA : (mcW n m 0 0 i).length ≤ 9 * L + β := by omega
    exact_mod_cast mcSlack_enc cE _ _ c₁ L β _ (logSlack_le_mul c₁ _) hwA
      (by nlinarith)
  · obtain ⟨t, htt, htS⟩ := exists_stage_mem_mcS hc (le_of_eq (hkj j)) htC
    have hmatch : C ∈ mcMatch c (mcTable d n m) n m (kj j) t (A j) i v := by
      rw [mem_mcMatch_iff]
      exact ⟨htS, mcHash_stable c _ n m i htt htC⟩
    have h1 := condK_le_of_pairCode_context hc₁ (hcM n m (kj j) e i t v (A j) C hi hmatch (hcnt j))
    have hlen := length_mcW_le d n m (kj j) e i c₀ hm (hkjm j) hi
    have hbe : (Nat.bits e).length ≤ B + L + 2 := length_bits_e_le E n
    have hT : (Nat.bits (d * (m + n + 2) * 2 ^ (d + 2 + e))).length ≤ β + L + d + 3 + e := by
      have h2 := length_bits_mul_le (d * (m + n + 2)) (2 ^ (d + 2 + e))
      have h3 := length_bits_N_le d n m c₀ hm
      rw [length_bits_two_pow] at h2
      omega
    refine h1.trans ?_
    unfold logSlack
    have hwB : (mcW n m (kj j) e i).length ≤ 9 * L + β + 2 * B := by omega
    have hcf : cM + β + d + 4 + E + (c₁ + 1) * (9 + β + 2 * B) + 2 * c₁ ≤
        cE + cM + β + d + 4 + E + (c₁ + 1) * (9 + β + 2 * B) + 2 * c₁ := by omega
    exact_mod_cast mcSlack_dec cM _ _ _ c₁ L β B E d _ (logSlack_le_mul c₁ _) hwB hT
      hcf

end ManyConditionsCode

/-- The same result for any fixed number `d` of conditions: one message of length
`k + O(log n)`, simple given `C`, serves `d` decoders, the `i`-th of them knowing `A i`.  The
constant depends on `d`, which is why it is quantified after it; the book also mentions
"polynomially many" conditions, which would need a constant uniform in `d`.

SUV Problem 325, p. 383. -/
theorem exists_manyConditionCode (D : Map) (hD : isOptimalConditional D) (d : ℕ) :
    ∃ c : ℕ, ∀ (n k : ℕ) (A : Fin d → BitString) (C : BitString),
      (∀ i, plainK D (A i) ≤ (n : ℕ∞)) → plainK D C ≤ (n : ℕ∞) → 0 < k →
      (∀ i, condK D C (A i) ≤ (k : ℕ∞)) →
      ∃ X : BitString, X.length ≤ k + logSlack c n ∧
        condK D X C ≤ (logSlack c n : ℕ∞) ∧
        ∀ i, condK D C (pairCode (A i) X) ≤ (logSlack c n : ℕ∞) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · obtain ⟨c, hc⟩ := condK_nil_le_const D hD
    refine ⟨c, fun n k A C _ _ _ _ => ⟨[], by simp, (hc C).trans ?_, fun i => i.elim0⟩⟩
    have : c ≤ logSlack c n := by unfold logSlack; omega
    exact_mod_cast this
  · obtain ⟨c, hc⟩ := exists_manyConditionCode_pos D hD d hd
    exact ⟨c, fun n k A C _ hC _ hCA => hc n k A C hC hCA⟩

/-- There is no universal fingerprint: for every constant `c` there are `n` and an
incompressible string `A` of length `n` such that no string `X` of length at most `n/2` lets
one restore `A` from every `B` with `C(A|B) ≤ n/2` — some such `B` (for instance `X` itself)
defeats it.

SUV Section 12.7, p. 383 (unnumbered remark). -/
theorem not_exists_universalFingerprint (D : Map) (hD : isOptimalConditional D) (c : ℕ) :
    ∃ (n : ℕ) (A : BitString), A.length = n ∧ (n : ℕ∞) ≤ plainK D A ∧
      ∀ X : BitString, X.length ≤ n / 2 →
        ∃ B : BitString, condK D A B ≤ ((n / 2 : ℕ) : ℕ∞) ∧
          ¬ condK D A (pairCode X B) ≤ (logSlack c n : ℕ∞) := by
  -- the recodings of the condition used below
  obtain ⟨cS, hS⟩ := condK_self D hD
  obtain ⟨c₁, h₁⟩ := condK_le_condK_cond_map_add_length D hD (fun w y => y ++ w)
    (Primrec.list_append.comp Primrec.snd Primrec.fst)
  obtain ⟨c₂, h₂⟩ := condK_le_condK_cond_map_add_length D hD
    (fun w y => pairCode (decodeFirst y) (decodeSecond y ++ w))
    (pairCode_primrec.comp (decodeFirst_primrec.comp Primrec.snd)
      (Primrec.list_append.comp (decodeSecond_primrec.comp Primrec.snd) Primrec.fst))
  obtain ⟨c₃, h₃⟩ := condK_le_condK_cond_map_add_length D hD (fun w _ => w) Primrec.fst
  obtain ⟨c₄, h₄⟩ := condK_le_condK_cond_map_add_length D hD (fun w y => pairCode y w)
    (pairCode_primrec.comp Primrec.snd Primrec.fst)
  obtain ⟨cDup, hDup⟩ := condK_cond_comp_le D hD (fun y => pairCode (decodeFirst y) y)
    (pairCode_primrec.comp decodeFirst_primrec Primrec.id).to_comp
  -- the scale: `n = 8 N` with `N = 2 ^ (2 u)` a power of two so large that every slack is small
  obtain ⟨K, hK⟩ : ∃ K, K = c + c₁ + c₂ + c₃ + c₄ + cS + cDup + 1 := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u, u = 29 * K := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N, N = 2 ^ (2 * u) := ⟨_, rfl⟩
  obtain ⟨S, hSdef⟩ : ∃ S, S = K * (2 * u + 4) + K := ⟨_, rfl⟩
  have hbits : (Nat.bits (8 * N)).length = 2 * u + 4 := by
    rw [Nat.size_eq_bits_len, hN, show 8 * 2 ^ (2 * u) = 2 ^ (2 * u + 3) by ring, Nat.size_pow]
  have hslack : ∀ c' m, c' ≤ K → m ≤ 8 * N → (logSlack c' m : ℕ∞) ≤ (S : ℕ∞) := by
    intro c' m hc' hm
    have : logSlack c' m ≤ S :=
      calc logSlack c' m ≤ logSlack c' (8 * N) := logSlack_mono_right c' hm
        _ = c' * (2 * u + 4) + c' := by rw [logSlack, hbits]
        _ ≤ S := by rw [hSdef]; nlinarith
    exact_mod_cast this
  have hbig : 4 * S + K < N := by
    have hu1 : u + 1 ≤ 2 ^ u := Nat.lt_two_pow_self
    rw [hN, two_mul, pow_add, hSdef]
    subst hu
    generalize 2 ^ (29 * K) = M at hu1 ⊢
    nlinarith [Nat.mul_le_mul hu1 hu1]
  obtain ⟨A, hAlen, hA⟩ := exists_incompressible_string D [] (8 * N)
  refine ⟨8 * N, A, hAlen, hA, fun X hX => ?_⟩
  have hX' : X.length ≤ 4 * N := by omega
  have hAtake : ∀ m, m ≤ 8 * N → (A.take m).length = m := fun m hm => by
    rw [List.length_take, hAlen]; omega
  -- the prefix of `A` of length `5 N` is a condition of the required strength
  have hB₁ : condK D A (A.take (5 * N)) ≤ ((8 * N / 2 : ℕ) : ℕ∞) := by
    have h := h₁ A (A.take (5 * N)) (A.drop (5 * N))
    simp only [List.take_append_drop] at h
    have hdl : (A.drop (5 * N)).length = 3 * N := by rw [List.length_drop, hAlen]; omega
    rw [hdl] at h
    have hs := hslack c₁ (3 * N) (by omega) (by omega)
    have hself := hS A
    calc condK D A (A.take (5 * N))
        ≤ condK D A A + ((3 * N : ℕ) : ℕ∞) + (logSlack c₁ (3 * N) : ℕ∞) := h
      _ ≤ (cS : ℕ∞) + ((3 * N : ℕ) : ℕ∞) + (S : ℕ∞) := by gcongr
      _ ≤ ((8 * N / 2 : ℕ) : ℕ∞) := by norm_cast; omega
  by_cases hcase : condK D A (pairCode X (A.take (5 * N))) ≤ (logSlack c (8 * N) : ℕ∞)
  · -- `X` serves the long prefix, so it cannot serve `X` together with the short prefix
    refine ⟨pairCode X (A.take (3 * N)), ?_, ?_⟩
    · have h := h₂ A (pairCode X (A.take (3 * N))) ((A.take (5 * N)).drop (3 * N))
      simp only [decodeFirst_pairCode, decodeSecond_pairCode] at h
      have hjoin : A.take (3 * N) ++ (A.take (5 * N)).drop (3 * N) = A.take (5 * N) := by
        conv_lhs => rw [show A.take (3 * N) = (A.take (5 * N)).take (3 * N) by
          rw [List.take_take, min_eq_left (by omega)]]
        exact List.take_append_drop _ _
      have hwl : ((A.take (5 * N)).drop (3 * N)).length = 2 * N := by
        rw [List.length_drop, List.length_take, hAlen]; omega
      rw [hjoin, hwl] at h
      have hs := hslack c₂ (2 * N) (by omega) (by omega)
      have hs' := hslack c (8 * N) (by omega) le_rfl
      calc condK D A (pairCode X (A.take (3 * N)))
          ≤ condK D A (pairCode X (A.take (5 * N))) + ((2 * N : ℕ) : ℕ∞)
              + (logSlack c₂ (2 * N) : ℕ∞) := h
        _ ≤ (S : ℕ∞) + ((2 * N : ℕ) : ℕ∞) + (S : ℕ∞) := by
          gcongr
          exact hcase.trans hs'
        _ ≤ ((8 * N / 2 : ℕ) : ℕ∞) := by norm_cast; omega
    · intro hbad
      have hdup : condK D A (pairCode X (A.take (3 * N))) ≤
          condK D A (pairCode X (pairCode X (A.take (3 * N)))) + (cDup : ℕ∞) := by
        simpa [decodeFirst_pairCode] using hDup A (pairCode X (A.take (3 * N)))
      have hlow1 : condK D A [] ≤ condK D A X + (X.length : ℕ∞) + (logSlack c₃ X.length : ℕ∞) :=
        h₃ A [] X
      have hlow2 : condK D A X ≤ condK D A (pairCode X (A.take (3 * N)))
          + ((3 * N : ℕ) : ℕ∞) + (logSlack c₄ (3 * N) : ℕ∞) := by
        have := h₄ A X (A.take (3 * N))
        rwa [hAtake (3 * N) (by omega)] at this
      have hs1 := hslack c₃ X.length (by omega) (by omega)
      have hs2 := hslack c₄ (3 * N) (by omega) (by omega)
      have hs' := hslack c (8 * N) (by omega) le_rfl
      have hfin : ((8 * N : ℕ) : ℕ∞) ≤ ((S + cDup + 3 * N + S + X.length + S : ℕ) : ℕ∞) := by
        calc ((8 * N : ℕ) : ℕ∞) ≤ plainK D A := hA
          _ = condK D A [] := rfl
          _ ≤ condK D A X + (X.length : ℕ∞) + (logSlack c₃ X.length : ℕ∞) := hlow1
          _ ≤ condK D A (pairCode X (A.take (3 * N))) + ((3 * N : ℕ) : ℕ∞)
              + (logSlack c₄ (3 * N) : ℕ∞) + (X.length : ℕ∞)
              + (logSlack c₃ X.length : ℕ∞) := by gcongr
          _ ≤ condK D A (pairCode X (pairCode X (A.take (3 * N)))) + (cDup : ℕ∞)
              + ((3 * N : ℕ) : ℕ∞) + (logSlack c₄ (3 * N) : ℕ∞) + (X.length : ℕ∞)
              + (logSlack c₃ X.length : ℕ∞) := by gcongr
          _ ≤ (logSlack c (8 * N) : ℕ∞) + (cDup : ℕ∞) + ((3 * N : ℕ) : ℕ∞)
              + (logSlack c₄ (3 * N) : ℕ∞) + (X.length : ℕ∞)
              + (logSlack c₃ X.length : ℕ∞) := by gcongr
          _ ≤ (S : ℕ∞) + (cDup : ℕ∞) + ((3 * N : ℕ) : ℕ∞) + (S : ℕ∞) + (X.length : ℕ∞)
              + (S : ℕ∞) := by gcongr
          _ = ((S + cDup + 3 * N + S + X.length + S : ℕ) : ℕ∞) := by push_cast; ring
      have : 8 * N ≤ S + cDup + 3 * N + S + X.length + S := by exact_mod_cast hfin
      omega
  · exact ⟨A.take (5 * N), hB₁, hcase⟩

private lemma not_exists_universalFingerprintFamily_bounds (d K P u N S : ℕ)
    (hK1 : 1 ≤ K) (hP1 : 1 ≤ P) (hP : P = K * (d + 1) ^ 2) (hu : u = 29 * P) (hN : N = 2 ^ (3 * u))
    (hSdef : S = K * (3 * u + 7) + K) (hQ1 : 1 ≤ (d + 1) ^ 2) :
    5 * (d + 1) ^ 2 * S ≤ N ∧ 5 * S ≤ N ∧ (4 * d + 3) * (4 * d + 2) * S ≤ 4 * N ∧
    (4 * d + 3) * S ≤ N ∧ d * (4 * d + 3) * S ≤ N ∧ d ≤ N := by
  have hbig : 5 * (d + 1) ^ 2 * S ≤ N := by
    have hu1 : u + 1 ≤ 2 ^ u := Nat.lt_two_pow_self
    have hS' : 5 * (d + 1) ^ 2 * S ≤ 475 * P * P := by
      have hPP : P * 1 ≤ P * P := Nat.mul_le_mul_left P hP1
      have hQK : (d + 1) ^ 2 * K = P := by rw [hP]; ring
      rw [hSdef, hu]
      calc 5 * (d + 1) ^ 2 * (K * (3 * (29 * P) + 7) + K)
        = 435 * ((d + 1) ^ 2 * K) * P + 40 * ((d + 1) ^ 2 * K) := by ring
      _ = 435 * P * P + 40 * P := by rw [hQK]
      _ ≤ 475 * P * P := by linarith only [hPP]
    rw [hN, show 3 * u = u + u + u by ring, pow_add, pow_add]
    generalize 2 ^ u = M at hu1 ⊢
    have hM : 29 * P ≤ M := by omega
    calc 5 * (d + 1) ^ 2 * S ≤ 475 * P * P := hS'
    _ ≤ 475 * (P * P * P) := by
        have := Nat.mul_le_mul_left (P * P) hP1
        rw [Nat.mul_one] at this
        linarith only [this]
    _ ≤ (29 * P) * (29 * P) * (29 * P) := by ring_nf; omega
    _ ≤ M * M * M := by gcongr
  have hN1 : 5 * S ≤ N := by
    have h := Nat.mul_le_mul_right S (Nat.mul_le_mul_left 5 hQ1)
    rw [Nat.mul_one] at h
    exact h.trans hbig
  have hTS : (4 * d + 3) * (4 * d + 2) * S ≤ 4 * N := by
    have h1 : (4 * d + 3) * (4 * d + 2) ≤ 4 * (5 * (d + 1) ^ 2) := by
      nlinarith only [Nat.zero_le d]
    calc
      (4 * d + 3) * (4 * d + 2) * S ≤ 4 * (5 * (d + 1) ^ 2) * S :=
        Nat.mul_le_mul_right S h1
    _ = 4 * (5 * (d + 1) ^ 2 * S) := by ring
    _ ≤ 4 * N := Nat.mul_le_mul_left 4 hbig
  have hdS : (4 * d + 3) * S ≤ N := by
    have h1 : 4 * d + 3 ≤ 5 * (d + 1) ^ 2 := by nlinarith only [Nat.zero_le d]
    exact (Nat.mul_le_mul_right S h1).trans hbig
  have hd2S : d * (4 * d + 3) * S ≤ N := by
    have h1 : d * (4 * d + 3) ≤ 5 * (d + 1) ^ 2 := by nlinarith only [Nat.zero_le d]
    exact (Nat.mul_le_mul_right S h1).trans hbig
  have hdN : d ≤ N := by
    have h1 : d ≤ (4 * d + 3) * S := by
      have := Nat.le_mul_of_pos_right (4 * d + 3) (show 0 < S by omega)
      omega
    exact h1.trans hdS
  exact ⟨hbig, hN1, hTS, hdS, hd2S, hdN⟩

/-- No fixed number `d` of fingerprints suffices either: some `B` with `C(A|B) ≤ n/2` is
served by none of them.

The problem leaves the exact quantifiers to the reader; the form below is the one of the
preceding remark, with a `d`-tuple of fingerprints of length at most `n/2` in place of the
single string `X`.

SUV Problem 326, p. 383. -/
theorem not_exists_universalFingerprintFamily (D : Map) (hD : isOptimalConditional D)
    (d c : ℕ) :
    ∃ (n : ℕ) (A : BitString), A.length = n ∧ (n : ℕ∞) ≤ plainK D A ∧
      ∀ X : Fin d → BitString, (∀ i, (X i).length ≤ n / 2) →
        ∃ B : BitString, condK D A B ≤ ((n / 2 : ℕ) : ℕ∞) ∧
          ∀ i, ¬ condK D A (pairCode (X i) B) ≤ (logSlack c n : ℕ∞) := by
  obtain ⟨cS, hS⟩ := condK_self D hD
  obtain ⟨c₁, h₁⟩ := condK_fingerprintLadder_le_condK_self (d := d) D hD
  obtain ⟨c₂, h₂⟩ := condK_fingerprintLadder_le_condK_pair_fingerprintLadder (d := d) D hD
  obtain ⟨c₃, h₃⟩ := plainK_le_condK_pair_fingerprintLadder (d := d) D hD
  -- the scale: `n = 8 N` with `N` a power of two so large that every slack `S` is tiny
  obtain ⟨K, hK⟩ : ∃ K, K = c + cS + c₁ + c₂ + c₃ + 1 := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P, P = K * (d + 1) ^ 2 := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u, u = 29 * P := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N, N = 2 ^ (3 * u) := ⟨_, rfl⟩
  obtain ⟨S, hSdef⟩ : ∃ S, S = K * (3 * u + 7) + K := ⟨_, rfl⟩
  have hbits : (Nat.bits (64 * N)).length = 3 * u + 7 := by
    rw [Nat.size_eq_bits_len, hN, show 64 * 2 ^ (3 * u) = 2 ^ (3 * u + 6) by ring, Nat.size_pow]
  have hslack : ∀ c' m, c' ≤ K → m ≤ 64 * N → (logSlack c' m : ℕ∞) ≤ (S : ℕ∞) := by
    intro c' m hc' hm
    have : logSlack c' m ≤ S :=
      calc logSlack c' m ≤ logSlack c' (64 * N) := logSlack_mono_right c' hm
        _ = c' * (3 * u + 7) + c' := by rw [logSlack, hbits]
        _ ≤ S := by rw [hSdef]; exact Nat.add_le_add (Nat.mul_le_mul_right _ hc') hc'
    exact_mod_cast this
  have hK1 : 1 ≤ K := by omega
  have hQ1 : 1 ≤ (d + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hP1 : 1 ≤ P := by rw [hP]; simpa using Nat.mul_le_mul hK1 hQ1
  have hSK : K ≤ S := by rw [hSdef]; exact Nat.le_add_left K _
  obtain ⟨hbig, hN1, hTS, hdS, hd2S, hdN⟩ :=
    not_exists_universalFingerprintFamily_bounds d K P u N S hK1 hP1 hP hu hN hSdef hQ1
  obtain ⟨A, hAlen, hA⟩ := exists_incompressible_string D [] (8 * N)
  refine ⟨8 * N, A, hAlen, hA, fun X hX => ?_⟩
  have hX' : ∀ j, (X j).length ≤ 4 * N := fun j => by have := hX j; omega
  have hε : (logSlack c (8 * N) : ℕ∞) ≤ (S : ℕ∞) := hslack c _ (by omega) (by omega)
  have hAself : condK D A A ≤ (S : ℕ∞) := (hS A).trans (by exact_mod_cast (show cS ≤ S by omega))
  rw [show 8 * N / 2 = 4 * N by omega]
  -- the ladder: rung `t` holds the `2 S t`-bit prefixes of the fingerprints and the first
  -- `m₀ - S t (t - 1)` bits of `A`; each rung is either the required `B` or served by some
  -- fingerprint, in which case the next rung is again a condition of strength `n / 2`
  set m₀ := 4 * N + 2 * S with hm₀
  suffices h : ∀ t, t ≤ 4 * d + 3 →
      (∃ B : BitString, condK D A B ≤ ((4 * N : ℕ) : ℕ∞) ∧
        ∀ i, ¬ condK D A (pairCode (X i) B) ≤ (logSlack c (8 * N) : ℕ∞)) ∨
      condK D A (fingerprintLadder A X (2 * S * t) (m₀ - S * (t * (t - 1)))) ≤
        ((4 * N : ℕ) : ℕ∞) by
    rcases h (4 * d + 3) le_rfl with hw | hT
    · exact hw
    by_cases hserve : ∀ j, ¬ condK D A (pairCode (X j)
        (fingerprintLadder A X (2 * S * (4 * d + 3)) (m₀ - S * ((4 * d + 3) * (4 * d + 3 - 1)))))
        ≤ (logSlack c (8 * N) : ℕ∞)
    · exact ⟨_, hT, hserve⟩
    push Not at hserve
    obtain ⟨j, hj⟩ := hserve
    exfalso
    -- the top rung is served: `A` would be too simple
    set i := 2 * S * (4 * d + 3) with hi
    set m := m₀ - S * ((4 * d + 3) * (4 * d + 3 - 1)) with hm
    have hprod : S * ((4 * d + 3) * (4 * d + 3 - 1)) = (4 * d + 3) * (4 * d + 2) * S := by
      rw [show 4 * d + 3 - 1 = 4 * d + 2 by omega]; ring
    have hmle : m ≤ A.length := by rw [hAlen]; omega
    have hmeq : m + (4 * d + 3) * (4 * d + 2) * S = m₀ := by rw [hm, hprod]; omega
    have hdi : d * (2 * i + 1) = 4 * (d * (4 * d + 3) * S) + d := by rw [hi]; ring
    have hs := hslack c₃ (3 * ((X j).length + m + d * (2 * i + 1)) + 2) (by omega)
      (by have := hX' j; omega)
    have hfin : ((8 * N : ℕ) : ℕ∞) ≤
        ((S + ((X j).length + m + d * (2 * i + 1)) + S : ℕ) : ℕ∞) := by
      calc ((8 * N : ℕ) : ℕ∞) ≤ plainK D A := hA
        _ ≤ condK D A (pairCode (X j) (fingerprintLadder A X i m)) +
            (((X j).length + m + d * (2 * i + 1) : ℕ) : ℕ∞) +
            (logSlack c₃ (3 * ((X j).length + m + d * (2 * i + 1)) + 2) : ℕ∞) := h₃ A X j i m hmle
        _ ≤ (S : ℕ∞) + (((X j).length + m + d * (2 * i + 1) : ℕ) : ℕ∞) + (S : ℕ∞) :=
            add_le_add (add_le_add (hj.trans hε) le_rfl) hs
        _ = _ := by push_cast; ring
    have hfin' : 8 * N ≤ S + ((X j).length + m + d * (2 * i + 1)) + S := by exact_mod_cast hfin
    have hdS1 : d ≤ d * S := Nat.le_mul_of_pos_right d (by omega)
    have hexp : (4 * d + 3) * (4 * d + 2) * S =
        4 * (d * (4 * d + 3) * S) + 8 * (d * S) + 6 * S := by ring
    have hXj := hX' j
    omega
  intro t
  induction t with
  | zero =>
    intro _
    right
    have h := h₁ A X 0 m₀
    have hdl : (A.drop m₀).length = 4 * N - 2 * S := by rw [List.length_drop, hAlen]; omega
    rw [hdl] at h
    have hs := hslack c₁ (4 * N - 2 * S) (by omega) (by omega)
    simp only [Nat.mul_zero, Nat.zero_mul, Nat.sub_zero]
    calc condK D A (fingerprintLadder A X 0 m₀)
        ≤ condK D A A + ((4 * N - 2 * S : ℕ) : ℕ∞) + (logSlack c₁ (4 * N - 2 * S) : ℕ∞) := h
      _ ≤ (S : ℕ∞) + ((4 * N - 2 * S : ℕ) : ℕ∞) + (S : ℕ∞) :=
          add_le_add (add_le_add hAself le_rfl) hs
      _ ≤ ((4 * N : ℕ) : ℕ∞) := by norm_cast; omega
  | succ t ih =>
    intro ht
    rcases ih (by omega) with hw | hval
    · exact Or.inl hw
    by_cases hserve : ∀ j, ¬ condK D A (pairCode (X j)
        (fingerprintLadder A X (2 * S * t) (m₀ - S * (t * (t - 1))))) ≤
          (logSlack c (8 * N) : ℕ∞)
    · exact Or.inl ⟨_, hval, hserve⟩
    push Not at hserve
    obtain ⟨j, hj⟩ := hserve
    right
    rw [Nat.add_sub_cancel]
    have hprod : S * ((t + 1) * t) = S * (t * (t - 1)) + 2 * S * t := by
      cases t with
      | zero => simp
      | succ k => rw [Nat.add_sub_cancel]; ring
    have htS : S * t ≤ S * (4 * d + 3) := Nat.mul_le_mul_left S (by omega)
    have hle : S * ((t + 1) * t) ≤ 4 * N := by
      calc S * ((t + 1) * t) ≤ S * ((4 * d + 3) * (4 * d + 2)) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))
        _ ≤ 4 * N := by linarith only [hTS]
    have hi' : 2 * S * (t + 1) ≤ 4 * N := by
      have := Nat.mul_le_mul_left (2 * S) (show t + 1 ≤ 4 * d + 3 by omega)
      linarith only [this, hdS]
    have h2St : 2 * S * t ≤ 2 * N := by linarith only [htS, hdS]
    have hdiff : m₀ - S * (t * (t - 1)) - (m₀ - S * ((t + 1) * t)) = 2 * S * t := by omega
    have hdrop : ((X j).drop (2 * S * (t + 1))).length ≤ 4 * N - 2 * S * (t + 1) := by
      rw [List.length_drop]; have := hX' j; omega
    have hs := hslack c₂ (3 * (d + 2 * S * t + (m₀ - S * (t * (t - 1))) + (X j).length) + 3)
      (by omega) (by have := hX' j; omega)
    have h := h₂ A X j (2 * S * t) (2 * S * (t + 1)) (m₀ - S * (t * (t - 1)))
      (m₀ - S * ((t + 1) * t)) (Nat.mul_le_mul_left _ (by omega)) (by omega)
      (by rw [hAlen]; omega)
    have h2 : 2 * S * (t + 1) = 2 * S * t + 2 * S := by ring
    calc condK D A (fingerprintLadder A X (2 * S * (t + 1)) (m₀ - S * ((t + 1) * t)))
        ≤ condK D A (pairCode (X j)
              (fingerprintLadder A X (2 * S * t) (m₀ - S * (t * (t - 1))))) +
            ((m₀ - S * (t * (t - 1)) - (m₀ - S * ((t + 1) * t)) : ℕ) : ℕ∞) +
            (((X j).drop (2 * S * (t + 1))).length : ℕ∞) +
            (logSlack c₂ (3 * (d + 2 * S * t + (m₀ - S * (t * (t - 1))) + (X j).length) + 3) :
              ℕ∞) := h
      _ ≤ (S : ℕ∞) + ((2 * S * t : ℕ) : ℕ∞) + ((4 * N - 2 * S * (t + 1) : ℕ) : ℕ∞) +
            (S : ℕ∞) :=
          add_le_add (add_le_add (add_le_add (hj.trans hε) (by rw [hdiff]))
            (by exact_mod_cast hdrop)) hs
      _ ≤ ((4 * N : ℕ) : ℕ∞) := by norm_cast; omega

end Kolmogorov
