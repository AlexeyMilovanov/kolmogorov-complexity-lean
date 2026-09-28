/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.Prefix.Optimal
import KolmogorovMathlib.Prefix.Symmetry
import KolmogorovMathlib.MonotoneComplexity.MonotoneOptimality
import Mathlib.Order.BourbakiWitt
import KolmogorovMathlib.MonotoneComplexity.MonotoneFromPrefix

/-!
# Monotone complexity of a concatenation (SUV Problem 134)

For an optimal monotone decompressor `D` and a prefix machine `M`,

`KM_D (x ++ y) ≤ KP_M (x) + KM_D (y) + O(1)`

with one constant uniform in `x` and `y`.

The construction is the "prefix prelude" machine: on an input stream `p` we look
for a halting prefix `q` of `p` (unique by prefix freeness of `M`), print
`M(q) = x`, and then continue printing `x ++ E(r)` where `r` is the remaining
part of the input and `E` is a fixed computable stream map.  Prefix freeness
makes the resulting relation a stream lower graph, and feeding `q` followed by a
shortest monotone `E`-program for `y` produces `x ++ y`.
-/

namespace Kolmogorov

/-- The lower graph of the monotone machine "run the prefix machine `M` on a halting
prefix `q` of the input, print its output `x`, then append the output of the stream
map `E` on the remaining input". -/
def prefixConcatStreamGraph (M : Map) (E : BitStream → BitStream) (p z : BitString) : Prop :=
  z = [] ∨ ∃ q r x y : BitString, q ++ r = p ∧ produces M q [] x ∧
    streamLowerGraph E r y ∧ z <+: x ++ y

/-- Running a prefix machine and then a monotone decompressor on the remaining bits gives a stream
lower graph. -/
lemma prefixConcatStreamGraph_isStreamLowerGraph {M : Map} {E : BitStream → BitStream}
    (hM : IsPrefixMachine M) (hE : IsContinuousStreamMap E) :
    IsStreamLowerGraph (prefixConcatStreamGraph M E) := by
  have hEgraph : IsStreamLowerGraph (streamLowerGraph E) :=
    continuousStreamMap_lowerGraph_isStreamLowerGraph hE.1
  refine ⟨fun _ => Or.inl rfl, ?_, ?_, ?_⟩
  · rintro p z z' (rfl | ⟨q, r, x, y, hp, hprod, hEy, hz⟩) hz'
    · exact Or.inl (List.prefix_nil.1 hz')
    · exact Or.inr ⟨q, r, x, y, hp, hprod, hEy, hz'.trans hz⟩
  · rintro p p' z (rfl | ⟨q, r, x, y, hp, hprod, hEy, hz⟩) hpp'
    · exact Or.inl rfl
    · rcases hpp' with ⟨s, rfl⟩
      refine Or.inr ⟨q, r ++ s, x, y, by rw [← List.append_assoc, hp], hprod, ?_, hz⟩
      exact hEgraph.2.2.1 r (r ++ s) y hEy (List.prefix_append r s)
  · rintro p z z' (rfl | ⟨q, r, x, y, hp, hprod, hEy, hz⟩) hz'
    · exact Or.inl List.nil_prefix
    · rcases hz' with rfl | ⟨q', r', x', y', hp', hprod', hEy', hz'⟩
      · exact Or.inr List.nil_prefix
      · have hqp : q <+: p := ⟨r, hp⟩
        have hqp' : q' <+: p := ⟨r', hp'⟩
        have hqq' : q = q' := by
          rcases isPrefix_or_isPrefix_of_isPrefix hqp hqp' with h | h
          · exact hM.eq_of_prefix hprod hprod' h
          · exact (hM.eq_of_prefix hprod' hprod h).symm
        subst hqq'
        have hrr' : r = r' := List.append_cancel_left (hp.trans hp'.symm)
        subst hrr'
        have hxx' : x = x' := Part.mem_unique hprod hprod'
        subst hxx'
        have hy : y <+: y' ∨ y' <+: y := hEgraph.2.2.2 r y y' hEy hEy'
        have hcat : x ++ y <+: x ++ y' ∨ x ++ y' <+: x ++ y := by
          rcases hy with h | h
          · exact Or.inl ((List.prefix_append_right_inj x).mpr h)
          · exact Or.inr ((List.prefix_append_right_inj x).mpr h)
        rcases hcat with h | h
        · exact isPrefix_or_isPrefix_of_isPrefix (hz.trans h) hz'
        · exact isPrefix_or_isPrefix_of_isPrefix hz (hz'.trans h)

/-- For computable components the concatenated graph is recursively enumerable. -/
lemma prefixConcatStreamGraph_isRE {M : Map} {E : BitStream → BitStream}
    (hMc : isDecompressor M) (hE : IsComputableStreamMap E) :
    IsRE (fun w : BitString × BitString => prefixConcatStreamGraph M E w.1 w.2) := by
  -- The witness tuple is `b = ((q, r), (x, y))`.
  have hgr : IsRE (fun w : (BitString × BitString) × BitString => w.2 ∈ M w.1) :=
    Partrec.graphIsRe M hMc
  have hcomp1 : Computable (fun w : (BitString × BitString) ×
      ((BitString × BitString) × (BitString × BitString)) =>
      ((w.2.1.1, ([] : BitString)), w.2.2.1)) :=
    Computable.pair
      (Computable.pair (Computable.fst.comp (Computable.fst.comp Computable.snd))
        (Computable.const []))
      (Computable.fst.comp (Computable.snd.comp Computable.snd))
  have hRE1 : IsRE (fun w : (BitString × BitString) ×
      ((BitString × BitString) × (BitString × BitString)) =>
      produces M w.2.1.1 [] w.2.2.1) := hgr.comp_computable hcomp1
  have hcomp2 : Computable (fun w : (BitString × BitString) ×
      ((BitString × BitString) × (BitString × BitString)) =>
      (w.2.1.2, w.2.2.2)) :=
    Computable.pair (Computable.snd.comp (Computable.fst.comp Computable.snd))
      (Computable.snd.comp (Computable.snd.comp Computable.snd))
  have hRE2 : IsRE (fun w : (BitString × BitString) ×
      ((BitString × BitString) × (BitString × BitString)) =>
      streamLowerGraph E w.2.1.2 w.2.2.2) := hE.2.comp_computable hcomp2
  have hbool : Computable (fun w : (BitString × BitString) ×
      ((BitString × BitString) × (BitString × BitString)) =>
      decide (w.2.1.1 ++ w.2.1.2 = w.1.1 ∧
        (w.2.2.1 ++ w.2.2.2).take w.1.2.length = w.1.2)) := by
    apply Primrec.to_comp
    have h1 : PrimrecPred (fun w : (BitString × BitString) ×
        ((BitString × BitString) × (BitString × BitString)) =>
        w.2.1.1 ++ w.2.1.2 = w.1.1) :=
      (Primrec.eq (α := BitString)).comp
        (Primrec.list_append.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
          (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
        (Primrec.fst.comp Primrec.fst)
    have h2 : PrimrecPred (fun w : (BitString × BitString) ×
        ((BitString × BitString) × (BitString × BitString)) =>
        (w.2.2.1 ++ w.2.2.2).take w.1.2.length = w.1.2) :=
      (Primrec.eq (α := BitString)).comp
        (Primrec.list_take.comp
          (Primrec.list_append.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
            (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
          (Primrec.list_length.comp (Primrec.snd.comp Primrec.fst)))
        (Primrec.snd.comp Primrec.fst)
    rcases h1.and h2 with ⟨_, hp⟩
    exact hp.of_eq (by intro w; congr)
  have htake : ∀ u v : BitString, v.take u.length = u ↔ u <+: v := by
    intro u v
    rw [List.prefix_iff_eq_take, eq_comm]
  have hRE3 : IsRE (fun w : (BitString × BitString) ×
      ((BitString × BitString) × (BitString × BitString)) =>
      w.2.1.1 ++ w.2.1.2 = w.1.1 ∧ produces M w.2.1.1 [] w.2.2.1 ∧
        streamLowerGraph E w.2.1.2 w.2.2.2 ∧ w.1.2 <+: w.2.2.1 ++ w.2.2.2) :=
    IsRE.of_iff (IsRE.and_computable (hRE1.and hRE2) hbool) (fun w => by
      rw [decide_eq_true_iff, htake]
      tauto)
  have hex := IsRE.exists_encodable
    (R := fun a : BitString × BitString =>
      fun b : (BitString × BitString) × (BitString × BitString) =>
        b.1.1 ++ b.1.2 = a.1 ∧ produces M b.1.1 [] b.2.1 ∧
          streamLowerGraph E b.1.2 b.2.2 ∧ a.2 <+: b.2.1 ++ b.2.2) hRE3
  have hor := IsRE.or isRE_nil hex
  refine IsRE.of_iff hor (fun w => ?_)
  dsimp only [prefixConcatStreamGraph]
  constructor
  · rintro (h | ⟨⟨⟨q, r⟩, x, y⟩, hp, hprod, hEy, hz⟩)
    · exact Or.inl h
    · exact Or.inr ⟨q, r, x, y, hp, hprod, hEy, hz⟩
  · rintro (h | ⟨q, r, x, y, hp, hprod, hEy, hz⟩)
    · exact Or.inl h
    · exact Or.inr ⟨((q, r), (x, y)), hp, hprod, hEy, hz⟩

/-- The monotone (stream) machine "prefix machine prelude, then `E`". -/
noncomputable def prefixConcatStreamMap (M : Map) (E : BitStream → BitStream)
    (hM : IsPrefixMachine M) (hE : IsContinuousStreamMap E) : BitStream → BitStream :=
  streamMapOfLowerGraph (prefixConcatStreamGraph M E)
    (prefixConcatStreamGraph_isStreamLowerGraph hM hE)

/-- The stream map built from the concatenated graph outputs exactly what the graph prescribes. -/
lemma prefixConcatStreamMap_finite_spec {M : Map} {E : BitStream → BitStream}
    (hM : IsPrefixMachine M) (hE : IsContinuousStreamMap E) (p z : BitString) :
    BitStream.finite z ≤ prefixConcatStreamMap M E hM hE (.finite p) ↔
      prefixConcatStreamGraph M E p z :=
  streamMapOfLowerGraph_finite_spec _ p z

/-- For computable components the concatenated stream map is computable. -/
lemma prefixConcatStreamMap_isComputableStreamMap {M : Map} {E : BitStream → BitStream}
    (hM : IsPrefixMachine M) (hMc : isDecompressor M) (hE : IsComputableStreamMap E) :
    IsComputableStreamMap (prefixConcatStreamMap M E hM hE.1) := by
  refine ⟨streamMapOfLowerGraph_isContinuousStreamMap _, ?_⟩
  refine IsRE.of_iff (prefixConcatStreamGraph_isRE hMc hE) (fun w => ?_)
  exact (prefixConcatStreamMap_finite_spec hM hE.1 w.1 w.2).symm

/-- If `KM_E y` is finite, the infimum defining it is attained by an actual program. -/
lemma exists_program_of_KMOf_ne_top {E : BitStream → BitStream} {y : BitString}
    (h : KMOf E y ≠ ⊤) :
    ∃ p : BitString, monotoneProduces E p y ∧ (p.length : ℕ∞) = KMOf E y := by
  set S : Set ℕ∞ := { l : ℕ∞ | ∃ p : BitString, monotoneProduces E p y ∧ l = p.length } with hS
  have hne : S.Nonempty := by
    rcases Set.eq_empty_or_nonempty S with he | hne
    · exact absurd (by rw [KMOf, ← hS, he, sInf_empty]) h
    · exact hne
  have hmem : KMOf E y ∈ S := by
    rw [KMOf, ← hS]
    exact csInf_mem hne
  obtain ⟨p, hp, hlen⟩ := hmem
  exact ⟨p, hp, hlen.symm⟩

/-- The concatenation machine turns a prefix program for `x` followed by a monotone
`E`-program for `y` into a monotone program for `x ++ y`. -/
lemma monotoneProduces_prefixConcatStreamMap {M : Map} {E : BitStream → BitStream}
    (hM : IsPrefixMachine M) (hE : IsContinuousStreamMap E) {q r x y : BitString}
    (hq : produces M q [] x) (hr : monotoneProduces E r y) :
    monotoneProduces (prefixConcatStreamMap M E hM hE) (q ++ r) (x ++ y) :=
  (prefixConcatStreamMap_finite_spec hM hE (q ++ r) (x ++ y)).mpr
    (Or.inr ⟨q, r, x, y, rfl, hq, hr, List.prefix_rfl⟩)

/-- The key bound for the concatenation machine: no additive constant is needed here,
the constant only appears when passing to an optimal decompressor. -/
lemma KMOf_prefixConcatStreamMap_le {M : Map} {E : BitStream → BitStream}
    (hM : IsPrefixMachine M) (hE : IsContinuousStreamMap E) (x y : BitString) :
    KMOf (prefixConcatStreamMap M E hM hE) (x ++ y) ≤ KP M x [] + KMOf E y := by
  rcases eq_or_ne (KP M x []) ⊤ with h1 | h1
  · rw [h1, top_add]; exact le_top
  rcases eq_or_ne (KMOf E y) ⊤ with h2 | h2
  · rw [h2, add_top]; exact le_top
  obtain ⟨q, hq, hqlen⟩ := exists_program_of_KP_ne_top h1
  obtain ⟨r, hr, hrlen⟩ := exists_program_of_KMOf_ne_top h2
  have hprog := monotoneProduces_prefixConcatStreamMap hM hE hq hr
  calc KMOf (prefixConcatStreamMap M E hM hE) (x ++ y)
      ≤ ((q ++ r).length : ℕ∞) := KMOf_le_length_of_monotoneProduces hprog
    _ = (q.length : ℕ∞) + (r.length : ℕ∞) := by
        rw [List.length_append]; push_cast; ring
    _ = KP M x [] + KMOf E y := by rw [hqlen, hrlen]

/-- **SUV Problem 134**: for an optimal monotone decompressor `D` and any prefix
machine `M` that is a decompressor, there is a constant `c`, uniform in `x` and `y`,
with `KM_D (x ++ y) ≤ KP_M (x) + KM_D (y) + c`. -/
theorem exists_const_KMOf_append_le_KP_add_KMOf {D : BitStream → BitStream}
    (hD : IsOptimalMonotoneDecompressor D) {M : Map} (hM : IsPrefixMachine M)
    (hMc : isDecompressor M) :
    ∃ c : ℕ, ∀ x y : BitString, KMOf D (x ++ y) ≤ KP M x [] + KMOf D y + c := by
  obtain ⟨c, hc⟩ := hD.2 _ (prefixConcatStreamMap_isComputableStreamMap hM hMc hD.1)
  refine ⟨c, fun x y => ?_⟩
  exact le_trans (hc (x ++ y))
    (add_le_add (KMOf_prefixConcatStreamMap_le hM hD.1.1 x y) le_rfl)

/-- **SUV Problem 134** in the canonical notation `K = KPPlain U` of an optimal prefix
decompressor `U`: `KM_D (x ++ y) ≤ K (x) + KM_D (y) + O(1)`. -/
theorem exists_const_KMOf_append_le_KPPlain_add_KMOf {D : BitStream → BitStream}
    (hD : IsOptimalMonotoneDecompressor D) {U : Map} (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x y : BitString, KMOf D (x ++ y) ≤ KPPlain U x + KMOf D y + c :=
  exists_const_KMOf_append_le_KP_add_KMOf hD hU.isPrefixMachine hU.isDecompressor

end Kolmogorov
