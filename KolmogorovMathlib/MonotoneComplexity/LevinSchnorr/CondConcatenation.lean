/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.MonotoneComplexity.LevinSchnorr.Basic
import KolmogorovMathlib.MonotoneComplexity.ConcatenationBound

/-!
# SUV Problem 135: the conditional concatenation bound

`ConcatenationBound.lean` proves Problem 134, `KM(xy) ≤ K(x) + KM(y) + O(1)`, by running a
prefix machine `M` on a self-delimiting prelude of the input, printing its output `x`, and
appending the output of a stream map `E` on the rest of the input.

Problem 135 (p. 132) replaces `KM(y)` by the *conditional* monotone complexity `KM(y | x)`.
The construction is the same, except that the tail of the input is fed to `Dc x` — the
conditional machine with the *already decoded* `x` as its condition.  Everything goes through
verbatim: the prefix machine determines `q`, hence `x`, hence which member of the family is
being run, so the consistency argument compares two runs of the *same* `Dc x`; and joint
enumerability of the family is exactly the second half of
`IsComputableConditionalStreamMap`.
-/

namespace Kolmogorov

/-- The lower graph of "run the prefix machine `M` on a halting prefix `q` of the input,
print its output `x`, then append the output of `Dc x` on the remaining input". -/
def condPrefixConcatStreamGraph (M : Map) (Dc : BitString → BitStream → BitStream)
    (p z : BitString) : Prop :=
  z = [] ∨ ∃ q r x y : BitString, q ++ r = p ∧ produces M q [] x ∧
    streamLowerGraph (Dc x) r y ∧ z <+: x ++ y

/-- Running a prefix machine and then a conditional monotone decompressor on the remaining bits
gives
a stream lower graph. -/
lemma condPrefixConcatStreamGraph_isStreamLowerGraph {M : Map}
    {Dc : BitString → BitStream → BitStream} (hM : IsPrefixMachine M)
    (hDc : ∀ y, IsContinuousStreamMap (Dc y)) :
    IsStreamLowerGraph (condPrefixConcatStreamGraph M Dc) := by
  have hDgraph : ∀ x : BitString, IsStreamLowerGraph (streamLowerGraph (Dc x)) :=
    fun x => continuousStreamMap_lowerGraph_isStreamLowerGraph (hDc x).1
  refine ⟨fun _ => Or.inl rfl, ?_, ?_, ?_⟩
  · rintro p z z' (rfl | ⟨q, r, x, y, hp, hprod, hEy, hz⟩) hz'
    · exact Or.inl (List.prefix_nil.1 hz')
    · exact Or.inr ⟨q, r, x, y, hp, hprod, hEy, hz'.trans hz⟩
  · rintro p p' z (rfl | ⟨q, r, x, y, hp, hprod, hEy, hz⟩) hpp'
    · exact Or.inl rfl
    · rcases hpp' with ⟨s, rfl⟩
      refine Or.inr ⟨q, r ++ s, x, y, by rw [← List.append_assoc, hp], hprod, ?_, hz⟩
      exact (hDgraph x).2.2.1 r (r ++ s) y hEy (List.prefix_append r s)
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
        have hy : y <+: y' ∨ y' <+: y := (hDgraph x).2.2.2 r y y' hEy hEy'
        have hcat : x ++ y <+: x ++ y' ∨ x ++ y' <+: x ++ y := by
          rcases hy with h | h
          · exact Or.inl ((List.prefix_append_right_inj x).mpr h)
          · exact Or.inr ((List.prefix_append_right_inj x).mpr h)
        rcases hcat with h | h
        · exact isPrefix_or_isPrefix_of_isPrefix (hz.trans h) hz'
        · exact isPrefix_or_isPrefix_of_isPrefix hz (hz'.trans h)

/-- For computable components the concatenated graph is recursively enumerable. -/
lemma condPrefixConcatStreamGraph_isRE {M : Map} {Dc : BitString → BitStream → BitStream}
    (hMc : isDecompressor M) (hDc : IsComputableConditionalStreamMap Dc) :
    IsRE (fun w : BitString × BitString => condPrefixConcatStreamGraph M Dc w.1 w.2) := by
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
      (w.2.2.1, w.2.1.2, w.2.2.2)) :=
    Computable.pair (Computable.fst.comp (Computable.snd.comp Computable.snd))
      (Computable.pair (Computable.snd.comp (Computable.fst.comp Computable.snd))
        (Computable.snd.comp (Computable.snd.comp Computable.snd)))
  have hRE2 : IsRE (fun w : (BitString × BitString) ×
      ((BitString × BitString) × (BitString × BitString)) =>
      streamLowerGraph (Dc w.2.2.1) w.2.1.2 w.2.2.2) := hDc.2.comp_computable hcomp2
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
          (Primrec.list_length.comp (Primrec.snd.comp Primrec.fst))
          (Primrec.list_append.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
            (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
        (Primrec.snd.comp Primrec.fst)
    rcases h1.and h2 with ⟨_, hp⟩
    exact hp.of_eq (by intro w; congr)
  have htake : ∀ u v : BitString, v.take u.length = u ↔ u <+: v := by
    intro u v
    rw [List.prefix_iff_eq_take, eq_comm]
  have hRE3 : IsRE (fun w : (BitString × BitString) ×
      ((BitString × BitString) × (BitString × BitString)) =>
      w.2.1.1 ++ w.2.1.2 = w.1.1 ∧ produces M w.2.1.1 [] w.2.2.1 ∧
        streamLowerGraph (Dc w.2.2.1) w.2.1.2 w.2.2.2 ∧ w.1.2 <+: w.2.2.1 ++ w.2.2.2) :=
    IsRE.of_iff (IsRE.and_computable (hRE1.and hRE2) hbool) (fun w => by
      rw [decide_eq_true_iff, htake]
      tauto)
  have hex := IsRE.exists_encodable
    (R := fun a : BitString × BitString =>
      fun b : (BitString × BitString) × (BitString × BitString) =>
        b.1.1 ++ b.1.2 = a.1 ∧ produces M b.1.1 [] b.2.1 ∧
          streamLowerGraph (Dc b.2.1) b.1.2 b.2.2 ∧ a.2 <+: b.2.1 ++ b.2.2) hRE3
  have hor := IsRE.or isRE_nil hex
  refine IsRE.of_iff hor (fun w => ?_)
  dsimp only [condPrefixConcatStreamGraph]
  constructor
  · rintro (h | ⟨⟨⟨q, r⟩, x, y⟩, hp, hprod, hEy, hz⟩)
    · exact Or.inl h
    · exact Or.inr ⟨q, r, x, y, hp, hprod, hEy, hz⟩
  · rintro (h | ⟨q, r, x, y, hp, hprod, hEy, hz⟩)
    · exact Or.inl h
    · exact Or.inr ⟨((q, r), (x, y)), hp, hprod, hEy, hz⟩

/-- The monotone machine "prefix-machine prelude, then the conditional machine on the decoded
condition". -/
noncomputable def condPrefixConcatStreamMap (M : Map) (Dc : BitString → BitStream → BitStream)
    (hM : IsPrefixMachine M) (hDc : ∀ y, IsContinuousStreamMap (Dc y)) :
    BitStream → BitStream :=
  streamMapOfLowerGraph (condPrefixConcatStreamGraph M Dc)
    (condPrefixConcatStreamGraph_isStreamLowerGraph hM hDc)

/-- The stream map built from the concatenated graph outputs exactly what the graph prescribes. -/
lemma condPrefixConcatStreamMap_finite_spec {M : Map} {Dc : BitString → BitStream → BitStream}
    (hM : IsPrefixMachine M) (hDc : ∀ y, IsContinuousStreamMap (Dc y)) (p z : BitString) :
    BitStream.finite z ≤ condPrefixConcatStreamMap M Dc hM hDc (.finite p) ↔
      condPrefixConcatStreamGraph M Dc p z :=
  streamMapOfLowerGraph_finite_spec _ p z

/-- For computable components the concatenated stream map is computable. -/
lemma condPrefixConcatStreamMap_isComputableStreamMap {M : Map}
    {Dc : BitString → BitStream → BitStream} (hM : IsPrefixMachine M)
    (hMc : isDecompressor M) (hDc : IsComputableConditionalStreamMap Dc) :
    IsComputableStreamMap (condPrefixConcatStreamMap M Dc hM hDc.1) := by
  refine ⟨streamMapOfLowerGraph_isContinuousStreamMap _, ?_⟩
  refine IsRE.of_iff (condPrefixConcatStreamGraph_isRE hMc hDc) (fun w => ?_)
  exact (condPrefixConcatStreamMap_finite_spec hM hDc.1 w.1 w.2).symm

/-- Concatenating a prefix program for `x` with a conditional program for `y` given `x` produces
`x ++ y`. -/
lemma monotoneProduces_condPrefixConcatStreamMap {M : Map}
    {Dc : BitString → BitStream → BitStream} (hM : IsPrefixMachine M)
    (hDc : ∀ y, IsContinuousStreamMap (Dc y)) {q r x y : BitString}
    (hq : produces M q [] x) (hr : monotoneProduces (Dc x) r y) :
    monotoneProduces (condPrefixConcatStreamMap M Dc hM hDc) (q ++ r) (x ++ y) :=
  (condPrefixConcatStreamMap_finite_spec hM hDc (q ++ r) (x ++ y)).mpr
    (Or.inr ⟨q, r, x, y, rfl, hq, hr, List.prefix_rfl⟩)

/-- The key bound for the conditional concatenation machine. -/
lemma KMOf_condPrefixConcatStreamMap_le {M : Map} {Dc : BitString → BitStream → BitStream}
    (hM : IsPrefixMachine M) (hDc : ∀ y, IsContinuousStreamMap (Dc y)) (x y : BitString) :
    KMOf (condPrefixConcatStreamMap M Dc hM hDc) (x ++ y) ≤ KP M x [] + condKMOf Dc y x := by
  rcases eq_or_ne (KP M x []) ⊤ with h1 | h1
  · rw [h1, top_add]; exact le_top
  rcases eq_or_ne (condKMOf Dc y x) ⊤ with h2 | h2
  · rw [h2, add_top]; exact le_top
  obtain ⟨q, hq, hqlen⟩ := exists_program_of_KP_ne_top h1
  obtain ⟨r, hr, hrlen⟩ := exists_program_of_KMOf_ne_top (E := Dc x) (y := y) h2
  have hprog := monotoneProduces_condPrefixConcatStreamMap hM hDc hq hr
  calc KMOf (condPrefixConcatStreamMap M Dc hM hDc) (x ++ y)
      ≤ ((q ++ r).length : ℕ∞) := KMOf_le_length_of_monotoneProduces hprog
    _ = (q.length : ℕ∞) + (r.length : ℕ∞) := by
        rw [List.length_append]; push_cast; ring
    _ = KP M x [] + condKMOf Dc y x := by rw [hqlen, hrlen]; rfl

/-- **SUV Problem 135** (Section 5.4, p. 132): `KM(xy) ≤ K(x) + KM(y | x) + O(1)`, with one
constant uniform in `x` and `y`. -/
theorem exists_const_KMOf_append_le_KP_add_condKMOf {D : BitStream → BitStream}
    (hD : IsOptimalMonotoneDecompressor D) {M : Map} (hM : IsPrefixMachine M)
    (hMc : isDecompressor M) {Dc : BitString → BitStream → BitStream}
    (hDc : IsComputableConditionalStreamMap Dc) :
    ∃ c : ℕ, ∀ x y : BitString, KMOf D (x ++ y) ≤ KP M x [] + condKMOf Dc y x + c := by
  obtain ⟨c, hc⟩ := hD.2 _ (condPrefixConcatStreamMap_isComputableStreamMap hM hMc hDc)
  refine ⟨c, fun x y => ?_⟩
  exact le_trans (hc (x ++ y))
    (add_le_add (KMOf_condPrefixConcatStreamMap_le hM hDc.1 x y) le_rfl)

end Kolmogorov
