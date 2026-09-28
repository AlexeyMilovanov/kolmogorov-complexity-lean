/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.Prefix.Machine
import KolmogorovMathlib.MonotoneComplexity.MonotoneOptimality
import Mathlib.Order.BourbakiWitt
import KolmogorovMathlib.MonotoneComplexity.MonotoneComplexityBounds

/-!
# Monotone complexity is bounded by prefix complexity (SUV Theorem 85(d))

A prefix machine `M` (a partial recursive `Map` whose halting domain is prefix free)
induces a computable stream map: on input stream `p` we look for a halting prefix
`q <+: p` and output the corresponding result of `M`.  Prefix freeness makes the
associated relation a stream lower graph, and the construction shows

`KM_D(x) ≤ KP_M(x, []) + O(1)`

for every optimal monotone decompressor `D`.
-/

namespace Kolmogorov

/-- The lower graph of the monotone machine induced by a prefix machine `M`:
`p` produces the prefixes of `M(q)` for any halting prefix `q` of `p`. -/
def prefixMachineStreamGraph (M : Map) (p y : BitString) : Prop :=
  y = [] ∨ ∃ q z : BitString, q <+: p ∧ produces M q [] z ∧ y <+: z

/-- Reading a prefix machine as a monotone decompressor gives a stream lower graph. -/
lemma prefixMachineStreamGraph_isStreamLowerGraph {M : Map} (hM : IsPrefixMachine M) :
    IsStreamLowerGraph (prefixMachineStreamGraph M) := by
  refine ⟨fun x => Or.inl rfl, ?_, ?_, ?_⟩
  · rintro x y y' (rfl | ⟨q, z, hq, hprod, hyz⟩) hy'
    · exact Or.inl (List.prefix_nil.1 hy')
    · exact Or.inr ⟨q, z, hq, hprod, hy'.trans hyz⟩
  · rintro x x' y (rfl | ⟨q, z, hq, hprod, hyz⟩) hx
    · exact Or.inl rfl
    · exact Or.inr ⟨q, z, hq.trans hx, hprod, hyz⟩
  · rintro x y y' (rfl | ⟨q, z, hq, hprod, hyz⟩) hy'
    · exact Or.inl List.nil_prefix
    · rcases hy' with rfl | ⟨q', z', hq', hprod', hyz'⟩
      · exact Or.inr List.nil_prefix
      · have hqq' : q = q' := by
          rcases isPrefix_or_isPrefix_of_isPrefix hq hq' with h | h
          · exact hM.eq_of_prefix hprod hprod' h
          · exact (hM.eq_of_prefix hprod' hprod h).symm
        subst hqq'
        have hzz' : z = z' := Part.mem_unique hprod hprod'
        subst hzz'
        exact isPrefix_or_isPrefix_of_isPrefix hyz hyz'

/-- For a computable prefix machine the associated stream graph is recursively enumerable. -/
lemma prefixMachineStreamGraph_isRE {M : Map} (hM : isDecompressor M) :
    IsRE (fun w : BitString × BitString => prefixMachineStreamGraph M w.1 w.2) := by
  have hgr : IsRE (fun w : (BitString × BitString) × BitString => w.2 ∈ M w.1) :=
    Partrec.graphIsRe M hM
  have hcomp : Computable (fun w : (BitString × BitString) × (BitString × BitString) =>
      ((w.2.1, ([] : BitString)), w.2.2)) :=
    Computable.pair
      (Computable.pair (Computable.fst.comp Computable.snd) (Computable.const []))
      (Computable.snd.comp Computable.snd)
  have hRE1 : IsRE (fun w : (BitString × BitString) × (BitString × BitString) =>
      produces M w.2.1 [] w.2.2) := hgr.comp_computable hcomp
  have hbool : Computable (fun w : (BitString × BitString) × (BitString × BitString) =>
      decide (w.1.1.take w.2.1.length = w.2.1 ∧ w.2.2.take w.1.2.length = w.1.2)) := by
    apply Primrec.to_comp
    have h1 : PrimrecPred (fun w : (BitString × BitString) × (BitString × BitString) =>
        w.1.1.take w.2.1.length = w.2.1) :=
      (Primrec.eq (α := BitString)).comp
        (Primrec.list_take.comp (Primrec.fst.comp Primrec.fst)
          (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd)))
        (Primrec.fst.comp Primrec.snd)
    have h2 : PrimrecPred (fun w : (BitString × BitString) × (BitString × BitString) =>
        w.2.2.take w.1.2.length = w.1.2) :=
      (Primrec.eq (α := BitString)).comp
        (Primrec.list_take.comp (Primrec.snd.comp Primrec.snd)
          (Primrec.list_length.comp (Primrec.snd.comp Primrec.fst)))
        (Primrec.snd.comp Primrec.fst)
    rcases h1.and h2 with ⟨_, hp⟩
    exact hp.of_eq (by intro w; congr)
  have htake : ∀ u v : BitString, v.take u.length = u ↔ u <+: v := by
    intro u v
    rw [List.prefix_iff_eq_take, eq_comm]
  have hRE2 : IsRE (fun w : (BitString × BitString) × (BitString × BitString) =>
      w.2.1 <+: w.1.1 ∧ produces M w.2.1 [] w.2.2 ∧ w.1.2 <+: w.2.2) :=
    IsRE.of_iff (IsRE.and_computable hRE1 hbool) (fun w => by
      rw [decide_eq_true_iff, htake, htake]
      tauto)
  have hex := IsRE.exists_encodable
    (R := fun a : BitString × BitString => fun b : BitString × BitString =>
      b.1 <+: a.1 ∧ produces M b.1 [] b.2 ∧ a.2 <+: b.2) hRE2
  have hor := IsRE.or isRE_nil hex
  refine IsRE.of_iff hor (fun w => ?_)
  dsimp only [prefixMachineStreamGraph]
  constructor
  · rintro (h | ⟨⟨q, z⟩, hq, hprod, hyz⟩)
    · exact Or.inl h
    · exact Or.inr ⟨q, z, hq, hprod, hyz⟩
  · rintro (h | ⟨q, z, hq, hprod, hyz⟩)
    · exact Or.inl h
    · exact Or.inr ⟨(q, z), hq, hprod, hyz⟩

/-- The monotone (stream) machine induced by a prefix machine. -/
noncomputable def prefixMachineStreamMap (M : Map) (hM : IsPrefixMachine M) :
    BitStream → BitStream :=
  streamMapOfLowerGraph (prefixMachineStreamGraph M)
    (prefixMachineStreamGraph_isStreamLowerGraph hM)

/-- The stream map built from a prefix machine outputs exactly what the machine's graph prescribes.
-/
lemma prefixMachineStreamMap_finite_spec {M : Map} (hM : IsPrefixMachine M) (p y : BitString) :
    BitStream.finite y ≤ prefixMachineStreamMap M hM (.finite p) ↔
      prefixMachineStreamGraph M p y :=
  streamMapOfLowerGraph_finite_spec _ p y

/-- For a computable prefix machine the associated stream map is computable, so prefix complexity
bounds monotone complexity. -/
lemma prefixMachineStreamMap_isComputableStreamMap {M : Map} (hM : IsPrefixMachine M)
    (hMc : isDecompressor M) : IsComputableStreamMap (prefixMachineStreamMap M hM) := by
  refine ⟨streamMapOfLowerGraph_isContinuousStreamMap _, ?_⟩
  refine IsRE.of_iff (prefixMachineStreamGraph_isRE hMc) (fun w => ?_)
  exact (prefixMachineStreamMap_finite_spec hM w.1 w.2).symm

/-- Every program of the prefix machine is a monotone program of the induced stream map. -/
lemma KMOf_prefixMachineStreamMap_le_KP {M : Map} (hM : IsPrefixMachine M) (x : BitString) :
    KMOf (prefixMachineStreamMap M hM) x ≤ KP M x [] := by
  rw [KP_eq_condK, condK]
  apply sInf_le_sInf
  rintro n ⟨p, hprod, rfl⟩
  exact ⟨p, (prefixMachineStreamMap_finite_spec hM p x).mpr
    (Or.inr ⟨p, x, List.prefix_rfl, hprod, List.prefix_rfl⟩), rfl⟩

/-- **SUV Theorem 85(d)**: monotone complexity is bounded by prefix complexity up to an
additive constant: for an optimal monotone decompressor `D` and any prefix machine `M`
that is a decompressor there is `c` with `KM_D(x) ≤ KP_M(x) + c` for all `x`. -/
theorem exists_const_KMOf_le_KP {D : BitStream → BitStream}
    (hD : IsOptimalMonotoneDecompressor D) {M : Map} (hM : IsPrefixMachine M)
    (hMc : isDecompressor M) :
    ∃ c : ℕ, ∀ x : BitString, KMOf D x ≤ KP M x [] + c := by
  obtain ⟨c, hc⟩ := hD.2 _ (prefixMachineStreamMap_isComputableStreamMap hM hMc)
  exact ⟨c, fun x => le_trans (hc x)
    (add_le_add (KMOf_prefixMachineStreamMap_le_KP hM x) le_rfl)⟩

end Kolmogorov
