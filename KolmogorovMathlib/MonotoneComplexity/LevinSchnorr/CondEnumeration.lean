/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.MonotoneComplexity.SharedCoding
import KolmogorovMathlib.MonotoneComplexity.StreamRelationSanitizer
import KolmogorovMathlib.MonotoneComplexity.StreamMapEnumeration

/-!
# Section 5.4: the conditional form of SUV Theorem 83

SUV Problem 135 (p. 132) needs the conditional monotone complexity `KM(y | x)`, hence a
*conditional* analogue of Theorem 83: an enumeration of the lower graphs of all computable
conditional stream maps `D : BitString → BitStream → BitStream`, with an index that does
**not** depend on the condition.  This was INTERFACE_PROBLEM 1 of the C10 skeleton.

The resolution needs no new machinery: `StreamRelationSanitizer.lean` already states its
sanitizer for an arbitrary `Primcodable` parameter type `α`, and `StreamGapFill.lean` closes a
consistent relation into a stream lower graph without touching parameters.  So it suffices to

* fold the condition into the *program* slot of the unconditional universal enumeration,
  `condStageBool (i, y) p z k = universalStageBool i ⟨y, p⟩ z k` (the pair `⟨y, p⟩` coded by
  the canonical computable bijection `natToBitString ∘ Encodable.encode`), which by the
  s-m-n-free completeness of `universalStreamRel` gives **one** index `i` valid for **all**
  conditions `y`;
* run the sanitizer with `α := ℕ × BitString` and then the gap filler.

`streamGapFill_isRE_uniform` is stated for a `ℕ`-indexed family, so the index `(i, y)` is
transported along the computable bijection `ℕ ≃ ℕ × BitString` given by `Nat.pair`/`Nat.unpair`
and `natToBitString`/`bitStringToNat`.
-/

namespace Kolmogorov

/-- The stage predicate of the conditional universal family: the condition is folded into the
program slot of the unconditional universal enumeration. -/
def condStageBool (a : ℕ × BitString) (p z : BitString) (k : ℕ) : Bool :=
  universalStageBool a.1 (natToBitString (Encodable.encode ((a.2, p) : BitString × BitString)))
    z k

/-- The staged Boolean approximation of the conditional universal relation is primitive recursive.
-/
lemma primrec_condStageBool :
    Primrec fun q : ((ℕ × BitString) × BitString × BitString) × ℕ =>
      condStageBool q.1.1 q.1.2.1 q.1.2.2 q.2 := by
  have hmap : Primrec fun q : ((ℕ × BitString) × BitString × BitString) × ℕ =>
      ((q.1.1.1,
        natToBitString (Encodable.encode ((q.1.1.2, q.1.2.1) : BitString × BitString)),
        q.1.2.2), q.2) := by
    refine Primrec.pair (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.pair ?_ (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))) Primrec.snd
    exact primrec_natToBitString.comp (Primrec.encode.comp
      (Primrec.pair (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))))
  exact primrec_universalStageBool.comp hmap

/-- The conditional universal family: sanitize, then gap-fill. -/
def condUniversalStreamRel (i : ℕ) (y : BitString) (p z : BitString) : Prop :=
  streamGapFill (sanitizedStreamRel condStageBool (i, y)) p z

/-- Each row of the conditional universal relation is a stream lower graph. -/
theorem condUniversalStreamRel_isStreamLowerGraph (i : ℕ) (y : BitString) :
    IsStreamLowerGraph (condUniversalStreamRel i y) :=
  streamGapFill_isStreamLowerGraph (sanitizedStreamRel_isConsistent condStageBool (i, y))

/-- Transport of the index `(i, y)` to a single natural number. -/
private def idxEncode (a : ℕ × BitString) : ℕ := Nat.pair a.1 (bitStringToNat a.2)

private def idxDecode (n : ℕ) : ℕ × BitString :=
  ((Nat.unpair n).1, natToBitString (Nat.unpair n).2)

private lemma idxDecode_idxEncode (a : ℕ × BitString) : idxDecode (idxEncode a) = a := by
  rcases a with ⟨i, y⟩
  simp [idxDecode, idxEncode, Nat.unpair_pair, natToBitString_bitStringToNat]

private lemma primrec_idxEncode : Primrec idxEncode :=
  Primrec₂.natPair.comp Primrec.fst (primrec_bitStringToNat.comp Primrec.snd)

private lemma primrec_idxDecode : Primrec idxDecode :=
  Primrec.pair (Primrec.fst.comp Primrec.unpair)
    (primrec_natToBitString.comp (Primrec.snd.comp Primrec.unpair))

/-- The conditional universal relation is recursively enumerable uniformly in the index and the
condition. -/
theorem condUniversalStreamRel_isRE :
    IsRE fun t : (ℕ × BitString) × BitString × BitString =>
      condUniversalStreamRel t.1.1 t.1.2 t.2.1 t.2.2 := by
  have hsan : IsRE fun p : (ℕ × BitString) × BitString × BitString =>
      sanitizedStreamRel condStageBool p.1 p.2.1 p.2.2 :=
    sanitizedStreamRel_isRE_uniform primrec_condStageBool
  have hn : IsRE fun p : ℕ × BitString × BitString =>
      sanitizedStreamRel condStageBool (idxDecode p.1) p.2.1 p.2.2 :=
    hsan.comp_computable
      (Computable.pair (primrec_idxDecode.to_comp.comp Computable.fst) Computable.snd)
  have hgap := streamGapFill_isRE_uniform
    (R := fun n : ℕ => sanitizedStreamRel condStageBool (idxDecode n)) hn
  have hmap : Computable fun t : (ℕ × BitString) × BitString × BitString =>
      (idxEncode t.1, t.2) :=
    Computable.pair (primrec_idxEncode.to_comp.comp Computable.fst) Computable.snd
  refine (hgap.comp_computable hmap).of_iff fun t => ?_
  simp only [condUniversalStreamRel, idxDecode_idxEncode, Prod.mk.eta]

/-- **Conditional SUV Theorem 83.**  The family contains the lower graph of every computable
conditional stream map, with an index independent of the condition. -/
theorem condUniversalStreamRel_complete {D : BitString → BitStream → BitStream}
    (hcont : ∀ y, IsContinuousStreamMap (D y))
    (hre : IsRE fun t : BitString × BitString × BitString =>
      streamLowerGraph (D t.1) t.2.1 t.2.2) :
    ∃ i, ∀ y p z, condUniversalStreamRel i y p z ↔ streamLowerGraph (D y) p z := by
  classical
  have hR'RE : IsRE fun w : BitString × BitString =>
      ∃ q : BitString × BitString,
        w.1 = natToBitString (Encodable.encode q) ∧ streamLowerGraph (D q.1) q.2 w.2 := by
    have hbase : IsRE fun v : (BitString × BitString) × (BitString × BitString) =>
        streamLowerGraph (D v.2.1) v.2.2 v.1.2 :=
      hre.comp_computable (Computable.pair (Computable.fst.comp Computable.snd)
        (Computable.pair (Computable.snd.comp Computable.snd)
          (Computable.snd.comp Computable.fst)))
    have hcheck : Computable fun v : (BitString × BitString) × (BitString × BitString) =>
        decide (v.1.1 = natToBitString (Encodable.encode v.2)) := by
      refine Primrec.to_comp (PrimrecPred.decide ?_)
      exact Primrec.eq.comp (Primrec.fst.comp Primrec.fst)
        (primrec_natToBitString.comp (Primrec.encode.comp Primrec.snd))
    refine (IsRE.exists_encodable
      (R := fun (w : BitString × BitString) (q : BitString × BitString) =>
        decide (w.1 = natToBitString (Encodable.encode q)) = true ∧
          streamLowerGraph (D q.1) q.2 w.2) (hbase.and_computable hcheck)).of_iff fun w => ?_
    constructor
    · rintro ⟨q, hq, hg⟩
      exact ⟨q, of_decide_eq_true hq, hg⟩
    · rintro ⟨q, hq, hg⟩
      exact ⟨q, decide_eq_true hq, hg⟩
  obtain ⟨i, hi⟩ := universalStreamRel_complete (R := fun u z =>
    ∃ q : BitString × BitString,
      u = natToBitString (Encodable.encode q) ∧ streamLowerGraph (D q.1) q.2 z) hR'RE
  refine ⟨i, fun y p z => ?_⟩
  have hstage : ∀ p' z' : BitString,
      (∃ k, condStageBool (i, y) p' z' k = true) ↔ streamLowerGraph (D y) p' z' := by
    intro p' z'
    have h1 : (∃ k, condStageBool (i, y) p' z' k = true)
        ↔ universalStreamRel i
            (natToBitString (Encodable.encode ((y, p') : BitString × BitString))) z' := Iff.rfl
    rw [h1, hi]
    constructor
    · rintro ⟨q, hq, hg⟩
      have hq' : ((y, p') : BitString × BitString) = q :=
        Encodable.encode_injective (natToBitString_injective hq)
      rw [← hq'] at hg
      exact hg
    · intro hg
      exact ⟨(y, p'), rfl, hg⟩
  have hlow : IsStreamLowerGraph (streamLowerGraph (D y)) :=
    continuousStreamMap_lowerGraph_isStreamLowerGraph (hcont y).1
  have hcons : IsConsistentStreamRelation
      (fun p' z' => ∃ k, condStageBool (i, y) p' z' k = true) := by
    intro x₁ x₂ y₁ y₂ h1 h2 hpre
    exact hlow.isConsistentStreamRelation x₁ x₂ y₁ y₂
      ((hstage _ _).1 h1) ((hstage _ _).1 h2) hpre
  have heqsan : ∀ p' z' : BitString,
      sanitizedStreamRel condStageBool (i, y) p' z' ↔ streamLowerGraph (D y) p' z' := by
    intro p' z'
    rw [sanitizedStreamRel_eq_of_consistent condStageBool (i, y) hcons p' z']
    exact hstage p' z'
  have h_self := streamGapFill_eq_self hlow p z
  rw [condUniversalStreamRel, ← h_self]
  apply streamGapFill_congr
  intro x' y'
  exact heqsan x' y'

end Kolmogorov
