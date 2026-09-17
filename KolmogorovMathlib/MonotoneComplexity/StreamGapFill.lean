/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.MonotoneComplexity.ContinuousStreamMap
import KolmogorovMathlib.MonotoneComplexity.ProbabilisticGenerator
import KolmogorovMathlib.Foundation.PrimrecExtras
import KolmogorovMathlib.MonotoneComplexity.REClosure

/-!
# Gap filling for consistent stream relations

A relation `R` between finite inputs and finite outputs is *consistent* when outputs
produced on comparable inputs are themselves comparable. Such a relation need not be
a lower graph of a continuous stream map: it is missing the closure conditions
(nonempty at the empty output, downward closed in the output, upward closed in the
input). `streamGapFill R` performs exactly this closure, and it preserves both
consistency (yielding a genuine lower graph) and recursive enumerability.
-/

namespace Kolmogorov

/-- A relation on finite strings is *consistent* when outputs at comparable inputs are
comparable. -/
def IsConsistentStreamRelation (R : BitString → BitString → Prop) : Prop :=
  ∀ x₁ x₂ y₁ y₂, R x₁ y₁ → R x₂ y₂ →
    (x₁ <+: x₂ ∨ x₂ <+: x₁) → (y₁ <+: y₂ ∨ y₂ <+: y₁)

/-- The gap filling of a relation: close it upward in the input and downward in the
output, and add the empty output everywhere. -/
def streamGapFill (R : BitString → BitString → Prop) (x y : BitString) : Prop :=
  y = [] ∨ ∃ z : BitString × BitString, (z.1 <+: x ∧ y <+: z.2) ∧ R z.1 z.2

/-- Gap filling only adds pairs. -/
lemma streamGapFill_of_rel {R : BitString → BitString → Prop} {x y : BitString} (h : R x y) :
    streamGapFill R x y :=
  Or.inr ⟨(x, y), ⟨List.prefix_rfl, List.prefix_rfl⟩, h⟩

/-- The gap filling of a consistent relation is the lower graph of a continuous
stream map. -/
theorem streamGapFill_isStreamLowerGraph {R : BitString → BitString → Prop}
    (hR : IsConsistentStreamRelation R) :
    IsStreamLowerGraph (streamGapFill R) := by
  refine ⟨fun _ => Or.inl rfl, ?_, ?_, ?_⟩
  · rintro x y y' (rfl | ⟨z, ⟨h1, h2⟩, h3⟩) hle
    · exact Or.inl (List.prefix_nil.mp hle)
    · exact Or.inr ⟨z, ⟨h1, hle.trans h2⟩, h3⟩
  · rintro x x' y (rfl | ⟨z, ⟨h1, h2⟩, h3⟩) hle
    · exact Or.inl rfl
    · exact Or.inr ⟨z, ⟨h1.trans hle, h2⟩, h3⟩
  · rintro x y y' (rfl | ⟨z, ⟨h1, h2⟩, h3⟩) hy'
    · exact Or.inl List.nil_prefix
    · rcases hy' with rfl | ⟨z', ⟨h1', h2'⟩, h3'⟩
      · exact Or.inr List.nil_prefix
      · rcases hR z.1 z'.1 z.2 z'.2 h3 h3' (isPrefix_or_isPrefix_of_isPrefix h1 h1') with hu | hu
        · exact isPrefix_or_isPrefix_of_isPrefix (h2.trans hu) h2'
        · exact isPrefix_or_isPrefix_of_isPrefix h2 (h2'.trans hu)

/-- Boolean test witnessing the two prefix side conditions in `streamGapFill`. -/
def gapFillCheck (w : (BitString × BitString) × (BitString × BitString)) : Bool :=
  decide (w.2.1 = w.1.1.take w.2.1.length) && decide (w.1.2 = w.2.2.take w.1.2.length)

/-- The gap-filling test accepts exactly the pairs in which the second input is a prefix of the
first
and the first output is a prefix of the second. -/
lemma gapFillCheck_eq_true_iff (w : (BitString × BitString) × (BitString × BitString)) :
    gapFillCheck w = true ↔ w.2.1 <+: w.1.1 ∧ w.1.2 <+: w.2.2 := by
  rw [gapFillCheck, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff,
    ← List.prefix_iff_eq_take, ← List.prefix_iff_eq_take]

/-- The gap-filling test is computable. -/
lemma computable_gapFillCheck : Computable gapFillCheck := by
  obtain ⟨_, h1⟩ : PrimrecPred fun w : (BitString × BitString) × (BitString × BitString) =>
      w.2.1 = w.1.1.take w.2.1.length :=
    Primrec.eq.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.list_take.comp
        (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd)) (Primrec.fst.comp Primrec.fst))
  obtain ⟨_, h2⟩ : PrimrecPred fun w : (BitString × BitString) × (BitString × BitString) =>
      w.1.2 = w.2.2.take w.1.2.length :=
    Primrec.eq.comp (Primrec.snd.comp Primrec.fst)
      (Primrec.list_take.comp
        (Primrec.list_length.comp (Primrec.snd.comp Primrec.fst)) (Primrec.snd.comp Primrec.snd))
  exact (((Primrec.and.comp h1 h2)).of_eq fun w => by simp only [gapFillCheck]; congr).to_comp

/-- Gap filling preserves recursive enumerability. -/
theorem streamGapFill_isRE {R : BitString → BitString → Prop}
    (hR : IsRE (fun p : BitString × BitString => R p.1 p.2)) :
    IsRE (fun p : BitString × BitString => streamGapFill R p.1 p.2) := by
  have hRcomp : IsRE fun w : (BitString × BitString) × (BitString × BitString) =>
      R w.2.1 w.2.2 := hR.comp_computable Computable.snd
  have hand : IsRE fun w : (BitString × BitString) × (BitString × BitString) =>
      gapFillCheck w = true ∧ R w.2.1 w.2.2 :=
    hRcomp.and_computable computable_gapFillCheck
  have hex : IsRE fun p : BitString × BitString =>
      ∃ z : BitString × BitString, gapFillCheck (p, z) = true ∧ R z.1 z.2 :=
    IsRE.exists_encodable
      (R := fun (p : BitString × BitString) (z : BitString × BitString) =>
        gapFillCheck (p, z) = true ∧ R z.1 z.2) hand
  obtain ⟨_, hnilc⟩ : PrimrecPred fun p : BitString × BitString => p.2 = [] :=
    Primrec.eq.comp Primrec.snd (Primrec.const [])
  have hnil : IsRE fun p : BitString × BitString => p.2 = [] :=
    isRE_of_computable_bool _ (fun p => decide (p.2 = [])) (fun _ => by simp)
      ((hnilc.of_eq fun p => by simp).to_comp)
  refine (hnil.or hex).of_iff fun p => ?_
  constructor
  · rintro (h | ⟨z, hz, hRz⟩)
    · exact Or.inl h
    · exact Or.inr ⟨z, (gapFillCheck_eq_true_iff (p, z)).mp hz, hRz⟩
  · rintro (h | ⟨z, hz, hRz⟩)
    · exact Or.inl h
    · exact Or.inr ⟨z, (gapFillCheck_eq_true_iff (p, z)).mpr hz, hRz⟩

/-- Gap filling a consistent recursively enumerable relation produces a computable stream
map in the sense of SUV §5.4.1, whose lower graph is exactly the gap filling. -/
theorem streamMapOfLowerGraph_streamGapFill_isComputableStreamMap
    {R : BitString → BitString → Prop} (hcons : IsConsistentStreamRelation R)
    (hre : IsRE (fun p : BitString × BitString => R p.1 p.2)) :
    IsComputableStreamMap
      (streamMapOfLowerGraph (streamGapFill R) (streamGapFill_isStreamLowerGraph hcons)) := by
  refine ⟨streamMapOfLowerGraph_isContinuousStreamMap _, ?_⟩
  refine (streamGapFill_isRE hre).of_iff fun p => ?_
  exact (streamMapOfLowerGraph_finite_spec (streamGapFill_isStreamLowerGraph hcons) p.1 p.2).symm


/-- Every stream lower graph is a consistent stream relation. -/
lemma IsStreamLowerGraph.isConsistentStreamRelation {R : BitString → BitString → Prop}
    (hR : IsStreamLowerGraph R) : IsConsistentStreamRelation R :=
  fun _ _ _ _ h1 h2 hx => hR.output_compatible_of_input_compatible hx h1 h2

/-- Gap filling leaves a relation that is already a stream lower graph unchanged. -/
lemma streamGapFill_eq_self {R : BitString → BitString → Prop} (hR : IsStreamLowerGraph R)
    (x y : BitString) :
    streamGapFill R x y ↔ R x y := by
  constructor
  · rintro (rfl | ⟨z, ⟨h1, h2⟩, h3⟩)
    · exact hR.1 x
    · exact hR.2.1 x z.2 y (hR.2.2.1 z.1 x z.2 h3 h1) h2
  · intro h
    exact streamGapFill_of_rel h

/-- Gap filling respects pointwise equality of relations. -/
lemma streamGapFill_congr {R₁ R₂ : BitString → BitString → Prop} (h : ∀ x y, R₁ x y ↔ R₂ x y)
    (x y : BitString) :
    streamGapFill R₁ x y ↔ streamGapFill R₂ x y := by
  dsimp [streamGapFill]
  have hz : (∃ z : BitString × BitString, (z.1 <+: x ∧ y <+: z.2) ∧ R₁ z.1 z.2) ↔
      ∃ z : BitString × BitString, (z.1 <+: x ∧ y <+: z.2) ∧ R₂ z.1 z.2 := by
    apply exists_congr
    intro z
    rw [h z.1 z.2]
  rw [hz]

/-- Gap filling preserves uniform recursive enumerability of a family of relations. -/
theorem streamGapFill_isRE_uniform {R : ℕ → BitString → BitString → Prop}
    (hR : IsRE (fun p : ℕ × BitString × BitString => R p.1 p.2.1 p.2.2)) :
    IsRE (fun p : ℕ × BitString × BitString => streamGapFill (R p.1) p.2.1 p.2.2) := by
  have hRcomp : IsRE fun w : (ℕ × BitString × BitString) × (BitString × BitString) =>
      R w.1.1 w.2.1 w.2.2 := hR.comp_computable
        (Computable.pair (Computable.fst.comp Computable.fst) Computable.snd)
  have hand : IsRE fun w : (ℕ × BitString × BitString) × (BitString × BitString) =>
      gapFillCheck (w.1.2, w.2) = true ∧ R w.1.1 w.2.1 w.2.2 :=
    hRcomp.and_computable (computable_gapFillCheck.comp
      (Computable.pair (Computable.snd.comp Computable.fst) Computable.snd))
  have hex : IsRE fun p : ℕ × BitString × BitString =>
      ∃ z : BitString × BitString, gapFillCheck (p.2, z) = true ∧ R p.1 z.1 z.2 :=
    IsRE.exists_encodable
      (R := fun (p : ℕ × BitString × BitString) (z : BitString × BitString) =>
        gapFillCheck (p.2, z) = true ∧ R p.1 z.1 z.2) hand
  obtain ⟨_, hnilc⟩ : PrimrecPred fun p : ℕ × BitString × BitString => p.2.2 = [] :=
    Primrec.eq.comp (Primrec.snd.comp Primrec.snd) (Primrec.const [])
  have hnil : IsRE fun p : ℕ × BitString × BitString => p.2.2 = [] :=
    isRE_of_computable_bool _ (fun p => decide (p.2.2 = [])) (fun _ => by simp)
      ((hnilc.of_eq fun p => by simp).to_comp)
  refine (hnil.or hex).of_iff fun p => ?_
  constructor
  · rintro (h | ⟨z, hz, hRz⟩)
    · exact Or.inl h
    · exact Or.inr ⟨z, (gapFillCheck_eq_true_iff (p.2, z)).mp hz, hRz⟩
  · rintro (h | ⟨z, hz, hRz⟩)
    · exact Or.inl h
    · exact Or.inr ⟨z, (gapFillCheck_eq_true_iff (p.2, z)).mpr hz, hRz⟩

end Kolmogorov
