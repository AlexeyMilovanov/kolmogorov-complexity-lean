import KolmogorovMathlib.MonotoneComplexity.StreamGapFill
import KolmogorovMathlib.MonotoneComplexity.MonotoneOptimality

/-!
# Complexity defined by a consistent enumerable relation

An alternative presentation of monotone complexity: `consistentRelationKMOf R x` is the least
length of a program that `R` relates to `x`, read off a consistent stream relation rather than a
decompressor, and `IsOptimalConsistentRelation` says the resulting complexity is minimal up to an
additive constant. The two presentations agree: `consistentRelationKMOf_streamLowerGraph`
identifies the complexity of the lower graph of a decompressor with monotone complexity,
`KMOf_streamMapOfLowerGraph_streamGapFill_le` turns a consistent relation back into a
decompressor by gap-filling, and `exists_const_KMOf_le_consistentRelationKMOf` compares them.
The conclusions are `streamLowerGraph_isOptimalConsistentRelation`,
`exists_const_KMOf_consistentRelationKMOf_equiv` and `exists_optimalConsistentRelation`.

Source: SUV, Problem 137.
-/

namespace Kolmogorov

/-- The monotone complexity read off a consistent stream relation directly: the least length of a
string related to `x`. -/
noncomputable def consistentRelationKMOf (R : BitString → BitString → Prop) (x : BitString) :
    ℕ∞ :=
  sInf { l : ℕ∞ | ∃ p, R p x ∧ l = p.length }

/-- A consistent enumerable relation is optimal when its induced complexity is
minimal, up to one additive constant uniform in the output string, among all
consistent enumerable relations. -/
def IsOptimalConsistentRelation (R : BitString → BitString → Prop) : Prop :=
  IsConsistentStreamRelation R ∧
    IsRE (fun q : BitString × BitString => R q.1 q.2) ∧
    ∀ S : BitString → BitString → Prop,
      IsConsistentStreamRelation S →
      IsRE (fun q : BitString × BitString => S q.1 q.2) →
      ∃ c : ℕ, ∀ x, consistentRelationKMOf R x ≤ consistentRelationKMOf S x + (c : ℕ∞)

/-- For the lower graph of a decompressor this notion agrees with the monotone complexity of that
decompressor. -/
theorem consistentRelationKMOf_streamLowerGraph (D : BitStream → BitStream) (x : BitString) :
    consistentRelationKMOf (streamLowerGraph D) x = KMOf D x := rfl

/-- The decompressor obtained by gap-filling a consistent relation is at least as good as the
relation itself. -/
theorem KMOf_streamMapOfLowerGraph_streamGapFill_le
    {R : BitString → BitString → Prop} (hR : IsConsistentStreamRelation R)
    (_hRE : IsRE fun q : BitString × BitString => R q.1 q.2) (x : BitString) :
    KMOf (streamMapOfLowerGraph (streamGapFill R) (streamGapFill_isStreamLowerGraph hR)) x ≤
      consistentRelationKMOf R x := by
  apply sInf_le_sInf
  rintro _ ⟨p, hp, rfl⟩
  use p
  constructor
  · dsimp [monotoneProduces]
    rw [streamMapOfLowerGraph_finite_spec]
    exact streamGapFill_of_rel hp
  · rfl

/-- An optimal monotone decompressor beats every recursively enumerable consistent relation up to an
additive constant. -/
theorem exists_const_KMOf_le_consistentRelationKMOf
    {D : BitStream → BitStream} (hD : IsOptimalMonotoneDecompressor D)
    {R : BitString → BitString → Prop} (hR : IsConsistentStreamRelation R)
    (hRE : IsRE fun q : BitString × BitString => R q.1 q.2) :
    ∃ c : ℕ, ∀ x, KMOf D x ≤ consistentRelationKMOf R x + (c : ℕ∞) := by
  have H := streamMapOfLowerGraph_streamGapFill_isComputableStreamMap hR hRE
  rcases hD.2 _ H with ⟨c, hc⟩
  use c
  intro x
  have hle1 := hc x
  have hle2 := KMOf_streamMapOfLowerGraph_streamGapFill_le hR hRE x
  calc
    KMOf D x
        ≤ KMOf (streamMapOfLowerGraph (streamGapFill R)
            (streamGapFill_isStreamLowerGraph hR)) x + (c : ℕ∞) := hle1
    _ ≤ consistentRelationKMOf R x + (c : ℕ∞) := add_le_add hle2 (le_refl _)

/-- **Problem 137.** The lower graph of an optimal monotone decompressor is an
optimal consistent enumerable relation, with exactly the same complexity. -/
theorem streamLowerGraph_isOptimalConsistentRelation
    {D : BitStream → BitStream} (hD : IsOptimalMonotoneDecompressor D) :
    IsOptimalConsistentRelation (streamLowerGraph D) := by
  refine ⟨(continuousStreamMap_lowerGraph_isStreamLowerGraph hD.1.1.1).isConsistentStreamRelation,
    hD.1.2, ?_⟩
  intro R hR hRE
  obtain ⟨c, hc⟩ := exists_const_KMOf_le_consistentRelationKMOf hD hR hRE
  exact ⟨c, fun x => by rw [consistentRelationKMOf_streamLowerGraph]; exact hc x⟩

/-- **Problem 137.** Any optimal consistent-relation complexity and any optimal
map-based monotone complexity differ by at most one additive constant, uniform
in the output string. -/
theorem exists_const_KMOf_consistentRelationKMOf_equiv
    {D : BitStream → BitStream} (hD : IsOptimalMonotoneDecompressor D)
    {R : BitString → BitString → Prop} (hR : IsOptimalConsistentRelation R) :
    ∃ c : ℕ, ∀ x,
      KMOf D x ≤ consistentRelationKMOf R x + (c : ℕ∞) ∧
      consistentRelationKMOf R x ≤ KMOf D x + (c : ℕ∞) := by
  obtain ⟨c₁, hc₁⟩ := exists_const_KMOf_le_consistentRelationKMOf hD hR.1 hR.2.1
  obtain ⟨c₂, hc₂⟩ := hR.2.2 (streamLowerGraph D)
    (continuousStreamMap_lowerGraph_isStreamLowerGraph hD.1.1.1).isConsistentStreamRelation
    hD.1.2
  refine ⟨c₁ + c₂, fun x => ⟨?_, ?_⟩⟩
  · calc
      KMOf D x ≤ consistentRelationKMOf R x + (c₁ : ℕ∞) := hc₁ x
      _ ≤ consistentRelationKMOf R x + (c₁ + c₂ : ℕ) := by gcongr; omega
  · have hc₂x := hc₂ x
    rw [consistentRelationKMOf_streamLowerGraph] at hc₂x
    calc
      consistentRelationKMOf R x ≤ KMOf D x + (c₂ : ℕ∞) := hc₂x
      _ ≤ KMOf D x + (c₁ + c₂ : ℕ) := by gcongr; omega

/-- There exists an optimal consistent enumerable relation, as asserted before
SUV Problem 137. -/
theorem exists_optimalConsistentRelation :
    ∃ R : BitString → BitString → Prop, IsOptimalConsistentRelation R := by
  obtain ⟨D, hD⟩ := exists_optimalMonotoneDecompressor
  exact ⟨streamLowerGraph D, streamLowerGraph_isOptimalConsistentRelation hD⟩

end Kolmogorov
