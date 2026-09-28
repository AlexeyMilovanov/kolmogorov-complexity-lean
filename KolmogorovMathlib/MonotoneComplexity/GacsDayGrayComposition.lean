import KolmogorovMathlib.MonotoneComplexity.GacsDayGrayArea
import KolmogorovMathlib.MonotoneComplexity.GacsDayGame

/-!
# Composing two gray areas

What happens when a second gray area is computed after the first has been declared unavailable.
`neighborhoodCells_union` distributes the neighbourhood over unions;
`newGrayCells_disjoint_of_augmented_unavailable` and
`newGrayCells_disjoint_of_gray_unavailable` show the newly gray cells of the second phase avoid
those of the first; and `newGrayCells_union_subset_compose` with
`card_add_le_card_newGrayCells_compose` bound the two phases together by a single gray area, so
the waste of a run of phases does not accumulate faster than that of one.
-/

namespace Kolmogorov
open MeasureTheory ENNReal

/-- The neighbourhood of a union is the union of the neighbourhoods. -/
theorem neighborhoodCells_union {depth : ℕ} {A B : Finset BitString} :
    neighborhoodCells depth (A ∪ B) = neighborhoodCells depth A ∪ neighborhoodCells depth B := by
  ext p
  simp only [neighborhoodCells, Finset.mem_filter, mem_stringsOfLength, Finset.mem_union]
  constructor
  · rintro ⟨hlen, c, hc, hcomp⟩
    rcases hc with h | h
    · exact Or.inl ⟨hlen, c, h, hcomp⟩
    · exact Or.inr ⟨hlen, c, h, hcomp⟩
  · rintro (⟨hlen, c, hc, hcomp⟩ | ⟨hlen, c, hc, hcomp⟩)
    · exact ⟨hlen, c, Or.inl hc, hcomp⟩
    · exact ⟨hlen, c, Or.inr hc, hcomp⟩

/-- Taking `m` after taking `n ≥ m` entries is taking `m` entries. -/
lemma List.take_take_eq_of_le {α} {l : List α} {m n : ℕ} (h : m ≤ n) :
    (l.take n).take m = l.take m := by
  rw [List.take_take, min_eq_left h]

/-- A second gray area computed against the enlarged unavailable set is disjoint from the first. -/
theorem newGrayCells_disjoint_of_augmented_unavailable
    {epsDepth1 epsDepth2 deltaDepth : ℕ} {A1 A2 U : Finset BitString}
    (hA1 : ∀ c ∈ A1, c.length ≤ epsDepth1) :
    Disjoint (newGrayCells epsDepth1 deltaDepth A1 U)
      (newGrayCells epsDepth2 deltaDepth A2 (U ∪ A1)) := by
  rw [Finset.disjoint_left]
  intro p hp1 hp2
  rw [mem_newGrayCells_iff] at hp1 hp2
  have h2 : p ∉ neighborhoodCells deltaDepth (U ∪ A1) := hp2.2.2
  rw [neighborhoodCells_union, Finset.mem_union] at h2
  push_neg at h2
  have h3 := h2.2
  have h4 : p.take epsDepth1 ∈ neighborhoodCells epsDepth1 A1 := hp1.2.1
  have h5 : p ∈ neighborhoodCells deltaDepth A1 := by
    apply neighborhoodCells_subset_of_le_depth hA1 hp1.1 h4
  exact h3 h5

/-- Once the first phase's *whole `eps₁`-neighbourhood* of `A₁` is declared unavailable,
the gray cells opened by the second phase are disjoint from the ones opened by the
first phase, at any depths.  This is the form of the disjointness statement that is
needed when the composition is run sequentially and the unavailable set is grown by
the neighbourhood (rather than only by the allocation) of the first phase. -/
theorem newGrayCells_disjoint_of_gray_unavailable
    {eps₁ eps₂ delta : ℕ} {A₁ A₂ U : Finset BitString} :
    Disjoint
      (newGrayCells eps₁ delta A₁ U)
      (newGrayCells eps₂ delta A₂ (U ∪ neighborhoodCells eps₁ A₁)) := by
  rw [Finset.disjoint_left]
  intro p hp1 hp2
  rw [mem_newGrayCells_iff] at hp1 hp2
  have h2 : p ∉ neighborhoodCells delta (U ∪ neighborhoodCells eps₁ A₁) := hp2.2.2
  rw [neighborhoodCells_union, Finset.mem_union] at h2
  push_neg at h2
  refine h2.2 ?_
  refine neighborhoodCells_subset_of_le_depth
    (fun c hc => le_of_eq (length_of_mem_neighborhoodCells hc)) hp1.1 ?_
  refine mem_neighborhoodCells_iff_prefixComparable.mpr
    ⟨length_of_mem_neighborhoodCells hp1.2.1, p.take eps₁, hp1.2.1, Or.inl List.prefix_rfl⟩

/-- Two successive gray areas, the second computed against the enlarged unavailable set, fit
inside the gray area of the combined allocation at the finer scale. -/
theorem newGrayCells_union_subset_compose
    {epsDepth1 epsDepth2 deltaDepth : ℕ} {A1 A2 U : Finset BitString}
    (hscale : epsDepth2 ≤ epsDepth1) :
    newGrayCells epsDepth1 deltaDepth A1 U ∪
        newGrayCells epsDepth2 deltaDepth A2 (U ∪ A1) ⊆
      newGrayCells epsDepth2 deltaDepth (A1 ∪ A2) U := by
  intro p hp
  rw [Finset.mem_union] at hp
  rw [mem_newGrayCells_iff]
  rcases hp with hp1 | hp2
  · rw [mem_newGrayCells_iff] at hp1
    have h1 : p.take epsDepth1 ∈ neighborhoodCells epsDepth1 A1 := hp1.2.1
    have h2 : p.take epsDepth2 ∈ neighborhoodCells epsDepth2 A1 := by
      have h_take := take_mem_neighborhoodCells hscale h1
      rw [List.take_take_eq_of_le (by omega)] at h_take
      exact h_take
    have h3 : p.take epsDepth2 ∈ neighborhoodCells epsDepth2 (A1 ∪ A2) := by
      rw [neighborhoodCells_union, Finset.mem_union]
      exact Or.inl h2
    exact ⟨hp1.1, h3, hp1.2.2⟩
  · rw [mem_newGrayCells_iff] at hp2
    have h1 : p.take epsDepth2 ∈ neighborhoodCells epsDepth2 A2 := hp2.2.1
    have h2 : p.take epsDepth2 ∈ neighborhoodCells epsDepth2 (A1 ∪ A2) := by
      rw [neighborhoodCells_union, Finset.mem_union]
      exact Or.inr h1
    have h3 : p ∉ neighborhoodCells deltaDepth (U ∪ A1) := hp2.2.2
    rw [neighborhoodCells_union, Finset.mem_union] at h3
    push_neg at h3
    exact ⟨hp2.1, h2, h3.1⟩

/-- Two successive gray areas have at most as many cells together as the gray area of the
combined allocation. -/
theorem card_add_le_card_newGrayCells_compose
    {epsDepth1 epsDepth2 deltaDepth : ℕ} {A1 A2 U : Finset BitString}
    (hscale : epsDepth2 ≤ epsDepth1)
    (hA1 : ∀ c ∈ A1, c.length ≤ epsDepth1) :
    (newGrayCells epsDepth1 deltaDepth A1 U).card +
        (newGrayCells epsDepth2 deltaDepth A2 (U ∪ A1)).card ≤
      (newGrayCells epsDepth2 deltaDepth (A1 ∪ A2) U).card := by
  have hd : Disjoint (newGrayCells epsDepth1 deltaDepth A1 U)
      (newGrayCells epsDepth2 deltaDepth A2 (U ∪ A1)) :=
    newGrayCells_disjoint_of_augmented_unavailable hA1
  have hu : newGrayCells epsDepth1 deltaDepth A1 U ∪
        newGrayCells epsDepth2 deltaDepth A2 (U ∪ A1) ⊆
      newGrayCells epsDepth2 deltaDepth (A1 ∪ A2) U :=
    newGrayCells_union_subset_compose hscale
  have h_card := Finset.card_union_of_disjoint hd
  rw [← h_card]
  exact Finset.card_le_card hu

/-- Two successive gray areas have at most the measure of the gray area of the combined
allocation. -/
theorem uniformMeasure_add_le_uniformMeasure_newGrayCells_compose
    {epsDepth1 epsDepth2 deltaDepth : ℕ} {A1 A2 U : Finset BitString}
    (hscale : epsDepth2 ≤ epsDepth1)
    (hA1 : ∀ c ∈ A1, c.length ≤ epsDepth1) :
    uniformMeasure (⋃ p ∈ newGrayCells epsDepth1 deltaDepth A1 U, cantorCylinder p) +
    uniformMeasure (⋃ p ∈ newGrayCells epsDepth2 deltaDepth A2 (U ∪ A1),
      cantorCylinder p) ≤
    uniformMeasure (⋃ p ∈ newGrayCells epsDepth2 deltaDepth (A1 ∪ A2) U,
      cantorCylinder p) := by
  have hu : newGrayCells epsDepth1 deltaDepth A1 U ∪
        newGrayCells epsDepth2 deltaDepth A2 (U ∪ A1) ⊆
      newGrayCells epsDepth2 deltaDepth (A1 ∪ A2) U :=
    newGrayCells_union_subset_compose hscale
  have h1 : ∀ p ∈ newGrayCells epsDepth1 deltaDepth A1 U,
      p.length = deltaDepth := fun p hp => (mem_newGrayCells_iff.mp hp).1
  have h2 : ∀ p ∈ newGrayCells epsDepth2 deltaDepth A2 (U ∪ A1),
      p.length = deltaDepth := fun p hp => (mem_newGrayCells_iff.mp hp).1
  have h3 : ∀ p ∈ newGrayCells epsDepth2 deltaDepth (A1 ∪ A2) U,
      p.length = deltaDepth := fun p hp => (mem_newGrayCells_iff.mp hp).1
  rw [uniformMeasure_iUnion_levelCells h1, uniformMeasure_iUnion_levelCells h2,
    uniformMeasure_iUnion_levelCells h3]
  rw [← add_mul]
  gcongr
  norm_cast
  exact card_add_le_card_newGrayCells_compose hscale hA1

/-- The same composition, with the second call blocked by the whole neighbourhood of the first
allocation rather than the allocation itself. -/
theorem newGrayCells_union_subset_compose_grayUnavailable
    {eps₁ eps₂ delta : ℕ} {A₁ A₂ U : Finset BitString}
    (hscale : eps₂ ≤ eps₁) :
    newGrayCells eps₁ delta A₁ U ∪
        newGrayCells eps₂ delta A₂ (U ∪ neighborhoodCells eps₁ A₁) ⊆
      newGrayCells eps₂ delta (A₁ ∪ A₂) U := by
  intro p hp
  rw [Finset.mem_union] at hp
  rw [mem_newGrayCells_iff]
  rcases hp with hp1 | hp2
  · rw [mem_newGrayCells_iff] at hp1
    have h1 : p.take eps₁ ∈ neighborhoodCells eps₁ A₁ := hp1.2.1
    have h2 : p.take eps₂ ∈ neighborhoodCells eps₂ A₁ := by
      have h_take := take_mem_neighborhoodCells hscale h1
      rw [List.take_take_eq_of_le (by omega)] at h_take
      exact h_take
    have h3 : p.take eps₂ ∈ neighborhoodCells eps₂ (A₁ ∪ A₂) := by
      rw [neighborhoodCells_union, Finset.mem_union]
      exact Or.inl h2
    exact ⟨hp1.1, h3, hp1.2.2⟩
  · rw [mem_newGrayCells_iff] at hp2
    have h1 : p.take eps₂ ∈ neighborhoodCells eps₂ A₂ := hp2.2.1
    have h2 : p.take eps₂ ∈ neighborhoodCells eps₂ (A₁ ∪ A₂) := by
      rw [neighborhoodCells_union, Finset.mem_union]
      exact Or.inr h1
    have h3 : p ∉ neighborhoodCells delta (U ∪ neighborhoodCells eps₁ A₁) := hp2.2.2
    rw [neighborhoodCells_union, Finset.mem_union] at h3
    push_neg at h3
    exact ⟨hp2.1, h2, h3.1⟩

/-- Blocking the second call by the neighbourhood of the first, the two gray areas still have at
most as many cells as the combined one. -/
theorem card_add_le_card_newGrayCells_grayUnavailable
    {eps₁ eps₂ delta : ℕ} {A₁ A₂ U : Finset BitString}
    (hscale : eps₂ ≤ eps₁) :
    (newGrayCells eps₁ delta A₁ U).card +
        (newGrayCells eps₂ delta A₂ (U ∪ neighborhoodCells eps₁ A₁)).card ≤
      (newGrayCells eps₂ delta (A₁ ∪ A₂) U).card := by
  have hd : Disjoint (newGrayCells eps₁ delta A₁ U)
      (newGrayCells eps₂ delta A₂ (U ∪ neighborhoodCells eps₁ A₁)) :=
    newGrayCells_disjoint_of_gray_unavailable
  have hu : newGrayCells eps₁ delta A₁ U ∪
        newGrayCells eps₂ delta A₂ (U ∪ neighborhoodCells eps₁ A₁) ⊆
      newGrayCells eps₂ delta (A₁ ∪ A₂) U :=
    newGrayCells_union_subset_compose_grayUnavailable hscale
  have h_card := Finset.card_union_of_disjoint hd
  rw [← h_card]
  exact Finset.card_le_card hu

/-- Blocking the second call by the neighbourhood of the first, the two gray areas still have at
most the measure of the combined one. -/
theorem uniformMeasure_add_le_newGrayCells_grayUnavailable
    {eps₁ eps₂ delta : ℕ} {A₁ A₂ U : Finset BitString}
    (hscale : eps₂ ≤ eps₁) :
    uniformMeasure (⋃ p ∈ newGrayCells eps₁ delta A₁ U, cantorCylinder p) +
    uniformMeasure (⋃ p ∈ newGrayCells eps₂ delta A₂ (U ∪ neighborhoodCells eps₁ A₁),
      cantorCylinder p) ≤
    uniformMeasure (⋃ p ∈ newGrayCells eps₂ delta (A₁ ∪ A₂) U,
      cantorCylinder p) := by
  have h1 : ∀ p ∈ newGrayCells eps₁ delta A₁ U,
      p.length = delta := fun p hp => (mem_newGrayCells_iff.mp hp).1
  have h2 : ∀ p ∈ newGrayCells eps₂ delta A₂ (U ∪ neighborhoodCells eps₁ A₁),
      p.length = delta := fun p hp => (mem_newGrayCells_iff.mp hp).1
  have h3 : ∀ p ∈ newGrayCells eps₂ delta (A₁ ∪ A₂) U,
      p.length = delta := fun p hp => (mem_newGrayCells_iff.mp hp).1
  rw [uniformMeasure_iUnion_levelCells h1, uniformMeasure_iUnion_levelCells h2,
    uniformMeasure_iUnion_levelCells h3]
  rw [← add_mul]
  gcongr
  norm_cast
  exact card_add_le_card_newGrayCells_grayUnavailable hscale

end Kolmogorov
