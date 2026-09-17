import KolmogorovMathlib.MonotoneComplexity.CylinderMass
import KolmogorovMathlib.Complexity.Incompressibility

/-!
# The gray area of an allocation

The *gray area* of a finite set `a` of cylinders at depth `eps` is `neighborhoodCells`, the set
of depth-`eps` cells comparable with some string of `a`; it is what a client must treat as spent
once the server has granted `a`. `mem_neighborhoodCells_iff_prefixComparable` characterises
membership, `length_of_mem_neighborhoodCells` and `take_mem_neighborhoodCells` give its shape
across depths, and `uniformMeasure_iUnion_levelCells`, together with the disjointness lemma
`pairwiseDisjoint_cantorCylinder_of_length_eq`, converts a cell count into uniform measure — the
form in which the counting bounds of the game are used.
-/

namespace Kolmogorov
open MeasureTheory ENNReal

/-- The cells of depth `depth` that are comparable with some string of `a`. -/
def neighborhoodCells (depth : ℕ) (a : Finset BitString) : Finset BitString :=
  (stringsOfLength depth).filter fun p => ∃ c ∈ a, p <+: c ∨ c <+: p

/-- A string lies in the neighbourhood of `a` at depth `depth` exactly when it has that length
and is comparable with a member of `a`. -/
theorem mem_neighborhoodCells_iff_prefixComparable
    {depth : ℕ} {a : Finset BitString} {p : BitString} :
    p ∈ neighborhoodCells depth a ↔
      p.length = depth ∧ ∃ c ∈ a, p <+: c ∨ c <+: p := by
  simp [neighborhoodCells, mem_stringsOfLength]

/-- Every cell of a neighbourhood at depth `depth` has length `depth`. -/
lemma length_of_mem_neighborhoodCells {depth : ℕ} {a : Finset BitString} {p : BitString}
    (hp : p ∈ neighborhoodCells depth a) : p.length = depth :=
  (mem_neighborhoodCells_iff_prefixComparable.mp hp).1

/-- Truncating a neighbourhood cell to a smaller depth lands in the neighbourhood at that depth. -/
lemma take_mem_neighborhoodCells {epsDepth deltaDepth : ℕ} {a : Finset BitString}
    {p : BitString} (hεδ : epsDepth ≤ deltaDepth)
    (hp : p ∈ neighborhoodCells deltaDepth a) :
    p.take epsDepth ∈ neighborhoodCells epsDepth a := by
  obtain ⟨hlen, c, hc, hcomp⟩ := mem_neighborhoodCells_iff_prefixComparable.mp hp
  have hlen' : (p.take epsDepth).length = epsDepth := by
    simp [hlen, min_eq_left hεδ]
  have htake : p.take epsDepth <+: p := List.take_prefix _ _
  refine mem_neighborhoodCells_iff_prefixComparable.mpr ⟨hlen', c, hc, ?_⟩
  rcases hcomp with h | h
  · exact Or.inl (htake.trans h)
  · rcases le_total c.length epsDepth with hle | hle
    · refine Or.inr ?_
      exact (List.prefix_take_iff.mpr ⟨h, hle⟩)
    · refine Or.inl ?_
      exact List.prefix_of_prefix_length_le htake h (by omega)

/-- Cylinders over strings of one common length are pairwise disjoint. -/
lemma pairwiseDisjoint_cantorCylinder_of_length_eq {depth : ℕ} {S : Finset BitString}
    (hlen : ∀ p ∈ S, p.length = depth) :
    (S : Set BitString).PairwiseDisjoint cantorCylinder := by
  intro x hx y hy hxy
  have hx' := hlen x (Finset.mem_coe.mp hx)
  have hy' := hlen y (Finset.mem_coe.mp hy)
  have hlen' : x.length = y.length := by rw [hx', hy']
  refine cantorCylinder_disjoint_of_incompatible ?_ ?_
  · intro hp; exact hxy (hp.eq_of_length hlen')
  · intro hp; exact hxy (hp.eq_of_length hlen'.symm).symm

/-- The uniform measure of the union of the cylinders over a set of strings of length `depth` is
the number of strings times `2⁻¹ ^ depth`. -/
theorem uniformMeasure_iUnion_levelCells {depth : ℕ} {S : Finset BitString}
    (hlen : ∀ p ∈ S, p.length = depth) :
    uniformMeasure (⋃ p ∈ S, cantorCylinder p) =
      (S.card : ℝ≥0∞) * (2⁻¹ : ℝ≥0∞) ^ depth := by
  rw [measure_biUnion_finset (pairwiseDisjoint_cantorCylinder_of_length_eq hlen)
    (fun p _ => measurableSet_cantorCylinder p)]
  have hterm : ∀ p ∈ S, uniformMeasure (cantorCylinder p) = (2⁻¹ : ℝ≥0∞) ^ depth := by
    intro p hp
    rw [uniformMeasure_cantorCylinder, hlen p hp]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]

/-- The cells of depth `deltaDepth` whose truncation to `epsDepth` meets the allocated set but
which stay clear of the unavailable set. -/
def newGrayCells (epsDepth deltaDepth : ℕ) (allocated unavailable : Finset BitString) :
    Finset BitString :=
  (stringsOfLength deltaDepth).filter fun p =>
    p.take epsDepth ∈ neighborhoodCells epsDepth allocated ∧
      p ∉ neighborhoodCells deltaDepth unavailable

/-- Membership in the new gray area spelled out: the cell has depth `deltaDepth`, its truncation
meets the allocated set, and it avoids the unavailable set. -/
theorem mem_newGrayCells_iff {epsDepth deltaDepth : ℕ} {allocated unavailable : Finset BitString}
    {p : BitString} :
    p ∈ newGrayCells epsDepth deltaDepth allocated unavailable ↔
      p.length = deltaDepth ∧
        p.take epsDepth ∈ neighborhoodCells epsDepth allocated ∧
        p ∉ neighborhoodCells deltaDepth unavailable := by
  simp [newGrayCells, mem_stringsOfLength]

/-- The new gray area is disjoint from the neighbourhood of the unavailable set. -/
theorem newGrayCells_disjoint_unavailable {epsDepth deltaDepth : ℕ}
    {allocated unavailable : Finset BitString} :
    Disjoint
      (newGrayCells epsDepth deltaDepth allocated unavailable)
      (neighborhoodCells deltaDepth unavailable) := by
  refine Finset.disjoint_left.mpr fun p hp hp' => ?_
  obtain ⟨-, -, hnot⟩ := mem_newGrayCells_iff.mp hp
  exact hnot hp'

/-- The uniform measure of the new gray area is its number of cells times `2⁻¹ ^ deltaDepth`. -/
theorem uniformMeasure_newGrayCells {epsDepth deltaDepth : ℕ} {allocated unavailable : Finset
  BitString} :
    uniformMeasure (⋃ p ∈ newGrayCells epsDepth deltaDepth allocated unavailable,
      cantorCylinder p) =
      ((newGrayCells epsDepth deltaDepth allocated unavailable).card : ℝ≥0∞)
        * (2⁻¹ : ℝ≥0∞) ^ deltaDepth := by
  apply uniformMeasure_iUnion_levelCells
  intro p hp
  exact (mem_newGrayCells_iff.mp hp).1

/-- The neighbourhood grows with the set it is taken of. -/
theorem neighborhoodCells_mono {depth : ℕ} {a1 a2 : Finset BitString} (h : a1 ⊆ a2) :
    neighborhoodCells depth a1 ⊆ neighborhoodCells depth a2 := by
  intro p hp
  rw [mem_neighborhoodCells_iff_prefixComparable] at hp ⊢
  rcases hp with ⟨h1, c, hc, h2⟩
  exact ⟨h1, c, h hc, h2⟩

/-- The new gray area grows with the allocated set. -/
theorem newGrayCells_mono_allocated {epsDepth deltaDepth : ℕ} {a1 a2 unavailable : Finset BitString}
    (h : a1 ⊆ a2) :
    newGrayCells epsDepth deltaDepth a1 unavailable
      ⊆ newGrayCells epsDepth deltaDepth a2 unavailable := by
  intro p hp
  rw [mem_newGrayCells_iff] at hp ⊢
  exact ⟨hp.1, neighborhoodCells_mono h hp.2.1, hp.2.2⟩

/-- The new gray area shrinks as the unavailable set grows. -/
theorem newGrayCells_mono_unavailable {epsDepth deltaDepth : ℕ} {allocated u1 u2 : Finset BitString}
    (h : u1 ⊆ u2) :
    newGrayCells epsDepth deltaDepth allocated u2 ⊆ newGrayCells epsDepth deltaDepth allocated u1 :=
      by
  intro p hp
  rw [mem_newGrayCells_iff] at hp ⊢
  exact ⟨hp.1, hp.2.1, fun hnot => hp.2.2 (neighborhoodCells_mono h hnot)⟩

/-- Measuring allocated cells at a coarser gray depth can only add gray cells.
This is the depth-change used when all frozen tail rounds are transported to
the common outer depth. -/
theorem newGrayCells_mono_epsDepth {eps1 eps2 delta : ℕ}
    {allocated unavailable : Finset BitString} (h12 : eps1 ≤ eps2) :
    newGrayCells eps2 delta allocated unavailable ⊆
      newGrayCells eps1 delta allocated unavailable := by
  intro p hp
  rw [mem_newGrayCells_iff] at hp ⊢
  refine ⟨hp.1, ?_, hp.2.2⟩
  have htake := take_mem_neighborhoodCells h12 hp.2.1
  simpa [List.take_take, min_eq_left h12] using htake

/-- For a set of strings no longer than `eps`, a cell whose truncation is in the neighbourhood at
`eps` is itself in the neighbourhood at the larger depth. -/
theorem neighborhoodCells_subset_of_le_depth {eps delta : ℕ} {A : Finset BitString}
    (hA : ∀ c ∈ A, c.length ≤ eps) {p : BitString} (hp : p.length = delta) :
    p.take eps ∈ neighborhoodCells eps A → p ∈ neighborhoodCells delta A := by
  intro h_in
  rw [mem_neighborhoodCells_iff_prefixComparable] at h_in ⊢
  rcases h_in with ⟨h_len, c, hc, hcomp⟩
  refine ⟨hp, c, hc, ?_⟩
  have hc_len := hA c hc
  rcases hcomp with h_prefix | h_prefix
  · have h_eq : p.take eps = c := by
      apply List.IsPrefix.eq_of_length h_prefix
      have h1 := h_prefix.length_le
      omega
    rw [← h_eq]
    exact Or.inr (List.take_prefix eps p)
  · exact Or.inr (h_prefix.trans (List.take_prefix eps p))

/-- When the unavailable strings are no longer than `epsDepth`, the new gray area has exactly
`2 ^ (deltaDepth - epsDepth)` cells above each free cell of depth `epsDepth`. -/
theorem card_newGrayCells_of_refine {epsDepth deltaDepth : ℕ} {allocated unavailable :
  Finset BitString}
    (hεδ : epsDepth ≤ deltaDepth)
    (hu : ∀ c ∈ unavailable, c.length ≤ epsDepth) :
    (newGrayCells epsDepth deltaDepth allocated unavailable).card =
      ((neighborhoodCells epsDepth allocated) \ (neighborhoodCells epsDepth unavailable)).card
        * 2 ^ (deltaDepth - epsDepth) := by
  classical
  set D : Finset BitString :=
    (neighborhoodCells epsDepth allocated) \ (neighborhoodCells epsDepth unavailable)
  have hcard : (newGrayCells epsDepth deltaDepth allocated unavailable).card =
      (D ×ˢ stringsOfLength (deltaDepth - epsDepth)).card := by
    refine Finset.card_nbij' (fun p => (p.take epsDepth, p.drop epsDepth))
      (fun qr => qr.1 ++ qr.2) ?_ ?_ ?_ ?_
    · intro p hp
      obtain ⟨hlen, hmem, hnot⟩ := mem_newGrayCells_iff.mp hp
      have hnot' : p.take epsDepth ∉ neighborhoodCells epsDepth unavailable := by
        intro h_in
        have h_in' := neighborhoodCells_subset_of_le_depth hu hlen h_in
        exact hnot h_in'
      refine Finset.mem_product.mpr ⟨Finset.mem_sdiff.mpr ⟨hmem, hnot'⟩, ?_⟩
      rw [mem_stringsOfLength]
      simp [hlen]
    · intro qr hqr
      obtain ⟨hq, hr⟩ := Finset.mem_product.mp hqr
      have hqlen : qr.1.length = epsDepth :=
        length_of_mem_neighborhoodCells (Finset.mem_sdiff.mp hq).1
      have hrlen : qr.2.length = deltaDepth - epsDepth := (mem_stringsOfLength _ _).mp hr
      have htake : (qr.1 ++ qr.2).take epsDepth = qr.1 := by
        rw [← hqlen, List.take_left]
      refine mem_newGrayCells_iff.mpr ⟨?_, ?_, ?_⟩
      · simp [hqlen, hrlen]; omega
      · rw [htake]; exact (Finset.mem_sdiff.mp hq).1
      · intro h_in
        have h_in' := take_mem_neighborhoodCells hεδ h_in
        rw [htake] at h_in'
        exact (Finset.mem_sdiff.mp hq).2 h_in'
    · intro p _
      exact List.take_append_drop _ _
    · intro qr hqr
      obtain ⟨hq, hr⟩ := Finset.mem_product.mp hqr
      have hqlen : qr.1.length = epsDepth :=
        length_of_mem_neighborhoodCells (Finset.mem_sdiff.mp hq).1
      have h1 : (qr.1 ++ qr.2).take epsDepth = qr.1 := by rw [← hqlen, List.take_left]
      have h2 : (qr.1 ++ qr.2).drop epsDepth = qr.2 := by rw [← hqlen, List.drop_left]
      exact Prod.ext h1 h2
  rw [hcard, Finset.card_product, card_stringsOfLength]

end Kolmogorov
