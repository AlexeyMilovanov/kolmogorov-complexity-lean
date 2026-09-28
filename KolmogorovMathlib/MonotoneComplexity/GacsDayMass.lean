import KolmogorovMathlib.MonotoneComplexity.GacsDayGame
import KolmogorovMathlib.AlgorithmicRandomness.Cylinders
import KolmogorovMathlib.MonotoneComplexity.CylinderMass
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# The uniform mass of a server allocation

Measure-theoretic bookkeeping for the server side of the game. `allocationSet` is the union of
the cylinders of an allocation and `allocationMass` its uniform measure; the mass is at most `1`
(`allocationMass_le_one`), monotone in the allocation, and at least the size of any request the
allocation serves (`serves_imp_request_le_mass`). For a coherent server move the allocations
nest along the tree (`getAlloc_subset_of_prefix`), distinct nodes of one depth get disjoint
allocations (`disjointAllocations_of_ne_of_length_eq`), and hence
`sum_allocationMass_level_le_one`: the total mass granted at one level never exceeds `1`. This
is the pigeonhole the client exploits.
-/

namespace Kolmogorov

open MeasureTheory ENNReal

/-- The set of infinite sequences covered by an allocation, the union of its cylinders. -/
noncomputable def allocationSet (a : Allocation) : Set CantorSeq := ⋃ c ∈ a, cantorCylinder c

/-- The uniform measure of the set covered by an allocation. -/
noncomputable def allocationMass (a : Allocation) : ℝ≥0∞ := uniformMeasure (allocationSet a)

/-- A smaller allocation covers a smaller set. -/
lemma allocationSet_mono_of_allocationSubset {a1 a2 : Allocation} (h : allocationSubset a1 a2) :
    allocationSet a1 ⊆ allocationSet a2 := by
  intro w hw
  simp only [allocationSet, Set.mem_iUnion, exists_prop] at hw ⊢
  rcases hw with ⟨c, hc, hw_in_c⟩
  rcases h c hc with ⟨y, hy, h_pref⟩
  use y
  exact ⟨hy, cantorCylinder_subset_of_prefix h_pref hw_in_c⟩

/-- An allocation has mass at most `1`. -/
theorem allocationMass_le_one (a : Allocation) : allocationMass a ≤ 1 := by
  apply prob_le_one

/-- An allocation that serves a request of size `r` has mass at least `r`. -/
theorem serves_imp_request_le_mass {a : Allocation} {r : ℚ} (hServes : Serves a r) :
    ENNReal.ofReal (r : ℝ) ≤ allocationMass a := by
  rcases hServes with ⟨c, hc, hr⟩
  have h_subset : cantorCylinder c ⊆ allocationSet a := by
    intro w hw
    simp only [allocationSet, Set.mem_iUnion, exists_prop]
    exact ⟨c, hc, hw⟩
  have h_meas : uniformMeasure (cantorCylinder c) ≤ uniformMeasure (allocationSet a) :=
    measure_mono h_subset
  rw [uniformMeasure_cantorCylinder] at h_meas
  have h_pow : ENNReal.ofReal ((1 / 2 : ℝ) ^ c.length) = (2⁻¹ : ℝ≥0∞) ^ c.length := by
    rw [ENNReal.ofReal_pow (by norm_num)]
    congr 1
    rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]
    exact congrArg Inv.inv (by norm_num)
  calc
    ENNReal.ofReal (r : ℝ) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ c.length) := ENNReal.ofReal_le_ofReal hr
    _ = (2⁻¹ : ℝ≥0∞) ^ c.length := h_pow
    _ ≤ allocationMass a := h_meas

/-- For a coherent server move, the allocation at a node is contained in the allocation at any of
its prefixes. -/
theorem getAlloc_subset_of_prefix {b : ℕ} {sm : ServerMove} (h_coh : serverMoveCoherent b sm)
    {x y : GacsDayNode} (h_pref : gacsDayNodePrefix x y) (hy_bound : ∀ a ∈ y, a < b) :
    allocationSubset (getAlloc sm y) (getAlloc sm x) := by
  rcases h_pref with ⟨z, rfl⟩
  induction z generalizing x with
  | nil =>
    simp only [List.append_nil]
    exact allocationSubset_refl _
  | cons c z ih =>
    have hc : c < b := hy_bound c (by simp)
    have h1 : allocationSubset (getAlloc sm (x ++ [c])) (getAlloc sm x) :=
      h_coh.1 x ⟨c, hc⟩
    have h2 : allocationSubset (getAlloc sm (x ++ c :: z)) (getAlloc sm (x ++ [c])) := by
      have h_eq : x ++ c :: z = (x ++ [c]) ++ z := by simp
      rw [h_eq]
      apply ih
      intro a ha
      apply hy_bound
      rw [h_eq]
      exact ha
    exact allocationSubset_trans h2 h1

/-- Allocations inside disjoint allocations are disjoint. -/
lemma disjointAllocations_mono {a1 a2 a3 a4 : Allocation}
    (h_disj : disjointAllocations a1 a2)
    (h_sub1 : allocationSubset a3 a1)
    (h_sub2 : allocationSubset a4 a2) :
    disjointAllocations a3 a4 := by
  intro x3 h3 y4 h4 h_comp
  rcases h_sub1 x3 h3 with ⟨x1, hx1, hpref1⟩
  rcases h_sub2 y4 h4 with ⟨y2, hy2, hpref2⟩
  have h_comp2 : x1 <+: y2 ∨ y2 <+: x1 := by
    rcases h_comp with h | h
    · have hx1_y4 : x1 <+: y4 := List.IsPrefix.trans hpref1 h
      exact isPrefix_or_isPrefix_of_isPrefix hx1_y4 hpref2
    · have hy2_x3 : y2 <+: x3 := List.IsPrefix.trans hpref2 h
      exact isPrefix_or_isPrefix_of_isPrefix hpref1 hy2_x3
  exact h_disj x1 hx1 y2 hy2 h_comp2

-- The `[DecidableEq α]` binder below is not used in the statement, only in the
-- proof, so the `unusedDecidableInType` linter asks for it to be dropped in
-- favour of `classical`.  Doing that would change the frozen statement of a
-- public lemma, which this cleanup phase may not do; the linter is therefore
-- silenced for this one declaration and the binder is left for the renaming
-- phase.
set_option linter.unusedDecidableInType false in
/-- Two distinct lists of the same length split at their first difference. -/
lemma exists_common_prefix_diff {α : Type*} [DecidableEq α]
    (x y : List α) (h_len : x.length = y.length) (h_ne : x ≠ y) :
    ∃ p c1 c2 z1 z2, x = p ++ c1 :: z1 ∧ y = p ++ c2 :: z2 ∧ c1 ≠ c2 := by
  induction x generalizing y with
  | nil =>
    have h_nil : y.length = 0 := h_len.symm
    have hy : y = [] := List.eq_nil_of_length_eq_zero h_nil
    subst hy
    exact False.elim (h_ne rfl)
  | cons x_hd x_tl ih =>
    cases y with
    | nil => exact False.elim (by simp at h_len)
    | cons y_hd y_tl =>
      simp only [List.length_cons, Nat.succ.injEq] at h_len
      by_cases hd_eq : x_hd = y_hd
      · subst hd_eq
        have h_ne_tl : x_tl ≠ y_tl := by
          intro h
          subst h
          exact h_ne rfl
        rcases ih y_tl h_len h_ne_tl with ⟨p, c1, c2, z1, z2, hx, hy, hne⟩
        use x_hd :: p, c1, c2, z1, z2
        simp [hx, hy, hne]
      · use [], x_hd, y_hd, x_tl, y_tl
        simp [hd_eq]

/-- For a coherent server move, distinct nodes of the same depth get disjoint allocations. -/
theorem disjointAllocations_of_ne_of_length_eq
    {b : ℕ} {sm : ServerMove} (h_coh : serverMoveCoherent b sm)
    {x y : GacsDayNode} (h_len : x.length = y.length) (h_ne : x ≠ y)
    (hx_bound : ∀ a ∈ x, a < b) (hy_bound : ∀ a ∈ y, a < b) :
    disjointAllocations (getAlloc sm x) (getAlloc sm y) := by
  rcases exists_common_prefix_diff x y h_len h_ne with ⟨p, c1, c2, z1, z2, hx, hy, hne⟩
  have hc1 : c1 < b := by
    apply hx_bound
    rw [hx]
    simp
  have hc2 : c2 < b := by
    apply hy_bound
    rw [hy]
    simp
  have h_disj := h_coh.2 p ⟨c1, hc1⟩ ⟨c2, hc2⟩ (by intro h; apply hne; exact congrArg Fin.val h)
  have h_sub1 : allocationSubset (getAlloc sm x) (getAlloc sm (p ++ [c1])) := by
    apply getAlloc_subset_of_prefix h_coh
    · use z1; rw [hx]; simp [List.append_assoc]
    · exact hx_bound
  have h_sub2 : allocationSubset (getAlloc sm y) (getAlloc sm (p ++ [c2])) := by
    apply getAlloc_subset_of_prefix h_coh
    · use z2; rw [hy]; simp [List.append_assoc]
    · exact hy_bound
  exact disjointAllocations_mono h_disj h_sub1 h_sub2


/-- The set covered by an allocation is measurable. -/
lemma measurableSet_allocationSet (a : Allocation) : MeasurableSet (allocationSet a) := by
  apply MeasurableSet.iUnion
  intro c
  apply MeasurableSet.iUnion
  intro hc
  exact measurableSet_cantorCylinder c

/-- Disjoint allocations cover disjoint sets. -/
lemma disjoint_allocationSet_of_disjointAllocations {a1 a2 : Allocation} (h :
  disjointAllocations a1 a2) :
    Disjoint (allocationSet a1) (allocationSet a2) := by
  rw [Set.disjoint_left]
  intro w h1 h2
  simp only [allocationSet, Set.mem_iUnion, exists_prop] at h1 h2
  rcases h1 with ⟨c1, hc1, hw1⟩
  rcases h2 with ⟨c2, hc2, hw2⟩
  have hd : Disjoint (cantorCylinder c1) (cantorCylinder c2) := by
    apply cantorCylinder_disjoint_of_incompatible
    · intro hc
      exact h c1 hc1 c2 hc2 (Or.inl hc)
    · intro hc
      exact h c1 hc1 c2 hc2 (Or.inr hc)
  exact Set.disjoint_left.mp hd hw1 hw2

/-- For a coherent server move, the allocations of the nodes of one level have total mass at most
`1`. -/
theorem sum_allocationMass_level_le_one
    {b : ℕ} {sm : ServerMove} (h_coh : serverMoveCoherent b sm)
    (h_len : ℕ) (S : Finset GacsDayNode)
    (h_S_len : ∀ x ∈ S, x.length = h_len)
    (h_bound : ∀ x ∈ S, ∀ a ∈ x, a < b) :
    ∑ x ∈ S, allocationMass (getAlloc sm x) ≤ 1 := by
  have h_meas : ∑ x ∈ S, allocationMass (getAlloc sm x) = uniformMeasure (⋃ x ∈ S,
    allocationSet (getAlloc sm x)) := by
    symm
    apply measure_biUnion_finset
    · intro x hx y hy hne
      have hd : disjointAllocations (getAlloc sm x) (getAlloc sm y) := by
        apply disjointAllocations_of_ne_of_length_eq h_coh _ hne (h_bound x hx) (h_bound y hy)
        rw [h_S_len x hx, h_S_len y hy]
      exact disjoint_allocationSet_of_disjointAllocations hd
    · intro x _
      exact measurableSet_allocationSet _
  rw [h_meas]
  exact prob_le_one

end Kolmogorov
