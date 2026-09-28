import KolmogorovMathlib.MonotoneComplexity.GacsDayMass

/-!
# Blocking and block counting in the Gacs-Day game

This file collects the two structural facts that any *relocation* argument for the
Gacs-Day game needs.

* `disjointAllocations_of_incomparable`: two nodes of the `b`-ary tree which are
  prefix-incomparable (not necessarily of the same length) always receive disjoint
  allocations from a coherent server move.  This is the general form of
  `disjointAllocations_of_ne_of_length_eq`.

* `cylinder_disjoint_of_blocked`: if an allocation `a₂` contains a string `t` lying
  inside a dyadic block `P`, then every cylinder of a disjoint allocation `a₁` whose
  length is at most `|P|` is disjoint from `P`.  In game terms: a single occupant
  placed inside a block *blocks* the whole block for all competitors, since they
  would have to swallow the occupant in order to use it.

* `card_mul_le_allocationMass_of_blocks`: a family of pairwise incomparable blocks of
  length at most `m`, all contained in the region of an allocation, forces that
  allocation to have measure at least `card * 2 ^ (-m)`.  This is the counting form of
  the resource bound used to derive contradictions from over-allocation.
-/

namespace Kolmogorov

open MeasureTheory ENNReal BigOperators

/-- Two prefix-incomparable lists split, after a common prefix, at different entries. -/
lemma exists_common_prefix_of_incomparable {α : Type*} (x y : List α)
    (hxy : ¬ x <+: y) (hyx : ¬ y <+: x) :
    ∃ p c1 c2 z1 z2, x = p ++ c1 :: z1 ∧ y = p ++ c2 :: z2 ∧ c1 ≠ c2 := by
  induction x generalizing y with
  | nil => exact absurd List.nil_prefix hxy
  | cons a x ih =>
    cases y with
    | nil => exact absurd List.nil_prefix hyx
    | cons c y =>
      by_cases hac : a = c
      · subst hac
        have h1 : ¬ x <+: y := fun h => hxy (List.cons_prefix_cons.mpr ⟨rfl, h⟩)
        have h2 : ¬ y <+: x := fun h => hyx (List.cons_prefix_cons.mpr ⟨rfl, h⟩)
        obtain ⟨p, c1, c2, z1, z2, hx, hy, hne⟩ := ih y h1 h2
        exact ⟨a :: p, c1, c2, z1, z2, by simp [hx], by simp [hy], hne⟩
      · exact ⟨[], a, c, x, y, by simp, by simp, hac⟩

/-- Prefix-incomparable nodes of the `b`-ary tree receive disjoint allocations. -/
theorem disjointAllocations_of_incomparable
    {b : ℕ} {sm : ServerMove} (h_coh : serverMoveCoherent b sm)
    {x y : GacsDayNode} (hxy : ¬ x <+: y) (hyx : ¬ y <+: x)
    (hx_bound : ∀ a ∈ x, a < b) (hy_bound : ∀ a ∈ y, a < b) :
    disjointAllocations (getAlloc sm x) (getAlloc sm y) := by
  obtain ⟨p, c1, c2, z1, z2, hx, hy, hne⟩ := exists_common_prefix_of_incomparable x y hxy hyx
  have hc1 : c1 < b := by
    apply hx_bound
    rw [hx]
    simp
  have hc2 : c2 < b := by
    apply hy_bound
    rw [hy]
    simp
  have h_disj := h_coh.2 p ⟨c1, hc1⟩ ⟨c2, hc2⟩ (by intro h; exact hne (congrArg Fin.val h))
  have h_sub1 : allocationSubset (getAlloc sm x) (getAlloc sm (p ++ [c1])) := by
    refine getAlloc_subset_of_prefix h_coh ⟨z1, ?_⟩ hx_bound
    rw [hx]; simp
  have h_sub2 : allocationSubset (getAlloc sm y) (getAlloc sm (p ++ [c2])) := by
    refine getAlloc_subset_of_prefix h_coh ⟨z2, ?_⟩ hy_bound
    rw [hy]; simp
  exact disjointAllocations_mono h_disj h_sub1 h_sub2

/-- **Blocking.** If the allocation `a₂` has an occupant `t` inside the dyadic block `P`,
then every cylinder of the disjoint allocation `a₁` of length at most `|P|` is
prefix-incomparable with `P`. -/
lemma incomparable_of_blocked {a1 a2 : Allocation} (h : disjointAllocations a1 a2)
    {t P c : BitString} (ht : t ∈ a2) (hP : P <+: t) (hc : c ∈ a1)
    (hlen : c.length ≤ P.length) :
    ¬ (c <+: P ∨ P <+: c) := by
  rintro (hcP | hPc)
  · exact h c hc t ht (Or.inl (hcP.trans hP))
  · have hceq : c = P := by
      have hlen' : P.length ≤ c.length := hPc.length_le
      have : c.length = P.length := le_antisymm hlen hlen'
      exact (List.IsPrefix.eq_of_length hPc this.symm).symm
    subst hceq
    exact h c hc t ht (Or.inl hP)

/-- **Blocking, measure form.** An occupant of a disjoint allocation inside the block `P`
keeps the whole cylinder of `P` free of all cylinders of length at most `|P|`. -/
lemma cylinder_disjoint_of_blocked {a1 a2 : Allocation} (h : disjointAllocations a1 a2)
    {t P c : BitString} (ht : t ∈ a2) (hP : P <+: t) (hc : c ∈ a1)
    (hlen : c.length ≤ P.length) :
    Disjoint (cantorCylinder c) (cantorCylinder P) := by
  have hincomp := incomparable_of_blocked h ht hP hc hlen
  rw [not_or] at hincomp
  exact cantorCylinder_disjoint_of_incompatible hincomp.1 hincomp.2

/-- **Block counting.** A family of pairwise incomparable blocks of length at most `m`,
all sitting inside the region of an allocation, forces that allocation to have measure at
least `card * 2 ^ (-m)`. -/
theorem card_mul_le_allocationMass_of_blocks {A : Allocation} {m : ℕ} (S : Finset BitString)
    (hlen : ∀ P ∈ S, P.length ≤ m)
    (hincomp : ∀ P ∈ S, ∀ Q ∈ S, P ≠ Q → ¬ (P <+: Q ∨ Q <+: P))
    (hsub : ∀ P ∈ S, cantorCylinder P ⊆ allocationSet A) :
    (S.card : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹) ^ m ≤ allocationMass A := by
  classical
  have hunion : ∑ P ∈ S, uniformMeasure (cantorCylinder P)
      = uniformMeasure (⋃ P ∈ S, cantorCylinder P) := by
    symm
    refine measure_biUnion_finset ?_ (fun P _ => measurableSet_cantorCylinder P)
    intro P hP Q hQ hne
    have hcomp := hincomp P hP Q hQ hne
    rw [not_or] at hcomp
    exact cantorCylinder_disjoint_of_incompatible hcomp.1 hcomp.2
  have hle : uniformMeasure (⋃ P ∈ S, cantorCylinder P) ≤ allocationMass A := by
    refine measure_mono ?_
    intro w hw
    simp only [Set.mem_iUnion, exists_prop] at hw
    obtain ⟨P, hP, hwP⟩ := hw
    exact hsub P hP hwP
  have hhalf : ((2 : ℝ≥0∞)⁻¹) ≤ 1 := ENNReal.inv_le_one.mpr (by norm_num)
  calc (S.card : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹) ^ m
      = ∑ _P ∈ S, ((2 : ℝ≥0∞)⁻¹) ^ m := by simp
    _ ≤ ∑ P ∈ S, uniformMeasure (cantorCylinder P) := by
        refine Finset.sum_le_sum (fun P hP => ?_)
        rw [uniformMeasure_cantorCylinder]
        exact pow_le_pow_right_of_le_one' hhalf (hlen P hP)
    _ = uniformMeasure (⋃ P ∈ S, cantorCylinder P) := hunion
    _ ≤ allocationMass A := hle

end Kolmogorov
