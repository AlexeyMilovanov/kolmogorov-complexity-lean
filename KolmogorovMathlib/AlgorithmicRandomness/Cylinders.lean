import KolmogorovMathlib.AlgorithmicRandomness.Cantor
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Cylinders of Cantor space

`cantorCylinder x` is the set of infinite sequences extending the finite string `x`.  The
module identifies these sets with Mathlib's `PiNat` cylinders (`cantorCylinder_eq_piNat_cylinder`,
`piNat_cylinder_eq_cantorCylinder`, `range_cantorCylinder_eq`), so that the topological and
measurable structure of Cantor space can be imported rather than rebuilt, and records their
combinatorics: a cylinder shrinks under extension, two cylinders meet in the longer one when
the strings are comparable and are disjoint when they are not.

`isTopologicalBasis_cantorCylinders` states that the cylinders are a basis of the topology;
`isOpen_cantorCylinder`, `isClosed_cantorCylinder` and `measurableSet_cantorCylinder` are the
facts about a single cylinder used throughout the measure-theoretic development.
-/

open Kolmogorov

/-- The cylinder of a finite bit string `x`: the set of infinite sequences extending `x`. -/
def cantorCylinder (x : BitString) : Set CantorSeq := {w | IsCantorPrefix x w}

/-- A cylinder of a bit string coincides with the `PiNat` cylinder of length `|x|` around any
extension of `x`. -/
lemma cantorCylinder_eq_piNat_cylinder (x : BitString) :
    cantorCylinder x = PiNat.cylinder (prependCantor x (fun _ => false)) x.length := by
  ext w
  simp only [cantorCylinder, Set.mem_setOf_eq, PiNat.cylinder]
  constructor
  · intro h i hi
    have h1 := h i hi
    simp only [prependCantor, hi, dite_true]
    exact h1
  · intro h i hi
    have h1 := h i hi
    simp only [prependCantor, hi, dite_true] at h1
    exact h1

/-- The `PiNat` cylinder of radius `n` around `z` is the cylinder of the length-`n` prefix
of `z`. -/
lemma piNat_cylinder_eq_cantorCylinder (z : CantorSeq) (n : ℕ) :
    PiNat.cylinder z n = cantorCylinder (cantorPrefix z n) := by
  ext w
  simp only [cantorCylinder, Set.mem_setOf_eq, PiNat.cylinder, IsCantorPrefix]
  constructor
  · intro h i hi
    have hlen : i < n := by simpa using hi
    rw [h i hlen]
    exact (cantorPrefix_getElem z n i hi).symm
  · intro h i hi
    have hlen : i < (cantorPrefix z n).length := by simpa using hi
    have h1 := h i hlen
    rw [cantorPrefix_getElem z n i hlen] at h1
    exact h1

/-- The cylinders of bit strings are exactly the `PiNat` cylinders of Cantor space. -/
lemma range_cantorCylinder_eq :
    Set.range cantorCylinder = {s | ∃ z n, s = PiNat.cylinder z n} := by
  ext s
  simp only [Set.mem_range, Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨prependCantor x (fun _ => false), x.length, cantorCylinder_eq_piNat_cylinder x⟩
  · rintro ⟨z, n, rfl⟩
    exact ⟨cantorPrefix z n, (piNat_cylinder_eq_cantorCylinder z n).symm⟩

/-- Extending a string shrinks its cylinder. -/
lemma cantorCylinder_subset_of_prefix {x y : BitString} (h : x <+: y) :
    cantorCylinder y ⊆ cantorCylinder x := by
  intro w hw i hi
  have hi_y : i < y.length := by
    calc i < x.length := hi
         _ ≤ y.length := List.IsPrefix.length_le h
  have hy := hw i hi_y
  rw [hy]
  exact (List.IsPrefix.getElem h hi).symm

/-- When `x` is a prefix of `y`, the two cylinders meet in the cylinder of `y`. -/
lemma cantorCylinder_inter_of_prefix {x y : BitString} (h : x <+: y) :
    cantorCylinder x ∩ cantorCylinder y = cantorCylinder y := by
  apply Set.inter_eq_right.mpr
  exact cantorCylinder_subset_of_prefix h

/-- Cylinders of two strings neither of which is a prefix of the other are disjoint. -/
lemma cantorCylinder_disjoint_of_incompatible {x y : BitString}
    (h1 : ¬ x <+: y) (h2 : ¬ y <+: x) :
    Disjoint (cantorCylinder x) (cantorCylinder y) := by
  rw [Set.disjoint_iff]
  intro w hw
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, cantorCylinder] at hw
  have hx := hw.1
  have hy := hw.2
  rcases le_total x.length y.length with hlen | hlen
  · have h_pref : x <+: y := by
      rw [List.prefix_iff_eq_take]
      apply List.ext_getElem
      · simp [hlen]
      · intro i hi1 hi2
        have hi : i < x.length := by simpa using hi1
        have hi_y : i < y.length := by omega
        simp only [List.getElem_take]
        rw [← hx i hi, ← hy i hi_y]
    exact (h1 h_pref).elim
  · have h_pref : y <+: x := by
      rw [List.prefix_iff_eq_take]
      apply List.ext_getElem
      · simp [hlen]
      · intro i hi1 hi2
        have hi : i < y.length := by simpa using hi1
        have hi_x : i < x.length := by omega
        simp only [List.getElem_take]
        rw [← hy i hi, ← hx i hi_x]
    exact (h2 h_pref).elim

/-- The cylinders form a basis of the topology of Cantor space. -/
theorem isTopologicalBasis_cantorCylinders :
    TopologicalSpace.IsTopologicalBasis (Set.range cantorCylinder) := by
  rw [range_cantorCylinder_eq]
  exact PiNat.isTopologicalBasis_cylinders (fun _ => Bool)

/-- Every cylinder is open. -/
lemma isOpen_cantorCylinder (x : BitString) :
    IsOpen (cantorCylinder x) := by
  rw [cantorCylinder_eq_piNat_cylinder]
  exact PiNat.isOpen_cylinder (fun _ => Bool) _ _

/-- Every cylinder is closed. -/
lemma isClosed_cantorCylinder (x : BitString) :
    IsClosed (cantorCylinder x) := by
  have h : cantorCylinder x =
      ⋂ i : Fin x.length, (fun w : CantorSeq => w (i : ℕ)) ⁻¹' {x[(i : ℕ)]} := by
    ext w
    simp only [cantorCylinder, IsCantorPrefix, Set.mem_setOf_eq, Set.mem_iInter,
      Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h i
      exact h i.1 i.2
    · intro h i hi
      exact h ⟨i, hi⟩
  rw [h]
  apply isClosed_iInter
  intro i
  apply IsClosed.preimage (continuous_apply i.val)
  exact isClosed_discrete _

/-- Every cylinder is measurable. -/
lemma measurableSet_cantorCylinder (x : BitString) :
    MeasurableSet (cantorCylinder x) :=
  (isOpen_cantorCylinder x).measurableSet
