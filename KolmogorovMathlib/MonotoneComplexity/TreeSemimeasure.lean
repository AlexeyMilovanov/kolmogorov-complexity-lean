import Mathlib.Data.ENNReal.Basic
import KolmogorovMathlib.Core.Basic
import KolmogorovMathlib.Foundation.RecursivelyEnumerable
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitinCore.LSCApproximation
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitinCore.UniformNumerators
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitinCore

/-!
# Continuous tree semimeasures

`IsContinuousTreeSemimeasure a` asks for mass `1` at the root and `a (x0) + a (x1) ≤ a x` at
every node; `IsLowerSemicomputableContinuousSemimeasure` adds lower semicomputability. The
elementary consequences are collected here: each child carries at most the mass of its parent
(`child_false_le`, `child_true_le`), extensions carry no more mass than their prefixes
(`antitone_of_prefix`), all masses lie in `[0, 1]` and are finite (`le_one`, `ne_top`), and
summing over a level or over the extensions of a fixed string stays below the available mass
(`sum_level_le_one`, `sum_extensions_le`).
-/

open scoped ENNReal BigOperators

namespace Kolmogorov

/-- A mass assignment on bit strings with total mass `1` at the root under which the two children of
a node never carry more mass than the node itself. -/
def IsContinuousTreeSemimeasure (a : BitString → ℝ≥0∞) : Prop :=
  a [] = 1 ∧ ∀ x, a (x ++ [false]) + a (x ++ [true]) ≤ a x

/-- A continuous tree semimeasure that is in addition lower semicomputable. -/
def IsLowerSemicomputableContinuousSemimeasure (a : BitString → ℝ≥0∞) : Prop :=
  IsContinuousTreeSemimeasure a ∧ IsLSC (fun x _ => a x)

/-- The zero child of a node carries at most the mass of the node. -/
theorem IsContinuousTreeSemimeasure.child_false_le {a : BitString → ℝ≥0∞}
    (ha : IsContinuousTreeSemimeasure a) (x : BitString) :
    a (x ++ [false]) ≤ a x :=
  le_trans le_self_add (ha.2 x)

/-- The one child of a node carries at most the mass of the node. -/
theorem IsContinuousTreeSemimeasure.child_true_le {a : BitString → ℝ≥0∞}
    (ha : IsContinuousTreeSemimeasure a) (x : BitString) :
    a (x ++ [true]) ≤ a x :=
  le_trans le_add_self (ha.2 x)

/-- Extensions carry no more mass than their prefixes. -/
theorem IsContinuousTreeSemimeasure.antitone_of_prefix {a : BitString → ℝ≥0∞}
    (ha : IsContinuousTreeSemimeasure a) {x y : BitString} (h : x <+: y) :
    a y ≤ a x := by
  have H : ∀ z x, a (x ++ z) ≤ a x := by
    intro z
    induction z with
    | nil => intro x; simp
    | cons b z ih =>
      intro x
      have h1 : x ++ b :: z = (x ++ [b]) ++ z := by simp
      rw [h1]
      apply le_trans (ih (x ++ [b]))
      cases b
      · exact ha.child_false_le x
      · exact ha.child_true_le x
  rcases h with ⟨z, rfl⟩
  exact H z x

/-- No node of a continuous tree semimeasure carries mass above `1`. -/
theorem IsContinuousTreeSemimeasure.le_one {a : BitString → ℝ≥0∞}
    (ha : IsContinuousTreeSemimeasure a) (x : BitString) :
    a x ≤ 1 := by
  have h : [] <+: x := ⟨x, by simp⟩
  have h2 := ha.antitone_of_prefix h
  rwa [ha.left] at h2

/-- The mass of a node of a continuous tree semimeasure is finite. -/
theorem IsContinuousTreeSemimeasure.ne_top {a : BitString → ℝ≥0∞}
    (ha : IsContinuousTreeSemimeasure a) (x : BitString) :
    a x ≠ ⊤ := by
  have h1 := ha.le_one x
  have h2 : (1 : ℝ≥0∞) < ⊤ := ENNReal.one_lt_top
  exact ne_of_lt (lt_of_le_of_lt h1 h2)

/-- The strings of length `n + 1` are obtained by prefixing the strings of length `n` with a zero or
a one. -/
theorem exactLengthPrograms_succ_eq_cons_image (n : ℕ) :
    (exactLengthPrograms (n + 1)).toFinset =
      (exactLengthPrograms n).toFinset.image (fun y => false :: y) ∪
      (exactLengthPrograms n).toFinset.image (fun y => true :: y) := by
  ext x
  simp only [exactLengthPrograms, List.mem_toFinset, Finset.mem_union, Finset.mem_image,
    List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨a, ha, hx⟩
    rcases hx with rfl | rfl
    · left; exact ⟨a, ha, rfl⟩
    · right; exact ⟨a, ha, rfl⟩
  · rintro (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩)
    · exact ⟨a, ha, Or.inl rfl⟩
    · exact ⟨a, ha, Or.inr rfl⟩

/-- The extensions of `x` by `n` further bits carry together at most the mass of `x`. -/
theorem IsContinuousTreeSemimeasure.sum_extensions_le {a : BitString → ℝ≥0∞}
    (ha : IsContinuousTreeSemimeasure a) (x : BitString) (n : ℕ) :
    ∑ y ∈ (exactLengthPrograms n).toFinset, a (x ++ y) ≤ a x := by
  induction n generalizing x with
  | zero =>
    simp only [exactLengthPrograms, List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
      Finset.sum_singleton, List.append_nil, le_refl]
  | succ n ih =>
    rw [exactLengthPrograms_succ_eq_cons_image]
    have h_disj : Disjoint ((exactLengthPrograms n).toFinset.image (fun y =>
    false :: y)) ((exactLengthPrograms n).toFinset.image (fun y =>
    true :: y)) := by
      rw [Finset.disjoint_iff_ne]
      rintro a ha b hb rfl
      rw [Finset.mem_image] at ha hb
      rcases ha with ⟨ya, _, rfl⟩
      rcases hb with ⟨yb, _, eq⟩
      simp only [List.cons.injEq] at eq
      rcases eq with ⟨h, _⟩
      contradiction
    rw [Finset.sum_union h_disj]
    have h_sum1 : ∑ y ∈ (exactLengthPrograms n).toFinset.image (fun y =>
    false :: y),
    a (x ++ y) = ∑ y ∈ (exactLengthPrograms n).toFinset,
    a (x ++ false :: y) := by
      apply Finset.sum_image
      intro y _ z _ eq
      simp only [List.cons.injEq] at eq
      exact eq.2
    have h_sum2 : ∑ y ∈ (exactLengthPrograms n).toFinset.image (fun y =>
    true :: y),
    a (x ++ y) = ∑ y ∈ (exactLengthPrograms n).toFinset,
    a (x ++ true :: y) := by
      apply Finset.sum_image
      intro y _ z _ eq
      simp only [List.cons.injEq] at eq
      exact eq.2
    rw [h_sum1, h_sum2]
    have h_rw1 : ∀ y, x ++ false :: y = (x ++ [false]) ++ y := by
      intro y
      exact (List.append_assoc x [false] y).symm
    have h_rw2 : ∀ y, x ++ true :: y = (x ++ [true]) ++ y := by
      intro y
      exact (List.append_assoc x [true] y).symm
    have h_eq1 : ∑ y ∈ (exactLengthPrograms n).toFinset,
    a (x ++ false :: y) = ∑ y ∈ (exactLengthPrograms n).toFinset,
    a ((x ++ [false]) ++ y) :=
    by
      apply Finset.sum_congr rfl
      intro y _
      rw [h_rw1 y]
    have h_eq2 : ∑ y ∈ (exactLengthPrograms n).toFinset,
    a (x ++ true :: y) = ∑ y ∈ (exactLengthPrograms n).toFinset,
    a ((x ++ [true]) ++ y) :=
    by
      apply Finset.sum_congr rfl
      intro y _
      rw [h_rw2 y]
    rw [h_eq1, h_eq2]
    have ih1 := ih (x ++ [false])
    have ih2 := ih (x ++ [true])
    calc
      _ ≤ a (x ++ [false]) + a (x ++ [true]) := add_le_add ih1 ih2
      _ ≤ a x := ha.2 x

/-- Each level of a continuous tree semimeasure carries total mass at most `1`. -/
theorem IsContinuousTreeSemimeasure.sum_level_le_one {a : BitString → ℝ≥0∞}
    (ha : IsContinuousTreeSemimeasure a) (n : ℕ) :
    ∑ y ∈ (exactLengthPrograms n).toFinset, a y ≤ 1 := by
  have h := ha.sum_extensions_le [] n
  simp only [List.nil_append] at h
  rwa [ha.left] at h

end Kolmogorov
