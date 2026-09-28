/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.MonotoneComplexity.TreeSemimeasure

/-!
# Kraft-type inequality for continuous tree semimeasures

A continuous tree semimeasure `a` satisfies `a(x) ≥ a(x0) + a(x1)`.  Iterating
this inequality along the tree shows that the values of `a` on any finite
prefix-free (antichain) set of strings add up to at most `a []` = `1`.

This generalizes `IsContinuousTreeSemimeasure.sum_level_le_one`, which is the
special case of the antichain consisting of all strings of a fixed length.
-/

namespace Kolmogorov

open scoped ENNReal BigOperators

/-- A proper extension of `x` extends one of the two children of `x`. -/
lemma exists_child_prefix_of_prefix_of_ne {x y : BitString} (h : x <+: y) (hne : x ≠ y) :
    ∃ b : Bool, x ++ [b] <+: y := by
  obtain ⟨t, rfl⟩ := h
  cases t with
  | nil => exact absurd (by simp) hne
  | cons b r => exact ⟨b, r, by simp⟩

/-- Sum of a continuous tree semimeasure over a finite antichain of extensions of
`x` whose lengths are bounded by `x.length + n`. -/
theorem IsContinuousTreeSemimeasure.sum_antichain_le_of_extends {a : BitString → ℝ≥0∞}
    (ha : IsContinuousTreeSemimeasure a) :
    ∀ (n : ℕ) (x : BitString) (S : Finset BitString),
      (∀ y ∈ S, x <+: y) → (∀ y ∈ S, y.length ≤ x.length + n) →
      (∀ y ∈ S, ∀ z ∈ S, y <+: z → y = z) →
      ∑ y ∈ S, a y ≤ a x := by
  intro n
  induction n with
  | zero =>
    intro x S hpref hlen _
    have hsub : S ⊆ {x} := by
      intro y hy
      have h1 := hpref y hy
      have h2 := hlen y hy
      have : y = x := (h1.eq_of_length (by have := h1.length_le; omega)).symm
      simp [this]
    calc ∑ y ∈ S, a y ≤ ∑ y ∈ ({x} : Finset BitString), a y :=
          Finset.sum_le_sum_of_subset hsub
      _ = a x := Finset.sum_singleton _ _
  | succ n ih =>
    intro x S hpref hlen hanti
    by_cases hxS : x ∈ S
    · have hS : S = {x} := by
        ext y
        simp only [Finset.mem_singleton]
        exact ⟨fun hy => (hanti x hxS y hy (hpref y hy)).symm, fun hy => hy ▸ hxS⟩
      simp [hS]
    · have hchild : ∀ y ∈ S, ∀ b : Bool, ¬ (x ++ [!b]) <+: y → (x ++ [b]) <+: y := by
        intro y hy b hb
        obtain ⟨c, hc⟩ := exists_child_prefix_of_prefix_of_ne (hpref y hy)
          (fun h => hxS (h ▸ hy))
        cases b <;> cases c <;> simp_all
      have hbound : ∀ (b : Bool), ∑ y ∈ S.filter (fun y => (x ++ [b]) <+: y), a y
          ≤ a (x ++ [b]) := by
        intro b
        refine ih (x ++ [b]) _ ?_ ?_ ?_
        · intro y hy
          exact (Finset.mem_filter.mp hy).2
        · intro y hy
          have := hlen y (Finset.mem_filter.mp hy).1
          simp only [List.length_append, List.length_singleton]
          omega
        · intro y hy z hz hyz
          exact hanti y (Finset.mem_filter.mp hy).1 z (Finset.mem_filter.mp hz).1 hyz
      have hsplit : ∑ y ∈ S, a y
          = ∑ y ∈ S.filter (fun y => (x ++ [false]) <+: y), a y
            + ∑ y ∈ S.filter (fun y => ¬ (x ++ [false]) <+: y), a y :=
        (Finset.sum_filter_add_sum_filter_not S _ a).symm
      have hnot : S.filter (fun y => ¬ (x ++ [false]) <+: y)
          ⊆ S.filter (fun y => (x ++ [true]) <+: y) := by
        intro y hy
        obtain ⟨hyS, hy'⟩ := Finset.mem_filter.mp hy
        exact Finset.mem_filter.mpr ⟨hyS, hchild y hyS true (by simpa using hy')⟩
      calc ∑ y ∈ S, a y
          = ∑ y ∈ S.filter (fun y => (x ++ [false]) <+: y), a y
            + ∑ y ∈ S.filter (fun y => ¬ (x ++ [false]) <+: y), a y := hsplit
        _ ≤ ∑ y ∈ S.filter (fun y => (x ++ [false]) <+: y), a y
            + ∑ y ∈ S.filter (fun y => (x ++ [true]) <+: y), a y :=
              add_le_add le_rfl (Finset.sum_le_sum_of_subset hnot)
        _ ≤ a (x ++ [false]) + a (x ++ [true]) := add_le_add (hbound false) (hbound true)
        _ ≤ a x := ha.2 x

/-- Kraft-type inequality: a continuous tree semimeasure has total mass at most
`1` on any finite prefix-free set of strings. -/
theorem IsContinuousTreeSemimeasure.sum_antichain_le {a : BitString → ℝ≥0∞}
    (ha : IsContinuousTreeSemimeasure a) (S : Finset BitString)
    (hanti : ∀ y ∈ S, ∀ z ∈ S, y <+: z → y = z) :
    ∑ y ∈ S, a y ≤ 1 := by
  have h := ha.sum_antichain_le_of_extends (S.sup List.length) [] S
    (fun y _ => List.nil_prefix)
    (fun y hy => by simpa using Finset.le_sup (f := List.length) hy) hanti
  rwa [ha.1] at h

/-- Kraft-type inequality for an arbitrary (possibly infinite) prefix-free set of
strings. -/
theorem IsContinuousTreeSemimeasure.tsum_antichain_le {a : BitString → ℝ≥0∞}
    (ha : IsContinuousTreeSemimeasure a) (S : Set BitString)
    (hanti : ∀ y ∈ S, ∀ z ∈ S, y <+: z → y = z) :
    ∑' y : S, a y ≤ 1 := by
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  have hinj : Set.InjOn (fun i : S => (i : BitString)) s := fun x _ y _ h => Subtype.ext h
  rw [← Finset.sum_image (f := a) (g := fun i : S => (i : BitString))
    (fun x hx y hy h => hinj hx hy h)]
  refine ha.sum_antichain_le _ ?_
  intro y hy z hz hyz
  simp only [Finset.mem_image] at hy hz
  obtain ⟨y', _, rfl⟩ := hy
  obtain ⟨z', _, rfl⟩ := hz
  exact hanti _ y'.2 _ z'.2 hyz

end Kolmogorov
