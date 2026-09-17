import KolmogorovMathlib.AlgorithmicRandomness.ComputableMeasure

/-!
# Bitstrings of a fixed length and integrals of prefix-determined functions

`levelList n` enumerates all bitstrings of length `n`.  Cantor space is the
disjoint union of the cylinders `Ω_x` for `x` of length `n`, so the integral of
a function depending only on the length-`n` prefix is the finite sum of its
values weighted by the cylinder masses.
-/

namespace Kolmogorov

open MeasureTheory ENNReal

/-- All bitstrings of length `n`, as a list. -/
def levelList : ℕ → List BitString
  | 0 => [[]]
  | n + 1 =>
      (levelList n).map (fun x => x ++ [false]) ++ (levelList n).map (fun x => x ++ [true])

/-- The list of level-`n` strings contains exactly the bit strings of length `n`. -/
lemma mem_levelList : ∀ {n : ℕ} {y : BitString}, y ∈ levelList n ↔ y.length = n := by
  intro n
  induction n with
  | zero =>
      intro y
      simp [levelList, List.length_eq_zero_iff]
  | succ n ih =>
      intro y
      constructor
      · intro hy
        simp only [levelList, List.mem_append, List.mem_map] at hy
        rcases hy with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩ <;>
          simp [ih.1 hx]
      · intro hy
        have hne : y ≠ [] := by
          intro h; rw [h] at hy; simp at hy
        have hsplit : y.dropLast ++ [y.getLast hne] = y := List.dropLast_append_getLast hne
        have hlen : y.dropLast.length = n := by
          have := List.length_dropLast (xs := y)
          omega
        simp only [levelList, List.mem_append, List.mem_map]
        cases hb : y.getLast hne with
        | false =>
            refine Or.inl ⟨y.dropLast, ih.2 hlen, ?_⟩
            rw [← hb]; exact hsplit
        | true =>
            refine Or.inr ⟨y.dropLast, ih.2 hlen, ?_⟩
            rw [← hb]; exact hsplit

/-- The list of all bit strings of length `n` has no repetitions. -/
lemma nodup_levelList : ∀ n : ℕ, (levelList n).Nodup := by
  intro n
  induction n with
  | zero => simp [levelList]
  | succ n ih =>
      have hinj₁ : Function.Injective (fun x : BitString => x ++ [false]) := by
        intro a b hab; simpa using hab
      have hinj₂ : Function.Injective (fun x : BitString => x ++ [true]) := by
        intro a b hab; simpa using hab
      refine List.Nodup.append (ih.map hinj₁) (ih.map hinj₂) ?_
      intro y hy₁ hy₂
      simp only [List.mem_map] at hy₁ hy₂
      obtain ⟨a, -, ha⟩ := hy₁
      obtain ⟨b, -, hb⟩ := hy₂
      have : (a ++ [false]).getLast (by simp) = (b ++ [true]).getLast (by simp) := by
        simp only [ha, hb]
      simp at this

/-- All bitstrings of length `n`, as a finite set. -/
def levelFinset (n : ℕ) : Finset BitString := (levelList n).toFinset

/-- The finset of level-`n` strings consists exactly of the bit strings of length `n`. -/
@[simp] lemma mem_levelFinset {n : ℕ} {y : BitString} :
    y ∈ levelFinset n ↔ y.length = n := by
  simp [levelFinset, mem_levelList]

/-- Summing over the finset of length-`n` strings agrees with summing over the corresponding
list, the list being duplicate-free. -/
lemma sum_levelFinset_eq_sum_levelList {M : Type*} [AddCommMonoid M] (n : ℕ) (f : BitString → M) :
    ∑ x ∈ levelFinset n, f x = ((levelList n).map f).sum := by
  rw [levelFinset, List.sum_toFinset _ (nodup_levelList n)]

/-- The length-`n` cylinders partition Cantor space: summing the indicator of each cylinder
weighted by `f` evaluates `f` at the length-`n` prefix of the point. -/
lemma sum_indicator_cantorCylinder (n : ℕ) (f : BitString → ℝ≥0∞) (w : CantorSeq) :
    ∑ x ∈ levelFinset n, (cantorCylinder x).indicator (fun _ => f x) w
      = f (cantorPrefix w n) := by
  classical
  rw [Finset.sum_eq_single (cantorPrefix w n)]
  · have hmem : w ∈ cantorCylinder (cantorPrefix w n) := by
      change IsCantorPrefix (cantorPrefix w n) w
      rw [isCantorPrefix_iff_cantorPrefix_eq]
      simp
    simp [Set.indicator_of_mem hmem]
  · intro x hx hne
    have hlen : x.length = n := mem_levelFinset.1 hx
    have hnot : w ∉ cantorCylinder x := by
      intro hmem
      have : cantorPrefix w x.length = x :=
        (isCantorPrefix_iff_cantorPrefix_eq x w).1 hmem
      rw [hlen] at this
      exact hne this.symm
    simp [Set.indicator_of_notMem hnot]
  · intro hnot
    exact absurd (mem_levelFinset.2 (by simp)) hnot

/-- A function determined by the length-`n` prefix is measurable. -/
lemma measurable_comp_cantorPrefix (n : ℕ) (f : BitString → ℝ≥0∞) :
    Measurable (fun w => f (cantorPrefix w n)) := by
  classical
  have hpt : (fun w => f (cantorPrefix w n))
      = fun w => ∑ x ∈ levelFinset n, (cantorCylinder x).indicator (fun _ => f x) w := by
    funext w
    exact (sum_indicator_cantorCylinder n f w).symm
  rw [hpt]
  exact Finset.measurable_sum _ fun x _ =>
    measurable_const.indicator (measurableSet_cantorCylinder x)

/-- The integral of a function determined by the length-`n` prefix is the finite
sum of its values against the cylinder masses. -/
lemma lintegral_comp_cantorPrefix (μ : Measure CantorSeq) (n : ℕ) (f : BitString → ℝ≥0∞) :
    ∫⁻ w, f (cantorPrefix w n) ∂μ = ∑ x ∈ levelFinset n, f x * cantorMass μ x := by
  classical
  have hpt : (fun w => f (cantorPrefix w n))
      = fun w => ∑ x ∈ levelFinset n, (cantorCylinder x).indicator (fun _ => f x) w := by
    funext w
    exact (sum_indicator_cantorCylinder n f w).symm
  rw [hpt]
  rw [lintegral_finsetSum _ (fun x _ =>
    (measurable_const.indicator (measurableSet_cantorCylinder x)))]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [lintegral_indicator_const (measurableSet_cantorCylinder x)]
  rfl

end Kolmogorov
