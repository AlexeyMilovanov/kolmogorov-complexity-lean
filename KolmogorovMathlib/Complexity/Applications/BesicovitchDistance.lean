/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.PiNat

/-!
# Lipschitz maps and Besicovitch distance: the definitions (SUV Section 8.7, p. 258)

The Cantor distance is Mathlib's `PiNat.dist`: `2^{-k}`, where `k` is the first place where two
sequences differ, and `0` for equal sequences.  The Besicovitch distance is the upper density of the
set of discrepancies.  These definitions are Mathlib-only; Theorem 165, which goes through effective
dimension, is in `Complexity/Applications/LipschitzBesicovitch.lean`.
-/

namespace Kolmogorov.Applications

open Filter

/-- The Cantor distance on `Ω`. -/
noncomputable def cantorDist (a b : ℕ → Bool) : ℝ :=
  @Dist.dist (ℕ → Bool) (PiNat.dist (E := fun _ => Bool)) a b

/-- **SUV p. 258.**  `f : Ω → Ω` is *Lipschitz* for the Cantor distance. -/
def IsCantorLipschitz (f : (ℕ → Bool) → ℕ → Bool) : Prop :=
  ∃ c : ℝ, ∀ a b, cantorDist (f a) (f b) ≤ c * cantorDist a b

open Classical in
/-- The number `d_n` of discrepancies among the first `n` terms. -/
noncomputable def discrepancies (a b : ℕ → Bool) (n : ℕ) : ℕ :=
  ((Finset.range n).filter fun i => a i ≠ b i).card

/-- **SUV p. 258.**  The *Besicovitch distance*: `ρ(a, b) = limsup d_n(a, b) / n`. -/
noncomputable def besicovitchDist (a b : ℕ → Bool) : ℝ :=
  limsup (fun n : ℕ => (discrepancies a b n : ℝ) / n) atTop

/-- **SUV p. 258.**  Transitivity of `f` for a distance `dist`: for every two sequences and every
`ε > 0` there is an orbit starting `ε`-close to the first and getting `ε`-close to the second. -/
def IsTransitiveFor (dist : (ℕ → Bool) → (ℕ → Bool) → ℝ) (f : (ℕ → Bool) → ℕ → Bool) : Prop :=
  ∀ a b, ∀ ε : ℝ, 0 < ε → ∃ (N : ℕ) (a' b' : ℕ → Bool),
    b' = f^[N] a' ∧ dist a a' < ε ∧ dist b b' < ε

/-- Transitivity for the Cantor distance. -/
abbrev IsCantorTransitive (f : (ℕ → Bool) → ℕ → Bool) : Prop := IsTransitiveFor cantorDist f

/-- **SUV p. 258.**  Transitivity for the Besicovitch distance. -/
abbrev IsBesicovitchTransitive (f : (ℕ → Bool) → ℕ → Bool) : Prop :=
  IsTransitiveFor besicovitchDist f

/-- The left shift, deleting the first bit of a sequence. -/
def leftShift (w : ℕ → Bool) : ℕ → Bool := fun i => w (i + 1)

private theorem isCantorTransitive_leftShift_iterate_apply
    (x : ℕ → Bool) (n i : ℕ) :
    leftShift^[n] x i = x (i + n) := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      dsimp [leftShift]
      rw [ih]
      congr 1
      omega

/-- **SUV p. 258.**  The left shift is transitive for the Cantor distance. -/
theorem isCantorTransitive_leftShift : IsCantorTransitive leftShift := by
  intro a b ε hε
  obtain ⟨M, hM⟩ : ∃ M : ℕ, (1 / 2 : ℝ) ^ M < ε := exists_pow_lt_of_lt_one hε (by norm_num)
  let a' (i : ℕ) : Bool := if i < M then a i else b (i - M)
  use M, a', b
  refine ⟨?_, ?_, ?_⟩
  · ext i
    rw [isCantorTransitive_leftShift_iterate_apply]
    dsimp [a']
    have hA : ¬(i + M < M) := by omega
    simp [hA]
  · apply lt_of_le_of_lt _ hM
    dsimp [cantorDist]
    rw [PiNat.dist_comm]
    apply (PiNat.mem_cylinder_iff_dist_le).mp
    intro i hi
    dsimp [a']
    have hB : i < M := hi
    simp [hB]
  · dsimp [cantorDist]
    rw [PiNat.dist_self]
    exact hε

/-- The left shift is Lipschitz for the Cantor distance, with constant `2`: if two sequences first
differ at place `k ≥ 1`, their shifts first differ at place `k - 1`. -/
theorem isCantorLipschitz_leftShift : IsCantorLipschitz leftShift := by
  use 2
  intro a b
  by_cases h : a = b
  · subst h
    have hz : cantorDist (leftShift a) (leftShift a) = 0 := PiNat.dist_self (leftShift a)
    have hza : cantorDist a a = 0 := PiNat.dist_self a
    rw [hz, hza]
    norm_num
  · have hc : cantorDist a b = (1 / 2) ^ PiNat.firstDiff a b := PiNat.dist_eq_of_ne h
    by_cases hl : leftShift a = leftShift b
    · have hz : cantorDist (leftShift a) (leftShift b) = 0 := by
        rw [hl]; exact PiNat.dist_self (leftShift b)
      rw [hz, hc]
      positivity
    · have hcl : cantorDist (leftShift a) (leftShift b) = (1 / 2) ^ PiNat.firstDiff (leftShift a)
        (leftShift b) := PiNat.dist_eq_of_ne hl
      rw [hcl, hc]
      have ha : (leftShift a) (PiNat.firstDiff (leftShift a) (leftShift b)) ≠ (leftShift b)
          (PiNat.firstDiff (leftShift a) (leftShift b)) := PiNat.apply_firstDiff_ne hl
      have hb : a (PiNat.firstDiff (leftShift a) (leftShift b) + 1) ≠ b (PiNat.firstDiff (leftShift
          a) (leftShift b) + 1) := ha
      have hle1 : PiNat.firstDiff a b ≤ PiNat.firstDiff (leftShift a) (leftShift b) + 1 := by
        by_contra! hcontra
        have hlt : PiNat.firstDiff (leftShift a) (leftShift b) + 1 < PiNat.firstDiff a b := hcontra
        have heq : a (PiNat.firstDiff (leftShift a) (leftShift b) + 1) = b (PiNat.firstDiff
            (leftShift a) (leftShift b) + 1) := PiNat.apply_eq_of_lt_firstDiff hlt
        exact hb heq
      have hp : (1 / 2 : ℝ) ^ PiNat.firstDiff (leftShift a) (leftShift b) = 2 * (1 / 2 : ℝ) ^
          (PiNat.firstDiff (leftShift a) (leftShift b) + 1) := by
        have : (1 / 2 : ℝ) ^ (PiNat.firstDiff (leftShift a) (leftShift b) + 1) = (1 / 2 : ℝ) ^
            PiNat.firstDiff (leftShift a) (leftShift b) * (1 / 2) := by ring
        rw [this]
        ring
      rw [hp]
      apply mul_le_mul_of_nonneg_left
      · apply pow_le_pow_of_le_one
        · norm_num
        · norm_num
        · exact hle1
      · norm_num

end Kolmogorov.Applications
