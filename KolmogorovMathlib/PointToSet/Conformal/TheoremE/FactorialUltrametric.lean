/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.Conformal.Classical
import Mathlib.Topology.Bases

/-!
# A factorial ultrametric product

The product of finite sets with factorially growing cardinalities carries a first-difference
ultrametric with factorially shrinking scales. This module constructs that metric and proves
positivity, monotonicity and decay of its scales. `FactorialPackingGeometry` uses these facts
to equip the product with a compact presentation and estimate its packing contents, yielding
the actual-diameter packing counterexample accompanying Theorem E.
-/

namespace Kolmogorov.PointToSet

open Filter
open scoped Topology ENNReal Computability

/-- The number of branches at level `n`: two initially and `2 ^ n!` thereafter. -/
noncomputable def factorialBranching (n : ℕ) : ℕ :=
  if n = 0 then 2 else 2 ^ n.factorial

/-- Infinite sequences whose `n`th coordinate has `factorialBranching n` possible values. -/
def FactorialProduct : Type :=
  ∀ n : ℕ, Fin (factorialBranching n)

/-- The first-difference scale at level `n`: one initially and `2 ^ (-n!)` thereafter. -/
noncomputable def factorialScale (n : ℕ) : ℝ :=
  if n = 0 then 1 else (1 / 2 : ℝ) ^ n.factorial

open Classical in
/-- First-difference distance on the factorial product. -/
private noncomputable def factorialDist
    (x y : FactorialProduct) : ℝ :=
  if h : x = y then 0 else factorialScale (Nat.find (Function.ne_iff.mp h))

private lemma factorialDist_self
    (x : FactorialProduct) :
    factorialDist x x = 0 := by
  unfold factorialDist
  exact dite_eq_left rfl

/-- Each first-difference scale is strictly positive. -/
lemma factorialScale_pos (n : ℕ) :
    0 < factorialScale n := by
  unfold factorialScale
  split_ifs <;> positivity

private lemma factorialDist_eq_zero
    (x y : FactorialProduct) :
    factorialDist x y = 0 ↔ x = y := by
  classical
  constructor
  · intro h
    by_contra hne
    unfold factorialDist at h
    rw [dite_eq_right hne] at h
    have := factorialScale_pos (Nat.find (Function.ne_iff.mp hne))
    linarith
  · intro h
    subst h
    exact factorialDist_self x

private lemma factorialDist_comm
    (x y : FactorialProduct) :
    factorialDist x y = factorialDist y x := by
  classical
  by_cases h : x = y
  · subst h; rfl
  · unfold factorialDist
    have h_not' : y ≠ x := Ne.symm h
    rw [dite_eq_right h, dite_eq_right h_not']
    congr 1
    exact Nat.find_congr' ne_comm

private lemma factorialDist_nonneg
    (x y : FactorialProduct) :
    0 ≤ factorialDist x y := by
  classical
  by_cases h : x = y
  · subst h; rw [factorialDist_self]
  · unfold factorialDist
    rw [dite_eq_right h]
    exact (factorialScale_pos _).le

/-- Passing to a later first difference can only decrease the distance. -/
lemma factorialScale_antitone : Antitone factorialScale := by
  intro n m h
  unfold factorialScale
  by_cases hm : m = 0
  · subst hm
    have : n = 0 := by omega
    subst this
    rfl
  · by_cases hn : n = 0
    · subst hn
      simp only [hm, ↓reduceIte]
      exact pow_le_one₀ (by norm_num) (by norm_num)
    · simp only [hn, hm, ↓reduceIte]
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.factorial_le h)

private lemma factorialDist_le_max
    (x y z : FactorialProduct) :
    factorialDist x z ≤
      max (factorialDist x y)
        (factorialDist y z) := by
  classical
  by_cases hxy : x = y
  · subst hxy
    rw [factorialDist_self, max_eq_right (factorialDist_nonneg _ _)]
  by_cases hyz : y = z
  · subst hyz
    rw [factorialDist_self,
      factorialDist_comm x y, max_eq_left (factorialDist_nonneg _ _)]
  by_cases hxz : x = z
  · subst hxz
    rw [factorialDist_self]
    apply le_max_iff.mpr
    left
    apply factorialDist_nonneg
  unfold factorialDist
  rw [dite_eq_right hxy, dite_eq_right hyz, dite_eq_right hxz]
  apply le_max_iff.mpr
  have hf_xy : ∃ n, x n ≠ y n := Function.ne_iff.mp hxy
  have hf_yz : ∃ n, y n ≠ z n := Function.ne_iff.mp hyz
  have hf_xz : ∃ n, x n ≠ z n := Function.ne_iff.mp hxz
  let nxy := Nat.find hf_xy
  let nyz := Nat.find hf_yz
  let nxz := Nat.find hf_xz
  have hxy_agree : ∀ k < nxy, x k = y k := fun k hk ↦ by
    by_contra hne
    exact Nat.find_min hf_xy hk hne
  have hyz_agree : ∀ k < nyz, y k = z k := fun k hk ↦ by
    by_contra hne
    exact Nat.find_min hf_yz hk hne
  have hxz_diff : x nxz ≠ z nxz := Nat.find_spec hf_xz
  by_cases hxy_le_nyz : nxy ≤ nyz
  · left
    have hxy_le_nxz : nxy ≤ nxz := by
      by_contra hbad
      have hzx : nxz < nxy := by exact Nat.lt_of_not_ge hbad
      have h1 := hxy_agree nxz hzx
      have h2 := hyz_agree nxz (lt_of_lt_of_le hzx hxy_le_nyz)
      exact hxz_diff (h1.trans h2)
    exact factorialScale_antitone hxy_le_nxz
  · right
    have hnzy_lt_nxy : nyz < nxy := by exact lt_of_not_ge hxy_le_nyz
    have hyz_le_nxz : nyz ≤ nxz := by
      by_contra hbad
      have hzx : nxz < nyz := by exact Nat.lt_of_not_ge hbad
      have h1 := hxy_agree nxz (lt_trans hzx hnzy_lt_nxy)
      have h2 := hyz_agree nxz hzx
      exact hxz_diff (h1.trans h2)
    exact factorialScale_antitone hyz_le_nxz

/-- The factorial product admits an ultrametric whose distance between distinct points
is the scale at their first differing coordinate. -/
lemma exists_factorialProduct_ultrametric :
    ∃ _m : MetricSpace FactorialProduct,
    (∀ x y z : FactorialProduct, dist x z ≤ max (dist x y) (dist y z)) ∧
    (∀ x y : FactorialProduct, ∀ n : ℕ,
      (∀ k < n, x k = y k) → x n ≠ y n → dist x y = factorialScale n) := by
  classical
  let _m : MetricSpace FactorialProduct :=
    { dist := factorialDist
      dist_self := factorialDist_self
      dist_comm := factorialDist_comm
      dist_triangle := fun x y z ↦ by
        calc factorialDist x z
          _ ≤ max (factorialDist x y)
                (factorialDist y z) :=
            factorialDist_le_max x y z
          _ ≤ factorialDist x y +
                factorialDist y z := by
            apply max_le
            · linarith [factorialDist_nonneg y z]
            · linarith [factorialDist_nonneg x y]
      eq_of_dist_eq_zero := fun h ↦
        (factorialDist_eq_zero _ _).mp h }
  refine ⟨_m, factorialDist_le_max, ?_⟩
  intro x y n h_agree h_diff
  have hxy : x ≠ y := by
    intro hc
    subst hc
    exact h_diff rfl
  change factorialDist x y = _
  unfold factorialDist
  rw [dite_eq_right hxy]
  congr 1
  have hf_xy : ∃ k, x k ≠ y k := Function.ne_iff.mp hxy
  exact le_antisymm (Nat.find_le h_diff) (not_lt.mp fun hlt ↦ Nat.find_spec hf_xy (h_agree _ hlt))

/-- The first-difference scales eventually lie below every positive radius. -/
lemma factorialScale_eventually_lt
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ j : ℕ, N ≤ j → factorialScale j < ε := by
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨max N 1, fun j hj ↦ ?_⟩
  have hj1 : j ≠ 0 := by omega
  have hjN : N ≤ j := le_trans (le_max_left _ _) hj
  unfold factorialScale
  simp only [hj1, ↓reduceIte]
  calc (1 / 2 : ℝ) ^ j.factorial ≤ (1 / 2 : ℝ) ^ N :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (le_trans hjN (Nat.self_le_factorial j))
    _ < ε := hN

end Kolmogorov.PointToSet
