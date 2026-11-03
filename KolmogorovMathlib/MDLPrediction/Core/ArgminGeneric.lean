/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.MDLPrediction.Core.Model

/-!
# Minimum of a score with finite complexity sublevels

The generic result is independent of probability measures. Positive masses at most one make
the negative logarithm nonnegative; finite complexity sublevels then contain every competitor
that can beat a fixed candidate.

Blueprint nodes: `base:argmin-generic`.
-/

namespace Kolmogorov.MDLPrediction

/-- A score `3k - log₂ m` has a minimum when the complexity sublevels are finite.
Blueprint node `base:argmin-generic`. -/
theorem base_argmin_generic {E : Type*} (k : E → ℕ) (m : E → ℝ)
    (hm : ∀ q, 0 < m q ∧ m q ≤ 1)
    (hfin : ∀ a, Set.Finite {q | k q ≤ a}) [Nonempty E] :
    ∃ q, ∀ r, 3 * (k q : ℝ) - Real.logb 2 (m q) ≤
      3 * (k r : ℝ) - Real.logb 2 (m r) := by
  have ⟨q0⟩ := ‹Nonempty E›
  let f (q : E) := 3 * (k q : ℝ) - Real.logb 2 (m q)
  have hlog : ∀ q, Real.logb 2 (m q) ≤ 0 := by
    intro q
    have h1 : 0 < m q := (hm q).1
    have h2 : m q ≤ 1 := (hm q).2
    rw [Real.logb]
    have hlogm : Real.log (m q) ≤ 0 := Real.log_nonpos (le_of_lt h1) h2
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    exact div_nonpos_of_nonpos_of_nonneg hlogm hlog2
  
  have h_bound : ∀ q, f q ≤ f q0 → k q ≤ ⌊f q0 / 3⌋₊ := by
    intro q hq
    have h3 : 3 * (k q : ℝ) ≤ f q := by
      dsimp [f]
      linarith [hlog q]
    have h4 : 3 * (k q : ℝ) ≤ f q0 := le_trans h3 hq
    have h5 : (k q : ℝ) ≤ f q0 / 3 := by linarith
    exact Nat.le_floor h5
  
  let S := {q | k q ≤ ⌊f q0 / 3⌋₊}
  have hS_fin : S.Finite := hfin _
  let S_finset := hS_fin.toFinset
  have hq0_in : q0 ∈ S_finset := by
    rw [Set.Finite.mem_toFinset]
    apply h_bound
    exact le_rfl
  
  have h_ne : S_finset.Nonempty := ⟨q0, hq0_in⟩
  
  obtain ⟨q_min, hq_min_in, hq_min_min⟩ := Finset.exists_min_image S_finset f h_ne
  use q_min
  intro r
  by_cases hr : r ∈ S_finset
  · exact hq_min_min r hr
  · have hr2 : ¬(f r ≤ f q0) := by
      intro hc
      have : r ∈ S_finset := by
        rw [Set.Finite.mem_toFinset]
        exact h_bound r hc
      contradiction
    have hr3 : f q0 < f r := not_le.mp hr2
    have hq_min_le_q0 : f q_min ≤ f q0 := hq_min_min q0 hq0_in
    exact le_trans hq_min_le_q0 (le_of_lt hr3)

end Kolmogorov.MDLPrediction
