/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.StoppingComplexity.Game

/-!
# Counting dyadic cells for the marker round

Elementary facts about dyadic cells and valid schedules used by the marker round (blueprint
part 02, §3–§4). Cells are nonempty, so a cell is never disjoint from itself and pairwise
disjoint cells are pairwise distinct. The dyadic pigeonhole bound of LEM-ROUND-02: distinct
cells of depth `b` whose depth-`a` ancestors lie among the cells of a list `K` number at most
`|K| · 2^(b - a)`. A cell of depth `D` starting before `U` has index below `⌈U / 2^{-D}⌉`, the
number `N` of coarse cells meeting `[0, U)` (§3). The depth-`D` descendants of a cell of depth at
most `D` lie inside it (LEM-ROUND-05). For a valid schedule, `δ_{j-1} < δ_j` and
`h_j = L_j s_j` (§3).
-/

namespace Kolmogorov

/-- The left endpoint of a cell lies strictly before its right endpoint (cells are nonempty).
Blueprint 02 DEF-02. -/
theorem cellLeft_lt_cellRight (c : DyadicCell) : cellLeft c < cellRight c := by
  have hpos : 0 < cellLength c := by
    unfold cellLength
    positivity
  rw [cellLength_eq_cellRight_sub_cellLeft] at hpos
  linarith

/-- A cell is never disjoint from itself. Blueprint 02 DEF-02. -/
theorem not_cellsDisjoint_self (c : DyadicCell) : ¬ CellsDisjoint c c := by
  have h := cellLeft_lt_cellRight c
  rintro (h' | h') <;> linarith

/-- Dyadic pigeonhole: pairwise distinct cells of depth `b` whose depth-`a` ancestors lie among
the cells of `K` number at most `|K| · 2^(b - a)` (a depth-`a` cell has `2^(b - a)` depth-`b`
descendants). Blueprint 02 LEM-ROUND-02. -/
theorem length_le_mul_of_cellAncestor_mem {cs K : List DyadicCell} {a b : ℕ} (hnd : cs.Nodup)
    (hd : ∀ c ∈ cs, c.1 = b) (hK : ∀ c ∈ cs, cellAncestor c a ∈ K) :
    cs.length ≤ K.length * 2 ^ (b - a) := by
  have hnd' : (cs.map Prod.snd).Nodup :=
    hnd.map_on fun c hc c' hc' h => Prod.ext ((hd c hc).trans (hd c' hc').symm) h
  have hsub : cs.map Prod.snd ⊆
      K.flatMap fun k => List.range' (k.2 * 2 ^ (b - a)) (2 ^ (b - a)) := by
    intro i hi
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hi
    refine List.mem_flatMap.2 ⟨cellAncestor c a, hK c hc, ?_⟩
    have hP : 0 < 2 ^ (b - a) := by positivity
    have h1 := Nat.div_mul_le_self c.2 (2 ^ (b - a))
    have h2 := Nat.lt_div_mul_add (a := c.2) hP
    rw [List.mem_range'_1]
    simp only [cellAncestor, hd c hc]
    omega
  have hlen := (hnd'.subperm hsub).length_le
  simpa [List.length_flatMap, List.map_const', List.sum_replicate] using hlen

/-- A cell of depth `D` starting before `U` is one of the `⌈U / 2^{-D}⌉` cells of depth `D`
meeting `[0, U)`: its index is below that number. Blueprint 02 §3 (the count `N`). -/
theorem index_lt_ceil_of_cellLeft_lt {U : ℚ} {c : DyadicCell} (h : cellLeft c < U) :
    c.2 < ⌈U / (1 / 2 : ℚ) ^ c.1⌉₊ := by
  rw [Nat.lt_ceil, one_div_pow, div_div_eq_mul_div, div_one]
  unfold cellLeft at h
  rwa [div_lt_iff₀ (by positivity)] at h

/-- The depth-`D` descendant `(D, a.2 · 2^(D - a.1) + i)`, `i < 2^(D - a.1)`, of a cell `a` of
depth at most `D` lies inside `a`. Blueprint 02 LEM-ROUND-05. -/
theorem cellSubset_descendant {a : DyadicCell} {D i : ℕ} (hD : a.1 ≤ D)
    (hi : i < 2 ^ (D - a.1)) : CellSubset (D, a.2 * 2 ^ (D - a.1) + i) a := by
  rw [cellSubset_iff_refined]
  simp only [max_eq_left hD, Nat.sub_self, pow_zero, mul_one, add_one_mul]
  omega

/-- For a valid schedule and `1 ≤ j ≤ R`, the coarse depth is below the fine depth:
`δ_{j-1} < δ_j`. Blueprint 02 DEF-03 / §3. -/
theorem GameSchedule.depth_pred_lt_depth {S : GameSchedule} (hS : S.IsValid) {j : ℕ}
    (hj1 : 1 ≤ j) (hjR : j ≤ S.R) : S.depth (j - 1) < S.depth j := by
  have hlen := hS.2.1
  have hdl := hS.1
  unfold GameSchedule.R at hjR
  unfold GameSchedule.depth
  rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
  exact List.pairwise_iff_getElem.1 hS.2.2.2.1 _ _ (by omega) (by omega) (by omega)

/-- `h_j = L_j s_j` for `1 ≤ j ≤ R`: the coarse length is the ratio times the fine length.
Blueprint 02 §3. -/
theorem GameSchedule.coarseLength_eq_ratio_mul_fineLength {S : GameSchedule} (hS : S.IsValid)
    {j : ℕ} (hj1 : 1 ≤ j) (hjR : j ≤ S.R) :
    S.coarseLength j = (S.ratio j : ℚ) * S.fineLength j := by
  have hle := (GameSchedule.depth_pred_lt_depth hS hj1 hjR).le
  obtain ⟨e, he⟩ : ∃ e, S.depth j = S.depth (j - 1) + e := ⟨_, (Nat.add_sub_cancel' hle).symm⟩
  unfold GameSchedule.coarseLength GameSchedule.ratio GameSchedule.fineLength
  rw [he, Nat.add_sub_cancel_left, pow_add, Nat.cast_pow, Nat.cast_ofNat]
  field_simp
  rw [← mul_pow]
  norm_num

end Kolmogorov
