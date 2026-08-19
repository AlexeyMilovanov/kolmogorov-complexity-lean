import KolmogorovMathlib.Restricted.Family
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Basic

/-!
# Finite sampled-run combinatorics

This file contains the parts of the sampled coupled-run argument that are stated
independently of the chronological transition system; that system itself is
built in `Restricted.FamilyCurve.CoupledRun`.
-/

namespace Kolmogorov

/-- If `s₀` is the least sampled scale whose live count is below its threshold,
then every earlier sampled scale is still safe. -/
lemma restricted_min_failed_scale_prefix_safe
    (N : ℕ) (live threshold : ℕ → ℕ)
    (hfail : ∃ s : ℕ, s ≤ N ∧ live s < threshold s) :
    ∀ r < Nat.find hfail, threshold r ≤ live r := by
  intro r hr
  have hmin := Nat.find_spec hfail
  have hnot := Nat.find_min hfail hr
  apply Nat.le_of_not_gt
  intro hlt
  exact hnot ⟨(Nat.le_of_lt hr).trans hmin.1, hlt⟩

/-- An end-to-end density inequality with a nonempty initial live set forces a
nonempty terminal live set.  `restricted_rebuild_suffix_density` supplies the
inequality for one rebuilt suffix; the chronological run must still show that
it applies at each rebuild. -/
lemma restricted_rebuild_suffix_terminal_nonempty
    (s k overheadBound : ℕ) (t : ℕ → ℕ)
    (live : ℕ → Finset BitString)
    (hLive : (live s).Nonempty)
    (hdensity :
      (2 ^ t k) * (live s).card ≤
        (overheadBound ^ (k - s) * 2 ^ t s) * (live k).card) :
    (live k).Nonempty := by
  apply Finset.nonempty_iff_ne_empty.mpr
  intro hempty
  rw [hempty] at hdensity
  simp only [Finset.card_empty, Nat.mul_zero] at hdensity
  have hpos : 0 < (2 ^ t k) * (live s).card :=
    Nat.mul_pos (pow_pos (by decide) _) (Finset.card_pos.mpr hLive)
  omega

/-- Small-event deletion blocks are pairwise disjoint. -/
lemma restricted_self_rebuild_deletedBlocks_pairwiseDisjoint
    {α : Type*} (S : ℕ → Finset α) (D : ℕ → Finset α)
    (h_mono : ∀ i j, i ≤ j → S j ⊆ S i)
    (h_sub : ∀ i, D i ⊆ S i)
    (h_disj : ∀ i, Disjoint (D i) (S (i + 1))) :
    (Set.univ : Set ℕ).PairwiseDisjoint D := by
  have key : ∀ i j, i < j → Disjoint (D i) (D j) := by
    intro i j hij
    apply Finset.disjoint_left.mpr
    intro x hxi hxj
    have hxS : x ∈ S (i + 1) :=
      h_mono (i + 1) j (by omega) (h_sub j hxj)
    exact (Finset.disjoint_left.mp (h_disj i)) hxi hxS
  intro i _hi j _hj hij
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact key i j hij
  · exact (key j i hji).symm

/-- The number of rebuilds is bounded by the sum of large bad appearances
and small bad volume divided by threshold. -/
lemma restricted_self_rebuilds_le
    (large_appearances small_bad_volume threshold : ℕ)
    (rebuilds_large rebuilds_small : ℕ)
    (hthreshold : 0 < threshold)
    (h_large : rebuilds_large ≤ large_appearances)
    (h_small : rebuilds_small * threshold ≤ small_bad_volume) :
    rebuilds_large + rebuilds_small ≤ large_appearances + small_bad_volume / threshold := by
  exact Nat.add_le_add h_large
    ((Nat.le_div_iff_mul_le hthreshold).mpr h_small)

/-- Arithmetic final step for one sampled scale: after charging large and
small rebuilds, the absorbed event bound controls the total version count. -/
lemma restrictedSampledRun_versions_le
    (n c t_s : ℕ)
    (large_appearances small_bad_volume threshold : ℕ)
    (rebuilds_large rebuilds_small : ℕ)
    (hthreshold : 0 < threshold)
    (h_large : rebuilds_large ≤ large_appearances)
    (h_small : rebuilds_small * threshold ≤ small_bad_volume)
    (h_bound : large_appearances + small_bad_volume / threshold + 1 ≤ 2 ^ (t_s + sqrtSlack c n)) :
    rebuilds_large + rebuilds_small + 1 ≤ 2 ^ (t_s + sqrtSlack c n) := by
  exact (Nat.add_le_add_right
    (restricted_self_rebuilds_le large_appearances small_bad_volume threshold
      rebuilds_large rebuilds_small hthreshold h_large h_small) 1).trans h_bound

end Kolmogorov
