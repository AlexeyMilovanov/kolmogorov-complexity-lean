import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Realization.ProfileExistence

/-! # Curve realization: the theorem that assembles the two halves.

`exists_string_with_profile` is the trailing declaration of
`KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Realization.ProfileExistence`, split off here
so that that module stays under the library's 1000-line cap.  It feeds the generic point of
`exists_point_in_all_coverableSets` to the upper half `realization_upper` and relaxes the
generic point's avoidance clause to the common slack. -/

namespace Kolmogorov
open scoped ENNReal
open Kolmogorov.CodedFiniteDistribution

/-- The profile / curve realization theorem.

For every admissible `ProfileCurve h` there is a length-`n` string `x` whose
description profile follows the curve up to logarithmic slack: `x` has an
`(i + O(log n), h i + O(log n))`-description for every `i` (the profile contains the
curve, upper half) and, wherever `h i` exceeds the slack, `x` has *no*
`(i, h i - O(log n))`-description (the profile does not cross below the curve, lower
half). -/
theorem exists_string_with_profile (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c_real, ∀ c n kx m h, ProfileCurve U c n kx m h →
      ∃ x : BitString, x.length = n ∧
        (∀ i, InDescriptionProfile U x (i + m + logSlack c_real n) (h i + logSlack c_real n))
            ∧
        (∀ i, ¬ InDescriptionProfile U x i (h i - (m + logSlack c_real n)) ∨ h i ≤ m +
            logSlack c_real n)
            := by
  obtain ⟨c_gen, hgen⟩ := exists_point_in_all_coverableSets U hU
  obtain ⟨c_up, hup⟩ := realization_upper U
  refine ⟨c_gen + c_up, fun c n kx m h hcurve => ?_⟩
  -- The generic point: lies in every coverable set, and avoids every small description.
  obtain ⟨x, hxlen, hxmem, hxavoid⟩ := hgen c n kx m h hcurve
  have hslack_gen : logSlack c_gen n ≤ logSlack (c_gen + c_up) n :=
    logSlack_mono_left (Nat.le_add_right _ _) n
  refine ⟨x, hxlen, fun i => ?_, fun i => ?_⟩
  · -- Upper half
    by_cases hle : i ≤ kx + logSlack c n
    · exact hup c_gen c n kx m h hcurve x (fun j hj => hxmem j hj) i hle
    · have h_k_le : kx + logSlack c n ≤ kx + logSlack c n := le_rfl
      have hF_k := hup c_gen c n kx m h hcurve x (fun j hj => hxmem j hj) (kx + logSlack c n)
          h_k_le
      have hi_gt := not_le.mp hle
      have hi_le : kx + logSlack c n ≤ i := le_of_lt hi_gt
      have hF_k' : InDescriptionProfile U x (i + m + logSlack (c_gen + c_up) n) (h (kx +
          logSlack c n) + logSlack (c_gen + c_up) n) :=
        hF_k.mono_i (by omega)
      have h_zero : h (kx + logSlack c n) = 0 := hcurve.bottom
      rw [h_zero] at hF_k'
      have h_zero_i : h i = 0 := by
        have h_antitone := hcurve.antitone hi_le
        rw [h_zero] at h_antitone
        omega
      rw [h_zero_i]
      exact hF_k'
  · -- Lower half: relax the generic point's avoidance clause to the larger slack.
    rcases hxavoid i with hno | hle
    · -- No `(i, h i - (m + logSlack c_gen n))`-description exists with the larger
      -- subtrahend.
      refine Or.inl (fun hcontra => hno ?_)
      have h_prof : InDescriptionProfile U x i (h i - (m + logSlack c_gen n)) :=
        hcontra.mono_j (Nat.sub_le_sub_left (Nat.add_le_add_left hslack_gen m) (h i))
      exact mem_badSetsUnion_of_inDescriptionProfile U n h m c_gen i h_prof
    · exact Or.inr (le_trans hle (Nat.add_le_add_left hslack_gen m))

/- Gate H1: antistochastic / extremal-profile strings exist.

An *antistochastic* string of length `n` and complexity `k` should have an almost
minimal description profile.  For budgets below `k`, every `(i, j)`-description
must lie near the full-cube boundary.  The correct lower-bound shape is
`i + j >= n - O(log n)`, not `j >= n - O(log n)` by itself.

This gate should be treated as a corollary of Gate H0 (`exists_string_with_profile`),
not as an independent construction.  Use the simple extremal curve
`h i = if i < k then n - i else 0` (encoded by the parameters `n,k`, hence with
only logarithmic/`m` overhead) and apply the lower half of the curve-realization
theorem.  That lower half gives `j >= h i - O(log n)` for `i` below the complexity
threshold, hence `i + j >= n - O(log n)`.  The endpoint/right-tail lemmas give
that `KPPlain U x` is equal to `k` up to `O(log n)`.

This replaces two earlier mistakes: a version with
`forall i >= k, not InDescriptionProfile U x i 0`, which is false because the singleton
`{x}` is available once `i >= K(x)`, and an overstrong version asking for
`j >= n - O(log n)` instead of the profile-boundary inequality `i + j >= n - O(log n)`. -/
-- Gate H1a: curve code complexity; `primrec_natCode` lives in
-- `AlgorithmicStatistics/CodedComputability.lean`.

end Kolmogorov
