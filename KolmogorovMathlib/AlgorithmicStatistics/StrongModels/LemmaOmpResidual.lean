import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.LemmaOmpEndpointGap

/-!
# Sharpness of the residual branch of the exact-`epsilon` corner

`exact_omp_corner_of_hard_branch` (`LemmaOmp.lean`) reduces the exact-`epsilon`
standard-block corner `ExactOmpStandardBlockCornerStatement` to the residual
branch `ExactOmpHardBranchStatement`, whose five extra hypotheses are

* `i < k_P`,
* `k_P + C * log(k_P + 2 * epsilon) < i + r`,
* `k_P + 2 * epsilon + C * log(k_P + 2 * epsilon) < n_P`,
* `epsilon + logSlack C n_P < k_P`,
* `epsilon + logSlack C n_P + C * log(k_P + 2 * epsilon) < r`.

This module records that the reduction is sharp in the only sense available at
the level of profile geometry: the kernel-checked obstruction of
`ProfileOmpExactObstruction` — an admissible profile set `P` together with an
admissible, profile-shaped, two-sidedly `epsilon`-close diagonal `Q` and a
two-part point of `Q` violating the corner conclusion — satisfies all five of
those side conditions.  So none of the five discharged cases can be widened by
profile data alone, and the residual branch is exactly where the obstruction
lives.
-/

namespace Kolmogorov

open Kolmogorov.CodedFiniteDistribution

/-- **The profile-level obstruction lies inside the residual branch.**

For every constant `C` the witness of
`not_m_P_eps_le_of_neighboring_diagonal_profile` additionally satisfies the
five side conditions of `ExactOmpHardBranchStatement`.  Consequently the five
cases discharged by `exact_omp_corner_of_hard_branch` cannot be enlarged using
only admissibility, the endpoints, the two-part budget and the two-sided
`epsilon`-closeness of the profiles. -/
theorem exists_ompObstruction_in_hard_branch (C : Nat) :
    ∃ (P Q : Set (Nat × Nat)) (kp np m epsilon i j : Nat),
      IsAdmissibleProfileSet P ∧
      IsAdmissibleProfileSet Q ∧
      ProfileSetsWithinNeighborhood Q P epsilon ∧
      (∀ p ∈ Q, m ≤ p.1 + p.2) ∧
      k_P Q = (m : ENat) ∧
      n_P Q = (m : ENat) ∧
      epsilon ≤ kp ∧
      k_P P = (kp : ENat) ∧
      n_P P = (np : ENat) ∧
      (i, j) ∈ Q ∧
      i + j ≤ m + logSlack C m ∧
      m ≤ kp + 2 * epsilon ∧
      kp ≤ m + 2 * epsilon ∧
      m ≤ 3 * np + logSlack C np ∧
      i < kp ∧
      kp + C * (kp + 2 * epsilon).bits.length < i + j ∧
      kp + 2 * epsilon + C * (kp + 2 * epsilon).bits.length < np ∧
      epsilon + logSlack C np < kp ∧
      epsilon + logSlack C np + C * (kp + 2 * epsilon).bits.length < j ∧
      ¬ m_P_eps P kp epsilon C ≤ (i : ENat) + (logSlack C np : ENat) := by
  obtain ⟨K, hK⟩ := exists_two_pow_gt_linear C
  set E : Nat := 2 ^ K with hE
  have hE1 : 1 ≤ E := Nat.one_le_two_pow
  have hkey : C * (K + 3) + C < E := by
    have hle : C * (K + 3) + C ≤ C * (K + 5) := by nlinarith
    exact lt_of_le_of_lt hle hK
  have hbits : ∀ n : Nat, n < 8 * E → (Nat.bits n).length ≤ K + 3 := by
    intro n hn
    rw [Nat.size_eq_bits_len]
    refine Nat.size_le.mpr ?_
    have h8 : (8 : Nat) * E = 2 ^ (K + 3) := by
      rw [hE, pow_add]; ring
    omega
  have hL : C * (Nat.bits (4 * E + 2 * E)).length ≤ C * (K + 3) :=
    Nat.mul_le_mul_left _ (hbits _ (by omega))
  have hL7 : C * (Nat.bits (7 * E)).length ≤ C * (K + 3) :=
    Nat.mul_le_mul_left _ (hbits _ (by omega))
  refine ⟨ompObstructionProfile E, diagonalProfileSet (6 * E),
    4 * E, 7 * E, 6 * E, E, 0, 6 * E,
    isAdmissibleProfileSet_ompObstructionProfile E,
    isAdmissibleProfileSet_diagonalProfileSet _,
    profileSetsWithinNeighborhood_diagonal_ompObstructionProfile E,
    ?_, k_P_diagonalProfileSet _, n_P_diagonalProfileSet _, by omega,
    k_P_ompObstructionProfile E, n_P_ompObstructionProfile E,
    ?_, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    by simp only [logSlack]; omega, by simp only [logSlack]; omega,
    ?_⟩
  · rintro ⟨a, b⟩ hq
    simpa [diagonalProfileSet] using hq
  · simp [diagonalProfileSet]
  · -- the failure of the exact-`epsilon` conclusion
    intro hle
    have hlow :
        ((3 * E : Nat) : ENat) ≤ m_P_eps (ompObstructionProfile E) (4 * E) E C := by
      refine le_sInf ?_
      rintro _ ⟨t, rfl, ht⟩
      have : 3 * E ≤ t := by
        rcases ht with h | h <;> simp only at h <;> omega
      exact_mod_cast this
    have hup : ((3 * E : Nat) : ENat) ≤
        ((0 : Nat) : ENat) + (logSlack C (7 * E) : ENat) := hlow.trans hle
    have hnat : 3 * E ≤ logSlack C (7 * E) := by
      have h : ((3 * E : Nat) : ENat) ≤ ((logSlack C (7 * E) : Nat) : ENat) := by
        simpa using hup
      exact_mod_cast h
    unfold logSlack at hnat
    omega

/-- The obstruction profile is not excluded by the curve shape either: being
admissible with finite endpoints, it is the decoded epigraph of a genuine
`ProfileBoundary` object (`exists_profileBoundary_of_admissible`).  So requiring
the profile set of the frozen statement to come from a boundary curve does not
remove the obstruction. -/
theorem exists_profileBoundary_ompObstructionProfile (V : Map) (E : Nat) :
    ∃ b : ProfileBoundary V,
      b.k_P = 4 * E ∧ b.n_P = 7 * E ∧
        profileSet V b = ompObstructionProfile E :=
  exists_profileBoundary_of_admissible V (ompObstructionProfile E) (4 * E) (7 * E)
    (isAdmissibleProfileSet_ompObstructionProfile E)
    (k_P_ompObstructionProfile E) (n_P_ompObstructionProfile E)

end Kolmogorov
