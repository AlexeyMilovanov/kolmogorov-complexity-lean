import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.ProfileOmpRadius

/-!
# The exact-`epsilon` corner of Lemma `omp` is unreachable from profile data

`ProfileOmpRadius.lean` shows that the exact-`epsilon` conclusion
`m_P_eps P k_P epsilon c ≤ i + logSlack c n_P` fails for an admissible profile
set `P` together with a transferred neighbourhood point obeying every numerical
budget of the standard-block route
(`not_m_P_eps_le_neighborhood_point_add_logSlack`).

That counterexample is stated purely in terms of `P` and one transferred point.
One could still hope that the *shape* of the profile set of an actual string —
which is admissible, lies within `epsilon` of `P` in the two-sided Hausdorff
sense used by `profileNeighborhood`, and whose every point obeys the two-part
lower bound `C(x) ≤ i + j` — rules the counterexample out.

The theorem below shows it does not.  It exhibits, for every constant `C`:

* an admissible profile set `P` with finite endpoints `k_P = kp`, `n_P = np`;
* an admissible profile set `Q` playing the role of the profile set of a string
  `x` of complexity `m`: `Q` is the diagonal half-plane
  `{(a, b) | m ≤ a + b}`, i.e. exactly the profile shape of an incompressible
  string of length `m`, so *every* point of `Q` obeys the two-part lower bound
  and both endpoints of `Q` equal `m`;
* the two-sided `epsilon`-closeness `ProfileSetsWithinNeighborhood Q P epsilon`
  that membership of `x` in `profileNeighborhood V P epsilon` unfolds to;
* the endpoint relations `m ≤ kp + 2 * epsilon`, `kp ≤ m + 2 * epsilon` and
  `m ≤ 3 * np + logSlack C np` that the endpoint estimates supply;
* a standard-block point `(i, j) ∈ Q` with the two-part budget
  `i + j ≤ m + logSlack C m`;

for which nonetheless

`m_P_eps P kp epsilon C > i + logSlack C np`.

Consequently the remaining exact-`epsilon` obligation
`ExactOmpStandardBlockCornerStatement` cannot be discharged by *any* argument
that uses only the profile set of `x`, its closeness to `P`, the two-part lower
and upper bounds, and the endpoint estimates: a proof must use finer
information about the standard block itself (its position in the completed
bound-`C(x)` enumeration), or the radius has to be widened as in
`lemma_omp_three_radius`.
-/

namespace Kolmogorov

/-- The jumpy profile set of the obstruction: its boundary height falls from
`7 * E` to `0` in one step of the complexity coordinate, at `4 * E`. -/
def ompObstructionProfile (E : Nat) : Set (Nat × Nat) :=
  {p | 4 * E ≤ p.1 ∨ 7 * E ≤ p.1 + p.2}

theorem isAdmissibleProfileSet_ompObstructionProfile (E : Nat) :
    IsAdmissibleProfileSet (ompObstructionProfile E) := by
  refine ⟨⟨(4 * E, 0), Or.inl le_rfl⟩, ?_, ?_⟩
  · rintro ⟨a, b⟩ ⟨a', b'⟩ ⟨ha, hb⟩ h
    simp only at ha hb
    rcases h with h | h
    · exact Or.inl (by simp only at h ⊢; omega)
    · exact Or.inr (by simp only at h ⊢; omega)
  · rintro a b d h
    rcases h with h | h
    · exact Or.inl (by simp only at h ⊢; omega)
    · exact Or.inr (by simp only at h ⊢; omega)

theorem k_P_ompObstructionProfile (E : Nat) :
    k_P (ompObstructionProfile E) = ((4 * E : Nat) : ENat) := by
  refine le_antisymm (sInf_le ⟨4 * E, rfl, Or.inl le_rfl⟩) (le_sInf ?_)
  rintro _ ⟨t, rfl, ht⟩
  have : 4 * E ≤ t := by
    rcases ht with h | h <;> simp only at h <;> omega
  exact_mod_cast this

theorem n_P_ompObstructionProfile (E : Nat) :
    n_P (ompObstructionProfile E) = ((7 * E : Nat) : ENat) := by
  refine le_antisymm (sInf_le ⟨7 * E, rfl, Or.inr (by simp only; omega)⟩) (le_sInf ?_)
  rintro _ ⟨t, rfl, ht⟩
  have : 7 * E ≤ t := by
    rcases ht with h | h <;> simp only at h <;> omega
  exact_mod_cast this

/-- The diagonal profile of complexity level `6 * E` — the profile shape of an
incompressible string of that length — is `E`-close to the jumpy obstruction
profile in the two-sided sense used by `profileNeighborhood`. -/
theorem profileSetsWithinNeighborhood_diagonal_ompObstructionProfile (E : Nat) :
    ProfileSetsWithinNeighborhood
      (diagonalProfileSet (6 * E)) (ompObstructionProfile E) E := by
  constructor
  · rintro ⟨a, b⟩ hq
    simp only [diagonalProfileSet, Set.mem_setOf_eq] at hq
    refine ⟨(a, b + E), Or.inr (by simp only; omega), ?_⟩
    unfold natPairLInfDistance
    simp only
    omega
  · rintro ⟨a, b⟩ hp
    refine ⟨(a + E, b + E), ?_, ?_⟩
    · simp only [diagonalProfileSet, Set.mem_setOf_eq]
      rcases hp with h | h <;> simp only at h <;> omega
    · unfold natPairLInfDistance
      simp only
      omega

/-- **The exact-`epsilon` corner is not implied by the profile data of a
neighbourhood member.**

For every constant `C` there are an admissible profile set `P` and an
admissible profile set `Q` with all of the following properties, where `Q` is
the diagonal half-plane at level `m` (the profile shape of an incompressible
string of complexity `m`, so every one of its points obeys the two-part lower
bound `m ≤ i + j`):

* `Q` and `P` are `epsilon`-close in the two-sided Hausdorff sense of
  `profileNeighborhood`, and `epsilon ≤ k_P P`;
* both endpoints of `Q` equal `m`, and `m` and `k_P P` differ by at most
  `2 * epsilon`, with `m ≤ 3 * n_P P + logSlack C (n_P P)`;
* `(i, j) ∈ Q` is a two-part description point with `i + j ≤ m + logSlack C m`;

and yet `m_P_eps P kp epsilon C > i + logSlack C np`.

Hence the exact-`epsilon` corner needs strictly more than the profile geometry
of the neighbourhood member. -/
theorem not_m_P_eps_le_of_neighboring_diagonal_profile (C : Nat) :
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
  refine ⟨ompObstructionProfile E, diagonalProfileSet (6 * E),
    4 * E, 7 * E, 6 * E, E, 0, 6 * E,
    isAdmissibleProfileSet_ompObstructionProfile E,
    isAdmissibleProfileSet_diagonalProfileSet _,
    profileSetsWithinNeighborhood_diagonal_ompObstructionProfile E,
    ?_, k_P_diagonalProfileSet _, n_P_diagonalProfileSet _, by omega,
    k_P_ompObstructionProfile E, n_P_ompObstructionProfile E,
    ?_, by omega, by omega, by omega, by omega, ?_⟩
  · rintro ⟨a, b⟩ hq
    simpa [diagonalProfileSet] using hq
  · simp [diagonalProfileSet]
  · -- the failure of the exact-`epsilon` conclusion
    intro hle
    have hlow : ((3 * E : Nat) : ENat) ≤ m_P_eps (ompObstructionProfile E) (4 * E) E C := by
      refine le_sInf ?_
      rintro _ ⟨t, rfl, ht⟩
      have hL : C * (Nat.bits (4 * E + 2 * E)).length ≤ C * (K + 3) :=
        Nat.mul_le_mul_left _ (hbits _ (by omega))
      have : 3 * E ≤ t := by
        rcases ht with h | h <;> simp only at h <;> omega
      exact_mod_cast this
    have hup : ((3 * E : Nat) : ENat) ≤
        ((0 : Nat) : ENat) + (logSlack C (7 * E) : ENat) := hlow.trans hle
    have hnat : 3 * E ≤ logSlack C (7 * E) := by
      have h : ((3 * E : Nat) : ENat) ≤ ((logSlack C (7 * E) : Nat) : ENat) := by
        simpa using hup
      exact_mod_cast h
    have hLb : (Nat.bits (7 * E)).length ≤ K + 3 := hbits _ (by omega)
    have hmul : C * (Nat.bits (7 * E)).length ≤ C * (K + 3) :=
      Nat.mul_le_mul_left _ hLb
    unfold logSlack at hnat
    omega

end Kolmogorov
