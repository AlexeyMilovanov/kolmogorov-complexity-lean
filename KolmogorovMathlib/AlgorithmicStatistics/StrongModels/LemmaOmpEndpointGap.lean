import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.LemmaOmp
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.ProfileOmpExactObstruction

/-!
# The exact-`epsilon` corner of Lemma `omp` for a controlled endpoint gap

`ProfileOmpRadius.lean` records two sufficient conditions under which the
shifted diagonal defining `m_P_eps` is met at complexity `0`, so that the frozen
exact-`epsilon` Lemma `omp` conclusion follows from the uniform bound
`condK_omegaFixedCode_zero_le_of_profileNeighborhood`:

* `m_P_eps_eq_zero_of_isUnitDropProfileSet` (jump-free profile sets), and
* `m_P_eps_eq_zero_of_n_P_le` (height endpoint within
  `k_P + epsilon + c log`), which only uses that `P` is an upper set.

The second condition is not optimal: admissibility gives more than upward
closure, namely the *step* (shift) rule `(a, b + c) ∈ P → (a + b, c) ∈ P`.
Applying the step rule to the height endpoint `(0, n_P)` before closing upwards
buys one extra `epsilon`:

`m_P_eps_eq_zero_of_n_P_le_add_two_mul` — for an **admissible** `P`,
`n_P ≤ k_P + 2 * epsilon + c * log(k_P + 2 * epsilon)` already forces
`m_P_eps P k_P epsilon c = 0`.

This is sharp for the geometry available here: the kernel-checked obstruction
`not_m_P_eps_le_of_neighboring_diagonal_profile` (`ProfileOmpExactObstruction`)
lives at `n_P = k_P + 3 * epsilon`.

The consequence for the frozen interface is `lemma_omp_endpointGap` below: the
frozen `LemmaOmpStatement` holds verbatim — at the exact radius `epsilon` — for
every admissible profile set whose endpoints satisfy `n_P ≤ k_P + 2 * epsilon`.
It strictly extends `lemma_omp_narrow` (`n_P ≤ k_P + epsilon`).

We also record the unconditional bound `m_P_eps ≤ k_P - epsilon`
(`m_P_eps_le_k_P_sub_of_isUpperSet`), which is exactly the value taken by the
obstruction profile.
-/

namespace Kolmogorov

open Kolmogorov.CodedFiniteDistribution

/-! The two profile-geometry facts used below,
`m_P_eps_eq_zero_of_n_P_le_add_two_mul` (the height endpoint reaches the shifted
diagonal at complexity `0` once `n_P ≤ k_P + 2 * epsilon + c * log`) and
`m_P_eps_le_k_P_sub_of_isUpperSet` (the unconditional bound
`m_P_eps ≤ k_P - epsilon`), are stated and proved in `ProfileOmpRadius`, so that
the exact-radius corner reduction in `LemmaOmp` can use them as well. -/

/-- **The `2 * epsilon` endpoint gap is sharp.**

For every constant `C` there is an admissible profile set with finite endpoints
and `n_P = k_P + 3 * epsilon` whose shifted diagonal at radius `epsilon` is *not*
met at complexity `0`.  Hence the hypothesis of
`m_P_eps_eq_zero_of_n_P_le_add_two_mul` cannot be relaxed from `2 * epsilon` to
`3 * epsilon`, and the exact-radius blind spot of Lemma `omp` starts exactly
there.  The witness is the jumpy obstruction profile of
`ProfileOmpExactObstruction`, taken at a scale where `C * log` is negligible. -/
theorem exists_admissible_n_P_eq_add_three_mul_and_m_P_eps_ne_zero (C : Nat) :
    ∃ (P : Set (Nat × Nat)) (kp np epsilon : Nat),
      IsAdmissibleProfileSet P ∧
      epsilon ≤ kp ∧
      k_P P = (kp : ENat) ∧
      n_P P = (np : ENat) ∧
      np = kp + 3 * epsilon ∧
      m_P_eps P kp epsilon C ≠ 0 := by
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
  refine ⟨ompObstructionProfile E, 4 * E, 7 * E, E,
    isAdmissibleProfileSet_ompObstructionProfile E, by omega,
    k_P_ompObstructionProfile E, n_P_ompObstructionProfile E, by omega, ?_⟩
  have hlow : ((3 * E : Nat) : ENat) ≤
      m_P_eps (ompObstructionProfile E) (4 * E) E C := by
    refine le_sInf ?_
    rintro _ ⟨t, rfl, ht⟩
    have hL : C * (Nat.bits (4 * E + 2 * E)).length ≤ C * (K + 3) :=
      Nat.mul_le_mul_left _ (hbits _ (by omega))
    have : 3 * E ≤ t := by
      rcases ht with h | h <;> simp only at h <;> omega
    exact_mod_cast this
  intro hzero
  rw [hzero] at hlow
  have : 3 * E ≤ 0 := by exact_mod_cast hlow
  omega

/-- The frozen `LemmaOmpStatement` restricted to admissible profile sets whose
height endpoint exceeds the complexity endpoint by at most `2 * epsilon`.
Everything else, including the exact neighbourhood radius `epsilon` inside
`m_P_eps`, is verbatim the frozen statement. -/
def LemmaOmpEndpointGapStatement (V : Map) : Prop :=
  ∃ c : Nat,
    ∀ (P : Set (Nat × Nat)) (epsilon kp np mp_eps : Nat)
        (x : BitString) (q : Nat.Partrec.Code),
    IsAdmissibleProfileSet P →
    IsCodeFor q V →
    epsilon ≤ kp →
    k_P P = (kp : ENat) →
    n_P P = (np : ENat) →
    np ≤ kp + 2 * epsilon →
    m_P_eps P kp epsilon c = (mp_eps : ENat) →
    x ∈ profileNeighborhood V P epsilon →
    condK V (omegaFixedCode q mp_eps) x ≤ (logSlack c np : ENat)

/-- **Lemma `omp` at the exact radius `epsilon`, for a controlled endpoint gap
(fully proved).**

When `n_P ≤ k_P + 2 * epsilon`, the height endpoint of an admissible `P`
reaches the shifted diagonal at complexity `0`
(`m_P_eps_eq_zero_of_n_P_le_add_two_mul`), so the target Ω-index vanishes and
`condK_omegaFixedCode_zero_le_of_profileNeighborhood` gives the frozen
conclusion.  This strictly extends `lemma_omp_narrow`, whose hypothesis is
`n_P ≤ k_P + epsilon`. -/
theorem lemma_omp_endpointGap (V : Map) (hV : isOptimalConditional V) :
    LemmaOmpEndpointGapStatement V := by
  obtain ⟨c, hc⟩ := condK_omegaFixedCode_zero_le_of_profileNeighborhood V hV
  refine ⟨c, ?_⟩
  intro P epsilon kp np mp_eps x q hadm hq heps hkP hnP hgap hmpeps hxnb
  have hzero : mp_eps = 0 := by
    have h := m_P_eps_eq_zero_of_n_P_le_add_two_mul P kp np epsilon c hadm hnP
      (by omega)
    rw [h] at hmpeps
    exact_mod_cast hmpeps.symm
  subst hzero
  exact hc P epsilon kp np x q hadm hq heps hkP hnP hxnb

end Kolmogorov
