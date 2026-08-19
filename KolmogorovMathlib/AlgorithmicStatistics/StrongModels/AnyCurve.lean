import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.JointRealization
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.MixedFamilyVersion

/-!
# Strong realization of an arbitrary profile curve

This module combines the mixed-family construction with the static
plain/strong profile bridges.  Cylinders provide strong upper descriptions,
while the full-family event stream excludes every unrestricted description
below the target curve for the same survivor.
-/

namespace Kolmogorov

/-- VS40 `stat-any-curve-1`: every strictly decreasing admissible boundary is
simultaneously realized, up to square-root slack, by the ordinary description
profile and by the logarithmically strong description profile of one string. -/
theorem stat_any_curve_1
    (V U T : Map)
    (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U)
    (hT : IsOptimalTotalConditional T) :
    ∃ c : ℕ, ∀ (n k : ℕ) (t : ℕ → ℕ),
      k ≤ n →
      t 0 ≤ n →
      t k = 0 →
      (∀ i : ℕ, i < k → t (i + 1) < t i) →
      ∃ x : BitString, ∃ n' : ℕ,
        x.length = n' ∧
        n ≤ n' ∧
        n' ≤ n + logSlack c n ∧
        plainK V x ≤ (k + sqrtSlack c n : ENat) ∧
        (k : ENat) ≤ plainK V x + (sqrtSlack c n : ENat) ∧
        ProfileSetsWithinNeighborhood
          (plainDescriptionProfileSet V x)
          {q | FamilyCurveTarget k t q.1 q.2}
          (sqrtSlack c n) ∧
        ProfileSetsWithinNeighborhood
          (strongDescriptionProfileSet V T x (logSlack c n))
          {q | FamilyCurveTarget k t q.1 q.2}
          (sqrtSlack c n) := by
  obtain ⟨cPost, hPost⟩ :=
    stat_any_curve_1_of_joint_prefix_realization V U T hV hU hT
  obtain ⟨cRun, hRun⟩ :=
    prop_family_curve_against U hU cylinderFamily fullFamily
      cylinderFamily_hasPolynomialOverhead cylinderFamily_le_fullFamily
  obtain ⟨cOut, hcOutBound, hOut⟩ := hPost cRun
  let c := cPost * (cRun + 1) + cRun
  refine ⟨c, ?_⟩
  intro n k t hkn ht0 htk hstrict
  obtain ⟨x, n', hxlen, hnlen, hnlenUpper, hKP,
      hCylinder, hFull⟩ :=
    hRun n k t hkn ht0 htk hstrict
  obtain ⟨hPlainUpper, hPlainLower, hPlain, hStrong⟩ :=
    hOut n k t x n' hkn ht0 htk hstrict hxlen hnlen
      hnlenUpper hKP hCylinder hFull
  have hcRun : cRun ≤ c := by
    dsimp [c]
    omega
  have hcOut : cOut ≤ c := by
    exact hcOutBound.trans (Nat.le_add_right _ _)
  have hsqrt :
      sqrtSlack cOut n ≤ sqrtSlack c n :=
    sqrtSlack_mono_left hcOut n
  have hlog :
      logSlack cOut n ≤ logSlack c n :=
    logSlack_mono_left hcOut n
  have hStrongFinal :
      ProfileSetsWithinNeighborhood
        (strongDescriptionProfileSet V T x (logSlack c n))
        {q | FamilyCurveTarget k t q.1 q.2}
        (sqrtSlack c n) := by
    constructor
    · intro q hq
      have hqPlain :
          q ∈ plainDescriptionProfileSet V x :=
        strongDescriptionProfileSet_subset_plain V T x
          (logSlack c n) hq
      obtain ⟨r, hr, hdr⟩ := hPlain.1 q hqPlain
      exact ⟨r, hr, hdr.trans hsqrt⟩
    · intro q hq
      obtain ⟨r, hr, hdr⟩ := hStrong.2 q hq
      exact ⟨r,
        strongDescriptionProfileSet_mono_epsilon V T x hlog hr,
        hdr.trans hsqrt⟩
  refine ⟨x, n', hxlen, hnlen, ?_, ?_, ?_, ?_, hStrongFinal⟩
  · exact hnlenUpper.trans
      (Nat.add_le_add_left (logSlack_mono_left hcRun n) n)
  · exact hPlainUpper.trans (by
      exact_mod_cast Nat.add_le_add_left hsqrt k)
  · exact hPlainLower.trans (by
      gcongr)
  · exact hPlain.mono hsqrt

/-- The normal-string consequence stated immediately after
`stat-any-curve-1`: the realizing witness has its ordinary and logarithmically
strong profiles within twice the realization radius of each other. -/
theorem exists_normal_string_with_curve
    (V U T : Map)
    (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U)
    (hT : IsOptimalTotalConditional T) :
    ∃ c : ℕ, ∀ (n k : ℕ) (t : ℕ → ℕ),
      k ≤ n →
      t 0 ≤ n →
      t k = 0 →
      (∀ i : ℕ, i < k → t (i + 1) < t i) →
      ∃ x : BitString, ∃ n' : ℕ,
        x.length = n' ∧
        n ≤ n' ∧
        n' ≤ n + logSlack c n ∧
        plainK V x ≤ (k + sqrtSlack c n : ENat) ∧
        (k : ENat) ≤ plainK V x + (sqrtSlack c n : ENat) ∧
        ProfileSetsWithinNeighborhood
          (plainDescriptionProfileSet V x)
          {q | FamilyCurveTarget k t q.1 q.2}
          (sqrtSlack c n) ∧
        IsNormalString V T x (logSlack c n)
          (2 * sqrtSlack c n) := by
  obtain ⟨c, hc⟩ := stat_any_curve_1 V U T hV hU hT
  refine ⟨c, ?_⟩
  intro n k t hkn ht0 htk hstrict
  obtain ⟨x, n', hxlen, hnlen, hnlenUpper,
      hPlainUpper, hPlainLower, hPlain, hStrong⟩ :=
    hc n k t hkn ht0 htk hstrict
  refine ⟨x, n', hxlen, hnlen, hnlenUpper,
    hPlainUpper, hPlainLower, hPlain, ?_⟩
  have hnormal :
      IsNormalString V T x (logSlack c n)
        (sqrtSlack c n + sqrtSlack c n) :=
    hPlain.trans hStrong.symm
  simpa [two_mul] using hnormal

end Kolmogorov
