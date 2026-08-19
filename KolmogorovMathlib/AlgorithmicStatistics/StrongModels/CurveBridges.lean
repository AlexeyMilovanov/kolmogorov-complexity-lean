import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.PlainProfile
import KolmogorovMathlib.Restricted.FamilyCurve.Basic

/-!
# Bridges from restricted curve profiles

This module relates the restricted profile approximation used by the family
curve theorem to the common symmetric neighborhood formulation.
-/

namespace Kolmogorov

/-- The restricted description profile as a subset of the parameter plane. -/
def restrictedDescriptionProfileSet
    (𝒜 : DescriptionFamily) (U : Map) (x : BitString) :
    Set (Nat × Nat) :=
  {q | InDescriptionProfileIn 𝒜 U x q.1 q.2}

/-- A restricted curve approximation gives a symmetric neighborhood
approximation of its target up-set. -/
theorem restrictedProfileWithinCurve_neighborhood
    (𝒜 : DescriptionFamily) (U : Map) (x : BitString)
    (k : Nat) (t : Nat → Nat) (Δ : Nat)
    (htk : t k = 0)
    (hcurve : RestrictedProfileWithinCurve 𝒜 U x k t Δ) :
    ProfileSetsWithinNeighborhood
      (restrictedDescriptionProfileSet 𝒜 U x)
      {q | FamilyCurveTarget k t q.1 q.2}
      Δ := by
  unfold RestrictedProfileWithinCurve at hcurve
  simp only [ProfileSetsWithinNeighborhood, restrictedDescriptionProfileSet, natPairLInfDistance]
  constructor
  · intro q hq
    simp only [Set.mem_setOf_eq] at hq
    -- Case split: use (q.1 + Δ, q.2) as target if q.1 + Δ > k, otherwise (q.1, t q.1)
    by_cases hikΔ : q.1 + Δ > k
    · -- q.1 + Δ > k: target (q.1 + Δ, q.2) is in target vacuously
      refine ⟨(q.1 + Δ, q.2), ?_, ?_⟩
      · simp only [Set.mem_setOf_eq, FamilyCurveTarget]
        intro h
        omega
      · simp
    · -- q.1 + Δ ≤ k: split on q.2 ≤ t q.1 + Δ
      by_cases hj : q.2 ≤ t q.1 + Δ
      · -- q.2 ≤ t q.1 + Δ: use target (q.1, t q.1)
        -- Need: |q.2 - t q.1| ≤ Δ
        -- Upper: q.2 ≤ t q.1 + Δ gives q.2 - t q.1 ≤ Δ
        -- Lower: from hcurve.2, either ¬ profile at (q.1, t q.1 - Δ - 1) or t q.1 ≤ Δ
        have hdist : q.2 ≤ t q.1 + Δ ∧ t q.1 ≤ q.2 + Δ := by
          constructor
          · exact hj
          · have hcurve2 := hcurve.2 q.1 (by omega : q.1 ≤ k)
            rcases hcurve2 with hnor | ht
            · -- ¬ InDescriptionProfileIn 𝒜 U x q.1 (t q.1 - (Δ + 1))
              rcases hq with ⟨S, hS, hmem, hdesc⟩
              have : ¬ (q.2 ≤ t q.1 - (Δ + 1)) := fun h => hnor ⟨S, hS, hmem, hdesc.mono_j h⟩
              omega
            · -- t q.1 ≤ Δ
              omega
        refine ⟨(q.1, t q.1), ?_, ?_⟩
        · simp only [Set.mem_setOf_eq, FamilyCurveTarget]
          exact fun _ => le_rfl
        · apply max_le <;> omega
      · -- q.2 > t q.1 + Δ: use target (q.1, q.2 + Δ)
        refine ⟨(q.1, q.2 + Δ), ?_, ?_⟩
        · simp only [Set.mem_setOf_eq, FamilyCurveTarget]
          intro _; omega
        · simp
  · intro q hq
    simp only [Set.mem_setOf_eq] at hq
    -- Case split on whether q.1 ≤ k
    by_cases hik : q.1 ≤ k
    · -- Case q.1 ≤ k: use (q.1 + Δ, q.2 + Δ) in profile
      -- (q.1 + Δ, t q.1 + Δ) is in profile by hcurve
      have hcurvept : InDescriptionProfileIn 𝒜 U x (q.1 + Δ) (t q.1 + Δ) := hcurve.1 q.1 hik
      -- Since q.2 ≥ t q.1 (from hq and hik), we have q.2 + Δ ≥ t q.1 + Δ
      have hj : t q.1 ≤ q.2 := hq hik
      -- Use monotonicity to get (q.1 + Δ, q.2 + Δ) in profile
      have hprofile : InDescriptionProfileIn 𝒜 U x (q.1 + Δ) (q.2 + Δ) :=
        hcurvept.mono_j (by omega)
      refine ⟨(q.1 + Δ, q.2 + Δ), hprofile, ?_⟩
      simp
    · -- Case q.1 > k: use up-set property from (k + Δ, Δ)
      -- Profile point (k + Δ, Δ) is in the profile since t k = 0
      have hkprofile : InDescriptionProfileIn 𝒜 U x (k + Δ) Δ := by
        simpa only [htk, zero_add] using hcurve.1 k (le_refl k)
      by_cases hikΔ : q.1 ≥ k + Δ
      · -- q.1 ≥ k + Δ: use (q.1, q.2 + Δ) in profile by up-set
        have hprofile : InDescriptionProfileIn 𝒜 U x q.1 (q.2 + Δ) :=
          hkprofile.mono_i hikΔ |>.mono_j (by omega)
        refine ⟨(q.1, q.2 + Δ), hprofile, ?_⟩
        simp
      · -- q.1 < k + Δ (but q.1 > k): use (k + Δ, max q.2 Δ) in profile
        have hjge : Δ ≤ max q.2 Δ := le_max_right _ _
        have hprofile : InDescriptionProfileIn 𝒜 U x (k + Δ) (max q.2 Δ) :=
          hkprofile.mono_j hjge
        refine ⟨(k + Δ, max q.2 Δ), hprofile, ?_⟩
        -- Distance: max(|q.1 - (k+Δ)|, |q.2 - max q.2 Δ|)
        apply max_le
        · -- First coordinate: q.1 - (k + Δ) + (k + Δ - q.1) = k + Δ - q.1 < Δ
          omega
        · -- Second coordinate: q.2 - max q.2 Δ + (max q.2 Δ - q.2) ≤ Δ
          omega

end Kolmogorov
