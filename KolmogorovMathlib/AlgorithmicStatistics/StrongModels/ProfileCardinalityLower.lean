import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.ThmCardNormal

/-!
# Lower bound for profile cardinality (S9 lower)

This file contains the proof of `thm_card` (VS40 Theorem `card`).  Both halves
are assembled from the auxiliary profile of `StrongModels.AuxiliaryProfile`: the
logarithmic half uses the logarithmic-precision boundary realization
(`thm_card_log_branch`), the normal half uses the square-root precision
realization by a normal string (`thm_card_normal_branch`), and both attach a
conditionally random tail through `exists_noise_finset_near_profile`.
-/

namespace Kolmogorov

open Kolmogorov.CodedFiniteDistribution

/-- The `ENat` difference of two natural endpoints is the cast of their
truncated difference. -/
theorem enat_sub_coe (kp mp : ℕ) :
    (kp : ENat) - (mp : ENat) = ((kp - mp : ℕ) : ENat) := by
  exact (ENat.coe_sub kp mp).symm

theorem thm_card
    (V U T : Map)
    (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U)
    (hT : IsOptimalTotalConditional T) :
    ThmCardStatement V T := by
  obtain ⟨cLog, hLog⟩ := thm_card_log_branch V U hV hU
  obtain ⟨cNorm, hNorm⟩ := thm_card_normal_branch V U T hV hU hT
  refine ⟨cLog + cNorm, ?_⟩
  intro P kp mp np b hadm hbP hkP hmP hnP
  have hcast : (kp : ENat) - (mp : ENat) = ((kp - mp : ℕ) : ENat) := enat_sub_coe kp mp
  have hcLog : cLog ≤ cLog + cNorm := Nat.le_add_right _ _
  have hcNorm : cNorm ≤ cLog + cNorm := Nat.le_add_left _ _
  constructor
  · obtain ⟨S, hSne, hSsub, hScard⟩ := hLog P kp mp np b hadm hbP hkP hmP hnP
    refine ⟨S, hSne, ?_, ?_⟩
    · intro x hx
      have hxmem := hSsub hx
      refine hxmem.mono ?_
      have h1 : cLog * b.KP ≤ (cLog + cNorm) * b.KP :=
        Nat.mul_le_mul_right _ hcLog
      have h2 : logSlack cLog np ≤ logSlack (cLog + cNorm) np :=
        logSlack_mono_left hcLog np
      omega
    · rw [hcast]
      refine hScard.trans ?_
      gcongr
  · obtain ⟨S, hSne, hSsub, hScard⟩ := hNorm P kp mp np b hadm hbP hkP hmP hnP
    refine ⟨S, hSne, ?_, ?_⟩
    · intro x hx
      obtain ⟨hnormal, hprofile⟩ := hSsub hx
      constructor
      · exact (hnormal.mono_delta (sqrtSlack_mono_left hcNorm np)).mono_epsilon
          (logSlack_mono_left hcNorm np)
      · refine hprofile.mono ?_
        have h1 : cNorm * b.KP ≤ (cLog + cNorm) * b.KP :=
          Nat.mul_le_mul_right _ hcNorm
        have h2 : sqrtSlack cNorm np ≤ sqrtSlack (cLog + cNorm) np :=
          sqrtSlack_mono_left hcNorm np
        omega
    · rw [hcast]
      refine hScard.trans ?_
      gcongr

end Kolmogorov
