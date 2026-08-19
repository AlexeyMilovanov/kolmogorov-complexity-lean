import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.AuxiliaryProfile
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.RemAddNoiseHalfPlane

/-!
# Attaching a random tail to a realization of the auxiliary profile

Let `P` be an admissible profile with endpoints `k_P = kp`, `m_P = mp` and let
`y` be a string whose plain description profile is `e`-close to the auxiliary
profile `P̃ = auxiliaryProfile P mp kp` and whose plain complexity is `eta`-close
to `mp`.  Appending a conditionally random tail `z` of length `d = kp - mp`
produces `2 ^ d`-many strings whose plain description profiles are all
`O(e + eta + log (|y| + d))`-close to `P` itself.

This is the common core of both halves of VS40 Theorem `card`; the two halves
differ only in how the head string `y` is produced.
-/

namespace Kolmogorov

open Kolmogorov.CodedFiniteDistribution

/-- Admissibility forces every profile point to lie above the sufficiency line
`i + j ≥ k_P`. -/
theorem admissibleProfile_k_P_le_add
    {P : Set (Nat × Nat)} {kp : ℕ}
    (hadm : IsAdmissibleProfileSet P) (hkP : k_P P = (kp : ENat)) :
    ∀ q ∈ P, kp ≤ q.1 + q.2 := by
  rintro ⟨a, b⟩ hab
  have hstep := hadm.step
  have hstep' : (a + b, 0) ∈ P := by simpa using hstep a b 0 (by simpa using hab)
  have hle : k_P P ≤ ((a + b : ℕ) : ENat) := sInf_le ⟨a + b, rfl, hstep'⟩
  rw [hkP] at hle
  exact_mod_cast hle

/-- The auxiliary profile lies above the sufficiency line of `P` shifted down by
the noise length `kp - mp`. -/
theorem auxiliaryProfile_k_P_le_add
    {P : Set (Nat × Nat)} {kp mp : ℕ}
    (hmp : mp ≤ kp)
    (hsuff : ∀ q ∈ P, kp ≤ q.1 + q.2) :
    ∀ q ∈ auxiliaryProfile P mp kp, kp ≤ q.1 + q.2 + (kp - mp) := by
  rintro ⟨a, b⟩ hq
  rcases hq with ⟨hle, hmem⟩ | hge
  · have := hsuff (a, b + (kp - mp)) hmem
    simp only at this ⊢
    omega
  · simp only at hge ⊢
    omega

/-- **Random-tail assembly.**  A head string `y` approximating the auxiliary
profile yields a large family of conditionally random tails whose pairs with `y`
all approximate `P`. -/
theorem exists_noise_finset_near_profile
    (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U) :
    ∃ C : ℕ, ∀ (P : Set (Nat × Nat)) (kp mp : ℕ) (y : BitString) (e eta ky : ℕ),
      IsAdmissibleProfileSet P →
      k_P P = (kp : ENat) →
      m_P P kp = (mp : ENat) →
      plainK V y = (ky : ENat) →
      ky ≤ mp + eta →
      mp ≤ ky + eta →
      ProfileSetsWithinNeighborhood (plainDescriptionProfileSet V y)
        (auxiliaryProfile P mp kp) e →
      ∃ R : Finset BitString,
        R.Nonempty ∧
        (∀ z ∈ R,
          z.length = kp - mp ∧
          ((kp - mp : ℕ) : ENat) ≤ condK V z y + (C : ENat) ∧
          ProfileSetsWithinNeighborhood
            (plainDescriptionProfileSet V (pairCode y z)) P
            (C * (e + eta) + logSlack C (y.length + (kp - mp)))) ∧
        ((kp - mp : ℕ) : ENat) ≤ (finiteSetLogCard R : ENat) + (C : ENat) := by
  classical
  obtain ⟨cRem, hRem⟩ := rem_add_noise V U hV hU
  obtain ⟨cCont, hCont⟩ := addNoiseProfileTransform_continuity
  obtain ⟨cPair, hPair⟩ := pair_complexity_close_of_random_tail V U hV hU
  obtain ⟨cTail, hTail⟩ := exists_many_conditionally_random_tails (V := V)
  set A := cCont * cPair with hA
  set A2 := A * cTail with hA2
  set A3 := cRem * cTail with hA3
  refine ⟨4 * cCont + 2 * A + A2 + A3 + 2 * cRem + cTail + 1, ?_⟩
  intro P kp mp y e eta ky hadm hkP hmP hky hkyup hkylow hnbhd
  set d := kp - mp with hd
  set C := 4 * cCont + 2 * A + A2 + A3 + 2 * cRem + cTail + 1 with hC
  have hCtail : cTail ≤ C := by omega
  -- Basic endpoint facts.
  have hmpkp : mp ≤ kp := by
    have h := m_P_le_k_P_of_eq P kp hkP
    rw [hmP, hkP] at h
    exact_mod_cast h
  have hsuffP : ∀ q ∈ P, kp ≤ q.1 + q.2 :=
    admissibleProfile_k_P_le_add hadm hkP
  have hsuffAux : ∀ q ∈ auxiliaryProfile P mp kp, kp ≤ q.1 + q.2 + d :=
    auxiliaryProfile_k_P_le_add hmpkp hsuffP
  have htransform :
      AddNoiseProfileTransform (auxiliaryProfile P mp kp) mp kp d = P :=
    addNoiseProfileTransform_auxiliaryProfile P kp mp hadm hkP hmP
  -- The random tails.
  obtain ⟨R, hRne, hRmem, hRcard⟩ := hTail y d
  refine ⟨R, hRne, ?_, ?_⟩
  · intro z hz
    obtain ⟨hzlen, hzrandom⟩ := hRmem z hz
    have hzrandom' : (z.length : ENat) ≤ condK V z y + (cTail : ENat) := by
      rw [hzlen]; exact hzrandom
    refine ⟨hzlen, ?_, ?_⟩
    · calc ((kp - mp : ℕ) : ENat) = (d : ENat) := by rw [hd]
        _ ≤ condK V z y + (cTail : ENat) := hzrandom
        _ ≤ condK V z y + (C : ENat) := by
            gcongr
    -- Complexity of the pair.
    have hpairFinite : plainK V (pairCode y z) ≠ ⊤ :=
      condK_ne_top_of_optimal V hV _ []
    set kyz := (plainK V (pairCode y z)).toNat with hkyz
    have hkyzval : plainK V (pairCode y z) = (kyz : ENat) :=
      (ENat.natCast_toNat hpairFinite).symm
    set Epair := cPair * (eta + cTail) + logSlack cPair (y.length + d) with hEpair
    obtain ⟨hpairUp, hpairLow⟩ :=
      hPair y z mp d eta cTail ky kyz hky hkyzval hkyup hkylow hzlen hzrandom
    rw [← hEpair] at hpairUp hpairLow
    -- Step 1: the profile of the pair is close to the transform of the profile of `y`.
    have hstep1' :
        ProfileSetsWithinNeighborhood
          (plainDescriptionProfileSet V (pairCode y z))
          (AddNoiseProfileTransform (plainDescriptionProfileSet V y) ky kyz z.length)
          (cRem * cTail + logSlack cRem (y.length + z.length)) :=
      hRem y z cTail ky kyz hky hkyzval hzrandom'
    rw [hzlen] at hstep1'
    -- Step 2: continuity of the transform.
    set eps := 3 * e + eta + Epair with heps
    have hsuffProfile :
        ∀ q ∈ plainDescriptionProfileSet V y, kyz ≤ q.1 + q.2 + d + eps := by
      intro q hq
      obtain ⟨q', hq', hdist⟩ := hnbhd.1 q hq
      have hsuff' := hsuffAux q' hq'
      unfold natPairLInfDistance at hdist
      have h1 : q'.1 ≤ q.1 + e := by
        have := le_of_max_le_left hdist; omega
      have h2 : q'.2 ≤ q.2 + e := by
        have := le_of_max_le_right hdist; omega
      omega
    have hsuffAux' :
        ∀ q ∈ auxiliaryProfile P mp kp, kp ≤ q.1 + q.2 + d + eps := by
      intro q hq
      have := hsuffAux q hq
      omega
    have hstep2 :
        ProfileSetsWithinNeighborhood
          (AddNoiseProfileTransform (plainDescriptionProfileSet V y) ky kyz d)
          (AddNoiseProfileTransform (auxiliaryProfile P mp kp) mp kp d)
          (cCont * eps) :=
      hCont (plainDescriptionProfileSet V y) (auxiliaryProfile P mp kp)
        ky mp kyz kp d d eps (hnbhd.mono (by omega)) (by omega) (by omega)
        (by omega) (by omega) (Nat.le_add_right _ _) (Nat.le_add_right _ _)
        hsuffProfile hsuffAux'
    have hcomb := hstep1'.trans hstep2
    rw [htransform] at hcomb
    refine hcomb.mono ?_
    -- Radius arithmetic.
    set len := (Nat.bits (y.length + d)).length with hlen
    have hexpand : cRem * cTail + logSlack cRem (y.length + d) + cCont * eps =
        (cCont * 3 * e + cCont * eta + A * eta) +
          (A * len + A + A3 + A2 + cRem * len + cRem) := by
      rw [heps, hEpair, hA, hA2, hA3]
      unfold logSlack
      rw [← hlen]
      ring
    have hcoef : cCont * 3 * e + cCont * eta + A * eta ≤ C * (e + eta) := by
      have hc : cCont * 3 + cCont + A ≤ C := by omega
      have hmul : (cCont * 3 + cCont + A) * (e + eta) ≤ C * (e + eta) :=
        Nat.mul_le_mul_right _ hc
      have hexp : (cCont * 3 + cCont + A) * (e + eta) =
          cCont * 3 * e + cCont * eta + A * eta +
            (cCont * 3 * eta + cCont * e + A * e) := by ring
      omega
    have hrest : A * len + A + A3 + A2 + cRem * len + cRem ≤ C * len + C := by
      have hc1 : A + cRem ≤ C := by omega
      have hmul : (A + cRem) * len ≤ C * len := Nat.mul_le_mul_right _ hc1
      have hexp : (A + cRem) * len = A * len + cRem * len := by ring
      have hc2 : A + A3 + A2 + cRem ≤ C := by omega
      omega
    have hlogC : logSlack C (y.length + d) = C * len + C := by
      unfold logSlack; rw [← hlen]
    rw [hexpand, hlogC]
    exact Nat.add_le_add hcoef hrest
  · calc ((kp - mp : ℕ) : ENat) = (d : ENat) := by rw [hd]
      _ ≤ (finiteSetLogCard R : ENat) + (cTail : ENat) := hRcard
      _ ≤ (finiteSetLogCard R : ENat) + (C : ENat) := by
          gcongr

end Kolmogorov
