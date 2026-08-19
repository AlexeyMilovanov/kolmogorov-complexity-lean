import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.BoundaryRealization
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.NoiseAssembly

/-!
# The logarithmic half of VS40 Theorem `card`

Realizing the auxiliary boundary with logarithmic precision and appending a
conditionally random tail produces `2 ^ (k_P - m_P)`-many strings whose plain
description profiles are all `O(KP + log n_P)`-close to the target profile.
-/

namespace Kolmogorov

open Kolmogorov.CodedFiniteDistribution

/-- Scaling a log-slack multiplies its constant. -/
theorem logSlack_mul (m c n : ℕ) : m * logSlack c n = logSlack (m * c) n := by
  unfold logSlack; ring

section RadiusArith

variable {KP np : ℕ}

theorem profileRadius_add {X Y a b a' b' : ℕ}
    (hX : X ≤ a * KP + logSlack b np) (hY : Y ≤ a' * KP + logSlack b' np) :
    X + Y ≤ (a + a') * KP + logSlack (b + b') np := by
  have h1 : (a + a') * KP = a * KP + a' * KP := by ring
  have h2 : logSlack (b + b') np = logSlack b np + logSlack b' np :=
    (logSlack_add_const b b' np).symm
  omega

theorem profileRadius_smul {X a b : ℕ} (m : ℕ)
    (h : X ≤ a * KP + logSlack b np) :
    m * X ≤ m * a * KP + logSlack (m * b) np := by
  have h1 : m * X ≤ m * (a * KP + logSlack b np) := Nat.mul_le_mul_left _ h
  have h2 : m * (a * KP + logSlack b np) = m * a * KP + m * logSlack b np := by ring
  have h3 : m * logSlack b np = logSlack (m * b) np := logSlack_mul m b np
  omega

end RadiusArith

/-- The image of a set of tails under pairing with a fixed head has the same
log-cardinality. -/
theorem finiteSetLogCard_image_pairCode (y : BitString) (R : Finset BitString) :
    finiteSetLogCard (R.image (fun z => pairCode y z)) = finiteSetLogCard R := by
  classical
  unfold finiteSetLogCard
  congr 1
  refine Finset.card_image_of_injective R ?_
  intro z1 z2 h
  have := congrArg decodeSecond h
  simpa [decodeSecond_pairCode] using this

/-- **Logarithmic half of Theorem `card`.**  For every admissible profile with a
boundary `b` there are `2 ^ (k_P - m_P)`-many strings whose plain description
profiles are `O(b.KP + log n_P)`-close to the profile. -/
theorem thm_card_log_branch
    (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (P : Set (Nat × Nat)) (kp mp np : ℕ) (b : ProfileBoundary V),
      IsAdmissibleProfileSet P →
      profileSet V b = P →
      k_P P = (kp : ENat) →
      m_P P kp = (mp : ENat) →
      n_P P = (np : ENat) →
      ∃ S : Finset BitString,
        S.Nonempty ∧
        (S : Set BitString) ⊆ profileNeighborhood V P (c * b.KP + logSlack c np) ∧
        ((kp - mp : ℕ) : ENat) ≤ (finiteSetLogCard S : ENat) + (c : ENat) := by
  classical
  obtain ⟨C1, hAux⟩ := auxiliaryProfile_boundary V U hV hU
  obtain ⟨C2, hReal⟩ := exists_string_realizing_profileBoundary V U hV hU
  obtain ⟨C3, hClose⟩ := plainK_close_of_profileBoundary_neighborhood V hV
  obtain ⟨C4, hAssm⟩ := exists_noise_finset_near_profile V U hV hU
  -- Constant bookkeeping.
  set aE := C2 * C1 with haE
  set bE := C2 * C1 + C2 with hbE
  set aEta := (C3 + 2) * aE with haEta
  set bEta := (C3 + 2) * bE + C3 + 2 * C3 with hbEta
  refine ⟨C4 * (aE + aEta) + C4 * (bE + bEta) + C4, ?_⟩
  intro P kp mp np b hadm hbP hkP hmP hnP
  set cFinal := C4 * (aE + aEta) + C4 * (bE + bEta) + C4 with hcFinal
  -- Endpoint facts.
  have hmpkp : mp ≤ kp := by
    have h := m_P_le_k_P_of_eq P kp hkP
    rw [hmP, hkP] at h
    exact_mod_cast h
  have hkpnp : kp ≤ np := by
    have h := k_P_le_n_P_of_admissible hadm
    rw [hkP, hnP] at h
    exact_mod_cast h
  set d := kp - mp with hd
  have hdnp : d ≤ np := by omega
  -- The auxiliary boundary and its realization.
  obtain ⟨bt, hbtk, hbtn, hbtP, hbtKP⟩ := hAux P kp mp np b hadm hbP hkP hmP hnP
  have hbtn_le : bt.n_P ≤ np := by rw [hbtn]; omega
  obtain ⟨y, hylen, hynb⟩ := hReal bt
  have hyFinite : plainK V y ≠ ⊤ := condK_ne_top_of_optimal V hV y []
  set ky := (plainK V y).toNat with hky
  have hkyval : plainK V y = (ky : ENat) := (ENat.coe_toNat hyFinite).symm
  set e := C2 * bt.KP + logSlack C2 bt.n_P with he
  set eta := C3 * (e + 1) + logSlack C3 bt.n_P + 2 * e + C3 with heta
  obtain ⟨hkyUp, hkyLow⟩ := hClose bt y e ky hynb hkyval
  rw [hbtk] at hkyUp hkyLow
  have hkyup : ky ≤ mp + eta := by omega
  have hkylow : mp ≤ ky + eta := by omega
  have hnbaux : ProfileSetsWithinNeighborhood (plainDescriptionProfileSet V y)
      (auxiliaryProfile P mp kp) e := by rw [← hbtP]; exact hynb
  obtain ⟨R, hRne, hRmem, hRcard⟩ :=
    hAssm P kp mp y e eta ky hadm hkP hmP hkyval hkyup hkylow hnbaux
  -- Radius arithmetic.
  have hEbound : e ≤ aE * b.KP + logSlack bE np := by
    have h1 : C2 * bt.KP ≤ aE * b.KP + logSlack (C2 * C1) np := by
      have := profileRadius_smul (KP := b.KP) (np := np) C2 hbtKP
      rw [haE]; exact this
    have h2 : logSlack C2 bt.n_P ≤ logSlack C2 np := logSlack_mono_right C2 hbtn_le
    have h3 : logSlack (C2 * C1) np + logSlack C2 np = logSlack bE np := by
      rw [hbE]; exact logSlack_add_const _ _ _
    rw [he]; omega
  have hEtaBound : eta ≤ aEta * b.KP + logSlack bEta np := by
    have h1 : (C3 + 2) * e ≤ aEta * b.KP + logSlack ((C3 + 2) * bE) np := by
      have := profileRadius_smul (KP := b.KP) (np := np) (C3 + 2) hEbound
      rw [haEta]; exact this
    have h2 : logSlack C3 bt.n_P ≤ logSlack C3 np := logSlack_mono_right C3 hbtn_le
    have h3 : logSlack ((C3 + 2) * bE) np + logSlack C3 np + logSlack (2 * C3) np =
        logSlack bEta np := by
      rw [hbEta, logSlack_add_const, logSlack_add_const]
    have h4 : 2 * C3 ≤ logSlack (2 * C3) np := by
      unfold logSlack
      have : 0 ≤ 2 * C3 * (Nat.bits np).length := Nat.zero_le _
      omega
    have h5 : eta = (C3 + 2) * e + logSlack C3 bt.n_P + 2 * C3 := by
      rw [heta]; ring
    omega
  have hSum : e + eta ≤ (aE + aEta) * b.KP + logSlack (bE + bEta) np :=
    profileRadius_add hEbound hEtaBound
  have hFinalRadius : C4 * (e + eta) + logSlack C4 np ≤
      cFinal * b.KP + logSlack cFinal np := by
    have h1 : C4 * (e + eta) ≤ C4 * (aE + aEta) * b.KP +
        logSlack (C4 * (bE + bEta)) np := profileRadius_smul C4 hSum
    have h2 : logSlack (C4 * (bE + bEta)) np + logSlack C4 np =
        logSlack (C4 * (bE + bEta) + C4) np := logSlack_add_const _ _ _
    have h3 : C4 * (aE + aEta) * b.KP ≤ cFinal * b.KP := by
      apply Nat.mul_le_mul_right
      rw [hcFinal]; omega
    have h4 : logSlack (C4 * (bE + bEta) + C4) np ≤ logSlack cFinal np :=
      logSlack_mono_left (by rw [hcFinal]; omega) _
    omega
  have hlenSum : y.length + (kp - mp) = np := by
    rw [hylen, hbtn]; omega
  refine ⟨R.image (fun z => pairCode y z), ?_, ?_, ?_⟩
  · exact hRne.image _
  · intro x hx
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    obtain ⟨-, -, hnb⟩ := hRmem z hz
    rw [hlenSum] at hnb
    exact hnb.mono hFinalRadius
  · rw [finiteSetLogCard_image_pairCode]
    refine hRcard.trans ?_
    gcongr
    exact_mod_cast (show C4 ≤ cFinal by rw [hcFinal]; omega)

end Kolmogorov
