import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.AddNoiseStochasticity
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.ProjectionConservation
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.RemAddNoiseHalfPlane
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.BudgetedStochasticity
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.Properties
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.PlainPairSymmetry
import KolmogorovMathlib.Prefix.TwoStage

/-!
# The stochasticity-profile add-noise theorem
-/

namespace Kolmogorov

open Nat

theorem propAddNoise_slack_absorption (cRem cBeta cC cS cLen cP : Nat) :
    ∃ C : Nat, ∀ (x y e : Nat),
      let baseBudget := x + logSlack (cLen + cBeta) x
      let R := cRem * e + logSlack cRem (x + y)
      let beta2_bound :=
        baseBudget + e + logSlack cP (x + y) + logSlack cC baseBudget + 2 * R
      let kxy_bound := 2 * x + y + 1 + cLen
      let N_bound := kxy_bound + beta2_bound
      e + logSlack cBeta x + logSlack cC baseBudget + 2 * R +
        logSlack cP (x + y) + logSlack cS N_bound
      ≤ C * e + logSlack C x + logSlack C y := by
  let a := cLen + cBeta
  obtain ⟨cBase, hBase⟩ := logSlack_linear_bound cC (a + 1) a
  let A := 3 + a + cP + cC * a + cC + 2 * cRem
  let B := 1 + cLen + a + cP + cC * a + cC + 2 * cRem
  obtain ⟨cN, hN⟩ := logSlack_linear_bound cS A B
  let cx := cBeta + cBase + cP + cN + 2 * cRem
  let cy := cP + cN + 2 * cRem
  let C := cx + cy + cN + 2 * cRem + 1
  refine ⟨C, fun x y e => ?_⟩
  dsimp only
  set baseBudget := x + logSlack (cLen + cBeta) x with hbase
  set R := cRem * e + logSlack cRem (x + y) with hR
  set beta2Bound :=
    baseBudget + e + logSlack cP (x + y) + logSlack cC baseBudget + 2 * R
    with hbeta
  set nBound := 2 * x + y + 1 + cLen + beta2Bound with hn
  have hbaseLinear : baseBudget ≤ (a + 1) * x + a := by
    rw [hbase]
    dsimp [a]
    unfold logSlack
    nlinarith [length_natBits_le_self x]
  have hbaseSlack : logSlack cC baseBudget ≤ logSlack cBase x := by
    exact (logSlack_mono_right cC hbaseLinear).trans (hBase x)
  have hnLinear : nBound ≤ A * (x + y + e) + B := by
    rw [hn, hbeta, hR]
    let D := (a + 1) * x + a
    have hPLog : logSlack cP (x + y) ≤ cP * (x + y) + cP := by
      unfold logSlack
      exact Nat.add_le_add_right
        (Nat.mul_le_mul_left cP (length_natBits_le_self (x + y))) cP
    have hCLog : logSlack cC baseBudget ≤ cC * baseBudget + cC := by
      unfold logSlack
      exact Nat.add_le_add_right
        (Nat.mul_le_mul_left cC (length_natBits_le_self baseBudget)) cC
    have hRemLog : logSlack cRem (x + y) ≤ cRem * (x + y) + cRem := by
      unfold logSlack
      exact Nat.add_le_add_right
        (Nat.mul_le_mul_left cRem (length_natBits_le_self (x + y))) cRem
    have hbaseD : baseBudget ≤ D := hbaseLinear
    have hCbaseD : cC * baseBudget ≤ cC * D :=
      Nat.mul_le_mul_left cC hbaseD
    have hCLogD : logSlack cC baseBudget ≤ cC * D + cC :=
      hCLog.trans (Nat.add_le_add_right hCbaseD cC)
    calc
      2 * x + y + 1 + cLen +
            (baseBudget + e + logSlack cP (x + y) + logSlack cC baseBudget +
              2 * (cRem * e + logSlack cRem (x + y)))
          ≤ 2 * x + y + 1 + cLen +
            (D + e + (cP * (x + y) + cP) + (cC * D + cC) +
              2 * (cRem * e + (cRem * (x + y) + cRem))) := by
                gcongr
      _ = (2 + (a + 1) + cP + cC * (a + 1) + 2 * cRem) * x +
            (1 + cP + 2 * cRem) * y + (1 + 2 * cRem) * e + B := by
            dsimp [D, B]
            ring
      _ ≤ A * x + A * y + A * e + B := by
            have hxCoeff : (2 + (a + 1) + cP + cC * (a + 1) + 2 * cRem) * x ≤ A * x := by
              have : 2 + (a + 1) + cP + cC * (a + 1) + 2 * cRem = A := by dsimp [A]; ring
              rw [this]
            have hyCoeff : (1 + cP + 2 * cRem) * y ≤ A * y := by
              have : 1 + cP + 2 * cRem ≤ A := by dsimp [A]; omega
              exact Nat.mul_le_mul_right y this
            have heCoeff : (1 + 2 * cRem) * e ≤ A * e := by
              have : 1 + 2 * cRem ≤ A := by dsimp [A]; omega
              exact Nat.mul_le_mul_right e this
            omega
      _ = A * (x + y + e) + B := by ring
  have hnSlack : logSlack cS nBound ≤ logSlack cN (x + y + e) := by
    exact (logSlack_mono_right cS hnLinear).trans (hN (x + y + e))
  have hPsplit : logSlack cP (x + y) ≤ logSlack cP x + logSlack cP y :=
    logSlack_add_le cP x y
  have hRsplit : logSlack cRem (x + y) ≤ logSlack cRem x + logSlack cRem y :=
    logSlack_add_le cRem x y
  have hNsplit :
      logSlack cN (x + y + e) ≤
        logSlack cN x + logSlack cN y + logSlack cN e := by
    calc
      logSlack cN (x + y + e)
          ≤ logSlack cN (x + y) + logSlack cN e := by
            simpa [Nat.add_assoc] using logSlack_add_le cN (x + y) e
      _ ≤ (logSlack cN x + logSlack cN y) + logSlack cN e := by
            gcongr
            exact logSlack_add_le cN x y
  have hlogs :
      e + logSlack cBeta x + logSlack cC baseBudget + 2 * (cRem * e + logSlack cRem (x + y)) +
          logSlack cP (x + y) + logSlack cS nBound ≤
        e + (logSlack cBeta x + logSlack cBase x + logSlack cP x + logSlack cN x +
          2 * logSlack cRem x) + (logSlack cP y + logSlack cN y + 2 * logSlack cRem y) +
          logSlack cN e + 2 * (cRem * e) := by
    omega
  refine hlogs.trans ?_
  unfold logSlack
  dsimp [C, cx, cy]
  nlinarith [length_natBits_le_self e]

theorem propAddNoise_of_remAddNoise
    (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U) :
    RemAddNoiseStatement V → PropAddNoiseStatement V U := by
  intro hRem
  obtain ⟨cRem, hcRem⟩ := hRem
  obtain ⟨cProj, hcProj⟩ := isStochastic_fst_of_pair U hU
  obtain ⟨cBeta, hcBeta⟩ := isStochastic_beta_le_length U hU
  obtain ⟨cC, hcC⟩ := budgeted_stochasticity_to_plain_corner_of_length_le V U hV hU
  obtain ⟨cS, hcS⟩ := isStochastic_of_plainProfile_twoPartSum V U hV hU
  obtain ⟨cLen, hcLen⟩ := plainKLeLength V hV
  obtain ⟨cP, hcP⟩ := plainK_pair_ge_plainK_add_length_of_random V U hV hU
  obtain ⟨C_abs, hcAbs⟩ := propAddNoise_slack_absorption cRem cBeta cC cS cLen cP
  let C := max cProj C_abs
  refine ⟨C, ?_⟩
  intro x y epsilon h_eps
  let radius := C * epsilon + logSlack C x.length + logSlack C y.length
  apply stochasticityProfileSet_neighborhood_of_uniform_shifts U x (pairCode x y) radius
  · intro alpha beta h_stoch
    let beta1 := min beta (x.length + logSlack cBeta x.length)
    have h_stoch1 := hcBeta x alpha beta h_stoch
    let baseBudget := x.length + logSlack (cLen + cBeta) x.length
    have hkx : ∃ kx : Nat, plainK V x = (kx : ENat) := by
      have h := hcLen x
      cases hz : plainK V x with
      | top => rw [hz] at h; exact False.elim (ENat.natCast_ne_top _ (top_le_iff.mp h))
      | coe k => exact ⟨k, rfl⟩
    obtain ⟨kx, hkx_eq⟩ := hkx
    have hkx_le : kx ≤ baseBudget := by
      have h := hcLen x
      rw [hkx_eq] at h
      have h_prog_x : programLength x = x.length := rfl
      rw [h_prog_x] at h
      have h' : kx ≤ x.length + cLen := by exact_mod_cast h
      have h_c : cLen ≤ logSlack (cLen + cBeta) x.length := by
        simp [logSlack]
        omega
      omega
    have h_beta1_le : beta1 ≤ baseBudget := by
      have h_c : logSlack cBeta x.length ≤ logSlack (cLen + cBeta) x.length :=
        logSlack_mono_left (by omega) x.length
      omega
    have h_xlen_le : x.length ≤ baseBudget := by omega
    obtain ⟨i, j, hprof, hi, hij⟩ := hcC x kx baseBudget (alpha + logSlack cBeta x.length) beta1
      hkx_eq hkx_le h_xlen_le h_beta1_le h_stoch1
    have hkxy : ∃ kxy : Nat, plainK V (pairCode x y) = (kxy : ENat) := by
      have h := hcLen (pairCode x y)
      cases hz : plainK V (pairCode x y) with
      | top => rw [hz] at h; exact False.elim (ENat.natCast_ne_top _ (top_le_iff.mp h))
      | coe k => exact ⟨k, rfl⟩
    obtain ⟨kxy, hkxy_eq⟩ := hkxy
    have hRem_app := hcRem x y epsilon kx kxy hkx_eq hkxy_eq h_eps
    let B := AddNoiseProfileTransform (plainDescriptionProfileSet V x) kx kxy y.length
    let q := if i ≤ kx then (i, j + y.length) else (i, kxy - i)
    have hq_in_B : q ∈ B := by
      dsimp [q, B, AddNoiseProfileTransform]
      split_ifs with h_case
      · exact Or.inl ⟨i, j, h_case, hprof, rfl⟩
      · push Not at h_case
        exact Or.inr ⟨h_case, by omega⟩
    obtain ⟨q', hq', hdist⟩ := hRem_app.2 q hq_in_B
    set R := cRem * epsilon + logSlack cRem (x.length + y.length) with hR
    set beta2 := beta1 + epsilon + logSlack cP (x.length + y.length) +
      logSlack cC baseBudget + 2 * R with hbeta2
    set N := kxy + beta2 with hN
    have hi2_N : q'.1 ≤ N := by
      have : q'.1 ≤ q.1 + R := by unfold natPairLInfDistance at hdist; omega
      have : q'.1 ≤ (if i ≤ kx then (i, j + y.length) else (i, kxy - i)).1 + R := this
      split_ifs at this with h_case
      · have : kx + y.length ≤ kxy + epsilon + logSlack cP (x.length + y.length) :=
          hcP x y epsilon kx kxy hkx_eq hkxy_eq h_eps
        omega
      · have : kx + y.length ≤ kxy + epsilon + logSlack cP (x.length + y.length) :=
          hcP x y epsilon kx kxy hkx_eq hkxy_eq h_eps
        omega
    have hj2_N : q'.2 ≤ N := by
      have : q'.2 ≤ q.2 + R := by unfold natPairLInfDistance at hdist; omega
      have : q'.2 ≤ (if i ≤ kx then (i, j + y.length) else (i, kxy - i)).2 + R := this
      split_ifs at this with h_case
      · have : kx + y.length ≤ kxy + epsilon + logSlack cP (x.length + y.length) :=
          hcP x y epsilon kx kxy hkx_eq hkxy_eq h_eps
        omega
      · have : kxy - i ≤ kxy := by omega
        omega
    have hbeta2_N : beta2 ≤ N := by omega
    have hkxy_N : kxy ≤ N := by omega
    have hq_sum : q'.1 + q'.2 ≤ kxy + beta2 := by
      have h1 : q'.1 ≤ q.1 + R := by unfold natPairLInfDistance at hdist; omega
      have h2 : q'.2 ≤ q.2 + R := by unfold natPairLInfDistance at hdist; omega
      have h3 : q'.1 + q'.2 ≤ q.1 + q.2 + 2 * R := by omega
      have h4 : q'.1 + q'.2 ≤ (if i ≤ kx then (i, j + y.length) else (i, kxy - i)).1 +
        (if i ≤ kx then (i, j + y.length) else (i, kxy - i)).2 + 2 * R := h3
      split_ifs at h4 with h_case
      · have : kx + y.length ≤ kxy + epsilon + logSlack cP (x.length + y.length) :=
          hcP x y epsilon kx kxy hkx_eq hkxy_eq h_eps
        omega
      · have : i + (kxy - i) = max i kxy := by omega
        have : kx + y.length ≤ kxy + epsilon + logSlack cP (x.length + y.length) :=
          hcP x y epsilon kx kxy hkx_eq hkxy_eq h_eps
        omega
    have h_stoch2 := hcS (pairCode x y) N kxy q'.1 q'.2 beta2 hi2_N hj2_N hbeta2_N
      hkxy_N hkxy_eq hq' hq_sum
    have h_abs := hcAbs x.length y.length epsilon
    have hkxy_bound : kxy ≤ 2 * x.length + y.length + 1 + cLen := by
      have h := hcLen (pairCode x y)
      rw [hkxy_eq] at h
      have h_prog : programLength (pairCode x y) = (pairCode x y).length := rfl
      rw [h_prog] at h
      have h_len : (pairCode x y).length = 2 * x.length + y.length + 1 := by
        rw [length_pairCode]
        omega
      rw [h_len] at h
      exact_mod_cast h
    let beta2Bound := baseBudget + epsilon + logSlack cP (x.length + y.length) +
      logSlack cC baseBudget + 2 * R
    have h_beta2_le : beta2 ≤ beta2Bound := by
      dsimp [beta2, beta2Bound]
      omega
    have h_N_le : N ≤ 2 * x.length + y.length + 1 + cLen + beta2Bound := by omega
    have h_logS : logSlack cS N ≤
        logSlack cS (2 * x.length + y.length + 1 + cLen + beta2Bound) :=
      logSlack_mono_right cS h_N_le
    apply isStochastic_mono _ _ h_stoch2
    · have h1 : q'.1 ≤ i + R := by
        have h_q_le : q'.1 ≤ q.1 + R := by unfold natPairLInfDistance at hdist; omega
        have hq1 : q.1 = i := by dsimp [q]; split_ifs <;> rfl
        rw [hq1] at h_q_le
        exact h_q_le
      have h3 : i ≤ alpha + logSlack cBeta x.length + logSlack cC baseBudget := hi
      have h4 : logSlack C_abs x.length ≤ logSlack C x.length :=
        logSlack_mono_left (le_max_right _ _) _
      have h5 : logSlack C_abs y.length ≤ logSlack C y.length :=
        logSlack_mono_left (le_max_right _ _) _
      have h6 : C_abs * epsilon ≤ C * epsilon := Nat.mul_le_mul_right _ (le_max_right _ _)
      dsimp [radius, N, beta2, beta2Bound, R, baseBudget] at *
      omega
    · have h4 : logSlack C_abs x.length ≤ logSlack C x.length :=
        logSlack_mono_left (le_max_right _ _) _
      have h5 : logSlack C_abs y.length ≤ logSlack C y.length :=
        logSlack_mono_left (le_max_right _ _) _
      have h6 : C_abs * epsilon ≤ C * epsilon := Nat.mul_le_mul_right _ (le_max_right _ _)
      have h_beta1 : beta1 ≤ beta := min_le_left _ _
      dsimp [radius, N, beta2, beta2Bound, R, baseBudget] at *
      omega
  · intro alpha beta h_stoch
    have h_proj := hcProj x y alpha beta h_stoch
    have h_le : cProj ≤ radius := by
      dsimp [radius]
      have : cProj ≤ C := le_max_left _ _
      exact this.trans (const_le_addNoiseRadius C epsilon x.length y.length)
    exact isStochastic_mono (by omega) (by omega) h_proj

theorem prop_add_noise
    (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U) :
    PropAddNoiseStatement V U :=
  propAddNoise_of_remAddNoise V U hV hU (rem_add_noise V U hV hU)

end Kolmogorov
