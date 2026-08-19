import KolmogorovMathlib.CommonInformation.IncidenceRegion
import KolmogorovMathlib.CommonInformation.IncidenceCoverArithmetic
import KolmogorovMathlib.CommonInformation.RegionConsequences
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.SlackArith

/-!
# Consequences of the incidence-region envelope

This module completes SUV Theorem 227.  It converts the Figure-37 region
containment into a weighted profile inequality, transports conditional values
with plain symmetry of information, and performs the small/large-`C(z)` split
needed to keep the final error at `O(log n)` rather than `O(log (n + C(z)))`.
-/

namespace Kolmogorov

/-- If `C(z)` is a sufficiently large linear multiple of the endpoint profile
scale, symmetry of information alone absorbs the marginal complexities and its
logarithmic errors into the two reverse conditional complexities. -/
theorem theorem_227_large_z_case
    (V : Map) (hV : isOptimalConditional V) :
  ∀ A, ∃ C L, ∀ n : Nat, ∀ x y : BitString, ∀ kx ky : Nat, ∀ z : BitString, ∀ kz kzx kzy : Nat,
    HasPlainComplexityValue V x kx → HasPlainComplexityValue V y ky →
    HasPlainComplexityValue V z kz →
    HasPlainConditionalComplexityValue V z x kzx →
    HasPlainConditionalComplexityValue V z y kzy →
    kx ≤ 2 * n + logSlack A n → ky ≤ 2 * n + logSlack A n →
    L * n + logSlack C n ≤ kz →
    kz ≤ 2 * kzx + 2 * kzy + logSlack C n := by
  intro A
  obtain ⟨cBal, hBal⟩ := plainK_conditional_balance_values V hV
  obtain ⟨cCond, hCond⟩ := condKLePlainK V hV
  let a := 2 * A + 6
  let b_const := 2 * A + 2 * cCond + 1
  obtain ⟨cFold, hFold⟩ := logSlack_linear_bound cBal a b_const
  obtain ⟨b1, hb1⟩ := logSlack_le_add_const (400 * cFold)
  let C := 400 * A + b1 + 1
  let L := 400 * A + 1000
  refine ⟨C, L, ?_⟩
  intro n x y kx ky z kz kzx kzy hx hy hz hzx hzy hkx hky hkz
  obtain ⟨kxz, hkxz⟩ := exists_plainConditionalComplexityValue V hV x z
  obtain ⟨kyz, hkyz⟩ := exists_plainConditionalComplexityValue V hV y z
  let ex := logSlack cBal (kx + kz + kzx + kxz + 1)
  let ey := logSlack cBal (ky + kz + kzy + kyz + 1)
  have hBalX : kz + kxz ≤ kx + kzx + ex := hBal x z kx kz kzx kxz hx hz hzx hkxz
  have hBalY : kz + kyz ≤ ky + kzy + ey := hBal y z ky kz kzy kyz hy hz hzy hkyz
  have hkxzUpper : kxz ≤ kx + cCond := by
    have h := hCond x z
    rw [hkxz, hx] at h
    exact_mod_cast h
  have hkyzUpper : kyz ≤ ky + cCond := by
    have h := hCond y z
    rw [hkyz, hy] at h
    exact_mod_cast h
  have hkzxUpper : kzx ≤ kz + cCond := by
    have h := hCond z x
    rw [hzx, hz] at h
    exact_mod_cast h
  have hkzyUpper : kzy ≤ kz + cCond := by
    have h := hCond z y
    rw [hzy, hz] at h
    exact_mod_cast h
  have hBits : (Nat.bits n).length ≤ n := length_natBits_le n
  have hdLinear : logSlack A n ≤ A * n + A := by
    unfold logSlack
    nlinarith [Nat.mul_le_mul_left A hBits]
  let M := n + kz + 1
  have hxArg : kx + kz + kzx + kxz + 1 ≤ a * M + b_const := by
    dsimp [a, b_const, M]
    nlinarith [Nat.zero_le (A * kz)]
  have hyArg : ky + kz + kzy + kyz + 1 ≤ a * M + b_const := by
    dsimp [a, b_const, M]
    nlinarith [Nat.zero_le (A * kz)]
  have hxLog : ex ≤ logSlack cFold M :=
    (logSlack_mono_right cBal hxArg).trans (hFold M)
  have hyLog : ey ≤ logSlack cFold M :=
    (logSlack_mono_right cBal hyArg).trans (hFold M)
  
  have hFoldMul : 400 * logSlack cFold M = logSlack (400 * cFold) M := logSlack_nsmul 400 cFold M
  have hBound : logSlack (400 * cFold) M ≤ M + b1 := hb1 M
  have hExEyBound : 200 * ex + 200 * ey ≤ M + b1 := by omega
  
  have hzxBound : kzx + kx + ex ≥ kz := by omega
  have hzyBound : kzy + ky + ey ≥ kz := by omega
  have hSum : 2 * kzx + 2 * kzy + 2 * kx + 2 * ky + 2 * ex + 2 * ey ≥ 2 * kz := by omega
  
  have hxUpper : kx ≤ 2 * n + A * n + A := hkx.trans (by omega)
  have hyUpper : ky ≤ 2 * n + A * n + A := hky.trans (by omega)
  
  have h100Sum :
      100 * (2 * kzx + 2 * kzy) + 100 * (2 * kx + 2 * ky) +
          (200 * ex + 200 * ey) ≥ 200 * kz := by
    omega
  have h100Upper : 100 * (2 * kx + 2 * ky) ≤ 400 * (2 * n + A * n + A) := by omega
  
  have hFinalInequality :
      100 * (2 * kzx + 2 * kzy) + 400 * (2 * n + A * n + A) +
          (n + kz + 1 + b1) ≥ 200 * kz := by
    have hM : M = n + kz + 1 := rfl
    omega
  
  have h_log_bound : 400 * A + b1 + 1 ≤ logSlack C n := by
    have hC : C = 400 * A + b1 + 1 := rfl
    rw [←hC]
    unfold logSlack
    exact Nat.le_add_left C (C * (Nat.bits n).length)
    
  have h_kz_lower : 400 * (A * n) + 1000 * n + 400 * A + b1 + 1 ≤ kz := by
    have hL : L = 400 * A + 1000 := rfl
    calc
      400 * (A * n) + 1000 * n + 400 * A + b1 + 1
        = (400 * A + 1000) * n + (400 * A + b1 + 1) := by ring
      _ ≤ L * n + logSlack C n := by
        rw [hL]
        exact Nat.add_le_add_left h_log_bound (L * n)
      _ ≤ kz := hkz
  
  clear hx hy hz hzx hzy hkxz hkyz hBalX hBalY hkxzUpper hkyzUpper
  clear hkzxUpper hkzyUpper hBits hdLinear hxArg hyArg hxLog hyLog hFoldMul
  clear hBound hExEyBound hzxBound hzyBound hSum hxUpper hyUpper h100Sum
  clear h100Upper hkz
  
  have h_goal_mul : 100 * kz ≤ 100 * (2 * kzx + 2 * kzy) + 100 * logSlack C n := by
    have h_log_pos : 0 ≤ 100 * logSlack C n := by positivity
    omega
  
  have h_goal : kz ≤ 2 * kzx + 2 * kzy + logSlack C n := by omega
  
  exact h_goal

/-- Every exact common-information witness profile for the incident edge obeys
the weighted `8n` lower bound, with one slack depending only on `n + C(z)`. -/
theorem theorem_227_weighted_profile_values
    (V : Map) (hV : isOptimalConditional V) :
  ∀ d, ∃ C, ∀ n (e : ConcreteIncidentEdge n)
      kxy kx ky z kz kxz kyz,
    HasPlainComplexityValue V
      (pairCode (concretePointCode n e.1.1)
        (concreteLineCode n e.1.2)) kxy →
    HasPlainComplexityValue V (concretePointCode n e.1.1) kx →
    HasPlainComplexityValue V (concreteLineCode n e.1.2) ky →
    HasPlainComplexityValue V z kz →
    HasPlainConditionalComplexityValue V (concretePointCode n e.1.1) z kxz →
    HasPlainConditionalComplexityValue V (concreteLineCode n e.1.2) z kyz →
    3 * n ≤ kxy + logSlack d n →
    NatCloseWithin kx (2 * n) (logSlack d n) →
    NatCloseWithin ky (2 * n) (logSlack d n) →
    let δ := logSlack C (n + kz + 1)
    8 * n ≤
      3 * (kz + 1 + δ) +
      2 * (kxz + 1 + δ) +
      2 * (kyz + 1 + δ) := by
  intro d
  obtain ⟨C_env, hEnv⟩ := theorem_227_incidence_region_containment V hV d
  obtain ⟨cBal, hBal⟩ := plainK_conditional_balance_values V hV
  obtain ⟨cCond, hCond⟩ := condKLePlainK V hV
  let a := 2 * d + 6
  let b_const := 2 * d + 2 * cCond + 1
  obtain ⟨cFold, hFold⟩ := logSlack_linear_bound cBal a b_const
  let a_env := 2 * d + 6
  let b_env := 2 * d + 2 * cCond + 1
  obtain ⟨cFold_env, hFold_env⟩ := logSlack_linear_bound C_env a_env b_env
  let C := cFold_env + cFold + d + cCond + 1
  refine ⟨C, ?_⟩
  intro n e kxy kx ky z kz kxz kyz hkxy hkx hky hz hkxz hkyz hHigh hxClose hyClose
  obtain ⟨kzx, hkzx⟩ := exists_plainConditionalComplexityValue V hV z (concretePointCode n e.1.1)
  obtain ⟨kzy, hkzy⟩ := exists_plainConditionalComplexityValue V hV z (concreteLineCode n e.1.2)
  have ht_in_region :
      (kz + 1, kxz + 1, kyz + 1) ∈ CommonInformationRegion V
        (concretePointCode n e.1.1) (concreteLineCode n e.1.2) := by
    dsimp [CommonInformationRegion]
    use z
    refine ⟨?_, ?_, ?_⟩
    · rw [hz]; exact_mod_cast Nat.lt_succ_self _
    · rw [hkxz]; exact_mod_cast Nat.lt_succ_self _
    · rw [hkyz]; exact_mod_cast Nat.lt_succ_self _
  have hEnv_app := hEnv n e kxy hkxy hHigh (kz + 1, kxz + 1, kyz + 1) ht_in_region
  
  have h_kxz : kxz ≤ kx + cCond := by
    have h := hCond (concretePointCode n e.1.1) z
    rw [hkxz, hkx] at h
    exact_mod_cast h
  have h_kyz : kyz ≤ ky + cCond := by
    have h := hCond (concreteLineCode n e.1.2) z
    rw [hkyz, hky] at h
    exact_mod_cast h
  have h_kzx : kzx ≤ kz + cCond := by
    have h := hCond z (concretePointCode n e.1.1)
    rw [hkzx, hz] at h
    exact_mod_cast h
  have h_kzy : kzy ≤ kz + cCond := by
    have h := hCond z (concreteLineCode n e.1.2)
    rw [hkzy, hz] at h
    exact_mod_cast h
    
  have h_kx_bound : kx ≤ 2 * n + logSlack d n := hxClose.left
  have h_ky_bound : ky ≤ 2 * n + logSlack d n := hyClose.left
  
  have hBits : (Nat.bits n).length ≤ n := length_natBits_le n
  have hdLinear : logSlack d n ≤ d * n + d := by
    unfold logSlack
    nlinarith [Nat.mul_le_mul_left d hBits]
    
  let M := n + kz + 1
  have hM_arg_env : n + kz + 1 + kxz + 1 + kyz + 1 + 1 ≤ a_env * M + b_env := by
    dsimp [a_env, b_env, M]
    nlinarith [h_kxz, h_kyz, h_kx_bound, h_ky_bound, hdLinear]
    
  have hxLog_env : logSlack C_env (n + kz + 1 + kxz + 1 + kyz + 1 + 1) ≤ logSlack cFold_env M :=
    (logSlack_mono_right C_env hM_arg_env).trans (hFold_env M)
  have hxLog_C : logSlack C_env (n + kz + 1 + kxz + 1 + kyz + 1 + 1) ≤ logSlack C (n + kz + 1) := by
    calc
      logSlack C_env (n + kz + 1 + kxz + 1 + kyz + 1 + 1) ≤
          logSlack cFold_env (n + kz + 1) := hxLog_env
      _ ≤ logSlack C (n + kz + 1) := by
        apply logSlack_mono_left
        dsimp [C]
        omega
        
  let α := kz + 1 + logSlack C (n + kz + 1)
  let β := kxz + 1 + logSlack C (n + kz + 1)
  let γ := kyz + 1 + logSlack C (n + kz + 1)
  
  have h_env_up : (α, β, γ) ∈ IncidenceRegionEnvelope n := by
    apply incidenceRegionEnvelope_upward_closed n hEnv_app
    · dsimp [α]; exact Nat.add_le_add_left hxLog_C _
    · dsimp [β]; exact Nat.add_le_add_left hxLog_C _
    · dsimp [γ]; exact Nat.add_le_add_left hxLog_C _
    
  let ex := logSlack cBal (kz + kx + kxz + kzx + 1)
  have hBalX : kx + kzx ≤ kz + kxz + ex :=
    hBal z (concretePointCode n e.1.1) kz kx kxz kzx hz hkx hkxz hkzx
  have hxArg : kz + kx + kxz + kzx + 1 ≤ a * M + b_const := by
    dsimp [a, b_const, M]
    nlinarith [h_kxz, h_kzx, h_kx_bound, hdLinear]
  have hex_bound : ex ≤ logSlack cFold M := (logSlack_mono_right cBal hxArg).trans (hFold M)
  
  have h2x : 2 * n ≤ α + β := by
    have hC1 : logSlack (cFold + d) M ≤ logSlack C M := by
      apply logSlack_mono_left
      dsimp [C]
      omega
    have h_d_mono : logSlack d n ≤ logSlack d M := logSlack_mono_right d (by dsimp [M]; omega)
    have h_sum :
        logSlack cFold M + logSlack d M = logSlack (cFold + d) M := by
      unfold logSlack
      ring
    calc
      2 * n ≤ kx + logSlack d n := hxClose.right
      _ ≤ (kx + kzx) + logSlack d n := by omega
      _ ≤ (kz + kxz + ex) + logSlack d n := by omega
      _ ≤ kz + kxz + logSlack cFold M + logSlack d n := by omega
      _ ≤ kz + kxz + logSlack cFold M + logSlack d M := by omega
      _ ≤ kz + kxz + logSlack (cFold + d) M := by omega
      _ ≤ kz + kxz + logSlack C M := by omega
      _ ≤ α + β := by
        dsimp [α, β, M]
        omega
  
  let ey := logSlack cBal (kz + ky + kyz + kzy + 1)
  have hBalY : ky + kzy ≤ kz + kyz + ey :=
    hBal z (concreteLineCode n e.1.2) kz ky kyz kzy hz hky hkyz hkzy
  have hyArg : kz + ky + kyz + kzy + 1 ≤ a * M + b_const := by
    dsimp [a, b_const, M]
    nlinarith [h_kyz, h_kzy, h_ky_bound, hdLinear]
  have hey_bound : ey ≤ logSlack cFold M := (logSlack_mono_right cBal hyArg).trans (hFold M)
  
  have h2y : 2 * n ≤ α + γ := by
    have hC1 : logSlack (cFold + d) M ≤ logSlack C M := by
      apply logSlack_mono_left
      dsimp [C]
      omega
    have h_d_mono : logSlack d n ≤ logSlack d M := logSlack_mono_right d (by dsimp [M]; omega)
    have h_sum :
        logSlack cFold M + logSlack d M = logSlack (cFold + d) M := by
      unfold logSlack
      ring
    calc
      2 * n ≤ ky + logSlack d n := hyClose.right
      _ ≤ (ky + kzy) + logSlack d n := by omega
      _ ≤ (kz + kyz + ey) + logSlack d n := by omega
      _ ≤ kz + kyz + logSlack cFold M + logSlack d n := by omega
      _ ≤ kz + kyz + logSlack cFold M + logSlack d M := by omega
      _ ≤ kz + kyz + logSlack (cFold + d) M := by omega
      _ ≤ kz + kyz + logSlack C M := by omega
      _ ≤ α + γ := by
        dsimp [α, γ, M]
        omega
        
  have h3xy : 3 * n ≤ α + β + γ := by
    have hS1 : 3 * n ≤ α + γ / 2 + max (γ / 2) β := h_env_up.1
    have h_max1 : max (γ / 2) β ≤ γ / 2 + β := by omega
    omega
          
  exact incidence_weighted_bound (fun _ => h_env_up.1) (fun _ => h_env_up.2) h2x h2y h3xy

/-- Theorem 227 with the intermediate `O(log (n + C(z)))` slack, obtained by
combining the weighted profile with conditional balance and
`theorem_227_arithmetic`. -/
theorem theorem_227_incidence_nonextractability_core
    (V : Map) (hV : isOptimalConditional V) :
  ∀ d, ∃ C, ∀ n (e : ConcreteIncidentEdge n) kxy kx ky,
    HasPlainComplexityValue V
      (pairCode (concretePointCode n e.1.1)
        (concreteLineCode n e.1.2)) kxy →
    HasPlainComplexityValue V (concretePointCode n e.1.1) kx →
    HasPlainComplexityValue V (concreteLineCode n e.1.2) ky →
    3 * n ≤ kxy + logSlack d n →
    NatCloseWithin kx (2 * n) (logSlack d n) →
    NatCloseWithin ky (2 * n) (logSlack d n) →
    ∀ z kz kzx kzy,
      HasPlainComplexityValue V z kz →
      HasPlainConditionalComplexityValue V z (concretePointCode n e.1.1) kzx →
      HasPlainConditionalComplexityValue V z (concreteLineCode n e.1.2) kzy →
      kz ≤ 2 * kzx + 2 * kzy + logSlack C (n + kz + 1) := by
  intro d
  obtain ⟨C_w, hW⟩ := theorem_227_weighted_profile_values V hV d
  obtain ⟨cBal, hBal⟩ := plainK_conditional_balance_values V hV
  obtain ⟨cCond, hCond⟩ := condKLePlainK V hV
  let a := 2 * d + 6
  let b_const := 2 * d + 2 * cCond + 1
  obtain ⟨cFold, hFold⟩ := logSlack_linear_bound cBal a b_const
  let C := 4 * cFold + 11 * C_w + 11 * d + 7
  refine ⟨C, ?_⟩
  intro n e kxy kx ky hkxy hkx hky hHigh hxClose hyClose z kz kzx kzy hz hkzx hkzy
  obtain ⟨kxz, hkxz⟩ := exists_plainConditionalComplexityValue V hV (concretePointCode n e.1.1) z
  obtain ⟨kyz, hkyz⟩ := exists_plainConditionalComplexityValue V hV (concreteLineCode n e.1.2) z
  have hW_app := hW n e kxy kx ky z kz kxz kyz hkxy hkx hky hz hkxz hkyz hHigh hxClose hyClose
  have h_kxz : kxz ≤ kx + cCond := by
    have h := hCond (concretePointCode n e.1.1) z
    rw [hkxz, hkx] at h
    exact_mod_cast h
  have h_kyz : kyz ≤ ky + cCond := by
    have h := hCond (concreteLineCode n e.1.2) z
    rw [hkyz, hky] at h
    exact_mod_cast h
  have h_kzx : kzx ≤ kz + cCond := by
    have h := hCond z (concretePointCode n e.1.1)
    rw [hkzx, hz] at h
    exact_mod_cast h
  have h_kzy : kzy ≤ kz + cCond := by
    have h := hCond z (concreteLineCode n e.1.2)
    rw [hkzy, hz] at h
    exact_mod_cast h
    
  have h_kx_bound : kx ≤ 2 * n + logSlack d n := hxClose.left
  have h_ky_bound : ky ≤ 2 * n + logSlack d n := hyClose.left
  
  have hBits : (Nat.bits n).length ≤ n := length_natBits_le n
  have hdLinear : logSlack d n ≤ d * n + d := by
    unfold logSlack
    nlinarith [Nat.mul_le_mul_left d hBits]
  let M := n + kz + 1
  let ex := logSlack cBal (kx + kz + kzx + kxz + 1)
  have hBalX : kz + kxz ≤ kx + kzx + ex :=
    hBal (concretePointCode n e.1.1) z kx kz kzx kxz hkx hz hkzx hkxz
  have hxArg : kx + kz + kzx + kxz + 1 ≤ a * M + b_const := by
    dsimp [a, b_const, M]
    nlinarith [h_kxz, h_kzx, h_kx_bound, hdLinear]
  have hex_bound : ex ≤ logSlack cFold M := (logSlack_mono_right cBal hxArg).trans (hFold M)
  
  let ey := logSlack cBal (ky + kz + kzy + kyz + 1)
  have hBalY : kz + kyz ≤ ky + kzy + ey :=
    hBal (concreteLineCode n e.1.2) z ky kz kzy kyz hky hz hkzy hkyz
  have hyArg : ky + kz + kzy + kyz + 1 ≤ a * M + b_const := by
    dsimp [a, b_const, M]
    nlinarith [h_kyz, h_kzy, h_ky_bound, hdLinear]
  have hey_bound : ey ≤ logSlack cFold M := (logSlack_mono_right cBal hyArg).trans (hFold M)
  have h_d_mono : logSlack d n ≤ logSlack d M := logSlack_mono_right d (by dsimp [M]; omega)
  let δ := logSlack C_w M
  let eps := logSlack cFold M
  let D := δ + logSlack d M
  have hEnvelope :
      8 * n ≤
        3 * (kz + 1 + D) + 2 * (kxz + 1 + D) +
          2 * (kyz + 1 + D) := by
    dsimp [D, δ, M]
    have := hW_app
    omega
  have hBalX' : kz + kxz ≤ kx + kzx + eps := by
    dsimp [eps]
    omega
  have hBalY' : kz + kyz ≤ ky + kzy + eps := by
    dsimp [eps]
    omega
  have hKx : kx ≤ 2 * n + D := by
    dsimp [D]
    omega
  have hKy : ky ≤ 2 * n + D := by
    dsimp [D]
    omega
  have hArith := theorem_227_arithmetic n kz kxz kyz D kx kzx eps ky kzy
    hEnvelope hBalX' hBalY' hKx hKy
  have hSlack : 4 * eps + 11 * D + 7 ≤ logSlack C M := by
    calc
      4 * eps + 11 * D + 7 =
          logSlack (4 * cFold + 11 * C_w + 11 * d) M + 7 := by
            dsimp [eps, D, δ]
            unfold logSlack
            ring
      _ ≤ logSlack (4 * cFold + 11 * C_w + 11 * d + 7) M :=
        logSlack_add_nat_le (4 * cFold + 11 * C_w + 11 * d) 7 M
      _ = logSlack C M := by rfl
  calc
    kz ≤ 2 * kzx + 2 * kzy + 4 * eps + 11 * D + 7 := hArith
    _ ≤ 2 * kzx + 2 * kzy + logSlack C M := by omega
    _ = 2 * kzx + 2 * kzy + logSlack C (n + kz + 1) := by rfl

/-- Value-level Theorem 227 once the incident edge's two marginal complexities
have been fixed and shown logarithmically close to `2 * n`. -/
theorem theorem_227_incidence_nonextractability_of_profile_values
    (V : Map) (hV : isOptimalConditional V) :
  ∀ d, ∃ C, ∀ n (e : ConcreteIncidentEdge n) kxy kx ky,
    HasPlainComplexityValue V
      (pairCode (concretePointCode n e.1.1)
        (concreteLineCode n e.1.2)) kxy →
    HasPlainComplexityValue V (concretePointCode n e.1.1) kx →
    HasPlainComplexityValue V (concreteLineCode n e.1.2) ky →
    3 * n ≤ kxy + logSlack d n →
    NatCloseWithin kx (2 * n) (logSlack d n) →
    NatCloseWithin ky (2 * n) (logSlack d n) →
    ∀ z kz kzx kzy,
      HasPlainComplexityValue V z kz →
      HasPlainConditionalComplexityValue V z (concretePointCode n e.1.1) kzx →
      HasPlainConditionalComplexityValue V z (concreteLineCode n e.1.2) kzy →
      kz ≤ 2 * kzx + 2 * kzy + logSlack C n := by
  intro d
  obtain ⟨Ccore, hcore⟩ := theorem_227_incidence_nonextractability_core V hV d
  obtain ⟨Clarge, L, hlarge⟩ := theorem_227_large_z_case V hV d
  obtain ⟨b, hb⟩ := logSlack_le_add_const Clarge
  obtain ⟨Csmall, hsmall⟩ :=
    logSlack_linear_bound Ccore (L + 2) (b + 1)
  let C := Clarge + Csmall
  refine ⟨C, ?_⟩
  intro n e kxy kx ky hkxy hkx hky hHigh hxClose hyClose
    z kz kzx kzy hz hkzx hkzy
  by_cases hLarge : L * n + logSlack Clarge n ≤ kz
  · have h := hlarge n
      (concretePointCode n e.1.1) (concreteLineCode n e.1.2)
      kx ky z kz kzx kzy hkx hky hz hkzx hkzy
      hxClose.1 hyClose.1 hLarge
    have hSlack : logSlack Clarge n ≤ logSlack C n := by
      apply logSlack_mono_left
      dsimp [C]
      omega
    omega
  · have hkz : kz ≤ L * n + logSlack Clarge n := by omega
    have harg : n + kz + 1 ≤ (L + 2) * n + (b + 1) := by
      have hlog := hb n
      nlinarith
    have hfold : logSlack Ccore (n + kz + 1) ≤ logSlack Csmall n :=
      (logSlack_mono_right Ccore harg).trans (hsmall n)
    have h := hcore n e kxy kx ky hkxy hkx hky hHigh hxClose hyClose
      z kz kzx kzy hz hkzx hkzy
    have hSlack : logSlack Csmall n ≤ logSlack C n := by
      apply logSlack_mono_left
      dsimp [C]
      omega
    omega

/-- **SUV Theorem 227.** Every sufficiently incompressible incident point/line
pair over the concrete field has no extractable common information: uniformly
for every string `z`, its plain complexity is bounded by twice each of its two
conditional complexities, up to `O(log n)`.

The marginal `2 * n + O(log n)` profile is derived here from Exercise 309; it
is not an extra hypothesis of the public theorem. -/
theorem theorem_227_incidence_nonextractability
    (V : Map) (hV : isOptimalConditional V) :
  ∀ d, ∃ C, ∀ n (e : ConcreteIncidentEdge n) kxy,
    HasPlainComplexityValue V
      (pairCode (concretePointCode n e.1.1)
        (concreteLineCode n e.1.2)) kxy →
    3 * n ≤ kxy + logSlack d n →
    ∀ z kz kzx kzy,
      HasPlainComplexityValue V z kz →
      HasPlainConditionalComplexityValue V z
        (concretePointCode n e.1.1) kzx →
      HasPlainConditionalComplexityValue V z
        (concreteLineCode n e.1.2) kzy →
      kz ≤ 2 * kzx + 2 * kzy + logSlack C n := by
  intro d
  obtain ⟨Cprofile, hprofile⟩ := exercise_309_incident_edge_profile V hV d
  let A := d + Cprofile
  obtain ⟨C, hC⟩ :=
    theorem_227_incidence_nonextractability_of_profile_values V hV A
  refine ⟨C, ?_⟩
  intro n e kxy hkxy hHigh z kz kzx kzy hz hkzx hkzy
  obtain ⟨kx, ky, hkx, hky, hxClose, hyClose, _, _⟩ :=
    hprofile n e kxy hkxy hHigh
  have hdA : logSlack d n ≤ logSlack A n := by
    apply logSlack_mono_left
    dsimp [A]
    omega
  have hprofileA : logSlack Cprofile n ≤ logSlack A n := by
    apply logSlack_mono_left
    dsimp [A]
    omega
  have hHighA : 3 * n ≤ kxy + logSlack A n := by omega
  have hxCloseA : NatCloseWithin kx (2 * n) (logSlack A n) := by
    unfold NatCloseWithin at hxClose ⊢
    omega
  have hyCloseA : NatCloseWithin ky (2 * n) (logSlack A n) := by
    unfold NatCloseWithin at hyClose ⊢
    omega
  exact hC n e kxy kx ky hkxy hkx hky hHighA hxCloseA hyCloseA
    z kz kzx kzy hz hkzx hkzy

end Kolmogorov
