import KolmogorovMathlib.CommonInformation.RegionLower
import KolmogorovMathlib.CommonInformation.PlainCoding
import KolmogorovMathlib.CommonInformation.PlainSymmetry
import KolmogorovMathlib.CommonInformation.SharedDescriptionLengths

/-!
# Consequences of the extremal common-information region

This module gives the exact value-level formalization of SUV Theorem 226 and
begins Exercise 308. Polyhedral arithmetic, symmetry-of-information transport,
and uniform logarithmic folding are kept as separate lemmas.
-/

namespace Kolmogorov

/-- Every point of the lower envelope satisfies the weighted inequality used
in the proof of SUV Theorem 226. -/
theorem commonInformationLowerEnvelope_weighted_bound
    {n : Nat} {t : CommonInformationTriple}
    (ht : t ∈ CommonInformationLowerEnvelope n) :
    8 * n < 3 * t.1 + 2 * t.2.1 + 2 * t.2.2 := by
  rcases ht with ⟨hUpper, hFace⟩
  change
    2 * n < t.1 + t.2.1 ∧
      2 * n < t.1 + t.2.2 ∧
      3 * n < t.1 + t.2.1 + t.2.2 at hUpper
  change
    3 * n < t.1 + t.2.1 ∨
      3 * n < t.1 + t.2.2 ∨
      4 * n < t.1 + t.2.1 + t.2.2 at hFace
  rcases hFace with hLeft | hRight | hJoint <;> omega

/-- Conditional-balance inequality. -/
theorem plainK_conditional_balance_values
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c, ∀ x z kx kz kzx kxz,
      HasPlainComplexityValue V x kx →
      HasPlainComplexityValue V z kz →
      HasPlainConditionalComplexityValue V z x kzx →
      HasPlainConditionalComplexityValue V x z kxz →
      kz + kxz ≤ kx + kzx + logSlack c (kx + kz + kzx + kxz + 1) := by
  obtain ⟨cRaw, hRaw⟩ := extractable_chain_length_close V hV
  obtain ⟨cCrude, hCrude⟩ :=
    pairPlainK_twoStage_crude_values V hV
  obtain ⟨cFold, hFold⟩ :=
    logSlack_linear_bound cRaw 3 (cCrude + 2)
  let C := cFold + cFold
  refine ⟨C, ?_⟩
  intro x z kx kz kzx kxz hx hz hzx hxz
  obtain ⟨kzxPair, hzxPair, hzxPairBound⟩ :=
    hCrude z x kz kxz hz hxz
  obtain ⟨kxzPair, hxzPair, hxzPairBound⟩ :=
    hCrude x z kx kzx hx hzx
  let N := kx + kz + kzx + kxz + 1
  have hzxPairLinear :
      kzxPair + 1 ≤ 3 * N + (cCrude + 2) := by
    dsimp [N]
    omega
  have hxzPairLinear :
      kxzPair + 1 ≤ 3 * N + (cCrude + 2) := by
    dsimp [N]
    omega
  have hzxLog :
      logSlack cRaw (kzxPair + 1) ≤ logSlack cFold N :=
    (logSlack_mono_right cRaw hzxPairLinear).trans (hFold N)
  have hxzLog :
      logSlack cRaw (kxzPair + 1) ≤ logSlack cFold N :=
    (logSlack_mono_right cRaw hxzPairLinear).trans (hFold N)
  have hLogs :
      logSlack cRaw (kzxPair + 1) +
          logSlack cRaw (kxzPair + 1) ≤ logSlack C N := by
    calc
      logSlack cRaw (kzxPair + 1) +
          logSlack cRaw (kxzPair + 1)
          ≤ logSlack cFold N + logSlack cFold N :=
        Nat.add_le_add hzxLog hxzLog
      _ = logSlack C N := by
        dsimp [C]
        exact logSlack_add_const _ _ _
  have hClose := hRaw x z kx kz kxz kzx kzxPair kxzPair kzx
    hx hz hxz hzx hzxPair hxzPair le_rfl
  dsimp [N] at hLogs
  unfold NatCloseWithin at hClose
  omega

/-- Pure arithmetic assembly for Theorem 226. -/
theorem theorem_226_arithmetic
    (n kz kxz kyz d kx kzx e ky kzy : Nat)
    (h_envelope : 8 * n < 3 * (kz + 1 + d) + 2 * (kxz + 1 + d) + 2 * (kyz + 1 + d))
    (h_bal_x : kz + kxz ≤ kx + kzx + e)
    (h_bal_y : kz + kyz ≤ ky + kzy + e)
    (h_kx : kx ≤ 2 * n + d)
    (h_ky : ky ≤ 2 * n + d) :
    kz ≤ 2 * kzx + 2 * kzy + 4 * e + 11 * d + 7 := by
  omega

/-- Uniform slack folding as specified in the Aristotle Leaf Packet. -/
theorem theorem_226_slack_folding
    (V : Map) (hV : isOptimalConditional V)
    (cBal A : Nat) :
    ∃ C : Nat, ∀ n x y kx ky kxy z kz kzx kzy kxz kyz,
      HasPlainComplexityValue V x kx →
      HasPlainComplexityValue V y ky →
      HasPlainComplexityValue V (pairCode x y) kxy →
      NatCloseWithin kx (2 * n) (logSlack A n) →
      NatCloseWithin ky (2 * n) (logSlack A n) →
      NatCloseWithin kxy (3 * n) (logSlack A n) →
      HasPlainComplexityValue V z kz →
      HasPlainConditionalComplexityValue V z x kzx →
      HasPlainConditionalComplexityValue V z y kzy →
      HasPlainConditionalComplexityValue V x z kxz →
      HasPlainConditionalComplexityValue V y z kyz →
      let d := logSlack A n
      let e := logSlack cBal (kx + kz + kzx + kxz + 1) + logSlack cBal (ky + kz + kzy + kyz + 1)
      kz ≤ 2 * kzx + 2 * kzy + 4 * e + 11 * d + 7 →
      kz ≤ 2 * kzx + 2 * kzy + logSlack C (n + kz + 1) := by
  obtain ⟨cCond, hCond⟩ := condKLePlainK V hV
  let a := 2 * A + 6
  let b := 2 * A + 2 * cCond + 1
  obtain ⟨cFold, hFold⟩ := logSlack_linear_bound cBal a b
  let cE := cFold + cFold
  let C := 4 * cE + 11 * A + 7
  refine ⟨C, ?_⟩
  intro n x y kx ky kxy z kz kzx kzy kxz kyz
    hx hy hxy hkx hky hkxy hz hzx hzy hxz hyz
  dsimp only
  intro hArith
  have hkzx : kzx ≤ kz + cCond := by
    have h := hCond z x
    rw [hzx, hz] at h
    exact_mod_cast h
  have hkzy : kzy ≤ kz + cCond := by
    have h := hCond z y
    rw [hzy, hz] at h
    exact_mod_cast h
  have hkxz : kxz ≤ kx + cCond := by
    have h := hCond x z
    rw [hxz, hx] at h
    exact_mod_cast h
  have hkyz : kyz ≤ ky + cCond := by
    have h := hCond y z
    rw [hyz, hy] at h
    exact_mod_cast h
  have hBits : (Nat.bits n).length ≤ n := length_natBits_le n
  have hdLinear : logSlack A n ≤ A * n + A := by
    unfold logSlack
    nlinarith [Nat.mul_le_mul_left A hBits]
  have hkxUpper : kx ≤ 2 * n + logSlack A n := hkx.1
  have hkyUpper : ky ≤ 2 * n + logSlack A n := hky.1
  let M := n + kz + 1
  have hxArg :
      kx + kz + kzx + kxz + 1 ≤ a * M + b := by
    dsimp [a, b, M]
    nlinarith [Nat.zero_le (A * kz)]
  have hyArg :
      ky + kz + kzy + kyz + 1 ≤ a * M + b := by
    dsimp [a, b, M]
    nlinarith [Nat.zero_le (A * kz)]
  have hxLog :
      logSlack cBal (kx + kz + kzx + kxz + 1) ≤
        logSlack cFold M :=
    (logSlack_mono_right cBal hxArg).trans (hFold M)
  have hyLog :
      logSlack cBal (ky + kz + kzy + kyz + 1) ≤
        logSlack cFold M :=
    (logSlack_mono_right cBal hyArg).trans (hFold M)
  have hE :
      logSlack cBal (kx + kz + kzx + kxz + 1) +
          logSlack cBal (ky + kz + kzy + kyz + 1) ≤
        logSlack cE M := by
    calc
      logSlack cBal (kx + kz + kzx + kxz + 1) +
          logSlack cBal (ky + kz + kzy + kyz + 1)
          ≤ logSlack cFold M + logSlack cFold M :=
        Nat.add_le_add hxLog hyLog
      _ = logSlack cE M := by
        dsimp [cE]
        exact logSlack_add_const _ _ _
  have hdM : logSlack A n ≤ logSlack A M :=
    logSlack_mono_right A (by dsimp [M]; omega)
  have hOverhead :
      4 * (logSlack cBal (kx + kz + kzx + kxz + 1) +
          logSlack cBal (ky + kz + kzy + kyz + 1)) +
          11 * logSlack A n + 7 ≤ logSlack C M := by
    calc
      4 * (logSlack cBal (kx + kz + kzx + kxz + 1) +
          logSlack cBal (ky + kz + kzy + kyz + 1)) +
          11 * logSlack A n + 7
          ≤ 4 * logSlack cE M + 11 * logSlack A M + 7 := by
        omega
      _ = logSlack (4 * cE + 11 * A) M + 7 := by
        unfold logSlack
        ring
      _ ≤ logSlack C M := by
        simpa [C] using
          logSlack_add_nat_le (4 * cE + 11 * A) 7 M
  calc
    kz ≤ 2 * kzx + 2 * kzy +
        (4 * (logSlack cBal (kx + kz + kzx + kxz + 1) +
          logSlack cBal (ky + kz + kzy + kyz + 1)) +
          11 * logSlack A n + 7) := by
      omega
    _ ≤ 2 * kzx + 2 * kzy + logSlack C M :=
      Nat.add_le_add_left hOverhead _
    _ = 2 * kzx + 2 * kzy + logSlack C (n + kz + 1) := by
      rfl

/-- **SUV Theorem 226.**  A pair whose exact common-information
region has the Theorem 225 lower-envelope upper containment cannot make a
complex string simultaneously simple relative to both components.  The public
statement uses exact finite plain-complexity values and keeps the source's
logarithmic dependence visible in `n + C(z) + 1`. -/
theorem theorem_226_minimal_region_nonextractability
    (V : Map) (hV : isOptimalConditional V) :
    ∀ A : Nat, ∃ C : Nat, ∀ n : Nat, ∀ x y : BitString,
      ∀ kx ky kxy : Nat,
        HasPlainComplexityValue V x kx →
        HasPlainComplexityValue V y ky →
        HasPlainComplexityValue V (pairCode x y) kxy →
        NatCloseWithin kx (2 * n) (logSlack A n) →
        NatCloseWithin ky (2 * n) (logSlack A n) →
        NatCloseWithin kxy (3 * n) (logSlack A n) →
        (∀ t ∈ CommonInformationRegion V x y,
          commonInformationTripleInflate (logSlack A n) t ∈
            CommonInformationLowerEnvelope n) →
        ∀ z : BitString, ∀ kz kzx kzy : Nat,
          HasPlainComplexityValue V z kz →
          HasPlainConditionalComplexityValue V z x kzx →
          HasPlainConditionalComplexityValue V z y kzy →
          kz ≤ 2 * kzx + 2 * kzy + logSlack C (n + kz + 1) := by
  intro A
  obtain ⟨cBal, hBal⟩ := plainK_conditional_balance_values V hV
  obtain ⟨C, hC⟩ := theorem_226_slack_folding V hV cBal A
  use C
  intro n x y kx ky kxy hx hy hxy hkx hky hkxy hEnv z kz kzx kzy hz hzx hzy
  obtain ⟨kxz, hkxz⟩ := exists_plainConditionalComplexityValue V hV x z
  obtain ⟨kyz, hkyz⟩ := exists_plainConditionalComplexityValue V hV y z
  let d := logSlack A n
  have ht_in_region : (kz + 1, kxz + 1, kyz + 1) ∈ CommonInformationRegion V x y := by
    dsimp [CommonInformationRegion]
    use z
    refine ⟨?_, ?_, ?_⟩
    · rw [hz]; exact_mod_cast Nat.lt_succ_self _
    · rw [hkxz]; exact_mod_cast Nat.lt_succ_self _
    · rw [hkyz]; exact_mod_cast Nat.lt_succ_self _
  have ht_env := hEnv (kz + 1, kxz + 1, kyz + 1) ht_in_region
  have h_bound := commonInformationLowerEnvelope_weighted_bound ht_env
  let e_x := logSlack cBal (kx + kz + kzx + kxz + 1)
  let e_y := logSlack cBal (ky + kz + kzy + kyz + 1)
  let e := e_x + e_y
  have h_bal_x_ineq : kz + kxz ≤ kx + kzx + e_x := hBal x z kx kz kzx kxz hx hz hzx hkxz
  have h_bal_x : kz + kxz ≤ kx + kzx + e := by omega
  have h_bal_y_ineq : kz + kyz ≤ ky + kzy + e_y := hBal y z ky kz kzy kyz hy hz hzy hkyz
  have h_bal_y : kz + kyz ≤ ky + kzy + e := by omega
  have h_kx : kx ≤ 2 * n + d := hkx.left
  have h_ky : ky ≤ 2 * n + d := hky.left
  have h_arith := theorem_226_arithmetic n kz kxz kyz d kx kzx e ky kzy
    h_bound h_bal_x h_bal_y h_kx h_ky
  exact hC n x y kx ky kxy z kz kzx kzy kxz kyz
    hx hy hxy hkx hky hkxy hz hzx hzy hkxz hkyz h_arith

/-- The face-by-face arithmetic behind the coefficient-one, small-`z` part of
Exercise 308. On either side face, smallness of `kz` converts the corresponding
conditional lower bound into the conclusion; on the joint face the conclusion
holds without the smallness hypothesis. -/
theorem exercise_308_small_arithmetic
    (n kz kxz kyz d kx kzx ex ky kzy ey : Nat)
    (h_face :
      3 * n < (kz + 1 + d) + (kxz + 1 + d) ∨
      3 * n < (kz + 1 + d) + (kyz + 1 + d) ∨
      4 * n < (kz + 1 + d) + (kxz + 1 + d) + (kyz + 1 + d))
    (h_bal_x : kz + kxz ≤ kx + kzx + ex)
    (h_bal_y : kz + kyz ≤ ky + kzy + ey)
    (h_kx : kx ≤ 2 * n + d)
    (h_ky : ky ≤ 2 * n + d)
    (h_small : kz ≤ n + d) :
    kz ≤ kzx + kzy + ex + ey + 5 * d + 3 := by
  rcases h_face with hLeft | hRight | hJoint <;> omega

/-- Pure logarithmic folding leaf for the small-`z` part of Exercise 308.
All parameters affecting the resulting constant precede the varying values. -/
theorem exercise_308_small_slack_folding
    (cBal A cCond : Nat) :
    ∃ C : Nat, ∀ n kx ky kz kzx kzy kxz kyz,
      kx ≤ 2 * n + logSlack A n →
      ky ≤ 2 * n + logSlack A n →
      kzx ≤ kz + cCond →
      kzy ≤ kz + cCond →
      kxz ≤ kx + cCond →
      kyz ≤ ky + cCond →
      logSlack cBal (kx + kz + kzx + kxz + 1) +
          logSlack cBal (ky + kz + kzy + kyz + 1) +
          5 * logSlack A n + 3 ≤
        logSlack C (n + kz + 1) := by
  let a := 2 * A + 6
  let b := 2 * A + 2 * cCond + 1
  obtain ⟨cFold, hFold⟩ := logSlack_linear_bound cBal a b
  let cE := cFold + cFold
  let C := cE + 5 * A + 3
  refine ⟨C, ?_⟩
  intro n kx ky kz kzx kzy kxz kyz
    hkx hky hkzx hkzy hkxz hkyz
  have hBits : (Nat.bits n).length ≤ n := length_natBits_le n
  have hdLinear : logSlack A n ≤ A * n + A := by
    unfold logSlack
    nlinarith [Nat.mul_le_mul_left A hBits]
  let M := n + kz + 1
  have hxArg :
      kx + kz + kzx + kxz + 1 ≤ a * M + b := by
    dsimp [a, b, M]
    nlinarith [Nat.zero_le (A * kz)]
  have hyArg :
      ky + kz + kzy + kyz + 1 ≤ a * M + b := by
    dsimp [a, b, M]
    nlinarith [Nat.zero_le (A * kz)]
  have hxLog :
      logSlack cBal (kx + kz + kzx + kxz + 1) ≤
        logSlack cFold M :=
    (logSlack_mono_right cBal hxArg).trans (hFold M)
  have hyLog :
      logSlack cBal (ky + kz + kzy + kyz + 1) ≤
        logSlack cFold M :=
    (logSlack_mono_right cBal hyArg).trans (hFold M)
  have hE :
      logSlack cBal (kx + kz + kzx + kxz + 1) +
          logSlack cBal (ky + kz + kzy + kyz + 1) ≤
        logSlack cE M := by
    calc
      logSlack cBal (kx + kz + kzx + kxz + 1) +
          logSlack cBal (ky + kz + kzy + kyz + 1)
          ≤ logSlack cFold M + logSlack cFold M :=
        Nat.add_le_add hxLog hyLog
      _ = logSlack cE M := by
        dsimp [cE]
        exact logSlack_add_const _ _ _
  have hdM : logSlack A n ≤ logSlack A M :=
    logSlack_mono_right A (by dsimp [M]; omega)
  calc
    logSlack cBal (kx + kz + kzx + kxz + 1) +
        logSlack cBal (ky + kz + kzy + kyz + 1) +
        5 * logSlack A n + 3
        ≤ logSlack cE M + 5 * logSlack A M + 3 := by
      omega
    _ = logSlack (cE + 5 * A) M + 3 := by
      unfold logSlack
      ring
    _ ≤ logSlack C M := by
      simpa [C] using logSlack_add_nat_le (cE + 5 * A) 3 M
    _ = logSlack C (n + kz + 1) := by
      rfl

/-- **SUV Exercise 308, small-complexity half.** For a pair realizing the
minimal common-information region, a string of complexity at most
`n + O(log n)` satisfies the coefficient-one non-extractability bound. The
precision is uniform and remains logarithmic in `n + C(z)`. -/
theorem exercise_308_small_common_string_nonextractability
    (V : Map) (hV : isOptimalConditional V) :
    ∀ A : Nat, ∃ C : Nat, ∀ n : Nat, ∀ x y : BitString,
      ∀ kx ky kxy : Nat,
        HasPlainComplexityValue V x kx →
        HasPlainComplexityValue V y ky →
        HasPlainComplexityValue V (pairCode x y) kxy →
        NatCloseWithin kx (2 * n) (logSlack A n) →
        NatCloseWithin ky (2 * n) (logSlack A n) →
        NatCloseWithin kxy (3 * n) (logSlack A n) →
        (∀ t ∈ CommonInformationRegion V x y,
          commonInformationTripleInflate (logSlack A n) t ∈
            CommonInformationLowerEnvelope n) →
        ∀ z : BitString, ∀ kz kzx kzy : Nat,
          HasPlainComplexityValue V z kz →
          HasPlainConditionalComplexityValue V z x kzx →
          HasPlainConditionalComplexityValue V z y kzy →
          kz ≤ n + logSlack A n →
          kz ≤ kzx + kzy + logSlack C (n + kz + 1) := by
  intro A
  obtain ⟨cBal, hBal⟩ := plainK_conditional_balance_values V hV
  obtain ⟨cCond, hCond⟩ := condKLePlainK V hV
  obtain ⟨C, hFold⟩ :=
    exercise_308_small_slack_folding cBal A cCond
  refine ⟨C, ?_⟩
  intro n x y kx ky kxy hx hy hxy hkx hky hkxy hEnv
    z kz kzx kzy hz hzx hzy hSmall
  obtain ⟨kxz, hkxz⟩ := exists_plainConditionalComplexityValue V hV x z
  obtain ⟨kyz, hkyz⟩ := exists_plainConditionalComplexityValue V hV y z
  let d := logSlack A n
  have ht_in_region :
      (kz + 1, kxz + 1, kyz + 1) ∈ CommonInformationRegion V x y := by
    dsimp [CommonInformationRegion]
    use z
    refine ⟨?_, ?_, ?_⟩
    · rw [hz]
      exact_mod_cast Nat.lt_succ_self _
    · rw [hkxz]
      exact_mod_cast Nat.lt_succ_self _
    · rw [hkyz]
      exact_mod_cast Nat.lt_succ_self _
  have hFace := (hEnv (kz + 1, kxz + 1, kyz + 1) ht_in_region).2
  change
    3 * n < (kz + 1 + d) + (kxz + 1 + d) ∨
      3 * n < (kz + 1 + d) + (kyz + 1 + d) ∨
      4 * n < (kz + 1 + d) + (kxz + 1 + d) + (kyz + 1 + d)
    at hFace
  let ex := logSlack cBal (kx + kz + kzx + kxz + 1)
  let ey := logSlack cBal (ky + kz + kzy + kyz + 1)
  have hBalX : kz + kxz ≤ kx + kzx + ex :=
    hBal x z kx kz kzx kxz hx hz hzx hkxz
  have hBalY : kz + kyz ≤ ky + kzy + ey :=
    hBal y z ky kz kzy kyz hy hz hzy hkyz
  have hRaw := exercise_308_small_arithmetic
    n kz kxz kyz d kx kzx ex ky kzy ey hFace hBalX hBalY
    hkx.1 hky.1 hSmall
  have hkzx : kzx ≤ kz + cCond := by
    have h := hCond z x
    rw [hzx, hz] at h
    exact_mod_cast h
  have hkzy : kzy ≤ kz + cCond := by
    have h := hCond z y
    rw [hzy, hz] at h
    exact_mod_cast h
  have hkxzUpper : kxz ≤ kx + cCond := by
    have h := hCond x z
    rw [hkxz, hx] at h
    exact_mod_cast h
  have hkyzUpper : kyz ≤ ky + cCond := by
    have h := hCond y z
    rw [hkyz, hy] at h
    exact_mod_cast h
  have hError := hFold n kx ky kz kzx kzy kxz kyz
    hkx.1 hky.1 hkzx hkzy hkxzUpper hkyzUpper
  dsimp [d, ex, ey] at hRaw
  calc
    kz ≤ kzx + kzy +
        (logSlack cBal (kx + kz + kzx + kxz + 1) +
          logSlack cBal (ky + kz + kzy + kyz + 1) +
          5 * logSlack A n + 3) := by
      omega
    _ ≤ kzx + kzy + logSlack C (n + kz + 1) :=
      Nat.add_le_add_left hError _

/-- A shortest representation of `y` transports a conditional description
from `x` while remaining simple given `y` and preserving the plain complexity
of `y`, all within one logarithmic budget. -/
theorem shortest_representation_transport
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c, ∀ x y ky kyx,
      HasPlainComplexityValue V y ky →
      HasPlainConditionalComplexityValue V y x kyx →
      ∃ z kz kzx kzy,
        HasPlainComplexityValue V z kz ∧
        HasPlainConditionalComplexityValue V z x kzx ∧
        HasPlainConditionalComplexityValue V z y kzy ∧
        NatCloseWithin kz ky (logSlack c (ky + kyx + 1)) ∧
        kzx ≤ kyx + logSlack c (ky + kyx + 1) ∧
        kzy ≤ logSlack c (ky + kyx + 1) := by
  -- We use z = y as the witness
  -- First obtain constants we'll need
  obtain ⟨cSelf, hcSelf⟩ := condKSelf V hV
  -- Use c = cSelf; for n ≥ 1, logSlack cSelf n ≥ 2*cSelf ≥ cSelf
  use cSelf
  intro x y ky kyx hy hyx
  -- Get a Nat value for condK V y y
  obtain ⟨kzy, hkzy⟩ := exists_plainConditionalComplexityValue V hV y y
  -- z = y, kz = ky, kzx = kyx, kzy = kzy from above
  use y, ky, kyx, kzy
  refine ⟨hy, hyx, hkzy, ?_, ?_, ?_⟩
  -- 1. NatCloseWithin ky ky (logSlack cSelf (ky + kyx + 1))
  · unfold NatCloseWithin
    exact ⟨le_add_right le_rfl, le_add_right le_rfl⟩
  -- 2. kyx ≤ kyx + logSlack cSelf (ky + kyx + 1)
  · apply Nat.le_add_right
  -- 3. kzy ≤ logSlack cSelf (ky + kyx + 1)
  · have h_bound := hcSelf y
    rw [hkzy] at h_bound
    have h_cs : kzy ≤ cSelf := by exact_mod_cast h_bound
    have h_log : cSelf ≤ logSlack cSelf (ky + kyx + 1) := by
      unfold logSlack
      have h_pos : 0 < ky + kyx + 1 := by omega
      have h_pow := lt_two_pow_length_natBits (ky + kyx + 1)
      have h_bits : 1 ≤ (Nat.bits (ky + kyx + 1)).length := by
        contrapose! h_pow
        interval_cases (Nat.bits (ky + kyx + 1)).length
        simp
      nlinarith
    exact h_cs.trans h_log

/-- Uniform logarithmic folding for the sharpness construction. -/
theorem exercise_308_sharp_slack_folding
    (A B c : Nat) :
    ∃ C : Nat, ∀ n ky kyx kz kzx kzy,
      NatCloseWithin ky (2 * n) (logSlack A n) →
      NatCloseWithin kyx n (logSlack B n) →
      NatCloseWithin kz ky (logSlack c (ky + kyx + 1)) →
      kzx ≤ kyx + logSlack c (ky + kyx + 1) →
      kzy ≤ logSlack c (ky + kyx + 1) →
      A ≤ C ∧
      NatCloseWithin kz (2 * n) (logSlack C n) ∧
      kzx ≤ n + logSlack C n ∧
      kzy ≤ logSlack C n ∧
      n + kzx + kzy ≤ kz + 3 * logSlack C n := by
  obtain ⟨cFold, hFold⟩ :=
    logSlack_linear_bound c (3 + A + B) (A + B + 1)
  let C := A + B + 3 * cFold
  refine ⟨C, ?_⟩
  intro n ky kyx kz kzx kzy hy hyx hz hzx hzy
  have hBits : (Nat.bits n).length ≤ n := length_natBits_le n
  have hALinear : logSlack A n ≤ A * n + A := by
    unfold logSlack
    nlinarith [Nat.mul_le_mul_left A hBits]
  have hBLinear : logSlack B n ≤ B * n + B := by
    unfold logSlack
    nlinarith [Nat.mul_le_mul_left B hBits]
  have hArg : ky + kyx + 1 ≤ (3 + A + B) * n + (A + B + 1) := by
    unfold NatCloseWithin at hy hyx
    nlinarith
  have hS :
      logSlack c (ky + kyx + 1) ≤ logSlack cFold n :=
    (logSlack_mono_right c hArg).trans (hFold n)
  have hA : logSlack A n ≤ logSlack C n :=
    logSlack_mono_left (by dsimp [C]; omega) n
  have hB : logSlack B n ≤ logSlack C n :=
    logSlack_mono_left (by dsimp [C]; omega) n
  have hF : logSlack cFold n ≤ logSlack C n :=
    logSlack_mono_left (by dsimp [C]; omega) n
  refine ⟨by dsimp [C]; omega, ?_, ?_, ?_, ?_⟩
  · exact (hz.trans hy).mono (by
      calc
        logSlack c (ky + kyx + 1) + logSlack A n
            ≤ logSlack cFold n + logSlack A n := Nat.add_le_add_right hS _
        _ ≤ logSlack C n := by
          rw [logSlack_add_const]
          exact logSlack_mono_left (by dsimp [C]; omega) n)
  · calc
      kzx ≤ kyx + logSlack c (ky + kyx + 1) := hzx
      _ ≤ kyx + logSlack cFold n := Nat.add_le_add_left hS _
      _ ≤ n + logSlack B n + logSlack cFold n :=
        Nat.add_le_add_right hyx.1 _
      _ ≤ n + logSlack C n := by
        rw [Nat.add_assoc]
        exact Nat.add_le_add_left (by
          rw [logSlack_add_const]
          exact logSlack_mono_left (by dsimp [C]; omega) n) n
  · exact hzy.trans (hS.trans hF)
  · unfold NatCloseWithin at hy hyx hz
    have hBudget :
        logSlack A n + logSlack B n + 3 * logSlack cFold n ≤
          3 * logSlack C n := by
      have hExact :
          logSlack A n + logSlack B n + 3 * logSlack cFold n =
            logSlack C n := by
        unfold logSlack
        dsimp [C]
        ring
      rw [hExact]
      omega
    omega

/-- **SUV Exercise 308, sharpness half.** The coefficient `2` from
Theorem 226 is asymptotically necessary: for a pair realizing the minimal
region there is a common string of complexity `2n + O(log n)` whose two
conditional complexities have sum at most `n + O(log n)`. The final additive
inequality exposes the resulting linear gap without division or truncated
subtraction. -/
theorem exercise_308_coefficient_two_sharp
    (V : Map) (hV : isOptimalConditional V) :
    ∃ C : Nat, ∀ n : Nat,
      ∃ x y z : BitString, ∃ kx ky kxy kz kzx kzy : Nat,
        HasPlainComplexityValue V x kx ∧
        HasPlainComplexityValue V y ky ∧
        HasPlainComplexityValue V (pairCode x y) kxy ∧
        NatCloseWithin kx (2 * n) (logSlack C n) ∧
        NatCloseWithin ky (2 * n) (logSlack C n) ∧
        NatCloseWithin kxy (3 * n) (logSlack C n) ∧
        (∀ t ∈ CommonInformationLowerEnvelope n,
          commonInformationTripleInflate (logSlack C n) t ∈
            CommonInformationRegion V x y) ∧
        (∀ t ∈ CommonInformationRegion V x y,
          commonInformationTripleInflate (logSlack C n) t ∈
            CommonInformationLowerEnvelope n) ∧
        HasPlainComplexityValue V z kz ∧
        HasPlainConditionalComplexityValue V z x kzx ∧
        HasPlainConditionalComplexityValue V z y kzy ∧
        NatCloseWithin kz (2 * n) (logSlack C n) ∧
        kzx ≤ n + logSlack C n ∧
        kzy ≤ logSlack C n ∧
        n + kzx + kzy ≤ kz + 3 * logSlack C n := by
  obtain ⟨A, hAchieved⟩ :=
    theorem_225_common_information_lower_envelope_achieved V hV
  obtain ⟨B, hConditional⟩ :=
    theorem_225_conditional_values_close V hV A
  obtain ⟨cTransport, hTransport⟩ :=
    shortest_representation_transport V hV
  obtain ⟨C, hFold⟩ :=
    exercise_308_sharp_slack_folding A B cTransport
  refine ⟨C, ?_⟩
  intro n
  obtain ⟨x, y, kx, ky, kxy, hx, hy, hxy,
      hxClose, hyClose, hxyClose, hLower, hUpper⟩ := hAchieved n
  obtain ⟨kyx, hkyx⟩ :=
    exists_plainConditionalComplexityValue V hV y x
  obtain ⟨kxyCond, hkxyCond⟩ :=
    exists_plainConditionalComplexityValue V hV x y
  have hkyxClose :=
    (hConditional n x y kx ky kxy kxyCond kyx
      hx hy hxy hkxyCond hkyx hxClose hyClose hxyClose).2
  obtain ⟨z, kz, kzx, kzy, hz, hzx, hzy,
      hzClose, hzxBound, hzyBound⟩ :=
    hTransport x y ky kyx hy hkyx
  obtain ⟨hAC, hkzClose, hkzxBound, hkzyBound, hGap⟩ :=
    hFold n ky kyx kz kzx kzy hyClose hkyxClose hzClose hzxBound hzyBound
  have hSlack : logSlack A n ≤ logSlack C n :=
    logSlack_mono_left hAC n
  refine ⟨x, y, z, kx, ky, kxy, kz, kzx, kzy,
    hx, hy, hxy, hxClose.mono hSlack, hyClose.mono hSlack,
    hxyClose.mono hSlack, ?_, ?_, hz, hzx, hzy,
    hkzClose, hkzxBound, hkzyBound, hGap⟩
  · intro t ht
    exact commonInformationRegion_upward_closed
      (by simp only [commonInformationTripleInflate]; omega)
      (by simp only [commonInformationTripleInflate]; omega)
      (by simp only [commonInformationTripleInflate]; omega)
      (hLower t ht)
  · intro t ht
    have h := hUpper t ht
    exact commonInformationLowerEnvelope_upward_closed n h
      (by simp only [commonInformationTripleInflate]; omega)
      (by simp only [commonInformationTripleInflate]; omega)
      (by simp only [commonInformationTripleInflate]; omega)

end Kolmogorov
