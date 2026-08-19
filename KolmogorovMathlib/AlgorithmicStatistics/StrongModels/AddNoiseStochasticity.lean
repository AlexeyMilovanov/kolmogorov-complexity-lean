import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.BudgetedStochasticity
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.ProfileBridges
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.FullCube
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.RemAddNoise
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.PlainPairSymmetry
import KolmogorovMathlib.Prefix.TwoStage
import KolmogorovMathlib.AlgorithmicStatistics.BoundedComplexityLists.NonStochasticRevisited

namespace Kolmogorov

open Nat

theorem isStochastic_fullCube_length (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : Nat, ∀ x : BitString, IsStochastic U x (logSlack c x.length) x.length := by
  obtain ⟨cS, hcS⟩ := isStochastic_of_inDescriptionProfile U hU
  obtain ⟨cF, hcF⟩ := fullSetComplexityGate U hU
  refine ⟨cS + cF, fun x => ?_⟩
  have h_ne : (stringsOfLength x.length).Nonempty := ⟨x, (memStringsOfLength x.length x).mpr rfl⟩
  have h_prof : InDescriptionProfile U x (logSlack cF x.length) x.length := by
    refine ⟨stringsOfLength x.length, h_ne, (memStringsOfLength x.length x).mpr rfl,
      hcF x.length h_ne, ?_⟩
    rw [cardStringsOfLength]
  have h_stoch := hcS x (logSlack cF x.length) x.length h_prof
  apply isStochastic_mono ?_ ?_ h_stoch
  · unfold logSlack
    rw [Nat.add_mul]
    omega
  · rfl

theorem isStochastic_beta_le_length (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : Nat, ∀ (x : BitString) (alpha beta : Nat),
      IsStochastic U x alpha beta →
      IsStochastic U x (alpha + logSlack c x.length)
        (min beta (x.length + logSlack c x.length)) := by
  obtain ⟨c, hc⟩ := isStochastic_fullCube_length U hU
  refine ⟨c, fun x alpha beta h => ?_⟩
  rcases le_or_gt beta (x.length + logSlack c x.length) with hle | hgt
  · rw [Nat.min_eq_left hle]
    exact isStochastic_mono (Nat.le_add_right alpha _) le_rfl h
  · rw [Nat.min_eq_right hgt.le]
    have h_cube := hc x
    exact isStochastic_mono (Nat.le_add_left _ _) (Nat.le_add_right _ _) h_cube

/-- **The sharp plain-profile ⇒ stochasticity conversion.**
An ordinary plain `(i,j)`-description of `z` whose two-part *sum* obeys
`i + j ≤ C(z) + β` witnesses `(i + O(log N), β + O(log N))`-stochasticity of `z`.

The randomness parameter is the two-part sum budget `β`, **not** the
log-cardinality `j` (which is what `isStochastic_of_inDescriptionProfile` /
`isStochastic_pair_of_addNoisePlainProfile` produce, and which is far too lossy
for the add-noise transport).  The proof bridges the plain description to a
prefix description (`inDescriptionProfile_of_inPlainDescriptionProfile`),
converts the exact plain complexity `C(z)` to prefix complexity
(`plainK_le_KPPlain`), applies the sharp two-part optimality-deficiency bound
`setOptimalityDeficiencyLe_of_profile`, and finally passes through
`randomness_optimality` and `isStochastic_of_model`. -/
theorem isStochastic_of_plainProfile_twoPartSum
    (V U : Map) (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U) :
    ∃ c : Nat, ∀ (z : BitString) (N kz i j beta : Nat),
      i ≤ N → j ≤ N → beta ≤ N → kz ≤ N →
      plainK V z = (kz : ENat) →
      InPlainDescriptionProfile V z i j →
      i + j ≤ kz + beta →
      IsStochastic U z (i + logSlack c N) (beta + logSlack c N) := by
  obtain ⟨cB, hB⟩ := inDescriptionProfile_of_inPlainDescriptionProfile V U hV hU
  obtain ⟨cP, hP⟩ := plainK_le_KPPlain V U hV hU.isPrefixDecompressor
  obtain ⟨cR, hR⟩ := randomness_optimality U hU
  refine ⟨cB + cP + cR, fun z N kz i j beta hi _hj _hbeta _hkzN hkz hprof hsum => ?_⟩
  -- Bridge the plain profile to a prefix `(i + logSlack cB i, j)`-description.
  obtain ⟨A, hA, hzA, hcompA, hcardA⟩ := hB z i j hprof
  -- Convert `C(z) = kz` (plain) to a lower bound on the prefix complexity `KPPlain U z`.
  have hkzP : (kz : ENat) ≤ KPPlain U z + (cP : ENat) := by
    have h := hP z; rwa [hkz] at h
  -- The sharp two-part-sum arithmetic feeding `setOptimalityDeficiencyLe_of_profile`.
  have hnat : i + logSlack cB i + j ≤ kz + beta + logSlack cB i := by omega
  have h_arith : (↑(i + logSlack cB i) : ENat) + (j : ENat)
      ≤ KPPlain U z + ((beta + cP + logSlack cB i : Nat) : ENat) := by
    calc (↑(i + logSlack cB i) : ENat) + (j : ENat)
        = ((i + logSlack cB i + j : Nat) : ENat) := by push_cast; ring
      _ ≤ ((kz + beta + logSlack cB i : Nat) : ENat) := by exact_mod_cast hnat
      _ = (kz : ENat) + ((beta + logSlack cB i : Nat) : ENat) := by push_cast; ring
      _ ≤ (KPPlain U z + (cP : ENat)) + ((beta + logSlack cB i : Nat) : ENat) := by
          gcongr
      _ = KPPlain U z + ((beta + cP + logSlack cB i : Nat) : ENat) := by push_cast; abel
  have hopt : OptimalityDeficiencyLe U (codedUniformOn A hA) z
      (beta + cP + logSlack cB i) :=
    setOptimalityDeficiencyLe_of_profile hzA hcompA hcardA h_arith
  have hdef := hR (codedUniformOn A hA) z (beta + cP + logSlack cB i) hopt
  have hstoch : IsStochastic U z (i + logSlack cB i)
      (beta + cP + logSlack cB i + cR) :=
    isStochastic_of_model U z (codedUniformOn A hA) (i + logSlack cB i)
      (beta + cP + logSlack cB i + cR) (codedUniformOn_isProbability A hA)
      (by simpa [setComplexity, CodedFiniteDistribution.complexity] using hcompA) hdef
  refine isStochastic_mono ?_ ?_ hstoch
  · -- `i + logSlack cB i ≤ i + logSlack (cB+cP+cR) N`.
    have h1 : logSlack cB i ≤ logSlack (cB + cP + cR) N :=
      (logSlack_mono_right cB hi).trans (logSlack_mono_left (by omega) N)
    omega
  · -- `beta + cP + logSlack cB i + cR ≤ beta + logSlack (cB+cP+cR) N`.
    have hle : logSlack cB i ≤ logSlack cB N := logSlack_mono_right cB hi
    have hroom : logSlack cB N + (cP + cR) ≤ logSlack (cB + cP + cR) N := by
      have h := logSlack_add_const_le cB (cP + cR) N
      rw [Nat.add_assoc cB cP cR]
      exact h
    omega

/-- Pure arithmetic absorption of slack constants for `prop_add_noise`. -/
theorem stochasticity_slack_absorption (cBeta cC cE cP cS cLen : Nat) :
    ∃ C : Nat, ∀ (x y e : Nat),
      let baseBudget := x + logSlack (cLen + cBeta) x
      let beta2_bound :=
        e + logSlack cP (x + y) + baseBudget + logSlack cC baseBudget +
          logSlack cE y
      let kxy_bound := 2 * x + y + 1 + cLen
      let N_bound := kxy_bound + beta2_bound
      e + logSlack cBeta x + logSlack cC baseBudget + logSlack cE y +
        logSlack cP (x + y) + logSlack cS N_bound
      ≤ C * e + logSlack C x + logSlack C y := by
  let a := cLen + cBeta
  obtain ⟨cBase, hBase⟩ := logSlack_linear_bound cC (a + 1) a
  let A := 3 + cP + cE + (cC + 1) * (a + 1)
  let B := 1 + cLen + cP + (cC + 1) * a + cC + cE
  obtain ⟨cN, hN⟩ := logSlack_linear_bound cS A B
  let cx := cBeta + cBase + cP + cN
  let cy := cE + cP + cN
  let C := cx + cy + cN + 1
  refine ⟨C, fun x y e => ?_⟩
  dsimp only
  set baseBudget := x + logSlack (cLen + cBeta) x with hbase
  set beta2Bound :=
    e + logSlack cP (x + y) + baseBudget + logSlack cC baseBudget + logSlack cE y
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
    rw [hn, hbeta]
    let D := (a + 1) * x + a
    let xCoeff := 2 + cP + (cC + 1) * (a + 1)
    let yCoeff := 1 + cP + cE
    have hPLog : logSlack cP (x + y) ≤ cP * (x + y) + cP := by
      unfold logSlack
      exact Nat.add_le_add_right
        (Nat.mul_le_mul_left cP (length_natBits_le_self (x + y))) cP
    have hCLog : logSlack cC baseBudget ≤ cC * baseBudget + cC := by
      unfold logSlack
      exact Nat.add_le_add_right
        (Nat.mul_le_mul_left cC (length_natBits_le_self baseBudget)) cC
    have hELog : logSlack cE y ≤ cE * y + cE := by
      unfold logSlack
      exact Nat.add_le_add_right
        (Nat.mul_le_mul_left cE (length_natBits_le_self y)) cE
    have hbaseD : baseBudget ≤ D := hbaseLinear
    have hCbaseD : cC * baseBudget ≤ cC * D :=
      Nat.mul_le_mul_left cC hbaseD
    have hxCoeff : xCoeff ≤ A := by
      dsimp [xCoeff, A]
      omega
    have hyCoeff : yCoeff ≤ A := by
      dsimp [yCoeff, A]
      omega
    have hOneA : 1 ≤ A := by
      dsimp [A]
      omega
    calc
      2 * x + y + 1 + cLen +
            (e + logSlack cP (x + y) + baseBudget + logSlack cC baseBudget +
              logSlack cE y)
          ≤ 2 * x + y + 1 + cLen +
            (e + (cP * (x + y) + cP) + baseBudget + (cC * baseBudget + cC) +
              (cE * y + cE)) := by
                gcongr
      _ ≤ 2 * x + y + 1 + cLen +
            (e + (cP * (x + y) + cP) + D + (cC * D + cC) +
              (cE * y + cE)) := by
                gcongr
      _ = xCoeff * x + yCoeff * y + e + B := by
            dsimp [D, xCoeff, yCoeff, B]
            ring
      _ ≤ A * x + A * y + A * e + B := by
            gcongr
            simpa using Nat.mul_le_mul_right e hOneA
      _ = A * (x + y + e) + B := by ring
  have hnSlack : logSlack cS nBound ≤ logSlack cN (x + y + e) := by
    exact (logSlack_mono_right cS hnLinear).trans (hN (x + y + e))
  have hPsplit : logSlack cP (x + y) ≤ logSlack cP x + logSlack cP y :=
    logSlack_add_le cP x y
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
      e + logSlack cBeta x + logSlack cC baseBudget + logSlack cE y +
          logSlack cP (x + y) + logSlack cS nBound ≤
        e + (logSlack cBeta x + logSlack cBase x + logSlack cP x + logSlack cN x) +
          (logSlack cE y + logSlack cP y + logSlack cN y) + logSlack cN e := by
    omega
  refine hlogs.trans ?_
  unfold logSlack
  dsimp [C, cx, cy]
  nlinarith [length_natBits_le_self e]

/-- A helper to extract exactly the natural number plain complexity. -/
theorem exists_plainK_eq_nat (V : Map) (hV : isOptimalConditional V) (z : BitString) :
    ∃ k : Nat, plainK V z = (k : ENat) := by
  obtain ⟨c, hc⟩ := plainKLeLength V hV
  have h := hc z
  cases hz : plainK V z with
  | top =>
    rw [hz] at h
    exact False.elim (ENat.coe_ne_top _ (top_le_iff.mp h))
  | coe k => exact ⟨k, rfl⟩

/-- **The add-noise pair corner.**
The forward direction of `prop_add_noise` bounding the stochasticity
profile of `(x, y)` when `y` is conditionally random given `x`. -/
theorem stochasticity_pair_of_plain_random_noise
    (V U : Map) (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U) :
    ∃ c : Nat, ∀ (x y : BitString) (epsilon alpha beta : Nat),
      (y.length : ENat) ≤ condK V y x + (epsilon : ENat) →
      IsStochastic U x alpha beta →
      IsStochastic U (pairCode x y)
        (alpha + (c * epsilon + logSlack c x.length + logSlack c y.length))
        (beta + (c * epsilon + logSlack c x.length + logSlack c y.length)) := by
  obtain ⟨cBeta, hBeta⟩ := isStochastic_beta_le_length U hU
  obtain ⟨cC, hC⟩ := budgeted_stochasticity_to_plain_corner_of_length_le V U hV hU
  obtain ⟨cE, hE⟩ := inPlainDescriptionProfile_pair_of_base V hV
  obtain ⟨cP, hP⟩ := plainK_pair_ge_plainK_add_length_of_random V U hV hU
  obtain ⟨cS, hS⟩ := isStochastic_of_plainProfile_twoPartSum V U hV hU
  obtain ⟨cLen, hLen⟩ := plainKLeLength V hV
  obtain ⟨C, hC_abs⟩ := stochasticity_slack_absorption cBeta cC cE cP cS cLen
  refine ⟨C, fun x y epsilon alpha beta h_eps h_stoch => ?_⟩
  set beta1 := min beta (x.length + logSlack cBeta x.length) with hbeta1
  have h_stoch1 := hBeta x alpha beta h_stoch
  set baseBudget := x.length + logSlack (cLen + cBeta) x.length with hbaseBudget
  obtain ⟨kx, hkx⟩ := exists_plainK_eq_nat V hV x
  have hkx_le : kx ≤ baseBudget := by
    have h := hLen x
    rw [hkx] at h
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
  obtain ⟨i, j, hprof, hi, hij⟩ :=
    hC x kx baseBudget (alpha + logSlack cBeta x.length) beta1 hkx hkx_le
      h_xlen_le h_beta1_le h_stoch1
  obtain ⟨kxy, hkxy⟩ := exists_plainK_eq_nat V hV (pairCode x y)
  have h_prof_pair := hE x y i j hprof
  set i2 := i + logSlack cE y.length with hi2
  set j2 := j + y.length with hj2
  have h_plain_symm := hP x y epsilon kx kxy hkx hkxy h_eps
  set beta2 :=
    epsilon + logSlack cP (x.length + y.length) + beta1 +
      logSlack cC baseBudget + logSlack cE y.length
    with hbeta2
  set N := kxy + beta2 with hN
  have hi2_j2 : i2 + j2 ≤ kxy + beta2 := by omega
  have hi2_N : i2 ≤ N := by omega
  have hj2_N : j2 ≤ N := by omega
  have hbeta2_N : beta2 ≤ N := by omega
  have hkxy_N : kxy ≤ N := by omega
  have h_stoch2 :=
    hS (pairCode x y) N kxy i2 j2 beta2 hi2_N hj2_N hbeta2_N hkxy_N hkxy
      h_prof_pair hi2_j2
  have h_abs := hC_abs x.length y.length epsilon
  have hkxy_bound : kxy ≤ 2 * x.length + y.length + 1 + cLen := by
    have h := hLen (pairCode x y)
    rw [hkxy] at h
    have h_prog_xy : programLength (pairCode x y) = (pairCode x y).length := rfl
    rw [h_prog_xy] at h
    have h' : kxy ≤ (pairCode x y).length + cLen := by exact_mod_cast h
    have h_len := length_pairCode x y
    omega
  set beta2_bound :=
    epsilon + logSlack cP (x.length + y.length) + baseBudget +
      logSlack cC baseBudget + logSlack cE y.length
    with hbeta2_bound
  have h_beta2_le : beta2 ≤ beta2_bound := by
    have : beta1 ≤ baseBudget := h_beta1_le
    omega
  set N_bound := (2 * x.length + y.length + 1 + cLen) + beta2_bound with hN_bound
  have hN_le : N ≤ N_bound := by omega
  have hS_mono : logSlack cS N ≤ logSlack cS N_bound := logSlack_mono_right cS hN_le
  apply isStochastic_mono _ _ h_stoch2
  · have hi_le :
        i ≤ alpha + logSlack cBeta x.length + logSlack cC baseBudget := hi
    have h2 :
        epsilon + logSlack cBeta x.length + logSlack cC baseBudget +
            logSlack cE y.length + logSlack cP (x.length + y.length) +
            logSlack cS N_bound ≤
          C * epsilon + logSlack C x.length + logSlack C y.length := h_abs
    omega
  · have hbeta1_le : beta1 ≤ beta := min_le_left _ _
    have h2 :
        epsilon + logSlack cBeta x.length + logSlack cC baseBudget +
            logSlack cE y.length + logSlack cP (x.length + y.length) +
            logSlack cS N_bound ≤
          C * epsilon + logSlack C x.length + logSlack C y.length := h_abs
    omega

/-- Every stochasticity-profile point has a representative whose two coordinates
are bounded by the string length up to logarithmic slack. -/
theorem stochasticity_has_length_bounded_representative
    (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c, ∀ x n alpha beta,
      x.length = n →
      IsStochastic U x alpha beta →
      ∃ alpha' beta',
        IsStochastic U x alpha' beta' ∧
        alpha' ≤ alpha + logSlack c n ∧
        beta' ≤ beta + logSlack c n ∧
        alpha' ≤ n + logSlack c n ∧
        beta' ≤ n + logSlack c n := by
  obtain ⟨c1, hc1⟩ := isStochastic_beta_le_length U hU
  obtain ⟨c2, hc2⟩ := isStochastic_singleton_length U hU
  let c := max c1 c2
  refine ⟨c, fun x n alpha beta hn h_stoch => ?_⟩
  set alpha1 := alpha + logSlack c1 n
  set beta1 := min beta (n + logSlack c1 n)
  have h_stoch1 : IsStochastic U x alpha1 beta1 := by
    have h := hc1 x alpha beta h_stoch
    rwa [hn] at h
  set alpha' := min alpha1 (n + logSlack c2 n)
  set beta' := beta1
  refine ⟨alpha', beta', ?_, ?_, ?_, ?_, ?_⟩
  · change IsStochastic U x (min alpha1 (n + logSlack c2 n)) beta1
    rcases le_or_gt alpha1 (n + logSlack c2 n) with hle | hgt
    · rw [Nat.min_eq_left hle]
      exact h_stoch1
    · rw [Nat.min_eq_right hgt.le]
      have h2 := hc2 x n hn
      exact isStochastic_mono le_rfl (by omega) h2
  · have h_slack : logSlack c1 n ≤ logSlack c n := logSlack_mono_left (le_max_left c1 c2) n
    omega
  · have h_slack : logSlack c1 n ≤ logSlack c n := logSlack_mono_left (le_max_left c1 c2) n
    omega
  · have h_slack : logSlack c2 n ≤ logSlack c n := logSlack_mono_left (le_max_right c1 c2) n
    omega
  · have h_slack : logSlack c1 n ≤ logSlack c n := logSlack_mono_left (le_max_left c1 c2) n
    omega

end Kolmogorov
