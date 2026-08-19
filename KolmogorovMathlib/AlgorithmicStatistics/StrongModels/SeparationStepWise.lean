import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.SeparationWitness
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.StepWisePlain
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.SeparationCylinderTotal
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.TotalReduction

/-!
# S7: the step-wise `KT(B | y)` upper bound

For the separation witness `x = y ++ z` (with `|y| = |z| = 2k`, `n = 4k`) whose
plain profile `P_x` is `O(log n)`-close to the Figure-4 gray region, let `B` be a
standard block whose public four-way maximum is `M` (so `B` is an `M`-strong set
model for `x` and its parameters `(C(B), log #B)` are `L∞`-within `M` of the
corner `(k, 2k)`).  This file assembles `thm_step_wise` (applied to `B` as the
minimal/strong statistic and the natural cylinder `A = cylinder n y` as the
second sufficient statistic) with the proved total equivalence between the
cylinder code and `y`, obtaining `KT(B | y) ≤ O(M) + O(log n)`.

The main theorem is proved in full from three Figure-4 geometric inputs — that
`B` and the cylinder are sufficient statistics, and that `B` is minimal — all
proved below.  The `thm_step_wise` application, the composition through the
cylinder equivalence, and all constant bookkeeping (including the closing
estimate, which uses `M ≤ n` derived from the budget) are handled here.
-/

namespace Kolmogorov

lemma plainK_lower_of_separationGrayProfile_neighborhood
    (V : Map) (hV : isOptimalConditional V) :
    ∃ cLower : Nat, ∀ (n k cSlack : Nat) (x : BitString),
      ProfileSetsWithinNeighborhood (plainDescriptionProfileSet V x)
        (separationGrayProfile k) (logSlack cSlack n) →
      (3 * k : ENat) ≤
        plainK V x + (logSlack (2 * cSlack + cLower) n : ENat) := by
  obtain ⟨cSingleton, hSingleton⟩ :=
    plainSetComplexity_singleton_le_plainK V hV
  refine ⟨cSingleton + 1, ?_⟩
  intro n k cSlack x hProf
  have hxFinite : plainK V x ≠ ⊤ :=
    condK_ne_top_of_optimal V hV x []
  set kx := (plainK V x).toNat with hkxDef
  have hkx : plainK V x = (kx : ENat) :=
    (ENat.natCast_toNat hxFinite).symm
  have hSingletonPoint :
      (kx + cSingleton, 0) ∈ plainDescriptionProfileSet V x := by
    refine ⟨{x}, Finset.singleton_nonempty x, ?_⟩
    refine ⟨Finset.mem_singleton_self x, ?_, by simp⟩
    calc
      plainSetComplexity V {x} (Finset.singleton_nonempty x)
          ≤ plainK V x + (cSingleton : ENat) := hSingleton x
      _ = ((kx + cSingleton : Nat) : ENat) := by
        rw [hkx]
        norm_cast
  obtain ⟨q, hqGray, hqDist⟩ :=
    hProf.1 (kx + cSingleton, 0) hSingletonPoint
  have hFirstDist :
      ((kx + cSingleton - q.1) + (q.1 - (kx + cSingleton))) ≤
        logSlack cSlack n :=
    (Nat.le_max_left _ _).trans hqDist
  have hSecondDist :
      ((0 - q.2) + (q.2 - 0)) ≤ logSlack cSlack n :=
    (Nat.le_max_right _ _).trans hqDist
  have hqFirst : q.1 ≤ kx + cSingleton + logSlack cSlack n := by
    omega
  have hqSecond : q.2 ≤ logSlack cSlack n := by
    omega
  have hqSum : 3 * k ≤ q.1 + q.2 := by
    rcases hqGray with hqGray | hqGray <;> omega
  have hNat :
      3 * k ≤ kx + logSlack (2 * cSlack + (cSingleton + 1)) n := by
    unfold logSlack at *
    nlinarith [Nat.zero_le ((Nat.bits n).length)]
  rw [hkx]
  exact_mod_cast hNat

/-- **Geometric leaf (sufficiency of the standard block).**  If `x ∈ B`, the
plain profile of `x` is within `logSlack cSlack n` of the gray region, and the
parameters `(C(B), log #B)` are `L∞`-within `M` of `(k, 2k)`, then `B` is a
`(2M + O(log n))`-sufficient statistic for `x`.  The factor `2` on both `M` and
the neighborhood radius is genuine: both coordinates contribute to the
two-part sum.  The `x ∈ B` hypothesis is required: it is the
`x ∈ S` conjunct of `IsSufficientStatistic` and is not implied by closeness. -/
lemma separationGrayProfile_sufficiency_of_near_target
    (V : Map) (hV : isOptimalConditional V) :
    ∃ cSuff : Nat, ∀ (n k M cSlack : Nat) (x : BitString)
      (B : Finset BitString) (hB : B.Nonempty),
      x ∈ B →
      x.length = n →
      ProfileSetsWithinNeighborhood (plainDescriptionProfileSet V x)
        (separationGrayProfile k) (logSlack cSlack n) →
      natPairLInfDistance ((plainSetComplexity V B hB).toNat, finiteSetLogCard B)
        (k, 2 * k) ≤ M →
      IsSufficientStatistic V x B hB
        (2 * M + logSlack (2 * cSlack + cSuff) n) := by
  obtain ⟨cLower, hLower⟩ :=
    plainK_lower_of_separationGrayProfile_neighborhood V hV
  refine ⟨cLower, ?_⟩
  intro n k M cSlack x B hB hxB _hxLength hProf hDist
  have hBFinite : plainSetComplexity V B hB ≠ ⊤ :=
    condK_ne_top_of_optimal V hV (codedUniformOn B hB).code []
  set a := (plainSetComplexity V B hB).toNat with haDef
  have ha : plainSetComplexity V B hB = (a : ENat) :=
    (ENat.natCast_toNat hBFinite).symm
  have hFirstDist :
      ((a - k) + (k - a)) ≤ M :=
    (Nat.le_max_left _ _).trans hDist
  have hSecondDist :
      ((finiteSetLogCard B - 2 * k) +
          (2 * k - finiteSetLogCard B)) ≤ M :=
    (Nat.le_max_right _ _).trans hDist
  have haUpper : a ≤ k + M := by omega
  have hCardUpper : finiteSetLogCard B ≤ 2 * k + M := by omega
  have hxFinite : plainK V x ≠ ⊤ :=
    condK_ne_top_of_optimal V hV x []
  set kx := (plainK V x).toNat with hkxDef
  have hkx : plainK V x = (kx : ENat) :=
    (ENat.natCast_toNat hxFinite).symm
  have hLower' := hLower n k cSlack x hProf
  rw [hkx] at hLower'
  have hLowerNat :
      3 * k ≤ kx + logSlack (2 * cSlack + cLower) n := by
    exact_mod_cast hLower'
  refine ⟨hxB, ?_⟩
  rw [ha, hkx]
  exact_mod_cast (show
    a + finiteSetLogCard B ≤
      kx + (2 * M + logSlack (2 * cSlack + cLower) n) by omega)

/-- **Geometric leaf (minimality of the standard block).**  Under the same
gray-region and `L∞`-closeness hypotheses (and `x ∈ B`), if the total budget is
below `k`, then `B` is `(2M + O(log n), kappa)`-minimal: no competitor of
complexity smaller by `2M + O(log n)` can keep its optimality deficiency within
`kappa`, because the gray region forbids sufficient models of complexity below
`k`. -/
lemma separationGrayProfile_minimality_of_near_target
    (V : Map) (hV : isOptimalConditional V) :
    ∃ cMin : Nat, ∀ (n k M cSlack kappa : Nat) (x : BitString)
      (B : Finset BitString) (hB : B.Nonempty),
      x ∈ B →
      x.length = n →
      ProfileSetsWithinNeighborhood (plainDescriptionProfileSet V x)
        (separationGrayProfile k) (logSlack cSlack n) →
      natPairLInfDistance ((plainSetComplexity V B hB).toNat, finiteSetLogCard B)
        (k, 2 * k) ≤ M →
      2 * M + kappa + logSlack (2 * cSlack + cMin) n < k →
      IsMinimalModel V x B hB
        (2 * M + logSlack (2 * cSlack + cMin) n) kappa := by
  refine ⟨1, ?_⟩
  intro n k M cSlack kappa x B hB hxB _hxLength hProf hDist hSmall
  have hBFinite : plainSetComplexity V B hB ≠ ⊤ :=
    condK_ne_top_of_optimal V hV (codedUniformOn B hB).code []
  set a := (plainSetComplexity V B hB).toNat with haDef
  have ha : plainSetComplexity V B hB = (a : ENat) :=
    (ENat.natCast_toNat hBFinite).symm
  have hFirstDist : ((a - k) + (k - a)) ≤ M :=
    (Nat.le_max_left _ _).trans hDist
  have hSecondDist :
      ((finiteSetLogCard B - 2 * k) +
          (2 * k - finiteSetLogCard B)) ≤ M :=
    (Nat.le_max_right _ _).trans hDist
  have haUpper : a ≤ k + M := by omega
  have hCardUpper : finiteSetLogCard B ≤ 2 * k + M := by omega
  refine ⟨hxB, ?_⟩
  intro D hD hxD hTwoPart hComplexityGap
  have hDFinite : plainSetComplexity V D hD ≠ ⊤ :=
    condK_ne_top_of_optimal V hV (codedUniformOn D hD).code []
  set d := (plainSetComplexity V D hD).toNat with hdDef
  have hd : plainSetComplexity V D hD = (d : ENat) :=
    (ENat.natCast_toNat hDFinite).symm
  have hTwoPartNat :
      d + finiteSetLogCard D ≤ a + finiteSetLogCard B + kappa := by
    rw [hd, ha] at hTwoPart
    exact_mod_cast hTwoPart
  have hComplexityGapNat :
      d + (2 * M + logSlack (2 * cSlack + 1) n) ≤ a := by
    rw [hd, ha] at hComplexityGap
    exact_mod_cast hComplexityGap
  have hDPoint :
      (d, finiteSetLogCard D) ∈ plainDescriptionProfileSet V x := by
    refine ⟨D, hD, hxD, le_of_eq hd, finiteSetLogCard_spec D⟩
  obtain ⟨q, hqGray, hqDist⟩ :=
    hProf.1 (d, finiteSetLogCard D) hDPoint
  have hqFirstDist :
      ((d - q.1) + (q.1 - d)) ≤ logSlack cSlack n :=
    (Nat.le_max_left _ _).trans hqDist
  have hqSecondDist :
      ((finiteSetLogCard D - q.2) +
          (q.2 - finiteSetLogCard D)) ≤ logSlack cSlack n :=
    (Nat.le_max_right _ _).trans hqDist
  have hSlackStrict :
      logSlack cSlack n < logSlack (2 * cSlack + 1) n := by
    unfold logSlack
    nlinarith [Nat.zero_le ((Nat.bits n).length)]
  have hqFirst : q.1 < k := by omega
  have hqSum : 4 * k ≤ q.1 + q.2 :=
    (separationGrayProfile_left_iff hqFirst).mp hqGray
  have hqSumUpper :
      q.1 + q.2 ≤
        d + finiteSetLogCard D + 2 * logSlack cSlack n := by
    omega
  have hSlackDouble :
      2 * logSlack cSlack n ≤ logSlack (2 * cSlack + 1) n := by
    unfold logSlack
    nlinarith [Nat.zero_le ((Nat.bits n).length)]
  omega

/-- **Geometric leaf (sufficiency of the natural cylinder).**  The natural
cylinder `A = cylinder n y` witnessing the corner `(k, 2k)` is an
`O(log n)`-sufficient statistic for `x = y ++ z`.  Its complexity is `k ± O(log
n)` (hypotheses `hLow`, `hUp`) and its log-cardinality is `2k`, matching
`C(x) ≈ 3k`; no `M` term is needed.  Membership `x ∈ cylinder n y` follows from
`x = y ++ z` and the lengths, so it is not a separate hypothesis. -/
lemma cylinder_isSufficientStatistic_at_witness
    (V : Map) (hV : isOptimalConditional V) :
    ∃ cSuff : Nat, ∀ (n k cSlack : Nat) (x y z : BitString)
      (hA : (cylinder n y).Nonempty),
      y.length = 2 * k →
      z.length = 2 * k →
      x = y ++ z →
      n = 4 * k →
      ProfileSetsWithinNeighborhood (plainDescriptionProfileSet V x)
        (separationGrayProfile k) (logSlack cSlack n) →
      (k : ENat) ≤ plainSetComplexity V (cylinder n y) hA + (logSlack cSlack n : ENat) →
      plainSetComplexity V (cylinder n y) hA ≤ (k + logSlack cSlack n : ENat) →
      IsSufficientStatistic V x (cylinder n y) hA
        (logSlack (3 * cSlack + cSuff) n) := by
  obtain ⟨cLower, hLower⟩ :=
    plainK_lower_of_separationGrayProfile_neighborhood V hV
  refine ⟨cLower, ?_⟩
  intro n k cSlack x y z hA hy hz hx hn hProf _hLow hUp
  have hxA : x ∈ cylinder n y := by
    rw [hx, mem_cylinder]
    constructor
    · rw [List.length_append, hy, hz, hn]
      omega
    · exact List.prefix_append y z
  have hyLe : y.length ≤ n := by rw [hy, hn]; omega
  have hCard : finiteSetLogCard (cylinder n y) = 2 * k := by
    unfold finiteSetLogCard
    rw [cylinder_card n y hyLe, hy]
    have hSub : n - 2 * k = 2 * k := by omega
    rw [hSub]
    simp
  have hLower' := hLower n k cSlack x hProf
  have hSlackEq :
      logSlack (2 * cSlack + cLower) n + logSlack cSlack n =
        logSlack (3 * cSlack + cLower) n := by
    rw [logSlack_add_const]
    congr 1
    omega
  refine ⟨hxA, ?_⟩
  rw [hCard]
  calc
    plainSetComplexity V (cylinder n y) hA + ((2 * k : Nat) : ENat)
        ≤ ((k : Nat) : ENat) + (logSlack cSlack n : ENat) +
            ((2 * k : Nat) : ENat) := by
          gcongr
    _ = 3 * (k : ENat) + (logSlack cSlack n : ENat) := by
          push_cast; ring
    _ ≤ (plainK V x + (logSlack (2 * cSlack + cLower) n : ENat)) +
          (logSlack cSlack n : ENat) := by
          gcongr
    _ = plainK V x + (logSlack (3 * cSlack + cLower) n : ENat) := by
          rw [add_assoc]
          congr 1
          exact_mod_cast hSlackEq

/-- Assuming the witness geometry, if the standard block
`B` has small four-way maximum `M` (it is `M`-strong for `x`, its parameters are
`L∞`-within `M` of `(k, 2k)`, and `cTot * M + O(log n) < k`), then the total
conditional complexity of `B` given the head `y` is `O(M) + O(log n)`.

The proof instantiates `thm_step_wise` with `B` as the minimal, strong,
sufficient statistic and the natural cylinder `A = cylinder n y` as the second
sufficient statistic, yielding `KT(B | A)`, and composes it with the proved
total equivalence between the cylinder code and `y`.  `lemma_4` is not used. -/
lemma separation_standardBlock_totalCondK_y_le
    (V T : Map) (hV : isOptimalConditional V) (hT : IsOptimalTotalConditional T) :
    ∃ cTot cSlk : Nat, ∀ (n k M cSlack : Nat) (x y z : BitString)
      (B : Finset BitString) (hB : B.Nonempty) (hA : (cylinder n y).Nonempty),
      x ∈ B →
      y.length = 2 * k →
      z.length = 2 * k →
      x = y ++ z →
      n = 4 * k →
      ProfileSetsWithinNeighborhood (plainDescriptionProfileSet V x)
        (separationGrayProfile k) (logSlack cSlack n) →
      natPairLInfDistance ((plainSetComplexity V B hB).toNat, finiteSetLogCard B)
        (k, 2 * k) ≤ M →
      totalCondK T (codedUniformOn B hB).code x ≤ (M : ENat) →
      (k : ENat) ≤ plainSetComplexity V (cylinder n y) hA + (logSlack cSlack n : ENat) →
      plainSetComplexity V (cylinder n y) hA ≤ (k + logSlack cSlack n : ENat) →
      cTot * M + logSlack (cTot * cSlack + cSlk) n < k →
      totalCondK T (codedUniformOn B hB).code y ≤
        (cTot * M + logSlack (cTot * cSlack + cSlk) n : ENat) := by
  obtain ⟨cSuffCyl, hSuffCyl⟩ := cylinder_isSufficientStatistic_at_witness V hV
  obtain ⟨cSuffB, hSuffB⟩ := separationGrayProfile_sufficiency_of_near_target V hV
  obtain ⟨cMin, hMin⟩ := separationGrayProfile_minimality_of_near_target V hV
  obtain ⟨cKappa, cPlain, cTotal, hStepWise⟩ := thm_step_wise V T hV hT
  obtain ⟨cEq, hEq⟩ := separationCylinder_totalEquivalent_prefix T hT
  obtain ⟨cTrans, hTrans⟩ := TotalReducesWithin.trans_logSlack T hT
  -- The composition slack `logSlack cTrans _` is bounded by its argument plus a
  -- fixed constant `b_trans`; folding `b_trans` into the output constants makes
  -- the closing estimate a matter of `logSlack` merging alone.
  obtain ⟨b_trans, hb_trans⟩ := logSlack_le_add_const cTrans
  set base := cSuffCyl + cSuffB + cMin + cKappa + cEq + cTrans + cTotal + b_trans with hbase
  refine ⟨16 * base + 16,
    2 * cEq + 2 * cTotal * (cSuffCyl + cSuffB + 1) + 2 * cTotal * cMin + 2 * cTotal
      + b_trans + base + 200, ?_⟩
  intro n k M cSlack x y z B hB hA hxB hy hz hx hn hProf hDist hStrong hLow hUp hBudget
  set cTot := 16 * base + 16 with hcTot
  set cSlk := 2 * cEq + 2 * cTotal * (cSuffCyl + cSuffB + 1) + 2 * cTotal * cMin + 2 * cTotal
    + b_trans + base + 200 with hcSlk
  -- Lower bounds on the output constants (all linear once `cTotal ≤ base`).
  have hbase_ct : cTotal ≤ base := by rw [hbase]; omega
  have hcTot1 : 1 ≤ cTot := by rw [hcTot]; omega
  have hcTot2 : 2 ≤ cTot := by rw [hcTot]; omega
  have hcTot4n : 4 ≤ cTot := by rw [hcTot]; omega
  have hcTot8 : 8 * cTotal ≤ cTot := by rw [hcTot]; omega
  have hcTot10 : 10 * cTotal ≤ cTot := by rw [hcTot]; omega
  have hAcSlk : cSuffCyl + cSuffB + cKappa + cMin + 1 ≤ cSlk := by rw [hcSlk, hbase]; omega
  have hbracket : 2 * cEq + 2 * cTotal * (cSuffCyl + cSuffB + 1) + 2 * cTotal * cMin
      + 2 * cTotal + b_trans ≤ cSlk := by rw [hcSlk]; omega
  -- Length of the witness and the budget-derived bound `M ≤ n`.
  have hx_len : x.length = n := by rw [hx, List.length_append, hy, hz, hn]; omega
  have hk_le_n : k ≤ n := by omega
  have hcTotM_lt : cTot * M < k := lt_of_le_of_lt (Nat.le_add_right _ _) hBudget
  have hMcTot : M ≤ cTot * M := Nat.le_mul_of_pos_left M hcTot1
  have hM_le_n : M ≤ n := le_trans hMcTot (le_trans (le_of_lt hcTotM_lt) hk_le_n)
  -- The cylinder code is total-equivalent to the head `y`.
  have hyn : y.length ≤ n := by rw [hy, hn]; omega
  have hCylEq : TotalEquivalentWithin T
      (codedUniformOn (cylinder n y) hA).code y (logSlack cEq n) := hEq y n hyn
  have hYACode : TotalReducesWithin T y
      (codedUniformOn (cylinder n y) hA).code (logSlack cEq n) := hCylEq.1
  -- The common sufficiency budget and the minimality gap.
  set epsilon := 2 * M +
    logSlack (3 * cSlack + cSuffCyl + cSuffB + 1) n with hepsilon
  set delta := 2 * M + logSlack (2 * cSlack + cMin) n with hdelta
  have hB_suff : IsSufficientStatistic V x B hB epsilon := by
    apply (hSuffB n k M cSlack x B hB hxB hx_len hProf hDist).mono
    rw [hepsilon]
    exact Nat.add_le_add_left (logSlack_mono_left (by omega) n) (2 * M)
  have hA_suff : IsSufficientStatistic V x (cylinder n y) hA epsilon := by
    apply (hSuffCyl n k cSlack x y z hA hy hz hx hn hProf hLow hUp).mono
    rw [hepsilon]
    exact le_trans (logSlack_mono_left (by omega) n) (Nat.le_add_left _ _)
  have hB_strong : IsStrongSetModel T x B hB epsilon := by
    apply hStrong.trans
    exact_mod_cast (show M ≤ epsilon by rw [hepsilon]; omega)
  -- Merge the three subsidiary slacks into the budget slack.
  have hsum : logSlack (3 * cSlack + cSuffCyl + cSuffB + 1) n +
      logSlack cKappa n + logSlack (2 * cSlack + cMin) n ≤
        logSlack (cTot * cSlack + cSlk) n := by
    rw [logSlack_add_const, logSlack_add_const]
    apply logSlack_mono_left
    have hmul : 5 * cSlack ≤ cTot * cSlack :=
      Nat.mul_le_mul_right cSlack (by omega : 5 ≤ cTot)
    omega
  -- The minimality smallness hypothesis, discharged from the public budget.
  have hsmall : 2 * M + (epsilon + logSlack cKappa n) +
      logSlack (2 * cSlack + cMin) n < k := by
    have hM4 : 4 * M ≤ cTot * M := Nat.mul_le_mul_right _ hcTot4n
    have hfinal : 2 * M + (epsilon + logSlack cKappa n) +
        logSlack (2 * cSlack + cMin) n
        ≤ cTot * M + logSlack (cTot * cSlack + cSlk) n := by
      rw [hepsilon]
      calc 2 * M + (2 * M +
              logSlack (3 * cSlack + cSuffCyl + cSuffB + 1) n +
              logSlack cKappa n) + logSlack (2 * cSlack + cMin) n
          = 4 * M + (logSlack (3 * cSlack + cSuffCyl + cSuffB + 1) n +
              logSlack cKappa n + logSlack (2 * cSlack + cMin) n) := by ring
        _ ≤ cTot * M + logSlack (cTot * cSlack + cSlk) n :=
          Nat.add_le_add hM4 hsum
    exact lt_of_le_of_lt hfinal hBudget
  have hB_min : IsMinimalModel V x B hB delta (epsilon + logSlack cKappa n) :=
    hMin n k M cSlack (epsilon + logSlack cKappa n) x B hB hxB hx_len hProf hDist hsmall
  -- Apply the step-wise theorem: `KT(B | A) ≤ cTotal * (epsilon + delta) + O(log n)`.
  have hStep := (hStepWise x n B hB (cylinder n y) hA epsilon delta hx_len
    hB_suff hA_suff hB_min).2 hB_strong
  have hACodeBCode : TotalReducesWithin T
      (codedUniformOn (cylinder n y) hA).code (codedUniformOn B hB).code
      (cTotal * (epsilon + delta) + logSlack cTotal n) := hStep
  -- Compose `y →ε cylinder →δ B` and discharge the closing estimate.
  have hYBCode := hTrans hYACode hACodeBCode
  apply hYBCode.mono
  set R := logSlack cEq n + (cTotal * (epsilon + delta) + logSlack cTotal n) with hRdef
  set CR := cEq + cTotal * (3 * cSlack + cSuffCyl + cSuffB + 1) +
    cTotal * (2 * cSlack + cMin) + cTotal
    with hCRdef
  -- `R = 4 cTotal M + logSlack CR n`, the intermediate composed radius.
  have hRval : R = 4 * cTotal * M + logSlack CR n := by
    rw [hRdef, hepsilon, hdelta, hCRdef]; simp only [logSlack]; ring
  -- The slack constant `2 CR + b_trans` fits inside the budget slack.
  have hCR_le : 2 * CR + b_trans ≤ cTot * cSlack + cSlk := by
    rw [hCRdef]
    have hexpand : 2 * (cEq + cTotal * (3 * cSlack + cSuffCyl + cSuffB + 1)
          + cTotal * (2 * cSlack + cMin) + cTotal) + b_trans
        = 10 * cTotal * cSlack + (2 * cEq + 2 * cTotal * (cSuffCyl + cSuffB + 1)
          + 2 * cTotal * cMin + 2 * cTotal + b_trans) := by ring
    rw [hexpand]
    exact Nat.add_le_add (Nat.mul_le_mul_right _ hcTot10) hbracket
  have hcomp : logSlack cTrans R ≤ R + b_trans := hb_trans R
  have hbt : b_trans ≤ logSlack b_trans n := by simp only [logSlack]; omega
  have hslackmerge : logSlack CR n + logSlack CR n + logSlack b_trans n
      ≤ logSlack (cTot * cSlack + cSlk) n := by
    rw [logSlack_add_const, logSlack_add_const]
    apply logSlack_mono_left
    omega
  calc R + logSlack cTrans R
      ≤ R + (R + b_trans) := by omega
    _ = 8 * cTotal * M + (logSlack CR n + logSlack CR n + b_trans) := by rw [hRval]; ring
    _ ≤ cTot * M + (logSlack CR n + logSlack CR n + b_trans) :=
        Nat.add_le_add_right (Nat.mul_le_mul_right _ hcTot8) _
    _ ≤ cTot * M + (logSlack CR n + logSlack CR n + logSlack b_trans n) :=
        Nat.add_le_add_left (Nat.add_le_add_left hbt _) _
    _ ≤ cTot * M + logSlack (cTot * cSlack + cSlk) n :=
        Nat.add_le_add_left hslackmerge _

end Kolmogorov
