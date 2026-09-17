import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.OrdinalPlainRandomness
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.StochasticTotalReduction
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.AddNoise
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.ProfileBridges
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.StepWiseTotal.Part01
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.StepWiseTotal
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.UpwardStagedCondition

/-!
# Conditional input for upward closure

This module isolates the genuine budget-scale random-noise transport still
needed for `prop:upward`.  The separate public theorem `prop_add_noise` is
already proved by a direct length-scale stochasticity transport; the charged
heavy-truncation development is still required to provide the plan-mandated
budget-scale provenance and close `prop:upward`.  The transport below starts
from a visible plain-complexity budget for the base string; it does not accept a
purified model or the desired pair-condition inequality as a premise.
-/

namespace Kolmogorov

open CodedFiniteDistribution
/-- The exact budgeted random-noise transport used in the upward assembly.  Proving this proposition
requires the direct information-splitting
argument; merely extending an arbitrary stochasticity witness is not sound
because its code may contain information about `y`. -/
def BudgetedRandomNoiseTransportStatement (V U : Map) : Prop :=
  ∃ c : Nat, ∀ (x y : BitString) (baseBudget epsilon alpha beta : Nat),
    plainK V x ≤ (baseBudget : ENat) →
    (y.length : ENat) ≤ condK V y x + (epsilon : ENat) →
    IsStochastic U x alpha beta →
    let r := c * epsilon + logSlack c baseBudget + logSlack c y.length
    IsStochastic U (pairCode x y) (alpha + r) (beta + r)

/-- A pair-complexity lower bound for a witness whose code is already simple
given `x`. Conditional prefix symmetry and the randomness of `y` given `x`
show that `y` remains random given the pair `(x, P.code)`. This is a valid
bookkeeping leaf, but an arbitrary stochasticity witness need not satisfy its
`KP U P.code x` premise. -/
theorem purified_witness_pair_condition_bound
    (V U : Map) (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U) :
    ∃ c : Nat, ∀ (x y : BitString) (P : CodedFiniteDistribution)
      (baseBudget epsilon P_cond_x : Nat),
      plainK V x ≤ (baseBudget : ENat) →
      (y.length : ENat) ≤ condK V y x + (epsilon : ENat) →
      KP U P.code x ≤ (P_cond_x : ENat) →
      KP U x P.code + (y.length : ENat) ≤
        KP U (pairCode x y) (pairCode P.code (natCode y.length)) +
        (epsilon + P_cond_x + logSlack c baseBudget + logSlack c y.length : ENat) := by
  obtain ⟨cRemove, hRemove⟩ := KP_cond_remove_short_info U hU
  obtain ⟨cLower, hLower⟩ := KPCondPair_chain_lower U hU
  obtain ⟨cNat, hNat⟩ := KPPlain_natCode_le_log U hU
  obtain ⟨cAdvice, hAdvice⟩ := KPPlain_advicePair_le U hU
  obtain ⟨cRandom, hRandom⟩ := random_given_stagedCondition V U hV hU
  obtain ⟨bLin, hLin⟩ := exists_condPrefixComplexityValue_linear_in_budget V U hV hU
  obtain ⟨cBase, hBase⟩ := logSlack_linear_bound 2 3 bLin
  let fixedCost := cRemove + cRandom + cLower + cNat + cAdvice
  let cLength := 4 + fixedCost
  let C := max cBase cLength
  refine ⟨C, ?_⟩
  intro x y P baseBudget epsilon P_cond_x hxBudget hyRandom hPCond
  let n := y.length
  let z := pairCode P.code (natCode n)
  have hPFinite : KP U P.code x ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.natCast_ne_top P_cond_x) hPCond
  obtain ⟨kP, hkP⟩ := ENat.ne_top_iff_exists.mp hPFinite
  obtain ⟨kx, hkx, hkxLinear⟩ := hLin x z baseBudget hxBudget
  have hSplit : KP U x P.code ≤ KP U x z + KPPlain U (natCode n) + (cRemove : ENat) := by
    simpa [z] using hRemove x P.code (natCode n)
  have hStaged :=
    hRandom x y P.code n kx kP epsilon P_cond_x hkP hPCond hyRandom
  have hChain := hLower x y z kx hkx
  have hBaseLog : logSlack 2 kx ≤ logSlack cBase baseBudget := by
    calc
      logSlack 2 kx ≤ logSlack 2 (3 * baseBudget + bLin) :=
        logSlack_mono_right 2 hkxLinear
      _ ≤ logSlack cBase baseBudget := hBase baseBudget
  have hFixedLog :
      4 * (Nat.bits n).length + fixedCost ≤ logSlack cLength n := by
    dsimp [cLength]
    unfold logSlack
    nlinarith [Nat.zero_le ((Nat.bits n).length)]
  have hCost :
      cRemove + cRandom + cLower + (2 * (Nat.bits n).length + cNat) +
          (2 * (Nat.bits n).length + 2 * (Nat.bits kx).length + cAdvice) ≤
        logSlack C baseBudget + logSlack C n := by
    have hKxLog : 2 * (Nat.bits kx).length ≤ logSlack cBase baseBudget := by
      calc
        2 * (Nat.bits kx).length ≤ logSlack 2 kx := by
          unfold logSlack
          omega
        _ ≤ logSlack cBase baseBudget := hBaseLog
    have hBaseMono : logSlack cBase baseBudget ≤ logSlack C baseBudget :=
      logSlack_mono_left (le_max_left _ _) baseBudget
    have hLengthMono : logSlack cLength n ≤ logSlack C n :=
      logSlack_mono_left (le_max_right _ _) n
    dsimp [fixedCost] at hFixedLog
    omega
  have hFinal :=
    enat_pair_condition_assembly (KP U x P.code) (KP U x z)
      (KP U y (prefixCondComplexityContext z x kx)) (KPCondPair U x y z)
      (KPPlain U (natCode n)) (KPPlain U (pairCode (natCode n) (natCode kx)))
      n (epsilon + P_cond_x) cRemove cRandom cLower
      (2 * (Nat.bits n).length + cNat)
      (2 * (Nat.bits n).length + 2 * (Nat.bits kx).length + cAdvice)
      (logSlack C baseBudget + logSlack C n)
      hSplit hStaged hChain (hNat n) (hAdvice n kx) hCost
  have hPairEq :
      KPCondPair U x y z = KP U (pairCode x y) (pairCode P.code (natCode y.length)) := rfl
  rw [hPairEq] at hFinal
  refine hFinal.trans_eq ?_
  push_cast
  ring

/-- Absorption of prospective purification costs into the uniform
`c * epsilon + log ...` radius. -/
theorem budgeted_noise_radius_absorb (cPurify cBound cExt : Nat) :
    ∃ C : Nat, ∀ (baseBudget epsilon y_len : Nat),
      logSlack cPurify baseBudget + logSlack cExt y_len ≤
        C * epsilon + logSlack C baseBudget + logSlack C y_len ∧
      (logSlack cPurify baseBudget) +
        (epsilon + logSlack cPurify baseBudget +
          logSlack cBound baseBudget + logSlack cBound y_len) +
        cExt ≤
        C * epsilon + logSlack C baseBudget + logSlack C y_len := by
  let C := 2 * cPurify + cBound + cExt + 1
  refine ⟨C, ?_⟩
  intro baseBudget epsilon y_len
  constructor
  · have hPurify : cPurify ≤ C := by
      dsimp [C]
      omega
    have hExt : cExt ≤ C := by
      dsimp [C]
      omega
    have hBase := logSlack_mono_left hPurify baseBudget
    have hLen := logSlack_mono_left hExt y_len
    omega
  · dsimp [C]
    unfold logSlack
    nlinarith [Nat.zero_le ((Nat.bits baseBudget).length),
      Nat.zero_le ((Nat.bits y_len).length), Nat.zero_le epsilon]

/-- The canonical code of a strong model has ordinary plain complexity at
most the member length plus the strongness budget and logarithmic slack.

The proof first forgets totality to obtain a short ordinary conditional
description of the model code from `x`, then applies the easy two-stage plain
coding inequality with a literal description of `x`. -/
theorem plainK_strongModelCode_le
    (V T : Map) (hV : isOptimalConditional V) (hT : isDecompressor T) :
    ∃ c : Nat, ∀ x A (hA : A.Nonempty) n epsilon,
      x.length = n →
      IsStrongSetModel T x A hA epsilon →
      plainK V (codedUniformOn A hA).code ≤
        (n + epsilon + logSlack c n : ENat) := by
  obtain ⟨cLength, hLength⟩ := plainK_le_length V hV
  obtain ⟨cSim, hSim⟩ := hV.2 T hT
  obtain ⟨cTwo, hTwo⟩ := plainK_two_stage V hV
  let c := cLength + cSim + cTwo + 2 * (Nat.bits cLength).length + 4
  refine ⟨c, ?_⟩
  intro x A hA n epsilon hxn hstrong
  have hx : plainK V x ≤ ((n + cLength : Nat) : ENat) := by
    simpa [hxn] using hLength x
  have hmodelCond :
      condK V (codedUniformOn A hA).code x ≤
        ((epsilon + cSim : Nat) : ENat) := by
    calc
      condK V (codedUniformOn A hA).code x
          ≤ condK T (codedUniformOn A hA).code x + (cSim : ENat) :=
            hSim (codedUniformOn A hA).code x
      _ ≤ totalCondK T (codedUniformOn A hA).code x + (cSim : ENat) := by
            gcongr
            exact condK_le_totalCondK T (codedUniformOn A hA).code x
      _ ≤ (epsilon : ENat) + (cSim : ENat) := by
            gcongr
            simpa [IsStrongSetModel] using hstrong
      _ = ((epsilon + cSim : Nat) : ENat) := by
            push_cast
            rfl
  have hraw := hTwo (codedUniformOn A hA).code x
    (n + cLength) (epsilon + cSim) hx hmodelCond
  refine hraw.trans ?_
  have hbits :
      (Nat.bits (n + cLength)).length ≤
        (Nat.bits n).length + (Nat.bits cLength).length + 1 :=
    length_natBits_add_le n cLength
  have hcTwo : 2 ≤ c := by
    dsimp [c]
    omega
  have hmul :
      2 * (Nat.bits n).length ≤ c * (Nat.bits n).length :=
    Nat.mul_le_mul_right (Nat.bits n).length hcTwo
  have hconst :
      cLength + cSim + cTwo + 2 * (Nat.bits cLength).length + 2 ≤ c := by
    dsimp [c]
    omega
  have hoverhead :
      cLength + cSim + 2 * (Nat.bits (n + cLength)).length + cTwo ≤
        logSlack c n := by
    unfold logSlack
    omega
  exact_mod_cast (show
    n + cLength + (epsilon + cSim) +
        2 * (Nat.bits (n + cLength)).length + cTwo ≤
      n + epsilon + logSlack c n by omega)

/-- The budgeted transport implies the public add-noise profile theorem. The
forward direction uses the literal plain-complexity bound for `x`; the reverse
direction is the already proved first-coordinate projection theorem. -/
theorem propAddNoise_of_budgetedRandomNoiseTransport
    (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U)
    (hNoise : BudgetedRandomNoiseTransportStatement V U) :
    PropAddNoiseStatement V U := by
  obtain ⟨cNoise, hNoise⟩ := hNoise
  obtain ⟨cLength, hLength⟩ := plainK_le_length V hV
  obtain ⟨cProj, hProj⟩ := isStochastic_fst_of_pair U hU
  let c := cNoise + cProj + logSlack cNoise cLength + 1
  refine ⟨c, ?_⟩
  intro x y epsilon hrandom
  let radius :=
    c * epsilon + logSlack c x.length + logSlack c y.length
  apply stochasticityProfileSet_neighborhood_of_uniform_shifts U x
    (pairCode x y) radius
  · intro alpha beta hstoch
    have hxBudget :
        plainK V x ≤ ((x.length + cLength : Nat) : ENat) := hLength x
    have hforward := hNoise x y (x.length + cLength) epsilon alpha beta
      hxBudget hrandom hstoch
    have hcNoise : cNoise ≤ c := by
      dsimp [c]
      omega
    have hbaseSplit :
        logSlack cNoise (x.length + cLength) ≤
          logSlack cNoise x.length + logSlack cNoise cLength :=
      logSlack_add_le cNoise x.length cLength
    have hxAbsorb :
        logSlack cNoise x.length + logSlack cNoise cLength ≤
          logSlack c x.length := by
      have hmul := Nat.mul_le_mul_right (Nat.bits x.length).length hcNoise
      have hconstNoise :
          cNoise + (cNoise * (Nat.bits cLength).length + cNoise) ≤ c := by
        dsimp [c]
        unfold logSlack
        omega
      unfold logSlack
      omega
    have hyAbsorb : logSlack cNoise y.length ≤ logSlack c y.length :=
      logSlack_mono_left hcNoise y.length
    have hcoef : cNoise * epsilon ≤ c * epsilon :=
      Nat.mul_le_mul_right epsilon hcNoise
    have hRadius :
        cNoise * epsilon + logSlack cNoise (x.length + cLength) +
            logSlack cNoise y.length ≤ radius := by
      dsimp [radius]
      omega
    exact isStochastic_mono (by omega) (by omega) hforward
  · intro alpha beta hstoch
    have hprojected := hProj x y alpha beta hstoch
    have hcProj : cProj ≤ c := by
      dsimp [c]
      omega
    have hRadius : cProj ≤ radius := by
      exact hcProj.trans (const_le_addNoiseRadius c epsilon x.length y.length)
    exact isStochastic_mono (by omega) (by omega) hprojected

/-- All losses in the upward assembly fit the source-facing
`O(epsilon + log n)` radius.  The parameter `m` is the fixed ordinal width;
its visible upper bound is the only fact about the finite set used here. -/
theorem upward_noise_equivalence_radius_absorb
    (cEquiv cTransport cOrdinal cModel cWidth cNoise cProj : Nat) :
    ∃ C : Nat, ∀ n epsilon m,
      m ≤ n + epsilon + logSlack cWidth n →
      2 * (epsilon + cEquiv) + cTransport +
          (cNoise * (cOrdinal * epsilon + logSlack cOrdinal n) +
            logSlack cNoise (n + epsilon + logSlack cModel n) +
            logSlack cNoise m + cProj) ≤
        C * epsilon + logSlack C n := by
  obtain ⟨bModel, hbModel⟩ := logSlack_le_add_const cModel
  obtain ⟨bWidth, hbWidth⟩ := logSlack_le_add_const cWidth
  obtain ⟨CModel, hCModel⟩ :=
    logSlack_linear_bound cNoise 2 bModel
  obtain ⟨CWidth, hCWidth⟩ :=
    logSlack_linear_bound cNoise 2 bWidth
  let K := cNoise * cOrdinal + CModel + CWidth
  let D := 2 * cEquiv + cTransport + CModel + CWidth + cProj
  let C := K + D + 2
  refine ⟨C, ?_⟩
  intro n epsilon m hm
  have hBaseLinear :
      n + epsilon + logSlack cModel n ≤
        2 * (n + epsilon) + bModel := by
    have h := hbModel n
    omega
  have hWidthLinear : m ≤ 2 * (n + epsilon) + bWidth := by
    have h := hbWidth n
    omega
  have hBaseLog :
      logSlack cNoise (n + epsilon + logSlack cModel n) ≤
        logSlack CModel (n + epsilon) :=
    (logSlack_mono_right cNoise hBaseLinear).trans
      (hCModel (n + epsilon))
  have hWidthLog :
      logSlack cNoise m ≤ logSlack CWidth (n + epsilon) :=
    (logSlack_mono_right cNoise hWidthLinear).trans
      (hCWidth (n + epsilon))
  have hModelSplit :
      logSlack CModel (n + epsilon) ≤
        logSlack CModel n + logSlack CModel epsilon :=
    logSlack_add_le CModel n epsilon
  have hWidthSplit :
      logSlack CWidth (n + epsilon) ≤
        logSlack CWidth n + logSlack CWidth epsilon :=
    logSlack_add_le CWidth n epsilon
  have hModelEpsilon :
      logSlack CModel epsilon ≤ CModel * epsilon + CModel := by
    unfold logSlack
    nlinarith [length_natBits_le epsilon]
  have hWidthEpsilon :
      logSlack CWidth epsilon ≤ CWidth * epsilon + CWidth := by
    unfold logSlack
    nlinarith [length_natBits_le epsilon]
  have hBaseFinal :
      logSlack cNoise (n + epsilon + logSlack cModel n) ≤
        logSlack CModel n + CModel * epsilon + CModel :=
    hBaseLog.trans (hModelSplit.trans (by
      calc
        logSlack CModel n + logSlack CModel epsilon
            ≤ logSlack CModel n + (CModel * epsilon + CModel) :=
              Nat.add_le_add_left hModelEpsilon _
        _ = logSlack CModel n + CModel * epsilon + CModel := by omega))
  have hWidthFinal :
      logSlack cNoise m ≤
        logSlack CWidth n + CWidth * epsilon + CWidth :=
    hWidthLog.trans (hWidthSplit.trans (by
      calc
        logSlack CWidth n + logSlack CWidth epsilon
            ≤ logSlack CWidth n + (CWidth * epsilon + CWidth) :=
              Nat.add_le_add_left hWidthEpsilon _
        _ = logSlack CWidth n + CWidth * epsilon + CWidth := by omega))
  have hOrdinal :
      cNoise * (cOrdinal * epsilon + logSlack cOrdinal n) =
        (cNoise * cOrdinal) * epsilon +
          logSlack (cNoise * cOrdinal) n := by
    unfold logSlack
    ring
  have hRaw :
      2 * (epsilon + cEquiv) + cTransport +
          (cNoise * (cOrdinal * epsilon + logSlack cOrdinal n) +
            logSlack cNoise (n + epsilon + logSlack cModel n) +
            logSlack cNoise m + cProj) ≤
        (K + 2) * epsilon + logSlack K n + D := by
    rw [hOrdinal]
    calc
      2 * (epsilon + cEquiv) + cTransport +
          ((cNoise * cOrdinal) * epsilon +
              logSlack (cNoise * cOrdinal) n +
            logSlack cNoise (n + epsilon + logSlack cModel n) +
            logSlack cNoise m + cProj)
          ≤
        2 * (epsilon + cEquiv) + cTransport +
          ((cNoise * cOrdinal) * epsilon +
              logSlack (cNoise * cOrdinal) n +
            (logSlack CModel n + CModel * epsilon + CModel) +
            (logSlack CWidth n + CWidth * epsilon + CWidth) + cProj) := by
              gcongr
      _ = (K + 2) * epsilon + logSlack K n + D := by
            dsimp [K, D]
            unfold logSlack
            ring
  have hCoeff : (K + 2) * epsilon ≤ C * epsilon := by
    apply Nat.mul_le_mul_right
    dsimp [C]
    omega
  have hLog : logSlack K n + D ≤ logSlack C n := by
    dsimp [C]
    unfold logSlack
    nlinarith [Nat.zero_le (D * (Nat.bits n).length)]
  refine hRaw.trans ?_
  calc
    (K + 2) * epsilon + logSlack K n + D
        = (K + 2) * epsilon + (logSlack K n + D) := by omega
    _ ≤ C * epsilon + logSlack C n := Nat.add_le_add hCoeff hLog


/-- The budgeted random-noise transport statement implies the upward proposition: the
description profile is stable under enlarging the model budget. -/
theorem propUpward_of_budgetedRandomNoiseTransport
    (V U T : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U)
    (hT : IsOptimalTotalConditional T)
    (hNoise : BudgetedRandomNoiseTransportStatement V U) :
    PropUpwardStatement U T := by
  obtain ⟨cNoise, hNoise⟩ := hNoise
  obtain ⟨cModel, hModel⟩ :=
    plainK_strongModelCode_le V T hV hT.1
  obtain ⟨cWidth, hWidth⟩ :=
    finiteSetLogCard_le_length_add_deficiency_log U hU
  obtain ⟨cOrdinal, hOrdinal⟩ :=
    strongModelOrdinalBits_plain_random_given_model V U hV hU
  obtain ⟨cEquiv, hEquiv⟩ :=
    strong_model_equivalent_fixed_ordinal_pair T hT
  obtain ⟨cTransport, hTransport⟩ :=
    totalEquivalentWithin_stochasticityProfiles U T hU hT.1
  obtain ⟨cProj, hProj⟩ := isStochastic_fst_of_pair U hU
  obtain ⟨C, hAbsorb⟩ := upward_noise_equivalence_radius_absorb
    cEquiv cTransport cOrdinal cModel cWidth cNoise cProj
  refine ⟨C, ?_⟩
  intro x A hA n epsilon hxn hx hstrong hdef
  let modelCode := (codedUniformOn A hA).code
  let u := strongModelOrdinalBits A x
  let noiseEpsilon := cOrdinal * epsilon + logSlack cOrdinal n
  let baseBudget := n + epsilon + logSlack cModel n
  let rawNoiseRadius :=
    cNoise * noiseEpsilon + logSlack cNoise baseBudget +
      logSlack cNoise u.length
  let noiseRadius := rawNoiseRadius + cProj
  let equivRadius := 2 * (epsilon + cEquiv) + cTransport
  have huLen : u.length = finiteSetLogCard A := by
    exact strongModelOrdinalBits_length A x hx
  have hModelBudget : plainK V modelCode ≤ (baseBudget : ENat) := by
    simpa [modelCode, baseBudget] using
      hModel x A hA n epsilon hxn hstrong
  have hWidthBound :
      finiteSetLogCard A ≤ n + epsilon + logSlack cWidth n :=
    hWidth A hA x n epsilon hxn hx hdef
  have hRandom :
      (u.length : ENat) ≤
        condK V u modelCode + (noiseEpsilon : ENat) := by
    simpa [u, modelCode, noiseEpsilon, huLen] using
      hOrdinal A hA x n epsilon hxn hx hdef
  have hNoiseProfiles :
      ProfileSetsWithinNeighborhood
        (stochasticityProfileSet U modelCode)
        (stochasticityProfileSet U (pairCode modelCode u))
        noiseRadius := by
    apply stochasticityProfileSet_neighborhood_of_uniform_shifts U
      modelCode (pairCode modelCode u) noiseRadius
    · intro alpha beta hstoch
      have hForward := hNoise modelCode u baseBudget noiseEpsilon
        alpha beta hModelBudget hRandom hstoch
      have hForward' :
          IsStochastic U (pairCode modelCode u)
            (alpha + rawNoiseRadius) (beta + rawNoiseRadius) := by
        simpa [rawNoiseRadius, noiseEpsilon, baseBudget] using hForward
      exact isStochastic_mono (by simp [noiseRadius])
        (by simp [noiseRadius]) hForward'
    · intro alpha beta hstoch
      have hProjected := hProj modelCode u alpha beta hstoch
      exact isStochastic_mono (by simp [noiseRadius])
        (by simp [noiseRadius]) hProjected
  have hEquivProfiles :
      ProfileSetsWithinNeighborhood
        (stochasticityProfileSet U x)
        (stochasticityProfileSet U (pairCode modelCode u))
        equivRadius := by
    have hequiv := hEquiv x A hA epsilon hx hstrong
    have hprofiles := hTransport x (strongModelOrdinalBitsPair A hA x)
      (epsilon + cEquiv) hequiv
    simpa [equivRadius, strongModelOrdinalBitsPair, modelCode, u] using hprofiles
  have hCombined :
      ProfileSetsWithinNeighborhood
        (stochasticityProfileSet U x)
        (stochasticityProfileSet U modelCode)
        (equivRadius + noiseRadius) :=
    hEquivProfiles.trans hNoiseProfiles.symm
  have hFinalRadius :
      equivRadius + noiseRadius ≤ C * epsilon + logSlack C n := by
    simpa [equivRadius, noiseRadius, rawNoiseRadius, noiseEpsilon,
      baseBudget, huLen] using
        hAbsorb n epsilon (finiteSetLogCard A) hWidthBound
  simpa [modelCode] using hCombined.mono hFinalRadius

/-- A description profile point yields a stochasticity witness. -/
theorem isStochastic_of_inDescriptionProfile (U : Map) (_hU : IsOptimalPrefixConditional U) :
    ∃ c : Nat, ∀ (z : BitString) (i j : Nat),
      InDescriptionProfile U z i j → IsStochastic U z (i + c) j := by
  refine ⟨0, ?_⟩
  rintro z i j ⟨S, hS, hz, hcomplexity, hcard⟩
  refine isStochastic_of_model U z (codedUniformOn S hS) i j
    (codedUniformOn_isProbability S hS) ?_ ?_
  · simpa [setComplexity, CodedFiniteDistribution.complexity] using hcomplexity
  · unfold CodedFiniteDistribution.DeficiencyLe
    rw [codedUniformOn_mass_of_mem S hS z hz]
    have hcard' : (S.card : ENNReal) ≤ (2 : ENNReal) ^ j := by
      exact_mod_cast hcard
    calc
      complexityWeight (KP U z (codedUniformOn S hS).code) ≤ 1 :=
        complexityWeight_le_one _
      _ = (S.card : ENNReal) * (S.card : ENNReal)⁻¹ := by
        symm
        apply ENNReal.mul_inv_cancel
        · exact_mod_cast hS.card_pos.ne'
        · exact ENNReal.natCast_ne_top S.card
      _ ≤ (2 : ENNReal) ^ j * (S.card : ENNReal)⁻¹ := by
        gcongr

/-- Reverse stochasticity transfer from the pair profile. -/
theorem isStochastic_pair_of_addNoisePlainProfile
    (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U) :
    ∃ c : Nat, ∀ (x y : BitString) (alpha beta N : Nat),
      InPlainDescriptionProfile V (pairCode x y) alpha beta →
      alpha ≤ N →
      IsStochastic U (pairCode x y)
        (alpha + logSlack c N)
        (beta + logSlack c N) := by
  obtain ⟨cBridge, hBridge⟩ :=
    inDescriptionProfile_of_inPlainDescriptionProfile V U hV hU
  obtain ⟨cStochastic, hStochastic⟩ :=
    isStochastic_of_inDescriptionProfile U hU
  refine ⟨cBridge + cStochastic, ?_⟩
  intro x y alpha beta N hprofile halpha
  have hprefix := hBridge (pairCode x y) alpha beta hprofile
  have hstochastic :=
    hStochastic (pairCode x y) (alpha + logSlack cBridge alpha) beta hprefix
  apply isStochastic_mono ?_ ?_ hstochastic
  · have hmono : logSlack cBridge alpha ≤ logSlack cBridge N :=
      logSlack_mono_right cBridge halpha
    have habsorb : logSlack cBridge N + cStochastic ≤
        logSlack (cBridge + cStochastic) N :=
      logSlack_add_const_le cBridge cStochastic N
    omega
  · omega

/-- Replace `plainK V x` by the visible `baseBudget` inside the radius. -/
theorem plainK_replace_by_baseBudget (c baseBudget _x_len kx : Nat) (hkx : kx ≤ baseBudget) :
    logSlack c kx ≤ logSlack c baseBudget :=
  logSlack_mono_right c hkx

/-- An additive constant is absorbed by enlarging the slack constant:
`c1 * epsilon + logSlack c1 baseBudget + logSlack c1 y_len + c2 ≤
(c1 + c2) * epsilon + logSlack (c1 + c2) baseBudget + logSlack (c1 + c2) y_len`.
No hypothesis is needed; the extra `c2` is paid for by the growth of both slack terms. -/
theorem budgeted_noise_radius_final_absorb (c1 c2 epsilon baseBudget y_len : Nat) :
    c1 * epsilon + logSlack c1 baseBudget + logSlack c1 y_len + c2 ≤
      (c1 + c2) * epsilon + logSlack (c1 + c2) baseBudget + logSlack (c1 + c2) y_len := by
  have he : c1 * epsilon ≤ (c1 + c2) * epsilon :=
    Nat.mul_le_mul (Nat.le_add_right c1 c2) (le_refl _)
  have ha : c1 * (Nat.bits baseBudget).length ≤ (c1 + c2) * (Nat.bits baseBudget).length :=
    Nat.mul_le_mul (Nat.le_add_right c1 c2) (le_refl _)
  have hb : c1 * (Nat.bits y_len).length ≤ (c1 + c2) * (Nat.bits y_len).length :=
    Nat.mul_le_mul (Nat.le_add_right c1 c2) (le_refl _)
  unfold logSlack
  omega

/-!
The public `prop_add_noise` endpoint is declared separately and proved by the
direct length-scale stochasticity route.  The public `prop_upward` endpoint
remains undeclared until the budget-scale transport is proved by the charged
heavy-truncation/multiplicity route.  The conditional wrappers above preserve
the exact upward assembly without treating that missing mathematical input as a
theorem.
-/

end Kolmogorov
