import KolmogorovMathlib.Prefix.ConditionalSymmetry
import KolmogorovMathlib.Prefix.Properties
import KolmogorovMathlib.AlgorithmicProbability.PairProjection
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.ParameterCharge
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.AddNoise
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.Properties
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.UpwardConditional
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.UpwardOrdinalNoiseTransport

namespace Kolmogorov

/-- **L1**: Removing known short info `z` from the condition. -/
theorem KP_fst_cond_le_pair_cond_pair_width
    (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (P : CodedFiniteDistribution) (a u : BitString) (m : ℕ),
      KP U a P.code ≤
        KP U (pairCode a u) (pairCode P.code (natCode m)) + (logSlack c m : ENat) := by
  obtain ⟨cRem, hRem⟩ := KP_cond_remove_short_info U hU
  obtain ⟨cMap, hMap⟩ := KP_map_le U hU decodeFirst decodeFirst_computable
  obtain ⟨cNat, hNat⟩ := KPPlain_natCode_le_logSlack U hU
  refine ⟨cRem + cMap + cNat + cNat, fun P a u m => ?_⟩
  calc
    KP U a P.code
        = KP U (decodeFirst (pairCode a u)) P.code := by rw [decodeFirst_pairCode]
      _ ≤ KP U (pairCode a u) P.code + (cMap : ENat) := hMap (pairCode a u) P.code
      _ ≤ KP U (pairCode a u) (pairCode P.code (natCode m))
            + KPPlain U (natCode m) + (cRem : ENat) + cMap := by
            have h1 := hRem (pairCode a u) P.code (natCode m)
            gcongr
      _ ≤ KP U (pairCode a u) (pairCode P.code (natCode m))
            + ((logSlack cNat m + cNat : ℕ) : ENat) + cRem + cMap := by
            have h2 := hNat m
            gcongr
      _ = KP U (pairCode a u) (pairCode P.code (natCode m))
            + (((logSlack cNat m + cNat : ℕ) : ENat) + cRem + cMap) := by
            rw [add_assoc, add_assoc, ← add_assoc ((logSlack cNat m + cNat : ℕ) : ENat)]
      _ ≤ KP U (pairCode a u) (pairCode P.code (natCode m))
            + ((logSlack (cRem + cMap + cNat + cNat) m : ℕ) : ENat) := by
            have h_nat : logSlack cNat m + cNat + cRem + cMap
                ≤ logSlack (cRem + cMap + cNat + cNat) m := by
              unfold logSlack
              simp only [add_mul]
              omega
            gcongr
            exact_mod_cast h_nat

/-- **L2**: Pair uniform extension stochasticity where the extra charge is
`m + logSlack c m + c`. -/
theorem pairUniformExtension_stochasticity_width_charged
    (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (P : CodedFiniteDistribution) (a u : BitString)
      (m alpha beta : ℕ),
      u.length = m →
      P.IsProbability →
      P.complexity U ≤ (alpha : ENat) →
      DeficiencyLe U P a beta →
      IsStochastic U (pairCode a u)
        (alpha + logSlack c m) (beta + m + logSlack c m + c) := by
  obtain ⟨cExt, hExt⟩ := pairUniformExtension_stochasticity_of_condition_bound U hU
  obtain ⟨cL1, hL1⟩ := KP_fst_cond_le_pair_cond_pair_width U hU
  refine ⟨cExt + cL1, fun P a u m alpha beta hu hP hAlpha hDef => ?_⟩
  have hCond : KP U a P.code + m ≤
      KP U (pairCode a u) (pairCode P.code (natCode m)) + ((m + logSlack cL1 m : ℕ) : ENat) := by
    calc
      KP U a P.code + (m : ENat)
          ≤ (KP U (pairCode a u) (pairCode P.code (natCode m)) + logSlack cL1 m) + m := by
        have h1 := hL1 P a u m
        gcongr
      _ = KP U (pairCode a u) (pairCode P.code (natCode m)) + (m + logSlack cL1 m : ℕ) := by
        rw [add_assoc, add_comm (logSlack cL1 m : ENat)]
        push_cast
        rfl
  have hStoch := hExt P a u m alpha beta (m + logSlack cL1 m) hu hP hAlpha hDef hCond
  apply isStochastic_mono _ _ hStoch
  · unfold logSlack; simp only [add_mul]; omega
  · unfold logSlack; simp only [add_mul]; omega

/-- **L3**: Consumer instantiation of the width-charged transport. -/
theorem strongModelOrdinalNoiseTransport_of_width_slack
    (V U T : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U)
    (hT : IsOptimalTotalConditional T) :
    ∃ c : Nat, ∀ x A (hA : A.Nonempty) n epsilon alpha beta,
      x.length = n →
      x ∈ A →
      IsStrongSetModel T x A hA epsilon →
      DeficiencyLe U (codedUniformOn A hA) x epsilon →
      (∃ (a b : Nat), a ≤ alpha ∧ b ≤ beta ∧
        IsStochastic U (codedUniformOn A hA).code a b ∧
        b + finiteSetLogCard A + logSlack c n ≤ beta) →
      let r := c * epsilon + logSlack c n
      IsStochastic U (strongModelOrdinalBitsPair A hA x) (alpha + r) (beta + r) := by
  obtain ⟨cExt, hExt⟩ := pairUniformExtension_stochasticity_width_charged U hU
  obtain ⟨cWidth, hWidth⟩ := finiteSetLogCard_le_length_add_deficiency_log U hU
  obtain ⟨cModel, hModel⟩ := plainK_strongModelCode_le V T hV hT.1
  let c1 := cExt + cExt
  obtain ⟨C, hAbsorb⟩ := upward_ordinal_noise_radius_absorb c1 0 cModel cWidth
  refine ⟨C, fun x A hA n epsilon alpha beta hxn hx hstrong hdef
    ⟨a, b, halpha, hbeta, hstoch, hslack⟩ => ?_⟩
  let m := finiteSetLogCard A
  let modelCode := (codedUniformOn A hA).code
  let u := strongModelOrdinalBits A x
  have huLen : u.length = m := strongModelOrdinalBits_length A x hx
  have hWidthBound : m ≤ n + epsilon + logSlack cWidth n := hWidth A hA x n epsilon hxn hx hdef
  have hAbs : c1 * (0 * epsilon + logSlack 0 n)
      + logSlack c1 (n + epsilon + logSlack cModel n) + logSlack c1 m
      ≤ C * epsilon + logSlack C n :=
    hAbsorb n epsilon m hWidthBound
  have hmAbs : logSlack cExt m + cExt ≤ C * epsilon + logSlack C n := by
    calc
      logSlack cExt m + cExt ≤ logSlack c1 m := by
        dsimp [c1]; unfold logSlack; simp only [add_mul]; omega
      _ ≤ c1 * (0 * epsilon + logSlack 0 n)
            + logSlack c1 (n + epsilon + logSlack cModel n) + logSlack c1 m := by
        omega
      _ ≤ C * epsilon + logSlack C n := hAbs
  obtain ⟨P, hP_prob, hP_alpha, hP_def⟩ := hstoch
  have hPair := hExt P modelCode u m a b huLen hP_prob hP_alpha hP_def
  apply isStochastic_mono _ _ hPair
  · omega
  · omega

end Kolmogorov
