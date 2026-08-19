import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.StrongModelImageSet
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.UniformDeficiencyBound
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.RadiusMonotone
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.UpwardConditional
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.PurityChargedArithmetic
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.CubeStochasticity
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.UpwardOrdinalNoiseTransport

open ENNReal

namespace Kolmogorov

theorem isStochastic_uniform_of_plainK_setCode
    (U V : Map) (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U)
    {B : Finset BitString} (hB : B.Nonempty) {z : BitString} (k d : Nat) :
    plainK V (codedUniformOn B hB).code ≤ (k : ENat) →
    CodedFiniteDistribution.DeficiencyLe U (codedUniformOn B hB) z d →
    ∃ c : Nat, IsStochastic U z (k + 2 * (Nat.bits k).length + c) d := by
  intro hk hd
  obtain ⟨cKP, hKP⟩ := KPPlain_le_plainK_add_KPPlain_plainK U V hU hV
  obtain ⟨cBits, hBits⟩ := KPPlain_le_two_mul_length U hU
  refine ⟨cBits + cKP, ?_⟩
  set c := cBits + cKP
  have hne : plainK V (codedUniformOn B hB).code ≠ ⊤ := ne_top_of_le_ne_top (by simp) hk
  obtain ⟨kC, hkC_symm⟩ := WithTop.ne_top_iff_exists.1 hne
  have hkC : plainK V (codedUniformOn B hB).code = (kC : ENat) := hkC_symm.symm
  have hcomp : setComplexity U B hB ≤ ((k + 2 * (Nat.bits k).length + c : Nat) : ENat) := by
    calc setComplexity U B hB = KPPlain U (codedUniformOn B hB).code := rfl
      _ ≤ (kC : ENat) + KPPlain U (Nat.bits kC) + (cKP : ENat) := hKP _ _ hkC
      _ ≤ (kC : ENat) + ((2 * (Nat.bits kC).length + cBits : Nat) : ENat) + (cKP : ENat) := by
            gcongr
            exact hBits (Nat.bits kC)
      _ = ((kC + 2 * (Nat.bits kC).length + cBits + cKP : Nat) : ENat) := by push_cast; ring
      _ ≤ ((k + 2 * (Nat.bits k).length + cBits + cKP : Nat) : ENat) := by
            gcongr
            · have hle : kC ≤ k := by exact_mod_cast hkC.symm.trans_le hk
              exact hle
            · have hle : kC ≤ k := by exact_mod_cast hkC.symm.trans_le hk
              exact length_natBits_mono hle
      _ = ((k + 2 * (Nat.bits k).length + c : Nat) : ENat) := by dsimp [c]; push_cast; ring
  refine isStochastic_of_model U z (codedUniformOn B hB)
    (k + 2 * (Nat.bits k).length + c) d (codedUniformOn_isProbability _ _) hcomp hd

theorem beta_regime_radius_absorb
    (c₁ c₂ : Nat) :
    ∃ C : Nat, ∀ eps n : Nat,
      eps + 2 * (Nat.bits (eps + logSlack c₁ n)).length + logSlack c₁ n + c₂ ≤
      C * eps + logSlack C n := by
  refine ⟨3 * c₁ + 3 + c₂ , fun eps n => ?_⟩
  dsimp [logSlack]
  have h1 := length_natBits_add_le eps (c₁ * (Nat.bits n).length + c₁)
  have h2 := length_natBits_le_self eps
  have h3 := length_natBits_le_self (c₁ * (Nat.bits n).length + c₁)
  have h4 : 3 * (c₁ * (Nat.bits n).length) ≤ (3 * c₁ + 3 + c₂) * (Nat.bits n).length := by
    calc 3 * (c₁ * (Nat.bits n).length) = (3 * c₁) * (Nat.bits n).length := by ring
    _ ≤ (3 * c₁ + 3 + c₂) * (Nat.bits n).length := by gcongr; omega
  have h5 : 3 * eps ≤ (3 * c₁ + 3 + c₂) * eps := by
    gcongr
    omega
  omega

theorem strongModelOrdinalNoiseTransport_of_n_le_beta
    (V U T : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U) (hT : IsOptimalTotalConditional T) :
    ∃ c : Nat, ∀ x A (hA : A.Nonempty) n epsilon alpha beta,
      x.length = n → x ∈ A →
      IsStrongSetModel T x A hA epsilon →
      n ≤ beta →
      IsStochastic U (strongModelOrdinalBitsPair A hA x)
        (alpha + (c * epsilon + logSlack c n))
        (beta + (c * epsilon + logSlack c n)) := by
  obtain ⟨c1, hc1⟩ := strongModelPairImage_exists T hT
  obtain ⟨c2, hc2⟩ := plainK_codedUniformOn_image_le V T hV hT.1
  obtain ⟨cKP, hKP⟩ := KPPlain_le_plainK_add_KPPlain_plainK U V hU hV
  obtain ⟨cBits, hBits⟩ := KPPlain_le_two_mul_length U hU
  obtain ⟨C, hC⟩ := beta_regime_radius_absorb c2 (cBits + cKP)
  refine ⟨C * c1 + C, ?_⟩
  intro x A hA n epsilon alpha beta hxn hxA hstrong hnbeta
  obtain ⟨B, hB, hy_in_B, hcard, htotal⟩ := hc1 x A hA n epsilon hxn hxA hstrong
  have hplain := hc2 n B hB (epsilon + c1) htotal
  let z := strongModelOrdinalBitsPair A hA x
  have hne : plainK V (codedUniformOn B hB).code ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.natCast_ne_top _) hplain
  obtain ⟨kC, hkC_symm⟩ := WithTop.ne_top_iff_exists.1 hne
  have hkC : plainK V (codedUniformOn B hB).code = (kC : ENat) := hkC_symm.symm
  let k := epsilon + c1 + logSlack c2 n
  have hcomp :
      setComplexity U B hB ≤
        ((k + 2 * (Nat.bits k).length + (cBits + cKP) : Nat) : ENat) := by
    calc setComplexity U B hB = KPPlain U (codedUniformOn B hB).code := rfl
      _ ≤ (kC : ENat) + KPPlain U (Nat.bits kC) + (cKP : ENat) := hKP _ _ hkC
      _ ≤ (kC : ENat) + ((2 * (Nat.bits kC).length + cBits : Nat) : ENat) + (cKP : ENat) := by
            gcongr
            exact hBits (Nat.bits kC)
      _ = ((kC + 2 * (Nat.bits kC).length + cBits + cKP : Nat) : ENat) := by push_cast; ring
      _ ≤ ((k + 2 * (Nat.bits k).length + cBits + cKP : Nat) : ENat) := by
            gcongr
            · exact_mod_cast hkC.symm.trans_le hplain
            · have hle : kC ≤ k := by exact_mod_cast hkC.symm.trans_le hplain
              exact length_natBits_mono hle
      _ = ((k + 2 * (Nat.bits k).length + (cBits + cKP) : Nat) : ENat) := by push_cast; ring
  have hstoch :
      IsStochastic U z
        (k + 2 * (Nat.bits k).length + (cBits + cKP)) (finiteSetLogCard B) :=
    isStochastic_of_model U z (codedUniformOn B hB)
      (k + 2 * (Nat.bits k).length + (cBits + cKP))
      (finiteSetLogCard B) (codedUniformOn_isProbability _ _) hcomp
      (deficiencyLe_codedUniformOn_finiteSetLogCard U hB hy_in_B)
  apply isStochastic_mono _ _ hstoch
  · have h1 := hC (epsilon + c1) n
    calc epsilon + c1 + logSlack c2 n +
          2 * (Nat.bits (epsilon + c1 + logSlack c2 n)).length +
          (cBits + cKP)
      _ = (epsilon + c1) +
          2 * (Nat.bits ((epsilon + c1) + logSlack c2 n)).length +
          logSlack c2 n + (cBits + cKP) := by omega
      _ ≤ C * (epsilon + c1) + logSlack C n := h1
      _ = C * epsilon + C * c1 + logSlack C n := by ring
      _ ≤ alpha + ((C * c1 + C) * epsilon + logSlack (C * c1 + C) n) := by
          dsimp [logSlack]
          have hc : C ≤ C * c1 + C := by omega
          have hle1 : C * epsilon ≤ (C * c1 + C) * epsilon :=
            Nat.mul_le_mul_right epsilon hc
          have hle2 :
              C * (Nat.bits n).length ≤
                (C * c1 + C) * (Nat.bits n).length :=
            Nat.mul_le_mul_right _ hc
          omega
  · have h2 : finiteSetLogCard B ≤ n := (finiteSetLogCard_le_iff B n).mpr hcard
    calc finiteSetLogCard B
      _ ≤ n := h2
      _ ≤ beta := hnbeta
      _ ≤ beta + ((C * c1 + C) * epsilon + logSlack (C * c1 + C) n) := by omega


/-- **The consumer-shaped ordinal noise transport, unconditionally.**  The two
regimes `beta ≤ n + epsilon + logSlack cBudget n`
(`strongModelOrdinalNoiseTransport_of_beta_le`) and `n ≤ beta`
(`strongModelOrdinalNoiseTransport_of_n_le_beta`) exhaust all deficiency
budgets, so the narrowed transport statement holds outright. -/
theorem strongModelOrdinalNoiseTransport (U T : Map)
    (hU : IsOptimalPrefixConditional U) (hT : IsOptimalTotalConditional T) :
    StrongModelOrdinalNoiseTransportStatement U T := by
  obtain ⟨V, hV⟩ := existsIsOptimalConditional
  obtain ⟨cBudget, c1, h1⟩ := strongModelOrdinalNoiseTransport_of_beta_le V U T hV hU hT
  obtain ⟨c2, h2⟩ := strongModelOrdinalNoiseTransport_of_n_le_beta V U T hV hU hT
  refine ⟨max c1 c2, ?_⟩
  intro x A hA n epsilon alpha beta hxn hx hstrong hdef hstoch
  set C := max c1 c2 with hC
  change IsStochastic U (strongModelOrdinalBitsPair A hA x)
    (alpha + (C * epsilon + logSlack C n)) (beta + (C * epsilon + logSlack C n))
  by_cases hbeta : beta ≤ n + epsilon + logSlack cBudget n
  · have hbranch := h1 x A hA n epsilon alpha beta hxn hx hstrong hdef hbeta hstoch
    have hle : c1 * epsilon + logSlack c1 n ≤ C * epsilon + logSlack C n := by
      have h1' : c1 * epsilon ≤ C * epsilon :=
        Nat.mul_le_mul_right _ (le_max_left c1 c2)
      have h2' : logSlack c1 n ≤ logSlack C n := logSlack_mono_left (le_max_left c1 c2) n
      omega
    exact isStochastic_mono (Nat.add_le_add_left hle alpha)
      (Nat.add_le_add_left hle beta) hbranch
  · have hnbeta : n ≤ beta := by omega
    have hbranch := h2 x A hA n epsilon alpha beta hxn hx hstrong hnbeta
    have hle : c2 * epsilon + logSlack c2 n ≤ C * epsilon + logSlack C n := by
      have h1' : c2 * epsilon ≤ C * epsilon :=
        Nat.mul_le_mul_right _ (le_max_right c1 c2)
      have h2' : logSlack c2 n ≤ logSlack C n := logSlack_mono_left (le_max_right c1 c2) n
      omega
    exact isStochastic_mono (Nat.add_le_add_left hle alpha)
      (Nat.add_le_add_left hle beta) hbranch

/-- **VS40 Proposition `prop:upward`, unconditionally.**  For an `epsilon`-strong
model `A` of an `n`-bit string `x` with optimality deficiency at most `epsilon`,
the stochasticity profile of `x` and that of the model code lie within
`O(epsilon + log n)` of each other. -/
theorem prop_upward (U T : Map)
    (hU : IsOptimalPrefixConditional U) (hT : IsOptimalTotalConditional T) :
    PropUpwardStatement U T :=
  propUpward_of_strongModelOrdinalNoiseTransport U T hU hT
    (strongModelOrdinalNoiseTransport U T hU hT)
end Kolmogorov
