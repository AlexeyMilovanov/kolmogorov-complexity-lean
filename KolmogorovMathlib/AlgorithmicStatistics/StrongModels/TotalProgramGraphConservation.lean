import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.TotalProgramGraph
import KolmogorovMathlib.AlgorithmicStatistics.Stochasticity
import KolmogorovMathlib.AlgorithmicStatistics.Deficiency
import KolmogorovMathlib.AlgorithmicStatistics.BoundedComplexityLists.NonStochasticRevisited

namespace Kolmogorov

theorem KPPlain_totalProgramGraphCode_le
    (U T : Map)
    (hU : IsOptimalPrefixConditional U)
    (hT : isDecompressor T) :
    ∃ c : ℕ, ∀ p P G,
      IsTotalProgramGraphModel T p P G →
      G.complexity U ≤ P.complexity U + KPPlain U p + c := by
  let f : BitString →. BitString := fun w =>
    totalProgramGraphCode T (decodeFirst w, decodeSecond w)
  have hf : Partrec f := by
    exact (totalProgramGraphCode_partrec T hT).comp
      (decodeFirst_computable.pair decodeSecond_computable)
  obtain ⟨cMap, hMap⟩ := KPPlain_partrec_map_le U hU f hf
  obtain ⟨cPair, hPair⟩ := KPPair_le_KPPlain_add_KPPlain U hU
  refine ⟨cMap + cPair, ?_⟩
  intro p P G hG
  have hgraphCode : G.code ∈ totalProgramGraphCode T (p, P.code) := by
    apply totalProgramGraphCode_eval T p P G.data
    exact (totalProgramGraphData_spec T p P.data G.data).mpr hG
  have hcode : G.code ∈ f (pairCode p P.code) := by
    simpa [f, decodeFirst_pairCode, decodeSecond_pairCode] using hgraphCode
  calc
    G.complexity U
        ≤ KPPlain U (pairCode p P.code) + (cMap : ENat) :=
          hMap (pairCode p P.code) G.code hcode
    _ = KPPair U p P.code + (cMap : ENat) := rfl
    _ ≤ (KPPlain U p + P.complexity U + (cPair : ENat)) + (cMap : ENat) := by
          gcongr
          exact hPair p P.code
    _ = P.complexity U + KPPlain U p + ((cMap + cPair : ℕ) : ENat) := by
          push_cast
          ac_rfl

theorem KP_sourceCondition_le_totalProgramGraph
    (U T : Map)
    (hU : IsOptimalPrefixConditional U)
    (hT : isDecompressor T) :
    ∃ c : ℕ, ∀ p P G x y,
      IsTotalProgramGraphModel T p P G →
      produces T p x y →
      KP U x P.code ≤
        KP U (pairCode y x) G.code + KPPlain U p + c := by
  let g : BitString → BitString →. BitString := fun sourceCode p =>
    totalProgramGraphCode T (p, sourceCode)
  have hg : Partrec (fun q : BitString × BitString => g q.1 q.2) := by
    exact (totalProgramGraphCode_partrec T hT).comp
      (Computable.snd.pair Computable.fst)
  obtain ⟨cCond, hCond⟩ := KP_cond_partrec_advice_map_le U hU g hg
  obtain ⟨cProj, hProj⟩ := KP_map_le U hU decodeSecond decodeSecond_computable
  refine ⟨cCond + cProj, ?_⟩
  intro p P G x y hG _hprod
  have hgraphCode : G.code ∈ totalProgramGraphCode T (p, P.code) := by
    apply totalProgramGraphCode_eval T p P G.data
    exact (totalProgramGraphData_spec T p P.data G.data).mpr hG
  have hchange :
      KP U x P.code ≤ KP U x G.code + KPPlain U p + (cCond : ENat) :=
    hCond x P.code p G.code hgraphCode
  have hproject :
      KP U x G.code ≤ KP U (pairCode y x) G.code + (cProj : ENat) := by
    simpa [decodeSecond_pairCode] using hProj (pairCode y x) G.code
  calc
    KP U x P.code
        ≤ KP U x G.code + KPPlain U p + (cCond : ENat) := hchange
    _ ≤ (KP U (pairCode y x) G.code + (cProj : ENat)) +
          KPPlain U p + (cCond : ENat) := by
          gcongr
    _ = KP U (pairCode y x) G.code + KPPlain U p +
          ((cCond + cProj : ℕ) : ENat) := by
          push_cast
          ac_rfl

theorem deficiency_of_equal_mass_and_condition_le (U : Map)
    (P G : CodedFiniteDistribution) (x z : BitString) (beta d : ℕ)
    (h_def : DeficiencyLe U P x beta)
    (h_cond : KP U x P.code ≤ KP U z G.code + d)
    (h_mass : G.mass z = P.mass x) :
    DeficiencyLe U G z (beta + d) :=
  by
    have hweight :
        complexityWeight (KP U z G.code) * (2 : ENNReal)⁻¹ ^ d ≤
          complexityWeight (KP U x P.code) := by
      simpa only [complexityWeight_add_nat] using
        (complexityWeight_le_of_le h_cond)
    have hcancel :
        (2 : ENNReal)⁻¹ ^ d * (2 : ENNReal) ^ d = 1 := by
      rw [← mul_pow, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_pow]
    unfold DeficiencyLe CodedFiniteDistribution.DeficiencyLe at *
    calc
      complexityWeight (KP U z G.code)
          = (complexityWeight (KP U z G.code) * (2 : ENNReal)⁻¹ ^ d) *
              (2 : ENNReal) ^ d := by
                rw [mul_assoc, hcancel, mul_one]
      _ ≤ complexityWeight (KP U x P.code) * (2 : ENNReal) ^ d := by
            gcongr
      _ ≤ ((2 : ENNReal) ^ beta * P.mass x) * (2 : ENNReal) ^ d := by
            gcongr
      _ = (2 : ENNReal) ^ (beta + d) * G.mass z := by
            rw [pow_add, h_mass]
            ring

theorem totalProgramGraph_complexity_le
    (U T : Map)
    (hU : IsOptimalPrefixConditional U)
    (hT : isDecompressor T) :
    ∃ c, ∀ p P G,
      IsTotalProgramGraphModel T p P G →
      G.complexity U ≤ P.complexity U + (2 * p.length + c : ℕ) := by
  obtain ⟨cGraph, hGraph⟩ := KPPlain_totalProgramGraphCode_le U T hU hT
  obtain ⟨cLength, hLength⟩ := KPPlain_le_two_mul_length U hU
  refine ⟨cGraph + cLength, ?_⟩
  intro p P G hG
  calc
    G.complexity U
        ≤ P.complexity U + KPPlain U p + (cGraph : ENat) := hGraph p P G hG
    _ ≤ P.complexity U +
          (2 * p.length + (cLength : ENat)) + (cGraph : ENat) := by
          gcongr
          exact hLength p
    _ = P.complexity U + ((2 * p.length + (cGraph + cLength) : ℕ) : ENat) := by
          push_cast
          ac_rfl

theorem deficiency_totalProgramGraph
    (U T : Map)
    (hU : IsOptimalPrefixConditional U)
    (hT : isDecompressor T) :
    ∃ c, ∀ p P G x y beta,
      IsTotalProgramGraphModel T p P G →
      produces T p x y →
      DeficiencyLe U P x beta →
      DeficiencyLe U G (pairCode y x)
        (beta + 2 * p.length + c) := by
  obtain ⟨cCond, hCond⟩ := KP_sourceCondition_le_totalProgramGraph U T hU hT
  obtain ⟨cLength, hLength⟩ := KPPlain_le_two_mul_length U hU
  refine ⟨cCond + cLength, ?_⟩
  intro p P G x y beta hG hprod hdef
  have hcondition :
      KP U x P.code ≤ KP U (pairCode y x) G.code +
        ((2 * p.length + (cCond + cLength) : ℕ) : ENat) := by
    calc
      KP U x P.code
          ≤ KP U (pairCode y x) G.code + KPPlain U p + (cCond : ENat) :=
            hCond p P G x y hG hprod
      _ ≤ KP U (pairCode y x) G.code +
            (2 * p.length + (cLength : ENat)) + (cCond : ENat) := by
            gcongr
            exact hLength p
      _ = KP U (pairCode y x) G.code +
            ((2 * p.length + (cCond + cLength) : ℕ) : ENat) := by
            push_cast
            ac_rfl
  simpa [Nat.add_assoc] using
    deficiency_of_equal_mass_and_condition_le U P G x (pairCode y x) beta
      (2 * p.length + (cCond + cLength)) hdef hcondition (hG.mass_pair hprod)

theorem isStochastic_totalProgramGraph
    (U T : Map)
    (hU : IsOptimalPrefixConditional U)
    (hT : isDecompressor T) :
    ∃ c, ∀ p x y alpha beta,
      IsTotalProgram T p →
      produces T p x y →
      IsStochastic U x alpha beta →
      IsStochastic U (pairCode y x) (alpha + 2 * p.length + c) (beta + 2 * p.length + c) := by
  obtain ⟨cComp, hComp⟩ := totalProgramGraph_complexity_le U T hU hT
  obtain ⟨cDef, hDef⟩ := deficiency_totalProgramGraph U T hU hT
  refine ⟨cComp + cDef, ?_⟩
  intro p x y alpha beta htotal hprod hstoch
  obtain ⟨P, hPprob, hPcomp, hPdef⟩ := hstoch
  obtain ⟨G, hG, hGprob, _hGcode⟩ :=
    exists_totalProgramGraphProbabilityModel T p htotal P hPprob
  refine ⟨G, hGprob, ?_, ?_⟩
  · calc
      G.complexity U
          ≤ P.complexity U + ((2 * p.length + cComp : ℕ) : ENat) :=
            hComp p P G hG
      _ ≤ (alpha : ENat) + ((2 * p.length + cComp : ℕ) : ENat) := by
            gcongr
      _ ≤ ((alpha + 2 * p.length + (cComp + cDef) : ℕ) : ENat) := by
            exact_mod_cast
              (show alpha + (2 * p.length + cComp) ≤
                alpha + 2 * p.length + (cComp + cDef) by omega)
  · exact (hDef p P G x y beta hG hprod hPdef).mono_beta (by omega)

end Kolmogorov
