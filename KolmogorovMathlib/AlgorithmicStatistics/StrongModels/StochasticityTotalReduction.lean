import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.TotalProgramGraphConservation
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.ProjectionConservation
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.Properties

namespace Kolmogorov

theorem isStochastic_of_totalReducesWithin
    (U T : Map)
    (hU : IsOptimalPrefixConditional U)
    (hT : isDecompressor T) :
    ∃ c, ∀ x y epsilon alpha beta,
      TotalReducesWithin T x y epsilon →
      IsStochastic U x alpha beta →
      IsStochastic U y
        (alpha + 2 * epsilon + c)
        (beta  + 2 * epsilon + c) := by
  obtain ⟨cGraph, hGraph⟩ := isStochastic_totalProgramGraph U T hU hT
  obtain ⟨cProj, hProj⟩ := isStochastic_fst_of_pair U hU
  refine ⟨cGraph + cProj, ?_⟩
  intro x y epsilon alpha beta hred hstoch
  obtain ⟨p, htotal, hlength, hprod⟩ :=
    (totalReducesWithin_iff T x y epsilon).mp hred
  have hlength' : p.length ≤ epsilon := by
    simpa [programLength] using hlength
  have hgraph := hGraph p x y alpha beta htotal hprod hstoch
  have hprojected :=
    hProj y x (alpha + 2 * p.length + cGraph)
      (beta + 2 * p.length + cGraph) hgraph
  exact isStochastic_mono (by omega) (by omega) hprojected

theorem totalEquivalentWithin_stochasticityProfiles
    (U T : Map)
    (hU : IsOptimalPrefixConditional U)
    (hT : isDecompressor T) :
    ∃ c, ∀ x y epsilon,
      TotalEquivalentWithin T x y epsilon →
      ProfileSetsWithinNeighborhood
        (stochasticityProfileSet U x)
        (stochasticityProfileSet U y)
        (2 * epsilon + c) := by
  obtain ⟨c, hred⟩ := isStochastic_of_totalReducesWithin U T hU hT
  refine ⟨c, ?_⟩
  intro x y epsilon hequiv
  obtain ⟨hxy, hyx⟩ := (totalEquivalentWithin_iff T x y epsilon).mp hequiv
  exact stochasticityProfileSet_neighborhood_of_uniform_shifts U x y
    (2 * epsilon + c)
    (fun alpha beta hstoch => by
      simpa [Nat.add_assoc] using hred x y epsilon alpha beta hxy hstoch)
    (fun alpha beta hstoch => by
      simpa [Nat.add_assoc] using hred y x epsilon alpha beta hyx hstoch)

end Kolmogorov
