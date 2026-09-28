-- Calibration fixture for scripts/cut_quality.py: hereditary_family_step_budget_caller.
-- Lines 250-262, 363-379 of KolmogorovMathlib/AlgorithmicStatistics/StrongModels/Hereditary/Part02/Steps.lean, verbatim at c989552;
-- everything between them is elided.  The fixture is not meant to
-- compile: it is the text the gate reads.

namespace Kolmogorov

lemma hereditary_core_family_from_model (V T : Map) (hV : isOptimalConditional V)
    (hT : IsOptimalTotalConditional T) (cIn : Nat) :
    ∃ cOut : Nat,
      ∀ x n A (hA : A.Nonempty) M (hM : M.Nonempty) (epsilon delta : Nat),
        x.length = n →
        epsilon * 2 < Nat.sqrt n →
        x ∈ M →
        IsSufficientStatistic V x A hA epsilon →
        IsStrongSetModel T x A hA epsilon →
        IsStrongSetModel T x M hM epsilon →
        plainSetComplexity V M hM ≤ plainSetComplexity V A hA + (delta : ENat) →
        condK V (codedUniformOn M hM).code (codedUniformOn A hA).code ≤
          (hereditarySlack cIn delta epsilon n : ENat) →

-- ------------------------------------------------------------

  -- Every accumulated overhead is inside the hereditary slack of `b ^ 34`.
  have hcardA1 : finiteSetLogCard A1 ≤ 2 * n + b := hA1Log.trans hcardA
  have hmCompMix : mComp ≤ 2 * n + b + hereditaryUnit delta epsilon n := by
    have h : (mComp : ENat) ≤ ((2 * n + b + delta : Nat) : ENat) := by
      rw [← hMVal]
      refine hMA.trans ?_
      calc plainSetComplexity V A hA + (delta : ENat)
          ≤ ((2 * n + b : Nat) : ENat) + (delta : ENat) := by gcongr
        _ = ((2 * n + b + delta : Nat) : ENat) := by push_cast; ring
    have hnat : mComp ≤ 2 * n + b + delta := by exact_mod_cast h
    have := delta_le_hereditaryUnit delta epsilon n
    omega
  have hbud : 2 * p_F1 + b + (b * p_F1 + logSlack b (finiteSetLogCard A1)) +
      (pPlain + 2 * (Nat.bits mComp).length + b) +
      b ^ 20 * hereditaryUnit delta epsilon n + 2 ≤
      hereditarySlack (b ^ 27) delta epsilon n :=
    hereditary_family_step_budget hb hsqrt1 le_rfl hcardA1 hmCompMix hpF1U hpPlainU le_rfl

end Kolmogorov
