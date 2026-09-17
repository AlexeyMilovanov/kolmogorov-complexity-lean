import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.HereditaryLift
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.FamilyStep.Filtered
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.FamilyStep.PlainTotal

/-!
# The sharp form of the family step

`hereditary_family_model_sharp` restates `hereditary_family_model` in the form the hereditary
theorem consumes: the framing of the total decoder is made to depend only on the data the
caller can supply, so the constant is uniform in the model.
-/

namespace Kolmogorov
open Kolmogorov.CodedFiniteDistribution

/-- Sharp worker form of `hereditary_family_model`.  The total decoder's
framing depends only on the partition and total-reduction programs, so its
strength does not need a visible bound for `C(M)` or `log #M`.  The ordinary
decoder only encodes the intersection threshold, which is bounded by
`log #A`.  Keeping these two budgets separate is essential in the hereditary
assembly, where `M` may have a loose cardinality coordinate. -/
theorem hereditary_family_model_sharp
    (V T : Map)
    (hV : isOptimalConditional V)
    (hT : IsOptimalTotalConditional T) :
    ∃ c, ∀ P A (hA : A.Nonempty) M (hM : M.Nonempty) (p s : Nat),
      IsPartition P →
      A ∈ P →
      (A ∩ M).Nonempty →
      partitionComplexity V P ≤ (p : ENat) →
      totalCondK T (codedUniformOn M hM).code
          (codedUniformOn A hA).code ≤ (s : ENat) →
      ∃ F, ∃ hF : F.Nonempty,
        (codedUniformOn A hA).code ∈ F ∧
        IsStrongSetModel T (codedUniformOn A hA).code F hF
          (c * (p + s) + c) ∧
        plainSetComplexity V F hF ≤
          plainSetComplexity V M hM +
            (c * p + logSlack c (finiteSetLogCard A) : ENat) ∧
        finiteSetLogCard F + finiteSetLogCard (A ∩ M) ≤
          finiteSetLogCard M + 2 := by
  obtain ⟨cPlain, hPlain⟩ :=
    plainSetComplexity_hereditaryFamily_le V hV
  obtain ⟨cStrong, hStrong⟩ := hereditaryFamily_isStrong V T hV hT
  let c := cPlain + cStrong
  refine ⟨c, ?_⟩
  intro P A hA M hM p s hPart hAP hinter hPcomp hMA
  let r := finiteSetLogCard (A ∩ M)
  let F := hereditaryFamily P M r
  have hmem : (codedUniformOn A hA).code ∈ F := by
    dsimp [F, r]
    exact hereditaryFamily_mem_code P A M hA hAP hinter
  have hF : F.Nonempty := ⟨(codedUniformOn A hA).code, hmem⟩
  refine ⟨F, hF, hmem, ?_, ?_, ?_⟩
  · have hs := hStrong P A hA M hM p s 0 hF hPcomp hMA
    refine hs.mono ?_
    rw [show logSlack cStrong 0 = cStrong by simp [logSlack]]
    dsimp [c]
    nlinarith [Nat.zero_le (cPlain * (p + s))]
  · have hrA : r ≤ finiteSetLogCard A := by
      dsimp [r]
      rw [finiteSetLogCard_le_iff]
      exact (Finset.card_le_card Finset.inter_subset_left).trans
        (finiteSetLogCard_spec A)
    refine (hPlain P M hM r hF p (finiteSetLogCard A) hPcomp hrA).trans ?_
    gcongr
    · dsimp [c]
      omega
    · exact_mod_cast logSlack_mono_left (show cPlain ≤ c by
        dsimp [c]
        omega) (finiteSetLogCard A)
  · dsimp [F, r]
    exact hereditaryFamily_card_add_intersection_le P A M hPart

end Kolmogorov
