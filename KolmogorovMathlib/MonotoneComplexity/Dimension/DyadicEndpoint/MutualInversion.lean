import KolmogorovMathlib.MonotoneComplexity.Dimension.DyadicEndpoint.GapCover
import KolmogorovMathlib.MonotoneComplexity.Dimension.DyadicEndpoint.MapTotality
import KolmogorovMathlib.MonotoneComplexity.Dimension.ArithmeticStreamMap
import KolmogorovMathlib.MonotoneComplexity.LevinSchnorr.Basic

/-!
# The interval maps invert each other on random sequences

`invArithMap_arithMap_of_isMartinLofRandom` completes the pair of inversion identities: on the
sequences that are random for the uniform measure, the reverse interval map undoes the forward
one. Together with the opposite identity proved with the totality statements, this makes the two
maps mutually inverse between the random sequences of `μ` and those of the uniform measure.

Source: SUV §5.9.1, Theorem 121.
-/

namespace Kolmogorov
open MeasureTheory
open scoped ENNReal

/-- **The reverse map inverts the forward map on the uniformly random sequences**
(SUV Theorem 121, the fourth conjunct of obligation (c)). -/
theorem invArithMap_arithMap_of_isMartinLofRandom (μ : Measure CantorSeq)
    [IsProbabilityMeasure μ] (hμ : IsComputableMeasure μ) (haμ : ∀ u : CantorSeq, μ {u} = 0)
    {v : CantorSeq} (hv : IsMartinLofRandom uniformMeasure v) :
    invArithMap μ (arithMap μ (BitStream.infinite v)) = BitStream.infinite v := by
  obtain ⟨u, hu⟩ := exists_infinite_arithMap_of_isMartinLofRandom μ hμ hv
  rw [hu]
  have hreal : measureReal μ u = treeReal lengthMeasure v :=
    measureReal_arithMap_eq_treeReal μ haμ hu
  -- the real is strictly inside every dyadic cell along `v`
  have hstrict : ∀ j : ℕ, treeLeftEnd lengthMeasure (cantorPrefix v j) < treeReal lengthMeasure v ∧
      treeReal lengthMeasure v < treeLeftEnd lengthMeasure (cantorPrefix v j)
        + (lengthMeasure (cantorPrefix v j)).toReal := by
    intro j
    have hL := treeLeftEnd_le_measureReal uniformMeasure v j
    have hR := measureReal_le_treeRightEnd uniformMeasure v j
    rw [cantorMass_uniformMeasure_eq_lengthMeasure] at hL hR
    simp only [measureReal_eq_treeReal, cantorMass_uniformMeasure_eq_lengthMeasure] at hL hR
    rw [treeLeftEnd_lengthMeasure_eq_div, lengthMeasure_toReal, cantorPrefix_length]
    rw [treeLeftEnd_lengthMeasure_eq_div, cantorPrefix_length] at hL
    rw [treeLeftEnd_lengthMeasure_eq_div, lengthMeasure_toReal, cantorPrefix_length] at hR
    have hd1 := treeReal_lengthMeasure_ne_div_two_pow hv j (devBitsToNat (cantorPrefix v j))
    have hd2 := treeReal_lengthMeasure_ne_div_two_pow hv j (devBitsToNat (cantorPrefix v j) + 1)
    have hsplit : ((devBitsToNat (cantorPrefix v j) : ℕ) + 1 : ℕ) / (2 : ℝ) ^ j
        = (devBitsToNat (cantorPrefix v j) : ℝ) / 2 ^ j + ((2 : ℝ)⁻¹) ^ j := by
      push_cast
      rw [inv_pow]
      field_simp
    rw [hsplit] at hd2
    constructor
    · exact lt_of_le_of_ne hL (Ne.symm hd1)
    · exact lt_of_le_of_ne hR hd2
  have hmuL : ∀ n : ℕ,
      treeLeftEnd (cantorMass μ) (cantorPrefix u n) ≤ treeReal lengthMeasure v := by
    intro n
    rw [← hreal]
    exact treeLeftEnd_le_measureReal μ u n
  have hmuR : ∀ n : ℕ, treeReal lengthMeasure v
      ≤ treeLeftEnd (cantorMass μ) (cantorPrefix u n)
        + (cantorMass μ (cantorPrefix u n)).toReal := by
    intro n
    rw [← hreal]
    exact measureReal_le_treeRightEnd μ u n
  have hL := tendsto_treeLeftEnd_measureReal μ u
  have hR := tendsto_treeRightEnd_measureReal μ (haμ u)
  rw [hreal] at hL hR
  refine BitStream.eq_of_forall_finite_le_iff _ _ (fun p => ?_)
  constructor
  · intro hle
    rw [streamLowerGraph_invArithMap_infinite] at hle
    obtain ⟨n, hn⟩ := hle
    rcases hn with hnil | hsub
    · subst hnil
      exact fun i hi => absurd hi (by simp)
    have hrmem : treeReal lengthMeasure v ∈ treeIcc (cantorMass μ) (cantorPrefix u n) := by
      rw [treeIcc, Set.mem_Icc]
      exact ⟨hmuL n, hmuR n⟩
    have hint := hsub hrmem
    rw [treeIco, interior_Ico, Set.mem_Ioo] at hint
    have h1 : treeReal lengthMeasure v ∈ treeIco lengthMeasure p := by
      rw [treeIco, Set.mem_Ico]
      exact ⟨hint.1.le, hint.2⟩
    have h2 : treeReal lengthMeasure v ∈ treeIco lengthMeasure (cantorPrefix v p.length) := by
      rw [treeIco, Set.mem_Ico]
      exact ⟨(hstrict p.length).1.le, (hstrict p.length).2⟩
    have heq : p = cantorPrefix v p.length := by
      rcases prefix_or_prefix_of_mem_treeIco lengthMeasure_isContinuousTreeSemimeasure h1 h2
        with h | h
      · exact h.eq_of_length (by rw [cantorPrefix_length])
      · exact (h.eq_of_length (by rw [cantorPrefix_length])).symm
    rw [heq]
    exact finite_cantorPrefix_le_infinite v p.length
  · intro hle
    have hpv : cantorPrefix v p.length = p := (isCantorPrefix_iff_cantorPrefix_eq p v).1 hle
    rw [streamLowerGraph_invArithMap_infinite]
    have hs := hstrict p.length
    rw [hpv] at hs
    have e1 : ∀ᶠ n in Filter.atTop, treeLeftEnd lengthMeasure p
        < treeLeftEnd (cantorMass μ) (cantorPrefix u n) :=
      hL.eventually (eventually_gt_nhds hs.1)
    have e2 : ∀ᶠ n in Filter.atTop, treeLeftEnd (cantorMass μ) (cantorPrefix u n)
        + (cantorMass μ (cantorPrefix u n)).toReal
        < treeLeftEnd lengthMeasure p + (lengthMeasure p).toReal :=
      hR.eventually (eventually_lt_nhds hs.2)
    obtain ⟨n, hn1, hn2⟩ := (e1.and e2).exists
    refine ⟨n, Or.inr ?_⟩
    rw [treeIco, interior_Ico]
    intro z hz
    rw [treeIcc, Set.mem_Icc] at hz
    exact ⟨lt_of_lt_of_le hn1 hz.1, lt_of_le_of_lt hz.2 hn2⟩

end Kolmogorov
