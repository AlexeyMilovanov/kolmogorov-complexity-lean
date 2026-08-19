import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.AddNoiseTruncation
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.ImprovingDescriptions

/-!
# Candidate truncations for the direct add-noise route

Given a string `x`, a noise length `l`, and description parameters `i, j`, we
enumerate the canonical first-coordinate truncations of all `(i,j)`-descriptions
that contain a pair code `⟨x, y⟩` for some noise string `y` of length `l`.

The two results here are the soundness of that enumeration (each candidate is a
nonempty set containing `x`, of size at most `2 ^ j`, whose set complexity is
`i + O(1)`) and the packaging of a cardinality lower bound for the enumeration
as a `ManyIJDescriptions` statement with the same additive constant.
-/

namespace Kolmogorov

open Kolmogorov.CodedFiniteDistribution

/-- The canonical first-coordinate truncations of all `(i,j)`-descriptions that
contain a pair code `⟨x, y⟩` with `y` of length `l`. -/
noncomputable def noiseCandidateTruncations
    (U : Map) (x : BitString) (l i j : Nat) :
    Finset (Finset BitString) :=
  ((descriptionsWithComplexityLeAndSizeLe U i j).filter
    (fun B => ∃ y ∈ stringsOfLength l, pairCode x y ∈ B)).image
      finiteSetFstTruncation

/-- Every candidate truncation is a nonempty set containing `x`, of cardinality
at most `2 ^ j`, whose set complexity exceeds the description bound `i` only by
a uniform additive constant. -/
theorem noiseCandidateTruncations_sound
    (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : Nat, ∀ x l i j A,
      A ∈ noiseCandidateTruncations U x l i j →
      ∃ hA : A.Nonempty,
        x ∈ A ∧
        setComplexity U A hA ≤ (i + c : ENat) ∧
        A.card ≤ 2 ^ j := by
  obtain ⟨c₀, hc₀⟩ := setComplexity_le_of_mem_descriptionsWithComplexityLe U
  obtain ⟨c₁, hc₁⟩ := finiteSetFstTruncation_setComplexity_le U hU
  refine ⟨c₀ + c₁, ?_⟩
  intro x l i j A hA
  rw [noiseCandidateTruncations, Finset.mem_image] at hA
  obtain ⟨B, hB, rfl⟩ := hA
  rw [Finset.mem_filter] at hB
  obtain ⟨hBmem, y, _, hpair⟩ := hB
  have hxA : x ∈ finiteSetFstTruncation B := finiteSetFstTruncation_mem hpair
  have hAne : (finiteSetFstTruncation B).Nonempty := ⟨x, hxA⟩
  have hBne : B.Nonempty := ⟨pairCode x y, hpair⟩
  have hBcard : B.card ≤ 2 ^ j :=
    (Finset.mem_filter.mp hBmem).2
  refine ⟨hAne, hxA, ?_, ?_⟩
  · have h1 : setComplexity U (finiteSetFstTruncation B) hAne ≤
        setComplexity U B hBne + (c₁ : ENat) := hc₁ B hBne
    have h2 : setComplexity U B hBne ≤ (i + c₀ : ENat) :=
      hc₀ i B hBne (Finset.mem_filter.mp hBmem).1
    refine h1.trans ?_
    calc setComplexity U B hBne + (c₁ : ENat) ≤ (i + c₀ : ENat) + (c₁ : ENat) :=
          add_le_add h2 le_rfl
      _ = (i + (c₀ + c₁) : ENat) := by ring
  · exact le_trans (finiteSetFstTruncation_card_le B) hBcard

/-- A cardinality lower bound for the candidate truncations packages directly as
a `ManyIJDescriptions` statement, with the complexity parameter shifted by a
uniform additive constant. -/
theorem manyIJDescriptions_of_noiseCandidateTruncations
    (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : Nat, ∀ x l i j k,
      2 ^ k ≤ (noiseCandidateTruncations U x l i j).card →
      ManyIJDescriptions U x (i + c) j k := by
  obtain ⟨c, hc⟩ := noiseCandidateTruncations_sound U hU
  refine ⟨c, ?_⟩
  intro x l i j k hk
  refine hk.trans (Finset.card_le_card ?_)
  intro A hA
  obtain ⟨hAne, hxA, hcomp, hcard⟩ := hc x l i j A hA
  rw [Finset.mem_filter]
  refine ⟨?_, hxA⟩
  rw [descriptionsWithComplexityLeAndSizeLe, Finset.mem_filter]
  refine ⟨mem_descriptionsWithComplexityLe_of_complexity hAne ?_, hcard⟩
  exact hcomp.trans_eq (by push_cast; ring)

end Kolmogorov
