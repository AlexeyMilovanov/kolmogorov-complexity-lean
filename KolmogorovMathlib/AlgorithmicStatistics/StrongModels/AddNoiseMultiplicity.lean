import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.AddNoiseGain
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.AddNoiseCandidates

namespace Kolmogorov

open Kolmogorov.CodedFiniteDistribution

/-- **Add-noise multiplicity composition.**
Compose the candidate-truncation cardinality lower bound
`noiseCandidateTruncations_card_lower_of_information_gain` with the packager
`manyIJDescriptions_of_noiseCandidateTruncations`.  Given a prefix `(i, j)`
model `B` containing `pairCode x y`, the conditional randomness premise
`|y| ≤ C(y | x) + epsilon`, and an exact information gain `k`
(`C(y | pairCode x A.code) + k ≤ |y|`, with `A = finiteSetFstTruncation B`),
`x` has `ManyIJDescriptions` of complexity `i + c0`, log-size `j`, and
multiplicity exponent `k - epsilon - logSlack c1 (|x|+|y|+i+j+k)`.  The two
constants are kept separate; the degenerate exponent-zero case is free because
the candidate family is nonempty. -/
theorem manyIJDescriptions_of_noise_information_gain
    (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U) :
    ∃ c0 c1 : ℕ, ∀ (x y : BitString) (epsilon i j k : ℕ) (B : Finset BitString)
      (_hB : B ∈ descriptionsWithComplexityLeAndSizeLe U i j)
      (hpair : pairCode x y ∈ B),
      (y.length : ENat) ≤ condK V y x + (epsilon : ENat) →
      condK V y (pairCode x
          (codedUniformOn (finiteSetFstTruncation B)
            ⟨x, finiteSetFstTruncation_mem hpair⟩).code) + (k : ENat) ≤
        (y.length : ENat) →
      ManyIJDescriptions U x (i + c0) j
        (k - epsilon - logSlack c1 (x.length + y.length + i + j + k)) := by
  obtain ⟨c1, hc1⟩ := noiseCandidateTruncations_card_lower_of_information_gain V U hV hU
  obtain ⟨c0, hc0⟩ := manyIJDescriptions_of_noiseCandidateTruncations U hU
  refine ⟨c0, c1, fun x y epsilon i j k B _hB hpair hrand hgain => ?_⟩
  apply hc0 x y.length i j
  exact hc1 x y epsilon i j k B _hB hpair hrand hgain

/-- Clamp the multiplicity exponent supplied by the gain theorem to the
complexity budget required by
`exists_description_smaller_complexity_of_many_logSlack`.  This loses no
usable multiplicity and packages the side condition with the witness. -/
theorem manyIJDescriptions_clamped_of_noise_information_gain
    (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U) :
    ∃ c0 c1 : ℕ, ∀ (x y : BitString) (epsilon i j k : ℕ) (B : Finset BitString)
      (_hB : B ∈ descriptionsWithComplexityLeAndSizeLe U i j)
      (hpair : pairCode x y ∈ B),
      (y.length : ENat) ≤ condK V y x + (epsilon : ENat) →
      condK V y (pairCode x
          (codedUniformOn (finiteSetFstTruncation B)
            ⟨x, finiteSetFstTruncation_mem hpair⟩).code) + (k : ENat) ≤
        (y.length : ENat) →
      let gain := k - epsilon -
        logSlack c1 (x.length + y.length + i + j + k)
      ManyIJDescriptions U x (i + c0) j (min gain (i + c0)) ∧
        min gain (i + c0) ≤ i + c0 := by
  obtain ⟨c0, c1, hc⟩ :=
    manyIJDescriptions_of_noise_information_gain V U hV hU
  refine ⟨c0, c1, ?_⟩
  intro x y epsilon i j k B hB hpair hrand hgain
  let gain := k - epsilon -
    logSlack c1 (x.length + y.length + i + j + k)
  have hmany : ManyIJDescriptions U x (i + c0) j gain :=
    hc x y epsilon i j k B hB hpair hrand hgain
  exact ⟨hmany.mono_k (Nat.min_le_left gain (i + c0)),
    Nat.min_le_right gain (i + c0)⟩

theorem inDescriptionProfile_of_noise_information_gain
    (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U) :
  ∃ c0 c1 c2 : ℕ, ∀ (x y : BitString) (epsilon i j k : ℕ) (B : Finset BitString)
    (_hB : B ∈ descriptionsWithComplexityLeAndSizeLe U i j)
    (hpair : pairCode x y ∈ B),
    (y.length : ENat) ≤ condK V y x + (epsilon : ENat) →
    condK V y
        (pairCode x
          (codedUniformOn (finiteSetFstTruncation B)
            ⟨x, finiteSetFstTruncation_mem hpair⟩).code) + (k : ENat)
      ≤ (y.length : ENat) →
    let gain :=
      k - epsilon -
        logSlack c1 (x.length + y.length + i + j + k)
    let r := min gain (i + c0)
    InDescriptionProfile U x
      ((i + c0) - r +
        logSlack c2 (x.length + (i + c0) + j))
      (j + logSlack c2 (x.length + (i + c0) + j)) := by
  obtain ⟨c0, c1, hc⟩ := manyIJDescriptions_clamped_of_noise_information_gain V U hV hU
  have h_comp := exists_description_smaller_complexity_of_many_logSlack U hU
  obtain ⟨c2, hc2⟩ := h_comp
  refine ⟨c0, c1, c2, fun x y epsilon i j k B hB hpair hrand hgain => ?_⟩
  let gain := k - epsilon - logSlack c1 (x.length + y.length + i + j + k)
  let r := min gain (i + c0)
  obtain ⟨hmany, hr⟩ := hc x y epsilon i j k B hB hpair hrand hgain
  exact hc2 x x.length (i + c0) j r rfl hmany hr

end Kolmogorov
