import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.ChargedHeavyNoiseRank
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.ChargedHeavyNoiseComplexity

/-!
# Raw (unclamped) charged accounting for the heavy noise candidates

The charged heavy candidate family of `ChargedHeavyNoiseCandidates.lean` is
usually accessed through a *stratum*, whose size coordinate is clamped to the
ambient budget.  The clamping is what keeps the rank program short, but it also
prevents the family from being used at size coordinates exceeding the budget.

This file redoes the two central charged estimates for the *raw* family
`chargedHeavyNoiseCandidatesRaw`, where the size coordinate `j` is an arbitrary
natural number and is charged explicitly, as the summand
`2 * (Nat.bits j).length`, in the rank bound.  The complexity coordinate is
still assumed bounded by the budget and the fibre threshold by the noise
length, since those are the only hypotheses the decoder actually needs.
-/

namespace Kolmogorov

open Nat.Partrec (Code)
open Kolmogorov.CodedFiniteDistribution

/-- Length bound for the packed charged rank program when the size coordinate
`j` is *not* clamped: it is charged explicitly as `2 * (Nat.bits j).length`. -/
theorem chargedHeavyRankProgramRaw_length_slack (C : ℕ)
    (noiseLen baseBudget thr i j k r : ℕ)
    (hthr : thr ≤ noiseLen) (hi : i ≤ baseBudget) (hrk : r < 2 ^ k) :
    (chargedHeavyRankProgram noiseLen thr i j k r).length + C ≤
      k + 2 * (Nat.bits j).length + logSlack (6 + C) baseBudget
        + logSlack (6 + C) noiseLen := by
  have hthrW : (Nat.bits thr).length ≤ (Nat.bits noiseLen).length := length_natBits_mono hthr
  have hiW : (Nat.bits i).length ≤ (Nat.bits baseBudget).length := length_natBits_mono hi
  have h1 : logSlack (6 + C) baseBudget =
      (6 + C) * (Nat.bits baseBudget).length + (6 + C) := rfl
  have h2 : logSlack (6 + C) noiseLen =
      (6 + C) * (Nat.bits noiseLen).length + (6 + C) := rfl
  have hb : 6 * (Nat.bits baseBudget).length ≤ (6 + C) * (Nat.bits baseBudget).length :=
    Nat.mul_le_mul_right _ (by omega)
  have hn : 6 * (Nat.bits noiseLen).length ≤ (6 + C) * (Nat.bits noiseLen).length :=
    Nat.mul_le_mul_right _ (by omega)
  rw [length_chargedHeavyRankProgram noiseLen thr i j k r hrk, h1, h2]
  omega

/-- **Raw charged rank compression.**  When `x` has fewer than `2 ^ k` raw
charged heavy candidates at noise length `noiseLen`, complexity coordinate
`i ≤ baseBudget`, size coordinate `j` and fibre threshold `threshold ≤ noiseLen`,
every such candidate has conditional plain complexity at most `k`, plus an
explicit charge `2 * (Nat.bits j).length` for the unbounded size stratum, plus
slack logarithmic in `baseBudget` and `noiseLen`, given `x`.

No term depends on `|x|`. -/
theorem condK_chargedHeavyCandidateRaw_of_card_lt_pow
    (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (noiseLen baseBudget i j threshold k : ℕ)
      (H : Finset BitString) (hH : H.Nonempty),
      i ≤ baseBudget →
      threshold ≤ noiseLen →
      H ∈ chargedHeavyNoiseCandidatesRaw U x noiseLen i j threshold →
      (chargedHeavyNoiseCandidatesRaw U x noiseLen i j threshold).card < 2 ^ k →
      condK V (codedUniformOn H hH).code x ≤
        ((k + 2 * (Nat.bits j).length + logSlack c baseBudget
          + logSlack c noiseLen : ℕ) : ENat) := by
  obtain ⟨cU, hcU⟩ : ∃ cU : Code, IsCodeFor cU U :=
    Nat.Partrec.Code.exists_code.mp hU.1.1
  obtain ⟨C, hC⟩ := condK_partrec_cond_map_le V hV (chargedHeavyRankDecoder cU)
    (chargedHeavyRankDecoder_partrec cU)
  refine ⟨6 + C, ?_⟩
  intro x noiseLen baseBudget i j threshold k H hH hi hthr hmem hcard
  obtain ⟨_, _, hiff, hlen⟩ := chargedHeavyAppearanceCodes_spec hcU
  obtain ⟨t, ht⟩ := (hiff x noiseLen i j threshold H).mp hmem
  rw [canonicalUniformCodeOfList_canonicalFinsetList H hH] at ht
  obtain ⟨r, hr, hget⟩ :
      ∃ r, r < (chargedHeavyAppearanceCodes cU x noiseLen i j threshold t).length ∧
        (chargedHeavyAppearanceCodes cU x noiseLen i j threshold t).getD r [] =
          (codedUniformOn H hH).code := by
    rw [List.mem_iff_getElem] at ht
    obtain ⟨r, hr, hget⟩ := ht
    exact ⟨r, hr, by simp [List.getD_eq_getElem?_getD, hr, hget]⟩
  have hrk : r < 2 ^ k :=
    lt_of_lt_of_le hr ((hlen x noiseLen i j threshold t).trans_lt hcard).le
  have hmemdec : (codedUniformOn H hH).code ∈
      chargedHeavyRankDecoder cU x (chargedHeavyRankProgram noiseLen threshold i j k r) :=
    mem_chargedHeavyRankDecoder_of_rank cU x noiseLen i j threshold k r t hr hget
  have hbound := hC x (chargedHeavyRankProgram noiseLen threshold i j k r) _ hmemdec
  have hslack := chargedHeavyRankProgramRaw_length_slack C noiseLen baseBudget threshold i j k r
    hthr hi hrk
  calc condK V (codedUniformOn H hH).code x
      ≤ ((chargedHeavyRankProgram noiseLen threshold i j k r).length : ENat) + (C : ENat) :=
        hbound
    _ = (((chargedHeavyRankProgram noiseLen threshold i j k r).length + C : ℕ) : ENat) := by
        norm_cast
    _ ≤ ((k + 2 * (Nat.bits j).length + logSlack (6 + C) baseBudget
          + logSlack (6 + C) noiseLen : ℕ) : ENat) := by exact_mod_cast hslack

/-! ### Raw charged multiplicity -/

/-- Raw form of the charged set-complexity estimate: every raw charged heavy
candidate at threshold `threshold ≤ noiseLen` is a description of `x` whose set
complexity exceeds `i` by at most slack logarithmic in the noise length. -/
theorem chargedHeavyNoiseCandidatesRaw_setComplexity_le
    (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (noiseLen i j threshold : ℕ)
      (H : Finset BitString) (hH : H.Nonempty),
      threshold ≤ noiseLen →
      H ∈ chargedHeavyNoiseCandidatesRaw U x noiseLen i j threshold →
      setComplexity U H hH ≤ ((i + logSlack c noiseLen : ℕ) : ENat) := by
  obtain ⟨c₀, hc₀⟩ := setComplexity_le_of_mem_descriptionsWithComplexityLe U
  obtain ⟨c₁, hc₁⟩ := finiteSetFstHeavyTruncation_setComplexity_le U hU
  refine ⟨c₀ + c₁, ?_⟩
  intro x noiseLen i j threshold H hH hthr hmem
  obtain ⟨B, hBdesc, ⟨y, _, hpair⟩, _, rfl⟩ := mem_chargedHeavyNoiseCandidatesRaw_iff.mp hmem
  have hBne : B.Nonempty := ⟨pairCode x y, hpair⟩
  have h1 : setComplexity U (finiteSetFstHeavyTruncation B threshold) hH ≤
      setComplexity U B hBne + (logSlack c₁ threshold : ENat) := hc₁ B hBne threshold hH
  have h2 : setComplexity U B hBne ≤ (i + c₀ : ENat) :=
    hc₀ i B hBne (Finset.mem_filter.mp hBdesc).1
  have hmono : logSlack c₁ threshold ≤ logSlack c₁ noiseLen := by
    unfold logSlack
    exact Nat.add_le_add_right
      (Nat.mul_le_mul_left _ (length_natBits_mono hthr)) _
  have hnum : c₀ + logSlack c₁ noiseLen ≤ logSlack (c₀ + c₁) noiseLen := by
    unfold logSlack
    have : c₁ * (Nat.bits noiseLen).length ≤ (c₀ + c₁) * (Nat.bits noiseLen).length :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  have hfinal : (i : ENat) + (c₀ : ENat) + (logSlack c₁ noiseLen : ENat) ≤
      ((i + logSlack (c₀ + c₁) noiseLen : ℕ) : ENat) := by
    have hnat : i + c₀ + logSlack c₁ noiseLen ≤ i + logSlack (c₀ + c₁) noiseLen := by omega
    calc (i : ENat) + (c₀ : ENat) + (logSlack c₁ noiseLen : ENat)
        = ((i + c₀ + logSlack c₁ noiseLen : ℕ) : ENat) := by push_cast; ring
      _ ≤ ((i + logSlack (c₀ + c₁) noiseLen : ℕ) : ENat) := by exact_mod_cast hnat
  refine le_trans h1 (le_trans (add_le_add h2 ?_) hfinal)
  exact_mod_cast hmono

/-- **Raw charged multiplicity packaging.**  A cardinality lower bound for the
raw charged heavy candidates of `x` yields `2 ^ k` genuine
`(i + logSlack c noiseLen, j - threshold + 1)`-descriptions of `x`.  No term
depends on `x.length`, and the size coordinate `j` is unrestricted. -/
theorem manyIJDescriptions_of_chargedHeavyNoiseCandidatesRaw
    (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (noiseLen i j threshold k : ℕ),
      threshold ≤ noiseLen →
      2 ^ k ≤ (chargedHeavyNoiseCandidatesRaw U x noiseLen i j threshold).card →
      ManyIJDescriptions U x (i + logSlack c noiseLen) (j - threshold + 1) k := by
  obtain ⟨c, hc⟩ := chargedHeavyNoiseCandidatesRaw_setComplexity_le U hU
  refine ⟨c, ?_⟩
  intro x noiseLen i j threshold k hthr hk
  refine hk.trans (Finset.card_le_card ?_)
  intro H hH
  have hxH : x ∈ H := mem_of_mem_chargedHeavyNoiseCandidatesRaw hH
  have hHne : H.Nonempty := ⟨x, hxH⟩
  have hcard : H.card ≤ 2 ^ (j - threshold + 1) :=
    card_le_of_mem_chargedHeavyNoiseCandidatesRaw hH
  rw [Finset.mem_filter]
  refine ⟨?_, hxH⟩
  rw [descriptionsWithComplexityLeAndSizeLe, Finset.mem_filter]
  exact ⟨mem_descriptionsWithComplexityLe_of_complexity hHne
    (hc x noiseLen i j threshold H hHne hthr hH), hcard⟩

end Kolmogorov
