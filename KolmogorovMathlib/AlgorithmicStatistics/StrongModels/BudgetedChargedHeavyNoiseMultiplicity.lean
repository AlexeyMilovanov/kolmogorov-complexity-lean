import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.BudgetedChargedHeavyNoiseGain

/-!
# Packaging the pooled charged-heavy multiplicity as `ManyIJDescriptions`

`BudgetedChargedHeavyNoiseGain.lean` ends with
`exists_budgetedChargedHeavyAppearanceCodes_many_of_information_gain`: exact
conditional information gain from the true heavy truncation forces some finite
stage of the *pooled* appearance enumeration to list exponentially many distinct
truncation codes, with an exponent that pays only logarithmic slack in the
visible budget and the noise length — in particular no `j` term.

The step recorded here is the combinatorial half that the header of that module
asks for: turning such a stage into a genuine `ManyIJDescriptions` certificate
with *common* complexity and size coordinates.

* `pooledChargedHeavyNoiseCandidates_setComplexity_le` — the complexity
  coordinate is uniform over the whole pool: every pooled candidate, whatever
  stratum it comes from and however large that stratum's raw size coordinate is,
  is a description of `x` of prefix set complexity at most
  `baseBudget + logSlack c noiseLen`.  Only the *complexity* coordinate of a
  stratum is clamped in `pooledChargedHeavyNoiseCandidates`, and that clamp is
  exactly what makes this bound free of `j`.
* `manyIJDescriptions_of_pooled_family` — consequently any finite collection of
  pooled candidates all of whose members have at most `2 ^ J` elements packages
  as `ManyIJDescriptions U x (baseBudget + logSlack c noiseLen) J k`, where
  `2 ^ k` is a lower bound for the size of the collection.
* `manyIJDescriptions_of_budgetedChargedHeavyAppearanceCodes` — the same
  statement read off the enumeration itself: the codes listed at a stage that
  decode to sets of at most `2 ^ J` elements are pairwise distinct descriptions
  of `x`, so a lower bound on the length of that size-filtered sublist is a
  `ManyIJDescriptions` certificate.

The size coordinate is therefore the only coordinate of the pooled route that
still has to be controlled: the complexity coordinate is already budget scale.

Nothing here assumes an open statement, and no frozen interface is edited.  Note
that these are reusable packaging lemmas for the pooled charged-heavy family, not
a step of the unconditional `prop:upward` chain: as recorded at the end of
`BudgetedPairProjectionMany.lean`, the pair-projection consumer
`BudgetedPairProjectionManyStatement` is refuted there, and the critical path
runs through the plain corner instead.
-/

namespace Kolmogorov

open Kolmogorov.CodedFiniteDistribution

open Nat.Partrec (Code)

/-- **Budget-scale complexity of a pooled candidate.**  Every member of
`pooledChargedHeavyNoiseCandidates U x noiseLen baseBudget stratum` is a
description of `x` whose prefix set complexity is at most
`baseBudget + logSlack c noiseLen`, uniformly in the stratum.

Only the complexity coordinate of the stratum enters, and it is clamped to
`baseBudget`; the raw size coordinate, which the pooled family leaves
unrestricted, plays no role. -/
theorem pooledChargedHeavyNoiseCandidates_setComplexity_le
    (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (noiseLen baseBudget : ℕ) (stratum : BitString)
      (H : Finset BitString) (hH : H.Nonempty),
      H ∈ pooledChargedHeavyNoiseCandidates U x noiseLen baseBudget stratum →
      setComplexity U H hH ≤ ((baseBudget + logSlack c noiseLen : ℕ) : ENat) := by
  obtain ⟨c₀, hc₀⟩ := setComplexity_le_of_mem_descriptionsWithComplexityLe U
  obtain ⟨c₁, hc₁⟩ := finiteSetFstHeavyTruncation_setComplexity_le U hU
  refine ⟨c₀ + c₁, ?_⟩
  intro x noiseLen baseBudget stratum H hH hmem
  rw [pooledChargedHeavyNoiseCandidates] at hmem
  set i := stratumComplexity baseBudget stratum with hi
  set thr := stratumThreshold noiseLen stratum with hthr
  obtain ⟨B, hBdesc, ⟨y, _, hpair⟩, _, rfl⟩ := mem_chargedHeavyNoiseCandidatesRaw_iff.mp hmem
  have hBne : B.Nonempty := ⟨pairCode x y, hpair⟩
  have h1 : setComplexity U (finiteSetFstHeavyTruncation B thr) hH ≤
      setComplexity U B hBne + (logSlack c₁ thr : ENat) := hc₁ B hBne thr hH
  have h2 : setComplexity U B hBne ≤ (i + c₀ : ENat) :=
    hc₀ i B hBne (Finset.mem_filter.mp hBdesc).1
  have hmono : logSlack c₁ thr ≤ logSlack c₁ noiseLen := by
    unfold logSlack
    exact Nat.add_le_add_right
      (Nat.mul_le_mul_left _ (length_natBits_mono (stratumThreshold_le noiseLen stratum))) _
  have hiB : i ≤ baseBudget := stratumComplexity_le baseBudget stratum
  have hfinal : (i : ENat) + (c₀ : ENat) + (logSlack c₁ noiseLen : ENat) ≤
      ((baseBudget + logSlack (c₀ + c₁) noiseLen : ℕ) : ENat) := by
    have hnum : i + c₀ + logSlack c₁ noiseLen ≤
        baseBudget + logSlack (c₀ + c₁) noiseLen := by
      unfold logSlack
      have : c₁ * (Nat.bits noiseLen).length ≤ (c₀ + c₁) * (Nat.bits noiseLen).length :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    calc (i : ENat) + (c₀ : ENat) + (logSlack c₁ noiseLen : ENat)
        = ((i + c₀ + logSlack c₁ noiseLen : ℕ) : ENat) := by push_cast; ring
      _ ≤ ((baseBudget + logSlack (c₀ + c₁) noiseLen : ℕ) : ENat) := by exact_mod_cast hnum
  refine le_trans h1 (le_trans (add_le_add h2 ?_) hfinal)
  exact_mod_cast hmono

/-- **Pooled multiplicity packaging.**  A finite collection `S` of pooled
charged-heavy candidates of `x`, each of cardinality at most `2 ^ J`, with
`2 ^ k ≤ #S`, is a `ManyIJDescriptions` certificate for `x` at the budget-scale
complexity coordinate `baseBudget + logSlack c noiseLen` and size coordinate `J`.

Different members of `S` may come from different strata, and their strata may
have arbitrarily large raw size coordinates: the complexity coordinate of the
certificate depends only on `baseBudget` and `noiseLen`. -/
theorem manyIJDescriptions_of_pooled_family
    (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (noiseLen baseBudget J k : ℕ)
      (S : Finset (Finset BitString)),
      (∀ H ∈ S, (∃ stratum : BitString,
          H ∈ pooledChargedHeavyNoiseCandidates U x noiseLen baseBudget stratum) ∧
        H.card ≤ 2 ^ J) →
      2 ^ k ≤ S.card →
      ManyIJDescriptions U x (baseBudget + logSlack c noiseLen) J k := by
  classical
  obtain ⟨c, hc⟩ := pooledChargedHeavyNoiseCandidates_setComplexity_le U hU
  refine ⟨c, ?_⟩
  intro x noiseLen baseBudget J k S hS hk
  refine hk.trans (Finset.card_le_card ?_)
  intro H hH
  obtain ⟨⟨stratum, hstratum⟩, hcard⟩ := hS H hH
  have hxH : x ∈ H := mem_of_mem_chargedHeavyNoiseCandidatesRaw hstratum
  have hHne : H.Nonempty := ⟨x, hxH⟩
  rw [Finset.mem_filter]
  refine ⟨?_, hxH⟩
  rw [descriptionsWithComplexityLeAndSizeLe, Finset.mem_filter]
  exact ⟨mem_descriptionsWithComplexityLe_of_complexity hHne
    (hc x noiseLen baseBudget stratum H hHne hstratum), hcard⟩

/-- **The size filter is a visible stratum gate.**  A pooled candidate coming
from a stratum whose raw size coordinate exceeds its fibre threshold by at most
`J - 1` has at most `2 ^ J` elements, because the heavy truncation trades the
size bound of the originating description for the heavy-fibre count.

Hence the size hypothesis of `manyIJDescriptions_of_pooled_family` can be read
off the strata alone, without decoding the candidates. -/
theorem manyIJDescriptions_of_pooled_family_of_gap
    (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (noiseLen baseBudget J k : ℕ)
      (S : Finset (Finset BitString)),
      (∀ H ∈ S, ∃ stratum : BitString,
          H ∈ pooledChargedHeavyNoiseCandidates U x noiseLen baseBudget stratum ∧
          stratumSizeRaw stratum - stratumThreshold noiseLen stratum + 1 ≤ J) →
      2 ^ k ≤ S.card →
      ManyIJDescriptions U x (baseBudget + logSlack c noiseLen) J k := by
  obtain ⟨c, hc⟩ := manyIJDescriptions_of_pooled_family U hU
  refine ⟨c, ?_⟩
  intro x noiseLen baseBudget J k S hS hk
  refine hc x noiseLen baseBudget J k S ?_ hk
  intro H hH
  obtain ⟨stratum, hstratum, hgap⟩ := hS H hH
  refine ⟨⟨stratum, hstratum⟩, ?_⟩
  refine (card_le_of_mem_chargedHeavyNoiseCandidatesRaw hstratum).trans ?_
  exact Nat.pow_le_pow_right (by decide) hgap

/-- **From the pooled enumeration to a multiplicity certificate.**  At any stage
`t` of the pooled appearance enumeration, the listed codes that decode to sets of
at most `2 ^ J` elements are codes of pairwise distinct descriptions of `x`, each
of prefix set complexity at most `baseBudget + logSlack c noiseLen`.  Hence a
lower bound `2 ^ k` on the length of that size-filtered sublist yields
`ManyIJDescriptions U x (baseBudget + logSlack c noiseLen) J k`.

This is the combinatorial half of the pooled route: the complexity coordinate of
the certificate is budget scale and free of the size coordinate `j` of the
originating pair descriptions; only the explicit size filter remains to be
supplied by the caller. -/
theorem manyIJDescriptions_of_budgetedChargedHeavyAppearanceCodes
    (U : Map) (hU : IsOptimalPrefixConditional U) {cU : Code} (hcU : IsCodeFor cU U) :
    ∃ c : ℕ, ∀ (x : BitString) (noiseLen baseBudget t J k : ℕ),
      2 ^ k ≤ ((budgetedChargedHeavyAppearanceCodes cU x noiseLen baseBudget t).filter
          (fun w => decide (((codeSupportList w).toFinset).card ≤ 2 ^ J))).length →
      ManyIJDescriptions U x (baseBudget + logSlack c noiseLen) J k := by
  classical
  obtain ⟨c, hc⟩ := manyIJDescriptions_of_pooled_family U hU
  refine ⟨c, ?_⟩
  intro x noiseLen baseBudget t J k hk
  set L := budgetedChargedHeavyAppearanceCodes cU x noiseLen baseBudget t with hL
  set L' := L.filter (fun w => decide (((codeSupportList w).toFinset).card ≤ 2 ^ J)) with hL'
  have hLnodup : L.Nodup := budgetedChargedHeavyAppearanceCodes_nodup cU x noiseLen baseBudget t
  have hsub : L' ⊆ L := by
    intro w hw
    exact (List.mem_filter.mp hw).1
  have hL'nodup : L'.Nodup := hLnodup.filter _
  -- Each listed code decodes to a pooled candidate.
  have hmaps : ∀ w ∈ L, ∃ stratum : BitString,
      (codeSupportList w).toFinset ∈
        pooledChargedHeavyNoiseCandidates U x noiseLen baseBudget stratum := by
    intro w hw
    obtain ⟨s, _, hs⟩ := exists_stage_of_mem_budgetedChargedHeavyAppearanceCodes hw
    rw [budgetedChargedHeavyTruncationCodes, List.mem_flatMap] at hs
    obtain ⟨stratum, _, hs_stratum⟩ := hs
    obtain ⟨H, _, hHmem, _, hdec⟩ := mem_chargedHeavyTruncationCodes_sound hcU hs_stratum
    exact ⟨stratum, by rw [hdec]; exact hHmem⟩
  -- Distinct codes decode to distinct sets.
  have hinj : ∀ w₁ ∈ L, ∀ w₂ ∈ L,
      (codeSupportList w₁).toFinset = (codeSupportList w₂).toFinset → w₁ = w₂ := by
    intro w₁ hw₁ w₂ hw₂ heq
    obtain ⟨s₁, _, hs₁⟩ := exists_stage_of_mem_budgetedChargedHeavyAppearanceCodes hw₁
    obtain ⟨s₂, _, hs₂⟩ := exists_stage_of_mem_budgetedChargedHeavyAppearanceCodes hw₂
    rw [budgetedChargedHeavyTruncationCodes, List.mem_flatMap] at hs₁ hs₂
    obtain ⟨_, _, hs₁'⟩ := hs₁
    obtain ⟨_, _, hs₂'⟩ := hs₂
    obtain ⟨H₁, hH₁, _, hcode₁, hdec₁⟩ := mem_chargedHeavyTruncationCodes_sound hcU hs₁'
    obtain ⟨H₂, hH₂, _, hcode₂, hdec₂⟩ := mem_chargedHeavyTruncationCodes_sound hcU hs₂'
    rw [hcode₁, hcode₂]
    refine codedUniformOn_code_congr hH₁ hH₂ ?_
    rw [← hdec₁, ← hdec₂]
    exact heq
  have hnd : (L'.map (fun w => (codeSupportList w).toFinset)).Nodup :=
    List.Nodup.map_on (fun w₁ h₁ w₂ h₂ h => hinj w₁ (hsub h₁) w₂ (hsub h₂) h) hL'nodup
  set S := (L'.map (fun w => (codeSupportList w).toFinset)).toFinset with hS
  have hcard : L'.length ≤ S.card := by
    rw [hS, List.toFinset_card_of_nodup hnd, List.length_map]
  refine hc x noiseLen baseBudget J k S ?_ (hk.trans hcard)
  intro H hH
  rw [hS, List.mem_toFinset, List.mem_map] at hH
  obtain ⟨w, hw, rfl⟩ := hH
  refine ⟨hmaps w (hsub hw), ?_⟩
  have := (List.mem_filter.mp hw).2
  simpa using this

end Kolmogorov
