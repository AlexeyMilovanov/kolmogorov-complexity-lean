import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.ChargedHeavyNoiseEnumeration
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.ChargedHeavyNoiseCandidates
import KolmogorovMathlib.AlgorithmicStatistics.Selector

namespace Kolmogorov

open Nat.Partrec (Code)
open Kolmogorov.CodedFiniteDistribution

/-- The genuinely pooled candidate family: complexity and threshold are
clamped to the visible budgets, while the size coordinate ranges over every
natural encoded by the stratum. -/
noncomputable def pooledChargedHeavyNoiseCandidates
    (U : Map) (x : BitString) (noiseLen baseBudget : ℕ)
    (stratum : BitString) : Finset (Finset BitString) :=
  chargedHeavyNoiseCandidatesRaw U x noiseLen
    (stratumComplexity baseBudget stratum) (stratumSizeRaw stratum)
    (stratumThreshold noiseLen stratum)

/-- Every concrete heavy truncation enters the pooled family at its canonical
stratum, including when its size coordinate exceeds `baseBudget`. -/
theorem mem_pooledChargedHeavyNoiseCandidates_of_heavy_fibre
    {U : Map} {x y : BitString} {baseBudget i j threshold : ℕ}
    {B : Finset BitString}
    (hB : B ∈ descriptionsWithComplexityLeAndSizeLe U i j)
    (hpair : pairCode x y ∈ B) (hi : i ≤ baseBudget)
    (hthreshold : threshold ≤ y.length)
    (hheavy : threshold ≤ finiteSetLogCard (finiteSetFstFiber B x)) :
    finiteSetFstHeavyTruncation B threshold ∈
      pooledChargedHeavyNoiseCandidates U x y.length baseBudget
        (chargedStratumCode i j threshold) := by
  unfold pooledChargedHeavyNoiseCandidates stratumComplexity stratumThreshold
  simp only [stratumComplexityRaw_code, stratumSizeRaw_code,
    stratumThresholdRaw_code]
  rw [Nat.min_eq_left hi, Nat.min_eq_left hthreshold]
  exact mem_chargedHeavyNoiseCandidatesRaw_of_heavy_fibre
    hB rfl hpair hheavy

noncomputable def budgetedChargedHeavyTruncationCodes
    (c : Code) (x : BitString) (noiseLen baseBudget t : ℕ) : List BitString :=
  (boundedPrograms t).flatMap (fun stratum =>
    chargedHeavyTruncationCodes c x noiseLen
      (stratumComplexity baseBudget stratum)
      (stratumSizeRaw stratum)
      (stratumThreshold noiseLen stratum) t)

noncomputable def budgetedChargedHeavyAppearanceCodes
    (c : Code) (x : BitString) (noiseLen baseBudget : ℕ) : ℕ → List BitString
  | 0 => (budgetedChargedHeavyTruncationCodes c x noiseLen baseBudget 0).eraseDups
  | t + 1 => (budgetedChargedHeavyAppearanceCodes c x noiseLen baseBudget t ++
      budgetedChargedHeavyTruncationCodes c x noiseLen baseBudget (t + 1)).eraseDups

theorem stratumComplexity_primrec : Primrec₂ stratumComplexity := by
  have h1 : Primrec bitsToNat := bitsToNat_primrec
  have h2 : Primrec decodeFirst := decodeFirst_primrec
  have h3 : Primrec (fun (stratum : BitString) => bitsToNat (decodeFirst stratum)) :=
    h1.comp h2
  exact Primrec.nat_min.comp (h3.comp Primrec.snd) Primrec.fst

theorem stratumSize_primrec : Primrec₂ stratumSize := by
  have h1 : Primrec bitsToNat := bitsToNat_primrec
  have h2 : Primrec decodeFirst := decodeFirst_primrec
  have h3 : Primrec decodeSecond := decodeSecond_primrec
  have h4 : Primrec (fun (stratum : BitString) => bitsToNat (decodeFirst (decodeSecond stratum))) :=
    h1.comp (h2.comp h3)
  exact Primrec.nat_min.comp (h4.comp Primrec.snd) Primrec.fst

theorem stratumSizeRaw_primrec : Primrec stratumSizeRaw := by
  unfold stratumSizeRaw
  exact bitsToNat_primrec.comp
    (decodeFirst_primrec.comp decodeSecond_primrec)

theorem stratumThreshold_primrec : Primrec₂ stratumThreshold := by
  have h1 : Primrec bitsToNat := bitsToNat_primrec
  have h3 : Primrec decodeSecond := decodeSecond_primrec
  have h4 : Primrec (fun (stratum : BitString) =>
      bitsToNat (decodeSecond (decodeSecond stratum))) :=
    h1.comp (h3.comp h3)
  exact Primrec.nat_min.comp (h4.comp Primrec.snd) Primrec.fst

theorem primrec_budgeted_boundedPrograms :
    Primrec (fun (p : ((BitString × ℕ) × ℕ) × ℕ) => boundedPrograms p.2) :=
  primrec_boundedPrograms.comp (Primrec.snd (α := ((BitString × ℕ) × ℕ)) (β := ℕ))

theorem budgetedChargedHeavyTruncationCodes_primrec (c : Code) :
    Primrec (fun p : ((BitString × ℕ) × ℕ) × ℕ =>
      budgetedChargedHeavyTruncationCodes c p.1.1.1 p.1.1.2 p.1.2 p.2) := by
  have h_comp : Primrec₂ (fun (p : ((BitString × ℕ) × ℕ) × ℕ)
      (stratum : BitString) => stratumComplexity p.1.2 stratum) :=
    stratumComplexity_primrec.comp
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd
  have h_size : Primrec₂ (fun (_p : ((BitString × ℕ) × ℕ) × ℕ)
      (stratum : BitString) => stratumSizeRaw stratum) :=
    stratumSizeRaw_primrec.comp Primrec.snd
  have h_thr : Primrec₂ (fun (p : ((BitString × ℕ) × ℕ) × ℕ)
      (stratum : BitString) => stratumThreshold p.1.1.2 stratum) :=
    stratumThreshold_primrec.comp
      (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
      Primrec.snd
  have h_arg : Primrec₂ (fun (p : ((BitString × ℕ) × ℕ) × ℕ)
      (stratum : BitString) =>
      (((p.1.1.1, p.1.1.2, stratumSizeRaw stratum,
          stratumThreshold p.1.1.2 stratum),
        stratumComplexity p.1.2 stratum), p.2)) := by
    exact Primrec.pair
      (Primrec.pair
        (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
          (Primrec.pair (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
            (Primrec.pair h_size h_thr)))
        h_comp)
      (Primrec.snd.comp Primrec.fst)
  exact Primrec.list_flatMap primrec_budgeted_boundedPrograms
    (((chargedHeavyTruncationCodes_primrec c).comp h_arg).to₂)

private theorem budgetedChargedHeavyAppearanceCodes_base_primrec (c : Code) :
    Primrec (fun p : ((BitString × ℕ) × ℕ) × ℕ =>
      (budgetedChargedHeavyTruncationCodes c p.1.1.1 p.1.1.2 p.1.2 0).eraseDups) :=
  eraseDups_bitstring_primrec.comp
    ((budgetedChargedHeavyTruncationCodes_primrec c).comp
      (Primrec.pair Primrec.fst (Primrec.const 0)))

private noncomputable def budgetedChargedHeavyTruncationCodesNext
    (c : Code) (p : ((BitString × ℕ) × ℕ) × ℕ)
    (q : ℕ × List BitString) : List BitString :=
  budgetedChargedHeavyTruncationCodes c p.1.1.1 p.1.1.2 p.1.2 (q.1 + 1)

private theorem budgetedChargedHeavyTruncationCodes_next_primrec (c : Code) :
    Primrec₂ (budgetedChargedHeavyTruncationCodesNext c) := by
  unfold budgetedChargedHeavyTruncationCodesNext
  unfold budgetedChargedHeavyTruncationCodes
  have hbound : Primrec (fun r :
      ((((BitString × ℕ) × ℕ) × ℕ) × (ℕ × List BitString)) =>
        boundedPrograms (r.2.1 + 1)) :=
    primrec_boundedPrograms.comp
      (Primrec.succ.comp (Primrec.fst.comp Primrec.snd))
  have hcomp : Primrec₂ (fun (r :
      ((((BitString × ℕ) × ℕ) × ℕ) × (ℕ × List BitString)))
      (stratum : BitString) => stratumComplexity r.1.1.2 stratum) :=
    stratumComplexity_primrec.comp
      (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
      Primrec.snd
  have hsize : Primrec₂ (fun (_r :
      ((((BitString × ℕ) × ℕ) × ℕ) × (ℕ × List BitString)))
      (stratum : BitString) => stratumSizeRaw stratum) :=
    stratumSizeRaw_primrec.comp Primrec.snd
  have hthr : Primrec₂ (fun (r :
      ((((BitString × ℕ) × ℕ) × ℕ) × (ℕ × List BitString)))
      (stratum : BitString) => stratumThreshold r.1.1.1.2 stratum) :=
    stratumThreshold_primrec.comp
      (Primrec.snd.comp (Primrec.fst.comp
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))) Primrec.snd
  have harg : Primrec₂ (fun (r :
      ((((BitString × ℕ) × ℕ) × ℕ) × (ℕ × List BitString)))
      (stratum : BitString) =>
        (((r.1.1.1.1, r.1.1.1.2, stratumSizeRaw stratum,
            stratumThreshold r.1.1.1.2 stratum),
          stratumComplexity r.1.1.2 stratum), r.2.1 + 1)) := by
    exact Primrec.pair
      (Primrec.pair
        (Primrec.pair
          (Primrec.fst.comp (Primrec.fst.comp
            (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
          (Primrec.pair
            (Primrec.snd.comp (Primrec.fst.comp
              (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
            (Primrec.pair hsize hthr)))
        hcomp)
      (Primrec.succ.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
  exact Primrec.list_flatMap hbound
    (((chargedHeavyTruncationCodes_primrec c).comp harg).to₂)

private theorem budgetedChargedHeavyAppearanceCodes_step_primrec (c : Code) :
    Primrec₂ (fun (p : ((BitString × ℕ) × ℕ) × ℕ)
      (q : ℕ × List BitString) => (q.2 ++
        budgetedChargedHeavyTruncationCodesNext c p q).eraseDups) :=
  eraseDups_bitstring_primrec.comp (Primrec.list_append.comp
    (Primrec.snd.comp Primrec.snd)
    (budgetedChargedHeavyTruncationCodes_next_primrec c))

theorem budgetedChargedHeavyAppearanceCodes_primrec (c : Code) :
    Primrec (fun p : ((BitString × ℕ) × ℕ) × ℕ =>
      budgetedChargedHeavyAppearanceCodes c p.1.1.1 p.1.1.2 p.1.2 p.2) := by
  refine (Primrec.nat_rec' Primrec.snd
    (budgetedChargedHeavyAppearanceCodes_base_primrec c)
    (budgetedChargedHeavyAppearanceCodes_step_primrec c)).of_eq ?_
  rintro ⟨⟨⟨x, noiseLen⟩, baseBudget⟩, t⟩
  induction t with
  | zero => rfl
  | succ t ih =>
      simp only [budgetedChargedHeavyAppearanceCodes]
      unfold budgetedChargedHeavyTruncationCodesNext
      unfold budgetedChargedHeavyTruncationCodesNext at ih
      dsimp only [Prod.fst, Prod.snd] at ih ⊢
      rw [← ih]

theorem budgetedChargedHeavyAppearanceCodes_computable (c : Code) :
    Computable (fun p : ((BitString × ℕ) × ℕ) × ℕ =>
      budgetedChargedHeavyAppearanceCodes c p.1.1.1 p.1.1.2 p.1.2 p.2) :=
  (budgetedChargedHeavyAppearanceCodes_primrec c).to_comp

@[simp] theorem budgetedChargedHeavyAppearanceCodes_zero
    (c : Code) (x : BitString) (noiseLen baseBudget : ℕ) :
    budgetedChargedHeavyAppearanceCodes c x noiseLen baseBudget 0 =
      (budgetedChargedHeavyTruncationCodes c x noiseLen baseBudget 0).eraseDups := rfl

theorem budgetedChargedHeavyAppearanceCodes_succ
    (c : Code) (x : BitString) (noiseLen baseBudget t : ℕ) :
    budgetedChargedHeavyAppearanceCodes c x noiseLen baseBudget (t + 1) =
      (budgetedChargedHeavyAppearanceCodes c x noiseLen baseBudget t ++
        budgetedChargedHeavyTruncationCodes c x noiseLen baseBudget (t + 1)).eraseDups := rfl

theorem budgetedChargedHeavyAppearanceCodes_nodup
    (c : Code) (x : BitString) (noiseLen baseBudget t : ℕ) :
    (budgetedChargedHeavyAppearanceCodes c x noiseLen baseBudget t).Nodup := by
  cases t <;> exact nodup_eraseDups_bitString _

theorem budgetedChargedHeavyAppearanceCodes_mono
    (c : Code) (x : BitString) (noiseLen baseBudget t : ℕ) :
    budgetedChargedHeavyAppearanceCodes c x noiseLen baseBudget t <+:
      budgetedChargedHeavyAppearanceCodes c x noiseLen baseBudget (t + 1) := by
  rw [budgetedChargedHeavyAppearanceCodes_succ]
  exact prefix_eraseDups_append_of_nodup _ _
    (budgetedChargedHeavyAppearanceCodes_nodup c x noiseLen baseBudget t)

theorem budgetedChargedHeavyAppearanceCodes_prefix_of_le
    (c : Code) (x : BitString) (noiseLen baseBudget : ℕ)
    {t₁ t₂ : ℕ} (h : t₁ ≤ t₂) :
    budgetedChargedHeavyAppearanceCodes c x noiseLen baseBudget t₁ <+:
      budgetedChargedHeavyAppearanceCodes c x noiseLen baseBudget t₂ := by
  induction h with
  | refl => exact List.prefix_refl _
  | step _ ih =>
      exact ih.trans
        (budgetedChargedHeavyAppearanceCodes_mono c x noiseLen baseBudget _)

theorem mem_budgetedChargedHeavyAppearanceCodes_of_mem_stage
    {c : Code} {x : BitString} {noiseLen baseBudget t : ℕ} {w : BitString}
    (hw : w ∈ budgetedChargedHeavyTruncationCodes c x noiseLen baseBudget t) :
    w ∈ budgetedChargedHeavyAppearanceCodes c x noiseLen baseBudget t := by
  cases t with
  | zero => exact mem_eraseDups_bitString.mpr hw
  | succ t =>
      rw [budgetedChargedHeavyAppearanceCodes_succ, mem_eraseDups_bitString, List.mem_append]
      exact Or.inr hw

theorem exists_stage_of_mem_budgetedChargedHeavyAppearanceCodes
    {c : Code} {x : BitString} {noiseLen baseBudget t : ℕ} {w : BitString}
    (hw : w ∈ budgetedChargedHeavyAppearanceCodes c x noiseLen baseBudget t) :
    ∃ s ≤ t, w ∈ budgetedChargedHeavyTruncationCodes c x noiseLen baseBudget s := by
  induction t with
  | zero =>
      rw [budgetedChargedHeavyAppearanceCodes_zero, mem_eraseDups_bitString] at hw
      exact ⟨0, Nat.le_refl _, hw⟩
  | succ t ih =>
      rw [budgetedChargedHeavyAppearanceCodes_succ, mem_eraseDups_bitString, List.mem_append] at hw
      cases hw with
      | inl hw =>
          obtain ⟨s, hs_le, hw'⟩ := ih hw
          exact ⟨s, Nat.le_succ_of_le hs_le, hw'⟩
      | inr hw => exact ⟨t + 1, Nat.le_refl _, hw⟩

theorem budgetedChargedHeavyAppearanceCodes_sound
    {U : Map} {c : Code} (hc : IsCodeFor c U)
    (x : BitString) (noiseLen baseBudget t : ℕ)
    (H : Finset BitString)
    (hmem : canonicalUniformCodeOfList (canonicalFinsetList H) ∈
      budgetedChargedHeavyAppearanceCodes c x noiseLen baseBudget t) :
    ∃ stratum, H ∈ pooledChargedHeavyNoiseCandidates U x noiseLen
      baseBudget stratum := by
  obtain ⟨s, _, hs⟩ := exists_stage_of_mem_budgetedChargedHeavyAppearanceCodes hmem
  rw [budgetedChargedHeavyTruncationCodes, List.mem_flatMap] at hs
  obtain ⟨stratum, _, hs_stratum⟩ := hs
  obtain ⟨H', hH', hmem_raw, hcode, _⟩ := mem_chargedHeavyTruncationCodes_sound hc hs_stratum
  have h_eq : canonicalUniformCodeOfList (canonicalFinsetList H) =
      canonicalUniformCodeOfList (canonicalFinsetList H') := by
    rw [hcode, canonicalUniformCodeOfList_canonicalFinsetList H' hH']
  have h_H : H = H' := by
    have h_list := canonicalUniformCodeOfList_injective h_eq
    have h_finset := congrArg List.toFinset h_list
    rwa [canonicalFinsetList_toFinset, canonicalFinsetList_toFinset] at h_finset
  rw [h_H]
  exact ⟨stratum, hmem_raw⟩

theorem budgetedChargedHeavyAppearanceCodes_complete
    {U : Map} {c : Code} (hc : IsCodeFor c U)
    (x : BitString) (noiseLen baseBudget : ℕ)
    (H : Finset BitString)
    (hmem : ∃ stratum, H ∈ pooledChargedHeavyNoiseCandidates U x
      noiseLen baseBudget stratum) :
    ∃ t, canonicalUniformCodeOfList (canonicalFinsetList H) ∈
      budgetedChargedHeavyAppearanceCodes c x noiseLen baseBudget t := by
  obtain ⟨stratum, hstratum⟩ := hmem
  let i := stratumComplexity baseBudget stratum
  let j := stratumSizeRaw stratum
  let thr := stratumThreshold noiseLen stratum
  obtain ⟨B, hBdesc, ⟨y, hy, hpair⟩, hxH, rfl⟩ :=
    mem_chargedHeavyNoiseCandidatesRaw_iff.mp hstratum
  have hylen : y.length = noiseLen := by
    simpa [stringsOfLength] using hy
  obtain ⟨t₀, hmax⟩ := exists_max_countHalts c i
  set t := max t₀ stratum.length
  have hmax_t : ∀ t', countHalts c i t' ≤ countHalts c i t := by
    intro t'
    calc countHalts c i t' ≤ countHalts c i t₀ := hmax t'
      _ ≤ countHalts c i t := countHalts_mono c i (le_max_left _ _)
  have hBsnap : B ∈ snapshotDescriptionsAndSizeLe c i j t := by
    rw [snapshotDescriptionsAndSizeLe_eq_descriptionsWithComplexityLeAndSizeLe hc i j t hmax_t]
    exact hBdesc
  rw [snapshotDescriptionsAndSizeLe, Finset.mem_filter, snapshotDescriptions,
    Finset.mem_image] at hBsnap
  obtain ⟨⟨v, hv, hvB⟩, hcard⟩ := hBsnap
  rw [List.mem_toFinset, List.mem_filter] at hv
  have hsupp : (codeSupportList v).toFinset = B := hvB
  have hheavy : 2 ^ (thr - 1) ≤ (finiteSetFstFiber B x).card :=
    ((mem_finiteSetFstHeavyTruncation_iff B thr x).mp hxH).2
  have hfilter : chargedHeavyCodeFilter x noiseLen j thr v = true := by
    rw [chargedHeavyCodeFilter_iff]
    refine ⟨⟨y, hylen, ?_⟩, by rw [hsupp]; exact hcard, by rw [hsupp]; exact hheavy⟩
    exact List.mem_toFinset.mp (by rw [hsupp]; exact hpair)
  have hvmem : v ∈ chargedHeavyFilteredCodes c x noiseLen i j thr t := by
    rw [chargedHeavyFilteredCodes, List.mem_filter, List.mem_filter]
    exact ⟨⟨hv.1, hv.2⟩, hfilter⟩
  have hHne : (finiteSetFstHeavyTruncation B thr).Nonempty := ⟨x, hxH⟩
  have hlist : (heavyOutputList ((codeSupportList v).dedup.map decodeFirst) thr).toFinset =
      finiteSetFstHeavyTruncation B thr := by
    rw [heavyOutputList_map_decodeFirst_toFinset (List.nodup_dedup _) thr,
      dedup_toFinset_bitString, hsupp]
  refine ⟨t, ?_⟩
  apply mem_budgetedChargedHeavyAppearanceCodes_of_mem_stage
  rw [budgetedChargedHeavyTruncationCodes, List.mem_flatMap]
  refine ⟨stratum, ?_, ?_⟩
  · exact (mem_boundedPrograms_iff stratum t).mpr (le_max_right _ _)
  · rw [canonicalUniformCodeOfList_canonicalFinsetList _ hHne,
      chargedHeavyTruncationCodes, List.mem_map]
    refine ⟨v, hvmem, ?_⟩
    rw [canonicalImageCodeOfList_eq_codedUniformOn _ (by rw [hlist]; exact hHne)]
    exact codedUniformOn_code_congr _ _ hlist

end Kolmogorov
