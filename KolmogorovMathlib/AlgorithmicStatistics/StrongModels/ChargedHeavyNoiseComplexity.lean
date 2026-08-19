import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.ChargedHeavyNoiseCandidates
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.ImprovingDescriptions

/-!
# Charged complexity accounting for the heavy truncation

The charged heavy truncation of a pair model costs, in prefix set complexity,
only the advice needed to name its fibre threshold.  Since the threshold of a
stratum is clamped to the noise length, every charged heavy candidate of `x` is
a description of `x` whose complexity exceeds the stratum's complexity
coordinate by at most `logSlack c noiseLen`, and whose size is bounded by the
heavy-fibre count.

Consequently a cardinality lower bound on the charged candidate family packages
as a `ManyIJDescriptions` statement whose slack is logarithmic in the noise
length alone: it does not mention `x.length`, nor the size coordinate, nor the
fibre threshold separately.
-/

namespace Kolmogorov

open Kolmogorov.CodedFiniteDistribution

/-- Naming a natural number in prefix complexity costs only logarithmic slack. -/
theorem KPPlain_natBits_le_logSlack (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ l : ℕ, KPPlain U (Nat.bits l) ≤ (logSlack c l : ENat) := by
  obtain ⟨c_len, hlen⟩ := KPPlain_le_length_add_log U hU
  refine ⟨3 + c_len, fun l => ?_⟩
  set W := (Nat.bits l).length with hW
  have hnum : W + 2 * (Nat.bits W).length + c_len ≤ logSlack (3 + c_len) l := by
    have hWW : (Nat.bits W).length ≤ W := length_natBits_le_self W
    have : logSlack (3 + c_len) l = (3 + c_len) * W + (3 + c_len) := by
      unfold logSlack; rw [← hW]
    have hmul : 3 * W ≤ (3 + c_len) * W := Nat.mul_le_mul_right _ (by omega)
    omega
  calc KPPlain U (Nat.bits l)
      ≤ ((Nat.bits l).length : ENat) + 2 * ((Nat.bits (Nat.bits l).length).length : ENat)
          + (c_len : ENat) := hlen _
    _ = ((W + 2 * (Nat.bits W).length + c_len : ℕ) : ENat) := by
        rw [hW]; push_cast; ring
    _ ≤ (logSlack (3 + c_len) l : ENat) := by exact_mod_cast hnum

/-- The executable heavy truncation costs only logarithmic advice for its
threshold in prefix complexity. -/
theorem KPPlain_finiteSetFstHeavyTruncationCode_le
    (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (Bcode : BitString) (l : ℕ),
      KPPlain U (finiteSetFstHeavyTruncationCode Bcode (Nat.bits l)) ≤
        KPPlain U Bcode + (logSlack c l : ENat) := by
  have hg : Computable (fun w : BitString =>
      finiteSetFstHeavyTruncationCode (decodeSecond w) (decodeFirst w)) :=
    finiteSetFstHeavyTruncationCode_computable.comp
      decodeSecond_computable decodeFirst_computable
  obtain ⟨c_map, hmap⟩ := KPPlain_map_le U hU _ hg
  obtain ⟨c_pair, hpair⟩ := KPPair_le_KPPlain_add_KPPlain U hU
  obtain ⟨c_bits, hbits⟩ := KPPlain_natBits_le_logSlack U hU
  refine ⟨c_bits + c_pair + c_map, fun Bcode l => ?_⟩
  have hstep : KPPlain U (finiteSetFstHeavyTruncationCode Bcode (Nat.bits l)) ≤
      KPPlain U (pairCode (Nat.bits l) Bcode) + (c_map : ENat) := by
    simpa [decodeFirst_pairCode, decodeSecond_pairCode] using
      hmap (pairCode (Nat.bits l) Bcode)
  have hsplit : KPPlain U (pairCode (Nat.bits l) Bcode) ≤
      KPPlain U (Nat.bits l) + KPPlain U Bcode + (c_pair : ENat) := by
    have := hpair (Nat.bits l) Bcode
    rwa [KPPair_eq_KP_pairCode, ← KPPlain_eq_KP] at this
  have hslack : (logSlack c_bits l : ENat) + (c_pair : ENat) + (c_map : ENat) ≤
      (logSlack (c_bits + c_pair + c_map) l : ENat) := by
    have hnum : logSlack c_bits l + c_pair + c_map ≤
        logSlack (c_bits + c_pair + c_map) l := by
      unfold logSlack
      have : c_bits * (Nat.bits l).length ≤
          (c_bits + c_pair + c_map) * (Nat.bits l).length :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    exact_mod_cast hnum
  calc KPPlain U (finiteSetFstHeavyTruncationCode Bcode (Nat.bits l))
      ≤ KPPlain U (pairCode (Nat.bits l) Bcode) + (c_map : ENat) := hstep
    _ ≤ (KPPlain U (Nat.bits l) + KPPlain U Bcode + (c_pair : ENat)) + (c_map : ENat) := by
        gcongr
    _ ≤ ((logSlack c_bits l : ENat) + KPPlain U Bcode + (c_pair : ENat)) + (c_map : ENat) := by
        gcongr
        exact hbits l
    _ = KPPlain U Bcode + ((logSlack c_bits l : ENat) + (c_pair : ENat) + (c_map : ENat)) := by
        ring
    _ ≤ KPPlain U Bcode + (logSlack (c_bits + c_pair + c_map) l : ENat) := by
        gcongr

/-- Prefix set-complexity companion to the ordinary heavy-truncation bound. -/
theorem finiteSetFstHeavyTruncation_setComplexity_le
    (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (B : Finset BitString) (hB : B.Nonempty) (l : ℕ)
        (hH : (finiteSetFstHeavyTruncation B l).Nonempty),
      setComplexity U (finiteSetFstHeavyTruncation B l) hH ≤
        setComplexity U B hB + (logSlack c l : ENat) := by
  obtain ⟨c, hc⟩ := KPPlain_finiteSetFstHeavyTruncationCode_le U hU
  refine ⟨c, fun B hB l hH => ?_⟩
  unfold setComplexity
  rw [← finiteSetFstHeavyTruncationCode_codedUniformOn B hB l hH]
  exact hc (codedUniformOn B hB).code l

/-! ### Charged accounting for the candidate family -/

/-- Every charged heavy candidate is a description of `x` whose complexity
exceeds the stratum's complexity coordinate by at most slack logarithmic in the
noise length. -/
theorem chargedHeavyNoiseCandidates_setComplexity_le
    (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (noiseLen baseBudget : ℕ) (stratum : BitString)
      (H : Finset BitString) (hH : H.Nonempty),
      H ∈ chargedHeavyNoiseCandidates U x noiseLen baseBudget stratum →
      setComplexity U H hH ≤
        ((stratumComplexity baseBudget stratum + logSlack c noiseLen : ℕ) : ENat) := by
  obtain ⟨c₀, hc₀⟩ := setComplexity_le_of_mem_descriptionsWithComplexityLe U
  obtain ⟨c₁, hc₁⟩ := finiteSetFstHeavyTruncation_setComplexity_le U hU
  refine ⟨c₀ + c₁, ?_⟩
  intro x noiseLen baseBudget stratum H hH hmem
  rw [chargedHeavyNoiseCandidates] at hmem
  set i := stratumComplexity baseBudget stratum with hi
  set thr := stratumThreshold noiseLen stratum with hthr
  obtain ⟨B, hBdesc, ⟨y, _, hpair⟩, hxH, rfl⟩ := mem_chargedHeavyNoiseCandidatesRaw_iff.mp hmem
  have hBne : B.Nonempty := ⟨pairCode x y, hpair⟩
  have h1 : setComplexity U (finiteSetFstHeavyTruncation B thr) hH ≤
      setComplexity U B hBne + (logSlack c₁ thr : ENat) := hc₁ B hBne thr hH
  have h2 : setComplexity U B hBne ≤ (i + c₀ : ENat) :=
    hc₀ i B hBne (Finset.mem_filter.mp hBdesc).1
  have hmono : logSlack c₁ thr ≤ logSlack c₁ noiseLen := by
    unfold logSlack
    exact Nat.add_le_add_right
      (Nat.mul_le_mul_left _ (length_natBits_mono (stratumThreshold_le noiseLen stratum))) _
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

/-- **Charged multiplicity packaging.**  A cardinality lower bound for the
charged heavy candidates of `x` yields `2 ^ k` genuine `(i', j')`-descriptions of
`x`, where the complexity coordinate is charged only `logSlack c noiseLen` and
the size coordinate is the heavy-fibre count.  No term depends on `x.length`. -/
theorem manyIJDescriptions_of_chargedHeavyNoiseCandidates
    (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (noiseLen baseBudget : ℕ) (stratum : BitString) (k : ℕ),
      2 ^ k ≤ (chargedHeavyNoiseCandidates U x noiseLen baseBudget stratum).card →
      ManyIJDescriptions U x
        (stratumComplexity baseBudget stratum + logSlack c noiseLen)
        (stratumSize baseBudget stratum - stratumThreshold noiseLen stratum + 1) k := by
  obtain ⟨c, hc⟩ := chargedHeavyNoiseCandidates_setComplexity_le U hU
  refine ⟨c, ?_⟩
  intro x noiseLen baseBudget stratum k hk
  refine hk.trans (Finset.card_le_card ?_)
  intro H hH
  obtain ⟨hxH, hHne, hcard⟩ :=
    chargedHeavyNoiseCandidates_sound U x noiseLen baseBudget stratum hH
  rw [Finset.mem_filter]
  refine ⟨?_, hxH⟩
  rw [descriptionsWithComplexityLeAndSizeLe, Finset.mem_filter]
  refine ⟨mem_descriptionsWithComplexityLe_of_complexity hHne ?_, hcard⟩
  exact hc x noiseLen baseBudget stratum H hHne hH

end Kolmogorov
