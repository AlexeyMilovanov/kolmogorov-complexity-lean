import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.AddNoiseCandidates
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.AddNoiseFibres

/-!
# Charged heavy-truncation candidates for the budgeted add-noise route

The budget-scale add-noise route replaces the ordinary first-coordinate
truncation of `AddNoiseCandidates.lean` by the *heavy* truncation of
`AddNoiseFibres.lean`: only first coordinates whose fibre is large survive.
All description coordinates are packed into a single *stratum* string, which is
decoded (and clamped to the ambient budgets) by the functions below.  Clamping
is what makes the resulting candidate family depend on the stratum only through
data of size `O(log baseBudget + log noiseLen)`, which is exactly the slack
allowed by the rank decoder of `ChargedHeavyNoiseRank.lean`.

The candidate family is the image, under the heavy truncation at the decoded
fibre threshold, of all budgeted pair descriptions that contain a pair code
`⟨x, y⟩` with `|y| = noiseLen` and whose fibre over `x` is heavy.
-/

namespace Kolmogorov

open Kolmogorov.CodedFiniteDistribution

/-! ### Stratum coordinates -/

/-- Pack the complexity, size and fibre-threshold coordinates of a charged
heavy stratum into a single string. -/
def chargedStratumCode (i j thr : ℕ) : BitString :=
  pairCode (Nat.bits i) (pairCode (Nat.bits j) (Nat.bits thr))

/-- The raw complexity coordinate of a stratum. -/
def stratumComplexityRaw (stratum : BitString) : ℕ := bitsToNat (decodeFirst stratum)

/-- The raw size coordinate of a stratum. -/
def stratumSizeRaw (stratum : BitString) : ℕ :=
  bitsToNat (decodeFirst (decodeSecond stratum))

/-- The raw fibre-threshold coordinate of a stratum. -/
def stratumThresholdRaw (stratum : BitString) : ℕ :=
  bitsToNat (decodeSecond (decodeSecond stratum))

/-- The complexity coordinate of a stratum, clamped to the ambient budget. -/
def stratumComplexity (baseBudget : ℕ) (stratum : BitString) : ℕ :=
  min (stratumComplexityRaw stratum) baseBudget

/-- The size coordinate of a stratum, clamped to the ambient budget. -/
def stratumSize (baseBudget : ℕ) (stratum : BitString) : ℕ :=
  min (stratumSizeRaw stratum) baseBudget

/-- The fibre threshold of a stratum, clamped to the noise length. -/
def stratumThreshold (noiseLen : ℕ) (stratum : BitString) : ℕ :=
  min (stratumThresholdRaw stratum) noiseLen

theorem stratumComplexity_le (baseBudget : ℕ) (stratum : BitString) :
    stratumComplexity baseBudget stratum ≤ baseBudget := min_le_right _ _

theorem stratumSize_le (baseBudget : ℕ) (stratum : BitString) :
    stratumSize baseBudget stratum ≤ baseBudget := min_le_right _ _

theorem stratumThreshold_le (noiseLen : ℕ) (stratum : BitString) :
    stratumThreshold noiseLen stratum ≤ noiseLen := min_le_right _ _

@[simp] theorem stratumComplexityRaw_code (i j thr : ℕ) :
    stratumComplexityRaw (chargedStratumCode i j thr) = i := by
  simp [stratumComplexityRaw, chargedStratumCode, decodeFirst_pairCode, bitsToNat_bits]

@[simp] theorem stratumSizeRaw_code (i j thr : ℕ) :
    stratumSizeRaw (chargedStratumCode i j thr) = j := by
  simp [stratumSizeRaw, chargedStratumCode, decodeFirst_pairCode, decodeSecond_pairCode,
    bitsToNat_bits]

@[simp] theorem stratumThresholdRaw_code (i j thr : ℕ) :
    stratumThresholdRaw (chargedStratumCode i j thr) = thr := by
  simp [stratumThresholdRaw, chargedStratumCode, decodeSecond_pairCode, bitsToNat_bits]

/-! ### List presentations of the heavy truncation -/

/-- Counting the fibre over `x` in a duplicate-free list is counting the fibre
in the finite set it represents. -/
theorem countP_decodeFirst_eq_fiber_card
    {L : List BitString} (hL : L.Nodup) (x : BitString) :
    L.countP (fun z => decide (decodeFirst z = x)) =
      (finiteSetFstFiber L.toFinset x).card := by
  have hcount := list_count_map_eq_card_filter L hL decodeFirst x
  have hLHS : (L.map decodeFirst).count x =
      L.countP (fun z => decide (decodeFirst z = x)) := by
    simp only [List.count, List.countP_map, Function.comp_def]
    congr 1
    funext z
    by_cases h : decodeFirst z = x <;> simp [h]
  rw [← hLHS, hcount, finiteSetFstFiber]

/-- Membership in the heavy output list of the first coordinates of any
duplicate-free list of pair codes. -/
theorem mem_heavyOutputList_map_decodeFirst_iff
    {L : List BitString} (hL : L.Nodup) (thr : ℕ) (y : BitString) :
    y ∈ heavyOutputList (L.map decodeFirst) thr ↔
      (∃ z ∈ L.toFinset, decodeFirst z = y) ∧
        2 ^ (thr - 1) ≤ (finiteSetFstFiber L.toFinset y).card := by
  have hcount : (L.map decodeFirst).count y =
      (finiteSetFstFiber L.toFinset y).card := by
    rw [show (L.map decodeFirst).count y =
        L.countP (fun z => decide (decodeFirst z = y)) by
      simp only [List.count, List.countP_map, Function.comp_def]
      congr 1
      funext z
      by_cases h : decodeFirst z = y <;> simp [h]]
    exact countP_decodeFirst_eq_fiber_card hL y
  rw [heavyOutputList, List.mem_filter, List.mem_dedup, List.mem_map,
    decide_eq_true_eq, hcount]
  refine and_congr ?_ Iff.rfl
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, List.mem_toFinset.mpr hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, List.mem_toFinset.mp hz, rfl⟩

/-- The heavy truncation of a finite set of pair codes is computed by the heavy
output list of any duplicate-free list representing it. -/
theorem heavyOutputList_map_decodeFirst_toFinset
    {L : List BitString} (hL : L.Nodup) (thr : ℕ) :
    (heavyOutputList (L.map decodeFirst) thr).toFinset =
      finiteSetFstHeavyTruncation L.toFinset thr := by
  ext y
  rw [List.mem_toFinset, mem_heavyOutputList_map_decodeFirst_iff hL thr y,
    finiteSetFstHeavyTruncation, List.mem_toFinset,
    mem_heavyOutputList_map_decodeFirst_iff (canonicalFinsetList_nodup _) thr y,
    canonicalFinsetList_toFinset]

/-- Membership criterion for the heavy truncation of a finite set. -/
theorem mem_finiteSetFstHeavyTruncation_iff
    (B : Finset BitString) (thr : ℕ) (y : BitString) :
    y ∈ finiteSetFstHeavyTruncation B thr ↔
      (∃ z ∈ B, decodeFirst z = y) ∧
        2 ^ (thr - 1) ≤ (finiteSetFstFiber B y).card := by
  rw [finiteSetFstHeavyTruncation, List.mem_toFinset,
    mem_heavyOutputList_map_decodeFirst_iff (canonicalFinsetList_nodup B) thr y,
    canonicalFinsetList_toFinset]

/-! ### The candidate family -/

/-- The charged heavy truncations at explicit coordinates: heavy truncations, at
threshold `thr`, of all `(i, j)`-descriptions containing a pair code `⟨x, y⟩`
with `|y| = noiseLen` whose distinguished fibre over `x` survives the
truncation. -/
noncomputable def chargedHeavyNoiseCandidatesRaw
    (U : Map) (x : BitString) (noiseLen i j thr : ℕ) :
    Finset (Finset BitString) :=
  ((descriptionsWithComplexityLeAndSizeLe U i j).filter
    (fun B => (∃ y ∈ stringsOfLength noiseLen, pairCode x y ∈ B) ∧
      x ∈ finiteSetFstHeavyTruncation B thr)).image
      (fun B => finiteSetFstHeavyTruncation B thr)

/-- The charged heavy truncation candidates of `x` at noise length `noiseLen`,
budget `baseBudget` and stratum `stratum`. -/
noncomputable def chargedHeavyNoiseCandidates
    (U : Map) (x : BitString) (noiseLen baseBudget : ℕ) (stratum : BitString) :
    Finset (Finset BitString) :=
  chargedHeavyNoiseCandidatesRaw U x noiseLen
    (stratumComplexity baseBudget stratum)
    (stratumSize baseBudget stratum)
    (stratumThreshold noiseLen stratum)

/-- Membership unfolded: a charged heavy candidate is the heavy truncation of a
budgeted description with a heavy distinguished fibre. -/
theorem mem_chargedHeavyNoiseCandidatesRaw_iff
    {U : Map} {x : BitString} {noiseLen i j thr : ℕ} {H : Finset BitString} :
    H ∈ chargedHeavyNoiseCandidatesRaw U x noiseLen i j thr ↔
      ∃ B ∈ descriptionsWithComplexityLeAndSizeLe U i j,
        (∃ y ∈ stringsOfLength noiseLen, pairCode x y ∈ B) ∧
          x ∈ finiteSetFstHeavyTruncation B thr ∧
          finiteSetFstHeavyTruncation B thr = H := by
  rw [chargedHeavyNoiseCandidatesRaw, Finset.mem_image]
  constructor
  · rintro ⟨B, hB, rfl⟩
    rw [Finset.mem_filter] at hB
    exact ⟨B, hB.1, hB.2.1, hB.2.2, rfl⟩
  · rintro ⟨B, hB, hy, hx, rfl⟩
    exact ⟨B, Finset.mem_filter.mpr ⟨hB, hy, hx⟩, rfl⟩

/-- A budgeted description whose fibre over `x` has logarithmic cardinality at
least the threshold contributes its heavy truncation to the candidates. -/
theorem mem_chargedHeavyNoiseCandidatesRaw_of_heavy_fibre
    {U : Map} {x y : BitString} {noiseLen i j thr : ℕ} {B : Finset BitString}
    (hB : B ∈ descriptionsWithComplexityLeAndSizeLe U i j)
    (hylen : y.length = noiseLen) (hpair : pairCode x y ∈ B)
    (hheavy : thr ≤ finiteSetLogCard (finiteSetFstFiber B x)) :
    finiteSetFstHeavyTruncation B thr ∈
      chargedHeavyNoiseCandidatesRaw U x noiseLen i j thr :=
  mem_chargedHeavyNoiseCandidatesRaw_iff.mpr
    ⟨B, hB, ⟨y, by simp [stringsOfLength, hylen], hpair⟩,
      finiteSetFstHeavyTruncation_mem hpair hheavy, rfl⟩

/-- Every charged heavy candidate contains `x`; in particular it is nonempty. -/
theorem mem_of_mem_chargedHeavyNoiseCandidatesRaw
    {U : Map} {x : BitString} {noiseLen i j thr : ℕ} {H : Finset BitString}
    (hH : H ∈ chargedHeavyNoiseCandidatesRaw U x noiseLen i j thr) :
    x ∈ H := by
  obtain ⟨B, _, _, hx, rfl⟩ := mem_chargedHeavyNoiseCandidatesRaw_iff.mp hH
  exact hx

theorem nonempty_of_mem_chargedHeavyNoiseCandidatesRaw
    {U : Map} {x : BitString} {noiseLen i j thr : ℕ} {H : Finset BitString}
    (hH : H ∈ chargedHeavyNoiseCandidatesRaw U x noiseLen i j thr) :
    H.Nonempty :=
  ⟨x, mem_of_mem_chargedHeavyNoiseCandidatesRaw hH⟩

/-- Charged heavy truncation trades the size bound `j` for the heavy count
`j - thr + 1`. -/
theorem card_le_of_mem_chargedHeavyNoiseCandidatesRaw
    {U : Map} {x : BitString} {noiseLen i j thr : ℕ} {H : Finset BitString}
    (hH : H ∈ chargedHeavyNoiseCandidatesRaw U x noiseLen i j thr) :
    H.card ≤ 2 ^ (j - thr + 1) := by
  obtain ⟨B, hB, _, _, rfl⟩ := mem_chargedHeavyNoiseCandidatesRaw_iff.mp hH
  have hBcard : B.card ≤ 2 ^ j := (Finset.mem_filter.mp hB).2
  have hlog : finiteSetLogCard B ≤ j := (finiteSetLogCard_le_iff B j).mpr hBcard
  refine (finiteSetFstHeavyTruncation_card_le B thr).trans ?_
  exact Nat.pow_le_pow_right (by decide) (by omega)

/-- Structural soundness of the charged heavy candidate family. -/
theorem chargedHeavyNoiseCandidates_sound
    (U : Map) (x : BitString) (noiseLen baseBudget : ℕ) (stratum : BitString)
    {H : Finset BitString}
    (hH : H ∈ chargedHeavyNoiseCandidates U x noiseLen baseBudget stratum) :
    x ∈ H ∧ H.Nonempty ∧
      H.card ≤ 2 ^ (stratumSize baseBudget stratum -
        stratumThreshold noiseLen stratum + 1) :=
  ⟨mem_of_mem_chargedHeavyNoiseCandidatesRaw hH,
    nonempty_of_mem_chargedHeavyNoiseCandidatesRaw hH,
    card_le_of_mem_chargedHeavyNoiseCandidatesRaw hH⟩

end Kolmogorov
