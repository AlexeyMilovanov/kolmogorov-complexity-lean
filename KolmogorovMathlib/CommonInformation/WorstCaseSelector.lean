import KolmogorovMathlib.CommonInformation.CompactAdvice
import KolmogorovMathlib.CommonInformation.WorstCaseCounting

/-!
# Common Information: exact data for the Muchnik selector

This file starts the executable selector used in SUV Theorem 223.  It keeps the
three finite streams distinct:

* unconditional outputs of complexity at most `2n - 1`;
* pair codes of complexity at most `3n - 1`;
* compact conditional-description pairs at the two bounds `τ(n) - 1`.

Only their merged cardinality will be supplied as binary advice.  The
declarations here establish the fixed-length candidate list, the sharp advice
bound, and exact recovery of all three semantic finsets from equality with the
merged stage count.  No executable definition inspects a semantic finset.
-/

namespace Kolmogorov

open Nat.Partrec (Code)
open Kolmogorov.CodedFiniteDistribution

/-- The exact integer threshold `⌈11n/10⌉` is primitive recursive. -/
theorem muchnikThreshold_primrec : Primrec muchnikThreshold := by
  unfold muchnikThreshold
  exact Primrec.nat_div.comp
    (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 11) Primrec.id)
      (Primrec.const 9))
    (Primrec.const 10)

/-! ### Fixed-length candidates -/

/-- All encoded pairs `pairCode x y` with both components of length `L`. -/
def fixedLengthPairCodes (L : Nat) : List BitString :=
  (allStrings L).flatMap fun x =>
    (allStrings L).map fun y => pairCode x y

/-- Exact membership in the fixed-length candidate list. -/
theorem mem_fixedLengthPairCodes_iff (L : Nat) (w : BitString) :
    w ∈ fixedLengthPairCodes L ↔
      ∃ x y, x.length = L ∧ y.length = L ∧ w = pairCode x y := by
  simp only [fixedLengthPairCodes, List.mem_flatMap, List.mem_map,
    mem_allStrings]
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact ⟨x, y, hx, hy, rfl⟩
  · rintro ⟨x, y, hx, hy, rfl⟩
    exact ⟨x, hx, y, hy, rfl⟩

/-- The fixed-length candidate list is primitive recursive in `L`. -/
theorem fixedLengthPairCodes_primrec : Primrec fixedLengthPairCodes := by
  unfold fixedLengthPairCodes
  have hbody : Primrec₂ (fun (L : Nat) (x : BitString) =>
      (allStrings L).map fun y => pairCode x y) :=
    (map_pairCode_primrec.comp
      (Primrec.pair Primrec.snd
        (allStrings_primrec.comp Primrec.fst))).to₂
  exact Primrec.list_flatMap allStrings_primrec hbody

/-! ### Semantic advice and its sharp size bound -/

/-- The single terminal count supplied to the selector.  It is the sum of the
three semantic cardinalities, never an executable input to a finite stage. -/
noncomputable def muchnikAdviceCount (V : Map) (n : Nat) : Nat :=
  (compressibleWords V [] (2 * n - 1)).card +
  (compressibleWords V [] (3 * n - 1)).card +
  (conditionalDescriptionPairsLe V
    (muchnikThreshold n - 1) (muchnikThreshold n - 1)).card

/-- The terminal count fits in `3n + 2` binary bits for positive `n`. -/
theorem muchnikAdviceCount_lt (V : Map) {n : Nat} (hn : 0 < n) :
    muchnikAdviceCount V n < 2 ^ (3 * n + 2) := by
  have hThresholdPos : 0 < muchnikThreshold n :=
    (muchnik_lt_threshold_iff 0 n).mpr (by omega)
  have hMarginal :
      (compressibleWords V [] (2 * n - 1)).card < 2 ^ (2 * n) := by
    have h := cardCompressibleWordsLt V [] (2 * n - 1)
    have hExponent : 2 * n - 1 + 1 = 2 * n := by omega
    simpa only [hExponent] using h
  have hPair :
      (compressibleWords V [] (3 * n - 1)).card < 2 ^ (3 * n) := by
    have h := cardCompressibleWordsLt V [] (3 * n - 1)
    have hExponent : 3 * n - 1 + 1 = 3 * n := by omega
    simpa only [hExponent] using h
  have hCompact :
      (conditionalDescriptionPairsLe V
        (muchnikThreshold n - 1) (muchnikThreshold n - 1)).card <
          2 ^ (2 * muchnikThreshold n) := by
    have h := card_conditionalDescriptionPairsLe_lt V
      (muchnikThreshold n - 1) (muchnikThreshold n - 1)
    have hExponent :
        (muchnikThreshold n - 1 + 1) +
          (muchnikThreshold n - 1 + 1) =
            2 * muchnikThreshold n := by omega
    simpa only [hExponent] using h
  by_cases hnOne : n = 1
  · subst n
    norm_num [muchnikAdviceCount, muchnikThreshold] at hMarginal hPair hCompact ⊢
    omega
  · have hnTwo : 2 ≤ n := by omega
    have hThreshold : 2 * muchnikThreshold n ≤ 3 * n := by
      unfold muchnikThreshold
      omega
    have hMarginal' :
        (compressibleWords V [] (2 * n - 1)).card < 2 ^ (3 * n) :=
      hMarginal.trans_le
        (Nat.pow_le_pow_right (by norm_num) (by omega))
    have hCompact' :
        (conditionalDescriptionPairsLe V
          (muchnikThreshold n - 1) (muchnikThreshold n - 1)).card <
            2 ^ (3 * n) :=
      hCompact.trans_le
        (Nat.pow_le_pow_right (by norm_num) hThreshold)
    unfold muchnikAdviceCount
    calc
      (compressibleWords V [] (2 * n - 1)).card +
            (compressibleWords V [] (3 * n - 1)).card +
            (conditionalDescriptionPairsLe V
              (muchnikThreshold n - 1) (muchnikThreshold n - 1)).card
          < 3 * 2 ^ (3 * n) := by omega
      _ < 4 * 2 ^ (3 * n) :=
        Nat.mul_lt_mul_of_pos_right (by norm_num)
          (Nat.pow_pos (by norm_num))
      _ = 2 ^ (3 * n + 2) := by
        rw [pow_add]
        norm_num
        ring

/-- Binary encoding of a count below `2^(3n+2)` gives the exact selector-input
length bound used by the public theorem. -/
theorem muchnik_advice_length_le {n S : Nat}
    (hS : S < 2 ^ (3 * n + 2)) :
    (pairCode (Nat.bits n) (Nat.bits S)).length ≤
      3 * n + 2 * (Nat.bits n).length + 3 := by
  have hBits : (Nat.bits S).length ≤ 3 * n + 2 :=
    length_natBits_lt_pow hS
  rw [length_pairCode]
  omega

/-- Pure additive packaging of the three near-complexity estimates into the two
subtraction-free mutual-information inequalities. -/
theorem mutualInformation_nat_bounds
    {n d kx ky kxy : Nat}
    (hxlo : 2 * n ≤ kx) (hxhi : kx ≤ 2 * n + d)
    (hylo : 2 * n ≤ ky) (hyhi : ky ≤ 2 * n + d)
    (hxylo : 3 * n ≤ kxy) (hxyhi : kxy ≤ 3 * n + d) :
    kxy + n ≤ kx + ky + 2 * d ∧
      kx + ky ≤ kxy + n + 2 * d := by
  omega

/-! ### Merged finite-stage count and exact recovery -/

/-- The executable sum of the three nodup stage lengths at time `t`. -/
def muchnikMergedStageCount (c : Code) (n t : Nat) : Nat :=
  (boundedOutputStage c (2 * n - 1) t).length +
  (boundedOutputStage c (3 * n - 1) t).length +
  (conditionalDescriptionPairsStage c
    (muchnikThreshold n - 1) (muchnikThreshold n - 1) t).length

/-- The merged finite-stage count is computable uniformly in `n` and `t`, for
each fixed decompressor code. -/
theorem muchnikMergedStageCount_computable (c : Code) :
    Computable (fun p : Nat × Nat =>
      muchnikMergedStageCount c p.1 p.2) := by
  have hn : Primrec (fun p : Nat × Nat => p.1) := Primrec.fst
  have ht : Computable (fun p : Nat × Nat => p.2) := Computable.snd
  have hMarginalBound : Computable (fun p : Nat × Nat => 2 * p.1 - 1) :=
    (Primrec.nat_sub.comp
      (Primrec.nat_mul.comp (Primrec.const 2) hn)
      (Primrec.const 1)).to_comp
  have hPairBound : Computable (fun p : Nat × Nat => 3 * p.1 - 1) :=
    (Primrec.nat_sub.comp
      (Primrec.nat_mul.comp (Primrec.const 3) hn)
      (Primrec.const 1)).to_comp
  have hCommonBound :
      Computable (fun p : Nat × Nat => muchnikThreshold p.1 - 1) :=
    (Primrec.nat_sub.comp
      (muchnikThreshold_primrec.comp hn)
      (Primrec.const 1)).to_comp
  have hStage₁ : Computable (fun p : Nat × Nat =>
      boundedOutputStage c (2 * p.1 - 1) p.2) :=
    (boundedOutputStage_computable c).comp
      (hMarginalBound.pair ht)
  have hStage₂ : Computable (fun p : Nat × Nat =>
      boundedOutputStage c (3 * p.1 - 1) p.2) :=
    (boundedOutputStage_computable c).comp
      (hPairBound.pair ht)
  have hStage₃ : Computable (fun p : Nat × Nat =>
      conditionalDescriptionPairsStage c
        (muchnikThreshold p.1 - 1) (muchnikThreshold p.1 - 1) p.2) :=
    (conditionalDescriptionPairsStage_computable c).comp
      ((hCommonBound.pair hCommonBound).pair ht)
  have hLength₁ := Computable.list_length.comp hStage₁
  have hLength₂ := Computable.list_length.comp hStage₂
  have hLength₃ := Computable.list_length.comp hStage₃
  have hAdd : Computable₂ (fun a b : Nat => a + b) :=
    Primrec.nat_add.to_comp
  exact hAdd.comp (hAdd.comp hLength₁ hLength₂) hLength₃

/-- Every unconditional finite stage is contained in its exact semantic
bounded-complexity finset. -/
theorem boundedOutputStage_toFinset_subset_compressibleWords
    {V : Map} {c : Code} (hc : IsCodeFor c V) (m t : Nat) :
    (boundedOutputStage c m t).toFinset ⊆ compressibleWords V [] m := by
  intro w hw
  apply (mem_compressibleWords_iff V [] w m).mpr
  apply (mem_completedBoundedOutput_iff_plainK_le hc m w).mp
  exact (boundedOutputStage_prefix_completed c m t).subset
    (List.mem_toFinset.mp hw)

/-- Every compact finite stage is contained in its exact semantic finset. -/
theorem conditionalDescriptionPairsStage_toFinset_subset
    {V : Map} {c : Code} (hc : IsCodeFor c V) (α β t : Nat) :
    (conditionalDescriptionPairsStage c α β t).toFinset ⊆
      conditionalDescriptionPairsLe V α β := by
  intro w hw
  obtain ⟨z, v, rfl, hz, hv⟩ :=
    mem_conditionalDescriptionPairsStage_sound hc
      (List.mem_toFinset.mp hw)
  exact (mem_conditionalDescriptionPairsLe_iff V α β (pairCode z v)).mpr
    ⟨z, v, rfl, hz, hv⟩

/-- The completed unconditional output list represents exactly the semantic
bounded-complexity finset. -/
theorem completedBoundedOutput_toFinset_eq_compressibleWords
    {V : Map} {c : Code} (hc : IsCodeFor c V) (m : Nat) :
    (completedBoundedOutput c m).toFinset =
      compressibleWords V [] m := by
  ext w
  rw [List.mem_toFinset, mem_completedBoundedOutput_iff_plainK_le hc,
    mem_compressibleWords_iff]
  rfl

/-- Equality of the executable merged count with the true semantic count forces
all three stage finsets to be complete. -/
theorem muchnikMergedStage_exact_of_total
    {V : Map} {c : Code} (hc : IsCodeFor c V)
    {n t : Nat}
    (hcount : muchnikMergedStageCount c n t = muchnikAdviceCount V n) :
    (boundedOutputStage c (2 * n - 1) t).toFinset =
        compressibleWords V [] (2 * n - 1) ∧
    (boundedOutputStage c (3 * n - 1) t).toFinset =
        compressibleWords V [] (3 * n - 1) ∧
    (conditionalDescriptionPairsStage c
      (muchnikThreshold n - 1) (muchnikThreshold n - 1) t).toFinset =
        conditionalDescriptionPairsLe V
          (muchnikThreshold n - 1) (muchnikThreshold n - 1) := by
  let l₁ := boundedOutputStage c (2 * n - 1) t
  let l₂ := boundedOutputStage c (3 * n - 1) t
  let l₃ := conditionalDescriptionPairsStage c
    (muchnikThreshold n - 1) (muchnikThreshold n - 1) t
  let F₁ := compressibleWords V [] (2 * n - 1)
  let F₂ := compressibleWords V [] (3 * n - 1)
  let F₃ := conditionalDescriptionPairsLe V
    (muchnikThreshold n - 1) (muchnikThreshold n - 1)
  have hsub₁ : l₁.toFinset ⊆ F₁ := by
    exact boundedOutputStage_toFinset_subset_compressibleWords hc _ _
  have hsub₂ : l₂.toFinset ⊆ F₂ := by
    exact boundedOutputStage_toFinset_subset_compressibleWords hc _ _
  have hsub₃ : l₃.toFinset ⊆ F₃ := by
    exact conditionalDescriptionPairsStage_toFinset_subset hc _ _ _
  have hle₁ : l₁.length ≤ F₁.card := by
    calc
      l₁.length = l₁.toFinset.card :=
        (List.toFinset_card_of_nodup
          (boundedOutputStage_nodup c (2 * n - 1) t)).symm
      _ ≤ F₁.card := Finset.card_le_card hsub₁
  have hle₂ : l₂.length ≤ F₂.card := by
    calc
      l₂.length = l₂.toFinset.card :=
        (List.toFinset_card_of_nodup
          (boundedOutputStage_nodup c (3 * n - 1) t)).symm
      _ ≤ F₂.card := Finset.card_le_card hsub₂
  have hle₃ : l₃.length ≤ F₃.card := by
    calc
      l₃.length = l₃.toFinset.card :=
        (List.toFinset_card_of_nodup
          (conditionalDescriptionPairsStage_nodup c
            (muchnikThreshold n - 1) (muchnikThreshold n - 1) t)).symm
      _ ≤ F₃.card := Finset.card_le_card hsub₃
  have hsum : l₁.length + l₂.length + l₃.length =
      F₁.card + F₂.card + F₃.card := by
    simpa only [muchnikMergedStageCount, muchnikAdviceCount, l₁, l₂, l₃,
      F₁, F₂, F₃] using hcount
  obtain ⟨hcard₁, hcard₂, hcard₃⟩ :=
    three_eq_of_le_and_sum_eq hle₁ hle₂ hle₃ hsum
  exact ⟨
    toFinset_eq_of_subset_card
      (boundedOutputStage_nodup c (2 * n - 1) t) hsub₁ hcard₁,
    toFinset_eq_of_subset_card
      (boundedOutputStage_nodup c (3 * n - 1) t) hsub₂ hcard₂,
    toFinset_eq_of_subset_card
      (conditionalDescriptionPairsStage_nodup c
        (muchnikThreshold n - 1) (muchnikThreshold n - 1) t)
      hsub₃ hcard₃⟩

/-- At some finite stage the executable merged count reaches the genuine
semantic advice total.  This is the termination fact required by the later
unbounded stage search. -/
theorem exists_muchnikMergedStageCount_eq
    {V : Map} {c : Code} (hc : IsCodeFor c V) (n : Nat) :
    ∃ t, muchnikMergedStageCount c n t = muchnikAdviceCount V n := by
  obtain ⟨T₃, hT₃⟩ :=
    exists_conditionalDescriptionPairsStage_complete hc
      (muchnikThreshold n - 1) (muchnikThreshold n - 1)
  let T₁ := boundedOutputCompletionTime c (2 * n - 1)
  let T₂ := boundedOutputCompletionTime c (3 * n - 1)
  let T := max T₁ (max T₂ T₃)
  have hT₁ : T₁ ≤ T := le_max_left _ _
  have hT₂ : T₂ ≤ T := le_trans (le_max_left _ _) (le_max_right _ _)
  have hT₃le : T₃ ≤ T := le_trans (le_max_right _ _) (le_max_right _ _)
  have hStage₁ :
      boundedOutputStage c (2 * n - 1) T =
        completedBoundedOutput c (2 * n - 1) :=
    boundedOutputStage_eq_completed_of_completion_le c _ _ hT₁
  have hStage₂ :
      boundedOutputStage c (3 * n - 1) T =
        completedBoundedOutput c (3 * n - 1) :=
    boundedOutputStage_eq_completed_of_completion_le c _ _ hT₂
  have hPrefix₃ :
      conditionalDescriptionPairsStage c
          (muchnikThreshold n - 1) (muchnikThreshold n - 1) T₃ <+:
        conditionalDescriptionPairsStage c
          (muchnikThreshold n - 1) (muchnikThreshold n - 1) T :=
    conditionalDescriptionPairsStage_prefix_of_le c
      (muchnikThreshold n - 1) (muchnikThreshold n - 1) hT₃le
  have hStage₃ :
      (conditionalDescriptionPairsStage c
        (muchnikThreshold n - 1) (muchnikThreshold n - 1) T).toFinset =
          conditionalDescriptionPairsLe V
            (muchnikThreshold n - 1) (muchnikThreshold n - 1) :=
    complete_stage_persists hT₃le hPrefix₃ hT₃
      (conditionalDescriptionPairsStage_toFinset_subset hc _ _ _)
  refine ⟨T, ?_⟩
  unfold muchnikMergedStageCount muchnikAdviceCount
  have hCard₁ :
      (boundedOutputStage c (2 * n - 1) T).length =
        (compressibleWords V [] (2 * n - 1)).card := by
    rw [hStage₁]
    calc
      (completedBoundedOutput c (2 * n - 1)).length =
          (completedBoundedOutput c (2 * n - 1)).toFinset.card :=
        (List.toFinset_card_of_nodup
          (boundedOutputStage_nodup c (2 * n - 1)
            (maxHaltingStage c (2 * n - 1)))).symm
      _ = (compressibleWords V [] (2 * n - 1)).card :=
        congrArg Finset.card
          (completedBoundedOutput_toFinset_eq_compressibleWords hc _)
  have hCard₂ :
      (boundedOutputStage c (3 * n - 1) T).length =
        (compressibleWords V [] (3 * n - 1)).card := by
    rw [hStage₂]
    calc
      (completedBoundedOutput c (3 * n - 1)).length =
          (completedBoundedOutput c (3 * n - 1)).toFinset.card :=
        (List.toFinset_card_of_nodup
          (boundedOutputStage_nodup c (3 * n - 1)
            (maxHaltingStage c (3 * n - 1)))).symm
      _ = (compressibleWords V [] (3 * n - 1)).card :=
        congrArg Finset.card
          (completedBoundedOutput_toFinset_eq_compressibleWords hc _)
  have hCard₃ :
      (conditionalDescriptionPairsStage c
        (muchnikThreshold n - 1) (muchnikThreshold n - 1) T).length =
          (conditionalDescriptionPairsLe V
            (muchnikThreshold n - 1) (muchnikThreshold n - 1)).card := by
    calc
      (conditionalDescriptionPairsStage c
          (muchnikThreshold n - 1) (muchnikThreshold n - 1) T).length =
          (conditionalDescriptionPairsStage c
            (muchnikThreshold n - 1)
            (muchnikThreshold n - 1) T).toFinset.card :=
        (List.toFinset_card_of_nodup
          (conditionalDescriptionPairsStage_nodup c
            (muchnikThreshold n - 1)
            (muchnikThreshold n - 1) T)).symm
      _ = (conditionalDescriptionPairsLe V
            (muchnikThreshold n - 1)
            (muchnikThreshold n - 1)).card :=
        congrArg Finset.card hStage₃
  omega

def muchnikBadAtStage (c : Code) (n t : Nat) (w : BitString) : Bool :=
  let marginal := boundedOutputStage c (2 * n - 1) t
  let pairs := boundedOutputStage c (3 * n - 1) t
  let conditional := conditionalDescriptionPairsStage c
    (muchnikThreshold n - 1) (muchnikThreshold n - 1) t
  decide (decodeFirst w ∈ marginal) ||
    decide (decodeSecond w ∈ marginal) ||
    decide (pairCode (decodeFirst w) (decodeSecond w) ∈ pairs) ||
    conditional.any fun p =>
      decide (pairCode (decodeFirst p) (decodeFirst w) ∈ conditional) &&
      decide (pairCode (decodeFirst p) (decodeSecond w) ∈ conditional)

/-- The complete-stage bad-candidate test is primitive recursive in the two
stage parameters and the candidate word. -/
theorem muchnikBadAtStage_primrec (c : Code) :
    Primrec (fun q : (Nat × Nat) × BitString =>
      muchnikBadAtStage c q.1.1 q.1.2 q.2) := by
  have hn : Primrec (fun q : (Nat × Nat) × BitString => q.1.1) :=
    Primrec.fst.comp Primrec.fst
  have ht : Primrec (fun q : (Nat × Nat) × BitString => q.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hw : Primrec (fun q : (Nat × Nat) × BitString => q.2) :=
    Primrec.snd
  have hMarginalBound : Primrec (fun q : (Nat × Nat) × BitString =>
      2 * q.1.1 - 1) :=
    Primrec.nat_sub.comp
      (Primrec.nat_mul.comp (Primrec.const 2) hn)
      (Primrec.const 1)
  have hPairBound : Primrec (fun q : (Nat × Nat) × BitString =>
      3 * q.1.1 - 1) :=
    Primrec.nat_sub.comp
      (Primrec.nat_mul.comp (Primrec.const 3) hn)
      (Primrec.const 1)
  have hCommonBound : Primrec (fun q : (Nat × Nat) × BitString =>
      muchnikThreshold q.1.1 - 1) :=
    Primrec.nat_sub.comp
      (muchnikThreshold_primrec.comp hn)
      (Primrec.const 1)
  have hMarginal : Primrec (fun q : (Nat × Nat) × BitString =>
      boundedOutputStage c (2 * q.1.1 - 1) q.1.2) :=
    (boundedOutputStage_primrec c).comp
      (Primrec.pair hMarginalBound ht)
  have hPairs : Primrec (fun q : (Nat × Nat) × BitString =>
      boundedOutputStage c (3 * q.1.1 - 1) q.1.2) :=
    (boundedOutputStage_primrec c).comp
      (Primrec.pair hPairBound ht)
  have hConditional : Primrec (fun q : (Nat × Nat) × BitString =>
      conditionalDescriptionPairsStage c
        (muchnikThreshold q.1.1 - 1) (muchnikThreshold q.1.1 - 1) q.1.2) :=
    (conditionalDescriptionPairsStage_primrec c).comp
      (Primrec.pair (Primrec.pair hCommonBound hCommonBound) ht)
  have hLeft : Primrec (fun q : (Nat × Nat) × BitString =>
      decide (decodeFirst q.2 ∈
        boundedOutputStage c (2 * q.1.1 - 1) q.1.2)) :=
    bitString_mem_primrec.comp
      (decodeFirst_primrec'.comp hw) hMarginal
  have hRight : Primrec (fun q : (Nat × Nat) × BitString =>
      decide (decodeSecond q.2 ∈
        boundedOutputStage c (2 * q.1.1 - 1) q.1.2)) :=
    bitString_mem_primrec.comp
      (decodeSecond_primrec'.comp hw) hMarginal
  have hPair : Primrec (fun q : (Nat × Nat) × BitString =>
      decide (pairCode (decodeFirst q.2) (decodeSecond q.2) ∈
        boundedOutputStage c (3 * q.1.1 - 1) q.1.2)) :=
    bitString_mem_primrec.comp
      (pairCode_primrec.comp
        (decodeFirst_primrec'.comp hw)
        (decodeSecond_primrec'.comp hw))
      hPairs
  have hCommonPred : Primrec₂
      (fun (q : (Nat × Nat) × BitString) (p : BitString) =>
        decide (pairCode (decodeFirst p) (decodeFirst q.2) ∈
          conditionalDescriptionPairsStage c
            (muchnikThreshold q.1.1 - 1)
            (muchnikThreshold q.1.1 - 1) q.1.2) &&
        decide (pairCode (decodeFirst p) (decodeSecond q.2) ∈
          conditionalDescriptionPairsStage c
            (muchnikThreshold q.1.1 - 1)
            (muchnikThreshold q.1.1 - 1) q.1.2)) := by
    have hFirst : Primrec (fun r :
        ((Nat × Nat) × BitString) × BitString =>
        decide (pairCode (decodeFirst r.2) (decodeFirst r.1.2) ∈
          conditionalDescriptionPairsStage c
            (muchnikThreshold r.1.1.1 - 1)
            (muchnikThreshold r.1.1.1 - 1) r.1.1.2)) :=
      bitString_mem_primrec.comp
        (pairCode_primrec.comp
          (decodeFirst_primrec'.comp Primrec.snd)
          (decodeFirst_primrec'.comp
            (Primrec.snd.comp Primrec.fst)))
        (hConditional.comp Primrec.fst)
    have hSecond : Primrec (fun r :
        ((Nat × Nat) × BitString) × BitString =>
        decide (pairCode (decodeFirst r.2) (decodeSecond r.1.2) ∈
          conditionalDescriptionPairsStage c
            (muchnikThreshold r.1.1.1 - 1)
            (muchnikThreshold r.1.1.1 - 1) r.1.1.2)) :=
      bitString_mem_primrec.comp
        (pairCode_primrec.comp
          (decodeFirst_primrec'.comp Primrec.snd)
          (decodeSecond_primrec'.comp
            (Primrec.snd.comp Primrec.fst)))
        (hConditional.comp Primrec.fst)
    exact (Primrec.and.comp hFirst hSecond).to₂
  have hCommon : Primrec (fun q : (Nat × Nat) × BitString =>
      (conditionalDescriptionPairsStage c
        (muchnikThreshold q.1.1 - 1)
        (muchnikThreshold q.1.1 - 1) q.1.2).any
          (fun p =>
            decide (pairCode (decodeFirst p) (decodeFirst q.2) ∈
              conditionalDescriptionPairsStage c
                (muchnikThreshold q.1.1 - 1)
                (muchnikThreshold q.1.1 - 1) q.1.2) &&
            decide (pairCode (decodeFirst p) (decodeSecond q.2) ∈
              conditionalDescriptionPairsStage c
                (muchnikThreshold q.1.1 - 1)
                (muchnikThreshold q.1.1 - 1) q.1.2))) :=
    list_any_primrec hConditional hCommonPred
  unfold muchnikBadAtStage
  exact Primrec.or.comp
    (Primrec.or.comp (Primrec.or.comp hLeft hRight) hPair) hCommon

theorem muchnikBadAtStage_false_iff
    {V : Map} {c : Code} (hc : IsCodeFor c V)
    {n t : Nat} (hn : 0 < n)
    (hcount : muchnikMergedStageCount c n t = muchnikAdviceCount V n)
    (w : BitString) :
    muchnikBadAtStage c n t w = false ↔
      (2 * n : ENat) ≤ plainK V (decodeFirst w) ∧
      (2 * n : ENat) ≤ plainK V (decodeSecond w) ∧
      (3 * n : ENat) ≤ pairPlainK V (decodeFirst w) (decodeSecond w) ∧
      (muchnikThreshold n, muchnikThreshold n, muchnikThreshold n) ∉
        CommonInformationRegion V (decodeFirst w) (decodeSecond w) := by
  obtain ⟨hMarginal, hPairs, hConditional⟩ :=
    muchnikMergedStage_exact_of_total hc hcount
  let marginal := boundedOutputStage c (2 * n - 1) t
  let pairs := boundedOutputStage c (3 * n - 1) t
  let conditional := conditionalDescriptionPairsStage c
    (muchnikThreshold n - 1) (muchnikThreshold n - 1) t
  let x := decodeFirst w
  let y := decodeSecond w
  have hTwoN : 0 < 2 * n := Nat.mul_pos (by norm_num) hn
  have hThreeN : 0 < 3 * n := Nat.mul_pos (by norm_num) hn
  have hMarginalMem (u : BitString) :
      u ∉ marginal ↔ (2 * n : ENat) ≤ plainK V u := by
    have hfinset :
        marginal.toFinset = compressibleWords V [] (2 * n - 1) := by
      simpa only [marginal] using hMarginal
    rw [← List.mem_toFinset, hfinset, mem_compressibleWords_iff]
    constructor
    · intro hnot
      apply le_of_not_gt
      intro hlt
      apply hnot
      exact (enat_lt_coe_iff_le_pred (q := plainK V u) hTwoN).mp hlt
    · intro hlo hle
      exact (not_lt_of_ge hlo)
        ((enat_lt_coe_iff_le_pred (q := plainK V u) hTwoN).mpr hle)
  have hPairMem :
      pairCode x y ∉ pairs ↔ (3 * n : ENat) ≤ pairPlainK V x y := by
    have hfinset :
        pairs.toFinset = compressibleWords V [] (3 * n - 1) := by
      simpa only [pairs] using hPairs
    rw [← List.mem_toFinset, hfinset, mem_compressibleWords_iff]
    change (¬plainK V (pairCode x y) ≤ ((3 * n - 1 : Nat) : ENat)) ↔
      (3 * n : ENat) ≤ pairPlainK V x y
    constructor
    · intro hnot
      apply le_of_not_gt
      intro hlt
      apply hnot
      exact (enat_lt_coe_iff_le_pred
        (q := pairPlainK V x y) hThreeN).mp hlt
    · intro hlo hle
      exact (not_lt_of_ge hlo)
        ((enat_lt_coe_iff_le_pred
          (q := pairPlainK V x y) hThreeN).mpr hle)
  have hCommonExists :
      (∃ p ∈ conditional,
          pairCode (decodeFirst p) x ∈ conditional ∧
          pairCode (decodeFirst p) y ∈ conditional) ↔
        ∃ z, plainK V z ≤ ((muchnikThreshold n - 1 : Nat) : ENat) ∧
          condK V x z ≤ ((muchnikThreshold n - 1 : Nat) : ENat) ∧
          condK V y z ≤ ((muchnikThreshold n - 1 : Nat) : ENat) := by
    constructor
    · rintro ⟨p, _hp, hpx, hpy⟩
      have hpxSem :
          pairCode (decodeFirst p) x ∈
            conditionalDescriptionPairsLe V
              (muchnikThreshold n - 1) (muchnikThreshold n - 1) := by
        rw [← hConditional]
        exact List.mem_toFinset.mpr hpx
      have hpySem :
          pairCode (decodeFirst p) y ∈
            conditionalDescriptionPairsLe V
              (muchnikThreshold n - 1) (muchnikThreshold n - 1) := by
        rw [← hConditional]
        exact List.mem_toFinset.mpr hpy
      obtain ⟨zx, vx, hxEq, hzx, hvx⟩ :=
        (mem_conditionalDescriptionPairsLe_iff V
          (muchnikThreshold n - 1) (muchnikThreshold n - 1)
          (pairCode (decodeFirst p) x)).mp hpxSem
      obtain ⟨zy, vy, hyEq, _hzy, hvy⟩ :=
        (mem_conditionalDescriptionPairsLe_iff V
          (muchnikThreshold n - 1) (muchnikThreshold n - 1)
          (pairCode (decodeFirst p) y)).mp hpySem
      have hxComponents : (decodeFirst p, x) = (zx, vx) :=
        pairCode_injective hxEq
      have hyComponents : (decodeFirst p, y) = (zy, vy) :=
        pairCode_injective hyEq
      cases hxComponents
      cases hyComponents
      exact ⟨decodeFirst p, hzx, hvx, hvy⟩
    · rintro ⟨z, hz, hx, hy⟩
      have hxSem :
          pairCode z x ∈ conditionalDescriptionPairsLe V
            (muchnikThreshold n - 1) (muchnikThreshold n - 1) :=
        (mem_conditionalDescriptionPairsLe_iff V
          (muchnikThreshold n - 1) (muchnikThreshold n - 1)
          (pairCode z x)).mpr ⟨z, x, rfl, hz, hx⟩
      have hySem :
          pairCode z y ∈ conditionalDescriptionPairsLe V
            (muchnikThreshold n - 1) (muchnikThreshold n - 1) :=
        (mem_conditionalDescriptionPairsLe_iff V
          (muchnikThreshold n - 1) (muchnikThreshold n - 1)
          (pairCode z y)).mpr ⟨z, y, rfl, hz, hy⟩
      have hxStage : pairCode z x ∈ conditional := by
        apply List.mem_toFinset.mp
        rw [hConditional]
        exact hxSem
      have hyStage : pairCode z y ∈ conditional := by
        apply List.mem_toFinset.mp
        rw [hConditional]
        exact hySem
      refine ⟨pairCode z x, hxStage, ?_, ?_⟩
      · simpa only [decodeFirst_pairCode] using hxStage
      · simpa only [decodeFirst_pairCode] using hyStage
  have hNoCommon :
      (¬∃ p ∈ conditional,
          pairCode (decodeFirst p) x ∈ conditional ∧
          pairCode (decodeFirst p) y ∈ conditional) ↔
        (muchnikThreshold n, muchnikThreshold n, muchnikThreshold n) ∉
          CommonInformationRegion V x y := by
    have hThresholdPos : 0 < muchnikThreshold n :=
      (muchnik_lt_threshold_iff 0 n).mpr (by omega)
    constructor
    · intro hnone hregion
      apply hnone
      apply hCommonExists.mpr
      change ∃ z,
        plainK V z < (muchnikThreshold n : ENat) ∧
        condK V x z < (muchnikThreshold n : ENat) ∧
        condK V y z < (muchnikThreshold n : ENat) at hregion
      obtain ⟨z, hz, hx, hy⟩ := hregion
      exact ⟨z,
        (enat_lt_coe_iff_le_pred hThresholdPos).mp hz,
        (enat_lt_coe_iff_le_pred hThresholdPos).mp hx,
        (enat_lt_coe_iff_le_pred hThresholdPos).mp hy⟩
    · intro hregion hex
      apply hregion
      change ∃ z,
        plainK V z < (muchnikThreshold n : ENat) ∧
        condK V x z < (muchnikThreshold n : ENat) ∧
        condK V y z < (muchnikThreshold n : ENat)
      obtain ⟨z, hz, hx, hy⟩ := hCommonExists.mp hex
      exact ⟨z,
        (enat_lt_coe_iff_le_pred hThresholdPos).mpr hz,
        (enat_lt_coe_iff_le_pred hThresholdPos).mpr hx,
        (enat_lt_coe_iff_le_pred hThresholdPos).mpr hy⟩
  have hCommonBool :
      conditional.any (fun p =>
        decide (pairCode (decodeFirst p) x ∈ conditional) &&
        decide (pairCode (decodeFirst p) y ∈ conditional)) = false ↔
      ¬∃ p ∈ conditional,
        pairCode (decodeFirst p) x ∈ conditional ∧
        pairCode (decodeFirst p) y ∈ conditional := by
    simp
  change
    (decide (x ∈ marginal) || decide (y ∈ marginal) ||
      decide (pairCode x y ∈ pairs) ||
      conditional.any (fun p =>
        decide (pairCode (decodeFirst p) x ∈ conditional) &&
        decide (pairCode (decodeFirst p) y ∈ conditional))) = false ↔ _
  simp only [Bool.or_eq_false_eq_eq_false_and_eq_false,
    decide_eq_false_iff_not]
  rw [hCommonBool, hMarginalMem x, hMarginalMem y, hPairMem, hNoCommon]
  simp only [x, y, and_assoc]

theorem exists_fixedLengthPairCode_not_bad
    {V : Map} {c : Code} (hc : IsCodeFor c V)
    {n t : Nat} (hn : 0 < n)
    (hcount : muchnikMergedStageCount c n t = muchnikAdviceCount V n) :
    ∃ w ∈ fixedLengthPairCodes (2 * n + 2), muchnikBadAtStage c n t w = false := by
  obtain ⟨x, y, hsurvivor⟩ := exists_muchnikSurvivor V hn
  refine ⟨pairCode x y, ?_, ?_⟩
  · apply (mem_fixedLengthPairCodes_iff (2 * n + 2) (pairCode x y)).mpr
    exact ⟨x, y, hsurvivor.1, hsurvivor.2.1, rfl⟩
  · apply (muchnikBadAtStage_false_iff hc hn hcount (pairCode x y)).mpr
    simpa only [decodeFirst_pairCode, decodeSecond_pairCode] using hsurvivor.2.2

/-- At every complete merged stage, the executable first-good-candidate search
returns a semantic Muchnik survivor. -/
theorem muchnikFindAtStage_spec
    {V : Map} {c : Code} (hc : IsCodeFor c V)
    {n t : Nat} (hn : 0 < n)
    (hcount : muchnikMergedStageCount c n t = muchnikAdviceCount V n) :
    ∃ w,
      (fixedLengthPairCodes (2 * n + 2)).find?
        (fun u => !muchnikBadAtStage c n t u) = some w ∧
      IsMuchnikSurvivor V n (decodeFirst w) (decodeSecond w) := by
  obtain ⟨w₀, hw₀Candidates, hw₀Good⟩ :=
    exists_fixedLengthPairCode_not_bad hc hn hcount
  have hw₀Predicate : (!muchnikBadAtStage c n t w₀) = true := by
    rw [hw₀Good]
    rfl
  have hFindSome :
      ∃ w, (fixedLengthPairCodes (2 * n + 2)).find?
        (fun u => !muchnikBadAtStage c n t u) = some w := by
    apply Option.isSome_iff_exists.mp
    rw [List.find?_isSome]
    exact ⟨w₀, hw₀Candidates, hw₀Predicate⟩
  obtain ⟨w, hwFind⟩ := hFindSome
  have hwCandidates : w ∈ fixedLengthPairCodes (2 * n + 2) :=
    List.mem_of_find?_eq_some hwFind
  have hwPredicate : (!muchnikBadAtStage c n t w) = true :=
    List.find?_some
      (p := fun u => !muchnikBadAtStage c n t u)
      (a := w) (l := fixedLengthPairCodes (2 * n + 2)) hwFind
  have hwGood : muchnikBadAtStage c n t w = false := by
    cases hbad : muchnikBadAtStage c n t w with
    | false => rfl
    | true =>
        have hfalse : false = true := by simpa only [hbad, Bool.not_true] using hwPredicate
        exact Bool.noConfusion hfalse
  have hwSemantics :=
    (muchnikBadAtStage_false_iff hc hn hcount w).mp hwGood
  obtain ⟨x, y, hxLength, hyLength, hwPair⟩ :=
    (mem_fixedLengthPairCodes_iff (2 * n + 2) w).mp hwCandidates
  refine ⟨w, hwFind, ?_⟩
  subst w
  simpa only [IsMuchnikSurvivor, decodeFirst_pairCode,
    decodeSecond_pairCode] using
    And.intro hxLength (And.intro hyLength hwSemantics)

def muchnikSelectorN (input : BitString) : Nat :=
  bitsToNat (decodeFirst input)

def muchnikSelectorTotal (input : BitString) : Nat :=
  bitsToNat (decodeSecond input)

def muchnikSelectorCandidates (input : BitString) : List BitString :=
  fixedLengthPairCodes (2 * muchnikSelectorN input + 2)

def muchnikSelectorGoodAtStage
    (c : Code) (input : BitString) (t : Nat) (w : BitString) : Bool :=
  !muchnikBadAtStage c (muchnikSelectorN input) t w

theorem muchnikSelectorGoodAtStage_eq_true_iff
    (c : Code) (input : BitString) (t : Nat) (w : BitString) :
    muchnikSelectorGoodAtStage c input t w = true ↔
      muchnikBadAtStage c (muchnikSelectorN input) t w = false := by
  unfold muchnikSelectorGoodAtStage
  cases muchnikBadAtStage c (muchnikSelectorN input) t w <;> simp

theorem muchnikSelectorN_primrec : Primrec muchnikSelectorN :=
  bitsToNat_primrec.comp decodeFirst_primrec'

theorem muchnikSelectorTotal_primrec : Primrec muchnikSelectorTotal :=
  bitsToNat_primrec.comp decodeSecond_primrec'

theorem muchnikSelectorCandidates_primrec :
    Primrec muchnikSelectorCandidates := by
  unfold muchnikSelectorCandidates
  exact fixedLengthPairCodes_primrec.comp
    (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 2) muchnikSelectorN_primrec)
      (Primrec.const 2))

theorem muchnikSelectorGoodAtStage_primrec (c : Code) :
    Primrec (fun q : (BitString × Nat) × BitString =>
      muchnikSelectorGoodAtStage c q.1.1 q.1.2 q.2) := by
  let f : ((BitString × Nat) × BitString) → ((Nat × Nat) × BitString) :=
    fun q => ((muchnikSelectorN q.1.1, q.1.2), q.2)
  have hf : Primrec f :=
    Primrec.pair
      (Primrec.pair
        (muchnikSelectorN_primrec.comp
          (Primrec.fst.comp Primrec.fst))
        (Primrec.snd.comp Primrec.fst))
      Primrec.snd
  have hbad : Primrec (fun q =>
      muchnikBadAtStage c (f q).1.1 (f q).1.2 (f q).2) :=
    (muchnikBadAtStage_primrec c).comp hf
  exact (Primrec.not.comp hbad).of_eq (fun q => by
    simp only [muchnikSelectorGoodAtStage, f])

noncomputable def muchnikSelector (c : Code) : BitString → Part BitString := fun input =>
  let n := muchnikSelectorN input
  let total := muchnikSelectorTotal input
  (Nat.rfind (fun t =>
    Part.some (muchnikMergedStageCount c n t == total))).bind fun t =>
      Part.ofOption
        ((muchnikSelectorCandidates input).find?
          (muchnikSelectorGoodAtStage c input t))

theorem muchnikSelectorCandidates_eq_of_n
    {input : BitString} {n : Nat} (hn : muchnikSelectorN input = n) :
    muchnikSelectorCandidates input =
      fixedLengthPairCodes (2 * n + 2) := by
  simp only [muchnikSelectorCandidates, hn]

theorem muchnikSelectorGoodAtStage_eq_of_n
    (c : Code) {input : BitString} {n t : Nat}
    (hn : muchnikSelectorN input = n) :
    muchnikSelectorGoodAtStage c input t =
      fun w => !muchnikBadAtStage c n t w := by
  funext w
  simp only [muchnikSelectorGoodAtStage, hn]

theorem muchnikSelector_eq_some_of_search
    (c : Code) (input : BitString) (t : Nat) (w : BitString)
    (ht : t ∈ Nat.rfind (fun s =>
      Part.some (muchnikMergedStageCount c (muchnikSelectorN input) s ==
        muchnikSelectorTotal input)))
    (hw : (muchnikSelectorCandidates input).find?
      (muchnikSelectorGoodAtStage c input t) = some w) :
    muchnikSelector c input = Part.some w := by
  apply Part.eq_some_iff.mpr
  unfold muchnikSelector
  rw [Part.mem_bind_iff]
  refine ⟨t, ht, ?_⟩
  rw [hw]
  exact Part.mem_some w

theorem muchnikSelector_partrec (c : Code) : Partrec (muchnikSelector c) := by
  let countInput : BitString × Nat → Nat × Nat :=
    fun st => (muchnikSelectorN st.1, st.2)
  have hCountInput : Computable countInput :=
    (muchnikSelectorN_primrec.to_comp.comp Computable.fst).pair Computable.snd
  have hCount : Computable (fun st : BitString × Nat =>
      muchnikMergedStageCount c
        (muchnikSelectorN st.1) st.2) :=
    ((muchnikMergedStageCount_computable c).comp hCountInput).of_eq
      (fun _ => rfl)
  have hCheck : Computable₂ (fun (input : BitString) (t : Nat) =>
      muchnikMergedStageCount c
        (muchnikSelectorN input) t ==
          muchnikSelectorTotal input) :=
    (Primrec.beq.to_comp.comp
      hCount
      (muchnikSelectorTotal_primrec.to_comp.comp Computable.fst)).to₂
  have hSearch : Partrec (fun input : BitString =>
      Nat.rfind (fun t =>
        Part.some (muchnikMergedStageCount c
          (muchnikSelectorN input) t ==
            muchnikSelectorTotal input))) :=
    Partrec.rfind hCheck.partrec₂
  have hFind : Primrec (fun st : BitString × Nat =>
      (muchnikSelectorCandidates st.1).find?
        (muchnikSelectorGoodAtStage c st.1 st.2)) :=
    list_find?_primrec
      (muchnikSelectorCandidates_primrec.comp Primrec.fst)
      (muchnikSelectorGoodAtStage_primrec c).to₂
  have hPost : Partrec₂
      (fun (input : BitString) (t : Nat) =>
        Part.ofOption
          ((muchnikSelectorCandidates input).find?
            (muchnikSelectorGoodAtStage c input t))) :=
    hFind.to_comp.ofOption.to₂
  unfold muchnikSelector
  exact Partrec.bind hSearch hPost

theorem muchnikSelector_spec
    {V : Map} {c : Code} (hc : IsCodeFor c V)
    {n : Nat} (hn : 0 < n) :
    ∃ x y,
      muchnikSelector c
        (pairCode (Nat.bits n) (Nat.bits (muchnikAdviceCount V n))) =
          Part.some (pairCode x y) ∧
      IsMuchnikSurvivor V n x y := by
  let input :=
    pairCode (Nat.bits n) (Nat.bits (muchnikAdviceCount V n))
  have hInputN : muchnikSelectorN input = n := by
    simp only [muchnikSelectorN, input, decodeFirst_pairCode, bitsToNat_bits]
  have hInputTotal : muchnikSelectorTotal input = muchnikAdviceCount V n := by
    simp only [muchnikSelectorTotal, input, decodeSecond_pairCode, bitsToNat_bits]
  let hex : ∃ t,
      muchnikMergedStageCount c n t = muchnikAdviceCount V n :=
    exists_muchnikMergedStageCount_eq hc n
  let t₀ := Nat.find hex
  have ht₀Count :
      muchnikMergedStageCount c n t₀ = muchnikAdviceCount V n :=
    Nat.find_spec hex
  have ht₀Search :
      t₀ ∈ Nat.rfind (fun t =>
        Part.some (muchnikMergedStageCount c (muchnikSelectorN input) t ==
          muchnikSelectorTotal input)) := by
    simp only [hInputN, hInputTotal]
    refine Nat.mem_rfind.mpr ⟨?_, ?_⟩
    · simp [ht₀Count]
    · intro m hm
      have hne : muchnikMergedStageCount c n m ≠ muchnikAdviceCount V n :=
        Nat.find_min hex hm
      simp [hne]
  obtain ⟨w, hwFindDirect, hSurvivor⟩ :=
    muchnikFindAtStage_spec hc hn ht₀Count
  have hwFind :
      (muchnikSelectorCandidates input).find?
        (muchnikSelectorGoodAtStage c input t₀) = some w := by
    rw [muchnikSelectorCandidates_eq_of_n hInputN,
      muchnikSelectorGoodAtStage_eq_of_n c hInputN]
    exact hwFindDirect
  have hwCandidates : w ∈ fixedLengthPairCodes (2 * n + 2) :=
    List.mem_of_find?_eq_some hwFindDirect
  obtain ⟨x, y, _hxLength, _hyLength, hwPair⟩ :=
    (mem_fixedLengthPairCodes_iff (2 * n + 2) w).mp hwCandidates
  subst w
  exact ⟨x, y,
    muchnikSelector_eq_some_of_search c input t₀ (pairCode x y)
      ht₀Search hwFind,
    by simpa only [decodeFirst_pairCode, decodeSecond_pairCode] using hSurvivor⟩

end Kolmogorov
