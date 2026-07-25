/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/

import KolmogorovMathlib.Restricted.FamilyCurve.EffectiveRun
import KolmogorovMathlib.Restricted.FamilyCurve.BadStream
import KolmogorovMathlib.Restricted.FamilyCurve.AnchoredRun

/-!
# Bounds for the effective sampled run

This file relates decoded bad-code unions to the run state and proves the cardinality and
rebuild bounds used by the anchored chain.
-/

namespace Kolmogorov

open Nat.Partrec (Code)

/-- Membership in a decoded prefix union is witnessed by one of the decoded
bad sets before the prefix bound. -/
lemma mem_restrictedBadPrefixUnion_iff
    (bads : List (Finset BitString)) (count : ℕ) (x : BitString) :
    x ∈ restrictedBadPrefixUnion bads count ↔
      ∃ i < count, x ∈ bads.getD i ∅ := by
  induction count with
  | zero => simp [restrictedBadPrefixUnion]
  | succ count ih =>
      rw [restrictedBadPrefixUnion, Finset.mem_union]
      constructor
      · rintro (hprevious | hlast)
        · obtain ⟨i, hi, hxi⟩ := ih.mp hprevious
          exact ⟨i, by omega, hxi⟩
        · exact ⟨count, Nat.lt_succ_self count, hlast⟩
      · rintro ⟨i, hi, hxi⟩
        by_cases hilast : i = count
        · subst i
          exact Or.inr hxi
        · exact Or.inl (ih.mpr ⟨i, by omega, hxi⟩)

/-- The decoded union contains exactly the elements of the decoded sets whose
codes occur in the input list. -/
lemma mem_restrictedDecodedBadCodesUnion_iff
    (codes : List BitString) (x : BitString) :
    x ∈ restrictedDecodedBadCodesUnion codes ↔
      ∃ w ∈ codes, x ∈ (decodeCoverCodeList w).toFinset := by
  rw [restrictedDecodedBadCodesUnion,
    mem_restrictedBadPrefixUnion_iff]
  constructor
  · rintro ⟨i, hi, hxi⟩
    have himap : i < (codes.map fun w =>
        (decodeCoverCodeList w).toFinset).length := by simpa using hi
    rw [List.getD_eq_getElem _ _ himap] at hxi
    simp only [List.getElem_map] at hxi
    exact ⟨codes[i], List.getElem_mem hi, hxi⟩
  · rintro ⟨w, hw, hxw⟩
    obtain ⟨i, hi, hwi⟩ := List.getElem_of_mem hw
    refine ⟨i, by simpa, ?_⟩
    have himap : i < (codes.map fun v =>
        (decodeCoverCodeList v).toFinset).length := by simpa
    rw [List.getD_eq_getElem _ _ himap]
    simp only [List.getElem_map]
    simpa [hwi] using hxw

/-- Decoding a concatenation unions the decoded bad sets from its two parts. -/
lemma restrictedDecodedBadCodesUnion_append
    (left right : List BitString) :
    restrictedDecodedBadCodesUnion (left ++ right) =
      restrictedDecodedBadCodesUnion left ∪
        restrictedDecodedBadCodesUnion right := by
  ext x
  simp only [mem_restrictedDecodedBadCodesUnion_iff, Finset.mem_union,
    List.mem_append]
  aesop

/-- The explicit processed-code trace is exactly the stream prefix whose
chronological batches have been executed by the next run time. -/
lemma restrictedAnchoredProcessedBadCodes_succ
    (c : Code) (𝒜 : DescriptionFamily)
    {n k N : ℕ} {target : ℕ → ℕ}
    (streamSlack : ℕ) (grid : RestrictedCurveGrid n k N target)
    (time : ℕ) :
    restrictedAnchoredProcessedBadCodes c 𝒜 streamSlack grid (time + 1) =
      restrictedSampledBadCodeStream c (restrictedCurveGridCode grid)
        𝒜.toPre N streamSlack time := by
  induction time with
  | zero =>
      simp [restrictedAnchoredProcessedBadCodes,
        restrictedSampledBadBatchAt]
  | succ time ih =>
      rw [restrictedAnchoredProcessedBadCodes, List.range_succ,
        List.flatMap_append, List.flatMap_singleton]
      change
        restrictedAnchoredProcessedBadCodes c 𝒜 streamSlack grid (time + 1) ++
            restrictedSampledBadBatchAt c (restrictedCurveGridCode grid)
              𝒜.toPre N streamSlack (time + 1) =
          restrictedSampledBadCodeStream c (restrictedCurveGridCode grid)
            𝒜.toPre N streamSlack (time + 1)
      rw [ih]
      exact restrictedSampledNewBadBatch_append c
        (restrictedCurveGridCode grid) 𝒜.toPre N streamSlack time

/-- The recursive processed union agrees with decoding the explicit
chronological processed-code trace. -/
lemma restrictedAnchoredProcessedBadUnion_eq_codes
    (c : Code) (𝒜 : DescriptionFamily)
    {n k N : ℕ} {target : ℕ → ℕ}
    (streamSlack : ℕ) (grid : RestrictedCurveGrid n k N target)
    (time : ℕ) :
    restrictedAnchoredProcessedBadUnion c 𝒜 streamSlack grid time =
      restrictedDecodedBadCodesUnion
        (restrictedAnchoredProcessedBadCodes c 𝒜 streamSlack grid time) := by
  induction time with
  | zero => simp [restrictedAnchoredProcessedBadUnion,
      restrictedAnchoredProcessedBadCodes, restrictedDecodedBadCodesUnion,
      restrictedBadPrefixUnion]
  | succ time ih =>
      change
        restrictedAnchoredProcessedBadUnion c 𝒜 streamSlack grid time ∪
            restrictedDecodedBadCodesUnion
              (restrictedSampledBadBatchAt c (restrictedCurveGridCode grid)
                𝒜.toPre N streamSlack time) =
          restrictedDecodedBadCodesUnion
            (restrictedAnchoredProcessedBadCodes c 𝒜 streamSlack grid
              (time + 1))
      rw [ih]
      rw [show restrictedAnchoredProcessedBadCodes c 𝒜 streamSlack grid
          (time + 1) =
          restrictedAnchoredProcessedBadCodes c 𝒜 streamSlack grid time ++
            restrictedSampledBadBatchAt c (restrictedCurveGridCode grid)
              𝒜.toPre N streamSlack time by
        simp [restrictedAnchoredProcessedBadCodes, List.range_succ,
          List.flatMap_append]]
      rw [restrictedDecodedBadCodesUnion_append]

/-- Removing duplicate indices from a list cannot increase a nonnegative
natural-valued sum. -/
private lemma sum_toFinset_le_list_sum {α : Type*} [DecidableEq α]
    (values : α → ℕ) : ∀ items : List α,
    ∑ item ∈ items.toFinset, values item ≤ (items.map values).sum := by
  intro items
  induction items with
  | nil => simp
  | cons item items ih =>
      by_cases hitem : item ∈ items
      · have hle : (items.map values).sum ≤
            values item + (items.map values).sum := by omega
        simpa [hitem] using ih.trans hle
      · simpa [hitem] using Nat.add_le_add_left ih (values item)

/-- A decoded-code union is no larger than the sum of the decoded set
cardinalities, even when the code list contains repetitions. -/
lemma restrictedDecodedBadCodesUnion_card_le (codes : List BitString) :
    (restrictedDecodedBadCodesUnion codes).card ≤
      (codes.map fun w => (decodeCoverCodeList w).toFinset.card).sum := by
  let decoded : BitString → Finset BitString := fun w =>
    (decodeCoverCodeList w).toFinset
  have hsubset : restrictedDecodedBadCodesUnion codes ⊆
      codes.toFinset.biUnion decoded := by
    intro x hx
    obtain ⟨w, hw, hxw⟩ :=
      (mem_restrictedDecodedBadCodesUnion_iff codes x).mp hx
    rw [Finset.mem_biUnion]
    exact ⟨w, List.mem_toFinset.mpr hw, hxw⟩
  calc
    (restrictedDecodedBadCodesUnion codes).card
        ≤ (codes.toFinset.biUnion decoded).card := Finset.card_le_card hsubset
    _ ≤ ∑ w ∈ codes.toFinset, (decoded w).card := Finset.card_biUnion_le
    _ ≤ (codes.map fun w => (decodeCoverCodeList w).toFinset.card).sum := by
      simpa [decoded] using
        (sum_toFinset_le_list_sum (fun w : BitString =>
          (decodeCoverCodeList w).toFinset.card) codes)

/-- The sum of the sizes decoded from one interval's visible model-code list
is bounded by the snapshot-code count times the advertised model size. -/
lemma familyStageModelCodesList_decoded_volume_le
    (c : Code) (i : ℕ) (𝒜 : PreDescriptionFamily) (j time : ℕ) :
    ((familyStageModelCodesList c i 𝒜 j time).map fun w =>
        (decodeCoverCodeList w).toFinset.card).sum ≤
      2 ^ (i + 1) * 2 ^ j := by
  let codes := familyStageModelCodesList c i 𝒜 j time
  have hcode : ∀ w ∈ codes,
      (decodeCoverCodeList w).toFinset.card ≤ 2 ^ j := by
    intro w hw
    obtain ⟨S, hS, _hSmem, hwcode, hScard⟩ :=
      familyStageModelCodesList_sound c i 𝒜 j time w hw
    rw [hwcode, decodeCoverCodeList_code S hS,
      canonicalFinsetList_toFinset]
    exact hScard
  calc
    (codes.map fun w => (decodeCoverCodeList w).toFinset.card).sum
        ≤ (codes.map fun _w => 2 ^ j).sum :=
          List.sum_le_sum (fun w hw => hcode w hw)
    _ = codes.length * 2 ^ j := by simp
    _ ≤ 2 ^ (i + 1) * 2 ^ j :=
      Nat.mul_le_mul_right _
        (familyStageModelCodesList_length_le c i 𝒜 j time)

/-- The raw sampled stream has the expected interval-wise bad-volume bound. -/
lemma restrictedSampledBadCodesRaw_decoded_volume_le
    (c : Code) (gridCode : BitString) (𝒜 : PreDescriptionFamily)
    (gridSteps streamSlack time : ℕ) :
    ((restrictedSampledBadCodesRaw c gridCode 𝒜 gridSteps streamSlack time).map
        fun w => (decodeCoverCodeList w).toFinset.card).sum ≤
      ((List.range gridSteps).map fun s =>
        2 ^ ((decode_restrictedCurveGridCode_sample gridCode (s + 1)).1 + 1) *
          2 ^ ((decode_restrictedCurveGridCode_sample gridCode s).2 -
            (streamSlack + 1))).sum := by
  induction gridSteps with
  | zero => simp [restrictedSampledBadCodesRaw]
  | succ gridSteps ih =>
      rw [restrictedSampledBadCodesRaw, List.range_succ,
        List.flatMap_append, List.flatMap_singleton, List.map_append,
        List.sum_append]
      rw [List.map_append, List.sum_append,
        List.map_singleton, List.sum_singleton]
      exact Nat.add_le_add ih
        (familyStageModelCodesList_decoded_volume_le c
          (decode_restrictedCurveGridCode_sample gridCode (gridSteps + 1)).1
          𝒜
          ((decode_restrictedCurveGridCode_sample gridCode gridSteps).2 -
            (streamSlack + 1)) time)

/-- Every code carried by the accumulated stream at time `t` is already in
the raw union of the sampled interval enumerations at the same time. -/
lemma restrictedSampledBadCodeStream_mem_raw
    (c : Code) (gridCode : BitString) (𝒜 : PreDescriptionFamily)
    (gridSteps Δ t : ℕ) {w : BitString}
    (hw : w ∈ restrictedSampledBadCodeStream c gridCode 𝒜 gridSteps Δ t) :
    w ∈ restrictedSampledBadCodesRaw c gridCode 𝒜 gridSteps Δ t := by
  induction t with
  | zero =>
      exact List.mem_eraseDups.mp hw
  | succ t ih =>
      have hw' := List.mem_eraseDups.mp hw
      rcases List.mem_append.mp hw' with hprevious | hcurrent
      · rw [restrictedSampledBadCodesRaw, List.mem_flatMap] at ih ⊢
        obtain ⟨s, hs, hcode⟩ := ih hprevious
        exact ⟨s, hs,
          (familyStageModelCodesList_mono c
            (decode_restrictedCurveGridCode_sample gridCode (s + 1)).1
            𝒜
            ((decode_restrictedCurveGridCode_sample gridCode s).2 - (Δ + 1))
            t).subset hcode⟩
      · exact List.mem_eraseDups.mp hcurrent

/-- Concrete bad-union bound for the anchored run.  Every processed code is
already present in the raw interval enumeration at the preceding stream stage,
so the processed union is bounded by the sum of the interval code counts times
their advertised set sizes. -/
lemma restrictedAnchoredProcessedBadUnion_card_le
    (c : Code) (𝒜 : DescriptionFamily)
    {n k N : ℕ} {target : ℕ → ℕ}
    (streamSlack : ℕ) (grid : RestrictedCurveGrid n k N target)
    (time : ℕ) :
    (restrictedAnchoredProcessedBadUnion c 𝒜 streamSlack grid
        (time + 1)).card ≤
      ((List.range N).map fun s =>
        2 ^ (grid.i (s + 1) + 1) *
          2 ^ (grid.j s - (streamSlack + 1))).sum := by
  let gridCode := restrictedCurveGridCode grid
  let stream := restrictedSampledBadCodeStream c gridCode
    𝒜.toPre N streamSlack time
  let raw := restrictedSampledBadCodesRaw c gridCode
    𝒜.toPre N streamSlack time
  have hstreamRaw : ∀ w ∈ stream, w ∈ raw := by
    intro w hw
    exact restrictedSampledBadCodeStream_mem_raw c gridCode 𝒜.toPre
      N streamSlack time hw
  have hsubset : restrictedDecodedBadCodesUnion stream ⊆
      restrictedDecodedBadCodesUnion raw := by
    intro x hx
    obtain ⟨w, hw, hxw⟩ :=
      (mem_restrictedDecodedBadCodesUnion_iff stream x).mp hx
    exact (mem_restrictedDecodedBadCodesUnion_iff raw x).mpr
      ⟨w, hstreamRaw w hw, hxw⟩
  rw [restrictedAnchoredProcessedBadUnion_eq_codes,
    restrictedAnchoredProcessedBadCodes_succ]
  calc
    (restrictedDecodedBadCodesUnion stream).card
        ≤ (restrictedDecodedBadCodesUnion raw).card := Finset.card_le_card hsubset
    _ ≤ (raw.map fun w => (decodeCoverCodeList w).toFinset.card).sum :=
      restrictedDecodedBadCodesUnion_card_le raw
    _ ≤ ((List.range N).map fun s =>
          2 ^ ((decode_restrictedCurveGridCode_sample gridCode (s + 1)).1 + 1) *
            2 ^ ((decode_restrictedCurveGridCode_sample gridCode s).2 -
              (streamSlack + 1))).sum :=
      restrictedSampledBadCodesRaw_decoded_volume_le c gridCode 𝒜.toPre
        N streamSlack time
    _ = ((List.range N).map fun s =>
          2 ^ (grid.i (s + 1) + 1) *
            2 ^ (grid.j s - (streamSlack + 1))).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro s hs
      have hslt : s < N := List.mem_range.mp hs
      have hsN : s ≤ N := Nat.le_of_lt hslt
      have hsNextN : s + 1 ≤ N := hslt
      rw [decode_restrictedCurveGridCode_sample_eq grid hsN,
        decode_restrictedCurveGridCode_sample_eq grid hsNextN]

/-- The complete chronological stream has the same finite interval-wise
counting bound as the raw family-stage lists. -/
lemma restrictedSampledBadCodeStream_length_le
    (c : Code) (gridCode : BitString) (𝒜 : PreDescriptionFamily)
    (gridSteps Δ t : ℕ) :
    (restrictedSampledBadCodeStream c gridCode 𝒜 gridSteps Δ t).length ≤
      ((List.range gridSteps).map (fun s =>
        2 ^ ((decode_restrictedCurveGridCode_sample gridCode (s + 1)).1 + 1))).sum := by
  classical
  have hsubset :
      (restrictedSampledBadCodeStream c gridCode 𝒜 gridSteps Δ t).toFinset ⊆
        (restrictedSampledBadCodesRaw c gridCode 𝒜 gridSteps Δ t).toFinset := by
    intro w hw
    rw [List.mem_toFinset] at hw ⊢
    exact restrictedSampledBadCodeStream_mem_raw
      c gridCode 𝒜 gridSteps Δ t hw
  calc
    (restrictedSampledBadCodeStream c gridCode 𝒜 gridSteps Δ t).length
        = (restrictedSampledBadCodeStream c gridCode 𝒜 gridSteps Δ t).toFinset.card :=
          (List.toFinset_card_of_nodup
            (restrictedSampledBadCodeStream_nodup
              c gridCode 𝒜 gridSteps Δ t)).symm
    _ ≤ (restrictedSampledBadCodesRaw c gridCode 𝒜 gridSteps Δ t).toFinset.card :=
      Finset.card_le_card hsubset
    _ ≤ (restrictedSampledBadCodesRaw c gridCode 𝒜 gridSteps Δ t).length :=
      List.toFinset_card_le _
    _ ≤ ((List.range gridSteps).map (fun s =>
        2 ^ ((decode_restrictedCurveGridCode_sample gridCode (s + 1)).1 + 1))).sum := by
      rw [restrictedSampledBadCodesRaw, List.length_flatMap]
      apply List.sum_le_sum
      intro s hs
      exact familyStageModelCodesList_length_le c
        (decode_restrictedCurveGridCode_sample gridCode (s + 1)).1 𝒜
        ((decode_restrictedCurveGridCode_sample gridCode s).2 - (Δ + 1)) t

/-- A stream whose length is bounded across all later times has stabilized. -/
lemma restrictedSampledBadCodeStream_stabilizes_of_length_bound
    (c : Code) (gridCode : BitString) (𝒜 : PreDescriptionFamily)
    (gridSteps Δ : ℕ) (length_bound : ℕ)
    (hbound : ∀ t,
        (restrictedSampledBadCodeStream c gridCode 𝒜 gridSteps Δ t).length ≤ length_bound) :
    ∃ T, ∀ t ≥ T, restrictedSampledBadCodeStream c gridCode 𝒜 gridSteps Δ t =
        restrictedSampledBadCodeStream c gridCode 𝒜 gridSteps Δ T := by
  classical
  let stream : ℕ → List BitString := fun t =>
    restrictedSampledBadCodeStream c gridCode 𝒜 gridSteps Δ t
  let deficit : ℕ → ℕ := fun t => length_bound - (stream t).length
  have hexists : ∃ d : ℕ, ∃ t : ℕ, deficit t = d :=
    ⟨deficit 0, 0, rfl⟩
  obtain ⟨T, hT⟩ := Nat.find_spec hexists
  refine ⟨T, ?_⟩
  intro t ht
  have hprefix : stream T <+: stream t := by
    induction ht with
    | refl => exact List.prefix_refl _
    | @step t ht ih =>
        exact ih.trans (restrictedSampledBadCodeStream_mono
          c gridCode 𝒜 gridSteps Δ t)
  have hlen_le : (stream T).length ≤ (stream t).length := hprefix.length_le
  have hlen_eq : (stream T).length = (stream t).length := by
    apply Nat.le_antisymm hlen_le
    by_contra hnot
    have hlt : deficit t < deficit T := by
      dsimp [deficit]
      have hTbound : (stream T).length ≤ length_bound := hbound T
      have htbound : (stream t).length ≤ length_bound := hbound t
      omega
    have hfind : deficit T = Nat.find hexists := hT
    have hlt_find : deficit t < Nat.find hexists := by simpa [hfind] using hlt
    exact (Nat.find_min hexists hlt_find) ⟨t, rfl⟩
  exact (hprefix.eq_of_length hlen_eq).symm

/-- The sampled bad-code stream stabilizes because every sampled interval has
only finitely many distinct programs at its advertised complexity level. -/
lemma restrictedSampledBadCodeStream_stabilizes
    (c : Code) (gridCode : BitString) (𝒜 : PreDescriptionFamily)
    (gridSteps Δ : ℕ) :
    ∃ T, ∀ t ≥ T,
      restrictedSampledBadCodeStream c gridCode 𝒜 gridSteps Δ t =
        restrictedSampledBadCodeStream c gridCode 𝒜 gridSteps Δ T := by
  exact restrictedSampledBadCodeStream_stabilizes_of_length_bound
    c gridCode 𝒜 gridSteps Δ
    ((List.range gridSteps).map (fun s =>
      2 ^ ((decode_restrictedCurveGridCode_sample gridCode (s + 1)).1 + 1))).sum
    (restrictedSampledBadCodeStream_length_le c gridCode 𝒜 gridSteps Δ)

/-- At every grid interval, the next horizontal coordinate plus the next
vertical height stays below the initial target height. -/
lemma restrictedCurveGrid_next_index_add_height_le
    {n k N : ℕ} {target : ℕ → ℕ}
    (grid : RestrictedCurveGrid n k N target)
    (htarget : target 0 ≤ n)
    (hstrict : ∀ i < k, target (i + 1) < target i)
    (s : ℕ) (hs : s < N) :
    grid.i (s + 1) + grid.j (s + 1) ≤ n := by
  by_cases hi : grid.i (s + 1) = 0
  · rw [hi, zero_add]
    exact grid.j_le_n (s + 1) hs
  · have hiPos : 0 < grid.i (s + 1) := Nat.pos_of_ne_zero hi
    have habove := grid.cross_above (s + 1) hs hiPos
    have hiPred : grid.i (s + 1) - 1 ≤ k :=
      (Nat.sub_le _ _).trans (grid.i_le_k (s + 1) hs)
    have hdrop := restricted_curve_drop_bound hstrict
      (Nat.zero_le (grid.i (s + 1) - 1)) hiPred
    omega

/-- The balanced grid's bad-description volume fits strictly inside an
`n + O(log n)` ambient cube once the stream uses the actual square-root slack.
The fixed coefficient `8` is the same one that bounds the grid mesh. -/
lemma restrictedCurveGrid_bad_volume_padding
    {n k N : ℕ} {target : ℕ → ℕ}
    (grid : RestrictedCurveGrid n k N target)
    (hN : N = Nat.sqrt (n / (Nat.log2 n + 1)) + 1)
    (hkn : k ≤ n)
    (htarget : target 0 ≤ n)
    (hstrict : ∀ i < k, target (i + 1) < target i) :
    ((List.range N).map fun s =>
        2 ^ (grid.i (s + 1) + 1) *
          2 ^ (grid.j s - (sqrtSlack 8 n + 1))).sum <
      2 ^ (n + logSlack 8 n) := by
  have hmesh : n / N + 1 ≤ sqrtSlack 8 n := by
    rw [hN]
    exact restrictedCurveGrid_mesh_le_sqrtSlack n
  have hterm : ∀ s ∈ List.range N,
      2 ^ (grid.i (s + 1) + 1) *
          2 ^ (grid.j s - (sqrtSlack 8 n + 1)) ≤
        2 ^ (n + 1) := by
    intro s hs
    have hslt : s < N := List.mem_range.mp hs
    have hnext := restrictedCurveGrid_next_index_add_height_le grid
      htarget hstrict s hslt
    have hjmono := grid.j_mono s hslt
    have hjstep := grid.j_step_le s hslt
    have hisum : grid.i (s + 1) + grid.j s ≤ n + sqrtSlack 8 n := by
      omega
    have hiN : grid.i (s + 1) ≤ n :=
      (grid.i_le_k (s + 1) hslt).trans hkn
    rw [← pow_add]
    apply Nat.pow_le_pow_right (by decide)
    by_cases hj : grid.j s ≤ sqrtSlack 8 n + 1
    · have hzero : grid.j s - (sqrtSlack 8 n + 1) = 0 :=
        Nat.sub_eq_zero_of_le hj
      omega
    · omega
  have hsum :
      ((List.range N).map fun s =>
          2 ^ (grid.i (s + 1) + 1) *
            2 ^ (grid.j s - (sqrtSlack 8 n + 1))).sum ≤
        N * 2 ^ (n + 1) := by
    calc
      ((List.range N).map fun s =>
          2 ^ (grid.i (s + 1) + 1) *
            2 ^ (grid.j s - (sqrtSlack 8 n + 1))).sum
          ≤ ((List.range N).map fun _s => 2 ^ (n + 1)).sum :=
            List.sum_le_sum hterm
      _ = N * 2 ^ (n + 1) := by simp
  have hNle : N ≤ n + 1 := by
    rw [hN]
    exact Nat.add_le_add_right
      ((Nat.sqrt_le_self (n / (Nat.log2 n + 1))).trans
        (Nat.div_le_self n (Nat.log2 n + 1))) 1
  have hnBits : n + 1 ≤ 2 ^ (Nat.bits n).length := by
    simpa [Nat.size_eq_bits_len] using
      (Nat.succ_le_iff.mpr (Nat.lt_size_self n))
  have hcount : N * 2 < 2 ^ logSlack 8 n := by
    have hcountLe : N * 2 ≤ 2 ^ ((Nat.bits n).length + 1) := by
      calc
        N * 2 ≤ (n + 1) * 2 := Nat.mul_le_mul_right 2 hNle
        _ ≤ 2 ^ (Nat.bits n).length * 2 :=
          Nat.mul_le_mul_right 2 hnBits
        _ = 2 ^ ((Nat.bits n).length + 1) := by rw [pow_succ]
    exact hcountLe.trans_lt (Nat.pow_lt_pow_right (by decide) (by
      unfold logSlack
      omega))
  have hambient : N * 2 ^ (n + 1) < 2 ^ (n + logSlack 8 n) := by
    calc
      N * 2 ^ (n + 1) = (N * 2) * 2 ^ n := by rw [pow_succ]; ring
      _ < 2 ^ logSlack 8 n * 2 ^ n :=
        Nat.mul_lt_mul_of_pos_right hcount (pow_pos (by decide) n)
      _ = 2 ^ (n + logSlack 8 n) := by rw [← pow_add]; ring
  exact hsum.trans_lt hambient

/-- Prefix monotonicity of the chronological bad-code stream at arbitrary
ordered stages. -/
lemma restrictedSampledBadCodeStream_prefix_of_le
    (c : Code) (gridCode : BitString) (𝒜 : PreDescriptionFamily)
    (gridSteps Δ : ℕ) {time₁ time₂ : ℕ} (htime : time₁ ≤ time₂) :
    restrictedSampledBadCodeStream c gridCode 𝒜 gridSteps Δ time₁ <+:
      restrictedSampledBadCodeStream c gridCode 𝒜 gridSteps Δ time₂ := by
  induction htime with
  | refl => exact List.prefix_refl _
  | @step time₂ htime ih =>
      exact ih.trans (restrictedSampledBadCodeStream_mono c gridCode 𝒜
        gridSteps Δ time₂)

/-- Every code visible in the stream by stage `time` occurs in one of the
chronological batches processed by run time `time + 1`. -/
lemma restrictedSampledBadCodeStream_mem_batchAt
    (c : Code) (gridCode : BitString) (𝒜 : PreDescriptionFamily)
    (gridSteps Δ time : ℕ) {w : BitString}
    (hw : w ∈ restrictedSampledBadCodeStream c gridCode 𝒜 gridSteps Δ time) :
    ∃ eventTime ≤ time,
      w ∈ restrictedSampledBadBatchAt c gridCode 𝒜 gridSteps Δ eventTime := by
  induction time with
  | zero =>
      exact ⟨0, le_rfl, hw⟩
  | succ time ih =>
      rw [← restrictedSampledNewBadBatch_append c gridCode 𝒜 gridSteps Δ time]
        at hw
      rcases List.mem_append.mp hw with hprevious | hcurrent
      · obtain ⟨eventTime, heventTime, hevent⟩ := ih hprevious
        exact ⟨eventTime, heventTime.trans (Nat.le_succ time), hevent⟩
      · exact ⟨time + 1, le_rfl, hcurrent⟩

/-- The final root live set is nonempty. -/
lemma restrictedAnchoredRun_terminal_nonempty
    (𝒜 : DescriptionFamily) (c : Code)
    {n k N : ℕ} {target : ℕ → ℕ}
    (ambientLength Δ time : ℕ)
    (grid : RestrictedCurveGrid n k N target)
    (hnambient : n ≤ ambientLength)
    (hcard : (restrictedAnchoredProcessedBadUnion c 𝒜 Δ grid time).card < 2 ^ ambientLength) :
    ∃ output : BitString,
      ∃ state : RestrictedSampledRunState 𝒜 (N + 1) ambientLength
          (2 * 𝒜.overhead ambientLength)
          (restrictedAnchoredTarget ambientLength Δ grid),
        restrictedEffectiveAnchoredSampledRun 𝒜 c ambientLength Δ grid time =
            Part.some output ∧
        DecodesToRestrictedSampledRunState output state ∧
        (state.live (N + 1)).Nonempty := by
  obtain ⟨output, state, hrun, hstate, _hBzero, hroot, _hprocessed⟩ :=
    restrictedEffectiveAnchoredSampledRun_spec 𝒜 c ambientLength Δ time grid
      hnambient
  have hroot_nonempty : (state.live 0).Nonempty := by
    rw [hroot]
    rw [Finset.sdiff_nonempty]
    intro hsubset
    have hcube_card : (stringsOfLength ambientLength).card = 2 ^ ambientLength :=
      cardStringsOfLength ambientLength
    have hcard_le := Finset.card_le_card hsubset
    rw [hcube_card] at hcard_le
    omega
  have hterminal : (state.live (N + 1)).Nonempty :=
    restricted_rebuild_suffix_preserves_terminal_nonempty
      0 (N + 1) (2 * 𝒜.overhead ambientLength)
      (restrictedAnchoredTarget ambientLength Δ grid) state.live
      (Nat.zero_le (N + 1)) hroot_nonempty
      (fun i _hi hiN => state.density i hiN)
  exact ⟨output, state, hrun, hstate, hterminal⟩

/-- Once the bad-code stream has stabilized, the next anchored run state has
processed every forbidden restricted description.  Hence every terminal live
candidate avoids the concrete profile bad set. -/
lemma restrictedAnchoredFinalState_avoids_profileBadSet
    (U : Map)
    (𝒜 : DescriptionFamily) (c : Code)
    {n k N : ℕ} {target : ℕ → ℕ}
    (ambientLength streamSlack profileSlack T : ℕ)
    (grid : RestrictedCurveGrid n k N target)
    (hc : IsCodeFor c U)
    (hnambient : n ≤ ambientLength)
    (hstrict : ∀ i < k, target (i + 1) < target i)
    (hslack : streamSlack ≤ profileSlack)
    (hstable : ∀ time ≥ T,
      restrictedSampledBadCodeStream c (restrictedCurveGridCode grid)
          𝒜.toPre N streamSlack time =
        restrictedSampledBadCodeStream c (restrictedCurveGridCode grid)
          𝒜.toPre N streamSlack T) :
    ∃ output : BitString,
      ∃ state : RestrictedSampledRunState 𝒜 (N + 1) ambientLength
          (2 * 𝒜.overhead ambientLength)
          (restrictedAnchoredTarget ambientLength streamSlack grid),
        restrictedEffectiveAnchoredSampledRun 𝒜 c ambientLength streamSlack grid (T + 1) =
            Part.some output ∧
        DecodesToRestrictedSampledRunState output state ∧
        ∀ x ∈ state.live (N + 1),
          x ∉ restrictedProfileBadSet 𝒜 U (state.live (N + 1)) k
            profileSlack target := by
  obtain ⟨output, state, hrun, hstate, _hBzero, _hroot, hprocessed⟩ :=
    restrictedEffectiveAnchoredSampledRun_spec 𝒜 c ambientLength streamSlack
      (T + 1) grid hnambient
  refine ⟨output, state, hrun, hstate, ?_⟩
  intro x hx hbad
  obtain ⟨_hbad_subset, hbad_spec⟩ :=
    restrictedProfileBadSet_spec 𝒜 U (state.live (N + 1)) k
      profileSlack target
  obtain ⟨i, hi, _htarget, hprof⟩ := (hbad_spec x hx).mp hbad
  have hprof' :
      InDescriptionProfileIn 𝒜 U x i (target i - (streamSlack + 1)) :=
    hprof.mono_j
      (Nat.sub_le_sub_left (Nat.succ_le_succ hslack) (target i))
  obtain ⟨w, appearanceTime, _s, _hs, hwstream, hdescription⟩ :=
    restrictedSampledBadCodeStream_catches_violation grid U c hc streamSlack
      hstrict x i hi 𝒜 hprof'
  have hwT : w ∈ restrictedSampledBadCodeStream c
      (restrictedCurveGridCode grid) 𝒜.toPre N streamSlack T := by
    by_cases htime : appearanceTime ≤ T
    · have hprefix := restrictedSampledBadCodeStream_prefix_of_le c
        (restrictedCurveGridCode grid) 𝒜.toPre N streamSlack htime
      exact hprefix.subset hwstream
    · have hTle : T ≤ appearanceTime := Nat.le_of_lt (Nat.lt_of_not_ge htime)
      rw [← hstable appearanceTime hTle]
      exact hwstream
  obtain ⟨eventTime, heventTime, hbatch⟩ :=
    restrictedSampledBadCodeStream_mem_batchAt c
      (restrictedCurveGridCode grid) 𝒜.toPre N streamSlack T hwT
  obtain ⟨bad, hdecode⟩ :=
    restrictedSampledBadBatchAt_decode_sound c (restrictedCurveGridCode grid)
      𝒜 N streamSlack eventTime w hbatch
  obtain ⟨S, hS, _hSmem, hwcode, _hScard, hxS⟩ := hdescription
  have hbad_eq : bad = S := by
    have hdecodeS : decodeCoverCodeList w = canonicalFinsetList S := by
      rw [hwcode]
      exact decodeCoverCodeList_code S hS
    rw [hdecodeS] at hdecode
    have hfinsets := congrArg List.toFinset hdecode.symm
    simpa using hfinsets
  have hdisjoint := hprocessed eventTime (by omega) w hbatch bad hdecode
    (N + 1) le_rfl
  rw [hbad_eq] at hdisjoint
  exact (Finset.disjoint_left.mp hdisjoint) hx hxS

/-- Structural terminal-survivor assembly at a stabilized stream stage.  The
separate arithmetic/coding phase must still choose `ambientLength`, prove the
strict root-cardinality gap, and bound the version ordinals. -/
lemma exists_restricted_anchored_final_state
    (U : Map)
    (𝒜 : DescriptionFamily) (c : Code)
    {n k N : ℕ} {target : ℕ → ℕ}
    (ambientLength streamSlack profileSlack T : ℕ)
    (grid : RestrictedCurveGrid n k N target)
    (hc : IsCodeFor c U)
    (hnambient : n ≤ ambientLength)
    (hstrict : ∀ i < k, target (i + 1) < target i)
    (hslack : streamSlack ≤ profileSlack)
    (hstable : ∀ time ≥ T,
      restrictedSampledBadCodeStream c (restrictedCurveGridCode grid)
          𝒜.toPre N streamSlack time =
        restrictedSampledBadCodeStream c (restrictedCurveGridCode grid)
          𝒜.toPre N streamSlack T)
    (hcard : (restrictedAnchoredProcessedBadUnion c 𝒜 streamSlack grid (T + 1)).card <
      2 ^ ambientLength) :
    ∃ output : BitString,
      ∃ state : RestrictedSampledRunState 𝒜 (N + 1) ambientLength
          (2 * 𝒜.overhead ambientLength)
          (restrictedAnchoredTarget ambientLength streamSlack grid),
        restrictedEffectiveAnchoredSampledRun 𝒜 c ambientLength streamSlack grid (T + 1) =
            Part.some output ∧
        DecodesToRestrictedSampledRunState output state ∧
        ∃ x : BitString, x ∈ state.live (N + 1) ∧
        x ∉ restrictedProfileBadSet 𝒜 U (state.live (N + 1)) k profileSlack target := by
  obtain ⟨output, state, hrun, hstate, hnonempty⟩ :=
    restrictedAnchoredRun_terminal_nonempty 𝒜 c ambientLength streamSlack
      (T + 1) grid hnambient hcard
  obtain ⟨output', state', hrun', hstate', havoids⟩ :=
    restrictedAnchoredFinalState_avoids_profileBadSet U 𝒜 c ambientLength
      streamSlack profileSlack T grid hc hnambient hstrict hslack hstable
  have houtput : output' = output := by
    rw [hrun] at hrun'
    exact Part.some_injective hrun'.symm
  subst output'
  have hlive_eq : state'.live (N + 1) = state.live (N + 1) := by
    have hcodes : canonicalFinsetList (state'.live (N + 1)) =
        canonicalFinsetList (state.live (N + 1)) :=
      (hstate'.2 (N + 1) le_rfl).2.symm.trans
        (hstate.2 (N + 1) le_rfl).2
    have hfinsets := congrArg List.toFinset hcodes
    simpa using hfinsets
  have hnonempty' : (state'.live (N + 1)).Nonempty := by
    rw [hlive_eq]
    exact hnonempty
  obtain ⟨x, hx⟩ := hnonempty'
  exact ⟨output, state', hrun', hstate', x, hx, havoids x hx⟩

/-- Complete structural output for a fixed code of the underlying
decompressor.  Keeping `c` explicit is important for the version decoder: its
invariance constant may depend on this code, so `c` must be chosen before that
constant. -/
lemma exists_restricted_anchored_structural_output_for_code
    (U : Map) (𝒜 : DescriptionFamily) (c : Code) (hc : IsCodeFor c U)
    {n k N : ℕ} {target : ℕ → ℕ}
    (grid : RestrictedCurveGrid n k N target)
    (hN : N = Nat.sqrt (n / (Nat.log2 n + 1)) + 1)
    (hkn : k ≤ n)
    (htarget : target 0 ≤ n)
    (hstrict : ∀ i < k, target (i + 1) < target i) :
    ∃ T output,
      ∃ state : RestrictedSampledRunState 𝒜 (N + 1)
          (n + logSlack 8 n) (2 * 𝒜.overhead (n + logSlack 8 n))
          (restrictedAnchoredTarget (n + logSlack 8 n)
            (sqrtSlack 8 n) grid),
        restrictedEffectiveAnchoredSampledRun 𝒜 c
            (n + logSlack 8 n) (sqrtSlack 8 n) grid (T + 1) =
              Part.some output ∧
        DecodesToRestrictedSampledRunState output state ∧
        ∃ x : BitString, x ∈ state.live (N + 1) ∧
          x ∉ restrictedProfileBadSet 𝒜 U (state.live (N + 1)) k
            (sqrtSlack 8 n) target := by
  obtain ⟨T, hstable⟩ := restrictedSampledBadCodeStream_stabilizes c
    (restrictedCurveGridCode grid) 𝒜.toPre N (sqrtSlack 8 n)
  have hcard :
      (restrictedAnchoredProcessedBadUnion c 𝒜 (sqrtSlack 8 n) grid
        (T + 1)).card < 2 ^ (n + logSlack 8 n) :=
    (restrictedAnchoredProcessedBadUnion_card_le c 𝒜
      (sqrtSlack 8 n) grid T).trans_lt
        (restrictedCurveGrid_bad_volume_padding grid hN hkn htarget hstrict)
  obtain ⟨output, state, hrun, hstate, hsurvivor⟩ :=
    exists_restricted_anchored_final_state U 𝒜 c
      (n + logSlack 8 n) (sqrtSlack 8 n) (sqrtSlack 8 n) T grid hc
      (by omega) hstrict le_rfl hstable hcard
  exact ⟨T, output, state, hrun, hstate, hsurvivor⟩

/-- Complete structural output of the anchored chronological run.  This
packages the fixed decompressor code, balanced padding, stream stabilization,
nonempty terminal survivor, and forbidden-profile avoidance.  Complexity of
the final model versions is deliberately not claimed here. -/
lemma exists_restricted_anchored_structural_output
    (U : Map) (hU : IsOptimalPrefixConditional U)
    (𝒜 : DescriptionFamily)
    {n k N : ℕ} {target : ℕ → ℕ}
    (grid : RestrictedCurveGrid n k N target)
    (hN : N = Nat.sqrt (n / (Nat.log2 n + 1)) + 1)
    (hkn : k ≤ n)
    (htarget : target 0 ≤ n)
    (hstrict : ∀ i < k, target (i + 1) < target i) :
    ∃ c : Code, IsCodeFor c U ∧
      ∃ T output,
        ∃ state : RestrictedSampledRunState 𝒜 (N + 1)
            (n + logSlack 8 n) (2 * 𝒜.overhead (n + logSlack 8 n))
            (restrictedAnchoredTarget (n + logSlack 8 n)
              (sqrtSlack 8 n) grid),
          restrictedEffectiveAnchoredSampledRun 𝒜 c
              (n + logSlack 8 n) (sqrtSlack 8 n) grid (T + 1) =
                Part.some output ∧
          DecodesToRestrictedSampledRunState output state ∧
          ∃ x : BitString, x ∈ state.live (N + 1) ∧
            x ∉ restrictedProfileBadSet 𝒜 U (state.live (N + 1)) k
              (sqrtSlack 8 n) target := by
  obtain ⟨c, hc⟩ : ∃ c : Code, IsCodeFor c U :=
    Nat.Partrec.Code.exists_code.mp hU.isDecompressor
  obtain ⟨T, output, state, hrun, hstate, hsurvivor⟩ :=
    exists_restricted_anchored_structural_output_for_code U 𝒜 c hc grid hN
      hkn htarget hstrict
  exact ⟨c, hc, T, output, state, hrun, hstate, hsurvivor⟩

/-- Package an anchored terminal state as the sampled output core once the two
version-coding complexity estimates have been supplied.  This separates the
pure state bookkeeping from the downstream ordinal/history argument. -/
lemma restrictedAnchoredState_to_sampledOutputCore
    (𝒜 : DescriptionFamily) (U : Map)
    {n k N c ambientLength streamSlack : ℕ} {target : ℕ → ℕ}
    (grid : RestrictedCurveGrid n k N target)
    (state : RestrictedSampledRunState 𝒜 (N + 1) ambientLength
      (2 * 𝒜.overhead ambientLength)
      (restrictedAnchoredTarget ambientLength streamSlack grid))
    (hnambient : n ≤ ambientLength)
    (hambient : ambientLength ≤ n + logSlack c n)
    (hcomplexity : ∀ s (_hs : s ≤ N) (hS : (state.B (s + 1)).Nonempty),
      setComplexity U (state.B (s + 1)) hS ≤
        (grid.i s + sqrtSlack c n : ENat))
    (hcandidate : ∀ x ∈ state.live (N + 1),
      KPPlain U x ≤ (k + sqrtSlack c n : ENat))
    (survivor : BitString)
    (hsurvivor : survivor ∈ state.live (N + 1))
    (havoids : survivor ∉ restrictedProfileBadSet 𝒜 U
      (state.live (N + 1)) k (sqrtSlack c n) target) :
    Nonempty (RestrictedSampledOutputCore 𝒜 U n k N c target grid) := by
  classical
  have hlive_le : ∀ {s₁ s₂ : ℕ}, s₁ ≤ s₂ → s₂ ≤ N + 1 →
      state.live s₂ ⊆ state.live s₁ := by
    intro s₁ s₂ h12
    induction h12 with
    | refl => exact fun _ _ hx => hx
    | @step m hm ih =>
        intro hm1 x hx
        exact ih (by omega) (state.live_monotonic m (by omega) hx)
  exact ⟨{
    ambientLength := ambientLength
    n_le_ambient := hnambient
    ambient_le := hambient
    sampledSets := fun s => state.B (s + 1)
    mem_family := fun s hs => state.mem_family (s + 1) (by omega)
    size_bound := fun s hs =>
      (state.size_bound (s + 1) (by omega)).trans
        (Nat.pow_le_pow_right (by norm_num) (by
          simp only [restrictedAnchoredTarget_succ]
          exact Nat.sub_le _ _))
    complexity_bound := fun s hs hS => hcomplexity s hs hS
    candidates := state.live (N + 1)
    candidates_nonempty := ⟨survivor, hsurvivor⟩
    candidate_len := fun x hx => state.live_ambient (N + 1) le_rfl x hx
    candidate_mem := fun x hx s hs =>
      state.live_subset (s + 1) (by omega)
        (hlive_le (Nat.succ_le_succ hs) le_rfl hx)
    candidate_complexity := hcandidate
    survivor := survivor
    survivor_mem := hsurvivor
    survivor_not_bad := havoids }⟩

end Kolmogorov
