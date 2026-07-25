/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/

import KolmogorovMathlib.Restricted.FamilyCurve.EffectiveRun

/-!
# Semantics of the effective sampled run

This file proves decoding, soundness, and termination properties for the chronological
partial-recursive sampled-run processor.
-/

namespace Kolmogorov

open scoped ENNReal
open Nat.Partrec (Code)

/-- Every code in a chronological batch is a canonical code of a finite bad
set.  This is the decoding form needed by the effective one-step theorem. -/
lemma restrictedSampledBadBatchAt_decode_sound
    (c : Code) (gridCode : BitString) (𝒜 : DescriptionFamily)
    (gridSteps Δ time : ℕ)
    (w : BitString)
    (hw : w ∈ restrictedSampledBadBatchAt c gridCode 𝒜.toPre gridSteps Δ time) :
    ∃ bad : Finset BitString,
      decodeCoverCodeList w = canonicalFinsetList bad := by
  have hstream :
      w ∈ restrictedSampledBadCodeStream c gridCode 𝒜.toPre gridSteps Δ time := by
    cases time with
    | zero => exact hw
    | succ time =>
        rw [← restrictedSampledNewBadBatch_append c gridCode 𝒜.toPre
          gridSteps Δ time]
        exact List.mem_append_right _ hw
  obtain ⟨_s, _hs, S, hS, _hmem, hcode, _hcard⟩ :=
    restrictedSampledBadCodeStream_sound c gridCode 𝒜.toPre
      gridSteps Δ time hstream
  refine ⟨S, ?_⟩
  rw [hcode]
  exact decodeCoverCodeList_code S hS

/-- The first `count` events of the executable batch processor.  This local
prefix form exposes the natural induction variable hidden by the public
processor's `Nat.rec` implementation. -/
private noncomputable def restrictedEffectiveSampledRunProcessPrefix
    (𝒜 : DescriptionFamily) (q0 : ℕ) (sizes : List ℕ)
    (stateCode : BitString) (badCodes : List BitString) (count : ℕ) :
    Part BitString :=
  Nat.rec (motive := fun _ => Part BitString)
    (Part.some stateCode)
    (fun idx current => current.bind (fun state =>
      restrictedEffectiveSampledRunStep 𝒜 q0 sizes state
        (badCodes.getD idx [])))
    count

/-- Union of the first `count` decoded bad sets, using the same index order as
the executable `Nat.rec` batch processor. -/
def restrictedBadPrefixUnion (bads : List (Finset BitString)) : ℕ → Finset BitString
  | 0 => ∅
  | count + 1 => restrictedBadPrefixUnion bads count ∪ bads.getD count ∅

/-- Decoded correctness of every prefix of a finite executable batch.  Besides
event disjointness, the result records containment in the input root; that
invariant is what preserves disjointness from earlier chronological batches. -/
private lemma restrictedEffectiveSampledRunProcessPrefix_spec
    (𝒜 : DescriptionFamily) (N ambientLength : ℕ) (t : ℕ → ℕ)
    (sizes : List ℕ)
    (hlen : sizes.length = N + 1)
    (hpowers : ∀ s ≤ N, sizes.getD s 0 = 2 ^ t s)
    (hmono : ∀ s < N, t (s + 1) ≤ t s)
    (stateCode : BitString)
    (state : RestrictedSampledRunState 𝒜 N ambientLength
      (2 * 𝒜.overhead ambientLength) t)
    (badCodes : List BitString) (bads : List (Finset BitString))
    (hstate : DecodesToRestrictedSampledRunState stateCode state)
    (hlen_bads : badCodes.length = bads.length)
    (hbad : ∀ i < badCodes.length,
      decodeCoverCodeList (badCodes.getD i []) =
        canonicalFinsetList (bads.getD i ∅))
    (count : ℕ) (hcount : count ≤ badCodes.length) :
    ∃ output : BitString,
      ∃ next : RestrictedSampledRunState 𝒜 N ambientLength
          (2 * 𝒜.overhead ambientLength) t,
        restrictedEffectiveSampledRunProcessPrefix 𝒜
            (𝒜.overhead ambientLength) sizes stateCode badCodes count =
          Part.some output ∧
        DecodesToRestrictedSampledRunState output next ∧
        next.B 0 = state.B 0 ∧
        next.live 0 = state.live 0 \ restrictedBadPrefixUnion bads count ∧
        (∀ s ≤ N, next.live s ⊆ state.live 0) ∧
        ∀ i < count, ∀ s ≤ N,
          Disjoint (next.live s) (bads.getD i ∅) := by
  induction count with
  | zero =>
      refine ⟨stateCode, state, rfl, hstate, rfl, ?_, ?_, ?_⟩
      · simp [restrictedBadPrefixUnion]
      · intro s hs
        exact state.live_subset_root hs
      · intro i hi
        omega
  | succ count ih =>
      have hcount_le : count ≤ badCodes.length := by omega
      obtain ⟨previousCode, previous, hrun, hprevious, hBzero, hliveZero,
          hroot, hdisjoint⟩ :=
        ih hcount_le
      have hcount_lt : count < badCodes.length := by omega
      obtain ⟨output, next, q, hstep, hnext, hcontract⟩ :=
        restrictedEffectiveSampledRun_step_spec 𝒜 N ambientLength t sizes
          hlen hpowers hmono hprevious (hbad count hcount_lt)
      refine ⟨output, next, ?_, hnext, ?_, ?_, ?_, ?_⟩
      · change
          (restrictedEffectiveSampledRunProcessPrefix 𝒜
            (𝒜.overhead ambientLength) sizes stateCode badCodes count).bind
              (fun current => restrictedEffectiveSampledRunStep 𝒜
                (𝒜.overhead ambientLength) sizes current
                  (badCodes.getD count [])) = Part.some output
        rw [hrun, Part.bind_some, hstep]
      · rw [(hcontract.2.2.1 0 (Nat.zero_le q)).1, hBzero]
      · rw [(hcontract.2.2.1 0 (Nat.zero_le q)).2, hliveZero]
        ext x
        simp [restrictedBadPrefixUnion, and_assoc]
      · intro s hs
        exact (hcontract.live_subset_old_root hs).trans
          (Finset.sdiff_subset.trans (hroot 0 (Nat.zero_le N)))
      · intro i hi s hs
        apply Finset.disjoint_left.mpr
        intro x hx hxbad
        have hxroot : x ∈ previous.live 0 \ (bads.getD count ∅) :=
          hcontract.live_subset_old_root hs hx
        by_cases hicount : i = count
        · subst i
          exact (Finset.mem_sdiff.mp hxroot).2 hxbad
        · have hiold : i < count := by omega
          exact (Finset.disjoint_left.mp
            (hdisjoint i hiold 0 (Nat.zero_le N)))
              (Finset.mem_sdiff.mp hxroot).1 hxbad

/-- Lifts the decoded one-event theorem through a finite sequence of bad codes
processed in order. -/
lemma restrictedEffectiveSampledRunProcess_spec
    (𝒜 : DescriptionFamily) (N ambientLength : ℕ) (t : ℕ → ℕ)
    (sizes : List ℕ)
    (hlen : sizes.length = N + 1)
    (hpowers : ∀ s ≤ N, sizes.getD s 0 = 2 ^ t s)
    (hmono : ∀ s < N, t (s + 1) ≤ t s)
    (stateCode : BitString)
    (state : RestrictedSampledRunState 𝒜 N ambientLength
      (2 * 𝒜.overhead ambientLength) t)
    (badCodes : List BitString) (bads : List (Finset BitString))
    (hstate : DecodesToRestrictedSampledRunState stateCode state)
    (hlen_bads : badCodes.length = bads.length)
    (hbad : ∀ i < badCodes.length,
      decodeCoverCodeList (badCodes.getD i []) =
        canonicalFinsetList (bads.getD i ∅)) :
    ∃ output : BitString,
      ∃ next : RestrictedSampledRunState 𝒜 N ambientLength
          (2 * 𝒜.overhead ambientLength) t,
        restrictedEffectiveSampledRunProcess 𝒜
            (𝒜.overhead ambientLength) sizes stateCode badCodes =
          Part.some output ∧
        DecodesToRestrictedSampledRunState output next ∧
        next.B 0 = state.B 0 ∧
        next.live 0 = state.live 0 \
          restrictedBadPrefixUnion bads badCodes.length ∧
        (∀ s ≤ N, next.live s ⊆ state.live 0) ∧
        ∀ i < bads.length, ∀ s ≤ N,
          Disjoint (next.live s) (bads.getD i ∅) := by
  obtain ⟨output, next, hrun, hnext, hBzero, hliveZero, hroot, hdisjoint⟩ :=
    restrictedEffectiveSampledRunProcessPrefix_spec 𝒜 N ambientLength t
      sizes hlen hpowers hmono stateCode state badCodes bads hstate
      hlen_bads hbad badCodes.length le_rfl
  refine ⟨output, next, ?_, hnext, hBzero, hliveZero, hroot, ?_⟩
  · exact hrun
  · intro i hi
    exact hdisjoint i (by omega)

/-- Every finite effective run over an actual sampled grid terminates in a
decoded state, and every previously processed canonical bad event is disjoint
from every live level.

The target exponent is deliberately tied to the executable size schedule. -/
lemma restrictedEffectiveSampledRun_processed_disjoint
    (𝒜 : DescriptionFamily) (c : Code)
    {n k N : ℕ} {target : ℕ → ℕ}
    (grid : RestrictedCurveGrid n k N target)
    (ambientLength Δ time : ℕ)
    (hnambient : n ≤ ambientLength) :
    ∃ output : BitString,
      ∃ state : RestrictedSampledRunState 𝒜 N ambientLength
          (2 * 𝒜.overhead ambientLength)
          (fun s => grid.j s - (Δ + 1)),
        restrictedEffectiveSampledRun 𝒜 c (restrictedCurveGridCode grid)
            ambientLength N Δ time = Part.some output ∧
        DecodesToRestrictedSampledRunState output state ∧
        ∀ time' < time,
          ∀ w ∈ restrictedSampledBadBatchAt c (restrictedCurveGridCode grid)
            𝒜.toPre N Δ time',
          ∀ bad : Finset BitString,
            decodeCoverCodeList w = canonicalFinsetList bad →
            ∀ s ≤ N, Disjoint (state.live s) bad := by
  let sampleTarget : ℕ → ℕ := fun s => grid.j s - (Δ + 1)
  let sizes := restrictedEffectiveSampledSizes
    (restrictedCurveGridCode grid) N Δ
  have hlen : sizes.length = N + 1 := by
    exact restrictedEffectiveSampledSizes_length _ _ _
  have hpowers : ∀ s ≤ N, sizes.getD s 0 = 2 ^ sampleTarget s := by
    intro s hs
    exact restrictedEffectiveSampledSizes_grid_getD grid Δ s hs
  have hmono : ∀ s < N, sampleTarget (s + 1) ≤ sampleTarget s := by
    intro s hs
    exact Nat.sub_le_sub_right (grid.j_mono s hs) (Δ + 1)
  have htop : sampleTarget 0 ≤ ambientLength := by
    dsimp [sampleTarget]
    rw [grid.j_start]
    omega
  induction time with
  | zero =>
      obtain ⟨output, state, hrun, hstate⟩ :=
        restrictedEffectiveSampledInitialState_spec 𝒜 N ambientLength
          sampleTarget sizes hlen hpowers htop hmono
      refine ⟨output, state, ?_, hstate, ?_⟩
      · exact hrun
      · intro time' htime'
        omega
  | succ time ih =>
      obtain ⟨previousCode, previous, hrun, hprevious, hprocessed⟩ := ih
      let badCodes := restrictedSampledBadBatchAt c
        (restrictedCurveGridCode grid) 𝒜.toPre N Δ time
      let bads : List (Finset BitString) :=
        badCodes.map (fun w => (decodeCoverCodeList w).toFinset)
      have hlen_bads : badCodes.length = bads.length := by
        simp [bads]
      have hbads_getD_eq {i : ℕ} (hi : i < badCodes.length)
          {bad : Finset BitString}
          (hdecode : decodeCoverCodeList badCodes[i] = canonicalFinsetList bad) :
          bads.getD i ∅ = bad := by
        have hibads : i < bads.length := by omega
        rw [List.getD_eq_getElem _ _ hibads]
        simp only [bads, List.getElem_map]
        rw [hdecode, canonicalFinsetList_toFinset]
      have hbad : ∀ i < badCodes.length,
          decodeCoverCodeList (badCodes.getD i []) =
            canonicalFinsetList (bads.getD i ∅) := by
        intro i hi
        have hwmem : badCodes[i] ∈ restrictedSampledBadBatchAt c
            (restrictedCurveGridCode grid) 𝒜.toPre N Δ time := by
          exact List.getElem_mem hi
        obtain ⟨bad, hdecode⟩ :=
          restrictedSampledBadBatchAt_decode_sound c
            (restrictedCurveGridCode grid) 𝒜 N Δ time badCodes[i] hwmem
        rw [List.getD_eq_getElem _ _ hi, hbads_getD_eq hi hdecode]
        exact hdecode
      obtain ⟨output, state, hbatch, hstate, _hBzero, _hliveZero,
          hroot, hbatchDisjoint⟩ :=
        restrictedEffectiveSampledRunProcess_spec 𝒜 N ambientLength
          sampleTarget sizes hlen hpowers hmono previousCode previous
          badCodes bads hprevious hlen_bads hbad
      refine ⟨output, state, ?_, hstate, ?_⟩
      · change
          (restrictedEffectiveSampledRun 𝒜 c (restrictedCurveGridCode grid)
            ambientLength N Δ time).bind
              (fun current => restrictedEffectiveSampledRunProcess 𝒜
                (𝒜.overhead ambientLength) sizes current badCodes) =
            Part.some output
        rw [hrun, Part.bind_some, hbatch]
      · intro eventTime heventTime w hw bad hdecode s hs
        by_cases hcurrent : eventTime = time
        · subst eventTime
          obtain ⟨i, hi, hwi⟩ := List.getElem_of_mem hw
          have hiBadCodes : i < badCodes.length := by
            simpa [badCodes] using hi
          have hibads : i < bads.length := by omega
          have hbadEq : bads.getD i ∅ = bad :=
            hbads_getD_eq hiBadCodes (hwi ▸ hdecode)
          have hdisjoint := hbatchDisjoint i hibads s hs
          rw [hbadEq] at hdisjoint
          exact hdisjoint
        · have heventPrevious : eventTime < time := by omega
          have hprevDisjoint := hprocessed eventTime heventPrevious w hw bad
            hdecode 0 (Nat.zero_le N)
          apply Finset.disjoint_left.mpr
          intro x hx hxbad
          exact (Finset.disjoint_left.mp hprevDisjoint) (hroot s hs hx) hxbad

/-- Public finite-time semantics of the effective sampled run. -/
lemma restrictedEffectiveSampledRun_spec
    (𝒜 : DescriptionFamily) (c : Code)
    {n k N : ℕ} {target : ℕ → ℕ}
    (grid : RestrictedCurveGrid n k N target)
    (ambientLength Δ time : ℕ)
    (hnambient : n ≤ ambientLength) :
    ∃ output : BitString,
      ∃ state : RestrictedSampledRunState 𝒜 N ambientLength
          (2 * 𝒜.overhead ambientLength)
          (fun s => grid.j s - (Δ + 1)),
        restrictedEffectiveSampledRun 𝒜 c (restrictedCurveGridCode grid)
            ambientLength N Δ time = Part.some output ∧
        DecodesToRestrictedSampledRunState output state ∧
        ∀ time' < time,
          ∀ w ∈ restrictedSampledBadBatchAt c (restrictedCurveGridCode grid)
            𝒜.toPre N Δ time',
          ∀ bad : Finset BitString,
            decodeCoverCodeList w = canonicalFinsetList bad →
            ∀ s ≤ N, Disjoint (state.live s) bad := by
  exact restrictedEffectiveSampledRun_processed_disjoint 𝒜 c grid
    ambientLength Δ time hnambient

end Kolmogorov
