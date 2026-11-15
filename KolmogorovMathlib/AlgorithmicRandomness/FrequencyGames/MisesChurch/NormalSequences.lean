/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.MisesChurch.Defs

/-!
# Normal Sequences

Normal sequences and their relation to Mises-Church randomness (Shen, Uspensky, Vereshchagin,
*Kolmogorov complexity and algorithmic randomness*, Theorem 168).

A sequence is *normal* if every string `U` occurs in it with limit frequency `2^{-|U|}`.  The
module defines the occurrence frequency `occurrenceFreq` and the predicate `IsNormal`, and proves
that every Mises-Church random sequence is normal (`isNormal_of_isMisesChurchRandom`).
-/

namespace Kolmogorov.FrequencyGames
open MeasureTheory Filter Topology

/-! ### Occurrences of a string and normality -/

/-- The string `U` occurs in `ω` at position `k`: `U_0 U_1 … = ω_k ω_{k+1} …`. -/
def OccursAt (U : BitString) (w : CantorSeq) (k : ℕ) : Prop :=
  ∀ j, (hj : j < U.length) → w (k + j) = U[j]

open Classical in
/-- The fraction of positions among the first `N` at which `U` occurs in `ω`. -/
noncomputable def occurrenceFreq (U : BitString) (w : CantorSeq) (N : ℕ) : ℝ :=
  (((Finset.range N).filter fun k => OccursAt U w k).card : ℝ) / N

/-- **SUV p. 265.**  A *normal* sequence: every string `U` occurs with limit frequency
`2^{-|U|}`. -/
def IsNormal (w : CantorSeq) : Prop :=
  ∀ U : BitString, Tendsto (occurrenceFreq U w) atTop (𝓝 ((2 : ℝ)⁻¹ ^ U.length))

open Classical in
/-- Step 1 of the proof of `isNormal_of_isMisesChurchRandom`: the limit frequency for the
empty string is 1. -/
lemma isNormal_of_isMisesChurchRandom_empty (w : CantorSeq) :
    Tendsto (occurrenceFreq ([] : BitString) w) atTop (𝓝 ((2 : ℝ)⁻¹ ^ ([] : BitString).length)) :=
        by
  have H : ∀ N, 1 ≤ N → occurrenceFreq ([] : BitString) w N = 1 := by
    intro N hN
    dsimp [occurrenceFreq]
    have h1 : (Finset.range N).filter (fun k => OccursAt [] w k) = Finset.range N := by
      ext k
      constructor
      · intro h
        exact (Finset.mem_filter.mp h).1
      · intro hk
        rw [Finset.mem_filter]
        refine ⟨hk, ?_⟩
        dsimp [OccursAt]
        intro j hj
        simp at hj
    rw [h1, Finset.card_range]
    have h2 : (N : ℝ) ≠ 0 := by
      exact_mod_cast ne_of_gt hN
    exact div_self h2
  have H3 : Tendsto (occurrenceFreq ([] : BitString) w) atTop (𝓝 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [Ici_mem_atTop 1] with N hN
    rw [H N hN]
  have H4 : ((2 : ℝ)⁻¹ ^ ([] : BitString).length) = 1 := by simp
  rwa [←H4] at H3

/-- Step 2 of the proof of `isNormal_of_isMisesChurchRandom`: the selection rule based on
a suffix is decidable. -/
private lemma isNormal_of_isMisesChurchRandom_decidable (U : BitString) :
    IsDecidableSet {x : BitString | U <:+ x} := by
  have hp : PrimrecPred (fun x => U <:+ x) := by
    have h1 : PrimrecPred (fun x => U = List.drop (x.length - U.length) x) := by
      apply Primrec.eq.comp (Primrec.const _)
      apply Primrec.list_drop.comp
      · apply Primrec.nat_sub.comp Primrec.list_length (Primrec.const _)
      · exact Primrec.id
    exact h1.of_eq fun x => List.suffix_iff_eq_drop.symm
  use fun x => decide (U <:+ x)
  refine ⟨hp.decide.to_comp, ?_⟩
  intro a
  simp

/-- Step 1 of the proof of `isNormal_of_isMisesChurchRandom_counts`:
a suffix of a prefix is an occurrence ending at the prefix boundary. -/
private lemma isNormal_of_isMisesChurchRandom_suffix
    (U : BitString) (w : CantorSeq) (n : ℕ) :
    U <:+ cantorPrefix w n ↔ U.length ≤ n ∧ OccursAt U w (n - U.length) := by
  rw [List.suffix_iff_eq_drop]
  simp only [cantorPrefix_length]
  constructor
  · intro h
    have hlen : U.length ≤ n := by
      have := congrArg List.length h
      simp only [List.length_drop, cantorPrefix_length] at this
      omega
    refine ⟨hlen, ?_⟩
    intro j hj
    have hget := List.getElem_of_eq h hj
    rw [hget, List.getElem_drop, cantorPrefix_getElem]
  · rintro ⟨hlen, hocc⟩
    apply List.ext_getElem
    · simp only [List.length_drop, cantorPrefix_length]
      omega
    · intro j h1 h2
      rw [List.getElem_drop, cantorPrefix_getElem]
      exact (hocc j h1).symm

/-- Step 2 of the proof of `isNormal_of_isMisesChurchRandom_counts`:
an occurrence of `U ++ [true]` is an occurrence of `U` followed by a one. -/
private lemma isNormal_of_isMisesChurchRandom_occurs_append
    (U : BitString) (w : CantorSeq) (k : ℕ) :
    OccursAt (U ++ [true]) w k ↔ OccursAt U w k ∧ w (k + U.length) = true := by
  unfold OccursAt
  constructor
  · intro h
    refine ⟨fun j hj => ?_, ?_⟩
    · have h' := h j (by simp; omega)
      simpa only [List.getElem_append_left hj] using h'
    · have h' := h U.length (by simp)
      simpa using h'
  · rintro ⟨hU, hb⟩ j hj
    by_cases hjU : j < U.length
    · rw [List.getElem_append_left hjU]
      exact hU j hjU
    · have hj' : j = U.length := by simp at hj; omega
      subst j
      simpa using hb

open Classical in
/-- Step 3 of the proof of `isNormal_of_isMisesChurchRandom`: length and count correspond
to occurrences. -/
private lemma isNormal_of_isMisesChurchRandom_counts (U : BitString) (w : CantorSeq) (t : ℕ) :
    (selectChain {x : BitString | U <:+ x} w t).length =
      ((Finset.range (t - U.length)).filter (fun k => OccursAt U w k)).card ∧
    (selectChain {x : BitString | U <:+ x} w t).count true =
      ((Finset.range (t - U.length)).filter (fun k => OccursAt (U ++ [true]) w k)).card := by
  have hselect (n : ℕ) (h : cantorPrefix w n ∈ {x : BitString | U <:+ x}) :
      selectChain {x : BitString | U <:+ x} w (n + 1) =
        selectChain {x : BitString | U <:+ x} w n ++ [w n] := by
    unfold selectChain
    rw [cantorPrefix_succ, selectedBits_append_singleton, ite_eq_left h]
  have hskip (n : ℕ) (h : cantorPrefix w n ∉ {x : BitString | U <:+ x}) :
      selectChain {x : BitString | U <:+ x} w (n + 1) =
        selectChain {x : BitString | U <:+ x} w n := by
    unfold selectChain
    rw [cantorPrefix_succ, selectedBits_append_singleton, ite_eq_right h, List.append_nil]
  have hcard (P : ℕ → Prop) (n : ℕ) :
      ((Finset.range (n + 1)).filter P).card =
        ((Finset.range n).filter P).card + if P n then 1 else 0 := by
    by_cases h : P n <;> simp [Finset.range_add_one, Finset.filter_insert, h]
  induction t with
  | zero => simp [selectChain, cantorPrefix, selectedBits, selectedAux]
  | succ t ih =>
    by_cases ht : U.length ≤ t
    · have hsub : t + 1 - U.length = (t - U.length) + 1 := by omega
      by_cases hs : U <:+ cantorPrefix w t
      · have hocc : OccursAt U w (t - U.length) :=
          ((isNormal_of_isMisesChurchRandom_suffix U w t).mp hs).2
        have hocc1 : OccursAt (U ++ [true]) w (t - U.length) ↔ w t = true := by
          rw [isNormal_of_isMisesChurchRandom_occurs_append,
            Nat.sub_add_cancel ht, and_iff_right hocc]
        rw [hselect t hs, hsub, hcard, hcard]
        constructor
        · simp [ih.1, hocc]
        · cases hb : w t <;> simp [List.count_append, ih.2, hocc1, hb]
      · have hocc : ¬ OccursAt U w (t - U.length) := by
          intro h
          exact hs ((isNormal_of_isMisesChurchRandom_suffix U w t).mpr
            ⟨ht, h⟩)
        have hocc1 : ¬ OccursAt (U ++ [true]) w (t - U.length) := by
          rw [isNormal_of_isMisesChurchRandom_occurs_append]
          simp [hocc]
        rw [hskip t hs, hsub, hcard, hcard]
        simpa only [ite_eq_right hocc, ite_eq_right hocc1, Nat.add_zero] using ih
    · have hs : ¬ U <:+ cantorPrefix w t := by
        intro h
        have hlen := h.length_le
        simp only [cantorPrefix_length] at hlen
        omega
      have hsub : t + 1 - U.length = 0 := by omega
      have hsub' : t - U.length = 0 := by omega
      rw [hskip t hs, hsub]
      simpa only [hsub'] using ih

/-- Step 4a of the proof of `isNormal_of_isMisesChurchRandom_limitFreq`: a stream
prefix set of unbounded length determines an infinite sequence of which every member is an initial
segment. -/
private lemma isNormal_of_isMisesChurchRandom_ofPrefixSet_infinite
    {T : Set BitString}
    (hT : IsStreamPrefixSet T) (h_unbdd : ¬ ∃ M, ∀ x ∈ T, x.length ≤ M) :
    ∃ u : CantorSeq, BitStream.ofPrefixSet T hT = .infinite u ∧ ∀ x ∈ T, IsCantorPrefix x u := by
  classical
  refine ⟨fun i => (Classical.choose (exists_mem_length_gt h_unbdd i)).get
      ⟨i, (Classical.choose_spec (exists_mem_length_gt h_unbdd i)).2⟩, ?_,
    isCantorPrefix_of_mem hT h_unbdd⟩
  unfold BitStream.ofPrefixSet
  rw [dite_eq_right h_unbdd]

/-- Step 4 of the proof of `isNormal_of_isMisesChurchRandom`: applying a decidable
selection rule with unbounded length to a Mises-Church random sequence gives a sequence with limit
frequency 1/2. -/
private lemma isNormal_of_isMisesChurchRandom_limitFreq {w : CantorSeq} {R : Set BitString}
    (hw : IsMisesChurchRandom w) (hR : IsDecidableSet R)
    (h_unbounded : Tendsto (fun t => (selectChain R w t).length) atTop atTop) :
    Tendsto (fun t => ((selectChain R w t).count true : ℝ) / (selectChain R w t).length) atTop
        (𝓝 (1 / 2)) := by
  have hwR := hw R hR
  have hT : IsStreamPrefixSet (chainPrefixSet (selectChain R w)) :=
    isStreamPrefixSet_chainPrefixSet (selectChain_prefix R w)
  have h_unbdd : ¬ ∃ M, ∀ x ∈ chainPrefixSet (selectChain R w), x.length ≤ M := by
    rintro ⟨M, hM⟩
    have hM_tendsto := Filter.tendsto_atTop_atTop.mp h_unbounded (M + 1)
    obtain ⟨N, hN⟩ := hM_tendsto
    have hN_val := hN N (le_refl N)
    have h_mem : selectChain R w N ∈ chainPrefixSet (selectChain R w) := ⟨N, List.prefix_rfl⟩
    have h_le := hM (selectChain R w N) h_mem
    omega
  unfold FiniteOrFreq at hwR
  have hsel : selectStream R w = BitStream.ofPrefixSet (chainPrefixSet (selectChain R w)) hT := rfl
  rw [hsel] at hwR
  obtain ⟨u, hu_eq, hu_pref⟩ :=
      isNormal_of_isMisesChurchRandom_ofPrefixSet_infinite hT h_unbdd
  unfold BitStream.ofPrefixSet at hwR
  rw [dite_eq_right h_unbdd] at hwR
  unfold HasLimitFreq at hwR
  have h_u_eq : u = fun (i : ℕ) =>
          ((Classical.choose (exists_mem_length_gt h_unbdd i)).get
            ⟨i, (Classical.choose_spec (exists_mem_length_gt h_unbdd i)).2⟩) := by
    have h1 : BitStream.infinite u = BitStream.infinite (fun i =>
          List.get (Classical.choose (exists_mem_length_gt h_unbdd i))
            ⟨i, (Classical.choose_spec (exists_mem_length_gt h_unbdd i)).2⟩) := by
      rw [← hu_eq]
      unfold BitStream.ofPrefixSet
      rw [dite_eq_right h_unbdd]
    injection h1
  have hwR_cast : Tendsto (fun n => (freqOne u n : ℝ)) atTop (𝓝 (1 / 2)) := by
    rw [h_u_eq]
    exact hwR
  have h_eq : (fun t => ((selectChain R w t).count true : ℝ) / (selectChain R w t).length) =
      (fun t => (freqOne u (selectChain R w t).length : ℝ)) := by
    funext t
    have hpref : IsCantorPrefix (selectChain R w t) u := hu_pref (selectChain R w t)
        ⟨t, List.prefix_rfl⟩
    have heq2 := (isCantorPrefix_iff_cantorPrefix_eq (selectChain R w t) u).mp hpref
    unfold freqOne
    rw [heq2]
    push_cast
    rfl
  rw [h_eq]
  exact hwR_cast.comp h_unbounded

open Classical in
/-- Step 5 of the proof of `isNormal_of_isMisesChurchRandom`: the length is unbounded if
the occurrence frequency is positive. -/
private lemma isNormal_of_isMisesChurchRandom_unbounded {w : CantorSeq} {U : BitString}
    (hU : Tendsto (occurrenceFreq U w) atTop (𝓝 ((2 : ℝ)⁻¹ ^ U.length)))
    (h_counts : ∀ t,
      (selectChain {x : BitString | U <:+ x} w t).length =
        ((Finset.range (t - U.length)).filter (fun k => OccursAt U w k)).card ∧
      (selectChain {x : BitString | U <:+ x} w t).count true =
        ((Finset.range (t - U.length)).filter (fun k => OccursAt (U ++ [true]) w k)).card) :
    Tendsto (fun t => (selectChain {x : BitString | U <:+ x} w t).length) atTop atTop := by
  let p : ℝ := (2:ℝ)⁻¹ ^ U.length
  have hp : 0 < p := by positivity
  let c := fun N => ((Finset.range N).filter (fun k => OccursAt U w k)).card
  
  have hc : ∀ N, (c N : ℝ) = N * occurrenceFreq U w N := by
    intro N
    unfold occurrenceFreq c
    by_cases hN : N = 0
    · subst hN
      simp
    · rw [mul_div_cancel₀]
      exact Nat.cast_ne_zero.mpr hN
  have hc_tendsto_real : Tendsto (fun N => (c N : ℝ)) atTop atTop := by
    apply tendsto_atTop_atTop.mpr
    intro (M : ℝ)
    have hU_ev : ∀ᶠ N : ℕ in atTop, p / 2 < occurrenceFreq U w N := by
      have h1 : p / 2 < p := half_lt_self hp
      exact Tendsto.eventually hU (lt_mem_nhds h1)
    have hN_ev : ∀ᶠ N : ℕ in atTop, (max 0 M) * 2 / p < (N : ℝ) := by
      exact tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop _)
    obtain ⟨N0, hN0⟩ := eventually_atTop.mp (hU_ev.and hN_ev)
    use N0
    intro N hN
    have ⟨hUN, hNN⟩ := hN0 N hN
    rw [hc N]
    have h0_le_max : 0 ≤ max 0 M := le_max_left 0 M
    have h_prod2 : 0 ≤ (max 0 M) * 2 / p := by positivity
    have h0N : 0 < (N : ℝ) := lt_of_le_of_lt h_prod2 hNN
    have h1 : (max 0 M) * 2 / p * (p / 2) < (N : ℝ) * occurrenceFreq U w N := by
      have hp2 : 0 < p / 2 := half_pos hp
      have hA : (max 0 M) * 2 / p * (p / 2) < (N : ℝ) * (p / 2) := mul_lt_mul_of_pos_right hNN hp2
      have hB : (N : ℝ) * (p / 2) < (N : ℝ) * occurrenceFreq U w N := mul_lt_mul_of_pos_left hUN h0N
      linarith
    have h2 : (max 0 M) * 2 / p * (p / 2) = max 0 M := by
      calc
        (max 0 M) * 2 / p * (p / 2) = (max 0 M) * (2 / p * (p / 2)) := by ring
        _ = (max 0 M) * 1 := by
          congr 1
          calc 2 / p * (p / 2) = (2 * p) / (p * 2) := div_mul_div_comm 2 p p 2
          _ = (2 * p) / (2 * p) := by ring_nf
          _ = 1 := div_self (by positivity)
        _ = max 0 M := mul_one _
    rw [h2] at h1
    exact le_trans (le_max_right 0 M) (le_of_lt h1)
  have hc_tendsto : Tendsto c atTop atTop := tendsto_natCast_atTop_iff.mp hc_tendsto_real
  
  have ht_tendsto : Tendsto (fun t => t - U.length) atTop atTop := tendsto_sub_atTop_nat U.length
  have h_comp := Tendsto.comp hc_tendsto ht_tendsto
  
  have h_eq : (fun (t : ℕ) => List.length (selectChain {x | U <:+ x} w t)) =
      (fun t => c (t - U.length)) := by
    ext t
    have h1 := (h_counts t).1
    exact h1
  
  rw [h_eq]
  exact h_comp

/-- Appending a bit specifies the next coordinate after an occurrence of `U`. -/
private lemma isNormal_of_isMisesChurchRandom_assemble_occurs_append
    (U : BitString) (w : CantorSeq) (k : ℕ) (b : Bool) :
    OccursAt (U ++ [b]) w k ↔ OccursAt U w k ∧ w (k + U.length) = b := by
  unfold OccursAt
  constructor
  · intro h
    refine ⟨fun j hj => ?_, ?_⟩
    · have h' := h j (by simp; omega)
      simpa only [List.getElem_append_left hj] using h'
    · have h' := h U.length (by simp)
      simpa using h'
  · rintro ⟨hU, hb⟩ j hj
    by_cases hjU : j < U.length
    · rw [List.getElem_append_left hjU]
      exact hU j hjU
    · have hj' : j = U.length := by simp at hj; omega
      subst j
      simpa using hb

open Classical in
/-- The frequencies of the two one-bit extensions sum to the frequency of `U`. -/
private lemma isNormal_of_isMisesChurchRandom_frequency_split
    (U : BitString) (w : CantorSeq) (N : ℕ) :
    occurrenceFreq (U ++ [false]) w N =
      occurrenceFreq U w N - occurrenceFreq (U ++ [true]) w N := by
  have hfilter (b : Bool) :
      (Finset.range N).filter (fun k => OccursAt (U ++ [b]) w k) =
        ((Finset.range N).filter (fun k => OccursAt U w k)).filter
          (fun k => w (k + U.length) = b) := by
    ext k
    simp [isNormal_of_isMisesChurchRandom_assemble_occurs_append, and_assoc]
  have hcard := Finset.card_filter_add_card_filter_not
    (s := (Finset.range N).filter (fun k => OccursAt U w k))
    (fun k => w (k + U.length) = true)
  simp only [Bool.not_eq_true] at hcard
  rw [← hfilter true, ← hfilter false] at hcard
  have hcardR :
      (((Finset.range N).filter (fun k => OccursAt (U ++ [true]) w k)).card : ℝ) +
        (((Finset.range N).filter (fun k => OccursAt (U ++ [false]) w k)).card : ℝ) =
      (((Finset.range N).filter (fun k => OccursAt U w k)).card : ℝ) := by
    exact_mod_cast hcard
  unfold occurrenceFreq
  rw [← hcardR, add_div]
  ring

open Classical in
/-- Step 6 of the proof of `isNormal_of_isMisesChurchRandom`: assembling the induction
step using the split of occurrences. -/
private lemma isNormal_of_isMisesChurchRandom_assemble {w : CantorSeq} {U : BitString}
    {b : Bool}
    (hU : Tendsto (occurrenceFreq U w) atTop (𝓝 ((2 : ℝ)⁻¹ ^ U.length)))
    (h_counts : ∀ t,
      (selectChain {x : BitString | U <:+ x} w t).length =
        ((Finset.range (t - U.length)).filter (fun k => OccursAt U w k)).card ∧
      (selectChain {x : BitString | U <:+ x} w t).count true =
        ((Finset.range (t - U.length)).filter (fun k => OccursAt (U ++ [true]) w k)).card)
    (h_limit : Tendsto (fun t => ((selectChain {x : BitString | U <:+ x} w t).count true : ℝ) /
                                 (selectChain {x : BitString | U <:+ x} w t).length)
                 atTop (𝓝 (1 / 2))) :
    Tendsto (occurrenceFreq (U ++ [b]) w) atTop (𝓝 ((2 : ℝ)⁻¹ ^ (U ++ [b]).length)) := by
  let L : ℕ → ℕ := fun N => ((Finset.range N).filter (fun k => OccursAt U w k)).card
  let C : ℕ → ℕ := fun N =>
    ((Finset.range N).filter (fun k => OccursAt (U ++ [true]) w k)).card
  have hcounts (N : ℕ) :
      (selectChain {x : BitString | U <:+ x} w (N + U.length)).length = L N ∧
      (selectChain {x : BitString | U <:+ x} w (N + U.length)).count true = C N := by
    simpa only [Nat.add_sub_cancel_right] using h_counts (N + U.length)
  have hratio : Tendsto (fun N => (C N : ℝ) / L N) atTop (𝓝 (1 / 2)) := by
    apply (h_limit.comp (tendsto_add_atTop_nat U.length)).congr
    intro N
    dsimp only [Function.comp_def]
    rw [(hcounts N).1, (hcounts N).2]
  have hproduct (N : ℕ) :
      (C N : ℝ) / L N * occurrenceFreq U w N = occurrenceFreq (U ++ [true]) w N := by
    change (C N : ℝ) / L N * ((L N : ℝ) / N) = (C N : ℝ) / N
    by_cases hL : L N = 0
    · have hle : (selectChain {x : BitString | U <:+ x} w (N + U.length)).count true ≤
          (selectChain {x : BitString | U <:+ x} w (N + U.length)).length :=
        List.count_le_length
      rw [(hcounts N).1, (hcounts N).2, hL] at hle
      have hC : C N = 0 := Nat.eq_zero_of_le_zero hle
      simp [hC]
    · exact div_mul_div_cancel₀ (Nat.cast_ne_zero.mpr hL)
  have htrue : Tendsto (occurrenceFreq (U ++ [true]) w) atTop
      (𝓝 ((1 / 2 : ℝ) * (2 : ℝ)⁻¹ ^ U.length)) :=
    (hratio.mul hU).congr hproduct
  cases b with
  | false =>
    have hfalse := (hU.sub htrue).congr
      (fun N => (isNormal_of_isMisesChurchRandom_frequency_split U w N).symm)
    convert hfalse using 1
    simp only [List.length_append, List.length_singleton, pow_succ]
    ring
  | true =>
    convert htrue using 1
    simp only [List.length_append, List.length_singleton, pow_succ]
    ring

/-- **SUV Theorem 168, p. 264.**  Every Mises-Church random sequence is normal: in a Mises-Church
random sequence each string `U` occurs at the fraction of positions tending to `2^{-|U|}`. -/
theorem isNormal_of_isMisesChurchRandom {w : CantorSeq} (hw : IsMisesChurchRandom w) :
    IsNormal w := by
  intro U
  induction U using List.reverseRecOn with
  | nil => exact isNormal_of_isMisesChurchRandom_empty w
  | append_singleton U' b ih =>
    have hR := isNormal_of_isMisesChurchRandom_decidable U'
    have h_counts := isNormal_of_isMisesChurchRandom_counts U' w
    have h_unbounded := isNormal_of_isMisesChurchRandom_unbounded ih h_counts
    have h_limit := isNormal_of_isMisesChurchRandom_limitFreq hw hR h_unbounded
    exact isNormal_of_isMisesChurchRandom_assemble ih h_counts h_limit

/-- The `i`-th block of length `k` of `ω` is `U`; `k` is the length of `U`. -/
def BlockIs (U : BitString) (w : CantorSeq) (i : ℕ) : Prop :=
  OccursAt U w (i * U.length)

open Classical in
/-- The fraction of the first `N` aligned blocks of length `|U|` of `ω` that are equal to `U`. -/
noncomputable def alignedFreq (U : BitString) (w : CantorSeq) (N : ℕ) : ℝ :=
  (((Finset.range N).filter fun i => BlockIs U w i).card : ℝ) / N

/-- Aligned normality: every string `U` is, with limit frequency `2^{-|U|}`, one of the aligned
`|U|`-blocks of `ω`. -/
def IsAlignedNormal (w : CantorSeq) : Prop :=
  ∀ U : BitString, Tendsto (alignedFreq U w) atTop (𝓝 ((2 : ℝ)⁻¹ ^ U.length))


private noncomputable def alignedPrefixFreq (k : ℕ) (V : BitString) (w : CantorSeq) (N : ℕ) : ℝ :=
  @Finset.card ℕ (@Finset.filter ℕ (fun i => OccursAt V w (i * k))
      (fun a => Classical.propDecidable (OccursAt V w (a * k))) (Finset.range N)) / N

/-- Step 1 of the proof of `isAlignedNormal_of_isMisesChurchRandom`: The frequency of the
empty prefix is 1. -/
private lemma isAlignedNormal_of_isMisesChurchRandom_empty (w : CantorSeq) (k : ℕ) :
    Tendsto (alignedPrefixFreq k [] w) atTop (𝓝 1) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ici_mem_atTop 1] with N hN
  have hN' : 1 ≤ N := hN
  have hfilt : (@Finset.filter ℕ (fun i => OccursAt ([] : BitString) w (i * k))
      (fun a => Classical.propDecidable (OccursAt ([] : BitString) w (a * k))) (Finset.range N))
      = Finset.range N := by
    classical
    convert Finset.filter_true_of_mem (s := Finset.range N)
      (p := fun i => OccursAt ([] : BitString) w (i * k)) ?_
    intro i _ j hj
    simp at hj
  unfold alignedPrefixFreq
  rw [hfilt, Finset.card_range]
  have : (N : ℝ) ≠ 0 := by positivity
  exact (div_self this).symm

/-- Step 2 of the proof of `isAlignedNormal_of_isMisesChurchRandom`: Induction step part
1: the aligned block rule is decidable. -/
private lemma isAlignedNormal_of_isMisesChurchRandom_decidable (k : ℕ) (V : BitString) :
    IsDecidableSet {x : BitString | x.length % k = V.length ∧ V <:+ x} := by
  have h : Primrec fun x : BitString =>
      decide (x.length % k = V.length) && decide (x.drop (x.length - V.length) = V) := by
    have h1 : Primrec fun x : BitString => decide (x.length % k = V.length) :=
      (PrimrecRel.comp Primrec.eq
        (Primrec.nat_mod.comp (Primrec.list_length) (Primrec.const k))
        (Primrec.const V.length)).decide
    have h2 : Primrec fun x : BitString => decide (x.drop (x.length - V.length) = V) :=
      (PrimrecRel.comp Primrec.eq
        (Primrec.list_drop.comp
          (Primrec.nat_sub.comp Primrec.list_length (Primrec.const V.length)) Primrec.id)
        (Primrec.const V)).decide
    exact Primrec.and.comp h1 h2
  refine ⟨_, h.to_comp, fun x => ?_⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq, Set.mem_ofPred_eq]
  rw [List.suffix_iff_eq_drop, eq_comm (a := V)]

private lemma isAlignedNormal_of_isMisesChurchRandom_count_aux1_mem
    (w : CantorSeq) (k : ℕ) (V : BitString) (N j : ℕ) (hj : j < k) :
    cantorPrefix w (N * k + j) ∈ {x : BitString | x.length % k = V.length ∧ V <:+ x} ↔
      (j = V.length ∧ OccursAt V w (N * k)) := by
  simp only [Set.mem_ofPred_eq, cantorPrefix_length]
  have hmod : (N * k + j) % k = j := by
    rw [Nat.mul_comm, Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hj
  rw [hmod]
  constructor
  · rintro ⟨h1, h2⟩
    subst h1
    have := (isNormal_of_isMisesChurchRandom_suffix V w (N * k + V.length)).mp h2
    refine ⟨rfl, ?_⟩
    simpa using this.2
  · rintro ⟨h1, h2⟩
    subst h1
    refine ⟨rfl, ?_⟩
    rw [isNormal_of_isMisesChurchRandom_suffix]
    exact ⟨by omega, by simpa using h2⟩

open Classical in
private lemma isAlignedNormal_of_isMisesChurchRandom_count_aux2_block
    (w : CantorSeq) (k : ℕ) (V : BitString) (N : ℕ) :
    ∀ j, j ≤ k →
    selectedBits {x : BitString | x.length % k = V.length ∧ V <:+ x} (cantorPrefix w (N * k + j)) =
      selectedBits {x : BitString | x.length % k = V.length ∧ V <:+ x} (cantorPrefix w (N * k)) ++
        (if V.length < j ∧ OccursAt V w (N * k) then [w (N * k + V.length)] else []) := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    have hjk : j < k := by omega
    rw [← Nat.add_assoc, cantorPrefix_succ, selectedBits_append_singleton, ih (by omega)]
    by_cases hm : cantorPrefix w (N * k + j) ∈ {x : BitString | x.length % k = V.length ∧ V <:+ x}
    · obtain ⟨h1, h2⟩ := (isAlignedNormal_of_isMisesChurchRandom_count_aux1_mem w k V N j
        hjk).mp hm
      subst h1
      rw [ite_eq_left hm]
      simp [h2]
    · rw [ite_eq_right hm, List.append_nil]
      have hn : ¬ (j = V.length ∧ OccursAt V w (N * k)) := fun h =>
        hm ((isAlignedNormal_of_isMisesChurchRandom_count_aux1_mem w k V N j hjk).mpr h)
      have hiff : (V.length < j + 1 ∧ OccursAt V w (N * k)) ↔ (V.length < j ∧ OccursAt V w (N * k))
          := by
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨?_, h2⟩
          by_contra hc
          exact hn ⟨by omega, h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
      simp only [hiff]

/-- Step 3 of the proof of `isAlignedNormal_of_isMisesChurchRandom`: Induction step part
2: the length and the count of true for the selected sequence. -/
private lemma isAlignedNormal_of_isMisesChurchRandom_count (w : CantorSeq) (k : ℕ)
    (V : BitString) (hV : V.length < k) (N : ℕ) :
    (selectedBits {x : BitString | x.length % k = V.length ∧ V <:+ x}
        (cantorPrefix w (N * k))).length =
      @Finset.card ℕ (@Finset.filter ℕ (fun i => OccursAt V w (i * k))
          (fun a => Classical.propDecidable (OccursAt V w (a * k))) (Finset.range N)) ∧
    ((selectedBits {x : BitString | x.length % k = V.length ∧ V <:+ x} (cantorPrefix w (N *
        k))).count true) =
      @Finset.card ℕ (@Finset.filter ℕ (fun i => OccursAt (V ++ [true]) w (i * k))
          (fun a => Classical.propDecidable (OccursAt (V ++ [true]) w (a * k))) (Finset.range N)) :=
          by
  classical
  have hcard (P : ℕ → Prop) [DecidablePred P] (n : ℕ) :
      ((Finset.range (n + 1)).filter P).card =
        ((Finset.range n).filter P).card + if P n then 1 else 0 := by
    by_cases h : P n <;> simp [Finset.range_add_one, Finset.filter_insert, h]
  induction N with
  | zero => simp [cantorPrefix, selectedBits, selectedAux]
  | succ N ih =>
    have hblock := isAlignedNormal_of_isMisesChurchRandom_count_aux2_block w k V N k le_rfl
    rw [Nat.succ_mul, hblock, hcard, hcard]
    by_cases hocc : OccursAt V w (N * k)
    · have hocc1 : OccursAt (V ++ [true]) w (N * k) ↔ w (N * k + V.length) = true := by
        rw [isNormal_of_isMisesChurchRandom_occurs_append, and_iff_right hocc]
      cases hb : w (N * k + V.length) <;>
        simp [List.count_append, ih.1, ih.2, hocc, hocc1, hb, hV]
    · have hocc1 : ¬ OccursAt (V ++ [true]) w (N * k) := by
        rw [isNormal_of_isMisesChurchRandom_occurs_append]
        simp [hocc]
      simp [ih.1, ih.2, hocc, hocc1, hV]

/-- Step 4 of the proof of `isAlignedNormal_of_isMisesChurchRandom`: General transfer
lemma for a selection rule on a sequence of indices. -/
private lemma isAlignedNormal_of_isMisesChurchRandom_transfer {w : CantorSeq}
    (hw : IsMisesChurchRandom w) {R : Set BitString} (hR : IsDecidableSet R)
    (s : ℕ → ℕ) (hs : Tendsto (fun N => (selectChain R w (s N)).length) atTop atTop) :
    Tendsto (fun N => ((selectChain R w (s N)).count true : ℝ) / (selectChain R w (s N)).length)
        atTop (𝓝 (1 / 2)) := by
  have hwR := hw R hR
  have hT : IsStreamPrefixSet (chainPrefixSet (selectChain R w)) :=
    isStreamPrefixSet_chainPrefixSet (selectChain_prefix R w)
  have h_unbdd : ¬ ∃ M, ∀ x ∈ chainPrefixSet (selectChain R w), x.length ≤ M := by
    rintro ⟨M, hM⟩
    obtain ⟨N, hN⟩ := Filter.tendsto_atTop_atTop.mp hs (M + 1)
    have hN_val := hN N (le_refl N)
    have h_mem : selectChain R w (s N) ∈ chainPrefixSet (selectChain R w) := ⟨s N, List.prefix_rfl⟩
    have h_le := hM (selectChain R w (s N)) h_mem
    omega
  unfold FiniteOrFreq at hwR
  have hsel : selectStream R w = BitStream.ofPrefixSet (chainPrefixSet (selectChain R w)) hT := rfl
  rw [hsel] at hwR
  obtain ⟨u, hu_eq, hu_pref⟩ :=
      isNormal_of_isMisesChurchRandom_ofPrefixSet_infinite hT h_unbdd
  unfold BitStream.ofPrefixSet at hwR
  rw [dite_eq_right h_unbdd] at hwR
  unfold HasLimitFreq at hwR
  have h_u_eq : u = fun (i : ℕ) =>
          ((Classical.choose (exists_mem_length_gt h_unbdd i)).get
            ⟨i, (Classical.choose_spec (exists_mem_length_gt h_unbdd i)).2⟩) := by
    have h1 : BitStream.infinite u = BitStream.infinite (fun i =>
          List.get (Classical.choose (exists_mem_length_gt h_unbdd i))
            ⟨i, (Classical.choose_spec (exists_mem_length_gt h_unbdd i)).2⟩) := by
      rw [← hu_eq]
      unfold BitStream.ofPrefixSet
      rw [dite_eq_right h_unbdd]
    injection h1
  have hwR_cast : Tendsto (fun n => (freqOne u n : ℝ)) atTop (𝓝 (1 / 2)) := by
    rw [h_u_eq]
    exact hwR
  have h_eq : (fun N => ((selectChain R w (s N)).count true : ℝ) / (selectChain R w (s N)).length) =
      (fun N => (freqOne u (selectChain R w (s N)).length : ℝ)) := by
    funext N
    have hpref : IsCantorPrefix (selectChain R w (s N)) u :=
      hu_pref (selectChain R w (s N)) ⟨s N, List.prefix_rfl⟩
    have heq2 := (isCantorPrefix_iff_cantorPrefix_eq (selectChain R w (s N)) u).mp hpref
    unfold freqOne
    rw [heq2]
    push_cast
    rfl
  rw [h_eq]
  exact hwR_cast.comp hs

private lemma isAlignedNormal_of_isMisesChurchRandom_ind_occ_append
    (U : BitString) (b : Bool) (w : CantorSeq) (m : ℕ) :
    OccursAt (U ++ [b]) w m ↔ OccursAt U w m ∧ w (m + U.length) = b := by
  constructor
  · intro h
    refine ⟨fun j hj => ?_, ?_⟩
    · have := h j (by simp; omega)
      simpa [List.getElem_append_left hj] using this
    · have := h U.length (by simp)
      simpa using this
  · rintro ⟨h1, h2⟩ j hj
    simp only [List.length_append, List.length_singleton] at hj
    rcases Nat.lt_or_ge j U.length with hlt | hge
    · rw [List.getElem_append_left hlt]
      exact h1 j hlt
    · have : j = U.length := by omega
      subst this
      simp [h2]

private noncomputable def isAlignedNormal_of_isMisesChurchRandom_ind_cnt
    (k : ℕ) (V : BitString) (w : CantorSeq) (N : ℕ) : ℕ :=
  @Finset.card ℕ (@Finset.filter ℕ (fun i => OccursAt V w (i * k))
      (fun a => Classical.propDecidable (OccursAt V w (a * k))) (Finset.range N))

private lemma isAlignedNormal_of_isMisesChurchRandom_ind_cnt_add
    (k : ℕ) (V : BitString) (w : CantorSeq) (N : ℕ) :
    isAlignedNormal_of_isMisesChurchRandom_ind_cnt k V w N =
      isAlignedNormal_of_isMisesChurchRandom_ind_cnt k (V ++ [true]) w N +
      isAlignedNormal_of_isMisesChurchRandom_ind_cnt k (V ++ [false]) w N := by
  classical
  unfold isAlignedNormal_of_isMisesChurchRandom_ind_cnt
  have e : ∀ U : BitString, (@Finset.filter ℕ (fun i => OccursAt U w (i * k))
      (fun a => Classical.propDecidable (OccursAt U w (a * k))) (Finset.range N)) =
      (Finset.range N).filter (fun i => OccursAt U w (i * k)) := by
    intro U; congr
  rw [e, e, e]
  simp only [Finset.card_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [isAlignedNormal_of_isMisesChurchRandom_ind_occ_append]
  cases h : w (i * k + V.length)
  · by_cases hV : OccursAt V w (i * k) <;> simp [hV]
  · by_cases hV : OccursAt V w (i * k) <;> simp [hV]

/-- Step 5 of the proof of `isAlignedNormal_of_isMisesChurchRandom`: Assembles steps 2-4
to prove the induction step. -/
private lemma isAlignedNormal_of_isMisesChurchRandom_ind {w : CantorSeq}
    (hw : IsMisesChurchRandom w) (k : ℕ) (V : BitString) (b : Bool) (hV : V.length < k) :
    Tendsto (alignedPrefixFreq k V w) atTop (𝓝 ((2 : ℝ)⁻¹ ^ V.length)) →
    Tendsto (alignedPrefixFreq k (V ++ [b]) w) atTop (𝓝 ((2 : ℝ)⁻¹ ^ (V ++ [b]).length)) := by
  intro hA
  set cnt := isAlignedNormal_of_isMisesChurchRandom_ind_cnt k with hcnt
  have hfreq : ∀ U N, alignedPrefixFreq k U w N = (cnt U w N : ℝ) / N := fun U N => rfl
  have hadd := isAlignedNormal_of_isMisesChurchRandom_ind_cnt_add k V w
  have hpos : (0 : ℝ) < (2 : ℝ)⁻¹ ^ V.length := by positivity
  -- (b) A_N → ∞
  have hAtop : Tendsto (fun N => cnt V w N) atTop atTop := by
    rw [← tendsto_natCast_atTop_iff (R := ℝ)]
    have h1 := Filter.Tendsto.pos_mul_atTop hpos hA tendsto_natCast_atTop_atTop
    refine h1.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    have : (N : ℝ) ≠ 0 := by positivity
    simp only [hfreq]
    field_simp
  -- (c) B_N / A_N → 1/2
  have hR := isAlignedNormal_of_isMisesChurchRandom_decidable k V
  have hlen : Tendsto (fun N => (selectChain {x : BitString | x.length % k = V.length ∧ V <:+ x} w
                                  (N * k)).length) atTop atTop := by
    refine hAtop.congr (fun N => ?_)
    exact (isAlignedNormal_of_isMisesChurchRandom_count w k V hV N).1.symm
  have h4 := isAlignedNormal_of_isMisesChurchRandom_transfer hw hR (fun N => N * k) hlen
  have hratio : Tendsto (fun N => (cnt (V ++ [true]) w N : ℝ) / (cnt V w N : ℝ)) atTop (𝓝 (1 / 2))
      := by
    refine h4.congr (fun N => ?_)
    have h3 := isAlignedNormal_of_isMisesChurchRandom_count w k V hV N
    simp only [selectChain]
    rw [h3.1, h3.2]
    rfl
  -- (d) B_N / N → 2⁻¹ ^ (|V|+1)
  have hB : Tendsto (fun N => (cnt (V ++ [true]) w N : ℝ) / N) atTop
      (𝓝 ((2 : ℝ)⁻¹ ^ (V ++ [true]).length)) := by
    have h5 := hratio.mul hA
    have e : (1 / 2 : ℝ) * (2 : ℝ)⁻¹ ^ V.length = (2 : ℝ)⁻¹ ^ (V ++ [true]).length := by
      simp [pow_succ]; ring
    rw [e] at h5
    refine h5.congr' ?_
    filter_upwards [hAtop.eventually_ge_atTop 1] with N hN
    have hA0 : (cnt V w N : ℝ) ≠ 0 := by
      have : (1 : ℝ) ≤ cnt V w N := by exact_mod_cast hN
      linarith
    simp only [hfreq]
    field_simp
  cases b
  · have h6 := hA.sub hB
    have e : (2 : ℝ)⁻¹ ^ V.length - (2 : ℝ)⁻¹ ^ (V ++ [true]).length = (2 : ℝ)⁻¹ ^
        (V ++ [false]).length := by
      simp [pow_succ]; ring
    rw [e] at h6
    refine h6.congr (fun N => ?_)
    have := hadd N
    simp only [hfreq]
    have h' : (cnt V w N : ℝ) = cnt (V ++ [true]) w N + cnt (V ++ [false]) w N := by
      exact_mod_cast this
    rw [h', ← sub_div]
    ring_nf
  · exact hB

/-- Step 6 of the proof of `isAlignedNormal_of_isMisesChurchRandom`: Generalizes the
induction to any prefix of length <= k. -/
private lemma isAlignedNormal_of_isMisesChurchRandom_prefix {w : CantorSeq}
    (hw : IsMisesChurchRandom w) (k : ℕ) (V : BitString) (hV : V.length ≤ k) :
    Tendsto (alignedPrefixFreq k V w) atTop (𝓝 ((2 : ℝ)⁻¹ ^ V.length)) := by
  induction V using List.reverseRecOn with
  | nil =>
    have h : (2 : ℝ)⁻¹ ^ (List.length (α := Bool) []) = 1 := by simp
    rw [h]
    exact isAlignedNormal_of_isMisesChurchRandom_empty w k
  | append_singleton L b ih =>
    have hL : L.length < k := by
      have : L.length + 1 = (L ++ [b]).length := by simp
      omega
    have hL_le : L.length ≤ k := by omega
    exact isAlignedNormal_of_isMisesChurchRandom_ind hw k L b hL (ih hL_le)

/-- Step 7 of the proof of `isAlignedNormal_of_isMisesChurchRandom`: Equality between
`alignedPrefixFreq` and `alignedFreq` when prefix length is k. -/
private lemma isAlignedNormal_of_isMisesChurchRandom_eq (U : BitString) (w : CantorSeq)
    (N : ℕ) :
    alignedPrefixFreq U.length U w N = alignedFreq U w N := by
  dsimp [alignedPrefixFreq, alignedFreq, BlockIs]
  rfl

/-- **SUV Problem 254, p. 264.**  In a Mises-Church random sequence each of the `2^k` aligned
`k`-blocks has limit frequency `2^{-k}`. -/
theorem isAlignedNormal_of_isMisesChurchRandom {w : CantorSeq} (hw : IsMisesChurchRandom w) :
    IsAlignedNormal w := by
  intro U
  have h := isAlignedNormal_of_isMisesChurchRandom_prefix hw U.length U (le_refl _)
  have h_eq : alignedPrefixFreq U.length U w = alignedFreq U w := by
    funext N
    exact isAlignedNormal_of_isMisesChurchRandom_eq U w N
  rw [← h_eq]
  exact h

end Kolmogorov.FrequencyGames
