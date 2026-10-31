/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Enumeration
import KolmogorovMathlib.RandomStrings.Plain.PrefixInterface

/-!
# The last short program of the canonical enumeration

For a base `B`, the canonical enumeration of the programs of `B.V` emits events
`(tick, position, program, output)`.  This module defines the *marker* at scale `n`: the last
program of length at most `n` to be emitted, together with its emission tick and position, and the
quantity `rest B n u` counting the `u`-simple outputs that appear after the marker.

We prove the stabilization property of the marker (blueprint node
`lem:marker-stabilization`): for large `n` the marker is a valid witnessed candidate, all
output tables of scale at most `n` are final at the marker tick, and no program of length at most
`n` is emitted later.  We also show that the marker program has length at most `n` and
conditional complexity `n + O(1)` given `bits n`, by decoding a fresh string of length `n + 1`
from a short description of the marker, which contradicts optimality unless the description is
long.

These results are used by the other modules of `Markers`, in particular for the tail bound
`lem:tail` on `rest`.
-/

namespace Kolmogorov.Milovanov

/-- The emission tick of a program, or zero if it never emits; this is a semantic function.
Blueprint node `lem:marker-stabilization`. -/
noncomputable def programTick (B : Base) (p : BitString) : ℕ :=
  sInf {t : ℕ | ∃ i x, eventAt B t = some (t, i, p, x)}

/-- The last emission tick among all programs of length at most `n`, with empty default zero.
Blueprint node `lem:marker-stabilization`. The maximum is over programs, including
different programs with identical outputs. -/
noncomputable def markerTick (B : Base) (n : ℕ) : ℕ :=
  (boundedPrograms n).toFinset.sup (programTick B)

/-- The last emitted short program, with the empty string as the empty-scale default.
Blueprint node `lem:marker-stabilization`. -/
noncomputable def lastProgram (B : Base) (n : ℕ) : BitString :=
  ((eventAt B (markerTick B n)).map (fun e => e.2.2.1)).getD []

/-- The zero-based position of the marker event, distinct from its numeric tick.
Blueprint node `lem:marker-stabilization`. Zero is also the empty-scale default. -/
noncomputable def markerPosition (B : Base) (n : ℕ) : ℕ :=
  ((eventAt B (markerTick B n)).map (fun e => e.2.1)).getD 0

/-- The semantic true candidate: the marker program together with its emission timestamp.
Blueprint node `lem:marker-stabilization`. This record is not computed by the construction. -/
noncomputable def markerCandidate (B : Base) (n : ℕ) : Candidate :=
  (lastProgram B n, markerTick B n)

/-- The number of new distinct `u`-simple outputs after the marker event at scale `n`.
Blueprint node `lem:tail`. This counts output-set differences, not later program events. -/
noncomputable def rest (B : Base) (n u : ℕ) : ℕ :=
  {x : BitString | Simple B.V x u ∧ x ∉ stageOutputs B u (markerTick B n)}.ncard

/-- If a program is emitted at tick `t`, then `t` is its emission tick. -/
private lemma programTick_eq_of_eventAt
    (B : Base) (p x : BitString) (t i : ℕ) (h : eventAt B t = some (t, i, p, x)) :
    programTick B p = t := by
  dsimp [programTick]
  have H : {t | ∃ i x, eventAt B t = some (t, i, p, x)} = {t} := by
    ext t'
    simp only [Set.mem_ofPred, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i', x', h'⟩
      obtain ⟨h_eq, _, _⟩ := canonical_enumeration_spec_unique B h' h
      exact h_eq
    · rintro rfl
      exact ⟨i, x, h⟩
  rw [H]
  exact csInf_singleton t

/-- For every large `n`, the marker at scale `n` is a valid witnessed candidate. -/
private lemma eventually_valid_markerCandidate (B : Base) :
    ∃ n₀ : ℕ, 32 ≤ n₀ ∧ ∀ n ≥ n₀, validCandidate B n (markerCandidate B n) = true := by
  obtain ⟨c, hc⟩ := plainK_le_length B.V B.optimalV
  have h1 : Simple B.V [] c := by
    rw [simple_iff_exists_program]
    have hc' := hc []
    change condK B.V [] [] ≤ (programLength [] : ENat) + c at hc'
    change condK B.V [] [] ≤ (0 : ENat) + c at hc'
    rw [zero_add] at hc'
    rw [← condK_le_iff B.V [] [] c]
    exact hc'
  have h2 : ∃ p, p.length ≤ c ∧ produces B.V p [] [] := by
    rw [← simple_iff_exists_program]
    exact h1
  obtain ⟨p0, hp0_len, hp0_prod⟩ := h2
  have h3 : ∃ t0 i0, eventAt B t0 = some (t0, i0, p0, []) := by
    rw [← canonical_enumeration_spec_complete]
    exact hp0_prod
  obtain ⟨t0, i0, ht0⟩ := h3
  have ht0_pos : 0 < t0 := (canonical_enumeration_spec_position B ht0).1
  use max 32 c
  constructor
  · exact le_max_left _ _
  · intro n hn
    have hn_ge_c : c ≤ n := le_trans (le_max_right _ _) hn
    have h_p0_mem : p0 ∈ boundedPrograms n := by
      rw [mem_boundedPrograms_iff]
      exact le_trans hp0_len hn_ge_c
    have h_p0_tick : programTick B p0 = t0 := programTick_eq_of_eventAt B p0 [] t0 i0 ht0
    have h_tau_ge_t0 : markerTick B n ≥ t0 := by
      dsimp [markerTick]
      have h_finset : p0 ∈ (boundedPrograms n).toFinset := by
        simp only [List.mem_toFinset, h_p0_mem]
      have le := Finset.le_sup (f := programTick B) h_finset
      rw [h_p0_tick] at le
      exact le
    have h_tau_pos : 0 < markerTick B n := lt_of_lt_of_le ht0_pos h_tau_ge_t0
    have h_nonempty : ((boundedPrograms n).toFinset).Nonempty := by
      use p0
      simp only [List.mem_toFinset, h_p0_mem]
    obtain ⟨q, hq_mem, hq_sup⟩ :=
      Finset.exists_mem_eq_sup (boundedPrograms n).toFinset h_nonempty (programTick B)
    have hq_len : q.length ≤ n := by
      rw [List.mem_toFinset] at hq_mem
      rw [mem_boundedPrograms_iff] at hq_mem
      exact hq_mem
    have hq_tick : programTick B q = markerTick B n := hq_sup.symm
    have h_q_ticks_nonempty : {t | ∃ i x, eventAt B t = some (t, i, q, x)}.Nonempty := by
      by_contra hc
      rw [Set.not_nonempty_iff_eq_empty] at hc
      have h_inf : programTick B q = 0 := by
        dsimp [programTick]
        rw [hc]
        exact Nat.sInf_empty
      rw [h_inf] at hq_tick
      omega
    have h_inf_mem := Nat.sInf_mem h_q_ticks_nonempty
    have h_inf_eq : sInf {t | ∃ i x, eventAt B t = some (t, i, q, x)} = markerTick B n := by
      rw [← hq_tick]
      rfl
    have h_event : ∃ i x, eventAt B (markerTick B n) = some (markerTick B n, i, q, x) := by
      rw [← h_inf_eq]
      exact h_inf_mem
    obtain ⟨iq, xq, h_event_q⟩ := h_event
    have h_lambda : lastProgram B n = q := by
      dsimp [lastProgram]
      rw [h_event_q]
      rfl
    rw [canonical_enumeration_spec_candidate]
    constructor
    · dsimp [markerCandidate]
      rw [h_lambda]
      exact hq_len
    · use iq, xq
      dsimp [markerCandidate]
      rw [h_lambda]
      exact h_event_q

/-- For every large `n`, the output table at the marker tick agrees with the set of
`k`-simple strings for every scale `k ≤ n`. -/
private lemma eventually_stageOutputs_markerTick_eq (B : Base) :
    ∃ n₀ : ℕ, 32 ≤ n₀ ∧ ∀ n ≥ n₀, ∀ k ≤ n,
      ((stageOutputs B k (markerTick B n) : Finset BitString) : Set BitString) =
        {x | Simple B.V x k} := by
  use 32
  constructor
  · decide
  · intro n _ k hk
    ext x
    simp only [Finset.mem_coe, Set.mem_ofPred_eq]
    constructor
    · intro hx
      exact (canonical_enumeration_spec_union B k x).mpr ⟨markerTick B n, hx⟩
    · intro hx
      obtain ⟨p, hp_len, hp_prod⟩ := (simple_iff_exists_program B.V x k).mp hx
      obtain ⟨t, i, h_event_t⟩ := (canonical_enumeration_spec_complete B p x).mp hp_prod
      have h_t_in_set : t ∈ {t' : ℕ | ∃ i' x', eventAt B t' = some (t', i', p, x')} := by
        simp only [Set.mem_ofPred_eq]
        exact ⟨i, x, h_event_t⟩
      have h_tick_eq_t : programTick B p = t := by
        obtain ⟨i', x', h_event_inf⟩ := Nat.sInf_mem (Set.nonempty_of_mem h_t_in_set)
        exact (canonical_enumeration_spec_unique B h_event_t h_event_inf).1.symm
      have h_p_bounded : p ∈ boundedPrograms n := by
        rw [mem_boundedPrograms_iff]
        omega
      have h_t_le_marker : t ≤ markerTick B n := by
        rw [← h_tick_eq_t]
        unfold markerTick
        apply Finset.le_sup
        rw [List.mem_toFinset]
        exact h_p_bounded
      have h_x_in_t : x ∈ stageOutputs B k t := by
        unfold stageOutputs stageOutputList
        rw [List.mem_toFinset, List.mem_eraseDups, List.mem_filterMap]
        obtain ⟨_, _, h_get⟩ := canonical_enumeration_spec_position B h_event_t
        use (t, i, p, x)
        constructor
        · exact List.mem_of_getElem? h_get
        · simp only [hp_len, ite_true]
      exact (canonical_enumeration_spec_mono B k h_t_le_marker).1 h_x_in_t

/-- Eventually the marker is a valid witnessed candidate, and every short-output table is final.
Blueprint node `lem:marker-stabilization`. -/
theorem last_program_stabilizes_short_descriptions (B : Base) :
    ∃ n₀ : ℕ, 32 ≤ n₀ ∧ ∀ n ≥ n₀,
      validCandidate B n (markerCandidate B n) = true ∧
      ∀ k ≤ n, (stageOutputs B k (markerTick B n) : Set BitString) =
        {x | Simple B.V x k} := by
  obtain ⟨n1, h1, h1'⟩ := eventually_valid_markerCandidate B
  obtain ⟨n2, h2, h2'⟩ := eventually_stageOutputs_markerTick_eq B
  use max n1 n2
  constructor
  · omega
  · intro n hn
    constructor
    · exact h1' n (by omega)
    · exact h2' n (by omega)

/-- No short program can emit after the last short program, even with a repeated output.
Blueprint node `lem:marker-stabilization`. -/
theorem last_program_stabilizes_short_descriptions_no_later (B : Base) :
    ∃ n₀ : ℕ, 32 ≤ n₀ ∧ ∀ n ≥ n₀, ∀ t > markerTick B n, ∀ i p x,
      eventAt B t = some (t, i, p, x) → n < p.length := by
  use 32, le_refl _
  intro n hn t ht i p x h_event
  by_contra h_len
  rw [not_lt] at h_len
  have hp : p ∈ (boundedPrograms n).toFinset := by
    simp only [List.mem_toFinset, mem_boundedPrograms_iff]
    exact h_len
  have ht_eq : programTick B p = t := programTick_eq_of_eventAt B p x t i h_event
  have h_le : programTick B p ≤ markerTick B n := by
    dsimp [markerTick]
    exact Finset.le_sup hp
  omega

/-- The marker's numeric snapshot ends at its event position, with that program and its output.
Blueprint node `lem:marker-stabilization`. -/
theorem last_program_stabilizes_short_descriptions_position (B : Base) :
    ∃ n₀ : ℕ, 32 ≤ n₀ ∧ ∀ n ≥ n₀,
      (eventHistory B (markerTick B n)).length = markerPosition B n + 1 ∧
      ∃ x, eventAt B (markerTick B n) =
        some (markerTick B n, markerPosition B n, lastProgram B n, x) := by
  obtain ⟨n₀, hn₀, h⟩ := last_program_stabilizes_short_descriptions B
  use n₀, hn₀
  intro n hn
  obtain ⟨h1, _⟩ := h n hn
  have h3 := (canonical_enumeration_spec_candidate B n (markerCandidate B n)).mp h1
  obtain ⟨_, i, x, h5⟩ := h3
  have h6 : eventAt B (markerTick B n) = some (markerTick B n, i, lastProgram B n, x) := h5
  have h_pos : markerPosition B n = i := by
    dsimp [markerPosition]
    rw [h6]
    rfl
  have h_hist := canonical_enumeration_spec_position B h6
  obtain ⟨_, h_len, _⟩ := h_hist
  refine ⟨by rw [h_len, h_pos], x, ?_⟩
  rw [h_pos]
  exact h6

/-- The first string of length `n + 1` that does not occur in the list `l`, if any. -/
private def firstMissing (n : ℕ) (l : List BitString) : Option BitString :=
  (allStrings (n + 1)).find? (fun s => decide (s ∉ l))

/-- `firstMissing` is primitive recursive. -/
private lemma primrec_firstMissing :
    Primrec (fun v : ℕ × List BitString => firstMissing v.1 v.2) := by
  have hlist : Primrec (fun v : ℕ × List BitString => allStrings (v.1 + 1)) :=
    CodedFiniteDistribution.allStrings_primrec.comp (Primrec.succ.comp Primrec.fst)
  have hnotmem : Primrec₂ (fun (v : ℕ × List BitString) (s : BitString) =>
      decide (s ∉ v.2)) := by
    refine (Primrec.not.comp
      (bitString_mem_primrec.comp Primrec.snd (Primrec.snd.comp Primrec.fst))).to₂.of_eq ?_
    intro v s
    simp
  exact list_find?_primrec hlist hnotmem

/-- A duplicate-free list shorter than `2 ^ (n + 1)` misses some string of length `n + 1`,
and `firstMissing` finds one. -/
private lemma exists_firstMissing_eq_some {n : ℕ} {l : List BitString} (hnodup : l.Nodup)
    (hlen : l.length < 2 ^ (n + 1)) :
    ∃ x, firstMissing n l = some x ∧ x.length = n + 1 ∧ x ∉ l := by
  obtain ⟨x0, hx0all, hx0missing⟩ := exists_mem_allStrings_not_mem_of_length_lt hnodup hlen
  obtain ⟨x, hxfind⟩ : ∃ x, firstMissing n l = some x :=
    Option.isSome_iff_exists.mp (List.find?_isSome.mpr ⟨x0, hx0all, by simp [hx0missing]⟩)
  refine ⟨x, hxfind, ?_, ?_⟩
  · exact (mem_allStrings (n + 1) x).mp (List.mem_of_find?_eq_some hxfind)
  · simpa using List.find?_some hxfind

/-- The stage-`t` output list at scale `n` has no repetition and fewer than `2 ^ (n + 1)`
entries, since all its entries are `n`-simple. -/
private lemma stageOutputList_nodup_length_lt (B : Base) (n t : ℕ) :
    (stageOutputList B n t).Nodup ∧ (stageOutputList B n t).length < 2 ^ (n + 1) := by
  have hnodup : (stageOutputList B n t).Nodup := by
    unfold stageOutputList
    exact nodup_eraseDups_list _
  refine ⟨hnodup, ?_⟩
  have h1 : (stageOutputList B n t).length = (stageOutputs B n t).card := by
    unfold stageOutputs
    exact (List.toFinset_card_of_nodup hnodup).symm
  have hsub : ((stageOutputs B n t : Finset BitString) : Set BitString) ⊆
      {x | Simple B.V x n} :=
    fun x hx => (canonical_enumeration_spec_union B n x).mpr ⟨t, Finset.mem_coe.mp hx⟩
  obtain ⟨hfin, hcard⟩ := simple_finite_card_lt B.V n
  have h2 : (stageOutputs B n t).card ≤ simpleCount B.V n := by
    rw [← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard hsub hfin
  omega

/-- Replay the enumeration up to the emission tick of `w` and return the first string of length
`a.1 + 1` that is missing from the outputs of scale `a.1` at that tick. -/
private noncomputable def missingAtEmission (B : Base) (a : ℕ × BitString) : Part BitString :=
  (findEmission B a.2).bind fun t =>
    Part.ofOption (firstMissing a.1 (stageOutputList B a.1 t))

/-- Run `B.V` on the program `a.2` with the advice `bits a.1`, then apply
`missingAtEmission` to its output. -/
private noncomputable def simulateMissing (B : Base) (a : ℕ × BitString) : Part BitString :=
  (B.V (a.2, bits a.1)).bind fun w => missingAtEmission B (a.1, w)

/-- The decoder that, given `integerCode c ++ p`, recovers `c` and `p`, sets `n = |p| + c`,
and returns a string of length `n + 1` that the enumeration has not yet output at scale `n`
when the program `p` run on `bits n` is emitted. -/
private noncomputable def freshStringDecoder (B : Base) : Map := fun qy =>
  simulateMissing B
    ((decodeSecond qy.1).length + (decodeNat (decodeFirst qy.1)).getD 0, decodeSecond qy.1)

/-- `missingAtEmission` is partial recursive. -/
private lemma partrec_missingAtEmission (B : Base) : Partrec (missingAtEmission B) := by
  have hlist : Computable (fun a : ℕ × ℕ => stageOutputList B a.1 a.2) :=
    Computable₂.comp (canonical_enumeration_spec_outputs B).1 Computable.fst Computable.snd
  have hout : Computable (fun a : ℕ × ℕ => (a.1, stageOutputList B a.1 a.2)) :=
    Computable.fst.pair hlist
  have hs := primrec_firstMissing.to_comp.comp hout
  have he : Partrec (fun a : ℕ × BitString => findEmission B a.2) :=
    (canonical_enumeration_spec_search B).comp Computable.snd
  have hk : Computable (fun z : (ℕ × BitString) × ℕ => (z.1.1, z.2)) :=
    (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd).to_comp
  exact Partrec.bind (f := fun a : ℕ × BitString => findEmission B a.2) he
    (hs.comp hk).ofOption.to₂

/-- `freshStringDecoder` is partial recursive. -/
private lemma partrec_freshStringDecoder (B : Base) : Partrec (freshStringDecoder B) := by
  have hv : Partrec (fun a : ℕ × BitString => B.V (a.2, bits a.1)) :=
    B.optimalV.1.comp (Computable.snd.pair (bits_computable.1.comp Computable.fst))
  have hk : Computable (fun z : (ℕ × BitString) × BitString => (z.1.1, z.2)) :=
    (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd).to_comp
  have hg : Partrec (fun z : (ℕ × BitString) × BitString => missingAtEmission B (z.1.1, z.2)) :=
    (partrec_missingAtEmission B).comp hk
  have hsimulate : Partrec (simulateMissing B) :=
    (Partrec.bind (f := fun a : ℕ × BitString => B.V (a.2, bits a.1)) hv hg.to₂).of_eq
      fun _ => rfl
  have hcOf : Computable (fun q : BitString => (decodeNat (decodeFirst q)).getD 0) :=
    Computable.option_getD (bits_computable.2.comp decodeFirst_computable) (Computable.const 0)
  have hinput : Computable (fun q : BitString =>
      ((decodeSecond q).length + (decodeNat (decodeFirst q)).getD 0, decodeSecond q)) :=
    Computable₂.comp Primrec.nat_add.to_comp
      (Computable.list_length.comp decodeSecond_computable) hcOf |>.pair decodeSecond_computable
  exact hsimulate.comp (hinput.comp Computable.fst)

/-- If `p` run on `bits (|p| + c)` outputs `w` and `w` is emitted at tick `t`, then
`freshStringDecoder` maps `integerCode c ++ p` to a string of length `|p| + c + 1` which is not
among the outputs of scale `|p| + c` at tick `t`. -/
private lemma exists_mem_freshStringDecoder (B : Base) (c : ℕ) (p w : BitString) (t : ℕ)
    (hw : w ∈ B.V (p, bits (p.length + c))) (ht : t ∈ findEmission B w) :
    ∃ x, x.length = p.length + c + 1 ∧
      x ∉ (stageOutputs B (p.length + c) t : Set BitString) ∧
      x ∈ freshStringDecoder B (integerCode c ++ p, []) := by
  obtain ⟨hnodup, hlen⟩ := stageOutputList_nodup_length_lt B (p.length + c) t
  obtain ⟨x, hxfind, hxlen, hxnot⟩ := exists_firstMissing_eq_some hnodup hlen
  refine ⟨x, hxlen, ?_, ?_⟩
  · simpa only [stageOutputs, Finset.mem_coe, List.mem_toFinset] using hxnot
  · have h1 : integerCode c ++ p = pairCode (bits c) p := by
      unfold integerCode sd pairCode
      simp
    dsimp only [freshStringDecoder, simulateMissing, missingAtEmission]
    rw [h1, decodeFirst_pairCode, decodeSecond_pairCode, decodeNat_bits, Option.getD_some]
    rw [Part.mem_bind_iff]
    refine ⟨w, hw, ?_⟩
    rw [Part.mem_bind_iff]
    exact ⟨t, ht, Part.mem_ofOption.mpr hxfind⟩

/-- Exponentials dominate the linear function `4 * k + 5` from `k = 16` on. -/
theorem four_mul_add_five_le_two_pow (k : ℕ) (hk : 16 ≤ k) : 4 * k + 5 ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    rw [pow_succ]
    omega

/-- For every `b`, the cost `integerLiteralBound (b + 1) c` of coding a natural `c` is below
`c` once `c` is large enough. -/
private lemma exists_integerLiteralBound_lt (b : ℕ) :
    ∃ c₀ : ℕ, ∀ c > c₀, integerLiteralBound (b + 1) c < c := by
  use max 64 (2 * (b + 1) + 1)
  intro c hc
  have hc64 : 64 ≤ c := le_trans (le_max_left _ _) (le_of_lt hc)
  have hcb : 2 * (b + 1) + 1 < c := lt_of_le_of_lt (le_max_right _ _) hc
  set k := c / 4
  have hk16 : 16 ≤ k := by omega
  have h1 : c + 2 ≤ 4 * k + 5 := by omega
  have h3 : c + 2 ≤ 2 ^ k := le_trans h1 (four_mul_add_five_le_two_pow k hk16)
  have h4 : Nat.clog 2 (c + 2) ≤ k := (Nat.clog_le_iff_le_pow (by decide)).mpr h3
  have h5 : 2 * Nat.clog 2 (c + 2) ≤ 2 * k := Nat.mul_le_mul_left 2 h4
  have h6 : 2 * k ≤ c / 2 := by omega
  have h7 : 2 * Nat.clog 2 (c + 2) ≤ c / 2 := le_trans h5 h6
  unfold integerLiteralBound
  omega

/-- Lower bound: for large `n`, the conditional complexity of the marker program given `bits n`
is at least `n` up to an additive constant.  Otherwise a short description of the marker would
decode, via `freshStringDecoder`, to a string of length `n + 1` that is not `n`-simple. -/
private lemma exists_le_condK_lastProgram_add (B : Base) :
    ∃ cW n₀ : ℕ, 32 ≤ n₀ ∧ ∀ n ≥ n₀,
      (n : ENat) ≤ condK B.V (lastProgram B n) (bits n) + cW := by
  obtain ⟨cDec, hcDec⟩ := B.optimalV.2 _ (partrec_freshStringDecoder B)
  obtain ⟨cW, hcW⟩ := exists_integerLiteralBound_lt cDec
  obtain ⟨n0_stab, h32, hstab⟩ := last_program_stabilizes_short_descriptions B
  use cW, n0_stab
  refine ⟨h32, fun n hn => ?_⟩
  cases h_k : condK B.V (lastProgram B n) (bits n) with
  | top => exact le_top
  | coe len =>
    by_cases h_len : n ≤ len
    · have : n ≤ len + cW := by omega
      exact_mod_cast this
    · push Not at h_len
      have h_cond_le : condK B.V (lastProgram B n) (bits n) ≤ (len : ENat) := le_of_eq h_k
      obtain ⟨p, hp_len, hp_prod⟩ :=
        (condK_le_iff B.V (lastProgram B n) (bits n) len).mp h_cond_le
      have hp_len' : p.length ≤ len := hp_len
      set c := n - p.length with hc_def
      have hp_len_lt : p.length < n := by omega
      have hn_eq : p.length + c = n := by omega
      have h_valid : validCandidate B n (markerCandidate B n) = true := (hstab n hn).1
      have hevent := (canonical_enumeration_spec_candidate B n (markerCandidate B n)).mp h_valid
      have hsearch : markerTick B n ∈ findEmission B (lastProgram B n) :=
        (canonical_enumeration_spec_search_eq B _ _).mpr hevent.2
      have hw : lastProgram B n ∈ B.V (p, bits (p.length + c)) := by
        rw [hn_eq]
        exact hp_prod
      obtain ⟨x, hx_len, hx_not_mem, hx_dec⟩ :=
        exists_mem_freshStringDecoder B c p (lastProgram B n) (markerTick B n) hw hsearch
      have hx_not_simple : ¬ Simple B.V x n := by
        intro hsimp
        have hx_mem : x ∈ {x | Simple B.V x n} := hsimp
        rw [← (hstab n hn).2 n le_rfl] at hx_mem
        rw [hn_eq] at hx_not_mem
        exact hx_not_mem hx_mem
      have hx_plainK : (n : ENat) < plainK B.V x := by
        have h_simple_iff : Simple B.V x n ↔ plainK B.V x ≤ n := Iff.rfl
        rw [h_simple_iff] at hx_not_simple
        push Not at hx_not_simple
        exact hx_not_simple
      have h_dec_K : condK (freshStringDecoder B) x [] ≤ ((integerCode c ++ p).length : ENat) :=
        (condK_le_iff _ x [] (integerCode c ++ p).length).mpr ⟨integerCode c ++ p, le_rfl, hx_dec⟩
      have h_plainK_le : plainK B.V x ≤ ((integerCode c ++ p).length + cDec : ENat) := by
        calc plainK B.V x ≤ condK (freshStringDecoder B) x [] + (cDec : ENat) := hcDec x []
          _ ≤ ((integerCode c ++ p).length : ENat) + (cDec : ENat) := by gcongr
          _ = ((integerCode c ++ p).length + cDec : ENat) := rfl
      have h1 : plainK B.V x ≤ (((integerCode c).length + p.length + cDec : ℕ) : ENat) := by
        have h_len_sum : (integerCode c ++ p).length = (integerCode c).length + p.length := by
          simp
        rw [h_len_sum] at h_plainK_le
        exact h_plainK_le
      have h2 : (((integerCode c).length + p.length + cDec : ℕ) : ENat) ≤
          ((integerLiteralBound (cDec + 1) c + p.length : ℕ) : ENat) := by
        have h_int_le := length_integerCode_le c
        have h_int_bound : (integerCode c).length + cDec ≤ integerLiteralBound (cDec + 1) c := by
          unfold integerLiteralBound
          omega
        exact_mod_cast (by omega)
      have h_bound : (n : ENat) < ((integerLiteralBound (cDec + 1) c + p.length : ℕ) : ENat) :=
        calc (n : ENat) < plainK B.V x := hx_plainK
          _ ≤ (((integerCode c).length + p.length + cDec : ℕ) : ENat) := h1
          _ ≤ ((integerLiteralBound (cDec + 1) c + p.length : ℕ) : ENat) := h2
      have h_c_bound : c < integerLiteralBound (cDec + 1) c := by
        have h_bound_nat : n < integerLiteralBound (cDec + 1) c + p.length := by
          exact_mod_cast h_bound
        omega
      have h_cW : c ≤ cW := by
        by_contra h_gt
        push Not at h_gt
        have h_def := hcW c h_gt
        omega
      have h_final : n ≤ len + cW := by omega
      exact_mod_cast h_final

/-- The marker program at scale `n` has length at most `n`, and its conditional complexity given
`bits n` is `n` up to an additive constant. -/
theorem last_program_conditional_complexity (B : Base) :
    ∃ cW n₀ : ℕ, 32 ≤ n₀ ∧ ∀ n ≥ n₀,
      (lastProgram B n).length ≤ n ∧
      (n : ENat) ≤ condK B.V (lastProgram B n) (bits n) + cW ∧
      condK B.V (lastProgram B n) (bits n) ≤ (n : ENat) + cW := by
  obtain ⟨n1, hn1, hstab⟩ := last_program_stabilizes_short_descriptions B
  obtain ⟨c2, hn2⟩ := plainK_le_length B.V B.optimalV
  obtain ⟨c3, hn3⟩ := condK_le_plainK B.V B.optimalV
  obtain ⟨cLower, nLower, hnLower, hLower⟩ := exists_le_condK_lastProgram_add B
  use max cLower (c2 + c3), max n1 (max 32 nLower)
  have h32_max : 32 ≤ max n1 (max 32 nLower) := le_trans hn1 (le_max_left _ _)
  refine ⟨h32_max, fun n hn => ?_⟩
  have hn_n1 : n1 ≤ n := le_trans (le_max_left _ _) hn
  have hn_nLower : nLower ≤ n :=
    le_trans (le_max_right 32 nLower) (le_trans (le_max_right n1 _) hn)
  have hlen : (lastProgram B n).length ≤ n :=
    ((canonical_enumeration_spec_candidate B n (markerCandidate B n)).mp (hstab n hn_n1).1).1
  refine ⟨hlen, ?_, ?_⟩
  · have h_low := hLower n hn_nLower
    exact le_trans h_low (add_le_add le_rfl (by exact_mod_cast le_max_left cLower (c2 + c3)))
  · have h_enat : ((lastProgram B n).length : ENat) ≤ (n : ENat) := by exact_mod_cast hlen
    calc condK B.V (lastProgram B n) (bits n) ≤ plainK B.V (lastProgram B n) + c3 := hn3 _ _
      _ ≤ (lastProgram B n).length + c2 + c3 := add_le_add (hn2 _) le_rfl
      _ ≤ n + c2 + c3 := by gcongr
      _ = n + (c2 + c3) := by rw [add_assoc]
      _ ≤ n + max cLower (c2 + c3) :=
        add_le_add le_rfl (by exact_mod_cast le_max_right cLower (c2 + c3))

end Kolmogorov.Milovanov
