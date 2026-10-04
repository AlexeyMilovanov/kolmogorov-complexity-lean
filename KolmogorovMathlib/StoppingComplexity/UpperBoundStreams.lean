/-
Copyright (c) 2024 Author Name. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Author Name
-/
import KolmogorovMathlib.StoppingComplexity.Allocator
import KolmogorovMathlib.StoppingComplexity.Universal

/-!
# Effective approximations behind the level-colouring upper bound

Upstream helpers of `KolmogorovMathlib.StoppingComplexity.UpperBound` (blueprint 03 §9, Lemma U1).
The universal stopping probability `M_stop(z)` is approximated from below by the dyadic rationals
`univStopProbNum t z / 2^t`, where the stage numerator `univStopProbNum t z` sums `2^{t - |p|}`
over the random prefixes `p` of length at most `t` accepted by the bounded universal search within
`t` steps. The numerator is primitive recursive, the approximations exhaust `M_stop(z)`, and a
strict dyadic threshold `2^{-n} < M_stop(z)` is detected at a finite stage by the natural-number
test `2^t < univStopProbNum t z · 2^n`; this is what makes the level sets `T_n` uniformly c.e.
A request stream that requests each string at most once carries, at every stage, either no mass or
the weight of that single request at each string (the level streams of U1 are of this kind).
Along any request stream the stage tables of the allocator are finite maps, computable uniformly in
a computable family of streams, and "the atom `j` is allocated to `z` at some stage" is c.e.; when
all requests live on one depth-`n` grid the precision stays `n` and atom lists only grow.
-/

namespace Kolmogorov

open scoped ENNReal

/-! ### The dyadic lower approximation of `M_stop` -/

/-- The stage-`t` numerator of the lower approximation of `M_stop(z)` over the common denominator
`2^t`: the sum of `2^{t - |p|}` over the random prefixes `p` of length `≤ t` accepted by the bounded
universal search within `t` steps. Blueprint 03 Lemma U1 (lower approximation of `M_stop`). -/
def univStopProbNum (t : ℕ) (z : BitString) : ℕ :=
  (((boundedPrograms t).filter fun p => univWitnessWithin t z p).map
    fun p => 2 ^ (t - p.length)).sum

/-- The stage numerator is primitive recursive in the stage and the input.
Blueprint 03 Lemma U1 (lower approximation of `M_stop`). -/
theorem primrec_univStopProbNum :
    Primrec fun a : ℕ × BitString => univStopProbNum a.1 a.2 := by
  have hacc : Primrec₂ fun (a : ℕ × BitString) (p : BitString) => univWitnessWithin a.1 a.2 p :=
    (primrec_univWitnessWithin.comp (Primrec.pair (Primrec.fst.comp Primrec.fst)
      (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd))).of_eq fun _ => rfl
  have hfilt : Primrec fun a : ℕ × BitString =>
      (boundedPrograms a.1).filter fun p => univWitnessWithin a.1 a.2 p :=
    Primrec.list_filter (primrec_boundedPrograms.comp Primrec.fst) hacc
  have hterm : Primrec₂ fun (a : ℕ × BitString) (p : BitString) => 2 ^ (a.1 - p.length) :=
    (nat_pow_primrec₂.comp (Primrec.const 2) (Primrec.nat_sub.comp
      (Primrec.fst.comp Primrec.fst) (Primrec.list_length.comp Primrec.snd))).of_eq fun _ => rfl
  exact (Primrec.list_foldr (Primrec.list_map hfilt hterm) (Primrec.const 0)
    (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun _ => rfl

/-- The stage approximation `univStopProbNum t z / 2^t` is the sum of the weights `2^{-|p|}` over
the stage-`t` accepted random prefixes (the filtered list has no duplicates).
Blueprint 03 Lemma U1 (lower approximation of `M_stop`). -/
theorem univStopProbNum_div_eq_sum (t : ℕ) (z : BitString) :
    (univStopProbNum t z : ℝ) / 2 ^ t =
      ∑ p ∈ ((boundedPrograms t).filter fun p => univWitnessWithin t z p).toFinset,
        (1 / 2 : ℝ) ^ p.length := by
  rw [List.sum_toFinset _ ((boundedPrograms_nodup t).filter _), univStopProbNum,
    Nat.cast_list_sum, List.map_map, div_eq_iff (by positivity), ← List.sum_map_mul_right]
  refine congrArg List.sum (List.map_congr_left fun p hp => ?_)
  have hlen : p.length ≤ t := (mem_boundedPrograms_iff p t).1 (List.mem_filter.1 hp).1
  simp only [Function.comp_apply, Nat.cast_pow, Nat.cast_ofNat]
  rw [pow_sub₀ (2 : ℝ) two_ne_zero hlen, one_div_pow, div_mul_eq_mul_div, one_mul,
    div_eq_mul_inv]

/-- The stage approximation read in `ℝ≥0∞` is the sum of the cylinder weights `2^{-|p|}` of the
stage-`t` accepted random prefixes. Blueprint 03 Lemma U1 (lower approximation of `M_stop`). -/
private theorem ofReal_univStopProbNum_div (t : ℕ) (z : BitString) :
    ENNReal.ofReal ((univStopProbNum t z : ℝ) / 2 ^ t) =
      ∑ p ∈ ((boundedPrograms t).filter fun p => univWitnessWithin t z p).toFinset,
        (2 : ℝ≥0∞)⁻¹ ^ p.length := by
  rw [univStopProbNum_div_eq_sum, ENNReal.ofReal_sum_of_nonneg fun p _ => by positivity]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [ENNReal.ofReal_pow (by norm_num), one_div, ENNReal.ofReal_inv_of_pos (by norm_num),
    ENNReal.ofReal_ofNat]

/-- `M_stop(z)` is the supremum of its stage approximations: every stage sums the weights of
distinct witnesses of the universal machine, and every finite set of witnesses is accepted at a
late enough stage. Blueprint 03 Lemma U1 (lower approximation of `M_stop`) with Lemma M4. -/
theorem univStopProb_eq_iSup_univStopProbNum (z : BitString) :
    univStopProb z = ⨆ t, ENNReal.ofReal ((univStopProbNum t z : ℝ) / 2 ^ t) := by
  classical
  rw [univStopProb, stopProb_eq_tsum]
  simp_rw [ofReal_univStopProbNum_div]
  apply le_antisymm
  · rw [ENNReal.tsum_eq_iSup_sum]
    refine iSup_le fun s => ?_
    choose tW htW using fun p : {p : BitString // Witness univStopping z p} =>
      (univWitness_iff_exists_univWitnessWithin z p.1).1 p.2
    refine le_iSup_of_le (s.sup fun p => max (tW p) (p : BitString).length) ?_
    calc ∑ p ∈ s, (2 : ℝ≥0∞)⁻¹ ^ (p : BitString).length
        = ∑ p ∈ s.image Subtype.val, (2 : ℝ≥0∞)⁻¹ ^ p.length :=
          (Finset.sum_image (f := fun p : BitString => (2 : ℝ≥0∞)⁻¹ ^ p.length)
            fun x _ y _ h => Subtype.ext h).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset fun p hp => ?_
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hp
    have hle := Finset.le_sup (f := fun p => max (tW p) (p : BitString).length) hq
    rw [List.mem_toFinset, List.mem_filter, mem_boundedPrograms_iff]
    exact ⟨le_trans (le_max_right _ _) hle,
      univWitnessWithin_mono (le_trans (le_max_left _ _) hle) (htW q)⟩
  · refine iSup_le fun t => ?_
    have hW : ∀ p ∈ ((boundedPrograms t).filter fun p => univWitnessWithin t z p).toFinset,
        Witness univStopping z p := fun p hp => by
      rw [List.mem_toFinset, List.mem_filter] at hp
      exact (univWitness_iff_exists_univWitnessWithin z p).2 ⟨t, hp.2⟩
    rw [← Finset.sum_subtype_of_mem (fun p : BitString => (2 : ℝ≥0∞)⁻¹ ^ p.length) hW]
    exact ENNReal.sum_le_tsum _

/-- A strict dyadic threshold is detected at a finite stage: `2^{-n} < M_stop(z)` iff some stage
`t` has `2^t < univStopProbNum t z · 2^n`, a decidable test in natural numbers.
Blueprint 03 Lemma U1 (strict thresholds are detected from a lower approximation). -/
theorem two_pow_neg_lt_univStopProb_iff (n : ℕ) (z : BitString) :
    (2 : ℝ≥0∞)⁻¹ ^ n < univStopProb z ↔ ∃ t, 2 ^ t < univStopProbNum t z * 2 ^ n := by
  have h2 : (2 : ℝ≥0∞)⁻¹ ^ n = ENNReal.ofReal ((1 / 2 : ℝ) ^ n) := by
    rw [ENNReal.ofReal_pow (by norm_num), one_div, ENNReal.ofReal_inv_of_pos (by norm_num),
      ENNReal.ofReal_ofNat]
  rw [univStopProb_eq_iSup_univStopProbNum, h2, lt_iSup_iff]
  refine exists_congr fun t => ?_
  have hreal : (1 / 2 : ℝ) ^ n < (univStopProbNum t z : ℝ) / 2 ^ t ↔
      2 ^ t < univStopProbNum t z * 2 ^ n := by
    rw [one_div_pow, lt_div_iff₀ (by positivity), one_div_mul_eq_div,
      div_lt_iff₀ (by positivity)]
    norm_cast
  rw [ENNReal.ofReal_lt_ofReal_iff', hreal]
  exact ⟨And.left, fun h => ⟨h, lt_trans (by positivity) (hreal.2 h)⟩⟩

/-! ### Request streams without repeated strings -/

/-- A request stream that requests each string at most once puts on a string, at every stage,
either no mass or exactly the weight of the one earlier request at that string.
Blueprint 03 Lemma U1 (enumeration without repetitions). -/
theorem streamStageMass_eq_zero_or_weight {ρ : RequestStream}
    (huniq : ∀ s s' r r', ρ s = some r → ρ s' = some r' → r.1 = r'.1 → s = s')
    (s : ℕ) (z : BitString) :
    streamStageMass ρ s z = 0 ∨
      ∃ s' < s, ∃ r, ρ s' = some r ∧ r.1 = z ∧ streamStageMass ρ s z = r.weight := by
  induction s with
  | zero => exact Or.inl (by simp [streamStageMass])
  | succ s ih =>
    have hstep : streamStageMass ρ (s + 1) z = streamStageMass ρ s z +
        (((ρ s).toList.filter fun r => decide (r.1 = z)).map DyadicRequest.weight).sum := by
      simp only [streamStageMass, List.range_succ, List.filterMap_append, List.filter_append,
        List.map_append, List.sum_append]
      cases h : ρ s <;> simp [h]
    rcases hρ : ρ s with _ | r
    · rw [hρ] at hstep
      simp only [Option.toList_none, List.filter_nil, List.map_nil, List.sum_nil,
        add_zero] at hstep
      rcases ih with h0 | ⟨s', hs', r', h1, h2, h3⟩
      · exact Or.inl (hstep.trans h0)
      · exact Or.inr ⟨s', by omega, r', h1, h2, hstep.trans h3⟩
    · by_cases hrz : r.1 = z
      · have h0 : streamStageMass ρ s z = 0 := by
          rcases ih with h0 | ⟨s', hs', r', h1, h2, -⟩
          · exact h0
          · exact absurd (huniq s' s r' r h1 hρ (h2.trans hrz.symm)) (by omega)
        refine Or.inr ⟨s, by omega, r, hρ, hrz, ?_⟩
        rw [hstep, h0, hρ]
        simp [hrz]
      · rw [hρ] at hstep
        simp only [Option.toList_some, List.filter_cons, hrz, decide_false, Bool.false_eq_true,
          ite_false, List.filter_nil, List.map_nil, List.sum_nil, add_zero] at hstep
        rcases ih with h0 | ⟨s', hs', r', h1, h2, h3⟩
        · exact Or.inl (hstep.trans h0)
        · exact Or.inr ⟨s', by omega, r', h1, h2, hstep.trans h3⟩

/-! ### The allocator along a request stream -/

/-- Along any request stream the rows of the stage table are keyed by pairwise distinct strings:
refinement rewrites only the atom lists, and one step replaces the row of the requested string by
a single new row. Blueprint 03 Lemma A3 (the stage table is a finite map). -/
theorem allocRun_keys_nodup (ρ : RequestStream) (s : ℕ) :
    ((allocRun ρ s).table.map Prod.fst).Nodup := by
  induction s with
  | zero => simp [allocRun]
  | succ s ih =>
    rw [allocRun]
    cases ρ s with
    | none => exact ih
    | some r =>
      have hkeys : (refineState (allocRun ρ s) (requestPrec (allocRun ρ s).prec r)).table.map
          Prod.fst = (allocRun ρ s).table.map Prod.fst := by
        simp [refineState, List.map_map, Function.comp_def]
      simp only [allocStep, AllocState.setAtoms, List.map_cons, List.nodup_cons]
      refine ⟨by simp, ?_⟩
      exact (hkeys ▸ ih).sublist (List.filter_sublist.map _)

/-- In a table keyed by distinct strings, the strings whose row lists the atom `j` are exactly the
strings `z` with `j ∈ A_z`. Blueprint 03 Lemma U1 (reading a colour class off the stage table). -/
theorem mem_map_fst_filter_iff_mem_atoms {st : AllocState} (hnd : (st.table.map Prod.fst).Nodup)
    (z : BitString) (j : ℕ) :
    z ∈ (st.table.filter fun e => decide (j ∈ e.2)).map Prod.fst ↔ j ∈ st.atoms z := by
  obtain ⟨L, t⟩ := st
  simp only [AllocState.atoms] at hnd ⊢
  induction t with
  | nil => simp
  | cons a t ih =>
    obtain ⟨k, b⟩ := a
    rw [List.map_cons, List.nodup_cons] at hnd
    by_cases hz : z = k
    · subst hz
      simp only [List.filter_cons, List.lookup_cons, beq_self_eq_true, Option.getD_some]
      constructor
      · intro h
        by_cases hj : j ∈ b
        · exact hj
        · simp only [hj, decide_false, Bool.false_eq_true, ite_false] at h
          obtain ⟨e, he, hek⟩ := List.mem_map.mp h
          exact absurd (List.mem_map.mpr ⟨e, (List.mem_filter.mp he).1, hek⟩) hnd.1
      · intro hj
        simp [hj]
    · have hne : (z == k) = false := beq_eq_false_iff_ne.mpr hz
      rw [List.lookup_cons, hne, ← ih hnd.2]
      by_cases hj : j ∈ b <;> simp [hj, hz]

/-- Along a request stream whose requests all live on the depth-`n` grid (`L = n`), every stage
table either is still the empty table at precision `0` or has precision exactly `n`.
Blueprint 03 Lemma U1 (the allocator runs on the fixed depth-`n` grid). -/
theorem allocRun_prec_eq_or_empty {ρ : RequestStream} {n : ℕ}
    (hρ : ∀ s r, ρ s = some r → r.2.2 = n) (s : ℕ) :
    (allocRun ρ s).prec = n ∨ ((allocRun ρ s).prec = 0 ∧ (allocRun ρ s).table = []) := by
  induction s with
  | zero => exact Or.inr ⟨rfl, rfl⟩
  | succ s ih =>
    rw [allocRun]
    cases h : ρ s with
    | none => exact ih
    | some r =>
      left
      simp only [allocStep, AllocState.setAtoms, refineState, requestPrec, hρ s r h]
      rcases ih with h' | ⟨h', -⟩ <;> rw [h'] <;> simp

/-- One allocation step at the grid precision keeps every allocated atom: when the state already
has the precision `L` of the request, refinement is the identity and the step only appends atoms
to the requested string. Blueprint 03 Lemma A2 (atom lists only grow on a fixed grid). -/
theorem mem_allocStep_atoms {st : AllocState} {r : DyadicRequest} (hprec : st.prec = r.2.2)
    {z : BitString} {j : ℕ} (hj : j ∈ st.atoms z) : j ∈ (allocStep st r).atoms z := by
  have href : (refineState st (requestPrec st.prec r)).atoms z = st.atoms z := by
    rw [refineState_atoms]
    simp [requestPrec, hprec]
  by_cases hz : z = r.1
  · subst hz
    have hset : ∀ (st' : AllocState) (l : List ℕ), (st'.setAtoms r.1 l).atoms r.1 = l :=
      fun st' l => by simp [AllocState.setAtoms, AllocState.atoms]
    simp only [allocStep, hset, href, List.mem_append]
    exact Or.inl hj
  · rw [allocStep_atoms_of_ne st r hz, href]
    exact hj

/-- Along a request stream on the depth-`n` grid the atom lists only grow: an atom allocated to
`z` at stage `s` is still allocated to `z` at every later stage.
Blueprint 03 Lemma U1 (colours are never withdrawn). -/
theorem mem_allocRun_atoms_of_le {ρ : RequestStream} {n : ℕ}
    (hρ : ∀ s r, ρ s = some r → r.2.2 = n) {s s' : ℕ} (hss' : s ≤ s') {z : BitString} {j : ℕ}
    (hj : j ∈ (allocRun ρ s).atoms z) : j ∈ (allocRun ρ s').atoms z := by
  induction s', hss' using Nat.le_induction with
  | base => exact hj
  | succ m _ ih =>
    rw [allocRun]
    cases h : ρ m with
    | none => exact ih
    | some r =>
      refine mem_allocStep_atoms ?_ ih
      rcases allocRun_prec_eq_or_empty hρ m with hp | ⟨-, ht⟩
      · rw [hp, hρ m r h]
      · simp [AllocState.atoms, ht] at ih

/-- The stage tables of the allocator are computable uniformly along a computable family of
request streams (the recursion of `allocRun_computable` with a parameter).
Blueprint 03 Lemma A3 (uniform effective allocation). -/
theorem allocRun_computable_family {α : Type} [Primcodable α] {ρ : α → RequestStream}
    (hρ : Computable fun a : α × ℕ => ρ a.1 a.2) :
    Computable fun a : α × ℕ => allocRun (ρ a.1) a.2 := by
  have hstep : Computable₂ fun (a : α × ℕ) (p : ℕ × AllocState) =>
      Option.casesOn (motive := fun _ => AllocState) (ρ a.1 p.1) p.2 fun r => allocStep p.2 r :=
    (Computable.option_casesOn
      (hρ.comp (Computable.pair (Computable.fst.comp Computable.fst)
        (Computable.fst.comp Computable.snd)))
      (Computable.snd.comp Computable.snd)
      (allocStep_computable.comp (Computable.pair
        (Computable.snd.comp (Computable.snd.comp Computable.fst)) Computable.snd)).to₂).to₂
  refine (Computable.nat_rec Computable.snd (Computable.const (⟨0, []⟩ : AllocState))
    hstep).of_eq fun a => ?_
  obtain ⟨a, s⟩ := a
  induction s with
  | zero => rfl
  | succ s ih =>
    simp only at ih ⊢
    rw [ih]
    simp only [allocRun]
    cases ρ a s <;> rfl

/-- Every request of a stream contributes its weight to the cumulative table one stage later:
`k / 2^L ≤ M_{s+1}(z)` when stage `s` requests `(z, k, L)`. Blueprint 01 F3 (F3-STREAM). -/
theorem weight_le_streamStageMass_succ {ρ : RequestStream} {s : ℕ} {r : DyadicRequest}
    (hs : ρ s = some r) : r.weight ≤ streamStageMass ρ (s + 1) r.1 := by
  have h : streamStageMass ρ (s + 1) r.1 = streamStageMass ρ s r.1 + r.weight := by
    simp only [streamStageMass, List.range_succ, List.filterMap_append, List.filter_append,
      List.map_append, List.sum_append]
    simp [hs]
  rw [h]
  linarith [streamStageMass_nonneg ρ s r.1]

/-- Membership of an element in a list is a primitive recursive test.
Blueprint 03 Lemma A3 (reading the stage table is effective). -/
theorem primrec_decide_mem_list {β : Type} [Primcodable β] [DecidableEq β] :
    Primrec₂ fun (b : β) (l : List β) => decide (b ∈ l) :=
  (list_any_primrec (f := fun x : β × List β => x.2) (p := fun x i => decide (i = x.1))
    Primrec.snd (PrimrecRel.comp Primrec.eq Primrec.snd
      (Primrec.fst.comp Primrec.fst)).decide.to₂).of_eq fun x => by
    rw [Bool.eq_iff_iff, List.any_eq_true, decide_eq_true_iff]
    simp

/-- The atom list `A_z` of a state is primitive recursive in the state and the string.
Blueprint 03 Lemma A3 (reading the stage table is effective). -/
theorem primrec_allocState_atoms : Primrec₂ AllocState.atoms := by
  have htab : Primrec AllocState.table :=
    (Primrec.snd.comp (Primrec.of_equiv (e := AllocState.equivProd))).of_eq fun _ => rfl
  have h : Primrec fun p : AllocState × BitString =>
      (@List.lookup _ _ instBEqOfDecidableEq p.2 p.1.table).getD [] :=
    Primrec.option_getD.comp (Primrec.listLookup.comp Primrec.snd (htab.comp Primrec.fst))
      (Primrec.const [])
  refine h.of_eq fun p => ?_
  simp only [AllocState.atoms]
  congr
  exact lawful_beq_subsingleton _ _

/-- Along a computable family of request streams, "the atom `j` is allocated to `z` at some stage"
is computably enumerable in `(a, j, z)`: it is the projection of the computable stage test
`j ∈ A_z(s)`. Blueprint 03 Lemma U1 (the colour classes are uniformly c.e.). -/
theorem isRE_exists_mem_allocRun_atoms {α : Type} [Primcodable α] {ρ : α → RequestStream}
    (hρ : Computable fun a : α × ℕ => ρ a.1 a.2) :
    IsRE fun a : α × ℕ × BitString => ∃ s, a.2.1 ∈ (allocRun (ρ a.1) s).atoms a.2.2 := by
  have hrun : Computable fun p : (α × ℕ × BitString) × ℕ => allocRun (ρ p.1.1) p.2 :=
    ((allocRun_computable_family hρ).comp (Computable.pair
      (Computable.fst.comp Computable.fst) Computable.snd)).of_eq fun _ => rfl
  have hatoms : Computable fun p : (α × ℕ × BitString) × ℕ =>
      (allocRun (ρ p.1.1) p.2).atoms p.1.2.2 :=
    (primrec_allocState_atoms.to_comp.comp hrun
      (Computable.snd.comp (Computable.snd.comp Computable.fst))).of_eq fun _ => rfl
  have hcheck : Computable fun p : (α × ℕ × BitString) × ℕ =>
      decide (p.1.2.1 ∈ (allocRun (ρ p.1.1) p.2).atoms p.1.2.2) :=
    (primrec_decide_mem_list.to_comp.comp
      (Computable.fst.comp (Computable.snd.comp Computable.fst)) hatoms).of_eq fun _ => rfl
  have hRE : IsRE fun p : (α × ℕ × BitString) × ℕ =>
      p.1.2.1 ∈ (allocRun (ρ p.1.1) p.2).atoms p.1.2.2 :=
    isRE_of_computable_bool _ _ (fun _ => decide_eq_true_iff) hcheck
  exact IsRE.exists_encodable
    (R := fun (a : α × ℕ × BitString) (s : ℕ) => a.2.1 ∈ (allocRun (ρ a.1) s).atoms a.2.2) hRE

end Kolmogorov
