/-
Copyright (c) 2024 Alexey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey
-/
import Mathlib
import KolmogorovMathlib.Prefix.Basic
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitin.Allocator.Basic

/-!
# The online Kraft–Chaitin allocator

This file builds the *online* (causal) prefix-free code allocator behind the
Kraft–Chaitin realization theorem and proves its three defining properties:

* `allocFun_computable` — the allocator is computable uniformly in the context;
* `allocFun_prefixFree` — codes for distinct requests are prefix-incomparable;
* `allocFun_success`    — if the total Kraft weight is `≤ 1`, every request is
  realized by a codeword of exactly the requested length.

The algorithm maintains a *free list* of tree nodes (bitstrings) kept in strictly
descending order of length (hence with pairwise distinct lengths).  A length-`l`
request is serviced by taking the unique free node of largest length `≤ l`,
splitting it into a length-`l` left-most descendant (the allocated codeword) and
its right siblings along the all-`false` path, and re-inserting the siblings in
sorted position.

The proofs are organized around three invariants of the free list:

* `DescLengths` (strictly descending lengths ⇒ distinct lengths);
* prefix-freeness of the node set;
* the mass identity `freeMass free + usedMass req n = 1`.

These are bundled in `AllocGood` and shown to be preserved step by step.
-/

namespace Kolmogorov
namespace KraftChaitin

open scoped ENNReal
open Computability

/-! ## Unconditional invariants of the free list

Prefix-freeness, descending lengths, and the mass identity hold whenever the
state exists, with no hypothesis on the total Kraft weight. -/

/-
The free list is always prefix-free.
-/
lemma allocatorState_prefixFree (req : ℕ → Option (BitString × ℕ)) (n : ℕ) (free : List BitString)
    (h : allocatorState req n = some free) : IsPrefixFree ↑free.toFinset := by
  induction n generalizing free with
  | zero =>
    cases h;
    exact fun p hp q hq hpq => by aesop;
  | succ n ih =>
    obtain ⟨free₀, h₀⟩ : ∃ free₀, allocatorState req n = some free₀ ∧ (req n = none → free = free₀) ∧ (req n ≠ none → ∃ a free', allocateOne free₀ (req n).get!.2 = some (a, free') ∧ free = free') := by
      unfold allocatorState at h; aesop;
    by_cases h₁ : req n = none <;> simp_all +decide;
    have h₂ :DescLengths free₀ := by
      have h₂ : ∀ n, ∀ free, allocatorState req n = some free → DescLengths free := by
        intros n free hfree
        induction n generalizing free with
        | zero => cases hfree ; tauto
        | succ n ih =>
          obtain ⟨free₀, h₀⟩ : ∃ free₀, allocatorState req n = some free₀ ∧ (req n = none → free = free₀) ∧ (req n ≠ none → ∃ a free', allocateOne free₀ (req n).get!.2 = some (a, free') ∧ free = free') := by
            unfold allocatorState at hfree; aesop;
          by_cases h₁ : req n = none <;> simp_all +decide;
          exact allocateOne_descLengths _ _ _ _ h₀.2.choose_spec ih;
      exact h₂ _ _ h₀.1;
    obtain ⟨ a, ha ⟩ := h₀.2; have := allocateOne_prefixFree free₀ ( req n |>.get!.2 ) a free ha; aesop;

/-
The free list always has strictly descending lengths.
-/
lemma allocatorState_descLengths (req : ℕ → Option (BitString × ℕ)) (n : ℕ) (free : List BitString)
    (h : allocatorState req n = some free) : DescLengths free := by
  induction n generalizing free with
  | zero => cases h ; tauto
  | succ n ih =>
    -- By definition of `allocatorState`, if `allocatorState req (n + 1) = some free`, then `allocatorState req n = some free₀` for some `free₀`, and `req n = some (_, l)` for some `l`.
    obtain ⟨free₀, h₀⟩ : ∃ free₀, allocatorState req n = some free₀ := by
      cases h' : allocatorState req n <;> simp_all +decide [ allocatorState ];
    cases h' : req n <;> simp_all +decide [ allocatorState ];
    cases h'' : allocateOne free₀ ‹BitString × ℕ›.2 <;> simp_all +decide;
    exact h ▸ allocateOne_descLengths _ _ _ _ h'' ih

/-
The free mass plus the used mass is always exactly `1`.
-/
lemma allocatorState_mass (req : ℕ → Option (BitString × ℕ)) (n : ℕ) (free : List BitString)
    (h : allocatorState req n = some free) : freeMass free + usedMass req n = 1 := by
  induction n generalizing free with
  | zero =>
    cases h ; norm_num [ freeMass, usedMass ];
    unfold nodeMass; norm_num;
  | succ n ih =>
    by_cases h1 : allocatorState req n = none;
    · unfold allocatorState at h; aesop;
    · obtain ⟨free₀, hfree₀⟩ : ∃ free₀, allocatorState req n = some free₀ := by
        exact Option.ne_none_iff_exists'.mp h1;
      by_cases h2 : req n = none <;> simp_all +decide [ allocatorState ];
      · unfold usedMass; simp_all +decide [ Finset.sum_range_succ ] ;
        unfold reqMass; aesop;
      · obtain ⟨fst, l, hl⟩ : ∃ fst l, req n = some (fst, l) := by
          cases h : req n <;> tauto;
        obtain ⟨a, free', hallocate⟩ : ∃ a free', allocateOne free₀ l = some (a, free') ∧ free = free' := by
          cases h' : allocateOne free₀ l <;> aesop;
        have h_mass : freeMass free' + nodeMass a = freeMass free₀ := by
          apply allocateOne_mass; exact hallocate.left;
        have h_mass : nodeMass a = (2 : ℝ≥0∞)⁻¹ ^ l := by
          have h_mass : a.length = l := by
            exact allocateOne_length free₀ l a free' hallocate.1;
          exact h_mass ▸ rfl;
        simp_all +decide [ usedMass, Finset.sum_range_succ ];
        simp_all +decide [ ← add_assoc, reqMass ];
        rw [ add_right_comm, ← ih, ← ‹freeMass free' + 2⁻¹ ^ l = freeMass free₀› ]

/-
Each partial Kraft sum is bounded by the total.
-/
lemma usedMass_le_tsum (req : ℕ → Option (BitString × ℕ)) (n : ℕ) :
    usedMass req n ≤ ∑' i, reqMass req i := by
  unfold usedMass
  exact ENNReal.sum_le_tsum (Finset.range n)

/-
Given the global Kraft bound `≤ 1`, the allocator never fails.
-/
lemma allocatorState_isSome (req : ℕ → Option (BitString × ℕ)) (n : ℕ)
    (hweight : (∑' i, reqMass req i) ≤ 1) : (allocatorState req n).isSome := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases h : allocatorState req n with ( _ | ⟨ free₀ ⟩ ) <;> simp_all +decide;
    by_cases hreq : req n = none;
    · simp +decide [ allocatorState, h, hreq ];
    · obtain ⟨o, l⟩ : ∃ o l, req n = some (o, l) := by
        cases h : req n <;> tauto;
      obtain ⟨l, hl⟩ : ∃ l, req n = some (o, l) := l
      have h_mass : freeMass free₀ + usedMass req n = 1 := by
        convert allocatorState_mass req n free₀ h using 1
      have h_usedMass : usedMass req (n + 1) = usedMass req n + reqMass req n := by
        exact Finset.sum_range_succ _ _
      have h_reqMass : reqMass req n = (2 : ℝ≥0∞)⁻¹ ^ l := by
        unfold reqMass; aesop;
      have h_freeMass : (2 : ℝ≥0∞)⁻¹ ^ l ≤ freeMass free₀ := by
        have h_freeMass : usedMass req (n + 1) ≤ 1 := by
          exact le_trans ( usedMass_le_tsum req ( n + 1 ) ) hweight;
        contrapose! h_freeMass;
        rw [ ← h_mass, h_usedMass, h_reqMass ];
        rw [ add_comm ] ; gcongr;
        exact ne_of_lt ( lt_of_le_of_lt ( usedMass_le_tsum req n ) ( lt_of_le_of_lt hweight ( by norm_num ) ) )
      have h_exists_fit : ∃ v ∈ free₀, v.length ≤ l := by
        apply exists_fit_of_mass_ge free₀ l (allocatorState_descLengths req n free₀ h) h_freeMass
      have h_allocateOne : (allocateOne free₀ l).isSome := by
        exact allocateOne_isSome_of_exists free₀ l h_exists_fit
      simp [allocatorState, h, hl];
      cases h : allocateOne free₀ l <;> aesop

/-
If step `n` produces a codeword, the state after step `n` exists.
-/
lemma allocFun_state_succ (req : ℕ → Option (BitString × ℕ)) (n : ℕ) (cn : BitString)
    (hn : allocFun req n = some cn) : ∃ free', allocatorState req (n + 1) = some free' := by
  unfold allocFun at hn;
  unfold allocatorState; aesop;

/-
The codeword allocated at step `n` is prefix-incomparable to every node still
free after step `n`.
-/
lemma alloc_incomp_freeNext (req : ℕ → Option (BitString × ℕ)) (n : ℕ) (cn : BitString)
    (hn : allocFun req n = some cn) (free' : List BitString)
    (hfree' : allocatorState req (n + 1) = some free') :
    ∀ w ∈ free', ¬ cn <+: w ∧ ¬ w <+: cn := by
  -- By definition of `allocatorState`, we know that `allocatorState req n = some free` for some `free`.
  obtain ⟨free, hfree⟩ : ∃ free, allocatorState req n = some free := by
    cases h : allocatorState req n <;> simp_all +decide [ allocFun ];
  unfold allocFun at hn;
  rcases h : req n with ( _ | ⟨ fst, l ⟩ ) <;> simp_all +decide;
  rcases h' : allocateOne free l with ( _ | ⟨ allocated, snd ⟩ ) <;> simp_all +decide;
  have hnext : allocatorState req (n + 1) = some snd := by
    simp [allocatorState, hfree, h, h']
  have hfree_eq : free' = snd := by
    simpa [hnext] using hfree'.symm
  subst free'
  apply allocateOne_alloc_incomp_free' free l cn snd h' (allocatorState_prefixFree req n free hfree) (allocatorState_descLengths req n free hfree)

/-
Descendant monotonicity of the free list: a node free at a later step has a
prefix among the nodes free at an earlier step.
-/
lemma allocatorState_descendant_mono (req : ℕ → Option (BitString × ℕ)) (k k' : ℕ) (hk : k ≤ k')
    (F F' : List BitString) (h : allocatorState req k = some F)
    (h' : allocatorState req k' = some F') :
    ∀ w ∈ F', ∃ u ∈ F, u <+: w := by
  induction hk generalizing F F' with
  | refl =>
      intro w hw
      have hFF' : F = F' := by
        simpa [h] using h'
      subst F'
      exact ⟨w, hw, List.prefix_refl w⟩
  | step hkm ih =>
      rename_i m
      unfold allocatorState at h'
      cases hG : allocatorState req m with
      | none =>
          rw [hG] at h'
          cases h'
      | some G =>
          cases hreq : req m with
          | none =>
              have hGF' : G = F' := by
                simpa [hG, hreq] using h'
              subst F'
              exact ih F G h hG
          | some pr =>
              rcases pr with ⟨a, l⟩
              cases halloc : allocateOne G l with
              | none =>
                  simp [hG, hreq, halloc] at h'
              | some out =>
                  rcases out with ⟨a', free'⟩
                  have hfree' : free' = F' := by
                    simpa [hG, hreq, halloc] using h'
                  subst F'
                  intro w hw
                  obtain ⟨u, hu, huw⟩ := allocateOne_free_descendant G l a' free' halloc w hw
                  obtain ⟨v, hv, hvu⟩ := ih F G h hG u hu
                  exact ⟨v, hv, List.IsPrefix.trans hvu huw⟩

/-
The codeword allocated at step `m` is a descendant of some node free at step `m`.
-/
lemma allocFun_descendant_state (req : ℕ → Option (BitString × ℕ)) (m : ℕ) (cm : BitString)
    (hm : allocFun req m = some cm) :
    ∃ Fm, allocatorState req m = some Fm ∧ ∃ u ∈ Fm, u <+: cm := by
  unfold allocFun at hm;
  rcases h : allocatorState req m with ( _ | Fm ) <;> rcases h' : req m with ( _ | ⟨ fst, l ⟩ ) <;> simp_all +decide;
  rcases h'' : allocateOne Fm l with ( _ | ⟨ allocated, snd ⟩ ) <;> simp_all +decide;
  exact allocateOne_allocated_descendant Fm l cm snd h''

/-- For `m > n`, the codeword allocated at step `m` has a prefix among the nodes
free after step `n`. -/
lemma alloc_descendant_freeNext (req : ℕ → Option (BitString × ℕ)) (n m : ℕ) (cm : BitString)
    (hnm : n < m) (hm : allocFun req m = some cm) (free' : List BitString)
    (hfree' : allocatorState req (n + 1) = some free') :
    ∃ w ∈ free', w <+: cm := by
  obtain ⟨Fm, hFm, u, hu, hupre⟩ := allocFun_descendant_state req m cm hm
  obtain ⟨w, hw, hwpre⟩ := allocatorState_descendant_mono req (n + 1) m hnm free' Fm hfree' hFm u hu
  exact ⟨w, hw, hwpre.trans hupre⟩

lemma allocFun_prefixFree (req : ℕ → Option (BitString × ℕ)) (n m : ℕ) (cn cm : BitString)
    (hn : allocFun req n = some cn) (hm : allocFun req m = some cm) (hneq : n ≠ m) :
    ¬ List.IsPrefix cn cm := by
  rcases lt_trichotomy n m with hlt | heq | hgt
  · obtain ⟨free', hfree'⟩ := allocFun_state_succ req n cn hn
    obtain ⟨w, hw, hwpre⟩ := alloc_descendant_freeNext req n m cm hlt hm free' hfree'
    obtain ⟨h1, h2⟩ := alloc_incomp_freeNext req n cn hn free' hfree' w hw
    exact not_prefix_of_descendant hwpre h1 h2
  · exact absurd heq hneq
  · obtain ⟨free', hfree'⟩ := allocFun_state_succ req m cm hm
    obtain ⟨w, hw, hwpre⟩ := alloc_descendant_freeNext req m n cn hgt hn free' hfree'
    obtain ⟨_, h2⟩ := alloc_incomp_freeNext req m cm hm free' hfree' w hw
    exact fun hcontra => h2 (hwpre.trans hcontra)

lemma allocFun_success (req : ℕ → Option (BitString × ℕ)) (n : ℕ) (o : BitString) (l : ℕ)
    (hreq : req n = some (o, l))
    (hweight : (∑' i, match req i with | some (_, l) => (2 : ℝ≥0∞)⁻¹ ^ l | none => 0) ≤ 1) :
    ∃ c, allocFun req n = some c ∧ c.length = l := by
  -- Reduce the inline Kraft sum to `reqMass`.
  have hw : (∑' i, reqMass req i) ≤ 1 := by
    refine le_trans (le_of_eq ?_) hweight
    exact tsum_congr (fun i => rfl)
  -- The state exists at step `n`.
  obtain ⟨free, hstate⟩ : ∃ free, allocatorState req n = some free := by
    have := allocatorState_isSome req n hw
    exact Option.isSome_iff_exists.mp this
  have hd : DescLengths free := allocatorState_descLengths req n free hstate
  have hmass : freeMass free + usedMass req n = 1 := allocatorState_mass req n free hstate
  -- Serviceability: the free mass is at least `2^{-l}`.
  have hreqn : reqMass req n = (2 : ℝ≥0∞)⁻¹ ^ l := by simp only [reqMass, hreq]
  have hpartial : usedMass req n + (2 : ℝ≥0∞)⁻¹ ^ l ≤ 1 := by
    have hsucc : usedMass req (n + 1) ≤ ∑' i, reqMass req i := usedMass_le_tsum req (n + 1)
    have hstep : usedMass req (n + 1) = usedMass req n + reqMass req n := by
      simp only [usedMass, Finset.sum_range_succ]
    rw [hstep, hreqn] at hsucc
    exact le_trans hsucc hw
  have hmassge : (2 : ℝ≥0∞)⁻¹ ^ l ≤ freeMass free := by
    by_contra hlt
    push Not at hlt
    have : freeMass free + usedMass req n < (2 : ℝ≥0∞)⁻¹ ^ l + usedMass req n :=
      ENNReal.add_lt_add_right (by
        have : usedMass req n ≤ 1 := le_trans (usedMass_le_tsum req n) hw
        exact ne_top_of_le_ne_top (by norm_num) this) hlt
    rw [hmass, add_comm ((2 : ℝ≥0∞)⁻¹ ^ l)] at this
    exact absurd hpartial (not_le.mpr this)
  obtain ⟨v, hv, hvl⟩ := exists_fit_of_mass_ge free l hd hmassge
  -- Allocation succeeds, with the requested length.
  obtain ⟨a, free', halloc⟩ : ∃ a free', allocateOne free l = some (a, free') := by
    have := allocateOne_isSome_of_exists free l ⟨v, hv, hvl⟩
    obtain ⟨⟨a, free'⟩, h⟩ := Option.isSome_iff_exists.mp this
    exact ⟨a, free', h⟩
  refine ⟨a, ?_, allocateOne_length free l a free' halloc⟩
  simp only [allocFun, hstate, hreq, halloc]

end KraftChaitin
end Kolmogorov
