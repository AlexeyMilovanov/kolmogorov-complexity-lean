/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.TTMeet2014.Accounting
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The entropy function realising a board

The paper builds a KC set `A_j` for each board.  The library provides the exact realisation
`K_{U'} = min (K_V + 5, F + 3)` for an entropy function `F`
(`Kolmogorov.exists_isOptimalPrefixConditional_min_toNat`), which controls the *exact* set of
compressed strings.  So a board is represented by

  `realizingF I j x = |x| - 4` if we compress `x`, and `2 |x| + 3` otherwise,

and then `|x| ≤ F x + 3` holds exactly when we do not compress `x` (`length_le_realizingF_iff`).
The move `⟨|τ| - 1, τ⟩` costs `2 ^ (1 - |τ|)` in the normalization of the paper, that is `8` times
this in the Kraft sum of `F`.

This module depends only on Mathlib; the statements of the Kraft sum and the overgraph are the
definitions `Kolmogorov.IsKraftFun` and `Kolmogorov.HasREOvergraph`, unfolded.
-/

namespace Kolmogorov.RandomStrings.TTMeet

open Finset

variable {I : Input}

open Classical in
/-- The entropy function of board `j`. -/
noncomputable def realizingF (I : Input) (j : Fin 3) (x : Str) : ℕ :=
  if x ∈ finalOurs I j then x.length - 4 else 2 * x.length + 3

/-- **Exactness.**  The threshold `|x| ≤ F x + 3` holds exactly off the strings compressed by us.
It uses `length_ge_of_mem_oursAt`: without it, a short string could be "compressed" with no
effect. -/
theorem length_le_realizingF_iff (j : Fin 3) (x : Str) :
    x.length ≤ realizingF I j x + 3 ↔ x ∉ finalOurs I j := by
  classical
  unfold realizingF
  by_cases hx : x ∈ finalOurs I j
  · obtain ⟨s, hs⟩ := hx
    have h8 := length_ge_of_mem_oursAt I hs
    have hx' : x ∈ finalOurs I j := ⟨s, hs⟩
    simp only [hx', ite_true, not_true_eq_false, iff_false]
    omega
  · simp only [hx, ite_false, not_false_eq_true, iff_true]
    omega

/-- There are at most `2 ^ n` strings of length `n` in any finite set. -/
theorem card_filter_length_le' (S : Finset Str) (n : ℕ) :
    (S.filter fun x => x.length = n).card ≤ 2 ^ n := by
  classical
  calc (S.filter fun x => x.length = n).card
      ≤ ((Finset.univ : Finset (List.Vector Bool n)).image fun v => v.toList).card := by
        apply Finset.card_le_card
        intro x hx
        rw [Finset.mem_filter] at hx
        rw [Finset.mem_image]
        exact ⟨⟨x, hx.2⟩, Finset.mem_univ _, rfl⟩
    _ ≤ (Finset.univ : Finset (List.Vector Bool n)).card := Finset.card_image_le
    _ = 2 ^ n := by simp [Finset.card_univ, card_vector]

/-- The default part of `F` has Kraft sum at most `1/4`. -/
theorem kraft_default (S : Finset Str) : ∑ x ∈ S, (2 : ℝ)⁻¹ ^ (2 * x.length + 3) ≤ 1 / 4 := by
  classical
  obtain ⟨M, hmaps⟩ : ∃ M, ∀ x ∈ S, x.length ∈ Finset.range M := by
    refine ⟨(S.image List.length).sup id + 1, fun x hx => ?_⟩
    rw [Finset.mem_range]
    have : x.length ≤ (S.image List.length).sup id :=
      Finset.le_sup (f := id) (Finset.mem_image_of_mem _ hx)
    omega
  calc ∑ x ∈ S, (2 : ℝ)⁻¹ ^ (2 * x.length + 3)
      = ∑ n ∈ Finset.range M, ∑ x ∈ S with x.length = n, (2 : ℝ)⁻¹ ^ (2 * x.length + 3) :=
        (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ ≤ ∑ n ∈ Finset.range M, (8 : ℝ)⁻¹ * (1 / 2 : ℝ) ^ n := by
        apply Finset.sum_le_sum
        intro n _
        have hc : ∑ x ∈ S with x.length = n, (2 : ℝ)⁻¹ ^ (2 * x.length + 3)
            = ((S.filter fun x => x.length = n).card : ℝ) * (2 : ℝ)⁻¹ ^ (2 * n + 3) := by
          rw [Finset.sum_congr rfl (g := fun _ => (2 : ℝ)⁻¹ ^ (2 * n + 3))
            (fun x hx => by rw [(Finset.mem_filter.1 hx).2]), Finset.sum_const, nsmul_eq_mul]
        rw [hc]
        have hcard : ((S.filter fun x => x.length = n).card : ℝ) ≤ 2 ^ n := by
          exact_mod_cast card_filter_length_le' S n
        have hpos : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ (2 * n + 3) := by positivity
        calc ((S.filter fun x => x.length = n).card : ℝ) * (2 : ℝ)⁻¹ ^ (2 * n + 3)
            ≤ 2 ^ n * (2 : ℝ)⁻¹ ^ (2 * n + 3) := mul_le_mul_of_nonneg_right hcard hpos
          _ = (8 : ℝ)⁻¹ * (1 / 2 : ℝ) ^ n := by
            have h2 : (2 : ℝ)⁻¹ ^ (2 * n + 3) = (2 : ℝ)⁻¹ ^ n * (2 : ℝ)⁻¹ ^ n * (8 : ℝ)⁻¹ := by
              rw [show 2 * n + 3 = n + n + 3 by ring, pow_add, pow_add]
              norm_num
            have h3 : (2 : ℝ) ^ n * (2 : ℝ)⁻¹ ^ n = 1 := by
              rw [← mul_pow, mul_inv_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_pow]
            rw [h2, one_div]
            calc (2 : ℝ) ^ n * ((2 : ℝ)⁻¹ ^ n * (2 : ℝ)⁻¹ ^ n * (8 : ℝ)⁻¹)
                = ((2 : ℝ) ^ n * (2 : ℝ)⁻¹ ^ n) * ((8 : ℝ)⁻¹ * (2 : ℝ)⁻¹ ^ n) := by ring
              _ = (8 : ℝ)⁻¹ * (2 : ℝ)⁻¹ ^ n := by rw [h3, one_mul]
    _ = (8 : ℝ)⁻¹ * ∑ n ∈ Finset.range M, (1 / 2 : ℝ) ^ n := by rw [Finset.mul_sum]
    _ ≤ (8 : ℝ)⁻¹ * 2 := by
        gcongr
        exact sum_geometric_two_le M
    _ = 1 / 4 := by norm_num

/-- The move costs `8` times `realCost` in the Kraft sum of `F`. -/
theorem pow_sub_four_eq {τ : Str} (h : 4 ≤ τ.length) :
    (2 : ℝ)⁻¹ ^ (τ.length - 4) = 8 * ((realCost τ : ℚ) : ℝ) := by
  have hl : τ.length = (τ.length - 4) + 4 := by omega
  unfold realCost
  push_cast
  rw [hl]
  simp only [Nat.add_sub_cancel]
  rw [pow_add, inv_pow]
  field_simp
  norm_num

/-- **Kraft for `F`.**  The compressed strings use at most `8 · 3/32 = 3/4`, by Lemma 4.4, and the
default uses at most `1/4`. -/
theorem realizingF_kraft (hI : I.Valid) (j : Fin 3) (S : Finset Str) :
    ∑ x ∈ S, (2 : ℝ)⁻¹ ^ realizingF I j x ≤ 1 := by
  classical
  have hsplit : ∑ x ∈ S, (2 : ℝ)⁻¹ ^ realizingF I j x ≤
      ∑ x ∈ S.filter (· ∈ finalOurs I j), 8 * ((realCost x : ℚ) : ℝ) +
        ∑ x ∈ S, (2 : ℝ)⁻¹ ^ (2 * x.length + 3) := by
    rw [← Finset.sum_filter_add_sum_filter_not S (· ∈ finalOurs I j)]
    refine add_le_add (le_of_eq ?_) ?_
    · refine Finset.sum_congr rfl fun x hx => ?_
      have hx' := (Finset.mem_filter.1 hx).2
      obtain ⟨s, hs⟩ := hx'
      have h8 := length_ge_of_mem_oursAt I hs
      have hxf : x ∈ finalOurs I j := ⟨s, hs⟩
      unfold realizingF
      rw [ite_eq_left hxf]
      exact pow_sub_four_eq (by omega)
    · calc ∑ x ∈ S.filter (¬ · ∈ finalOurs I j), (2 : ℝ)⁻¹ ^ realizingF I j x
          = ∑ x ∈ S.filter (¬ · ∈ finalOurs I j), (2 : ℝ)⁻¹ ^ (2 * x.length + 3) := by
            refine Finset.sum_congr rfl fun x hx => ?_
            unfold realizingF
            rw [ite_eq_right (Finset.mem_filter.1 hx).2]
        _ ≤ ∑ x ∈ S, (2 : ℝ)⁻¹ ^ (2 * x.length + 3) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              fun _ _ _ => by positivity
  have hours : ∑ x ∈ S.filter (· ∈ finalOurs I j), 8 * ((realCost x : ℚ) : ℝ) ≤ 3 / 4 := by
    obtain ⟨s, hs⟩ := exists_stage_of_subset_finalOurs I j (S.filter (· ∈ finalOurs I j))
      fun τ hτ => (Finset.mem_filter.1 hτ).2
    have h1 : trueCost (S.filter (· ∈ finalOurs I j)) ≤ 3 / 32 :=
      (Finset.sum_le_sum_of_subset_of_nonneg hs fun τ _ _ => (realCost_pos τ).le).trans
        (lemma_4_4 I hI s j)
    have h2 : ((trueCost (S.filter (· ∈ finalOurs I j)) : ℚ) : ℝ) ≤ 3 / 32 := by
      calc ((trueCost (S.filter (· ∈ finalOurs I j)) : ℚ) : ℝ) ≤ ((3 / 32 : ℚ) : ℝ) :=
            Rat.cast_le.2 h1
        _ = 3 / 32 := by norm_num
    rw [← Finset.mul_sum]
    have h3 : ((trueCost (S.filter (· ∈ finalOurs I j)) : ℚ) : ℝ) =
        ∑ x ∈ S.filter (· ∈ finalOurs I j), ((realCost x : ℚ) : ℝ) := by
      simp [trueCost]
    rw [← h3]
    linarith
  have := kraft_default S
  linarith

/-- The projection along `ℕ` of a computable predicate is c.e. -/
theorem rePred_exists_of_computable {α : Type*} [Primcodable α] {f : α × ℕ → Bool}
    (hf : Computable f) : REPred fun a => ∃ s, f (a, s) = true := by
  have hrf := Partrec.rfind (Computable.to₂ hf).partrec₂
  refine hrf.dom_re.of_eq fun a => ?_
  rw [Nat.rfind_dom]
  constructor
  · rintro ⟨s, hs, -⟩
    exact ⟨s, (Part.mem_some_iff.1 hs).symm⟩
  · intro h
    classical
    exact ⟨Nat.find h, Part.mem_some_iff.2 (Nat.find_spec h).symm, fun _ => trivial⟩

/-- The test for the overgraph of `F`, for a computable enumeration `o` of the compressed
strings. -/
theorem overgraph_re {o : ℕ × Str → Bool} (ho : Computable o) :
    REPred fun p : Str × ℕ => ∃ s, (decide (2 * p.1.length + 3 ≤ p.2) ||
      (o (s, p.1) && decide (p.1.length - 4 ≤ p.2))) = true := by
  have hlen : Computable fun q : (Str × ℕ) × ℕ => q.1.1.length :=
    Primrec.list_length.to_comp.comp (Computable.fst.comp Computable.fst)
  have hn : Computable fun q : (Str × ℕ) × ℕ => q.1.2 := Computable.snd.comp Computable.fst
  have h1 : Computable fun q : (Str × ℕ) × ℕ => decide (2 * q.1.1.length + 3 ≤ q.1.2) :=
    Primrec.nat_le.decide.to_comp.comp
      (Primrec.nat_add.to_comp.comp
        (Primrec.nat_mul.to_comp.comp (Computable.const 2) hlen) (Computable.const 3)) hn
  have h2 : Computable fun q : (Str × ℕ) × ℕ => decide (q.1.1.length - 4 ≤ q.1.2) :=
    Primrec.nat_le.decide.to_comp.comp
      (Primrec.nat_sub.to_comp.comp hlen (Computable.const 4)) hn
  have h3 : Computable fun q : (Str × ℕ) × ℕ => o (q.2, q.1.1) :=
    ho.comp (Computable.snd.pair (Computable.fst.comp Computable.fst))
  have hc : Computable fun q : (Str × ℕ) × ℕ =>
      (decide (2 * q.1.1.length + 3 ≤ q.1.2) ||
        (o (q.2, q.1.1) && decide (q.1.1.length - 4 ≤ q.1.2))) :=
    Primrec.or.to_comp.comp h1 (Primrec.and.to_comp.comp h3 h2)
  exact rePred_exists_of_computable hc

/-- **The overgraph of `F` is c.e.**, from the computability of what we enumerate. -/
theorem realizingF_re (hI : I.Valid) (j : Fin 3) :
    REPred fun p : Str × ℕ => realizingF I j p.1 ≤ p.2 := by
  classical
  -- `F x ≤ n` iff the default is small or some stage compresses `x` with `|x| - 4 ≤ n`.
  have hiff : ∀ p : Str × ℕ, realizingF I j p.1 ≤ p.2 ↔
      ∃ s, (decide (2 * p.1.length + 3 ≤ p.2) ||
        (oursB I j s p.1 && decide (p.1.length - 4 ≤ p.2))) = true := by
    intro p
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, oursB]
    constructor
    · intro h
      unfold realizingF at h
      split_ifs at h with hx
      · obtain ⟨s, hs⟩ := hx
        exact ⟨s, Or.inr ⟨hs, h⟩⟩
      · exact ⟨0, Or.inl h⟩
    · rintro ⟨s, h | ⟨hs, h⟩⟩
      · unfold realizingF
        split_ifs <;> omega
      · unfold realizingF
        rw [ite_eq_left ⟨s, hs⟩]
        exact h
  exact (overgraph_re (o := fun p => oursB I j p.1 p.2) (oursB_computable hI j)).of_eq
    fun p => (hiff p).symm

end Kolmogorov.RandomStrings.TTMeet
