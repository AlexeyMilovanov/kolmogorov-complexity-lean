/-
Copyright (c) 2024 Alexey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey
-/
import Mathlib
import KolmogorovMathlib.Prefix.Basic

/-!
# Kraft's theorem, existence direction (combinatorial)

This is the classical converse of the Kraft inequality: given a finite list of
requested codeword lengths whose Kraft sum is `≤ 1`, there is an injective
prefix-free code realizing exactly those lengths.  It is purely combinatorial
(no computability), and is the combinatorial engine behind the Kraft–Chaitin
coding theorem.
-/

namespace Kolmogorov

open scoped ENNReal

/-- The length-`L` binary codeword (MSB first) for a natural number `a`. -/
def natToCode (L a : ℕ) : BitString :=
  (List.range L).reverse.map (fun i => a.testBit i)

theorem natToCode_length (L a : ℕ) : (natToCode L a).length = L := by
  simp [natToCode]

theorem natToCode_injective_of_lt (L a b : ℕ) (ha : a < 2 ^ L) (hb : b < 2 ^ L)
    (h_eq : natToCode L a = natToCode L b) : a = b := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  by_cases hi : i < L
  · unfold natToCode at h_eq
    simp_all +decide
  · rw [Nat.testBit_eq_false_of_lt, Nat.testBit_eq_false_of_lt]
    · exact hb.trans_le (Nat.pow_le_pow_right (by decide) (le_of_not_gt hi))
    · exact ha.trans_le (Nat.pow_le_pow_right (by decide) (le_of_not_gt hi))

theorem exists_sorted_indices (L : List ℕ) :
    ∃ σ : Fin L.length → Fin L.length,
      Function.Injective σ ∧ ∀ i j, i < j → L.get (σ i) ≤ L.get (σ j) := by
  have h_exists_min : ∀ (s : Finset (Fin L.length)), s.Nonempty →
      ∃ m ∈ s, ∀ n ∈ s, L.get n ≥ L.get m := by
    exact fun s hs => Finset.exists_min_image _ _ hs
  -- We can construct such a permutation by repeatedly selecting the minimum element
  -- from the remaining elements.
  have h_perm : ∀ (k : ℕ) (hk : k ≤ L.length), ∀ (s : Finset (Fin L.length)),
      s.card = k →
      ∃ σ : Fin k → Fin L.length,
        Function.Injective σ ∧ (∀ i, σ i ∈ s) ∧
          ∀ i j, i < j → L.get (σ i) ≤ L.get (σ j) := by
    intro k hk s hs_card
    induction k generalizing s with
    | zero => simp +decide [Function.Injective]
    | succ k ih =>
      obtain ⟨m, hm₁, hm₂⟩ := h_exists_min s (Finset.card_pos.mp (by linarith))
      obtain ⟨σ, hσ₁, hσ₂, hσ₃⟩ :=
        ih (Nat.le_of_succ_le hk) (s.erase m) (by
          rw [Finset.card_erase_of_mem hm₁, hs_card]
          simp +decide)
      use Fin.cons m σ
      simp_all +decide [Fin.forall_fin_succ, Function.Injective]
      exact ⟨fun i hi => False.elim <| hσ₂ i |>.1 <| hi.symm,
        fun i j hij => hσ₁ hij⟩
  exact Exists.elim (h_perm L.length le_rfl Finset.univ (by simp +decide)) fun σ hσ =>
    ⟨σ, hσ.1, hσ.2.2⟩

/-
**Kraft's theorem, existence direction.** For any finite list of requested
lengths whose Kraft sum `∑_i 2^{-Lᵢ}` is `≤ 1`, there is an injective family of
codewords of exactly those lengths whose range is prefix-free.
-/

-- The proof sorts the requested lengths, builds explicit codewords from partial
-- Kraft sums, and verifies prefix-freeness by integer arithmetic; elaborating
-- that combination needs a local heartbeat increase.
theorem exists_prefixFree_code_of_kraft_le_one (L : List ℕ)
    (hK : (L.map (fun l => (1 / 2 : ℝ) ^ l)).sum ≤ 1) :
    ∃ f : Fin L.length → BitString,
      (∀ j, (f j).length = L.get j) ∧
      Function.Injective f ∧
      IsPrefixFree (Set.range f) := by
  -- Let's sort the list of lengths in non-decreasing order.
  obtain ⟨σ, hσ⟩ := exists_sorted_indices L
  -- Define the codeword for each index using the sorted sequence.
  obtain ⟨f, hf⟩ : ∃ f : Fin L.length → BitString, (∀ i, (f i).length = L.get (σ i)) ∧ (∀ i j, i < j → ¬ IsStrictPrefix (f i) (f j)) ∧ (∀ i j, i ≠ j → f i ≠ f j) := by
    -- Define the codeword for each index using the sorted sequence and the Kraft inequality.
    obtain ⟨a, ha⟩ : ∃ a : Fin L.length → ℕ, (∀ i, a i < 2 ^ (L.get (σ i))) ∧ (∀ i j, i < j → a j ≥ (a i + 1) * 2 ^ (L.get (σ j) - L.get (σ i))) := by
      refine ⟨ fun i => ∑ j ∈ Finset.univ.filter ( fun j => j < i ), 2 ^ ( L.get ( σ i ) - L.get ( σ j ) ), ?_, ?_ ⟩ <;> simp_all +decide [ Finset.sum_filter ];
      · intro i
        have h_sum_lt : ∑ a ∈ Finset.univ.filter (fun a => a < i), (2 : ℝ) ^ (L.get (σ i) - L.get (σ a)) < 2 ^ L.get (σ i) := by
          have h_sum_lt : ∑ a ∈ Finset.univ.filter (fun a => a < i), (2 : ℝ) ^ (L.get (σ i) - L.get (σ a)) ≤ 2 ^ L.get (σ i) * (∑ a ∈ Finset.univ.filter (fun a => a < i), (1 / 2 : ℝ) ^ L.get (σ a)) := by
            rw [ Finset.mul_sum _ _ _ ] ; refine Finset.sum_le_sum fun j hj => ?_ ; rw [ ← Nat.sub_add_cancel ( show L.get ( σ j ) ≤ L.get ( σ i ) from ?_ ) ] ; norm_num [ pow_add, pow_mul ] ; ring_nf ;
            · norm_num [ mul_assoc, mul_comm, mul_left_comm, ← mul_pow ];
              norm_num [ ← mul_assoc, ← mul_pow ];
            · aesop;
          have h_sum_lt : ∑ a ∈ Finset.univ.filter (fun a => a < i), (1 / 2 : ℝ) ^ L.get (σ a) < ∑ a ∈ Finset.univ, (1 / 2 : ℝ) ^ L.get (σ a) := by
            rw [ ← Finset.sum_sdiff ( Finset.filter_subset ( fun a => a < i ) Finset.univ ) ];
            exact lt_add_of_pos_left _ ( Finset.sum_pos ( fun x hx => by positivity ) ⟨ i, by aesop ⟩ );
          have h_sum_lt : ∑ a ∈ Finset.univ, (1 / 2 : ℝ) ^ L.get (σ a) ≤ 1 := by
            convert hK using 1;
            have h_sum_lt : ∑ a ∈ Finset.univ, (1 / 2 : ℝ) ^ L.get (σ a) = ∑ a ∈ Finset.image σ Finset.univ, (1 / 2 : ℝ) ^ L.get a := by
              rw [ Finset.sum_image <| by tauto ];
            rw [ h_sum_lt, Finset.eq_of_subset_of_card_le ( Finset.image_subset_iff.mpr fun i _ => Finset.mem_univ ( σ i ) ) ( by rw [ Finset.card_image_of_injective _ hσ.1 ] ) ] ; norm_num [ List.sum_map_mul_right ];
            norm_num [ ← inv_pow ];
          nlinarith [ pow_pos ( zero_lt_two' ℝ ) ( L.get ( σ i ) ) ];
        norm_cast at * ; simp_all +decide [ Finset.sum_ite ];
      · intro i j hij; rw [ add_mul, one_mul ] ; simp +decide [ Finset.sum_ite ] ;
        rw [ show ( Finset.filter ( fun x => x < j ) Finset.univ : Finset ( Fin L.length ) ) = Finset.filter ( fun x => x < i ) Finset.univ ∪ { i } ∪ Finset.filter ( fun x => i < x ∧ x < j ) Finset.univ from ?_, Finset.sum_union, Finset.sum_union ] <;> norm_num [ Finset.sum_singleton, Finset.sum_union, Finset.sum_filter, Finset.sum_range_succ, Nat.pow_succ', mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul ];
        · refine le_add_of_le_of_nonneg ?_ ?_;
          · gcongr;
            split_ifs <;> norm_num [ ← pow_add ];
            grind +qlia;
          · exact Finset.sum_nonneg fun _ _ => by positivity;
        · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => lt_asymm ( Finset.mem_filter.mp hx₁ |>.2 ) ( Finset.mem_filter.mp hx₂ |>.2.1 );
        · grind;
    refine ⟨ fun i => natToCode ( L.get ( σ i ) ) ( a i ), ?_, ?_, ?_ ⟩ <;> simp_all +decide [ IsStrictPrefix ];
    · grind +locals;
    · intro i j hij h;
      -- By the properties of `natToCode`, if `natToCode L[σ i] (a i)` is a prefix of `natToCode L[σ j] (a j)`, then `a j / 2^(L[σ j] - L[σ i]) = a i`.
      have h_div : a j / 2 ^ (L[σ j] - L[σ i]) = a i := by
        have h_div : ∀ (L1 L2 : ℕ) (a1 a2 : ℕ), L1 ≤ L2 → a1 < 2 ^ L1 → a2 < 2 ^ L2 → natToCode L1 a1 <+: natToCode L2 a2 → a2 / 2 ^ (L2 - L1) = a1 := by
          intros L1 L2 a1 a2 hL1L2 ha1 ha2 hprefix
          have h_div : a2 / 2 ^ (L2 - L1) = a1 := by
            have h_eq : ∀ i < L1, (a2.testBit (L2 - 1 - i)) = (a1.testBit (L1 - 1 - i)) := by
              intro i hi
              have h_eq : (natToCode L1 a1)[i]? = (natToCode L2 a2)[i]? := by
                grind +suggestions;
              unfold natToCode at h_eq; simp_all +decide ;
              grind +revert
            refine Nat.eq_of_testBit_eq fun i => ?_;
            by_cases hi : i < L1;
            · convert h_eq ( L1 - 1 - i ) ( by omega ) using 1;
              · rw [ show L2 - 1 - ( L1 - 1 - i ) = L2 - L1 + i by omega ];
                grind +revert;
              · rw [ Nat.sub_sub_self ( Nat.le_sub_one_of_lt hi ) ];
            · rw [ Nat.testBit_eq_false_of_lt, Nat.testBit_eq_false_of_lt ];
              · exact ha1.trans_le ( Nat.pow_le_pow_right ( by decide ) ( le_of_not_gt hi ) );
              · refine lt_of_lt_of_le
                  (Nat.div_lt_of_lt_mul (m := a2) (n := 2 ^ (L2 - L1)) (k := 2 ^ L1) ?_) ?_;
                · rwa [ ← pow_add, Nat.sub_add_cancel hL1L2 ];
                · exact pow_le_pow_right₀ ( by decide ) ( le_of_not_gt hi );
          exact h_div;
        exact h_div _ _ _ _ ( hσ.2 i j hij ) ( ha.1 i ) ( ha.1 j ) h;
      have := ha.2 i j hij;
      exact absurd h_div ( Nat.ne_of_gt <| Nat.le_div_iff_mul_le ( by positivity ) |>.2 <| by linarith! );
    · intro i j hij; contrapose! hij; have := ha.2 i j; have := ha.2 j i; simp_all +decide ;
      -- Since the codewords are equal, their lengths must be equal.
      have h_len_eq : L.get (σ i) = L.get (σ j) := by
        replace hij := congr_arg List.length hij ; simp_all +decide [ natToCode_length ];
      have h_eq : a i = a j := by
        have hi_lt : a i < 2 ^ L.get (σ j) := by
          exact h_len_eq ▸ ha.1 i
        have h_code_eq :
            natToCode (L.get (σ j)) (a i) = natToCode (L.get (σ j)) (a j) := by
          convert hij using 1
          · exact congrArg (fun n => natToCode n (a i)) h_len_eq.symm
          · rfl
        exact natToCode_injective_of_lt _ _ _ hi_lt (ha.1 j) h_code_eq
      exact le_antisymm ( le_of_not_gt fun hi => by have := ha.2 _ _ hi; aesop ) ( le_of_not_gt fun hj => by have := ha.2 _ _ hj; aesop );
  let e : Fin L.length ≃ Fin L.length :=
    Equiv.ofBijective σ ⟨hσ.1, Finite.injective_iff_surjective.mp hσ.1⟩
  refine ⟨fun j => f (e.symm j), ?_, ?_, ?_⟩
  · intro j
    have hσj : σ (e.symm j) = j := by
      change e (e.symm j) = j
      exact e.apply_symm_apply j
    rw [hf.1 (e.symm j), hσj]
  · intro i j hij
    have hidx : e.symm i = e.symm j := by
      by_contra hne
      exact hf.2.2 (e.symm i) (e.symm j) hne hij
    exact Equiv.injective e.symm hidx
  · intro p hp q hq hpref_pq
    rcases hp with ⟨i, rfl⟩
    rcases hq with ⟨j, rfl⟩
    let a : Fin L.length := e.symm i
    let b : Fin L.length := e.symm j
    change f a = f b
    have hpref : f a <+: f b := by
      simpa [a, b, e] using hpref_pq
    rcases lt_trichotomy a b with hab | hab | hba
    · by_contra hne
      exact hf.2.1 a b hab ⟨hpref, hne⟩
    · exact congrArg f hab
    · have hlen : (f a).length = (f b).length := by
        apply le_antisymm
        · exact List.IsPrefix.length_le hpref
        · rw [hf.1 b, hf.1 a]
          exact hσ.2 b a hba
      exact List.IsPrefix.eq_of_length hpref hlen

end Kolmogorov
