/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Complexity.Applications.ComplexSubsequences.SetPairComplexity

/-!
# Failure of the set-pair complexity bound for Martin-Löf random sequences

For a Martin-Löf random sequence `w`, we show that no threshold `N` makes every finite set `F` of
at least `N` positions contain an element `t` whose set-pair complexity `setPairComplexity V w F t`
is at least `α * |F|`, for any fixed `α > 0`.  The proof finds a long run of zeros of `w`
(via a computable test built from blocks of length `L`), and then codes the interval `F` by its
start and length, so that the complexity of `w` on `F` is only logarithmic in `|F|`.

The main declaration is `not_exists_max_setPairComplexity_ge_of_isMartinLofRandom`; the module
belongs to the part of the book of Shen, Uspensky and Vereshchagin on complex subsequences and
substrings.
-/

namespace Kolmogorov.Applications
open MeasureTheory

private def not_exists_max_setPairComplexity_ge_of_isMartinLofRandom_zero_runs_seq (L : ℕ)
    (n : ℕ) (x : List Bool) : Bool :=
  decide (x.length = n * (2 ^ L) * L ∧ ∀ j < n * (2 ^ L), true ∈ List.drop (j * L)
      (List.take ((j + 1) * L) x))

private lemma not_exists_max_setPairComplexity_ge_of_isMartinLofRandom_computable (L : ℕ) :
  Computable₂ (not_exists_max_setPairComplexity_ge_of_isMartinLofRandom_zero_runs_seq L) := by
  have hj1 : Primrec (fun (p : (ℕ × List Bool) × ℕ) => p.2 * L) :=
    Primrec.nat_mul.comp Primrec.snd (Primrec.const L |>.comp Primrec.fst)
  have hj2 : Primrec (fun (p : (ℕ × List Bool) × ℕ) => (p.2 + 1) * L) :=
    Primrec.nat_mul.comp (Primrec.nat_add.comp Primrec.snd (Primrec.const 1 |>.comp Primrec.fst))
        (Primrec.const L |>.comp Primrec.fst)
  have hlist1 : Primrec (fun (p : (ℕ × List Bool) × ℕ) => List.take ((p.2 + 1) * L) p.1.2) :=
    (Primrec.list_take (α := Bool)).comp hj2 (Primrec.snd.comp Primrec.fst)
  have hlist2 : Primrec (fun (p : (ℕ × List Bool) × ℕ) => List.drop (p.2 * L)
                                                            (List.take ((p.2 + 1) * L) p.1.2)) :=
    (Primrec.list_drop (α := Bool)).comp hj1 hlist1
  have hmem : Primrec (fun (p : (ℕ × List Bool) × ℕ) => decide (true ∈ List.drop (p.2 * L)
                                                          (List.take ((p.2 + 1) * L) p.1.2))) :=
    (@Kolmogorov.list_mem_decide_primrec Bool _ _).comp (Primrec.const true |>.comp Primrec.fst)
        hlist2
  have h_inner : Primrec₂ (fun (p : ℕ × List Bool) (j : ℕ) =>
    decide (true ∈ List.drop (j * L) (List.take ((j + 1) * L) p.2))) :=
    hmem
  have h_range : Primrec (fun (p : ℕ × List Bool) => List.range (p.1 * (2 ^ L))) :=
    Primrec.list_range.comp (Primrec.nat_mul.comp Primrec.fst (Primrec.const (2 ^ L)))
  have h_forall : Computable₂ (fun (n : ℕ) (x : List Bool) =>
    (List.range (n * (2 ^ L))).all (fun j => decide (true ∈ List.drop (j * L) (List.take ((j + 1) *
                                               L) x)))) :=
    (@Kolmogorov.list_all_primrec (ℕ × List Bool) ℕ _ _ (fun p => List.range (p.1 * (2 ^ L)))
        (fun p j => decide (true ∈ List.drop (j * L) (List.take ((j + 1) * L) p.2))) h_range
        h_inner).to₂.to_comp
  have h_target : Computable₂ (fun (n : ℕ) (x : List Bool) => n * (2 ^ L) * L) :=
    Computable₂.comp Primrec.nat_mul.to_comp (Computable₂.comp Primrec.nat_mul.to_comp
        Computable.fst (Computable.const (2 ^ L))) (Computable.const L |>.comp Computable.fst)
  have hlen : Computable₂ (fun (n : ℕ) (x : List Bool) => x.length) :=
      Primrec.list_length.to_comp.comp Computable.snd
  
  have heq : Computable₂ (fun (n : ℕ) (x : List Bool) => decide (x.length = n * (2 ^ L) * L)) :=
    Computable₂.comp (Primrec.eq (α := ℕ)).decide.to₂.to_comp hlen h_target
  have h_final : Computable₂ (fun (n : ℕ) (x : List Bool) =>
    decide (x.length = n * (2 ^ L) * L ∧ ∀ j < n * (2 ^ L), true ∈ List.drop (j * L)
    (List.take ((j + 1) * L) x))) := by
    have h_equiv : (fun (n : ℕ) (x : List Bool) => decide (x.length = n * (2 ^ L) * L ∧ ∀ j < n *
                                                     (2 ^ L), true ∈ List.drop (j * L)
                                                     (List.take ((j + 1) * L) x))) = 
                   (fun (n : ℕ) (x : List Bool) => decide (x.length = n * (2 ^ L) * L) &&
                     (List.range (n * (2 ^ L))).all (fun j =>
                       decide (true ∈ List.drop (j * L) (List.take ((j + 1) * L) x)))) := by
      funext n x
      simp only [Bool.decide_and]
      congr 1
      have h1 : (∀ (j : ℕ), j < n * 2 ^ L → true ∈ List.drop (j * L) (List.take ((j + 1) * L) x)) ↔
          ((List.range (n * 2 ^ L)).all (fun j => decide (true ∈ List.drop (j * L) (List.take ((j +
                                                    1) * L) x))) = true) := by
        rw [List.all_eq_true]
        constructor
        · intro h j hj
          exact decide_eq_true (h j (List.mem_range.mp hj))
        · intro h j hj
          exact of_decide_eq_true (h j (List.mem_range.mpr hj))
      cases h_dec : decide (∀ j < n * (2 ^ L), true ∈ List.drop (j * L) (List.take ((j + 1) * L) x))
      · have h_false : ¬(∀ j < n * (2 ^ L), true ∈ List.drop (j * L) (List.take ((j + 1) * L) x)) :=
          of_decide_eq_false h_dec
        have h_all_false : (List.range (n * (2 ^ L))).all
            (fun j => decide (true ∈ List.drop (j * L) (List.take ((j + 1) * L) x))) = false := by
          cases h_all : (List.range (n * (2 ^ L))).all
              (fun j => decide (true ∈ List.drop (j * L) (List.take ((j + 1) * L) x)))
          · rfl
          · exfalso
            exact h_false (h1.mpr h_all)
        exact h_all_false.symm
      · have h_true : (∀ j < n * (2 ^ L), true ∈ List.drop (j * L) (List.take ((j + 1) * L) x)) :=
          of_decide_eq_true h_dec
        have h_all_true : (List.range (n * (2 ^ L))).all
            (fun j => decide (true ∈ List.drop (j * L) (List.take ((j + 1) * L) x))) = true :=
            h1.mp h_true
        exact h_all_true.symm
    rw [h_equiv]
    exact Computable₂.comp (Primrec.dom_bool₂ (fun a b => a && b)).to_comp heq h_forall
  exact (Computable.of_eq h_final fun _ => rfl)


/-- Step 1 of the proof of
`not_exists_max_setPairComplexity_ge_of_isMartinLofRandom_measure_eq`:
Splitting off the first aligned block shifts the remaining block indices by one. -/
private lemma not_exists_max_setPairComplexity_ge_of_isMartinLofRandom_split_blocks (L m : ℕ)
    (x : List Bool) :
    (∀ j < m + 1, true ∈ (x.drop (j * L)).take L) ↔
      true ∈ x.take L ∧ ∀ j < m, true ∈ ((x.drop L).drop (j * L)).take L := by
  constructor
  · intro h
    refine ⟨by simpa using h 0 (by omega), ?_⟩
    intro j hj
    simpa [List.drop_drop, Nat.add_mul, Nat.add_comm] using h (j + 1) (by omega)
  · rintro ⟨h0, h⟩ (j | j) hj
    · simpa using h0
    · simpa [List.drop_drop, Nat.add_mul, Nat.add_comm] using h j (by omega)

/-- Step 2 of the proof of
`not_exists_max_setPairComplexity_ge_of_isMartinLofRandom_measure_eq`:
Among length-`L` bit strings, precisely `2 ^ L - 1` contain `true`. -/
private lemma not_exists_max_setPairComplexity_ge_of_isMartinLofRandom_card_block (L : ℕ) :
    ((stringsOfLength L).filter (fun x => true ∈ x)).card = 2 ^ L - 1 := by
  have heq : (stringsOfLength L).filter (fun x => true ∈ x) =
      (stringsOfLength L).erase (List.replicate L false) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_erase, mem_stringsOfLength]
    constructor
    · rintro ⟨hlen, ht⟩
      refine ⟨?_, hlen⟩
      intro hx
      rw [hx] at ht
      simp at ht
    · rintro ⟨hne, hlen⟩
      refine ⟨hlen, ?_⟩
      by_contra ht
      apply hne
      rw [← hlen]
      apply List.eq_replicate_of_mem
      intro b hb
      cases b with
      | false => rfl
      | true => exact (ht hb).elim
  rw [heq, Finset.card_erase_of_mem, card_stringsOfLength]
  simp [mem_stringsOfLength]

/-- Step 3 of the proof of
`not_exists_max_setPairComplexity_ge_of_isMartinLofRandom_measure_eq`:
Splitting into consecutive blocks counts the length-`m * L` strings whose every aligned block
contains `true`. -/
private lemma not_exists_max_setPairComplexity_ge_of_isMartinLofRandom_card_blocks (L m : ℕ) :
    ((stringsOfLength (m * L)).filter
      (fun x => ∀ j < m, true ∈ (x.drop (j * L)).take L)).card =
      (2 ^ L - 1) ^ m := by
  classical
  let G : ℕ → Finset BitString := fun k =>
    (stringsOfLength (k * L)).filter (fun x => ∀ j < k, true ∈ (x.drop (j * L)).take L)
  change (G m).card = _
  have hmem (k : ℕ) (x : BitString) : x ∈ G k ↔
      x.length = k * L ∧ ∀ j < k, true ∈ (x.drop (j * L)).take L := by
    simp [G, mem_stringsOfLength]
  let T := (stringsOfLength L).filter (fun x => true ∈ x)
  have hT (x : BitString) : x ∈ T ↔ x.length = L ∧ true ∈ x := by
    simp [T, mem_stringsOfLength]
  induction m with
  | zero =>
    have hG : G 0 = {[]} := by
      ext x
      simp [hmem]
    simp [hG]
  | succ m ih =>
    have hcard : (G (m + 1)).card = (T ×ˢ G m).card := by
      refine Finset.card_nbij' (fun x => (x.take L, x.drop L))
        (fun yz => yz.1 ++ yz.2) ?_ ?_ ?_ ?_
      · intro x hx
        obtain ⟨hlen, hall⟩ := (hmem _ _).mp hx
        obtain ⟨hfirst, hrest⟩ :=
            (not_exists_max_setPairComplexity_ge_of_isMartinLofRandom_split_blocks L m x).mp hall
        apply Finset.mem_product.mpr
        constructor
        · apply (hT _).mpr
          exact ⟨by simp [List.length_take, hlen, Nat.succ_mul], hfirst⟩
        · apply (hmem _ _).mpr
          exact ⟨by simp [List.length_drop, hlen, Nat.succ_mul], hrest⟩
      · intro yz hyz
        obtain ⟨hy, hz⟩ := Finset.mem_product.mp hyz
        obtain ⟨hylen, hytrue⟩ := (hT _).mp hy
        obtain ⟨hzlen, hzblocks⟩ := (hmem _ _).mp hz
        apply (hmem _ _).mpr
        constructor
        · simp [List.length_append, hylen, hzlen, Nat.succ_mul, Nat.add_comm]
        · apply (not_exists_max_setPairComplexity_ge_of_isMartinLofRandom_split_blocks L m _).mpr
          simpa [← hylen, List.take_left, List.drop_left] using And.intro hytrue hzblocks
      · intro x _
        exact List.take_append_drop _ _
      · intro yz hyz
        have hylen := ((hT _).mp (Finset.mem_product.mp hyz).1).1
        apply Prod.ext
        · dsimp only
          rw [← hylen, List.take_left]
        · dsimp only
          rw [← hylen, List.drop_left]
    rw [hcard, Finset.card_product, show T.card = 2 ^ L -
        1 from not_exists_max_setPairComplexity_ge_of_isMartinLofRandom_card_block L, ih,
      pow_succ, Nat.mul_comm]

/-- Step 1 of the proof of
`not_exists_max_setPairComplexity_ge_of_isMartinLofRandom_measure`: measure
equation -/
private lemma not_exists_max_setPairComplexity_ge_of_isMartinLofRandom_measure_eq (L n : ℕ) :
  uniformMeasure (⋃ x,
      if not_exists_max_setPairComplexity_ge_of_isMartinLofRandom_zero_runs_seq L n x =
      true then cantorCylinder x else ∅) =
    (((2 ^ L - 1) ^ (n * 2 ^ L) : ℕ) : ENNReal) * (2 : ENNReal)⁻¹ ^ (n * 2 ^ L * L) := by
  classical
  let S := (stringsOfLength (n * 2 ^ L * L)).filter
    (fun x => ∀ j < n * 2 ^ L, true ∈ (x.drop (j * L)).take L)
  have hmem (x : BitString) : x ∈ S ↔
      not_exists_max_setPairComplexity_ge_of_isMartinLofRandom_zero_runs_seq L n x = true :=
          by
    simp only [S, Finset.mem_filter, mem_stringsOfLength,
      not_exists_max_setPairComplexity_ge_of_isMartinLofRandom_zero_runs_seq,
      decide_eq_true_eq, List.drop_take, Nat.add_mul, Nat.one_mul, Nat.add_sub_cancel_left]
  have hcover :
      (⋃ x, if not_exists_max_setPairComplexity_ge_of_isMartinLofRandom_zero_runs_seq L n x =
          true
        then cantorCylinder x else ∅) = ⋃ x ∈ S, cantorCylinder x := by
    ext w
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨x, hx⟩
      by_cases h : not_exists_max_setPairComplexity_ge_of_isMartinLofRandom_zero_runs_seq L n
          x = true
      · exact ⟨x, (hmem x).mpr h, by simpa [h] using hx⟩
      · simp [h] at hx
    · rintro ⟨x, hx, hw⟩
      exact ⟨x, by simpa [(hmem x).mp hx] using hw⟩
  have hlen : ∀ x ∈ S, x.length = n * 2 ^ L * L := by
    intro x hx
    exact (mem_stringsOfLength _ _).mp (Finset.mem_filter.mp hx).1
  have hdisj : (S : Set BitString).PairwiseDisjoint cantorCylinder := by
    intro x hx y hy hxy
    have hlength : x.length = y.length := (hlen x hx).trans (hlen y hy).symm
    refine cantorCylinder_disjoint_of_incompatible ?_ ?_
    · intro hp
      exact hxy (hp.eq_of_length hlength)
    · intro hp
      exact hxy (hp.eq_of_length hlength.symm).symm
  rw [hcover, measure_biUnion_finset hdisj (fun x _ => measurableSet_cantorCylinder x)]
  have hterm : ∀ x ∈ S, uniformMeasure (cantorCylinder x) =
      (2 : ENNReal)⁻¹ ^ (n * 2 ^ L * L) := by
    intro x hx
    rw [uniformMeasure_cantorCylinder, hlen x hx]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
  congr 1
  exact_mod_cast not_exists_max_setPairComplexity_ge_of_isMartinLofRandom_card_blocks L (n * 2 ^ L)

/-- Step 2 of the proof of
`not_exists_max_setPairComplexity_ge_of_isMartinLofRandom_measure`: inequality
-/
private lemma not_exists_max_setPairComplexity_ge_of_isMartinLofRandom_ineq (L : ℕ) (_ : 1 ≤ L)
    (n : ℕ) :
  (((2 ^ L - 1) ^ (n * 2 ^ L) : ℕ) : ENNReal) * (2 : ENNReal)⁻¹ ^ (n * 2 ^ L * L) ≤ dyadicValue 1
      n := by
  have H : 1 ≤ 2^L := Nat.one_le_two_pow
  have h_nonneg : 0 ≤ 1 - ((2 : ℝ)^L)⁻¹ := by
    have h2L_ge_1 : (1 : ℝ) ≤ (2 : ℝ)^L := by exact_mod_cast Nat.one_le_two_pow
    have h_inv : ((2 : ℝ)^L)⁻¹ ≤ 1 := (inv_le_one₀ (by positivity)).mpr h2L_ge_1
    linarith
  have h1 : (1 - ((2 : ℝ)^L)⁻¹) ^ (2 ^ L) ≤ (2 : ℝ)⁻¹ := by
    have H2 : 1 + (2 ^ L : ℝ) * ((2 : ℝ)^L)⁻¹ ≤ (1 + ((2 : ℝ)^L)⁻¹) ^ (2 ^ L) := by
      have h_nonneg2 : -2 ≤ ((2 : ℝ)^L)⁻¹ := by
        linarith [show (0 : ℝ) ≤ ((2 : ℝ)^L)⁻¹ by positivity]
      exact_mod_cast one_add_mul_le_pow h_nonneg2 (2 ^ L)
    have H3 : (1 + ((2 : ℝ)^L)⁻¹) ^ (2 ^ L) ≥ 2 := by
      calc (1 + ((2 : ℝ)^L)⁻¹) ^ (2 ^ L) 
        _ ≥ 1 + (2 ^ L : ℝ) * ((2 : ℝ)^L)⁻¹ := H2
        _ = 2 := by
          have H4 : (2 ^ L : ℝ) * ((2 : ℝ)^L)⁻¹ = 1 := by
            apply mul_inv_cancel₀
            positivity
          rw [H4]
          norm_num
    have H5 : (1 - ((2 : ℝ)^L)⁻¹) * (1 + ((2 : ℝ)^L)⁻¹) = 1 - (((2 : ℝ)^L)⁻¹) ^ 2 := by ring
    have H6 : (1 - ((2 : ℝ)^L)⁻¹) * (1 + ((2 : ℝ)^L)⁻¹) ≤ 1 := by
      rw [H5]
      linarith [show 0 ≤ (((2 : ℝ)^L)⁻¹) ^ 2 by positivity]
    have h_nonneg_mul : 0 ≤ (1 - ((2 : ℝ)^L)⁻¹) * (1 + ((2 : ℝ)^L)⁻¹) := by positivity
    have H7 : (1 - ((2 : ℝ)^L)⁻¹) ^ (2 ^ L) * (1 + ((2 : ℝ)^L)⁻¹) ^ (2 ^ L) ≤ 1 := by
      have H7' : (1 - ((2 : ℝ)^L)⁻¹) ^ (2 ^ L) * (1 + ((2 : ℝ)^L)⁻¹) ^ (2 ^ L) =
          ((1 - ((2 : ℝ)^L)⁻¹) * (1 + ((2 : ℝ)^L)⁻¹)) ^ (2 ^ L) := by
        rw [← mul_pow]
      rw [H7']
      have H7'' : ((1 - ((2 : ℝ)^L)⁻¹) * (1 + ((2 : ℝ)^L)⁻¹)) ^ (2 ^ L) ≤ 1 ^ (2 ^ L) := by
        gcongr
      have H7''' : (1 : ℝ) ^ (2 ^ L) = 1 := one_pow _
      rw [H7'''] at H7''
      exact H7''
    have H8 : (1 - ((2 : ℝ)^L)⁻¹) ^ (2 ^ L) * 2 ≤ (1 - ((2 : ℝ)^L)⁻¹) ^ (2 ^ L) *
        (1 + ((2 : ℝ)^L)⁻¹) ^ (2 ^ L) := by
      gcongr
    linarith
  have step1 : (((2 ^ L - 1) : ℕ) : ℝ) = ((2 : ℝ)^L - 1) := by
    exact_mod_cast rfl
  have step2 : (((2 ^ L - 1) ^ (n * 2 ^ L) : ℕ) : ℝ) = ((2 : ℝ)^L - 1) ^ (n * 2 ^ L) := by
    rw [Nat.cast_pow, step1]
  have step3 : (2 : ℝ)⁻¹ ^ (n * 2 ^ L * L) = ((2 : ℝ)⁻¹ ^ L) ^ (n * 2 ^ L) := by
    rw [← pow_mul]
    congr 1
    ring
  have step4 : ((2 : ℝ)^L - 1) * ((2 : ℝ)^L)⁻¹ = 1 - ((2 : ℝ)^L)⁻¹ := by
    rw [sub_mul]
    have h_cancel : (2 : ℝ) ^ L * ((2 : ℝ) ^ L)⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
    rw [h_cancel, one_mul]
  have step4' : (2 : ℝ)⁻¹ ^ L = ((2 : ℝ)^L)⁻¹ := by rw [inv_pow]
  have step5 : (1 - ((2 : ℝ)^L)⁻¹) ^ (n * 2 ^ L) = ((1 - ((2 : ℝ)^L)⁻¹) ^ (2 ^ L)) ^ n := by
    rw [← pow_mul]
    congr 1
    ring
  have h2 : ((2 : ℝ)^L - 1) ^ (n * 2 ^ L) * ((2 : ℝ)⁻¹ ^ L) ^ (n * 2 ^ L) ≤ (2 : ℝ)⁻¹ ^ n := by
    rw [← mul_pow]
    rw [step4']
    rw [step4]
    rw [step5]
    have h_bound1 : ((1 - ((2 : ℝ)^L)⁻¹) ^ (2 ^ L)) ^ n ≤ ((2 : ℝ)⁻¹) ^ n := by
      have h3 : 0 ≤ (1 - ((2 : ℝ)^L)⁻¹) ^ (2 ^ L) := by positivity
      gcongr
    exact h_bound1
  rw [dyadicValue, Nat.cast_one, ENNReal.div_eq_inv_mul, mul_comm, ← ENNReal.inv_pow]
  have h3 : (((2 ^ L - 1) ^ (n * 2 ^ L) : ℕ) : ENNReal) = ENNReal.ofReal
      (((2 ^ L - 1) ^ (n * 2 ^ L) : ℕ) : ℝ) := by
    rw [ENNReal.ofReal_natCast]
  have h4 : (2 : ENNReal)⁻¹ ^ (n * 2 ^ L * L) = ENNReal.ofReal ((2 : ℝ)⁻¹ ^ (n * 2 ^ L * L)) := by
    have h4_1 : (2 : ENNReal)⁻¹ = ENNReal.ofReal ((2 : ℝ)⁻¹) := by
      have h4_2 : (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) := by
        exact ENNReal.ofReal_ofNat 2 |>.symm
      rw [h4_2, ← ENNReal.ofReal_inv_of_pos (by positivity)]
    rw [h4_1]
    have h_nonneg_2_inv : 0 ≤ (2 : ℝ)⁻¹ := by positivity
    rw [← ENNReal.ofReal_pow h_nonneg_2_inv]
  rw [h3]
  have h4' : ((2:ENNReal)^ (n * 2 ^ L * L))⁻¹ = (2 : ENNReal)⁻¹ ^ (n * 2 ^ L * L) := by
    rw [ENNReal.inv_pow]
  rw [h4']
  rw [h4]
  rw [← ENNReal.ofReal_mul (by positivity)]
  have h5 : ((2 : ENNReal)⁻¹) ^ n = ENNReal.ofReal (((2 : ℝ)⁻¹) ^ n) := by
    have h5_1 : (2 : ENNReal)⁻¹ = ENNReal.ofReal ((2 : ℝ)⁻¹) := by
      have h5_2 : (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) := by
        exact ENNReal.ofReal_ofNat 2 |>.symm
      rw [h5_2, ← ENNReal.ofReal_inv_of_pos (by positivity)]
    rw [h5_1]
    have h_nonneg_2_inv : 0 ≤ (2 : ℝ)⁻¹ := by positivity
    rw [← ENNReal.ofReal_pow h_nonneg_2_inv]
  have h5_1 : (((2 : ENNReal)^n)⁻¹) * 1 = ENNReal.ofReal (((2 : ℝ)⁻¹) ^ n) := by
    have h5_2 : ((2 : ENNReal)^n)⁻¹ = (2 : ENNReal)⁻¹ ^ n := by rw [ENNReal.inv_pow]
    rw [h5_2]
    rw [mul_one, h5]
  rw [h5_1]
  apply ENNReal.ofReal_le_ofReal
  have h6 : (((2 ^ L - 1) ^ (n * 2 ^ L) : ℕ) : ℝ) * (2 : ℝ)⁻¹ ^ (n * 2 ^ L * L) = ((2 : ℝ)^L - 1) ^
      (n * 2 ^ L) * ((2 : ℝ)⁻¹ ^ L) ^ (n * 2 ^ L) := by
    rw [step2, step3]
  have h7 : (2 : ℝ)⁻¹ ^ (n * 2 ^ L * L) * (((2 ^ L - 1) ^ (n * 2 ^ L) : ℕ) : ℝ) = ((2 : ℝ)^L - 1) ^
      (n * 2 ^ L) * ((2 : ℝ)⁻¹ ^ L) ^ (n * 2 ^ L) := by
    rw [mul_comm]
    exact h6
  rw [h7]
  exact h2

private lemma not_exists_max_setPairComplexity_ge_of_isMartinLofRandom_measure
    (L : ℕ) (hL : 1 ≤ L) (n : ℕ) :
  uniformMeasure (⋃ x,
      if not_exists_max_setPairComplexity_ge_of_isMartinLofRandom_zero_runs_seq L n x =
      true then cantorCylinder x else ∅) ≤ dyadicValue 1 n := by
  have h := not_exists_max_setPairComplexity_ge_of_isMartinLofRandom_measure_eq L n
  rw [h]
  exact not_exists_max_setPairComplexity_ge_of_isMartinLofRandom_ineq L hL n

private lemma not_exists_max_setPairComplexity_ge_of_isMartinLofRandom_subset
    (L : ℕ) :
  {w : CantorSeq | ∀ n, ∃ i, n ≤ i ∧ i < n + L ∧ w i = true} ⊆
    ⋂ n, ⋃ x, if not_exists_max_setPairComplexity_ge_of_isMartinLofRandom_zero_runs_seq L n x
        = true then cantorCylinder x else ∅ := by
  intro w hw
  simp only [Set.mem_iInter, Set.mem_iUnion]
  intro n
  let m := n * (2 ^ L)
  let x := cantorPrefix w (m * L)
  use x
  split_ifs with h
  · apply mem_cantorCylinder_cantorPrefix
  · simp only [not_exists_max_setPairComplexity_ge_of_isMartinLofRandom_zero_runs_seq,
      decide_eq_true_eq] at h
    push Not at h
    have h1 : x.length = m * L := cantorPrefix_length w (m * L)
    have h2 := h h1
    obtain ⟨j, hj, hj_false⟩ := h2
    have h3 := hw (j * L)
    obtain ⟨i, hi1, hi2, hi3⟩ := h3
    have hi_bounds : i < m * L := by
      calc i < j * L + L := hi2
           _ = (j + 1) * L := by ring
           _ ≤ m * L := Nat.mul_le_mul_right L (Nat.succ_le_of_lt hj)
    have hi_bounds2 : i < x.length := by rw [h1]; exact hi_bounds
    have hj_mem : true ∈ List.drop (j * L) (List.take ((j + 1) * L) x) := by
      have h_ith : x[i] = true := by
        have h_get := cantorPrefix_getElem w (m * L) i hi_bounds2
        rw [h_get]
        exact hi3
      apply List.mem_drop_iff_getElem.mpr
      use (i - j * L)
      have himin : i < min ((j + 1) * L) x.length := by
        rw [lt_min_iff]
        refine ⟨by linarith, hi_bounds2⟩
      have h_add : i - j * L + j * L = i := Nat.sub_add_cancel hi1
      have h_lt : i - j * L + j * L < (List.take ((j + 1) * L) x).length := by
        rw [h_add, List.length_take]
        exact himin
      refine ⟨h_lt, ?_⟩
      have h_get : (List.take ((j + 1) * L) x)[j * L + (i - j * L)] = true := by
        have h_eq : j * L + (i - j * L) = i := by rw [add_comm]; exact h_add
        simp_rw [h_eq]
        have himin2 : i < (List.take ((j + 1) * L) x).length := by
          rw [List.length_take]
          exact himin
        have h_get_take := @List.getElem_take Bool x ((j + 1) * L) i himin2
        rw [h_get_take]
        exact h_ith
      exact h_get
    exact hj_false hj_mem

/-- Step 1 of the proof of `not_exists_max_setPairComplexity_ge_of_isMartinLofRandom`:
every Martin-Löf random sequence has zero intervals of every finite length. -/
private theorem not_exists_max_setPairComplexity_ge_of_isMartinLofRandom_zero_runs
    {w : CantorSeq} (hw : IsMartinLofRandom uniformMeasure w) :
    ∀ L : ℕ, ∃ n : ℕ, ∀ i : ℕ, n ≤ i → i < n + L → w i = false :=  by
  intro L
  by_cases hL : L = 0
  · use 0; intro i _ h_lt; rw [hL] at h_lt; omega
  · have hL1 : 1 ≤ L := by omega
    by_contra h_contra
    push Not at h_contra
    set A := {w : CantorSeq | ∀ n, ∃ i, n ≤ i ∧ i < n + L ∧ w i = true}
    have h_in_A : w ∈ A := by
      intro n
      obtain ⟨i, h1, h2, h3⟩ := h_contra n
      use i
      refine ⟨h1, h2, ?_⟩
      cases h : w i
      · contradiction
      · rfl
    have h_null : IsEffectivelyNull uniformMeasure A := by
      rw [isEffectivelyNull_iff_decidable]
      use not_exists_max_setPairComplexity_ge_of_isMartinLofRandom_zero_runs_seq L
      refine ⟨not_exists_max_setPairComplexity_ge_of_isMartinLofRandom_computable L,
              not_exists_max_setPairComplexity_ge_of_isMartinLofRandom_subset L,
              not_exists_max_setPairComplexity_ge_of_isMartinLofRandom_measure L hL1⟩
    have h_not_rand := (isEffectivelyNull_iff_forall_not_random isComputableMeasure_uniform A).mp
        h_null w h_in_A
    exact h_not_rand hw

/-- Step 1 of the proof of
`not_exists_max_setPairComplexity_ge_of_isMartinLofRandom_interval_code`:
the increasing enumeration of the interval is a translated range. -/
private lemma not_exists_max_setPairComplexity_ge_of_isMartinLofRandom_sort
    (n L : ℕ) :
    (Finset.Ico n (n + L)).sort (· ≤ ·) = (List.range L).map (n + ·) := by
  rw [← List.range'_eq_map_range, ← List.toFinset_range'_1 n L]
  exact (List.toFinset_sort (· ≤ ·) List.nodup_range').2 (List.pairwise_le_range')

/-- Step 2 of the proof of
`not_exists_max_setPairComplexity_ge_of_isMartinLofRandom_interval_code`:
the restriction to an all-zero interval is a list of `L` false bits. -/
private lemma not_exists_max_setPairComplexity_ge_of_isMartinLofRandom_restrict
    (w : CantorSeq) (n L : ℕ)
    (hw : ∀ i : ℕ, n ≤ i → i < n + L → w i = false) :
    restrictBits w (Finset.Ico n (n + L)) = List.replicate L false := by
  unfold restrictBits
  apply List.eq_replicate_iff.mpr
  constructor
  · rw [List.length_map, Finset.length_sort, Nat.card_Ico]
    omega
  · intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    have hi' := (Finset.mem_sort (· ≤ ·)).mp hi
    exact hw i (Finset.mem_Ico.mp hi').1 (Finset.mem_Ico.mp hi').2

/-- Step 3 of the proof of
`not_exists_max_setPairComplexity_ge_of_isMartinLofRandom_interval_code`:
the encoded pair consisting of an interval and `L` false bits is computable from its
left endpoint and length. -/
private lemma not_exists_max_setPairComplexity_ge_of_isMartinLofRandom_interval_code_computable :
    Computable₂ (fun n L : ℕ =>
      pairCode (finsetCode (Finset.Ico n (n + L))) (List.replicate L false)) := by
  have hlist : Primrec (fun q : ℕ × ℕ =>
      (List.range q.2).map (fun i => natBits (q.1 + i))) :=
    Primrec.list_map (Primrec.list_range.comp Primrec.snd)
      (primrec_natBits.comp
        (Primrec.nat_add.comp (Primrec.fst.comp Primrec.fst) Primrec.snd))
  have hrep : Primrec (fun q : ℕ × ℕ => List.replicate q.2 false) :=
    Primrec.list_replicate.comp Primrec.snd (Primrec.const false)
  have hout : Computable (fun q : ℕ × ℕ =>
      pairCode (listCode ((List.range q.2).map (fun i => natBits (q.1 + i))))
        (List.replicate q.2 false)) :=
    (show Computable₂ pairCode from pairCode_computable).comp
      (listCode_primrec.comp hlist).to_comp hrep.to_comp
  exact hout.of_eq (fun q => by
    simp only [finsetCode,
      not_exists_max_setPairComplexity_ge_of_isMartinLofRandom_sort, List.map_map]
    rfl)

/-- Step 2 of the proof of `not_exists_max_setPairComplexity_ge_of_isMartinLofRandom`: on
an all-zero interval, the encoded pair has logarithmic complexity given any point of the interval.
-/
private theorem not_exists_max_setPairComplexity_ge_of_isMartinLofRandom_interval_code
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ (w : CantorSeq) (n L : ℕ),
      (∀ i : ℕ, n ≤ i → i < n + L → w i = false) →
      ∀ t ∈ Finset.Ico n (n + L),
        setPairComplexity V w (Finset.Ico n (n + L)) t ≤
          (((3 * (Nat.bits L).length + c : ℕ) : ℕ) : ℝ) := by
  let f : BitString × BitString → BitString := fun q =>
    let L := bitsToNat (decodeFirst q.1)
    let d := bitsToNat (decodeSecond q.1)
    let n := bitsToNat q.2 - d
    pairCode (finsetCode (Finset.Ico n (n + L))) (List.replicate L false)
  have hL : Computable (fun q : BitString × BitString => bitsToNat (decodeFirst q.1)) :=
    bitsToNat_computable.comp (decodeFirst_computable.comp Computable.fst)
  have hd : Computable (fun q : BitString × BitString => bitsToNat (decodeSecond q.1)) :=
    bitsToNat_computable.comp (decodeSecond_computable.comp Computable.fst)
  have hn : Computable (fun q : BitString × BitString =>
      bitsToNat q.2 - bitsToNat (decodeSecond q.1)) :=
    Primrec.nat_sub.to_comp.comp (bitsToNat_computable.comp Computable.snd) hd
  have hf : Computable f :=
    not_exists_max_setPairComplexity_ge_of_isMartinLofRandom_interval_code_computable.comp hn hL
  let D : Map := fun q => Part.some (f q)
  have hD : isDecompressor D := hf
  obtain ⟨c, hc⟩ := hV.2 D hD
  refine ⟨c + 1, ?_⟩
  intro w n L hw t ht
  have hnt : n ≤ t := (Finset.mem_Ico.mp ht).1
  have hdt : t - n < L := by
    have ht_upper := (Finset.mem_Ico.mp ht).2
    omega
  have hsize : (Nat.bits (t - n)).length ≤ (Nat.bits L).length := by
    rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len]
    exact Nat.size_le_size hdt.le
  -- Encode the length and an offset padded to the same binary width.
  let p := pairCode (Nat.bits L) (ShortDescriptions.padBits (t - n) (Nat.bits L).length)
  have hp_len : p.length = 3 * (Nat.bits L).length + 1 := by
    dsimp [p]
    rw [length_pairCode, ShortDescriptions.padBits_length _ _ hsize]
    omega
  have hrestore : t - (t - n) = n := by omega
  have hprod : produces D p (natBits t)
      (pairCode (finsetCode (Finset.Ico n (n + L))) (restrictBits w (Finset.Ico n (n + L)))) := by
    rw [
      not_exists_max_setPairComplexity_ge_of_isMartinLofRandom_restrict w n L hw]
    simp only [produces, D, f, p, decodeFirst_pairCode, decodeSecond_pairCode, bitsToNat_bits,
      ShortDescriptions.padBits_bitsToNat, natBits, hrestore]
    exact Part.mem_some _
  have hcode : condK D
      (pairCode (finsetCode (Finset.Ico n (n + L))) (restrictBits w (Finset.Ico n (n + L))))
      (natBits t) ≤ (p.length : ENat) := sInf_le ⟨p, hprod, rfl⟩
  have hbound : condK V
      (pairCode (finsetCode (Finset.Ico n (n + L))) (restrictBits w (Finset.Ico n (n + L))))
      (natBits t) ≤ ((3 * (Nat.bits L).length + (c + 1) : ℕ) : ENat) := by
    calc
      _ ≤ condK D _ _ + (c : ENat) := hc _ _
      _ ≤ (p.length : ENat) + (c : ENat) := add_le_add hcode le_rfl
      _ = _ := by rw [hp_len, ← Nat.cast_add]; congr 1; omega
  dsimp only [setPairComplexity]
  exact_mod_cast ENat.toNat_le_of_le_natCast hbound

/-- Step 3 of the proof of `not_exists_max_setPairComplexity_ge_of_isMartinLofRandom`: a
logarithmic code bound is eventually below a positive linear bound. -/
private theorem not_exists_max_setPairComplexity_ge_of_isMartinLofRandom_length
    (α : ℝ) (hα0 : 0 < α) (c N : ℕ) :
    ∃ L : ℕ, N ≤ L ∧ 0 < L ∧
      (((3 * (Nat.bits L).length + c : ℕ) : ℕ) : ℝ) < α * L := by
  have h1 : Filter.Tendsto (fun m : ℕ => (m : ℝ) / (2:ℝ)^m) Filter.atTop (nhds 0) := by
    have h_limit := tendsto_pow_const_div_const_pow_of_one_lt (1:ℕ) (by norm_num : (1:ℝ) < 2)
    simpa using h_limit
  have h2 : Filter.Tendsto (fun m : ℕ => (1 : ℝ) / (2:ℝ)^m) Filter.atTop (nhds 0) := by
    have h_limit := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 2⁻¹)
        (by norm_num : (2⁻¹ : ℝ) < 1)
    have hr : (fun (m:ℕ) => (2⁻¹ : ℝ)^m) = (fun m : ℕ => (1 : ℝ) / (2:ℝ)^m) := by
      ext m
      calc
        (2⁻¹ : ℝ)^m = (1/2:ℝ)^m := by
          congr 1
          exact one_div 2 |>.symm
        _ = 1 / (2:ℝ)^m := by
          exact one_div_pow 2 m
    rwa [← hr]
  
  have h3 : Filter.Tendsto (fun m : ℕ => 3 * ((m : ℝ) / (2:ℝ)^m) + (3 + (c:ℝ)) *
                                           ((1 : ℝ) / (2:ℝ)^m)) Filter.atTop (nhds 0) := by
    have h3a := Filter.Tendsto.const_mul 3 h1
    have h3b := Filter.Tendsto.const_mul (3 + (c:ℝ)) h2
    have h3c := Filter.Tendsto.add h3a h3b
    simpa using h3c
  have h4 := (tendsto_order.mp h3).2 α hα0
  rw [Filter.eventually_atTop] at h4
  rcases h4 with ⟨m0, hm0⟩
  
  use 2 ^ (max m0 N)
  have hm := hm0 (max m0 N) (le_max_left _ _)
  have hN : N ≤ 2 ^ max m0 N := calc
    N ≤ max m0 N := le_max_right _ _
    _ ≤ 2 ^ max m0 N := (Nat.lt_two_pow_self).le
  
  refine ⟨hN, by positivity, ?_⟩
  have hl : (Nat.bits (2 ^ (max m0 N))).length = max m0 N + 1 := by
    have hl_rw : (Nat.bits (2 ^ (max m0 N))).length = Nat.size (2 ^ (max m0 N)) := by
      exact Nat.size_eq_bits_len (2 ^ (max m0 N))
    rw [hl_rw, Nat.size_pow]
  rw [hl]
  have hl_cast : (((3 * (max m0 N + 1) + c : ℕ) : ℕ) : ℝ) = 3 * ((max m0 N : ℝ) + 1) + (c:ℝ) := by
    push_cast
    rfl
  rw [hl_cast]
  have hm_eq : 3 * (↑(max m0 N) / (2:ℝ) ^ max m0 N) + (3 + ↑c) * (1 / (2:ℝ) ^ max m0 N) =
      (3 * (↑(max m0 N) + 1) + ↑c) / (2:ℝ) ^ max m0 N := by
    have : (3 + (c:ℝ)) * (1 / (2:ℝ) ^ max m0 N) = (3 + (c:ℝ)) / (2:ℝ) ^ max m0 N :=
        mul_one_div (3 + (c:ℝ)) _
    rw [this]
    have hmul : 3 * (↑(max m0 N) / (2:ℝ) ^ max m0 N) = 3 * ↑(max m0 N) / (2:ℝ) ^ max m0 N := by
      exact mul_div_assoc' 3 _ _
    rw [hmul, ← add_div]
    congr 1
    ring
  rw [hm_eq] at hm
  have hhh : 3 * (↑(max m0 N) + 1) + ↑c < α * (2:ℝ) ^ max m0 N := (div_lt_iff₀ (by positivity)).mp
      hm
  have h2pow : ((2 ^ max m0 N : ℕ) : ℝ) = (2:ℝ) ^ max m0 N := by
    exact Nat.cast_pow 2 (max m0 N)
  rw [h2pow]
  have hcast_eq : (max (m0:ℝ) (N:ℝ)) = ↑(max m0 N) := by
    exact (Nat.cast_max m0 N).symm
  rw [hcast_eq]
  exact hhh

/-- For a Martin-Löf random sequence `w` and any `α > 0`, there is no bound `N` such that every
finite set `F` of at least `N` indices contains an element `t` with set-pair complexity at least
`α * |F|`; that is, the complexity of a Martin-Löf random sequence cannot be spread evenly over
every large set of positions. -/
theorem not_exists_max_setPairComplexity_ge_of_isMartinLofRandom (V : Map)
    (hV : isOptimalConditional V) {w : CantorSeq} (hw : IsMartinLofRandom uniformMeasure w) {α : ℝ}
    (hα0 : 0 < α) :
    ¬ ∃ N : ℕ, ∀ F : Finset ℕ, N ≤ F.card → ∃ t ∈ F, α * F.card ≤ setPairComplexity V w F t := by
  intro ⟨N, hN⟩
  obtain ⟨c, hc⟩ := not_exists_max_setPairComplexity_ge_of_isMartinLofRandom_interval_code V
      hV
  obtain ⟨L, hL_N, hL_pos, hL_lt⟩ :=
      not_exists_max_setPairComplexity_ge_of_isMartinLofRandom_length α hα0 c N
  obtain ⟨n, hn⟩ := not_exists_max_setPairComplexity_ge_of_isMartinLofRandom_zero_runs hw L
  set F := Finset.Ico n (n + L)
  have hF_card : F.card = L := by
    rw [Nat.card_Ico n (n + L)]
    omega
  have h_le : N ≤ F.card := by rw [hF_card]; exact hL_N
  obtain ⟨t, ht, h_ge⟩ := hN F h_le
  have h_step2 := hc w n L hn t ht
  have h_contra : setPairComplexity V w F t < α * F.card := by
    calc setPairComplexity V w F t ≤ (((3 * (Nat.bits L).length + c : ℕ) : ℕ) : ℝ) := h_step2
      _ < α * L := hL_lt
      _ = α * F.card := by rw [hF_card]
  linarith


end Kolmogorov.Applications
