/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.MisesChurch.NormalInBase

/-!
# Champernowne

This file shows that multiplication by a nonzero rational preserves normality in a base
(`isNormalInBase_mul_rat`, Section 9.3 of Shen–Uspensky–Vereshchagin), and defines Champernowne's
sequence `champernowne`, the binary expansions of `1, 2, 3, …` written one after another
(`msbBits` is the expansion with the most significant bit first).  The main result is
`isNormal_champernowne`: the Champernowne sequence is normal.
-/

namespace Kolmogorov.FrequencyGames
open MeasureTheory Filter Topology
open scoped BigOperators

/-- **SUV Section 9.3, p. 265 (Wall)**, the stated consequence: multiplication by an arbitrary
nonzero rational preserves normality.  The zero factor must be excluded, as in Problem 258. -/
theorem isNormalInBase_mul_rat {b : ℕ} (hb : 2 ≤ b) {α : ℝ} (hα : IsNormalInBase b α)
    {q : ℚ} (hq : q ≠ 0) : IsNormalInBase b ((q : ℝ) * α) := by
  have H1 : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := by exact Rat.cast_def q
  rw [H1]
  have H2 : IsNormalInBase b ((q.num : ℝ) * α) := isNormalInBase_mul hb hα (by
    intro h
    apply hq
    have hq_num : q.num = 0 := by exact_mod_cast h
    rw [←Rat.num_ne_zero] at hq
    exact False.elim (hq hq_num)
  )
  have H3 := isNormalInBase_div_int (k := q.den) hb H2 (by
    intro h
    have h_den : q.den = 0 := by exact_mod_cast h
    have h_den_pos := q.den_pos
    omega
  )
  have H4 : ((q.num : ℝ) * α) / (q.den : ℤ) = ((q.num : ℝ) / (q.den : ℝ)) * α := by
    push_cast
    ring
  rwa [H4] at H3

/-- The most significant bit first binary expansion of `n`. -/
def msbBits (n : ℕ) : BitString := (Nat.bits n).reverse

/-- **SUV p. 265.**  Champernowne's sequence: `1, 2, 3, …` written in binary and concatenated.
The first `i + 1` numbers contribute at least `i + 1` bits, so the `i`-th bit is defined. -/
def champernowne : CantorSeq := fun i =>
  (((List.range (i + 1)).map fun n => msbBits (n + 1)).flatten)[i]?.getD false

/-- The concatenation of the binary expansions of `1, 2, …, M`. -/
private def isNormal_champernowne_cw (M : ℕ) : List Bool :=
  ((List.range M).map fun n => msbBits (n + 1)).flatten

/-- The number of prefixes of `L` that end with `U` (= the number of occurrences of `U` in `L`
for `U ≠ []`). -/
private def isNormal_champernowne_occ (U L : List Bool) : ℕ :=
  (L.inits.filter fun P => decide (U <:+ P)).length

/-- The total length of the binary expansions of `1, …, M`. -/
private def isNormal_champernowne_Lam (M : ℕ) : ℕ := ∑ x ∈ Finset.Icc 1 M, Nat.size x

open Classical in
/-- The number of positions `p < N` where `U` occurs in the Champernowne sequence. -/
private noncomputable def isNormal_champernowne_O (U : BitString) (N : ℕ) : ℕ :=
  ((Finset.range N).filter fun p => OccursAt U champernowne p).card

private lemma isNormal_champernowne_aux_A_cw_zero : isNormal_champernowne_cw 0 = [] := by
  simp [isNormal_champernowne_cw]

private lemma isNormal_champernowne_aux_A_cw_succ (M : ℕ) :
    isNormal_champernowne_cw (M + 1) = isNormal_champernowne_cw M ++ msbBits (M + 1) := by
  simp [isNormal_champernowne_cw, List.range_succ]

private lemma isNormal_champernowne_aux_A_length_msbBits (n : ℕ) :
    (msbBits n).length = Nat.size n := by
  simp [msbBits, Nat.size_eq_bits_len]

private lemma isNormal_champernowne_aux_A_Lam_succ (M : ℕ) :
    isNormal_champernowne_Lam (M + 1) = isNormal_champernowne_Lam M + Nat.size (M + 1) := by
  unfold isNormal_champernowne_Lam
  rw [Finset.sum_Icc_succ_top (by omega)]

private lemma isNormal_champernowne_aux_A_cw_prefix_of_le {M M' : ℕ} (h : M ≤ M') :
    isNormal_champernowne_cw M <+: isNormal_champernowne_cw M' := by
  induction M', h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ M' hM ih =>
    rw [isNormal_champernowne_aux_A_cw_succ]
    exact ih.trans (List.prefix_append _ _)

private lemma isNormal_champernowne_aux_A_le_length (M : ℕ) :
    M ≤ (isNormal_champernowne_cw M).length := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [isNormal_champernowne_aux_A_cw_succ, List.length_append,
      isNormal_champernowne_aux_A_length_msbBits]
    have : 0 < Nat.size (M + 1) := Nat.size_pos.mpr (Nat.succ_pos M)
    omega

private lemma isNormal_champernowne_aux_A_champernowne_eq (M i : ℕ)
    (hi : i < (isNormal_champernowne_cw M).length) :
    champernowne i = (isNormal_champernowne_cw M)[i] := by
  have hi1 : i < (isNormal_champernowne_cw (i + 1)).length := by
    have := isNormal_champernowne_aux_A_le_length (i + 1)
    omega
  have hdef : champernowne i = (isNormal_champernowne_cw (i + 1))[i]?.getD false := rfl
  have hp1 := isNormal_champernowne_aux_A_cw_prefix_of_le (le_max_right M (i + 1))
  have hp2 := isNormal_champernowne_aux_A_cw_prefix_of_le (le_max_left M (i + 1))
  rw [hdef, List.getElem?_eq_getElem hi1]
  simp only [Option.getD_some]
  rw [hp1.getElem hi1, hp2.getElem hi]

private lemma isNormal_champernowne_aux_A_inits_eq (L : List Bool) :
    L.inits = (List.range (L.length + 1)).map (fun m => L.take m) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [List.getElem_inits]

private lemma isNormal_champernowne_aux_A_occ_eq_card (U L : List Bool) :
    isNormal_champernowne_occ U L =
      ((Finset.range (L.length + 1)).filter fun m => U <:+ L.take m).card := by
  unfold isNormal_champernowne_occ
  rw [isNormal_champernowne_aux_A_inits_eq, List.filter_map, List.length_map]
  simp [Finset.card, Finset.filter_val, Finset.range_val, Multiset.range, Multiset.filter_coe,
    Function.comp_def]

private lemma isNormal_champernowne_aux_A_suffix_cantorPrefix (w : CantorSeq) (U : BitString)
    (m : ℕ) :
    U <:+ cantorPrefix w m ↔ U.length ≤ m ∧ OccursAt U w (m - U.length) := by
  rw [List.suffix_iff_eq_drop]
  simp only [cantorPrefix_length]
  constructor
  · intro h
    have hk : U.length ≤ m := by
      have := congrArg List.length h
      simp only [List.length_drop, cantorPrefix_length] at this
      omega
    refine ⟨hk, ?_⟩
    intro j hj
    have h1 := List.getElem_of_eq h hj
    rw [h1, List.getElem_drop, cantorPrefix_getElem]
  · rintro ⟨hk, hocc⟩
    apply List.ext_getElem
    · simp only [List.length_drop, cantorPrefix_length]
      omega
    · intro j h1 h2
      rw [List.getElem_drop, cantorPrefix_getElem]
      exact (hocc j h1).symm

/-- Step 1 of the proof of `isNormal_champernowne`: the concatenation of the binary
expansions of `1, …, M` has length `∑_{x ≤ M} size x`. -/
private lemma isNormal_champernowne_cw_length (M : ℕ) :
    (isNormal_champernowne_cw M).length = isNormal_champernowne_Lam M := by
  induction M with
  | zero => simp [isNormal_champernowne_aux_A_cw_zero, isNormal_champernowne_Lam]
  | succ M ih =>
    rw [isNormal_champernowne_aux_A_cw_succ, List.length_append, ih,
      isNormal_champernowne_aux_A_length_msbBits, isNormal_champernowne_aux_A_Lam_succ]

/-- Step 2 of the proof of `isNormal_champernowne`: every prefix of `cw M` is a prefix of
the Champernowne sequence. -/
private lemma isNormal_champernowne_cw_prefix (M e : ℕ)
    (he : e ≤ (isNormal_champernowne_cw M).length) :
    cantorPrefix champernowne e = (isNormal_champernowne_cw M).take e := by
  apply List.ext_getElem
  · simp [he]
  · intro i h1 h2
    have hie : i < e := by simpa using h1
    rw [cantorPrefix_getElem, List.getElem_take]
    exact isNormal_champernowne_aux_A_champernowne_eq M i (by omega)

/-- Step 3 of the proof of `isNormal_champernowne`: the occurrences of `U` in `cw M`
are the occurrences of `U` in the first `Lam M + 1 - |U|` positions of the Champernowne sequence. -/
private lemma isNormal_champernowne_occ_cw_eq (U : BitString) (hU : U ≠ []) (M : ℕ) :
    isNormal_champernowne_occ U (isNormal_champernowne_cw M) =
      isNormal_champernowne_O U (isNormal_champernowne_Lam M + 1 - U.length) := by
  classical
  have hlen := isNormal_champernowne_cw_length M
  rw [isNormal_champernowne_aux_A_occ_eq_card, hlen]
  unfold isNormal_champernowne_O
  have hk : 1 ≤ U.length := List.length_pos_iff.mpr hU
  refine Finset.card_nbij' (fun m => m - U.length) (fun p => p + U.length) ?_ ?_ ?_ ?_
  · intro m hm
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hm ⊢
    obtain ⟨hm1, hm2⟩ := hm
    have hpre := isNormal_champernowne_cw_prefix M m (by omega)
    rw [← hpre] at hm2
    obtain ⟨hkm, hocc⟩ := (isNormal_champernowne_aux_A_suffix_cantorPrefix _ _ _).mp hm2
    exact ⟨by omega, hocc⟩
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hp ⊢
    obtain ⟨hp1, hp2⟩ := hp
    refine ⟨by omega, ?_⟩
    have hpre := isNormal_champernowne_cw_prefix M (p + U.length) (by omega)
    rw [← hpre]
    refine (isNormal_champernowne_aux_A_suffix_cantorPrefix _ _ _).mpr ⟨by omega, ?_⟩
    simpa using hp2
  · intro m hm
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hm
    obtain ⟨hm1, hm2⟩ := hm
    have hpre := isNormal_champernowne_cw_prefix M m (by omega)
    rw [← hpre] at hm2
    obtain ⟨hkm, _⟩ := (isNormal_champernowne_aux_A_suffix_cantorPrefix _ _ _).mp hm2
    change m - U.length + U.length = m
    omega
  · intro p hp
    change p + U.length - U.length = p
    omega

/-- The empty list has no prefix ending with a nonempty `U`. -/
private lemma isNormal_champernowne_aux_B_occ_nil (U : List Bool) (hU : U ≠ []) :
    isNormal_champernowne_occ U [] = 0 := by
  simp [isNormal_champernowne_occ, hU]

/-- Appending one bit adds exactly one prefix (the whole list), which counts iff it ends with `U`.
-/
private lemma isNormal_champernowne_aux_B_occ_snoc (U L : List Bool) (b : Bool) :
    isNormal_champernowne_occ U (L ++ [b]) =
      isNormal_champernowne_occ U L + (if U <:+ L ++ [b] then 1 else 0) := by
  unfold isNormal_champernowne_occ
  simp only [List.inits_append, List.filter_append, List.length_append]
  congr 1
  by_cases h : U <:+ L ++ [b] <;> simp [h]

/-- A suffix of `l₁ ++ P` that is no longer than `P` is a suffix of `P`. -/
private lemma isNormal_champernowne_aux_B_suffix_of_append (U l₁ P : List Bool)
    (h : U <:+ l₁ ++ P) (hlen : U.length ≤ P.length) : U <:+ P := by
  obtain ⟨s, hs⟩ := h
  rcases List.append_eq_append_iff.mp hs with ⟨a', _, hP⟩ | ⟨c', _, hP⟩
  · have h0 : a' = [] := by
      have h1 := congrArg List.length hP
      simp only [List.length_append] at h1
      exact List.eq_nil_of_length_eq_zero (by omega)
    subst h0
    simp only [List.nil_append] at hP
    subst hP
    exact List.suffix_refl _
  · exact ⟨c', hP.symm⟩

/-- The strengthened concatenation bound, with the number of crossing occurrences bounded by
`min |l₂| (|U| - 1)`. -/
private lemma isNormal_champernowne_aux_B_append_aux (U : List Bool) (hU : U ≠ [])
    (l₁ l₂ : List Bool) :
    isNormal_champernowne_occ U l₁ + isNormal_champernowne_occ U l₂ ≤
        isNormal_champernowne_occ U (l₁ ++ l₂) ∧
      isNormal_champernowne_occ U (l₁ ++ l₂) ≤
        isNormal_champernowne_occ U l₁ + isNormal_champernowne_occ U l₂ +
          min l₂.length (U.length - 1) := by
  induction l₂ using List.reverseRecOn with
  | nil =>
    simp [isNormal_champernowne_aux_B_occ_nil U hU]
  | append_singleton l₂ b ih =>
    obtain ⟨ih1, ih2⟩ := ih
    rw [← List.append_assoc, isNormal_champernowne_aux_B_occ_snoc U (l₁ ++ l₂) b,
      isNormal_champernowne_aux_B_occ_snoc U l₂ b]
    have hlen : (l₂ ++ [b]).length = l₂.length + 1 := by simp
    have himp : U <:+ l₂ ++ [b] → U <:+ l₁ ++ l₂ ++ [b] := by
      intro h
      rw [List.append_assoc]
      exact h.trans (List.suffix_append l₁ (l₂ ++ [b]))
    rw [hlen]
    by_cases h1 : U <:+ l₁ ++ l₂ ++ [b]
    · by_cases h2 : U <:+ l₂ ++ [b]
      · simp only [h1, h2, ↓reduceIte]
        refine ⟨by omega, by omega⟩
      · have hlt : l₂.length + 1 < U.length := by
          by_contra hge
          apply h2
          refine isNormal_champernowne_aux_B_suffix_of_append U l₁ (l₂ ++ [b])
            (by rwa [← List.append_assoc]) (by rw [hlen]; omega)
        simp only [h1, h2, ↓reduceIte]
        refine ⟨by omega, by omega⟩
    · have h2 : ¬ U <:+ l₂ ++ [b] := fun h => h1 (himp h)
      simp only [h1, h2, ↓reduceIte]
      refine ⟨by omega, by omega⟩

/-- `cw 0` is empty. -/
private lemma isNormal_champernowne_aux_B_cw_zero : isNormal_champernowne_cw 0 = [] := by
  simp [isNormal_champernowne_cw]

/-- `cw (M + 1)` is `cw M` followed by the binary expansion of `M + 1`. -/
private lemma isNormal_champernowne_aux_B_cw_succ (M : ℕ) :
    isNormal_champernowne_cw (M + 1) = isNormal_champernowne_cw M ++ msbBits (M + 1) := by
  simp [isNormal_champernowne_cw, List.range_succ]

/-- Step 4 of the proof of `isNormal_champernowne`: occurrences in a concatenation
`l₁ ++ l₂` are those of `l₁`, those of `l₂`, and at most `|U| - 1` crossing ones. -/
private lemma isNormal_champernowne_occ_append (U : BitString) (hU : U ≠ [])
    (l₁ l₂ : List Bool) :
    isNormal_champernowne_occ U l₁ + isNormal_champernowne_occ U l₂ ≤
        isNormal_champernowne_occ U (l₁ ++ l₂) ∧
      isNormal_champernowne_occ U (l₁ ++ l₂) ≤
        isNormal_champernowne_occ U l₁ + isNormal_champernowne_occ U l₂ + (U.length - 1) := by
  obtain ⟨h1, h2⟩ := isNormal_champernowne_aux_B_append_aux U hU l₁ l₂
  refine ⟨h1, ?_⟩
  have := min_le_right l₂.length (U.length - 1)
  omega

/-- Step 5 of the proof of `isNormal_champernowne`: occurrences in `cw M` are the sum
of the occurrences in the blocks `msbBits 1, …, msbBits M`, up to `(|U| - 1) M` crossing ones. -/
private lemma isNormal_champernowne_occ_cw_bounds (U : BitString) (hU : U ≠ []) (M : ℕ) :
    ∑ x ∈ Finset.Icc 1 M, isNormal_champernowne_occ U (msbBits x) ≤
        isNormal_champernowne_occ U (isNormal_champernowne_cw M) ∧
      isNormal_champernowne_occ U (isNormal_champernowne_cw M) ≤
        ∑ x ∈ Finset.Icc 1 M, isNormal_champernowne_occ U (msbBits x) + (U.length - 1) * M := by
  induction M with
  | zero =>
    simp [isNormal_champernowne_aux_B_cw_zero, isNormal_champernowne_aux_B_occ_nil U hU]
  | succ M ih =>
    obtain ⟨ih1, ih2⟩ := ih
    obtain ⟨h1, h2⟩ := isNormal_champernowne_occ_append U hU
      (isNormal_champernowne_cw M) (msbBits (M + 1))
    rw [isNormal_champernowne_aux_B_cw_succ, Finset.sum_Icc_succ_top (by omega), Nat.mul_succ]
    refine ⟨by omega, by omega⟩

private lemma isNormal_champernowne_aux_C_msbBits_succ (y : ℕ) (hy : 0 < y) :
    msbBits y = msbBits (y / 2) ++ [decide (y % 2 = 1)] := by
  unfold msbBits
  rcases Nat.even_or_odd' y with ⟨n, hn | hn⟩
  · have hn0 : n ≠ 0 := by omega
    subst hn
    have h2 : 2 * n / 2 = n := by omega
    have h3 : 2 * n % 2 = 0 := by omega
    rw [h2, Nat.bit0_bits n hn0]
    simp [h3]
  · subst hn
    have h2 : (2 * n + 1) / 2 = n := by omega
    have h3 : (2 * n + 1) % 2 = 1 := by omega
    rw [h2, Nat.bit1_bits]
    simp [h3]

private lemma isNormal_champernowne_aux_C_length_msbBits (y : ℕ) :
    (msbBits y).length = Nat.size y := by
  simp [msbBits, Nat.size_eq_bits_len]

private lemma isNormal_champernowne_aux_C_size_succ (y : ℕ) (hy : 0 < y) :
    Nat.size y = Nat.size (y / 2) + 1 := by
  have h := congrArg List.length (isNormal_champernowne_aux_C_msbBits_succ y hy)
  simpa [isNormal_champernowne_aux_C_length_msbBits] using h

private lemma isNormal_champernowne_aux_C_occ_concat (U L : List Bool) (b : Bool) :
    isNormal_champernowne_occ U (L ++ [b]) =
      isNormal_champernowne_occ U L + (if U <:+ L ++ [b] then 1 else 0) := by
  unfold isNormal_champernowne_occ
  rw [List.inits_append]
  simp [List.filter_append]
  split_ifs <;> simp_all

open Classical in
/-- Step 6 of the proof of `isNormal_champernowne`: the number of occurrences of `U` in
`msbBits x` is the number of `t ≤ size x` such that `U` is a suffix of `msbBits (x >>> t)` (the
prefix of `msbBits x` obtained by deleting its last `t` bits). -/
private lemma isNormal_champernowne_occ_msbBits (U : BitString) (x : ℕ) :
    isNormal_champernowne_occ U (msbBits x) =
      ((Finset.range (Nat.size x + 1)).filter fun t => U <:+ msbBits (x >>> t)).card := by
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · by_cases hU : U = [] <;> simp [isNormal_champernowne_occ, msbBits, hU]
    · have h1 := isNormal_champernowne_aux_C_msbBits_succ x hx
      have h2 := ih (x / 2) (Nat.div_lt_self hx (by norm_num))
      have h3 := isNormal_champernowne_aux_C_size_succ x hx
      have hcat : isNormal_champernowne_occ U (msbBits x) =
          isNormal_champernowne_occ U (msbBits (x / 2)) +
            (if U <:+ msbBits x then 1 else 0) := by
        conv_lhs => rw [h1]
        rw [isNormal_champernowne_aux_C_occ_concat, ← h1]
      rw [hcat, h2, Finset.card_filter, Finset.card_filter, h3]
      conv_rhs => rw [Finset.sum_range_succ']
      simp only [Nat.shiftRight_succ_inside, Nat.shiftRight_zero]

/-- Step 7 of the proof of `isNormal_champernowne`: `U` is a suffix of `msbBits y` iff
`y` has at least `|U|` bits and its last `|U|` bits, read as a number, are `v` (the value of `U`).
-/
private lemma isNormal_champernowne_suffix_iff (U : BitString) :
    ∃ v : ℕ, v < 2 ^ U.length ∧
      ∀ y : ℕ, (U <:+ msbBits y ↔ U.length ≤ Nat.size y ∧ y % 2 ^ U.length = v) := by
  induction U using List.reverseRecOn with
  | nil =>
    refine ⟨0, by simp, fun y => ?_⟩
    simp [Nat.mod_one]
  | append_singleton U' b ih =>
    obtain ⟨v, hv, h⟩ := ih
    have hb : b.toNat ≤ 1 := by cases b <;> simp
    refine ⟨2 * v + b.toNat, ?_, fun y => ?_⟩
    · rw [List.length_append, List.length_singleton, pow_succ]
      omega
    · rcases Nat.eq_zero_or_pos y with rfl | hy
      · simp [msbBits]
      · have h1 := isNormal_champernowne_aux_C_msbBits_succ y hy
        have h3 := isNormal_champernowne_aux_C_size_succ y hy
        have hy2 := h (y / 2)
        have hmod : y % 2 ^ (U'.length + 1) = y % 2 + 2 * ((y / 2) % 2 ^ U'.length) := by
          rw [pow_succ', Nat.mod_mul]
        have hsuf : (U' ++ [b] <:+ msbBits (y / 2) ++ [decide (y % 2 = 1)]) ↔
            (b = decide (y % 2 = 1) ∧ U' <:+ msbBits (y / 2)) := by
          rw [List.suffix_concat_iff]
          simp
        rw [h1, hsuf, hy2, List.length_append, List.length_singleton, h3, hmod]
        have hy' : y % 2 < 2 := Nat.mod_lt _ (by norm_num)
        cases b <;> by_cases hc : y % 2 = 1 <;> simp [hc] <;> omega

/-- Auxiliary for `isNormal_champernowne_layer`: shifting by whole periods does not change
the residue `⌊x / 2^t⌋ mod 2^k` inside one period. -/
private lemma isNormal_champernowne_aux_D_div_mod (t k q r : ℕ) (hr : r < 2 ^ (t + k)) :
    ((2 ^ (t + k) * q + r) >>> t) % 2 ^ k = r / 2 ^ t := by
  have hpos : 0 < 2 ^ t := Nat.two_pow_pos t
  have h1 : 2 ^ (t + k) * q = 2 ^ t * (2 ^ k * q) := by rw [pow_add]; ring
  have h2 : (2 ^ (t + k) * q + r) >>> t = 2 ^ k * q + r / 2 ^ t := by
    rw [Nat.shiftRight_eq_div_pow, h1, Nat.mul_add_div hpos]
  have h3 : r / 2 ^ t < 2 ^ k := by
    rw [Nat.div_lt_iff_lt_mul hpos]
    calc r < 2 ^ (t + k) := hr
      _ = 2 ^ k * 2 ^ t := by rw [pow_add, mul_comm]
  rw [h2, Nat.mul_add_mod, Nat.mod_eq_of_lt h3]

/-- Auxiliary for `isNormal_champernowne_layer`: one full period `[P q, P (q + 1))`, with
`P = 2^(t+k)`, contains exactly `2^t` numbers `x` with `⌊x / 2^t⌋ ≡ v (mod 2^k)`. -/
private lemma isNormal_champernowne_aux_D_block (t k v q : ℕ) (hv : v < 2 ^ k) :
    ((Finset.Ico (2 ^ (t + k) * q) (2 ^ (t + k) * (q + 1))).filter
        fun x => (x >>> t) % 2 ^ k = v).card = 2 ^ t := by
  have hpos : 0 < 2 ^ t := Nat.two_pow_pos t
  have hP : 2 ^ (t + k) * (q + 1) = 2 ^ (t + k) * q + 2 ^ (t + k) := by ring
  have hvP : v * 2 ^ t + 2 ^ t ≤ 2 ^ (t + k) := by
    calc v * 2 ^ t + 2 ^ t = (v + 1) * 2 ^ t := by ring
      _ ≤ 2 ^ k * 2 ^ t := Nat.mul_le_mul_right _ hv
      _ = 2 ^ (t + k) := by rw [pow_add, mul_comm]
  have hfilter : ((Finset.Ico (2 ^ (t + k) * q) (2 ^ (t + k) * (q + 1))).filter
      fun x => (x >>> t) % 2 ^ k = v) =
      Finset.Ico (2 ^ (t + k) * q + v * 2 ^ t) (2 ^ (t + k) * q + v * 2 ^ t + 2 ^ t) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Ico]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      obtain ⟨r, rfl⟩ : ∃ r, x = 2 ^ (t + k) * q + r := ⟨x - 2 ^ (t + k) * q, by omega⟩
      have hr : r < 2 ^ (t + k) := by omega
      rw [isNormal_champernowne_aux_D_div_mod t k q r hr] at h3
      have h4 : v * 2 ^ t ≤ r := (Nat.le_div_iff_mul_le hpos).mp h3.ge
      have h5 : r < (v + 1) * 2 ^ t := (Nat.div_lt_iff_lt_mul hpos).mp (by omega)
      have h6 : (v + 1) * 2 ^ t = v * 2 ^ t + 2 ^ t := by ring
      omega
    · rintro ⟨h1, h2⟩
      obtain ⟨r, rfl⟩ : ∃ r, x = 2 ^ (t + k) * q + r := ⟨x - 2 ^ (t + k) * q, by omega⟩
      have hr : r < 2 ^ (t + k) := by omega
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      rw [isNormal_champernowne_aux_D_div_mod t k q r hr]
      have h6 : (v + 1) * 2 ^ t = v * 2 ^ t + 2 ^ t := by ring
      exact Nat.div_eq_of_lt_le (by omega) (by omega)
  rw [hfilter, Nat.card_Ico]
  omega

/-- Auxiliary for `isNormal_champernowne_layer`: splitting the count at `a ≤ b`. -/
private lemma isNormal_champernowne_aux_D_split (t k v : ℕ) {a b : ℕ} (hab : a ≤ b) :
    ((Finset.range b).filter fun x => (x >>> t) % 2 ^ k = v).card =
      ((Finset.range a).filter fun x => (x >>> t) % 2 ^ k = v).card +
        ((Finset.Ico a b).filter fun x => (x >>> t) % 2 ^ k = v).card := by
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter]
  exact (Finset.sum_range_add_sum_Ico _ hab).symm

/-- Auxiliary for `isNormal_champernowne_layer`: the count up to `b` is monotone. -/
private lemma isNormal_champernowne_aux_D_mono (t k v : ℕ) {b b' : ℕ} (h : b ≤ b') :
    ((Finset.range b).filter fun x => (x >>> t) % 2 ^ k = v).card ≤
      ((Finset.range b').filter fun x => (x >>> t) % 2 ^ k = v).card :=
  Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_subset_range.mpr h))

/-- Auxiliary for `isNormal_champernowne_layer`: the count up to `2^(t+k) q` is `2^t q`. -/
private lemma isNormal_champernowne_aux_D_mul (t k v q : ℕ) (hv : v < 2 ^ k) :
    ((Finset.range (2 ^ (t + k) * q)).filter fun x => (x >>> t) % 2 ^ k = v).card = 2 ^ t * q := by
  induction q with
  | zero => simp
  | succ q ih =>
    have hle : 2 ^ (t + k) * q ≤ 2 ^ (t + k) * (q + 1) :=
      Nat.mul_le_mul_left _ (Nat.le_succ q)
    rw [isNormal_champernowne_aux_D_split t k v hle, ih,
      isNormal_champernowne_aux_D_block t k v q hv]
    ring

/-- Auxiliary for `isNormal_champernowne_layer`: `2^k` times the count up to `b` is `b` up
to the period `2^(t+k)`. -/
private lemma isNormal_champernowne_aux_D_err (t k v b : ℕ) (hv : v < 2 ^ k) :
    2 ^ k * ((Finset.range b).filter fun x => (x >>> t) % 2 ^ k = v).card ≤ b + 2 ^ (t + k) ∧
      b ≤ 2 ^ k * ((Finset.range b).filter fun x => (x >>> t) % 2 ^ k = v).card + 2 ^ (t + k) := by
  have hPpos : 0 < 2 ^ (t + k) := Nat.two_pow_pos _
  have hb1 : 2 ^ (t + k) * (b / 2 ^ (t + k)) ≤ b := Nat.mul_div_le b _
  have hb2 : b < 2 ^ (t + k) * (b / 2 ^ (t + k)) + 2 ^ (t + k) := by
    have h1 := Nat.div_add_mod b (2 ^ (t + k))
    have h2 := Nat.mod_lt b hPpos
    omega
  generalize b / 2 ^ (t + k) = q at hb1 hb2
  have hlo := isNormal_champernowne_aux_D_mono t k v hb1
  have hb3 : b ≤ 2 ^ (t + k) * (q + 1) := by
    have : 2 ^ (t + k) * (q + 1) = 2 ^ (t + k) * q + 2 ^ (t + k) := by ring
    omega
  have hhi := isNormal_champernowne_aux_D_mono t k v hb3
  rw [isNormal_champernowne_aux_D_mul t k v q hv] at hlo
  rw [isNormal_champernowne_aux_D_mul t k v (q + 1) hv] at hhi
  generalize ((Finset.range b).filter fun x => (x >>> t) % 2 ^ k = v).card = F at hlo hhi ⊢
  have h1 : 2 ^ (t + k) * q ≤ 2 ^ k * F := by
    calc 2 ^ (t + k) * q = 2 ^ k * (2 ^ t * q) := by rw [pow_add]; ring
      _ ≤ 2 ^ k * F := Nat.mul_le_mul_left _ hlo
  have h2 : 2 ^ k * F ≤ 2 ^ (t + k) * q + 2 ^ (t + k) := by
    calc 2 ^ k * F ≤ 2 ^ k * (2 ^ t * (q + 1)) := Nat.mul_le_mul_left _ hhi
      _ = 2 ^ (t + k) * q + 2 ^ (t + k) := by rw [pow_add]; ring
  constructor <;> omega

open Classical in
/-- Step 8 of the proof of `isNormal_champernowne`: one layer. Among the numbers
`2^(t+k-1) ≤ x ≤ M`, a fraction `2^(-k)` of them satisfy `⌊x / 2^t⌋ ≡ v (mod 2^k)`, up to an
error of `2^(t+k+1)` in the count scaled by `2^k`. -/
private lemma isNormal_champernowne_layer (k v t M : ℕ) (hv : v < 2 ^ k) :
    |(2 : ℤ) ^ k *
        (((Finset.Icc 1 M).filter fun x => 2 ^ (t + k - 1) ≤ x ∧ (x >>> t) % 2 ^ k = v).card : ℤ) -
      (((Finset.Icc 1 M).filter fun x => 2 ^ (t + k - 1) ≤ x).card : ℤ)| ≤ 2 ^ (t + k + 1) := by
  have ha : 1 ≤ 2 ^ (t + k - 1) := Nat.one_le_two_pow
  have hP : (2 : ℤ) ^ (t + k + 1) = 2 * 2 ^ (t + k) := by ring
  have hAeq : (Finset.Icc 1 M).filter (fun x => 2 ^ (t + k - 1) ≤ x) =
      Finset.Ico (2 ^ (t + k - 1)) (M + 1) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico]
    omega
  have hCeq : (Finset.Icc 1 M).filter (fun x => 2 ^ (t + k - 1) ≤ x ∧ (x >>> t) % 2 ^ k = v) =
      (Finset.Ico (2 ^ (t + k - 1)) (M + 1)).filter (fun x => (x >>> t) % 2 ^ k = v) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨⟨h3, by omega⟩, h4⟩
    · rintro ⟨⟨h1, h2⟩, h4⟩
      exact ⟨⟨by omega, by omega⟩, h1, h4⟩
  rw [hAeq, hCeq]
  by_cases haM : 2 ^ (t + k - 1) ≤ M + 1
  · have hsplit := isNormal_champernowne_aux_D_split t k v haM
    obtain ⟨e1, e2⟩ := isNormal_champernowne_aux_D_err t k v (M + 1) hv
    obtain ⟨e3, e4⟩ := isNormal_champernowne_aux_D_err t k v (2 ^ (t + k - 1)) hv
    rw [Nat.card_Ico]
    generalize ((Finset.Ico (2 ^ (t + k - 1)) (M + 1)).filter
      fun x => (x >>> t) % 2 ^ k = v).card = C at hsplit ⊢
    generalize ((Finset.range (M + 1)).filter fun x => (x >>> t) % 2 ^ k = v).card = F1
      at hsplit e1 e2
    generalize ((Finset.range (2 ^ (t + k - 1))).filter
      fun x => (x >>> t) % 2 ^ k = v).card = F2 at hsplit e3 e4
    have hmul : 2 ^ k * F1 = 2 ^ k * F2 + 2 ^ k * C := by rw [hsplit]; ring
    obtain ⟨A, hA⟩ : ∃ A, A + 2 ^ (t + k - 1) = M + 1 := ⟨M + 1 - 2 ^ (t + k - 1), by omega⟩
    have hA' : M + 1 - 2 ^ (t + k - 1) = A := by omega
    rw [hA']
    have L1 : A ≤ 2 ^ k * C + 2 * 2 ^ (t + k) := by omega
    have L2 : 2 ^ k * C ≤ A + 2 * 2 ^ (t + k) := by omega
    have L1' : (A : ℤ) ≤ 2 ^ k * (C : ℤ) + 2 * 2 ^ (t + k) := by exact_mod_cast L1
    have L2' : 2 ^ k * (C : ℤ) ≤ (A : ℤ) + 2 * 2 ^ (t + k) := by exact_mod_cast L2
    rw [abs_le, hP]
    constructor <;> linarith
  · have hlt : M + 1 ≤ 2 ^ (t + k - 1) := (not_le.mp haM).le
    rw [Finset.Ico_eq_empty_of_le hlt]
    simp

/-- `k ≤ size (x >>> t)` iff `2^(t+k-1) ≤ x` (for `k ≥ 1`). -/
private lemma isNormal_champernowne_aux_E_size_iff (k t x : ℕ) (hk : 1 ≤ k) :
    k ≤ Nat.size (x >>> t) ↔ 2 ^ (t + k - 1) ≤ x := by
  have h1 : k ≤ Nat.size (x >>> t) ↔ 2 ^ (k - 1) ≤ x >>> t := by
    rw [← Nat.lt_size]; omega
  rw [h1, Nat.shiftRight_eq_div_pow, Nat.le_div_iff_mul_le (by positivity),
    ← pow_add]
  have h2 : k - 1 + t = t + k - 1 := by omega
  rw [h2]

/-- A geometric-sum bound. -/
private lemma isNormal_champernowne_aux_E_geom (k n : ℕ) :
    ∑ t ∈ Finset.range (n + 1), (2 : ℤ) ^ (t + k + 1) ≤ 2 ^ (n + k + 2) := by
  induction n with
  | zero => simp [pow_succ]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h1 : (2 : ℤ) ^ (n + 1 + k + 1) = 2 ^ (n + k + 2) := by
      congr 1; omega
    have h2 : (2 : ℤ) ^ (n + 1 + k + 2) = 2 * 2 ^ (n + k + 2) := by
      rw [show n + 1 + k + 2 = (n + k + 2) + 1 by omega, pow_succ]; ring
    rw [h1, h2]
    linarith

open Classical in
/-- Re-indexing of the inner count of `step9`: for `x ≤ M` it is a sum over the common range
`t ≤ size M` of an indicator. -/
private lemma isNormal_champernowne_aux_E_inner1 (k v M x : ℕ) (hk : 1 ≤ k) (hx : x ≤ M) :
    (((Finset.range (Nat.size x + 1)).filter
        fun t => k ≤ Nat.size (x >>> t) ∧ (x >>> t) % 2 ^ k = v).card : ℤ) =
      ∑ t ∈ Finset.range (Nat.size M + 1),
        (if 2 ^ (t + k - 1) ≤ x ∧ (x >>> t) % 2 ^ k = v then (1 : ℤ) else 0) := by
  rw [Finset.card_filter]
  push_cast
  have hsub : Finset.range (Nat.size x + 1) ⊆ Finset.range (Nat.size M + 1) := by
    intro t ht
    simp only [Finset.mem_range] at ht ⊢
    have := Nat.size_le_size hx
    omega
  have hcongr : ∑ t ∈ Finset.range (Nat.size x + 1),
        (if k ≤ Nat.size (x >>> t) ∧ (x >>> t) % 2 ^ k = v then (1 : ℤ) else 0) =
      ∑ t ∈ Finset.range (Nat.size x + 1),
        (if 2 ^ (t + k - 1) ≤ x ∧ (x >>> t) % 2 ^ k = v then (1 : ℤ) else 0) := by
    apply Finset.sum_congr rfl
    intro t _
    simp only [isNormal_champernowne_aux_E_size_iff k t x hk]
  rw [hcongr]
  apply Finset.sum_subset hsub
  intro t _ htn
  simp only [Finset.mem_range, not_lt] at htn
  have hnot : ¬ 2 ^ (t + k - 1) ≤ x := by
    intro h
    have h3 : t + k - 1 < Nat.size x := Nat.lt_size.mpr h
    omega
  simp [hnot]

open Classical in
/-- Re-indexing of the second sum of `step9`: `size x + 1 - k` counts the layers `t` with
`2^(t+k-1) ≤ x`. -/
private lemma isNormal_champernowne_aux_E_inner2 (k M x : ℕ) (hk : 1 ≤ k) (hx : x ≤ M) :
    ((Nat.size x + 1 - k : ℕ) : ℤ) =
      ∑ t ∈ Finset.range (Nat.size M + 1), (if 2 ^ (t + k - 1) ≤ x then (1 : ℤ) else 0) := by
  rw [Finset.sum_boole]
  have hfilt : (Finset.range (Nat.size M + 1)).filter (fun t => 2 ^ (t + k - 1) ≤ x) =
      Finset.range (Nat.size x + 1 - k) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨_, h⟩
      have h3 : t + k - 1 < Nat.size x := Nat.lt_size.mpr h
      omega
    · intro h
      have hsz := Nat.size_le_size hx
      refine ⟨by omega, ?_⟩
      apply Nat.lt_size.mp
      omega
  rw [hfilt, Finset.card_range]

open Classical in
/-- Step 9 of the proof of `isNormal_champernowne`: the sum of the layers.  The number
of pairs `(x, t)` with `x ≤ M`, `t ≤ size x`, `k ≤ size (x >>> t)` and `(x >>> t) % 2^k = v`, scaled
by `2^k`, differs from `∑_{x ≤ M} (size x + 1 - k)` by at most `2^(k+3) M`. -/
private lemma isNormal_champernowne_discrepancy (k v M : ℕ) (hk : 1 ≤ k) (hv : v < 2 ^ k) :
    |(2 : ℤ) ^ k * ∑ x ∈ Finset.Icc 1 M,
          (((Finset.range (Nat.size x + 1)).filter
              fun t => k ≤ Nat.size (x >>> t) ∧ (x >>> t) % 2 ^ k = v).card : ℤ) -
        ∑ x ∈ Finset.Icc 1 M, ((Nat.size x + 1 - k : ℕ) : ℤ)| ≤ 2 ^ (k + 3) * M := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp
  have e1 : ∑ x ∈ Finset.Icc 1 M,
      (((Finset.range (Nat.size x + 1)).filter
          fun t => k ≤ Nat.size (x >>> t) ∧ (x >>> t) % 2 ^ k = v).card : ℤ) =
      ∑ t ∈ Finset.range (Nat.size M + 1),
        (((Finset.Icc 1 M).filter
          fun x => 2 ^ (t + k - 1) ≤ x ∧ (x >>> t) % 2 ^ k = v).card : ℤ) := by
    rw [Finset.sum_congr rfl (fun x hx =>
      isNormal_champernowne_aux_E_inner1 k v M x hk (Finset.mem_Icc.mp hx).2)]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    rw [Finset.card_filter]
    push_cast
    rfl
  have e2 : ∑ x ∈ Finset.Icc 1 M, ((Nat.size x + 1 - k : ℕ) : ℤ) =
      ∑ t ∈ Finset.range (Nat.size M + 1),
        (((Finset.Icc 1 M).filter fun x => 2 ^ (t + k - 1) ≤ x).card : ℤ) := by
    rw [Finset.sum_congr rfl (fun x hx =>
      isNormal_champernowne_aux_E_inner2 k M x hk (Finset.mem_Icc.mp hx).2)]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    rw [Finset.card_filter]
    push_cast
    rfl
  rw [e1, e2, Finset.mul_sum, ← Finset.sum_sub_distrib]
  have hsz : 1 ≤ Nat.size M := Nat.size_pos.mpr hM
  have hpow : 2 ^ (Nat.size M - 1) ≤ M := Nat.lt_size.mp (by omega)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum (fun t _ => isNormal_champernowne_layer k v t M hv)).trans ?_
  refine (isNormal_champernowne_aux_E_geom k (Nat.size M)).trans ?_
  have h2 : Nat.size M + k + 2 = (Nat.size M - 1) + (k + 3) := by omega
  rw [h2, pow_add]
  have h3 : ((2 : ℤ) ^ (Nat.size M - 1)) ≤ M := by exact_mod_cast hpow
  nlinarith [pow_pos (show (0 : ℤ) < 2 by norm_num) (k + 3)]

/-- Auxiliary for steps 10-12: `Lam 0 = 0`. -/
private lemma isNormal_champernowne_aux_F_Lam_zero : isNormal_champernowne_Lam 0 = 0 := by
  simp [isNormal_champernowne_Lam]

/-- Auxiliary for steps 10-12: `Lam (M + 1) = Lam M + size (M + 1)`. -/
private lemma isNormal_champernowne_aux_F_Lam_succ (M : ℕ) :
    isNormal_champernowne_Lam (M + 1) = isNormal_champernowne_Lam M + Nat.size (M + 1) := by
  unfold isNormal_champernowne_Lam
  exact Finset.sum_Icc_succ_top (by omega) _

/-- Auxiliary for steps 10-12: `Lam` is monotone. -/
private lemma isNormal_champernowne_aux_F_Lam_mono {a b : ℕ} (h : a ≤ b) :
    isNormal_champernowne_Lam a ≤ isNormal_champernowne_Lam b := by
  induction b, h using Nat.le_induction with
  | base => exact le_rfl
  | succ b hb ih => rw [isNormal_champernowne_aux_F_Lam_succ]; omega

/-- Step 10 of the proof of `isNormal_champernowne`: `Lam M / M → ∞`. -/
private lemma isNormal_champernowne_lam_growth (c : ℕ) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → c * (M + 1) ≤ isNormal_champernowne_Lam M := by
  refine ⟨2 ^ (2 * c + 1), fun M hM => ?_⟩
  -- every `x ∈ [2^r, M]` has at least `r + 1` bits
  have hr1 : 1 ≤ 2 ^ (2 * c) := Nat.one_le_two_pow
  have hpow : 2 ^ (2 * c + 1) = 2 * 2 ^ (2 * c) := by rw [pow_succ]; ring
  have hsub : (Finset.Icc (2 ^ (2 * c)) M) ⊆ Finset.Icc 1 M := by
    intro x hx
    simp only [Finset.mem_Icc] at hx ⊢
    omega
  have hge : ∀ x ∈ Finset.Icc (2 ^ (2 * c)) M, 2 * c + 1 ≤ Nat.size x := by
    intro x hx
    simp only [Finset.mem_Icc] at hx
    by_contra hlt
    have h1 : Nat.size x ≤ 2 * c := by omega
    have h2 := Nat.size_le.mp h1
    omega
  have h1 : (2 * c + 1) * (M + 1 - 2 ^ (2 * c)) ≤ isNormal_champernowne_Lam M := by
    calc (2 * c + 1) * (M + 1 - 2 ^ (2 * c))
        = ∑ x ∈ Finset.Icc (2 ^ (2 * c)) M, (2 * c + 1) := by
          rw [Finset.sum_const, Nat.card_Icc, smul_eq_mul, mul_comm]
      _ ≤ ∑ x ∈ Finset.Icc (2 ^ (2 * c)) M, Nat.size x := Finset.sum_le_sum hge
      _ ≤ ∑ x ∈ Finset.Icc 1 M, Nat.size x := Finset.sum_le_sum_of_subset hsub
  have h2a : M + 1 ≤ 2 * (M + 1 - 2 ^ (2 * c)) := by omega
  calc c * (M + 1) ≤ c * (2 * (M + 1 - 2 ^ (2 * c))) := Nat.mul_le_mul_left c h2a
    _ = (2 * c) * (M + 1 - 2 ^ (2 * c)) := by ring
    _ ≤ (2 * c + 1) * (M + 1 - 2 ^ (2 * c)) := Nat.mul_le_mul_right _ (by omega)
    _ ≤ isNormal_champernowne_Lam M := h1

/-- Step 11 of the proof of `isNormal_champernowne`: every `N` lies in some block. -/
private lemma isNormal_champernowne_exists_block (N : ℕ) :
    ∃ M : ℕ, isNormal_champernowne_Lam M ≤ N ∧ N < isNormal_champernowne_Lam (M + 1) := by
  induction N with
  | zero =>
    refine ⟨0, by simp [isNormal_champernowne_aux_F_Lam_zero], ?_⟩
    rw [isNormal_champernowne_aux_F_Lam_succ, isNormal_champernowne_aux_F_Lam_zero]
    have : 1 ≤ Nat.size (0 + 1) := Nat.size_pos.mpr (Nat.succ_pos 0)
    omega
  | succ N ih =>
    obtain ⟨M, h1, h2⟩ := ih
    by_cases h : N + 1 < isNormal_champernowne_Lam (M + 1)
    · exact ⟨M, by omega, h⟩
    · refine ⟨M + 1, by omega, ?_⟩
      rw [isNormal_champernowne_aux_F_Lam_succ (M + 1)]
      have : 1 ≤ Nat.size (M + 1 + 1) := Nat.size_pos.mpr (Nat.succ_pos _)
      omega

/-- Step 12 of the proof of `isNormal_champernowne`: the final `ε`-argument.  If
`|2^k O(N) - N| ≤ C (M + 1)` whenever `Lam M ≤ N < Lam (M + 1)`, then the frequency of `U` tends
to `2^(-k)`. -/
private lemma isNormal_champernowne_final (U : BitString) (C : ℕ)
    (hC : ∀ M N : ℕ, isNormal_champernowne_Lam M ≤ N → N < isNormal_champernowne_Lam (M + 1) →
      |(2 : ℤ) ^ U.length * (isNormal_champernowne_O U N : ℤ) - (N : ℤ)| ≤ (C : ℤ) * (M + 1)) :
    Tendsto (occurrenceFreq U champernowne) atTop (𝓝 ((2 : ℝ)⁻¹ ^ U.length)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨c, hc⟩ := exists_nat_gt ((C : ℝ) / ε)
  have hcpos : (0 : ℝ) < c := lt_of_le_of_lt (by positivity) hc
  have hCc : (C : ℝ) < c * ε := by
    rw [div_lt_iff₀ hε] at hc
    linarith
  obtain ⟨M₀, hM₀⟩ := isNormal_champernowne_lam_growth c
  refine ⟨isNormal_champernowne_Lam M₀ + 1, fun N hN => ?_⟩
  obtain ⟨M, hM1, hM2⟩ := isNormal_champernowne_exists_block N
  have hMM₀ : M₀ ≤ M := by
    by_contra hlt
    have := isNormal_champernowne_aux_F_Lam_mono (show M + 1 ≤ M₀ by omega)
    omega
  have hcM : c * (M + 1) ≤ N := le_trans (hM₀ M hMM₀) hM1
  have hbound := hC M N hM1 hM2
  have hb : |(2 : ℝ) ^ U.length * (isNormal_champernowne_O U N : ℝ) - (N : ℝ)|
      ≤ (C : ℝ) * ((M : ℝ) + 1) := by
    exact_mod_cast hbound
  have hcMr : (c : ℝ) * ((M : ℝ) + 1) ≤ (N : ℝ) := by exact_mod_cast hcM
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : 0 < N := by omega
    exact_mod_cast this
  have hA1 : (1 : ℝ) ≤ (2 : ℝ) ^ U.length := one_le_pow₀ (by norm_num)
  have hApos : (0 : ℝ) < (2 : ℝ) ^ U.length := lt_of_lt_of_le one_pos hA1
  have hfreq : occurrenceFreq U champernowne N
      = (isNormal_champernowne_O U N : ℝ) / (N : ℝ) := rfl
  rw [hfreq, Real.dist_eq, inv_pow]
  have key : (isNormal_champernowne_O U N : ℝ) / (N : ℝ) - ((2 : ℝ) ^ U.length)⁻¹
      = ((2 : ℝ) ^ U.length * (isNormal_champernowne_O U N : ℝ) - (N : ℝ))
        / ((2 : ℝ) ^ U.length * (N : ℝ)) := by
    field_simp
  rw [key, abs_div, abs_of_pos (mul_pos hApos hNpos), div_lt_iff₀ (mul_pos hApos hNpos)]
  have h1 : (c : ℝ) * ((C : ℝ) * ((M : ℝ) + 1)) ≤ (C : ℝ) * (N : ℝ) := by
    calc (c : ℝ) * ((C : ℝ) * ((M : ℝ) + 1)) = (C : ℝ) * ((c : ℝ) * ((M : ℝ) + 1)) := by ring
      _ ≤ (C : ℝ) * (N : ℝ) := by gcongr
  have h2 : (C : ℝ) * (N : ℝ) < (c : ℝ) * ε * (N : ℝ) := mul_lt_mul_of_pos_right hCc hNpos
  have h3 : (c : ℝ) * ε * (N : ℝ) ≤ (c : ℝ) * ε * ((2 : ℝ) ^ U.length * (N : ℝ)) := by
    have h0 : (0 : ℝ) ≤ (c : ℝ) * ε * (N : ℝ) := by positivity
    nlinarith
  have h4 : (c : ℝ) * ((C : ℝ) * ((M : ℝ) + 1))
      < (c : ℝ) * (ε * ((2 : ℝ) ^ U.length * (N : ℝ))) := by nlinarith
  have h5 : (C : ℝ) * ((M : ℝ) + 1) < ε * ((2 : ℝ) ^ U.length * (N : ℝ)) :=
    lt_of_mul_lt_mul_left h4 hcpos.le
  exact lt_of_le_of_lt hb h5

private lemma isNormal_champernowne_aux_G_size_le (n : ℕ) : Nat.size n ≤ n :=
  Nat.size_le.mpr Nat.lt_two_pow_self

private lemma isNormal_champernowne_aux_G_Lam_succ (M : ℕ) :
    isNormal_champernowne_Lam (M + 1) = isNormal_champernowne_Lam M + Nat.size (M + 1) := by
  unfold isNormal_champernowne_Lam
  rw [Finset.sum_Icc_succ_top (by omega)]

private lemma isNormal_champernowne_aux_G_Lam_le (M j : ℕ) :
    isNormal_champernowne_Lam (M + j) ≤ isNormal_champernowne_Lam M + j * (M + j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have e : M + (j + 1) = (M + j) + 1 := by omega
    rw [e, isNormal_champernowne_aux_G_Lam_succ]
    have h := isNormal_champernowne_aux_G_size_le (M + j + 1)
    nlinarith [ih, h]

private lemma isNormal_champernowne_aux_G_Lam_ge (M j : ℕ) :
    isNormal_champernowne_Lam M + j ≤ isNormal_champernowne_Lam (M + j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have e : M + (j + 1) = (M + j) + 1 := by omega
    rw [e, isNormal_champernowne_aux_G_Lam_succ]
    have h : 0 < Nat.size (M + j + 1) := Nat.size_pos.mpr (by omega)
    omega

private lemma isNormal_champernowne_aux_G_O_mono (U : BitString) {a b : ℕ} (h : a ≤ b) :
    isNormal_champernowne_O U a ≤ isNormal_champernowne_O U b := by
  classical
  unfold isNormal_champernowne_O
  apply Finset.card_le_card
  intro p hp
  rw [Finset.mem_filter, Finset.mem_range] at hp ⊢
  exact ⟨by omega, hp.2⟩

private lemma isNormal_champernowne_aux_G_lower (U : BitString) (hU : U ≠ []) (M N : ℕ)
    (hN1 : isNormal_champernowne_Lam M ≤ N) :
    ∑ x ∈ Finset.Icc 1 M, isNormal_champernowne_occ U (msbBits x) ≤
      isNormal_champernowne_O U N := by
  have hk : 0 < U.length := List.length_pos_iff.mpr hU
  calc ∑ x ∈ Finset.Icc 1 M, isNormal_champernowne_occ U (msbBits x)
      ≤ isNormal_champernowne_occ U (isNormal_champernowne_cw M) :=
        (isNormal_champernowne_occ_cw_bounds U hU M).1
    _ = isNormal_champernowne_O U (isNormal_champernowne_Lam M + 1 - U.length) :=
        isNormal_champernowne_occ_cw_eq U hU M
    _ ≤ isNormal_champernowne_O U N :=
        isNormal_champernowne_aux_G_O_mono U (by omega)

private lemma isNormal_champernowne_aux_G_upper (U : BitString) (hU : U ≠ []) (M N : ℕ)
    (hN2 : N < isNormal_champernowne_Lam (M + 1)) :
    isNormal_champernowne_O U N ≤
      ∑ x ∈ Finset.Icc 1 (M + U.length), isNormal_champernowne_occ U (msbBits x) +
        (U.length - 1) * (M + U.length) := by
  have hk : 0 < U.length := List.length_pos_iff.mpr hU
  have h1 : isNormal_champernowne_Lam (M + 1) + (U.length - 1) ≤
      isNormal_champernowne_Lam (M + U.length) := by
    have h := isNormal_champernowne_aux_G_Lam_ge (M + 1) (U.length - 1)
    have e : M + 1 + (U.length - 1) = M + U.length := by omega
    rw [e] at h
    exact h
  calc isNormal_champernowne_O U N
      ≤ isNormal_champernowne_O U (isNormal_champernowne_Lam (M + U.length) + 1 - U.length) :=
        isNormal_champernowne_aux_G_O_mono U (by omega)
    _ = isNormal_champernowne_occ U (isNormal_champernowne_cw (M + U.length)) :=
        (isNormal_champernowne_occ_cw_eq U hU (M + U.length)).symm
    _ ≤ _ := (isNormal_champernowne_occ_cw_bounds U hU (M + U.length)).2

private lemma isNormal_champernowne_aux_G_arith (P k B M N L L₁ L' s G G' O : ℤ)
    (hP : 0 ≤ P) (hk : 1 ≤ k) (hB0 : 0 ≤ B) (hM : 0 ≤ M)
    (hL : L ≤ N) (hN : N < L₁) (hL₁ : L₁ = L + s) (hs : s ≤ M + 1)
    (hL' : L' ≤ L + k * (M + k))
    (hGlow : G ≤ O) (hGup : O ≤ G' + (k - 1) * (M + k))
    (hB1 : |P * G - L| ≤ B * M) (hB2 : |P * G' - L'| ≤ B * (M + k)) :
    |P * O - N| ≤ ((k + B + P * k) * k + B + 1) * (M + 1) := by
  rw [abs_le] at hB1 hB2 ⊢
  have h1 : P * G ≤ P * O := mul_le_mul_of_nonneg_left hGlow hP
  have h2 : P * O ≤ P * (G' + (k - 1) * (M + k)) := mul_le_mul_of_nonneg_left hGup hP
  have hE : 0 ≤ k + B + P * k := by nlinarith [mul_nonneg hP (by linarith : (0 : ℤ) ≤ k)]
  have hX : 0 ≤ (k + B + P * k) * ((k - 1) * M) :=
    mul_nonneg hE (mul_nonneg (by linarith) hM)
  have hY : 0 ≤ P * (M + k) := mul_nonneg hP (by linarith)
  have hZ : 0 ≤ (B + 1) * (M + 1) := mul_nonneg (by linarith) (by linarith)
  have hW : 0 ≤ (k + B + P * k) * k * (M + 1) :=
    mul_nonneg (mul_nonneg hE (by linarith)) (by linarith)
  have hBM : 0 ≤ B * M := mul_nonneg hB0 hM
  constructor
  · nlinarith [hB1.1, hB1.2, h1, hW, hBM]
  · nlinarith [hB2.1, hB2.2, h2, hX, hY, hZ]

/-- Step 13 of the proof of `isNormal_champernowne`: the sum of the occurrences in the
blocks `msbBits 1, …, msbBits M`, scaled by `2^|U|`, is `Lam M` up to `B M`. -/
private lemma isNormal_champernowne_blocks (U : BitString) (hU : U ≠ []) :
    ∃ B : ℕ, ∀ M : ℕ,
      |(2 : ℤ) ^ U.length *
          ((∑ x ∈ Finset.Icc 1 M, isNormal_champernowne_occ U (msbBits x) : ℕ) : ℤ) -
        (isNormal_champernowne_Lam M : ℤ)| ≤ (B : ℤ) * M := by
  classical
  have hk : 1 ≤ U.length := List.length_pos_iff.mpr hU
  obtain ⟨v, hv, hiff⟩ := isNormal_champernowne_suffix_iff U
  refine ⟨2 ^ (U.length + 3) + U.length, fun M => ?_⟩
  have h9 := isNormal_champernowne_discrepancy U.length v M hk hv
  have hocc : ∀ x : ℕ, isNormal_champernowne_occ U (msbBits x) =
      ((Finset.range (Nat.size x + 1)).filter fun t =>
        U.length ≤ Nat.size (x >>> t) ∧ (x >>> t) % 2 ^ U.length = v).card := by
    intro x
    rw [isNormal_champernowne_occ_msbBits]
    congr 1
    apply Finset.filter_congr
    intro t _
    exact hiff _
  have hS : ((∑ x ∈ Finset.Icc 1 M, isNormal_champernowne_occ U (msbBits x) : ℕ) : ℤ) =
      ∑ x ∈ Finset.Icc 1 M, (((Finset.range (Nat.size x + 1)).filter fun t =>
        U.length ≤ Nat.size (x >>> t) ∧ (x >>> t) % 2 ^ U.length = v).card : ℤ) := by
    rw [Nat.cast_sum]
    exact Finset.sum_congr rfl fun x _ => by rw [hocc x]
  have hT1 : ∑ x ∈ Finset.Icc 1 M, ((Nat.size x + 1 - U.length : ℕ) : ℤ) ≤
      (isNormal_champernowne_Lam M : ℤ) := by
    unfold isNormal_champernowne_Lam
    rw [Nat.cast_sum]
    apply Finset.sum_le_sum
    intro x _
    omega
  have hT2 : (isNormal_champernowne_Lam M : ℤ) - U.length * M ≤
      ∑ x ∈ Finset.Icc 1 M, ((Nat.size x + 1 - U.length : ℕ) : ℤ) := by
    have h : ∑ x ∈ Finset.Icc 1 M, ((Nat.size x : ℤ) - U.length) ≤
        ∑ x ∈ Finset.Icc 1 M, ((Nat.size x + 1 - U.length : ℕ) : ℤ) := by
      apply Finset.sum_le_sum
      intro x _
      omega
    rw [Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc] at h
    unfold isNormal_champernowne_Lam
    rw [Nat.cast_sum]
    simp only [Nat.add_sub_cancel, nsmul_eq_mul] at h
    linarith
  have hkM : (0 : ℤ) ≤ U.length * M := by positivity
  rw [hS]
  rw [abs_le] at h9 ⊢
  push_cast
  constructor <;> nlinarith [h9.1, h9.2, hT1, hT2, hkM]

/-- Step 14 of the proof of `isNormal_champernowne`: from the block counts to the
counts `O U N` at an arbitrary position `N` (`Lam M ≤ N < Lam (M + 1)`). -/
private lemma isNormal_champernowne_sandwich (U : BitString) (hU : U ≠ []) (B : ℕ)
    (hB : ∀ M : ℕ,
      |(2 : ℤ) ^ U.length *
          ((∑ x ∈ Finset.Icc 1 M, isNormal_champernowne_occ U (msbBits x) : ℕ) : ℤ) -
        (isNormal_champernowne_Lam M : ℤ)| ≤ (B : ℤ) * M) :
    ∃ C : ℕ, ∀ M N : ℕ, isNormal_champernowne_Lam M ≤ N →
      N < isNormal_champernowne_Lam (M + 1) →
      |(2 : ℤ) ^ U.length * (isNormal_champernowne_O U N : ℤ) - (N : ℤ)| ≤ (C : ℤ) * (M + 1) := by
  have hk : 1 ≤ U.length := List.length_pos_iff.mpr hU
  refine ⟨(U.length + B + 2 ^ U.length * U.length) * U.length + B + 1, ?_⟩
  intro M N hN1 hN2
  have hlow := isNormal_champernowne_aux_G_lower U hU M N hN1
  have hup := isNormal_champernowne_aux_G_upper U hU M N hN2
  have hBM := hB M
  have hBM' := hB (M + U.length)
  have hLs := isNormal_champernowne_aux_G_Lam_succ M
  have hsz := isNormal_champernowne_aux_G_size_le (M + 1)
  have hLle := isNormal_champernowne_aux_G_Lam_le M U.length
  have hlowZ : ((∑ x ∈ Finset.Icc 1 M, isNormal_champernowne_occ U (msbBits x) : ℕ) : ℤ) ≤
      (isNormal_champernowne_O U N : ℤ) := Nat.cast_le.mpr hlow
  have hupZ : (isNormal_champernowne_O U N : ℤ) ≤
      ((∑ x ∈ Finset.Icc 1 (M + U.length), isNormal_champernowne_occ U (msbBits x) : ℕ) : ℤ) +
        ((U.length : ℤ) - 1) * ((M : ℤ) + U.length) := by
    have h := Nat.cast_le (α := ℤ) |>.mpr hup
    have e : ((U.length - 1 : ℕ) : ℤ) = (U.length : ℤ) - 1 := by omega
    simp only [Nat.cast_add, Nat.cast_mul, e] at h
    exact h
  simp only [Nat.cast_add] at hBM'
  have hL'Z : (isNormal_champernowne_Lam (M + U.length) : ℤ) ≤
      (isNormal_champernowne_Lam M : ℤ) + (U.length : ℤ) * ((M : ℤ) + U.length) := by
    exact_mod_cast hLle
  have hL1Z : (isNormal_champernowne_Lam (M + 1) : ℤ) =
      (isNormal_champernowne_Lam M : ℤ) + (Nat.size (M + 1) : ℤ) := by
    exact_mod_cast hLs
  have hsZ : (Nat.size (M + 1) : ℤ) ≤ (M : ℤ) + 1 := by exact_mod_cast hsz
  have := isNormal_champernowne_aux_G_arith ((2 : ℤ) ^ U.length) (U.length : ℤ) (B : ℤ) (M : ℤ)
    (N : ℤ) (isNormal_champernowne_Lam M : ℤ) (isNormal_champernowne_Lam (M + 1) : ℤ)
    (isNormal_champernowne_Lam (M + U.length) : ℤ) (Nat.size (M + 1) : ℤ)
    ((∑ x ∈ Finset.Icc 1 M, isNormal_champernowne_occ U (msbBits x) : ℕ) : ℤ)
    ((∑ x ∈ Finset.Icc 1 (M + U.length), isNormal_champernowne_occ U (msbBits x) : ℕ) : ℤ)
    (isNormal_champernowne_O U N : ℤ) (by positivity) (by exact_mod_cast hk)
    (by positivity) (by positivity) (by exact_mod_cast hN1) (by exact_mod_cast hN2) hL1Z hsZ
    hL'Z hlowZ hupZ hBM hBM'
  push_cast
  exact this

/-- **SUV Problem 259, p. 266.**  Champernowne's sequence is normal. -/
theorem isNormal_champernowne : IsNormal champernowne := by
  intro U
  by_cases hU : U = []
  · subst hU
    exact isNormal_of_isMisesChurchRandom_empty champernowne
  · obtain ⟨B, hB⟩ := isNormal_champernowne_blocks U hU
    obtain ⟨C, hC⟩ := isNormal_champernowne_sandwich U hU B hB
    exact isNormal_champernowne_final U C hC

end Kolmogorov.FrequencyGames
