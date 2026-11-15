/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Complexity.Applications.ForbiddenSubstrings.BiinfiniteSequences

/-!
# Computable Avoidance

Effective versions of the forbidden-substring theorem: if the set `F` of forbidden strings is
decidable and has at most `2^{αn}` strings of each length `n` (with `α < 1`), there is a
*computable* sequence with no long substring from `F`.  The sequence is built by keeping a
truncated, computable version of Miller's potential below a threshold.  A bi-infinite version is
obtained by interleaving two computable halves into one one-sided sequence.

## Main results

* `exists_computable_avoidsLong`: a computable one-sided sequence with no long substring from `F`
  (SUV Problem 248).
* `exists_computable_biinfinite_avoidsLong`: a bi-infinite sequence with no long substring from
  `F`, computable on both halves (the observation of K. Makarychev reported after Problem 248).

This formalizes part of the chapter of Shen, Uspensky and Vereshchagin, "Kolmogorov complexity
and algorithmic randomness", on applications of Kolmogorov complexity to forbidden substrings.
-/

namespace Kolmogorov.Applications
open scoped ENNReal

/-! ### An effective version: the truncated Miller potential

For a decidable `g` (the forbidden strings of length `≥ L`) the potential of `x` with fuel `d` is
the finite sum, over the non-empty suffixes `s` of `x` and the extensions `t` of length `≤ d`, of
`r ^ |t|` when `s ++ t` is forbidden.  It is computable, and keeping it below `1 - γ` keeps a
computable sequence free of forbidden substrings. -/

/-- All strings of length `m`. -/
private def exists_computable_avoidsLong_allStrs : ℕ → List (List Bool)
  | 0 => [[]]
  | m + 1 => (exists_computable_avoidsLong_allStrs m).map (List.cons false) ++
      (exists_computable_avoidsLong_allStrs m).map (List.cons true)

/-- The number of strings `t` of length `m` such that `s ++ t` is accepted by `g`. -/
private def exists_computable_avoidsLong_cnt (g : List Bool → Bool) (s : List Bool) (m : ℕ) : ℕ :=
  ((exists_computable_avoidsLong_allStrs m).map
    fun t => if g (s ++ t) = true then 1 else 0).sum

/-- The forward potential of `s` with fuel `d`: the weighted number of forbidden extensions of `s`
by at most `d` bits. -/
private def exists_computable_avoidsLong_fwd (g : List Bool → Bool) (r : ℚ) (d : ℕ)
    (s : List Bool) : ℚ :=
  ∑ m ∈ Finset.range (d + 1), r ^ m * (exists_computable_avoidsLong_cnt g s m : ℚ)

/-- The truncated Miller potential of `x`: the sum of the forward potentials of its non-empty
suffixes. -/
private def exists_computable_avoidsLong_pot (g : List Bool → Bool) (r : ℚ) (d : ℕ)
    (x : List Bool) : ℚ :=
  ∑ i ∈ Finset.range x.length, exists_computable_avoidsLong_fwd g r d (x.drop i)

/-- The strings of length `m`, as a list: membership. -/
private lemma exists_computable_avoidsLong_mem_allStrs (m : ℕ) (t : List Bool) :
    t ∈ exists_computable_avoidsLong_allStrs m ↔ t.length = m := by
  induction m generalizing t with
  | zero =>
    simp [exists_computable_avoidsLong_allStrs]
  | succ m ih =>
    simp only [exists_computable_avoidsLong_allStrs, List.mem_append, List.mem_map]
    constructor
    · rintro (⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩)
      · simp [(ih u).mp hu]
      · simp [(ih u).mp hu]
    · intro h
      cases t with
      | nil => simp at h
      | cons b u =>
        have hu : u.length = m := by simpa using h
        cases b
        · exact Or.inl ⟨u, (ih u).mpr hu, rfl⟩
        · exact Or.inr ⟨u, (ih u).mpr hu, rfl⟩

/-- The strings of length `m`, as a list: no repetitions. -/
private lemma exists_computable_avoidsLong_nodup_allStrs (m : ℕ) :
    (exists_computable_avoidsLong_allStrs m).Nodup := by
  induction m with
  | zero => simp [exists_computable_avoidsLong_allStrs]
  | succ m ih =>
    simp only [exists_computable_avoidsLong_allStrs]
    rw [List.nodup_append]
    refine ⟨ih.map List.cons_injective, ih.map List.cons_injective, ?_⟩
    intro a ha b hb
    obtain ⟨u, _, rfl⟩ := List.mem_map.mp ha
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hb
    simp

/-- The count at extension length `0`. -/
private lemma exists_computable_avoidsLong_cnt_zero (g : List Bool → Bool) (s : List Bool) :
    exists_computable_avoidsLong_cnt g s 0 = if g s = true then 1 else 0 := by
  simp [exists_computable_avoidsLong_cnt, exists_computable_avoidsLong_allStrs]

/-- The count at extension length `m + 1` splits according to the first added bit. -/
private lemma exists_computable_avoidsLong_cnt_succ (g : List Bool → Bool) (s : List Bool)
    (m : ℕ) :
    exists_computable_avoidsLong_cnt g s (m + 1) =
      exists_computable_avoidsLong_cnt g (s ++ [false]) m +
        exists_computable_avoidsLong_cnt g (s ++ [true]) m := by
  unfold exists_computable_avoidsLong_cnt
  simp only [exists_computable_avoidsLong_allStrs, List.map_append, List.sum_append, List.map_map]
  congr 3 <;> funext t <;> simp

/-- Peeling the first bit of `s` into `g`. -/
private lemma exists_computable_avoidsLong_f3_cnt_cons (g : List Bool → Bool) (c : Bool)
    (s : List Bool) (m : ℕ) :
    exists_computable_avoidsLong_cnt (fun z => g (c :: z)) s m =
      exists_computable_avoidsLong_cnt g (c :: s) m := by
  simp [exists_computable_avoidsLong_cnt]

/-- Extensions of `s` by `m` bits inject into the strings of length `|s| + m`. -/
private lemma exists_computable_avoidsLong_cnt_le (g : List Bool → Bool) (s : List Bool)
    (m : ℕ) :
    exists_computable_avoidsLong_cnt g s m ≤
      exists_computable_avoidsLong_cnt g [] (s.length + m) := by
  induction s generalizing g m with
  | nil => simp
  | cons c s ih =>
    have h1 := ih (fun z => g (c :: z)) m
    rw [exists_computable_avoidsLong_f3_cnt_cons, exists_computable_avoidsLong_f3_cnt_cons] at h1
    have h2 : exists_computable_avoidsLong_cnt g [c] (s.length + m) ≤
        exists_computable_avoidsLong_cnt g [] (s.length + m + 1) := by
      rw [exists_computable_avoidsLong_cnt_succ g [] (s.length + m)]
      cases c <;> simp
    calc exists_computable_avoidsLong_cnt g (c :: s) m
        ≤ exists_computable_avoidsLong_cnt g [c] (s.length + m) := h1
      _ ≤ exists_computable_avoidsLong_cnt g [] (s.length + m + 1) := h2
      _ = exists_computable_avoidsLong_cnt g [] ((c :: s).length + m) := by
          congr 1
          simp only [List.length_cons]
          omega

/-- Nothing shorter than `L` is accepted, so there is nothing to count below `L`. -/
private lemma exists_computable_avoidsLong_cnt_nil_eq_zero {g : List Bool → Bool} {L : ℕ}
    (hgL : ∀ z, g z = true → L ≤ z.length) {m : ℕ} (hm : m < L) :
    exists_computable_avoidsLong_cnt g [] m = 0 := by
  unfold exists_computable_avoidsLong_cnt
  refine List.sum_eq_zero fun x hx => ?_
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
  have hlen := (exists_computable_avoidsLong_mem_allStrs m t).mp ht
  have hgt : g t = false := by
    by_contra h
    have h' : g t = true := by simpa using h
    have := hgL t h'
    omega
  simp [hgt]

/-- A sum of indicators is the length of a filter. -/
private lemma exists_computable_avoidsLong_f3_sum_ite (l : List (List Bool))
    (p : List Bool → Bool) :
    (l.map fun t => if p t = true then 1 else 0).sum = (l.filter p).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases hpa : p a
    · simp [hpa, ih]
    · simp [hpa, ih]
      omega

/-- The count of accepted strings of length `M` is at most the number of strings of `F` of length
`M`, if `g` accepts only strings of `F`. -/
private lemma exists_computable_avoidsLong_cnt_nil_le_ncard {F : Set (List Bool)}
    {g : List Bool → Bool} (hg : ∀ z, g z = true → z ∈ F) (M : ℕ) :
    exists_computable_avoidsLong_cnt g [] M ≤
      ({x ∈ F | x.length = M} : Set (List Bool)).ncard := by
  classical
  have hcnt : exists_computable_avoidsLong_cnt g [] M =
      ((exists_computable_avoidsLong_allStrs M).filter g).length := by
    unfold exists_computable_avoidsLong_cnt
    simpa using exists_computable_avoidsLong_f3_sum_ite (exists_computable_avoidsLong_allStrs M) g
  have hnd : ((exists_computable_avoidsLong_allStrs M).filter g).Nodup :=
    (exists_computable_avoidsLong_nodup_allStrs M).filter g
  rw [hcnt, ← List.toFinset_card_of_nodup hnd, ← Set.ncard_coe_finset]
  refine Set.ncard_le_ncard ?_ ((finite_length_eq M).subset fun x hx => hx.2)
  intro t ht
  have ht' := List.mem_toFinset.mp (Finset.mem_coe.mp ht)
  rcases List.mem_filter.mp ht' with ⟨h1, h2⟩
  exact ⟨hg t h2, (exists_computable_avoidsLong_mem_allStrs M t).mp h1⟩

/-- The recursion of the forward potential:
`fwd (d+1) s = [s accepted] + r (fwd d (s0) + fwd d (s1))`. -/
private lemma exists_computable_avoidsLong_fwd_succ (g : List Bool → Bool) (r : ℚ) (d : ℕ)
    (s : List Bool) :
    exists_computable_avoidsLong_fwd g r (d + 1) s =
      (if g s = true then 1 else 0) +
        r * (exists_computable_avoidsLong_fwd g r d (s ++ [false]) +
          exists_computable_avoidsLong_fwd g r d (s ++ [true])) := by
  unfold exists_computable_avoidsLong_fwd
  rw [Finset.sum_range_succ']
  have h0 : r ^ 0 * (exists_computable_avoidsLong_cnt g s 0 : ℚ) =
      if g s = true then 1 else 0 := by
    rw [exists_computable_avoidsLong_cnt_zero]
    split_ifs <;> simp
  have hsum : ∑ m ∈ Finset.range (d + 1),
      r ^ (m + 1) * (exists_computable_avoidsLong_cnt g s (m + 1) : ℚ) =
      r * (∑ m ∈ Finset.range (d + 1),
        r ^ m * (exists_computable_avoidsLong_cnt g (s ++ [false]) m : ℚ) +
        ∑ m ∈ Finset.range (d + 1),
        r ^ m * (exists_computable_avoidsLong_cnt g (s ++ [true]) m : ℚ)) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [exists_computable_avoidsLong_cnt_succ]
    push_cast
    ring
  rw [hsum, h0]
  ring

/-- The forward potential is non-negative. -/
private lemma exists_computable_avoidsLong_fwd_nonneg (g : List Bool → Bool) {r : ℚ} (hr : 0 ≤ r)
    (d : ℕ) (s : List Bool) : 0 ≤ exists_computable_avoidsLong_fwd g r d s := by
  unfold exists_computable_avoidsLong_fwd
  exact Finset.sum_nonneg fun m _ => mul_nonneg (pow_nonneg hr m) (Nat.cast_nonneg _)

/-- An accepted string has forward potential at least `1`, whatever the fuel. -/
private lemma exists_computable_avoidsLong_one_le_fwd (g : List Bool → Bool) {r : ℚ} (hr : 0 ≤ r)
    {s : List Bool} (hs : g s = true) (d : ℕ) :
    1 ≤ exists_computable_avoidsLong_fwd g r d s := by
  unfold exists_computable_avoidsLong_fwd
  have h0 : (0 : ℕ) ∈ Finset.range (d + 1) := Finset.mem_range.mpr (Nat.succ_pos d)
  have hterm : r ^ 0 * (exists_computable_avoidsLong_cnt g s 0 : ℚ) = 1 := by
    rw [exists_computable_avoidsLong_cnt_zero, ite_eq_left hs]
    simp
  calc (1 : ℚ) = r ^ 0 * (exists_computable_avoidsLong_cnt g s 0 : ℚ) := hterm.symm
    _ ≤ ∑ m ∈ Finset.range (d + 1), r ^ m * (exists_computable_avoidsLong_cnt g s m : ℚ) :=
      Finset.single_le_sum
        (f := fun m => r ^ m * (exists_computable_avoidsLong_cnt g s m : ℚ))
        (fun m _ => mul_nonneg (pow_nonneg hr m) (Nat.cast_nonneg _)) h0

/-- If a non-empty suffix of `x` is accepted, the potential of `x` is at least `1`. -/
private lemma exists_computable_avoidsLong_one_le_pot (g : List Bool → Bool) {r : ℚ} (hr : 0 ≤ r)
    {x : List Bool} {i : ℕ} (hi : i < x.length) (hg : g (x.drop i) = true) (d : ℕ) :
    1 ≤ exists_computable_avoidsLong_pot g r d x := by
  unfold exists_computable_avoidsLong_pot
  calc (1 : ℚ) ≤ exists_computable_avoidsLong_fwd g r d (x.drop i) :=
        exists_computable_avoidsLong_one_le_fwd g hr hg d
    _ ≤ ∑ j ∈ Finset.range x.length, exists_computable_avoidsLong_fwd g r d (x.drop j) :=
      Finset.single_le_sum
        (f := fun j => exists_computable_avoidsLong_fwd g r d (x.drop j))
        (fun j _ => exists_computable_avoidsLong_fwd_nonneg g hr d _) (Finset.mem_range.mpr hi)

/-- The potential of `x ++ [c]`: the suffixes of `x`, extended by `c`, and the string `[c]`. -/
private lemma exists_computable_avoidsLong_f4_pot_snoc (g : List Bool → Bool) (r : ℚ) (d : ℕ)
    (x : List Bool) (c : Bool) :
    exists_computable_avoidsLong_pot g r d (x ++ [c]) =
      (∑ i ∈ Finset.range x.length,
          exists_computable_avoidsLong_fwd g r d (x.drop i ++ [c])) +
        exists_computable_avoidsLong_fwd g r d [c] := by
  unfold exists_computable_avoidsLong_pot
  rw [List.length_append, List.length_singleton, Finset.sum_range_succ]
  congr 1
  · refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i ≤ x.length := (Finset.mem_range.mp hi).le
    rw [List.drop_append_of_le_length hi']
  · rw [List.drop_left]

/-- **The drift identity.**  If no non-empty suffix of `x` is accepted (and the empty string is
not), `r (pot d (x0) + pot d (x1)) = pot (d+1) x + fwd (d+1) []`. -/
private lemma exists_computable_avoidsLong_pot_drift (g : List Bool → Bool) {r : ℚ}
    (hg0 : g [] = false) {x : List Bool} (hclean : ∀ i < x.length, g (x.drop i) = false)
    (d : ℕ) :
    r * exists_computable_avoidsLong_pot g r d (x ++ [false]) +
        r * exists_computable_avoidsLong_pot g r d (x ++ [true]) =
      exists_computable_avoidsLong_pot g r (d + 1) x +
        exists_computable_avoidsLong_fwd g r (d + 1) [] := by
  rw [exists_computable_avoidsLong_f4_pot_snoc, exists_computable_avoidsLong_f4_pot_snoc]
  have hnil : exists_computable_avoidsLong_fwd g r (d + 1) [] =
      r * (exists_computable_avoidsLong_fwd g r d [false] +
        exists_computable_avoidsLong_fwd g r d [true]) := by
    rw [exists_computable_avoidsLong_fwd_succ, hg0]
    simp
  have hsum : ∀ i ∈ Finset.range x.length,
      r * exists_computable_avoidsLong_fwd g r d (x.drop i ++ [false]) +
        r * exists_computable_avoidsLong_fwd g r d (x.drop i ++ [true]) =
      exists_computable_avoidsLong_fwd g r (d + 1) (x.drop i) := by
    intro i hi
    rw [exists_computable_avoidsLong_fwd_succ, hclean i (Finset.mem_range.mp hi)]
    simp
    ring
  have hS : r * (∑ i ∈ Finset.range x.length,
        exists_computable_avoidsLong_fwd g r d (x.drop i ++ [false])) +
      r * (∑ i ∈ Finset.range x.length,
        exists_computable_avoidsLong_fwd g r d (x.drop i ++ [true])) =
      ∑ i ∈ Finset.range x.length, exists_computable_avoidsLong_fwd g r (d + 1) (x.drop i) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl hsum
  unfold exists_computable_avoidsLong_pot
  rw [hnil]
  linear_combination hS

/-- One more unit of fuel adds one term to the forward potential. -/
private lemma exists_computable_avoidsLong_f5_fwd_succ_fuel (g : List Bool → Bool) (r : ℚ) (d : ℕ)
    (s : List Bool) :
    exists_computable_avoidsLong_fwd g r (d + 1) s =
      exists_computable_avoidsLong_fwd g r d s +
        r ^ (d + 1) * (exists_computable_avoidsLong_cnt g s (d + 1) : ℚ) := by
  unfold exists_computable_avoidsLong_fwd
  rw [Finset.sum_range_succ _ (d + 1)]

/-- The tail of the forward potential, with the exact geometric factor. -/
private lemma exists_computable_avoidsLong_f5_fwd_tail_aux (g : List Bool → Bool) {r q : ℚ}
    (hr : 0 ≤ r) (_hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hcount : ∀ M : ℕ, (exists_computable_avoidsLong_cnt g [] M : ℚ) * r ^ M ≤ q ^ M)
    (s : List Bool) (d e : ℕ) :
    exists_computable_avoidsLong_fwd g r d s ≤ exists_computable_avoidsLong_fwd g r (d + e) s ∧
      (1 - q) * r ^ s.length * (exists_computable_avoidsLong_fwd g r (d + e) s -
        exists_computable_avoidsLong_fwd g r d s) ≤ q ^ (s.length + d + 1) * (1 - q ^ e) := by
  induction e with
  | zero => simp
  | succ e ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hde : d + (e + 1) = d + e + 1 := rfl
    rw [hde, exists_computable_avoidsLong_f5_fwd_succ_fuel g r (d + e) s]
    obtain ⟨T, hT⟩ : ∃ T : ℚ, T = r ^ (d + e + 1) *
        (exists_computable_avoidsLong_cnt g s (d + e + 1) : ℚ) := ⟨_, rfl⟩
    rw [← hT]
    have hT0 : 0 ≤ T := by rw [hT]; positivity
    have hTb : r ^ s.length * T ≤ q ^ (s.length + (d + e + 1)) := by
      have hle : (exists_computable_avoidsLong_cnt g s (d + e + 1) : ℚ) ≤
          (exists_computable_avoidsLong_cnt g [] (s.length + (d + e + 1)) : ℚ) := by
        exact_mod_cast exists_computable_avoidsLong_cnt_le g s (d + e + 1)
      calc r ^ s.length * T
          = r ^ (s.length + (d + e + 1)) *
              (exists_computable_avoidsLong_cnt g s (d + e + 1) : ℚ) := by
            rw [hT, pow_add]; ring
        _ ≤ r ^ (s.length + (d + e + 1)) *
              (exists_computable_avoidsLong_cnt g [] (s.length + (d + e + 1)) : ℚ) :=
            mul_le_mul_of_nonneg_left hle (pow_nonneg hr _)
        _ = (exists_computable_avoidsLong_cnt g [] (s.length + (d + e + 1)) : ℚ) *
              r ^ (s.length + (d + e + 1)) := by ring
        _ ≤ q ^ (s.length + (d + e + 1)) := hcount _
    refine ⟨by linarith, ?_⟩
    have h1q : 0 ≤ 1 - q := by linarith
    calc (1 - q) * r ^ s.length * (exists_computable_avoidsLong_fwd g r (d + e) s + T -
          exists_computable_avoidsLong_fwd g r d s)
        = (1 - q) * r ^ s.length * (exists_computable_avoidsLong_fwd g r (d + e) s -
            exists_computable_avoidsLong_fwd g r d s) + (1 - q) * (r ^ s.length * T) := by ring
      _ ≤ q ^ (s.length + d + 1) * (1 - q ^ e) + (1 - q) * q ^ (s.length + (d + e + 1)) :=
          add_le_add ih2 (mul_le_mul_of_nonneg_left hTb h1q)
      _ = q ^ (s.length + d + 1) * (1 - q ^ (e + 1)) := by ring

/-- The tail of the forward potential of `s`, beyond fuel `d`, is small. -/
private lemma exists_computable_avoidsLong_fwd_tail (g : List Bool → Bool) {r q : ℚ} (hr : 0 ≤ r)
    (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hcount : ∀ M : ℕ, (exists_computable_avoidsLong_cnt g [] M : ℚ) * r ^ M ≤ q ^ M)
    (s : List Bool) (d e : ℕ) :
    exists_computable_avoidsLong_fwd g r d s ≤ exists_computable_avoidsLong_fwd g r (d + e) s ∧
      (1 - q) * r ^ s.length * (exists_computable_avoidsLong_fwd g r (d + e) s -
        exists_computable_avoidsLong_fwd g r d s) ≤ q ^ (s.length + d + 1) := by
  obtain ⟨h1, h2⟩ := exists_computable_avoidsLong_f5_fwd_tail_aux g hr hq hq1 hcount s d e
  refine ⟨h1, h2.trans ?_⟩
  have h3 : 0 ≤ q ^ (s.length + d + 1) * q ^ e := by positivity
  have h4 : q ^ (s.length + d + 1) * (1 - q ^ e) =
      q ^ (s.length + d + 1) - q ^ (s.length + d + 1) * q ^ e := by ring
  linarith

/-- The tail of the potential of `x`, beyond fuel `d`, is small. -/
private lemma exists_computable_avoidsLong_pot_tail (g : List Bool → Bool) {r q : ℚ} (hr : 0 < r)
    (hr1 : r ≤ 1) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hcount : ∀ M : ℕ, (exists_computable_avoidsLong_cnt g [] M : ℚ) * r ^ M ≤ q ^ M)
    (x : List Bool) (d e : ℕ) :
    (1 - q) * r ^ x.length * (exists_computable_avoidsLong_pot g r (d + e) x -
      exists_computable_avoidsLong_pot g r d x) ≤ (x.length : ℚ) * q ^ (d + 2) := by
  have hsub : exists_computable_avoidsLong_pot g r (d + e) x -
      exists_computable_avoidsLong_pot g r d x =
      ∑ i ∈ Finset.range x.length, (exists_computable_avoidsLong_fwd g r (d + e) (x.drop i) -
        exists_computable_avoidsLong_fwd g r d (x.drop i)) := by
    unfold exists_computable_avoidsLong_pot
    rw [Finset.sum_sub_distrib]
  rw [hsub, Finset.mul_sum]
  calc ∑ i ∈ Finset.range x.length, (1 - q) * r ^ x.length *
        (exists_computable_avoidsLong_fwd g r (d + e) (x.drop i) -
          exists_computable_avoidsLong_fwd g r d (x.drop i))
      ≤ ∑ _i ∈ Finset.range x.length, q ^ (d + 2) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i < x.length := Finset.mem_range.mp hi
        obtain ⟨h1, h2⟩ :=
          exists_computable_avoidsLong_fwd_tail g hr.le hq hq1 hcount (x.drop i) d e
        have hlen : (x.drop i).length = x.length - i := List.length_drop
        rw [hlen] at h2
        have hrn : r ^ x.length ≤ r ^ (x.length - i) :=
          pow_le_pow_of_le_one hr.le hr1 (Nat.sub_le _ _)
        have hqexp : q ^ (x.length - i + d + 1) ≤ q ^ (d + 2) :=
          pow_le_pow_of_le_one hq hq1 (by omega)
        have h1q : 0 ≤ 1 - q := by linarith
        calc (1 - q) * r ^ x.length * (exists_computable_avoidsLong_fwd g r (d + e) (x.drop i) -
              exists_computable_avoidsLong_fwd g r d (x.drop i))
            ≤ (1 - q) * r ^ (x.length - i) *
              (exists_computable_avoidsLong_fwd g r (d + e) (x.drop i) -
                exists_computable_avoidsLong_fwd g r d (x.drop i)) := by
              apply mul_le_mul_of_nonneg_right
              · exact mul_le_mul_of_nonneg_left hrn h1q
              · linarith
          _ ≤ q ^ (x.length - i + d + 1) := h2
          _ ≤ q ^ (d + 2) := hqexp
    _ = (x.length : ℚ) * q ^ (d + 2) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- The partial sums of the forward potential of the empty string, with the telescoping bound. -/
private lemma exists_computable_avoidsLong_f5_fwd_nil_aux (g : List Bool → Bool) {r q : ℚ} {L : ℕ}
    (_hr : 0 ≤ r) (hq1 : q ≤ 1) (hgL : ∀ z, g z = true → L ≤ z.length)
    (hcount : ∀ M : ℕ, (exists_computable_avoidsLong_cnt g [] M : ℚ) * r ^ M ≤ q ^ M) (k : ℕ) :
    (1 - q) * ∑ m ∈ Finset.range k, r ^ m * (exists_computable_avoidsLong_cnt g [] m : ℚ) ≤
      q ^ L - q ^ (max k L) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    rcases lt_or_ge k L with hk | hk
    · have hz : exists_computable_avoidsLong_cnt g [] k = 0 :=
        exists_computable_avoidsLong_cnt_nil_eq_zero hgL hk
      rw [hz]
      have hmax1 : max (k + 1) L = max k L := by
        rw [max_eq_right (by omega), max_eq_right (by omega)]
      rw [hmax1]
      simpa using ih
    · have hmax0 : max k L = k := max_eq_left hk
      have hmax1 : max (k + 1) L = k + 1 := max_eq_left (by omega)
      rw [hmax0] at ih
      rw [hmax1]
      have hterm : r ^ k * (exists_computable_avoidsLong_cnt g [] k : ℚ) ≤ q ^ k := by
        have := hcount k
        linarith [mul_comm (exists_computable_avoidsLong_cnt g [] k : ℚ) (r ^ k)]
      have h1q : 0 ≤ 1 - q := by linarith
      calc (1 - q) * (∑ m ∈ Finset.range k, r ^ m * (exists_computable_avoidsLong_cnt g [] m : ℚ) +
            r ^ k * (exists_computable_avoidsLong_cnt g [] k : ℚ))
          = (1 - q) * ∑ m ∈ Finset.range k, r ^ m * (exists_computable_avoidsLong_cnt g [] m : ℚ) +
            (1 - q) * (r ^ k * (exists_computable_avoidsLong_cnt g [] k : ℚ)) := by ring
        _ ≤ q ^ L - q ^ k + (1 - q) * q ^ k :=
            add_le_add ih (mul_le_mul_of_nonneg_left hterm h1q)
        _ = q ^ L - q ^ (k + 1) := by ring

/-- The forward potential of the empty string is at most `q ^ L / (1 - q)`. -/
private lemma exists_computable_avoidsLong_fwd_nil_le (g : List Bool → Bool) {r q : ℚ} {L : ℕ}
    (hr : 0 ≤ r) (hq : 0 ≤ q) (hq1 : q ≤ 1) (hgL : ∀ z, g z = true → L ≤ z.length)
    (hcount : ∀ M : ℕ, (exists_computable_avoidsLong_cnt g [] M : ℚ) * r ^ M ≤ q ^ M) (d : ℕ) :
    (1 - q) * exists_computable_avoidsLong_fwd g r d [] ≤ q ^ L := by
  have h := exists_computable_avoidsLong_f5_fwd_nil_aux g hr hq1 hgL hcount (d + 1)
  have hpos : 0 ≤ q ^ max (d + 1) L := pow_nonneg hq _
  unfold exists_computable_avoidsLong_fwd
  linarith

/-- A sum of a computable mapped computable list is computable. -/
private lemma exists_computable_avoidsLong_f1_computable_sum_map {α β : Type*} [Primcodable α]
    [Primcodable β] {l : α → List β} {h : α → β → ℕ} (hl : Computable l)
    (hh : Computable₂ h) : Computable fun a => ((l a).map (h a)).sum := by
  have hstep : Computable₂ (fun (a : α) (p : ℕ × β) => p.1 + h a p.2) :=
    Primrec.nat_add.to_comp.comp (Computable.fst.comp Computable.snd)
      (hh.comp Computable.fst (Computable.snd.comp Computable.snd))
  have hfold := Computable.list_foldl (l := l) (g := fun _ => (0 : ℕ))
    (h := fun a (p : ℕ × β) => p.1 + h a p.2) hl (Computable.const 0) hstep
  refine hfold.of_eq fun a => ?_
  have key : ∀ (L : List β) (acc : ℕ),
      L.foldl (fun s b => s + h a b) acc = acc + (L.map (h a)).sum := by
    intro L
    induction L with
    | nil => intro acc; simp
    | cons b L ih => intro acc; simp [ih]; ring
  simpa using key (l a) 0

/-- The list of all strings of length `m` is computable in `m`. -/
private lemma exists_computable_avoidsLong_f1_computable_allStrs :
    Computable exists_computable_avoidsLong_allStrs := by
  have hstep : Computable₂ (fun (_ : ℕ) (p : ℕ × List (List Bool)) =>
      p.2.map (List.cons false) ++ p.2.map (List.cons true)) := by
    have hcf : Computable₂ (fun (_ : ℕ × (ℕ × List (List Bool))) (t : List Bool) => false :: t) :=
      Computable₂.comp (f := List.cons) Computable.list_cons (Computable.const false)
        Computable.snd
    have hct : Computable₂ (fun (_ : ℕ × (ℕ × List (List Bool))) (t : List Bool) => true :: t) :=
      Computable₂.comp (f := List.cons) Computable.list_cons (Computable.const true)
        Computable.snd
    have hl : Computable (fun a : ℕ × (ℕ × List (List Bool)) => a.2.2) :=
      Computable.snd.comp Computable.snd
    exact Computable₂.comp (f := fun l1 l2 : List (List Bool) => l1 ++ l2) Computable.list_append
      (Computable.list_map hl hcf) (Computable.list_map hl hct)
  have hrec : Computable (fun n : ℕ => Nat.rec (motive := fun _ => List (List Bool)) [[]]
      (fun y IH => (fun (_ : ℕ) (p : ℕ × List (List Bool)) =>
        p.2.map (List.cons false) ++ p.2.map (List.cons true)) n (y, IH)) n) :=
    Computable.nat_rec (f := fun n : ℕ => n) (g := fun _ => [[]])
      (h := fun (_ : ℕ) (p : ℕ × List (List Bool)) =>
        p.2.map (List.cons false) ++ p.2.map (List.cons true))
      Computable.id (Computable.const _) hstep
  refine hrec.of_eq fun n => ?_
  induction n with
  | zero => rfl
  | succ n ih =>
    change _ = (exists_computable_avoidsLong_allStrs n).map (List.cons false) ++
      (exists_computable_avoidsLong_allStrs n).map (List.cons true)
    rw [← ih]

/-- The count `cnt g s m` is computable in `(s, m)`, for computable `g`. -/
private lemma exists_computable_avoidsLong_f1_computable_cnt {g : List Bool → Bool}
    (hg : Computable g) :
    Computable₂ (fun (s : List Bool) (m : ℕ) => exists_computable_avoidsLong_cnt g s m) := by
  have hl : Computable (fun p : List Bool × ℕ => exists_computable_avoidsLong_allStrs p.2) :=
    exists_computable_avoidsLong_f1_computable_allStrs.comp Computable.snd
  have happ : Computable₂ (fun (p : List Bool × ℕ) (t : List Bool) => p.1 ++ t) :=
    Computable₂.comp (f := fun l1 l2 : List Bool => l1 ++ l2) Computable.list_append
      (Computable.fst.comp Computable.fst) Computable.snd
  have hind : Computable₂ (fun (p : List Bool × ℕ) (t : List Bool) =>
      if g (p.1 ++ t) = true then 1 else 0) := by
    have hc : Computable₂ (fun (p : List Bool × ℕ) (t : List Bool) =>
        cond (g (p.1 ++ t)) 1 0) :=
      Computable.cond (hg.comp happ) (Computable.const 1) (Computable.const 0)
    refine hc.of_eq fun p => ?_
    cases g (p.1.1 ++ p.2) <;> simp
  exact exists_computable_avoidsLong_f1_computable_sum_map hl hind

/-- Exponentiation of natural numbers is primitive recursive. -/
private lemma exists_computable_avoidsLong_f1_primrec_pow : Primrec₂ (fun (a b : ℕ) => a ^ b) :=
  Primrec.nat_iff.mpr Nat.Primrec.pow

/-- The potential, scaled to a natural number: `rd ^ d * pot` when `r = rn / rd`. -/
private def exists_computable_avoidsLong_f1_potN (g : List Bool → Bool) (rn rd d : ℕ)
    (x : List Bool) : ℕ :=
  ((List.range x.length).map fun i =>
    ((List.range (d + 1)).map fun m =>
      rn ^ m * rd ^ (d - m) * exists_computable_avoidsLong_cnt g (x.drop i) m).sum).sum

/-- A sum over `Finset.range` is the sum of the mapped list `List.range`. -/
private lemma exists_computable_avoidsLong_f1_sum_range_eq {M : Type*} [AddCommMonoid M]
    (f : ℕ → M) (n : ℕ) : ∑ i ∈ Finset.range n, f i = ((List.range n).map f).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, List.range_succ, List.map_append, List.sum_append]
    simp

/-- The scaled potential is `rd ^ d` times the potential. -/
private lemma exists_computable_avoidsLong_f1_potN_cast (g : List Bool → Bool) {rn rd : ℕ}
    (hrd : 0 < rd) (d : ℕ) (x : List Bool) :
    (exists_computable_avoidsLong_f1_potN g rn rd d x : ℚ) =
      (rd : ℚ) ^ d * exists_computable_avoidsLong_pot g ((rn : ℚ) / rd) d x := by
  have hfin : exists_computable_avoidsLong_f1_potN g rn rd d x =
      ∑ i ∈ Finset.range x.length, ∑ m ∈ Finset.range (d + 1),
        rn ^ m * rd ^ (d - m) * exists_computable_avoidsLong_cnt g (x.drop i) m := by
    unfold exists_computable_avoidsLong_f1_potN
    rw [← exists_computable_avoidsLong_f1_sum_range_eq]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← exists_computable_avoidsLong_f1_sum_range_eq]
  rw [hfin]
  unfold exists_computable_avoidsLong_pot exists_computable_avoidsLong_fwd
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmd : m ≤ d := by have := Finset.mem_range.mp hm; omega
  have hpow : (rd : ℚ) ^ d = (rd : ℚ) ^ m * (rd : ℚ) ^ (d - m) := by
    rw [← pow_add]; congr 1; omega
  have hrd' : (rd : ℚ) ≠ 0 := by exact_mod_cast hrd.ne'
  rw [hpow, div_pow]
  field_simp

/-- The scaled potential is computable. -/
private lemma exists_computable_avoidsLong_f1_computable_potN {g : List Bool → Bool}
    (hg : Computable g) (rn rd c b : ℕ) :
    Computable fun x : List Bool =>
      exists_computable_avoidsLong_f1_potN g rn rd (c * x.length + b) x := by
  have hcnt := exists_computable_avoidsLong_f1_computable_cnt hg
  have hpow : Computable₂ (fun (a b : ℕ) => a ^ b) :=
    exists_computable_avoidsLong_f1_primrec_pow.to_comp
  have hlen : Computable (fun p : List Bool × ℕ => p.1.length) :=
    Primrec.list_length.to_comp.comp Computable.fst
  have hd : Computable (fun p : List Bool × ℕ => c * p.1.length + b) :=
    Primrec.nat_add.to_comp.comp (Primrec.nat_mul.to_comp.comp (Computable.const c) hlen)
      (Computable.const b)
  have hdQ : Computable (fun q : (List Bool × ℕ) × ℕ => c * q.1.1.length + b) :=
    hd.comp Computable.fst
  have hA : Computable (fun q : (List Bool × ℕ) × ℕ => rn ^ q.2) :=
    hpow.comp (Computable.const rn) Computable.snd
  have hB : Computable (fun q : (List Bool × ℕ) × ℕ => rd ^ (c * q.1.1.length + b - q.2)) :=
    hpow.comp (Computable.const rd) (Primrec.nat_sub.to_comp.comp hdQ Computable.snd)
  have hC : Computable (fun q : (List Bool × ℕ) × ℕ =>
      exists_computable_avoidsLong_cnt g (q.1.1.drop q.1.2) q.2) :=
    hcnt.comp (Primrec.list_drop.to_comp.comp (Computable.snd.comp Computable.fst)
      (Computable.fst.comp Computable.fst)) Computable.snd
  have hterm : Computable₂ (fun (p : List Bool × ℕ) (m : ℕ) =>
      rn ^ m * rd ^ (c * p.1.length + b - m) *
        exists_computable_avoidsLong_cnt g (p.1.drop p.2) m) :=
    Primrec.nat_mul.to_comp.comp (Primrec.nat_mul.to_comp.comp hA hB) hC
  have hrange : Computable (fun p : List Bool × ℕ => List.range (c * p.1.length + b + 1)) :=
    Primrec.list_range.to_comp.comp
      (Primrec.nat_add.to_comp.comp hd (Computable.const 1))
  have hinner : Computable (fun p : List Bool × ℕ =>
      ((List.range (c * p.1.length + b + 1)).map fun m =>
        rn ^ m * rd ^ (c * p.1.length + b - m) *
          exists_computable_avoidsLong_cnt g (p.1.drop p.2) m).sum) :=
    exists_computable_avoidsLong_f1_computable_sum_map hrange hterm
  have hrange2 : Computable (fun x : List Bool => List.range x.length) :=
    Primrec.list_range.to_comp.comp Primrec.list_length.to_comp
  exact exists_computable_avoidsLong_f1_computable_sum_map hrange2 hinner

/-- A positive rational is a quotient of natural numbers. -/
private lemma exists_computable_avoidsLong_f1_rat_eq_div {q : ℚ} (hq : 0 < q) :
    ∃ n d : ℕ, 0 < d ∧ q = (n : ℚ) / d := by
  refine ⟨q.num.toNat, q.den, q.den_pos, ?_⟩
  have hnum : 0 ≤ q.num := Rat.num_nonneg.mpr hq.le
  have h1 : ((q.num.toNat : ℕ) : ℚ) = (q.num : ℚ) := by
    have := Int.toNat_of_nonneg hnum
    exact_mod_cast this
  rw [h1]
  exact (Rat.num_div_den q).symm

/-- The predicate "potential `< 1 - γ`" is decidable, for computable `g`. -/
private lemma exists_computable_avoidsLong_computable_good {g : List Bool → Bool}
    (hg : Computable g) {r γ : ℚ} (hr : 0 < r) (hγ : 0 < γ) (c b : ℕ) :
    ComputablePred fun x : List Bool =>
      exists_computable_avoidsLong_pot g r (c * x.length + b) x + γ < 1 := by
  obtain ⟨rn, rd, hrd, rfl⟩ := exists_computable_avoidsLong_f1_rat_eq_div hr
  obtain ⟨gn, gd, hgd, rfl⟩ := exists_computable_avoidsLong_f1_rat_eq_div hγ
  have hiff : ∀ x : List Bool,
      (exists_computable_avoidsLong_pot g ((rn : ℚ) / rd) (c * x.length + b) x +
        (gn : ℚ) / gd < 1) ↔
      exists_computable_avoidsLong_f1_potN g rn rd (c * x.length + b) x * gd +
        gn * rd ^ (c * x.length + b) < gd * rd ^ (c * x.length + b) := by
    intro x
    have hbridge := exists_computable_avoidsLong_f1_potN_cast g (rn := rn) hrd
      (c * x.length + b) x
    rw [← Nat.cast_lt (α := ℚ)]
    push_cast
    rw [hbridge]
    have hrdQ : (0 : ℚ) < rd := by exact_mod_cast hrd
    have hA : (0 : ℚ) < (rd : ℚ) ^ (c * x.length + b) := pow_pos hrdQ _
    have hG : (0 : ℚ) < gd := by exact_mod_cast hgd
    have hG' : (gd : ℚ) ≠ 0 := hG.ne'
    have e : (rd : ℚ) ^ (c * x.length + b) * gd *
        (exists_computable_avoidsLong_pot g ((rn : ℚ) / rd) (c * x.length + b) x +
          (gn : ℚ) / gd) =
        (rd : ℚ) ^ (c * x.length + b) *
          exists_computable_avoidsLong_pot g ((rn : ℚ) / rd) (c * x.length + b) x * gd +
        gn * (rd : ℚ) ^ (c * x.length + b) := by
      field_simp
    constructor
    · intro h
      have := mul_lt_mul_of_pos_left h (mul_pos hA hG)
      linarith [e]
    · intro h
      by_contra hcon
      push Not at hcon
      have := mul_le_mul_of_nonneg_left hcon (mul_pos hA hG).le
      linarith [e]
  have hcomp : Computable (fun x : List Bool => decide (
      exists_computable_avoidsLong_f1_potN g rn rd (c * x.length + b) x * gd +
        gn * rd ^ (c * x.length + b) < gd * rd ^ (c * x.length + b))) := by
    have hpotN := exists_computable_avoidsLong_f1_computable_potN hg rn rd c b
    have hpow : Computable₂ (fun (a b : ℕ) => a ^ b) :=
      exists_computable_avoidsLong_f1_primrec_pow.to_comp
    have hd : Computable (fun x : List Bool => c * x.length + b) :=
      Primrec.nat_add.to_comp.comp
        (Primrec.nat_mul.to_comp.comp (Computable.const c) Primrec.list_length.to_comp)
        (Computable.const b)
    have hP : Computable (fun x : List Bool => rd ^ (c * x.length + b)) :=
      hpow.comp (Computable.const rd) hd
    have hL : Computable (fun x : List Bool =>
        exists_computable_avoidsLong_f1_potN g rn rd (c * x.length + b) x * gd +
          gn * rd ^ (c * x.length + b)) :=
      Primrec.nat_add.to_comp.comp
        (Primrec.nat_mul.to_comp.comp hpotN (Computable.const gd))
        (Primrec.nat_mul.to_comp.comp (Computable.const gn) hP)
    have hR : Computable (fun x : List Bool => gd * rd ^ (c * x.length + b)) :=
      Primrec.nat_mul.to_comp.comp (Computable.const gd) hP
    exact (PrimrecRel.decide Primrec.nat_lt).to_comp.comp hL hR
  refine ⟨Classical.decPred _, hcomp.of_eq fun x => ?_⟩
  exact decide_eq_decide.mpr (hiff x).symm

/-- A decidable tree in which every node has a child has a computable infinite path. -/
private lemma exists_computable_avoidsLong_path {Good : List Bool → Prop}
    (hGood : ComputablePred Good) (h0 : Good [])
    (hstep : ∀ x, Good x → ∃ b, Good (x ++ [b])) :
    ∃ w : ℕ → Bool, Computable w ∧ ∀ n, Good (seqFactor w 0 n) := by
  obtain ⟨inst, hc⟩ := hGood
  -- the greedy choice of the next bit
  obtain ⟨ch, hch⟩ : ∃ ch : List Bool → Bool,
      ch = fun x => !(decide (Good (x ++ [false]))) := ⟨_, rfl⟩
  have hchc : Computable ch := by
    rw [hch]
    exact Primrec.not.to_comp.comp
      (hc.comp (Computable.list_concat.comp Computable.id (Computable.const false)))
  have hchspec : ∀ x, Good x → Good (x ++ [ch x]) := by
    intro x hx
    by_cases h : Good (x ++ [false])
    · have : ch x = false := by rw [hch]; simp [h]
      rw [this]; exact h
    · have : ch x = true := by rw [hch]; simp [h]
      rw [this]
      obtain ⟨b, hb⟩ := hstep x hx
      cases b with
      | false => exact absurd hb h
      | true => exact hb
  -- the prefixes of the path
  obtain ⟨pre, hpre⟩ : ∃ pre : ℕ → List Bool, pre = fun n =>
      Nat.rec (motive := fun _ => List Bool) [] (fun _ x => x ++ [ch x]) n := ⟨_, rfl⟩
  have hprec : Computable pre := by
    rw [hpre]
    exact Computable.nat_rec (f := id) (g := fun _ => ([] : List Bool))
      (h := fun _ p => p.2 ++ [ch p.2]) Computable.id (Computable.const [])
      (Computable.list_concat.comp (Computable.snd.comp Computable.snd)
        (hchc.comp (Computable.snd.comp Computable.snd)))
  have hpre_zero : pre 0 = [] := by subst hpre; rfl
  have hpre_succ : ∀ n, pre (n + 1) = pre n ++ [ch (pre n)] := by
    intro n; subst hpre; rfl
  have hgood : ∀ n, Good (pre n) := by
    intro n
    induction n with
    | zero => rw [hpre_zero]; exact h0
    | succ n ih => rw [hpre_succ]; exact hchspec _ ih
  have hfac : ∀ n, seqFactor (fun n => ch (pre n)) 0 n = pre n := by
    intro n
    induction n with
    | zero => rw [hpre_zero]; simp [seqFactor]
    | succ n ih => rw [seqFactor_succ, ih, hpre_succ]; simp
  exact ⟨fun n => ch (pre n), hchc.comp hprec, fun n => by rw [hfac]; exact hgood n⟩

/-- Rational `1/2 < r < 1` and `0 < q < 1` such that `r ^ M` times the number of strings of `F` of
length `M` is at most `q ^ M`: `r` is below `2 ^ (-α)` and `q` is above `2 ^ α * r`. -/
private lemma exists_computable_avoidsLong_f2_rq {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {F : Set (List Bool)} (hF : IsAtMostForbidden α F) :
    ∃ r q : ℚ, 1 / 2 < r ∧ r < 1 ∧ 0 < q ∧ q < 1 ∧
      ∀ M : ℕ, (({x ∈ F | x.length = M} : Set (List Bool)).ncard : ℚ) * r ^ M ≤ q ^ M := by
  have h2a : (1 : ℝ) / 2 < (2 : ℝ) ^ (-α) := by
    have h : (1 : ℝ) / 2 = (2 : ℝ) ^ (-1 : ℝ) := by rw [Real.rpow_neg_one]; norm_num
    rw [h]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
  have h2b : (2 : ℝ) ^ (-α) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn h2a
  have hrhalf : (1 : ℝ) / 2 < (r : ℝ) := hr1
  have hrq1 : (r : ℝ) < 1 := hr2.trans h2b
  have hr0 : (0 : ℝ) < r := by linarith
  have hρ1 : (2 : ℝ) ^ α * r < 1 := by
    have h : (2 : ℝ) ^ α * (2 : ℝ) ^ (-α) = 1 := by
      rw [← Real.rpow_add (by norm_num)]; simp
    calc (2 : ℝ) ^ α * r < (2 : ℝ) ^ α * (2 : ℝ) ^ (-α) :=
          mul_lt_mul_of_pos_left hr2 (by positivity)
      _ = 1 := h
  have hρ0 : (0 : ℝ) < (2 : ℝ) ^ α * r := by positivity
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hρ1
  have hq0 : (0 : ℝ) < q := hρ0.trans hq1
  refine ⟨r, q, ?_, ?_, ?_, ?_, ?_⟩
  · have h : ((1 / 2 : ℚ) : ℝ) < (r : ℝ) := by push_cast; exact hrhalf
    exact Rat.cast_lt.mp h
  · exact_mod_cast hrq1
  · exact_mod_cast hq0
  · exact_mod_cast hq2
  · intro M
    have hcount := hF M
    have h1 : (({x ∈ F | x.length = M} : Set (List Bool)).ncard : ℝ) * (r : ℝ) ^ M ≤
        (q : ℝ) ^ M := by
      calc _ ≤ (2 : ℝ) ^ (α * M) * (r : ℝ) ^ M :=
            mul_le_mul_of_nonneg_right hcount (pow_nonneg hr0.le M)
        _ = ((2 : ℝ) ^ α * r) ^ M := by
            rw [mul_pow, Real.rpow_mul (by norm_num), Real.rpow_natCast]
        _ ≤ (q : ℝ) ^ M := pow_le_pow_left₀ hρ0.le hq1.le M
    exact_mod_cast h1

/-- A length `L ≥ 1` with `q ^ L / (1 - q) < 2 r - 1`, and the slack `γ` with
`1 + q ^ L / (1 - q) = 2 r (1 - γ)`. -/
private lemma exists_computable_avoidsLong_f2_Lgamma {r q : ℚ} (hr : 1 / 2 < r) (hq0 : 0 < q)
    (hq1 : q < 1) :
    ∃ (L : ℕ) (γ : ℚ), 0 < L ∧ 0 < γ ∧ γ < 1 ∧ 1 + q ^ L / (1 - q) ≤ 2 * r * (1 - γ) := by
  have h1q : 0 < 1 - q := by linarith
  have h2r : 0 < 2 * r - 1 := by linarith
  have hr0 : r ≠ 0 := by intro h; rw [h] at hr; norm_num at hr
  obtain ⟨L₀, hL₀⟩ := exists_pow_lt_of_lt_one (mul_pos h2r h1q) hq1
  have hL : q ^ (L₀ + 1) < (2 * r - 1) * (1 - q) :=
    lt_of_le_of_lt (pow_le_pow_of_le_one hq0.le hq1.le (Nat.le_succ L₀)) hL₀
  obtain ⟨S, hSdef⟩ : ∃ S : ℚ, S = q ^ (L₀ + 1) / (1 - q) := ⟨_, rfl⟩
  have hS : S < 2 * r - 1 := by
    rw [hSdef, div_lt_iff₀ h1q]; exact hL
  have hS0 : 0 ≤ S := by rw [hSdef]; positivity
  refine ⟨L₀ + 1, (2 * r - 1 - S) / (2 * r), Nat.succ_pos _, ?_, ?_, ?_⟩
  · exact div_pos (by linarith) (by linarith)
  · rw [div_lt_one (by linarith)]; linarith
  · rw [← hSdef]
    apply le_of_eq
    field_simp
    ring

/-- `c` and `b` with `n * q ^ (c * n + b + 2) ≤ γ (1 - q) r ^ n` for all `n`. -/
private lemma exists_computable_avoidsLong_f2_cb {r q γ : ℚ} (hr : 0 < r) (hq0 : 0 < q)
    (hq1 : q < 1) (hγ : 0 < γ) :
    ∃ c b : ℕ, ∀ n : ℕ, (n : ℚ) * q ^ (c * n + b + 2) ≤ γ * (1 - q) * r ^ n := by
  have h1q : 0 < 1 - q := by linarith
  obtain ⟨c, hc⟩ := exists_pow_lt_of_lt_one (half_pos hr) hq1
  obtain ⟨b, hb⟩ := exists_pow_lt_of_lt_one (mul_pos hγ h1q) hq1
  refine ⟨c, b, fun n => ?_⟩
  have hb2 : q ^ (b + 2) ≤ γ * (1 - q) :=
    (pow_le_pow_of_le_one hq0.le hq1.le (Nat.le_add_right b 2)).trans hb.le
  have hn : (n : ℚ) ≤ 2 ^ n := by exact_mod_cast (Nat.lt_two_pow_self (n := n)).le
  have hcn : (q ^ c) ^ n ≤ (r / 2) ^ n := pow_le_pow_left₀ (pow_nonneg hq0.le c) hc.le n
  have hexp : q ^ (c * n + b + 2) = (q ^ c) ^ n * q ^ (b + 2) := by
    rw [show c * n + b + 2 = c * n + (b + 2) by ring, pow_add q (c * n) (b + 2), pow_mul]
  rw [hexp]
  have hmid : (n : ℚ) * (r / 2) ^ n ≤ r ^ n := by
    rw [div_pow, mul_div_assoc', div_le_iff₀ (by positivity)]
    calc (n : ℚ) * r ^ n ≤ 2 ^ n * r ^ n := by gcongr
      _ = r ^ n * 2 ^ n := by ring
  calc (n : ℚ) * ((q ^ c) ^ n * q ^ (b + 2)) = ((n : ℚ) * (q ^ c) ^ n) * q ^ (b + 2) := by ring
    _ ≤ ((n : ℚ) * (r / 2) ^ n) * q ^ (b + 2) := by gcongr
    _ ≤ r ^ n * q ^ (b + 2) := by gcongr
    _ ≤ r ^ n * (γ * (1 - q)) := by gcongr
    _ = γ * (1 - q) * r ^ n := by ring

/-- The numerical parameters. -/
private lemma exists_computable_avoidsLong_params {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {F : Set (List Bool)} (hF : IsAtMostForbidden α F) :
    ∃ (r q γ : ℚ) (L c b : ℕ), 1 / 2 < r ∧ r < 1 ∧ 0 < q ∧ q < 1 ∧ 0 < γ ∧ γ < 1 ∧ 0 < L ∧
      (∀ M : ℕ, (({x ∈ F | x.length = M} : Set (List Bool)).ncard : ℚ) * r ^ M ≤ q ^ M) ∧
      1 + q ^ L / (1 - q) ≤ 2 * r * (1 - γ) ∧
      ∀ n : ℕ, (n : ℚ) * q ^ (c * n + b + 2) ≤ γ * (1 - q) * r ^ n := by
  obtain ⟨r, q, hr, hr1, hq0, hq1, hcount⟩ := exists_computable_avoidsLong_f2_rq hα0 hα1 hF
  obtain ⟨L, γ, hL, hγ0, hγ1, hS⟩ := exists_computable_avoidsLong_f2_Lgamma hr hq0 hq1
  obtain ⟨c, b, hcb⟩ := exists_computable_avoidsLong_f2_cb (r := r) (by linarith) hq0 hq1 hγ0
  exact ⟨r, q, γ, L, c, b, hr, hr1, hq0, hq1, hγ0, hγ1, hL, hcount, hS, hcb⟩

/-- The effective Miller construction, for a computable `g` that accepts no string shorter than
`L`: the potential is kept below `1 - γ`, which is a decidable invariant. -/
private lemma exists_computable_avoidsLong_main {g : List Bool → Bool} (hg : Computable g)
    {r q γ : ℚ} {L c b : ℕ} (hr : 1 / 2 < r) (hr1 : r < 1) (hq : 0 < q) (hq1 : q < 1)
    (hγ : 0 < γ) (hγ1 : γ < 1) (hL : 0 < L) (hgL : ∀ z, g z = true → L ≤ z.length)
    (hcount : ∀ M : ℕ, (exists_computable_avoidsLong_cnt g [] M : ℚ) * r ^ M ≤ q ^ M)
    (hS : 1 + q ^ L / (1 - q) ≤ 2 * r * (1 - γ))
    (htail : ∀ n : ℕ, (n : ℚ) * q ^ (c * n + b + 2) ≤ γ * (1 - q) * r ^ n) :
    ∃ w : ℕ → Bool, Computable w ∧ ∀ u, g u = true → ¬ OccursIn u w := by
  have hr0 : (0 : ℚ) < r := by linarith
  have hg0 : g [] = false := by
    by_contra h
    have h' : g [] = true := by simpa using h
    have := hgL [] h'
    simp at this
    omega
  have hcomp := exists_computable_avoidsLong_computable_good hg hr0 hγ c b
  have h0 : exists_computable_avoidsLong_pot g r (c * ([] : List Bool).length + b) [] + γ < 1 := by
    simpa [exists_computable_avoidsLong_pot] using hγ1
  have hstep : ∀ x : List Bool,
      exists_computable_avoidsLong_pot g r (c * x.length + b) x + γ < 1 →
      ∃ bit : Bool, exists_computable_avoidsLong_pot g r (c * (x ++ [bit]).length + b)
        (x ++ [bit]) + γ < 1 := by
    intro x hx
    obtain ⟨n, hn⟩ : ∃ n, n = x.length := ⟨_, rfl⟩
    obtain ⟨d₀, hd₀⟩ : ∃ d₀, d₀ = c * n + b := ⟨_, rfl⟩
    obtain ⟨d, hd⟩ : ∃ d, d = c * (n + 1) + b := ⟨_, rfl⟩
    rw [← hn, ← hd₀] at hx
    have hclean : ∀ i < x.length, g (x.drop i) = false := by
      intro i hi
      by_contra h
      have h' : g (x.drop i) = true := by simpa using h
      have := exists_computable_avoidsLong_one_le_pot g hr0.le hi h' d₀
      rw [← hn] at *
      linarith
    have hdrift := exists_computable_avoidsLong_pot_drift g (r := r) hg0 hclean d
    have hd1 : d + 1 = d₀ + (c + 1) := by rw [hd, hd₀]; ring
    have htl := exists_computable_avoidsLong_pot_tail g hr0 hr1.le hq.le hq1.le hcount x d₀ (c + 1)
    rw [← hd1, ← hn] at htl
    have hpos : 0 < (1 - q) * r ^ n := mul_pos (by linarith) (pow_pos hr0 n)
    have hΔ : exists_computable_avoidsLong_pot g r (d + 1) x ≤
        exists_computable_avoidsLong_pot g r d₀ x + γ := by
      have h1 : (1 - q) * r ^ n * (exists_computable_avoidsLong_pot g r (d + 1) x -
          exists_computable_avoidsLong_pot g r d₀ x) ≤ (1 - q) * r ^ n * γ := by
        calc _ ≤ (n : ℚ) * q ^ (d₀ + 2) := htl
          _ = (n : ℚ) * q ^ (c * n + b + 2) := by rw [hd₀]
          _ ≤ γ * (1 - q) * r ^ n := htail n
          _ = _ := by ring
      have := le_of_mul_le_mul_left h1 hpos
      linarith
    have hfwd : exists_computable_avoidsLong_fwd g r (d + 1) [] ≤ q ^ L / (1 - q) := by
      have := exists_computable_avoidsLong_fwd_nil_le g hr0.le hq.le hq1.le hgL hcount (d + 1)
      rw [le_div_iff₀ (by linarith)]
      linarith
    have hsum : exists_computable_avoidsLong_pot g r d (x ++ [false]) +
        exists_computable_avoidsLong_pot g r d (x ++ [true]) < 2 * (1 - γ) := by
      have h1 : r * (exists_computable_avoidsLong_pot g r d (x ++ [false]) +
          exists_computable_avoidsLong_pot g r d (x ++ [true])) < r * (2 * (1 - γ)) := by
        calc _ = r * exists_computable_avoidsLong_pot g r d (x ++ [false]) +
              r * exists_computable_avoidsLong_pot g r d (x ++ [true]) := by ring
          _ = _ := hdrift
          _ < 1 + q ^ L / (1 - q) := by linarith
          _ ≤ 2 * r * (1 - γ) := hS
          _ = _ := by ring
      exact lt_of_mul_lt_mul_left h1 hr0.le
    by_cases hA : exists_computable_avoidsLong_pot g r d (x ++ [false]) + γ < 1
    · refine ⟨false, ?_⟩
      have hlen : c * (x ++ [false]).length + b = d := by
        rw [hd, hn]; simp
      rw [hlen]
      exact hA
    · refine ⟨true, ?_⟩
      have hlen : c * (x ++ [true]).length + b = d := by
        rw [hd, hn]; simp
      rw [hlen]
      push Not at hA
      linarith
  obtain ⟨w, hw, hwg⟩ := exists_computable_avoidsLong_path hcomp h0 hstep
  refine ⟨w, hw, fun u hu ⟨i, hi⟩ => ?_⟩
  have hLu : L ≤ u.length := hgL u hu
  have hfac : seqFactor w 0 (i + u.length) = seqFactor w 0 i ++ u := by
    rw [seqFactor_add, Nat.zero_add, hi]
  have hdrop : (seqFactor w 0 (i + u.length)).drop i = u := by
    rw [hfac]
    simp [length_seqFactor]
  have hi' : i < (seqFactor w 0 (i + u.length)).length := by
    rw [length_seqFactor]; omega
  have h1 := exists_computable_avoidsLong_one_le_pot g hr0.le hi' (by rw [hdrop]; exact hu)
    (c * (seqFactor w 0 (i + u.length)).length + b)
  have h2 := hwg (i + u.length)
  linarith

/-- **SUV Problem 248, p. 244.**  If `F` satisfies the conditions and is decidable, there is a
*computable* sequence with no long substrings from `F`.  The published text says "no short
substrings"; that is a slip, since the conclusion is that of Theorem 157 and short strings cannot be
avoided in general. -/
theorem exists_computable_avoidsLong {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {F : Set (List Bool)}
    (hF : IsAtMostForbidden α F) (hdec : ComputablePred (· ∈ F)) :
    ∃ c w, Computable w ∧ AvoidsLong F c w := by
  obtain ⟨r, q, γ, L, c, b, hr, hr1, hq, hq1, hγ, hγ1, hL, hcnt, hS, htail⟩ :=
    exists_computable_avoidsLong_params hα0 hα1 hF
  obtain ⟨inst, hcomp⟩ := hdec
  obtain ⟨g, hgdef⟩ : ∃ g : List Bool → Bool,
      g = fun z => @decide (z ∈ F) (inst z) && decide (L ≤ z.length) := ⟨_, rfl⟩
  have hgz : ∀ z, g z = true ↔ z ∈ F ∧ L ≤ z.length := by
    intro z
    rw [hgdef]
    simp
  have hg : Computable g := by
    rw [hgdef]
    exact Primrec.and.to_comp.comp hcomp
      (Primrec.nat_le.comp (Primrec.const L) Primrec.list_length).decide.to_comp
  have hcount : ∀ M : ℕ, (exists_computable_avoidsLong_cnt g [] M : ℚ) * r ^ M ≤ q ^ M := by
    intro M
    refine le_trans (mul_le_mul_of_nonneg_right ?_ (pow_nonneg (by linarith) M)) (hcnt M)
    exact_mod_cast exists_computable_avoidsLong_cnt_nil_le_ncard (fun z hz => ((hgz z).mp hz).1) M
  obtain ⟨w, hw, hwg⟩ := exists_computable_avoidsLong_main hg hr hr1 hq hq1 hγ hγ1 hL
    (fun z hz => ((hgz z).mp hz).2) hcount hS htail
  exact ⟨L, w, hw, fun u hu hlen => hwg u ((hgz u).mpr ⟨hu, hlen⟩)⟩

/-! ### The bi-infinite version, by interleaving the two halves into one sequence

A one-sided sequence `w` gives the bi-infinite sequence `z` with `z n = w (2 n)` for `n ≥ 0` and
`z (-n) = w (2 n - 1)` for `n ≥ 1`.  A substring `u` of `z` is then read off a window `y` of `w`:
at the even (resp. odd) positions of `y` when `u` lies in the non-negative (resp. negative) half,
and at the first positions of `w` when `u` straddles the origin.  The windows that read a string of
`F` (or of its reversal) form a set `forb F N` of strings with `2 ^ ((3 + α) / 4 * n)` elements of
each length `n ≥ N`, which is decidable: so the one-sided `exists_computable_avoidsLong` applies. -/

/-- The bi-infinite sequence with the non-negative half on the even positions of `w` and the
negative half on the odd ones. -/
private def exists_computable_biinfinite_avoidsLong_zOf (w : ℕ → Bool) (i : ℤ) : Bool :=
  if 0 ≤ i then w (2 * i.toNat) else w (2 * (-i).toNat - 1)

/-- The position in `w` of the `j`-th letter of the `a + b + 1` letters `z (-a), …, z b`. -/
private def exists_computable_biinfinite_avoidsLong_pos (a j : ℕ) : ℕ :=
  if j < a then 2 * (a - j) - 1 else 2 * (j - a)

/-- The length of the window of `w` that holds the letters `z (-a), …, z b`. -/
private def exists_computable_biinfinite_avoidsLong_win (a b : ℕ) : ℕ :=
  max (2 * a) (2 * b + 1)

/-- The string `z (-a) … z b` read off the window `y` of `w`. -/
private def exists_computable_biinfinite_avoidsLong_rd (a b : ℕ) (y : List Bool) : List Bool :=
  (List.range (a + b + 1)).map fun j =>
    y.getD (exists_computable_biinfinite_avoidsLong_pos a j) false

/-- The windows of length `≥ N` that read a string of `F` or of its reversal. -/
private def exists_computable_biinfinite_avoidsLong_forb (F : Set (List Bool)) (N : ℕ) :
    Set (List Bool) :=
  {y | N ≤ y.length ∧ ∃ a b : ℕ, y.length = exists_computable_biinfinite_avoidsLong_win a b ∧
    (exists_computable_biinfinite_avoidsLong_rd a b y ∈ F ∨
      (exists_computable_biinfinite_avoidsLong_rd a b y).reverse ∈ F)}

/-- Step 1 of the proof of `exists_computable_biinfinite_avoidsLong`: the two halves of
the interleaved sequence are computable when `w` is. -/
private lemma exists_computable_biinfinite_avoidsLong_halves {w : ℕ → Bool}
    (hw : Computable w) :
    Computable (fun n : ℕ => exists_computable_biinfinite_avoidsLong_zOf w n) ∧
      Computable (fun n : ℕ => exists_computable_biinfinite_avoidsLong_zOf w (-(n : ℤ))) := by
  have h2n : Computable (fun n : ℕ => 2 * n) :=
    Primrec.nat_mul.to_comp.comp (Computable.const 2) Computable.id
  constructor
  · refine (hw.comp h2n).of_eq fun n => ?_
    simp [exists_computable_biinfinite_avoidsLong_zOf]
  · refine (hw.comp (Primrec.nat_sub.to_comp.comp h2n (Computable.const 1))).of_eq fun n => ?_
    unfold exists_computable_biinfinite_avoidsLong_zOf
    split_ifs with h
    · have : n = 0 := by omega
      subst this
      simp
    · simp

/-- The positions of a window of `a + b + 1` letters lie inside the window of length `win a b`. -/
private lemma exists_computable_biinfinite_avoidsLong_pos_lt {a b j : ℕ} (hj : j < a + b + 1) :
    exists_computable_biinfinite_avoidsLong_pos a j <
      exists_computable_biinfinite_avoidsLong_win a b := by
  unfold exists_computable_biinfinite_avoidsLong_pos exists_computable_biinfinite_avoidsLong_win
  split_ifs <;> omega

/-- Reading a factor of `w` through `rd`. -/
private lemma exists_computable_biinfinite_avoidsLong_rd_seqFactor (w : ℕ → Bool) (p a b : ℕ) :
    exists_computable_biinfinite_avoidsLong_rd a b
        (seqFactor w p (exists_computable_biinfinite_avoidsLong_win a b)) =
      (List.range (a + b + 1)).map fun j =>
        w (p + exists_computable_biinfinite_avoidsLong_pos a j) := by
  unfold exists_computable_biinfinite_avoidsLong_rd
  refine List.map_congr_left fun j hj => ?_
  have hlt := exists_computable_biinfinite_avoidsLong_pos_lt (List.mem_range.mp hj)
  simp [List.getD_eq_getElem?_getD, getElem?_seqFactor, hlt]

/-- The letters read through `rd` from a factor of `w` are the letters of `w` at the positions. -/
private lemma exists_computable_biinfinite_avoidsLong_rd_eq (w : ℕ → Bool) (p a b : ℕ)
    {u : List Bool} (hlen : u.length = a + b + 1)
    (h : ∀ (j : ℕ) (hj : j < u.length),
      w (p + exists_computable_biinfinite_avoidsLong_pos a j) = u[j]) :
    exists_computable_biinfinite_avoidsLong_rd a b
        (seqFactor w p (exists_computable_biinfinite_avoidsLong_win a b)) = u := by
  rw [exists_computable_biinfinite_avoidsLong_rd_seqFactor]
  refine List.ext_getElem (by simp [hlen]) fun j hj hj' => ?_
  simp only [List.getElem_map, List.getElem_range]
  exact h j hj'

/-- A factor of `w` that reads a string of `F` (or its reversal) is a forbidden window. -/
private lemma exists_computable_biinfinite_avoidsLong_window_of_rd (w : ℕ → Bool)
    {F : Set (List Bool)} {N : ℕ} {u : List Bool} (hNu : N ≤ u.length) (a b p : ℕ)
    (hlen : u.length = a + b + 1)
    (hrd : exists_computable_biinfinite_avoidsLong_rd a b
        (seqFactor w p (exists_computable_biinfinite_avoidsLong_win a b)) ∈ F ∨
      (exists_computable_biinfinite_avoidsLong_rd a b
        (seqFactor w p (exists_computable_biinfinite_avoidsLong_win a b))).reverse ∈ F) :
    ∃ y ∈ exists_computable_biinfinite_avoidsLong_forb F N, u.length ≤ y.length ∧ OccursIn y w := by
  have hwin : a + b + 1 ≤ exists_computable_biinfinite_avoidsLong_win a b := by
    unfold exists_computable_biinfinite_avoidsLong_win; omega
  refine ⟨seqFactor w p (exists_computable_biinfinite_avoidsLong_win a b),
    ⟨?_, a, b, ?_, hrd⟩, ?_, ?_⟩
  · rw [length_seqFactor]; omega
  · rw [length_seqFactor]
  · rw [length_seqFactor]; omega
  · exact ⟨p, by rw [length_seqFactor]⟩

/-- Step 2 of the proof of `exists_computable_biinfinite_avoidsLong`: an occurrence of
a string `u ∈ F` of length `≥ N ≥ 1` in the interleaved sequence is an occurrence in `w` of a
window `y ∈ forb F N` of length `≥ |u|`. -/
private lemma exists_computable_biinfinite_avoidsLong_window (w : ℕ → Bool)
    {F : Set (List Bool)} {N : ℕ} {u : List Bool} (hu : u ∈ F) (hN1 : 1 ≤ N) (hNu : N ≤ u.length)
    (hocc : OccursInBi u (exists_computable_biinfinite_avoidsLong_zOf w)) :
    ∃ y ∈ exists_computable_biinfinite_avoidsLong_forb F N, u.length ≤ y.length ∧ OccursIn y w := by
  obtain ⟨i, hi⟩ := hocc
  have hm : 1 ≤ u.length := le_trans hN1 hNu
  by_cases hi0 : 0 ≤ i
  · -- `u` lies in the non-negative half: it is read at the even positions from `2 i`
    have hread := exists_computable_biinfinite_avoidsLong_rd_eq w (2 * i.toNat) 0 (u.length - 1)
      (u := u) (by omega) (fun j hj => by
        have h : exists_computable_biinfinite_avoidsLong_zOf w (i + (j : ℤ)) = u[j] := hi ⟨j, hj⟩
        unfold exists_computable_biinfinite_avoidsLong_zOf at h
        rw [ite_eq_left (by omega)] at h
        rw [← h]
        congr 1
        unfold exists_computable_biinfinite_avoidsLong_pos
        split_ifs <;> omega)
    exact exists_computable_biinfinite_avoidsLong_window_of_rd w hNu 0 (u.length - 1)
      (2 * i.toNat) (by omega) (Or.inl (by rw [hread]; exact hu))
  · by_cases hneg : i + (u.length : ℤ) ≤ 0
    · -- `u` lies in the negative half: its reversal is read at the odd positions
      have hread := exists_computable_biinfinite_avoidsLong_rd_eq w
        (2 * (-(i + (u.length : ℤ) - 1)).toNat - 1) 0 (u.length - 1)
        (u := u.reverse) (by simp; omega) (fun j hj => by
          have hj' : j < u.length := by simpa using hj
          have h : exists_computable_biinfinite_avoidsLong_zOf w
              (i + ((u.length - 1 - j : ℕ) : ℤ)) = u[u.length - 1 - j] :=
            hi ⟨u.length - 1 - j, by omega⟩
          unfold exists_computable_biinfinite_avoidsLong_zOf at h
          rw [ite_eq_right (by omega)] at h
          rw [List.getElem_reverse, ← h]
          congr 1
          unfold exists_computable_biinfinite_avoidsLong_pos
          split_ifs <;> omega)
      refine exists_computable_biinfinite_avoidsLong_window_of_rd w hNu 0 (u.length - 1)
        (2 * (-(i + (u.length : ℤ) - 1)).toNat - 1) (by omega) (Or.inr ?_)
      rw [hread, List.reverse_reverse]
      exact hu
    · -- `u` straddles the origin: it is read from the start of `w`
      have hread := exists_computable_biinfinite_avoidsLong_rd_eq w 0 (-i).toNat
        (i + (u.length : ℤ) - 1).toNat (u := u) (by omega) (fun j hj => by
          have h : exists_computable_biinfinite_avoidsLong_zOf w (i + (j : ℤ)) = u[j] :=
            hi ⟨j, hj⟩
          unfold exists_computable_biinfinite_avoidsLong_zOf at h
          rw [← h]
          by_cases hj0 : 0 ≤ i + (j : ℤ)
          · rw [ite_eq_left hj0]
            congr 1
            unfold exists_computable_biinfinite_avoidsLong_pos
            split_ifs <;> omega
          · rw [ite_eq_right hj0]
            congr 1
            unfold exists_computable_biinfinite_avoidsLong_pos
            split_ifs <;> omega)
      exact exists_computable_biinfinite_avoidsLong_window_of_rd w hNu (-i).toNat
        (i + (u.length : ℤ) - 1).toNat 0 (by omega) (Or.inl (by rw [hread]; exact hu))

/-- There are `2 ^ n` strings of length `n`. -/
private lemma exists_computable_biinfinite_avoidsLong_ncard_length_eq (n : ℕ) :
    ({r : List Bool | r.length = n} : Set (List Bool)).ncard = 2 ^ n := by
  have hlen : ∀ n : ℕ, (exists_computable_avoidsLong_allStrs n).length = 2 ^ n := by
    intro n
    induction n with
    | zero => simp [exists_computable_avoidsLong_allStrs]
    | succ n ih =>
      simp only [exists_computable_avoidsLong_allStrs, List.length_append, List.length_map, ih,
        pow_succ]
      ring
  have hset : ({r : List Bool | r.length = n} : Set (List Bool)) =
      ↑(exists_computable_avoidsLong_allStrs n).toFinset := by
    ext r
    simp [exists_computable_avoidsLong_mem_allStrs]
  rw [hset, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup (exists_computable_avoidsLong_nodup_allStrs n), hlen]

/-- The cube bound: the strings of length `W` that read a string of `S` at `n` distinct positions
number at most `|S ∩ {length n}| * 2 ^ (W - n)`. -/
private lemma exists_computable_biinfinite_avoidsLong_ncard_pattern_le (S : Set (List Bool))
    (P : List ℕ) (W : ℕ) (hnd : P.Nodup) (hlt : ∀ p ∈ P, p < W) :
    ({y : List Bool | y.length = W ∧ P.map (fun p => y.getD p false) ∈ S}).ncard ≤
      ({u ∈ S | u.length = P.length} : Set (List Bool)).ncard * 2 ^ (W - P.length) := by
  classical
  obtain ⟨Q, hQ⟩ : ∃ Q : List ℕ, Q = ((Finset.range W) \ P.toFinset).toList := ⟨_, rfl⟩
  have hsub : P.toFinset ⊆ Finset.range W := fun p hp => by
    simpa using hlt p (List.mem_toFinset.mp hp)
  have hQlen : Q.length = W - P.length := by
    rw [hQ, Finset.length_toList, Finset.card_sdiff_of_subset hsub, Finset.card_range,
      List.toFinset_card_of_nodup hnd]
  have hQmem : ∀ p, p ∈ Q ↔ p < W ∧ p ∉ P := by
    intro p
    simp [hQ]
  have hfin : ({u ∈ S | u.length = P.length} ×ˢ
      {r : List Bool | r.length = W - P.length} : Set (List Bool × List Bool)).Finite :=
    ((finite_length_eq _).subset fun u hu => hu.2).prod (finite_length_eq _)
  calc _ ≤ ({u ∈ S | u.length = P.length} ×ˢ
        {r : List Bool | r.length = W - P.length} : Set (List Bool × List Bool)).ncard :=
        Set.ncard_le_ncard_of_injOn
          (fun y => (P.map (fun p => y.getD p false), Q.map (fun p => y.getD p false)))
          ?_ ?_ hfin
    _ = _ := by rw [Set.ncard_prod, exists_computable_biinfinite_avoidsLong_ncard_length_eq]
  · rintro y ⟨hy, hyS⟩
    exact ⟨⟨hyS, by simp⟩, by simp [hQlen]⟩
  · rintro y ⟨hy, -⟩ y' ⟨hy', -⟩ hyy'
    simp only [Prod.mk.injEq] at hyy'
    obtain ⟨h1, h2⟩ := hyy'
    refine List.ext_getElem (hy.trans hy'.symm) fun p hp hp' => ?_
    have hpW : p < W := hy ▸ hp
    have key : y.getD p false = y'.getD p false := by
      by_cases hpP : p ∈ P
      · exact (List.map_inj_left.mp h1) p hpP
      · exact (List.map_inj_left.mp h2) p ((hQmem p).mpr ⟨hpW, hpP⟩)
    simpa [List.getD_eq_getElem?_getD, hp, hp'] using key

/-- The cube bound for the windows that read a string of `S` through `rd a b`. -/
private lemma exists_computable_biinfinite_avoidsLong_ncard_rd_le (S : Set (List Bool))
    (a b : ℕ) :
    ({y : List Bool | y.length = exists_computable_biinfinite_avoidsLong_win a b ∧
        exists_computable_biinfinite_avoidsLong_rd a b y ∈ S}).ncard ≤
      ({u ∈ S | u.length = a + b + 1} : Set (List Bool)).ncard *
        2 ^ (exists_computable_biinfinite_avoidsLong_win a b - (a + b + 1)) := by
  have hnd : ((List.range (a + b + 1)).map
      (exists_computable_biinfinite_avoidsLong_pos a)).Nodup := by
    refine List.Nodup.map_on ?_ List.nodup_range
    intro j hj j' hj' hjj
    simp only [List.mem_range] at hj hj'
    unfold exists_computable_biinfinite_avoidsLong_pos at hjj
    split_ifs at hjj <;> omega
  have hlt : ∀ p ∈ (List.range (a + b + 1)).map
      (exists_computable_biinfinite_avoidsLong_pos a),
      p < exists_computable_biinfinite_avoidsLong_win a b := by
    intro p hp
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hp
    exact exists_computable_biinfinite_avoidsLong_pos_lt (List.mem_range.mp hj)
  have h := exists_computable_biinfinite_avoidsLong_ncard_pattern_le S _
    (exists_computable_biinfinite_avoidsLong_win a b) hnd hlt
  simpa [exists_computable_biinfinite_avoidsLong_rd, List.map_map, Function.comp_def] using h

/-- Closing `F` under reversal at most doubles the number of strings of each length. -/
private lemma exists_computable_biinfinite_avoidsLong_ncard_fpm_le (F : Set (List Bool))
    (m : ℕ) :
    ({u ∈ {u : List Bool | u ∈ F ∨ u.reverse ∈ F} | u.length = m} : Set (List Bool)).ncard ≤
      2 * ({x ∈ F | x.length = m} : Set (List Bool)).ncard := by
  have hfin : ({x ∈ F | x.length = m} : Set (List Bool)).Finite :=
    (finite_length_eq m).subset fun x hx => hx.2
  have hsub : ({u ∈ {u : List Bool | u ∈ F ∨ u.reverse ∈ F} | u.length = m} :
      Set (List Bool)) ⊆
      {x ∈ F | x.length = m} ∪ List.reverse '' {x ∈ F | x.length = m} := by
    rintro u ⟨hu | hu, hlen⟩
    · exact Or.inl ⟨hu, hlen⟩
    · exact Or.inr ⟨u.reverse, ⟨hu, by simpa using hlen⟩, List.reverse_reverse u⟩
  calc _ ≤ ({x ∈ F | x.length = m} ∪ List.reverse '' {x ∈ F | x.length = m} :
          Set (List Bool)).ncard := Set.ncard_le_ncard hsub (hfin.union (hfin.image _))
    _ ≤ ({x ∈ F | x.length = m} : Set (List Bool)).ncard +
          (List.reverse '' {x ∈ F | x.length = m} : Set (List Bool)).ncard :=
        Set.ncard_union_le _ _
    _ ≤ 2 * ({x ∈ F | x.length = m} : Set (List Bool)).ncard := by
        have := Set.ncard_image_le (f := List.reverse) hfin
        omega

/-- The union bound for `Set.ncard`, over a finite index set. -/
private lemma exists_computable_biinfinite_avoidsLong_ncard_biUnion_le {ι β : Type*}
    (T : Finset ι) (s : ι → Set β) :
    (⋃ i ∈ T, s i).ncard ≤ ∑ i ∈ T, (s i).ncard := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert i T hi ih =>
    rw [Finset.sum_insert hi]
    calc (⋃ j ∈ insert i T, s j).ncard
        = (s i ∪ ⋃ j ∈ T, s j).ncard := by
          congr 1
          ext x
          simp
      _ ≤ (s i).ncard + (⋃ j ∈ T, s j).ncard := Set.ncard_union_le _ _
      _ ≤ _ := Nat.add_le_add_left ih _

/-- The exponent bookkeeping: `2 ^ (α m) * 2 ^ (W - m) ≤ 2 ^ ((1 + α) / 2 * W)` when
`(W + 1) / 2 ≤ m ≤ W`. -/
private lemma exists_computable_biinfinite_avoidsLong_exp_le {α : ℝ} (hα1 : α < 1) (m W : ℕ)
    (hmW : m ≤ W) (hWm : W + 1 ≤ 2 * m) :
    (2 : ℝ) ^ (α * m) * (2 : ℝ) ^ (W - m) ≤ (2 : ℝ) ^ ((1 + α) / 2 * W) := by
  have hcast : ((W - m : ℕ) : ℝ) = W - m := Nat.cast_sub hmW
  rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num), hcast]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have h1 : (W : ℝ) + 1 ≤ 2 * m := by exact_mod_cast hWm
  have h2 : (0 : ℝ) ≤ 1 - α := by linarith
  nlinarith [mul_nonneg h2 (sub_nonneg.mpr h1), h2]

/-- A polynomial is eventually below an exponential. -/
private lemma exists_computable_biinfinite_avoidsLong_poly_le_exp {δ : ℝ} (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ W : ℕ, N₀ ≤ W → 2 * ((W : ℝ) + 1) ^ 2 ≤ (2 : ℝ) ^ (δ * W) := by
  have hr : 1 < (2 : ℝ) ^ δ := Real.one_lt_rpow (by norm_num) hδ
  have hlim := tendsto_pow_const_div_const_pow_of_one_lt 2 hr
  have hev := hlim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 8 by norm_num))
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max N₀ 1, fun W hW => ?_⟩
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast le_trans (le_max_right _ _) hW
  have h := hN₀ W (le_trans (le_max_left _ _) hW)
  have hrpow : (2 : ℝ) ^ (δ * W) = ((2 : ℝ) ^ δ) ^ W := by
    rw [Real.rpow_mul (by norm_num), Real.rpow_natCast]
  rw [hrpow]
  have hpos : 0 < ((2 : ℝ) ^ δ) ^ W := by positivity
  rw [div_lt_iff₀ hpos] at h
  nlinarith [mul_nonneg (sub_nonneg.mpr hW1) (show (0 : ℝ) ≤ 6 * W + 2 by positivity)]

/-- The windows of length `W` that read, through `rd a b`, a string of `F` or of its reversal. -/
private lemma exists_computable_biinfinite_avoidsLong_term_le {α : ℝ} (hα1 : α < 1)
    {F : Set (List Bool)} (hF : IsAtMostForbidden α F) (a b : ℕ) :
    (({y : List Bool | y.length = exists_computable_biinfinite_avoidsLong_win a b ∧
        exists_computable_biinfinite_avoidsLong_rd a b y ∈
          {u : List Bool | u ∈ F ∨ u.reverse ∈ F}}).ncard : ℝ) ≤
      2 * (2 : ℝ) ^ ((1 + α) / 2 * (exists_computable_biinfinite_avoidsLong_win a b : ℕ)) := by
  have h1 := exists_computable_biinfinite_avoidsLong_ncard_rd_le
    {u : List Bool | u ∈ F ∨ u.reverse ∈ F} a b
  have h2 := exists_computable_biinfinite_avoidsLong_ncard_fpm_le F (a + b + 1)
  have h3 := hF (a + b + 1)
  have hmW : a + b + 1 ≤ exists_computable_biinfinite_avoidsLong_win a b := by
    unfold exists_computable_biinfinite_avoidsLong_win; omega
  have hWm : exists_computable_biinfinite_avoidsLong_win a b + 1 ≤ 2 * (a + b + 1) := by
    unfold exists_computable_biinfinite_avoidsLong_win; omega
  have h4 : (({y : List Bool | y.length = exists_computable_biinfinite_avoidsLong_win a b ∧
        exists_computable_biinfinite_avoidsLong_rd a b y ∈
          {u : List Bool | u ∈ F ∨ u.reverse ∈ F}}).ncard : ℝ) ≤
      2 * (({x ∈ F | x.length = a + b + 1} : Set (List Bool)).ncard : ℝ) *
        (2 : ℝ) ^ (exists_computable_biinfinite_avoidsLong_win a b - (a + b + 1)) := by
    have := (Nat.cast_le (α := ℝ)).mpr (h1.trans (Nat.mul_le_mul_right _ h2))
    push_cast at this
    exact this
  calc _ ≤ 2 * (({x ∈ F | x.length = a + b + 1} : Set (List Bool)).ncard : ℝ) *
          (2 : ℝ) ^ (exists_computable_biinfinite_avoidsLong_win a b - (a + b + 1)) := h4
    _ ≤ 2 * (2 : ℝ) ^ (α * ((a + b + 1 : ℕ) : ℝ)) *
          (2 : ℝ) ^ (exists_computable_biinfinite_avoidsLong_win a b - (a + b + 1)) := by
        gcongr
    _ = 2 * ((2 : ℝ) ^ (α * ((a + b + 1 : ℕ) : ℝ)) *
          (2 : ℝ) ^ (exists_computable_biinfinite_avoidsLong_win a b - (a + b + 1))) := by ring
    _ ≤ _ := by
        gcongr
        exact exists_computable_biinfinite_avoidsLong_exp_le hα1 _ _ hmW hWm

/-- `pos` is primitive recursive. -/
private lemma exists_computable_biinfinite_avoidsLong_primrec_pos :
    Primrec₂ exists_computable_biinfinite_avoidsLong_pos := by
  change Primrec fun p : ℕ × ℕ => if p.2 < p.1 then 2 * (p.1 - p.2) - 1 else 2 * (p.2 - p.1)
  exact Primrec.ite (Primrec.nat_lt.comp Primrec.snd Primrec.fst)
    (Primrec.nat_sub.comp (Primrec.nat_mul.comp (Primrec.const 2)
      (Primrec.nat_sub.comp Primrec.fst Primrec.snd)) (Primrec.const 1))
    (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.nat_sub.comp Primrec.snd Primrec.fst))

/-- `win` is primitive recursive. -/
private lemma exists_computable_biinfinite_avoidsLong_primrec_win :
    Primrec₂ exists_computable_biinfinite_avoidsLong_win := by
  change Primrec fun p : ℕ × ℕ => max (2 * p.1) (2 * p.2 + 1)
  exact Primrec.nat_max.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.fst)
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd)
      (Primrec.const 1))

/-- Reading a window is computable. -/
private lemma exists_computable_biinfinite_avoidsLong_computable_rd :
    Computable (fun q : (List Bool × ℕ) × ℕ =>
      exists_computable_biinfinite_avoidsLong_rd q.1.2 q.2 q.1.1) := by
  unfold exists_computable_biinfinite_avoidsLong_rd
  have hl : Computable (fun q : (List Bool × ℕ) × ℕ => List.range (q.1.2 + q.2 + 1)) :=
    Primrec.list_range.to_comp.comp (Primrec.nat_add.to_comp.comp
      (Primrec.nat_add.to_comp.comp (Computable.snd.comp Computable.fst) Computable.snd)
      (Computable.const 1))
  have hf : Computable₂ (fun (q : (List Bool × ℕ) × ℕ) (j : ℕ) =>
      q.1.1.getD (exists_computable_biinfinite_avoidsLong_pos q.1.2 j) false) :=
    (Primrec.list_getD false).to_comp.comp (Computable.fst.comp (Computable.fst.comp
      Computable.fst))
      (exists_computable_biinfinite_avoidsLong_primrec_pos.to_comp.comp
        (Computable.snd.comp (Computable.fst.comp Computable.fst)) Computable.snd)
  exact Computable.list_map hl hf

/-- Step 3 of the proof of `exists_computable_biinfinite_avoidsLong`: `forb F N` is
decidable when `F` is. -/
private lemma exists_computable_biinfinite_avoidsLong_decidable {F : Set (List Bool)}
    (hdec : ComputablePred (· ∈ F)) (N : ℕ) :
    ComputablePred (· ∈ exists_computable_biinfinite_avoidsLong_forb F N) := by
  obtain ⟨inst, hcomp⟩ := hdec
  obtain ⟨g, hgdef⟩ : ∃ g : List Bool → Bool, g = fun u =>
      @decide (u ∈ F) (inst u) || @decide (u.reverse ∈ F) (inst u.reverse) := ⟨_, rfl⟩
  have hgz : ∀ u, g u = true ↔ u ∈ F ∨ u.reverse ∈ F := by
    intro u
    rw [hgdef]
    simp
  have hg : Computable g := by
    rw [hgdef]
    exact Primrec.or.to_comp.comp hcomp (hcomp.comp Computable.list_reverse)
  -- the indicator of "`(a, b)` is a spec of `y` that reads a string of `F`"
  obtain ⟨tm, htm⟩ : ∃ tm : (List Bool × ℕ) × ℕ → ℕ, tm = fun q =>
      cond (decide (q.1.1.length = exists_computable_biinfinite_avoidsLong_win q.1.2 q.2) &&
        g (exists_computable_biinfinite_avoidsLong_rd q.1.2 q.2 q.1.1)) 1 0 := ⟨_, rfl⟩
  have hlenq : Computable (fun q : (List Bool × ℕ) × ℕ => q.1.1.length) :=
    Computable.list_length.comp (Computable.fst.comp Computable.fst)
  have haq : Computable (fun q : (List Bool × ℕ) × ℕ => q.1.2) :=
    Computable.snd.comp Computable.fst
  have hwinq : Computable (fun q : (List Bool × ℕ) × ℕ =>
      exists_computable_biinfinite_avoidsLong_win q.1.2 q.2) :=
    exists_computable_biinfinite_avoidsLong_primrec_win.to_comp.comp haq Computable.snd
  have hdeceq : Computable (fun q : (List Bool × ℕ) × ℕ =>
      decide (q.1.1.length = exists_computable_biinfinite_avoidsLong_win q.1.2 q.2)) :=
    (PrimrecRel.decide Primrec.eq).to_comp.comp hlenq hwinq
  have hrdq : Computable (fun q : (List Bool × ℕ) × ℕ =>
      exists_computable_biinfinite_avoidsLong_rd q.1.2 q.2 q.1.1) :=
    exists_computable_biinfinite_avoidsLong_computable_rd
  have htmC : Computable tm := by
    rw [htm]
    exact Computable.cond (Primrec.and.to_comp.comp hdeceq (hg.comp hrdq))
      (Computable.const 1) (Computable.const 0)
  -- the number of such specs, as nested sums over lists
  obtain ⟨cnt, hcnt⟩ : ∃ cnt : List Bool → ℕ, cnt = fun y =>
      ((List.range (y.length + 1)).map fun a =>
        ((List.range (y.length + 1)).map fun b => tm ((y, a), b)).sum).sum := ⟨_, rfl⟩
  have hinner : Computable (fun p : List Bool × ℕ =>
      ((List.range (p.1.length + 1)).map fun b => tm (p, b)).sum) :=
    exists_computable_avoidsLong_f1_computable_sum_map
      (Primrec.list_range.to_comp.comp (Primrec.nat_add.to_comp.comp
        (Computable.list_length.comp Computable.fst) (Computable.const 1))) htmC
  have hcntC : Computable cnt := by
    rw [hcnt]
    exact exists_computable_avoidsLong_f1_computable_sum_map
      (Primrec.list_range.to_comp.comp (Primrec.nat_add.to_comp.comp
        Computable.list_length (Computable.const 1))) (hinner.comp Computable.id)
  -- the test
  have hiff : ∀ y : List Bool, y ∈ exists_computable_biinfinite_avoidsLong_forb F N ↔
      N ≤ y.length ∧ 0 < cnt y := by
    intro y
    have hzero : cnt y = 0 ↔ ∀ a ∈ Finset.range (y.length + 1), ∀ b ∈ Finset.range (y.length + 1),
        tm ((y, a), b) = 0 := by
      rw [hcnt]
      simp only [← exists_computable_avoidsLong_f1_sum_range_eq]
      rw [Finset.sum_eq_zero_iff]
      refine forall₂_congr fun a _ => ?_
      rw [Finset.sum_eq_zero_iff]
    rw [Nat.pos_iff_ne_zero, Ne, hzero]
    push Not
    constructor
    · rintro ⟨hN, a, b, hab, hrd⟩
      refine ⟨hN, a, ?_, b, ?_, ?_⟩
      · unfold exists_computable_biinfinite_avoidsLong_win at hab
        simp only [Finset.mem_range]
        omega
      · unfold exists_computable_biinfinite_avoidsLong_win at hab
        simp only [Finset.mem_range]
        omega
      · have hd : decide (y.length = exists_computable_biinfinite_avoidsLong_win a b) = true :=
          decide_eq_true hab
        have hg' : g (exists_computable_biinfinite_avoidsLong_rd a b y) = true :=
          (hgz _).mpr hrd
        simp only [htm, hd, hg', Bool.and_self, Bool.cond_true]
        exact one_ne_zero
    · rintro ⟨hN, a, -, b, -, h⟩
      simp only [htm] at h
      have hc : (decide (y.length = exists_computable_biinfinite_avoidsLong_win a b) &&
          g (exists_computable_biinfinite_avoidsLong_rd a b y)) = true := by
        by_contra hc
        simp only [Bool.not_eq_true] at hc
        simp [hc] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      exact ⟨hN, a, b, hc.1, (hgz _).mp hc.2⟩
  refine ⟨Classical.decPred _, ?_⟩
  have h1 : Computable (fun y : List Bool => decide (N ≤ y.length)) :=
    (PrimrecRel.decide Primrec.nat_le).to_comp.comp (Computable.const N) Computable.list_length
  have h2 : Computable (fun y : List Bool => decide (0 < cnt y)) :=
    (PrimrecRel.decide Primrec.nat_lt).to_comp.comp (Computable.const 0) hcntC
  refine (Primrec.and.to_comp.comp h1 h2).of_eq fun y => ?_
  rw [← Bool.decide_and]
  exact decide_eq_decide.mpr (hiff y).symm

/-- Step 4 of the proof of `exists_computable_biinfinite_avoidsLong`: counting.  For
large `N` the set `forb F N` has at most `2 ^ ((3 + α) / 4 * n)` strings of each length `n`. -/
private lemma exists_computable_biinfinite_avoidsLong_count {α : ℝ} (_hα0 : 0 < α)
    (hα1 : α < 1) {F : Set (List Bool)} (hF : IsAtMostForbidden α F) :
    ∃ N : ℕ, 1 ≤ N ∧
      IsAtMostForbidden ((3 + α) / 4) (exists_computable_biinfinite_avoidsLong_forb F N) := by
  classical
  obtain ⟨N₀, hN₀⟩ := exists_computable_biinfinite_avoidsLong_poly_le_exp
    (δ := (1 - α) / 4) (by linarith)
  refine ⟨max N₀ 1, le_max_right _ _, fun W => ?_⟩
  by_cases hW : max N₀ 1 ≤ W
  · -- the windows of length `W` are covered by those of the pairs `(a, b)` with `win a b = W`
    obtain ⟨T, hT⟩ : ∃ T : Finset (ℕ × ℕ), T = ((Finset.range (W + 1)) ×ˢ
        (Finset.range (W + 1))).filter
          (fun p => exists_computable_biinfinite_avoidsLong_win p.1 p.2 = W) := ⟨_, rfl⟩
    have hsub : ({y ∈ exists_computable_biinfinite_avoidsLong_forb F (max N₀ 1) |
        y.length = W} : Set (List Bool)) ⊆
        ⋃ p ∈ T, {y : List Bool | y.length = W ∧
          exists_computable_biinfinite_avoidsLong_rd p.1 p.2 y ∈
            {u : List Bool | u ∈ F ∨ u.reverse ∈ F}} := by
      rintro y ⟨⟨hN, a, b, hab, hrd⟩, hlen⟩
      simp only [Set.mem_iUnion]
      have hwin : exists_computable_biinfinite_avoidsLong_win a b = W := hab.symm.trans hlen
      have hwin' := hwin
      unfold exists_computable_biinfinite_avoidsLong_win at hwin'
      refine ⟨(a, b), ?_, hlen, hrd⟩
      rw [hT]
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      exact ⟨⟨by omega, by omega⟩, hwin⟩
    have hfinU : (⋃ p ∈ T, {y : List Bool | y.length = W ∧
        exists_computable_biinfinite_avoidsLong_rd p.1 p.2 y ∈
          {u : List Bool | u ∈ F ∨ u.reverse ∈ F}}).Finite :=
      T.finite_toSet.biUnion fun p _ => (finite_length_eq W).subset fun y hy => hy.1
    have hcard := Set.ncard_le_ncard hsub hfinU
    have hbU := exists_computable_biinfinite_avoidsLong_ncard_biUnion_le T
      (fun p => {y : List Bool | y.length = W ∧
        exists_computable_biinfinite_avoidsLong_rd p.1 p.2 y ∈
          {u : List Bool | u ∈ F ∨ u.reverse ∈ F}})
    have hTcard : (T.card : ℝ) ≤ ((W : ℝ) + 1) ^ 2 := by
      have : T.card ≤ (W + 1) ^ 2 := by
        rw [hT]
        refine (Finset.card_filter_le _ _).trans ?_
        rw [Finset.card_product, Finset.card_range, sq]
      exact_mod_cast this
    have hsum : (∑ p ∈ T, (({y : List Bool | y.length = W ∧
        exists_computable_biinfinite_avoidsLong_rd p.1 p.2 y ∈
          {u : List Bool | u ∈ F ∨ u.reverse ∈ F}}).ncard : ℝ)) ≤
        T.card * (2 * (2 : ℝ) ^ ((1 + α) / 2 * W)) := by
      calc _ ≤ ∑ _p ∈ T, 2 * (2 : ℝ) ^ ((1 + α) / 2 * W) := by
            refine Finset.sum_le_sum fun p hp => ?_
            have hpW : exists_computable_biinfinite_avoidsLong_win p.1 p.2 = W := by
              rw [hT] at hp
              exact (Finset.mem_filter.mp hp).2
            have := exists_computable_biinfinite_avoidsLong_term_le hα1 hF p.1 p.2
            rw [hpW] at this
            exact this
        _ = _ := by simp
    have hmain : (({y ∈ exists_computable_biinfinite_avoidsLong_forb F (max N₀ 1) |
        y.length = W} : Set (List Bool)).ncard : ℝ) ≤
        T.card * (2 * (2 : ℝ) ^ ((1 + α) / 2 * W)) := by
      refine le_trans ?_ hsum
      have h1 := hcard.trans hbU
      exact_mod_cast h1
    have hpoly := hN₀ W (le_trans (le_max_left _ _) hW)
    have hexp : (2 : ℝ) ^ ((1 - α) / 4 * (W : ℝ)) * (2 : ℝ) ^ ((1 + α) / 2 * W) =
        (2 : ℝ) ^ ((3 + α) / 4 * (W : ℝ)) := by
      rw [← Real.rpow_add (by norm_num)]
      congr 1
      ring
    calc _ ≤ T.card * (2 * (2 : ℝ) ^ ((1 + α) / 2 * W)) := hmain
      _ ≤ ((W : ℝ) + 1) ^ 2 * (2 * (2 : ℝ) ^ ((1 + α) / 2 * W)) := by
          gcongr
      _ = (2 * ((W : ℝ) + 1) ^ 2) * (2 : ℝ) ^ ((1 + α) / 2 * W) := by ring
      _ ≤ (2 : ℝ) ^ ((1 - α) / 4 * (W : ℝ)) * (2 : ℝ) ^ ((1 + α) / 2 * W) := by
          gcongr
      _ = _ := hexp
  · have hempty : ({x ∈ exists_computable_biinfinite_avoidsLong_forb F (max N₀ 1) |
        x.length = W} : Set (List Bool)) = ∅ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨⟨hN, -⟩, hlen⟩
      omega
    rw [hempty, Set.ncard_empty]
    simp only [Nat.cast_zero]
    positivity

/-- **SUV p. 244**, reported by the book after Problem 248 as an observation of K. Makarychev, with
a sketch and a reference: for decidable `F` there is also a computable bi-infinite sequence with no
long substrings from `F`.  Computability of `z` is that of the two half-sequences. -/
theorem exists_computable_biinfinite_avoidsLong {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {F : Set (List Bool)} (hF : IsAtMostForbidden α F) (hdec : ComputablePred (· ∈ F)) :
    ∃ (c : ℕ) (z : ℤ → Bool), Computable (fun n : ℕ => z n) ∧
      Computable (fun n : ℕ => z (-(n : ℤ))) ∧ ∀ u ∈ F, c ≤ u.length → ¬ OccursInBi u z := by
  obtain ⟨N, hN1, hcount⟩ := exists_computable_biinfinite_avoidsLong_count hα0 hα1 hF
  have hdec' := exists_computable_biinfinite_avoidsLong_decidable hdec N
  obtain ⟨c, w, hw, hav⟩ := exists_computable_avoidsLong (α := (3 + α) / 4) (by linarith)
    (by linarith) hcount hdec'
  obtain ⟨h1, h2⟩ := exists_computable_biinfinite_avoidsLong_halves hw
  refine ⟨max N c, exists_computable_biinfinite_avoidsLong_zOf w, h1, h2,
    fun u hu hlen hocc => ?_⟩
  obtain ⟨y, hy, hylen, hyocc⟩ := exists_computable_biinfinite_avoidsLong_window w hu hN1
    (le_trans (le_max_left _ _) hlen) hocc
  exact hav y hy (le_trans (le_trans (le_max_right _ _) hlen) hylen) hyocc

end Kolmogorov.Applications
