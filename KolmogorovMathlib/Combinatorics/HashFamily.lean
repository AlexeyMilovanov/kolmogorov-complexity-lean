/-
Copyright (c) 2025 The Kolmogorov Project Developers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Kolmogorov Project Developers
-/
import KolmogorovMathlib.Complexity.Incompressibility
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Families of hash functions with the prefix expansion property

The two-condition theorem of SUV Section 12.7 replaces the bipartite expander of Section 12.3
by a family of `N` maps `χ₁, …, χ_N : 𝔹ⁿ → 𝔹ⁿ`, and it uses all the prefixes `[χ_i(x)]_m` at
once.  A left vertex is bad when *most* (not all) of its fingerprints are bad, so the
expansion property is stated for the set of strings `x` whose prefixes land in a small `U` for
at least half of the indices `i`.

Strings are `BitString`s here (not `Fin n → Bool`), so that `prefixBits` is `List.take` and
the sets of arguments and values are the library's `stringsOfLength`.

The existence proof is the book's probabilistic argument made into a count of *tables*: a
family is a table `Fin N × 𝔹ⁿ → 𝔹ⁿ`, the tables violating the property for a pair `(T, U)`
of sets of equal size `t` are at most a `(2^N ε^{N/2})^t` fraction of all tables, and the sum
of these fractions over `m`, `t`, `T`, `U` is less than one.

SUV Section 12.7, pp. 381–382.
-/

namespace Kolmogorov

open Finset

/-- `[u]_m`: the `m`-bit prefix of `u`.

SUV Section 12.7, p. 381. -/
def prefixBits (m : ℕ) (u : BitString) : BitString := u.take m

/-- The strings of length `n` whose `m`-bit fingerprint prefixes land in `U` for at least half
of the indices `i` — the "bad" left vertices of the argument of SUV Section 12.7.

SUV Section 12.7, pp. 381–382. -/
def majorityPrefixHits {N : ℕ} (χ : Fin N → BitString → BitString) (n m : ℕ)
    (U : Finset BitString) : Finset BitString :=
  (stringsOfLength n).filter fun x =>
    N ≤ 2 * (Finset.univ.filter fun i : Fin N => prefixBits m (χ i x) ∈ U).card

section HashTables

/-- A table of hash values: for every index `i < N` and every argument of length `n`, a value
of length `n`.  Choosing a table uniformly is choosing the values `χ_i(x)` independently. -/
private abbrev HashTable (N n : ℕ) := Fin N × ↥(stringsOfLength n) → ↥(stringsOfLength n)

/-- The hash family read off a table: the table value on arguments of length `n`, the zero
string elsewhere. -/
private def tableFamily (N n : ℕ) (f : HashTable N n) : Fin N → BitString → BitString :=
  fun i x => if h : x ∈ stringsOfLength n then (f (i, ⟨x, h⟩)).1 else List.replicate n false

private lemma tableFamily_length (N n : ℕ) (f : HashTable N n) (i : Fin N) (x : BitString) :
    (tableFamily N n f i x).length = n := by
  unfold tableFamily
  split_ifs with h
  · exact (mem_stringsOfLength n _).1 (f (i, ⟨x, h⟩)).2
  · simp

private lemma tableFamily_apply (N n : ℕ) (f : HashTable N n) (i : Fin N)
    (x : ↥(stringsOfLength n)) : tableFamily N n f i x.1 = (f (i, x)).1 := by
  unfold tableFamily
  rw [dite_eq_left x.2]

/-- The values of length `n` whose `m`-bit prefix lies in `U`. -/
private def goodValues (n m : ℕ) (U : Finset BitString) : Finset ↥(stringsOfLength n) :=
  univ.filter fun v => prefixBits m v.1 ∈ U

/-- Each element of `U ⊆ 𝔹ᵐ` has `2^(n-m)` extensions of length `n`. -/
private lemma card_goodValues_le (n m : ℕ) (U : Finset BitString) :
    (goodValues n m U).card ≤ U.card * 2 ^ (n - m) := by
  classical
  calc (goodValues n m U).card
      ≤ ((U ×ˢ stringsOfLength (n - m)).image fun p => p.1 ++ p.2).card := by
        refine card_le_card_of_injOn (fun v => v.1) ?_ Subtype.val_injective.injOn
        intro v hv
        simp only [goodValues, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hv
        simp only [coe_image, coe_product, Set.mem_image, Set.mem_prod, mem_coe, Prod.exists]
        refine ⟨v.1.take m, v.1.drop m, ⟨hv, ?_⟩, List.take_append_drop m v.1⟩
        rw [mem_stringsOfLength, List.length_drop, (mem_stringsOfLength n _).1 v.2]
    _ ≤ (U ×ˢ stringsOfLength (n - m)).card := card_image_le
    _ = U.card * 2 ^ (n - m) := by rw [card_product, card_stringsOfLength]

/-- The constrained coordinates of a table: the pairs `(i, x)` with `x ∈ T` and `i ∈ X x`. -/
private def constrained (N n : ℕ) (T : Finset BitString) (X : ↥T → Finset (Fin N)) :
    Finset (Fin N × ↥(stringsOfLength n)) :=
  univ.filter fun p => ∃ h : p.2.1 ∈ T, p.1 ∈ X ⟨p.2.1, h⟩

/-- There are at least `∑ x, |X x|` constrained coordinates. -/
private lemma sum_card_le_card_constrained (N n : ℕ) (T : Finset BitString)
    (hT : T ⊆ stringsOfLength n) (X : ↥T → Finset (Fin N)) :
    ∑ x : ↥T, (X x).card ≤ (constrained N n T X).card := by
  classical
  let φ : (Σ x : ↥T, ↥(X x)) → Fin N × ↥(stringsOfLength n) :=
    fun q => (q.2.1, ⟨q.1.1, hT q.1.2⟩)
  have hcard : Fintype.card (Σ x : ↥T, ↥(X x)) = ∑ x : ↥T, (X x).card := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_coe]
  rw [← hcard, ← card_univ]
  refine card_le_card_of_injOn φ ?_ ?_
  · intro q _
    simp only [constrained, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq]
    exact ⟨q.1.2, q.2.2⟩
  · rintro ⟨⟨x, hx⟩, ⟨i, hi⟩⟩ _ ⟨⟨x', hx'⟩, ⟨i', hi'⟩⟩ _ h
    simp only [φ, Prod.mk.injEq, Subtype.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl

/-- The tables in which, for every `x ∈ T` and every `i ∈ X x`, `[χ_i(x)]_m ∈ U`. -/
private def constrainedTables (N n m : ℕ) (T : Finset BitString) (X : ↥T → Finset (Fin N))
    (U : Finset BitString) : Finset (HashTable N n) :=
  univ.filter fun f => ∀ x : ↥T, ∀ i ∈ X x, prefixBits m (tableFamily N n f i x.1) ∈ U

private lemma constrainedTables_subset_piFinset (N n m : ℕ) (T : Finset BitString)
    (X : ↥T → Finset (Fin N)) (U : Finset BitString) :
    constrainedTables N n m T X U ⊆ Fintype.piFinset fun p =>
      if p ∈ constrained N n T X then goodValues n m U else univ := by
  classical
  intro f hf
  rw [Fintype.mem_piFinset]
  intro p
  split_ifs with hp
  · obtain ⟨h, hi⟩ := (mem_filter.1 hp).2
    have := (mem_filter.1 hf).2 ⟨p.2.1, h⟩ p.1 hi
    rw [tableFamily_apply] at this
    simpa [goodValues] using this
  · exact mem_univ _

/-- The constrained tables are at most an `ε^{|constrained|}` fraction of all tables when the
good values are at most an `ε` fraction of all values. -/
private lemma card_constrainedTables_le (N n m : ℕ) (T : Finset BitString)
    (X : ↥T → Finset (Fin N)) (U : Finset BitString) (ε : ℝ)
    (hG : ((goodValues n m U).card : ℝ) ≤ ε * Fintype.card ↥(stringsOfLength n)) :
    ((constrainedTables N n m T X U).card : ℝ) ≤
      Fintype.card (HashTable N n) * ε ^ (constrained N n T X).card := by
  classical
  set C := constrained N n T X
  set D : ℝ := (Fintype.card ↥(stringsOfLength n) : ℝ)
  have hD : 0 ≤ D := by positivity
  calc ((constrainedTables N n m T X U).card : ℝ)
      ≤ ((Fintype.piFinset fun p =>
          if p ∈ C then goodValues n m U else (univ : Finset ↥(stringsOfLength n))).card : ℝ) := by
        exact_mod_cast card_le_card (constrainedTables_subset_piFinset N n m T X U)
    _ = ∏ p : Fin N × ↥(stringsOfLength n),
          (if p ∈ C then ((goodValues n m U).card : ℝ) else D) := by
        rw [Fintype.card_piFinset]
        push_cast
        refine prod_congr rfl fun p _ => ?_
        split_ifs <;> simp [D]
    _ ≤ ∏ p : Fin N × ↥(stringsOfLength n), (if p ∈ C then ε else 1) * D := by
        refine prod_le_prod₀ (fun p _ => ?_) (fun p _ => ?_)
        · split_ifs <;> positivity
        · split_ifs
          · simpa using hG
          · simp
    _ = ε ^ C.card * Fintype.card (HashTable N n) := by
        rw [prod_mul_distrib, prod_ite_mem, univ_inter, prod_const, prod_const, card_univ,
          Fintype.card_fun]
        push_cast
        ring
    _ = Fintype.card (HashTable N n) * ε ^ C.card := by ring

/-- The tables in which every `x ∈ T` has `[χ_i(x)]_m ∈ U` for at least half of the `i`. -/
private def majorityTables (N n m : ℕ) (T U : Finset BitString) : Finset (HashTable N n) :=
  univ.filter fun f => ∀ x ∈ T,
    N ≤ 2 * (univ.filter fun i : Fin N => prefixBits m (tableFamily N n f i x) ∈ U).card

private lemma majorityTables_subset_biUnion (N n m : ℕ) (T U : Finset BitString) :
    majorityTables N n m T U ⊆
      (univ.filter fun X : ↥T → Finset (Fin N) => ∀ x, N ≤ 2 * (X x).card).biUnion
        fun X => constrainedTables N n m T X U := by
  classical
  intro f hf
  rw [mem_biUnion]
  refine ⟨fun x => univ.filter fun i => prefixBits m (tableFamily N n f i x.1) ∈ U, ?_, ?_⟩
  · exact mem_filter.2 ⟨mem_univ _, fun x => (mem_filter.1 hf).2 x.1 x.2⟩
  · exact mem_filter.2 ⟨mem_univ _, fun x i hi => (mem_filter.1 hi).2⟩

/-- The number of `X : T → Finset (Fin N)` is `(2^N)^{|T|}`. -/
private lemma card_fun_finset_fin (N : ℕ) (T : Finset BitString) :
    Fintype.card (↥T → Finset (Fin N)) = (2 ^ N) ^ T.card := by
  rw [Fintype.card_fun, Fintype.card_finset, Fintype.card_fin, Fintype.card_coe]

/-- The book's bound `(2^N ε^{N/2})^{|T|}` on the fraction of tables in which every `x ∈ T`
has at least half of its fingerprints in `U`. -/
private lemma card_majorityTables_le (N n m : ℕ) (T U : Finset BitString) (ε : ℝ) (hε0 : 0 < ε)
    (hε1 : ε ≤ 1) (hT : T ⊆ stringsOfLength n)
    (hG : ((goodValues n m U).card : ℝ) ≤ ε * Fintype.card ↥(stringsOfLength n)) :
    ((majorityTables N n m T U).card : ℝ) ≤
      Fintype.card (HashTable N n) * (2 ^ N * ε ^ ((N : ℝ) / 2)) ^ T.card := by
  classical
  set S := univ.filter fun X : ↥T → Finset (Fin N) => ∀ x, N ≤ 2 * (X x).card
  have hpow : ∀ X ∈ S, ε ^ (constrained N n T X).card ≤ (ε ^ ((N : ℝ) / 2)) ^ T.card := by
    intro X hX
    rw [← Real.rpow_natCast, ← Real.rpow_natCast (ε ^ ((N : ℝ) / 2)), ← Real.rpow_mul hε0.le]
    refine Real.rpow_le_rpow_of_exponent_ge hε0 hε1 ?_
    have h1 : ((∑ x : ↥T, (X x).card : ℕ) : ℝ) ≤ (constrained N n T X).card := by
      exact_mod_cast sum_card_le_card_constrained N n T hT X
    have h2 : ∑ x : ↥T, ((N : ℝ) / 2) ≤ ∑ x : ↥T, ((X x).card : ℝ) := by
      refine sum_le_sum fun x _ => ?_
      have := (mem_filter.1 hX).2 x
      have h' : (N : ℝ) ≤ 2 * (X x).card := by exact_mod_cast this
      linarith
    rw [sum_const, card_univ, Fintype.card_coe, nsmul_eq_mul] at h2
    push_cast at h1
    linarith
  calc ((majorityTables N n m T U).card : ℝ)
      ≤ ((S.biUnion fun X => constrainedTables N n m T X U).card : ℝ) := by
        exact_mod_cast card_le_card (majorityTables_subset_biUnion N n m T U)
    _ ≤ ∑ X ∈ S, ((constrainedTables N n m T X U).card : ℝ) := by
        exact_mod_cast card_biUnion_le
    _ ≤ ∑ X ∈ S, (Fintype.card (HashTable N n) : ℝ) * (ε ^ ((N : ℝ) / 2)) ^ T.card := by
        refine sum_le_sum fun X hX => ?_
        refine (card_constrainedTables_le N n m T X U ε hG).trans ?_
        exact mul_le_mul_of_nonneg_left (hpow X hX) (by positivity)
    _ = S.card * (Fintype.card (HashTable N n) * (ε ^ ((N : ℝ) / 2)) ^ T.card) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ ((2 ^ N) ^ T.card : ℕ) * (Fintype.card (HashTable N n) * (ε ^ ((N : ℝ) / 2)) ^ T.card) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        rw [← card_fun_finset_fin N T, ← card_univ]
        exact_mod_cast card_filter_le _ _
    _ = Fintype.card (HashTable N n) * (2 ^ N * ε ^ ((N : ℝ) / 2)) ^ T.card := by
        push_cast
        rw [mul_pow]
        ring

/-- The geometric tail `∑_{t=1}^{K} r^t ≤ 2r` for `0 ≤ r ≤ 1/2`. -/
private lemma sum_pow_Icc_le (r : ℝ) (hr0 : 0 ≤ r) (hr1 : 2 * r ≤ 1) (K : ℕ) :
    ∑ t ∈ Icc 1 K, r ^ t ≤ 2 * r := by
  suffices h : ∑ t ∈ Icc 1 K, r ^ t + 2 * r ^ (K + 1) ≤ 2 * r by
    have : 0 ≤ 2 * r ^ (K + 1) := by positivity
    linarith
  induction K with
  | zero => simp
  | succ K ih =>
    rw [sum_Icc_succ_top (by omega)]
    have : 2 * r ^ (K + 1 + 1) ≤ r ^ (K + 1) := by
      rw [pow_succ]
      have : 0 ≤ r ^ (K + 1) := by positivity
      nlinarith
    linarith

end HashTables

/-- The hash family of SUV Section 12.7: if `n · 2^{N+2n+1} · ε^{N/2} < 1` then there are `N`
maps `χ₁, …, χ_N : 𝔹ⁿ → 𝔹ⁿ` such that for every `m ∈ {1, …, n}` and every nonempty
`U ⊆ 𝔹ᵐ` with `|U| ≤ ε 2^m`, fewer than `|U|` strings `x ∈ 𝔹ⁿ` have `[χ_i(x)]_m ∈ U` for at
least half of the indices `i`.

The exponent `N/2` is the real one (`Real.rpow`), as in the book, not natural division.

SUV Lemma of Section 12.7, pp. 381–382. -/
theorem exists_prefixHashFamily (n N : ℕ) (ε : ℝ) (hn : 0 < n) (hN : 0 < N) (hε : 0 < ε)
    (hbound : (n : ℝ) * 2 ^ (N + 2 * n + 1) * ε ^ ((N : ℝ) / 2) < 1) :
    ∃ χ : Fin N → BitString → BitString,
      (∀ i x, (χ i x).length = n) ∧
      ∀ m : ℕ, 1 ≤ m → m ≤ n → ∀ U : Finset BitString, U.Nonempty →
        (∀ u ∈ U, u.length = m) → (U.card : ℝ) ≤ ε * 2 ^ m →
        (majorityPrefixHits χ n m U).card < U.card := by
  classical
  have hpow0 : 0 < ε ^ ((N : ℝ) / 2) := by positivity
  have hkey : 2 * (2 ^ (N + 2 * n) * ε ^ ((N : ℝ) / 2)) < 1 := by
    have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have h2 : (2 : ℝ) ^ (N + 2 * n + 1) = 2 * 2 ^ (N + 2 * n) := by rw [pow_succ]; ring
    rw [h2] at hbound
    have h3 : 0 < 2 * (2 ^ (N + 2 * n) * ε ^ ((N : ℝ) / 2)) := by positivity
    nlinarith
  have hε1 : ε ≤ 1 := by
    by_contra h
    push Not at h
    have h1 : 1 ≤ ε ^ ((N : ℝ) / 2) := Real.one_le_rpow h.le (by positivity)
    have h2 : (1 : ℝ) ≤ 2 ^ (N + 2 * n) := one_le_pow₀ (by norm_num)
    nlinarith
  set r0 : ℝ := 2 ^ N * ε ^ ((N : ℝ) / 2) with hr0
  have hr0pos : 0 < r0 := by positivity
  have hratio : ∀ m ≤ n,
      2 * (2 ^ m * 2 ^ n * r0) ≤ 2 * (2 ^ (N + 2 * n) * ε ^ ((N : ℝ) / 2)) := by
    intro m hm
    have h2 : (2 : ℝ) ^ (N + 2 * n) = 2 ^ N * (2 ^ n * 2 ^ n) := by
      rw [pow_add, two_mul, pow_add]
    rw [h2, hr0]
    calc 2 * (2 ^ m * 2 ^ n * (2 ^ N * ε ^ ((N : ℝ) / 2)))
        = 2 * ((2 : ℝ) ^ m * (2 ^ n * 2 ^ N * ε ^ ((N : ℝ) / 2))) := by ring
      _ ≤ 2 * ((2 : ℝ) ^ n * (2 ^ n * 2 ^ N * ε ^ ((N : ℝ) / 2))) := by gcongr; norm_num
      _ = 2 * (2 ^ N * (2 ^ n * 2 ^ n) * ε ^ ((N : ℝ) / 2)) := by ring
  by_contra hcon
  push Not at hcon
  set K : ℕ → ℕ := fun m => ⌊ε * 2 ^ m⌋₊ with hK
  set bad : Finset (HashTable N n) := (Icc 1 n).biUnion fun m => (Icc 1 (K m)).biUnion fun t =>
    (powersetCard t (stringsOfLength m)).biUnion fun U =>
      (powersetCard t (stringsOfLength n)).biUnion fun T => majorityTables N n m T U with hbad
  have hcover : (univ : Finset (HashTable N n)) ⊆ bad := by
    intro f _
    obtain ⟨m, hm1, hmn, U, hUne, hUlen, hUcard, hUmaj⟩ :=
      hcon (tableFamily N n f) (tableFamily_length N n f)
    obtain ⟨T, hTsub, hTcard⟩ := exists_subset_card_eq hUmaj
    simp only [hbad, mem_biUnion, mem_Icc, mem_powersetCard]
    refine ⟨m, ⟨hm1, hmn⟩, U.card, ⟨hUne.card_pos, Nat.le_floor hUcard⟩, U,
      ⟨fun u hu => (mem_stringsOfLength m u).2 (hUlen u hu), rfl⟩, T,
      ⟨hTsub.trans (filter_subset _ _), hTcard⟩, ?_⟩
    refine mem_filter.2 ⟨mem_univ _, fun x hx => ?_⟩
    simpa [majorityPrefixHits] using (mem_filter.1 (hTsub hx)).2
  have hΩ : (0 : ℝ) < Fintype.card (HashTable N n) := by
    have : Nonempty (HashTable N n) :=
      ⟨fun _ => ⟨List.replicate n false, by simp [mem_stringsOfLength]⟩⟩
    exact_mod_cast Fintype.card_pos
  have hG : ∀ m, m ≤ n → ∀ t ∈ Icc 1 (K m), ∀ U ∈ powersetCard t (stringsOfLength m),
      ((goodValues n m U).card : ℝ) ≤ ε * Fintype.card ↥(stringsOfLength n) := by
    intro m hmn t ht U hU
    rw [mem_powersetCard] at hU
    have htK : (t : ℝ) ≤ ε * 2 ^ m := (Nat.le_floor_iff (by positivity)).1 (mem_Icc.1 ht).2
    calc ((goodValues n m U).card : ℝ)
        ≤ U.card * 2 ^ (n - m) := by exact_mod_cast card_goodValues_le n m U
      _ ≤ ε * 2 ^ m * 2 ^ (n - m) := by rw [hU.2]; gcongr
      _ = ε * 2 ^ n := by rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hmn]
      _ = ε * Fintype.card ↥(stringsOfLength n) := by
          rw [Fintype.card_coe, card_stringsOfLength]; push_cast; ring
  have hsum1 : (Fintype.card (HashTable N n) : ℝ) ≤ ∑ m ∈ Icc 1 n, ∑ t ∈ Icc 1 (K m),
      ∑ U ∈ powersetCard t (stringsOfLength m), ∑ T ∈ powersetCard t (stringsOfLength n),
        ((majorityTables N n m T U).card : ℝ) := by
    have h := card_le_card hcover
    rw [card_univ] at h
    refine (Nat.cast_le.2 h).trans ?_
    refine (Nat.cast_le.2 card_biUnion_le).trans ?_
    push_cast
    refine sum_le_sum fun m _ => ?_
    refine (Nat.cast_le.2 card_biUnion_le).trans ?_
    push_cast
    refine sum_le_sum fun t _ => ?_
    refine (Nat.cast_le.2 card_biUnion_le).trans ?_
    push_cast
    refine sum_le_sum fun U _ => ?_
    exact_mod_cast card_biUnion_le
  have hsum2 : ∀ m ∈ Icc 1 n, ∀ t ∈ Icc 1 (K m),
      ∑ U ∈ powersetCard t (stringsOfLength m), ∑ T ∈ powersetCard t (stringsOfLength n),
        ((majorityTables N n m T U).card : ℝ) ≤
      Fintype.card (HashTable N n) * (2 ^ m * 2 ^ n * r0) ^ t := by
    intro m hm t ht
    have hmn := (mem_Icc.1 hm).2
    have h1 : (powersetCard t (stringsOfLength m)).card ≤ (2 ^ m) ^ t := by
      rw [card_powersetCard, card_stringsOfLength]; exact Nat.choose_le_pow _ _
    have h2 : (powersetCard t (stringsOfLength n)).card ≤ (2 ^ n) ^ t := by
      rw [card_powersetCard, card_stringsOfLength]; exact Nat.choose_le_pow _ _
    calc ∑ U ∈ powersetCard t (stringsOfLength m), ∑ T ∈ powersetCard t (stringsOfLength n),
          ((majorityTables N n m T U).card : ℝ)
        ≤ ∑ U ∈ powersetCard t (stringsOfLength m), ∑ T ∈ powersetCard t (stringsOfLength n),
          (Fintype.card (HashTable N n) : ℝ) * r0 ^ t := by
          refine sum_le_sum fun U hU => sum_le_sum fun T hT => ?_
          have hT' := mem_powersetCard.1 hT
          rw [← hT'.2]
          exact card_majorityTables_le N n m T U ε hε hε1 hT'.1 (hG m hmn t ht U hU)
      _ = (powersetCard t (stringsOfLength m)).card * ((powersetCard t (stringsOfLength n)).card *
            (Fintype.card (HashTable N n) * r0 ^ t)) := by
          simp only [sum_const, nsmul_eq_mul]
      _ ≤ ((2 ^ m) ^ t : ℕ) * (((2 ^ n) ^ t : ℕ) * (Fintype.card (HashTable N n) * r0 ^ t)) := by
          gcongr
      _ = Fintype.card (HashTable N n) * (2 ^ m * 2 ^ n * r0) ^ t := by push_cast; ring
  have hfinal : (Fintype.card (HashTable N n) : ℝ) ≤
      Fintype.card (HashTable N n) * (n * (2 * (2 ^ (N + 2 * n) * ε ^ ((N : ℝ) / 2)))) := by
    refine hsum1.trans ?_
    calc ∑ m ∈ Icc 1 n, ∑ t ∈ Icc 1 (K m), ∑ U ∈ powersetCard t (stringsOfLength m),
          ∑ T ∈ powersetCard t (stringsOfLength n), ((majorityTables N n m T U).card : ℝ)
        ≤ ∑ m ∈ Icc 1 n, ∑ t ∈ Icc 1 (K m),
            (Fintype.card (HashTable N n) : ℝ) * (2 ^ m * 2 ^ n * r0) ^ t :=
          sum_le_sum fun m hm => sum_le_sum fun t ht => hsum2 m hm t ht
      _ = ∑ m ∈ Icc 1 n,
            (Fintype.card (HashTable N n) : ℝ) * ∑ t ∈ Icc 1 (K m), (2 ^ m * 2 ^ n * r0) ^ t := by
          simp only [mul_sum]
      _ ≤ ∑ m ∈ Icc 1 n,
            (Fintype.card (HashTable N n) : ℝ) * (2 * (2 ^ (N + 2 * n) * ε ^ ((N : ℝ) / 2))) := by
          refine sum_le_sum fun m hm => mul_le_mul_of_nonneg_left ?_ hΩ.le
          have hmn := (mem_Icc.1 hm).2
          exact (sum_pow_Icc_le _ (by positivity) ((hratio m hmn).trans hkey.le) _).trans
            (hratio m hmn)
      _ = Fintype.card (HashTable N n) * (n * (2 * (2 ^ (N + 2 * n) * ε ^ ((N : ℝ) / 2)))) := by
          rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]; ring
  have hq : (n : ℝ) * (2 * (2 ^ (N + 2 * n) * ε ^ ((N : ℝ) / 2))) < 1 := by
    have h2 : (2 : ℝ) ^ (N + 2 * n + 1) = 2 * 2 ^ (N + 2 * n) := by rw [pow_succ]; ring
    rw [h2] at hbound
    linarith [hbound]
  have := mul_lt_mul_of_pos_left hq hΩ
  linarith

/-- A specialization of `exists_prefixHashFamily` used in the two-condition theorem. -/
theorem exists_prefixHashFamily_twoConditions (n : ℕ) (hn : 0 < n)
    (hbound : (n : ℝ) * 2 ^ (2 * n + 2 + 2 * n + 1) * (1 / 64) ^ (((2 * n + 2 : ℕ) : ℝ) / 2) < 1) :
    ∃ χ : Fin (2 * n + 2) → BitString → BitString,
      (∀ i x, (χ i x).length = n) ∧
      ∀ m : ℕ, 1 ≤ m → m ≤ n → ∀ U : Finset BitString, U.Nonempty →
        (∀ u ∈ U, u.length = m) → (U.card : ℝ) ≤ (1 / 64) * 2 ^ m →
        (majorityPrefixHits χ n m U).card < U.card := by
  have hN : 0 < 2 * n + 2 := by omega
  have hε : (0 : ℝ) < 1 / 64 := by norm_num
  exact exists_prefixHashFamily n (2 * n + 2) (1 / 64) hn hN hε hbound

end Kolmogorov
