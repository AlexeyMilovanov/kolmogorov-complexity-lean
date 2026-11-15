/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Complexity.Applications.LibraryAPI
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.NumberTheory.PrimeCounting

/-!
# There are infinitely many primes (SUV Section 8.1, p. 233)

The book's "toy example" has no numbered statement.  The fact itself is Mathlib's
`Nat.infinite_setOfPred_prime`.  What the argument of the book adds is a complexity bound for
numbers all of whose prime factors lie in a fixed finite set,
`plainK_natBits_le_of_primeFactors`, and, in the footnote after Li and Vitányi, a bound
`log p_n ≤ K(n) + O(1)` for infinitely many `n`.

The combinatorial translation of the footnote, the divergence of `∑ 1/p`, is Mathlib's
`not_summable_one_div_on_primes`.
-/

namespace Kolmogorov.Applications

open Filter

/-- **SUV p. 233.**  There are infinitely many primes (Euclid). -/
theorem infinite_setOf_prime' : {p : ℕ | p.Prime}.Infinite := Nat.infinite_setOfPred_prime

open Finset Finsupp

private lemma foldl_mul_eq_mul_foldl (l : List ℕ) (f : ℕ → ℕ) (a : ℕ) :
  l.foldl (fun acc p => acc * f p) a = a * l.foldl (fun acc p => acc * f p) 1 := by
  induction l generalizing a with
  | nil => simp
  | cons hd tl ih =>
    rw [List.foldl_cons, List.foldl_cons, ih (a * f hd), ih (1 * f hd), one_mul, mul_assoc]

private lemma foldl_eq_prod_map (l : List ℕ) (f : ℕ → ℕ) :
  l.foldl (fun acc p => acc * f p) 1 = (l.map f).prod := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    rw [List.map_cons, List.prod_cons, List.foldl_cons]
    rw [foldl_mul_eq_mul_foldl, ih, one_mul]

/-- Step 1 of the proof of `plainK_natBits_le_of_primeFactors`: a number with prime
factors only in P is the product of those primes to their factorization exponents, and each exponent
is at most log_2 x. -/
private theorem plainK_natBits_le_of_primeFactors_exponents (P : Finset ℕ) :
    ∀ x : ℕ, 2 ≤ x → (∀ p, p.Prime → p ∣ x → p ∈ P) →
      x = P.toList.foldl (fun acc p => acc * p ^ (Nat.factorization x p)) 1 ∧
      ∀ p ∈ P, Nat.factorization x p ≤ Nat.log 2 x := by
  intro x hx2 hP
  have hx0 : x ≠ 0 := by linarith
  constructor
  · have h1 : x = x.factorization.prod (fun p e => p ^ e) := (Nat.prod_factorization_pow_eq_self
      hx0).symm
    have h2 : x.factorization.support ⊆ P := by
      intro p hp
      rw [Nat.support_factorization, Nat.mem_primeFactors] at hp
      exact hP p hp.1 hp.2.1
    have h3 : x.factorization.prod (fun p e => p ^ e) = ∏ p ∈ P, p ^ (x.factorization p) := by
      apply Finsupp.prod_of_support_subset x.factorization h2
      intro i _
      exact pow_zero i
    have h4 : ∏ p ∈ P, p ^ (x.factorization p) = (P.toList.map (fun p => p ^ (Nat.factorization x
        p))).prod := by
      rw [Finset.prod_map_toList]
    have h5 : (P.toList.map (fun p => p ^ (Nat.factorization x p))).prod = P.toList.foldl (fun acc p
        => acc * p ^ (Nat.factorization x p)) 1 := by
      rw [← foldl_eq_prod_map]
    calc x
      _ = x.factorization.prod (fun p e => p ^ e) := h1
      _ = ∏ p ∈ P, p ^ (x.factorization p) := h3
      _ = (P.toList.map (fun p => p ^ (Nat.factorization x p))).prod := h4
      _ = P.toList.foldl (fun acc p => acc * p ^ (Nat.factorization x p)) 1 := h5
  · intro p _
    by_cases hp : p.Prime
    · have h_dvd : p ^ (x.factorization p) ∣ x := Nat.ordProj_dvd x p
      have h_le : p ^ (x.factorization p) ≤ x := Nat.le_of_dvd (by linarith) h_dvd
      have h_2_le_p : 2 ≤ p := hp.two_le
      have h_pow_le : 2 ^ (x.factorization p) ≤ x := by
        calc
          2 ^ (x.factorization p) ≤ p ^ (x.factorization p) := Nat.pow_le_pow_left h_2_le_p _
          _ ≤ x := h_le
      exact Nat.le_log_of_pow_le (by decide) h_pow_le
    · have h_zero : x.factorization p = 0 := by
        rw [Nat.factorization_eq_zero_iff]
        left
        exact hp
      rw [h_zero]
      exact Nat.zero_le _

/-- Step 2 of the proof of `plainK_natBits_le_of_primeFactors`: the optimal plain
complexity of such a product is bounded by O(log log x), since it is determined by the list of
exponents, each ≤ log_2 x. -/
private def plainK_natBits_le_of_primeFactors_complexity_G (L : List ℕ) : BitString →
    BitString :=
  fun s =>
    let es := decodeListCode s
    let res := L.foldl (fun (acc_es : ℕ × List BitString) q =>
      let e_str := acc_es.2.headI
      let e := decodeBits e_str
      let next_acc := acc_es.1 * q ^ e
      (next_acc, acc_es.2.tail)
    ) (1, es)
    natBits res.1

private lemma plainK_natBits_le_of_primeFactors_complexity_G_computable (L : List ℕ) : 
  Computable (plainK_natBits_le_of_primeFactors_complexity_G L) := by
  have h1 : Primrec (fun s : BitString => (1, decodeListCode s)) :=
    (Primrec.const 1).pair decodeListCode_primrec
  have h2 : Primrec (fun s : BitString => L.foldl (fun (acc_es : ℕ × List BitString) (q : ℕ) =>
      (acc_es.1 * q ^ (decodeBits acc_es.2.headI), acc_es.2.tail)) (1, decodeListCode s)) := by
    have hm1 : Primrec (fun (p : BitString × ((ℕ × List BitString) × ℕ)) => p.2.1.1) :=
      (Primrec.fst.comp Primrec.fst).comp Primrec.snd
    have hm2 : Primrec (fun (p : BitString × ((ℕ × List BitString) × ℕ)) => p.2.2 ^ (decodeBits
        p.2.1.2.headI)) := by
      have hm21 : Primrec (fun (p : BitString × ((ℕ × List BitString) × ℕ)) => p.2.2) :=
          Primrec.snd.comp Primrec.snd
      have hm22 : Primrec (fun (p : BitString × ((ℕ × List BitString) × ℕ)) => decodeBits
          p.2.1.2.headI) :=
        primrec_decodeBits.comp (Primrec.list_headI.comp (Primrec.snd.comp (Primrec.fst.comp
            Primrec.snd)))
      exact (Primrec₂.unpaired'.mp Nat.Primrec.pow).comp hm21 hm22
    have h3 : Primrec₂ (fun (_ : BitString) (p : (ℕ × List BitString) × ℕ) => (p.1.1 * p.2 ^
        (decodeBits p.1.2.headI), p.1.2.tail)) :=
      Primrec.to₂ (Primrec.pair ((Primrec₂.unpaired'.mp Nat.Primrec.mul).comp hm1 hm2)
          (Primrec.list_tail.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))))
    exact Primrec.list_foldl (Primrec.const L) h1 h3
  exact natBits_computable.comp (Primrec.to_comp (Primrec.fst.comp h2))

private lemma plainK_natBits_le_of_primeFactors_complexity_G_spec
  (L : List ℕ) (f : ℕ → ℕ) :
  plainK_natBits_le_of_primeFactors_complexity_G L (listCode (L.map fun q => natBits (f q))) =
      
  natBits (L.foldl (fun acc q => acc * q ^ (f q)) 1) := by
  dsimp [plainK_natBits_le_of_primeFactors_complexity_G]
  rw [decodeListCode_listCode]
  have h_fold : ∀ (acc : ℕ) (L' : List ℕ),
    L'.foldl (fun (acc_es : ℕ × List BitString) q =>
      (acc_es.1 * q ^ (decodeBits acc_es.2.headI), acc_es.2.tail)
    ) (acc, L'.map fun q => natBits (f q)) = 
    (L'.foldl (fun acc q => acc * q ^ (f q)) acc, []) := by
    intro acc L'
    induction L' generalizing acc with
    | nil => rfl
    | cons hd tl ih =>
      rw [List.map_cons, List.foldl_cons, List.foldl_cons]
      dsimp
      have h1 : decodeBits (natBits (f hd)) = f hd := decodeBits_natBits (f hd)
      rw [h1]
      exact ih (acc * hd ^ (f hd))
  have h := h_fold 1 L
  rw [h]

private lemma plainK_natBits_le_of_primeFactors_test_bound (L : List ℕ) (f : ℕ → ℕ) (x : ℕ)
    (hf : ∀ p ∈ L, f p ≤ Nat.log 2 x) :
  (listCode (L.map fun q => natBits (f q))).length ≤ L.length * (2 * (Nat.log 2 (Nat.log 2 x)) + 3)
      := by
  induction L with
  | nil => simp
  | cons hd tl ih =>
    rw [List.map_cons, length_listCode_cons, List.length_cons]
    have h1 : (natBits (f hd)).length ≤ Nat.log 2 (f hd) + 1 := length_natBits_le_log (f hd)
    have h2 : Nat.log 2 (f hd) ≤ Nat.log 2 (Nat.log 2 x) := by
      apply Nat.log_mono_right
      apply hf hd
      simp
    have h3 : (natBits (f hd)).length ≤ Nat.log 2 (Nat.log 2 x) + 1 := by omega
    have h4 : 2 * (natBits (f hd)).length + 1 ≤ 2 * Nat.log 2 (Nat.log 2 x) + 3 := by omega
    have h5 : (listCode (tl.map fun q => natBits (f q))).length ≤ tl.length * (2 * Nat.log 2
        (Nat.log 2 x) + 3) := by
      apply ih
      intro p hp
      apply hf
      simp [hp]
    calc 2 * (natBits (f hd)).length + 1 + (listCode (tl.map fun q => natBits (f q))).length
      _ ≤ 2 * Nat.log 2 (Nat.log 2 x) + 3 + tl.length * (2 * Nat.log 2 (Nat.log 2 x) + 3) := by
          gcongr
      _ = (tl.length + 1) * (2 * Nat.log 2 (Nat.log 2 x) + 3) := by ring

/-- Step 2 of the proof of `plainK_natBits_le_of_primeFactors`: the optimal plain
complexity of such a product is bounded by O(log log x), since it is determined by the list of
exponents, each ≤ log_2 x. -/
private theorem plainK_natBits_le_of_primeFactors_complexity (V : Map) (hV :
    isOptimalConditional V) (P : Finset ℕ) :
    ∃ c : ℕ, ∀ f : ℕ → ℕ, ∀ x : ℕ, 2 ≤ x → (∀ p ∈ P, f p ≤ Nat.log 2 x) → 
      plainK V (natBits (P.toList.foldl (fun acc p => acc * p ^ (f p)) 1)) ≤ 
      ((c * Nat.log 2 (Nat.log 2 x) + c : ℕ) : ℕ∞) := by
  let G := plainK_natBits_le_of_primeFactors_complexity_G P.toList
  have hG_comp := plainK_natBits_le_of_primeFactors_complexity_G_computable P.toList
  obtain ⟨c_map, hc_map⟩ := plainK_map_le V hV G hG_comp
  obtain ⟨c_len, hc_len⟩ := plainK_le_length V hV
  set m := P.toList.length
  let c := 3 * m + c_map + c_len
  use c
  intro f x _ hf
  have h_code : plainK V (natBits (P.toList.foldl (fun acc p => acc * p ^ (f p)) 1)) = plainK V (G
      (listCode (P.toList.map fun q => natBits (f q)))) := by
    have h_spec := plainK_natBits_le_of_primeFactors_complexity_G_spec P.toList f
    rw [← h_spec]
  rw [h_code]
  have h1 : plainK V (G (listCode (P.toList.map fun q => natBits (f q)))) ≤ plainK V (listCode
      (P.toList.map fun q => natBits (f q))) + c_map := hc_map _
  have h2 : plainK V (listCode (P.toList.map fun q => natBits (f q))) ≤ (listCode (P.toList.map fun
      q => natBits (f q))).length + c_len := hc_len _
  have h3 : (listCode (P.toList.map fun q => natBits (f q))).length ≤ m * (2 * (Nat.log 2 (Nat.log 2
      x)) + 3) := by
    apply plainK_natBits_le_of_primeFactors_test_bound
    intro p hp
    exact hf p (Finset.mem_toList.mp hp)
  have h3_enat : ((listCode (P.toList.map fun q => natBits (f q))).length : ENat) ≤ (m * (2 *
      (Nat.log 2 (Nat.log 2 x)) + 3) : ENat) := by
    exact_mod_cast h3
  have h4 : plainK V (G (listCode (P.toList.map fun q => natBits (f q)))) ≤ (m * (2 * (Nat.log 2
      (Nat.log 2 x)) + 3) : ENat) + c_len + c_map := by
    calc plainK V (G (listCode (P.toList.map fun q => natBits (f q))))
      _ ≤ plainK V (listCode (P.toList.map fun q => natBits (f q))) + c_map := h1
      _ ≤ ((listCode (P.toList.map fun q => natBits (f q))).length : ENat) + c_len + c_map := by
          gcongr
      _ ≤ (m * (2 * (Nat.log 2 (Nat.log 2 x)) + 3) : ENat) + c_len + c_map := by gcongr
  have h5 : (m * (2 * (Nat.log 2 (Nat.log 2 x)) + 3) : ENat) + c_len + c_map = (m * (2 * (Nat.log 2
      (Nat.log 2 x)) + 3) + c_len + c_map : ℕ) := by norm_cast
  rw [h5] at h4
  have h6 : (m * (2 * (Nat.log 2 (Nat.log 2 x)) + 3) + c_len + c_map) ≤ c * (Nat.log 2 (Nat.log 2
      x)) + c := by
    dsimp [c, m]
    have h_c1 : P.toList.length * 2 ≤ 3 * P.toList.length + c_map + c_len := by omega
    have h_c2 : P.toList.length * 3 + c_len + c_map ≤ 3 * P.toList.length + c_map + c_len := by
        omega
    nlinarith
  calc plainK V (G (listCode (P.toList.map fun q => natBits (f q))))
    _ ≤ (m * (2 * (Nat.log 2 (Nat.log 2 x)) + 3) + c_len + c_map : ℕ) := h4
    _ ≤ (c * (Nat.log 2 (Nat.log 2 x)) + c : ℕ) := by exact_mod_cast h6
/-- A natural number `x ≥ 2` all of whose prime factors lie in a fixed finite set `P` has plain
Kolmogorov complexity `O(log log x)`, with a constant depending only on `P`. -/
theorem plainK_natBits_le_of_primeFactors (V : Map) (hV : isOptimalConditional V) (P : Finset ℕ) :
    ∃ c : ℕ, ∀ x : ℕ, 2 ≤ x → (∀ p, p.Prime → p ∣ x → p ∈ P) →
      plainK V (natBits x) ≤ ((c * Nat.log 2 (Nat.log 2 x) + c : ℕ) : ℕ∞) := by
  obtain ⟨c, hc⟩ := plainK_natBits_le_of_primeFactors_complexity V hV P
  use c
  intro x hx2 hp
  have h1 := plainK_natBits_le_of_primeFactors_exponents P x hx2 hp
  have hcx := hc (Nat.factorization x) x hx2 h1.2
  rwa [← h1.1] at hcx

private lemma not_le_logb_iff {p : ℝ} {y : ℝ} (hp : (0 : ℝ) < p) :
    ¬ (Real.logb 2 p ≤ y) ↔ 2^y < p := by
  rw [not_le]
  rw [Real.logb, lt_div_iff₀ (Real.log_pos (by norm_num))]
  rw [← Real.log_rpow (by norm_num)]
  exact (Real.log_lt_log_iff (Real.rpow_pos_of_pos (by norm_num) y) hp)

private lemma not_le_logb_iff' {p : ℝ} {y : ℝ} (hp : (0 : ℝ) < p) :
    ¬ (Real.logb 2 p ≤ y) ↔ (1:ℝ)/p < 2^(-y) := by
  rw [not_le_logb_iff hp]
  rw [Real.rpow_neg (by norm_num)]
  have h1 : (1:ℝ)/p = p⁻¹ := one_div p
  rw [h1]
  exact (inv_lt_inv₀ hp (Real.rpow_pos_of_pos (by norm_num: (0:ℝ)<2) y)).symm

/-- Step 1 of the proof of `frequently_logb_nth_prime_le`: a summability bound using
Kraft's inequality on the prefix complexity of `natBits n`. -/
private theorem frequently_logb_nth_prime_le_kraft_natBits
    (U : Map) (hU : IsOptimalPrefixConditional U) :
    Summable (fun n : ℕ =>
      (2 : ℝ) ^ (-((KPPlain U (natBits n)).toNat : ℝ))) := by
  have h_inj : Function.Injective natBits := natBits_injective
  have hk_ennreal : (∑' n : ℕ, complexityWeight (KPPlain U (natBits n))) ≤ 1 := by
    have h1 : (∑' n : ℕ, complexityWeight (KPPlain U (natBits n))) ≤ ∑' x : BitString,
        complexityWeight (KPPlain U x) :=
      ENNReal.tsum_comp_le_tsum_of_injective h_inj (fun x => complexityWeight (KPPlain U x))
    have h2 := KPPlain_kraft_sum_le_one U hU.isPrefixDecompressor
    exact le_trans h1 h2
  have hk_ne_top : (∑' n : ℕ, complexityWeight (KPPlain U (natBits n))) ≠ ⊤ := by
    exact ne_top_of_le_ne_top ENNReal.one_ne_top hk_ennreal
  have h3 : Summable (fun n : ℕ => ENNReal.toReal (complexityWeight (KPPlain U (natBits n)))) :=
    ENNReal.summable_toReal hk_ne_top
  have h_eq : (fun n : ℕ => ENNReal.toReal (complexityWeight (KPPlain U (natBits n)))) =
      (fun n : ℕ => (2 : ℝ) ^ (-((KPPlain U (natBits n)).toNat : ℝ))) := by
    ext n
    set k := (KPPlain U (natBits n)).toNat
    have htop : KPPlain U (natBits n) ≠ ⊤ := KPPlain_ne_top_of_optimal U hU (natBits n)
    have heq : KPPlain U (natBits n) = (k : ℕ∞) := (ENat.natCast_toNat htop).symm
    rw [heq]
    rw [complexityWeight_coe]
    rw [ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_ofNat]
    rw [Real.rpow_neg zero_le_two]
    rw [Real.rpow_natCast]
    exact inv_pow 2 k
  rw [← h_eq]
  exact h3

/-- Step 2 of the proof of `frequently_logb_nth_prime_le`: if `2^(-f n)` is summable, then
`log_2 p_n <= f n` frequently. -/
private theorem frequently_logb_nth_prime_le_nth_prime_comparison
    {f : ℕ → ℕ}
    (hf : Summable (fun n : ℕ => (2 : ℝ) ^ (-(f n : ℝ)))) :
    ∃ᶠ n in atTop,
      Real.logb 2 (Nat.nth Nat.Prime n) ≤ (f n : ℝ) := by
  by_contra h
  have h1 : ∀ᶠ n in atTop, ¬ (Real.logb 2 (Nat.nth Nat.Prime n) ≤ (f n : ℝ)) :=
      Filter.not_frequently.mp h
  have h2 : ∀ᶠ n in atTop, (1:ℝ) / Nat.nth Nat.Prime n < 2 ^ (-(f n : ℝ)) := by
    filter_upwards [h1] with n hn
    have hp : (0:ℝ) < Nat.nth Nat.Prime n := by
      have h3 := Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime n
      exact Nat.cast_pos.mpr (Nat.Prime.pos h3)
    exact (not_le_logb_iff' hp).mp hn
  have h2_le : ∀ᶠ n in atTop, ‖(1:ℝ) / Nat.nth Nat.Prime n‖ ≤ 2 ^ (-(f n : ℝ)) := by
    filter_upwards [h2] with n hn
    have hp : (0:ℝ) < Nat.nth Nat.Prime n := by
      have h4 := Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime n
      exact Nat.cast_pos.mpr (Nat.Prime.pos h4)
    have h_nonneg : 0 ≤ (1:ℝ) / Nat.nth Nat.Prime n := div_nonneg zero_le_one (le_of_lt hp)
    rw [Real.norm_eq_abs, abs_of_nonneg h_nonneg]
    exact le_of_lt hn
  have h2_cofinite : ∀ᶠ n in cofinite, ‖(1:ℝ) / Nat.nth Nat.Prime n‖ ≤ 2 ^ (-(f n : ℝ)) := by
    exact Nat.cofinite_eq_atTop ▸ h2_le
  have h3 : Summable (fun n : ℕ => (1:ℝ) / Nat.nth Nat.Prime n) := 
    Summable.of_norm_bounded_eventually hf h2_cofinite
  have not_sum : ¬ Summable (fun n : ℕ => (1 : ℝ) / Nat.nth Nat.Prime n) := by
    intro hs
    have hs1 := not_summable_one_div_on_primes
    have h_equiv : Summable (fun p : {p : ℕ // p.Prime} => (1 : ℝ) / p.val) ↔ 
              Summable (fun n : ℕ => (1 : ℝ) / Nat.nth Nat.Prime n) := by
      set f_bij : ℕ → {p : ℕ // p.Prime} := (fun n => ⟨Nat.nth Nat.Prime n, Nat.nth_mem_of_infinite
          Nat.infinite_setOfPred_prime n⟩)
      have hb : Function.Bijective f_bij := by
        constructor
        · intro x y hxy
          have h_inj_eq : Nat.nth Nat.Prime x = Nat.nth Nat.Prime y := by
            exact (Subtype.ext_iff.mp hxy)
          exact Nat.nth_injective Nat.infinite_setOfPred_prime h_inj_eq
        · intro ⟨p, hp_mem⟩
          have h_range : p ∈ Set.range (Nat.nth Nat.Prime) := by
            rw [Nat.range_nth_of_infinite Nat.infinite_setOfPred_prime]
            exact hp_mem
          obtain ⟨n, hn_eq⟩ := h_range
          exact ⟨n, Subtype.ext hn_eq⟩
      have eq := Equiv.summable_iff (α := ℝ) (β := {p : ℕ // p.Prime}) (γ := ℕ) (e :=
          Equiv.ofBijective f_bij hb) (f := fun p => (1 : ℝ) / p.val)
      have heq : ((fun p : {p : ℕ // p.Prime} => (1 : ℝ) / p.val) ∘ ⇑(Equiv.ofBijective f_bij hb)) =
          (fun n : ℕ => (1 : ℝ) / ((Equiv.ofBijective f_bij hb) n).val) := rfl
      have hf_eq : (fun n : ℕ => (1 : ℝ) / ((Equiv.ofBijective f_bij hb) n).val) = (fun n : ℕ => (1
          : ℝ) / Nat.nth Nat.Prime n) := by
        ext n
        have : (Equiv.ofBijective f_bij hb) n = f_bij n := Equiv.ofBijective_apply f_bij hb n
        have h_val : (f_bij n).val = Nat.nth Nat.Prime n := rfl
        rw [this, h_val]
      rw [heq, hf_eq] at eq
      exact eq.symm
    have h_sub : Summable (fun p : {p : ℕ // p.Prime} => (1 : ℝ) / p.val) ↔
              Summable ({p : ℕ | p.Prime}.indicator (fun n : ℕ => (1 : ℝ) / n)) := by
      exact summable_subtype_iff_indicator (α := ℝ) (β := ℕ) (f := fun n => (1 : ℝ) / n) (s := {p :
          ℕ | p.Prime})
    rw [← h_equiv, h_sub] at hs
    exact hs1 hs
  exact not_sum h3

/-- **SUV p. 233, footnote 1**, after Li and Vitányi: with `p_n` the `n`-th prime and `K` prefix
complexity, one has `log p_n ≤ K(n) + O(1)` for infinitely many `n`. -/
theorem frequently_logb_nth_prime_le (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∃ᶠ n in atTop,
      Real.logb 2 (Nat.nth Nat.Prime n) ≤ ((KPPlain U (natBits n)).toNat : ℝ) + c := by
  use 0
  have h := frequently_logb_nth_prime_le_nth_prime_comparison
      (frequently_logb_nth_prime_le_kraft_natBits U hU)
  simp only [Nat.cast_zero, add_zero]
  exact h

/-- **SUV p. 233, footnote 1**, the combinatorial translation: the series of inverse primes
diverges. -/
theorem not_summable_inv_primes :
    ¬ Summable (Set.indicator {p : ℕ | p.Prime} fun n : ℕ => (1 : ℝ) / n) :=
  not_summable_one_div_on_primes

end Kolmogorov.Applications
