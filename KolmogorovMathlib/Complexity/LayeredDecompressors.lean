/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Foundation.EffectiveNotions
import KolmogorovMathlib.Interface.Dovetailing
import KolmogorovMathlib.Foundation.PrimrecExtras
import Mathlib.Data.Nat.Dist
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Computability.Reduce
import KolmogorovMathlib.Complexity.Uncomputability
import KolmogorovMathlib.AlgorithmicStatistics.Selector
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.ModelsToSets2
import KolmogorovMathlib.CommonInformation.Counting
import KolmogorovMathlib.Complexity.Properties
import Mathlib.Computability.PartrecCode
import KolmogorovMathlib.Complexity.Incompressibility
import KolmogorovMathlib.Complexity.CanonicalObjects

/-!
# Complexity layers, averages, and `q`-ary description modes

Three things one can do by choosing the decompressor or the description alphabet.

`exists_isOptimalConditional_infinite_empty_complexityLayer` shows a layer `{x | C(x) = n}` may
be empty for infinitely many `n` — the layer structure is not invariant.
`sum_cVal_allStrings_within_const` computes the total complexity of the strings of length `n`
as `n · 2 ^ n + O(2 ^ n)`, so the average complexity is `n + O(1)`; the summation lemmas
around it (`sum_Ioc_pow`, `card_Ioc_sum_boole_le`, `list_sum_map_eq_finset_sum`) do the
counting.

`QMap`, `qCondK` and `qPlainK` set up complexity with respect to a `q`-letter description
alphabet, and `D_bin` with the conversion lemmas `bitsToFin4List_fin4ListToBits`,
`fin4ListToBits_bitsToFin4List_of_even` and `bitsToFin4List_length_of_even` translate between
bit strings and four-letter strings; the exercises about those complexities are in
`AlphabetComplexity`.
-/

namespace Kolmogorov
open Nat.Partrec (Code)
open Kolmogorov.CodedFiniteDistribution
open Nat.Partrec (Code)

private noncomputable def layerEmptyV (U : Map) : Map := fun pr =>
  let p := pr.1
  let y := pr.2
  let n := p.length
  if n % 2 = 1 then Part.none
  else
    if p.head? = some false then
      U (p.tail, y)
    else if p.take 2 = [true, false] then
      U (p.drop 2, y)
    else Part.none

private lemma layerEmptyV_isDecompressor (U : Map) (hU : isDecompressor U) :
    isDecompressor (layerEmptyV U) := by
  have h_len : Primrec (fun pr : BitString × BitString => pr.1.length) :=
    Primrec.list_length.comp Primrec.fst
  have h_mod : Primrec (fun pr : BitString × BitString => pr.1.length % 2) :=
    Primrec.nat_mod.comp h_len (Primrec.const 2)
  have h_cond1 : Primrec (fun pr : BitString × BitString => decide (pr.1.length % 2 = 1)) :=
    PrimrecPred.decide (PrimrecRel.comp Primrec.eq h_mod (Primrec.const 1))
  have h_head : Primrec (fun pr : BitString × BitString => pr.1.head?) :=
    Primrec.list_head?.comp Primrec.fst
  have h_cond2 : Primrec (fun pr : BitString × BitString => decide (pr.1.head? = some false)) :=
    PrimrecPred.decide (PrimrecRel.comp Primrec.eq h_head (Primrec.const (some false)))
  have h_take2 : Primrec (fun pr : BitString × BitString => pr.1.take 2) :=
    Primrec.list_take.comp (Primrec.const 2) Primrec.fst
  have h_cond3 : Primrec (fun pr : BitString × BitString => decide (pr.1.take 2 = [true, false])) :=
    PrimrecPred.decide (PrimrecRel.comp Primrec.eq h_take2 (Primrec.const [true, false]))
  have h_tail : Primrec (fun pr : BitString × BitString => pr.1.tail) :=
    Primrec.list_tail.comp Primrec.fst
  have h_drop2 : Primrec (fun pr : BitString × BitString => pr.1.drop 2) :=
    Primrec.list_drop.comp (Primrec.const 2) Primrec.fst
  have h_U1 : Partrec (fun pr : BitString × BitString => U (pr.1.tail, pr.2)) :=
    Partrec.comp hU (Computable.pair h_tail.to_comp Computable.snd)
  have h_U2 : Partrec (fun pr : BitString × BitString => U (pr.1.drop 2, pr.2)) :=
    Partrec.comp hU (Computable.pair h_drop2.to_comp Computable.snd)
  have h_inner : Partrec (fun pr : BitString × BitString =>
      if pr.1.take 2 = [true, false] then U (pr.1.drop 2, pr.2) else Part.none) :=
    (Partrec.cond h_cond3.to_comp.to₂ h_U2 Partrec.none).of_eq (fun pr => by
      by_cases h : pr.1.take 2 = [true, false] <;> simp [h])
  have h_mid : Partrec (fun pr : BitString × BitString =>
      if pr.1.head? = some false then U (pr.1.tail, pr.2)
      else if pr.1.take 2 = [true, false] then U (pr.1.drop 2, pr.2) else Part.none) :=
    (Partrec.cond h_cond2.to_comp.to₂ h_U1 h_inner).of_eq (fun pr => by
      by_cases h : pr.1.head? = some false <;> simp [h])
  have h_all : Partrec (fun pr : BitString × BitString =>
      if pr.1.length % 2 = 1 then Part.none
      else if pr.1.head? = some false then U (pr.1.tail, pr.2)
      else if pr.1.take 2 = [true, false] then U (pr.1.drop 2, pr.2) else Part.none) :=
    (Partrec.cond h_cond1.to_comp.to₂ Partrec.none h_mid).of_eq (fun pr => by
      by_cases h : pr.1.length % 2 = 1 <;> simp [h])
  exact h_all

open Classical in
/-- For a suitable optimal decompressor the layer `{x | C(x) = n}` is empty for infinitely many
`n`. SUV Exercise 2. -/
theorem exists_isOptimalConditional_infinite_empty_complexityLayer :
    ∃ V : Map, isOptimalConditional V ∧
      {n : ℕ | ∀ x : BitString, plainK V x ≠ (n : ℕ∞)}.Infinite := by
  obtain ⟨U, hU⟩ := exists_isOptimalConditional
  use layerEmptyV U
  have hV_decomp : isDecompressor (layerEmptyV U) := layerEmptyV_isDecompressor U hU.1
  have hV_opt : isOptimalConditional (layerEmptyV U) := by
    refine ⟨hV_decomp, fun D hD => ?_⟩
    obtain ⟨c, hc⟩ := hU.2 D hD
    use c + 2
    intro x y
    cases hK : condK D x y with
    | top => simp
    | coe N =>
      have hU_le : condK U x y ≤ ((N + c : ℕ) : ℕ∞) := by
        have h1 := hc x y
        rw [hK] at h1
        calc condK U x y
          _ ≤ (N : ℕ∞) + (c : ℕ∞) := h1
          _ = ((N + c : ℕ) : ℕ∞) := by push_cast; ring
      rw [condK_le_iff] at hU_le
      obtain ⟨q, hq_len, hq_prod⟩ := hU_le
      by_cases hq_even : q.length % 2 = 0
      · set w := true :: false :: q
        have hw_even : w.length % 2 = 0 := by
          dsimp [w]
          omega
        have hw_prod : x ∈ layerEmptyV U (w, y) := by
          change x ∈ (if (true :: false :: q).length % 2 = 1 then Part.none
            else if (true :: false :: q).head? = some false then
              U ((true :: false :: q).tail, y)
            else if (true :: false :: q).take 2 = [true, false] then
              U ((true :: false :: q).drop 2, y)
            else Part.none)
          have h1 : (true :: false :: q).length % 2 = 0 := hw_even
          have h2 : (true :: false :: q).head? = some true := rfl
          have h3 : (true :: false :: q).take 2 = [true, false] := rfl
          have h4 : (true :: false :: q).drop 2 = q := rfl
          rw [h1, ite_eq_right (by decide), h2, ite_eq_right (by decide), h3, ite_eq_left rfl, h4]
          exact hq_prod
        have h_condK_V : condK (layerEmptyV U) x y ≤ ((N + c + 2 : ℕ) : ℕ∞) := by
          rw [condK_le_iff]
          refine ⟨w, ?_, hw_prod⟩
          change w.length ≤ N + c + 2
          dsimp [w, programLength] at hq_len ⊢
          omega
        have h_sum : ((N + c + 2 : ℕ) : ℕ∞) = (N : ℕ∞) + ((c + 2 : ℕ) : ℕ∞) := by push_cast; ring
        exact h_condK_V.trans h_sum.le
      · have hq_odd : q.length % 2 = 1 := by omega
        set w := false :: q
        have hw_even : w.length % 2 = 0 := by
          dsimp [w]
          omega
        have hw_prod : x ∈ layerEmptyV U (w, y) := by
          change x ∈ (if (false :: q).length % 2 = 1 then Part.none
            else if (false :: q).head? = some false then
              U ((false :: q).tail, y)
            else if (false :: q).take 2 = [true, false] then
              U ((false :: q).drop 2, y)
            else Part.none)
          have h1 : (false :: q).length % 2 = 0 := hw_even
          have h2 : (false :: q).head? = some false := rfl
          have h3 : (false :: q).tail = q := rfl
          rw [h1, ite_eq_right (by decide), h2, ite_eq_left rfl, h3]
          exact hq_prod
        have h_condK_V : condK (layerEmptyV U) x y ≤ ((N + c + 1 : ℕ) : ℕ∞) := by
          rw [condK_le_iff]
          refine ⟨w, ?_, hw_prod⟩
          change w.length ≤ N + c + 1
          dsimp [w, programLength] at hq_len ⊢
          omega
        have h_sum : ((N + c + 2 : ℕ) : ℕ∞) = (N : ℕ∞) + ((c + 2 : ℕ) : ℕ∞) := by push_cast; ring
        have h1 : ((N + c + 1 : ℕ) : ℕ∞) ≤ ((N + c + 2 : ℕ) : ℕ∞) := by exact_mod_cast (by omega)
        exact (h_condK_V.trans h1).trans h_sum.le
  refine ⟨hV_opt, ?_⟩
  have h_odd_empty : ∀ k : ℕ, ∀ x : BitString,
      plainK (layerEmptyV U) x ≠ ((2 * k + 1 : ℕ) : ℕ∞) := by
    intro k x h_eq
    have h_ne : plainK (layerEmptyV U) x ≠ ⊤ := by rw [h_eq]; exact WithTop.coe_ne_top
    unfold plainK condK candidateLengths at h_ne h_eq
    have h_nonempty : {n_1 : ENat |
        ∃ p, x ∈ layerEmptyV U (p, []) ∧ (p.length : ENat) = n_1}.Nonempty := by
      by_contra hc
      rw [Set.not_nonempty_iff_eq_empty] at hc
      rw [hc, sInf_empty] at h_ne
      contradiction
    have h_mem := csInf_mem h_nonempty
    rw [h_eq] at h_mem
    obtain ⟨p, hp_prod, hp_len⟩ := h_mem
    have hp_len_nat : p.length = 2 * k + 1 := WithTop.coe_inj.mp hp_len
    have hp_odd : p.length % 2 = 1 := by rw [hp_len_nat]; omega
    dsimp [layerEmptyV] at hp_prod
    rw [hp_odd] at hp_prod
    simp at hp_prod
  have h_sub : {n : ℕ | ∃ k, n = 2 * k + 1} ⊆
      {n : ℕ | ∀ x : BitString, plainK (layerEmptyV U) x ≠ (n : ℕ∞)} := by
    intro n hn x
    obtain ⟨k, rfl⟩ := hn
    exact h_odd_empty k x
  have h_odd_inf : {n : ℕ | ∃ k, n = 2 * k + 1}.Infinite := by
    have h_eq : {n : ℕ | ∃ k, n = 2 * k + 1} = Set.range (fun k => 2 * k + 1) := by
      ext n; constructor <;> rintro ⟨k, rfl⟩ <;> exact ⟨k, rfl⟩
    rw [h_eq]
    exact Set.infinite_range_of_injective (fun a b hab => by omega)
  exact Set.Infinite.mono h_sub h_odd_inf


/-- A uniform bound on the values of a function bounds the sum of its values over a list. -/
lemma list_sum_map_le {α : Type*} (l : List α) (f : α → ℕ) (C : ℕ)
    (h : ∀ x ∈ l, f x ≤ C) : (l.map f).sum ≤ l.length * C := by
  induction l with
  | nil => simp
  | cons a as ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h1 : f a ≤ C := h a (by simp)
    have h2 : (as.map f).sum ≤ as.length * C :=
      ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    rw [add_mul, one_mul]
    omega

/-- Summing over a duplicate-free list is summing over the corresponding finite set. -/
lemma list_sum_map_eq_finset_sum {α : Type*} [DecidableEq α] (l : List α)
    (hl : l.Nodup) (f : α → ℕ) :
    (l.map f).sum = ∑ x ∈ l.toFinset, f x := by
  induction l with
  | nil => simp
  | cons a as ih =>
    simp only [List.nodup_cons] at hl
    simp only [List.map_cons, List.sum_cons, List.toFinset_cons]
    rw [Finset.sum_insert (by simp [hl.1]), ih hl.2]

/-- Counting the indices `k ≤ n` with `v ≤ n - k` bounds `n` from above by `v` plus that
count. -/
lemma card_Ioc_sum_boole_le (v n : ℕ) :
    n - ∑ k ∈ Finset.Ioc 0 n, (if v ≤ n - k then 1 else 0) ≤ v := by
  by_cases h : n ≤ v
  · calc n - ∑ k ∈ Finset.Ioc 0 n, (if v ≤ n - k then 1 else 0)
      _ ≤ n := Nat.sub_le _ _
      _ ≤ v := h
  · push Not at h
    let d := n - v
    have hd_pos : 1 ≤ d := by omega
    have hd_le : d ≤ n := by omega
    have h_filter : (Finset.Ioc 0 n).filter (fun k => v ≤ n - k) = Finset.Ioc 0 d := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_Ioc]
      omega
    have h_sum : ∑ k ∈ Finset.Ioc 0 n, (if v ≤ n - k then 1 else 0) = d := by
      rw [Finset.sum_boole, h_filter]
      simp
    rw [h_sum]
    omega

/-- The powers `2 ^ (n - k + 1)` for `0 < k ≤ n` sum to `2 ^ (n + 1) - 2`. -/
lemma sum_Ioc_pow (n : ℕ) :
    ∑ k ∈ Finset.Ioc 0 n, 2 ^ (n - k + 1) = 2 ^ (n + 1) - 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h_ins := Finset.insert_Ioc_right_eq_Ioc_add_one (by omega : 0 ≤ n)
    rw [← h_ins, Finset.sum_insert (by simp)]
    have h_assoc : (∑ k ∈ Finset.Ioc 0 n, 2 ^ (n + 1 - k + 1)) =
        ∑ k ∈ Finset.Ioc 0 n, 2 * 2 ^ (n - k + 1) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_Ioc] at hk
      have : n + 1 - k + 1 = (n - k + 1) + 1 := by omega
      rw [this, pow_succ, mul_comm]
    rw [h_assoc, ← Finset.mul_sum, ih]
    have : 2 ≤ 2 ^ (n + 1) := by
      have := Nat.one_le_two_pow (n := n)
      omega
    have : n + 1 - (n + 1) + 1 = 1 := by omega
    rw [this, pow_one]
    omega

/-- The total complexity of the strings of length `n` is `n · 2 ^ n` up to `O(2 ^ n)`; the average
complexity of a string of length `n` is `n + O(1)`. SUV Exercise 3. -/
theorem sum_cVal_allStrings_within_const (U : Map) (hU : isOptimalConditional U) :
    ∃ k : ℕ, ∀ n : ℕ,
      (n - k) * 2 ^ n ≤ ((allStrings n).map (cVal U)).sum ∧
      ((allStrings n).map (cVal U)).sum ≤ (n + k) * 2 ^ n := by
  obtain ⟨c, hc⟩ := plainK_le_length U hU
  use max 2 c
  intro n
  have h_len_ub : ∀ x ∈ allStrings n, cVal U x ≤ n + max 2 c := by
    intro x hx
    rw [mem_allStrings] at hx
    have h1 := hc x
    unfold programLength at h1
    rw [hx] at h1
    unfold cVal
    have h_top : plainK U x ≠ ⊤ := by
      intro h_contra
      rw [h_contra] at h1
      contradiction
    have h_eq : plainK U x = (((plainK U x).toNat : ℕ) : ENat) :=
      (ENat.natCast_toNat h_top).symm
    rw [h_eq] at h1
    have h_le : (plainK U x).toNat ≤ n + c := ENat.natCast_le_natCast.mp h1
    have hc2 : c ≤ max 2 c := le_max_right 2 c
    calc (plainK U x).toNat ≤ n + c := h_le
      _ ≤ n + max 2 c := by omega
  constructor
  · by_cases hn : n < max 2 c
    · have h_sub : n - max 2 c = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_lt hn)
      rw [h_sub, zero_mul]
      exact Nat.zero_le _
    · push Not at hn
      have h_nodup := allStrings_nodup n
      rw [list_sum_map_eq_finset_sum (allStrings n) h_nodup (cVal U)]
      have h_lower : ∑ x ∈ stringsOfLength n,
            (n - ∑ k ∈ Finset.Ioc 0 n, (if cVal U x ≤ n - k then 1 else 0)) ≤
          ∑ x ∈ stringsOfLength n, cVal U x := by
        apply Finset.sum_le_sum
        intro x hx
        exact card_Ioc_sum_boole_le (cVal U x) n
      have h_inner_le : ∀ x ∈ stringsOfLength n,
          ∑ k ∈ Finset.Ioc 0 n, (if cVal U x ≤ n - k then 1 else 0) ≤ n := by
        intro x hx
        have h_f : (Finset.Ioc 0 n).filter (fun k => cVal U x ≤ n - k) ⊆
            Finset.Ioc 0 n := Finset.filter_subset _ _
        have h_c := Finset.card_le_card h_f
        rw [Nat.card_Ioc, Nat.sub_zero] at h_c
        rw [Finset.sum_boole]
        exact h_c
      have h_sum_sub : ∑ x ∈ stringsOfLength n,
            (n - ∑ k ∈ Finset.Ioc 0 n, (if cVal U x ≤ n - k then 1 else 0)) =
          (stringsOfLength n).card * n -
            ∑ x ∈ stringsOfLength n,
              ∑ k ∈ Finset.Ioc 0 n, (if cVal U x ≤ n - k then 1 else 0) := by
        have h_add : ∑ x ∈ stringsOfLength n,
              (n - ∑ k ∈ Finset.Ioc 0 n, (if cVal U x ≤ n - k then 1 else 0)) +
            ∑ x ∈ stringsOfLength n,
              ∑ k ∈ Finset.Ioc 0 n, (if cVal U x ≤ n - k then 1 else 0) =
            (stringsOfLength n).card * n := by
          rw [← Finset.sum_add_distrib]
          have h_eq : ∑ x ∈ stringsOfLength n, n = (stringsOfLength n).card * n := by
            simp [mul_comm]
          rw [← h_eq]
          apply Finset.sum_congr rfl
          intro x hx
          exact Nat.sub_add_cancel (h_inner_le x hx)
        omega
      rw [h_sum_sub, card_stringsOfLength] at h_lower
      rw [Finset.sum_comm] at h_lower
      have h_card_bound : ∀ k ∈ Finset.Ioc 0 n,
          (∑ x ∈ stringsOfLength n, if cVal U x ≤ n - k then 1 else 0) ≤
            2 ^ (n - k + 1) := by
        intro k hk
        rw [Finset.sum_boole]
        have h_sub : (stringsOfLength n).filter (fun x => cVal U x ≤ n - k) ⊆
            compressibleWords U [] (n - k) := by
          intro x hx
          rw [Finset.mem_filter, mem_stringsOfLength] at hx
          have h_cval_le := hx.2
          have h1 := hc x
          have h_not_top : plainK U x ≠ ⊤ := by
            intro h_contra
            rw [h_contra] at h1
            contradiction
          have h_plainK_le : plainK U x ≤ ((n - k : ℕ) : ENat) := by
            have h_eq : plainK U x = (((cVal U x : ℕ) : ENat)) :=
              (ENat.natCast_toNat h_not_top).symm
            rw [h_eq]
            exact ENat.natCast_le_natCast.mpr h_cval_le
          rw [compressibleWords, Finset.mem_filter]
          refine ⟨?_, h_plainK_le⟩
          · have h_cond : condK U x [] ≤ ((n - k : ℕ) : ENat) := h_plainK_le
            change condK U x [] ≤ ((n - k : ℕ) : ENat) at h_cond
            rw [condK_le_iff] at h_cond
            obtain ⟨p, hp_len, hp_prod⟩ := h_cond
            rw [generatedWords, List.mem_toFinset, List.mem_filterMap]
            exact ⟨p, mem_programsLe (n - k) p hp_len, progToOut_eq_some.mpr hp_prod⟩
        have h_card_le := Finset.card_le_card h_sub
        have h_comp_lt := card_compressibleWordsLt U [] (n - k)
        calc ((stringsOfLength n).filter (fun x => cVal U x ≤ n - k)).card
          _ ≤ (compressibleWords U [] (n - k)).card := h_card_le
          _ ≤ 2 ^ (n - k + 1) := by omega
      have h_sum_cards : ∑ k ∈ Finset.Ioc 0 n,
            (∑ x ∈ stringsOfLength n, if cVal U x ≤ n - k then 1 else 0) ≤
          ∑ k ∈ Finset.Ioc 0 n, 2 ^ (n - k + 1) := by
        apply Finset.sum_le_sum
        exact h_card_bound
      rw [sum_Ioc_pow n] at h_sum_cards
      have h_2pow : 2 ^ (n + 1) - 2 ≤ 2 * 2 ^ n := by
        rw [pow_succ]
        omega
      have h_sum_le_2pow : ∑ k ∈ Finset.Ioc 0 n,
        (∑ x ∈ stringsOfLength n, if cVal U x ≤ n - k then 1 else 0) ≤ 2 * 2 ^ n :=
        le_trans h_sum_cards h_2pow
      calc (n - max 2 c) * 2 ^ n
        _ ≤ (n - 2) * 2 ^ n := by
          have : max 2 c ≥ 2 := le_max_left 2 c
          gcongr
        _ = 2 ^ n * n - 2 * 2 ^ n := by
          rw [Nat.sub_mul, mul_comm n (2 ^ n)]
        _ ≤ 2 ^ n * n - ∑ k ∈ Finset.Ioc 0 n,
              ∑ x ∈ stringsOfLength n, if cVal U x ≤ n - k then 1 else 0 := by
          omega
        _ ≤ ∑ x ∈ stringsOfLength n, cVal U x := h_lower
  · have h1 := list_sum_map_le (allStrings n) (cVal U) (n + max 2 c) h_len_ub
    rw [length_allStrings] at h1
    calc ((allStrings n).map (cVal U)).sum ≤ 2 ^ n * (n + max 2 c) := h1
      _ = (n + max 2 c) * 2 ^ n := mul_comm (2 ^ n) (n + max 2 c)

/-! #### Complexity with respect to a `q`-letter description alphabet -/

/-- Description modes whose descriptions are words over a `q`-letter alphabet. -/
abbrev QMap (q : ℕ) := List (Fin q) × BitString →. BitString

/-- Conditional complexity with respect to a `q`-ary description mode. -/
noncomputable def qCondK {q : ℕ} (D : QMap q) (x y : BitString) : ℕ∞ :=
  sInf {n : ℕ∞ | ∃ p : List (Fin q), x ∈ D (p, y) ∧ (p.length : ℕ∞) = n}

/-- Plain complexity with respect to a `q`-ary description mode. -/
noncomputable def qPlainK {q : ℕ} (D : QMap q) (x : BitString) : ℕ∞ := qCondK D x []

/-- Optimality of a `q`-ary description mode. -/
def IsQOptimal {q : ℕ} (D : QMap q) : Prop :=
  Partrec D ∧ ∀ D' : QMap q, Partrec D' →
    ∃ c : ℕ, ∀ x y : BitString, qCondK D x y ≤ qCondK D' x y + (c : ℕ∞)

/-- Convert a 4-letter alphabet symbol to 2 bits. -/
def fin4ToBits (a : Fin 4) : BitString :=
  match a with
  | ⟨0, _⟩ => [false, false]
  | ⟨1, _⟩ => [false, true]
  | ⟨2, _⟩ => [true, false]
  | _      => [true, true]

/-- Convert a list of 4-letter alphabet symbols to a bit string. -/
def fin4ListToBits (l : List (Fin 4)) : BitString :=
  l.flatMap fin4ToBits

/-- Convert 2 bits to a 4-letter alphabet symbol. -/
def pairToFin4 (b : Bool × Bool) : Fin 4 :=
  match b with
  | (false, false) => 0
  | (false, true)  => 1
  | (true, false)  => 2
  | (true, true)   => 3

/-- One step of the fold that reads a bit string as a string over the four-letter alphabet:
it buffers a bit and emits a letter on every second bit. -/
def bitsToFin4FoldStep (b : Bool) (st : Option Bool × List (Fin 4)) :
    Option Bool × List (Fin 4) :=
  match st.1 with
  | none => (some b, st.2)
  | some b' => (none, pairToFin4 (b, b') :: st.2)

/-- Convert a bit string to a list of 4-letter alphabet symbols by pairing bits. -/
def bitsToFin4List (l : BitString) : List (Fin 4) :=
  (l.foldr bitsToFin4FoldStep (none, [])).2

/-- A letter of the four-letter alphabet is written with two bits. -/
theorem fin4ToBits_length (a : Fin 4) : (fin4ToBits a).length = 2 := by
  rcases a with ⟨val, h⟩
  interval_cases val <;> rfl

/-- Writing a string over the four-letter alphabet doubles its length. -/
theorem fin4ListToBits_length (l : List (Fin 4)) :
    (fin4ListToBits l).length = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    change (fin4ToBits a ++ fin4ListToBits t).length = 2 * (t.length + 1)
    rw [List.length_append, fin4ToBits_length a, ih]
    omega

/-- Reading a bit string of even length leaves no buffered bit. -/
theorem bitsToFin4Fold_fst_of_even :
    ∀ (p : BitString), p.length % 2 = 0 → (p.foldr bitsToFin4FoldStep (none, [])).1 = none
  | [], _ => rfl
  | [b], h => by simp at h
  | b1 :: b2 :: rest, h => by
    have hrest : rest.length % 2 = 0 := by
      have hlen : (b1 :: b2 :: rest).length = rest.length + 2 := rfl
      omega
    have ih := bitsToFin4Fold_fst_of_even rest hrest
    have hst : rest.foldr bitsToFin4FoldStep (none, []) =
        (none, (rest.foldr bitsToFin4FoldStep (none, [])).2) := Prod.ext ih rfl
    dsimp [bitsToFin4FoldStep]
    rw [hst]

/-- Reading a bit string of even length consumes it two bits at a time. -/
theorem bitsToFin4List_cons_cons (b1 b2 : Bool) (rest : BitString) (h : rest.length % 2 = 0) :
    bitsToFin4List (b1 :: b2 :: rest) = pairToFin4 (b1, b2) :: bitsToFin4List rest := by
  have hfst := bitsToFin4Fold_fst_of_even rest h
  have hst : rest.foldr bitsToFin4FoldStep (none, []) =
      (none, (rest.foldr bitsToFin4FoldStep (none, [])).2) := Prod.ext hfst rfl
  dsimp [bitsToFin4List, bitsToFin4FoldStep]
  rw [hst]

/-- Reading back a written string over the four-letter alphabet returns it. -/
theorem bitsToFin4List_fin4ListToBits (l : List (Fin 4)) :
    bitsToFin4List (fin4ListToBits l) = l := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    have hlen : (fin4ListToBits t).length % 2 = 0 := by
      rw [fin4ListToBits_length]
      omega
    rcases a with ⟨val, h⟩
    interval_cases val
    · change bitsToFin4List (false :: false :: fin4ListToBits t) = 0 :: t
      rw [bitsToFin4List_cons_cons false false _ hlen]
      change 0 :: bitsToFin4List (fin4ListToBits t) = 0 :: t
      rw [ih]
    · change bitsToFin4List (false :: true :: fin4ListToBits t) = 1 :: t
      rw [bitsToFin4List_cons_cons false true _ hlen]
      change 1 :: bitsToFin4List (fin4ListToBits t) = 1 :: t
      rw [ih]
    · change bitsToFin4List (true :: false :: fin4ListToBits t) = 2 :: t
      rw [bitsToFin4List_cons_cons true false _ hlen]
      change 2 :: bitsToFin4List (fin4ListToBits t) = 2 :: t
      rw [ih]
    · change bitsToFin4List (true :: true :: fin4ListToBits t) = 3 :: t
      rw [bitsToFin4List_cons_cons true true _ hlen]
      change 3 :: bitsToFin4List (fin4ListToBits t) = 3 :: t
      rw [ih]

/-- Writing back a bit string of even length that has been read returns it. -/
theorem fin4ListToBits_bitsToFin4List_of_even :
    ∀ (p : BitString), p.length % 2 = 0 → fin4ListToBits (bitsToFin4List p) = p
  | [], _ => rfl
  | [b], h => by simp at h
  | b1 :: b2 :: rest, h => by
    have hrest : rest.length % 2 = 0 := by
      have hlen : (b1 :: b2 :: rest).length = rest.length + 2 := rfl
      omega
    have ih := fin4ListToBits_bitsToFin4List_of_even rest hrest
    rw [bitsToFin4List_cons_cons b1 b2 rest hrest]
    cases b1 <;> cases b2
    · change false :: false :: fin4ListToBits (bitsToFin4List rest) = false :: false :: rest
      rw [ih]
    · change false :: true :: fin4ListToBits (bitsToFin4List rest) = false :: true :: rest
      rw [ih]
    · change true :: false :: fin4ListToBits (bitsToFin4List rest) = true :: false :: rest
      rw [ih]
    · change true :: true :: fin4ListToBits (bitsToFin4List rest) = true :: true :: rest
      rw [ih]

/-- Reading a bit string of even length halves its length. -/
theorem bitsToFin4List_length_of_even (p : BitString) (h : p.length % 2 = 0) :
    (bitsToFin4List p).length = p.length / 2 := by
  have h1 := fin4ListToBits_bitsToFin4List_of_even p h
  have h2 := fin4ListToBits_length (bitsToFin4List p)
  rw [h1] at h2
  omega

/-- The binary decompressor constructed from a 4-ary decompressor `D`. -/
def D_bin (D : QMap 4) : Map := fun (p, y) =>
  if p.length % 2 = 0 then
    D (bitsToFin4List p, y)
  else
    Part.none

end Kolmogorov
