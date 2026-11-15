/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Complexity.Applications.LibraryAPI
import KolmogorovMathlib.Complexity.Applications.ForbiddenSubstrings
import KolmogorovMathlib.Complexity.KolmogorovLevin.ShortDescriptions
import KolmogorovMathlib.Prefix.ExtensionTheorem
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.Instances.RealVectorSpace

/-!
# Complexity Profile

This module realises a prescribed complexity profile by an infinite binary sequence.  Given an
integer-valued function `f` whose increments over long intervals lie strictly between `eps * h`
and `(1 - eps) * h`, we construct a sequence `w` such that the prefix complexity of the length-`n`
prefix of `w` equals `f n` up to an additive constant.

The construction cuts the sequence into blocks of a fixed length `m`, chosen so that the price of
every number up to `m` is a small fraction of `m`.  Inside each block the complexity of the
prefixes is steered by an intermediate-value argument over the choice of the next bits, and the
block boundaries are matched with the values of `f`.

The main declaration is `exists_seq_KP_profile` (SUV Problem 246, p. 242), the version of
Problem 47 for prefix complexity.  It belongs to the part of the book on sequences with
complex substrings.
-/

namespace Kolmogorov.Applications
open Filter

/-- The price of a number `i ≤ 2 ^ j`: `K(bin i) ≤ 2 (j + 1) + c`. -/
private lemma exists_seq_KP_profile_price (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ i j : ℕ, i ≤ 2 ^ j → kNatVal U i ≤ 2 * (j + 1) + c := by
  obtain ⟨c, hc⟩ := KPPlain_le_two_mul_length U hU
  refine ⟨c, fun i j hij => ?_⟩
  have h1 : (natBits i).length ≤ j + 1 := by
    have h0 : (Nat.bits i).length ≤ Nat.log 2 i + 1 := length_natBits_le_log i
    have h2 : Nat.log 2 i ≤ j := by
      calc Nat.log 2 i ≤ Nat.log 2 (2 ^ j) := Nat.log_mono_right hij
        _ = j := Nat.log_pow (by norm_num) j
    have h3 : (natBits i).length = (Nat.bits i).length := rfl
    omega
  have h4 : KPPlain U (natBits i) ≤ ((2 * (j + 1) + c : ℕ) : ℕ∞) := by
    calc KPPlain U (natBits i) ≤ 2 * (((natBits i).length : ℕ) : ℕ∞) + (c : ℕ∞) := hc (natBits i)
      _ ≤ 2 * (((j + 1 : ℕ)) : ℕ∞) + (c : ℕ∞) := by
        have h5 : (((natBits i).length : ℕ) : ℕ∞) ≤ ((j + 1 : ℕ) : ℕ∞) := by exact_mod_cast h1
        gcongr
      _ = ((2 * (j + 1) + c : ℕ) : ℕ∞) := by push_cast; ring
  exact ENat.toNat_le_of_le_natCast h4

/-- Step 1 of the proof of `exists_seq_KP_profile`: the block length.  For `δ > 0`
and constants `C`, `M` there is a block length `m ≥ M`, `m > 0`, such that the price `K(bin i)` of
every number `i ≤ m`, plus `C`, is at most `δ m` (`K(bin i) = O(log i)`). -/
private lemma exists_seq_KP_profile_blockLength (U : Map)
    (hU : IsOptimalPrefixConditional U) {δ : ℝ} (hδ : 0 < δ) (C M : ℕ) :
    ∃ m : ℕ, M ≤ m ∧ 0 < m ∧ ∀ i : ℕ, i ≤ m → ((kNatVal U i : ℕ) : ℝ) + C ≤ δ * m := by
  obtain ⟨c, hK⟩ := exists_seq_KP_profile_price U hU
  set s : ℕ := M + ⌈(6 + (c : ℝ) + C) / δ⌉₊ with hs
  have hMs : M ≤ s := Nat.le_add_right _ _
  have hslt : s < 2 ^ s := Nat.lt_two_pow_self
  have hpow : 2 ^ (2 * s) = 2 ^ s * 2 ^ s := by rw [two_mul, pow_add]
  refine ⟨2 ^ (2 * s), ?_, by positivity, ?_⟩
  · have h3 : 2 ^ s ≤ 2 ^ (2 * s) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · intro i hi
    have hKi : kNatVal U i ≤ 2 * (2 * s + 1) + c := hK i (2 * s) hi
    have hKi' : ((kNatVal U i : ℕ) : ℝ) ≤ 2 * (2 * (s : ℝ) + 1) + c := by
      have := (Nat.cast_le (α := ℝ)).mpr hKi
      push_cast at this
      linarith
    have hD : (6 + (c : ℝ) + C) ≤ δ * ((s : ℝ) + 1) := by
      have h1 : (6 + (c : ℝ) + C) / δ ≤ (s : ℝ) := by
        calc (6 + (c : ℝ) + C) / δ ≤ ((⌈(6 + (c : ℝ) + C) / δ⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
          _ ≤ (s : ℝ) := by
            rw [hs]
            push_cast
            linarith [(Nat.cast_nonneg M : (0 : ℝ) ≤ M)]
      have h2 : (6 + (c : ℝ) + C) ≤ (s : ℝ) * δ := (div_le_iff₀ hδ).mp h1
      nlinarith
    have hP : ((s : ℝ) + 1) * ((s : ℝ) + 1) ≤ ((2 ^ (2 * s) : ℕ) : ℝ) := by
      rw [hpow]
      have h5 : s + 1 ≤ 2 ^ s := hslt
      have h6 : (s + 1) * (s + 1) ≤ 2 ^ s * 2 ^ s := Nat.mul_le_mul h5 h5
      exact_mod_cast h6
    have hcnn : (0 : ℝ) ≤ c := Nat.cast_nonneg c
    have hCnn : (0 : ℝ) ≤ C := Nat.cast_nonneg C
    have hsnn : (0 : ℝ) ≤ s := Nat.cast_nonneg s
    calc ((kNatVal U i : ℕ) : ℝ) + C ≤ 2 * (2 * (s : ℝ) + 1) + c + C := by linarith
      _ ≤ (6 + (c : ℝ) + C) * ((s : ℝ) + 1) := by
        nlinarith [mul_nonneg hcnn hsnn, mul_nonneg hCnn hsnn]
      _ ≤ (δ * ((s : ℝ) + 1)) * ((s : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right hD (by positivity)
      _ = δ * (((s : ℝ) + 1) * ((s : ℝ) + 1)) := by ring
      _ ≤ δ * ((2 ^ (2 * s) : ℕ) : ℝ) := mul_le_mul_of_nonneg_left hP hδ.le

/-- The prefix complexity of an optimal prefix machine is finite: `KPPlain` is the cast of
`kVal`. -/
private lemma exists_seq_KP_profile_KPPlain_eq (U : Map)
    (hU : IsOptimalPrefixConditional U) (z : BitString) :
    KPPlain U z = (kVal U z : ℕ∞) :=
  (ENat.natCast_toNat (KPPlain_ne_top_of_optimal U hU z)).symm

/-- A computable map applied to the pair code of `x` and `y` has complexity at most
`K x + K y + O(1)`. -/
private lemma exists_seq_KP_profile_map_pair (U : Map)
    (hU : IsOptimalPrefixConditional U) (F : BitString → BitString) (hF : Computable F) :
    ∃ c : ℕ, ∀ x y : BitString, kVal U (F (pairCode x y)) ≤ kVal U x + kVal U y + c := by
  obtain ⟨c1, hc1⟩ := KPPlain_map_le U hU F hF
  obtain ⟨c2, hc2⟩ := KPPair_le_KPPlain_add_KPPlain U hU
  refine ⟨c1 + c2, fun x y => ?_⟩
  have h1 : KPPlain U (F (pairCode x y)) ≤
      KPPlain U x + KPPlain U y + (c2 : ℕ∞) + (c1 : ℕ∞) := by
    calc KPPlain U (F (pairCode x y)) ≤ KPPlain U (pairCode x y) + (c1 : ℕ∞) := hc1 _
      _ = KPPair U x y + (c1 : ℕ∞) := rfl
      _ ≤ KPPlain U x + KPPlain U y + (c2 : ℕ∞) + (c1 : ℕ∞) := by
        gcongr
        exact hc2 x y
  have e0 := exists_seq_KP_profile_KPPlain_eq U hU (F (pairCode x y))
  have ex := exists_seq_KP_profile_KPPlain_eq U hU x
  have ey := exists_seq_KP_profile_KPPlain_eq U hU y
  rw [e0, ex, ey] at h1
  have h2 : ((kVal U (F (pairCode x y)) : ℕ) : ℕ∞) ≤
      ((kVal U x + kVal U y + (c1 + c2) : ℕ) : ℕ∞) := by
    push_cast
    calc _ ≤ _ := h1
      _ = _ := by ring
  exact_mod_cast h2

/-- The map `pairCode x (bin m) ↦ x 0^m` is computable. -/
private lemma exists_seq_KP_profile_F_computable :
    Computable (fun z : BitString =>
      decodeFirst z ++ List.replicate (bitsToNat (decodeSecond z)) false) := by
  have h1 : Primrec (fun z : BitString => decodeFirst z) :=
    CodedFiniteDistribution.decodeFirst_primrec
  have h2 : Primrec (fun z : BitString => decodeSecond z) :=
    CodedFiniteDistribution.decodeSecond_primrec
  have h3 : Primrec (fun z : BitString => bitsToNat (decodeSecond z)) :=
    bitsToNat_primrec.comp h2
  have h4 : Primrec (fun z : BitString =>
      List.replicate (bitsToNat (decodeSecond z)) false) :=
    Primrec.list_replicate.comp h3 (Primrec.const false)
  exact (Primrec.list_append.comp h1 h4).to_comp

/-- Step 2 of the proof of `exists_seq_KP_profile`: appending `m` zeros to `x` costs
`K(bin m) + O(1)` (the map `(x, bin m) ↦ x 0^m` is computable). -/
private lemma exists_seq_KP_profile_append_zeros (U : Map)
    (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (m : ℕ),
      kVal U (x ++ List.replicate m false) ≤ kVal U x + kNatVal U m + c := by
  obtain ⟨c, hc⟩ := exists_seq_KP_profile_map_pair U hU
    (fun z : BitString => decodeFirst z ++ List.replicate (bitsToNat (decodeSecond z)) false)
    exists_seq_KP_profile_F_computable
  refine ⟨c, fun x m => ?_⟩
  have h := hc x (natBits m)
  have hb : bitsToNat (natBits m) = m := bitsToNat_bits m
  simp only [decodeFirst_pairCode, decodeSecond_pairCode, hb] at h
  exact h

/-- The natural-number value of the prefix complexity is the prefix complexity, since the latter is
finite for an optimal machine. -/
private lemma exists_seq_KP_profile_cast (U : Map) (hU : IsOptimalPrefixConditional U)
    (x : BitString) : ((kVal U x : ℕ) : ℕ∞) = KPPlain U x :=
  ENat.natCast_toNat (KPPlain_ne_top_of_optimal U hU x)

/-- The map `(z, bin r) ↦ z` with the bit `b` put at the position `|z| - 1 - r` is computable. -/
private lemma exists_seq_KP_profile_map (b : Bool) :
    Computable (fun w : BitString =>
      (decodeFirst w).take ((decodeFirst w).length - 1 - bitsToNat (decodeSecond w)) ++
        b :: (decodeFirst w).drop
          ((decodeFirst w).length - 1 - bitsToNat (decodeSecond w) + 1)) := by
  have hfst : Primrec (fun w : BitString => decodeFirst w) :=
    CodedFiniteDistribution.decodeFirst_primrec
  have hr : Primrec (fun w : BitString => bitsToNat (decodeSecond w)) :=
    bitsToNat_primrec.comp CodedFiniteDistribution.decodeSecond_primrec
  have hj : Primrec (fun w : BitString =>
      (decodeFirst w).length - 1 - bitsToNat (decodeSecond w)) :=
    Primrec.nat_sub.comp (Primrec.nat_sub.comp (Primrec.list_length.comp hfst)
      (Primrec.const 1)) hr
  have htake := Primrec.list_take.comp hj hfst
  have hdrop := Primrec.list_drop.comp (Primrec.succ.comp hj) hfst
  have hcons := Primrec.list_cons.comp (Primrec.const b) hdrop
  exact (Primrec.list_append.comp htake hcons).to_comp

/-- The value of that map on a pair code. -/
private lemma exists_seq_KP_profile_eval (z : BitString) (r : ℕ) (b : Bool)
    (hr : r < z.length) :
    (decodeFirst (pairCode z (natBits r))).take
        ((decodeFirst (pairCode z (natBits r))).length - 1 -
          bitsToNat (decodeSecond (pairCode z (natBits r)))) ++
      b :: (decodeFirst (pairCode z (natBits r))).drop
        ((decodeFirst (pairCode z (natBits r))).length - 1 -
          bitsToNat (decodeSecond (pairCode z (natBits r))) + 1) =
      z.set (z.length - 1 - r) b := by
  rw [decodeFirst_pairCode, decodeSecond_pairCode]
  unfold natBits
  rw [bitsToNat_bits, List.set_eq_take_append_cons_drop, ite_eq_left (by omega)]

/-- Step 3 of the proof of `exists_seq_KP_profile`: changing one bit of `z`, the bit
being given by its distance `r` from the end of `z`, costs `K(bin r) + O(1)`. -/
private lemma exists_seq_KP_profile_flip (U : Map)
    (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (z : BitString) (r : ℕ) (b : Bool), r < z.length →
      kVal U (z.set (z.length - 1 - r) b) ≤ kVal U z + kNatVal U r + c := by
  obtain ⟨c2, hc2⟩ := KPPair_le_KPPlain_add_KPPlain U hU
  have key : ∀ b : Bool, ∃ c : ℕ, ∀ (z : BitString) (r : ℕ), r < z.length →
      kVal U (z.set (z.length - 1 - r) b) ≤ kVal U z + kNatVal U r + c := by
    intro b
    obtain ⟨c1, hc1⟩ := KPPlain_map_le U hU _ (exists_seq_KP_profile_map b)
    refine ⟨c1 + c2, fun z r hr => ?_⟩
    have h1 := hc1 (pairCode z (natBits r))
    rw [exists_seq_KP_profile_eval z r b hr] at h1
    have h2 := hc2 z (natBits r)
    have hz := exists_seq_KP_profile_cast U hU z
    have hn : ((kNatVal U r : ℕ) : ℕ∞) = KPPlain U (natBits r) :=
      exists_seq_KP_profile_cast U hU (natBits r)
    have h3 : KPPlain U (z.set (z.length - 1 - r) b) ≤
        ((kVal U z + kNatVal U r + (c1 + c2) : ℕ) : ℕ∞) := by
      calc KPPlain U (z.set (z.length - 1 - r) b)
          ≤ KPPlain U (pairCode z (natBits r)) + (c1 : ℕ∞) := h1
        _ = KPPair U z (natBits r) + (c1 : ℕ∞) := rfl
        _ ≤ (KPPlain U z + KPPlain U (natBits r) + (c2 : ℕ∞)) + (c1 : ℕ∞) := by
          gcongr
        _ = ((kVal U z + kNatVal U r + (c1 + c2) : ℕ) : ℕ∞) := by
          rw [← hz, ← hn]
          push_cast
          ring
    exact ENat.toNat_le_of_le_natCast h3
  obtain ⟨cT, hT⟩ := key true
  obtain ⟨cF, hF⟩ := key false
  refine ⟨cT + cF, fun z r b hr => ?_⟩
  cases b
  · have := hF z r hr
    omega
  · have := hT z r hr
    omega

/-- Step 4 of the proof of `exists_seq_KP_profile`: discrete intermediate value lemma.
A sequence `g` with `g (i + 1) ≤ g i + s`, `g 0 ≤ t ≤ g N` takes a value in `[t, t + s]`. -/
private lemma exists_seq_KP_profile_ivt (g : ℕ → ℕ) (N s t : ℕ)
    (hstep : ∀ i, i < N → g (i + 1) ≤ g i + s) (h0 : g 0 ≤ t) (hN : t ≤ g N) :
    ∃ i, i ≤ N ∧ t ≤ g i ∧ g i ≤ t + s := by
  induction N with
  | zero => exact ⟨0, le_rfl, by omega, by omega⟩
  | succ N ih =>
    by_cases h : t ≤ g N
    · obtain ⟨i, hi, h1, h2⟩ := ih (fun i hi => hstep i (by omega)) h
      exact ⟨i, by omega, h1, h2⟩
    · have := hstep N (by omega)
      exact ⟨N + 1, le_rfl, hN, by omega⟩

/-- Changing the `i`-th bit of the block `y1.take i ++ 0^(m - i)` to `y1[i]` gives the next element
of the path from `0^m` to `y1`. -/
private lemma exists_seq_KP_profile_path_set (x y1 : BitString) (m i : ℕ)
    (hy : y1.length = m) (hi : i < m) :
    (x ++ (y1.take i ++ List.replicate (m - i) false)).set (x.length + i)
        (y1[i]'(by omega)) =
      x ++ (y1.take (i + 1) ++ List.replicate (m - (i + 1)) false) := by
  have hi' : i < y1.length := by omega
  have h1 : y1.take (i + 1) = y1.take i ++ [y1[i]'hi'] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hi']
    rfl
  have h2 : List.replicate (m - i) false = false :: List.replicate (m - (i + 1)) false := by
    have : m - i = (m - (i + 1)) + 1 := by omega
    rw [this, List.replicate_succ]
  have hlen : (y1.take i).length = i := by
    rw [List.length_take]; omega
  rw [h1, h2]
  rw [List.set_append_right _ _ (by omega)]
  rw [Nat.add_sub_cancel_left]
  rw [List.set_append_right _ _ (by omega)]
  rw [hlen, Nat.sub_self]
  simp only [List.set_cons_zero, List.append_assoc, List.singleton_append]

/-- Step 5 of the proof of `exists_seq_KP_profile`: one block step.  If `K(x)` is within
`c1` of `t`, the numbers `i ≤ m` have price `K(bin i) + c0 ≤ e ≤ c1`, and the new target `t'` is
between `t + e + c1` and `t + m - e - c1`, then some `y` of length `m` has `K(x y)` within `c1` of
`t'`. -/
private lemma exists_seq_KP_profile_block (U : Map)
    (hU : IsOptimalPrefixConditional U) :
    ∃ c0 : ℕ, ∀ (x : BitString) (m t t' e c1 : ℕ),
      (∀ i : ℕ, i ≤ m → kNatVal U i + c0 ≤ e) → e ≤ c1 →
      kVal U x ≤ t + c1 → t ≤ kVal U x + c1 →
      t + e + c1 ≤ t' → t' + e + c1 ≤ t + m →
      ∃ y : BitString, y.length = m ∧ kVal U (x ++ y) ≤ t' + c1 ∧ t' ≤ kVal U (x ++ y) + c1 := by
  obtain ⟨cE, hE⟩ := exists_extension_KP_ge_sub U hU
  obtain ⟨cB1, hB1⟩ := exists_seq_KP_profile_append_zeros U hU
  obtain ⟨cB2, hB2⟩ := exists_seq_KP_profile_flip U hU
  refine ⟨cE + cB1 + cB2, fun x m t t' e c1 hK hec hx1 hx2 hlo hhi => ?_⟩
  obtain ⟨y1, hy1, hy1K⟩ := hE x m
  have hlen : ∀ i, i ≤ m →
      (x ++ (y1.take i ++ List.replicate (m - i) false)).length = x.length + m := by
    intro i hi
    simp [hy1]
    omega
  have hstep : ∀ i, i < m →
      kVal U (x ++ (y1.take (i + 1) ++ List.replicate (m - (i + 1)) false)) ≤
        kVal U (x ++ (y1.take i ++ List.replicate (m - i) false)) + e := by
    intro i hi
    have hi' : i < y1.length := by omega
    have hset := exists_seq_KP_profile_path_set x y1 m i hy1 hi
    have hr : m - 1 - i < (x ++ (y1.take i ++ List.replicate (m - i) false)).length := by
      rw [hlen i hi.le]; omega
    have h1 := hB2 (x ++ (y1.take i ++ List.replicate (m - i) false)) (m - 1 - i)
      (y1[i]'hi') hr
    have hpos : (x ++ (y1.take i ++ List.replicate (m - i) false)).length - 1 - (m - 1 - i) =
        x.length + i := by
      rw [hlen i hi.le]; omega
    rw [hpos, hset] at h1
    have h2 := hK (m - 1 - i) (by omega)
    omega
  have h0 : kVal U (x ++ (y1.take 0 ++ List.replicate (m - 0) false)) ≤ t' := by
    have h1 := hB1 x m
    have h2 := hK m le_rfl
    have : x ++ (y1.take 0 ++ List.replicate (m - 0) false) = x ++ List.replicate m false := by
      simp
    rw [this]
    omega
  have hm' : t' ≤ kVal U (x ++ (y1.take m ++ List.replicate (m - m) false)) := by
    have h2 := hK m le_rfl
    have : x ++ (y1.take m ++ List.replicate (m - m) false) = x ++ y1 := by
      simp [hy1]
    rw [this]
    omega
  obtain ⟨i, hi, hti, hit⟩ := exists_seq_KP_profile_ivt
    (fun i => kVal U (x ++ (y1.take i ++ List.replicate (m - i) false))) m e t' hstep h0 hm'
  refine ⟨y1.take i ++ List.replicate (m - i) false, ?_, ?_, ?_⟩
  · simp [hy1]
    omega
  · omega
  · omega

/-- Step 6 of the proof of `exists_seq_KP_profile`: a chain lemma.  If a property `P`
of the strings of length `k m` holds for `[]` and every string with `P k` has an extension by a
block of `m` bits with `P (k + 1)`, then some infinite sequence has `P k` for all its prefixes of
length `k m`. -/
private lemma exists_seq_KP_profile_chain {m : ℕ} (hm : 0 < m) (P : ℕ → BitString → Prop)
    (h0 : P 0 [])
    (hstep : ∀ (k : ℕ) (x : BitString), x.length = k * m → P k x →
      ∃ y : BitString, y.length = m ∧ P (k + 1) (x ++ y)) :
    ∃ w : CantorSeq, ∀ k : ℕ, P k (cantorPrefix w (k * m)) := by
  classical
  -- the next block, chosen when the hypotheses of `hstep` hold
  let next : ℕ → BitString → BitString := fun k x =>
    if h : x.length = k * m ∧ P k x then (hstep k x h.1 h.2).choose else []
  have hnext : ∀ k x, x.length = k * m → P k x →
      (next k x).length = m ∧ P (k + 1) (x ++ next k x) := by
    intro k x hx hP
    have h : x.length = k * m ∧ P k x := ⟨hx, hP⟩
    have hnk : next k x = (hstep k x h.1 h.2).choose := by
      simp only [next, dite_eq_left h]
    rw [hnk]
    exact (hstep k x h.1 h.2).choose_spec
  -- the chain of strings
  let X : ℕ → BitString := fun k => Nat.rec (motive := fun _ => BitString) []
    (fun j x => x ++ next j x) k
  have hX0 : X 0 = [] := rfl
  have hXs : ∀ k, X (k + 1) = X k ++ next k (X k) := fun k => rfl
  have hXinv : ∀ k, (X k).length = k * m ∧ P k (X k) := by
    intro k
    induction k with
    | zero => exact ⟨by simp [hX0], by rw [hX0]; exact h0⟩
    | succ k ih =>
      obtain ⟨hlen, hP⟩ := ih
      obtain ⟨hl, hP'⟩ := hnext k (X k) hlen hP
      refine ⟨?_, ?_⟩
      · rw [hXs, List.length_append, hlen, hl]; ring
      · rw [hXs]; exact hP'
  have hXpre : ∀ a b, X a <+: X (a + b) := by
    intro a b
    induction b with
    | zero => exact List.prefix_refl _
    | succ b ih =>
      have h1 : X (a + b + 1) = X (a + b) ++ next (a + b) (X (a + b)) := hXs (a + b)
      change X a <+: X (a + b + 1)
      rw [h1]
      exact ih.trans (List.prefix_append _ _)
  refine ⟨fun n => (X (n / m + 1)).getD n false, fun k => ?_⟩
  have key : cantorPrefix (fun n => (X (n / m + 1)).getD n false) (k * m) = X k := by
    apply List.ext_getElem
    · rw [cantorPrefix_length, (hXinv k).1]
    · intro i h1 h2
      rw [cantorPrefix_getElem]
      have hik : i < k * m := by rw [cantorPrefix_length] at h1; exact h1
      have hq : i / m + 1 ≤ k := by
        have := (Nat.div_lt_iff_lt_mul hm).mpr hik
        omega
      have hi1 : i < (X (i / m + 1)).length := by
        have hlen1 : (X (i / m + 1)).length = (i / m + 1) * m := (hXinv (i / m + 1)).1
        rw [hlen1]
        have e1 := Nat.div_add_mod i m
        have e2 := Nat.mod_lt i hm
        nlinarith
      have hpre : X (i / m + 1) <+: X k := by
        obtain ⟨b, hb⟩ := Nat.exists_eq_add_of_le hq
        have hb' := hXpre (i / m + 1) b
        rw [← hb] at hb'
        exact hb'
      change (X (i / m + 1)).getD i false = (X k)[i]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi1]
      simp only [Option.getD_some]
      exact hpre.getElem hi1
  rw [key]
  exact (hXinv k).2

/-- The map `pairCode x y ↦ x y` is computable. -/
private lemma exists_seq_KP_profile_concat_computable :
    Computable (fun z : BitString => decodeFirst z ++ decodeSecond z) := by
  have h1 : Primrec (fun z : BitString => decodeFirst z) :=
    CodedFiniteDistribution.decodeFirst_primrec
  have h2 : Primrec (fun z : BitString => decodeSecond z) :=
    CodedFiniteDistribution.decodeSecond_primrec
  exact (Primrec.list_append.comp h1 h2).to_comp

/-- The map `pairCode (x y) y ↦ x` is computable. -/
private lemma exists_seq_KP_profile_chop_computable :
    Computable (fun z : BitString =>
      (decodeFirst z).take ((decodeFirst z).length - (decodeSecond z).length)) := by
  have h1 : Primrec (fun z : BitString => decodeFirst z) :=
    CodedFiniteDistribution.decodeFirst_primrec
  have h2 : Primrec (fun z : BitString => decodeSecond z) :=
    CodedFiniteDistribution.decodeSecond_primrec
  have h3 : Primrec (fun z : BitString => (decodeFirst z).length - (decodeSecond z).length) :=
    Primrec.nat_sub.comp (Primrec.list_length.comp h1) (Primrec.list_length.comp h2)
  exact (Primrec.list_take.comp h3 h1).to_comp

/-- Step 7 of the proof of `exists_seq_KP_profile`: appending a short string `y` to `x`
changes the prefix complexity by at most `2 |y| + O(1)`.  (Uses the auxiliary lemmas
`exists_seq_KP_profile_KPPlain_eq` and `exists_seq_KP_profile_map_pair`, which must be
declared before it.) -/
private lemma exists_seq_KP_profile_append_short (U : Map)
    (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x y : BitString),
      kVal U (x ++ y) ≤ kVal U x + 2 * y.length + c ∧
        kVal U x ≤ kVal U (x ++ y) + 2 * y.length + c := by
  obtain ⟨c1, hc1⟩ := exists_seq_KP_profile_map_pair U hU
    (fun z : BitString => decodeFirst z ++ decodeSecond z)
    exists_seq_KP_profile_concat_computable
  obtain ⟨c2, hc2⟩ := exists_seq_KP_profile_map_pair U hU
    (fun z : BitString =>
      (decodeFirst z).take ((decodeFirst z).length - (decodeSecond z).length))
    exists_seq_KP_profile_chop_computable
  obtain ⟨c3, hc3⟩ := KPPlain_le_two_mul_length U hU
  have hlen : ∀ y : BitString, kVal U y ≤ 2 * y.length + c3 := by
    intro y
    have h := hc3 y
    rw [exists_seq_KP_profile_KPPlain_eq U hU y] at h
    exact_mod_cast h
  refine ⟨c1 + c2 + c3, fun x y => ⟨?_, ?_⟩⟩
  · have h := hc1 x y
    simp only [decodeFirst_pairCode, decodeSecond_pairCode] at h
    have := hlen y
    omega
  · have h := hc2 (x ++ y) y
    simp only [decodeFirst_pairCode, decodeSecond_pairCode, List.length_append,
      Nat.add_sub_cancel, List.take_left] at h
    have := hlen y
    omega

/-- Step 8 of the proof of `exists_seq_KP_profile`: the profile `f` cannot drift by more
than `r + H` over `r` steps. -/
private lemma exists_seq_KP_profile_f_drift (f : ℕ → ℕ) {eps : ℝ} (heps : 0 < eps)
    (H : ℕ)
    (hlow : ∀ n h : ℕ, H ≤ h → (f n : ℝ) + eps * h ≤ (f (n + h) : ℝ))
    (hhigh : ∀ n h : ℕ, H ≤ h → (f (n + h) : ℝ) ≤ (f n : ℝ) + (1 - eps) * h) :
    ∀ n r : ℕ, f n ≤ f (n + r) + H ∧ f (n + r) ≤ f n + r + H := by
  intro n r
  have h1 := hlow (n + r) H le_rfl
  have h2 := hhigh n (r + H) (by omega)
  have h3 := hhigh (n + r) H le_rfl
  have h4 := hlow n (r + H) (by omega)
  have e : n + r + H = n + (r + H) := by omega
  rw [e] at h1 h3
  push_cast at h2 h4
  have hH : 0 ≤ eps * (H : ℝ) := by positivity
  have hr : 0 ≤ eps * (r : ℝ) := by positivity
  have e1 : (1 - eps) * ((r : ℝ) + H) = r + H - eps * r - eps * H := by ring
  have e2 : eps * ((r : ℝ) + H) = eps * r + eps * H := by ring
  have e3 : (1 - eps) * (H : ℝ) = H - eps * H := by ring
  constructor
  · have : (f n : ℝ) ≤ (f (n + r) : ℝ) + H := by
      rw [e2] at h4
      rw [e3] at h3
      linarith
    exact_mod_cast this
  · have : (f (n + r) : ℝ) ≤ (f n : ℝ) + r + H := by
      rw [e1] at h2
      linarith
    exact_mod_cast this

/-- Step 9 of the proof of `exists_seq_KP_profile`: for a suitable large block length
`m`, some sequence `w` has `K` of its prefixes of length `k m` within `c1` of `f (k m)`. -/
private lemma exists_seq_KP_profile_boundaries (U : Map)
    (hU : IsOptimalPrefixConditional U) (f : ℕ → ℕ) {eps : ℝ} (heps : 0 < eps) (H : ℕ)
    (hlow : ∀ n h : ℕ, H ≤ h → (f n : ℝ) + eps * h ≤ (f (n + h) : ℝ))
    (hhigh : ∀ n h : ℕ, H ≤ h → (f (n + h) : ℝ) ≤ (f n : ℝ) + (1 - eps) * h) :
    ∃ (m : ℕ) (w : CantorSeq) (c1 : ℕ), 0 < m ∧ ∀ k : ℕ,
      kVal U (cantorPrefix w (k * m)) ≤ f (k * m) + c1 ∧
        f (k * m) ≤ kVal U (cantorPrefix w (k * m)) + c1 := by
  obtain ⟨c0, hc0⟩ := exists_seq_KP_profile_block U hU
  obtain ⟨m, hMm, hmpos, hK⟩ := exists_seq_KP_profile_blockLength U hU
    (δ := eps / 4) (by positivity) c0
    (H + 1 + ⌈2 * ((f 0 : ℝ) + (kVal U [] : ℝ) + 4) / eps⌉₊)
  have hHm : H ≤ m := by omega
  -- the block length is large
  have hεm : 2 * ((f 0 : ℝ) + (kVal U [] : ℝ) + 4) ≤ eps * m := by
    have h1 : (⌈2 * ((f 0 : ℝ) + (kVal U [] : ℝ) + 4) / eps⌉₊ : ℝ) ≤ m := by
      exact_mod_cast (by omega : ⌈2 * ((f 0 : ℝ) + (kVal U [] : ℝ) + 4) / eps⌉₊ ≤ m)
    have h2 := Nat.le_ceil (2 * ((f 0 : ℝ) + (kVal U [] : ℝ) + 4) / eps)
    have h3 : 2 * ((f 0 : ℝ) + (kVal U [] : ℝ) + 4) / eps ≤ m := h2.trans h1
    rw [div_le_iff₀ heps] at h3
    linarith
  have hf0 : (0 : ℝ) ≤ f 0 := Nat.cast_nonneg _
  have hk0 : (0 : ℝ) ≤ kVal U [] := Nat.cast_nonneg _
  have hεm8 : 8 ≤ eps * m := by linarith
  -- the two error radii
  have hmreal : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have he1 : (⌈eps / 4 * m⌉₊ : ℝ) < eps / 4 * m + 1 := Nat.ceil_lt_add_one (by positivity)
  have hc1 : (⌈eps * m / 2⌉₊ : ℝ) < eps * m / 2 + 1 := Nat.ceil_lt_add_one (by positivity)
  have hc1' : eps * m / 2 ≤ (⌈eps * m / 2⌉₊ : ℝ) := Nat.le_ceil _
  have hee : ⌈eps / 4 * m⌉₊ ≤ ⌈eps * m / 2⌉₊ := by
    apply Nat.ceil_le_ceil
    nlinarith
  have hsum : (⌈eps / 4 * m⌉₊ : ℝ) + (⌈eps * m / 2⌉₊ : ℝ) ≤ eps * m := by nlinarith
  have hKe : ∀ i : ℕ, i ≤ m → kNatVal U i + c0 ≤ ⌈eps / 4 * m⌉₊ := by
    intro i hi
    have h1 := hK i hi
    have h2 : ((kNatVal U i + c0 : ℕ) : ℝ) ≤ (⌈eps / 4 * m⌉₊ : ℝ) := by
      push_cast
      exact h1.trans (Nat.le_ceil _)
    exact_mod_cast h2
  have hbig : f 0 + kVal U [] + 4 ≤ ⌈eps * m / 2⌉₊ := by
    have h1 : ((f 0 + kVal U [] + 4 : ℕ) : ℝ) ≤ (⌈eps * m / 2⌉₊ : ℝ) := by
      push_cast
      linarith
    exact_mod_cast h1
  have hP0 : kVal U [] ≤ f (0 * m) + ⌈eps * m / 2⌉₊ ∧
      f (0 * m) ≤ kVal U [] + ⌈eps * m / 2⌉₊ := by
    rw [Nat.zero_mul]
    omega
  have hstep : ∀ (k : ℕ) (x : BitString), x.length = k * m →
      (kVal U x ≤ f (k * m) + ⌈eps * m / 2⌉₊ ∧ f (k * m) ≤ kVal U x + ⌈eps * m / 2⌉₊) →
      ∃ y : BitString, y.length = m ∧
        (kVal U (x ++ y) ≤ f ((k + 1) * m) + ⌈eps * m / 2⌉₊ ∧
          f ((k + 1) * m) ≤ kVal U (x ++ y) + ⌈eps * m / 2⌉₊) := by
    intro k x _ hx
    have hkm : (k + 1) * m = k * m + m := by ring
    have hl := hlow (k * m) m hHm
    have hh := hhigh (k * m) m hHm
    have hA : f (k * m) + ⌈eps / 4 * m⌉₊ + ⌈eps * m / 2⌉₊ ≤ f ((k + 1) * m) := by
      rw [hkm]
      have : ((f (k * m) + ⌈eps / 4 * m⌉₊ + ⌈eps * m / 2⌉₊ : ℕ) : ℝ) ≤ (f (k * m + m) : ℝ) := by
        push_cast
        linarith
      exact_mod_cast this
    have hB : f ((k + 1) * m) + ⌈eps / 4 * m⌉₊ + ⌈eps * m / 2⌉₊ ≤ f (k * m) + m := by
      rw [hkm]
      have : ((f (k * m + m) + ⌈eps / 4 * m⌉₊ + ⌈eps * m / 2⌉₊ : ℕ) : ℝ) ≤
          ((f (k * m) + m : ℕ) : ℝ) := by
        push_cast
        linarith
      exact_mod_cast this
    exact hc0 x m (f (k * m)) (f ((k + 1) * m)) ⌈eps / 4 * m⌉₊ ⌈eps * m / 2⌉₊ hKe hee
      hx.1 hx.2 hA hB
  obtain ⟨w, hw⟩ := exists_seq_KP_profile_chain hmpos
    (fun k x => kVal U x ≤ f (k * m) + ⌈eps * m / 2⌉₊ ∧ f (k * m) ≤ kVal U x + ⌈eps * m / 2⌉₊)
    hP0 hstep
  exact ⟨m, w, ⌈eps * m / 2⌉₊, hmpos, hw⟩

/-- **SUV Problem 246, p. 242.**  The statement of Problem 47 with prefix instead of plain
complexity: realisation of a prescribed complexity profile.

We use the uniformly large-increment reading of Problem 47, also used by the archived
`exercise47_profile`.  The printed Problem 47 (p. 42; author's PDF p. 55) says the two inequalities
hold for all `n, h`.  For integer-valued `f`, its case `h = 1` is impossible when `eps > 0`.
Here they hold for all `n` and all `h ≥ H`, for one fixed threshold `H`.  This makes the intended
block construction non-vacuous; it is a correction of the printed premise, not a verbatim copy. -/
theorem exists_seq_KP_profile (U : Map) (hU : IsOptimalPrefixConditional U) (f : ℕ → ℕ) {eps : ℝ}
    (heps : 0 < eps) (H : ℕ)
    (hlow : ∀ n h : ℕ, H ≤ h → (f n : ℝ) + eps * h ≤ (f (n + h) : ℝ))
    (hhigh : ∀ n h : ℕ, H ≤ h → (f (n + h) : ℝ) ≤ (f n : ℝ) + (1 - eps) * h) :
    ∃ (w : CantorSeq) (c : ℕ), ∀ n : ℕ,
      KPPlain U (cantorPrefix w n) ≤ ((f n + c : ℕ) : ℕ∞) ∧
        ((f n : ℕ) : ℕ∞) ≤ KPPlain U (cantorPrefix w n) + (c : ℕ∞) := by
  obtain ⟨m, w, c1, hm, hw⟩ := exists_seq_KP_profile_boundaries U hU f heps H hlow hhigh
  obtain ⟨c7, h7⟩ := exists_seq_KP_profile_append_short U hU
  have h8 := exists_seq_KP_profile_f_drift f heps H hlow hhigh
  refine ⟨w, c1 + 3 * m + c7 + H, fun n => ?_⟩
  have hn : n = n / m * m + n % m := (Nat.div_add_mod' n m).symm
  have hr_lt : n % m < m := Nat.mod_lt n hm
  have hkm_le : n / m * m ≤ n := by omega
  set y : BitString := (cantorPrefix w n).drop (n / m * m) with hy
  have hylen : y.length = n % m := by
    rw [hy, List.length_drop, cantorPrefix_length]
    omega
  have hxy : cantorPrefix w n = cantorPrefix w (n / m * m) ++ y := by
    rw [hy, ← cantorPrefix_take w (n / m * m) n hkm_le]
    exact (List.take_append_drop _ _).symm
  have h7' := h7 (cantorPrefix w (n / m * m)) y
  rw [← hxy] at h7'
  obtain ⟨hw1, hw2⟩ := hw (n / m)
  obtain ⟨hf1, hf2⟩ := h8 (n / m * m) (n % m)
  rw [← hn] at hf1 hf2
  have hK : KPPlain U (cantorPrefix w n) = (kVal U (cantorPrefix w n) : ℕ∞) := by
    unfold kVal
    exact (ENat.natCast_toNat (KPPlain_ne_top_of_optimal U hU _)).symm
  rw [hK]
  rw [hylen] at h7'
  constructor
  · have : kVal U (cantorPrefix w n) ≤ f n + (c1 + 3 * m + c7 + H) := by omega
    exact_mod_cast this
  · have : f n ≤ kVal U (cantorPrefix w n) + (c1 + 3 * m + c7 + H) := by omega
    exact_mod_cast this

end Kolmogorov.Applications
