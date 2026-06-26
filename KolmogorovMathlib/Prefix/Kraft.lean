/-
Copyright (c) 2024 Alexey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey
-/
import KolmogorovMathlib.Prefix.UniquelyDecodable
import KolmogorovMathlib.AlgorithmicProbability.Semimeasure
import KolmogorovMathlib.Complexity.Incompressibility
import Mathlib.Data.ENNReal.Basic

/-!
# Finite Kraft Inequality for Prefix-Free Bitstring Codes

This module specializes Mathlib's `InformationTheory.kraft_mcmillan_inequality` —
stated for finite, uniquely decodable codes over ℝ — to *prefix-free* finite sets of
bitstrings. The bridge `IsPrefixFree.uniquelyDecodable` (from
`KolmogorovMathlib.Prefix.UniquelyDecodable`) discharges the unique-decodability
hypothesis; the alphabet is `Bool`, so `Fintype.card Bool = 2` gives the familiar
base `1/2`.

Two forms are provided:

* `finset_kraft_real_le_one` — over ℝ, `∑_{w ∈ F} (1/2)^|w| ≤ 1`, with **no** extra
  hypothesis beyond prefix-freeness. The empty-string corner case (`[] ∈ F`, where
  Mathlib's unique-decodability hypothesis fails) is handled directly: a prefix-free
  set containing `[]` is the singleton `{[]}`, whose Kraft sum is exactly `1`.
* `finset_kraft_progWeight_le_one` — the same bound transported to `ℝ≥0∞` using the
  repository's `progWeight`, matching the shape of `domainWeight` so a later slot can
  push it to the countable `domainWeight M y ≤ 1`.

This slot stays **finite**: no `tsum`, no countable Kraft, no normalization theorem.
Those are deliberately deferred. No logarithms, no coding-theorem equality.
-/

namespace Kolmogorov

open scoped ENNReal
open InformationTheory

/-! ### Leaf-counting toolkit for the Kraft inequality

Since this Mathlib version does not provide `kraft_mcmillan_inequality`, we prove the
finite Kraft bound directly by the classical leaf-counting argument: a codeword `w`
of length `≤ L` is the prefix of exactly `2^(L - |w|)` strings of length `L`, and
prefix-freeness makes these "leaf sets" pairwise disjoint subsets of the `2^L`
strings of length `L`. -/

/-- The length-`L` strings having `w` as a prefix (the "leaves below `w`"). -/
noncomputable def kraftLeaves (w : BitString) (L : ℕ) : Finset BitString :=
  (stringsOfLength L).filter (fun u => w <+: u)

lemma mem_kraftLeaves {w u : BitString} {L : ℕ} :
    u ∈ kraftLeaves w L ↔ u.length = L ∧ w <+: u := by
  rw [kraftLeaves, Finset.mem_filter, memStringsOfLength]

lemma kraftLeaves_subset (w : BitString) (L : ℕ) :
    kraftLeaves w L ⊆ stringsOfLength L :=
  Finset.filter_subset _ _

lemma kraftLeaves_card {w : BitString} {L : ℕ} (h : w.length ≤ L) :
    (kraftLeaves w L).card = 2 ^ (L - w.length) := by
  have hset : kraftLeaves w L = (stringsOfLength (L - w.length)).image (fun s => w ++ s) := by
    ext u
    rw [mem_kraftLeaves, Finset.mem_image]
    constructor
    · rintro ⟨hlen, hpre⟩
      refine ⟨u.drop w.length, ?_, ?_⟩
      · rw [memStringsOfLength, List.length_drop, hlen]
      · exact List.prefix_iff_eq_append.mp hpre
    · rintro ⟨s, hs, rfl⟩
      rw [memStringsOfLength] at hs
      refine ⟨?_, List.prefix_append w s⟩
      rw [List.length_append, hs]; omega
  rw [hset, Finset.card_image_of_injective _ (fun a b hab => List.append_cancel_left hab),
      cardStringsOfLength]

lemma kraftLeaves_disjoint {S : Set BitString} (hS : IsPrefixFree S) {L : ℕ}
    {w1 w2 : BitString} (h1 : w1 ∈ S) (h2 : w2 ∈ S) (hne : w1 ≠ w2) :
    Disjoint (kraftLeaves w1 L) (kraftLeaves w2 L) := by
  rw [Finset.disjoint_left]
  intro u hu1 hu2
  rw [mem_kraftLeaves] at hu1 hu2
  rcases List.prefix_or_prefix_of_prefix hu1.2 hu2.2 with hp | hp
  · exact hne (hS h1 h2 hp)
  · exact hne (hS h2 h1 hp).symm

/-- **Finite Kraft inequality (real form).** For any prefix-free finite set `F` of
bitstrings, the Kraft sum `∑_{w ∈ F} (1/2)^{|w|}` is at most `1`. The proof is the
classical leaf-counting argument (`kraftLeaves`): each codeword `w` of length `≤ L`
(with `L` the maximum codeword length) is the prefix of exactly `2^(L - |w|)` strings
of length `L`, prefix-freeness makes these leaf sets pairwise disjoint, and there are
only `2^L` strings of length `L`, giving `∑ 2^(L - |w|) ≤ 2^L`, i.e. the bound. -/
theorem finset_kraft_real_le_one (F : Finset BitString)
    (hF : IsPrefixFree (F : Set BitString)) :
    ∑ w ∈ F, ((1 : ℝ) / 2) ^ w.length ≤ 1 := by
  rcases F.eq_empty_or_nonempty with rfl | hFne
  · simp
  · set L := F.sup (fun w => w.length) with hL
    have hwL : ∀ w ∈ F, w.length ≤ L := fun w hw => Finset.le_sup hw
    -- The leaf sets are pairwise disjoint and live inside the `2^L` strings of length `L`.
    have hcard_bu : (F.biUnion (fun w => kraftLeaves w L)).card
        = ∑ w ∈ F, (kraftLeaves w L).card := by
      apply Finset.card_biUnion
      intro w1 h1 w2 h2 hne12
      exact kraftLeaves_disjoint hF (Finset.mem_coe.mpr h1) (Finset.mem_coe.mpr h2) hne12
    have hbu_sub : (F.biUnion (fun w => kraftLeaves w L)) ⊆ stringsOfLength L := by
      intro u hu
      rw [Finset.mem_biUnion] at hu
      obtain ⟨w, _, hw⟩ := hu
      exact kraftLeaves_subset w L hw
    have hsum_card : ∑ w ∈ F, (kraftLeaves w L).card = ∑ w ∈ F, 2 ^ (L - w.length) :=
      Finset.sum_congr rfl (fun w hw => kraftLeaves_card (hwL w hw))
    have hnat : ∑ w ∈ F, 2 ^ (L - w.length) ≤ 2 ^ L := by
      rw [← hsum_card, ← hcard_bu]
      calc (F.biUnion (fun w => kraftLeaves w L)).card
            ≤ (stringsOfLength L).card := Finset.card_le_card hbu_sub
        _ = 2 ^ L := cardStringsOfLength L
    -- Transport the natural-number bound to the real Kraft sum, scaled by `2^L`.
    have h2L_pos : (0 : ℝ) < 2 ^ L := by positivity
    have key : ∀ w ∈ F, ((1 : ℝ) / 2) ^ w.length * 2 ^ L = (2 ^ (L - w.length) : ℝ) := by
      intro w hw
      rw [div_pow, one_pow, pow_sub₀ (2 : ℝ) (by norm_num) (hwL w hw)]
      field_simp
    have hsum_real : (∑ w ∈ F, ((1 : ℝ) / 2) ^ w.length) * 2 ^ L
        = ∑ w ∈ F, (2 ^ (L - w.length) : ℝ) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl key
    have hreal : (∑ w ∈ F, ((1 : ℝ) / 2) ^ w.length) * 2 ^ L ≤ 2 ^ L := by
      rw [hsum_real]
      calc ∑ w ∈ F, (2 ^ (L - w.length) : ℝ)
            = ((∑ w ∈ F, 2 ^ (L - w.length) : ℕ) : ℝ) := by push_cast; ring
        _ ≤ ((2 ^ L : ℕ) : ℝ) := by exact_mod_cast hnat
        _ = (2 : ℝ) ^ L := by push_cast; ring
    nlinarith [hreal, h2L_pos]

/-- The repository weight `progWeight w = (2⁻¹)^{|w|}` is the `ℝ≥0∞`-coercion of the
real weight `(1/2)^{|w|}`. This is the only bridge needed to transport the real Kraft
sum into `ℝ≥0∞`. -/
theorem progWeight_eq_ofReal (w : BitString) :
    progWeight w = ENNReal.ofReal (((1 : ℝ) / 2) ^ w.length) := by
  rw [progWeight, programLength, ENNReal.ofReal_pow (by norm_num)]
  congr 1
  rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]

/-- **Finite Kraft inequality (`ℝ≥0∞` form).** The total `progWeight` of a prefix-free
finite set of bitstrings is at most `1`. This is the finite precursor of the bound
`domainWeight M y ≤ 1` that the normalization reduction
(`tsum_aprioriMeasure_le_one_of_domainWeight_le_one`) is waiting on; lifting from this
finite sum to the countable `tsum` is the subject of a later slot. -/
theorem finset_kraft_progWeight_le_one (F : Finset BitString)
    (hF : IsPrefixFree (F : Set BitString)) :
    ∑ w ∈ F, progWeight w ≤ 1 := by
  have hsum_nonneg : (0 : ℝ) ≤ ∑ w ∈ F, ((1 : ℝ) / 2) ^ w.length :=
    Finset.sum_nonneg fun w _ => by positivity
  calc
    ∑ w ∈ F, progWeight w
        = ∑ w ∈ F, ENNReal.ofReal (((1 : ℝ) / 2) ^ w.length) := by
          exact Finset.sum_congr rfl fun w _ => progWeight_eq_ofReal w
    _ = ENNReal.ofReal (∑ w ∈ F, ((1 : ℝ) / 2) ^ w.length) :=
          (ENNReal.ofReal_sum_of_nonneg fun w _ => by positivity).symm
    _ ≤ ENNReal.ofReal 1 :=
          ENNReal.ofReal_le_ofReal (finset_kraft_real_le_one F hF)
    _ = 1 := ENNReal.ofReal_one

end Kolmogorov
