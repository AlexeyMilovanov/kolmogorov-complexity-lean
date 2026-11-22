/-
Copyright (c) 2026 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Relativization.Definitions
import KolmogorovMathlib.Relativization.Typization
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.ModelsToSets2
import KolmogorovMathlib.CommonInformation.PlainSymmetry
import KolmogorovMathlib.CommonInformation.OverlapExtraction
import KolmogorovMathlib.CommonInformation.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Nonstochastic Pairs

This module formalizes the construction of nonstochastic pairs and the relativized stability theorem
in Section 5 of Muchnik and Romashchenko, “Stability of properties of Kolmogorov complexity under
relativization.” Its main result constructs a finite graph with bounded degrees and many edges that
avoid every prescribed family of small nearness relations.
-/

namespace Kolmogorov.Relativization

/-- A *nearness relation* on the finite set `S` with degree bound `2 ^ s` (Section 5 of the
paper): every `x ∈ S` is related to at most `2 ^ s` strings, and every string is related to at
most `2 ^ s` elements of `S`.  ("At most `2 ^ s`" is phrased through finite subsets, so that no
finiteness assumption on `N` is needed.) -/
private def theorem6_IsNearness (S : Finset BitString) (s : ℕ)
    (N : BitString → BitString → Prop) : Prop :=
  (∀ x ∈ S, ∀ F : Finset BitString, (∀ y ∈ F, N x y) → F.card ≤ 2 ^ s) ∧
    ∀ y : BitString, ∀ F : Finset BitString, F ⊆ S → (∀ x ∈ F, N x y) → F.card ≤ 2 ^ s

open scoped Classical in
/-- The property (3) of the graph `A` in Section 5 of the paper, in the cleaned-up form used
here (only the suitable edges are kept): `A ⊆ S₁ × S₂` where `S₁, S₂` are the strings of
lengths `a, b`; `|A| ≤ 2 ^ g`; every left vertex has degree `≤ 2 ^ (g - a)` and every right
vertex degree `≤ 2 ^ (g - b)`; and for every pair of nearness relations `N₁, N₂` (degree bound
`2 ^ s`) at least `2 ^ (g - 3 s)` edges of `A` are not `(N₁, N₂)`-close to a pair whose pair
code lies in `R`. -/
private def theorem6_GoodGraph (a b g s : ℕ) (R : Finset BitString)
    (A : Finset (BitString × BitString)) : Prop :=
  A ⊆ stringsOfLength a ×ˢ stringsOfLength b ∧ A.card ≤ 2 ^ g ∧
    (∀ x : BitString, (A.filter fun e => e.1 = x).card ≤ 2 ^ (g - a)) ∧
    (∀ y : BitString, (A.filter fun e => e.2 = y).card ≤ 2 ^ (g - b)) ∧
    ∀ N₁ N₂ : BitString → BitString → Prop,
      theorem6_IsNearness (stringsOfLength a) s N₁ →
      theorem6_IsNearness (stringsOfLength b) s N₂ →
      2 ^ (g - 3 * s) ≤ (A.filter fun e =>
        ¬ ∃ y₁ y₂ : BitString, pairCode y₁ y₂ ∈ R ∧ N₁ e.1 y₁ ∧ N₂ e.2 y₂).card

/-- The code of a finite set of pairs of strings: the ordered list of their pair codes. -/
private def theorem6_graphCode (A : Finset (BitString × BitString)) : BitString :=
  finsetListCode (A.image fun e => pairCode e.1 e.2)

/-- choice of the integer parameters.  With
`a ≈ αn`, `b ≈ βn`, `g ≈ γn` (within `1`) and the logarithmic slack `s = logSlack K n`, the
strict inequalities `α, β < γ < α + β` give, for all large `n`, the margins
`a + 5s ≤ g`, `b + 5s ≤ g`, `g + 5s ≤ a + b`, and also `g + s + 1 ≤ 2 ^ s` (as `K ≥ 10`) and
`s ≤ n`; all three parameters are bounded linearly in `n` with a constant `B` independent of
`K`. -/
private theorem theorem6_rounding (α β γ : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hαβ : γ < α + β) (hαγ : α < γ) (hβγ : β < γ) :
    ∃ B : ℕ, 1 ≤ B ∧ ∀ K : ℕ, 10 ≤ K → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∃ a b g : ℕ,
      |(a : ℝ) - α * n| ≤ 1 ∧ |(b : ℝ) - β * n| ≤ 1 ∧ |(g : ℝ) - γ * n| ≤ 1 ∧
      a + 5 * logSlack K n ≤ g ∧ b + 5 * logSlack K n ≤ g ∧
      g + 5 * logSlack K n ≤ a + b ∧
      g + logSlack K n + 1 ≤ 2 ^ logSlack K n ∧ logSlack K n ≤ n ∧
      a ≤ B * (n + 1) ∧ b ≤ B * (n + 1) ∧ g ≤ B * (n + 1) := by
  have hγ : 0 < γ := lt_trans hα hαγ
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = min (γ - α) (min (γ - β) (α + β - γ)) := ⟨_, rfl⟩
  have hεpos : 0 < ε := by
    rw [hεdef, lt_min_iff, lt_min_iff]
    refine ⟨by linarith, by linarith, by linarith⟩
  have hε1 : ε ≤ γ - α := by rw [hεdef]; exact min_le_left _ _
  have hε2 : ε ≤ γ - β := by
    rw [hεdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hε3 : ε ≤ α + β - γ := by
    rw [hεdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  obtain ⟨m, hm⟩ : ∃ m : ℕ, 1 / ε < m := exists_nat_gt (1 / ε)
  have hmpos : (0 : ℝ) < m := lt_trans (by positivity) hm
  have hm1 : 1 ≤ m := by
    have : (0 : ℕ) < m := by exact_mod_cast hmpos
    omega
  have hmε : 1 ≤ ε * m := by
    have h := (div_lt_iff₀ hεpos).1 hm
    linarith [mul_comm (m : ℝ) ε]
  refine ⟨⌊α⌋₊ + ⌊β⌋₊ + ⌊γ⌋₊ + 1, by omega, fun K hK => ?_⟩
  obtain ⟨M, hM⟩ := exists_bits_linear_domination m (5 * K) (5 * K + 2)
  refine ⟨max M (⌊α⌋₊ + ⌊β⌋₊ + ⌊γ⌋₊ + 1), fun n hn => ?_⟩
  have hMn : M ≤ n := le_trans (le_max_left _ _) hn
  have hBn : ⌊α⌋₊ + ⌊β⌋₊ + ⌊γ⌋₊ + 1 ≤ n := le_trans (le_max_right _ _) hn
  obtain ⟨L, hL⟩ : ∃ L : ℕ, L = (Nat.bits n).length := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s : ℕ, s = logSlack K n := ⟨_, rfl⟩
  rw [← hs]
  have hsdef : s = K * L + K := by rw [hs, hL]; rfl
  have hdom : m * (5 * s + 2) ≤ n := by
    have h := hM n hMn
    have heq : 5 * s + 2 = 5 * K * (Nat.bits n).length + (5 * K + 2) := by
      rw [hsdef, hL]; ring
    rw [heq]
    exact h
  have hsn : 5 * s + 2 ≤ n := by
    calc 5 * s + 2 = 1 * (5 * s + 2) := by ring
      _ ≤ m * (5 * s + 2) := Nat.mul_le_mul_right _ hm1
      _ ≤ n := hdom
  have hdomR : (m : ℝ) * (5 * s + 2) ≤ n := by exact_mod_cast hdom
  have hkey : (5 * (s : ℝ) + 2) ≤ ε * n := by
    have h0 : (0 : ℝ) ≤ 5 * (s : ℝ) + 2 := by positivity
    calc (5 * (s : ℝ) + 2) = 1 * (5 * (s : ℝ) + 2) := by ring
      _ ≤ (ε * m) * (5 * (s : ℝ) + 2) := mul_le_mul_of_nonneg_right hmε h0
      _ = ε * (m * (5 * (s : ℝ) + 2)) := by ring
      _ ≤ ε * n := mul_le_mul_of_nonneg_left hdomR hεpos.le
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hk1 : ε * n ≤ (γ - α) * n := mul_le_mul_of_nonneg_right hε1 hn0
  have hk2 : ε * n ≤ (γ - β) * n := mul_le_mul_of_nonneg_right hε2 hn0
  have hk3 : ε * n ≤ (α + β - γ) * n := mul_le_mul_of_nonneg_right hε3 hn0
  have hαn : 0 ≤ α * n := mul_nonneg hα.le hn0
  have hβn : 0 ≤ β * n := mul_nonneg hβ.le hn0
  have hγn : 0 ≤ γ * n := mul_nonneg hγ.le hn0
  have ha1 : ((⌊α * n⌋₊ : ℕ) : ℝ) ≤ α * n := Nat.floor_le hαn
  have ha2 : α * n < ((⌊α * n⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  have hb1 : ((⌊β * n⌋₊ : ℕ) : ℝ) ≤ β * n := Nat.floor_le hβn
  have hb2 : β * n < ((⌊β * n⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  have hg1 : ((⌊γ * n⌋₊ : ℕ) : ℝ) ≤ γ * n := Nat.floor_le hγn
  have hg2 : γ * n < ((⌊γ * n⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  -- linear bounds
  have hlinear : ∀ δ : ℝ, 0 < δ → ⌊δ * n⌋₊ ≤ (⌊δ⌋₊ + 1) * n := by
    intro δ hδ
    have h1 : ((⌊δ * n⌋₊ : ℕ) : ℝ) ≤ δ * n := Nat.floor_le (mul_nonneg hδ.le hn0)
    have h2 : δ ≤ (⌊δ⌋₊ : ℝ) + 1 := (Nat.lt_floor_add_one δ).le
    have h3 : δ * n ≤ ((⌊δ⌋₊ : ℝ) + 1) * n := mul_le_mul_of_nonneg_right h2 hn0
    have h4 : ((⌊δ * n⌋₊ : ℕ) : ℝ) ≤ (((⌊δ⌋₊ + 1) * n : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast h4
  have haB : ⌊α * n⌋₊ ≤ (⌊α⌋₊ + ⌊β⌋₊ + ⌊γ⌋₊ + 1) * (n + 1) :=
    (hlinear α hα).trans (Nat.mul_le_mul (by omega) (by omega))
  have hbB : ⌊β * n⌋₊ ≤ (⌊α⌋₊ + ⌊β⌋₊ + ⌊γ⌋₊ + 1) * (n + 1) :=
    (hlinear β hβ).trans (Nat.mul_le_mul (by omega) (by omega))
  have hgB : ⌊γ * n⌋₊ ≤ (⌊α⌋₊ + ⌊β⌋₊ + ⌊γ⌋₊ + 1) * (n + 1) :=
    (hlinear γ hγ).trans (Nat.mul_le_mul (by omega) (by omega))
  refine ⟨⌊α * n⌋₊, ⌊β * n⌋₊, ⌊γ * n⌋₊, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by omega, haB, hbB, hgB⟩
  · rw [abs_le]; constructor <;> linarith
  · rw [abs_le]; constructor <;> linarith
  · rw [abs_le]; constructor <;> linarith
  · have h : ((⌊α * n⌋₊ + 5 * s : ℕ) : ℝ) < ((⌊γ * n⌋₊ : ℕ) : ℝ) := by
      push_cast
      linarith
    exact (Nat.cast_lt.1 h).le
  · have h : ((⌊β * n⌋₊ + 5 * s : ℕ) : ℝ) < ((⌊γ * n⌋₊ : ℕ) : ℝ) := by
      push_cast
      linarith
    exact (Nat.cast_lt.1 h).le
  · have h : ((⌊γ * n⌋₊ + 5 * s : ℕ) : ℝ) < ((⌊α * n⌋₊ + ⌊β * n⌋₊ : ℕ) : ℝ) := by
      push_cast
      linarith
    exact (Nat.cast_lt.1 h).le
  · -- `g + s + 1 ≤ (n + 1) ^ 2 ≤ 2 ^ (2 L) ≤ 2 ^ s`
    have hgn : ⌊γ * n⌋₊ ≤ n * (n + 1) :=
      hgB.trans (Nat.mul_le_mul_right _ (by omega))
    have hsize : n < 2 ^ L := by
      rw [hL, Nat.size_eq_bits_len]
      exact Nat.lt_size_self n
    have hsq : (n + 1) * (n + 1) ≤ 2 ^ (2 * L) := by
      have h1 : n + 1 ≤ 2 ^ L := hsize
      calc (n + 1) * (n + 1) ≤ 2 ^ L * 2 ^ L := Nat.mul_le_mul h1 h1
        _ = 2 ^ (2 * L) := by rw [← pow_add]; ring_nf
    have h2L : 2 * L ≤ s := by
      rw [hsdef]
      have : 2 * L ≤ K * L := Nat.mul_le_mul_right _ (by omega)
      omega
    have hpow : 2 ^ (2 * L) ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) h2L
    have hnn : n * (n + 1) + n + 1 = (n + 1) * (n + 1) := by ring
    omega

/-- a string `y` that is `C`-equivalent to a
string `x` of complexity `O(n)` is simple given `x` and conversely: both conditional
complexities are `O(log n)`.  (Bootstrapping: `K(x, y) ≤ K(x) + K(y | x) + O(log K(x, y))`
and `K(y | x) ≤ C log K(x, y) + C` force `K(x, y) = O(n)`, and then both conditional
complexities are at most `logSlack C (O(n))`.) -/
private theorem theorem6_equiv_conditional (D : Map) (hD : isOptimalConditional D)
    (C B : ℕ) :
    ∃ c : ℕ, ∀ n : ℕ, ∀ x y : BitString, natK D x ≤ B * (n + 1) → EquivWithin D C x y →
      natCondK D y x ≤ logSlack c n ∧ natCondK D x y ≤ logSlack c n := by
  obtain ⟨cChain, hChain⟩ := pairPlainK_chain_upper_values D hD
  obtain ⟨cC, hcC⟩ := condK_le_plainK D hD
  obtain ⟨b', hb'⟩ := logSlack_le_add_const (2 * (C + cChain))
  obtain ⟨cF, hF⟩ := logSlack_linear_bound C (2 * B) (2 * B + 1 + b')
  refine ⟨cF, fun n x y hx hE => ?_⟩
  have hPlainVal : ∀ w : BitString, HasPlainComplexityValue D w (natK D w) := fun w => by
    change plainK D w = ((plainK D w).toNat : ENat)
    exact (ENat.natCast_toNat (Kolmogorov.plainK_ne_top D hD w)).symm
  have hCondVal : ∀ u w : BitString,
      HasPlainConditionalComplexityValue D u w (natCondK D u w) := fun u w => by
    change condK D u w = ((condK D u w).toNat : ENat)
    refine (ENat.natCast_toNat ?_).symm
    intro h
    have h1 := hcC u w
    rw [h, top_le_iff] at h1
    exact Kolmogorov.plainK_ne_top D hD u (by
      rcases (WithTop.add_eq_top).mp h1 with h2 | h2
      · exact h2
      · exact absurd h2 (ENat.natCast_ne_top cC))
  obtain ⟨hxy, hyx⟩ := hE
  have hch := hChain x y (natK D x) (natCondK D y x) (natK D (pairCode x y))
    (hPlainVal x) (hCondVal y x) (hPlainVal _)
  have hmono : logSlack C (natK D (pairCode x y)) ≤ logSlack C (natK D (pairCode x y) + 1) :=
    logSlack_mono_right C (Nat.le_succ _)
  have hsum : logSlack C (natK D (pairCode x y) + 1) +
      logSlack cChain (natK D (pairCode x y) + 1) =
      logSlack (C + cChain) (natK D (pairCode x y) + 1) :=
    (logSlack_add_constants C cChain _).symm
  have hdouble : logSlack (2 * (C + cChain)) (natK D (pairCode x y) + 1) =
      2 * logSlack (C + cChain) (natK D (pairCode x y) + 1) := by
    unfold logSlack
    ring
  have hb := hb' (natK D (pairCode x y) + 1)
  have hBn : B * (n + 1) = B * n + B := by ring
  have h2B : 2 * B * n = 2 * (B * n) := by ring
  have hMbound : natK D (pairCode x y) ≤ 2 * B * n + (2 * B + 1 + b') := by
    omega
  have hfin : logSlack C (natK D (pairCode x y)) ≤ logSlack cF n :=
    (logSlack_mono_right C hMbound).trans (hF n)
  exact ⟨hyx.trans hfin, hxy.trans hfin⟩

/-- fewer than `2 ^ (T + 1)` strings have
conditional complexity at most `T` given a fixed condition `z` (count of programs). -/
private theorem theorem6_count_conditional (D : Map) (hD : isOptimalConditional D)
    (z : BitString) (T : ℕ) (F : Finset BitString) (hF : ∀ y ∈ F, natCondK D y z ≤ T) :
    F.card < 2 ^ (T + 1) := by
  classical
  have hsub : F ⊆ Kolmogorov.compressibleWords D z T := by
    intro y hy
    have hk := hF y hy
    obtain ⟨cC, hcC⟩ := condK_le_plainK D hD
    have htop : condK D y z ≠ ⊤ := by
      intro h
      have h1 := hcC y z
      rw [h, top_le_iff] at h1
      exact Kolmogorov.plainK_ne_top D hD y (by
        rcases (WithTop.add_eq_top).mp h1 with h2 | h2
        · exact h2
        · exact absurd h2 (ENat.natCast_ne_top cC))
    have hcond : condK D y z ≤ (T : ENat) := by
      rw [← ENat.natCast_toNat htop]
      exact_mod_cast hk
    rw [Kolmogorov.compressibleWords, Finset.mem_filter]
    refine ⟨?_, hcond⟩
    obtain ⟨p, hpLen, hpProd⟩ := (Kolmogorov.condK_le_iff D y z T).mp hcond
    rw [Kolmogorov.generatedWords, List.mem_toFinset, List.mem_filterMap]
    exact ⟨p, Kolmogorov.mem_programsLe T p hpLen,
      Kolmogorov.progToOut_eq_some.mpr hpProd⟩
  exact lt_of_le_of_lt (Finset.card_le_card hsub)
    (Kolmogorov.card_compressibleWordsLt D z T)

/-- if `x₁ ∼_C x₁'` and `x₂ ∼_C x₂'`, where
`x₁, x₂` and the pair `⟨x₁, x₂⟩` have complexity `O(n)`, then
`K(x₁', x₂') ≤ K(x₁, x₂) + O(log n)` (the paper's estimate
`K(x₁', x₂') ≤ K(x₁, x₂) + K(x₁' | x₁) + K(x₂' | x₂) + O(log …)`, with both conditional
complexities `O(log n)` as established by the conditional-complexity bound). -/
private theorem theorem6_equiv_pair (D : Map) (hD : isOptimalConditional D) (C B : ℕ) :
    ∃ c : ℕ, ∀ n : ℕ, ∀ x₁ x₂ x₁' x₂' : BitString,
      natK D x₁ ≤ B * (n + 1) → natK D x₂ ≤ B * (n + 1) →
      natK D (pairCode x₁ x₂) ≤ B * (n + 1) →
      EquivWithin D C x₁ x₁' → EquivWithin D C x₂ x₂' →
      natK D (pairCode x₁' x₂') ≤ natK D (pairCode x₁ x₂) + logSlack c n := by
  obtain ⟨c₂, h₂⟩ := theorem6_equiv_conditional D hD C B
  obtain ⟨cL, hL⟩ := Kolmogorov.condK_condPair_left_le D hD
  obtain ⟨cR, hR⟩ := Kolmogorov.condK_condPair_right_le D hD
  obtain ⟨cPair, hPair⟩ := Kolmogorov.condK_pair_le_add D hD
  obtain ⟨cChain, hChain⟩ := pairPlainK_chain_upper_values D hD
  obtain ⟨cProj, hProj⟩ := pairPlainK_right_le D hD
  obtain ⟨cC, hcC⟩ := condK_le_plainK D hD
  obtain ⟨b', hb'⟩ := logSlack_le_add_const (2 * cChain)
  obtain ⟨cF1, hF1⟩ := logSlack_linear_bound cPair (2 * c₂) (2 * c₂ + cL + cR + 1)
  obtain ⟨cF2, hF2⟩ := logSlack_linear_bound cChain (2 * B + 4 * c₂ + 2 * cF1)
    (2 * B + 4 * c₂ + 2 * cF1 + 2 * cL + 2 * cR + 2 + b')
  have hlin : ∀ c m : ℕ, logSlack c m ≤ c * (m + 1) := fun c m => by
    rw [mul_add_one]
    exact logSlack_le_self_linear c m
  have hge : ∀ c m : ℕ, c ≤ logSlack c m := fun c m => by
    unfold logSlack
    exact Nat.le_add_left _ _
  have hPV : ∀ w : BitString, plainK D w = (natK D w : ENat) := fun w =>
    (ENat.natCast_toNat (Kolmogorov.plainK_ne_top D hD w)).symm
  have hCV : ∀ u w : BitString, condK D u w = (natCondK D u w : ENat) := fun u w => by
    refine (ENat.natCast_toNat ?_).symm
    intro h
    have h1 := hcC u w
    rw [h, top_le_iff] at h1
    exact Kolmogorov.plainK_ne_top D hD u (by
      rcases (WithTop.add_eq_top).mp h1 with h2 | h2
      · exact h2
      · exact absurd h2 (ENat.natCast_ne_top cC))
  refine ⟨2 * c₂ + cL + cR + cF1 + cF2 + cProj,
    fun n x₁ x₂ x₁' x₂' hx₁ hx₂ hx₁₂ hE₁ hE₂ => ?_⟩
  have hk₁ := (h₂ n x₁ x₁' hx₁ hE₁).1
  have hk₂ := (h₂ n x₂ x₂' hx₂ hE₂).1
  have hL' : natCondK D x₁' (pairCode x₁ x₂) ≤ natCondK D x₁' x₁ + cL := by
    have h := hL x₁' x₁ x₂
    rw [hCV, hCV] at h
    exact_mod_cast h
  have hR' : natCondK D x₂' (pairCode x₁ x₂) ≤ natCondK D x₂' x₂ + cR := by
    have h := hR x₂' x₁ x₂
    rw [hCV, hCV] at h
    exact_mod_cast h
  have hVU : natCondK D (pairCode x₁' x₂') (pairCode x₁ x₂) ≤
      natCondK D x₁' (pairCode x₁ x₂) + natCondK D x₂' (pairCode x₁ x₂) +
        logSlack cPair (natCondK D x₁' (pairCode x₁ x₂) +
          natCondK D x₂' (pairCode x₁ x₂) + 1) := by
    have h := hPair x₁' x₂' (pairCode x₁ x₂) _ _ (hCV _ _) (hCV _ _)
    rw [hCV] at h
    exact_mod_cast h
  have hl₂ := hlin c₂ n
  have hlF1 := hlin cF1 n
  have hF1' : logSlack cPair (natCondK D x₁' (pairCode x₁ x₂) +
      natCondK D x₂' (pairCode x₁ x₂) + 1) ≤ logSlack cF1 n := by
    apply logSlack_le_of_linear_bound hF1
    have e1 : 2 * c₂ * n = 2 * (c₂ * n) := by ring
    have e2 : c₂ * (n + 1) = c₂ * n + c₂ := by ring
    omega
  have hch := hChain (pairCode x₁ x₂) (pairCode x₁' x₂') (natK D (pairCode x₁ x₂))
    (natCondK D (pairCode x₁' x₂') (pairCode x₁ x₂))
    (natK D (pairCode (pairCode x₁ x₂) (pairCode x₁' x₂'))) (hPV _) (hCV _ _) (hPV _)
  have hdouble : logSlack (2 * cChain)
      (natK D (pairCode (pairCode x₁ x₂) (pairCode x₁' x₂')) + 1) =
      2 * logSlack cChain (natK D (pairCode (pairCode x₁ x₂) (pairCode x₁' x₂')) + 1) := by
    unfold logSlack
    ring
  have hb := hb' (natK D (pairCode (pairCode x₁ x₂) (pairCode x₁' x₂')) + 1)
  have hMb : natK D (pairCode (pairCode x₁ x₂) (pairCode x₁' x₂')) + 1 ≤
      (2 * B + 4 * c₂ + 2 * cF1) * n +
        (2 * B + 4 * c₂ + 2 * cF1 + 2 * cL + 2 * cR + 2 + b') := by
    have e : (2 * B + 4 * c₂ + 2 * cF1) * n = 2 * (B * n) + 4 * (c₂ * n) + 2 * (cF1 * n) := by
      ring
    have e2 : B * (n + 1) = B * n + B := by ring
    have e3 : c₂ * (n + 1) = c₂ * n + c₂ := by ring
    have e4 : cF1 * (n + 1) = cF1 * n + cF1 := by ring
    omega
  have hF2' := logSlack_le_of_linear_bound hF2 hMb
  have hproj : natK D (pairCode x₁' x₂') ≤
      natK D (pairCode (pairCode x₁ x₂) (pairCode x₁' x₂')) + cProj := by
    have h := hProj (pairCode x₁ x₂) (pairCode x₁' x₂')
    simp only [pairPlainK] at h
    rw [hPV, hPV] at h
    exact_mod_cast h
  have hsplit : logSlack (2 * c₂ + cL + cR + cF1 + cF2 + cProj) n =
      2 * logSlack c₂ n + logSlack cL n + logSlack cR n + logSlack cF1 n +
        logSlack cF2 n + logSlack cProj n := by
    unfold logSlack
    ring
  have h1 := hge cL n
  have h2 := hge cR n
  have h3 := hge cProj n
  omega

/-- The union of the decoded lists coded in `S` whose lengths are at most `2 ^ u`. -/
private def theorem6_aux_union (S : List BitString) (u : ℕ) : List BitString :=
  (S.filter (fun w => decide ((decodeListCode w).length ≤ 2 ^ u))).flatMap decodeListCode

/-- The union of the decoded short lists is primitive recursive. -/
private theorem theorem6_aux_union_primrec :
    Primrec (fun p : List BitString × ℕ => theorem6_aux_union p.1 p.2) := by
  unfold theorem6_aux_union
  have hpow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) := Primrec₂.unpaired'.1 Nat.Primrec.pow
  have htest : Primrec (fun q : (List BitString × ℕ) × BitString =>
      decide ((decodeListCode q.2).length ≤ 2 ^ q.1.2)) :=
    PrimrecPred.decide (PrimrecRel.comp Primrec.nat_le
      (Primrec.list_length.comp (decodeListCode_primrec.comp Primrec.snd))
      (hpow.comp (Primrec.const 2) (Primrec.snd.comp Primrec.fst)))
  have hfilt : Primrec (fun p : List BitString × ℕ =>
      p.1.filter (fun w => decide ((decodeListCode w).length ≤ 2 ^ p.2))) :=
    Primrec.list_filter Primrec.fst htest.to₂
  exact Primrec.list_flatMap hfilt (decodeListCode_primrec.comp Primrec.snd).to₂

/-- If each list in a flattened family has length at most `K`, the resulting list has length
at most `K` times the number of lists. -/
private theorem theorem6_aux_length_flatMap (l : List BitString)
    (f : BitString → List BitString) (K : ℕ) (h : ∀ x ∈ l, (f x).length ≤ K) :
    (l.flatMap f).length ≤ l.length * K := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.flatMap_cons, List.length_append, List.length_cons]
    have ha := h a (by simp)
    have hl := ih (fun x hx => h x (by simp [hx]))
    calc (f a).length + (l.flatMap f).length ≤ K + l.length * K := Nat.add_le_add ha hl
      _ = (l.length + 1) * K := by ring

/-- The partial procedure that waits for `N` outputs of complexity at most `m` and returns
the code of the union of their decoded lists of length at most `2 ^ u`. -/
private noncomputable def theorem6_aux_F (cD : Nat.Partrec.Code) (z : BitString) :
    Part BitString :=
  (Nat.rfind (fun s => Part.some
      ((boundedOutputStage cD (Nat.unpair (decodeBits z)).1 s).length ==
        (Nat.unpair (Nat.unpair (decodeBits z)).2).2))).map
    (fun s => listCode (canonicalFinsetList (theorem6_aux_union
      (boundedOutputStage cD (Nat.unpair (decodeBits z)).1 s)
      (Nat.unpair (Nat.unpair (decodeBits z)).2).1).toFinset))

/-- The procedure returning the union code is partial recursive. -/
private theorem theorem6_aux_F_partrec (cD : Nat.Partrec.Code) :
    Partrec (theorem6_aux_F cD) := by
  have hd : Computable (fun z : BitString => decodeBits z) := decodeBits_computable
  have hun : Computable Nat.unpair := Primrec.unpair.to_comp
  have hm : Computable (fun z : BitString => (Nat.unpair (decodeBits z)).1) :=
    Computable.fst.comp (hun.comp hd)
  have hu : Computable (fun z : BitString => (Nat.unpair (Nat.unpair (decodeBits z)).2).1) :=
    Computable.fst.comp (hun.comp (Computable.snd.comp (hun.comp hd)))
  have hcnt : Computable (fun z : BitString => (Nat.unpair (Nat.unpair (decodeBits z)).2).2) :=
    Computable.snd.comp (hun.comp (Computable.snd.comp (hun.comp hd)))
  have hstage : Computable (fun p : BitString × ℕ =>
      boundedOutputStage cD (Nat.unpair (decodeBits p.1)).1 p.2) :=
    (boundedOutputStage_primrec cD).to_comp.comp
      (Computable.pair (hm.comp Computable.fst) Computable.snd)
  have hcheck : Computable₂ (fun (z : BitString) (s : ℕ) =>
      (boundedOutputStage cD (Nat.unpair (decodeBits z)).1 s).length ==
        (Nat.unpair (Nat.unpair (decodeBits z)).2).2) :=
    (Primrec.beq.to_comp.comp (Computable.list_length.comp hstage)
      (hcnt.comp Computable.fst)).to₂
  have hsearch := Partrec.rfind hcheck.partrec₂
  have hout : Computable₂ (fun (z : BitString) (s : ℕ) =>
      listCode (canonicalFinsetList (theorem6_aux_union
        (boundedOutputStage cD (Nat.unpair (decodeBits z)).1 s)
        (Nat.unpair (Nat.unpair (decodeBits z)).2).1).toFinset)) :=
    (listCode_computable.comp (canonicalFinsetList_toFinset_primrec.to_comp.comp
      (theorem6_aux_union_primrec.to_comp.comp
        (Computable.pair hstage (hu.comp Computable.fst))))).to₂
  exact hsearch.map hout

/-- the set `R̂` of Section 5.  Let `R̂` be the
union of all finite sets `R` with `K(list R) ≤ C log n` (that is, `logSlack C n`) and
`|R| ≤ 2 ^ (g + t + O(1))`.  Every `(C log n, C log n)`-stochastic string `w` with
`K(w) + C log n ≤ g + t` lies in `R̂` (its witness set is one of these `R`, because
`K(w | list R) ≤ K(w) + O(1)`); there are at most `2 ^ (C log n + 1)` such sets, so
`|R̂| ≤ 2 ^ (g + t + O(log n))`; and `R̂` is computed from `n, g, t` and the number of such sets,
so `K(list R̂) = O(log n)` when `g, t = O(n)`. -/
private theorem theorem6_stochastic_union (D : Map) (hD : isOptimalConditional D)
    (C B : ℕ) :
    ∃ c : ℕ, ∀ n g t : ℕ, g ≤ B * (n + 1) → t ≤ n →
      ∃ R : Finset BitString, R.card ≤ 2 ^ (g + t + logSlack c n) ∧
        natK D (finsetListCode R) ≤ logSlack c n ∧
        ∀ w : BitString, IsSetStochastic D w (logSlack C n) (logSlack C n) →
          natK D w + logSlack C n ≤ g + t → w ∈ R := by
  obtain ⟨cD, hcD⟩ : ∃ c : Nat.Partrec.Code, IsCodeFor c D :=
    Nat.Partrec.Code.exists_code.mp hD.1
  obtain ⟨c₀, hc₀⟩ := condK_le_plainK D hD
  obtain ⟨cF, hF⟩ := Kolmogorov.plainK_partrec_map_le D hD _ (theorem6_aux_F_partrec cD)
  obtain ⟨cLit, hLit⟩ := plainK_le_length D hD
  obtain ⟨cA, hA⟩ := logSlack_absorb_of_le_linear 1 (B + 1) (B + c₀)
  refine ⟨4 * C + 4 * cA + 10 + cLit + cF + C + c₀ + 1, fun n g t hg ht => ?_⟩
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = logSlack C n := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : ℕ, u = g + t + c₀ := ⟨_, rfl⟩
  have hsplit : logSlack (4 * C + 4 * cA + 10 + cLit + cF + C + c₀ + 1) n =
      4 * logSlack C n + 4 * logSlack cA n + logSlack C n +
        logSlack (10 + cLit + cF + c₀ + 1) n := by
    unfold logSlack
    ring
  have hconst : 10 + cLit + cF + c₀ + 1 ≤ logSlack (10 + cLit + cF + c₀ + 1) n := by
    unfold logSlack
    exact Nat.le_add_left _ _
  refine ⟨(theorem6_aux_union (completedBoundedOutput cD m) u).toFinset, ?_, ?_, ?_⟩
  · -- the size of `R̂`
    have h1 : (theorem6_aux_union (completedBoundedOutput cD m) u).toFinset.card ≤
        (theorem6_aux_union (completedBoundedOutput cD m) u).length :=
      List.toFinset_card_le _
    have h2 : (theorem6_aux_union (completedBoundedOutput cD m) u).length ≤
        ((completedBoundedOutput cD m).filter
          (fun w => decide ((decodeListCode w).length ≤ 2 ^ u))).length * 2 ^ u := by
      apply theorem6_aux_length_flatMap
      intro x hx
      have := (List.mem_filter.1 hx).2
      simpa using this
    have h3 : ((completedBoundedOutput cD m).filter
          (fun w => decide ((decodeListCode w).length ≤ 2 ^ u))).length ≤
        (completedBoundedOutput cD m).length := List.length_filter_le _ _
    have h4 : (completedBoundedOutput cD m).length < 2 ^ (m + 1) :=
      Kolmogorov.omegaCount_lt_two_pow_succ cD m
    have h5 : u + (m + 1) ≤
        g + t + logSlack (4 * C + 4 * cA + 10 + cLit + cF + C + c₀ + 1) n := by
      omega
    calc (theorem6_aux_union (completedBoundedOutput cD m) u).toFinset.card
        ≤ ((completedBoundedOutput cD m).filter
          (fun w => decide ((decodeListCode w).length ≤ 2 ^ u))).length * 2 ^ u := h1.trans h2
      _ ≤ 2 ^ (m + 1) * 2 ^ u := Nat.mul_le_mul_right _ (h3.trans h4.le)
      _ = 2 ^ (u + (m + 1)) := by rw [pow_add]; ring
      _ ≤ 2 ^ (g + t + logSlack (4 * C + 4 * cA + 10 + cLit + cF + C + c₀ + 1) n) :=
        Nat.pow_le_pow_right (by norm_num) h5
  · -- the complexity of `R̂`
    obtain ⟨N, hN⟩ : ∃ N : ℕ, N = Nat.pair m (Nat.pair u (omegaCount cD m)) := ⟨_, rfl⟩
    have hmem : finsetListCode (theorem6_aux_union (completedBoundedOutput cD m) u).toFinset
        ∈ theorem6_aux_F cD (Nat.bits N) := by
      unfold theorem6_aux_F
      simp only [decodeBits_natBits, hN, Nat.unpair_pair]
      have hdom : (Nat.rfind fun s => Part.some
          ((boundedOutputStage cD m s).length == omegaCount cD m)).Dom := by
        refine Nat.rfind_dom.2 ⟨boundedOutputCompletionTime cD m, ?_, fun _ => trivial⟩
        show true ∈ Part.some _
        rw [Kolmogorov.boundedOutputStage_eq_completed_at_completion]
        simp [omegaCount]
      refine (Part.mem_map_iff _).2 ⟨_, Part.get_mem hdom, ?_⟩
      have hspec := Nat.rfind_spec (Part.get_mem hdom)
      have hlen : (boundedOutputStage cD m ((Nat.rfind fun s => Part.some
          ((boundedOutputStage cD m s).length == omegaCount cD m)).get hdom)).length =
          omegaCount cD m := by
        simpa using hspec
      rw [Kolmogorov.boundedOutputStage_eq_completed_of_length_eq cD m _ hlen]
      rfl
    have hK := hF (Nat.bits N) _ hmem
    have hLitN : plainK D (Nat.bits N) ≤ (((Nat.bits N).length + cLit : ℕ) : ENat) := by
      simpa [programLength] using hLit (Nat.bits N)
    -- the length of the input
    obtain ⟨k, hk⟩ : ∃ k : ℕ, k = m + 1 + Nat.size u := ⟨_, rfl⟩
    have hmk : m < 2 ^ k :=
      lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.pow_le_pow_right (by norm_num) (by omega))
    have huk : u < 2 ^ k :=
      lt_of_lt_of_le (Nat.lt_size_self u) (Nat.pow_le_pow_right (by norm_num) (by omega))
    have hck : omegaCount cD m < 2 ^ k :=
      lt_of_lt_of_le (Kolmogorov.omegaCount_lt_two_pow_succ cD m)
        (Nat.pow_le_pow_right (by norm_num) (by omega))
    have hP : Nat.pair u (omegaCount cD m) < 2 ^ (2 * k) := by
      have h := Nat.pair_lt_max_add_one_sq u (omegaCount cD m)
      have hmax : max u (omegaCount cD m) + 1 ≤ 2 ^ k := by
        rcases le_total u (omegaCount cD m) with h' | h'
        · rw [max_eq_right h']; omega
        · rw [max_eq_left h']; omega
      calc Nat.pair u (omegaCount cD m) < (max u (omegaCount cD m) + 1) ^ 2 := h
        _ ≤ (2 ^ k) ^ 2 := Nat.pow_le_pow_left hmax 2
        _ = 2 ^ (2 * k) := by rw [← pow_mul]; ring_nf
    have hNk : N < 2 ^ (4 * k) := by
      rw [hN]
      have h := Nat.pair_lt_max_add_one_sq m (Nat.pair u (omegaCount cD m))
      have hm2 : m < 2 ^ (2 * k) :=
        lt_of_lt_of_le hmk (Nat.pow_le_pow_right (by norm_num) (by omega))
      have hmax : max m (Nat.pair u (omegaCount cD m)) + 1 ≤ 2 ^ (2 * k) := by
        rcases le_total m (Nat.pair u (omegaCount cD m)) with h' | h'
        · rw [max_eq_right h']; omega
        · rw [max_eq_left h']; omega
      calc Nat.pair m (Nat.pair u (omegaCount cD m))
          < (max m (Nat.pair u (omegaCount cD m)) + 1) ^ 2 := h
        _ ≤ (2 ^ (2 * k)) ^ 2 := Nat.pow_le_pow_left hmax 2
        _ = 2 ^ (4 * k) := by rw [← pow_mul]; ring_nf
    have hlenN : (Nat.bits N).length ≤ 4 * k := by
      rw [Nat.size_eq_bits_len]
      exact (Nat.size_le).2 hNk
    -- `size u` is logarithmic in `n`
    have hulin : u ≤ (B + 1) * n + (B + c₀) := by
      have e : (B + 1) * n = B * n + n := by ring
      have e2 : B * (n + 1) = B * n + B := by ring
      omega
    have hsizeu : Nat.size u ≤ logSlack cA n := by
      have h := hA n u hulin
      have h' : Nat.size u ≤ logSlack 1 u := by
        unfold logSlack
        rw [Nat.size_eq_bits_len]
        omega
      exact h'.trans h
    have hfinal : plainK D (finsetListCode
        (theorem6_aux_union (completedBoundedOutput cD m) u).toFinset) ≤
        (((Nat.bits N).length + cLit + cF : ℕ) : ENat) := by
      calc plainK D (finsetListCode
            (theorem6_aux_union (completedBoundedOutput cD m) u).toFinset)
          ≤ plainK D (Nat.bits N) + (cF : ENat) := hK
        _ ≤ (((Nat.bits N).length + cLit : ℕ) : ENat) + (cF : ENat) := by gcongr
        _ = (((Nat.bits N).length + cLit + cF : ℕ) : ENat) := by push_cast; ring
    have hnat := ENat.toNat_le_of_le_natCast hfinal
    change (plainK D _).toNat ≤ _
    omega
  · -- every relevant stochastic string lies in `R̂`
    intro w hst hle
    obtain ⟨A, hwA, hAK, hAcard⟩ := hst
    rw [List.mem_toFinset]
    unfold theorem6_aux_union
    rw [List.mem_flatMap]
    have hcond : natCondK D w (finsetListCode A) ≤ natK D w + c₀ := by
      have h := hc₀ w (finsetListCode A)
      have hfin := Kolmogorov.plainK_ne_top D hD w
      have h' : condK D w (finsetListCode A) ≤ ((natK D w + c₀ : ℕ) : ENat) := by
        rw [Nat.cast_add]
        unfold natK
        rw [ENat.natCast_toNat hfin]
        exact h
      exact ENat.toNat_le_of_le_natCast h'
    refine ⟨finsetListCode A, ?_, ?_⟩
    · rw [List.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [Kolmogorov.mem_completedBoundedOutput_iff_plainK_le hcD]
        have hfin := Kolmogorov.plainK_ne_top D hD (finsetListCode A)
        rw [← ENat.natCast_toNat hfin]
        have hAK' : natK D (finsetListCode A) ≤ m := by omega
        exact_mod_cast hAK'
      · rw [decide_eq_true_iff, finsetListCode, decodeListCode_listCode,
          length_canonicalFinsetList]
        exact hAcard.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
    · rw [finsetListCode, decodeListCode_listCode, mem_canonicalFinsetList]
      exact hwA

/-- A finite set `Y` has at most `(K + 1) (|Y| + 1) ^ K` subsets of size at most `K`. -/
private theorem theorem6_aux_spoiled_aux_small_card (Y : Finset BitString) (K : ℕ) :
    (Y.powerset.filter (fun t => t.card ≤ K)).card ≤ (K + 1) * (Y.card + 1) ^ K := by
  have hsub : Y.powerset.filter (fun t => t.card ≤ K) ⊆
      (Finset.range (K + 1)).biUnion (fun j => Y.powersetCard j) := by
    intro t ht
    rw [Finset.mem_filter, Finset.mem_powerset] at ht
    rw [Finset.mem_biUnion]
    exact ⟨t.card, Finset.mem_range.2 (by omega), Finset.mem_powersetCard.2 ⟨ht.1, rfl⟩⟩
  calc (Y.powerset.filter (fun t => t.card ≤ K)).card
      ≤ ((Finset.range (K + 1)).biUnion (fun j => Y.powersetCard j)).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ j ∈ Finset.range (K + 1), (Y.powersetCard j).card := Finset.card_biUnion_le
    _ ≤ ∑ j ∈ Finset.range (K + 1), (Y.card + 1) ^ K := by
        apply Finset.sum_le_sum
        intro j hj
        rw [Finset.card_powersetCard]
        have hj' : j ≤ K := by
          have := Finset.mem_range.1 hj
          omega
        calc Y.card.choose j ≤ Y.card ^ j := Nat.choose_le_pow _ _
          _ ≤ (Y.card + 1) ^ j := Nat.pow_le_pow_left (Nat.le_succ _) _
          _ ≤ (Y.card + 1) ^ K := Nat.pow_le_pow_right (Nat.succ_pos _) hj'
    _ = (K + 1) * (Y.card + 1) ^ K := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

/-- The number of restricted nearness relations is bounded by the stated power of two under
the given parameter inequalities. -/
private theorem theorem6_aux_spoiled_aux_arith (a b g s : ℕ) (hs : 10 ≤ s)
    (hgs : g + s + 1 ≤ 2 ^ s) (ha : a + 5 * s ≤ g) (hb : b + 5 * s ≤ g) :
    (g + s + 2) * 2 ^ s * 2 ^ a + (g + s + 2) * 2 ^ s * 2 ^ b ≤ 2 ^ (g - 2 * s - 1) := by
  have hgs2 : g + s + 2 ≤ 2 ^ (s + 1) := by
    rw [pow_succ]
    omega
  have hEa : 2 ^ a ≤ 2 ^ (g - 5 * s) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hEb : 2 ^ b ≤ 2 ^ (g - 5 * s) := Nat.pow_le_pow_right (by norm_num) (by omega)
  calc (g + s + 2) * 2 ^ s * 2 ^ a + (g + s + 2) * 2 ^ s * 2 ^ b
      ≤ 2 ^ (s + 1) * 2 ^ s * 2 ^ (g - 5 * s) + 2 ^ (s + 1) * 2 ^ s * 2 ^ (g - 5 * s) := by
        gcongr
    _ = 2 ^ (s + 1 + s + (g - 5 * s) + 1) := by ring
    _ ≤ 2 ^ (g - 2 * s - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- The number of subsets of size at most `2 ^ s` from a set of size at most `2 ^ (g + s)`
is bounded by the stated power of two. -/
private theorem theorem6_aux_spoiled_aux_bound (g s n : ℕ) (hn : n ≤ 2 ^ (g + s)) :
    (2 ^ s + 1) * (n + 1) ^ (2 ^ s) ≤ 2 ^ ((g + s + 2) * 2 ^ s) := by
  have h1 : 2 ^ s + 1 ≤ 2 ^ (2 ^ s) := Nat.lt_two_pow_self
  have h2 : n + 1 ≤ 2 ^ (g + s + 1) := by
    have := Nat.one_le_two_pow (n := g + s)
    rw [pow_succ]
    omega
  calc (2 ^ s + 1) * (n + 1) ^ (2 ^ s) ≤ 2 ^ (2 ^ s) * (2 ^ (g + s + 1)) ^ (2 ^ s) :=
        Nat.mul_le_mul h1 (Nat.pow_le_pow_left h2 _)
    _ = 2 ^ ((g + s + 2) * 2 ^ s) := by
        rw [← pow_mul, ← pow_add]
        congr 1
        ring

/-- (Pure combinatorics, counting nearness
relations): the sets of spoiled edges are covered by a small family of small sets.  For a pair of
nearness relations `N₁, N₂` (degree bound `2 ^ s`), call an edge `e ∈ S₁ × S₂` spoiled if it is
`(N₁, N₂)`-close to a pair whose pair code lies in `R`.  Only the restrictions of `N₁, N₂` to
`S₁ × π₁(R)` and `S₂ × π₂(R)` matter (`πᵢ(R)` the components of the pairs coded in `R`, at most
`|R| ≤ 2 ^ (g + s)` strings each); every `x ∈ Sᵢ` has at most `2 ^ s` partners, so there are at most
`(2 ^ (g + s) + 1) ^ (2 ^ s · (2 ^ a + 2 ^ b)) ≤ 2 ^ (2 ^ (g - 2s - 1))` restrictions (using
`g + s + 1 ≤ 2 ^ s` and `a + 5s, b + 5s ≤ g`); and every spoiled set has at most
`|R| · 2 ^ s · 2 ^ s ≤ 2 ^ (g + 3s)` elements (each `y` has at most `2 ^ s` partners in `Sᵢ`).  The
family consists of the spoiled sets of the restrictions. -/
private theorem theorem6_aux_spoiled_family (a b g s : ℕ) (R : Finset BitString)
    (hR : R.card ≤ 2 ^ (g + s)) (hs : 10 ≤ s) (hgs : g + s + 1 ≤ 2 ^ s)
    (ha : a + 5 * s ≤ g) (hb : b + 5 * s ≤ g) :
    ∃ 𝓕 : Finset (Finset (BitString × BitString)),
      𝓕.card ≤ 2 ^ (2 ^ (g - 2 * s - 1)) ∧
      (∀ F ∈ 𝓕, F.card ≤ 2 ^ (g + 3 * s)) ∧
      ∀ N₁ N₂ : BitString → BitString → Prop,
        theorem6_IsNearness (stringsOfLength a) s N₁ →
        theorem6_IsNearness (stringsOfLength b) s N₂ →
        ∃ F ∈ 𝓕, ∀ e ∈ stringsOfLength a ×ˢ stringsOfLength b,
          (∃ y₁ y₂ : BitString, pairCode y₁ y₂ ∈ R ∧ N₁ e.1 y₁ ∧ N₂ e.2 y₂) → e ∈ F := by
  classical
  obtain ⟨Y₁, hY₁⟩ : ∃ Y : Finset BitString, Y = R.image decodeFirst := ⟨_, rfl⟩
  obtain ⟨Y₂, hY₂⟩ : ∃ Y : Finset BitString, Y = R.image decodeSecond := ⟨_, rfl⟩
  obtain ⟨T₁, hT₁⟩ : ∃ T : Finset (Finset BitString),
      T = Y₁.powerset.filter (fun t => t.card ≤ 2 ^ s) := ⟨_, rfl⟩
  obtain ⟨T₂, hT₂⟩ : ∃ T : Finset (Finset BitString),
      T = Y₂.powerset.filter (fun t => t.card ≤ 2 ^ s) := ⟨_, rfl⟩
  obtain ⟨P₁, hP₁⟩ := (⟨_, rfl⟩ : ∃ P, P = (stringsOfLength a).pi (fun _ => T₁))
  obtain ⟨P₂, hP₂⟩ := (⟨_, rfl⟩ : ∃ P, P = (stringsOfLength b).pi (fun _ => T₂))
  let Sp : ((x : BitString) → x ∈ stringsOfLength a → Finset BitString) ×
      ((x : BitString) → x ∈ stringsOfLength b → Finset BitString) →
      Finset (BitString × BitString) := fun p =>
    (stringsOfLength a ×ˢ stringsOfLength b).filter (fun e =>
      ∃ (h₁ : e.1 ∈ stringsOfLength a) (h₂ : e.2 ∈ stringsOfLength b), ∃ y₁ y₂ : BitString,
        pairCode y₁ y₂ ∈ R ∧ y₁ ∈ p.1 e.1 h₁ ∧ y₂ ∈ p.2 e.2 h₂)
  refine ⟨((P₁ ×ˢ P₂).image Sp).filter (fun F => F.card ≤ 2 ^ (g + 3 * s)), ?_, ?_, ?_⟩
  · -- the number of restricted relations
    have hY₁c : Y₁.card ≤ 2 ^ (g + s) := by
      rw [hY₁]
      exact Finset.card_image_le.trans hR
    have hY₂c : Y₂.card ≤ 2 ^ (g + s) := by
      rw [hY₂]
      exact Finset.card_image_le.trans hR
    have hT₁c : T₁.card ≤ 2 ^ ((g + s + 2) * 2 ^ s) := by
      rw [hT₁]
      exact (theorem6_aux_spoiled_aux_small_card Y₁ (2 ^ s)).trans
        (theorem6_aux_spoiled_aux_bound g s _ hY₁c)
    have hT₂c : T₂.card ≤ 2 ^ ((g + s + 2) * 2 ^ s) := by
      rw [hT₂]
      exact (theorem6_aux_spoiled_aux_small_card Y₂ (2 ^ s)).trans
        (theorem6_aux_spoiled_aux_bound g s _ hY₂c)
    have hP₁c : P₁.card = T₁.card ^ (2 ^ a) := by
      rw [hP₁, Finset.card_pi, Finset.prod_const, card_stringsOfLength]
    have hP₂c : P₂.card = T₂.card ^ (2 ^ b) := by
      rw [hP₂, Finset.card_pi, Finset.prod_const, card_stringsOfLength]
    have hexp := theorem6_aux_spoiled_aux_arith a b g s hs hgs ha hb
    calc (((P₁ ×ˢ P₂).image Sp).filter (fun F => F.card ≤ 2 ^ (g + 3 * s))).card
        ≤ ((P₁ ×ˢ P₂).image Sp).card := Finset.card_filter_le _ _
      _ ≤ (P₁ ×ˢ P₂).card := Finset.card_image_le
      _ = T₁.card ^ (2 ^ a) * T₂.card ^ (2 ^ b) := by
          rw [Finset.card_product, hP₁c, hP₂c]
      _ ≤ (2 ^ ((g + s + 2) * 2 ^ s)) ^ (2 ^ a) * (2 ^ ((g + s + 2) * 2 ^ s)) ^ (2 ^ b) :=
          Nat.mul_le_mul (Nat.pow_le_pow_left hT₁c _) (Nat.pow_le_pow_left hT₂c _)
      _ = 2 ^ ((g + s + 2) * 2 ^ s * 2 ^ a + (g + s + 2) * 2 ^ s * 2 ^ b) := by
          rw [← pow_mul, ← pow_mul, ← pow_add]
      _ ≤ 2 ^ (2 ^ (g - 2 * s - 1)) := Nat.pow_le_pow_right (by norm_num) hexp
  · intro F hF
    exact (Finset.mem_filter.1 hF).2
  · intro N₁ N₂ hN₁ hN₂
    let f₁ : (x : BitString) → x ∈ stringsOfLength a → Finset BitString :=
      fun x _ => Y₁.filter (fun y => N₁ x y)
    let f₂ : (x : BitString) → x ∈ stringsOfLength b → Finset BitString :=
      fun x _ => Y₂.filter (fun y => N₂ x y)
    have hf₁ : f₁ ∈ P₁ := by
      rw [hP₁, Finset.mem_pi]
      intro x hx
      rw [hT₁, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.filter_subset _ _,
        hN₁.1 x hx _ (fun y hy => (Finset.mem_filter.1 hy).2)⟩
    have hf₂ : f₂ ∈ P₂ := by
      rw [hP₂, Finset.mem_pi]
      intro x hx
      rw [hT₂, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.filter_subset _ _,
        hN₂.1 x hx _ (fun y hy => (Finset.mem_filter.1 hy).2)⟩
    have hcol₁ : ∀ y, ((stringsOfLength a).filter (fun x => N₁ x y)).card ≤ 2 ^ s := fun y =>
      hN₁.2 y _ (Finset.filter_subset _ _) (fun x hx => (Finset.mem_filter.1 hx).2)
    have hcol₂ : ∀ y, ((stringsOfLength b).filter (fun x => N₂ x y)).card ≤ 2 ^ s := fun y =>
      hN₂.2 y _ (Finset.filter_subset _ _) (fun x hx => (Finset.mem_filter.1 hx).2)
    have hsub : Sp (f₁, f₂) ⊆ R.biUnion (fun w =>
        ((stringsOfLength a).filter (fun x => N₁ x (decodeFirst w))) ×ˢ
          ((stringsOfLength b).filter (fun x => N₂ x (decodeSecond w)))) := by
      intro e he
      simp only [Sp, Finset.mem_filter] at he
      obtain ⟨_, h₁, h₂, y₁, y₂, hw, hy₁, hy₂⟩ := he
      rw [Finset.mem_biUnion]
      refine ⟨pairCode y₁ y₂, hw, ?_⟩
      rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter, decodeFirst_pairCode,
        decodeSecond_pairCode]
      have hy₁' : N₁ e.1 y₁ := (Finset.mem_filter.1 hy₁).2
      have hy₂' : N₂ e.2 y₂ := (Finset.mem_filter.1 hy₂).2
      exact ⟨⟨h₁, hy₁'⟩, ⟨h₂, hy₂'⟩⟩
    have hcard : (Sp (f₁, f₂)).card ≤ 2 ^ (g + 3 * s) := by
      calc (Sp (f₁, f₂)).card
          ≤ (R.biUnion (fun w =>
            ((stringsOfLength a).filter (fun x => N₁ x (decodeFirst w))) ×ˢ
              ((stringsOfLength b).filter (fun x => N₂ x (decodeSecond w))))).card :=
            Finset.card_le_card hsub
        _ ≤ ∑ w ∈ R, (((stringsOfLength a).filter (fun x => N₁ x (decodeFirst w))) ×ˢ
              ((stringsOfLength b).filter (fun x => N₂ x (decodeSecond w)))).card :=
            Finset.card_biUnion_le
        _ ≤ ∑ w ∈ R, 2 ^ s * 2 ^ s := by
            apply Finset.sum_le_sum
            intro w _
            rw [Finset.card_product]
            exact Nat.mul_le_mul (hcol₁ _) (hcol₂ _)
        _ = R.card * (2 ^ s * 2 ^ s) := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ 2 ^ (g + s) * (2 ^ s * 2 ^ s) := Nat.mul_le_mul_right _ hR
        _ = 2 ^ (g + 3 * s) := by
            rw [← pow_add, ← pow_add]
            congr 1
            ring
    refine ⟨Sp (f₁, f₂), ?_, ?_⟩
    · rw [Finset.mem_filter]
      exact ⟨Finset.mem_image.2 ⟨(f₁, f₂), Finset.mem_product.2 ⟨hf₁, hf₂⟩, rfl⟩, hcard⟩
    · intro e he hsp
      obtain ⟨y₁, y₂, hw, h1, h2⟩ := hsp
      have he' := Finset.mem_product.1 he
      simp only [Sp, Finset.mem_filter]
      refine ⟨he, he'.1, he'.2, y₁, y₂, hw, ?_, ?_⟩
      · change y₁ ∈ Y₁.filter (fun y => N₁ e.1 y)
        rw [Finset.mem_filter, hY₁]
        exact ⟨Finset.mem_image.2 ⟨pairCode y₁ y₂, hw, decodeFirst_pairCode y₁ y₂⟩, h1⟩
      · change y₂ ∈ Y₂.filter (fun y => N₂ e.2 y)
        rw [Finset.mem_filter, hY₂]
        exact ⟨Finset.mem_image.2 ⟨pairCode y₁ y₂, hw, decodeSecond_pairCode y₁ y₂⟩, h2⟩

/-- An edge of the finite bipartite graph used by the random-family argument. -/
private abbrev theorem6_aux_random_family_edgeType (a b : ℕ) :=
  {e : BitString × BitString // e ∈ stringsOfLength a ×ˢ stringsOfLength b}

/-- A length-`k` independent sample of edges from the finite bipartite graph. -/
private abbrev theorem6_aux_random_family_sampleType (a b k : ℕ) :=
  Fin k → theorem6_aux_random_family_edgeType a b

private def theorem6_aux_random_family_leftCount (a b k : ℕ)
    (ω : theorem6_aux_random_family_sampleType a b k) (x : BitString) : ℕ :=
  ((Finset.univ : Finset (Fin k)).filter fun i => (ω i).val.1 = x).card

private def theorem6_aux_random_family_rightCount (a b k : ℕ)
    (ω : theorem6_aux_random_family_sampleType a b k) (y : BitString) : ℕ :=
  ((Finset.univ : Finset (Fin k)).filter fun i => (ω i).val.2 = y).card

private def theorem6_aux_random_family_suitable (a b g k : ℕ)
    (ω : theorem6_aux_random_family_sampleType a b k) (i : Fin k) : Prop :=
  theorem6_aux_random_family_leftCount a b k ω (ω i).val.1 ≤ 2 ^ (g - a) ∧
    theorem6_aux_random_family_rightCount a b k ω (ω i).val.2 ≤ 2 ^ (g - b)

private noncomputable def theorem6_aux_random_family_unsuitableCount (a b g k : ℕ)
    (ω : theorem6_aux_random_family_sampleType a b k) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Fin k)).filter fun i =>
    ¬ theorem6_aux_random_family_suitable a b g k ω i).card

private noncomputable def theorem6_aux_random_family_repeatIndices (a b k : ℕ)
    (ω : theorem6_aux_random_family_sampleType a b k) : Finset (Fin k) := by
  classical
  exact Finset.univ.filter fun i =>
    ∃ j : Fin k, j < i ∧ (ω j).val = (ω i).val

private noncomputable def theorem6_aux_random_family_familyBadSamples (a b k : ℕ)
    (𝓕 : Finset (Finset (BitString × BitString))) :
    Finset (theorem6_aux_random_family_sampleType a b k) := by
  classical
  exact Finset.univ.filter fun ω =>
    ∃ F ∈ 𝓕, k ≤ 2 * ((Finset.univ : Finset (Fin k)).filter fun i => (ω i).val ∈ F).card

private noncomputable def theorem6_aux_random_family_unsuitableBadSamples (a b g k : ℕ) :
    Finset (theorem6_aux_random_family_sampleType a b k) := by
  classical
  exact Finset.univ.filter fun ω =>
    k ≤ 4 * theorem6_aux_random_family_unsuitableCount a b g k ω

private noncomputable def theorem6_aux_random_family_repeatBadSamples (a b k : ℕ) :
    Finset (theorem6_aux_random_family_sampleType a b k) := by
  classical
  exact Finset.univ.filter fun ω =>
    k ≤ 8 * (theorem6_aux_random_family_repeatIndices a b k ω).card

/-- for a fixed member of the family, count samples with at least half their indices in that set. -/
private theorem theorem6_fixedSetTail
    (a b g s k : ℕ) (F : Finset (BitString × BitString))
    (hk : k = 2 ^ (g - 2 * s)) (hF : F.card ≤ 2 ^ (g + 3 * s))
    (hs : 10 ≤ s) (ha : a + 5 * s ≤ g) (hab : g + 5 * s ≤ a + b) :
    ((Finset.univ : Finset (theorem6_aux_random_family_sampleType a b k)).filter
      fun ω => k ≤ 2 * ((Finset.univ : Finset (Fin k)).filter
        fun i => (ω i).val ∈ F).card).card * 2 ^ (s * k) ≤
      (Finset.univ : Finset (theorem6_aux_random_family_sampleType a b k)).card * 2 ^ k := by
  classical
  let Ω : Finset (theorem6_aux_random_family_sampleType a b k) := Finset.univ
  let I : Finset (Fin k) := Finset.univ
  let E := theorem6_aux_random_family_edgeType a b
  let edges : Finset E := Finset.univ
  let inF : Finset E := edges.filter fun e => e.val ∈ F
  let t := k / 2
  have hd : 0 < g - 2 * s := by omega
  have hdecomp : g - 2 * s = (g - 2 * s - 1) + 1 := by omega
  have hkpos : 0 < k := by rw [hk]; positivity
  have hkhalf : k / 2 = 2 ^ (g - 2 * s - 1) := by
    rw [hk, hdecomp, pow_succ]
    calc
      2 ^ (g - 2 * s - 1) * 2 / 2 = 2 ^ (g - 2 * s - 1) :=
        Nat.mul_div_left _ (by norm_num)
      _ = 2 ^ (g - 2 * s - 1 + 1 - 1) := by congr 1
  have htwok : 2 * t = k := by
    dsimp [t]
    calc
      2 * (k / 2) = 2 * 2 ^ (g - 2 * s - 1) := by rw [hkhalf]
      _ = 2 ^ (g - 2 * s - 1) * 2 := by ring
      _ = k := by rw [← pow_succ, ← hdecomp, hk]
  have hEcard : edges.card = 2 ^ (a + b) := by
    simp [edges, E, theorem6_aux_random_family_edgeType,
      Finset.card_product, card_stringsOfLength, ← pow_add]
  have hΩcard : Ω.card = (2 ^ (a + b)) ^ k := by
    simp [Ω, theorem6_aux_random_family_sampleType, card_stringsOfLength,
      ← pow_add, ← pow_mul]
  have hinFcard : inF.card ≤ 2 ^ (g + 3 * s) := by
    have hmap : Set.MapsTo (fun e : E => e.val) (inF : Set E) (F : Set (BitString × BitString)) :=
        by
      intro e he
      exact (Finset.mem_filter.mp he).2
    have hinj : (inF : Set E).InjOn (fun e : E => e.val) := by
      intro e he e' he' h
      exact Subtype.ext h
    exact (Finset.card_le_card_of_injOn (fun e : E => e.val) hmap hinj).trans hF
  let admissible := fun T : Finset (Fin k) =>
    Ω.filter fun ω => ∀ i ∈ T, (ω i).val ∈ F
  let C : Finset (Finset (Fin k)) := I.powersetCard t
  have hIcard : I.card = k := by simp [I]
  have hCcard : C.card ≤ 2 ^ k := by
    change (I.powersetCard t).card ≤ 2 ^ k
    rw [Finset.card_powersetCard, hIcard]
    exact Nat.choose_le_two_pow _ _
  have hIfilter (T : Finset (Fin k)) (hT : T ⊆ I) :
      I.filter (fun i => i ∈ T) = T := by
    ext i
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨_, hi⟩
      exact hi
    · intro hi
      exact ⟨hT hi, hi⟩
  have hbadSub :
      (Ω.filter fun ω => k ≤ 2 * ((I.filter fun i => (ω i).val ∈ F).card)) ⊆
        C.biUnion admissible := by
    intro ω hω
    have hω' := (Finset.mem_filter.mp hω).2
    let hits := I.filter fun i => (ω i).val ∈ F
    have ht : t ≤ hits.card := by
      have hhit : k ≤ 2 * hits.card := by simpa [hits] using hω'
      have hdiv : k / 2 ≤ hits.card := by
        have hhalf : 2 * (k / 2) = k := by simpa [t] using htwok
        omega
      simpa [t] using hdiv
    obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq ht
    have hTC : T ∈ C := by
      change T ∈ I.powersetCard t
      rw [Finset.mem_powersetCard]
      exact ⟨hTsub.trans (Finset.filter_subset _ _), hTcard⟩
    refine Finset.mem_biUnion.mpr ⟨T, hTC, ?_⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    intro i hi
    have : i ∈ hits := hTsub hi
    exact (Finset.mem_filter.mp this).2
  have hprodBound (T : Finset (Fin k)) (hTC : T ∈ C) :
      (admissible T).card ≤ inF.card ^ t * edges.card ^ (k - t) := by
    let allowed (i : Fin k) : Finset E := if i ∈ T then inF else edges
    let restricted : Finset (∀ i : Fin k, i ∈ I →
      theorem6_aux_random_family_edgeType a b) := I.pi allowed
    let lift : theorem6_aux_random_family_sampleType a b k →
      (∀ i : Fin k, i ∈ I → theorem6_aux_random_family_edgeType a b) :=
        fun ω i _ => ω i
    have hTsub : T ⊆ I := (Finset.mem_powersetCard.mp hTC).1
    have hTcard : T.card = t := (Finset.mem_powersetCard.mp hTC).2
    have hmap (ω : theorem6_aux_random_family_sampleType a b k)
        (hω : ω ∈ admissible T) : lift ω ∈ restricted := by
      change (lift ω) ∈ I.pi allowed
      rw [Finset.mem_pi]
      intro i hi
      by_cases hit : i ∈ T
      · have hmem : ω i ∈ inF :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hω).2 i hit⟩
        simpa [lift, allowed, hit] using hmem
      · have hmem : ω i ∈ edges := Finset.mem_univ _
        simpa [lift, allowed, hit] using hmem
    have hinj : (admissible T : Set (theorem6_aux_random_family_sampleType a b k)).InjOn
        lift := by
      intro ω hω ω' hω' heq
      funext i
      exact congrFun (congrFun heq i) (Finset.mem_univ i)
    have hcardRestr : (admissible T).card ≤ restricted.card :=
      Finset.card_le_card_of_injOn lift
        (by intro ω hω; exact hmap ω hω) hinj
    have hIfilterT := hIfilter T hTsub
    have hnotcard : (I.filter fun i => i ∉ T).card = k - t := by
      have hp := Finset.card_filter_add_card_filter_not (s := I) (fun i => i ∈ T)
      rw [hIfilterT, hTcard, hIcard] at hp
      omega
    have hrestrictedCard : restricted.card = inF.card ^ t * edges.card ^ (k - t) := by
      change (I.pi allowed).card = inF.card ^ t * edges.card ^ (k - t)
      rw [Finset.card_pi]
      rw [← Finset.prod_filter_mul_prod_filter_not I (fun i => i ∈ T)
        (fun i => (allowed i).card)]
      have hprodT : (∏ i ∈ I with i ∈ T, (allowed i).card) = inF.card ^ t := by
        rw [show I.filter (fun i => i ∈ T) = T from hIfilterT]
        calc
          (∏ i ∈ T, (allowed i).card) = inF.card ^ T.card :=
            Finset.prod_eq_pow_card (s := T) (f := fun i => (allowed i).card)
              (b := inF.card) (by intro i hi; simp [allowed, hi])
          _ = inF.card ^ t := by rw [hTcard]
      have hprodNot : (∏ i ∈ I with i ∉ T, (allowed i).card) = edges.card ^ (k - t) := by
        rw [show I.filter (fun i => i ∉ T) = I.filter (fun i => ¬ i ∈ T) by rfl]
        have hprod := Finset.prod_eq_pow_card
          (s := I.filter fun i => ¬ i ∈ T) (f := fun i => (allowed i).card)
          (b := edges.card) (by
            intro i hi
            have hi' : i ∉ T := (Finset.mem_filter.mp hi).2
            simp [allowed, hi'])
        simpa [hnotcard] using hprod
      rw [hprodT, hprodNot]
    exact hcardRestr.trans_eq hrestrictedCard
  have hbadCard :
      (Ω.filter fun ω => k ≤ 2 * ((I.filter fun i => (ω i).val ∈ F).card)).card ≤
        2 ^ k * (inF.card ^ t * edges.card ^ (k - t)) := by
    calc
      _ ≤ (C.biUnion admissible).card := Finset.card_le_card hbadSub
      _ ≤ ∑ T ∈ C, (admissible T).card := Finset.card_biUnion_le
      _ ≤ ∑ _T ∈ C, inF.card ^ t * edges.card ^ (k - t) := by
        apply Finset.sum_le_sum
        intro T hTC
        exact hprodBound T hTC
      _ = C.card * (inF.card ^ t * edges.card ^ (k - t)) := by
        rw [Finset.sum_const, smul_eq_mul]
      _ ≤ 2 ^ k * (inF.card ^ t * edges.card ^ (k - t)) :=
        Nat.mul_le_mul_right _ hCcard
  have hExpBound : k + (g + 3 * s) * t + (a + b) * (k - t) + s * k ≤
      (a + b) * k + k := by
    have hgap : g + 3 * s + 2 * s ≤ a + b := by omega
    have hgapmul := Nat.mul_le_mul_right t hgap
    have hkt : k - t = t := by omega
    rw [hkt]
    nlinarith [hgapmul, htwok]
  calc
    _ ≤ (2 ^ k * (inF.card ^ t * edges.card ^ (k - t))) * 2 ^ (s * k) :=
      Nat.mul_le_mul_right _ hbadCard
    _ ≤ (2 ^ k * ((2 ^ (g + 3 * s)) ^ t * (2 ^ (a + b)) ^ (k - t))) *
        2 ^ (s * k) := by
      exact Nat.mul_le_mul_right (2 ^ (s * k)) <| Nat.mul_le_mul_left (2 ^ k) <|
        Nat.mul_le_mul (Nat.pow_le_pow_left hinFcard t)
          (Nat.pow_le_pow_left hEcard.le (k - t))
    _ = 2 ^ (k + (g + 3 * s) * t + (a + b) * (k - t) + s * k) := by
      rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
      ring
    _ ≤ 2 ^ ((a + b) * k + k) := Nat.pow_le_pow_right (by norm_num) hExpBound
    _ = Ω.card * 2 ^ k := by
      rw [hΩcard, ← pow_mul, ← pow_add]

/-- the family union bound.
Among all samples, fewer than one quarter have at least half their indices in some member of the
family. -/
private theorem theorem6_familyBound
    (a b g s k : ℕ) (𝓕 : Finset (Finset (BitString × BitString)))
    (hk : k = 2 ^ (g - 2 * s))
    (h𝓕 : 𝓕.card ≤ 2 ^ (2 ^ (g - 2 * s - 1)))
    (hF : ∀ F ∈ 𝓕, F.card ≤ 2 ^ (g + 3 * s))
    (hs : 10 ≤ s) (ha : a + 5 * s ≤ g)
    (hab : g + 5 * s ≤ a + b) :
    (theorem6_aux_random_family_familyBadSamples a b k 𝓕).card * 4 <
      (Finset.univ : Finset (theorem6_aux_random_family_sampleType a b k)).card := by
  classical
  let Ω : Finset (theorem6_aux_random_family_sampleType a b k) := Finset.univ
  let P := 2 ^ (s * k)
  let badFor := fun F : Finset (BitString × BitString) =>
    Ω.filter fun ω => k ≤ 2 * ((Finset.univ : Finset (Fin k)).filter
      fun i => (ω i).val ∈ F).card
  have hbadSub : theorem6_aux_random_family_familyBadSamples a b k 𝓕 ⊆
      𝓕.biUnion badFor := by
    intro ω hω
    simp only [theorem6_aux_random_family_familyBadSamples,
      Finset.mem_filter] at hω
    rcases hω.2 with ⟨F, hF𝓕, hhit⟩
    rw [Finset.mem_biUnion]
    exact ⟨F, hF𝓕, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hhit⟩⟩
  have hbadCard : (theorem6_aux_random_family_familyBadSamples a b k 𝓕).card ≤
      ∑ F ∈ 𝓕, (badFor F).card := by
    calc
      (theorem6_aux_random_family_familyBadSamples a b k 𝓕).card ≤
          (𝓕.biUnion badFor).card := Finset.card_le_card hbadSub
      _ ≤ ∑ F ∈ 𝓕, (badFor F).card := Finset.card_biUnion_le
  have hscaled :
      (theorem6_aux_random_family_familyBadSamples a b k 𝓕).card * P ≤
        𝓕.card * (Ω.card * 2 ^ k) := by
    calc
      (theorem6_aux_random_family_familyBadSamples a b k 𝓕).card * P ≤
          (∑ F ∈ 𝓕, (badFor F).card) * P := Nat.mul_le_mul_right P hbadCard
      _ = ∑ F ∈ 𝓕, (badFor F).card * P := by rw [Finset.sum_mul]
      _ ≤ ∑ F ∈ 𝓕, Ω.card * 2 ^ k := by
          apply Finset.sum_le_sum
          intro F hF𝓕
          have htail := theorem6_fixedSetTail
            a b g s k F hk (hF F hF𝓕) hs ha hab
          simpa [badFor, Ω, P] using htail
      _ = 𝓕.card * (Ω.card * 2 ^ k) := by
          rw [Finset.sum_const, smul_eq_mul]
  have hd : 3 * s ≤ g - 2 * s := by omega
  have hdpos : 0 < g - 2 * s := by omega
  have hkpos : 0 < k := by rw [hk]; positivity
  have hkhalf : k / 2 = 2 ^ (g - 2 * s - 1) := by
    rw [hk]
    have heq : g - 2 * s = (g - 2 * s - 1) + 1 := by omega
    rw [heq, pow_succ]
    calc
      2 ^ (g - 2 * s - 1) * 2 / 2 = 2 ^ (g - 2 * s - 1) :=
        Nat.mul_div_left _ (by norm_num)
      _ = 2 ^ (g - 2 * s - 1 + 1 - 1) := by congr 1
  have h𝓕' : 𝓕.card ≤ 2 ^ (k / 2) := by
    simpa [hkhalf] using h𝓕
  have hpowerExp : 2 + k / 2 + k < s * k := by
    have hsk : 10 * k ≤ s * k := Nat.mul_le_mul_right k hs
    have hhalf : k / 2 ≤ k := Nat.div_le_self _ _
    omega
  have hfactor : 4 * (𝓕.card * 2 ^ k) < P := by
    calc
      4 * (𝓕.card * 2 ^ k) ≤ 4 * (2 ^ (k / 2) * 2 ^ k) :=
        Nat.mul_le_mul_left 4 (Nat.mul_le_mul_right (2 ^ k) h𝓕')
      _ = 2 ^ (2 + k / 2 + k) := by
        rw [show 4 = 2 ^ 2 by norm_num, ← pow_add, ← pow_add]
        ring
      _ < 2 ^ (s * k) := Nat.pow_lt_pow_right (by norm_num) hpowerExp
      _ = P := rfl
  have hΩpos : 0 < Ω.card := by
    apply Finset.card_pos.mpr
    let e : theorem6_aux_random_family_edgeType a b :=
      ⟨(List.replicate a false, List.replicate b false), by
        simp [Finset.mem_product, mem_stringsOfLength]⟩
    exact ⟨fun _ => e, Finset.mem_univ _⟩
  have hstrict :
      4 * (theorem6_aux_random_family_familyBadSamples a b k 𝓕).card * P <
        Ω.card * P := by
    calc
      4 * (theorem6_aux_random_family_familyBadSamples a b k 𝓕).card * P =
          4 * ((theorem6_aux_random_family_familyBadSamples a b k 𝓕).card * P) := by ring
      _ ≤ 4 * (𝓕.card * (Ω.card * 2 ^ k)) := Nat.mul_le_mul_left 4 hscaled
      _ = Ω.card * (4 * (𝓕.card * 2 ^ k)) := by ring
      _ < Ω.card * P := Nat.mul_lt_mul_of_pos_left hfactor hΩpos
  have hcancel :
      4 * (theorem6_aux_random_family_familyBadSamples a b k 𝓕).card < Ω.card := by
    exact (Nat.mul_lt_mul_right (by positivity : 0 < P)).mp (by simpa [P] using hstrict)
  simpa [Ω, Nat.mul_comm] using hcancel

private def theorem6_expectedCount_leftCollisions
    (a b k : ℕ) (ω : theorem6_aux_random_family_sampleType a b k) (i : Fin k) : ℕ :=
  ((Finset.univ : Finset (Fin k)).filter fun j =>
    j ≠ i ∧ (ω j).val.1 = (ω i).val.1).card

private def theorem6_expectedCount_rightCollisions
    (a b k : ℕ) (ω : theorem6_aux_random_family_sampleType a b k) (i : Fin k) : ℕ :=
  ((Finset.univ : Finset (Fin k)).filter fun j =>
    j ≠ i ∧ (ω j).val.2 = (ω i).val.2).card

/-- for fixed distinct
sample positions, the number of samples matching at one endpoint is at most the inverse endpoint
space fraction of all samples. -/
private theorem theorem6_expectedCount_leftEvent
    (a b k : ℕ) (i j : Fin k) (hij : i ≠ j) :
    ((Finset.univ : Finset (theorem6_aux_random_family_sampleType a b k)).filter
      fun ω => (ω i).val.1 = (ω j).val.1).card * 2 ^ a ≤
      (Finset.univ : Finset (theorem6_aux_random_family_sampleType a b k)).card := by
  classical
  let Sample := theorem6_aux_random_family_sampleType a b k
  let Edge := theorem6_aux_random_family_edgeType a b
  let Left := {x : BitString // x ∈ stringsOfLength a}
  let Ω : Finset Sample := Finset.univ
  let EqualSamples := {ω : Sample // (ω i).val.1 = (ω j).val.1}
  let put : EqualSamples × Left → Sample := fun q =>
    Function.update q.1.val j
      ⟨(q.2.val, (q.1.val j).val.2),
        Finset.mem_product.mpr
          ⟨q.2.property, (Finset.mem_product.mp (q.1.val j).property).2⟩⟩
  have hput : Function.Injective put := by
    intro q q' hqq'
    apply Prod.ext
    · apply Subtype.ext
      funext t
      by_cases ht : t = j
      · subst t
        apply Subtype.ext
        apply Prod.ext
        · calc
            (q.1.val j).val.1 = (q.1.val i).val.1 := q.1.property.symm
            _ = (q'.1.val i).val.1 := by
              have hi := congrArg (fun e : Edge => e.val.1) (congrFun hqq' i)
              simpa [put, hij] using hi
            _ = (q'.1.val j).val.1 := q'.1.property
        · have hj := congrArg (fun e : Edge => e.val.2) (congrFun hqq' j)
          simpa [put] using hj
      · have ht' := congrFun hqq' t
        simpa [put, Function.update_of_ne ht] using ht'
    · apply Subtype.ext
      have hj := congrArg (fun e : Edge => e.val.1) (congrFun hqq' j)
      simpa [put] using hj
  have hcard := Fintype.card_le_of_injective put hput
  have hequal : Fintype.card EqualSamples =
      ((Finset.univ : Finset Sample).filter fun ω =>
        (ω i).val.1 = (ω j).val.1).card := by
    rw [Fintype.card_subtype]
  have hleft : Fintype.card Left = 2 ^ a := by
    simp [Left, Fintype.card_coe, card_stringsOfLength]
  rw [Fintype.card_prod, hequal, hleft] at hcard
  calc
    _ ≤ Fintype.card Sample := hcard
    _ = (Finset.univ : Finset Sample).card := Finset.card_univ.symm

/-- the corresponding
fixed-pair estimate for right endpoints. -/
private theorem theorem6_expectedCount_rightEvent
    (a b k : ℕ) (i j : Fin k) (hij : i ≠ j) :
    ((Finset.univ : Finset (theorem6_aux_random_family_sampleType a b k)).filter
      fun ω => (ω i).val.2 = (ω j).val.2).card * 2 ^ b ≤
      (Finset.univ : Finset (theorem6_aux_random_family_sampleType a b k)).card := by
  classical
  let Sample := theorem6_aux_random_family_sampleType a b k
  let Edge := theorem6_aux_random_family_edgeType a b
  let Right := {y : BitString // y ∈ stringsOfLength b}
  let Ω : Finset Sample := Finset.univ
  let EqualSamples := {ω : Sample // (ω i).val.2 = (ω j).val.2}
  let put : EqualSamples × Right → Sample := fun q =>
    Function.update q.1.val j
      ⟨((q.1.val j).val.1, q.2.val),
        Finset.mem_product.mpr
          ⟨(Finset.mem_product.mp (q.1.val j).property).1, q.2.property⟩⟩
  have hput : Function.Injective put := by
    intro q q' hqq'
    apply Prod.ext
    · apply Subtype.ext
      funext t
      by_cases ht : t = j
      · subst t
        apply Subtype.ext
        apply Prod.ext
        · have hj := congrArg (fun e : Edge => e.val.1) (congrFun hqq' j)
          simpa [put] using hj
        · calc
            (q.1.val j).val.2 = (q.1.val i).val.2 := q.1.property.symm
            _ = (q'.1.val i).val.2 := by
              have hi := congrArg (fun e : Edge => e.val.2) (congrFun hqq' i)
              simpa [put, hij] using hi
            _ = (q'.1.val j).val.2 := q'.1.property
      · have ht' := congrFun hqq' t
        simpa [put, Function.update_of_ne ht] using ht'
    · apply Subtype.ext
      have hj := congrArg (fun e : Edge => e.val.2) (congrFun hqq' j)
      simpa [put] using hj
  have hcard := Fintype.card_le_of_injective put hput
  have hequal : Fintype.card EqualSamples =
      ((Finset.univ : Finset Sample).filter fun ω =>
        (ω i).val.2 = (ω j).val.2).card := by
    rw [Fintype.card_subtype]
  have hright : Fintype.card Right = 2 ^ b := by
    simp [Right, Fintype.card_coe, card_stringsOfLength]
  rw [Fintype.card_prod, hequal, hright] at hcard
  calc
    _ ≤ Fintype.card Sample := hcard
    _ = (Finset.univ : Finset Sample).card := Finset.card_univ.symm

/-- sum the endpoint
collision probabilities over all ordered pairs of distinct sample positions. -/
private theorem theorem6_expectedCount_collisionSum
    (a b k : ℕ) :
    ((∑ ω : theorem6_aux_random_family_sampleType a b k,
        ∑ i : Fin k,
          theorem6_expectedCount_leftCollisions
            a b k ω i) * 2 ^ a) +
      ((∑ ω : theorem6_aux_random_family_sampleType a b k,
        ∑ i : Fin k,
          theorem6_expectedCount_rightCollisions
            a b k ω i) * 2 ^ b) ≤
      2 * k * (k - 1) *
        (Finset.univ : Finset (theorem6_aux_random_family_sampleType a b k)).card := by
  classical
  let Sample := theorem6_aux_random_family_sampleType a b k
  let Ω : Finset Sample := Finset.univ
  let I : Finset (Fin k) := Finset.univ
  let pairs : Finset (Fin k × Fin k) :=
    Finset.univ.filter fun p => p.1 ≠ p.2
  have hpairs : pairs.card = k * (k - 1) := by
    have hcard (i : Fin k) :
        ((Finset.univ : Finset (Fin k)).filter fun j => i ≠ j).card = k - 1 := by
      have h : ((Finset.univ : Finset (Fin k)).filter fun j => i ≠ j) =
          Finset.univ.erase i := by
        ext j
        simp [ne_comm]
      rw [h, Finset.card_erase_of_mem (Finset.mem_univ i)]
      simp
    have hEq : pairs.card =
        ∑ i : Fin k, ((Finset.univ : Finset (Fin k)).filter fun j => i ≠ j).card := by
      simp only [pairs, Finset.card_filter]
      rw [← Finset.univ_product_univ, Finset.sum_product]
    simp [hEq, hcard]
  have hleftPerSample (ω : Sample) :
      (∑ i ∈ I,
        theorem6_expectedCount_leftCollisions
          a b k ω i) = (pairs.filter fun p =>
            (ω p.1).val.1 = (ω p.2).val.1).card := by
    calc
      _ = ∑ i ∈ I, ∑ j ∈ I,
          if j ≠ i ∧ (ω j).val.1 = (ω i).val.1 then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        change ((Finset.univ : Finset (Fin k)).filter fun j =>
          j ≠ i ∧ (ω j).val.1 = (ω i).val.1).card = _
        rw [Finset.card_filter]
      _ = ∑ p ∈ I ×ˢ I,
          if p.2 ≠ p.1 ∧ (ω p.2).val.1 = (ω p.1).val.1 then 1 else 0 := by
        rw [Finset.sum_product]
      _ = ∑ p ∈ pairs,
          if (ω p.1).val.1 = (ω p.2).val.1 then 1 else 0 := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro p hp
        by_cases h : p.1 ≠ p.2 <;> simp [h, eq_comm]
      _ = (pairs.filter fun p =>
          (ω p.1).val.1 = (ω p.2).val.1).card := by
        rw [Finset.card_filter]
  have hleftSum :
      (∑ ω : Sample, ∑ i ∈ I,
        theorem6_expectedCount_leftCollisions
          a b k ω i) =
        ∑ p ∈ pairs, (Ω.filter fun ω => (ω p.1).val.1 = (ω p.2).val.1).card := by
    calc
      _ = ∑ ω : Sample, (pairs.filter fun p =>
          (ω p.1).val.1 = (ω p.2).val.1).card := by
        apply Finset.sum_congr rfl
        intro ω hω
        exact hleftPerSample ω
      _ = ∑ ω : Sample, ∑ p ∈ pairs,
          if (ω p.1).val.1 = (ω p.2).val.1 then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro ω hω
        rw [Finset.card_filter]
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro p hp
        exact Finset.sum_boole (fun ω : Sample =>
          (ω p.1).val.1 = (ω p.2).val.1) Ω
  have hrightPerSample (ω : Sample) :
      (∑ i ∈ I,
        theorem6_expectedCount_rightCollisions
          a b k ω i) = (pairs.filter fun p =>
            (ω p.1).val.2 = (ω p.2).val.2).card := by
    calc
      _ = ∑ i ∈ I, ∑ j ∈ I,
          if j ≠ i ∧ (ω j).val.2 = (ω i).val.2 then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        change ((Finset.univ : Finset (Fin k)).filter fun j =>
          j ≠ i ∧ (ω j).val.2 = (ω i).val.2).card = _
        rw [Finset.card_filter]
      _ = ∑ p ∈ I ×ˢ I,
          if p.2 ≠ p.1 ∧ (ω p.2).val.2 = (ω p.1).val.2 then 1 else 0 := by
        rw [Finset.sum_product]
      _ = ∑ p ∈ pairs,
          if (ω p.1).val.2 = (ω p.2).val.2 then 1 else 0 := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro p hp
        by_cases h : p.1 ≠ p.2 <;> simp [h, eq_comm]
      _ = (pairs.filter fun p =>
          (ω p.1).val.2 = (ω p.2).val.2).card := by
        rw [Finset.card_filter]
  have hrightSum :
      (∑ ω : Sample, ∑ i ∈ I,
        theorem6_expectedCount_rightCollisions
          a b k ω i) =
        ∑ p ∈ pairs, (Ω.filter fun ω => (ω p.1).val.2 = (ω p.2).val.2).card := by
    calc
      _ = ∑ ω : Sample, (pairs.filter fun p =>
          (ω p.1).val.2 = (ω p.2).val.2).card := by
        apply Finset.sum_congr rfl
        intro ω hω
        exact hrightPerSample ω
      _ = ∑ ω : Sample, ∑ p ∈ pairs,
          if (ω p.1).val.2 = (ω p.2).val.2 then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro ω hω
        rw [Finset.card_filter]
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro p hp
        exact Finset.sum_boole (fun ω : Sample =>
          (ω p.1).val.2 = (ω p.2).val.2) Ω
  have hleftFinset :
      (∑ ω : Sample, ∑ i ∈ I,
        theorem6_expectedCount_leftCollisions
          a b k ω i) * 2 ^ a ≤ k * (k - 1) * Ω.card := by
    rw [hleftSum, Finset.sum_mul]
    calc
      _ ≤ ∑ p ∈ pairs, Ω.card := by
        apply Finset.sum_le_sum
        intro p hp
        have h := theorem6_expectedCount_leftEvent
          a b k p.1 p.2 ((Finset.mem_filter.mp hp).2)
        exact h
      _ = pairs.card * Ω.card := by simp
      _ = k * (k - 1) * Ω.card := by rw [hpairs]
  have hleft :
      (∑ ω : Sample, ∑ i : Fin k,
        theorem6_expectedCount_leftCollisions
          a b k ω i) * 2 ^ a ≤ k * (k - 1) * Ω.card := by
    simpa [I] using hleftFinset
  have hrightFinset :
      (∑ ω : Sample, ∑ i ∈ I,
        theorem6_expectedCount_rightCollisions
          a b k ω i) * 2 ^ b ≤ k * (k - 1) * Ω.card := by
    rw [hrightSum, Finset.sum_mul]
    calc
      _ ≤ ∑ p ∈ pairs, Ω.card := by
        apply Finset.sum_le_sum
        intro p hp
        have h := theorem6_expectedCount_rightEvent
          a b k p.1 p.2 ((Finset.mem_filter.mp hp).2)
        exact h
      _ = pairs.card * Ω.card := by simp
      _ = k * (k - 1) * Ω.card := by rw [hpairs]
  have hright :
      (∑ ω : Sample, ∑ i : Fin k,
        theorem6_expectedCount_rightCollisions
          a b k ω i) * 2 ^ b ≤ k * (k - 1) * Ω.card := by
    simpa [I] using hrightFinset
  calc
    _ ≤ k * (k - 1) * Ω.card + k * (k - 1) * Ω.card := Nat.add_le_add hleft hright
    _ = 2 * k * (k - 1) * Ω.card := by ring
    _ = _ := by rfl

/-- the first-moment estimate for
unsuitable indices, obtained by counting endpoint collisions. -/
private theorem theorem6_expectedCount
    (a b g k : ℕ) (ha : a ≤ g) (hb : b ≤ g) :
    (∑ ω ∈ (Finset.univ : Finset (theorem6_aux_random_family_sampleType a b k)),
      theorem6_aux_random_family_unsuitableCount a b g k ω) * 2 ^ g ≤
        2 * k * (k - 1) *
          (Finset.univ : Finset (theorem6_aux_random_family_sampleType a b k)).card := by
  classical
  let Sample := theorem6_aux_random_family_sampleType a b k
  let Ω : Finset Sample := Finset.univ
  let leftCollisions : Sample → Fin k → ℕ :=
    theorem6_expectedCount_leftCollisions
      a b k
  let rightCollisions : Sample → Fin k → ℕ :=
    theorem6_expectedCount_rightCollisions
      a b k
  have hpoint (ω : Sample) :
      theorem6_aux_random_family_unsuitableCount a b g k ω * 2 ^ g ≤
        2 ^ a * (∑ i : Fin k, leftCollisions ω i) +
          2 ^ b * (∑ i : Fin k, rightCollisions ω i) := by
    have hleftAt (i : Fin k) :
        theorem6_aux_random_family_leftCount a b k ω (ω i).val.1 ≤
          1 + leftCollisions ω i := by
      let matchSet : Finset (Fin k) := (Finset.univ : Finset (Fin k)).filter fun j =>
        (ω j).val.1 = (ω i).val.1
      let otherSet : Finset (Fin k) := (Finset.univ : Finset (Fin k)).filter fun j =>
        j ≠ i ∧ (ω j).val.1 = (ω i).val.1
      have hi : i ∈ matchSet := by simp [matchSet]
      have hother : otherSet = matchSet.erase i := by
        ext j
        simp [matchSet, otherSet, ne_comm]
      change matchSet.card ≤ 1 + otherSet.card
      rw [hother, Finset.card_erase_of_mem hi]
      have hpos : 1 ≤ matchSet.card := Finset.card_pos.mpr ⟨i, hi⟩
      omega
    have hrightAt (i : Fin k) :
        theorem6_aux_random_family_rightCount a b k ω (ω i).val.2 ≤
          1 + rightCollisions ω i := by
      let matchSet : Finset (Fin k) := (Finset.univ : Finset (Fin k)).filter fun j =>
        (ω j).val.2 = (ω i).val.2
      let otherSet : Finset (Fin k) := (Finset.univ : Finset (Fin k)).filter fun j =>
        j ≠ i ∧ (ω j).val.2 = (ω i).val.2
      have hi : i ∈ matchSet := by simp [matchSet]
      have hother : otherSet = matchSet.erase i := by
        ext j
        simp [matchSet, otherSet, ne_comm]
      change matchSet.card ≤ 1 + otherSet.card
      rw [hother, Finset.card_erase_of_mem hi]
      have hpos : 1 ≤ matchSet.card := Finset.card_pos.mpr ⟨i, hi⟩
      omega
    have hbadAt (i : Fin k) :
        (if ¬ theorem6_aux_random_family_suitable a b g k ω i then 2 ^ g else 0) ≤
          2 ^ a * leftCollisions ω i + 2 ^ b * rightCollisions ω i := by
      by_cases hL : theorem6_aux_random_family_leftCount a b k ω (ω i).val.1 ≤ 2 ^ (g - a)
      · by_cases hR : theorem6_aux_random_family_rightCount a b k ω (ω i).val.2 ≤ 2 ^ (g - b)
        · simp? [theorem6_aux_random_family_suitable, hL, hR]
        · have hR' : 2 ^ (g - b) <
              theorem6_aux_random_family_rightCount a b k ω (ω i).val.2 := by omega
          have hcoll : 2 ^ (g - b) ≤ rightCollisions ω i := by
            have h := hrightAt i
            omega
          have hpow : 2 ^ b * 2 ^ (g - b) = 2 ^ g := by
            rw [← Nat.pow_add]
            congr 1
            omega
          simp? [theorem6_aux_random_family_suitable, hL, hR]
          calc
            2 ^ g = 2 ^ b * 2 ^ (g - b) := hpow.symm
            _ ≤ 2 ^ b * rightCollisions ω i := Nat.mul_le_mul_left _ hcoll
            _ ≤ 2 ^ a * leftCollisions ω i +
                2 ^ b * rightCollisions ω i := Nat.le_add_left _ _
      · have hL' : 2 ^ (g - a) <
            theorem6_aux_random_family_leftCount a b k ω (ω i).val.1 := by omega
        have hLcoll : 2 ^ (g - a) ≤ leftCollisions ω i := by
          have h := hleftAt i
          omega
        have hpow : 2 ^ a * 2 ^ (g - a) = 2 ^ g := by
          rw [← Nat.pow_add]
          congr 1
          omega
        simp only [theorem6_aux_random_family_suitable, hL]
        calc
          2 ^ g = 2 ^ a * 2 ^ (g - a) := hpow.symm
          _ ≤ 2 ^ a * leftCollisions ω i := Nat.mul_le_mul_left _ hLcoll
          _ ≤ 2 ^ a * leftCollisions ω i +
              2 ^ b * rightCollisions ω i := Nat.le_add_right _ _
    have hsum :
        (∑ i : Fin k,
          if ¬ theorem6_aux_random_family_suitable a b g k ω i then 2 ^ g else 0) ≤
          ∑ i : Fin k,
            (2 ^ a * leftCollisions ω i + 2 ^ b * rightCollisions ω i) :=
      Finset.sum_le_sum fun i _ => hbadAt i
    have hcount :
        theorem6_aux_random_family_unsuitableCount a b g k ω =
          ∑ i : Fin k,
            if ¬ theorem6_aux_random_family_suitable a b g k ω i then 1 else 0 := by
      simp [theorem6_aux_random_family_unsuitableCount, Finset.card_filter]
    rw [hcount]
    calc
      _ = ∑ i : Fin k,
          if ¬ theorem6_aux_random_family_suitable a b g k ω i then 2 ^ g else 0 := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        by_cases h : ¬ theorem6_aux_random_family_suitable a b g k ω i <;> simp [h]
      _ ≤ ∑ i : Fin k,
          (2 ^ a * leftCollisions ω i + 2 ^ b * rightCollisions ω i) := hsum
      _ = 2 ^ a * (∑ i : Fin k, leftCollisions ω i) +
          2 ^ b * (∑ i : Fin k, rightCollisions ω i) := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hsumPoint :
      (∑ ω ∈ Ω,
        theorem6_aux_random_family_unsuitableCount a b g k ω * 2 ^ g) ≤
        ∑ ω ∈ Ω,
          (2 ^ a * (∑ i : Fin k, leftCollisions ω i) +
            2 ^ b * (∑ i : Fin k, rightCollisions ω i)) :=
    Finset.sum_le_sum fun ω hω => hpoint ω
  have hcollision :=
    theorem6_expectedCount_collisionSum
      a b k
  have hcollision' :
      ((∑ ω : Sample, ∑ i : Fin k, leftCollisions ω i) * 2 ^ a) +
        ((∑ ω : Sample, ∑ i : Fin k, rightCollisions ω i) * 2 ^ b) ≤
          2 * k * (k - 1) * Ω.card := by
    exact hcollision
  calc
    (∑ ω ∈ Ω, theorem6_aux_random_family_unsuitableCount a b g k ω) * 2 ^ g =
        ∑ ω ∈ Ω,
          theorem6_aux_random_family_unsuitableCount a b g k ω * 2 ^ g := by
      rw [Finset.sum_mul]
    _ ≤ ∑ ω ∈ Ω,
          (2 ^ a * (∑ i : Fin k, leftCollisions ω i) +
            2 ^ b * (∑ i : Fin k, rightCollisions ω i)) := hsumPoint
    _ = ((∑ ω : Sample, ∑ i : Fin k, leftCollisions ω i) * 2 ^ a) +
        ((∑ ω : Sample, ∑ i : Fin k, rightCollisions ω i) * 2 ^ b) := by
      rw [Finset.sum_add_distrib]
      congr 1
      · calc
          (∑ ω ∈ Ω, 2 ^ a * (∑ i : Fin k, leftCollisions ω i)) =
              ∑ ω ∈ Ω, (∑ i : Fin k, leftCollisions ω i) * 2 ^ a := by
            apply Finset.sum_congr rfl
            intro ω hω
            ring
          _ = (∑ ω ∈ Ω, ∑ i : Fin k, leftCollisions ω i) * 2 ^ a := by
            rw [Finset.sum_mul]
          _ = (∑ ω : Sample, ∑ i : Fin k, leftCollisions ω i) * 2 ^ a := by
            simp [Ω]
      · calc
          (∑ ω ∈ Ω, 2 ^ b * (∑ i : Fin k, rightCollisions ω i)) =
              ∑ ω ∈ Ω, (∑ i : Fin k, rightCollisions ω i) * 2 ^ b := by
            apply Finset.sum_congr rfl
            intro ω hω
            ring
          _ = (∑ ω ∈ Ω, ∑ i : Fin k, rightCollisions ω i) * 2 ^ b := by
            rw [Finset.sum_mul]
          _ = (∑ ω : Sample, ∑ i : Fin k, rightCollisions ω i) * 2 ^ b := by
            simp [Ω]
    _ ≤ 2 * k * (k - 1) * Ω.card := hcollision'
    _ = _ := by rfl

/-- the degree estimate.
Fewer than one quarter of all samples have at least a quarter of their indices unsuitable. -/
private theorem theorem6_unsuitableBound
    (a b g s k : ℕ) (hk : k = 2 ^ (g - 2 * s))
    (hs : 10 ≤ s) (ha : a + 5 * s ≤ g) (hb : b + 5 * s ≤ g) :
    (theorem6_aux_random_family_unsuitableBadSamples a b g k).card * 4 <
      (Finset.univ : Finset (theorem6_aux_random_family_sampleType a b k)).card := by
  classical
  let Ω : Finset (theorem6_aux_random_family_sampleType a b k) := Finset.univ
  let bad := theorem6_aux_random_family_unsuitableBadSamples a b g k
  let total := ∑ ω ∈ Ω, theorem6_aux_random_family_unsuitableCount a b g k ω
  have hmean := theorem6_expectedCount
    a b g k (by omega) (by omega)
  have hmean' : total * 2 ^ g ≤ 2 * k * (k - 1) * Ω.card := by
    simpa [total, Ω] using hmean
  have hmarkov : bad.card * k ≤ 4 * total := by
    calc
      bad.card * k = ∑ ω ∈ bad, k := by simp
      _ ≤ ∑ ω ∈ bad, 4 * theorem6_aux_random_family_unsuitableCount a b g k ω := by
        apply Finset.sum_le_sum
        intro ω hω
        have hω' : k ≤ 4 * theorem6_aux_random_family_unsuitableCount a b g k ω := by
          simpa [bad, theorem6_aux_random_family_unsuitableBadSamples] using hω
        exact hω'
      _ ≤ ∑ ω ∈ Ω, 4 * theorem6_aux_random_family_unsuitableCount a b g k ω := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro ω hω hωbad
        positivity
      _ = 4 * total := by rw [Finset.mul_sum]
  have hkpos : 0 < k := by
    rw [hk]
    exact Nat.pow_pos (by omega)
  have h2s : 2 * s ≤ g := by omega
  have hsmall : 5 ≤ 2 * s := by omega
  have hExp : 5 + (g - 2 * s) ≤ g := by omega
  have h32 : 32 * k ≤ 2 ^ g := by
    rw [hk]
    calc
      32 * 2 ^ (g - 2 * s) = 2 ^ 5 * 2 ^ (g - 2 * s) := by norm_num
      _ = 2 ^ (5 + (g - 2 * s)) := by rw [← pow_add]
      _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hExp
  have hcoeff : 32 * k * (k - 1) < k * 2 ^ g := by
    have hinner : 32 * (k - 1) < 2 ^ g := by
      calc
        32 * (k - 1) < 32 * k :=
          Nat.mul_lt_mul_of_pos_left (Nat.sub_lt hkpos (by omega)) (by omega)
        _ ≤ 2 ^ g := h32
    calc
      32 * k * (k - 1) = k * (32 * (k - 1)) := by ring
      _ < k * 2 ^ g := Nat.mul_lt_mul_of_pos_left hinner hkpos
  have hΩpos : 0 < Ω.card := by
    have hx : (stringsOfLength a).Nonempty := by
      apply Finset.card_pos.mp
      rw [card_stringsOfLength]
      exact Nat.pow_pos (by omega)
    have hy : (stringsOfLength b).Nonempty := by
      apply Finset.card_pos.mp
      rw [card_stringsOfLength]
      exact Nat.pow_pos (by omega)
    obtain ⟨x, hx⟩ := hx
    obtain ⟨y, hy⟩ := hy
    let e : theorem6_aux_random_family_edgeType a b :=
      ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩⟩
    exact Finset.card_pos.mpr ⟨(fun _ : Fin k => e), Finset.mem_univ _⟩
  have hweak : (bad.card * 4) * (k * 2 ^ g) ≤ 32 * k * (k - 1) * Ω.card := by
    calc
      (bad.card * 4) * (k * 2 ^ g) = (4 * 2 ^ g) * (bad.card * k) := by ring
      _ ≤ (4 * 2 ^ g) * (4 * total) := Nat.mul_le_mul_left _ hmarkov
      _ = 16 * (total * 2 ^ g) := by ring
      _ ≤ 16 * (2 * k * (k - 1) * Ω.card) := Nat.mul_le_mul_left _ hmean'
      _ = 32 * k * (k - 1) * Ω.card := by ring
  have hstrict : (32 * k * (k - 1)) * Ω.card < (k * 2 ^ g) * Ω.card := by
    exact Nat.mul_lt_mul_of_pos_right (by simpa [Nat.mul_assoc] using hcoeff) hΩpos
  have hcancel : (k * 2 ^ g) * (bad.card * 4) < (k * 2 ^ g) * Ω.card := by
    calc
      (k * 2 ^ g) * (bad.card * 4) = (bad.card * 4) * (k * 2 ^ g) := by ring
      _ ≤ 32 * k * (k - 1) * Ω.card := hweak
      _ < (k * 2 ^ g) * Ω.card := hstrict
  have hresult := Nat.lt_of_mul_lt_mul_left hcancel
  simpa [bad, Ω, Nat.mul_comm] using hresult

/-- charge every repeated index to an earlier
equal pair. Distinct repeated indices give distinct pairs because the repeated index is the second
coordinate. -/
private theorem theorem6_repeatCharge
    (a b k : ℕ) (ω : theorem6_aux_random_family_sampleType a b k) :
    (theorem6_aux_random_family_repeatIndices a b k ω).card ≤
      ((Finset.univ : Finset (Fin k × Fin k)).filter fun p =>
        p.1 < p.2 ∧ (ω p.1).val = (ω p.2).val).card := by
  classical
  let repeats : Fin k → Prop := fun i =>
    ∃ j : Fin k, j < i ∧ (ω j).val = (ω i).val
  let pairs : Finset (Fin k × Fin k) :=
    Finset.univ.filter fun p => p.1 < p.2 ∧ (ω p.1).val = (ω p.2).val
  let charge : Fin k → Fin k × Fin k := fun i =>
    if h : repeats i then (Classical.choose h, i) else (i, i)
  have hmaps : ∀ i, i ∈ theorem6_aux_random_family_repeatIndices a b k ω →
      charge i ∈ pairs := by
    intro i hi
    have hrep : repeats i := by
      simpa [repeats, theorem6_aux_random_family_repeatIndices] using
        (Finset.mem_filter.mp hi).2
    have hs := Classical.choose_spec hrep
    have hcharge : charge i = (Classical.choose hrep, i) := by simp [charge, hrep]
    rw [hcharge]
    change (Classical.choose hrep, i) ∈
      Finset.univ.filter (fun p : Fin k × Fin k =>
        p.1 < p.2 ∧ (ω p.1).val = (ω p.2).val)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hs.1, hs.2⟩
  have hinj : (theorem6_aux_random_family_repeatIndices a b k ω : Set (Fin k)).InjOn
      charge := by
    intro i hi j hj hij
    have hsnd := congrArg Prod.snd hij
    have hsecond (i : Fin k) : (charge i).2 = i := by
      by_cases h : repeats i <;> simp [charge, h]
    rw [hsecond i, hsecond j] at hsnd
    exact hsnd
  exact Finset.card_le_card_of_injOn charge hmaps hinj

/-- the average number of equal earlier-index
pairs in a uniform sample is at most `k^2` divided by the number of possible edges. -/
private theorem theorem6_averageCollisionBound
    (a b k : ℕ) :
    (∑ ω : theorem6_aux_random_family_sampleType a b k,
      ((Finset.univ : Finset (Fin k × Fin k)).filter fun p =>
        p.1 < p.2 ∧ ((ω p.1).val = (ω p.2).val)).card) *
      Fintype.card (theorem6_aux_random_family_edgeType a b) ≤
        k * k * Fintype.card (theorem6_aux_random_family_sampleType a b k) := by
  classical
  let Edge := theorem6_aux_random_family_edgeType a b
  let Sample := theorem6_aux_random_family_sampleType a b k
  let Ω : Finset Sample := Finset.univ
  let pairs : Finset (Fin k × Fin k) :=
    Finset.univ.filter fun p => p.1 < p.2
  let collisionCount := fun ω : Sample =>
    (pairs.filter fun p => (ω p.1).val = (ω p.2).val).card
  let edgeCount := Fintype.card Edge
  let sampleCount := Fintype.card Sample
  have hpairs : pairs.card ≤ k * k := by
    calc
      pairs.card ≤ (Finset.univ : Finset (Fin k × Fin k)).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = k * k := by simp
  have hcollisionEvent (p : Fin k × Fin k) (hp : p ∈ pairs) :
      (Ω.filter fun ω : Sample => (ω p.1).val = (ω p.2).val).card *
        edgeCount ≤ sampleCount := by
    have hp' : p.1 < p.2 := (Finset.mem_filter.mp hp).2
    let i := p.1
    let j := p.2
    have hij : i < j := hp'
    let equalSamples := {ω : Sample // (ω i).val = (ω j).val}
    let insertSample : equalSamples × Edge → Sample := fun q =>
      Function.update q.1.val j q.2
    have hinj : Function.Injective insertSample := by
      intro q q' hqq'
      apply Prod.ext
      · apply Subtype.ext
        funext t
        by_cases ht : t = j
        · subst t
          have hi := congrFun hqq' i
          have hi' : q.1.val i = q'.1.val i := by
            simpa [insertSample, Function.update_of_ne (ne_of_lt hij)] using hi
          calc
            q.1.val j = q.1.val i := Subtype.ext q.1.property.symm
            _ = q'.1.val i := hi'
            _ = q'.1.val j := Subtype.ext q'.1.property
        · have ht' := congrFun hqq' t
          simpa [insertSample, Function.update_of_ne ht] using ht'
      · have hj := congrFun hqq' j
        simpa [insertSample] using hj
    have hcard := Fintype.card_le_of_injective insertSample hinj
    have hequalSamples : Fintype.card equalSamples =
        (Ω.filter fun ω : Sample => (ω i).val = (ω j).val).card := by
      rw [Fintype.card_subtype]
    rw [Fintype.card_prod, hequalSamples] at hcard
    simpa [edgeCount, sampleCount, i, j] using hcard
  have hcollisionCount (ω : Sample) :
      ((Finset.univ : Finset (Fin k × Fin k)).filter fun p =>
        p.1 < p.2 ∧ (ω p.1).val = (ω p.2).val).card = collisionCount ω := by
    congr 1
    ext p
    simp [pairs]
  have hsumEq : (∑ ω : Sample,
      ((Finset.univ : Finset (Fin k × Fin k)).filter fun p =>
        p.1 < p.2 ∧ (ω p.1).val = (ω p.2).val).card) =
      ∑ p ∈ pairs, (Ω.filter fun ω : Sample => (ω p.1).val = (ω p.2).val).card := by
    calc
      _ = ∑ ω : Sample, collisionCount ω := by
        apply Finset.sum_congr rfl
        intro ω hω
        exact hcollisionCount ω
      _ = ∑ ω : Sample, ∑ p ∈ pairs,
          if (ω p.1).val = (ω p.2).val then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro ω hω
        change (pairs.filter fun p => (ω p.1).val = (ω p.2).val).card = _
        rw [Finset.card_filter]
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro p hp
        exact Finset.sum_boole (fun ω : Sample =>
          (ω p.1).val = (ω p.2).val) Ω
  calc
    _ = (∑ p ∈ pairs,
      (Ω.filter fun ω : Sample => (ω p.1).val = (ω p.2).val).card) * edgeCount := by
      rw [hsumEq]
    _ = ∑ p ∈ pairs,
      (Ω.filter fun ω : Sample => (ω p.1).val = (ω p.2).val).card * edgeCount :=
      Finset.sum_mul ..
    _ ≤ ∑ p ∈ pairs, sampleCount := by
      apply Finset.sum_le_sum
      intro p hp
      exact hcollisionEvent p hp
    _ = pairs.card * sampleCount := by simp [Finset.sum_const]
    _ ≤ k * k * sampleCount := Nat.mul_le_mul_right sampleCount hpairs

/-- the collision estimate.
Fewer than one quarter of all samples have at least an eighth of their indices repeated. -/
private theorem theorem6_repeatBound
    (a b g s k : ℕ) (hk : k = 2 ^ (g - 2 * s))
    (hs : 10 ≤ s) (ha : a + 5 * s ≤ g) (hb : b + 5 * s ≤ g)
    (hab : g + 5 * s ≤ a + b) :
    (theorem6_aux_random_family_repeatBadSamples a b k).card * 4 <
      (Finset.univ : Finset (theorem6_aux_random_family_sampleType a b k)).card := by
  classical
  let Edge := theorem6_aux_random_family_edgeType a b
  let Sample := theorem6_aux_random_family_sampleType a b k
  let bad := theorem6_aux_random_family_repeatBadSamples a b k
  let edgeCount := Fintype.card Edge
  let sampleCount := Fintype.card Sample
  let repeatCount := fun ω : Sample =>
    (theorem6_aux_random_family_repeatIndices a b k ω).card
  let collisionCount := fun ω : Sample =>
    ((Finset.univ : Finset (Fin k × Fin k)).filter fun p =>
      p.1 < p.2 ∧ ((ω p.1).val = (ω p.2).val)).card
  have hcharge (ω : Sample) : repeatCount ω ≤ collisionCount ω := by
    exact theorem6_repeatCharge a b k ω
  have hsumCharge : (∑ ω : Sample, repeatCount ω) ≤ ∑ ω : Sample, collisionCount ω :=
    Finset.sum_le_sum fun ω _ => hcharge ω
  have hcollision :=
    theorem6_averageCollisionBound a b k
  have hcollision' : (∑ ω : Sample, collisionCount ω) * edgeCount ≤
      k * k * sampleCount := by
    simpa only [collisionCount] using hcollision
  have hrepeatAvg : (∑ ω : Sample, repeatCount ω) * edgeCount ≤
      k * k * sampleCount := by
    exact le_trans (Nat.mul_le_mul_right edgeCount hsumCharge) hcollision'
  have hbadMarkov : bad.card * k ≤ 8 * (∑ ω : Sample, repeatCount ω) := by
    calc
      bad.card * k = ∑ ω ∈ bad, k := by simp [Finset.sum_const]
      _ ≤ ∑ ω ∈ bad, 8 * repeatCount ω := by
        apply Finset.sum_le_sum
        intro ω hω
        have hω' : k ≤ 8 * repeatCount ω := by
          simpa [bad, repeatCount, theorem6_aux_random_family_repeatBadSamples,
            Finset.mem_filter] using hω
        exact hω'
      _ ≤ ∑ ω : Sample, 8 * repeatCount ω := by
        calc
          _ = ∑ ω ∈ (Finset.univ : Finset Sample).filter (fun ω => ω ∈ bad),
              8 * repeatCount ω := by simp
          _ = ∑ ω ∈ (Finset.univ : Finset Sample),
              if ω ∈ bad then 8 * repeatCount ω else 0 := by rw [Finset.sum_filter]
          _ ≤ ∑ ω : Sample, 8 * repeatCount ω := by
            apply Finset.sum_le_sum
            intro ω hω
            by_cases hωbad : ω ∈ bad <;> simp [hωbad]
      _ = 8 * (∑ ω : Sample, repeatCount ω) := by rw [← Finset.mul_sum]
  have hgs : 2 * s ≤ g := by omega
  have hExp : g - 2 * s + 5 < a + b := by
    have hsmall : g - 2 * s + 5 < g + 5 * s := by omega
    exact lt_of_lt_of_le hsmall hab
  have hEdgeCount : edgeCount = 2 ^ (a + b) := by
    simp [edgeCount, Edge,
      Fintype.card_coe, Finset.card_product, card_stringsOfLength, ← Nat.pow_add]
  have hEdgeLarge : 32 * k < edgeCount := by
    rw [hEdgeCount, hk]
    calc
      32 * 2 ^ (g - 2 * s) = 2 ^ 5 * 2 ^ (g - 2 * s) := by norm_num
      _ = 2 ^ (g - 2 * s + 5) := by
        rw [← Nat.pow_add]
        congr 1
        omega
      _ < 2 ^ (a + b) := Nat.pow_lt_pow_right (by norm_num) hExp
  have hkpos : 0 < k := by rw [hk]; exact Nat.pow_pos (by norm_num)
  have hedgepos : 0 < edgeCount := by rw [hEdgeCount]; exact Nat.pow_pos (by norm_num)
  have hsamplepos : 0 < sampleCount := by
    dsimp [sampleCount, Sample]
    rw [Fintype.card_fun, Fintype.card_fin]
    exact Nat.pow_pos hedgepos
  have hknpos : 0 < k * edgeCount := Nat.mul_pos hkpos hedgepos
  have hsmall : 32 * (k * k) < k * edgeCount := by
    calc
      32 * (k * k) = (32 * k) * k := by ring
      _ < edgeCount * k := Nat.mul_lt_mul_of_pos_right hEdgeLarge hkpos
      _ = k * edgeCount := Nat.mul_comm _ _
  have hscaled : (bad.card * 4) * (k * edgeCount) ≤
      32 * ((∑ ω : Sample, repeatCount ω) * edgeCount) := by
    calc
      (bad.card * 4) * (k * edgeCount) = (bad.card * k) * (4 * edgeCount) := by ring
      _ ≤ (8 * (∑ ω : Sample, repeatCount ω)) * (4 * edgeCount) :=
        Nat.mul_le_mul_right (4 * edgeCount) hbadMarkov
      _ = 32 * ((∑ ω : Sample, repeatCount ω) * edgeCount) := by ring
  have hscaledlt : (bad.card * 4) * (k * edgeCount) < sampleCount * (k * edgeCount) := by
    calc
      (bad.card * 4) * (k * edgeCount) ≤
          32 * ((∑ ω : Sample, repeatCount ω) * edgeCount) := hscaled
      _ ≤ 32 * (k * k * sampleCount) := Nat.mul_le_mul_left 32 hrepeatAvg
      _ = (32 * (k * k)) * sampleCount := by ring
      _ < (k * edgeCount) * sampleCount := Nat.mul_lt_mul_of_pos_right hsmall hsamplepos
      _ = sampleCount * (k * edgeCount) := by ring
  have hresult : bad.card * 4 < sampleCount :=
    (Nat.mul_lt_mul_right hknpos).1 hscaledlt
  simpa [bad, sampleCount, Sample, Fintype.card_fun, Fintype.card_fin] using hresult

/-- keep the suitable
sampled edges and discard repetitions. -/
private theorem theorem6_keepSample
    (a b g s k : ℕ) (𝓕 : Finset (Finset (BitString × BitString)))
    (ω : theorem6_aux_random_family_sampleType a b k)
    (hk : k = 2 ^ (g - 2 * s))
    (hs : 10 ≤ s) (ha : a + 5 * s ≤ g) (hb : b + 5 * s ≤ g)
    (hab : g + 5 * s ≤ a + b)
    (hFamily : ∀ F ∈ 𝓕,
      2 * ((Finset.univ : Finset (Fin k)).filter fun i => (ω i).val ∈ F).card < k)
    (hUnsuitable : 4 * theorem6_aux_random_family_unsuitableCount a b g k ω < k)
    (hRepeat : 8 * (theorem6_aux_random_family_repeatIndices a b k ω).card < k) :
    ∃ A : Finset (BitString × BitString),
      A ⊆ stringsOfLength a ×ˢ stringsOfLength b ∧ A.card ≤ 2 ^ g ∧
      (∀ x : BitString, (A.filter fun e => e.1 = x).card ≤ 2 ^ (g - a)) ∧
      (∀ y : BitString, (A.filter fun e => e.2 = y).card ≤ 2 ^ (g - b)) ∧
      ∀ F ∈ 𝓕, 2 ^ (g - 3 * s) ≤ (A \ F).card := by
  classical
  let edge : Fin k → BitString × BitString := fun i => (ω i).val
  let selected : Finset (Fin k) := (Finset.univ : Finset (Fin k)).filter fun i =>
    theorem6_aux_random_family_suitable a b g k ω i
  let A : Finset (BitString × BitString) := selected.image edge
  have hkg : k ≤ 2 ^ g := by
    rw [hk]
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have hselected : selected.card ≤ k := by
    dsimp [selected]
    calc
      _ ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = k := by simp
  have hAsub : A ⊆ stringsOfLength a ×ˢ stringsOfLength b := by
    intro e he
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
    exact (ω i).property
  have hAcard : A.card ≤ 2 ^ g := by
    calc
      A.card ≤ selected.card := by simpa [A] using (Finset.card_image_le (f := edge))
      _ ≤ k := hselected
      _ ≤ 2 ^ g := hkg
  have hLeftEq (x : BitString) :
      A.filter (fun e => e.1 = x) =
        (selected.filter (fun i => (edge i).1 = x)).image edge := by
    ext e
    constructor
    · intro he
      obtain ⟨heA, hleft⟩ := Finset.mem_filter.mp he
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp heA
      exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hleft⟩, rfl⟩
    · intro he
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨hi, hleft⟩ := Finset.mem_filter.mp hi
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_image.mpr ⟨i, hi, rfl⟩, hleft⟩
  have hRightEq (y : BitString) :
      A.filter (fun e => e.2 = y) =
        (selected.filter (fun i => (edge i).2 = y)).image edge := by
    ext e
    constructor
    · intro he
      obtain ⟨heA, hright⟩ := Finset.mem_filter.mp he
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp heA
      exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hright⟩, rfl⟩
    · intro he
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨hi, hright⟩ := Finset.mem_filter.mp hi
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_image.mpr ⟨i, hi, rfl⟩, hright⟩
  have hLeftCard (x : BitString) :
      (A.filter (fun e => e.1 = x)).card ≤
        theorem6_aux_random_family_leftCount a b k ω x := by
    rw [hLeftEq]
    apply le_trans Finset.card_image_le
    apply Finset.card_le_card
    intro i hi
    obtain ⟨_, hleft⟩ := Finset.mem_filter.mp hi
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by simpa [edge] using hleft⟩
  have hRightCard (y : BitString) :
      (A.filter (fun e => e.2 = y)).card ≤
        theorem6_aux_random_family_rightCount a b k ω y := by
    rw [hRightEq]
    apply le_trans Finset.card_image_le
    apply Finset.card_le_card
    intro i hi
    obtain ⟨_, hright⟩ := Finset.mem_filter.mp hi
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by simpa [edge] using hright⟩
  have hAleft (x : BitString) : (A.filter (fun e => e.1 = x)).card ≤ 2 ^ (g - a) := by
    by_cases hz : (A.filter (fun e => e.1 = x)).card = 0
    · rw [hz]
      exact Nat.zero_le _
    · have hpos : 0 < (A.filter (fun e => e.1 = x)).card := Nat.pos_of_ne_zero hz
      obtain ⟨e, he⟩ := Finset.card_pos.mp hpos
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp he).1
      have hleft : (edge i).1 = x := (Finset.mem_filter.mp he).2
      have hdegree := (Finset.mem_filter.mp hi).2 |>.1
      change theorem6_aux_random_family_leftCount a b k ω (edge i).1 ≤ _ at hdegree
      rw [hleft] at hdegree
      exact (hLeftCard x).trans hdegree
  have hAright (y : BitString) : (A.filter (fun e => e.2 = y)).card ≤ 2 ^ (g - b) := by
    by_cases hz : (A.filter (fun e => e.2 = y)).card = 0
    · rw [hz]
      exact Nat.zero_le _
    · have hpos : 0 < (A.filter (fun e => e.2 = y)).card := Nat.pos_of_ne_zero hz
      obtain ⟨e, he⟩ := Finset.card_pos.mp hpos
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp he).1
      have hright : (edge i).2 = y := (Finset.mem_filter.mp he).2
      have hdegree := (Finset.mem_filter.mp hi).2 |>.2
      change theorem6_aux_random_family_rightCount a b k ω (edge i).2 ≤ _ at hdegree
      rw [hright] at hdegree
      exact (hRightCard y).trans hdegree
  have hOutside (F : Finset (BitString × BitString)) (hF : F ∈ 𝓕) :
      2 ^ (g - 3 * s) ≤ (A \ F).card := by
    let repeats := theorem6_aux_random_family_repeatIndices a b k ω
    let hits : Finset (Fin k) := (Finset.univ : Finset (Fin k)).filter fun i => edge i ∈ F
    let unsuitable : Finset (Fin k) := (Finset.univ : Finset (Fin k)).filter fun i =>
      ¬ theorem6_aux_random_family_suitable a b g k ω i
    let good : Finset (Fin k) := (Finset.univ : Finset (Fin k)).filter fun i =>
      theorem6_aux_random_family_suitable a b g k ω i ∧
        i ∉ repeats ∧ edge i ∉ F
    have hComplement : (Finset.univ \ good) ⊆ unsuitable ∪ repeats ∪ hits := by
      intro i hi
      have hiuniv := (Finset.mem_sdiff.mp hi).1
      have hnotgood := (Finset.mem_sdiff.mp hi).2
      by_cases hsuit : theorem6_aux_random_family_suitable a b g k ω i
      · by_cases hrep : i ∈ repeats
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hrep)))
        · by_cases hhit : edge i ∈ F
          · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hiuniv, hhit⟩))
          · exact (hnotgood (Finset.mem_filter.mpr ⟨hiuniv, hsuit, hrep, hhit⟩)).elim
      · exact Finset.mem_union.mpr
          (Or.inl (Finset.mem_union.mpr
            (Or.inl (Finset.mem_filter.mpr ⟨hiuniv, hsuit⟩))))
    have hComplementCard : (Finset.univ \ good).card ≤ unsuitable.card + repeats.card + hits.card :=
        by
      calc
        (Finset.univ \ good).card ≤ (unsuitable ∪ repeats ∪ hits).card :=
            Finset.card_le_card hComplement
        _ ≤ unsuitable.card + repeats.card + hits.card := by
          calc
            _ ≤ (unsuitable ∪ repeats).card + hits.card := Finset.card_union_le _ _
            _ ≤ unsuitable.card + repeats.card + hits.card :=
              Nat.add_le_add_right (Finset.card_union_le _ _) _
    have hUnsuitableCard : unsuitable.card =
        theorem6_aux_random_family_unsuitableCount a b g k ω := by
      simp [unsuitable, theorem6_aux_random_family_unsuitableCount]
    have hHits : 2 * hits.card < k := by
      simpa [hits, edge] using hFamily F hF
    have hRepeats : 8 * repeats.card < k := by
      simpa [repeats] using hRepeat
    have hLoss : 8 * (unsuitable.card + repeats.card + hits.card) < 7 * k := by
      rw [hUnsuitableCard]
      omega
    have hComplementScaled := Nat.mul_le_mul_left 8 hComplementCard
    have hGoodTotal : (Finset.univ \ good).card + good.card = k := by
      simpa using (Finset.card_sdiff_add_card_eq_card (Finset.subset_univ good))
    have hGoodLarge : k < 8 * good.card := by
      omega
    have hg3 : 3 * s ≤ g := by omega
    have hexp : (g - 3 * s) + 3 ≤ g - 2 * s := by omega
    have hPowScale : 8 * 2 ^ (g - 3 * s) ≤ k := by
      calc
        8 * 2 ^ (g - 3 * s) = 2 ^ ((g - 3 * s) + 3) := by
          calc
            8 * 2 ^ (g - 3 * s) = 2 ^ (g - 3 * s) * 2 ^ 3 := by norm_num [Nat.mul_comm]
            _ = 2 ^ ((g - 3 * s) + 3) := by rw [pow_add]
        _ ≤ 2 ^ (g - 2 * s) := Nat.pow_le_pow_right (by norm_num) hexp
        _ = k := hk.symm
    have hTargetGood : 2 ^ (g - 3 * s) ≤ good.card := by omega
    have hGoodSelected : good ⊆ selected := by
      intro i hi
      rw [Finset.mem_filter] at hi ⊢
      exact ⟨Finset.mem_univ _, (hi.2).1⟩
    have hImageSub : good.image edge ⊆ A \ F := by
      intro e he
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
      refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨i, hGoodSelected hi, rfl⟩
      · exact (Finset.mem_filter.mp hi).2.2.2
    have hImageInj : Set.InjOn edge good := by
      intro i hi j hj hij
      have hiGood := (Finset.mem_filter.mp hi).2
      have hjGood := (Finset.mem_filter.mp hj).2
      by_contra hne
      rcases lt_or_gt_of_ne hne with hij' | hji'
      · have hjRepeat : j ∈ repeats := by
          change j ∈ (Finset.univ : Finset (Fin k)).filter
            (fun t => ∃ l : Fin k, l < t ∧ (ω l).val = (ω t).val)
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, i, hij', by simpa [edge] using hij⟩
        exact hjGood.2.1 hjRepeat
      · have hiRepeat : i ∈ repeats := by
          change i ∈ (Finset.univ : Finset (Fin k)).filter
            (fun t => ∃ l : Fin k, l < t ∧ (ω l).val = (ω t).val)
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, hji', by simpa [edge] using hij.symm⟩
        exact hiGood.2.1 hiRepeat
    have hImageCard : (good.image edge).card = good.card := Finset.card_image_iff.mpr hImageInj
    calc
      2 ^ (g - 3 * s) ≤ good.card := hTargetGood
      _ = (good.image edge).card := hImageCard.symm
      _ ≤ (A \ F).card := Finset.card_le_card hImageSub
  exact ⟨A, hAsub, hAcard, hAleft, hAright, hOutside⟩

/-- For every family `𝓕` of at most `2 ^ (2 ^ (g - 2s - 1))` sets of at most
`2 ^ (g + 3s)` pairs each, under the margins `a + 5s ≤ g`, `b + 5s ≤ g`, `g + 5s ≤ a + b`, `s ≥ 10`,
there is `A ⊆ S₁ × S₂` (strings of lengths `a, b`) with `|A| ≤ 2 ^ g`, left degrees
`≤ 2 ^ (g - a)`, right degrees `≤ 2 ^ (g - b)`, and at least `2 ^ (g - 3s)` edges outside each
`F ∈ 𝓕`.  (Take `k = 2 ^ (g - 2s)` independent uniform edges of `S₁ × S₂` and keep the suitable
ones, those whose endpoints have degree at most `2 ^ (g - a)`, `2 ^ (g - b)` in the sample.  A
sampled edge lies in a fixed `F` with probability `≤ 2 ^ (g + 3s - a - b) ≤ 2 ^ (-2s)`, so at least
`k/2` samples fall into `F` with probability `≤ 2 ^ k · 2 ^ (-sk)`; the union bound over
`|𝓕| ≤ 2 ^ (k/2)` sets applies; by Markov's inequality, with probability `≥ 1/2` fewer than `k/4`
samples are unsuitable and fewer than `k/8` samples are repeated; this leaves at least
`k/8 ≥ 2 ^ (g - 3s)` distinct suitable edges outside each `F`.) -/
private theorem theorem6_aux_random_family (a b g s : ℕ)
    (𝓕 : Finset (Finset (BitString × BitString)))
    (h𝓕 : 𝓕.card ≤ 2 ^ (2 ^ (g - 2 * s - 1))) (hF : ∀ F ∈ 𝓕, F.card ≤ 2 ^ (g + 3 * s))
    (hs : 10 ≤ s) (ha : a + 5 * s ≤ g) (hb : b + 5 * s ≤ g) (hab : g + 5 * s ≤ a + b) :
    ∃ A : Finset (BitString × BitString),
      A ⊆ stringsOfLength a ×ˢ stringsOfLength b ∧ A.card ≤ 2 ^ g ∧
      (∀ x : BitString, (A.filter fun e => e.1 = x).card ≤ 2 ^ (g - a)) ∧
      (∀ y : BitString, (A.filter fun e => e.2 = y).card ≤ 2 ^ (g - b)) ∧
      ∀ F ∈ 𝓕, 2 ^ (g - 3 * s) ≤ (A \ F).card := by
  classical
  let k := 2 ^ (g - 2 * s)
  let Ω : Finset (theorem6_aux_random_family_sampleType a b k) := Finset.univ
  let badFamily := theorem6_aux_random_family_familyBadSamples a b k 𝓕
  let badUnsuitable := theorem6_aux_random_family_unsuitableBadSamples a b g k
  let badRepeat := theorem6_aux_random_family_repeatBadSamples a b k
  have hk : k = 2 ^ (g - 2 * s) := rfl
  have hFamilyCount := theorem6_familyBound
    a b g s k 𝓕 hk h𝓕 hF hs ha hab
  have hUnsuitableCount := theorem6_unsuitableBound
    a b g s k hk hs ha hb
  have hRepeatCount := theorem6_repeatBound
    a b g s k hk hs ha hb hab
  have hFamilyQuarter : badFamily.card * 4 < Ω.card := by
    simpa [badFamily, Ω] using hFamilyCount
  have hUnsuitableQuarter : badUnsuitable.card * 4 < Ω.card := by
    simpa [badUnsuitable, Ω] using hUnsuitableCount
  have hRepeatQuarter : badRepeat.card * 4 < Ω.card := by
    simpa [badRepeat, Ω] using hRepeatCount
  have hsum : badFamily.card + badUnsuitable.card + badRepeat.card < Ω.card := by
    omega
  have hunion : (badFamily ∪ badUnsuitable ∪ badRepeat).card ≤
      badFamily.card + badUnsuitable.card + badRepeat.card := by
    calc
      (badFamily ∪ badUnsuitable ∪ badRepeat).card ≤
          (badFamily ∪ badUnsuitable).card + badRepeat.card :=
            Finset.card_union_le (badFamily ∪ badUnsuitable) badRepeat
      _ ≤ badFamily.card + badUnsuitable.card + badRepeat.card := by
          exact Nat.add_le_add_right (Finset.card_union_le badFamily badUnsuitable) _
  have hbad : (badFamily ∪ badUnsuitable ∪ badRepeat).card < Ω.card :=
    lt_of_le_of_lt hunion hsum
  obtain ⟨ω, hωΩ, hωnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hbad
  have hωnotFamily : ω ∉ badFamily := by
    intro hmem
    apply hωnot
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hmem)))
  have hωnotUnsuitable : ω ∉ badUnsuitable := by
    intro hmem
    apply hωnot
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hmem)))
  have hωnotRepeat : ω ∉ badRepeat := by
    intro hmem
    apply hωnot
    exact Finset.mem_union.mpr (Or.inr hmem)
  have hFamilyGood : ∀ F ∈ 𝓕,
      2 * ((Finset.univ : Finset (Fin k)).filter fun i => (ω i).val ∈ F).card < k := by
    intro F hFm
    by_contra hnot
    have hbadHit : k ≤ 2 * ((Finset.univ : Finset (Fin k)).filter
        (fun i => (ω i).val ∈ F)).card := Nat.le_of_not_gt hnot
    apply hωnotFamily
    simp only [badFamily, theorem6_aux_random_family_familyBadSamples,
      Finset.mem_filter]
    exact ⟨Finset.mem_univ _, ⟨F, hFm, hbadHit⟩⟩
  have hUnsuitableGood :
      4 * theorem6_aux_random_family_unsuitableCount a b g k ω < k := by
    by_contra hnot
    have hbadCount : k ≤ 4 * theorem6_aux_random_family_unsuitableCount a b g k ω :=
      Nat.le_of_not_gt hnot
    apply hωnotUnsuitable
    simp only [badUnsuitable, theorem6_aux_random_family_unsuitableBadSamples,
      Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hbadCount⟩
  have hRepeatGood :
      8 * (theorem6_aux_random_family_repeatIndices a b k ω).card < k := by
    by_contra hnot
    have hbadCount :
        k ≤ 8 * (theorem6_aux_random_family_repeatIndices a b k ω).card :=
      Nat.le_of_not_gt hnot
    apply hωnotRepeat
    simp only [badRepeat, theorem6_aux_random_family_repeatBadSamples,
      Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hbadCount⟩
  exact theorem6_keepSample
    a b g s k 𝓕 ω hk hs ha hb hab hFamilyGood hUnsuitableGood hRepeatGood

/-- for every finite set `R` of at most `2 ^ (g + s)` strings, under the margins
`a + 5s ≤ g`, `b + 5s ≤ g`, `g + 5s ≤ a + b`, `g + s + 1 ≤ 2 ^ s`, `s ≥ 10`, a graph with the
property `theorem6_GoodGraph a b g s R` exists.  (Take `2 ^ (g - 2s)` independent uniform edges of
`S₁ × S₂` and keep the suitable ones.  For a fixed pair of nearness relations an edge is spoiled
with probability `≤ 2 ^ (g + 3s - a - b) ≤ 2 ^ (-2s)`; only the restrictions of `N₁, N₂` to
`S₁ × π₁(R)`, `S₂ × π₂(R)` matter, and there are at most `2 ^ (2 ^ (g - 2s - 1))` of them, so a
union bound applies; Markov's inequality bounds the unsuitable edges and the repeated edges.) -/
private theorem theorem6_random_graph (a b g s : ℕ) (R : Finset BitString)
    (hR : R.card ≤ 2 ^ (g + s)) (hs : 10 ≤ s) (hgs : g + s + 1 ≤ 2 ^ s)
    (ha : a + 5 * s ≤ g) (hb : b + 5 * s ≤ g) (hab : g + 5 * s ≤ a + b) :
    ∃ A : Finset (BitString × BitString), theorem6_GoodGraph a b g s R A := by
  classical
  obtain ⟨𝓕, h𝓕card, h𝓕size, h𝓕cover⟩ :=
    theorem6_aux_spoiled_family a b g s R hR hs hgs ha hb
  obtain ⟨A, hAsub, hAcard, hdeg1, hdeg2, hAF⟩ :=
    theorem6_aux_random_family a b g s 𝓕 h𝓕card h𝓕size hs ha hb hab
  refine ⟨A, hAsub, hAcard, hdeg1, hdeg2, fun N₁ N₂ hN₁ hN₂ => ?_⟩
  obtain ⟨F, hF𝓕, hFcov⟩ := h𝓕cover N₁ N₂ hN₁ hN₂
  refine (hAF F hF𝓕).trans (Finset.card_le_card ?_)
  intro e he
  rw [Finset.mem_sdiff] at he
  rw [Finset.mem_filter]
  exact ⟨he.1, fun hsp => he.2 (hFcov e (hAsub he.1) hsp)⟩

/-- The finite list of pair codes for the two length-bounded vertex sets. -/
private def theorem6_edge_codes
    (ab : ℕ × ℕ) : List BitString :=
  (allStrings ab.1).flatMap fun x =>
    (allStrings ab.2).map fun y => pairCode x y

/-- The candidate graph codes, obtained from all sublists of the finite edge list. -/
private def theorem6_candidate_list
    (p : ℕ × ℕ × ℕ × ℕ × BitString) : List BitString :=
  ((theorem6_edge_codes
    (p.1, p.2.1)).sublists).map
    (fun L => finsetListCode L.toFinset)

/-- The finite relations on `S × Y` satisfying both degree bounds. -/
private noncomputable def theorem6_restriction_decider_nearRelations
    (S Y : Finset BitString) (s : ℕ) : Finset (Finset (BitString × BitString)) := by
  classical
  exact ((S ×ˢ Y).powerset).filter fun N =>
    (∀ x ∈ S, (N.filter fun e => e.1 = x).card ≤ 2 ^ s) ∧
    (∀ y ∈ Y, (N.filter fun e => e.2 = y).card ≤ 2 ^ s)

/-- The finite version of the graph test, where it suffices to check near relations restricted to
the decoded projections of `R`. -/
private noncomputable def theorem6_restriction_decider_finiteGoodGraph
    (a b g s : ℕ) (R : Finset BitString) (A : Finset (BitString × BitString)) : Prop := by
  classical
  exact A ⊆ stringsOfLength a ×ˢ stringsOfLength b ∧ A.card ≤ 2 ^ g ∧
    (∀ x ∈ stringsOfLength a, (A.filter fun e => e.1 = x).card ≤ 2 ^ (g - a)) ∧
    (∀ y ∈ stringsOfLength b, (A.filter fun e => e.2 = y).card ≤ 2 ^ (g - b)) ∧
    ∀ N₁ ∈ theorem6_restriction_decider_nearRelations
        (stringsOfLength a) (R.image decodeFirst) s,
      ∀ N₂ ∈ theorem6_restriction_decider_nearRelations
        (stringsOfLength b) (R.image decodeSecond) s,
        2 ^ (g - 3 * s) ≤ (A.filter fun e =>
          ¬ ∃ y₁ y₂ : BitString, pairCode y₁ y₂ ∈ R ∧
            (e.1, y₁) ∈ N₁ ∧ (e.2, y₂) ∈ N₂).card

/-- Decode a graph-code list by interpreting each item as a pair code. -/
private def theorem6_restriction_decider_decodeGraph
    (w : BitString) : Finset (BitString × BitString) :=
  ((decodeListCode w).map fun z => (decodeFirst z, decodeSecond z)).toFinset

/-- The Boolean test evaluates the finite graph conditions on the decoded code, and rejects
noncanonical graph codes. -/
private noncomputable def theorem6_restriction_decider_finiteTest :
    ((ℕ × ℕ × ℕ × ℕ × BitString) × BitString) → Bool := by
  classical
  exact fun q =>
    let p := q.1
    let w := q.2
    let R := (decodeListCode p.2.2.2.2).toFinset
    let A := theorem6_restriction_decider_decodeGraph w
    decide (theorem6_graphCode A = w ∧
      theorem6_restriction_decider_finiteGoodGraph
        p.1 p.2.1 p.2.2.1 p.2.2.2.1 R A)

private theorem theorem6_finite_relation_is_near
    (S Y : Finset BitString) (s : ℕ)
    (N : Finset (BitString × BitString))
    (hN : N ∈ theorem6_restriction_decider_nearRelations
      S Y s) :
    theorem6_IsNearness S s (fun x y => (x, y) ∈ N) := by
  classical
  change N ∈ ((S ×ˢ Y).powerset).filter (fun N =>
    (∀ x ∈ S, (N.filter fun e => e.1 = x).card ≤ 2 ^ s) ∧
    (∀ y ∈ Y, (N.filter fun e => e.2 = y).card ≤ 2 ^ s)) at hN
  have hsub : N ⊆ S ×ˢ Y := Finset.mem_powerset.mp (Finset.mem_filter.mp hN).1
  have hdeg := (Finset.mem_filter.mp hN).2
  constructor
  · intro x hx F hF
    calc
      F.card = (F.image fun y => (x, y)).card := by
        symm
        apply Finset.card_image_of_injective
        intro y z hyz
        exact congrArg Prod.snd hyz
      _ ≤ (N.filter fun e => e.1 = x).card := Finset.card_le_card (by
        intro e he
        rcases Finset.mem_image.mp he with ⟨y, hy, rfl⟩
        simp only [Finset.mem_filter]
        exact ⟨hF y hy, by simp⟩)
      _ ≤ 2 ^ s := hdeg.1 x hx
  · intro y F hFsub hF
    calc
      F.card = (F.image fun x => (x, y)).card := by
        symm
        apply Finset.card_image_of_injective
        intro x z hxz
        exact congrArg Prod.fst hxz
      _ ≤ (N.filter fun e => e.2 = y).card := Finset.card_le_card (by
        intro e he
        rcases Finset.mem_image.mp he with ⟨x, hx, rfl⟩
        simp only [Finset.mem_filter]
        exact ⟨hF x hx, by simp⟩)
      _ ≤ 2 ^ s := by
        by_cases hy : y ∈ Y
        · exact hdeg.2 y hy
        · have hempty : N.filter (fun e => e.2 = y) = ∅ := by
            apply Finset.filter_eq_empty_iff.mpr
            intro e he hey
            exact hy (by simpa [hey] using (Finset.mem_product.mp (hsub he)).2)
          simp [hempty]

open scoped Classical in
private theorem theorem6_restrict_near_relation
    (S Y : Finset BitString) (s : ℕ)
    (N : BitString → BitString → Prop)
    (hN : theorem6_IsNearness S s N) :
    (S ×ˢ Y).filter (fun e => N e.1 e.2) ∈
      theorem6_restriction_decider_nearRelations
        S Y s := by
  classical
  let M := (S ×ˢ Y).filter (fun e => N e.1 e.2)
  have hprops (e : BitString × BitString) (he : e ∈ M) :
      e.1 ∈ S ∧ e.2 ∈ Y ∧ N e.1 e.2 := by
    change e ∈ (S ×ˢ Y).filter (fun e => N e.1 e.2) at he
    rcases Finset.mem_filter.mp he with ⟨heprod, hN⟩
    rcases Finset.mem_product.mp heprod with ⟨heS, heY⟩
    exact ⟨heS, heY, hN⟩
  change M ∈ ((S ×ˢ Y).powerset).filter (fun M =>
    (∀ x ∈ S, (M.filter fun e => e.1 = x).card ≤ 2 ^ s) ∧
    (∀ y ∈ Y, (M.filter fun e => e.2 = y).card ≤ 2 ^ s))
  apply Finset.mem_filter.mpr
  constructor
  · exact Finset.mem_powerset.mpr (Finset.filter_subset _ _)
  constructor
  · intro x hx
    let F := M.filter fun e => e.1 = x
    have hcard : (F.image Prod.snd).card = F.card := by
      apply Finset.card_image_iff.mpr
      intro e he e' he' hee'
      apply Prod.ext
      · exact (Finset.mem_filter.mp he).2 |>.trans
          ((Finset.mem_filter.mp he').2).symm
      · exact hee'
    have hrel : ∀ y ∈ F.image Prod.snd, N x y := by
      intro y hy
      rcases Finset.mem_image.mp hy with ⟨e, he, rfl⟩
      have hp := hprops e (Finset.mem_filter.mp he).1
      have hxeq := (Finset.mem_filter.mp he).2
      simpa [hxeq] using hp.2.2
    calc
      (M.filter fun e => e.1 = x).card = F.card := by rfl
      _ = (F.image Prod.snd).card := hcard.symm
      _ ≤ 2 ^ s := hN.1 x hx (F.image Prod.snd) hrel
  · intro y hy
    let F := M.filter fun e => e.2 = y
    have hcard : (F.image Prod.fst).card = F.card := by
      apply Finset.card_image_iff.mpr
      intro e he e' he' hee'
      apply Prod.ext
      · exact hee'
      · exact (Finset.mem_filter.mp he).2 |>.trans
          ((Finset.mem_filter.mp he').2).symm
    have hsubset : F.image Prod.fst ⊆ S := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨e, he, rfl⟩
      exact (hprops e (Finset.mem_filter.mp he).1).1
    have hrel : ∀ x ∈ F.image Prod.fst, N x y := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨e, he, rfl⟩
      have hp := hprops e (Finset.mem_filter.mp he).1
      have hyeq := (Finset.mem_filter.mp he).2
      simpa [hyeq] using hp.2.2
    calc
      (M.filter fun e => e.2 = y).card = F.card := by rfl
      _ = (F.image Prod.fst).card := hcard.symm
      _ ≤ 2 ^ s := hN.2 y (F.image Prod.fst) hsubset hrel

/-- Restricting near relations to the finite decoded projections preserves exactly the
surviving-edge condition, and finite relations extend by false to full near relations. -/
private theorem theorem6_restriction_equivalence
    (a b g s : ℕ) (R : Finset BitString) (A : Finset (BitString × BitString)) :
    theorem6_GoodGraph a b g s R A ↔
      theorem6_restriction_decider_finiteGoodGraph
        a b g s R A := by
  classical
  unfold theorem6_GoodGraph theorem6_IsNearness
    theorem6_restriction_decider_finiteGoodGraph
  constructor
  · rintro ⟨hSub, hCard, hDeg₁, hDeg₂, hSurvives⟩
    refine ⟨hSub, hCard, ?_, ?_, ?_⟩
    · intro x hx
      exact hDeg₁ x
    · intro y hy
      exact hDeg₂ y
    · intro N₁ hN₁ N₂ hN₂
      have hNear₁ :=
        theorem6_finite_relation_is_near
          (stringsOfLength a) (R.image decodeFirst) s N₁ hN₁
      have hNear₂ :=
        theorem6_finite_relation_is_near
          (stringsOfLength b) (R.image decodeSecond) s N₂ hN₂
      simpa using hSurvives (fun x y => (x, y) ∈ N₁) (fun x y => (x, y) ∈ N₂)
        hNear₁ hNear₂
  · rintro ⟨hSub, hCard, hDeg₁, hDeg₂, hSurvives⟩
    refine ⟨hSub, hCard, ?_, ?_, ?_⟩
    · intro x
      by_cases hx : x ∈ stringsOfLength a
      · exact hDeg₁ x hx
      · have hEmpty : A.filter (fun e => e.1 = x) = ∅ := by
          apply Finset.filter_eq_empty_iff.mpr
          intro e he hEq
          have heSupport := Finset.mem_product.mp (hSub he)
          exact hx (by simpa [hEq] using heSupport.1)
        simp [hEmpty]
    · intro y
      by_cases hy : y ∈ stringsOfLength b
      · exact hDeg₂ y hy
      · have hEmpty : A.filter (fun e => e.2 = y) = ∅ := by
          apply Finset.filter_eq_empty_iff.mpr
          intro e he hEq
          have heSupport := Finset.mem_product.mp (hSub he)
          exact hy (by simpa [hEq] using heSupport.2)
        simp [hEmpty]
    · intro N₁ N₂ hN₁ hN₂
      let N₁' := (stringsOfLength a ×ˢ R.image decodeFirst).filter
        (fun e => N₁ e.1 e.2)
      let N₂' := (stringsOfLength b ×ˢ R.image decodeSecond).filter
        (fun e => N₂ e.1 e.2)
      have hN₁' :=
        theorem6_restrict_near_relation
          (stringsOfLength a) (R.image decodeFirst) s N₁ hN₁
      have hN₂' :=
        theorem6_restrict_near_relation
          (stringsOfLength b) (R.image decodeSecond) s N₂ hN₂
      have hFinite := hSurvives N₁' hN₁' N₂' hN₂'
      have hBad (e : BitString × BitString) (he : e ∈ A) :
          (∃ y₁ y₂ : BitString, pairCode y₁ y₂ ∈ R ∧
            (e.1, y₁) ∈ N₁' ∧ (e.2, y₂) ∈ N₂') ↔
          (∃ y₁ y₂ : BitString, pairCode y₁ y₂ ∈ R ∧
            N₁ e.1 y₁ ∧ N₂ e.2 y₂) := by
        constructor
        · rintro ⟨y₁, y₂, hR, h₁, h₂⟩
          have h₁' : (e.1, y₁) ∈
              (stringsOfLength a ×ˢ R.image decodeFirst).filter
                (fun z => N₁ z.1 z.2) := by
            simpa [N₁'] using h₁
          have h₂' : (e.2, y₂) ∈
              (stringsOfLength b ×ˢ R.image decodeSecond).filter
                (fun z => N₂ z.1 z.2) := by
            simpa [N₂'] using h₂
          exact ⟨y₁, y₂, hR, (Finset.mem_filter.mp h₁').2,
            (Finset.mem_filter.mp h₂').2⟩
        · rintro ⟨y₁, y₂, hR, h₁, h₂⟩
          have heSupport := Finset.mem_product.mp (hSub he)
          have hy₁ : y₁ ∈ R.image decodeFirst :=
            Finset.mem_image.mpr ⟨pairCode y₁ y₂, hR, decodeFirst_pairCode y₁ y₂⟩
          have hy₂ : y₂ ∈ R.image decodeSecond :=
            Finset.mem_image.mpr ⟨pairCode y₁ y₂, hR, decodeSecond_pairCode y₁ y₂⟩
          have h₁' : (e.1, y₁) ∈
              (stringsOfLength a ×ˢ R.image decodeFirst).filter
                (fun z => N₁ z.1 z.2) := by
            apply Finset.mem_filter.mpr
            exact ⟨Finset.mem_product.mpr ⟨heSupport.1, hy₁⟩, h₁⟩
          have h₂' : (e.2, y₂) ∈
              (stringsOfLength b ×ˢ R.image decodeSecond).filter
                (fun z => N₂ z.1 z.2) := by
            apply Finset.mem_filter.mpr
            exact ⟨Finset.mem_product.mpr ⟨heSupport.2, hy₂⟩, h₂⟩
          exact ⟨y₁, y₂, hR, by simpa [N₁'] using h₁', by simpa [N₂'] using h₂'⟩
      have hFilterEq :
          A.filter (fun e => ¬ ∃ y₁ y₂ : BitString, pairCode y₁ y₂ ∈ R ∧
            (e.1, y₁) ∈ N₁' ∧ (e.2, y₂) ∈ N₂') =
          A.filter (fun e => ¬ ∃ y₁ y₂ : BitString, pairCode y₁ y₂ ∈ R ∧
            N₁ e.1 y₁ ∧ N₂ e.2 y₂) := by
        ext e
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨he, hnot⟩
          exact ⟨he, fun hbad => hnot ((hBad e he).2 hbad)⟩
        · rintro ⟨he, hnot⟩
          exact ⟨he, fun hbad => hnot ((hBad e he).1 hbad)⟩
      have hFinite' : 2 ^ (g - 3 * s) ≤
          (A.filter (fun e => ¬ ∃ y₁ y₂ : BitString, pairCode y₁ y₂ ∈ R ∧
            (e.1, y₁) ∈ N₁' ∧ (e.2, y₂) ∈ N₂')).card := by
        simpa [N₁', N₂'] using hFinite
      calc
        2 ^ (g - 3 * s) ≤
            (A.filter (fun e => ¬ ∃ y₁ y₂ : BitString, pairCode y₁ y₂ ∈ R ∧
              (e.1, y₁) ∈ N₁' ∧ (e.2, y₂) ∈ N₂')).card := hFinite'
        _ = (A.filter (fun e => ¬ ∃ y₁ y₂ : BitString, pairCode y₁ y₂ ∈ R ∧
              N₁ e.1 y₁ ∧ N₂ e.2 y₂)).card := congrArg Finset.card hFilterEq

/-- decoding a canonical graph code recovers the represented finite graph. -/
private theorem theorem6_decode_graphCode
    (A : Finset (BitString × BitString)) :
    theorem6_restriction_decider_decodeGraph
      (theorem6_graphCode A) = A := by
  classical
  apply Finset.ext
  intro e
  cases e with
  | mk x y =>
    simp [theorem6_restriction_decider_decodeGraph,
      theorem6_graphCode, finsetListCode, decodeListCode_listCode,
      decodeFirst_pairCode, decodeSecond_pairCode]

/-- membership in a finite list is a primitive recursive relation. -/
private theorem theorem6_list_mem
    {β : Type*} [Primcodable β] :
    PrimrecRel (fun (L : List β) (x : β) => x ∈ L) := by
  exact PrimrecRel.of_eq (Primrec.eq.exists_mem_list) (fun L x => by simp)

/-- Bounded universal quantification over a primitive recursive list preserves primitive
recursiveness. -/
private theorem theorem6_list_forall
    {α β : Type*} [Primcodable α] [Primcodable β]
    {L : α → List β} {P : α → β → Prop}
    (hL : Primrec L) (hP : PrimrecRel P) :
    PrimrecPred (fun a => ∀ b ∈ L a, P a b) := by
  exact hP.swap.forall_mem_list.comp hL Primrec.id

/-- bounded existential quantification over a primitive recursive list preserves primitive
recursiveness. -/
private theorem theorem6_list_exists
    {α β : Type*} [Primcodable α] [Primcodable β]
    {L : α → List β} {P : α → β → Prop}
    (hL : Primrec L) (hP : PrimrecRel P) :
    PrimrecPred (fun a => ∃ b ∈ L a, P a b) := by
  exact hP.swap.exists_mem_list.comp hL Primrec.id

/-- removing duplicate entries of a list is primitive recursive for every primitive codable type. -/
private theorem theorem6_dedup
    {β : Type*} [Primcodable β] [DecidableEq β] :
    Primrec (fun L : List β => L.dedup) := by
  have hmem : PrimrecPred (fun q : List β × (β × List β) => q.2.1 ∈ q.2.2) :=
    theorem6_list_mem.comp
      (Primrec.snd.comp Primrec.snd) (Primrec.fst.comp Primrec.snd)
  have hstep : Primrec₂ (fun (_ : List β) (q : β × List β) =>
      if q.1 ∈ q.2 then q.2 else q.1 :: q.2) :=
    Primrec.ite hmem (Primrec.snd.comp Primrec.snd)
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd))
  refine (Primrec.list_foldr Primrec.id (Primrec.const []) hstep).of_eq ?_
  intro L
  induction L with
  | nil => rfl
  | cons x L ih =>
      change List.foldr (fun b s => if b ∈ s then s else b :: s) [] L = L.dedup at ih
      change List.foldr (fun b s => if b ∈ s then s else b :: s) [] (x :: L) = (x :: L).dedup
      rw [List.foldr_cons, ih, List.dedup_cons]
      by_cases hx : x ∈ L <;> simp [hx]

/-- The number of distinct entries satisfying a primitive recursive predicate is primitive
recursive. This counts a finite set, so repetitions in the input list have no effect. -/
private theorem theorem6_filter_card
    {α β : Type*} [Primcodable α] [Primcodable β] [DecidableEq β]
    {L : α → List β} {P : α → β → Prop} [DecidableRel P]
    (hL : Primrec L) (hP : PrimrecRel P) :
    Primrec (fun a => ((L a).toFinset.filter (P a)).card) := by
  have hfilter : Primrec (fun a => (L a).dedup.filter (fun b => decide (P a b))) :=
    Primrec.list_filter (theorem6_dedup.comp hL) hP.decide
  refine (Primrec.list_length.comp hfilter).of_eq ?_
  intro a
  rw [← List.toFinset_card_of_nodup ((List.nodup_dedup _).filter _)]
  congr 1
  ext b
  simp

/-- the canonical graph re-encoding, including deduplication and sorting of pair codes, is primitive
recursive. -/
private theorem theorem6_canonical_code :
    Primrec (fun w : BitString => theorem6_graphCode
      (theorem6_restriction_decider_decodeGraph w)) := by
  classical
  have hpair : Primrec (fun z : BitString => pairCode (decodeFirst z) (decodeSecond z)) :=
    CodedFiniteDistribution.pairCode_primrec.comp
      CodedFiniteDistribution.decodeFirst_primrec
      CodedFiniteDistribution.decodeSecond_primrec
  have hmapped : Primrec (fun w : BitString =>
      (decodeListCode w).map fun z => pairCode (decodeFirst z) (decodeSecond z)) :=
    Primrec.list_map decodeListCode_primrec (hpair.comp Primrec.snd).to₂
  have hcanonical := canonicalFinsetList_toFinset_primrec.comp hmapped
  apply (listCode_primrec.comp hcanonical).of_eq
  intro w
  unfold theorem6_graphCode finsetListCode
  apply congrArg listCode
  apply congrArg canonicalFinsetList
  ext code
  simp [theorem6_restriction_decider_decodeGraph,
    Finset.mem_image, List.mem_toFinset, List.mem_map]

/-- finite vertex-degree bounds are primitive recursive, uniformly in the edge list, vertex list,
endpoint projection, and numerical degree bound. -/
private theorem theorem6_degree
    {α β : Type*} [Primcodable α] [Primcodable β] [DecidableEq β]
    {A : α → List β} {X : α → List BitString} {f : β → BitString} {d : α → ℕ}
    (hA : Primrec A) (hX : Primrec X) (hf : Primrec f) (hd : Primrec d) :
    PrimrecPred (fun a => ∀ x ∈ X a,
      ((A a).toFinset.filter (fun e => f e = x)).card ≤ d a) := by
  have hcount : Primrec (fun q : α × BitString =>
      ((A q.1).toFinset.filter (fun e => f e = q.2)).card) :=
    theorem6_filter_card (hA.comp Primrec.fst)
      (Primrec.eq.comp (hf.comp Primrec.snd) (Primrec.snd.comp Primrec.fst))
  exact theorem6_list_forall hX
    (Primrec.nat_le.comp hcount (hd.comp Primrec.fst))

/-- The powers of two used in the finite degree and cardinality thresholds are primitive
recursive. -/
private theorem theorem6_pow2 :
    Primrec (fun n : ℕ => 2 ^ n) := by
  have hpow : Primrec₂ (fun a b : ℕ => a ^ b) := Primrec.nat_iff.mpr Nat.Primrec.pow
  exact hpow.comp (Primrec.const 2) Primrec.id

/-- enumerate every bounded-degree relation on a finite rectangle by filtering the sublists of its
edge list. The contract gives both primitive recursiveness and exact membership; it makes no
assumption that either input list is duplicate-free. -/
private theorem theorem6_relation_enumeration :
    ∃ E : (List BitString × List BitString × ℕ) → List (List (BitString × BitString)),
      Primrec E ∧ ∀ (S Y : List BitString) (s : ℕ) (N : Finset (BitString × BitString)),
        N ∈ theorem6_restriction_decider_nearRelations
          S.toFinset Y.toFinset s ↔
        ∃ L ∈ E (S, Y, s), L.toFinset = N := by
  classical
  let E : (List BitString × List BitString × ℕ) → List (List (BitString × BitString)) := fun p =>
    (p.1.product p.2.1).sublists.filter fun L => decide
      ((∀ x ∈ p.1, (L.toFinset.filter fun e => e.1 = x).card ≤ 2 ^ p.2.2) ∧
       (∀ y ∈ p.2.1, (L.toFinset.filter fun e => e.2 = y).card ≤ 2 ^ p.2.2))
  have hprod : Primrec (fun p : List BitString × List BitString × ℕ =>
      p.1.product p.2.1) := by
    apply Primrec.list_flatMap Primrec.fst
    apply Primrec.list_map (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
    exact (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂
  have hbound : Primrec (fun q : (List BitString × List BitString × ℕ) ×
      List (BitString × BitString) => 2 ^ q.1.2.2) :=
    theorem6_pow2.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hleft : PrimrecPred (fun q : (List BitString × List BitString × ℕ) ×
      List (BitString × BitString) =>
      ∀ x ∈ q.1.1, (q.2.toFinset.filter fun e => e.1 = x).card ≤ 2 ^ q.1.2.2) :=
    theorem6_degree Primrec.snd (Primrec.fst.comp Primrec.fst) Primrec.fst hbound
  have hright : PrimrecPred (fun q : (List BitString × List BitString × ℕ) ×
      List (BitString × BitString) =>
      ∀ y ∈ q.1.2.1, (q.2.toFinset.filter fun e => e.2 = y).card ≤ 2 ^ q.1.2.2) :=
    theorem6_degree Primrec.snd (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
      Primrec.snd hbound
  refine ⟨E, Primrec.list_filter (primrec_sublists_gen hprod) (hleft.and hright).decide, ?_⟩
  intro S Y s N
  simp only [theorem6_restriction_decider_nearRelations,
    Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨hN, hdeg⟩
    let L := (S.product Y).filter (fun e => decide (e ∈ N))
    have hLset : L.toFinset = N := by
      ext e
      simp only [L, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
      constructor
      · exact fun h => h.2
      · intro he
        have he' := Finset.mem_product.mp (hN he)
        exact ⟨List.mem_product.mpr ⟨List.mem_toFinset.mp he'.1, List.mem_toFinset.mp he'.2⟩, he⟩
    refine ⟨L, ?_, hLset⟩
    apply List.mem_filter.mpr
    refine ⟨List.mem_sublists.mpr List.filter_sublist, ?_⟩
    apply decide_eq_true
    simpa only [hLset, List.mem_toFinset] using hdeg
  · rintro ⟨L, hL, hLset⟩
    obtain ⟨hsub, hdeg⟩ := List.mem_filter.mp hL
    have hsub' := List.mem_sublists.mp hsub
    constructor
    · intro e he
      have he' : e ∈ S.product Y := hsub'.subset (List.mem_toFinset.mp (hLset.symm ▸ he))
      simpa only [Finset.mem_product, List.mem_toFinset] using List.mem_product.mp he'
    · simpa only [hLset, List.mem_toFinset] using (of_decide_eq_true hdeg)

/-- the unbounded spoiling existential is equivalent to searching the two finite relation lists.
The search tests actual pair-code membership in `R`, including for noncanonical input strings. -/
private theorem theorem6_spoiling
    {α : Type*} [Primcodable α]
    {R : α → List BitString} {N₁ N₂ : α → List (BitString × BitString)}
    {x₁ x₂ : α → BitString}
    (hR : Primrec R) (hN₁ : Primrec N₁) (hN₂ : Primrec N₂)
    (hx₁ : Primrec x₁) (hx₂ : Primrec x₂) :
    PrimrecPred (fun a => ∃ y₁ y₂ : BitString, pairCode y₁ y₂ ∈ (R a).toFinset ∧
      (x₁ a, y₁) ∈ (N₁ a).toFinset ∧ (x₂ a, y₂) ∈ (N₂ a).toFinset) := by
  have hfirst : PrimrecPred (fun q : (α × (BitString × BitString)) ×
      (BitString × BitString) => q.1.2.1 = x₁ q.1.1) :=
    Primrec.eq.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
      (hx₁.comp (Primrec.fst.comp Primrec.fst))
  have hsecond : PrimrecPred (fun q : (α × (BitString × BitString)) ×
      (BitString × BitString) => q.2.1 = x₂ q.1.1) :=
    Primrec.eq.comp (Primrec.fst.comp Primrec.snd)
      (hx₂.comp (Primrec.fst.comp Primrec.fst))
  have hcode : PrimrecPred (fun q : (α × (BitString × BitString)) ×
      (BitString × BitString) => pairCode q.1.2.2 q.2.2 ∈ R q.1.1) :=
    theorem6_list_mem.comp (hR.comp (Primrec.fst.comp Primrec.fst))
      (CodedFiniteDistribution.pairCode_primrec.comp
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) (Primrec.snd.comp Primrec.snd))
  have hinner := theorem6_list_exists (hN₂.comp Primrec.fst)
    (hfirst.and (hsecond.and hcode)).primrecRel
  have houter := theorem6_list_exists hN₁ hinner.primrecRel
  refine houter.of_eq ?_
  intro a
  simp only [List.mem_toFinset]
  constructor
  · rintro ⟨u, hu, v, hv, h₁, h₂, hRuv⟩
    refine ⟨u.2, v.2, hRuv, ?_, ?_⟩
    · simpa only [← h₁, Prod.eta] using hu
    · simpa only [← h₂, Prod.eta] using hv
  · rintro ⟨y₁, y₂, hRuv, h₁, h₂⟩
    exact ⟨(x₁ a, y₁), h₁, (x₂ a, y₂), h₂, rfl, rfl, hRuv⟩

open scoped Classical in
/-- count the distinct surviving edges for one pair of finite relations. This combines the finite
spoiling search with duplicate-insensitive filtered cardinality, without enumerating relations. -/
private theorem theorem6_survivor_count
    {α : Type*} [Primcodable α]
    {R : α → List BitString} {A N₁ N₂ : α → List (BitString × BitString)}
    (hR : Primrec R) (hA : Primrec A) (hN₁ : Primrec N₁) (hN₂ : Primrec N₂) :
    Primrec (fun a => ((A a).toFinset.filter fun e : BitString × BitString =>
      ¬ ∃ y₁ y₂ : BitString, pairCode y₁ y₂ ∈ (R a).toFinset ∧
        (e.1, y₁) ∈ (N₁ a).toFinset ∧ (e.2, y₂) ∈ (N₂ a).toFinset).card) := by
  classical
  exact theorem6_filter_card hA
    (theorem6_spoiling (hR.comp Primrec.fst) (hN₁.comp Primrec.fst)
      (hN₂.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).not.primrecRel

/-- The support, total-cardinality and two degree checks on a finite graph are primitive
recursive. -/
private theorem theorem6_graph_checks
    {α : Type*} [Primcodable α]
    {a b g : α → ℕ} {A : α → List (BitString × BitString)}
    (ha : Primrec a) (hb : Primrec b) (hg : Primrec g) (hA : Primrec A) :
    PrimrecPred (fun p =>
      (A p).toFinset ⊆ stringsOfLength (a p) ×ˢ stringsOfLength (b p) ∧
      (A p).toFinset.card ≤ 2 ^ g p ∧
      (∀ x ∈ stringsOfLength (a p),
        ((A p).toFinset.filter fun e => e.1 = x).card ≤ 2 ^ (g p - a p)) ∧
      (∀ y ∈ stringsOfLength (b p),
        ((A p).toFinset.filter fun e => e.2 = y).card ≤ 2 ^ (g p - b p))) := by
  classical
  have hsupport : PrimrecPred (fun p => ∀ e ∈ A p,
      e.1.length = a p ∧ e.2.length = b p) :=
    theorem6_list_forall hA
      ((Primrec.eq.comp (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd))
        (ha.comp Primrec.fst)).and
       (Primrec.eq.comp (Primrec.list_length.comp (Primrec.snd.comp Primrec.snd))
        (hb.comp Primrec.fst)))
  have hsupport' : PrimrecPred (fun p =>
      (A p).toFinset ⊆ stringsOfLength (a p) ×ˢ stringsOfLength (b p)) :=
    hsupport.of_eq (fun p => by
      simp only [Finset.subset_iff, Finset.mem_product, mem_stringsOfLength, List.mem_toFinset])
  have hcard : Primrec (fun p => (A p).toFinset.card) :=
    (Primrec.list_length.comp (theorem6_dedup.comp hA)).of_eq
      (fun p => (List.card_toFinset (A p)).symm)
  have hcardBound := Primrec.nat_le.comp hcard (theorem6_pow2.comp hg)
  have hleft := theorem6_degree hA
    (CodedFiniteDistribution.allStrings_primrec.comp ha) Primrec.fst
    (theorem6_pow2.comp (Primrec.nat_sub.comp hg ha))
  have hright := theorem6_degree hA
    (CodedFiniteDistribution.allStrings_primrec.comp hb) Primrec.snd
    (theorem6_pow2.comp (Primrec.nat_sub.comp hg hb))
  exact (hsupport'.and (hcardBound.and (hleft.and hright))).of_eq
    (fun p => by simp only [stringsOfLength, List.mem_toFinset])

/-- universal quantification over the two finite bounded-degree relation families is primitive
recursive whenever its body is primitive recursive on list presentations of the relations.
Exact enumeration membership is the only property required of the enumeration witness. -/
private theorem theorem6_relation_forall
    {α : Type*} [Primcodable α]
    {S₁ S₂ Y₁ Y₂ : α → List BitString} {s : α → ℕ}
    {P : α → Finset (BitString × BitString) → Finset (BitString × BitString) → Prop}
    (hS₁ : Primrec S₁) (hS₂ : Primrec S₂) (hY₁ : Primrec Y₁) (hY₂ : Primrec Y₂)
    (hs : Primrec s)
    (hP : PrimrecPred (fun q : (α × List (BitString × BitString)) ×
      List (BitString × BitString) => P q.1.1 q.1.2.toFinset q.2.toFinset)) :
    PrimrecPred (fun a =>
      ∀ N₁ ∈ theorem6_restriction_decider_nearRelations
        (S₁ a).toFinset (Y₁ a).toFinset (s a),
      ∀ N₂ ∈ theorem6_restriction_decider_nearRelations
        (S₂ a).toFinset (Y₂ a).toFinset (s a), P a N₁ N₂) := by
  obtain ⟨E, hE, hEspec⟩ := theorem6_relation_enumeration
  have hE₁ := hE.comp (hS₁.pair (hY₁.pair hs))
  have hE₂ := hE.comp (hS₂.pair (hY₂.pair hs))
  have hinner := theorem6_list_forall (hE₂.comp Primrec.fst) hP.primrecRel
  have houter := theorem6_list_forall hE₁ hinner.primrecRel
  refine houter.of_eq ?_
  intro a
  constructor
  · intro h N₁ hN₁ N₂ hN₂
    obtain ⟨L₁, hL₁, rfl⟩ := (hEspec (S₁ a) (Y₁ a) (s a) N₁).mp hN₁
    obtain ⟨L₂, hL₂, rfl⟩ := (hEspec (S₂ a) (Y₂ a) (s a) N₂).mp hN₂
    exact h L₁ hL₁ L₂ hL₂
  · intro h L₁ hL₁ L₂ hL₂
    exact h L₁.toFinset ((hEspec (S₁ a) (Y₁ a) (s a) _).mpr ⟨L₁, hL₁, rfl⟩)
      L₂.toFinset ((hEspec (S₂ a) (Y₂ a) (s a) _).mpr ⟨L₂, hL₂, rfl⟩)

/-- all finite restrictions, bounded-degree checks, and canonical code checks in the finite Boolean
test are primitive recursive. -/
private theorem theorem6_finite_test_primrec :
    Primrec theorem6_restriction_decider_finiteTest := by
  classical
  let Q := (ℕ × ℕ × ℕ × ℕ × BitString) × BitString
  let R : Q → List BitString := fun q => decodeListCode q.1.2.2.2.2
  let A : Q → List (BitString × BitString) := fun q =>
    (decodeListCode q.2).map fun z => (decodeFirst z, decodeSecond z)
  have ha : Primrec (fun q : Q => q.1.1) := Primrec.fst.comp Primrec.fst
  have hb : Primrec (fun q : Q => q.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hg : Primrec (fun q : Q => q.1.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hs : Primrec (fun q : Q => q.1.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
  have hR : Primrec R :=
    decodeListCode_primrec.comp
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))
  have hA : Primrec A :=
    Primrec.list_map (decodeListCode_primrec.comp Primrec.snd)
      (Primrec.pair (CodedFiniteDistribution.decodeFirst_primrec.comp Primrec.snd)
        (CodedFiniteDistribution.decodeSecond_primrec.comp Primrec.snd)).to₂
  have hY₁ : Primrec (fun q => (R q).map decodeFirst) :=
    Primrec.list_map hR (CodedFiniteDistribution.decodeFirst_primrec.comp Primrec.snd).to₂
  have hY₂ : Primrec (fun q => (R q).map decodeSecond) :=
    Primrec.list_map hR (CodedFiniteDistribution.decodeSecond_primrec.comp Primrec.snd).to₂
  have hcount : Primrec (fun q : (Q × List (BitString × BitString)) ×
      List (BitString × BitString) => ((A q.1.1).toFinset.filter fun e =>
      ¬ ∃ y₁ y₂ : BitString, pairCode y₁ y₂ ∈ (R q.1.1).toFinset ∧
        (e.1, y₁) ∈ q.1.2.toFinset ∧ (e.2, y₂) ∈ q.2.toFinset).card) :=
    theorem6_survivor_count
      (hR.comp (Primrec.fst.comp Primrec.fst))
      (hA.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.snd.comp Primrec.fst) Primrec.snd
  have hthreshold : Primrec (fun q : Q => 2 ^ (q.1.2.2.1 - 3 * q.1.2.2.2.1)) :=
    theorem6_pow2.comp
      (Primrec.nat_sub.comp hg (Primrec.nat_mul.comp (Primrec.const 3) hs))
  have hsurvivors := theorem6_relation_forall
    (P := fun q N₁ N₂ => 2 ^ (q.1.2.2.1 - 3 * q.1.2.2.2.1) ≤
      ((A q).toFinset.filter fun e => ¬ ∃ y₁ y₂ : BitString,
        pairCode y₁ y₂ ∈ (R q).toFinset ∧ (e.1, y₁) ∈ N₁ ∧ (e.2, y₂) ∈ N₂).card)
    (CodedFiniteDistribution.allStrings_primrec.comp ha)
    (CodedFiniteDistribution.allStrings_primrec.comp hb) hY₁ hY₂ hs
    (Primrec.nat_le.comp (hthreshold.comp (Primrec.fst.comp Primrec.fst)) hcount)
  have hchecks := theorem6_graph_checks ha hb hg hA
  have hcanonical : PrimrecPred (fun q : Q => theorem6_graphCode
      (theorem6_restriction_decider_decodeGraph q.2) =
          q.2) :=
    Primrec.eq.comp (theorem6_canonical_code.comp Primrec.snd) Primrec.snd
  have hmap (L : List BitString) (f : BitString → BitString) :
      (L.map f).toFinset = L.toFinset.image f := by
    ext x
    simp
  refine (hcanonical.and (hchecks.and hsurvivors)).decide.of_eq ?_
  intro q
  dsimp only [theorem6_restriction_decider_finiteTest]
  apply Bool.decide_congr
  simp only [theorem6_restriction_decider_finiteGoodGraph,
    theorem6_restriction_decider_decodeGraph,
    A, R, stringsOfLength, hmap, and_assoc]

/-- the restriction
argument gives a primitive recursive Boolean test for whether a graph code represents a good
graph. The test is required to be correct on the canonical input codes used by the selector. -/
private theorem theorem6_restriction_decider :
    ∃ test : (ℕ × ℕ × ℕ × ℕ × BitString) × BitString → Bool,
      Primrec test ∧
      ∀ a b g s : ℕ, ∀ R : Finset BitString, ∀ w : BitString,
        test ((a, b, g, s, finsetListCode R), w) = true ↔
          ∃ A : Finset (BitString × BitString),
            theorem6_GoodGraph a b g s R A ∧ theorem6_graphCode A = w := by
  classical
  refine ⟨theorem6_restriction_decider_finiteTest,
    theorem6_finite_test_primrec,
    ?_⟩
  intro a b g s R w
  let R' := (decodeListCode (finsetListCode R)).toFinset
  let A' := theorem6_restriction_decider_decodeGraph w
  have hR' : R' = R := by
    simp [R', finsetListCode, decodeListCode_listCode]
  change (decide (theorem6_graphCode A' = w ∧
      theorem6_restriction_decider_finiteGoodGraph
        a b g s R' A') = true) ↔ _
  rw [decide_eq_true_eq, hR']
  constructor
  · rintro ⟨hCode, hFinite⟩
    have hGood : theorem6_GoodGraph a b g s R A' :=
      (theorem6_restriction_equivalence
        a b g s R A').2 hFinite
    exact ⟨A', hGood, hCode⟩
  · rintro ⟨A, hGood, hCode⟩
    have hDecode : A' = A := by
      dsimp [A']
      rw [← hCode]
      exact theorem6_decode_graphCode A
    refine ⟨?_, ?_⟩
    · simpa [hDecode] using hCode
    · simpa [hDecode] using
        (theorem6_restriction_equivalence
          a b g s R A).1 hGood

/-- all graphs
supported on `stringsOfLength a × stringsOfLength b` occur among the codes of sublists of the
finite edge list, and this candidate list is primitive recursive in its input. -/
private theorem theorem6_candidates :
    Primrec theorem6_candidate_list ∧
    ∀ a b g s : ℕ, ∀ R : Finset BitString,
      ∀ A : Finset (BitString × BitString),
        A ⊆ stringsOfLength a ×ˢ stringsOfLength b →
        theorem6_graphCode A ∈
          theorem6_candidate_list
          (a, b, g, s, finsetListCode R) := by
  classical
  constructor
  · have hLeft : Primrec (fun ab : ℕ × ℕ => allStrings ab.1) :=
      CodedFiniteDistribution.allStrings_primrec.comp Primrec.fst
    have hRightLen : Primrec (fun q : (ℕ × ℕ) × BitString => q.1.2) :=
      Primrec.snd.comp Primrec.fst
    have hRight : Primrec (fun q : (ℕ × ℕ) × BitString => allStrings q.1.2) :=
      CodedFiniteDistribution.allStrings_primrec.comp hRightLen
    have hPair : Primrec (fun q : ((ℕ × ℕ) × BitString) × BitString =>
        pairCode q.1.2 q.2) :=
      CodedFiniteDistribution.pairCode_primrec.comp
        (Primrec.snd.comp Primrec.fst) Primrec.snd
    have hMap : Primrec (fun q : (ℕ × ℕ) × BitString =>
        (allStrings q.1.2).map (fun y => pairCode q.2 y)) :=
      Primrec.list_map hRight hPair.to₂
    have hEdges : Primrec theorem6_edge_codes :=
      Primrec.list_flatMap hLeft hMap.to₂
    have hParamEdges : Primrec (fun p : ℕ × ℕ × ℕ × ℕ × BitString =>
        theorem6_edge_codes
          (p.1, p.2.1)) := by
      exact hEdges.comp (Primrec.pair Primrec.fst (Primrec.fst.comp Primrec.snd))
    have hSubsets := primrec_sublists_gen hParamEdges
    have hGraphCode : Primrec (fun L : List BitString => finsetListCode L.toFinset) := by
      exact listCode_primrec.comp canonicalFinsetList_toFinset_primrec
    exact Primrec.list_map hSubsets (hGraphCode.comp Primrec.snd).to₂
  · intro a b g s R A hA
    let E := theorem6_edge_codes (a, b)
    let L := E.filter (fun w => decide ((decodeFirst w, decodeSecond w) ∈ A))
    have hLsub : L.Sublist E := by
      exact List.filter_sublist
    have hLmem : L ∈ E.sublists := List.mem_sublists.mpr hLsub
    have hLset : L.toFinset = A.image (fun e : BitString × BitString =>
        pairCode e.1 e.2) := by
      ext w
      constructor
      · intro hw
        have hwL : w ∈ L := List.mem_toFinset.mp hw
        change w ∈ E.filter (fun w => decide ((decodeFirst w, decodeSecond w) ∈ A)) at hwL
        rw [List.mem_filter] at hwL
        rcases hwL with ⟨hwE, hAdec⟩
        have hAdec' : (decodeFirst w, decodeSecond w) ∈ A :=
          decide_eq_true_eq.mp hAdec
        change w ∈ theorem6_edge_codes (a, b) at hwE
        rw [theorem6_edge_codes,
          List.mem_flatMap] at hwE
        rcases hwE with ⟨x, hx, hwMap⟩
        rcases List.mem_map.mp hwMap with ⟨y, hy, hEq⟩
        subst w
        rw [decodeFirst_pairCode, decodeSecond_pairCode] at hAdec'
        exact Finset.mem_image.mpr ⟨(x, y), hAdec', rfl⟩
      · intro hw
        rcases Finset.mem_image.mp hw with ⟨e, heA, rfl⟩
        have heProd : e ∈ stringsOfLength a ×ˢ stringsOfLength b := hA heA
        rcases Finset.mem_product.mp heProd with ⟨he1, he2⟩
        have he1' : e.1 ∈ allStrings a := by
          rw [mem_allStrings, (mem_stringsOfLength a e.1).1 he1]
        have he2' : e.2 ∈ allStrings b := by
          rw [mem_allStrings, (mem_stringsOfLength b e.2).1 he2]
        apply List.mem_toFinset.mpr
        change pairCode e.1 e.2 ∈
          E.filter (fun w => decide ((decodeFirst w, decodeSecond w) ∈ A))
        rw [List.mem_filter]
        refine ⟨?_, ?_⟩
        · change pairCode e.1 e.2 ∈
            theorem6_edge_codes (a, b)
          rw [theorem6_edge_codes,
            List.mem_flatMap]
          refine ⟨e.1, he1', ?_⟩
          apply List.mem_map.mpr
          exact ⟨e.2, by simpa using he2', rfl⟩
        · simp only [decodeFirst_pairCode, decodeSecond_pairCode]
          simp [heA]
    have hCode : finsetListCode L.toFinset = theorem6_graphCode A := by
      simp [theorem6_graphCode, finsetListCode, hLset]
    change theorem6_graphCode A ∈
      (E.sublists.map fun T => finsetListCode T.toFinset)
    exact List.mem_map.mpr ⟨L, hLmem, hCode⟩

/-- a computable
finite candidate list and a primitive recursive Boolean test yield a computable first-match
selector, with a default output when the list has no match. -/
private theorem theorem6_list_search
    (candidates : ℕ × ℕ × ℕ × ℕ × BitString → List BitString)
    (hcandidates : Primrec candidates)
    (test : (ℕ × ℕ × ℕ × ℕ × BitString) × BitString → Bool)
    (htest : Primrec test) :
    ∃ f : ℕ × ℕ × ℕ × ℕ × BitString → BitString,
      Computable f ∧ ∀ p,
        (∃ w ∈ candidates p, test (p, w) = true) →
          test (p, f p) = true ∧ f p ∈ candidates p := by
  let f : ℕ × ℕ × ℕ × ℕ × BitString → BitString := fun p =>
    ((candidates p).find? (fun w => test (p, w))).getD []
  have hpred : Primrec₂ (fun (p : ℕ × ℕ × ℕ × ℕ × BitString) (w : BitString) =>
      test (p, w)) :=
    (htest.comp (Primrec.pair Primrec.fst Primrec.snd)).to₂
  have hf : Primrec f := by
    dsimp [f]
    exact Primrec.option_getD.comp (list_find?_primrec hcandidates hpred)
      (Primrec.const [])
  refine ⟨f, hf.to_comp, ?_⟩
  intro p h
  obtain ⟨w, hw, htestw⟩ := h
  have hsome : ((candidates p).find? (fun w => test (p, w))).isSome :=
    List.find?_isSome.mpr ⟨w, hw, htestw⟩
  cases hfind : (candidates p).find? (fun w => test (p, w)) with
  | none => simp [hfind] at hsome
  | some z =>
    have hz : z ∈ candidates p := List.mem_of_find?_eq_some hfind
    have htestz : (fun w : BitString => test (p, w)) z = true :=
      List.find?_some (p := fun w : BitString => test (p, w)) hfind
    constructor
    · simpa [f, hfind] using htestz
    · simpa [f, hfind] using hz

/-- the restriction argument makes
`theorem6_GoodGraph` decidable, so exhaustive search gives a total computable selector. -/
private theorem theorem6_finite_search :
    ∃ f : ℕ × ℕ × ℕ × ℕ × BitString → BitString,
      Computable f ∧
      ∀ a b g s : ℕ, ∀ R : Finset BitString,
        (∃ A, theorem6_GoodGraph a b g s R A) →
        ∃ A, theorem6_GoodGraph a b g s R A ∧
          f (a, b, g, s, finsetListCode R) = theorem6_graphCode A := by
  obtain ⟨test, htest, htestSpec⟩ :=
    theorem6_restriction_decider
  obtain ⟨hcandidates, hcandidatesSpec⟩ :=
    theorem6_candidates
  obtain ⟨f, hf, hfSpec⟩ :=
    theorem6_list_search
      theorem6_candidate_list
      hcandidates test htest
  refine ⟨f, hf, fun a b g s R hGood => ?_⟩
  obtain ⟨A, hA⟩ := hGood
  let p : ℕ × ℕ × ℕ × ℕ × BitString := (a, b, g, s, finsetListCode R)
  have hCodeGood : test (p, theorem6_graphCode A) = true :=
    (htestSpec a b g s R (theorem6_graphCode A)).2 ⟨A, hA, rfl⟩
  have hFound := hfSpec p ⟨theorem6_graphCode A,
    hcandidatesSpec a b g s R A hA.1, hCodeGood⟩
  obtain ⟨A', hA', hCode⟩ :=
    (htestSpec a b g s R (f p)).1 hFound.1
  exact ⟨A', hA', hCode.symm⟩

/-- a uniform computable operation
whose four natural-number parameters are supplied as advice increases plain complexity by only
logarithmic overhead in the sum of those parameters. -/
private theorem theorem6_parametric_computable_image
    (D : Map) (hD : isOptimalConditional D) :
    ∀ f : ℕ × ℕ × ℕ × ℕ × BitString → BitString, Computable f →
      ∃ c : ℕ, ∀ a b g s : ℕ, ∀ x : BitString,
        natK D (f (a, b, g, s, x)) ≤ natK D x + logSlack c (a + b + g + s) := by
  classical
  intro f hf
  let read (i : ℕ) (q : BitString) : ℕ :=
    decodeBits ((decodeListCode (decodeFirst q)).getD i [])
  have hlist : Computable (fun q : BitString => decodeListCode (decodeFirst q)) :=
    decodeListCode_computable.comp decodeFirst_computable
  have hread (i : ℕ) : Computable (fun q : BitString => read i q) := by
    dsimp [read]
    exact decodeBits_computable.comp
      ((Primrec.list_getD []).to_comp.comp hlist (Computable.const i))
  have hq0 : Computable (fun z : (BitString × BitString) × BitString => read 0 z.1.1) :=
    (hread 0).comp (Computable.fst.comp Computable.fst)
  have hq1 : Computable (fun z : (BitString × BitString) × BitString => read 1 z.1.1) :=
    (hread 1).comp (Computable.fst.comp Computable.fst)
  have hq2 : Computable (fun z : (BitString × BitString) × BitString => read 2 z.1.1) :=
    (hread 2).comp (Computable.fst.comp Computable.fst)
  have hq3 : Computable (fun z : (BitString × BitString) × BitString => read 3 z.1.1) :=
    (hread 3).comp (Computable.fst.comp Computable.fst)
  have hpost : Computable (fun z : (BitString × BitString) × BitString =>
      f (read 0 z.1.1, read 1 z.1.1, read 2 z.1.1, read 3 z.1.1, z.2)) := by
    exact hf.comp (hq0.pair (hq1.pair (hq2.pair (hq3.pair Computable.snd))))
  let E : Map := fun pr =>
    (D (decodeSecond pr.1, [])).map
      (fun x => f (read 0 pr.1, read 1 pr.1, read 2 pr.1, read 3 pr.1, x))
  have hrun : Partrec (fun pr : BitString × BitString => D (decodeSecond pr.1, [])) :=
    Partrec.comp hD.1
      ((decodeSecond_computable.comp Computable.fst).pair (Computable.const []))
  have hE : isDecompressor E := by
    exact Partrec.map hrun hpost.to₂
  obtain ⟨cE, hEopt⟩ := hD.2 E hE
  refine ⟨32 + cE + 20, fun a b g s x => ?_⟩
  let params := listCode [Nat.bits a, Nat.bits b, Nat.bits g, Nat.bits s]
  let p := Classical.choose (exists_program_le_cVal D hD x)
  have hp := Classical.choose_spec (exists_program_le_cVal D hD x)
  have hpProd : produces D p [] x := hp.1
  have hpLen' : p.length ≤ cVal D x := hp.2
  have hpLen : p.length ≤ natK D x := by
    simpa [cVal, natK, plainK] using hpLen'
  let q := pairCode params p
  have hparams : decodeListCode params = [Nat.bits a, Nat.bits b, Nat.bits g, Nat.bits s] := by
    dsimp only [params]
    exact decodeListCode_listCode _
  have hread0 : read 0 q = a := by
    simp only [read, q, decodeFirst_pairCode]
    rw [hparams]
    simp [decodeBits_natBits]
  have hread1 : read 1 q = b := by
    simp only [read, q, decodeFirst_pairCode]
    rw [hparams]
    simp [decodeBits_natBits]
  have hread2 : read 2 q = g := by
    simp only [read, q, decodeFirst_pairCode]
    rw [hparams]
    simp [decodeBits_natBits]
  have hread3 : read 3 q = s := by
    simp only [read, q, decodeFirst_pairCode]
    rw [hparams]
    simp [decodeBits_natBits]
  have hprod : produces E q [] (f (a, b, g, s, x)) := by
    change f (a, b, g, s, x) ∈
      (D (decodeSecond q, [])).map
        (fun z => f (read 0 q, read 1 q, read 2 q, read 3 q, z))
    rw [decodeSecond_pairCode]
    have hfun : (fun z => f (read 0 q, read 1 q, read 2 q, read 3 q, z)) =
        (fun z => f (a, b, g, s, z)) := by
      funext z
      simp [hread0, hread1, hread2, hread3]
    rw [hfun]
    exact Part.mem_map _ hpProd
  have hEbound : plainK E (f (a, b, g, s, x)) ≤ (q.length : ENat) := by
    change sInf (candidateLengths E (f (a, b, g, s, x)) []) ≤ _
    exact sInf_le ⟨q, hprod, rfl⟩
  have hmap := hEopt (f (a, b, g, s, x)) []
  have hplain : plainK D (f (a, b, g, s, x)) ≤
      ((natK D x + (2 * params.length + 2 + cE) : ℕ) : ENat) := by
    calc
      plainK D (f (a, b, g, s, x)) ≤ plainK E (f (a, b, g, s, x)) + cE := hmap
      _ ≤ (q.length : ENat) + cE := by
        simpa [add_comm] using add_le_add_right hEbound (cE : ENat)
      _ ≤ ((p.length + (2 * params.length + 2 + cE) : ℕ) : ENat) := by
        have hlen : q.length + cE ≤ p.length + (2 * params.length + 2 + cE) := by
          simp [q, length_pairCode]
          omega
        exact_mod_cast hlen
      _ ≤ ((natK D x + (2 * params.length + 2 + cE) : ℕ) : ENat) := by
        exact_mod_cast Nat.add_le_add_right hpLen _
  have hbitsA : (Nat.bits a).length ≤ (Nat.bits (a + b + g + s)).length :=
    length_natBits_mono (by omega)
  have hbitsB : (Nat.bits b).length ≤ (Nat.bits (a + b + g + s)).length :=
    length_natBits_mono (by omega)
  have hbitsG : (Nat.bits g).length ≤ (Nat.bits (a + b + g + s)).length :=
    length_natBits_mono (by omega)
  have hbitsS : (Nat.bits s).length ≤ (Nat.bits (a + b + g + s)).length :=
    length_natBits_mono (by omega)
  have hparamsLen : params.length ≤ 8 * (Nat.bits (a + b + g + s)).length + 4 := by
    simp [params, length_pairCode]
    omega
  have hcomplex : natK D (f (a, b, g, s, x)) ≤
      natK D x + (2 * params.length + 2 + cE) := by
    have hyfin := plainK_ne_top D hD (f (a, b, g, s, x))
    have hxfin := plainK_ne_top D hD x
    have hyval : (natK D (f (a, b, g, s, x)) : ENat) =
        plainK D (f (a, b, g, s, x)) := ENat.natCast_toNat hyfin
    have hxval : (natK D x : ENat) = plainK D x :=
      ENat.natCast_toNat hxfin
    have h := hplain
    rw [← hyval] at h
    exact_mod_cast h
  have hfinal : 2 * params.length + 2 + cE ≤
      logSlack (32 + cE + 20) (a + b + g + s) := by
    unfold logSlack
    have hprod : 0 ≤ cE * (Nat.bits (a + b + g + s)).length := Nat.zero_le _
    nlinarith [hparamsLen, hprod]
  have hadd : natK D x + (2 * params.length + 2 + cE) ≤
      natK D x + logSlack (32 + cE + 20) (a + b + g + s) :=
    Nat.add_le_add_left hfinal (natK D x)
  exact hcomplex.trans hadd

/-- if some graph has the
property `theorem6_GoodGraph a b g s R`, then the lexicographically first one is computable from
`a, b, g, s` and `list R` (the property is decidable: only the restrictions of the nearness
relations to `S₁ × π₁(R)` and `S₂ × π₂(R)` matter, and these are finitely many), so some good graph
has complexity at most `K(list R) + O(log n)` when `a, b, g, s = O(n)`. -/
private theorem theorem6_search (D : Map) (hD : isOptimalConditional D) (B : ℕ) :
    ∃ c : ℕ, ∀ n a b g s : ℕ, ∀ R : Finset BitString,
      a ≤ B * (n + 1) → b ≤ B * (n + 1) → g ≤ B * (n + 1) → s ≤ B * (n + 1) →
      (∃ A, theorem6_GoodGraph a b g s R A) →
      ∃ A, theorem6_GoodGraph a b g s R A ∧
        natK D (theorem6_graphCode A) ≤ natK D (finsetListCode R) + logSlack c n := by
  classical
  obtain ⟨f, hf, hsearch⟩ := theorem6_finite_search
  obtain ⟨c₀, hc₀⟩ := theorem6_parametric_computable_image D hD f hf
  obtain ⟨c, hc⟩ := logSlack_absorb_of_le_linear c₀ (4 * B) (4 * B)
  refine ⟨c, fun n a b g s R ha hb hg hs hGood => ?_⟩
  obtain ⟨A, hA, hCode⟩ := hsearch a b g s R hGood
  refine ⟨A, hA, ?_⟩
  rw [← hCode]
  have hsum : a + b + g + s ≤ (4 * B) * n + 4 * B := by
    have hM : a + b + g + s ≤ 4 * (B * (n + 1)) := by omega
    calc
      a + b + g + s ≤ 4 * (B * (n + 1)) := hM
      _ = (4 * B) * n + 4 * B := by ring
  calc
    natK D (f (a, b, g, s, finsetListCode R))
        ≤ natK D (finsetListCode R) + logSlack c₀ (a + b + g + s) :=
          hc₀ a b g s (finsetListCode R)
    _ ≤ natK D (finsetListCode R) + logSlack c n :=
          Nat.add_le_add_left (hc n (a + b + g + s) hsum) _

/-- An element at a given position of a computable finite list has conditional complexity,
given the list argument, at most the logarithm of the list length plus a constant. -/
private theorem theorem6_aux_rank (D : Map) (hD : isOptimalConditional D)
    (f : BitString → List BitString) (hf : Computable f) :
    ∃ c : ℕ, ∀ (y : BitString) (i : ℕ), i < (f y).length →
      natCondK D ((f y).getD i []) y ≤ Nat.clog 2 (f y).length + c := by
  let decoder : Map := fun q => Part.some ((f q.2).getD (decodeBits q.1) [])
  have hget : Computable (fun q : BitString × BitString =>
      (f q.2).getD (decodeBits q.1) []) := by
    have hf' : Computable (fun q : BitString × BitString => f q.2) := hf.comp Computable.snd
    have hi : Computable (fun q : BitString × BitString => decodeBits q.1) :=
      decodeBits_computable.comp Computable.fst
    exact (Primrec.list_getD []).to_comp.comp hf' hi
  have hdecoder : isDecompressor decoder := Computable.partrec hget
  obtain ⟨c, hc⟩ := hD.2 decoder hdecoder
  refine ⟨c, fun y i hi => ?_⟩
  have hprod : produces decoder (Nat.bits i) y ((f y).getD i []) := by
    simp [produces, decoder, decodeBits_natBits]
  have hcond : condK decoder ((f y).getD i []) y ≤ ((Nat.bits i).length : ℕ∞) := by
    change sInf (candidateLengths decoder ((f y).getD i []) y) ≤ _
    exact sInf_le ⟨Nat.bits i, hprod, rfl⟩
  have hD_bound : condK D ((f y).getD i []) y ≤
      ((Nat.bits i).length + c : ℕ∞) := by
    calc
      condK D ((f y).getD i []) y ≤ condK decoder ((f y).getD i []) y + c := hc _ _
      _ ≤ ((Nat.bits i).length : ℕ∞) + c := by
        simpa [add_comm] using add_le_add_left hcond (c : ℕ∞)
      _ = ((Nat.bits i).length + c : ℕ∞) := rfl
  have hNat : natCondK D ((f y).getD i []) y ≤ (Nat.bits i).length + c :=
    ENat.toNat_le_of_le_natCast hD_bound
  have hbit : (Nat.bits i).length ≤ Nat.clog 2 (f y).length := by
    rw [Nat.size_eq_bits_len]
    apply (Nat.size_le).2
    exact lt_of_lt_of_le hi (Nat.le_pow_clog (by decide) _)
  omega

/-- The canonical list of right neighbours of `decodeSecond z` in the graph coded by
`decodeFirst z`. -/
private def theorem6_aux_rightNbrs (z : BitString) : List BitString :=
  canonicalFinsetList (((decodeListCode (decodeFirst z)).filter
    (fun e => decide (decodeFirst e = decodeSecond z))).map decodeSecond).toFinset

/-- The canonical list of left neighbours of `decodeSecond z` in the graph coded by
`decodeFirst z`. -/
private def theorem6_aux_leftNbrs (z : BitString) : List BitString :=
  canonicalFinsetList (((decodeListCode (decodeFirst z)).filter
    (fun e => decide (decodeSecond e = decodeSecond z))).map decodeFirst).toFinset

/-- The right-neighbour list is computable. -/
private theorem theorem6_aux_rightNbrs_computable :
    Computable theorem6_aux_rightNbrs := by
  have htuples : Primrec (fun z : BitString => decodeListCode (decodeFirst z)) :=
    decodeListCode_primrec.comp CodedFiniteDistribution.decodeFirst_primrec
  have htest : Primrec (fun q : BitString × BitString =>
      decide (decodeFirst q.2 = decodeSecond q.1)) := by
    exact PrimrecPred.decide (PrimrecRel.comp Primrec.eq
      (CodedFiniteDistribution.decodeFirst_primrec.comp Primrec.snd)
      (CodedFiniteDistribution.decodeSecond_primrec.comp Primrec.fst))
  have hfiltered : Primrec (fun z : BitString =>
      (decodeListCode (decodeFirst z)).filter
        (fun e => decide (decodeFirst e = decodeSecond z))) :=
    Primrec.list_filter htuples htest.to₂
  have hmapped : Primrec (fun z : BitString =>
      ((decodeListCode (decodeFirst z)).filter
        (fun e => decide (decodeFirst e = decodeSecond z))).map decodeSecond) :=
    Primrec.list_map hfiltered
      (CodedFiniteDistribution.decodeSecond_primrec.comp Primrec.snd).to₂
  exact (canonicalFinsetList_toFinset_primrec.comp hmapped).to_comp

/-- The left-neighbour list is computable. -/
private theorem theorem6_aux_leftNbrs_computable :
    Computable theorem6_aux_leftNbrs := by
  have htuples : Primrec (fun z : BitString => decodeListCode (decodeFirst z)) :=
    decodeListCode_primrec.comp CodedFiniteDistribution.decodeFirst_primrec
  have htest : Primrec (fun q : BitString × BitString =>
      decide (decodeSecond q.2 = decodeSecond q.1)) := by
    exact PrimrecPred.decide (PrimrecRel.comp Primrec.eq
      (CodedFiniteDistribution.decodeSecond_primrec.comp Primrec.snd)
      (CodedFiniteDistribution.decodeSecond_primrec.comp Primrec.fst))
  have hfiltered : Primrec (fun z : BitString =>
      (decodeListCode (decodeFirst z)).filter
        (fun e => decide (decodeSecond e = decodeSecond z))) :=
    Primrec.list_filter htuples htest.to₂
  have hmapped : Primrec (fun z : BitString =>
      ((decodeListCode (decodeFirst z)).filter
        (fun e => decide (decodeSecond e = decodeSecond z))).map decodeFirst) :=
    Primrec.list_map hfiltered
      (CodedFiniteDistribution.decodeFirst_primrec.comp Primrec.snd).to₂
  exact (canonicalFinsetList_toFinset_primrec.comp hmapped).to_comp

/-- Membership in the right-neighbour list of `x` in `A` is equivalent to adjacency in `A`. -/
private theorem theorem6_aux_mem_rightNbrs (A : Finset (BitString × BitString))
    (x y : BitString) :
    y ∈ theorem6_aux_rightNbrs (pairCode (theorem6_graphCode A) x) ↔ (x, y) ∈ A := by
  simp only [theorem6_aux_rightNbrs, theorem6_graphCode, finsetListCode,
    decodeFirst_pairCode, decodeSecond_pairCode, decodeListCode_listCode,
    mem_canonicalFinsetList, List.mem_toFinset, List.mem_map, List.mem_filter,
    Finset.mem_image, decide_eq_true_eq]
  constructor
  · rintro ⟨e, ⟨⟨p, hp, rfl⟩, hfirst⟩, rfl⟩
    rw [decodeFirst_pairCode] at hfirst
    rw [decodeSecond_pairCode]
    subst hfirst
    simpa using hp
  · intro h
    exact ⟨pairCode x y, ⟨⟨(x, y), h, rfl⟩, decodeFirst_pairCode x y⟩,
      decodeSecond_pairCode x y⟩

/-- Membership in the left-neighbour list of `y` in `A` is equivalent to adjacency in `A`. -/
private theorem theorem6_aux_mem_leftNbrs (A : Finset (BitString × BitString))
    (x y : BitString) :
    x ∈ theorem6_aux_leftNbrs (pairCode (theorem6_graphCode A) y) ↔ (x, y) ∈ A := by
  simp only [theorem6_aux_leftNbrs, theorem6_graphCode, finsetListCode,
    decodeFirst_pairCode, decodeSecond_pairCode, decodeListCode_listCode,
    mem_canonicalFinsetList, List.mem_toFinset, List.mem_map, List.mem_filter,
    Finset.mem_image, decide_eq_true_eq]
  constructor
  · rintro ⟨e, ⟨⟨p, hp, rfl⟩, hsecond⟩, rfl⟩
    rw [decodeSecond_pairCode] at hsecond
    rw [decodeFirst_pairCode]
    subst hsecond
    simpa using hp
  · intro h
    exact ⟨pairCode x y, ⟨⟨(x, y), h, rfl⟩, decodeSecond_pairCode x y⟩,
      decodeFirst_pairCode x y⟩

/-- The right-neighbour list of a vertex has length at most its degree in `A`. -/
private theorem theorem6_aux_length_rightNbrs (A : Finset (BitString × BitString))
    (x : BitString) :
    (theorem6_aux_rightNbrs (pairCode (theorem6_graphCode A) x)).length ≤
      (A.filter fun e => e.1 = x).card := by
  have hsub : (theorem6_aux_rightNbrs (pairCode (theorem6_graphCode A) x)).toFinset ⊆
      (A.filter fun e => e.1 = x).image Prod.snd := by
    intro y hy
    rw [List.mem_toFinset] at hy
    have h := (theorem6_aux_mem_rightNbrs A x y).1 hy
    exact Finset.mem_image.2 ⟨(x, y), Finset.mem_filter.2 ⟨h, rfl⟩, rfl⟩
  have hnd : (theorem6_aux_rightNbrs (pairCode (theorem6_graphCode A) x)).Nodup :=
    canonicalFinsetList_nodup _
  calc (theorem6_aux_rightNbrs (pairCode (theorem6_graphCode A) x)).length
      = (theorem6_aux_rightNbrs (pairCode (theorem6_graphCode A) x)).toFinset.card :=
        (List.toFinset_card_of_nodup hnd).symm
    _ ≤ ((A.filter fun e => e.1 = x).image Prod.snd).card := Finset.card_le_card hsub
    _ ≤ (A.filter fun e => e.1 = x).card := Finset.card_image_le

/-- The left-neighbour list of a vertex has length at most its degree in `A`. -/
private theorem theorem6_aux_length_leftNbrs (A : Finset (BitString × BitString))
    (y : BitString) :
    (theorem6_aux_leftNbrs (pairCode (theorem6_graphCode A) y)).length ≤
      (A.filter fun e => e.2 = y).card := by
  have hsub : (theorem6_aux_leftNbrs (pairCode (theorem6_graphCode A) y)).toFinset ⊆
      (A.filter fun e => e.2 = y).image Prod.fst := by
    intro x hx
    rw [List.mem_toFinset] at hx
    have h := (theorem6_aux_mem_leftNbrs A x y).1 hx
    exact Finset.mem_image.2 ⟨(x, y), Finset.mem_filter.2 ⟨h, rfl⟩, rfl⟩
  have hnd : (theorem6_aux_leftNbrs (pairCode (theorem6_graphCode A) y)).Nodup :=
    canonicalFinsetList_nodup _
  calc (theorem6_aux_leftNbrs (pairCode (theorem6_graphCode A) y)).length
      = (theorem6_aux_leftNbrs (pairCode (theorem6_graphCode A) y)).toFinset.card :=
        (List.toFinset_card_of_nodup hnd).symm
    _ ≤ ((A.filter fun e => e.2 = y).image Prod.fst).card := Finset.card_le_card hsub
    _ ≤ (A.filter fun e => e.2 = y).card := Finset.card_image_le

/-- A member of a computable list of length at most `2 ^ d` has conditional complexity at
most `d` plus a constant given the list argument. -/
private theorem theorem6_aux_rank_mem (D : Map) (hD : isOptimalConditional D)
    (f : BitString → List BitString) (hf : Computable f) :
    ∃ c : ℕ, ∀ (y x : BitString) (d : ℕ), x ∈ f y → (f y).length ≤ 2 ^ d →
      natCondK D x y ≤ d + c := by
  obtain ⟨c, hc⟩ := theorem6_aux_rank D hD f hf
  refine ⟨c, fun y x d hx hlen => ?_⟩
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.1 hx
  have hgetD : (f y).getD i [] = x := by
    rw [List.getD_eq_getElem _ _ hi]
    exact hget
  have h := hc y i hi
  rw [hgetD] at h
  have hclog : Nat.clog 2 (f y).length ≤ d := Nat.clog_le_of_le_pow hlen
  omega

/-- for an edge `(x₁, x₂)` of a
finite graph `A` with `|A| ≤ 2 ^ d₀`, `deg x₁ ≤ 2 ^ d₁`, `deg x₂ ≤ 2 ^ d₂`, the pair is described by
a description of `A` and its index in `A`, and `x₂` (resp. `x₁`) given `x₁` (resp. `x₂`) by a
description of `A` and its index among the neighbours: `K(x₁, x₂) ≤ d₀ + K(A) + O(log n)`,
`K(x₂ | x₁) ≤ d₁ + K(A) + O(log n)`, `K(x₁ | x₂) ≤ d₂ + K(A) + O(log n)` when all these numbers are
`O(n)`. -/
private theorem theorem6_degree_coding (D : Map) (hD : isOptimalConditional D) (B : ℕ) :
    ∃ c : ℕ, ∀ n d₀ d₁ d₂ : ℕ, ∀ A : Finset (BitString × BitString), ∀ x₁ x₂ : BitString,
      d₀ ≤ B * (n + 1) → d₁ ≤ B * (n + 1) → d₂ ≤ B * (n + 1) →
      natK D (theorem6_graphCode A) ≤ B * (n + 1) → (x₁, x₂) ∈ A →
      A.card ≤ 2 ^ d₀ → (A.filter fun e => e.1 = x₁).card ≤ 2 ^ d₁ →
      (A.filter fun e => e.2 = x₂).card ≤ 2 ^ d₂ →
      natK D (pairCode x₁ x₂) ≤ d₀ + natK D (theorem6_graphCode A) + logSlack c n ∧
      natCondK D x₂ x₁ ≤ d₁ + natK D (theorem6_graphCode A) + logSlack c n ∧
      natCondK D x₁ x₂ ≤ d₂ + natK D (theorem6_graphCode A) + logSlack c n := by
  obtain ⟨cR0, hR0⟩ := theorem6_aux_rank_mem D hD decodeListCode
    decodeListCode_primrec.to_comp
  obtain ⟨cR1, hR1⟩ := theorem6_aux_rank_mem D hD theorem6_aux_rightNbrs
    theorem6_aux_rightNbrs_computable
  obtain ⟨cR2, hR2⟩ := theorem6_aux_rank_mem D hD theorem6_aux_leftNbrs
    theorem6_aux_leftNbrs_computable
  obtain ⟨cRank, hcRank⟩ : ∃ c : ℕ, c = cR0 + cR1 + cR2 := ⟨_, rfl⟩
  obtain ⟨cCh, hCh⟩ := Kolmogorov.condK_pairCode_chain_upper_values D hD
  obtain ⟨cChain, hChain⟩ := pairPlainK_chain_upper_values D hD
  obtain ⟨cProj, hProj⟩ := pairPlainK_right_le D hD
  obtain ⟨cC, hcC⟩ := condK_le_plainK D hD
  obtain ⟨cMap, hMap⟩ := condK_map_le D hD decodeSecond decodeSecond_computable
  obtain ⟨b₁, hb₁⟩ := logSlack_le_add_const (2 * cCh)
  obtain ⟨b₂, hb₂⟩ := logSlack_le_add_const (2 * cChain)
  obtain ⟨cF1, hF1⟩ := logSlack_linear_bound cCh (4 * B) (4 * B + 2 * cC + 2 * cRank + 2 + b₁)
  obtain ⟨cF2, hF2⟩ := logSlack_linear_bound cChain (4 * B) (4 * B + 2 * cRank + 2 + b₂)
  have hge : ∀ c m : ℕ, c ≤ logSlack c m := fun c m => by
    unfold logSlack
    exact Nat.le_add_left _ _
  have hPV : ∀ w : BitString, plainK D w = (natK D w : ENat) := fun w =>
    (ENat.natCast_toNat (Kolmogorov.plainK_ne_top D hD w)).symm
  have hCV : ∀ u w : BitString, condK D u w = (natCondK D u w : ENat) := fun u w =>
    (ENat.natCast_toNat (condK_ne_top_of_optimal D hD u w)).symm
  refine ⟨cC + cRank + cMap + cProj + cF1 + cF2,
    fun n d₀ d₁ d₂ A x₁ x₂ hd₀ hd₁ hd₂ hA hx hcard hdeg₁ hdeg₂ => ?_⟩
  obtain ⟨w, hw⟩ : ∃ w : BitString, w = theorem6_graphCode A := ⟨_, rfl⟩
  rw [← hw] at hA ⊢
  have hsplit : logSlack (cC + cRank + cMap + cProj + cF1 + cF2) n =
      logSlack cC n + logSlack cRank n + logSlack cMap n + logSlack cProj n +
        logSlack cF1 n + logSlack cF2 n := by
    simp only [logSlack_add_constants]
  have hgC := hge cC n
  have hgR := hge cRank n
  have hgM := hge cMap n
  have hgP := hge cProj n
  have hBn : B * (n + 1) = B * n + B := by ring
  have h4B : 4 * B * n = 4 * (B * n) := by ring
  -- rank bounds
  have hr0 : natCondK D (pairCode x₁ x₂) w ≤ d₀ + cR0 := by
    have hL : decodeListCode w = canonicalFinsetList (A.image fun e => pairCode e.1 e.2) := by
      rw [hw, theorem6_graphCode, finsetListCode, decodeListCode_listCode]
    have hmem : pairCode x₁ x₂ ∈ decodeListCode w := by
      rw [hL, mem_canonicalFinsetList]
      exact Finset.mem_image.2 ⟨(x₁, x₂), hx, rfl⟩
    have hlen : (decodeListCode w).length ≤ 2 ^ d₀ := by
      rw [hL, length_canonicalFinsetList]
      exact Finset.card_image_le.trans hcard
    exact hR0 w (pairCode x₁ x₂) d₀ hmem hlen
  have hr1 : natCondK D x₂ (pairCode w x₁) ≤ d₁ + cR1 := by
    have hmem : x₂ ∈ theorem6_aux_rightNbrs (pairCode w x₁) := by
      rw [hw]
      exact (theorem6_aux_mem_rightNbrs A x₁ x₂).2 hx
    have hlen : (theorem6_aux_rightNbrs (pairCode w x₁)).length ≤ 2 ^ d₁ := by
      rw [hw]
      exact (theorem6_aux_length_rightNbrs A x₁).trans hdeg₁
    exact hR1 (pairCode w x₁) x₂ d₁ hmem hlen
  have hr2 : natCondK D x₁ (pairCode w x₂) ≤ d₂ + cR2 := by
    have hmem : x₁ ∈ theorem6_aux_leftNbrs (pairCode w x₂) := by
      rw [hw]
      exact (theorem6_aux_mem_leftNbrs A x₁ x₂).2 hx
    have hlen : (theorem6_aux_leftNbrs (pairCode w x₂)).length ≤ 2 ^ d₂ := by
      rw [hw]
      exact (theorem6_aux_length_leftNbrs A x₂).trans hdeg₂
    exact hR2 (pairCode w x₂) x₁ d₂ hmem hlen
  -- the code of `A` given anything
  have hwc : ∀ z : BitString, natCondK D w z ≤ natK D w + cC := fun z => by
    have h := hcC w z
    rw [hCV, hPV] at h
    exact_mod_cast h
  -- conditional parts
  have hcond : ∀ (u v : BitString) (d cr : ℕ), d ≤ B * (n + 1) → cr ≤ cRank →
      natCondK D u (pairCode w v) ≤ d + cr →
      natCondK D u v ≤ d + natK D w + logSlack (cC + cRank + cMap + cProj + cF1 + cF2) n := by
    intro u v d cr hd hcr hu
    have hch := hCh w u v (natCondK D w v) (natCondK D u (pairCode w v))
      (natCondK D (pairCode w u) v) (hCV _ _) (hCV _ _) (hCV _ _)
    have hdouble : logSlack (2 * cCh) (natCondK D (pairCode w u) v + 1) =
        2 * logSlack cCh (natCondK D (pairCode w u) v + 1) := by
      unfold logSlack
      ring
    have hb := hb₁ (natCondK D (pairCode w u) v + 1)
    have hwv := hwc v
    have hMb : natCondK D (pairCode w u) v + 1 ≤
        4 * B * n + (4 * B + 2 * cC + 2 * cRank + 2 + b₁) := by
      omega
    have hF := logSlack_le_of_linear_bound hF1 hMb
    have hmap : natCondK D u v ≤ natCondK D (pairCode w u) v + cMap := by
      have h := hMap (pairCode w u) v
      rw [decodeSecond_pairCode, hCV, hCV] at h
      exact_mod_cast h
    omega
  refine ⟨?_, hcond x₂ x₁ d₁ cR1 hd₁ (by omega) hr1, hcond x₁ x₂ d₂ cR2 hd₂ (by omega) hr2⟩
  -- the pair
  have hch := hChain w (pairCode x₁ x₂) (natK D w) (natCondK D (pairCode x₁ x₂) w)
    (natK D (pairCode w (pairCode x₁ x₂))) (hPV _) (hCV _ _) (hPV _)
  have hdouble : logSlack (2 * cChain) (natK D (pairCode w (pairCode x₁ x₂)) + 1) =
      2 * logSlack cChain (natK D (pairCode w (pairCode x₁ x₂)) + 1) := by
    unfold logSlack
    ring
  have hb := hb₂ (natK D (pairCode w (pairCode x₁ x₂)) + 1)
  have hMb : natK D (pairCode w (pairCode x₁ x₂)) + 1 ≤
      4 * B * n + (4 * B + 2 * cRank + 2 + b₂) := by
    omega
  have hF := logSlack_le_of_linear_bound hF2 hMb
  have hproj : natK D (pairCode x₁ x₂) ≤ natK D (pairCode w (pairCode x₁ x₂)) + cProj := by
    have h := hProj w (pairCode x₁ x₂)
    simp only [pairPlainK] at h
    rw [hPV, hPV] at h
    exact_mod_cast h
  omega

/-- more than `2^(k+1) - 1` distinct pairs cannot
all have joint complexity at most `k`, by the standard count of descriptions of length at most
`k`. -/
private theorem theorem6_count_high_complexity_edge
    (D : Map) (hD : isOptimalConditional D) (k : ℕ)
    (B : Finset (BitString × BitString)) (hB : 2 ^ (k + 1) ≤ B.card) :
    ∃ e : BitString × BitString, e ∈ B ∧
      k < natK D (pairCode e.1 e.2) := by
  classical
  by_contra h
  push Not at h
  let S := B.image (fun e : BitString × BitString => pairCode e.1 e.2)
  have hsub : S ⊆ Kolmogorov.compressibleWords D [] k := by
    intro z hz
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hz
    have hk := h e he
    have htop : plainK D (pairCode e.1 e.2) ≠ ⊤ :=
      Kolmogorov.plainK_ne_top D hD _
    have hcond : condK D (pairCode e.1 e.2) [] ≤ (k : ENat) := by
      change plainK D (pairCode e.1 e.2) ≤ (k : ENat)
      rw [← ENat.natCast_toNat htop]
      exact_mod_cast hk
    rw [Kolmogorov.compressibleWords, Finset.mem_filter]
    refine ⟨?_, hcond⟩
    obtain ⟨p, hpLen, hpProd⟩ := (Kolmogorov.condK_le_iff D _ [] k).mp hcond
    rw [Kolmogorov.generatedWords, List.mem_toFinset, List.mem_filterMap]
    exact ⟨p, Kolmogorov.mem_programsLe k p hpLen,
      Kolmogorov.progToOut_eq_some.mpr hpProd⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective B pairCode_injective] at hcard
  have hlt := Kolmogorov.card_compressibleWordsLt D [] k
  omega

/-- Swapping the two components of a pair code increases plain complexity by at most a
constant, since the swap is computable. -/
private theorem theorem6_aux_swap (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ x y : BitString,
      plainK D (pairCode y x) ≤ plainK D (pairCode x y) + (c : ℕ∞) := by
  let swap : BitString → BitString := fun w => pairCode (decodeSecond w) (decodeFirst w)
  have hEq : swap = (fun p : BitString × BitString => pairCode p.1 p.2) ∘
      (fun w : BitString => (decodeSecond w, decodeFirst w)) := by
    funext w
    rfl
  have hSwap : Computable swap := by
    rw [hEq]
    exact pairCode_computable.comp (decodeSecond_computable.pair decodeFirst_computable)
  obtain ⟨c, hc⟩ := plainK_map_le D hD swap hSwap
  refine ⟨c, fun x y => ?_⟩
  simpa [swap, decodeFirst_pairCode, decodeSecond_pairCode] using hc (pairCode x y)

/-- from
`K(x₁) ≤ a + O(log n)`, `K(x₂) ≤ b + O(log n)`, `K(x₂ | x₁) ≤ g - a + O(log n)`,
`K(x₁ | x₂) ≤ g - b + O(log n)` and `K(x₁, x₂) = g ± O(log n)`, where `a, b, g` approximate
`αn, βn, γn` within `1`, the chain rule `K(x₁, x₂) ≤ K(xᵢ) + K(x_{3-i} | xᵢ) + O(log K(x₁, x₂))`
turns all inequalities into equalities up to `O(log n)`. -/
private theorem theorem6_extraction (D : Map) (hD : isOptimalConditional D)
    (α β γ : ℝ) (c₀ : ℕ) :
    ∃ c : ℕ, ∀ n a b g : ℕ, ∀ x₁ x₂ : BitString,
      |(a : ℝ) - α * n| ≤ 1 → |(b : ℝ) - β * n| ≤ 1 → |(g : ℝ) - γ * n| ≤ 1 →
      a ≤ g → b ≤ g →
      natK D x₁ ≤ a + logSlack c₀ n → natK D x₂ ≤ b + logSlack c₀ n →
      natCondK D x₂ x₁ ≤ g - a + logSlack c₀ n → natCondK D x₁ x₂ ≤ g - b + logSlack c₀ n →
      natK D (pairCode x₁ x₂) ≤ g + logSlack c₀ n →
      g ≤ natK D (pairCode x₁ x₂) + logSlack c₀ n →
      |(natK D x₁ : ℝ) - α * n| ≤ logSlack c n ∧
      |(natK D x₂ : ℝ) - β * n| ≤ logSlack c n ∧
      |(natK D (pairCode x₁ x₂) : ℝ) - γ * n| ≤ logSlack c n := by
  obtain ⟨cChain, hChain⟩ := pairPlainK_chain_upper_values D hD
  obtain ⟨cSwap, hSwap⟩ := theorem6_aux_swap D hD
  obtain ⟨cAbs, hAbs⟩ :=
    logSlack_absorb_of_le_linear cChain (⌈γ⌉₊ + c₀) (c₀ + 2 + cSwap)
  refine ⟨c₀ + c₀ + cAbs + cSwap + 1, ?_⟩
  intro n a b g x₁ x₂ ha hb hg hag hbg hK1 hK2 hC21 hC12 hKup hKlo
  -- exact values of the complexities
  have hPV : ∀ w : BitString, HasPlainComplexityValue D w (natK D w) := fun w => by
    change plainK D w = ((plainK D w).toNat : ENat)
    exact (ENat.natCast_toNat (Kolmogorov.plainK_ne_top D hD w)).symm
  have hCV : ∀ w z : BitString,
      HasPlainConditionalComplexityValue D w z (natCondK D w z) := fun w z => by
    change condK D w z = ((condK D w z).toNat : ENat)
    exact (ENat.natCast_toNat (condK_ne_top_of_optimal D hD w z)).symm
  have hsw : ∀ x y : BitString,
      natK D (pairCode y x) ≤ natK D (pairCode x y) + cSwap := by
    intro x y
    have h := hSwap x y
    have hfin := Kolmogorov.plainK_ne_top D hD (pairCode x y)
    have h' : plainK D (pairCode y x) ≤ ((natK D (pairCode x y) + cSwap : ℕ) : ENat) := by
      rw [Nat.cast_add]
      unfold natK
      rw [ENat.natCast_toNat hfin]
      exact h
    exact ENat.toNat_le_of_le_natCast h'
  -- the two chain rules
  have hch1 := hChain x₁ x₂ (natK D x₁) (natCondK D x₂ x₁) (natK D (pairCode x₁ x₂))
    (hPV x₁) (hCV x₂ x₁) (hPV _)
  have hch2 := hChain x₂ x₁ (natK D x₂) (natCondK D x₁ x₂) (natK D (pairCode x₂ x₁))
    (hPV x₂) (hCV x₁ x₂) (hPV _)
  have hsw12 := hsw x₁ x₂
  have hsw21 := hsw x₂ x₁
  -- a linear bound on `g`
  have hgR : (g : ℝ) ≤ (⌈γ⌉₊ : ℝ) * n + 1 := by
    have h1 := (abs_le.mp hg).2
    have h2 : γ * n ≤ (⌈γ⌉₊ : ℝ) * n :=
      mul_le_mul_of_nonneg_right (Nat.le_ceil γ) (Nat.cast_nonneg n)
    linarith
  have hgN : g ≤ ⌈γ⌉₊ * n + 1 := by exact_mod_cast hgR
  have hls : logSlack c₀ n ≤ c₀ * n + c₀ := logSlack_le_self_linear c₀ n
  have hA1 : logSlack cChain (natK D (pairCode x₁ x₂) + 1) ≤ logSlack cAbs n :=
    hAbs n _ (by rw [add_mul]; omega)
  have hA2 : logSlack cChain (natK D (pairCode x₂ x₁) + 1) ≤ logSlack cAbs n :=
    hAbs n _ (by rw [add_mul]; omega)
  have hsplit : logSlack (c₀ + c₀ + cAbs + cSwap + 1) n = logSlack c₀ n + logSlack c₀ n +
      logSlack cAbs n + logSlack cSwap n + logSlack 1 n := by
    simp only [logSlack_add_constants]
  have hge1 : 1 ≤ logSlack 1 n := by
    unfold logSlack
    exact Nat.le_add_left _ _
  have hgeS : cSwap ≤ logSlack cSwap n := by
    unfold logSlack
    exact Nat.le_add_left _ _
  -- natural-number bounds
  have h1u : natK D x₁ + 1 ≤ a + logSlack (c₀ + c₀ + cAbs + cSwap + 1) n := by omega
  have h1l : a + 1 ≤ natK D x₁ + logSlack (c₀ + c₀ + cAbs + cSwap + 1) n := by omega
  have h2u : natK D x₂ + 1 ≤ b + logSlack (c₀ + c₀ + cAbs + cSwap + 1) n := by omega
  have h2l : b + 1 ≤ natK D x₂ + logSlack (c₀ + c₀ + cAbs + cSwap + 1) n := by omega
  have hpu : natK D (pairCode x₁ x₂) + 1 ≤
      g + logSlack (c₀ + c₀ + cAbs + cSwap + 1) n := by omega
  have hpl : g + 1 ≤
      natK D (pairCode x₁ x₂) + logSlack (c₀ + c₀ + cAbs + cSwap + 1) n := by omega
  -- real conclusions
  have r1u : (natK D x₁ : ℝ) + 1 ≤
      (a : ℝ) + (logSlack (c₀ + c₀ + cAbs + cSwap + 1) n : ℝ) := by
    exact_mod_cast h1u
  have r1l : (a : ℝ) + 1 ≤
      (natK D x₁ : ℝ) + (logSlack (c₀ + c₀ + cAbs + cSwap + 1) n : ℝ) := by
    exact_mod_cast h1l
  have r2u : (natK D x₂ : ℝ) + 1 ≤
      (b : ℝ) + (logSlack (c₀ + c₀ + cAbs + cSwap + 1) n : ℝ) := by
    exact_mod_cast h2u
  have r2l : (b : ℝ) + 1 ≤
      (natK D x₂ : ℝ) + (logSlack (c₀ + c₀ + cAbs + cSwap + 1) n : ℝ) := by
    exact_mod_cast h2l
  have rpu : (natK D (pairCode x₁ x₂) : ℝ) + 1 ≤
      (g : ℝ) + (logSlack (c₀ + c₀ + cAbs + cSwap + 1) n : ℝ) := by
    exact_mod_cast hpu
  have rpl : (g : ℝ) + 1 ≤
      (natK D (pairCode x₁ x₂) : ℝ) + (logSlack (c₀ + c₀ + cAbs + cSwap + 1) n : ℝ) := by
    exact_mod_cast hpl
  have ha' := abs_le.mp ha
  have hb' := abs_le.mp hb
  have hg' := abs_le.mp hg
  refine ⟨?_, ?_, ?_⟩
  · rw [abs_le]
    constructor <;> linarith [ha'.1, ha'.2]
  · rw [abs_le]
    constructor <;> linarith [hb'.1, hb'.2]
  · rw [abs_le]
    constructor <;> linarith [hg'.1, hg'.2]

/-- **Theorem 6.** For reals `α, β < γ < α + β` and every `C`, for all large `n` there are
strings `x₁, x₂` with `K(x₁) = αn + O(log n)`, `K(x₂) = βn + O(log n)`,
`K(x₁, x₂) = γn + O(log n)` such that no `(C log n, C log n)`-stochastic pair is `C`-equivalent
to `⟨x₁, x₂⟩`.  Proof: Section 5. -/
theorem theorem6 (D : Map) (hD : isOptimalConditional D) (α β γ : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hαβ : γ < α + β) (hαγ : α < γ) (hβγ : β < γ) (C : ℕ) :
    ∃ c n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∃ x₁ x₂ : BitString,
      |(natK D x₁ : ℝ) - α * n| ≤ logSlack c n ∧
      |(natK D x₂ : ℝ) - β * n| ≤ logSlack c n ∧
      |(natK D (pairCode x₁ x₂) : ℝ) - γ * n| ≤ logSlack c n ∧
      ¬ ∃ x₁' x₂' : BitString,
        IsSetStochastic D (pairCode x₁' x₂') (logSlack C n) (logSlack C n) ∧
          EquivWithin D C x₁ x₁' ∧ EquivWithin D C x₂ x₂' := by
  classical
  obtain ⟨B, hB1, hRound⟩ := theorem6_rounding α β γ hα hβ hαβ hαγ hβγ
  obtain ⟨cLit, hLit⟩ := plainK_le_length D hD
  have hLitNat : ∀ w : BitString, natK D w ≤ w.length + cLit := fun w => by
    have h : plainK D w ≤ ((w.length + cLit : ℕ) : ENat) := by
      simpa [programLength] using hLit w
    exact ENat.toNat_le_of_le_natCast h
  have hlin : ∀ c m : ℕ, logSlack c m ≤ c * (m + 1) := fun c m => by
    rw [mul_add_one]
    exact logSlack_le_self_linear c m
  have hge : ∀ c m : ℕ, c ≤ logSlack c m := fun c m => by
    unfold logSlack
    exact Nat.le_add_left _ _
  obtain ⟨cN, hN⟩ := theorem6_equiv_conditional D hD C (B + cLit)
  obtain ⟨cR, hR⟩ := theorem6_stochastic_union D hD C B
  obtain ⟨cS, hS⟩ := theorem6_search D hD B
  obtain ⟨cG, hG⟩ := theorem6_degree_coding D hD (B + cR + cS)
  obtain ⟨cP, hP⟩ := theorem6_equiv_pair D hD C (B + cR + cS + cG + cLit)
  obtain ⟨K₁, hK₁⟩ : ∃ K : ℕ, K = cR + cS + cG + cP + C := ⟨_, rfl⟩
  obtain ⟨K₂, hK₂⟩ : ∃ K : ℕ, K = K₁ + cR + cN + 10 := ⟨_, rfl⟩
  obtain ⟨n₀, hn₀⟩ := hRound K₂ (by omega)
  obtain ⟨c3, h3⟩ :=
    theorem6_extraction D hD α β γ (3 * K₂ + 1 + cR + cS + cG + cLit)
  refine ⟨c3, n₀, fun n hn => ?_⟩
  obtain ⟨a, b, g, ha, hb, hg, hag, hbg, hgab, hgs, hsn, haB, hbB, hgB⟩ := hn₀ n hn
  obtain ⟨s, hs_def⟩ : ∃ s : ℕ, s = logSlack K₂ n := ⟨_, rfl⟩
  rw [← hs_def] at hag hbg hgab hgs hsn
  -- slack bookkeeping
  have hK₁split : logSlack K₁ n = logSlack cR n + logSlack cS n + logSlack cG n +
      logSlack cP n + logSlack C n := by
    rw [hK₁]
    simp only [logSlack_add_constants]
  have hK₂split : s = logSlack K₁ n + logSlack cR n + logSlack cN n + logSlack 10 n := by
    rw [hs_def, hK₂]
    simp only [logSlack_add_constants]
  have hc₀split : logSlack (3 * K₂ + 1 + cR + cS + cG + cLit) n =
      3 * s + logSlack 1 n + logSlack cR n + logSlack cS n + logSlack cG n +
        logSlack cLit n := by
    rw [hs_def]
    unfold logSlack
    ring
  have h10 := hge 10 n
  have h1 := hge 1 n
  have hcLit := hge cLit n
  have hs10 : 10 ≤ s := by omega
  -- the set `R̂`
  have ht : logSlack K₁ n ≤ n := by omega
  obtain ⟨R, hRcard, hRK, hRmem⟩ := hR n g (logSlack K₁ n) hgB ht
  have hRcard' : R.card ≤ 2 ^ (g + s) :=
    hRcard.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
  -- the graph `A`
  obtain ⟨A₀, hA₀⟩ := theorem6_random_graph a b g s R hRcard' hs10 hgs hag hbg hgab
  have hnB : n ≤ B * (n + 1) :=
    calc n ≤ 1 * (n + 1) := by omega
      _ ≤ B * (n + 1) := Nat.mul_le_mul_right _ hB1
  have hsB : s ≤ B * (n + 1) := by omega
  have hmul : ∀ c : ℕ, c ≤ c * (n + 1) := fun c => Nat.le_mul_of_pos_right c (Nat.succ_pos n)
  obtain ⟨A, hA, hAK⟩ := hS n a b g s R haB hbB hgB hsB ⟨A₀, hA₀⟩
  have hAK' : natK D (theorem6_graphCode A) ≤ logSlack cR n + logSlack cS n := by omega
  obtain ⟨hAsub, hAcard, hdeg1, hdeg2, hnear⟩ := hA
  -- `C`-equivalence is a nearness relation
  have hSimple : ∀ (m : ℕ) (x : BitString), x ∈ stringsOfLength m → m ≤ B * (n + 1) →
      natK D x ≤ (B + cLit) * (n + 1) := by
    intro m x hx hm
    have hxl : x.length = m := (mem_stringsOfLength _ _).1 hx
    have := hLitNat x
    have := hmul cLit
    rw [add_mul]
    omega
  have hNear : ∀ m : ℕ, m ≤ B * (n + 1) →
      theorem6_IsNearness (stringsOfLength m) s (fun x y => EquivWithin D C x y) := by
    intro m hm
    have hTs : logSlack cN n + 1 ≤ s := by omega
    refine ⟨fun x hx F hF => ?_, fun y F hFS hF => ?_⟩
    · have hlt := theorem6_count_conditional D hD x (logSlack cN n) F
        (fun y hy => (hN n x y (hSimple m x hx hm) (hF y hy)).1)
      exact hlt.le.trans (Nat.pow_le_pow_right (by norm_num) hTs)
    · have hlt := theorem6_count_conditional D hD y (logSlack cN n) F
        (fun x hx => (hN n x y (hSimple m x (hFS hx) hm) (hF x hx)).2)
      exact hlt.le.trans (Nat.pow_le_pow_right (by norm_num) hTs)
  have hBig := hnear _ _ (hNear a haB) (hNear b hbB)
  have hg3 : g - 3 * s - 1 + 1 = g - 3 * s := by omega
  rw [← hg3] at hBig
  -- an edge of high complexity that is not close to `R̂`
  obtain ⟨e, heB, heK⟩ := theorem6_count_high_complexity_edge D hD _ _ hBig
  rw [Finset.mem_filter] at heB
  obtain ⟨heA, hens⟩ := heB
  have he12 : e.1 ∈ stringsOfLength a ∧ e.2 ∈ stringsOfLength b :=
    Finset.mem_product.1 (hAsub heA)
  have heA' : (e.1, e.2) ∈ A := by simpa using heA
  have hAKB : natK D (theorem6_graphCode A) ≤ (B + cR + cS) * (n + 1) := by
    have h1 := hlin cR n
    have h2 := hlin cS n
    rw [add_mul, add_mul]
    omega
  have hgB' : g ≤ (B + cR + cS) * (n + 1) := by
    rw [add_mul, add_mul]
    omega
  obtain ⟨hKe, hK21, hK12⟩ := hG n g (g - a) (g - b) A e.1 e.2 hgB'
    ((Nat.sub_le g a).trans hgB') ((Nat.sub_le g b).trans hgB') hAKB heA' hAcard
    (hdeg1 e.1) (hdeg2 e.2)
  have he1K : natK D e.1 ≤ a + cLit := by
    have := hLitNat e.1
    have hl := (mem_stringsOfLength _ _).1 he12.1
    omega
  have he2K : natK D e.2 ≤ b + cLit := by
    have := hLitNat e.2
    have hl := (mem_stringsOfLength _ _).1 he12.2
    omega
  -- the complexity profile of the edge
  obtain ⟨r1, r2, r3⟩ := h3 n a b g e.1 e.2 ha hb hg (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  refine ⟨e.1, e.2, r1, r2, r3, ?_⟩
  -- no stochastic pair is `C`-equivalent to the edge
  rintro ⟨x₁', x₂', hst, hE1, hE2⟩
  apply hens
  refine ⟨x₁', x₂', ?_, hE1, hE2⟩
  apply hRmem _ hst
  have hlG := hlin cG n
  have hlR := hlin cR n
  have hlS := hlin cS n
  have hmL := hmul cLit
  have hPb := hP n e.1 e.2 x₁' x₂' (by rw [add_mul, add_mul, add_mul, add_mul]; omega)
    (by rw [add_mul, add_mul, add_mul, add_mul]; omega)
    (by rw [add_mul, add_mul, add_mul, add_mul]; omega) hE1 hE2
  omega

end Kolmogorov.Relativization
