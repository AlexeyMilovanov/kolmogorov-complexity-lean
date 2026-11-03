/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.MDLPrediction.Mean.Sanitizer
import KolmogorovMathlib.MDLPrediction.Core.Index

/-!
# Pair-index complexity compiler

One machine constant precedes the measures. Shortest programs for their numeric
indices are paired to select the corresponding member of the sanitized family.
Blueprint nodes: `exp:mean-compiler`.
-/

namespace Kolmogorov.MDLPrediction

open MeasureTheory
open scoped ENNReal

/-- Pairing numeric codes costs at most an additive constant in prefix complexity. -/
private lemma KPNat_pair_le (U : Map) (hU : IsOptimalPrefixConditional U) :
  ∃ c : ℕ, ∀ (eP eQ : ℕ), KPNat U (Nat.pair eP eQ) ≤ KPNat U eP + KPNat U eQ + c := by
  let f := fun z : BitString => natToBitString
    (Nat.pair (bitStringToNat (decodeFirst z)) (bitStringToNat (decodeSecond z)))
  have hf : Computable f :=
    computable_natToBitString.comp
      (Primrec₂.natPair.to_comp.comp
        (computable_bitStringToNat.comp decodeFirst_computable)
        (computable_bitStringToNat.comp decodeSecond_computable))
  obtain ⟨c1, h1⟩ := KPPlain_map_le U hU f hf
  obtain ⟨c2, h2⟩ := KPPair_le_KPPlain_add_KPPlain U hU
  use c1 + c2
  intro eP eQ
  have H1 := h1 (pairCode (natToBitString eP) (natToBitString eQ))
  have H2 := h2 (natToBitString eP) (natToBitString eQ)
  have h_simp : f (pairCode (natToBitString eP) (natToBitString eQ)) =
      natToBitString (Nat.pair eP eQ) := by
    dsimp [f]
    rw [decodeFirst_pairCode, decodeSecond_pairCode]
    rw [bitStringToNat_natToBitString, bitStringToNat_natToBitString]
  have h3 : KPNat U (Nat.pair eP eQ) ≤ KPNat U eP + KPNat U eQ + (c1 + c2 : ℕ) := by
    calc
      KPNat U (Nat.pair eP eQ)
        = KPPlain U (natToBitString (Nat.pair eP eQ)) := rfl
      _ = KPPlain U (f (pairCode (natToBitString eP) (natToBitString eQ))) := by rw [h_simp]
      _ ≤ KPPlain U (pairCode (natToBitString eP) (natToBitString eQ)) + c1 := H1
      _ = KPPair U (natToBitString eP) (natToBitString eQ) + c1 := rfl
      _ ≤ KPPlain U (natToBitString eP) + KPPlain U (natToBitString eQ) + c2 + c1 := by gcongr
      _ = KPNat U eP + KPNat U eQ + (c1 + c2 : ℕ) := by
        dsimp [KPNat]
        push_cast
        abel
  exact h3

/-- The numeric pair-complexity bound passes to finite natural values. -/
private theorem KPNat_pair_toNat_le
    (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ eP eQ : ℕ,
      (KPNat U (Nat.pair eP eQ)).toNat ≤
        (KPNat U eP).toNat + (KPNat U eQ).toNat + c := by
  obtain ⟨c, hc⟩ := KPNat_pair_le U hU
  use c
  intro eP eQ
  have h := hc eP eQ
  have H_eP : KPNat U eP ≠ ⊤ := by
    obtain ⟨c', hc'⟩ := KPPlain_le_length_add_log U hU
    have h_len := hc' (natToBitString eP)
    have h_fin : (↑((natToBitString eP).length + 2 *
        (Nat.bits (natToBitString eP).length).length) + (c' : ℕ∞) : ℕ∞) ≠ ⊤ := by
      exact WithTop.add_ne_top.mpr ⟨ENat.natCast_ne_top _, ENat.natCast_ne_top _⟩
    exact ne_top_of_le_ne_top h_fin h_len
  have H_eQ : KPNat U eQ ≠ ⊤ := by
    obtain ⟨c', hc'⟩ := KPPlain_le_length_add_log U hU
    have h_len := hc' (natToBitString eQ)
    have h_fin : (↑((natToBitString eQ).length + 2 *
        (Nat.bits (natToBitString eQ).length).length) + (c' : ℕ∞) : ℕ∞) ≠ ⊤ := by
      exact WithTop.add_ne_top.mpr ⟨ENat.natCast_ne_top _, ENat.natCast_ne_top _⟩
    exact ne_top_of_le_ne_top h_fin h_len
  have h_le : KPNat U (Nat.pair eP eQ) ≤ ↑((KPNat U eP).toNat + (KPNat U eQ).toNat + c) := by
    calc KPNat U (Nat.pair eP eQ)
      _ ≤ KPNat U eP + KPNat U eQ + (c : ℕ∞) := h
      _ = ↑((KPNat U eP).toNat) + ↑((KPNat U eQ).toNat) + ↑c := by
        congr 2
        · exact (ENat.natCast_toNat H_eP).symm
        · exact (ENat.natCast_toNat H_eQ).symm
      _ = ↑((KPNat U eP).toNat + (KPNat U eQ).toNat + c) := by push_cast; rfl
  exact ENat.toNat_le_of_le_natCast h_le

/-- A valid pair can be represented in the sanitized family by an index with
complexity bounded by the two measure complexities and one fixed constant.
Blueprint node `exp:mean-compiler`. -/
theorem exp_mean_compiler (U : Map) (hU : IsOptimalPrefixConditional U)
    (ν : ℕ → BitString → ℝ≥0∞)
    (hν : ∀ (P Q : Measure CantorSeq) [IsProbabilityMeasure P]
      [IsProbabilityMeasure Q], ∀ eP eQ,
        IsComputableMeasureIndex P eP → IsComputableMeasureIndex Q eQ →
          ∀ x, ν (Nat.pair eP eQ) x = meanTree P Q x) :
    ∃ c : ℕ, ∀ (P Q : Measure CantorSeq) [IsProbabilityMeasure P]
      [IsProbabilityMeasure Q], IsComputableMeasure P → IsComputableMeasure Q →
        ∃ e : ℕ, (∀ x, ν e x = meanTree P Q x) ∧
          (KPNat U e).toNat ≤
            (computableMeasureComplexity U P).toNat +
            (computableMeasureComplexity U Q).toNat + c := by
  obtain ⟨c, hc⟩ := KPNat_pair_toNat_le U hU
  use c
  intro P Q _ _ hcompP hcompQ
  obtain ⟨_, ⟨eP, heP1, heP2⟩⟩ := base_complexity_attained U hU P hcompP
  obtain ⟨_, ⟨eQ, heQ1, heQ2⟩⟩ := base_complexity_attained U hU Q hcompQ
  use Nat.pair eP eQ
  constructor
  · exact hν P Q eP eQ heP1 heQ1
  · have hbound := hc eP eQ
    rw [heP2, heQ2] at hbound
    exact hbound

end Kolmogorov.MDLPrediction
