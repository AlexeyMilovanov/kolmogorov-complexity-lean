/-
Copyright (c) 2026 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Relativization.Definitions
import KolmogorovMathlib.Complexity.Information.MutualInformation

/-!
# Quantifier-free formulae: Proposition 1 and Theorem 3 of Muchnik–Romashchenko

Sections 1 and 2 of the paper; the proof is at the beginning of Section 4.
-/

namespace Kolmogorov.Relativization

open Finset

private def proposition1_positions {n : ℕ} (V : Finset (Fin n)) : List ℕ :=
  (V.sort (· ≤ ·)).map Fin.val

private def proposition1_projectListCode (positions : List ℕ) (w : BitString) : BitString :=
  listCode (positions.map fun k => (decodeListCode w).getD k [])

private lemma proposition1_projectListCode_primrec (positions : List ℕ) :
    Primrec (proposition1_projectListCode positions) := by
  induction positions with
  | nil => exact Primrec.const []
  | cons k positions ih =>
      have hget : Primrec (fun w : BitString => (decodeListCode w).getD k []) :=
        (Primrec.list_getD ([] : BitString)).comp decodeListCode_primrec (Primrec.const k)
      exact Primrec.of_eq (CodedFiniteDistribution.pairCode_primrec.comp hget ih) (by
        intro w
        unfold proposition1_projectListCode
        rfl)

private lemma proposition1_projectListCode_computable (positions : List ℕ) :
    Computable (proposition1_projectListCode positions) :=
  (proposition1_projectListCode_primrec positions).to_comp

private def proposition1_projectPairCode (positions : List ℕ) (w : BitString) : BitString :=
  pairCode (proposition1_projectListCode positions (decodeFirst w)) (decodeSecond w)

private lemma proposition1_projectPairCode_computable (positions : List ℕ) :
    Computable (proposition1_projectPairCode positions) := by
  exact CodedFiniteDistribution.pairCode_primrec.to_comp.comp
    ((proposition1_projectListCode_computable positions).comp decodeFirst_computable)
    decodeSecond_computable

private lemma proposition1_projectListCode_tupleCode (n : ℕ) (V : Finset (Fin n))
    (x : Fin n → BitString) :
    proposition1_projectListCode (proposition1_positions V) (tupleCode x) = subtupleCode x V := by
  unfold proposition1_projectListCode proposition1_positions subtupleCode
  simp only [tupleCode, decodeListCode_listCode]
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hget : (List.ofFn x).getD i.val [] = x i := by
    rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact i.isLt),
      List.getElem_ofFn]
  exact hget

private noncomputable def proposition1_condMapOverhead (D : Map)
    (hD : isOptimalConditional D) (n : ℕ) (V : Finset (Fin n)) : ℕ :=
  Classical.choose (condK_cond_map_le D hD
    (proposition1_projectListCode (proposition1_positions V))
    (proposition1_projectListCode_computable _))

private lemma proposition1_condMapOverhead_spec (D : Map) (hD : isOptimalConditional D)
    (n : ℕ) (V : Finset (Fin n)) (a z : BitString) :
    condK D a z ≤
      condK D a (proposition1_projectListCode (proposition1_positions V) z) +
        (proposition1_condMapOverhead D hD n V : ℕ∞) := by
  exact Classical.choose_spec (condK_cond_map_le D hD
    (proposition1_projectListCode (proposition1_positions V))
    (proposition1_projectListCode_computable _)) a z

private noncomputable def proposition1_pairMapOverhead (D : Map)
    (hD : isOptimalConditional D) (n : ℕ) (V : Finset (Fin n)) : ℕ :=
  Classical.choose (plainK_map_le D hD
    (proposition1_projectPairCode (proposition1_positions V))
    (proposition1_projectPairCode_computable _))

private lemma proposition1_pairMapOverhead_spec (D : Map) (hD : isOptimalConditional D)
    (n : ℕ) (V : Finset (Fin n)) (w : BitString) :
    plainK D (proposition1_projectPairCode (proposition1_positions V) w) ≤
      plainK D w + (proposition1_pairMapOverhead D hD n V : ℕ∞) := by
  exact Classical.choose_spec (plainK_map_le D hD
    (proposition1_projectPairCode (proposition1_positions V))
    (proposition1_projectPairCode_computable _)) w

/-- The two orientations of mutual information between two strings differ by at most logarithmic
slack, by symmetry of information. -/
private theorem proposition1_mutual_information_symmetry
    (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ a z : BitString,
      natK D a + natCondK D z a ≤
          natK D z + natCondK D a z + logSlack c (natK D (pairCode a z)) ∧
        natK D z + natCondK D a z ≤
          natK D a + natCondK D z a + logSlack c (natK D (pairCode a z)) := by
  obtain ⟨cPair, hPair⟩ := Kolmogorov.pairPlainK_symmetryOfInformation_values D hD
  obtain ⟨cSwap, hSwap⟩ := plainK_map_le D hD Kolmogorov.swapPairCode
    Kolmogorov.swapPairCode_computable
  obtain ⟨cFold, hFold⟩ := logSlack_linear_bound cPair 1 (cSwap + 1)
  refine ⟨2 * cFold + cSwap, fun a z => ?_⟩
  let ka := natK D a
  let kz := natK D z
  let kaz := natCondK D z a
  let kza := natCondK D a z
  let kp := natK D (pairCode a z)
  let kp' := natK D (pairCode z a)
  have ha : HasPlainComplexityValue D a ka := by
    unfold HasPlainComplexityValue ka natK
    exact (ENat.natCast_toNat (plainK_ne_top D hD a)).symm
  have hz : HasPlainComplexityValue D z kz := by
    unfold HasPlainComplexityValue kz natK
    exact (ENat.natCast_toNat (plainK_ne_top D hD z)).symm
  have haz : HasPlainConditionalComplexityValue D z a kaz := by
    unfold HasPlainConditionalComplexityValue kaz natCondK
    exact (ENat.natCast_toNat (condK_ne_top_of_optimal D hD z a)).symm
  have hza : HasPlainConditionalComplexityValue D a z kza := by
    unfold HasPlainConditionalComplexityValue kza natCondK
    exact (ENat.natCast_toNat (condK_ne_top_of_optimal D hD a z)).symm
  have hp : HasPlainComplexityValue D (pairCode a z) kp := by
    unfold HasPlainComplexityValue kp natK
    exact (ENat.natCast_toNat (plainK_ne_top D hD (pairCode a z))).symm
  have hp' : HasPlainComplexityValue D (pairCode z a) kp' := by
    unfold HasPlainComplexityValue kp' natK
    exact (ENat.natCast_toNat (plainK_ne_top D hD (pairCode z a))).symm
  have hAZ := hPair a z ka kaz kp ha haz hp
  have hZA := hPair z a kz kza kp' hz hza hp'
  have hSwapAZ : kp' ≤ kp + cSwap := by
    have h := hSwap (pairCode a z)
    rw [Kolmogorov.swapPairCode_pairCode] at h
    have h' := h
    rw [← ENat.natCast_toNat (plainK_ne_top D hD (pairCode z a)),
      ← ENat.natCast_toNat (plainK_ne_top D hD (pairCode a z))] at h'
    exact_mod_cast h'
  have hSwapZA : kp ≤ kp' + cSwap := by
    have h := hSwap (pairCode z a)
    rw [Kolmogorov.swapPairCode_pairCode] at h
    have h' := h
    rw [← ENat.natCast_toNat (plainK_ne_top D hD (pairCode a z)),
      ← ENat.natCast_toNat (plainK_ne_top D hD (pairCode z a))] at h'
    exact_mod_cast h'
  have hFoldA : logSlack cPair (kp + 1) ≤ logSlack cFold kp := by
    exact logSlack_le_of_linear_bound hFold (by dsimp [kp]; omega)
  have hFoldZ : logSlack cPair (kp' + 1) ≤ logSlack cFold kp := by
    exact logSlack_le_of_linear_bound hFold (by dsimp [kp, kp']; omega)
  have hFoldSum : logSlack cFold kp + cSwap + logSlack cFold kp ≤
      logSlack (2 * cFold + cSwap) kp := by
    calc
      logSlack cFold kp + cSwap + logSlack cFold kp =
          logSlack (cFold + cFold) kp + cSwap := by
        rw [← logSlack_add_const]
        omega
      _ ≤ logSlack (cFold + cFold + cSwap) kp :=
        logSlack_add_nat_le (cFold + cFold) cSwap kp
      _ = logSlack (2 * cFold + cSwap) kp := by congr 1; omega
  dsimp [ka, kz, kaz, kza, kp, kp'] at *
  constructor <;> omega

/-- **Proposition 1.** With `δ = K(x̄) − K(x̄ | z)`, for every subtuple
`K(x̄_V) − K(x̄_V | z) ≤ δ + O(log N)`, `N = K(x̄, z)`; the constant depends on `n` only.
Proof: Section 4 (`I(x̄_V : z) ≤ I(x̄ : z) + O(log N)`). -/
theorem proposition1 (D : Map) (hD : isOptimalConditional D) (n : ℕ) :
    ∃ c : ℕ, ∀ (x : Fin n → BitString) (z : BitString) (V : Finset (Fin n)),
      subK D x V + natCondK D (tupleCode x) z ≤
        subKRel D x z V + natK D (tupleCode x) +
          logSlack c (natK D (pairCode (tupleCode x) z)) := by
  obtain ⟨cSym, hSym⟩ := proposition1_mutual_information_symmetry D hD
  let cCond := Finset.univ.sup fun V : Finset (Fin n) =>
    proposition1_condMapOverhead D hD n V
  let cPair := Finset.univ.sup fun V : Finset (Fin n) =>
    proposition1_pairMapOverhead D hD n V
  obtain ⟨cFold, hFold⟩ := logSlack_linear_bound cSym 1 cPair
  refine ⟨2 * cFold + cCond, fun x z V => ?_⟩
  let pos := proposition1_positions V
  let a := subtupleCode x V
  let t := tupleCode x
  let N := natK D (pairCode t z)
  have hProj : proposition1_projectListCode pos t = a := by
    exact proposition1_projectListCode_tupleCode n V x
  have hPairCode : proposition1_projectPairCode pos (pairCode t z) = pairCode a z := by
    dsimp [proposition1_projectPairCode, pos, t, a]
    simp only [decodeFirst_pairCode, decodeSecond_pairCode]
    rw [proposition1_projectListCode_tupleCode]
  have hCCondBound : proposition1_condMapOverhead D hD n V ≤ cCond := by
    exact Finset.le_sup (Finset.mem_univ V)
  have hCPairBound : proposition1_pairMapOverhead D hD n V ≤ cPair := by
    exact Finset.le_sup (Finset.mem_univ V)
  have hPairENat := proposition1_pairMapOverhead_spec D hD n V (pairCode t z)
  rw [hPairCode] at hPairENat
  have hPairNatV : natK D (pairCode a z) ≤
      N + proposition1_pairMapOverhead D hD n V := by
    unfold natK
    have hLeft := plainK_ne_top D hD (pairCode a z)
    have hRight := plainK_ne_top D hD (pairCode t z)
    rw [← ENat.natCast_toNat hLeft, ← ENat.natCast_toNat hRight] at hPairENat
    exact_mod_cast hPairENat
  have hPairNat : natK D (pairCode a z) ≤ N + cPair :=
    hPairNatV.trans (Nat.add_le_add_left hCPairBound N)
  have hCondENat := proposition1_condMapOverhead_spec D hD n V z t
  rw [hProj] at hCondENat
  have hCondNat : natCondK D z t ≤ natCondK D z a + cCond := by
    have hCondNatV : natCondK D z t ≤
        natCondK D z a + proposition1_condMapOverhead D hD n V := by
      unfold natCondK
      have hLeft := condK_ne_top_of_optimal D hD z t
      have hRight := condK_ne_top_of_optimal D hD z a
      rw [← ENat.natCast_toNat hLeft, ← ENat.natCast_toNat hRight] at hCondENat
      exact_mod_cast hCondENat
    exact hCondNatV.trans (Nat.add_le_add_left hCCondBound _)
  have hSymA := (hSym a z).1
  have hSymT := (hSym t z).2
  have hSlackA : logSlack cSym (natK D (pairCode a z)) ≤ logSlack cFold N := by
    exact logSlack_le_of_linear_bound hFold (by dsimp [N]; omega)
  have hSlackA' : logSlack cSym (natK D (pairCode a z)) ≤
      logSlack cFold (natK D (pairCode t z)) := by
    simpa [N] using hSlackA
  have hSlackT : logSlack cSym N ≤ logSlack cFold N := by
    calc
      logSlack cSym N ≤ logSlack cSym (1 * N + cPair) :=
        logSlack_mono_right cSym (by omega)
      _ ≤ logSlack cFold N := hFold N
  have hSlackT' : logSlack cSym (natK D (pairCode t z)) ≤
      logSlack cFold (natK D (pairCode t z)) := by
    simpa [N] using hSlackT
  have hSlackSum : logSlack cFold N + cCond + logSlack cFold N ≤
      logSlack (2 * cFold + cCond) N := by
    calc
      logSlack cFold N + cCond + logSlack cFold N =
          logSlack (cFold + cFold) N + cCond := by
        rw [← logSlack_add_const]
        omega
      _ ≤ logSlack (cFold + cFold + cCond) N :=
        logSlack_add_nat_le (cFold + cFold) cCond N
      _ = logSlack (2 * cFold + cCond) N := by congr 1; omega
  have hSlackSum' :
      logSlack cFold (natK D (pairCode t z)) + cCond +
        logSlack cFold (natK D (pairCode t z)) ≤
      logSlack (2 * cFold + cCond) (natK D (pairCode t z)) := by
    simpa [N] using hSlackSum
  change natK D a + natCondK D t z ≤ natCondK D a z + natK D t +
    logSlack (2 * cFold + cCond) (natK D (pairCode t z))
  have hCore : natK D a + natCondK D t z ≤ natCondK D a z + natK D t +
      logSlack cFold (natK D (pairCode t z)) + cCond +
        logSlack cFold (natK D (pairCode t z)) := by
    omega
  exact hCore.trans (by omega)

/-- **Theorem 3.** If `I(x̄ : z) ≤ δ`, then the complexity profiles `K(x̄)` and `K(x̄ | z)` differ
componentwise by at most `δ + O(log K(x̄, z))`.  Proof: Section 4. -/
theorem theorem3 (D : Map) (hD : isOptimalConditional D) (n : ℕ) :
    ∃ c : ℕ, ∀ (x : Fin n → BitString) (z : BitString) (δ : ℕ),
      MutualInfoLe D (tupleCode x) z δ →
        ProfileWithin (subK D x) (subKRel D x z)
          (δ + logSlack c (natK D (pairCode (tupleCode x) z))) := by
  obtain ⟨c₁, h₁⟩ := proposition1 D hD n
  obtain ⟨c₂, h₂⟩ := condK_le_plainK D hD
  refine ⟨max c₁ c₂, ?_⟩
  intro x z δ hI V hV
  constructor
  · have hP := h₁ x z V
    have hslack :
        logSlack c₁ (natK D (pairCode (tupleCode x) z)) ≤
          logSlack (max c₁ c₂) (natK D (pairCode (tupleCode x) z)) :=
      logSlack_mono_left (Nat.le_max_left c₁ c₂) _
    change natK D (tupleCode x) ≤ natCondK D (tupleCode x) z + δ at hI
    omega
  · have hraw := h₂ (subtupleCode x V) z
    have hfiniteCond : condK D (subtupleCode x V) z ≠ ⊤ := by
      obtain ⟨c₀, h₀⟩ := plainK_le_length D hD
      apply ne_top_of_le_natCast_add
      calc
        condK D (subtupleCode x V) z ≤
            plainK D (subtupleCode x V) + (c₂ : ENat) := hraw
        _ ≤ (programLength (subtupleCode x V) : ENat) + (c₀ : ENat) + c₂ := by
          gcongr
          exact h₀ _
    have hfinitePlain : plainK D (subtupleCode x V) ≠ ⊤ := by
      obtain ⟨c₀, h₀⟩ := plainK_le_length D hD
      exact ne_top_of_le_natCast_add (h₀ _)
    rw [← ENat.natCast_toNat hfiniteCond,
      ← ENat.natCast_toNat hfinitePlain] at hraw
    have hnat :
        natCondK D (subtupleCode x V) z ≤ natK D (subtupleCode x V) + c₂ := by
      exact_mod_cast hraw
    have hconst : c₂ ≤ logSlack (max c₁ c₂)
        (natK D (pairCode (tupleCode x) z)) := by
      unfold logSlack
      omega
    change natCondK D (subtupleCode x V) z ≤
      natK D (subtupleCode x V) +
        (δ + logSlack (max c₁ c₂) (natK D (pairCode (tupleCode x) z)))
    omega

end Kolmogorov.Relativization
