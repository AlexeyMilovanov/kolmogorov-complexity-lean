/-
Copyright (c) 2026 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Relativization.CommonInformation.CloneCoordinateChains
import KolmogorovMathlib.Relativization.CommonInformation.ExtractionIndexBounds
import KolmogorovMathlib.Relativization.CommonInformation.PairCloneBounds

/-!
# Pair Padding Bounds

This module proves the pair-extraction and oracle-replacement bounds used in the
relativized common-information argument. It formalizes the pair-padding part of the proof of
Theorem 2 in Muchnik and Romashchenko, “Stability of properties of Kolmogorov complexity under
relativization.”
-/

namespace Kolmogorov.Relativization
open Filter Asymptotics

/-- The short descriptions relative to `x₁` and the bounds on `z'`, `z''` give
a linear plain complexity bound for the paired extracted string.
the short descriptions relative to `x₁` and the bounds on `z'`, `z''` give a linear plain
complexity bound for the paired extracted string. -/
private theorem theorem2_linear_pair_complexity
    (D : Map) (hD : isOptimalConditional D) (c₀ : ℕ) :
    ∃ A : ℕ, ∀ (x₁ x₂ z : BitString) (t M : ℕ)
      (v' z' v'' z'' : BitString),
      M = natK D (pairCode (pairCode x₁ x₂) z) →
      t ≤ M →
      natCondK D v' (pairCode x₁ z') ≤ t + logSlack c₀ M →
      natCondK D v'' (pairCode x₁ z'') ≤ t + logSlack c₀ M →
      natK D z' ≤ natK D z + logSlack c₀ M →
      natK D z'' ≤ natK D z + logSlack c₀ M →
      natK D (pairCode v' v'') ≤ A * (M + 1) := by
  obtain ⟨cProjX, hProjX⟩ := plainK_map_le D hD
    (decodeFirst ∘ decodeFirst)
    (decodeFirst_computable.comp decodeFirst_computable)
  obtain ⟨cProjZ, hProjZ⟩ := plainK_map_le D hD decodeSecond decodeSecond_computable
  obtain ⟨cPair, hPair⟩ := plainK_pair_le_add_two_log D hD
  obtain ⟨cDesc, hDesc⟩ :=
    theorem2_plain_from_conditional
      D hD (5 + 2 * c₀ + 3 * cProjX + cProjZ + cPair)
  have hFold₀ := logSlack_le_self_linear c₀
  have hFoldD := logSlack_le_self_linear cDesc
  let B := 5 + 2 * c₀ + 3 * cProjX + cProjZ + cPair
  let C := B + 1 + c₀ + cDesc
  refine ⟨4 * C + cPair, ?_⟩
  intro x₁ x₂ z t M v' z' v'' z'' hM ht hv₁ hv₂ hz₁ hz₂
  let w := pairCode (pairCode x₁ x₂) z
  have hProjXRaw := hProjX w
  have hProjXBound : plainK D x₁ ≤ plainK D w + (cProjX : ℕ∞) := by
    simpa [w, Function.comp_apply, decodeFirst_pairCode] using hProjXRaw
  have hX₁ : natK D x₁ ≤ M + cProjX := by
    rw [← ENat.natCast_toNat (plainK_ne_top D hD x₁),
      ← ENat.natCast_toNat (plainK_ne_top D hD w)] at hProjXBound
    have hNat : natK D x₁ ≤ natK D w + cProjX := by exact_mod_cast hProjXBound
    simpa [w, hM] using hNat
  have hProjZRaw := hProjZ w
  have hProjZBound : plainK D z ≤ plainK D w + (cProjZ : ℕ∞) := by
    simpa [w, decodeSecond_pairCode] using hProjZRaw
  have hZ : natK D z ≤ M + cProjZ := by
    rw [← ENat.natCast_toNat (plainK_ne_top D hD z),
      ← ENat.natCast_toNat (plainK_ne_top D hD w)] at hProjZBound
    have hNat : natK D z ≤ natK D w + cProjZ := by exact_mod_cast hProjZBound
    simpa [w, hM] using hNat
  have hSlack₀ : logSlack c₀ M ≤ c₀ * (M + 1) := by
    have h := hFold₀ M
    simpa [Nat.mul_succ] using h
  have hSlackD : logSlack cDesc M ≤ cDesc * (M + 1) := by
    have h := hFoldD M
    simpa [Nat.mul_succ] using h
  have hZ' : natK D z' ≤ (1 + c₀) * (M + 1) + cProjZ := by
    nlinarith [hz₁, hZ, hSlack₀]
  have hZ'' : natK D z'' ≤ (1 + c₀) * (M + 1) + cProjZ := by
    nlinarith [hz₂, hZ, hSlack₀]
  have hPairCtx (y : BitString) :
      natK D (pairCode x₁ y) ≤ 3 * natK D x₁ + natK D y + cPair := by
    have h := hPair x₁ y
    change plainK D (pairCode x₁ y) ≤ plainK D x₁ + plainK D y +
      ((2 * Nat.log 2 (cVal D x₁) + cPair : ℕ) : ℕ∞) at h
    rw [← ENat.natCast_toNat (plainK_ne_top D hD (pairCode x₁ y)),
      ← ENat.natCast_toNat (plainK_ne_top D hD x₁),
      ← ENat.natCast_toNat (plainK_ne_top D hD y)] at h
    have hNat : natK D (pairCode x₁ y) ≤ natK D x₁ + natK D y +
        (2 * Nat.log 2 (cVal D x₁) + cPair) := by exact_mod_cast h
    have hCVal : cVal D x₁ = natK D x₁ := rfl
    rw [hCVal] at hNat
    have hLog : Nat.log 2 (natK D x₁) ≤ natK D x₁ := Nat.log_le_self 2 _
    omega
  have hContext₁ : natK D (pairCode x₁ z') ≤ B * (M + 1) := by
    have h := hPairCtx z'
    dsimp [B]
    nlinarith [h, hX₁, hZ']
  have hContext₂ : natK D (pairCode x₁ z'') ≤ B * (M + 1) := by
    have h := hPairCtx z''
    dsimp [B]
    nlinarith [h, hX₁, hZ'']
  have hV' : natK D v' ≤ C * (M + 1) := by
    have h := hDesc v' (pairCode x₁ z') M hContext₁
    dsimp [C]
    nlinarith [h, hv₁, hSlack₀, hSlackD, ht]
  have hV'' : natK D v'' ≤ C * (M + 1) := by
    have h := hDesc v'' (pairCode x₁ z'') M hContext₂
    dsimp [C]
    nlinarith [h, hv₂, hSlack₀, hSlackD, ht]
  have hPairUV : natK D (pairCode v' v'') ≤
      3 * natK D v' + natK D v'' + cPair := by
    have h := hPair v' v''
    change plainK D (pairCode v' v'') ≤ plainK D v' + plainK D v'' +
      ((2 * Nat.log 2 (cVal D v') + cPair : ℕ) : ℕ∞) at h
    rw [← ENat.natCast_toNat (plainK_ne_top D hD (pairCode v' v'')),
      ← ENat.natCast_toNat (plainK_ne_top D hD v'),
      ← ENat.natCast_toNat (plainK_ne_top D hD v'')] at h
    have hNat : natK D (pairCode v' v'') ≤ natK D v' + natK D v'' +
        (2 * Nat.log 2 (cVal D v') + cPair) := by exact_mod_cast h
    have hCVal : cVal D v' = natK D v' := rfl
    rw [hCVal] at hNat
    have hLog : Nat.log 2 (natK D v') ≤ natK D v' := Nat.log_le_self 2 _
    omega
  have hConst : cPair ≤ cPair * (M + 1) := by
    have hM : 1 ≤ M + 1 := by omega
    simpa using Nat.mul_le_mul_left cPair hM
  have hScaledV' : 3 * natK D v' ≤ 3 * C * (M + 1) := by
    calc
      3 * natK D v' ≤ 3 * (C * (M + 1)) := Nat.mul_le_mul_left 3 hV'
      _ = 3 * C * (M + 1) := by ring
  have hScaledPair : 3 * natK D v' + natK D v'' ≤ 4 * C * (M + 1) := by
    calc
      3 * natK D v' + natK D v'' ≤ 3 * C * (M + 1) + C * (M + 1) :=
        Nat.add_le_add hScaledV' hV''
      _ = 4 * C * (M + 1) := by ring
  have hFinal : natK D (pairCode v' v'') ≤ (4 * C + cPair) * (M + 1) := by
    calc
      natK D (pairCode v' v'') ≤ 3 * natK D v' + natK D v'' + cPair := hPairUV
      _ ≤ 4 * C * (M + 1) + cPair := Nat.add_le_add_right hScaledPair cPair
      _ ≤ 4 * C * (M + 1) + cPair * (M + 1) :=
        Nat.add_le_add_left hConst _
      _ = (4 * C + cPair) * (M + 1) := by rw [Nat.add_mul]
  simpa using hFinal

/-- Given the linear plain complexity bound, combine the two descriptions available from each
`xᵢ` to describe the extracted pair relative to the paired oracle.
given the linear plain complexity bound, combine the two descriptions available from each `xᵢ`
to describe the extracted pair relative to the paired oracle. -/
private theorem theorem2_conditional_pair_descriptions
    (D : Map) (hD : isOptimalConditional D) (A c₀ : ℕ) :
    ∃ c : ℕ, ∀ (x₁ x₂ : BitString) (t M : ℕ)
      (v' z' v'' z'' : BitString),
      t ≤ M →
      natK D (pairCode v' v'') ≤ A * (M + 1) →
      natCondK D v' (pairCode x₁ z') ≤ t + logSlack c₀ M →
      natCondK D v' (pairCode x₂ z') ≤ t + logSlack c₀ M →
      natCondK D v'' (pairCode x₁ z'') ≤ t + logSlack c₀ M →
      natCondK D v'' (pairCode x₂ z'') ≤ t + logSlack c₀ M →
      natCondK D (pairCode v' v'') (pairCode x₁ (pairCode z' z'')) ≤
          2 * t + logSlack c M ∧
        natCondK D (pairCode v' v'') (pairCode x₂ (pairCode z' z'')) ≤
          2 * t + logSlack c M := by
  obtain ⟨cLeft, hLeft⟩ := Kolmogorov.condK_cond_map_le D hD
    (fun p : BitString => pairCode (decodeFirst p) (decodeFirst (decodeSecond p)))
    (by
      have hPair : Computable₂ (fun a b : BitString => pairCode a b) := pairCode_computable
      exact hPair.comp decodeFirst_computable
        (decodeFirst_computable.comp decodeSecond_computable))
  obtain ⟨cRight, hRight⟩ := Kolmogorov.condK_cond_map_le D hD
    (fun p : BitString => pairCode (decodeFirst p) (decodeSecond (decodeSecond p)))
    (by
      have hPair : Computable₂ (fun a b : BitString => pairCode a b) := pairCode_computable
      exact hPair.comp decodeFirst_computable
        (decodeSecond_computable.comp decodeSecond_computable))
  obtain ⟨cPair, hPair⟩ := Kolmogorov.condK_pair_le_add D hD
  let cCtx := max cLeft cRight
  obtain ⟨cFold, hFold⟩ := logSlack_linear_bound cPair (2 + 2 * c₀)
    (2 * c₀ + 2 * cCtx + 1)
  let c := 2 * c₀ + 2 * cCtx + cFold
  refine ⟨c, ?_⟩
  intro x₁ x₂ t M v' z' v'' z'' ht hPairBound hv'₁ hv'₂ hv''₁ hv''₂
  let zPair := pairCode z' z''
  let ctx₁ := pairCode x₁ zPair
  let ctx₂ := pairCode x₂ zPair
  let kv'₁ := natCondK D v' ctx₁
  let kv'₂ := natCondK D v' ctx₂
  let kv''₁ := natCondK D v'' ctx₁
  let kv''₂ := natCondK D v'' ctx₂
  have hRec'₁ : kv'₁ ≤ natCondK D v' (pairCode x₁ z') + cLeft := by
    have h := hLeft v' ctx₁
    have h' : condK D v' ctx₁ ≤ condK D v' (pairCode x₁ z') + (cLeft : ℕ∞) := by
      simpa only [ctx₁, zPair, decodeFirst_pairCode, decodeSecond_pairCode] using h
    rw [condK_le_add_condMutualInfo_value D hD v' ctx₁,
      condK_le_add_condMutualInfo_value D hD v' (pairCode x₁ z')] at h'
    exact_mod_cast h'
  have hRec'₂ : kv'₂ ≤ natCondK D v' (pairCode x₂ z') + cLeft := by
    have h := hLeft v' ctx₂
    have h' : condK D v' ctx₂ ≤ condK D v' (pairCode x₂ z') + (cLeft : ℕ∞) := by
      simpa only [ctx₂, zPair, decodeFirst_pairCode, decodeSecond_pairCode] using h
    rw [condK_le_add_condMutualInfo_value D hD v' ctx₂,
      condK_le_add_condMutualInfo_value D hD v' (pairCode x₂ z')] at h'
    exact_mod_cast h'
  have hRec''₁ : kv''₁ ≤ natCondK D v'' (pairCode x₁ z'') + cRight := by
    have h := hRight v'' ctx₁
    have h' : condK D v'' ctx₁ ≤ condK D v'' (pairCode x₁ z'') + (cRight : ℕ∞) := by
      simpa only [ctx₁, zPair, decodeFirst_pairCode, decodeSecond_pairCode] using h
    rw [condK_le_add_condMutualInfo_value D hD v'' ctx₁,
      condK_le_add_condMutualInfo_value D hD v'' (pairCode x₁ z'')] at h'
    exact_mod_cast h'
  have hRec''₂ : kv''₂ ≤ natCondK D v'' (pairCode x₂ z'') + cRight := by
    have h := hRight v'' ctx₂
    have h' : condK D v'' ctx₂ ≤ condK D v'' (pairCode x₂ z'') + (cRight : ℕ∞) := by
      simpa only [ctx₂, zPair, decodeFirst_pairCode, decodeSecond_pairCode] using h
    rw [condK_le_add_condMutualInfo_value D hD v'' ctx₂,
      condK_le_add_condMutualInfo_value D hD v'' (pairCode x₂ z'')] at h'
    exact_mod_cast h'
  have hcLeft : cLeft ≤ cCtx := le_max_left _ _
  have hcRight : cRight ≤ cCtx := le_max_right _ _
  have hComp'₁ : kv'₁ ≤ t + logSlack c₀ M + cCtx := by omega
  have hComp'₂ : kv'₂ ≤ t + logSlack c₀ M + cCtx := by omega
  have hComp''₁ : kv''₁ ≤ t + logSlack c₀ M + cCtx := by omega
  have hComp''₂ : kv''₂ ≤ t + logSlack c₀ M + cCtx := by omega
  have hVals₁ := condK_le_add_condMutualInfo_value D hD v' ctx₁
  have hVals₂ := condK_le_add_condMutualInfo_value D hD v'' ctx₁
  have hVals₃ := condK_le_add_condMutualInfo_value D hD v' ctx₂
  have hVals₄ := condK_le_add_condMutualInfo_value D hD v'' ctx₂
  have hOut₁ : natCondK D (pairCode v' v'') ctx₁ ≤
      kv'₁ + kv''₁ + logSlack cPair (kv'₁ + kv''₁ + 1) := by
    have h := hPair v' v'' ctx₁ kv'₁ kv''₁ hVals₁ hVals₂
    rw [condK_le_add_condMutualInfo_value D hD (pairCode v' v'') ctx₁] at h
    exact_mod_cast h
  have hOut₂ : natCondK D (pairCode v' v'') ctx₂ ≤
      kv'₂ + kv''₂ + logSlack cPair (kv'₂ + kv''₂ + 1) := by
    have h := hPair v' v'' ctx₂ kv'₂ kv''₂ hVals₃ hVals₄
    rw [condK_le_add_condMutualInfo_value D hD (pairCode v' v'') ctx₂] at h
    exact_mod_cast h
  have hLogLinear : logSlack c₀ M ≤ c₀ * M + c₀ := logSlack_le_self_linear c₀ M
  have hArg₁ : kv'₁ + kv''₁ + 1 ≤ (2 + 2 * c₀) * M + (2 * c₀ + 2 * cCtx + 1) := by
    dsimp [kv'₁, kv''₁]
    nlinarith [hComp'₁, hComp''₁, ht, hLogLinear]
  have hArg₂ : kv'₂ + kv''₂ + 1 ≤ (2 + 2 * c₀) * M + (2 * c₀ + 2 * cCtx + 1) := by
    dsimp [kv'₂, kv''₂]
    nlinarith [hComp'₂, hComp''₂, ht, hLogLinear]
  have hErr₁ : logSlack cPair (kv'₁ + kv''₁ + 1) ≤ logSlack cFold M := by
    exact logSlack_le_of_linear_bound hFold hArg₁
  have hErr₂ : logSlack cPair (kv'₂ + kv''₂ + 1) ≤ logSlack cFold M := by
    exact logSlack_le_of_linear_bound hFold hArg₂
  have hSlack : 2 * logSlack c₀ M + 2 * cCtx + logSlack cFold M ≤ logSlack c M := by
    have hCtxSlack : 2 * cCtx ≤ logSlack (2 * cCtx) M := by
      unfold logSlack
      omega
    have hEq₀ : 2 * logSlack c₀ M = logSlack (2 * c₀) M := by
      unfold logSlack
      ring
    have hEq : logSlack (2 * c₀) M + logSlack (2 * cCtx) M +
        logSlack cFold M = logSlack c M := by
      rw [← logSlack_add_constants, ← logSlack_add_constants]
    calc
      2 * logSlack c₀ M + 2 * cCtx + logSlack cFold M
          ≤ logSlack (2 * c₀) M + logSlack (2 * cCtx) M + logSlack cFold M := by omega
      _ = logSlack c M := hEq
  constructor
  · calc
      natCondK D (pairCode v' v'') ctx₁ ≤
          kv'₁ + kv''₁ + logSlack cPair (kv'₁ + kv''₁ + 1) := hOut₁
      _ ≤ 2 * t + 2 * logSlack c₀ M + 2 * cCtx + logSlack cFold M := by
        have := hErr₁
        omega
      _ ≤ 2 * t + logSlack c M := by
        have := Nat.add_le_add_left hSlack (2 * t)
        omega
  · calc
      natCondK D (pairCode v' v'') ctx₂ ≤
          kv'₂ + kv''₂ + logSlack cPair (kv'₂ + kv''₂ + 1) := hOut₂
      _ ≤ 2 * t + 2 * logSlack c₀ M + 2 * cCtx + logSlack cFold M := by
        have := hErr₂
        omega
      _ ≤ 2 * t + logSlack c M := by
        have := Nat.add_le_add_left hSlack (2 * t)
        omega

/-- Chain rules applied to the regrouped pair convert the far-pair condition into a lower bound
on conditional information, with chain-rule errors absorbed at scale `M`.
the chain rules applied to the regrouped pair convert the far-pair condition into the lower bound
on conditional information, with all chain-rule errors absorbed at scale `M`. -/
private theorem theorem2_information_lower_bound
    (D : Map) (hD : isOptimalConditional D) (c₀ A : ℕ) :
    ∃ c : ℕ, ∀ (x₁ x₂ z : BitString) (q δ M β : ℕ)
      (a b v' z' v'' z'' : BitString),
      M = natK D (pairCode (pairCode x₁ x₂) z) →
      natK D z + logSlack c₀ M + (δ + 1) / 2 ≤ β →
      a = pairCode v' z' → b = pairCode v'' z'' →
      natK D (pairCode v' v'') ≤ A * (M + 1) →
      natK D z' ≤ natK D z + logSlack c₀ M →
      natK D z'' ≤ natK D z + logSlack c₀ M →
      natK D z + q ≤ natK D a + logSlack c₀ M →
      β ≤ natCondK D b a →
      q + (δ + 1) / 2 ≤
        natCondK D (pairCode v' v'') (pairCode z' z'') + logSlack c M := by
  obtain ⟨cChain, hChain⟩ :=
    theorem2_regrouped_chain_rule
      D hD
  obtain ⟨B, hBounds⟩ :=
    theorem2_linear_regrouped_complexities
      D hD c₀ A
  obtain ⟨cFold, hFold⟩ := logSlack_linear_bound cChain B (B + 1)
  let C := 2 * c₀ + 3 * cFold + cChain
  refine ⟨C, ?_⟩
  intro x₁ x₂ z q δ M β a b v' z' v'' z'' hM hBeta ha hb hPair hz' hz'' hKlower hfar
  let L := logSlack c₀ M
  let d := (δ + 1) / 2
  have hChain' := hChain v' z' v'' z''
  have hChain'' :
      natK D a + natCondK D b a ≤
        natK D z' + natK D z'' + natCondK D (pairCode v' v'') (pairCode z' z'') +
          logSlack cChain (natK D (pairCode (pairCode v' z') (pairCode v'' z'')) + 1) +
          logSlack cChain (natK D (pairCode (pairCode z' z'') (pairCode v' v'')) + 1) +
          logSlack cChain (natK D (pairCode z' z'') + 1) + cChain := by
    simpa [ha, hb] using hChain'
  obtain ⟨habLinear, hZULinear, hZLinear⟩ :=
    hBounds x₁ x₂ z M v' z' v'' z'' hM hPair hz' hz''
  have hFoldArg : B * (M + 1) + 1 = B * M + (B + 1) := by
    rw [Nat.mul_add]
    simp
    omega
  have hErrAb :
      logSlack cChain (natK D (pairCode (pairCode v' z') (pairCode v'' z'')) + 1) ≤
        logSlack cFold M := by
    calc
      logSlack cChain (natK D (pairCode (pairCode v' z') (pairCode v'' z'')) + 1)
          ≤ logSlack cChain (B * (M + 1) + 1) :=
            logSlack_mono_right cChain (by omega)
      _ = logSlack cChain (B * M + (B + 1)) := by rw [hFoldArg]
      _ ≤ logSlack cFold M := hFold M
  have hErrZU :
      logSlack cChain (natK D (pairCode (pairCode z' z'') (pairCode v' v'')) + 1) ≤
        logSlack cFold M := by
    calc
      logSlack cChain (natK D (pairCode (pairCode z' z'') (pairCode v' v'')) + 1)
          ≤ logSlack cChain (B * (M + 1) + 1) :=
            logSlack_mono_right cChain (by omega)
      _ = logSlack cChain (B * M + (B + 1)) := by rw [hFoldArg]
      _ ≤ logSlack cFold M := hFold M
  have hErrZ :
      logSlack cChain (natK D (pairCode z' z'') + 1) ≤ logSlack cFold M := by
    calc
      logSlack cChain (natK D (pairCode z' z'') + 1)
          ≤ logSlack cChain (B * (M + 1) + 1) :=
            logSlack_mono_right cChain (by omega)
      _ = logSlack cChain (B * M + (B + 1)) := by rw [hFoldArg]
      _ ≤ logSlack cFold M := hFold M
  have hLogEq :
      logSlack c₀ M + logSlack c₀ M + logSlack cFold M +
          logSlack cFold M + logSlack cFold M = logSlack (2 * c₀ + 3 * cFold) M := by
    unfold logSlack
    ring
  have hAbsorb :
      2 * L + logSlack cFold M + logSlack cFold M + logSlack cFold M + cChain ≤
        logSlack C M := by
    calc
      2 * L + logSlack cFold M + logSlack cFold M + logSlack cFold M + cChain
          = logSlack (2 * c₀ + 3 * cFold) M + cChain := by
              dsimp [L, logSlack]
              ring
      _ ≤ logSlack C M := by
        exact logSlack_add_nat_le (2 * c₀ + 3 * cFold) cChain M
  have hBase : 2 * natK D z + q + d ≤
      natK D a + natCondK D b a := by
    dsimp [L, d]
    omega
  have hRaw : q + d ≤
      natCondK D (pairCode v' v'') (pairCode z' z'') + 2 * L +
        logSlack cChain (natK D (pairCode (pairCode v' z') (pairCode v'' z'')) + 1) +
        logSlack cChain (natK D (pairCode (pairCode z' z'') (pairCode v' v'')) + 1) +
        logSlack cChain (natK D (pairCode z' z'') + 1) + cChain := by
    dsimp [L, d] at hBase hBeta hKlower hfar
    omega
  have hRaw' : q + d ≤
      natCondK D (pairCode v' v'') (pairCode z' z'') +
        2 * L + 3 * logSlack cFold M + cChain := by
    dsimp [d]
    omega
  have hFinal : q + d ≤
      natCondK D (pairCode v' v'') (pairCode z' z'') + logSlack C M := by
    omega
  simpa [C, d] using hFinal

/-- Estimate the information and conditional description costs of the pair of strings before
padding.
information and conditional description costs of the pair of strings before padding. -/
private theorem theorem2_pair_bounds
    (D : Map) (hD : isOptimalConditional D) (c₀ : ℕ) :
    ∃ A c : ℕ, ∀ (x₁ x₂ z : BitString) (q t δ M β : ℕ)
      (a b v' z' v'' z'' : BitString),
      M = natK D (pairCode (pairCode x₁ x₂) z) →
      t ≤ M →
      8 * (t + logSlack 1 M) ≤ δ →
      2 * (natK D z + logSlack c₀ M) + δ ≤ 2 * β →
      a = pairCode v' z' → b = pairCode v'' z'' →
      q ≤ natCondK D v' z' + logSlack c₀ M →
      q ≤ natCondK D v'' z'' + logSlack c₀ M →
      natCondK D v' (pairCode x₁ z') ≤ t + logSlack c₀ M →
      natCondK D v' (pairCode x₂ z') ≤ t + logSlack c₀ M →
      natCondK D v'' (pairCode x₁ z'') ≤ t + logSlack c₀ M →
      natCondK D v'' (pairCode x₂ z'') ≤ t + logSlack c₀ M →
      natK D z' ≤ natK D z + logSlack c₀ M →
      natK D z'' ≤ natK D z + logSlack c₀ M →
      natK D z + q ≤ natK D a + logSlack c₀ M →
      β ≤ natCondK D b a →
      q + (δ + 1) / 2 ≤
          natCondK D (pairCode v' v'') (pairCode z' z'') + logSlack c M ∧
        natK D (pairCode v' v'') ≤ A * (M + 1) ∧
        natCondK D (pairCode v' v'') (pairCode x₁ (pairCode z' z'')) ≤
          2 * t + logSlack c M ∧
        natCondK D (pairCode v' v'') (pairCode x₂ (pairCode z' z'')) ≤
          2 * t + logSlack c M := by
  obtain ⟨A, hA⟩ :=
    theorem2_linear_pair_complexity
      D hD c₀
  obtain ⟨cUpper, hUpper⟩ :=
    theorem2_conditional_pair_descriptions
      D hD A c₀
  obtain ⟨cLower, hLower⟩ :=
    theorem2_information_lower_bound
      D hD c₀ A
  let c := cUpper + cLower
  refine ⟨A, c, ?_⟩
  intro x₁ x₂ z q t δ M β a b v' z' v'' z'' hM ht hδ hβ ha hb hq₁ hq₂
    hv₁₁ hv₁₂ hv₂₁ hv₂₂ hz₁ hz₂ haKlower hfar
  have hPair := hA x₁ x₂ z t M v' z' v'' z'' hM ht hv₁₁ hv₂₁ hz₁ hz₂
  have hCond := hUpper x₁ x₂ t M v' z' v'' z'' ht hPair hv₁₁ hv₁₂ hv₂₁ hv₂₂
  have hBetaGain : natK D z + logSlack c₀ M + (δ + 1) / 2 ≤ β := by omega
  have hInfo := hLower x₁ x₂ z q δ M β a b v' z' v'' z'' hM hBetaGain ha hb
    hPair hz₁ hz₂ haKlower hfar
  have hLogUpper : logSlack cUpper M ≤ logSlack c M := by
    dsimp [c]
    exact logSlack_mono_left (Nat.le_add_right cUpper cLower) M
  have hLogLower : logSlack cLower M ≤ logSlack c M := by
    dsimp [c]
    exact logSlack_mono_left (Nat.le_add_left cLower cUpper) M
  refine ⟨?_, hPair, ?_, ?_⟩
  · exact hInfo.trans (Nat.add_le_add_left hLogLower _)
  · exact hCond.1.trans (Nat.add_le_add_left hLogUpper _)
  · exact hCond.2.trans (Nat.add_le_add_left hLogUpper _)

/-- The plain complexity of a coded pair is bounded linearly by the first component and the
literal length of the second component. -/
private theorem theorem2_pad_pair_aux_pair_upper
    (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ (w s : BitString),
      natK D (pairCode w s) ≤ 3 * natK D w + s.length + c := by
  obtain ⟨cPair, hPair⟩ := plainK_pair_le_add_two_log D hD
  obtain ⟨cLen, hLen⟩ := plainK_le_length D hD
  have hPlainFinite (x : BitString) : plainK D x ≠ ⊤ := by
    exact Kolmogorov.ne_top_of_le_natCast_add (hLen x)
  have hPlainValue (x : BitString) : plainK D x = (natK D x : ℕ∞) := by
    change plainK D x = ((plainK D x).toNat : ℕ∞)
    exact (ENat.natCast_toNat (hPlainFinite x)).symm
  refine ⟨cPair + cLen, fun w s => ?_⟩
  have hPairCast :
      (natK D (pairCode w s) : ℕ∞) ≤
        (natK D w : ℕ∞) + (natK D s : ℕ∞) +
          ((2 * Nat.log 2 (natK D w) + cPair : ℕ) : ℕ∞) := by
    simpa [Kolmogorov.cPair, Kolmogorov.cVal, hPlainValue] using hPair w s
  have hPairNat : natK D (pairCode w s) ≤
      natK D w + natK D s + (2 * Nat.log 2 (natK D w) + cPair) := by
    exact_mod_cast hPairCast
  have hLenCast : (natK D s : ℕ∞) ≤ (s.length + cLen : ℕ∞) := by
    have h := hLen s
    rw [hPlainValue s] at h
    simpa [programLength] using h
  have hLenNat : natK D s ≤ s.length + cLen := by
    exact_mod_cast hLenCast
  have hLog : Nat.log 2 (natK D w) ≤ natK D w := Nat.log_le_self 2 _
  nlinarith [hPairNat, hLog, hLenNat]

/-- Choose one logarithmic padding budget that absorbs both the original slack and the chain-rule
error at the complexity of the padded pair. -/
private theorem theorem2_pad_pair_aux_absorb_log_overhead
    (a c m : ℕ) :
    ∃ p : ℕ, ∀ N : ℕ,
      logSlack a N +
        logSlack c (m * (N + 1) + logSlack p N + 1) ≤ logSlack p N := by
  let T := a + c + m + 4
  let p := 2 ^ (4 * T)
  refine ⟨p, fun N => ?_⟩
  let A := m + p + 1
  let X := m * (N + 1) + logSlack p N + 1
  have hT : 4 ≤ T := by dsimp [T]; omega
  have hTpow : T < 2 ^ T := Nat.lt_pow_self (by decide : 1 < 2)
  have hpowT : 2 ^ T ≤ p := by
    dsimp [p]
    exact Nat.pow_le_pow_right (by omega : 0 < 2) (by dsimp [T]; omega)
  have hMpow : m + 1 ≤ 2 ^ T := by
    have hm : m + 1 ≤ T := by dsimp [T]; omega
    exact hm.trans hTpow.le
  have hMA : m + 1 ≤ p := hMpow.trans hpowT
  have hAexp : A < 2 ^ (4 * T + 2) := by
    calc
      A ≤ 2 * p := by dsimp [A]; omega
      _ = 2 ^ (4 * T + 1) := by
        dsimp [p]
        rw [Nat.pow_succ]
        ring
      _ < 2 ^ (4 * T + 2) := by
        calc
          2 ^ (4 * T + 1) < 2 ^ (4 * T + 1) * 2 := by
            nlinarith [Nat.two_pow_pos (4 * T + 1)]
          _ = 2 ^ (4 * T + 2) := by rw [Nat.pow_succ]; ring
  have hlogA : Nat.log 2 A ≤ 4 * T + 1 := by
    have h := Nat.log_lt_of_lt_pow' (by omega : 4 * T + 2 ≠ 0) hAexp
    omega
  have hpEq : p = (2 ^ T) ^ 4 := by
    dsimp [p]
    rw [show 4 * T = T * 4 by omega, Nat.pow_mul]
  have hpLarge : T ^ 4 ≤ p := by
    rw [hpEq]
    exact Nat.pow_le_pow_left hTpow.le 4
  have hT2 : 16 ≤ T ^ 2 := by nlinarith [hT]
  have hT4 : 4 * T ^ 2 + 6 * T ≤ T ^ 4 := by
    have hm := Nat.mul_le_mul_right (T ^ 2) hT2
    nlinarith [hm, hT2, hT]
  have hconst : a + c + c * (Nat.log 2 A + 3) ≤ p := by
    have ha : a ≤ T := by dsimp [T]; omega
    have hc : c ≤ T := by dsimp [T]; omega
    have hmul : c * (Nat.log 2 A + 3) ≤ T * (4 * T + 4) :=
      Nat.mul_le_mul hc (by omega)
    nlinarith [ha, hc, hmul, hT4, hpLarge]
  have hNlt : N < 2 ^ (Nat.bits N).length := by
    simpa [Nat.size_eq_bits_len] using Nat.lt_size_self N
  have hNplus : N + 1 ≤ 2 ^ (Nat.bits N).length := by omega
  have hAlength : A < 2 ^ (Nat.log 2 A + 1) :=
    Nat.lt_pow_succ_log_self (by decide : 1 < 2) A
  have hXbound : X ≤ A * (N + 1) := by
    have hSlack := logSlack_le_self_linear p N
    dsimp [X, A]
    nlinarith [hSlack]
  have hProduct :
      A * (N + 1) ≤ 2 ^ (Nat.log 2 A + 1) * 2 ^ (Nat.bits N).length :=
    Nat.mul_le_mul hAlength.le hNplus
  have hXlt : X < 2 ^ ((Nat.bits N).length + Nat.log 2 A + 2) := by
    calc
      X ≤ A * (N + 1) := hXbound
      _ ≤ 2 ^ (Nat.log 2 A + 1) * 2 ^ (Nat.bits N).length := hProduct
      _ = 2 ^ (Nat.log 2 A + 1 + (Nat.bits N).length) := by rw [← Nat.pow_add]
      _ ≤ 2 ^ ((Nat.bits N).length + Nat.log 2 A + 1) := by
        apply Nat.pow_le_pow_right (by omega : 0 < 2)
        omega
      _ < 2 ^ ((Nat.bits N).length + Nat.log 2 A + 2) := by
        calc
          2 ^ ((Nat.bits N).length + Nat.log 2 A + 1) <
              2 ^ ((Nat.bits N).length + Nat.log 2 A + 1) * 2 := by
            nlinarith [Nat.two_pow_pos ((Nat.bits N).length + Nat.log 2 A + 1)]
          _ = 2 ^ ((Nat.bits N).length + Nat.log 2 A + 2) := by
            rw [Nat.pow_succ]
            congr 1
  have hBitsX :
      (Nat.bits X).length ≤ (Nat.bits N).length + Nat.log 2 A + 2 := by
    have hsize := Nat.size_le.mpr hXlt
    simpa [Nat.size_eq_bits_len] using hsize
  have hSlackTotal :
      logSlack a N + logSlack c X ≤
        logSlack (a + c) N + c * (Nat.log 2 A + 2) := by
    unfold logSlack
    nlinarith [hBitsX]
  have hFinal : logSlack a N + logSlack c X ≤ logSlack p N := by
    calc
      logSlack a N + logSlack c X ≤
          logSlack (a + c) N + c * (Nat.log 2 A + 2) := hSlackTotal
      _ ≤ logSlack p N := by
        have hCoeff : a + c ≤ p := by omega
        have hConst' : a + c + c * (Nat.log 2 A + 2) ≤ p := by
          nlinarith [hconst]
        have hCoeffMul := Nat.mul_le_mul_right (Nat.bits N).length hCoeff
        unfold logSlack
        omega
  simpa [X] using hFinal

/-- Pad a string
whose conditional complexity is short by logarithmic slack, using an incompressible suffix; the
linear plain-complexity budget keeps the chain-rule error logarithmic in `M`. -/
private theorem theorem2_pad_pair
    (D : Map) (hD : isOptimalConditional D) (A c₀ : ℕ) :
    ∃ c : ℕ, c₀ ≤ c ∧ ∀ (x₁ x₂ z u : BitString) (q t δ M : ℕ),
      t ≤ M →
      8 * (t + logSlack 1 M) ≤ δ →
      q + (δ + 1) / 2 ≤ natCondK D u z + logSlack c₀ M →
      natK D u ≤ A * (M + 1) →
      natCondK D u (pairCode x₁ z) ≤ 2 * t + logSlack c₀ M →
      natCondK D u (pairCode x₂ z) ≤ 2 * t + logSlack c₀ M →
      ∃ q' : ℕ, 2 * q + δ ≤ 2 * q' ∧
        CommonInfoExtractableRel D x₁ x₂ z q' (3 * t + logSlack c M) := by
  obtain ⟨cPairPlain, hPairPlain⟩ :=
    theorem2_pad_pair_aux_pair_upper
      D hD
  obtain ⟨cPair, hPair⟩ := Kolmogorov.condK_pair_le_add D hD
  obtain ⟨cLower, hLower⟩ := condK_pairCode_chain_lower_values D hD
  obtain ⟨cCond, hCond⟩ := condK_le_plainK D hD
  obtain ⟨cLen, hLen⟩ := plainK_le_length D hD
  let m := 3 * A + cPairPlain + cCond
  obtain ⟨cPad, hPad⟩ :=
    theorem2_pad_pair_aux_absorb_log_overhead
      c₀ cLower m
  let B := 2 + c₀ + cPad + cLen + cCond + 1
  obtain ⟨cPairFold, hPairFold⟩ := logSlack_linear_bound cPair B B
  let cUpper := c₀ + cPad + cLen + cCond + cPairFold
  let c := max c₀ cUpper
  have hc₀ : c₀ ≤ c := le_max_left _ _
  have hcUpper : cUpper ≤ c := le_max_right _ _
  refine ⟨c, hc₀, ?_⟩
  intro x₁ x₂ z u q t δ M ht hδ hq hK hu₁ hu₂
  let r := logSlack cPad M
  let q' := q + (δ + 1) / 2
  have hq' : q' ≤ natCondK D u z + logSlack c₀ M := by
    simpa [q'] using hq
  have htwoq : 2 * q + δ ≤ 2 * q' := by
    dsimp [q']
    omega
  obtain ⟨s, hsLen, hsIncomp⟩ := exists_incompressible_string D (pairCode u z) r
  have hsIncompNat : r ≤ natCondK D s (pairCode u z) := by
    rw [← ENat.natCast_toNat (condK_ne_top_of_optimal D hD s (pairCode u z))] at hsIncomp
    exact_mod_cast hsIncomp
  have hPlainFinite (y : BitString) : plainK D y ≠ ⊤ := by
    exact Kolmogorov.ne_top_of_le_natCast_add (hLen y)
  have hPlainValue (y : BitString) : plainK D y = (natK D y : ℕ∞) := by
    change plainK D y = ((plainK D y).toNat : ℕ∞)
    exact (ENat.natCast_toNat (hPlainFinite y)).symm
  have hLiteral : natK D s ≤ r + cLen := by
    have h := hLen s
    rw [hPlainValue s] at h
    have h' : (natK D s : ℕ∞) ≤ (s.length + cLen : ℕ∞) := by
      simpa [programLength] using h
    rw [hsLen] at h'
    exact_mod_cast h'
  have hCondPlain (y w : BitString) : natCondK D y w ≤ natK D y + cCond := by
    have h := hCond y w
    rw [condK_le_add_condMutualInfo_value D hD y w, hPlainValue y] at h
    exact_mod_cast h
  have hSuffixCost (w : BitString) :
      natCondK D s w ≤ r + cLen + cCond := by
    calc
      natCondK D s w ≤ natK D s + cCond := hCondPlain s w
      _ ≤ r + cLen + cCond := Nat.add_le_add_right hLiteral cCond
  have hPairComplexityBound :
      natCondK D (pairCode u s) z + 1 ≤ m * (M + 1) + r + 1 := by
    have hPairK := hPairPlain u s
    rw [hsLen] at hPairK
    have hK3 := Nat.mul_le_mul_left 3 hK
    have hConst : cPairPlain + cCond ≤ (cPairPlain + cCond) * (M + 1) := by
      simpa using Nat.mul_le_mul_left (cPairPlain + cCond)
        (by omega : 1 ≤ M + 1)
    have hPairCond := hCondPlain (pairCode u s) z
    dsimp [m]
    nlinarith [hPairK, hK3, hConst, hPairCond]
  have hAbsorb := hPad M
  have hChainError :
      logSlack cLower (natCondK D (pairCode u s) z + 1) ≤
        logSlack cLower (m * (M + 1) + r + 1) :=
    logSlack_mono_right cLower hPairComplexityBound
  have hGap :
      logSlack c₀ M + logSlack cLower (natCondK D (pairCode u s) z + 1) ≤ r := by
    dsimp [r] at hAbsorb ⊢
    exact le_trans (Nat.add_le_add_left hChainError (logSlack c₀ M)) hAbsorb
  have hLowerInst := hLower u s z (natCondK D u z)
    (natCondK D s (pairCode u z)) (natCondK D (pairCode u s) z)
    (condK_le_add_condMutualInfo_value D hD u z)
    (condK_le_add_condMutualInfo_value D hD s (pairCode u z))
    (condK_le_add_condMutualInfo_value D hD (pairCode u s) z)
  have hLowerPad :
      natCondK D u z + r ≤ natCondK D (pairCode u s) z +
        logSlack cLower (natCondK D (pairCode u s) z + 1) := by
    calc
      natCondK D u z + r ≤
          natCondK D u z + natCondK D s (pairCode u z) :=
        Nat.add_le_add_left hsIncompNat _
      _ ≤ natCondK D (pairCode u s) z +
            logSlack cLower (natCondK D (pairCode u s) z + 1) := hLowerInst
  have hqPad : q' ≤ natCondK D (pairCode u s) z := by
    let e := logSlack cLower (natCondK D (pairCode u s) z + 1)
    have hmid : natCondK D u z + logSlack c₀ M + e ≤ natCondK D u z + r := by
      dsimp [e]
      have := Nat.add_le_add_left hGap (natCondK D u z)
      omega
    have hqErr : q' + e ≤ natCondK D (pairCode u s) z + e := by
      calc
        q' + e ≤ natCondK D u z + logSlack c₀ M + e :=
          Nat.add_le_add_right hq' e
        _ ≤ natCondK D u z + r := hmid
        _ ≤ natCondK D (pairCode u s) z + e := by
          simpa [e] using hLowerPad
    omega
  have hSuffixLinear : r ≤ cPad * (M + 1) := by
    have h := logSlack_le_self_linear cPad M
    dsimp [r]
    nlinarith
  have hArg₁ :
      natCondK D u (pairCode x₁ z) + natCondK D s (pairCode x₁ z) + 1 ≤ B * (M + 1) := by
    have hU : natCondK D u (pairCode x₁ z) ≤ 2 * M + c₀ * (M + 1) := by
      calc
        _ ≤ 2 * t + logSlack c₀ M := hu₁
        _ ≤ 2 * M + c₀ * (M + 1) := by
          exact Nat.add_le_add (by omega) (logSlack_le_self_linear c₀ M)
    have hS : natCondK D s (pairCode x₁ z) ≤
        cPad * (M + 1) + cLen + cCond := by
      calc
        _ ≤ r + cLen + cCond := hSuffixCost _
        _ ≤ cPad * (M + 1) + cLen + cCond := by
          simpa [Nat.add_assoc] using
            Nat.add_le_add_right hSuffixLinear (cLen + cCond)
    have hU' : natCondK D u (pairCode x₁ z) ≤ (2 + c₀) * (M + 1) := by
      calc
        _ ≤ 2 * (M + 1) + c₀ * (M + 1) := by
          exact Nat.le_trans hU (Nat.add_le_add_right
            (Nat.mul_le_mul_left 2 (by omega : M ≤ M + 1)) _)
        _ = (2 + c₀) * (M + 1) := by rw [Nat.add_mul]
    have hS' : natCondK D s (pairCode x₁ z) ≤
        (cPad + cLen + cCond) * (M + 1) := by
      have hConst : cLen + cCond ≤ (cLen + cCond) * (M + 1) := by
        simpa using Nat.mul_le_mul_left (cLen + cCond) (by omega : 1 ≤ M + 1)
      calc
        _ ≤ cPad * (M + 1) + (cLen + cCond) := by
          simpa [Nat.add_assoc] using hS
        _ ≤ cPad * (M + 1) + (cLen + cCond) * (M + 1) :=
          Nat.add_le_add_left hConst _
        _ = (cPad + cLen + cCond) * (M + 1) := by
          simp [Nat.add_mul, Nat.add_assoc]
    have hCoeff : (2 + c₀) + (cPad + cLen + cCond) + 1 ≤ B := by
      dsimp [B]
      omega
    calc
      _ ≤ (2 + c₀) * (M + 1) + (cPad + cLen + cCond) * (M + 1) + 1 :=
        Nat.add_le_add_right (Nat.add_le_add hU' hS') 1
      _ ≤ (2 + c₀) * (M + 1) + (cPad + cLen + cCond) * (M + 1) + (M + 1) :=
        Nat.add_le_add_left (by omega : 1 ≤ M + 1) _
      _ = ((2 + c₀) + (cPad + cLen + cCond) + 1) * (M + 1) := by
        ring
      _ ≤ B * (M + 1) := Nat.mul_le_mul_right _ hCoeff
  have hArg₂ :
      natCondK D u (pairCode x₂ z) + natCondK D s (pairCode x₂ z) + 1 ≤ B * (M + 1) := by
    have hU : natCondK D u (pairCode x₂ z) ≤ 2 * M + c₀ * (M + 1) := by
      calc
        _ ≤ 2 * t + logSlack c₀ M := hu₂
        _ ≤ 2 * M + c₀ * (M + 1) := by
          exact Nat.add_le_add (by omega) (logSlack_le_self_linear c₀ M)
    have hS : natCondK D s (pairCode x₂ z) ≤
        cPad * (M + 1) + cLen + cCond := by
      calc
        _ ≤ r + cLen + cCond := hSuffixCost _
        _ ≤ cPad * (M + 1) + cLen + cCond := by
          simpa [Nat.add_assoc] using
            Nat.add_le_add_right hSuffixLinear (cLen + cCond)
    have hU' : natCondK D u (pairCode x₂ z) ≤ (2 + c₀) * (M + 1) := by
      calc
        _ ≤ 2 * (M + 1) + c₀ * (M + 1) := by
          exact Nat.le_trans hU (Nat.add_le_add_right
            (Nat.mul_le_mul_left 2 (by omega : M ≤ M + 1)) _)
        _ = (2 + c₀) * (M + 1) := by rw [Nat.add_mul]
    have hS' : natCondK D s (pairCode x₂ z) ≤
        (cPad + cLen + cCond) * (M + 1) := by
      have hConst : cLen + cCond ≤ (cLen + cCond) * (M + 1) := by
        simpa using Nat.mul_le_mul_left (cLen + cCond) (by omega : 1 ≤ M + 1)
      calc
        _ ≤ cPad * (M + 1) + (cLen + cCond) := by
          simpa [Nat.add_assoc] using hS
        _ ≤ cPad * (M + 1) + (cLen + cCond) * (M + 1) :=
          Nat.add_le_add_left hConst _
        _ = (cPad + cLen + cCond) * (M + 1) := by
          simp [Nat.add_mul, Nat.add_assoc]
    have hCoeff : (2 + c₀) + (cPad + cLen + cCond) + 1 ≤ B := by
      dsimp [B]
      omega
    calc
      _ ≤ (2 + c₀) * (M + 1) + (cPad + cLen + cCond) * (M + 1) + 1 :=
        Nat.add_le_add_right (Nat.add_le_add hU' hS') 1
      _ ≤ (2 + c₀) * (M + 1) + (cPad + cLen + cCond) * (M + 1) + (M + 1) :=
        Nat.add_le_add_left (by omega : 1 ≤ M + 1) _
      _ = ((2 + c₀) + (cPad + cLen + cCond) + 1) * (M + 1) := by
        ring
      _ ≤ B * (M + 1) := Nat.mul_le_mul_right _ hCoeff
  have hPairError₁ :
      logSlack cPair (natCondK D u (pairCode x₁ z) +
        natCondK D s (pairCode x₁ z) + 1) ≤ logSlack cPairFold M := by
    apply logSlack_le_of_linear_bound hPairFold
    simpa [Nat.mul_add, Nat.add_mul, Nat.add_assoc] using hArg₁
  have hPairError₂ :
      logSlack cPair (natCondK D u (pairCode x₂ z) +
        natCondK D s (pairCode x₂ z) + 1) ≤ logSlack cPairFold M := by
    apply logSlack_le_of_linear_bound hPairFold
    simpa [Nat.mul_add, Nat.add_mul, Nat.add_assoc] using hArg₂
  have hPairOut₁ : natCondK D (pairCode u s) (pairCode x₁ z) ≤
      natCondK D u (pairCode x₁ z) + natCondK D s (pairCode x₁ z) +
        logSlack cPair (natCondK D u (pairCode x₁ z) +
          natCondK D s (pairCode x₁ z) + 1) := by
    have h := hPair u s (pairCode x₁ z)
      (natCondK D u (pairCode x₁ z)) (natCondK D s (pairCode x₁ z))
      (condK_le_add_condMutualInfo_value D hD u (pairCode x₁ z))
      (condK_le_add_condMutualInfo_value D hD s (pairCode x₁ z))
    rw [← ENat.natCast_toNat
      (condK_ne_top_of_optimal D hD (pairCode u s) (pairCode x₁ z))] at h
    exact_mod_cast h
  have hPairOut₂ : natCondK D (pairCode u s) (pairCode x₂ z) ≤
      natCondK D u (pairCode x₂ z) + natCondK D s (pairCode x₂ z) +
        logSlack cPair (natCondK D u (pairCode x₂ z) +
          natCondK D s (pairCode x₂ z) + 1) := by
    have h := hPair u s (pairCode x₂ z)
      (natCondK D u (pairCode x₂ z)) (natCondK D s (pairCode x₂ z))
      (condK_le_add_condMutualInfo_value D hD u (pairCode x₂ z))
      (condK_le_add_condMutualInfo_value D hD s (pairCode x₂ z))
    rw [← ENat.natCast_toNat
      (condK_ne_top_of_optimal D hD (pairCode u s) (pairCode x₂ z))] at h
    exact_mod_cast h
  have hSlackUpper :
      logSlack c₀ M + logSlack cPad M + cLen + cCond + logSlack cPairFold M ≤
        logSlack cUpper M := by
    calc
      logSlack c₀ M + logSlack cPad M + cLen + cCond + logSlack cPairFold M
          = logSlack (c₀ + cPad) M + logSlack cPairFold M + (cLen + cCond) := by
              rw [logSlack_add_const]
              omega
      _ = logSlack (c₀ + cPad + cPairFold) M + (cLen + cCond) := by
        rw [logSlack_add_const]
      _ ≤ logSlack (c₀ + cPad + cPairFold + (cLen + cCond)) M :=
        logSlack_add_nat_le (c₀ + cPad + cPairFold) (cLen + cCond) M
      _ = logSlack cUpper M := by
        congr 1
        dsimp [cUpper]
        omega
  have hFinal₁ :
      natCondK D (pairCode u s) (pairCode x₁ z) ≤ 3 * t + logSlack c M := by
    have h1 := hPairOut₁
    have h2 := hPairError₁
    have h3 := hSuffixCost (pairCode x₁ z)
    have h4 := hu₁
    have hc : cUpper ≤ c := hcUpper
    have hSlackMono := logSlack_mono_left hc M
    calc
      natCondK D (pairCode u s) (pairCode x₁ z)
          ≤ 2 * t + logSlack c₀ M + r + cLen + cCond +
              logSlack cPairFold M := by
                dsimp [r]
                omega
      _ ≤ 3 * t + logSlack c M := by
        have hsl := hSlackUpper.trans (logSlack_mono_left hcUpper M)
        omega
  have hFinal₂ :
      natCondK D (pairCode u s) (pairCode x₂ z) ≤ 3 * t + logSlack c M := by
    have h1 := hPairOut₂
    have h2 := hPairError₂
    have h3 := hSuffixCost (pairCode x₂ z)
    have h4 := hu₂
    have hc : cUpper ≤ c := hcUpper
    have hSlackMono := logSlack_mono_left hc M
    calc
      natCondK D (pairCode u s) (pairCode x₂ z)
          ≤ 2 * t + logSlack c₀ M + r + cLen + cCond +
              logSlack cPairFold M := by
                dsimp [r]
                omega
      _ ≤ 3 * t + logSlack c M := by
        have hsl := hSlackUpper.trans (logSlack_mono_left hcUpper M)
        omega
  refine ⟨q', htwoq, ?_⟩
  change ∃ v : BitString, q' ≤ natCondK D v z ∧
    natCondK D v (pairCode x₁ z) ≤ 3 * t + logSlack c M ∧
    natCondK D v (pairCode x₂ z) ≤ 3 * t + logSlack c M
  exact ⟨pairCode u s, hqPad, hFinal₁, hFinal₂⟩

/-- The far pair gives a longer extractable string relative to the paired oracle; pad its missing
logarithmic complexity with an incompressible suffix to reach the stated gain. -/
private theorem theorem2_pair_extractable
    (D : Map) (hD : isOptimalConditional D) (c₀ : ℕ) :
    ∃ c : ℕ, ∀ (x₁ x₂ z : BitString) (q t δ M β : ℕ)
      (a b v' z' v'' z'' : BitString),
      M = natK D (pairCode (pairCode x₁ x₂) z) →
      t ≤ M →
      8 * (t + logSlack 1 M) ≤ δ →
      2 * (natK D z + logSlack c₀ M) + δ ≤ 2 * β →
      a = pairCode v' z' → b = pairCode v'' z'' →
      q ≤ natCondK D v' z' + logSlack c₀ M →
      q ≤ natCondK D v'' z'' + logSlack c₀ M →
      natCondK D v' (pairCode x₁ z') ≤ t + logSlack c₀ M →
      natCondK D v' (pairCode x₂ z') ≤ t + logSlack c₀ M →
      natCondK D v'' (pairCode x₁ z'') ≤ t + logSlack c₀ M →
      natCondK D v'' (pairCode x₂ z'') ≤ t + logSlack c₀ M →
      natK D z' ≤ natK D z + logSlack c₀ M →
      natK D z'' ≤ natK D z + logSlack c₀ M →
      natK D z + q ≤ natK D a + logSlack c₀ M →
      β ≤ natCondK D b a →
      ∃ q' : ℕ, 2 * q + δ ≤ 2 * q' ∧
        CommonInfoExtractableRel D x₁ x₂ (pairCode z' z'') q'
          (3 * t + logSlack c M) := by
  obtain ⟨A, cPair, hPair⟩ :=
    theorem2_pair_bounds
      D hD c₀
  obtain ⟨cPad, hcPad, hPad⟩ :=
    theorem2_pad_pair
      D hD A cPair
  refine ⟨cPad, ?_⟩
  intro x₁ x₂ z q t δ M β a b v' z' v'' z'' hM ht hδ hβ ha hb hq₁ hq₂
    hv₁₁ hv₁₂ hv₂₁ hv₂₂ hz₁ hz₂ haKlower hfar
  have hBounds := hPair x₁ x₂ z q t δ M β a b v' z' v'' z'' hM ht hδ hβ
    ha hb hq₁ hq₂ hv₁₁ hv₁₂ hv₂₁ hv₂₂ hz₁ hz₂ haKlower hfar
  rcases hBounds with ⟨hLower, hK, hUpper₁, hUpper₂⟩
  obtain ⟨q', hq', hExtractable⟩ :=
    hPad x₁ x₂ (pairCode z' z'') (pairCode v' v'') q t δ M ht hδ hLower hK
      hUpper₁ hUpper₂
  exact ⟨q', hq', hExtractable⟩

/-- In Case 2 of the proof of Theorem 2, some clone
`a = ⟨v', z'⟩ ∈ A` has at least half of `A` at conditional complexity `≥ β` from it, so
`I(a : b) < q - δ/2 + O(log)` for those `b`.  Among them pick `b = ⟨v'', z''⟩` with maximal
`K(b | x̄, a)` (`≥ α - 1`, by counting), so `I(z' : z'' | x̄) = O(log M)` and
`I(⟨z', z''⟩ : x̄) ≤ 3t + O(log M)`; the new oracle is `⟨z', z''⟩` and the new extracted string is
`⟨v', v''⟩`, with `K(v'v'' | z'z'') ≥ q + δ/2`, `K(v'v'' | xᵢ, z'z'') ≤ 3t + O(log M)` and
`K(x̄, z', z'') ≤ M + 2m + O(log M) ≤ 4M + O(log M)`. -/
private theorem theorem2_replace_oracle (D : Map)
    (hD : isOptimalConditional D) (c₀ : ℕ) :
    ∃ c : ℕ, ∀ (x₁ x₂ z : BitString) (q t δ M α β γ : ℕ)
      (A : Finset BitString),
      M = natK D (pairCode (pairCode x₁ x₂) z) →
      MutualInfoLe D (pairCode x₁ x₂) z t →
      CommonInfoExtractableRel D x₁ x₂ z q t →
      t ≤ M → 8 * (t + logSlack 1 M) ≤ δ →
      A.card = 2 ^ α →
      natK D z ≤ α + t + logSlack c₀ M →
      α ≤ natK D z + t + logSlack c₀ M →
      2 * (natK D z + logSlack c₀ M) + δ ≤ 2 * β →
      γ ≤ natK D z + q + logSlack c₀ M + 1 →
      (∀ a ∈ A, ∃ v' z', a = pairCode v' z' ∧
        q ≤ natCondK D v' z' + logSlack c₀ M ∧
        natCondK D v' (pairCode x₁ z') ≤ t + logSlack c₀ M ∧
        natCondK D v' (pairCode x₂ z') ≤ t + logSlack c₀ M ∧
        natCondK D x₁ a ≤ natK D x₁ - q + t + logSlack c₀ M ∧
        natCondK D x₂ a ≤ natK D x₂ - q + t + logSlack c₀ M ∧
        natK D z' ≤ natK D z + logSlack c₀ M ∧
        natK D z ≤ natK D z' + logSlack c₀ M ∧
        natK D a ≤ natK D z + q + logSlack c₀ M ∧
        natK D z + q ≤ natK D a + logSlack c₀ M ∧
        MutualInfoLe D (pairCode x₁ x₂) z' (t + logSlack c₀ M) ∧
        natCondK D a (pairCode x₁ x₂) ≤ α + logSlack c₀ M ∧
        α ≤ natCondK D a (pairCode x₁ x₂) + logSlack c₀ M) →
      (∃ a ∈ A, A.card ≤ 2 * (A.filter fun b => β ≤ natCondK D b a).card) →
      ∃ (z' : BitString) (q' : ℕ),
        2 * q + δ ≤ 2 * q' ∧
        MutualInfoLe D (pairCode x₁ x₂) z' (3 * t + logSlack c M) ∧
        CommonInfoExtractableRel D x₁ x₂ z' q' (3 * t + logSlack c M) ∧
        natK D (pairCode (pairCode x₁ x₂) z') ≤ 4 * M + logSlack c M := by
  classical
  obtain ⟨cOracle, hOracle⟩ :=
    theorem2_oracle_bounds D hD c₀
  obtain ⟨cExtract, hExtract⟩ :=
    theorem2_pair_extractable D hD c₀
  let c := max cOracle cExtract
  have hcOracle : cOracle ≤ c := le_max_left _ _
  have hcExtract : cExtract ≤ c := le_max_right _ _
  refine ⟨c, ?_⟩
  intro x₁ x₂ z q t δ M α β γ A hM hMI hRel ht hδ hcard hsize₁ hsize₂ hbeta hgamma
    hclones hbad
  obtain ⟨a, b, ha, hb, hfar, hmax⟩ :=
    theorem2_select_pair
      D hD x₁ x₂ α β A hcard hbad
  obtain ⟨v', z', haEq, hq₁, hvx₁₁, hvx₂₁, _hx₁a, _hx₂a, hz₁up, _hz₁low,
    _haKupper, haKlower, hMI₁, haCondUpper, haCondLower⟩ := hclones a ha
  obtain ⟨v'', z'', hbEq, hq₂, hvx₁₂, hvx₂₂, _hx₁b, _hx₂b, hz₂up, _hz₂low,
    _hbKupper, _hbKlower, hMI₂, hbCondUpper, hbCondLower⟩ := hclones b hb
  have hOracleBounds := hOracle x₁ x₂ z t M α A a b v' z' v'' z'' hM ht
    hsize₁ hsize₂ ha hb haEq hbEq hz₁up hz₂up hMI₁ hMI₂ haCondUpper haCondLower
    hbCondUpper hbCondLower hmax
  have hExtractable := hExtract x₁ x₂ z q t δ M β a b v' z' v'' z'' hM ht hδ
    hbeta haEq hbEq hq₁ hq₂ hvx₁₁ hvx₂₁ hvx₁₂ hvx₂₂ hz₁up hz₂up haKlower hfar
  rcases hOracleBounds with ⟨hMI', hK'⟩
  rcases hExtractable with ⟨q', hq', hExtractable'⟩
  have hlogOracle : logSlack cOracle M ≤ logSlack c M :=
    logSlack_mono_left hcOracle M
  have hlogExtract : logSlack cExtract M ≤ logSlack c M :=
    logSlack_mono_left hcExtract M
  have hMI'' : MutualInfoLe D (pairCode x₁ x₂) (pairCode z' z'')
      (3 * t + logSlack c M) := by
    change natK D (pairCode x₁ x₂) ≤
      natCondK D (pairCode x₁ x₂) (pairCode z' z'') + (3 * t + logSlack c M)
    change natK D (pairCode x₁ x₂) ≤
      natCondK D (pairCode x₁ x₂) (pairCode z' z'') +
        (3 * t + logSlack cOracle M) at hMI'
    omega
  have hK'' : natK D (pairCode (pairCode x₁ x₂) (pairCode z' z'')) ≤
      4 * M + logSlack c M := by
    change natK D (pairCode (pairCode x₁ x₂) (pairCode z' z'')) ≤
      4 * M + logSlack cOracle M at hK'
    omega
  rcases hExtractable' with ⟨w, hwq, hw₁, hw₂⟩
  refine ⟨pairCode z' z'', q', hq', hMI'', ⟨w, hwq, ?_, ?_⟩, hK''⟩
  · change natCondK D w (pairCode x₁ (pairCode z' z'')) ≤
      3 * t + logSlack cExtract M at hw₁
    omega
  · change natCondK D w (pairCode x₂ (pairCode z' z'')) ≤
      3 * t + logSlack cExtract M at hw₂
    omega

/-- Typize the pair consisting of an extracted
string and the oracle, then apply the standard semi-bunch cover from Lemma 6.  Either this gives a
common-information witness with the stated loss, or a pair of clones yields a new oracle, a larger
extractable amount, and the same hypotheses with a larger threshold.  The size parameter `M` is
the complexity of the current tuple `(x₁, x₂, z)`; the bounds in the contract are the bookkeeping
needed when this step is iterated. -/
theorem theorem2_typization_and_cover (D : Map)
    (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ (x₁ x₂ z : BitString) (q t δ M : ℕ),
      M = natK D (pairCode (pairCode x₁ x₂) z) →
      MutualInfoLe D (pairCode x₁ x₂) z t →
      CommonInfoExtractableRel D x₁ x₂ z q t →
      t ≤ M → 8 * (t + logSlack 1 M) ≤ δ →
      (∃ w : BitString,
        q ≤ natK D w + 2 * δ + logSlack c M ∧
        natCondK D w x₁ ≤ 3 * δ + logSlack c M ∧
        natCondK D w x₂ ≤ 3 * δ + logSlack c M ∧
        natK D w ≤ c * (M + 1)) ∨
      (∃ (z' : BitString) (q' : ℕ),
        2 * q + δ ≤ 2 * q' ∧
        MutualInfoLe D (pairCode x₁ x₂) z' (3 * t + logSlack c M) ∧
        CommonInfoExtractableRel D x₁ x₂ z' q' (3 * t + logSlack c M) ∧
        natK D (pairCode (pairCode x₁ x₂) z') ≤ 4 * M + logSlack c M) := by
  obtain ⟨cCut, hCut⟩ := theorem2_cut D hD
  obtain ⟨cTypize, hTypize⟩ := theorem2_typize D hD cCut
  obtain ⟨cCover, hCover⟩ :=
    theorem2_cover_semibunch D hD cTypize
  obtain ⟨cReplace, hReplace⟩ :=
    theorem2_replace_oracle D hD cTypize
  let c := max cTypize (max cCover cReplace)
  have hcTypize : cTypize ≤ c := le_max_left _ _
  have hcCover : cCover ≤ c := (le_max_left _ _).trans (le_max_right _ _)
  have hcReplace : cReplace ≤ c := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨c, ?_⟩
  intro x₁ x₂ z q t δ M hM hMI hExtract ht hδ
  obtain ⟨v, hv₁, hv₂, hv₃, hv₄⟩ := hCut x₁ x₂ z q t M hM hExtract ht
  obtain ⟨α, β, γ, A, hcard, hsize₁, hsize₂, hbeta, hbeta', hgamma, hclones, hcomplex⟩ :=
    hTypize x₁ x₂ z v q t δ M hM hMI hv₁ hv₂ hv₃ hv₄ ht hδ
  have hcases := theorem2_semi_bunch_dichotomy
    D α β γ A hcard hcomplex
  rcases hcases with hsemi | hbad
  · obtain ⟨w, hq, hx₁, hx₂, hw⟩ := hCover x₁ x₂ z q t δ M α β γ A hM hMI
      hExtract ht hδ hcard hsize₁ hsize₂ hbeta hbeta' hgamma hclones hsemi
    have hlog := logSlack_mono_left hcCover M
    refine Or.inl ⟨w, ?_, ?_, ?_, ?_⟩
    · exact hq.trans (by omega)
    · exact hx₁.trans (by omega)
    · exact hx₂.trans (by omega)
    · exact hw.trans (Nat.mul_le_mul_right (M + 1) hcCover)
  · obtain ⟨z', q', hq', hMI', hExtract', hK'⟩ := hReplace x₁ x₂ z q t δ M
      α β γ A hM hMI hExtract ht hδ hcard hsize₁ hsize₂ hbeta hgamma hclones hbad
    have hlog := logSlack_mono_left hcReplace M
    have hMI'' : MutualInfoLe D (pairCode x₁ x₂) z' (3 * t + logSlack c M) := by
      change natK D (pairCode x₁ x₂) ≤
        natCondK D (pairCode x₁ x₂) z' + (3 * t + logSlack c M)
      change natK D (pairCode x₁ x₂) ≤
        natCondK D (pairCode x₁ x₂) z' + (3 * t + logSlack cReplace M) at hMI'
      omega
    rcases hExtract' with ⟨v, hvq, hv₁, hv₂⟩
    refine Or.inr ⟨z', q', hq', hMI'', ⟨v, hvq, ?_, ?_⟩, ?_⟩ <;> omega

/- `logSlack` is logarithmic because the bit length is bounded by a real logarithm. -/

end Kolmogorov.Relativization
