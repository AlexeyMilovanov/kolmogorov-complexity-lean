/-
Copyright (c) 2026 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Relativization.CommonInformation.MutualInformationBounds

/-!
# Pair Clone Bounds

This module proves bounds for pairs of clones and paired replacement oracles.
It formalizes oracle bounds in the relativization argument of Muchnik and Romashchenko.
-/

namespace Kolmogorov.Relativization
open Filter Asymptotics

/-! The remaining helpers isolate the size estimate for a pair of clones, its
conditional independence, and the data-processing step for their oracle
components. -/

/-- The conditional complexity of a pair of clones is bounded linearly by the
complexity of the original triple. -/
private theorem theorem2_clone_pair_complexity
    (D : Map) (hD : isOptimalConditional D) (c₀ : ℕ) :
    ∃ c : ℕ, ∀ (x₁ x₂ z : BitString) (t M α : ℕ) (a b : BitString),
      M = natK D (pairCode (pairCode x₁ x₂) z) →
      t ≤ M →
      natK D z ≤ α + t + logSlack c₀ M →
      α ≤ natK D z + t + logSlack c₀ M →
      natCondK D a (pairCode x₁ x₂) ≤ α + logSlack c₀ M →
      natCondK D b (pairCode x₁ x₂) ≤ α + logSlack c₀ M →
      natCondK D (pairCode a b) (pairCode x₁ x₂) ≤
        4 * M + logSlack c M := by
  obtain ⟨cRight, hRight⟩ := pairPlainK_right_le D hD
  obtain ⟨cPair, hPair⟩ := condK_pair_le_add D hD
  obtain ⟨cFold, hFold⟩ := logSlack_linear_bound cPair
    (8 + 12 * c₀) (2 * cRight + 12 * c₀ + 1)
  let c := cFold + 12 * c₀ + 2 * cRight
  refine ⟨c, ?_⟩
  intro x₁ x₂ z t M α a b hM ht hsize₁ hsize₂ ha hb
  let X := pairCode x₁ x₂
  let L := logSlack c₀ M
  have hMX : M = natK D (pairCode X z) := by simpa [X] using hM
  have hzproj := hRight X z
  change plainK D z ≤ plainK D (pairCode X z) + (cRight : ℕ∞) at hzproj
  rw [commonInfo_le_mutualInfo_hasPlainValue D hD z,
    commonInfo_le_mutualInfo_hasPlainValue D hD (pairCode X z)] at hzproj
  rw [← hMX] at hzproj
  have hz : natK D z ≤ M + cRight := by exact_mod_cast hzproj
  have hCa := condK_le_add_condMutualInfo_value D hD a X
  have hCb := condK_le_add_condMutualInfo_value D hD b X
  have hPairENat := hPair a b X (natCondK D a X) (natCondK D b X) hCa hCb
  change condK D (pairCode a b) X ≤
    (natCondK D a X : ℕ∞) + (natCondK D b X : ℕ∞) +
      (logSlack cPair (natCondK D a X + natCondK D b X + 1) : ℕ∞) at hPairENat
  rw [← ENat.natCast_toNat
    (condK_ne_top_of_optimal D hD (pairCode a b) X)] at hPairENat
  have hPairNat : natCondK D (pairCode a b) X ≤
      natCondK D a X + natCondK D b X +
        logSlack cPair (natCondK D a X + natCondK D b X + 1) := by
    exact_mod_cast hPairENat
  have hLlin : L ≤ c₀ * M + c₀ := by
    dsimp [L]
    exact logSlack_le_self_linear c₀ M
  have hCaBound : natCondK D a X ≤ 2 * M + cRight + 3 * L := by
    dsimp [X, L] at ha hsize₁ hsize₂ ⊢
    omega
  have hCbBound : natCondK D b X ≤ 2 * M + cRight + 3 * L := by
    dsimp [X, L] at hb hsize₁ hsize₂ ⊢
    omega
  have hArg : natCondK D a X + natCondK D b X + 1 ≤
      (8 + 12 * c₀) * M + (2 * cRight + 12 * c₀ + 1) := by
    have h := Nat.mul_le_mul_left 12 hLlin
    dsimp [L] at h ⊢
    nlinarith [hCaBound, hCbBound]
  have hPairLog :
      logSlack cPair (natCondK D a X + natCondK D b X + 1) ≤ logSlack cFold M :=
    logSlack_le_of_linear_bound hFold hArg
  have hResidual : 6 * L + 2 * cRight + logSlack cFold M ≤ logSlack c M := by
    dsimp [L, c]
    unfold logSlack
    have hcoef : 6 * c₀ + cFold ≤ cFold + 12 * c₀ + 2 * cRight := by omega
    have hconst : 6 * c₀ + cFold + 2 * cRight ≤ cFold + 12 * c₀ + 2 * cRight := by
      omega
    nlinarith [Nat.mul_le_mul_right (Nat.bits M).length hcoef]
  change natCondK D (pairCode a b) X ≤ 4 * M + logSlack c M
  have hPairBound : natCondK D (pairCode a b) X ≤
      4 * M + 2 * cRight + 6 * L + logSlack cFold M := by
    calc
      natCondK D (pairCode a b) X
          ≤ natCondK D a X + natCondK D b X +
              logSlack cPair (natCondK D a X + natCondK D b X + 1) := hPairNat
      _ ≤ 4 * M + 2 * cRight + 6 * L + logSlack cFold M := by
        omega
  omega

/-- A clone complexity window and a conditional lower bound imply small
conditional mutual information between the clones. -/
private theorem theorem2_clone_independence
    (D : Map) (hD : isOptimalConditional D) (c₀ cPair : ℕ) :
    ∃ c : ℕ, ∀ (X _z : BitString) (M α : ℕ) (a b : BitString),
      natCondK D (pairCode a b) X ≤ 4 * M + logSlack cPair M →
      natCondK D b X ≤ α + logSlack c₀ M →
      α ≤ natCondK D b (pairCode X a) + 1 →
      natCondK D a X + natCondK D b X ≤
        natCondK D (pairCode a b) X + logSlack c M := by
  obtain ⟨cSwap, hSwap⟩ := Kolmogorov.condK_cond_swapPairCode_le D hD
  obtain ⟨cChain, hChain⟩ := Kolmogorov.condK_pairCode_chain_lower_values D hD
  obtain ⟨cFold, hFold⟩ := logSlack_absorb_of_le_linear cChain (4 + cPair) (cPair + 1)
  let c := cFold + c₀ + cSwap + 1
  refine ⟨c, ?_⟩
  intro X z M α a b hPairBound hBUpper hmax
  let L := logSlack c₀ M
  have hSwapENat := hSwap b a X
  change condK D b (pairCode X a) ≤
    condK D b (pairCode a X) + (cSwap : ℕ∞) at hSwapENat
  rw [← ENat.natCast_toNat
      (condK_ne_top_of_optimal D hD b (pairCode X a)),
    ← ENat.natCast_toNat
      (condK_ne_top_of_optimal D hD b (pairCode a X))] at hSwapENat
  have hSwapNat : natCondK D b (pairCode X a) ≤
      natCondK D b (pairCode a X) + cSwap := by exact_mod_cast hSwapENat
  have hBLower : α ≤ natCondK D b (pairCode a X) + cSwap + 1 := by omega
  have hBWindow : natCondK D b X ≤
      natCondK D b (pairCode a X) + cSwap + 1 + L := by
    dsimp [L] at hBUpper ⊢
    omega
  have hCaValue := condK_le_add_condMutualInfo_value D hD a X
  have hBValue := condK_le_add_condMutualInfo_value D hD b (pairCode a X)
  have hABValue := condK_le_add_condMutualInfo_value D hD (pairCode a b) X
  have hChain := hChain a b X (natCondK D a X)
    (natCondK D b (pairCode a X)) (natCondK D (pairCode a b) X)
    hCaValue hBValue hABValue
  have hChainNat : natCondK D a X + natCondK D b (pairCode a X) ≤
      natCondK D (pairCode a b) X +
        logSlack cChain (natCondK D (pairCode a b) X + 1) := hChain
  have hPairArg : natCondK D (pairCode a b) X + 1 ≤
      (4 + cPair) * M + (cPair + 1) := by
    have hLinear := logSlack_le_self_linear cPair M
    calc
      natCondK D (pairCode a b) X + 1
          ≤ 4 * M + logSlack cPair M + 1 := Nat.add_le_add_right hPairBound 1
      _ ≤ 4 * M + (cPair * M + cPair) + 1 := by omega
      _ = (4 + cPair) * M + (cPair + 1) := by ring
  have hChainErr :
      logSlack cChain (natCondK D (pairCode a b) X + 1) ≤ logSlack cFold M :=
    hFold M (natCondK D (pairCode a b) X + 1) hPairArg
  have hResidual : logSlack cFold M + L + (cSwap + 1) ≤ logSlack c M := by
    calc
      logSlack cFold M + L + (cSwap + 1)
          = logSlack (cFold + c₀) M + (cSwap + 1) := by
            dsimp [L]
            rw [logSlack_add_const]
      _ ≤ logSlack (cFold + c₀ + (cSwap + 1)) M :=
        logSlack_add_nat_le (cFold + c₀) (cSwap + 1) M
      _ = logSlack c M := by simp [c, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  calc
    natCondK D a X + natCondK D b X
        ≤ natCondK D (pairCode a b) X +
            (logSlack cChain (natCondK D (pairCode a b) X + 1) + L + (cSwap + 1)) := by
              omega
    _ ≤ natCondK D (pairCode a b) X + logSlack c M := by omega

/-- Computable images satisfy a conditional data-processing inequality, with
the chain-rule error measured at the input pair's complexity. -/
private theorem theorem2_projection_data_processing
    (D : Map) (hD : isOptimalConditional D)
    (f g : BitString → BitString) (hf : Computable f) (hg : Computable g) :
    ∃ c : ℕ, ∀ (X a b : BitString) (n k : ℕ),
      natCondK D (pairCode a b) X ≤ n →
      natCondK D a X + natCondK D b X ≤
        natCondK D (pairCode a b) X + k →
      natCondK D (f a) X + natCondK D (g b) X ≤
        natCondK D (pairCode (f a) (g b)) X + k + logSlack c (n + 1) := by
  obtain ⟨cMut, hMut⟩ := condK_le_add_condMutualInfo D hD
  obtain ⟨cComp, hComp⟩ := Kolmogorov.condK_comp D hD
    (fun q : BitString => f (decodeFirst q)) (hf.comp decodeFirst_computable)
  let contextImage : BitString → BitString := fun q =>
    pairCode (g (decodeFirst q)) (decodeSecond q)
  have hContextImage : Computable contextImage := by
    exact pairCode_computable.comp
      ((hg.comp decodeFirst_computable).pair decodeSecond_computable)
  obtain ⟨cCtx, hCtx⟩ := Kolmogorov.condK_cond_map_le D hD
    contextImage hContextImage
  let pairImage : BitString → BitString := fun q =>
    pairCode (f (decodeFirst q)) (g (decodeSecond q))
  have hPairImage : Computable pairImage := by
    exact Computable₂.comp pairCode_computable
      (hf.comp decodeFirst_computable) (hg.comp decodeSecond_computable)
  obtain ⟨cImage, hImage⟩ := condK_le_add_condMutualInfo_nat_map D hD
    pairImage hPairImage
  let tripleImage : BitString → BitString := fun q =>
    pairCode q (f (decodeFirst q))
  have hTripleImage : Computable tripleImage := by
    exact pairCode_computable.comp
      (Computable.id.pair (hf.comp decodeFirst_computable))
  obtain ⟨cTriple, hTriple⟩ := condK_le_add_condMutualInfo_nat_map D hD
    tripleImage hTripleImage
  obtain ⟨cSwap, hSwap⟩ := condK_le_add_condMutualInfo_nat_map D hD
    swapPairCode swapPairCode_computable
  obtain ⟨cChain, hChain⟩ := Kolmogorov.condK_pairCode_chain_lower_values D hD
  obtain ⟨cMutFold, hMutFold⟩ := logSlack_absorb_of_le_linear cMut 1 cTriple
  obtain ⟨cChainFold, hChainFold⟩ :=
    logSlack_absorb_of_le_linear cChain 1 (cImage + cSwap)
  refine ⟨cMutFold + cChainFold + cComp + cCtx + cSwap, ?_⟩
  intro X a b n k hPairInput hIndependent
  let imagePair := pairCode (f a) (g b)
  let reverseImagePair := pairCode (g b) (f a)
  let triple := pairCode (pairCode a b) (f a)
  have hCompENat : condK D (f a) (pairCode a X) ≤ (cComp : ℕ∞) := by
    simpa [decodeFirst_pairCode] using hComp (pairCode a X)
  have hCompNat : natCondK D (f a) (pairCode a X) ≤ cComp := by
    rw [← ENat.natCast_toNat
      (condK_ne_top_of_optimal D hD (f a) (pairCode a X))] at hCompENat
    exact_mod_cast hCompENat
  have hCtxENat : condK D (f a) (pairCode b X) ≤
      condK D (f a) (pairCode (g b) X) + (cCtx : ℕ∞) := by
    simpa [contextImage, decodeFirst_pairCode, decodeSecond_pairCode] using
      hCtx (f a) (pairCode b X)
  have hCtxNat : natCondK D (f a) (pairCode b X) ≤
      natCondK D (f a) (pairCode (g b) X) + cCtx := by
    rw [← ENat.natCast_toNat
      (condK_ne_top_of_optimal D hD (f a) (pairCode b X)),
      ← ENat.natCast_toNat
        (condK_ne_top_of_optimal D hD (f a) (pairCode (g b) X))] at hCtxENat
    exact_mod_cast hCtxENat
  have hPairImageBound : natCondK D imagePair X ≤
      natCondK D (pairCode a b) X + cImage := by
    simpa [pairImage, imagePair, decodeFirst_pairCode,
      decodeSecond_pairCode] using hImage (pairCode a b) X
  have hTripleBound : natCondK D triple X ≤ n + cTriple := by
    calc
      natCondK D triple X ≤ natCondK D (pairCode a b) X + cTriple := by
        simpa [tripleImage, triple, decodeFirst_pairCode] using
          hTriple (pairCode a b) X
      _ ≤ n + cTriple := Nat.add_le_add_right hPairInput cTriple
  have hSwapBound : natCondK D reverseImagePair X ≤
      natCondK D imagePair X + cSwap := by
    simpa [reverseImagePair, imagePair] using hSwap imagePair X
  have hReverseBound : natCondK D reverseImagePair X ≤ n + cImage + cSwap := by
    calc
      natCondK D reverseImagePair X ≤ natCondK D imagePair X + cSwap := hSwapBound
      _ ≤ natCondK D (pairCode a b) X + cImage + cSwap := by omega
      _ ≤ n + cImage + cSwap := by
        simpa [Nat.add_assoc] using
          Nat.add_le_add_right hPairInput (cImage + cSwap)
  have hImageMI : natCondK D (f a) X + natCondK D (pairCode a b) X ≤
      natCondK D (f a) (pairCode a X) + natCondK D (f a) (pairCode b X) +
        natCondK D a X + natCondK D b X + logSlack cMut (natCondK D triple X) := by
    simpa [triple] using hMut a b (f a) X
  have hImageMI' : natCondK D (f a) X + natCondK D (pairCode a b) X ≤
      natCondK D (f a) (pairCode a X) + natCondK D (f a) (pairCode (g b) X) +
        natCondK D a X + natCondK D b X + cCtx +
        logSlack cMut (natCondK D triple X) := by
    omega
  have hFirstImage : natCondK D (f a) X ≤
      natCondK D (f a) (pairCode (g b) X) + k + cComp + cCtx +
        logSlack cMut (natCondK D triple X) := by
    omega
  have hChainInstance := hChain (g b) (f a) X
    (natCondK D (g b) X) (natCondK D (f a) (pairCode (g b) X))
    (natCondK D reverseImagePair X)
    (condK_le_add_condMutualInfo_value D hD (g b) X)
    (condK_le_add_condMutualInfo_value D hD (f a) (pairCode (g b) X))
    (condK_le_add_condMutualInfo_value D hD reverseImagePair X)
  have hOutputRaw : natCondK D (f a) X + natCondK D (g b) X ≤
      natCondK D imagePair X + k + cComp + cCtx + cSwap +
        logSlack cMut (natCondK D triple X) +
        logSlack cChain (natCondK D reverseImagePair X + 1) := by
    omega
  have hMutSlack : logSlack cMut (natCondK D triple X) ≤
      logSlack cMutFold (n + 1) := by
    calc
      logSlack cMut (natCondK D triple X) ≤ logSlack cMut (n + cTriple) :=
        logSlack_mono_right cMut hTripleBound
      _ ≤ logSlack cMutFold n := hMutFold n (n + cTriple) (by omega)
      _ ≤ logSlack cMutFold (n + 1) :=
        logSlack_mono_right cMutFold (by omega)
  have hChainSlack : logSlack cChain (natCondK D reverseImagePair X + 1) ≤
      logSlack cChainFold (n + 1) := by
    apply hChainFold (n + 1) (natCondK D reverseImagePair X + 1)
    omega
  have hSlackAndConstants :
      logSlack cMutFold (n + 1) + logSlack cChainFold (n + 1) +
          (cComp + cCtx + cSwap) ≤
        logSlack (cMutFold + cChainFold + cComp + cCtx + cSwap) (n + 1) := by
    calc
      logSlack cMutFold (n + 1) + logSlack cChainFold (n + 1) +
          (cComp + cCtx + cSwap)
          = logSlack (cMutFold + cChainFold) (n + 1) +
              (cComp + cCtx + cSwap) := by rw [logSlack_add_const]
      _ ≤ logSlack (cMutFold + cChainFold + (cComp + cCtx + cSwap)) (n + 1) :=
        logSlack_add_nat_le _ _ _
      _ = logSlack (cMutFold + cChainFold + cComp + cCtx + cSwap) (n + 1) := by
        simp [Nat.add_assoc]
  change natCondK D (f a) X + natCondK D (g b) X ≤
    natCondK D imagePair X + k +
      logSlack (cMutFold + cChainFold + cComp + cCtx + cSwap) (n + 1)
  omega

/-- The data-processing chain-rule error can be absorbed into the logarithmic
budget at the original complexity. -/
private theorem theorem2_projection_slack_absorption
    (D : Map) (hD : isOptimalConditional D) (cPair cInd : ℕ)
    (f g : BitString → BitString) (hf : Computable f) (hg : Computable g) :
    ∃ c : ℕ, ∀ (X : BitString) (M : ℕ) (a b : BitString),
      natCondK D (pairCode a b) X ≤ 4 * M + logSlack cPair M →
      natCondK D a X + natCondK D b X ≤
        natCondK D (pairCode a b) X + logSlack cInd M →
      natCondK D (f a) X + natCondK D (g b) X ≤
        natCondK D (pairCode (f a) (g b)) X + logSlack c M := by
  obtain ⟨cData, hData⟩ :=
    theorem2_projection_data_processing
      D hD f g hf hg
  obtain ⟨cFold, hFold⟩ :=
    logSlack_absorb_of_le_linear cData (4 + cPair) (cPair + 1)
  let c := cInd + cFold
  refine ⟨c, ?_⟩
  intro X M a b hPairBound hInd
  have hLinear := logSlack_le_self_linear cPair M
  have hArg : natCondK D (pairCode a b) X + 1 ≤
      (4 + cPair) * M + (cPair + 1) := by
    calc
      natCondK D (pairCode a b) X + 1
          ≤ 4 * M + logSlack cPair M + 1 := Nat.add_le_add_right hPairBound 1
      _ ≤ 4 * M + (cPair * M + cPair) + 1 := by omega
      _ = (4 + cPair) * M + (cPair + 1) := by ring
  have hData' := hData X a b (natCondK D (pairCode a b) X)
    (logSlack cInd M) le_rfl hInd
  have hFolded := hFold M (natCondK D (pairCode a b) X + 1) hArg
  calc
    natCondK D (f a) X + natCondK D (g b) X
        ≤ natCondK D (pairCode (f a) (g b)) X +
            logSlack cInd M + logSlack cFold M := by omega
    _ = natCondK D (pairCode (f a) (g b)) X + logSlack c M := by
      simp [logSlack, c]
      ring

/-- Conditional independence of the selected clones bounds the dependence
between their oracle components. -/
private theorem theorem2_oracle_bounds_clone_independence
    (D : Map) (hD : isOptimalConditional D) (c₀ : ℕ) :
    ∃ c : ℕ, ∀ (x₁ x₂ z : BitString) (t M α : ℕ)
      (a b v' z' v'' z'' : BitString),
      M = natK D (pairCode (pairCode x₁ x₂) z) →
      t ≤ M →
      natK D z ≤ α + t + logSlack c₀ M →
      α ≤ natK D z + t + logSlack c₀ M →
      a = pairCode v' z' → b = pairCode v'' z'' →
      natK D z' ≤ natK D z + logSlack c₀ M →
      natK D z'' ≤ natK D z + logSlack c₀ M →
      natCondK D a (pairCode x₁ x₂) ≤ α + logSlack c₀ M →
      natCondK D b (pairCode x₁ x₂) ≤ α + logSlack c₀ M →
      α ≤ natCondK D b (pairCode x₁ x₂) + logSlack c₀ M →
      α ≤ natCondK D b (pairCode (pairCode x₁ x₂) a) + 1 →
      natCondK D z' (pairCode x₁ x₂) + natCondK D z'' (pairCode x₁ x₂) ≤
        natCondK D (pairCode z' z'') (pairCode x₁ x₂) + logSlack c M := by
  obtain ⟨cPair, hPair⟩ :=
    theorem2_clone_pair_complexity
      D hD c₀
  obtain ⟨cInd, hInd⟩ :=
    theorem2_clone_independence
      D hD c₀ cPair
  obtain ⟨cProj, hProj⟩ :=
    theorem2_projection_slack_absorption
      D hD cPair cInd decodeSecond decodeSecond
      decodeSecond_computable decodeSecond_computable
  refine ⟨cProj, ?_⟩
  intro x₁ x₂ z t M α a b v' z' v'' z'' hM ht hsize₁ hsize₂ haEq hbEq hz' hz''
    haUpper hbUpper hbLower hmax
  let X := pairCode x₁ x₂
  have hPairBound := hPair x₁ x₂ z t M α a b hM ht hsize₁ hsize₂ haUpper hbUpper
  have hCloneInd := hInd X z M α a b hPairBound hbUpper hmax
  have hProj := hProj X M a b hPairBound hCloneInd
  simpa [X, haEq, hbEq, decodeFirst_pairCode, decodeSecond_pairCode] using hProj

/-- Orient mutual information using plain symmetry of information. -/
private theorem theorem2_pair_information_orientation
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

/-- Conditional independence of the oracle components combines with their
individual information bounds to control the paired oracle. -/
private theorem theorem2_pair_information
    (D : Map) (hD : isOptimalConditional D) (c₀ cInd : ℕ) :
    ∃ c : ℕ, ∀ (x₁ x₂ z z' z'' : BitString) (t M α : ℕ),
      M = natK D (pairCode (pairCode x₁ x₂) z) →
      t ≤ M →
      natK D z ≤ α + t + logSlack c₀ M →
      α ≤ natK D z + t + logSlack c₀ M →
      natK D z' ≤ natK D z + logSlack c₀ M →
      natK D z'' ≤ natK D z + logSlack c₀ M →
      MutualInfoLe D (pairCode x₁ x₂) z' (t + logSlack c₀ M) →
      MutualInfoLe D (pairCode x₁ x₂) z'' (t + logSlack c₀ M) →
      natCondK D z' (pairCode x₁ x₂) + natCondK D z'' (pairCode x₁ x₂) ≤
        natCondK D (pairCode z' z'') (pairCode x₁ x₂) + logSlack cInd M →
      MutualInfoLe D (pairCode x₁ x₂) (pairCode z' z'')
        (3 * t + logSlack c M) := by
  obtain ⟨cOrient, hOrient⟩ :=
    theorem2_pair_information_orientation
      D hD
  obtain ⟨cSym, hSym⟩ := Kolmogorov.pairPlainK_symmetryOfInformation_values D hD
  obtain ⟨cProjX, hProjX⟩ := plainK_map_le D hD decodeFirst decodeFirst_computable
  obtain ⟨cProjZ, hProjZ⟩ := plainK_map_le D hD decodeSecond decodeSecond_computable
  obtain ⟨cPair, hPair⟩ := plainK_pair_le_two_mul D hD
  obtain ⟨cCond, hCond⟩ := condK_le_plainK D hD
  let B₀ := max (cProjX + 1) (cProjZ + c₀ + 1)
  let Bpair := 2 * B₀ + cPair
  let Bjoint := 2 * Bpair + cPair
  obtain ⟨cOrientFold, hOrientFold⟩ :=
    logSlack_linear_bound cOrient Bjoint Bjoint
  obtain ⟨cSymFold, hSymFold⟩ :=
    logSlack_linear_bound cSym Bpair (Bpair + 1)
  let cPre := cSymFold + cCond + 2 * cOrientFold + cInd + 2 * c₀
  let c := cPre + cOrientFold
  refine ⟨c, ?_⟩
  intro x₁ x₂ z z' z'' t M α hM ht hsizeZ hsizeAlpha hz' hz'' hMI' hMI'' hCI
  let X := pairCode x₁ x₂
  let S := pairCode z' z''
  let L := logSlack c₀ M
  have hXRaw := hProjX (pairCode X z)
  rw [decodeFirst_pairCode] at hXRaw
  have hZRaw := hProjZ (pairCode X z)
  rw [decodeSecond_pairCode] at hZRaw
  rw [commonInfo_le_mutualInfo_hasPlainValue D hD X,
    commonInfo_le_mutualInfo_hasPlainValue D hD (pairCode X z)] at hXRaw
  rw [commonInfo_le_mutualInfo_hasPlainValue D hD z,
    commonInfo_le_mutualInfo_hasPlainValue D hD (pairCode X z)] at hZRaw
  have hXNat : natK D X ≤ M + cProjX := by
    have hCast : (natK D X : ℕ∞) ≤ ((M + cProjX : ℕ) : ℕ∞) := by
      rw [Nat.cast_add, hM]
      exact hXRaw
    exact_mod_cast hCast
  have hZNat : natK D z ≤ M + cProjZ := by
    have hCast : (natK D z : ℕ∞) ≤ ((M + cProjZ : ℕ) : ℕ∞) := by
      rw [Nat.cast_add, hM]
      exact hZRaw
    exact_mod_cast hCast
  have hLlinear : L ≤ c₀ * (M + 1) := by
    calc
      L ≤ c₀ * M + c₀ := logSlack_le_self_linear c₀ M
      _ = c₀ * (M + 1) := by rw [Nat.mul_add]; simp
  have hMaxX : cProjX + 1 ≤ B₀ := by
    dsimp [B₀]
    exact le_max_left _ _
  have hMaxZ : cProjZ + c₀ + 1 ≤ B₀ := by
    dsimp [B₀]
    exact le_max_right _ _
  have hXSmall : natK D X ≤ B₀ * (M + 1) := by
    calc
      natK D X ≤ (cProjX + 1) * (M + 1) := by
        have hp : 0 ≤ cProjX * M := Nat.zero_le _
        nlinarith
      _ ≤ B₀ * (M + 1) := Nat.mul_le_mul_right _ hMaxX
  have hZ'Small : natK D z' ≤ B₀ * (M + 1) := by
    calc
      natK D z' ≤ natK D z + L := hz'
      _ ≤ M + cProjZ + c₀ * (M + 1) := by omega
      _ ≤ (cProjZ + c₀ + 1) * (M + 1) := by
        have hp : 0 ≤ cProjZ * M := Nat.zero_le _
        nlinarith
      _ ≤ B₀ * (M + 1) := Nat.mul_le_mul_right _ hMaxZ
  have hZ''Small : natK D z'' ≤ B₀ * (M + 1) := by
    calc
      natK D z'' ≤ natK D z + L := hz''
      _ ≤ M + cProjZ + c₀ * (M + 1) := by omega
      _ ≤ (cProjZ + c₀ + 1) * (M + 1) := by
        have hp : 0 ≤ cProjZ * M := Nat.zero_le _
        nlinarith
      _ ≤ B₀ * (M + 1) := Nat.mul_le_mul_right _ hMaxZ
  have hPairNat (n : ℕ) (a b : BitString) (ha : natK D a ≤ n)
      (hb : natK D b ≤ n) : natK D (pairCode a b) ≤ 2 * n + cPair := by
    have haENat : plainK D a ≤ (n : ℕ∞) := by
      rw [commonInfo_le_mutualInfo_hasPlainValue D hD a]
      exact_mod_cast ha
    have hbENat : plainK D b ≤ (n : ℕ∞) := by
      rw [commonInfo_le_mutualInfo_hasPlainValue D hD b]
      exact_mod_cast hb
    have hRaw := hPair n a b haENat hbENat
    change plainK D (pairCode a b) ≤ ((2 * n + cPair : ℕ) : ℕ∞) at hRaw
    rw [commonInfo_le_mutualInfo_hasPlainValue D hD (pairCode a b)] at hRaw
    exact_mod_cast hRaw
  have hSLinear : natK D S ≤ Bpair * (M + 1) := by
    have h := hPairNat (B₀ * (M + 1)) z' z'' hZ'Small hZ''Small
    dsimp [Bpair]
    dsimp [S] at h ⊢
    have hp : 0 ≤ cPair * M := Nat.zero_le _
    nlinarith
  have hPairZ'X : natK D (pairCode z' X) ≤ Bpair * (M + 1) := by
    have h := hPairNat (B₀ * (M + 1)) z' X hZ'Small hXSmall
    dsimp [Bpair]
    have hp : 0 ≤ cPair * M := Nat.zero_le _
    nlinarith
  have hPairZ''X : natK D (pairCode z'' X) ≤ Bpair * (M + 1) := by
    have h := hPairNat (B₀ * (M + 1)) z'' X hZ''Small hXSmall
    dsimp [Bpair]
    have hp : 0 ≤ cPair * M := Nat.zero_le _
    nlinarith
  have hB₀Bpair : B₀ ≤ Bpair := by
    dsimp [Bpair]
    omega
  have hBpairBjoint : Bpair ≤ Bjoint := by
    dsimp [Bjoint]
    omega
  have hXLinearBpair : natK D X ≤ Bpair * (M + 1) :=
    hXSmall.trans (Nat.mul_le_mul_right (M + 1) hB₀Bpair)
  have hPairXS : natK D (pairCode X S) ≤ Bjoint * (M + 1) := by
    have h := hPairNat (Bpair * (M + 1)) X S hXLinearBpair hSLinear
    change natK D (pairCode X S) ≤ (2 * Bpair + cPair) * (M + 1)
    have hcPair : cPair ≤ cPair * (M + 1) := by
      calc
        cPair = cPair * 1 := by simp
        _ ≤ cPair * (M + 1) := Nat.mul_le_mul_left cPair (by omega)
    calc
      natK D (pairCode X S) ≤ 2 * (Bpair * (M + 1)) + cPair := h
      _ ≤ 2 * (Bpair * (M + 1)) + cPair * (M + 1) :=
        Nat.add_le_add_left hcPair _
      _ = (2 * Bpair + cPair) * (M + 1) := by
        calc
          2 * (Bpair * (M + 1)) + cPair * (M + 1) =
              (2 * Bpair) * (M + 1) + cPair * (M + 1) := by
            rw [← Nat.mul_assoc]
          _ = (2 * Bpair + cPair) * (M + 1) := (Nat.add_mul _ _ _).symm
  have hSVal : HasPlainComplexityValue D S (natK D S) := by
    simpa [S] using commonInfo_le_mutualInfo_hasPlainValue D hD (pairCode z' z'')
  have hSymS := hSym z' z'' (natK D z') (natCondK D z'' z') (natK D S)
    (commonInfo_le_mutualInfo_hasPlainValue D hD z')
    (condK_le_add_condMutualInfo_value D hD z'' z') hSVal
  have hSymSUpper : natK D S ≤ natK D z' + natCondK D z'' z' +
      logSlack cSym (natK D S + 1) := by
    simpa [S] using hSymS.1
  have hlogS : logSlack cSym (natK D S + 1) ≤ logSlack cSymFold M := by
    have hArg : natK D S + 1 ≤ Bpair * M + (Bpair + 1) := by
      calc
        natK D S + 1 ≤ Bpair * (M + 1) + 1 := Nat.add_le_add_right hSLinear 1
        _ = Bpair * M + (Bpair + 1) := by ring
    calc
      logSlack cSym (natK D S + 1) ≤
          logSlack cSym (Bpair * M + (Bpair + 1)) := logSlack_mono_right cSym hArg
      _ ≤ logSlack cSymFold M := hSymFold M
  have hCondNat : natCondK D z'' z' ≤ natK D z'' + cCond := by
    have h := hCond z'' z'
    rw [← ENat.natCast_toNat (condK_ne_top_of_optimal D hD z'' z'),
      ← ENat.natCast_toNat (plainK_ne_top D hD z'')] at h
    exact_mod_cast h
  let cPairOver := cSymFold + cCond
  have hPairOverSlack : logSlack cSymFold M + logSlack cCond M =
      logSlack cPairOver M := by
    dsimp [cPairOver]
    unfold logSlack
    ring
  have hCondConst : cCond ≤ logSlack cCond M := by
    unfold logSlack
    omega
  have hSBound : natK D S ≤ natK D z' + natK D z'' + logSlack cPairOver M := by
    rw [← hPairOverSlack]
    omega
  have hOrientLogZ' :
      logSlack cOrient (natK D (pairCode z' X)) ≤ logSlack cOrientFold M := by
    have hPairZ'XJoint : natK D (pairCode z' X) ≤ Bjoint * (M + 1) :=
      hPairZ'X.trans (Nat.mul_le_mul_right (M + 1) hBpairBjoint)
    calc
      logSlack cOrient (natK D (pairCode z' X)) ≤
          logSlack cOrient (Bjoint * (M + 1)) :=
        logSlack_mono_right cOrient hPairZ'XJoint
      _ = logSlack cOrient (Bjoint * M + Bjoint) := by
        congr 1
      _ ≤ logSlack cOrientFold M := hOrientFold M
  have hOrientLogZ'' :
      logSlack cOrient (natK D (pairCode z'' X)) ≤ logSlack cOrientFold M := by
    have hPairZ''XJoint : natK D (pairCode z'' X) ≤ Bjoint * (M + 1) :=
      hPairZ''X.trans (Nat.mul_le_mul_right (M + 1) hBpairBjoint)
    calc
      logSlack cOrient (natK D (pairCode z'' X)) ≤
          logSlack cOrient (Bjoint * (M + 1)) :=
        logSlack_mono_right cOrient hPairZ''XJoint
      _ = logSlack cOrient (Bjoint * M + Bjoint) := by
        congr 1
      _ ≤ logSlack cOrientFold M := hOrientFold M
  have hOrientLogFinal :
      logSlack cOrient (natK D (pairCode X S)) ≤ logSlack cOrientFold M := by
    calc
      logSlack cOrient (natK D (pairCode X S)) ≤
          logSlack cOrient (Bjoint * (M + 1)) :=
        logSlack_mono_right cOrient hPairXS
      _ = logSlack cOrient (Bjoint * M + Bjoint) := by
        congr 1
      _ ≤ logSlack cOrientFold M := hOrientFold M
  have hMIz' : natK D X ≤ natCondK D X z' + (t + L) := by
    simpa [MutualInfoLe, X, L] using hMI'
  have hMIz'' : natK D X ≤ natCondK D X z'' + (t + L) := by
    simpa [MutualInfoLe, X, L] using hMI''
  have hZ'Info : natK D z' ≤ natCondK D z' X + t + L +
      logSlack cOrientFold M := by
    have h := hOrient z' X
    omega
  have hZ''Info : natK D z'' ≤ natCondK D z'' X + t + L +
      logSlack cOrientFold M := by
    have h := hOrient z'' X
    omega
  have hCI' : natCondK D z' X + natCondK D z'' X ≤
      natCondK D S X + logSlack cInd M := by
    simpa [S, X] using hCI
  have hZsum : natK D z' + natK D z'' ≤
      natCondK D z' X + natCondK D z'' X + 2 * t + 2 * L +
        2 * logSlack cOrientFold M := by
    omega
  have hSlackPre : logSlack cPairOver M + 2 * L +
      2 * logSlack cOrientFold M + logSlack cInd M = logSlack cPre M := by
    dsimp [cPre, cPairOver, L]
    unfold logSlack
    ring
  have hSInfo : natK D S ≤ natCondK D S X + 2 * t + logSlack cPre M := by
    have h := hSBound
    have h' : natK D S ≤ natCondK D S X + 2 * t +
        (logSlack cPairOver M + 2 * L +
          2 * logSlack cOrientFold M + logSlack cInd M) := by
      omega
    rw [hSlackPre] at h'
    exact h'
  have hFinalRaw : natK D X + natCondK D S X ≤
      natK D S + natCondK D X S + logSlack cOrientFold M := by
    have h := (hOrient X S).1
    have h' := Nat.add_le_add_left hOrientLogFinal
      (natK D S + natCondK D X S)
    simpa [S, X] using h.trans h'
  have hFinalBound : natK D X ≤ natCondK D X S + 2 * t +
      logSlack cPre M + logSlack cOrientFold M := by
    omega
  have hFinalSlack : logSlack cPre M + logSlack cOrientFold M = logSlack c M := by
    dsimp [c]
    unfold logSlack
    ring
  have hResult : natK D X ≤ natCondK D X S + (3 * t + logSlack c M) := by
    rw [← hFinalSlack]
    omega
  simpa [MutualInfoLe, X, S] using hResult

/-- Complexity bounds for the two components give a linear total-complexity
bound for the paired oracle. -/
private theorem theorem2_pair_complexity
    (D : Map) (hD : isOptimalConditional D) (c₀ : ℕ) :
    ∃ c : ℕ, ∀ (x₁ x₂ z z' z'' : BitString) (t M α : ℕ),
      M = natK D (pairCode (pairCode x₁ x₂) z) →
      t ≤ M →
      natK D z ≤ α + t + logSlack c₀ M →
      α ≤ natK D z + t + logSlack c₀ M →
      natK D z' ≤ natK D z + logSlack c₀ M →
      natK D z'' ≤ natK D z + logSlack c₀ M →
      natK D (pairCode (pairCode x₁ x₂) (pairCode z' z'')) ≤
        4 * M + logSlack c M := by
  obtain ⟨cLeft, hLeft⟩ := pairPlainK_left_le D hD
  obtain ⟨cRight, hRight⟩ := pairPlainK_right_le D hD
  obtain ⟨cPair, hPair⟩ := plainK_pair_le_two_mul D hD
  let c := 4 * c₀ + 4 * cRight + 3 * cPair + 2 * cLeft + 2
  refine ⟨c, ?_⟩
  intro x₁ x₂ z z' z'' t M α hM ht hsize₁ hsize₂ hz' hz''
  let X := pairCode x₁ x₂
  let L := logSlack c₀ M
  let n₁ := M + cRight + L
  let n₂ := 2 * M + 2 * L + 2 * cRight + cPair + cLeft + 1
  have hMX : M = natK D (pairCode X z) := by simpa [X] using hM
  have hXproj := hLeft X z
  change plainK D X ≤ plainK D (pairCode X z) + (cLeft : ℕ∞) at hXproj
  rw [commonInfo_le_mutualInfo_hasPlainValue D hD X,
    commonInfo_le_mutualInfo_hasPlainValue D hD (pairCode X z)] at hXproj
  rw [← hMX] at hXproj
  have hX : natK D X ≤ M + cLeft := by exact_mod_cast hXproj
  have hzproj := hRight X z
  change plainK D z ≤ plainK D (pairCode X z) + (cRight : ℕ∞) at hzproj
  rw [commonInfo_le_mutualInfo_hasPlainValue D hD z,
    commonInfo_le_mutualInfo_hasPlainValue D hD (pairCode X z)] at hzproj
  rw [← hMX] at hzproj
  have hz : natK D z ≤ M + cRight := by exact_mod_cast hzproj
  have hz'Nat : natK D z' ≤ n₁ := by dsimp [n₁, L]; omega
  have hz''Nat : natK D z'' ≤ n₁ := by dsimp [n₁, L]; omega
  have hz'ENat : plainK D z' ≤ (n₁ : ℕ∞) := by
    rw [commonInfo_le_mutualInfo_hasPlainValue D hD z']
    exact_mod_cast hz'Nat
  have hz''ENat : plainK D z'' ≤ (n₁ : ℕ∞) := by
    rw [commonInfo_le_mutualInfo_hasPlainValue D hD z'']
    exact_mod_cast hz''Nat
  have hSENat := hPair n₁ z' z'' hz'ENat hz''ENat
  change plainK D (pairCode z' z'') ≤ ((2 * n₁ + cPair : ℕ) : ℕ∞) at hSENat
  rw [commonInfo_le_mutualInfo_hasPlainValue D hD (pairCode z' z'')] at hSENat
  have hS : natK D (pairCode z' z'') ≤ 2 * n₁ + cPair := by exact_mod_cast hSENat
  have hX₂ : natK D X ≤ n₂ := by dsimp [n₂]; omega
  have hS₂ : natK D (pairCode z' z'') ≤ n₂ := by dsimp [n₂, n₁, L]; omega
  have hX₂ENat : plainK D X ≤ (n₂ : ℕ∞) := by
    rw [commonInfo_le_mutualInfo_hasPlainValue D hD X]
    exact_mod_cast hX₂
  have hS₂ENat : plainK D (pairCode z' z'') ≤ (n₂ : ℕ∞) := by
    rw [commonInfo_le_mutualInfo_hasPlainValue D hD (pairCode z' z'')]
    exact_mod_cast hS₂
  have hTotalENat := hPair n₂ X (pairCode z' z'') hX₂ENat hS₂ENat
  change plainK D (pairCode X (pairCode z' z'')) ≤
    ((2 * n₂ + cPair : ℕ) : ℕ∞) at hTotalENat
  rw [commonInfo_le_mutualInfo_hasPlainValue D hD (pairCode X (pairCode z' z''))]
    at hTotalENat
  have hTotal : natK D (pairCode X (pairCode z' z'')) ≤ 2 * n₂ + cPair :=
    by exact_mod_cast hTotalENat
  have hTotalTarget :
      natK D (pairCode (pairCode x₁ x₂) (pairCode z' z'')) ≤ 2 * n₂ + cPair := by
    simpa [X] using hTotal
  let B := 4 * cRight + 3 * cPair + 2 * cLeft + 2
  have hPairArith : 2 * n₂ + cPair = 4 * M + 4 * L + B := by
    dsimp [n₂, B]
    omega
  have hSlack : 4 * L + B ≤ logSlack c M := by
    dsimp [L, B, c]
    unfold logSlack
    have hcoef : 4 * c₀ ≤ 4 * c₀ + 4 * cRight + 3 * cPair + 2 * cLeft + 2 := by omega
    have hconst : 4 * c₀ + (4 * cRight + 3 * cPair + 2 * cLeft + 2) ≤
        4 * c₀ + 4 * cRight + 3 * cPair + 2 * cLeft + 2 := by omega
    calc
      4 * (c₀ * (Nat.bits M).length + c₀) +
          (4 * cRight + 3 * cPair + 2 * cLeft + 2) =
        (4 * c₀) * (Nat.bits M).length +
          (4 * c₀ + (4 * cRight + 3 * cPair + 2 * cLeft + 2)) := by ring
      _ ≤ (4 * c₀ + 4 * cRight + 3 * cPair + 2 * cLeft + 2) *
          (Nat.bits M).length +
          (4 * c₀ + 4 * cRight + 3 * cPair + 2 * cLeft + 2) := by
        exact Nat.add_le_add (Nat.mul_le_mul_right _ hcoef) hconst
  have hSlack : 2 * n₂ + cPair ≤ 4 * M + logSlack c M := by
    rw [hPairArith]
    calc
      4 * M + 4 * L + B = 4 * M + (4 * L + B) := by omega
      _ ≤ 4 * M + logSlack c M := Nat.add_le_add_left hSlack _
  exact hTotalTarget.trans hSlack


/-- Conditional independence of the selected clones bounds the information and
total complexity of the paired replacement oracle. -/
theorem theorem2_oracle_bounds
    (D : Map) (hD : isOptimalConditional D) (c₀ : ℕ) :
    ∃ c : ℕ, ∀ (x₁ x₂ z : BitString) (t M α : ℕ) (A : Finset BitString)
      (a b v' z' v'' z'' : BitString),
      M = natK D (pairCode (pairCode x₁ x₂) z) →
      t ≤ M →
      natK D z ≤ α + t + logSlack c₀ M →
      α ≤ natK D z + t + logSlack c₀ M →
      a ∈ A → b ∈ A →
      a = pairCode v' z' → b = pairCode v'' z'' →
      natK D z' ≤ natK D z + logSlack c₀ M →
      natK D z'' ≤ natK D z + logSlack c₀ M →
      MutualInfoLe D (pairCode x₁ x₂) z' (t + logSlack c₀ M) →
      MutualInfoLe D (pairCode x₁ x₂) z'' (t + logSlack c₀ M) →
      natCondK D a (pairCode x₁ x₂) ≤ α + logSlack c₀ M →
      α ≤ natCondK D a (pairCode x₁ x₂) + logSlack c₀ M →
      natCondK D b (pairCode x₁ x₂) ≤ α + logSlack c₀ M →
      α ≤ natCondK D b (pairCode x₁ x₂) + logSlack c₀ M →
      α ≤ natCondK D b (pairCode (pairCode x₁ x₂) a) + 1 →
      MutualInfoLe D (pairCode x₁ x₂) (pairCode z' z'')
          (3 * t + logSlack c M) ∧
        natK D (pairCode (pairCode x₁ x₂) (pairCode z' z'')) ≤
          4 * M + logSlack c M := by
  obtain ⟨cInd, hInd⟩ :=
    theorem2_oracle_bounds_clone_independence
      D hD c₀
  obtain ⟨cMI, hMI⟩ :=
    theorem2_pair_information
      D hD c₀ cInd
  obtain ⟨cK, hK⟩ :=
    theorem2_pair_complexity
      D hD c₀
  let c := max cMI cK
  refine ⟨c, ?_⟩
  intro x₁ x₂ z t M α A a b v' z' v'' z'' hM ht hsize₁ hsize₂ ha hb haEq hbEq
    hz₁ hz₂ hMI₁ hMI₂ haUpper haLower hbUpper hbLower hmax
  have hCI := hInd x₁ x₂ z t M α a b v' z' v'' z'' hM ht hsize₁ hsize₂
    haEq hbEq hz₁ hz₂ haUpper hbUpper hbLower hmax
  have hMI' := hMI x₁ x₂ z z' z'' t M α hM ht hsize₁ hsize₂ hz₁ hz₂ hMI₁ hMI₂ hCI
  have hK' := hK x₁ x₂ z z' z'' t M α hM ht hsize₁ hsize₂ hz₁ hz₂
  have hcMI : cMI ≤ c := le_max_left _ _
  have hcK : cK ≤ c := le_max_right _ _
  constructor
  · change natK D (pairCode x₁ x₂) ≤
      natCondK D (pairCode x₁ x₂) (pairCode z' z'') + (3 * t + logSlack c M)
    change natK D (pairCode x₁ x₂) ≤
      natCondK D (pairCode x₁ x₂) (pairCode z' z'') + (3 * t + logSlack cMI M) at hMI'
    have hlog := logSlack_mono_left hcMI M
    omega
  · change natK D (pairCode (pairCode x₁ x₂) (pairCode z' z'')) ≤
      4 * M + logSlack cK M at hK'
    exact hK'.trans (Nat.add_le_add_left (logSlack_mono_left hcK M) _)

end Kolmogorov.Relativization
