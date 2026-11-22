/-
Copyright (c) 2026 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Relativization.CommonInformation.MutualInformationBounds

/-!
# Clone Coordinate Chains

This module proves the typization and covering statements for common information in Theorem 2 of
Muchnik and Romashchenko's paper on relativization. It develops the coordinate, chain-rule, and
description bounds used to transfer a clone's complexity profile and construct a semi-bunch.
-/

namespace Kolmogorov.Relativization
open Filter Asymptotics

/-- Strong typization supplies enough clones for `theorem2_typize`:
Lemmas 1 and 2 for the pair `(v, z)` given `x̄ = (x₁, x₂)`.  The strong-typization constant `C` and
the slack constant `c` are fixed *before* the instance (they come from Lemma 2 for `n = m = 2` and
Lemma 1, after converting `N = K(v, z, x₁, x₂) ≤ 2M + O(log M)` to a slack in `M`, which uses
`K(v | x₁, z) ≤ t + O(log M)` and `t ≤ M`).  The strong typization `ST_{logSlack C M}(v,z | x̄)` has
more than `|T|/2 ≥ 2^{K(v,z | x̄) - O(log M) - 1}` elements; take
`α = K(v,z | x̄) - logSlack c M` (truncated at `0`; the set contains `(v, z)`, so it is non-empty)
and `B` the set of the pair codes of all its elements. -/
private theorem theorem2_strong_typization_count
    (D : Map) (hD : isOptimalConditional D) (c₀ : ℕ) :
    ∃ C c : ℕ, ∀ (x₁ x₂ z v : BitString) (t M : ℕ),
      M = natK D (pairCode (pairCode x₁ x₂) z) →
      natCondK D v (pairCode x₁ z) ≤ t + logSlack c₀ M →
      t ≤ M →
      ∃ (α : ℕ) (B : Finset BitString),
        2 ^ α ≤ B.card ∧
        natCondK D (pairCode v z) (pairCode x₁ x₂) ≤ α + logSlack c M ∧
        α ≤ natCondK D (pairCode v z) (pairCode x₁ x₂) + logSlack c M ∧
        (∀ a ∈ B, ∃ v' z', a = pairCode v' z' ∧
          (![v', z'] : Fin 2 → BitString) ∈
            strongTypization D (logSlack C M) ![v, z] ![x₁, x₂]) := by
  classical
  obtain ⟨b, hBudget⟩ :=
    theorem2_total_complexity_budget
      D hD c₀
  obtain ⟨C₀, c₁, hCount⟩ :=
    theorem2_typization_cardinality
      D hD
  obtain ⟨d, hPairCode⟩ :=
    theorem2_pair_code_conversion
      D hD
  obtain ⟨C, hC⟩ := logSlack_absorb_of_le_linear C₀ 5 b
  obtain ⟨c₂, hc₂⟩ := logSlack_absorb_of_le_linear c₁ 5 b
  let c := c₂ + d + 1
  refine ⟨C, c, ?_⟩
  intro x₁ x₂ z v t M hM hv ht
  let x : Fin 2 → BitString := ![v, z]
  let y : Fin 2 → BitString := ![x₁, x₂]
  let N := natK D (tupleCode (Fin.append x y))
  let kTuple := natCondK D (tupleCode x) (tupleCode y)
  let k := natCondK D (pairCode v z) (pairCode x₁ x₂)
  have hkPair : k ≤ kTuple + d := by
    simpa [k, kTuple, x, y] using hPairCode x₁ x₂ v z
  have hN : N ≤ 5 * M + b := by
    simpa [x, y, N] using hBudget x₁ x₂ z v t M hM hv ht
  have hCslack : logSlack C₀ N ≤ logSlack C M := hC M N hN
  have hc₂slack : logSlack c₁ N ≤ logSlack c₂ M := hc₂ M N hN
  have hdSlack : d + 1 ≤ logSlack (d + 1) M := by
    unfold logSlack
    omega
  have hslack : logSlack c₂ M + (d + 1) ≤ logSlack c M := by
    calc
      logSlack c₂ M + (d + 1) ≤ logSlack c₂ M + logSlack (d + 1) M :=
        Nat.add_le_add_left hdSlack _
      _ = logSlack (c₂ + (d + 1)) M :=
        (logSlack_add_constants c₂ (d + 1) M).symm
      _ = logSlack c M := by congr 1
  let α := k - logSlack c M
  let S₀ := strongTypization D (logSlack C₀ N) x y
  let S := strongTypization D (logSlack C M) x y
  have hcount₀ : 2 ^ (kTuple - (logSlack c₁ N + 1)) ≤ S₀.ncard := by
    simpa [x, y, N, kTuple, S₀] using hCount x y
  have hTfinite : (typization D x y).Finite := by
    obtain ⟨cFin, hFin⟩ := lemma1 D hD 2 2
    exact (hFin x y).1
  have hSfinite : S.Finite := hTfinite.subset (by
    intro a ha
    exact ha.1)
  have hS₀sub : S₀ ⊆ S := by
    intro a ha
    change ExtProfileLe D (Fin.append a y) (Fin.append x y) ∧ _ at ha
    change ExtProfileLe D (Fin.append a y) (Fin.append x y) ∧ _
    refine ⟨ha.1, ?_⟩
    intro V W hV hdis
    exact (ha.2 V W hV hdis).trans
      (Nat.add_le_add_left hCslack _)
  have hS₀le : S₀.ncard ≤ S.ncard := Set.ncard_le_ncard hS₀sub hSfinite
  let F : (Fin 2 → BitString) → BitString := fun p => pairCode (p 0) (p 1)
  have hFinj : Function.Injective F := by
    intro p q hpq
    have hpair : (p 0, p 1) = (q 0, q 1) := by
      apply pairCode_injective
      exact hpq
    funext i
    fin_cases i
    · exact congrArg Prod.fst hpair
    · exact congrArg Prod.snd hpair
  let B := hSfinite.toFinset.image F
  have hBcard : B.card = S.ncard := by
    calc
      B.card = (hSfinite.toFinset.image F).card := rfl
      _ = hSfinite.toFinset.card := Finset.card_image_iff.mpr (by
        intro p hp q hq heq
        exact hFinj heq)
      _ = S.ncard := (Set.ncard_eq_toFinset_card S hSfinite).symm
  have hpow : 2 ^ α ≤ S₀.ncard := by
    have hslack' : logSlack c₁ N + d + 1 ≤ logSlack c M := by omega
    have hexp : k - logSlack c M ≤ kTuple - (logSlack c₁ N + 1) := by omega
    dsimp [α, k]
    exact (Nat.pow_le_pow_right (by decide : 0 < 2) hexp).trans hcount₀
  have hpowB : 2 ^ α ≤ B.card := by
    calc
      2 ^ α ≤ S₀.ncard := hpow
      _ ≤ S.ncard := hS₀le
      _ = B.card := hBcard.symm
  have hαlo : k ≤ α + logSlack c M := by
    dsimp [α]
    omega
  have hαhi : α ≤ k + logSlack c M := by
    dsimp [α]
    omega
  have hB : ∀ a ∈ B, ∃ v' z', a = pairCode v' z' ∧
      (![v', z'] : Fin 2 → BitString) ∈ S := by
    intro a ha
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
    refine ⟨p 0, p 1, rfl, ?_⟩
    have hp' : p ∈ S := hSfinite.mem_toFinset.mp hp
    have hpEq : ![p 0, p 1] = p := by
      funext i
      fin_cases i <;> simp
    simpa [x, S, hpEq] using hp'
  refine ⟨α, B, hpowB, ?_, ?_, ?_⟩
  · simpa [k, x, y] using hαlo
  · simpa [k, x, y] using hαhi
  · intro a ha
    simpa [x, y, S] using hB a ha

/-- The lower side of the exponent window in `theorem2_alpha_window` follows from
derive the lower half of the window from plain symmetry of information and projection of the pair
`(v,z)` to `z`. -/
private theorem theorem2_lower
    (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ (x₁ x₂ z v : BitString) (t M : ℕ),
      M = natK D (pairCode (pairCode x₁ x₂) z) →
      MutualInfoLe D (pairCode x₁ x₂) z t →
      natK D z ≤ natCondK D (pairCode v z) (pairCode x₁ x₂) + t + logSlack c M := by
  obtain ⟨cSym, hSym⟩ := pairPlainK_symmetryOfInformation_values D hD
  obtain ⟨cSwap, hSwap⟩ := plainK_map_le D hD swapPairCode swapPairCode_computable
  obtain ⟨cProj, hProj⟩ := condK_drop_left D hD
  obtain ⟨cFold₁, hFold₁⟩ := logSlack_linear_bound cSym 1 1
  obtain ⟨cFold₂, hFold₂⟩ := logSlack_linear_bound cSym 1 (cSwap + 1)
  let c := cFold₁ + cFold₂ + cSwap + cProj
  refine ⟨c, ?_⟩
  intro x₁ x₂ z v t M hM hMI
  let x := pairCode x₁ x₂
  let kx := natK D x
  let kz := natK D z
  let kzx := natCondK D z x
  let kxz := natCondK D x z
  let kp := natK D (pairCode x z)
  let kps := natK D (pairCode z x)
  let kvz := natCondK D (pairCode v z) x
  have hx : HasPlainComplexityValue D x kx := by
    dsimp [kx, x]
    exact commonInfo_le_mutualInfo_hasPlainValue D hD _
  have hz : HasPlainComplexityValue D z kz := by
    dsimp [kz]
    exact commonInfo_le_mutualInfo_hasPlainValue D hD z
  have hzx : HasPlainConditionalComplexityValue D z x kzx := by
    dsimp [kzx, x]
    exact commonInfo_le_mutualInfo_hasCondValue D hD z _
  have hxz : HasPlainConditionalComplexityValue D x z kxz := by
    dsimp [kxz, x]
    exact commonInfo_le_mutualInfo_hasCondValue D hD _ z
  have hp : HasPlainComplexityValue D (pairCode x z) kp := by
    dsimp [kp, x]
    exact commonInfo_le_mutualInfo_hasPlainValue D hD _
  have hps : HasPlainComplexityValue D (pairCode z x) kps := by
    dsimp [kps, x]
    exact commonInfo_le_mutualInfo_hasPlainValue D hD _
  have hvz : HasPlainConditionalComplexityValue D (pairCode v z) x kvz := by
    dsimp [kvz, x]
    exact commonInfo_le_mutualInfo_hasCondValue D hD _ _
  have hSym₁ := hSym x z kx kzx kp hx hzx hp
  have hSym₂ := hSym z x kz kxz kps hz hxz hps
  have hMkp : M = kp := by simpa [kp, x] using hM
  have hSwap' : kps ≤ M + cSwap := by
    have hh := hSwap (pairCode x z)
    have hh' : plainK D (pairCode z x) ≤ plainK D (pairCode x z) + (cSwap : ℕ∞) := by
      simpa only [swapPairCode_pairCode] using hh
    rw [hps, hp] at hh'
    have hn : (kps : ℕ∞) ≤ ((M + cSwap : ℕ) : ℕ∞) := by
      rw [Nat.cast_add, hM]
      exact hh'
    exact_mod_cast hn
  have hlog₁ : logSlack cSym (M + 1) ≤ logSlack cFold₁ M := by
    simpa [Nat.add_assoc] using hFold₁ M
  have hlog₁' : logSlack cSym (kp + 1) ≤ logSlack cFold₁ M := by
    calc
      logSlack cSym (kp + 1) = logSlack cSym (M + 1) := by rw [← hMkp]
      _ ≤ logSlack cFold₁ M := hlog₁
  have hlog₂ : logSlack cSym (kps + 1) ≤ logSlack cFold₂ M := by
    calc
      logSlack cSym (kps + 1) ≤ logSlack cSym (M + (cSwap + 1)) :=
        logSlack_mono_right cSym (by omega)
      _ ≤ logSlack cFold₂ M := by simpa [Nat.add_assoc] using hFold₂ M
  have hMI' : kx ≤ kxz + t := by
    change natK D x ≤ natCondK D x z + t at hMI
    simpa [x, kx, kxz] using hMI
  have hZX : kz ≤ kzx + t + logSlack cFold₁ M + logSlack cFold₂ M + cSwap := by
    have hSym₁' : M ≤ kx + kzx + logSlack cFold₁ M := by
      calc
        M = kp := hMkp
        _ ≤ kx + kzx + logSlack cSym (kp + 1) := hSym₁.1
        _ ≤ kx + kzx + logSlack cFold₁ M := Nat.add_le_add_left hlog₁' _
    have hSym₂' : kz + kxz ≤ kps + logSlack cFold₂ M :=
      hSym₂.2.trans (Nat.add_le_add_left hlog₂ kps)
    omega
  have hProj' : kzx ≤ kvz + cProj := by
    have hh := hProj v z x (natCondK D (pairCode v z) x) kzx hvz hzx
    change natCondK D z x ≤ natCondK D (pairCode v z) x + cProj at hh
    simpa [kzx, kvz, x] using hh
  have hSwapConst : cSwap ≤ logSlack cSwap M := by
    unfold logSlack
    omega
  have hProjConst : cProj ≤ logSlack cProj M := by
    unfold logSlack
    omega
  have hsum : logSlack c M = logSlack cFold₁ M + logSlack cFold₂ M +
      logSlack cSwap M + logSlack cProj M := by
    dsimp [c]
    unfold logSlack
    ring
  have hErr : logSlack cFold₁ M + logSlack cFold₂ M + cSwap + cProj ≤ logSlack c M := by
    rw [hsum]
    omega
  calc
    kz ≤ kzx + t + logSlack cFold₁ M + logSlack cFold₂ M + cSwap := hZX
    _ ≤ kvz + cProj + t + logSlack cFold₁ M + logSlack cFold₂ M + cSwap := by omega
    _ ≤ kvz + t +
        (logSlack cFold₁ M + logSlack cFold₂ M + cSwap + cProj) := by omega
    _ ≤ kvz + t + logSlack c M := Nat.add_le_add_left hErr (kvz + t)

/-- Encode `z` first and then encode `v` using the recovered `x₁` and `z`. This mixed-context
coding bound is the conditional chain step used to prove the upper side of the exponent window. -/
private lemma theorem2_mixed_context_chain
    (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ (x₁ x₂ z v : BitString),
      natCondK D (pairCode v z) (pairCode x₁ x₂) ≤
        natK D z + natCondK D v (pairCode x₁ z) +
          logSlack c (natK D z + natCondK D v (pairCode x₁ z) + 1) := by
  let splitLength : BitString → Nat := fun q => decodeBits (decodeFirst q)
  let joinedProg : BitString → BitString := fun q => decodeSecond q
  let firstProg : BitString → BitString := fun q => (joinedProg q).take (splitLength q)
  let secondProg : BitString → BitString := fun q => (joinedProg q).drop (splitLength q)
  let E : Map := fun pr =>
    (D (firstProg pr.1, [])).bind fun z =>
      (D (secondProg pr.1, pairCode (decodeFirst pr.2) z)).map fun v => pairCode v z
  have hSplitLength : Computable splitLength := decodeBits_computable.comp decodeFirst_computable
  have hJoinedProg : Computable joinedProg := decodeSecond_computable
  have hFirstProg : Computable firstProg :=
    Primrec.list_take.to_comp.comp hSplitLength hJoinedProg
  have hSecondProg : Computable secondProg :=
    Primrec.list_drop.to_comp.comp hSplitLength hJoinedProg
  have hE : isDecompressor E := by
    have h1 : Partrec (fun pr : BitString × BitString => D (firstProg pr.1, [])) :=
      Partrec.comp hD.1 ((hFirstProg.comp Computable.fst).pair (Computable.const []))
    have hContext : Computable (fun q : (BitString × BitString) × BitString =>
        pairCode (decodeFirst q.1.2) q.2) :=
      (show Computable₂ (fun a b : BitString => pairCode a b) from pairCode_computable).comp
        (decodeFirst_computable.comp (Computable.snd.comp Computable.fst)) Computable.snd
    have h2 : Partrec (fun q : (BitString × BitString) × BitString =>
        D (secondProg q.1.1, pairCode (decodeFirst q.1.2) q.2)) :=
      Partrec.comp hD.1
        (Computable.pair
          (hSecondProg.comp (Computable.fst.comp Computable.fst)) hContext)
    have hOutput : Computable
        (fun q : ((BitString × BitString) × BitString) × BitString =>
          pairCode q.2 q.1.2) :=
      (show Computable₂ (fun a b : BitString => pairCode a b) from pairCode_computable).comp
        Computable.snd (Computable.snd.comp Computable.fst)
    exact Partrec.bind h1 (Partrec.map h2 hOutput)
  obtain ⟨cE, hE⟩ := hD.2 E hE
  refine ⟨cE + 3, fun x₁ x₂ z v => ?_⟩
  let x := pairCode x₁ x₂
  let ka := natK D z
  let kb := natCondK D v (pairCode x₁ z)
  have hza : HasPlainConditionalComplexityValue D z [] ka := by
    change HasPlainComplexityValue D z ka
    exact commonInfo_le_mutualInfo_hasPlainValue D hD z
  have hvb : HasPlainConditionalComplexityValue D v (pairCode x₁ z) kb := by
    exact commonInfo_le_mutualInfo_hasCondValue D hD v (pairCode x₁ z)
  obtain ⟨p, hpLen, hp⟩ := (condK_le_iff D z [] ka).mp (by
    unfold HasPlainConditionalComplexityValue at hza
    exact le_of_eq hza)
  obtain ⟨q, hqLen, hq⟩ := (condK_le_iff D v (pairCode x₁ z) kb).mp (by
    unfold HasPlainConditionalComplexityValue at hvb
    exact le_of_eq hvb)
  let prog : BitString := pairCode (Nat.bits p.length) (p ++ q)
  have hFirstEval : firstProg prog = p := by
    dsimp [firstProg, joinedProg, splitLength]
    rw [show prog = pairCode (Nat.bits p.length) (p ++ q) from rfl,
      decodeFirst_pairCode, decodeSecond_pairCode, decodeBits_natBits, List.take_left]
  have hSecondEval : secondProg prog = q := by
    dsimp [secondProg, joinedProg, splitLength]
    rw [show prog = pairCode (Nat.bits p.length) (p ++ q) from rfl,
      decodeFirst_pairCode, decodeSecond_pairCode, decodeBits_natBits, List.drop_left]
  have hEProd : produces E prog x (pairCode v z) := by
    change pairCode v z ∈
      (D (firstProg prog, [])).bind fun z =>
        (D (secondProg prog, pairCode (decodeFirst x) z)).map fun v => pairCode v z
    rw [hFirstEval, hSecondEval, decodeFirst_pairCode]
    exact Part.mem_bind_iff.mpr ⟨z, hp, Part.mem_map _ hq⟩
  have hBound : condK D (pairCode v z) x ≤ (prog.length : ENat) + (cE : ENat) :=
    (hE (pairCode v z) x).trans (by
      gcongr
      exact sInf_le ⟨prog, hEProd, rfl⟩)
  have hProgLength : prog.length =
      2 * (Nat.bits p.length).length + p.length + q.length + 1 := by
    dsimp [prog]
    rw [length_pairCode, List.length_append]
    omega
  have hpLen' : p.length ≤ ka := hpLen
  have hqLen' : q.length ≤ kb := hqLen
  have hBits : 2 * (Nat.bits p.length).length ≤ 2 * (Nat.bits (ka + kb + 1)).length := by
    have h1 : p.length ≤ ka + kb + 1 := by omega
    have h2 := length_natBits_mono h1
    omega
  have hLength : prog.length + cE ≤ ka + kb + logSlack (cE + 3) (ka + kb + 1) := by
    unfold logSlack
    set L := (Nat.bits (ka + kb + 1)).length with hL
    have hexpand : (cE + 3) * L + (cE + 3) =
        2 * L + (cE * L + L + cE + 3) := by ring
    rw [hexpand, hProgLength]
    omega
  have hMain : condK D (pairCode v z) x ≤
      ((ka + kb + logSlack (cE + 3) (ka + kb + 1) : Nat) : ENat) := by
    calc
      condK D (pairCode v z) x ≤ (prog.length : ENat) + (cE : ENat) := hBound
      _ = ((prog.length + cE : Nat) : ENat) := by rw [Nat.cast_add]
      _ ≤ ((ka + kb + logSlack (cE + 3) (ka + kb + 1) : Nat) : ENat) := by
        exact_mod_cast hLength
  have hValue := condK_ne_top_of_optimal D hD (pairCode v z) x
  rw [← ENat.natCast_toNat hValue] at hMain
  exact_mod_cast hMain

/-- The upper side of the exponent window in `theorem2_alpha_window` follows from
the conditional chain bound for the upper side of the exponent window, including absorption of its
complexity argument into `M`. -/
private theorem theorem2_upper
    (D : Map) (hD : isOptimalConditional D) (c₀ : ℕ) :
    ∃ c : ℕ, ∀ (x₁ x₂ z v : BitString) (t M : ℕ),
      M = natK D (pairCode (pairCode x₁ x₂) z) →
      natCondK D v (pairCode x₁ z) ≤ t + logSlack c₀ M →
      t ≤ M →
      natCondK D (pairCode v z) (pairCode x₁ x₂) ≤ natK D z + t + logSlack c M := by
  obtain ⟨cChain, hChain⟩ :=
    theorem2_mixed_context_chain
      D hD
  obtain ⟨cDrop, hDrop⟩ := plainK_map_le D hD decodeSecond decodeSecond_computable
  obtain ⟨cFold, hFold⟩ := logSlack_linear_bound cChain (c₀ + 2) (cDrop + c₀ + 1)
  let c := cFold + c₀
  refine ⟨c, ?_⟩
  intro x₁ x₂ z v t M hM hv ht
  let b := natCondK D v (pairCode x₁ z)
  have hzVal := commonInfo_le_mutualInfo_hasPlainValue D hD z
  have hPairVal := commonInfo_le_mutualInfo_hasPlainValue D hD (pairCode (pairCode x₁ x₂) z)
  have hzM : natK D z ≤ M + cDrop := by
    have h := hDrop (pairCode (pairCode x₁ x₂) z)
    rw [decodeSecond_pairCode, hzVal, hPairVal] at h
    have h' : (natK D z : ENat) ≤ (M + cDrop : Nat) := by
      rw [Nat.cast_add, hM]
      exact h
    exact_mod_cast h'
  have hLogLinear : logSlack c₀ M ≤ c₀ * M + c₀ := logSlack_le_self_linear c₀ M
  have hArg : natK D z + b + 1 ≤ (c₀ + 2) * M + (cDrop + c₀ + 1) := by
    calc
      natK D z + b + 1 ≤ (M + cDrop) + (t + logSlack c₀ M) + 1 := by
        dsimp [b]
        omega
      _ ≤ (M + cDrop) + (M + (c₀ * M + c₀)) + 1 := by
        omega
      _ = (c₀ + 2) * M + (cDrop + c₀ + 1) := by ring
  have hFolded :
      logSlack cChain (natK D z + b + 1) ≤ logSlack cFold M := by
    calc
      logSlack cChain (natK D z + b + 1) ≤
          logSlack cChain ((c₀ + 2) * M + (cDrop + c₀ + 1)) :=
        logSlack_mono_right cChain hArg
      _ ≤ logSlack cFold M := hFold M
  have hFolded' : logSlack cChain
      (natK D z + natCondK D v (pairCode x₁ z) + 1) ≤ logSlack cFold M := by
    simpa [b] using hFolded
  calc
    natCondK D (pairCode v z) (pairCode x₁ x₂) ≤
        natK D z + b + logSlack cChain (natK D z + b + 1) := hChain x₁ x₂ z v
    _ ≤ natK D z + t + logSlack cFold M + logSlack c₀ M := by
      dsimp [b]
      have hb : natCondK D v (pairCode x₁ z) ≤ t + logSlack c₀ M := hv
      omega
    _ = natK D z + t + logSlack c M := by
      dsimp [c]
      rw [← logSlack_add_const cFold c₀ M]
      omega

/-- The exponent window used by `theorem2_typize`:
the exponent window.  With `x̄ = (x₁, x₂)`, `K(z | x̄) ≥ K(z) - t - O(log M)` (symmetry of
information and `K(x̄) ≤ K(x̄ | z) + t`), `K(⟨v,z⟩ | x̄) ≥ K(z | x̄) - O(1)`, and
`K(⟨v,z⟩ | x̄) ≤ K(z | x̄) + K(v | x̄, z) + O(log M) ≤ K(z) + t + O(log M)`, using
`K(v | x̄, z) ≤ K(v | x₁, z) + O(1) ≤ t + O(log M)`. -/
private theorem theorem2_alpha_window
    (D : Map) (hD : isOptimalConditional D) (c₀ : ℕ) :
    ∃ c : ℕ, ∀ (x₁ x₂ z v : BitString) (t M : ℕ),
      M = natK D (pairCode (pairCode x₁ x₂) z) →
      MutualInfoLe D (pairCode x₁ x₂) z t →
      natCondK D v (pairCode x₁ z) ≤ t + logSlack c₀ M →
      t ≤ M →
      natK D z ≤ natCondK D (pairCode v z) (pairCode x₁ x₂) + t + logSlack c M ∧
      natCondK D (pairCode v z) (pairCode x₁ x₂) ≤ natK D z + t + logSlack c M := by
  obtain ⟨c₁, h₁⟩ :=
    theorem2_lower D hD
  obtain ⟨c₂, h₂⟩ :=
    theorem2_upper D hD c₀
  refine ⟨c₁ + c₂, ?_⟩
  intro x₁ x₂ z v t M hM hMI hv ht
  have h₁' := h₁ x₁ x₂ z v t M hM hMI
  have h₂' := h₂ x₁ x₂ z v t M hM hv ht
  constructor
  · exact h₁'.trans (Nat.add_le_add_left
      (logSlack_mono_left (Nat.le_add_right c₁ c₂) M) (natCondK D (pairCode v z) (pairCode x₁ x₂) +
          t))
  · exact h₂'.trans (Nat.add_le_add_left
      (logSlack_mono_left (Nat.le_add_left c₂ c₁) M) (natK D z + t))

private theorem theorem2_clone_coordinates_plain_map
    (D : Map) (hD : isOptimalConditional D) (f : BitString → BitString)
    (hf : Computable f) :
    ∃ c : ℕ, ∀ x : BitString, natK D (f x) ≤ natK D x + c := by
  obtain ⟨c, hc⟩ := plainK_map_le D hD f hf
  refine ⟨c, fun x => ?_⟩
  have h := hc x
  rw [← ENat.natCast_toNat (plainK_ne_top D hD (f x)),
    ← ENat.natCast_toNat (plainK_ne_top D hD x)] at h
  exact_mod_cast h

private theorem theorem2_clone_coordinates_cond_recode
    (D : Map) (hD : isOptimalConditional D)
    (f g : BitString → BitString) (hf : Computable f) (hg : Computable g) :
    ∃ c : ℕ, ∀ a b : BitString,
      natCondK D (f a) b ≤ natCondK D a (g b) + c := by
  obtain ⟨c₁, h₁⟩ := condK_map_le D hD f hf
  obtain ⟨c₂, h₂⟩ := condK_cond_map_le D hD g hg
  refine ⟨c₁ + c₂, fun a b => ?_⟩
  have h : condK D (f a) b ≤ condK D a (g b) + ((c₁ + c₂ : ℕ) : ℕ∞) := by
    calc
      condK D (f a) b ≤ condK D a b + (c₁ : ℕ∞) := h₁ a b
      _ ≤ (condK D a (g b) + (c₂ : ℕ∞)) + (c₁ : ℕ∞) :=
        add_le_add (h₂ a b) le_rfl
      _ = _ := by push_cast; ac_rfl
  rw [← ENat.natCast_toNat (condK_ne_top_of_optimal D hD (f a) b),
    ← ENat.natCast_toNat (condK_ne_top_of_optimal D hD a (g b))] at h
  exact_mod_cast h

private theorem theorem2_clone_coordinates_pair_cond_conversion
    (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ (a b x y : BitString),
      natCondK D (pairCode a b) (pairCode x y) ≤
        natCondK D (listCode [a, b]) (listCode [x, y]) + c ∧
      natCondK D (listCode [a, b]) (listCode [x, y]) ≤
        natCondK D (pairCode a b) (pairCode x y) + c := by
  let toList : BitString → BitString := fun w =>
    listCode [decodeFirst w, decodeSecond w]
  let toPair : BitString → BitString := fun w =>
    pairCode (decodeFirst w) (decodeFirst (decodeSecond w))
  have hList : Computable toList := by
    dsimp [toList]
    exact Computable₂.comp pairCode_computable decodeFirst_computable
      (Computable₂.comp pairCode_computable decodeSecond_computable (Computable.const []))
  have hPair : Computable toPair :=
    Computable₂.comp pairCode_computable decodeFirst_computable
      (decodeFirst_computable.comp decodeSecond_computable)
  obtain ⟨c₁, h₁⟩ :=
    theorem2_clone_coordinates_cond_recode
      D hD toPair toList hPair hList
  obtain ⟨c₂, h₂⟩ :=
    theorem2_clone_coordinates_cond_recode
      D hD toList toPair hList hPair
  refine ⟨c₁ + c₂, fun a b x y => ?_⟩
  have hForward : natCondK D (pairCode a b) (pairCode x y) ≤
      natCondK D (listCode [a, b]) (listCode [x, y]) + c₁ := by
    simpa [toPair, toList, listCode_cons, decodeFirst_pairCode, decodeSecond_pairCode] using
      h₁ (listCode [a, b]) (pairCode x y)
  have hBackward : natCondK D (listCode [a, b]) (listCode [x, y]) ≤
      natCondK D (pairCode a b) (pairCode x y) + c₂ := by
    simpa [toPair, toList, listCode_cons, decodeFirst_pairCode, decodeSecond_pairCode] using
      h₂ (pairCode a b) (listCode [x, y])
  constructor <;> omega

/-- Read the three relevant extended-profile coordinates of a clone in
`theorem2_total_profile`, translating tuple codes to the string and pair codes used by the theorem.
-/
private theorem theorem2_clone_coordinates
    (D : Map) (hD : isOptimalConditional D) (C : ℕ) :
    ∃ c : ℕ, ∀ (x₁ x₂ z v v' z' : BitString) (M : ℕ),
      (![v', z'] : Fin 2 → BitString) ∈
        strongTypization D (logSlack C M) ![v, z] ![x₁, x₂] →
      natK D z' ≤ natK D z + logSlack C M + c ∧
      natK D z ≤ natK D z' + logSlack C M + c ∧
      natK D (pairCode v' z') ≤ natK D (pairCode v z) + logSlack C M + c ∧
      natK D (pairCode v z) ≤ natK D (pairCode v' z') + logSlack C M + c ∧
      natCondK D (pairCode v' z') (pairCode x₁ x₂) ≤
        natCondK D (pairCode v z) (pairCode x₁ x₂) + logSlack C M + c ∧
      natCondK D (pairCode v z) (pairCode x₁ x₂) ≤
        natCondK D (pairCode v' z') (pairCode x₁ x₂) + logSlack C M + c := by
  let singleton : BitString → BitString := fun x => listCode [x]
  let toList : BitString → BitString := fun w =>
    listCode [decodeFirst w, decodeSecond w]
  let toPair : BitString → BitString := fun w =>
    pairCode (decodeFirst w) (decodeFirst (decodeSecond w))
  have hSingleton : Computable singleton := by
    dsimp [singleton]
    change Computable (fun w : BitString => pairCode w [])
    exact Computable₂.comp pairCode_computable Computable.id (Computable.const [])
  have hDecodeSingleton : Computable decodeFirst := decodeFirst_computable
  have hList : Computable toList := by
    dsimp [toList]
    exact Computable₂.comp pairCode_computable decodeFirst_computable
      (Computable₂.comp pairCode_computable decodeSecond_computable (Computable.const []))
  have hPair : Computable toPair :=
    Computable₂.comp pairCode_computable decodeFirst_computable
      (decodeFirst_computable.comp decodeSecond_computable)
  obtain ⟨cSingleton, hSingletonMap⟩ :=
    theorem2_clone_coordinates_plain_map
      D hD singleton hSingleton
  obtain ⟨cDecode, hDecodeMap⟩ :=
    theorem2_clone_coordinates_plain_map
      D hD decodeFirst hDecodeSingleton
  obtain ⟨cList, hListMap⟩ :=
    theorem2_clone_coordinates_plain_map
      D hD toList hList
  obtain ⟨cPair, hPairMap⟩ :=
    theorem2_clone_coordinates_plain_map
      D hD toPair hPair
  obtain ⟨cCond, hCondConversion⟩ :=
    theorem2_clone_coordinates_pair_cond_conversion
      D hD
  let c := cSingleton + cDecode + cList + cPair + 2 * cCond
  refine ⟨c, ?_⟩
  intro x₁ x₂ z v v' z' M hst
  let Vz : Finset (Fin 4) := {(1 : Fin 4)}
  let Vpair : Finset (Fin 4) := {(0 : Fin 4), (1 : Fin 4)}
  let Vcontext : Finset (Fin 4) := {(2 : Fin 4), (3 : Fin 4)}
  let base : Fin 4 → BitString := Fin.append ![v, z] ![x₁, x₂]
  let clone : Fin 4 → BitString := Fin.append ![v', z'] ![x₁, x₂]
  have hZBase : subtupleCode base Vz = listCode [z] := by
    simp [Vz, base, subtupleCode, Fin.append, Fin.addCases]
  have hZClone : subtupleCode clone Vz = listCode [z'] := by
    simp [Vz, clone, subtupleCode, Fin.append, Fin.addCases]
  have hPairBase : subtupleCode base Vpair = listCode [v, z] := by
    dsimp [Vpair, base]
    unfold subtupleCode
    rw [Finset.sort_insert (r := (· ≤ ·)) (by
      intro b hb
      simp only [Finset.mem_singleton] at hb
      subst b
      exact Fin.zero_le _) (by simp)]
    simp [Fin.append, Fin.addCases]
  have hPairClone : subtupleCode clone Vpair = listCode [v', z'] := by
    dsimp [Vpair, clone]
    unfold subtupleCode
    rw [Finset.sort_insert (r := (· ≤ ·)) (by
      intro b hb
      simp only [Finset.mem_singleton] at hb
      subst b
      exact Fin.zero_le _) (by simp)]
    simp [Fin.append, Fin.addCases]
  have hContextBase : subtupleCode base Vcontext = listCode [x₁, x₂] := by
    dsimp [Vcontext, base]
    unfold subtupleCode
    rw [Finset.sort_insert (r := (· ≤ ·)) (by
      intro b hb
      simp only [Finset.mem_singleton] at hb
      subst b
      exact (by decide : (2 : Fin 4) ≤ 3)) (by simp)]
    simp [Fin.append, Fin.addCases]
  have hContextClone : subtupleCode clone Vcontext = listCode [x₁, x₂] := by
    dsimp [Vcontext, clone]
    unfold subtupleCode
    rw [Finset.sort_insert (r := (· ≤ ·)) (by
      intro b hb
      simp only [Finset.mem_singleton] at hb
      subst b
      exact (by decide : (2 : Fin 4) ≤ 3)) (by simp)]
    simp [Fin.append, Fin.addCases]
  change ExtProfileLe D clone base ∧
    (∀ V W : Finset (Fin 4), V.Nonempty → Disjoint V W →
      subCondK D base V W ≤ subCondK D clone V W + logSlack C M) at hst
  have hVz : Vz.Nonempty := by simp [Vz]
  have hVpair : Vpair.Nonempty := by simp [Vpair]
  have hVcontext : Vpair.Nonempty := hVpair
  have hVcontextDisjoint : Disjoint Vpair Vcontext := by decide
  have hZForwardRaw := hst.1 Vz ∅ hVz (by simp)
  have hZBackwardRaw := hst.2 Vz ∅ hVz (by simp)
  have hPairForwardRaw := hst.1 Vpair ∅ hVpair (by simp)
  have hPairBackwardRaw := hst.2 Vpair ∅ hVpair (by simp)
  have hCondForwardRaw := hst.1 Vpair Vcontext hVcontext hVcontextDisjoint
  have hCondBackwardRaw := hst.2 Vpair Vcontext hVcontext hVcontextDisjoint
  have hZForward : natK D (listCode [z']) ≤ natK D (listCode [z]) + logSlack C M := by
    change natCondK D (subtupleCode clone Vz) (subtupleCode clone ∅) ≤
      natCondK D (subtupleCode base Vz) (subtupleCode base ∅) at hZForwardRaw
    rw [subtupleCode_empty, hZClone, subtupleCode_empty, hZBase] at hZForwardRaw
    have hRaw : natK D (listCode [z']) ≤ natK D (listCode [z]) := by
      simpa [subCondK, natK, natCondK, plainK] using hZForwardRaw
    exact hRaw.trans (Nat.le_add_right _ _)
  have hZBackward : natK D (listCode [z]) ≤ natK D (listCode [z']) + logSlack C M := by
    change natCondK D (subtupleCode base Vz) (subtupleCode base ∅) ≤
      natCondK D (subtupleCode clone Vz) (subtupleCode clone ∅) + logSlack C M at hZBackwardRaw
    rw [subtupleCode_empty, hZBase, subtupleCode_empty, hZClone] at hZBackwardRaw
    simpa [subCondK, natK, natCondK, plainK] using hZBackwardRaw
  have hPairForward : natK D (listCode [v', z']) ≤
      natK D (listCode [v, z]) + logSlack C M := by
    change natCondK D (subtupleCode clone Vpair) (subtupleCode clone ∅) ≤
      natCondK D (subtupleCode base Vpair) (subtupleCode base ∅) at hPairForwardRaw
    rw [subtupleCode_empty, hPairClone, subtupleCode_empty, hPairBase] at hPairForwardRaw
    have hRaw : natK D (listCode [v', z']) ≤ natK D (listCode [v, z]) := by
      simpa [subCondK, natK, natCondK, plainK] using hPairForwardRaw
    exact hRaw.trans (Nat.le_add_right _ _)
  have hPairBackward : natK D (listCode [v, z]) ≤
      natK D (listCode [v', z']) + logSlack C M := by
    change natCondK D (subtupleCode base Vpair) (subtupleCode base ∅) ≤
      (natCondK D (subtupleCode clone Vpair) (subtupleCode clone ∅) +
        logSlack C M) at hPairBackwardRaw
    rw [subtupleCode_empty, hPairBase, subtupleCode_empty, hPairClone] at hPairBackwardRaw
    simpa [subCondK, natK, natCondK, plainK] using hPairBackwardRaw
  have hCondForward : natCondK D (listCode [v', z']) (listCode [x₁, x₂]) ≤
      natCondK D (listCode [v, z]) (listCode [x₁, x₂]) + logSlack C M := by
    change natCondK D (subtupleCode clone Vpair) (subtupleCode clone Vcontext) ≤
      natCondK D (subtupleCode base Vpair) (subtupleCode base Vcontext) at hCondForwardRaw
    rw [hPairClone, hPairBase, hContextClone, hContextBase] at hCondForwardRaw
    exact hCondForwardRaw.trans (Nat.le_add_right _ _)
  have hCondBackward : natCondK D (listCode [v, z]) (listCode [x₁, x₂]) ≤
      natCondK D (listCode [v', z']) (listCode [x₁, x₂]) + logSlack C M := by
    change natCondK D (subtupleCode base Vpair) (subtupleCode base Vcontext) ≤
      (natCondK D (subtupleCode clone Vpair) (subtupleCode clone Vcontext) +
        logSlack C M) at hCondBackwardRaw
    rw [hPairBase, hPairClone, hContextBase, hContextClone] at hCondBackwardRaw
    exact hCondBackwardRaw
  have hDecodeZ' : natK D z' ≤ natK D (listCode [z']) + cDecode := by
    simpa [listCode_cons, decodeFirst_pairCode] using hDecodeMap (listCode [z'])
  have hDecodeZ : natK D z ≤ natK D (listCode [z]) + cDecode := by
    simpa [listCode_cons, decodeFirst_pairCode] using hDecodeMap (listCode [z])
  have hEncodeZ : natK D (listCode [z]) ≤ natK D z + cSingleton := by
    simpa [singleton] using hSingletonMap z
  have hEncodeZ' : natK D (listCode [z']) ≤ natK D z' + cSingleton := by
    simpa [singleton] using hSingletonMap z'
  have hDecodePair' : natK D (pairCode v' z') ≤
      natK D (listCode [v', z']) + cPair := by
    simpa [toPair, listCode_cons, decodeFirst_pairCode, decodeSecond_pairCode] using
      hPairMap (listCode [v', z'])
  have hDecodePair : natK D (pairCode v z) ≤ natK D (listCode [v, z]) + cPair := by
    simpa [toPair, listCode_cons, decodeFirst_pairCode, decodeSecond_pairCode] using
      hPairMap (listCode [v, z])
  have hEncodePair : natK D (listCode [v, z]) ≤ natK D (pairCode v z) + cList := by
    simpa [toList, listCode_cons, decodeFirst_pairCode, decodeSecond_pairCode] using
      hListMap (pairCode v z)
  have hEncodePair' : natK D (listCode [v', z']) ≤
      natK D (pairCode v' z') + cList := by
    simpa [toList, listCode_cons, decodeFirst_pairCode, decodeSecond_pairCode] using
      hListMap (pairCode v' z')
  obtain ⟨hCondEncode, hCondDecode⟩ := hCondConversion v z x₁ x₂
  obtain ⟨hCondEncode', hCondDecode'⟩ := hCondConversion v' z' x₁ x₂
  have hZFinal₁ : natK D z' ≤ natK D z + logSlack C M + cSingleton + cDecode := by
    omega
  have hZFinal₂ : natK D z ≤ natK D z' + logSlack C M + cSingleton + cDecode := by
    omega
  have hPairFinal₁ : natK D (pairCode v' z') ≤
      natK D (pairCode v z) + logSlack C M + cList + cPair := by
    omega
  have hPairFinal₂ : natK D (pairCode v z) ≤
      natK D (pairCode v' z') + logSlack C M + cList + cPair := by
    omega
  have hCondFinal₁ : natCondK D (pairCode v' z') (pairCode x₁ x₂) ≤
      natCondK D (pairCode v z) (pairCode x₁ x₂) + logSlack C M + 2 * cCond := by
    omega
  have hCondFinal₂ : natCondK D (pairCode v z) (pairCode x₁ x₂) ≤
      natCondK D (pairCode v' z') (pairCode x₁ x₂) + logSlack C M + 2 * cCond := by
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> dsimp [c] <;> omega

/-- The chain rule bounds the total profile in `theorem2_total_profile`:
`K(v,z) = K(z) + K(v | z) ± O(log M)`, with `K(v | z) = q ± O(log M)` and all chain-rule
budgets controlled by `M`. -/
private theorem theorem2_base_chain_rule
    (D : Map) (hD : isOptimalConditional D) (c₀ : ℕ) :
    ∃ c : ℕ, ∀ (x₁ x₂ z v : BitString) (q t M : ℕ),
      M = natK D (pairCode (pairCode x₁ x₂) z) →
      q ≤ natCondK D v z + logSlack c₀ M →
      natCondK D v z ≤ q + logSlack c₀ M →
      natCondK D v (pairCode x₁ z) ≤ t + logSlack c₀ M →
      t ≤ M →
      natK D (pairCode v z) ≤ natK D z + q + logSlack c M ∧
      natK D z + q ≤ natK D (pairCode v z) + logSlack c M := by
  obtain ⟨cProjZ, hProjZ⟩ := plainK_map_le D hD decodeSecond decodeSecond_computable
  let fA : BitString → BitString := fun p =>
    pairCode (decodeFirst (decodeFirst p)) (decodeSecond p)
  have hfA : Computable fA := by
    simpa [fA] using
      (show Computable₂ (fun a b : BitString => pairCode a b) from pairCode_computable).comp
        (decodeFirst_computable.comp decodeFirst_computable) decodeSecond_computable
  obtain ⟨cProjA, hProjA⟩ := plainK_map_le D hD fA hfA
  obtain ⟨cChain, hChain⟩ := Kolmogorov.condK_chain_upper_values D hD
  obtain ⟨cCondPlain, hCondPlain⟩ := condK_le_plainK D hD
  obtain ⟨cPair, hPair⟩ := plainK_pair_le_add_two_log_add_condK D hD
  obtain ⟨cSym, hSym⟩ := pairPlainK_symmetryOfInformation_values D hD
  obtain ⟨cSwap, hSwap⟩ := plainK_map_le D hD swapPairCode swapPairCode_computable
  obtain ⟨b₀, hb₀⟩ := logSlack_le_add_const c₀
  let cA := cProjA + cCondPlain
  obtain ⟨cChainFold, hChainFold⟩ :=
    logSlack_linear_bound cChain 3 (cA + b₀ + 1)
  obtain ⟨bChain, hbChain⟩ := logSlack_le_add_const cChainFold
  let bV := cA + b₀ + bChain
  let bZ := cProjZ
  let bPair := 3 * bZ + bV + cPair
  obtain ⟨cSymFold, hSymFold⟩ := logSlack_linear_bound cSym 7 (bPair + 1)
  let c := cSymFold + c₀ + cSwap
  refine ⟨c, ?_⟩
  intro x₁ x₂ z v q t M hM hq₁ hq₂ hv ht
  let p := pairCode (pairCode x₁ x₂) z
  let a := pairCode x₁ z
  let kz := natK D z
  let ka := natK D a
  let kza := natCondK D a z
  let kva := natCondK D v a
  let kvz := natCondK D v z
  let kp := natK D (pairCode z v)
  let kpv := natK D (pairCode v z)
  have hqLo : q ≤ kvz + logSlack c₀ M := by simpa [kvz] using hq₁
  have hqHi : kvz ≤ q + logSlack c₀ M := by simpa [kvz] using hq₂
  have hMapZ : kz ≤ M + cProjZ := by
    have h := hProjZ p
    have hNat : natK D (decodeSecond p) ≤ natK D p + cProjZ := by
      rw [← ENat.natCast_toNat (plainK_ne_top D hD (decodeSecond p)),
        ← ENat.natCast_toNat (plainK_ne_top D hD p)] at h
      exact_mod_cast h
    rw [hM]
    simpa [kz, p, decodeSecond_pairCode] using hNat
  have hMapA : ka ≤ M + cProjA := by
    have h := hProjA p
    have hNat : natK D (fA p) ≤ natK D p + cProjA := by
      rw [← ENat.natCast_toNat (plainK_ne_top D hD (fA p)),
        ← ENat.natCast_toNat (plainK_ne_top D hD p)] at h
      exact_mod_cast h
    rw [show fA p = a by simp [fA, a, p, decodeFirst_pairCode, decodeSecond_pairCode]] at hNat
    rw [hM]
    simpa [ka, a, p] using hNat
  have hCondA : kza ≤ ka + cCondPlain := by
    have h := hCondPlain a z
    rw [← ENat.natCast_toNat (condK_ne_top_of_optimal D hD a z),
      ← ENat.natCast_toNat (plainK_ne_top D hD a)] at h
    exact_mod_cast h
  have hCondABound : kza ≤ M + cA := by
    dsimp [cA]
    omega
  have hVA : kva ≤ t + logSlack c₀ M := by simpa [kva, a] using hv
  have hZValue : HasPlainConditionalComplexityValue D a z kza := by
    exact condK_le_add_condMutualInfo_value D hD a z
  have hVAValue : HasPlainConditionalComplexityValue D v a kva := by
    exact condK_le_add_condMutualInfo_value D hD v a
  have hVZValue : HasPlainConditionalComplexityValue D v z kvz := by
    exact condK_le_add_condMutualInfo_value D hD v z
  have hChainRaw := hChain z v a kza kva kvz hZValue hVAValue hVZValue
  have hChainNat : kvz ≤ kza + kva + logSlack cChain (kza + kva + 1) := by
    simpa [kza, kva, kvz] using hChainRaw
  have hChainArg : kza + kva + 1 ≤ 3 * M + (cA + b₀ + 1) := by
    have hRight : kva ≤ 2 * M + b₀ := by
      have hLog0 := hb₀ M
      calc
        kva ≤ t + logSlack c₀ M := hVA
        _ ≤ 2 * M + b₀ := by omega
    omega
  have hChainSlack : logSlack cChain (kza + kva + 1) ≤ logSlack cChainFold M := by
    calc
      logSlack cChain (kza + kva + 1) ≤ logSlack cChain (3 * M + (cA + b₀ + 1)) :=
        logSlack_mono_right cChain hChainArg
      _ ≤ logSlack cChainFold M := hChainFold M
  have hKVZBound : kvz ≤ 4 * M + bV := by
    have hRight : kva ≤ 2 * M + b₀ := by
      have hLog0 := hb₀ M
      calc
        kva ≤ t + logSlack c₀ M := hVA
        _ ≤ 2 * M + b₀ := by omega
    calc
      kvz ≤ kza + kva + logSlack cChainFold M := by
        exact hChainNat.trans (Nat.add_le_add_left hChainSlack (kza + kva))
      _ ≤ (M + cA) + (2 * M + b₀) + logSlack cChainFold M := by omega
      _ ≤ 4 * M + bV := by
        have hLogChain := hbChain M
        dsimp [bV, cA]
        omega
  have hKzValue : HasPlainComplexityValue D z kz := by
    exact commonInfo_le_mutualInfo_hasPlainValue D hD z
  have hPairValue : HasPlainComplexityValue D (pairCode z v) kp := by
    exact commonInfo_le_mutualInfo_hasPlainValue D hD (pairCode z v)
  have hKzCast : plainK D z = (kz : ℕ∞) := by
    exact hKzValue
  have hVZCast : condK D v z = (kvz : ℕ∞) := by
    exact hVZValue
  have hPairCast : Kolmogorov.cPair D z v = (kp : ℕ∞) := by
    change plainK D (pairCode z v) = (kp : ℕ∞)
    exact hPairValue
  have hPairUpperCast : (kp : ℕ∞) ≤
      (kz : ℕ∞) + (kvz : ℕ∞) +
        ((2 * Nat.log 2 kz + cPair : ℕ) : ℕ∞) := by
    have h := hPair z v
    rw [hPairCast, hKzCast, hVZCast] at h
    simpa [Kolmogorov.cVal, kz, hKzCast] using h
  have hPairUpper : kp ≤ kz + kvz + (2 * Nat.log 2 kz + cPair) := by
    exact_mod_cast hPairUpperCast
  have hPairBound : kp ≤ 7 * M + bPair := by
    have hLogKz : Nat.log 2 kz ≤ kz := Nat.log_le_self 2 kz
    dsimp [bPair, bZ, bV, cA]
    omega
  have hPairValueZV : HasPlainComplexityValue D (pairCode z v) kp := by
    exact commonInfo_le_mutualInfo_hasPlainValue D hD (pairCode z v)
  have hSymRaw := hSym z v kz kvz kp hKzValue hVZValue hPairValueZV
  have hSymSlack : logSlack cSym (kp + 1) ≤ logSlack cSymFold M := by
    calc
      logSlack cSym (kp + 1) ≤ logSlack cSym (7 * M + (bPair + 1)) :=
        logSlack_mono_right cSym (by omega)
      _ ≤ logSlack cSymFold M := hSymFold M
  have hSwapForward : kpv ≤ kp + cSwap := by
    have h := hSwap (pairCode z v)
    have h' : plainK D (pairCode v z) ≤ plainK D (pairCode z v) + cSwap := by
      simpa only [swapPairCode_pairCode] using h
    rw [← ENat.natCast_toNat (plainK_ne_top D hD (pairCode v z)),
      ← ENat.natCast_toNat (plainK_ne_top D hD (pairCode z v))] at h'
    simpa [kpv, kp] using (show natK D (pairCode v z) ≤ natK D (pairCode z v) + cSwap by
      exact_mod_cast h')
  have hSwapBackward : kp ≤ kpv + cSwap := by
    have h := hSwap (pairCode v z)
    have h' : plainK D (pairCode z v) ≤ plainK D (pairCode v z) + cSwap := by
      simpa only [swapPairCode_pairCode] using h
    rw [← ENat.natCast_toNat (plainK_ne_top D hD (pairCode z v)),
      ← ENat.natCast_toNat (plainK_ne_top D hD (pairCode v z))] at h'
    simpa [kpv, kp] using (show natK D (pairCode z v) ≤ natK D (pairCode v z) + cSwap by
      exact_mod_cast h')
  have hSlackTotal : logSlack cSymFold M + logSlack c₀ M + cSwap ≤
      logSlack (cSymFold + c₀ + cSwap) M := by
    calc
      logSlack cSymFold M + logSlack c₀ M + cSwap =
          logSlack (cSymFold + c₀) M + cSwap := by rw [logSlack_add_const]
      _ ≤ logSlack (cSymFold + c₀ + cSwap) M :=
        logSlack_add_nat_le (cSymFold + c₀) cSwap M
  have hSymUpper : kp ≤ kz + kvz + logSlack cSymFold M := by
    have h := hSymRaw.1
    omega
  have hSymLower : kz + kvz ≤ kp + logSlack cSymFold M := by
    have h := hSymRaw.2
    omega
  constructor
  · calc
      kpv ≤ kp + cSwap := hSwapForward
      _ ≤ kz + kvz + logSlack cSymFold M + cSwap := Nat.add_le_add_right hSymUpper cSwap
      _ ≤ kz + q + logSlack (cSymFold + c₀ + cSwap) M := by
        have h := hqHi
        omega
  · calc
      kz + q ≤ kz + kvz + logSlack c₀ M := by omega
      _ ≤ kp + logSlack cSymFold M + logSlack c₀ M := by
        omega
      _ ≤ kpv + logSlack (cSymFold + c₀ + cSwap) M := by
        have h := hSwapBackward
        omega

/-- Total-complexity coordinates of a clone used by `theorem2_typize`:
total-complexity coordinates of a clone.  Fix the strong-typization constant `C` first.  If
`(v', z')` lies in `ST_{logSlack C M}(v, z | x̄)`, then the coordinates `K(z')`, `K(v', z')` and
`K(v', z' | x̄)` of the extended profile are within `logSlack C M + O(1)` of those of `(v, z)` (the
extended profile coordinates `V = {1}`, `V = {0,1}` with `W = ∅`, and `V = {0,1}`, `W = {2,3}`),
and `K(v, z) = K(z) + K(v | z) ± O(log M) = K(z) + q ± O(log M)` (chain rule, `K(v | z) = q ± L₀`
and `K(v | z) ≤ K(v | x₁, z) + K(x₁ | z) + O(log M) ≤ 2M + O(log M)`). -/
private theorem theorem2_total_profile
    (D : Map) (hD : isOptimalConditional D) (c₀ C : ℕ) :
    ∃ c : ℕ, ∀ (x₁ x₂ z v v' z' : BitString) (q t M : ℕ),
      M = natK D (pairCode (pairCode x₁ x₂) z) →
      q ≤ natCondK D v z + logSlack c₀ M →
      natCondK D v z ≤ q + logSlack c₀ M →
      natCondK D v (pairCode x₁ z) ≤ t + logSlack c₀ M →
      t ≤ M →
      (![v', z'] : Fin 2 → BitString) ∈
        strongTypization D (logSlack C M) ![v, z] ![x₁, x₂] →
      natK D z' ≤ natK D z + logSlack c M ∧
      natK D z ≤ natK D z' + logSlack c M ∧
      natK D (pairCode v' z') ≤ natK D z + q + logSlack c M ∧
      natK D z + q ≤ natK D (pairCode v' z') + logSlack c M ∧
      natCondK D (pairCode v' z') (pairCode x₁ x₂) ≤
        natCondK D (pairCode v z) (pairCode x₁ x₂) + logSlack c M ∧
      natCondK D (pairCode v z) (pairCode x₁ x₂) ≤
        natCondK D (pairCode v' z') (pairCode x₁ x₂) + logSlack c M := by
  obtain ⟨cProfile, hProfile⟩ :=
    theorem2_clone_coordinates
      D hD C
  obtain ⟨cChain, hChain⟩ :=
    theorem2_base_chain_rule
      D hD c₀
  let c := C + cProfile + cChain
  refine ⟨c, ?_⟩
  intro x₁ x₂ z v v' z' q t M hM hq₁ hq₂ hv ht hst
  obtain ⟨hZ₁, hZ₂, hPair₁, hPair₂, hCond₁, hCond₂⟩ :=
    hProfile x₁ x₂ z v v' z' M hst
  obtain ⟨hBase₁, hBase₂⟩ := hChain x₁ x₂ z v q t M hM hq₁ hq₂ hv ht
  have hProfileSlack : logSlack C M + cProfile ≤ logSlack (C + cProfile + cChain) M := by
    calc
      logSlack C M + cProfile ≤ logSlack (C + cProfile) M := by
        have hconst : cProfile ≤ logSlack cProfile M := by
          unfold logSlack
          omega
        calc
          logSlack C M + cProfile ≤ logSlack C M + logSlack cProfile M :=
            Nat.add_le_add_left hconst _
          _ = logSlack (C + cProfile) M := logSlack_add_const C cProfile M
      _ ≤ logSlack (C + cProfile + cChain) M :=
        logSlack_mono_left (by omega) M
  have hCombinedSlack : logSlack C M + cProfile + logSlack cChain M ≤
      logSlack (C + cProfile + cChain) M := by
    calc
      logSlack C M + cProfile + logSlack cChain M ≤
          logSlack (C + cProfile) M + logSlack cChain M :=
        Nat.add_le_add_right (by
          have hconst : cProfile ≤ logSlack cProfile M := by
            unfold logSlack
            omega
          calc
            logSlack C M + cProfile ≤ logSlack C M + logSlack cProfile M :=
              Nat.add_le_add_left hconst _
            _ = logSlack (C + cProfile) M := logSlack_add_const C cProfile M) _
      _ = logSlack (C + cProfile + cChain) M :=
        logSlack_add_const (C + cProfile) cChain M
  dsimp [c]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- Computable changes to the output and condition cost a uniform additive constant in
plain conditional complexity. -/
private theorem theorem2_conditional_profile_aux_recode
    (D : Map) (hD : isOptimalConditional D)
    (f g : BitString → BitString) (hf : Computable f) (hg : Computable g) :
    ∃ c : ℕ, ∀ a b : BitString,
      natCondK D (f a) b ≤ natCondK D a (g b) + c := by
  obtain ⟨c₁, h₁⟩ := condK_map_le D hD f hf
  obtain ⟨c₂, h₂⟩ := condK_cond_map_le D hD g hg
  refine ⟨c₁ + c₂, fun a b => ?_⟩
  have h : condK D (f a) b ≤ condK D a (g b) + ((c₁ + c₂ : ℕ) : ℕ∞) := by
    calc
      condK D (f a) b ≤ condK D a b + (c₁ : ℕ∞) := h₁ a b
      _ ≤ (condK D a (g b) + (c₂ : ℕ∞)) + (c₁ : ℕ∞) :=
        add_le_add (h₂ a b) le_rfl
      _ = _ := by push_cast; ac_rfl
  rw [← ENat.natCast_toNat (condK_ne_top_of_optimal D hD (f a) b),
    ← ENat.natCast_toNat (condK_ne_top_of_optimal D hD a (g b))] at h
  exact_mod_cast h

/-- Coding the output and condition as singleton lists changes complexity by a constant. -/
private theorem theorem2_conditional_profile_aux_singletons
    (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ a b : BitString,
      natCondK D a b ≤ natCondK D (listCode [a]) (listCode [b]) + c ∧
      natCondK D (listCode [a]) (listCode [b]) ≤ natCondK D a b + c := by
  let s : BitString → BitString := fun w => listCode [w]
  have hs : Computable s := by
    change Computable (fun w : BitString => pairCode w [])
    exact Computable₂.comp pairCode_computable Computable.id (Computable.const [])
  obtain ⟨c₁, h₁⟩ :=
    theorem2_conditional_profile_aux_recode
      D hD decodeFirst s decodeFirst_computable hs
  obtain ⟨c₂, h₂⟩ :=
    theorem2_conditional_profile_aux_recode
      D hD s decodeFirst hs decodeFirst_computable
  refine ⟨c₁ + c₂, fun a b => ?_⟩
  have hforward : natCondK D a b ≤ natCondK D (listCode [a]) (listCode [b]) + c₁ := by
    simpa [s, listCode_cons, decodeFirst_pairCode] using h₁ (listCode [a]) b
  have hbackward : natCondK D (listCode [a]) (listCode [b]) ≤ natCondK D a b + c₂ := by
    simpa [s, listCode_cons, decodeFirst_pairCode] using h₂ a (listCode [b])
  constructor <;> omega

/-- Convert a pair condition to the reversed two-entry subtuple and a singleton output. -/
private theorem theorem2_conditional_profile_aux_pair_condition
    (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ a x z : BitString,
      natCondK D a (pairCode x z) ≤
        natCondK D (listCode [a]) (listCode [z, x]) + c ∧
      natCondK D (listCode [a]) (listCode [z, x]) ≤
        natCondK D a (pairCode x z) + c := by
  let s : BitString → BitString := fun w => listCode [w]
  let toList : BitString → BitString := fun w =>
    listCode [decodeSecond w, decodeFirst w]
  let toPair : BitString → BitString := fun w =>
    pairCode (decodeFirst (decodeSecond w)) (decodeFirst w)
  have hs : Computable s := by
    change Computable (fun w : BitString => pairCode w [])
    exact Computable₂.comp pairCode_computable Computable.id (Computable.const [])
  have hList : Computable toList := by
    change Computable (fun w : BitString =>
      pairCode (decodeSecond w) (pairCode (decodeFirst w) []))
    exact Computable₂.comp pairCode_computable decodeSecond_computable
      (Computable₂.comp pairCode_computable decodeFirst_computable (Computable.const []))
  have hPair : Computable toPair :=
    Computable₂.comp pairCode_computable
      (decodeFirst_computable.comp decodeSecond_computable) decodeFirst_computable
  obtain ⟨c₁, h₁⟩ :=
    theorem2_conditional_profile_aux_recode
      D hD decodeFirst toList decodeFirst_computable hList
  obtain ⟨c₂, h₂⟩ :=
    theorem2_conditional_profile_aux_recode
      D hD s toPair hs hPair
  refine ⟨c₁ + c₂, fun a x z => ?_⟩
  have hforward : natCondK D a (pairCode x z) ≤
      natCondK D (listCode [a]) (listCode [z, x]) + c₁ := by
    simpa [toList, listCode_cons, decodeFirst_pairCode, decodeSecond_pairCode] using
      h₁ (listCode [a]) (pairCode x z)
  have hbackward : natCondK D (listCode [a]) (listCode [z, x]) ≤
      natCondK D a (pairCode x z) + c₂ := by
    simpa [s, toPair, listCode_cons, decodeFirst_pairCode, decodeSecond_pairCode] using
      h₂ a (listCode [z, x])
  constructor <;> omega

/-- Convert a pair output and singleton condition to their subtuple list codes. -/
private theorem theorem2_conditional_profile_aux_pair_output
    (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ x₁ x₂ z : BitString,
      natCondK D (pairCode x₁ x₂) z ≤
        natCondK D (listCode [x₁, x₂]) (listCode [z]) + c ∧
      natCondK D (listCode [x₁, x₂]) (listCode [z]) ≤
        natCondK D (pairCode x₁ x₂) z + c := by
  let s : BitString → BitString := fun w => listCode [w]
  let toList : BitString → BitString := fun w =>
    listCode [decodeFirst w, decodeSecond w]
  let toPair : BitString → BitString := fun w =>
    pairCode (decodeFirst w) (decodeFirst (decodeSecond w))
  have hs : Computable s := by
    change Computable (fun w : BitString => pairCode w [])
    exact Computable₂.comp pairCode_computable Computable.id (Computable.const [])
  have hList : Computable toList := by
    change Computable (fun w : BitString =>
      pairCode (decodeFirst w) (pairCode (decodeSecond w) []))
    exact Computable₂.comp pairCode_computable decodeFirst_computable
      (Computable₂.comp pairCode_computable decodeSecond_computable (Computable.const []))
  have hPair : Computable toPair :=
    Computable₂.comp pairCode_computable decodeFirst_computable
      (decodeFirst_computable.comp decodeSecond_computable)
  obtain ⟨c₁, h₁⟩ :=
    theorem2_conditional_profile_aux_recode
      D hD toPair s hPair hs
  obtain ⟨c₂, h₂⟩ :=
    theorem2_conditional_profile_aux_recode
      D hD toList decodeFirst hList decodeFirst_computable
  refine ⟨c₁ + c₂, fun x₁ x₂ z => ?_⟩
  have hforward : natCondK D (pairCode x₁ x₂) z ≤
      natCondK D (listCode [x₁, x₂]) (listCode [z]) + c₁ := by
    simpa [toPair, s, listCode_cons, decodeFirst_pairCode, decodeSecond_pairCode] using
      h₁ (listCode [x₁, x₂]) z
  have hbackward : natCondK D (listCode [x₁, x₂]) (listCode [z]) ≤
      natCondK D (pairCode x₁ x₂) z + c₂ := by
    simpa [toList, listCode_cons, decodeFirst_pairCode, decodeSecond_pairCode] using
      h₂ (pairCode x₁ x₂) (listCode [z])
  constructor <;> omega

/-- Conditional coordinates of a clone used by `theorem2_typize`:
conditional coordinates of a clone.  Fix the strong-typization constant `C` first.  If
`(v', z')` lies in `ST_{logSlack C M}(v, z | x̄)`, the profile coordinates
`K(v' | z')`, `K(v' | x_i, z')` and `K(x̄ | z')` are within `logSlack C M + O(1)` of those of
`(v, z, x₁, x₂)` (the permutations of the tuple entries cost `O(1)`); hence
`q ≤ K(v' | z') + O(log M)`, `K(v' | x_i, z') ≤ t + O(log M)` and
`K(x̄) ≤ K(x̄ | z') + t + O(log M)`. -/
private theorem theorem2_conditional_profile
    (D : Map) (hD : isOptimalConditional D) (c₀ C : ℕ) :
    ∃ c : ℕ, ∀ (x₁ x₂ z v v' z' : BitString) (q t M : ℕ),
      M = natK D (pairCode (pairCode x₁ x₂) z) →
      MutualInfoLe D (pairCode x₁ x₂) z t →
      q ≤ natCondK D v z + logSlack c₀ M →
      natCondK D v (pairCode x₁ z) ≤ t + logSlack c₀ M →
      natCondK D v (pairCode x₂ z) ≤ t + logSlack c₀ M →
      t ≤ M →
      (![v', z'] : Fin 2 → BitString) ∈
        strongTypization D (logSlack C M) ![v, z] ![x₁, x₂] →
      q ≤ natCondK D v' z' + logSlack c M ∧
      natCondK D v' (pairCode x₁ z') ≤ t + logSlack c M ∧
      natCondK D v' (pairCode x₂ z') ≤ t + logSlack c M ∧
      MutualInfoLe D (pairCode x₁ x₂) z' (t + logSlack c M) := by
  obtain ⟨cS, hS⟩ :=
    theorem2_conditional_profile_aux_singletons D hD
  obtain ⟨cCtx, hCtx⟩ :=
    theorem2_conditional_profile_aux_pair_condition D hD
  obtain ⟨cPair, hPair⟩ :=
    theorem2_conditional_profile_aux_pair_output D hD
  let d := 2 * (cS + cCtx + cPair)
  refine ⟨c₀ + C + d, ?_⟩
  intro x₁ x₂ z v v' z' q t M hM hMI hq hv₁ hv₂ ht hst
  have hCodePair (w : Fin 4 → BitString) (i j : Fin 4) (hij : i < j) :
      subtupleCode w {i, j} = listCode [w i, w j] := by
    unfold subtupleCode
    rw [Finset.sort_insert (r := (· ≤ ·)) (by simpa using le_of_lt hij)
      (by simpa using ne_of_lt hij)]
    simp
  have hCode₀ (a b c d : BitString) :
      subtupleCode (Fin.append ![a, b] ![c, d]) ({0} : Finset (Fin 4)) =
        listCode [a] := by
    simp [subtupleCode, Fin.append, Fin.addCases]
  have hCode₁ (a b c d : BitString) :
      subtupleCode (Fin.append ![a, b] ![c, d]) ({1} : Finset (Fin 4)) =
        listCode [b] := by
    simp [subtupleCode, Fin.append, Fin.addCases]
  have hCode₁₂ (a b c d : BitString) :
      subtupleCode (Fin.append ![a, b] ![c, d]) ({1, 2} : Finset (Fin 4)) =
        listCode [b, c] := by
    rw [hCodePair _ 1 2 (by decide)]
    simp [Fin.append, Fin.addCases]
  have hCode₁₃ (a b c d : BitString) :
      subtupleCode (Fin.append ![a, b] ![c, d]) ({1, 3} : Finset (Fin 4)) =
        listCode [b, d] := by
    rw [hCodePair _ 1 3 (by decide)]
    simp [Fin.append, Fin.addCases]
  have hCode₂₃ (a b c d : BitString) :
      subtupleCode (Fin.append ![a, b] ![c, d]) ({2, 3} : Finset (Fin 4)) =
        listCode [c, d] := by
    rw [hCodePair _ 2 3 (by decide)]
    simp [Fin.append, Fin.addCases]
  have hV : natCondK D (listCode [v]) (listCode [z]) ≤
      natCondK D (listCode [v']) (listCode [z']) + logSlack C M := by
    simpa only [subCondK, hCode₀, hCode₁] using
      hst.2 ({0} : Finset (Fin 4)) {1} (by simp) (by decide)
  have hX₁ : natCondK D (listCode [v']) (listCode [z', x₁]) ≤
      natCondK D (listCode [v]) (listCode [z, x₁]) := by
    simpa only [subCondK, hCode₀, hCode₁₂] using
      hst.1 ({0} : Finset (Fin 4)) {1, 2} (by simp) (by decide)
  have hX₂ : natCondK D (listCode [v']) (listCode [z', x₂]) ≤
      natCondK D (listCode [v]) (listCode [z, x₂]) := by
    simpa only [subCondK, hCode₀, hCode₁₃] using
      hst.1 ({0} : Finset (Fin 4)) {1, 3} (by simp) (by decide)
  have hXZ : natCondK D (listCode [x₁, x₂]) (listCode [z]) ≤
      natCondK D (listCode [x₁, x₂]) (listCode [z']) + logSlack C M := by
    simpa only [subCondK, hCode₂₃, hCode₁] using
      hst.2 ({2, 3} : Finset (Fin 4)) {1} (by simp) (by decide)
  have hSlack : logSlack c₀ M + logSlack C M + d ≤ logSlack (c₀ + C + d) M := by
    rw [← logSlack_add_constants c₀ C M]
    exact logSlack_add_nat_le (c₀ + C) d M
  have hSV := hS v z
  have hSV' := hS v' z'
  have hCtx₁ := hCtx v x₁ z
  have hCtx₁' := hCtx v' x₁ z'
  have hCtx₂ := hCtx v x₂ z
  have hCtx₂' := hCtx v' x₂ z'
  have hPairZ := hPair x₁ x₂ z
  have hPairZ' := hPair x₁ x₂ z'
  change natK D (pairCode x₁ x₂) ≤ natCondK D (pairCode x₁ x₂) z + t at hMI
  change _ ∧ _ ∧ _ ∧
    natK D (pairCode x₁ x₂) ≤ natCondK D (pairCode x₁ x₂) z' + (t + _)
  have hd : d = 2 * cS + 2 * cCtx + 2 * cPair := by dsimp [d]; omega
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-- The typization profile transfers each conditional description from `(v,z)` to `(v',z')`
in `theorem2_common_description`.
with logarithmic overhead. -/
private theorem theorem2_profile_transfer
    (D : Map) (hD : isOptimalConditional D) (C : ℕ) :
    ∃ c : ℕ, ∀ (x₁ x₂ z v v' z' : BitString) (M : ℕ),
      M = natK D (pairCode (pairCode x₁ x₂) z) →
      (![v', z'] : Fin 2 → BitString) ∈
        strongTypization D (logSlack C M) ![v, z] ![x₁, x₂] →
      natCondK D x₁ (pairCode v' z') ≤
          natCondK D x₁ (pairCode v z) + logSlack c M ∧
        natCondK D x₂ (pairCode v' z') ≤
          natCondK D x₂ (pairCode v z) + logSlack c M := by
  let singleton : BitString → BitString := fun w => listCode [w]
  let pairToList : BitString → BitString := fun w =>
    listCode [decodeFirst w, decodeSecond w]
  let listToPair : BitString → BitString := fun w =>
    pairCode (decodeFirst w) (decodeFirst (decodeSecond w))
  have hSingleton : Computable singleton := by
    change Computable (fun w : BitString => pairCode w [])
    exact Computable₂.comp pairCode_computable Computable.id (Computable.const [])
  have hPairToList : Computable pairToList := by
    change Computable (fun w : BitString =>
      pairCode (decodeFirst w) (pairCode (decodeSecond w) []))
    exact Computable₂.comp pairCode_computable decodeFirst_computable
      (Computable₂.comp pairCode_computable decodeSecond_computable (Computable.const []))
  have hListToPair : Computable listToPair :=
    Computable₂.comp pairCode_computable decodeFirst_computable
      (decodeFirst_computable.comp decodeSecond_computable)
  obtain ⟨cOut, hOut⟩ :=
    theorem2_conditional_profile_aux_recode
      D hD decodeFirst pairToList decodeFirst_computable hPairToList
  obtain ⟨cIn, hIn⟩ :=
    theorem2_conditional_profile_aux_recode
      D hD singleton listToPair hSingleton hListToPair
  let c := cOut + cIn
  refine ⟨c, ?_⟩
  intro x₁ x₂ z v v' z' M hM hst
  have hCodePair (w : Fin 4 → BitString) (i j : Fin 4) (hij : i < j) :
      subtupleCode w {i, j} = listCode [w i, w j] := by
    unfold subtupleCode
    rw [Finset.sort_insert (r := (· ≤ ·)) (by simpa using le_of_lt hij)
      (by simpa using ne_of_lt hij)]
    simp
  have hCodeSingleton (a b c d : BitString) :
      subtupleCode (Fin.append ![a, b] ![c, d]) ({2} : Finset (Fin 4)) =
        listCode [c] := by
    simp [subtupleCode, Fin.append, Fin.addCases]
  have hCodeSingleton' (a b c d : BitString) :
      subtupleCode (Fin.append ![a, b] ![c, d]) ({3} : Finset (Fin 4)) =
        listCode [d] := by
    simp [subtupleCode, Fin.append, Fin.addCases]
  have hCodeContext (a b c d : BitString) :
      subtupleCode (Fin.append ![a, b] ![c, d]) ({0, 1} : Finset (Fin 4)) =
        listCode [a, b] := by
    rw [hCodePair _ 0 1 (by decide)]
    simp [Fin.append, Fin.addCases]
  have hProf₁ : natCondK D (listCode [x₁]) (listCode [v', z']) ≤
      natCondK D (listCode [x₁]) (listCode [v, z]) := by
    simpa only [subCondK, hCodeSingleton, hCodeContext] using
      hst.1 ({2} : Finset (Fin 4)) {0, 1} (by simp) (by decide)
  have hProf₂ : natCondK D (listCode [x₂]) (listCode [v', z']) ≤
      natCondK D (listCode [x₂]) (listCode [v, z]) := by
    simpa only [subCondK, hCodeSingleton', hCodeContext] using
      hst.1 ({3} : Finset (Fin 4)) {0, 1} (by simp) (by decide)
  have hOut₁ : natCondK D x₁ (pairCode v' z') ≤
      natCondK D (listCode [x₁]) (listCode [v', z']) + cOut := by
    simpa [pairToList, listCode_cons, decodeFirst_pairCode, decodeSecond_pairCode] using
      hOut (listCode [x₁]) (pairCode v' z')
  have hOut₂ : natCondK D x₂ (pairCode v' z') ≤
      natCondK D (listCode [x₂]) (listCode [v', z']) + cOut := by
    simpa [pairToList, listCode_cons, decodeFirst_pairCode, decodeSecond_pairCode] using
      hOut (listCode [x₂]) (pairCode v' z')
  have hIn₁ : natCondK D (listCode [x₁]) (listCode [v, z]) ≤
      natCondK D x₁ (pairCode v z) + cIn := by
    simpa [singleton, listToPair, listCode_cons, decodeFirst_pairCode,
      decodeSecond_pairCode] using hIn x₁ (listCode [v, z])
  have hIn₂ : natCondK D (listCode [x₂]) (listCode [v, z]) ≤
      natCondK D x₂ (pairCode v z) + cIn := by
    simpa [singleton, listToPair, listCode_cons, decodeFirst_pairCode,
      decodeSecond_pairCode] using hIn x₂ (listCode [v, z])
  have hConst : cOut + cIn ≤ logSlack (cOut + cIn) M := by
    simp [logSlack, Nat.add_comm]
  have hRaw₁ : natCondK D x₁ (pairCode v' z') ≤
      natCondK D x₁ (pairCode v z) + (cOut + cIn) := by
    omega
  have hRaw₂ : natCondK D x₂ (pairCode v' z') ≤
      natCondK D x₂ (pairCode v z) + (cOut + cIn) := by
    omega
  dsimp [c]
  constructor
  · exact hRaw₁.trans (Nat.add_le_add_left hConst _)
  · exact hRaw₂.trans (Nat.add_le_add_left hConst _)

/-- The conditional chain upper bound in `theorem2_chain_rule`:
the conditional chain upper bound, together with a linear bound on its two inputs, gives a linear
bound on the joint pair complexity. -/
private theorem theorem2_joint_budget
    (D : Map) (hD : isOptimalConditional D) (c₀ b₀ : ℕ) :
    ∃ b : ℕ, ∀ (x v z : BitString) (t M : ℕ),
      natCondK D x z ≤ M + b₀ →
      natCondK D v (pairCode x z) ≤ t + logSlack c₀ M →
      t ≤ M →
      natCondK D (pairCode x v) z ≤ b * (M + 1) := by
  obtain ⟨cChain, hChain⟩ := Kolmogorov.condK_pairCode_chain_upper_values D hD
  obtain ⟨cTwice, hTwice⟩ := logSlack_le_add_const (2 * cChain)
  let b := 2 * (c₀ + 2) + 2 * (b₀ + c₀) + cTwice + 1
  refine ⟨b, ?_⟩
  intro x v z t M hx hv ht
  let kx := natCondK D x z
  let kv := natCondK D v (pairCode x z)
  let kp := natCondK D (pairCode x v) z
  have hChainNat : kp ≤ kx + kv + logSlack cChain (kp + 1) := by
    simpa [kx, kv, kp] using hChain x v z kx kv kp
      (condK_le_add_condMutualInfo_value D hD x z)
      (condK_le_add_condMutualInfo_value D hD v (pairCode x z))
      (condK_le_add_condMutualInfo_value D hD (pairCode x v) z)
  have hTwice' : 2 * logSlack cChain (kp + 1) ≤ kp + 1 + cTwice := by
    have h := hTwice (kp + 1)
    simpa [Kolmogorov.logSlack_nsmul] using h
  have hAbsorb : kp ≤ 2 * (2 * M + b₀ + logSlack c₀ M) + cTwice + 1 := by
    dsimp [kx, kv, kp] at hChainNat hTwice' ⊢
    omega
  have hSlack := Kolmogorov.logSlack_le_self_linear c₀ M
  have hLinear : kp ≤ 2 * (c₀ + 2) * M + 2 * (b₀ + c₀) + cTwice + 1 := by
    calc
      kp ≤ 2 * (2 * M + b₀ + logSlack c₀ M) + cTwice + 1 := hAbsorb
      _ ≤ 2 * (c₀ + 2) * M + (2 * (b₀ + c₀) + cTwice + 1) := by
        unfold Kolmogorov.logSlack at hSlack ⊢
        nlinarith
      _ = 2 * (c₀ + 2) * M + 2 * (b₀ + c₀) + cTwice + 1 := by omega
  have hb₁ : 2 * (c₀ + 2) ≤ b := by dsimp [b]; omega
  have hb₂ : 2 * (b₀ + c₀) + cTwice + 1 ≤ b := by dsimp [b]; omega
  have hFinal : kp ≤ b * M + b := by
    calc
      kp ≤ 2 * (c₀ + 2) * M + (2 * (b₀ + c₀) + cTwice + 1) := by
        simpa [Nat.add_assoc] using hLinear
      _ ≤ b * M + b := Nat.add_le_add (Nat.mul_le_mul_right M hb₁) hb₂
  simpa [kp, Nat.mul_add] using hFinal

/-- Conditional symmetry of information bounds each description in
`theorem2_common_description`:
symmetry of information to bound each description from `(v,z)`. -/
private theorem theorem2_chain_rule
    (D : Map) (hD : isOptimalConditional D) (c₀ : ℕ) :
    ∃ c : ℕ, ∀ (x₁ x₂ z v : BitString) (q t M : ℕ),
      M = natK D (pairCode (pairCode x₁ x₂) z) →
      q ≤ natCondK D v z + logSlack c₀ M →
      natCondK D v (pairCode x₁ z) ≤ t + logSlack c₀ M →
      natCondK D v (pairCode x₂ z) ≤ t + logSlack c₀ M →
      t ≤ M →
      natCondK D x₁ (pairCode v z) ≤ natK D x₁ - q + t + logSlack c M ∧
        natCondK D x₂ (pairCode v z) ≤ natK D x₂ - q + t + logSlack c M := by
  obtain ⟨cMap₁, hMap₁⟩ := plainK_map_le D hD
    (decodeFirst ∘ decodeFirst)
    (decodeFirst_computable.comp decodeFirst_computable)
  obtain ⟨cMap₂, hMap₂⟩ := plainK_map_le D hD
    (decodeSecond ∘ decodeFirst)
    (decodeSecond_computable.comp decodeFirst_computable)
  obtain ⟨cCtx, hCtx⟩ := condK_le_plainK D hD
  obtain ⟨cSwap, hSwap⟩ := condK_swapPairCode_le D hD
  obtain ⟨cChain, hChain⟩ := Kolmogorov.condK_pairCode_chain_upper_values D hD
  obtain ⟨cSym, hSym⟩ := condK_pairCode_symmetryOfInformation_values D hD
  let b₀ := max cMap₁ cMap₂ + cCtx
  obtain ⟨bJoint, hJoint⟩ :=
    theorem2_joint_budget
      D hD c₀ b₀
  obtain ⟨cChainFold, hChainFold⟩ :=
    logSlack_linear_bound cChain bJoint (bJoint + 1)
  obtain ⟨cSymFold, hSymFold⟩ :=
    logSlack_linear_bound cSym bJoint (bJoint + cSwap + 1)
  let c := 2 * c₀ + cChainFold + cSymFold + cCtx + cSwap
  refine ⟨c, ?_⟩
  intro x₁ x₂ z v q t M hM hq hv₁ hv₂ ht
  let triple := pairCode (pairCode x₁ x₂) z
  have hPlain₁ : natK D x₁ ≤ M + cMap₁ := by
    have h := hMap₁ triple
    have h' : plainK D x₁ ≤ plainK D triple + (cMap₁ : ℕ∞) := by
      simpa [triple, Function.comp_apply, decodeFirst_pairCode] using h
    have hx := commonInfo_le_mutualInfo_hasPlainValue D hD x₁
    have htriple := commonInfo_le_mutualInfo_hasPlainValue D hD triple
    rw [hx, htriple] at h'
    rw [hM]
    exact_mod_cast h'
  have hPlain₂ : natK D x₂ ≤ M + cMap₂ := by
    have h := hMap₂ triple
    have h' : plainK D x₂ ≤ plainK D triple + (cMap₂ : ℕ∞) := by
      simpa [triple, Function.comp_apply, decodeFirst_pairCode, decodeSecond_pairCode] using h
    have hx := commonInfo_le_mutualInfo_hasPlainValue D hD x₂
    have htriple := commonInfo_le_mutualInfo_hasPlainValue D hD triple
    rw [hx, htriple] at h'
    rw [hM]
    exact_mod_cast h'
  have hCtxNat (x : BitString) :
      natCondK D x z ≤ natK D x + cCtx := by
    have h := hCtx x z
    rw [condK_le_add_condMutualInfo_value D hD x z,
      commonInfo_le_mutualInfo_hasPlainValue D hD x] at h
    exact_mod_cast h
  have hX₁Z : natCondK D x₁ z ≤ M + b₀ := by
    dsimp [b₀]
    calc
      natCondK D x₁ z ≤ natK D x₁ + cCtx := hCtxNat x₁
      _ ≤ M + cMap₁ + cCtx := Nat.add_le_add_right hPlain₁ cCtx
      _ ≤ M + (max cMap₁ cMap₂ + cCtx) := by omega
  have hX₂Z : natCondK D x₂ z ≤ M + b₀ := by
    dsimp [b₀]
    calc
      natCondK D x₂ z ≤ natK D x₂ + cCtx := hCtxNat x₂
      _ ≤ M + cMap₂ + cCtx := Nat.add_le_add_right hPlain₂ cCtx
      _ ≤ M + (max cMap₁ cMap₂ + cCtx) := by omega
  have hJoint₁ := hJoint x₁ v z t M hX₁Z hv₁ ht
  have hJoint₂ := hJoint x₂ v z t M hX₂Z hv₂ ht
  have hOne (x : BitString) (hXZ : natCondK D x z ≤ M + b₀)
      (hVXZ : natCondK D v (pairCode x z) ≤ t + logSlack c₀ M)
      (hPair : natCondK D (pairCode x v) z ≤ bJoint * (M + 1)) :
      natCondK D x (pairCode v z) ≤ natK D x - q + t + logSlack c M := by
    let kx := natCondK D x z
    let kvx := natCondK D v (pairCode x z)
    let kp := natCondK D (pairCode x v) z
    let kps := natCondK D (pairCode v x) z
    let kdesc := natCondK D x (pairCode v z)
    let kv := natCondK D v z
    have hSwapNat : kps ≤ kp + cSwap := by
      have h := hSwap x v z
      rw [← ENat.natCast_toNat (condK_ne_top_of_optimal D hD (pairCode v x) z),
        ← ENat.natCast_toNat (condK_ne_top_of_optimal D hD (pairCode x v) z)] at h
      exact_mod_cast h
    have hChainNat : kp ≤ kx + kvx + logSlack cChain (kp + 1) := by
      simpa [kx, kvx, kp] using hChain x v z kx kvx kp
        (condK_le_add_condMutualInfo_value D hD x z)
        (condK_le_add_condMutualInfo_value D hD v (pairCode x z))
        (condK_le_add_condMutualInfo_value D hD (pairCode x v) z)
    have hSymNat : kv + kdesc ≤ kps + logSlack cSym (kps + 1) := by
      simpa [kv, kdesc, kps] using (hSym v x z kv kdesc kps
        (condK_le_add_condMutualInfo_value D hD v z)
        (condK_le_add_condMutualInfo_value D hD x (pairCode v z))
        (condK_le_add_condMutualInfo_value D hD (pairCode v x) z)).2
    have hPairLin : natCondK D (pairCode x v) z ≤ bJoint * M + bJoint := by
      calc
        natCondK D (pairCode x v) z ≤ bJoint * (M + 1) := hPair
        _ = bJoint * M + bJoint := by rw [Nat.mul_add]; simp
    have hPairArg : kp + 1 ≤ bJoint * M + (bJoint + 1) := by
      dsimp [kp]
      omega
    have hChainErr : logSlack cChain (kp + 1) ≤ logSlack cChainFold M := by
      calc
        logSlack cChain (kp + 1) ≤ logSlack cChain (bJoint * M + (bJoint + 1)) :=
          logSlack_mono_right cChain hPairArg
        _ ≤ logSlack cChainFold M := hChainFold M
    have hSwapArg : kps + 1 ≤ bJoint * M + (bJoint + cSwap + 1) := by
      dsimp [kps, kp]
      omega
    have hSymErr : logSlack cSym (kps + 1) ≤ logSlack cSymFold M := by
      calc
        logSlack cSym (kps + 1) ≤
            logSlack cSym (bJoint * M + (bJoint + cSwap + 1)) :=
          logSlack_mono_right cSym hSwapArg
        _ ≤ logSlack cSymFold M := hSymFold M
    have hCore : kv + kdesc ≤ kx + kvx +
        logSlack cChainFold M + logSlack cSymFold M + cSwap := by
      calc
        kv + kdesc ≤ kps + logSlack cSym (kps + 1) := hSymNat
        _ ≤ kp + cSwap + logSlack cSymFold M := by omega
        _ ≤ kx + kvx + logSlack cChainFold M + logSlack cSymFold M + cSwap := by
          omega
    have hMain : kdesc + q ≤ natK D x + t +
        (2 * logSlack c₀ M + logSlack cChainFold M + logSlack cSymFold M + cCtx + cSwap) := by
      dsimp [kx, kvx, kdesc, kv] at hCore hq hVXZ ⊢
      have hX := hCtxNat x
      omega
    have hSlack :
        2 * logSlack c₀ M + logSlack cChainFold M + logSlack cSymFold M + cCtx + cSwap ≤
          logSlack c M := by
      calc
        2 * logSlack c₀ M + logSlack cChainFold M + logSlack cSymFold M + cCtx + cSwap
            = logSlack (2 * c₀ + cChainFold + cSymFold) M + cCtx + cSwap := by
              rw [Kolmogorov.logSlack_nsmul,
                ← logSlack_add_constants (2 * c₀) cChainFold M,
                ← logSlack_add_constants (2 * c₀ + cChainFold) cSymFold M]
        _ ≤ logSlack c M := by
          simpa [c, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            logSlack_add_nat_le (2 * c₀ + cChainFold + cSymFold) (cCtx + cSwap) M
    dsimp [kdesc] at hMain ⊢
    omega
  exact ⟨hOne x₁ hX₁Z hv₁ hJoint₁, hOne x₂ hX₂Z hv₂ hJoint₂⟩

/-- Descriptions of the two context strings from a clone in `theorem2_typize`:
descriptions of `xᵢ` from a clone.  Fix the strong-typization constant `C` first.  If
`(v', z')` lies in `ST_{logSlack C M}(v, z | x̄)`, then `K(xᵢ | v', z') ≤ K(xᵢ | v, z) + O(1)`
(typization half of the profile, coordinates `V = {i}`, `W = {0,1}`), and by the chain rule
`K(xᵢ | v, z) = K(xᵢ | z) + K(v | xᵢ, z) - K(v | z) ± O(log M) ≤ K(xᵢ) - q + t + O(log M)`
using `K(v | z) ≥ q - L₀`, `K(v | xᵢ, z) ≤ t + L₀`, `K(xᵢ | z) ≤ K(xᵢ) + O(1)`. -/
private theorem theorem2_common_description
    (D : Map) (hD : isOptimalConditional D) (c₀ C : ℕ) :
    ∃ c : ℕ, ∀ (x₁ x₂ z v v' z' : BitString) (q t M : ℕ),
      M = natK D (pairCode (pairCode x₁ x₂) z) →
      q ≤ natCondK D v z + logSlack c₀ M →
      natCondK D v z ≤ q + logSlack c₀ M →
      natCondK D v (pairCode x₁ z) ≤ t + logSlack c₀ M →
      natCondK D v (pairCode x₂ z) ≤ t + logSlack c₀ M →
      t ≤ M →
      (![v', z'] : Fin 2 → BitString) ∈
        strongTypization D (logSlack C M) ![v, z] ![x₁, x₂] →
      natCondK D x₁ (pairCode v' z') ≤ natK D x₁ - q + t + logSlack c M ∧
      natCondK D x₂ (pairCode v' z') ≤ natK D x₂ - q + t + logSlack c M := by
  obtain ⟨cProf, hProf⟩ :=
    theorem2_profile_transfer
      D hD C
  obtain ⟨cChain, hChain⟩ :=
    theorem2_chain_rule
      D hD c₀
  let c := cProf + cChain
  refine ⟨c, ?_⟩
  intro x₁ x₂ z v v' z' q t M hM hq₁ hq₂ hv₁ hv₂ ht hst
  obtain ⟨hProf₁, hProf₂⟩ := hProf x₁ x₂ z v v' z' M hM hst
  obtain ⟨hChain₁, hChain₂⟩ := hChain x₁ x₂ z v q t M hM hq₁ hv₁ hv₂ ht
  have hSlack : logSlack c M = logSlack cProf M + logSlack cChain M := by
    dsimp [c]
    rw [← logSlack_add_constants]
  constructor <;> omega

/-- Strong typization produces a reservoir of clones for `theorem2_typization_and_cover`:
`(v, z)` given `x̄ = (x₁, x₂)` (Lemmas 1 and 2) and keep a reservoir `A` of exactly `2 ^ α` clones
`a = ⟨v', z'⟩` of `⟨v, z⟩`.  Here `α = K(v, z | x̄) - O(log M) ∈ [m - t, m + t] ± O(log M)` with
`m = K(z)` (as `K(z | x̄) ≥ m - t` and `K(v | x̄, z) ≤ t`), `β = m + ⌈δ/2⌉ + O(log M)` is pinned
from both sides, and `γ = m + q + O(log M)` bounds the complexity of every clone (clones keep the
whole extended profile of `(v, z, x₁, x₂)` up to `O(log M)`, and `K(v, z) = m + K(v | z) ± O(log M)`
with `K(v | z) = q ± O(log M)` by the cut). -/
theorem theorem2_typize (D : Map)
    (hD : isOptimalConditional D) (c₀ : ℕ) :
    ∃ c : ℕ, ∀ (x₁ x₂ z v : BitString) (q t δ M : ℕ),
      M = natK D (pairCode (pairCode x₁ x₂) z) →
      MutualInfoLe D (pairCode x₁ x₂) z t →
      q ≤ natCondK D v z + logSlack c₀ M →
      natCondK D v z ≤ q + logSlack c₀ M →
      natCondK D v (pairCode x₁ z) ≤ t + logSlack c₀ M →
      natCondK D v (pairCode x₂ z) ≤ t + logSlack c₀ M →
      t ≤ M → 8 * (t + logSlack 1 M) ≤ δ →
    ∃ (α β γ : ℕ) (A : Finset BitString),
      A.card = 2 ^ α ∧
      natK D z ≤ α + t + logSlack c M ∧
      α ≤ natK D z + t + logSlack c M ∧
      2 * (natK D z + logSlack c M) + δ ≤ 2 * β ∧
      2 * β ≤ 2 * (natK D z + logSlack c M) + δ + 1 ∧
      γ ≤ natK D z + q + logSlack c M + 1 ∧
      (∀ a ∈ A, ∃ v' z', a = pairCode v' z' ∧
        q ≤ natCondK D v' z' + logSlack c M ∧
        natCondK D v' (pairCode x₁ z') ≤ t + logSlack c M ∧
        natCondK D v' (pairCode x₂ z') ≤ t + logSlack c M ∧
        natCondK D x₁ a ≤ natK D x₁ - q + t + logSlack c M ∧
        natCondK D x₂ a ≤ natK D x₂ - q + t + logSlack c M ∧
        natK D z' ≤ natK D z + logSlack c M ∧
        natK D z ≤ natK D z' + logSlack c M ∧
        natK D a ≤ natK D z + q + logSlack c M ∧
        natK D z + q ≤ natK D a + logSlack c M ∧
        MutualInfoLe D (pairCode x₁ x₂) z' (t + logSlack c M) ∧
        natCondK D a (pairCode x₁ x₂) ≤ α + logSlack c M ∧
        α ≤ natCondK D a (pairCode x₁ x₂) + logSlack c M) ∧
      (∀ a ∈ A, natK D a < γ) := by
  obtain ⟨C, cCount, hCount⟩ :=
    theorem2_strong_typization_count D hD c₀
  obtain ⟨cWin, hWin⟩ :=
    theorem2_alpha_window D hD c₀
  obtain ⟨cTot, hTot⟩ :=
    theorem2_total_profile D hD c₀ C
  obtain ⟨cCond, hCond⟩ :=
    theorem2_conditional_profile D hD c₀ C
  obtain ⟨cDesc, hDesc⟩ :=
    theorem2_common_description D hD c₀ C
  refine ⟨cCount + cWin + cTot + cCond + cDesc, ?_⟩
  intro x₁ x₂ z v q t δ M hM hMI hq₁ hq₂ hv₁ hv₂ ht hδ
  obtain ⟨α, B, hBcard, hαlo, hαhi, hB⟩ := hCount x₁ x₂ z v t M hM hv₁ ht
  obtain ⟨hwin₁, hwin₂⟩ := hWin x₁ x₂ z v t M hM hMI hv₁ ht
  have hsum : logSlack (cCount + cWin + cTot + cCond + cDesc) M =
      logSlack cCount M + logSlack cWin M + logSlack cTot M + logSlack cCond M +
        logSlack cDesc M := by
    unfold logSlack; ring
  generalize hcdef : cCount + cWin + cTot + cCond + cDesc = c at hsum ⊢
  let L := logSlack c M
  let β := natK D z + L + (δ + 1) / 2
  let γ := natK D z + q + L + 1
  obtain ⟨A, hAB, hAcard⟩ := Finset.exists_subset_card_eq (s := B) (n := 2 ^ α) hBcard
  have hcl : ∀ a ∈ B,
      ∃ v' z', a = pairCode v' z' ∧
        q ≤ natCondK D v' z' + L ∧
        natCondK D v' (pairCode x₁ z') ≤ t + L ∧
        natCondK D v' (pairCode x₂ z') ≤ t + L ∧
        natCondK D x₁ a ≤ natK D x₁ - q + t + L ∧
        natCondK D x₂ a ≤ natK D x₂ - q + t + L ∧
        natK D z' ≤ natK D z + L ∧
        natK D z ≤ natK D z' + L ∧
        natK D a ≤ natK D z + q + L ∧
        natK D z + q ≤ natK D a + L ∧
        MutualInfoLe D (pairCode x₁ x₂) z' (t + L) ∧
        natCondK D a (pairCode x₁ x₂) ≤ α + L ∧
        α ≤ natCondK D a (pairCode x₁ x₂) + L := by
    intro a ha
    obtain ⟨v', z', hpair, hst⟩ := hB a ha
    subst hpair
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hTot x₁ x₂ z v v' z' q t M hM hq₁ hq₂ hv₁ ht hst
    obtain ⟨h7, h8, h9, h10⟩ := hCond x₁ x₂ z v v' z' q t M hM hMI hq₁ hv₁ hv₂ ht hst
    obtain ⟨h11, h12⟩ := hDesc x₁ x₂ z v v' z' q t M hM hq₁ hq₂ hv₁ hv₂ ht hst
    refine ⟨v', z', rfl, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
      by omega, by omega, ?_, by omega, by omega⟩
    change natK D (pairCode x₁ x₂) ≤ natCondK D (pairCode x₁ x₂) z' + (t + L)
    change natK D (pairCode x₁ x₂) ≤ natCondK D (pairCode x₁ x₂) z' + (t + logSlack cCond M)
      at h10
    omega
  refine ⟨α, β, γ, A, hAcard, by omega, by omega, by dsimp [β]; omega, by dsimp [β]; omega,
    le_refl _, ?_, ?_⟩
  · intro a ha
    obtain ⟨v', z', hpair, h⟩ := hcl a (hAB ha)
    exact ⟨v', z', hpair, h⟩
  · intro a ha
    obtain ⟨v', z', hpair, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ :=
      hcl a (hAB ha)
    dsimp [γ]
    omega

/-- The reservoir `A` in `theorem2_typization_and_cover` is
either an `(α, β, γ)`-semi-bunch or some clone `a ∈ A` has at least half of `A` at conditional
complexity `≥ β` from it. -/
theorem theorem2_semi_bunch_dichotomy (D : Map)
    (α β γ : ℕ) (A : Finset BitString)
    (hcard : A.card = 2 ^ α) (hcomplex : ∀ a ∈ A, natK D a < γ) :
    IsSemiBunch D α β γ A ∨
      ∃ a ∈ A, A.card ≤ 2 * (A.filter fun b => β ≤ natCondK D b a).card := by
  classical
  by_cases hgood : ∀ a ∈ A,
      A.card < 2 * (A.filter fun b => natCondK D b a < β).card
  · exact Or.inl ⟨hcard, hgood, hcomplex⟩
  · right
    push Not at hgood
    obtain ⟨a, ha, hfail⟩ := hgood
    refine ⟨a, ha, ?_⟩
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := A) (fun b => natCondK D b a < β)
    have hbadFilter : A.filter (fun b => ¬ natCondK D b a < β) =
        A.filter (fun b => β ≤ natCondK D b a) := by
      ext b
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hb, hnot⟩
        exact ⟨hb, Nat.not_lt.mp hnot⟩
      · rintro ⟨hb, hle⟩
        exact ⟨hb, Nat.not_lt.mpr hle⟩
    rw [hbadFilter] at hsplit
    omega

end Kolmogorov.Relativization
