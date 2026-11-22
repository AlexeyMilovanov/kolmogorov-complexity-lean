/-
Copyright (c) 2026 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Relativization.CommonInformation.CommonInformationTheorem

/-!
# Conjecture Reduction

This module proves that Conjecture 3 implies Conjecture 2 and establishes the
padding estimates needed for the reduction. Its main results formalize the
reduction in Section 4 of Muchnik and Romashchenko's paper on relativization of
Kolmogorov complexity.
-/

namespace Kolmogorov.Relativization
open Filter Asymptotics

/-- The singleton profile coordinate transfers the extracted complexity to an
unrelativized witness, with logarithmic loss and a linear plain-complexity bound. -/
private theorem conjecture2_of_conjecture3_profile_plain_complexity
    (D : Map) (hD : isOptimalConditional D) (C₁ c₀ : ℕ) :
    ∃ c : ℕ, ∀ (x₁ x₂ z v w₀ : BitString) (q : ℕ),
      q ≤ natCondK D v z →
      natCondK D v (pairCode x₁ z) ≤
        logSlack C₁ (natK D (pairCode (pairCode x₁ x₂) z)) →
      ProfileWithin
        (subKRel D
          (Fin.append (fun i : Fin 2 => if i.val = 0 then x₁ else x₂)
            (fun _ : Fin 1 => v)) z)
        (subK D
          (Fin.append (fun i : Fin 2 => if i.val = 0 then x₁ else x₂)
            (fun _ : Fin 1 => w₀)))
        (logSlack c₀ (natK D (pairCode (pairCode x₁ x₂) z))) →
      q ≤ natK D w₀ + logSlack c (natK D (pairCode (pairCode x₁ x₂) z)) ∧
      natK D w₀ ≤ c * (natK D (pairCode (pairCode x₁ x₂) z) + 1) := by
  let listSingleton : BitString → BitString := fun s => listCode [s]
  let decodeSingleton : BitString → BitString := fun s => (decodeListCode s).getD 0 []
  have hListComp : Computable listSingleton := by
    dsimp [listSingleton]
    exact listCode_computable.comp
      ((Primrec.list_cons.comp Primrec.id (Primrec.const ([] : List BitString))).to_comp)
  have hDecodeComp : Computable decodeSingleton := by
    dsimp [decodeSingleton]
    exact ((Primrec.list_getD ([] : BitString)).comp decodeListCode_primrec
      (Primrec.const 0)).to_comp
  obtain ⟨cList, hList⟩ := condK_le_add_condMutualInfo_nat_map D hD listSingleton hListComp
  obtain ⟨cDecode, hDecode⟩ :=
    condK_le_add_condMutualInfo_nat_map D hD decodeSingleton hDecodeComp
  obtain ⟨cProj, hProj⟩ := condK_le_add_condMutualInfo_nat_map D hD
    (fun s : BitString => decodeFirst (decodeFirst s))
    (decodeFirst_computable.comp decodeFirst_computable)
  obtain ⟨cCondPlain, hCondPlain⟩ := condK_le_plainK D hD
  obtain ⟨cSelf, hSelf⟩ := condK_comp D hD (fun s : BitString => s) Computable.id
  obtain ⟨cPairCtx, hPairCtx⟩ := condK_pair_le_add D hD
  obtain ⟨cTrans, hTrans⟩ := Kolmogorov.condK_chain_upper_values D hD
  let aCtx := cPairCtx + 1
  let bCtx := aCtx * (cProj + cCondPlain) + cSelf + cPairCtx * cSelf + 2 * cPairCtx
  let aArg := C₁ + aCtx
  let bArg := bCtx + 2 * C₁ + 1
  obtain ⟨cFold, hFold⟩ := logSlack_linear_bound cTrans aArg bArg
  let cWitness := C₁ + cFold + cList + cDecode + c₀
  let cLinear := aCtx + cWitness + bCtx + 2 * cWitness + 2
  let cLoss := c₀ + cDecode + cList
  let c := max cLoss cLinear
  refine ⟨c, ?_⟩
  intro x₁ x₂ z v w₀ q hq hvx₁ hProfile
  let N := natK D (pairCode (pairCode x₁ x₂) z)
  have hCoord := hProfile ({Fin.last 2} : Finset (Fin 3)) (by simp)
  have hCodeV :
      subtupleCode
        (Fin.append (fun i : Fin 2 => if i.val = 0 then x₁ else x₂)
          (fun _ : Fin 1 => v)) ({Fin.last 2} : Finset (Fin 3)) = listCode [v] := by
    simp [subtupleCode, Fin.append, Fin.addCases]
  have hCodeW :
      subtupleCode
        (Fin.append (fun i : Fin 2 => if i.val = 0 then x₁ else x₂)
          (fun _ : Fin 1 => w₀)) ({Fin.last 2} : Finset (Fin 3)) = listCode [w₀] := by
    simp [subtupleCode, Fin.append, Fin.addCases]
  change natCondK D
      (subtupleCode
        (Fin.append (fun i : Fin 2 => if i.val = 0 then x₁ else x₂)
          (fun _ : Fin 1 => v)) {Fin.last 2}) z ≤
      natK D (subtupleCode
        (Fin.append (fun i : Fin 2 => if i.val = 0 then x₁ else x₂)
          (fun _ : Fin 1 => w₀)) {Fin.last 2}) +
        logSlack c₀ (natK D (pairCode (pairCode x₁ x₂) z)) ∧
    natK D (subtupleCode
        (Fin.append (fun i : Fin 2 => if i.val = 0 then x₁ else x₂)
          (fun _ : Fin 1 => w₀)) {Fin.last 2}) ≤
      natCondK D (subtupleCode
        (Fin.append (fun i : Fin 2 => if i.val = 0 then x₁ else x₂)
          (fun _ : Fin 1 => v)) {Fin.last 2}) z +
        logSlack c₀ (natK D (pairCode (pairCode x₁ x₂) z)) at hCoord
  rw [hCodeV, hCodeW] at hCoord
  have hCoord₁ : natCondK D (listCode [v]) z ≤
      natK D (listCode [w₀]) + logSlack c₀ N := by
    simpa [N] using hCoord.1
  have hCoord₂ : natK D (listCode [w₀]) ≤
      natCondK D (listCode [v]) z + logSlack c₀ N := by
    simpa [N] using hCoord.2
  have hListPlain (w : BitString) :
      natK D (listCode [w]) ≤ natK D w + cList := by
    simpa only [natK, natCondK, plainK, listSingleton] using hList w []
  have hDecodePlain (w : BitString) :
      natK D w ≤ natK D (listCode [w]) + cDecode := by
    have hh := hDecode (listCode [w]) []
    simpa only [natK, natCondK, plainK, decodeSingleton, decodeListCode_listCode,
      List.getD_cons_zero] using hh
  have hDecodeCond (w z : BitString) :
      natCondK D w z ≤ natCondK D (listCode [w]) z + cDecode := by
    have hh := hDecode (listCode [w]) z
    simpa only [decodeSingleton, decodeListCode_listCode, List.getD_cons_zero] using hh
  have hListCond (w z : BitString) :
      natCondK D (listCode [w]) z ≤ natCondK D w z + cList := by
    simpa only [listSingleton] using hList w z
  have hqBound : q ≤ natK D w₀ + logSlack cLoss N := by
    have hraw : q ≤ natK D w₀ + logSlack c₀ N + (cDecode + cList) := by
      have h₁ := hDecodeCond v z
      have h₂ := hListPlain w₀
      omega
    calc
      q ≤ natK D w₀ + logSlack c₀ N + (cDecode + cList) := hraw
      _ ≤ natK D w₀ + logSlack cLoss N := by
        simpa [cLoss, Nat.add_assoc] using
          (Nat.add_le_add_left (logSlack_add_nat_le c₀ (cDecode + cList) N)
            (natK D w₀))
  have hTripleVal := condK_le_add_condMutualInfo_value D hD
    (pairCode (pairCode x₁ x₂) z) z
  have hTriplePlainVal := commonInfo_le_mutualInfo_hasPlainValue D hD
    (pairCode (pairCode x₁ x₂) z)
  have hTripleCondBound :
      natCondK D (pairCode (pairCode x₁ x₂) z) z ≤ N + cCondPlain := by
    have hh := hCondPlain (pairCode (pairCode x₁ x₂) z) z
    rw [hTripleVal, hTriplePlainVal] at hh
    exact_mod_cast hh
  have hX₁Bound : natCondK D x₁ z ≤ N + cProj + cCondPlain := by
    have hp := hProj (pairCode (pairCode x₁ x₂) z) z
    simpa [decodeFirst_pairCode] using hp.trans (by omega)
  let kx := natCondK D x₁ z
  let kzx := natCondK D (pairCode x₁ z) z
  let kyx := natCondK D v (pairCode x₁ z)
  let kvz := natCondK D v z
  have hSelfVal := condK_le_add_condMutualInfo_value D hD z z
  have hSelfNat : natCondK D z z ≤ cSelf := by
    have hh := hSelf z
    rw [hSelfVal] at hh
    exact_mod_cast hh
  have hKxVal := condK_le_add_condMutualInfo_value D hD x₁ z
  have hKzxVal := condK_le_add_condMutualInfo_value D hD (pairCode x₁ z) z
  have hKzxPair : kzx ≤ kx + natCondK D z z +
      logSlack cPairCtx (kx + natCondK D z z + 1) := by
    have hh := hPairCtx x₁ z z kx (natCondK D z z) hKxVal hSelfVal
    rw [hKzxVal] at hh
    exact_mod_cast hh
  have hKzxPairBound : kzx ≤ kx + cSelf +
      logSlack cPairCtx (kx + cSelf + 1) := by
    have hArgSelf : kx + natCondK D z z + 1 ≤ kx + cSelf + 1 := by omega
    have hSlackSelf := logSlack_mono_right cPairCtx hArgSelf
    omega
  have hKzxLinear : kzx ≤ aCtx * N + bCtx := by
    have hSlack := Kolmogorov.logSlack_le_self_linear cPairCtx (kx + cSelf + 1)
    have hraw : kzx ≤ (cPairCtx + 1) * kx +
        (cSelf + cPairCtx * cSelf + 2 * cPairCtx) := by
      have hEq : kx + cSelf + (cPairCtx * (kx + cSelf + 1) + cPairCtx) =
          (cPairCtx + 1) * kx + (cSelf + cPairCtx * cSelf + 2 * cPairCtx) := by ring
      have hSlack' := Nat.add_le_add_left hSlack (kx + cSelf)
      have hraw' := hKzxPairBound.trans hSlack'
      rw [hEq] at hraw'
      exact hraw'
    have hkx := hX₁Bound
    dsimp [kx, aCtx, bCtx]
    calc
      kzx ≤ (cPairCtx + 1) * kx +
          (cSelf + cPairCtx * cSelf + 2 * cPairCtx) := hraw
      _ ≤ (cPairCtx + 1) * (N + cProj + cCondPlain) +
          (cSelf + cPairCtx * cSelf + 2 * cPairCtx) := by gcongr
      _ = (cPairCtx + 1) * N +
          ((cPairCtx + 1) * (cProj + cCondPlain) +
            cSelf + cPairCtx * cSelf + 2 * cPairCtx) := by ring
  have hTransNat := hTrans z v (pairCode x₁ z) kzx kyx kvz
    hKzxVal
    (condK_le_add_condMutualInfo_value D hD v (pairCode x₁ z))
    (condK_le_add_condMutualInfo_value D hD v z)
  have hArg : kzx + kyx + 1 ≤ aArg * N + bArg := by
    have hLog : logSlack C₁ N ≤ C₁ * N + 2 * C₁ := by
      exact (Kolmogorov.logSlack_le_self_linear C₁ N).trans (by omega)
    have h0 : kzx + kyx + 1 ≤ aCtx * N + bCtx + C₁ * N + 2 * C₁ + 1 := by
      have hkzx := hKzxLinear
      have hkyx := hvx₁.trans hLog
      omega
    dsimp [aArg, bArg]
    rw [Nat.add_mul]
    omega
  have hLogTrans : logSlack cTrans (kzx + kyx + 1) ≤ logSlack cFold N :=
    (logSlack_mono_right cTrans hArg).trans (hFold N)
  have hKvzRaw : kvz ≤ aCtx * N + bCtx + logSlack C₁ N + logSlack cFold N := by
    have hsum : kzx + kyx ≤ aCtx * N + bCtx + logSlack C₁ N := by
      exact Nat.add_le_add hKzxLinear hvx₁
    calc
      kvz ≤ kzx + kyx + logSlack cTrans (kzx + kyx + 1) := hTransNat
      _ ≤ aCtx * N + bCtx + logSlack C₁ N +
          logSlack cTrans (kzx + kyx + 1) := Nat.add_le_add_right hsum _
      _ ≤ aCtx * N + bCtx + logSlack C₁ N + logSlack cFold N := by omega
  have hKvzBound : kvz ≤ aCtx * N + bCtx +
      logSlack (C₁ + cFold) N := by
    calc
      kvz ≤ aCtx * N + bCtx + logSlack C₁ N + logSlack cFold N := hKvzRaw
      _ ≤ aCtx * N + bCtx + logSlack (C₁ + cFold) N := by
        rw [← logSlack_add_const C₁ cFold N]
        omega
  have hWBound : natK D w₀ ≤ aCtx * N + bCtx + logSlack cWitness N := by
    have hraw : natK D w₀ ≤ aCtx * N + bCtx + logSlack (C₁ + cFold) N +
        logSlack c₀ N + (cDecode + cList) := by
      have h₁ := hDecodePlain w₀
      have h₂ := hCoord₂
      have h₃ := hListCond v z
      have h₄ := hKvzBound
      dsimp [N] at h₁ h₂ h₃ h₄ ⊢
      omega
    calc
      natK D w₀ ≤ aCtx * N + bCtx + logSlack (C₁ + cFold) N +
          logSlack c₀ N + (cDecode + cList) := hraw
      _ ≤ aCtx * N + bCtx + logSlack (C₁ + cFold + c₀ + cDecode + cList) N := by
        have hh : logSlack (C₁ + cFold) N + logSlack c₀ N + (cDecode + cList) ≤
            logSlack (C₁ + cFold + c₀ + cDecode + cList) N := by
          calc
            logSlack (C₁ + cFold) N + logSlack c₀ N + (cDecode + cList)
                = logSlack (C₁ + cFold + c₀) N + (cDecode + cList) := by
                    rw [logSlack_add_const]
            _ ≤ logSlack (C₁ + cFold + c₀ + (cDecode + cList)) N :=
              logSlack_add_nat_le (C₁ + cFold + c₀) (cDecode + cList) N
            _ = logSlack (C₁ + cFold + c₀ + cDecode + cList) N := by
              congr 1; omega
        simpa [Nat.add_assoc] using Nat.add_le_add_left hh (aCtx * N + bCtx)
      _ ≤ aCtx * N + bCtx + logSlack cWitness N := by
        exact Nat.add_le_add_left
          (logSlack_mono_left (by dsimp [cWitness]; omega) N) _
  have hWLinear : natK D w₀ ≤ cLinear * (N + 1) := by
    calc
      natK D w₀ ≤ aCtx * N + bCtx + logSlack cWitness N := hWBound
      _ ≤ aCtx * N + bCtx + (cWitness * N + 2 * cWitness) :=
        Nat.add_le_add_left (Nat.le_trans (Kolmogorov.logSlack_le_self_linear cWitness N)
          (by omega)) (aCtx * N + bCtx)
      _ ≤ cLinear * (N + 1) := by
        dsimp [cLinear]
        nlinarith [Nat.zero_le (cWitness * N), Nat.zero_le cWitness, Nat.zero_le N,
          Nat.zero_le aCtx, Nat.zero_le bCtx]
  exact ⟨hqBound.trans (Nat.add_le_add_left
      (logSlack_mono_left (Nat.le_max_left cLoss cLinear) N) _),
    hWLinear.trans (Nat.mul_le_mul_right (N + 1) (Nat.le_max_right cLoss cLinear))⟩

private theorem listToPair_computable :
    Computable (fun s : BitString =>
      pairCode (decodeFirst s) (decodeFirst (decodeSecond s))) := by
  exact Computable₂.comp pairCode_computable decodeFirst_computable
    (decodeFirst_computable.comp decodeSecond_computable)

/-- The singleton and pair coordinates of the three-string profile yield bounds
for strings and canonical pair codes at constant logarithmic cost. -/
private theorem conjecture2_of_conjecture3_profile_coordinates
    (D : Map) (hD : isOptimalConditional D) (c₀ : ℕ) :
    ∃ c : ℕ, ∀ (x₁ x₂ z v w₀ : BitString),
      ProfileWithin
        (subKRel D
          (Fin.append (fun i : Fin 2 => if i.val = 0 then x₁ else x₂)
            (fun _ : Fin 1 => v)) z)
        (subK D
          (Fin.append (fun i : Fin 2 => if i.val = 0 then x₁ else x₂)
            (fun _ : Fin 1 => w₀)))
        (logSlack c₀ (natK D (pairCode (pairCode x₁ x₂) z))) →
      (natCondK D x₁ z ≤ natK D x₁ +
          logSlack c (natK D (pairCode (pairCode x₁ x₂) z)) ∧
        natK D (pairCode x₁ w₀) ≤ natCondK D (pairCode x₁ v) z +
          logSlack c (natK D (pairCode (pairCode x₁ x₂) z))) ∧
      (natCondK D x₂ z ≤ natK D x₂ +
          logSlack c (natK D (pairCode (pairCode x₁ x₂) z)) ∧
        natK D (pairCode x₂ w₀) ≤ natCondK D (pairCode x₂ v) z +
          logSlack c (natK D (pairCode (pairCode x₁ x₂) z))) := by
  let singleton : BitString → BitString := fun s => listCode [s]
  let decodeSingleton : BitString → BitString := fun s =>
    (decodeListCode s).getD 0 []
  let pairToList : BitString → BitString := fun s =>
    listCode [decodeFirst s, decodeSecond s]
  let listToPair : BitString → BitString := fun s =>
    pairCode (decodeFirst s) (decodeFirst (decodeSecond s))
  have hSingletonComp : Computable singleton := by
    dsimp [singleton]
    exact listCode_computable.comp
      ((Primrec.list_cons.comp Primrec.id (Primrec.const ([] : List BitString))).to_comp)
  have hDecodeSingletonComp : Computable decodeSingleton := by
    dsimp [decodeSingleton]
    exact ((Primrec.list_getD ([] : BitString)).comp decodeListCode_primrec
      (Primrec.const 0)).to_comp
  have hPairToListComp : Computable pairToList := by
    dsimp [pairToList]
    exact listCode_computable.comp
      (Computable₂.comp Primrec.list_cons.to_comp decodeFirst_computable
        (Computable₂.comp Primrec.list_cons.to_comp decodeSecond_computable
          (Computable.const ([] : List BitString))))
  have hListToPairComp : Computable listToPair := by
    dsimp [listToPair]
    exact listToPair_computable
  obtain ⟨cSingleton, hSingleton⟩ :=
    condK_le_add_condMutualInfo_nat_map D hD singleton hSingletonComp
  obtain ⟨cDecode, hDecode⟩ :=
    condK_le_add_condMutualInfo_nat_map D hD decodeSingleton hDecodeSingletonComp
  obtain ⟨cPairToList, hPairToList⟩ :=
    condK_le_add_condMutualInfo_nat_map D hD pairToList hPairToListComp
  obtain ⟨cListToPair, hListToPair⟩ :=
    condK_le_add_condMutualInfo_nat_map D hD listToPair hListToPairComp
  let overhead := cSingleton + cDecode + cPairToList + cListToPair
  let c := c₀ + overhead
  refine ⟨c, fun x₁ x₂ z v w₀ hProfile => ?_⟩
  let N := natK D (pairCode (pairCode x₁ x₂) z)
  have hSlack : logSlack c₀ N + overhead ≤ logSlack c N := by
    dsimp [c]
    exact logSlack_add_const_le c₀ overhead N
  let tV : Fin 3 → BitString := Fin.append
    (fun i : Fin 2 => if i.val = 0 then x₁ else x₂) (fun _ : Fin 1 => v)
  let tW : Fin 3 → BitString := Fin.append
    (fun i : Fin 2 => if i.val = 0 then x₁ else x₂) (fun _ : Fin 1 => w₀)
  have hX₁VCode : subtupleCode tV ({(0 : Fin 3)} : Finset (Fin 3)) = singleton x₁ := by
    simp [tV, singleton, subtupleCode, Fin.append, Fin.addCases]
  have hX₁WCode : subtupleCode tW ({(0 : Fin 3)} : Finset (Fin 3)) = singleton x₁ := by
    simp [tW, singleton, subtupleCode, Fin.append, Fin.addCases]
  have hX₂VCode : subtupleCode tV ({(1 : Fin 3)} : Finset (Fin 3)) = singleton x₂ := by
    simp [tV, singleton, subtupleCode, Fin.append, Fin.addCases]
  have hX₂WCode : subtupleCode tW ({(1 : Fin 3)} : Finset (Fin 3)) = singleton x₂ := by
    simp [tW, singleton, subtupleCode, Fin.append, Fin.addCases]
  have hPair₁VCode :
      subtupleCode tV ({(0 : Fin 3), Fin.last 2} : Finset (Fin 3)) =
        listCode [x₁, v] := by
    unfold subtupleCode
    rw [Finset.sort_insert (r := (· ≤ ·)) (by
      intro b hb
      simp only [Finset.mem_singleton] at hb
      subst b
      exact Fin.zero_le _) (by simp)]
    simp [tV, Fin.append, Fin.addCases]
  have hPair₁WCode :
      subtupleCode tW ({(0 : Fin 3), Fin.last 2} : Finset (Fin 3)) =
        listCode [x₁, w₀] := by
    unfold subtupleCode
    rw [Finset.sort_insert (r := (· ≤ ·)) (by
      intro b hb
      simp only [Finset.mem_singleton] at hb
      subst b
      exact Fin.zero_le _) (by simp)]
    simp [tW, Fin.append, Fin.addCases]
  have hPair₂VCode :
      subtupleCode tV ({(1 : Fin 3), Fin.last 2} : Finset (Fin 3)) =
        listCode [x₂, v] := by
    unfold subtupleCode
    rw [Finset.sort_insert (r := (· ≤ ·)) (by
      intro b hb
      simp only [Finset.mem_singleton] at hb
      subst b
      exact Fin.le_last _) (by simp)]
    simp [tV, Fin.append, Fin.addCases]
  have hPair₂WCode :
      subtupleCode tW ({(1 : Fin 3), Fin.last 2} : Finset (Fin 3)) =
        listCode [x₂, w₀] := by
    unfold subtupleCode
    rw [Finset.sort_insert (r := (· ≤ ·)) (by
      intro b hb
      simp only [Finset.mem_singleton] at hb
      subst b
      exact Fin.le_last _) (by simp)]
    simp [tW, Fin.append, Fin.addCases]
  have hX₁Profile := hProfile ({(0 : Fin 3)} : Finset (Fin 3)) (by simp)
  have hX₁Profile : natCondK D (singleton x₁) z ≤
      natK D (singleton x₁) + logSlack c₀ N := by
    change natCondK D (subtupleCode tV {0}) z ≤
      natK D (subtupleCode tW {0}) + logSlack c₀ N ∧ _ at hX₁Profile
    rw [hX₁VCode, hX₁WCode] at hX₁Profile
    exact hX₁Profile.1
  have hX₂Profile := hProfile ({(1 : Fin 3)} : Finset (Fin 3)) (by simp)
  have hX₂Profile : natCondK D (singleton x₂) z ≤
      natK D (singleton x₂) + logSlack c₀ N := by
    change natCondK D (subtupleCode tV {1}) z ≤
      natK D (subtupleCode tW {1}) + logSlack c₀ N ∧ _ at hX₂Profile
    rw [hX₂VCode, hX₂WCode] at hX₂Profile
    exact hX₂Profile.1
  have hPair₁Profile :=
    hProfile ({(0 : Fin 3), Fin.last 2} : Finset (Fin 3)) (by simp)
  have hPair₁Profile : natK D (listCode [x₁, w₀]) ≤
      natCondK D (listCode [x₁, v]) z + logSlack c₀ N := by
    have hback := hPair₁Profile.2
    change natK D (subtupleCode tW {0, Fin.last 2}) ≤
      natCondK D (subtupleCode tV {0, Fin.last 2}) z + logSlack c₀ N at hback
    rw [hPair₁WCode, hPair₁VCode] at hback
    exact hback
  have hPair₂Profile :=
    hProfile ({(1 : Fin 3), Fin.last 2} : Finset (Fin 3)) (by simp)
  have hPair₂Profile : natK D (listCode [x₂, w₀]) ≤
      natCondK D (listCode [x₂, v]) z + logSlack c₀ N := by
    have hback := hPair₂Profile.2
    change natK D (subtupleCode tW {1, Fin.last 2}) ≤
      natCondK D (subtupleCode tV {1, Fin.last 2}) z + logSlack c₀ N at hback
    rw [hPair₂WCode, hPair₂VCode] at hback
    exact hback
  have hSingletonPlain (x : BitString) :
      natK D (singleton x) ≤ natK D x + cSingleton := by
    have h := hSingleton x []
    simpa only [natK, natCondK, plainK, singleton] using h
  have hDecodeAt (x z : BitString) :
      natCondK D x z ≤ natCondK D (singleton x) z + cDecode := by
    have h := hDecode (singleton x) z
    change natCondK D ((decodeListCode (listCode [x])).getD 0 []) z ≤
      natCondK D (listCode [x]) z + cDecode at h
    simpa only [decodeListCode_listCode, List.getD_cons_zero] using h
  have hToListAt (x y z : BitString) :
      natCondK D (listCode [x, y]) z ≤ natCondK D (pairCode x y) z + cPairToList := by
    have h := hPairToList (pairCode x y) z
    simpa [pairToList, decodeFirst_pairCode, decodeSecond_pairCode] using h
  have hToPairAt (x y : BitString) :
      natK D (pairCode x y) ≤ natK D (listCode [x, y]) + cListToPair := by
    have h := hListToPair (listCode [x, y]) []
    simpa only [natK, natCondK, plainK, listToPair, listCode_cons,
      decodeFirst_pairCode, decodeSecond_pairCode] using h
  have hX₁Core : natCondK D x₁ z ≤
      natK D x₁ + (logSlack c₀ N + overhead) := by
    have hDec := hDecodeAt x₁ z
    have hPlain := hSingletonPlain x₁
    have hProf := hX₁Profile
    dsimp [overhead]
    omega
  have hX₂Core : natCondK D x₂ z ≤
      natK D x₂ + (logSlack c₀ N + overhead) := by
    have hDec := hDecodeAt x₂ z
    have hPlain := hSingletonPlain x₂
    have hProf := hX₂Profile
    dsimp [overhead]
    omega
  have hPair₁Core : natK D (pairCode x₁ w₀) ≤
      natCondK D (pairCode x₁ v) z + (logSlack c₀ N + overhead) := by
    have hRight := hToPairAt x₁ w₀
    have hLeft := hToListAt x₁ v z
    dsimp [overhead]
    omega
  have hPair₂Core : natK D (pairCode x₂ w₀) ≤
      natCondK D (pairCode x₂ v) z + (logSlack c₀ N + overhead) := by
    have hRight := hToPairAt x₂ w₀
    have hLeft := hToListAt x₂ v z
    dsimp [overhead]
    omega
  constructor
  · constructor
    · exact hX₁Core.trans (Nat.add_le_add_left hSlack _)
    · exact hPair₁Core.trans (Nat.add_le_add_left hSlack _)
  · constructor
    · exact hX₂Core.trans (Nat.add_le_add_left hSlack _)
    · exact hPair₂Core.trans (Nat.add_le_add_left hSlack _)

/-- The conditional chain rule bounds the complexity of each pair `(xᵢ,v)`
linearly in the joint input complexity. -/
private theorem conjecture2_of_conjecture3_pair_bound
    (D : Map) (hD : isOptimalConditional D) (C₁ : ℕ) :
    ∃ b : ℕ, ∀ (x₁ x₂ z v : BitString),
      natCondK D v (pairCode x₁ z) ≤
        logSlack C₁ (natK D (pairCode (pairCode x₁ x₂) z)) →
      natCondK D v (pairCode x₂ z) ≤
        logSlack C₁ (natK D (pairCode (pairCode x₁ x₂) z)) →
      natCondK D (pairCode x₁ v) z ≤
        b * (natK D (pairCode (pairCode x₁ x₂) z) + 1) ∧
      natCondK D (pairCode x₂ v) z ≤
        b * (natK D (pairCode (pairCode x₁ x₂) z) + 1) := by
  obtain ⟨cChain, hChain⟩ :=
    Kolmogorov.condK_pairCode_chain_upper_values D hD
  obtain ⟨cCond, hCond⟩ := condK_le_plainK D hD
  obtain ⟨cMap₁, hMap₁⟩ := plainK_map_le D hD
    (decodeFirst ∘ decodeFirst)
    (decodeFirst_computable.comp decodeFirst_computable)
  obtain ⟨cMap₂, hMap₂⟩ := plainK_map_le D hD
    (decodeSecond ∘ decodeFirst)
    (decodeSecond_computable.comp decodeFirst_computable)
  obtain ⟨cTwice, hTwice⟩ := logSlack_le_add_const (2 * cChain)
  let cBase := max cMap₁ cMap₂ + cCond
  let b := 2 * (C₁ + 1) + 2 * (cBase + C₁) + cTwice + 1
  refine ⟨b, ?_⟩
  intro x₁ x₂ z v hv₁ hv₂
  let N := natK D (pairCode (pairCode x₁ x₂) z)
  let k₁ := natCondK D x₁ z
  let k₂ := natCondK D x₂ z
  let kv₁ := natCondK D v (pairCode x₁ z)
  let kv₂ := natCondK D v (pairCode x₂ z)
  let kp₁ := natCondK D (pairCode x₁ v) z
  let kp₂ := natCondK D (pairCode x₂ v) z
  have hPlain₁ : natK D x₁ ≤ N + cMap₁ := by
    have h := hMap₁ (pairCode (pairCode x₁ x₂) z)
    have h' : plainK D x₁ ≤
        plainK D (pairCode (pairCode x₁ x₂) z) + (cMap₁ : ℕ∞) := by
      simpa [Function.comp_apply, decodeFirst_pairCode] using h
    have hx := commonInfo_le_mutualInfo_hasPlainValue D hD x₁
    have hN := commonInfo_le_mutualInfo_hasPlainValue D hD
      (pairCode (pairCode x₁ x₂) z)
    rw [hx, hN] at h'
    exact_mod_cast h'
  have hPlain₂ : natK D x₂ ≤ N + cMap₂ := by
    have h := hMap₂ (pairCode (pairCode x₁ x₂) z)
    have h' : plainK D x₂ ≤
        plainK D (pairCode (pairCode x₁ x₂) z) + (cMap₂ : ℕ∞) := by
      simpa [Function.comp_apply, decodeSecond_pairCode, decodeFirst_pairCode] using h
    have hx := commonInfo_le_mutualInfo_hasPlainValue D hD x₂
    have hN := commonInfo_le_mutualInfo_hasPlainValue D hD
      (pairCode (pairCode x₁ x₂) z)
    rw [hx, hN] at h'
    exact_mod_cast h'
  have hCond₁ : k₁ ≤ natK D x₁ + cCond := by
    have h := hCond x₁ z
    rw [condK_le_add_condMutualInfo_value D hD x₁ z,
      commonInfo_le_mutualInfo_hasPlainValue D hD x₁] at h
    exact_mod_cast h
  have hCond₂ : k₂ ≤ natK D x₂ + cCond := by
    have h := hCond x₂ z
    rw [condK_le_add_condMutualInfo_value D hD x₂ z,
      commonInfo_le_mutualInfo_hasPlainValue D hD x₂] at h
    exact_mod_cast h
  have hk₁ : k₁ ≤ N + cBase := by
    dsimp [k₁, cBase]
    calc
      natCondK D x₁ z ≤ natK D x₁ + cCond := hCond₁
      _ ≤ N + cMap₁ + cCond := Nat.add_le_add_right hPlain₁ cCond
      _ ≤ N + (max cMap₁ cMap₂ + cCond) := by omega
  have hk₂ : k₂ ≤ N + cBase := by
    dsimp [k₂, cBase]
    calc
      natCondK D x₂ z ≤ natK D x₂ + cCond := hCond₂
      _ ≤ N + cMap₂ + cCond := Nat.add_le_add_right hPlain₂ cCond
      _ ≤ N + (max cMap₁ cMap₂ + cCond) := by omega
  have hkp₁ : kp₁ ≤ k₁ + kv₁ + logSlack cChain (kp₁ + 1) := by
    have h₁ := hChain x₁ v z k₁ kv₁ kp₁
      (condK_le_add_condMutualInfo_value D hD x₁ z)
      (condK_le_add_condMutualInfo_value D hD v (pairCode x₁ z))
      (condK_le_add_condMutualInfo_value D hD (pairCode x₁ v) z)
    simpa [k₁, kv₁, kp₁] using h₁
  have hkp₂ : kp₂ ≤ k₂ + kv₂ + logSlack cChain (kp₂ + 1) := by
    have h₂ := hChain x₂ v z k₂ kv₂ kp₂
      (condK_le_add_condMutualInfo_value D hD x₂ z)
      (condK_le_add_condMutualInfo_value D hD v (pairCode x₂ z))
      (condK_le_add_condMutualInfo_value D hD (pairCode x₂ v) z)
    simpa [k₂, kv₂, kp₂] using h₂
  have hTwice₁ : 2 * logSlack cChain (kp₁ + 1) ≤ kp₁ + 1 + cTwice := by
    have h := hTwice (kp₁ + 1)
    simpa [Kolmogorov.logSlack_nsmul] using h
  have hTwice₂ : 2 * logSlack cChain (kp₂ + 1) ≤ kp₂ + 1 + cTwice := by
    have h := hTwice (kp₂ + 1)
    simpa [Kolmogorov.logSlack_nsmul] using h
  have hAbsorb₁ : kp₁ ≤ 2 * (N + cBase + logSlack C₁ N) + cTwice + 1 := by
    have hv : kv₁ ≤ logSlack C₁ N := by simpa [kv₁, N] using hv₁
    omega
  have hAbsorb₂ : kp₂ ≤ 2 * (N + cBase + logSlack C₁ N) + cTwice + 1 := by
    have hv : kv₂ ≤ logSlack C₁ N := by simpa [kv₂, N] using hv₂
    omega
  have hSlackN : logSlack C₁ N ≤ C₁ * N + C₁ :=
    Kolmogorov.logSlack_le_self_linear C₁ N
  let A := 2 * (C₁ + 1)
  let B := 2 * (cBase + C₁) + cTwice + 1
  have hA : A ≤ b := by dsimp [A, B, b]; omega
  have hB : B ≤ b := by dsimp [A, B, b]; omega
  have hFinal₁ : kp₁ ≤ b * (N + 1) := by
    have hLin : kp₁ ≤ A * N + B := by
      calc
        kp₁ ≤ 2 * (N + cBase + logSlack C₁ N) + cTwice + 1 := hAbsorb₁
        _ ≤ 2 * (N + cBase + (C₁ * N + C₁)) + cTwice + 1 := by omega
        _ = A * N + B := by dsimp [A, B]; ring
    have hAN : A * N ≤ b * N := Nat.mul_le_mul_right N hA
    calc
      kp₁ ≤ A * N + B := hLin
      _ ≤ b * N + b := Nat.add_le_add hAN hB
      _ = b * (N + 1) := by rw [Nat.mul_add]; simp
  have hFinal₂ : kp₂ ≤ b * (N + 1) := by
    have hLin : kp₂ ≤ A * N + B := by
      calc
        kp₂ ≤ 2 * (N + cBase + logSlack C₁ N) + cTwice + 1 := hAbsorb₂
        _ ≤ 2 * (N + cBase + (C₁ * N + C₁)) + cTwice + 1 := by omega
        _ = A * N + B := by dsimp [A, B]; ring
    have hAN : A * N ≤ b * N := Nat.mul_le_mul_right N hA
    calc
      kp₂ ≤ A * N + B := hLin
      _ ≤ b * N + b := Nat.add_le_add hAN hB
      _ = b * (N + 1) := by rw [Nat.mul_add]; simp
  exact ⟨by simpa [N, kp₁] using hFinal₁, by simpa [N, kp₂] using hFinal₂⟩

/-- The chain rule, profile inequalities for one coordinate, and symmetry of
information bound the conditional complexity of the extracted string. -/
private theorem conjecture2_of_conjecture3_symmetry
    (D : Map) (hD : isOptimalConditional D) (C₁ c₀ b : ℕ) :
    ∃ c : ℕ, ∀ (x z v w₀ : BitString) (N : ℕ),
      natCondK D v (pairCode x z) ≤ logSlack C₁ N →
      natCondK D x z ≤ natK D x + logSlack c₀ N →
      natK D (pairCode x w₀) ≤
        natCondK D (pairCode x v) z + logSlack c₀ N →
      natCondK D (pairCode x v) z ≤ b * (N + 1) →
      natCondK D w₀ x ≤ logSlack c N := by
  obtain ⟨cChain, hChain⟩ :=
    Kolmogorov.condK_pairCode_symmetryOfInformation_values D hD
  obtain ⟨cPlain, hPlain⟩ :=
    Kolmogorov.pairPlainK_symmetryOfInformation_values D hD
  obtain ⟨cChainFold, hChainFold⟩ := logSlack_linear_bound cChain b (b + 1)
  obtain ⟨cPlainFold, hPlainFold⟩ :=
    logSlack_linear_bound cPlain (b + c₀) (b + c₀ + 1)
  let c := 2 * c₀ + C₁ + cChainFold + cPlainFold
  refine ⟨c, fun x z v w₀ N hv hs hp hb => ?_⟩
  let kx := natK D x
  let kxz := natCondK D x z
  let kvxz := natCondK D v (pairCode x z)
  let kpairz := natCondK D (pairCode x v) z
  let kpair := natK D (pairCode x w₀)
  let kwx := natCondK D w₀ x
  have hx : HasPlainComplexityValue D x kx := commonInfo_le_mutualInfo_hasPlainValue D hD x
  have hxz : HasPlainConditionalComplexityValue D x z kxz :=
    condK_le_add_condMutualInfo_value D hD x z
  have hvxz : HasPlainConditionalComplexityValue D v (pairCode x z) kvxz :=
    condK_le_add_condMutualInfo_value D hD v (pairCode x z)
  have hpairz : HasPlainConditionalComplexityValue D (pairCode x v) z kpairz :=
    condK_le_add_condMutualInfo_value D hD (pairCode x v) z
  have hpair : HasPlainComplexityValue D (pairCode x w₀) kpair :=
    commonInfo_le_mutualInfo_hasPlainValue D hD (pairCode x w₀)
  have hwx : HasPlainConditionalComplexityValue D w₀ x kwx :=
    condK_le_add_condMutualInfo_value D hD w₀ x
  have hChainNat := hChain x v z kxz kvxz kpairz hxz hvxz hpairz
  have hPlainNat := hPlain x w₀ kx kwx kpair hx hwx hpair
  have hCondArg : kpairz + 1 ≤ b * N + (b + 1) := by
    calc
      kpairz + 1 ≤ b * (N + 1) + 1 := Nat.add_le_add_right hb 1
      _ = b * N + (b + 1) := by ring
  have hCondLog : logSlack cChain (kpairz + 1) ≤ logSlack cChainFold N := by
    calc
      logSlack cChain (kpairz + 1) ≤ logSlack cChain (b * N + (b + 1)) :=
        logSlack_mono_right cChain hCondArg
      _ ≤ logSlack cChainFold N := hChainFold N
  have hBits : (Nat.bits N).length ≤ N := length_natBits_le N
  have hProfileSlack : logSlack c₀ N ≤ c₀ * (N + 1) := by
    unfold logSlack
    calc
      c₀ * (Nat.bits N).length + c₀ ≤ c₀ * N + c₀ := by
        exact Nat.add_le_add_right (Nat.mul_le_mul_left c₀ hBits) c₀
      _ = c₀ * (N + 1) := by ring
  have hPairBound : kpair ≤ (b + c₀) * (N + 1) := by
    dsimp [kpair, kpairz] at hp hb ⊢
    calc
      natK D (pairCode x w₀) ≤
          natCondK D (pairCode x v) z + logSlack c₀ N := hp
      _ ≤ b * (N + 1) + c₀ * (N + 1) := Nat.add_le_add hb hProfileSlack
      _ = (b + c₀) * (N + 1) := by rw [Nat.add_mul]
  have hPlainArg : kpair + 1 ≤ (b + c₀) * N + (b + c₀ + 1) := by
    calc
      kpair + 1 ≤ (b + c₀) * (N + 1) + 1 := Nat.add_le_add_right hPairBound 1
      _ = (b + c₀) * N + (b + c₀ + 1) := by ring
  have hPlainLog : logSlack cPlain (kpair + 1) ≤ logSlack cPlainFold N := by
    calc
      logSlack cPlain (kpair + 1) ≤
          logSlack cPlain ((b + c₀) * N + (b + c₀ + 1)) :=
        logSlack_mono_right cPlain hPlainArg
      _ ≤ logSlack cPlainFold N := hPlainFold N
  have hChainUpper : kpairz ≤ kxz + kvxz + logSlack cChainFold N := by
    exact hChainNat.1.trans
      (Nat.add_le_add_left hCondLog (kxz + kvxz))
  have hPlainUpper : kx + kwx ≤ kpair + logSlack cPlainFold N := by
    exact hPlainNat.2.trans (Nat.add_le_add_left hPlainLog kpair)
  have hMain : kx + kwx ≤
      kx + (logSlack c₀ N + logSlack C₁ N + logSlack cChainFold N +
        logSlack c₀ N + logSlack cPlainFold N) := by
    have h1 : kx + kwx ≤
        (kxz + kvxz + logSlack cChainFold N) +
          logSlack c₀ N + logSlack cPlainFold N := by
      calc
        kx + kwx ≤ kpair + logSlack cPlainFold N := hPlainUpper
        _ ≤ (kpairz + logSlack c₀ N) + logSlack cPlainFold N := by omega
        _ ≤ (kxz + kvxz + logSlack cChainFold N) +
            logSlack c₀ N + logSlack cPlainFold N := by omega
    omega
  have hSlack : logSlack c₀ N + logSlack C₁ N + logSlack cChainFold N +
      logSlack c₀ N + logSlack cPlainFold N ≤ logSlack c N := by
    dsimp [c]
    rw [← logSlack_add_constants c₀ C₁ N,
      ← logSlack_add_constants (c₀ + C₁) cChainFold N,
      ← logSlack_add_constants (c₀ + C₁ + cChainFold) c₀ N,
      ← logSlack_add_constants (c₀ + C₁ + cChainFold + c₀) cPlainFold N]
    apply logSlack_mono_left
    omega
  have hResult : kwx ≤ logSlack c N := by omega
  simpa [kwx] using hResult

/-- The pair and singleton profile coordinates, together with symmetry of
information, bound the conditional complexities of the unrelativized witness. -/
private theorem conjecture2_of_conjecture3_conditional
    (D : Map) (hD : isOptimalConditional D) (C₁ c₀ : ℕ) :
    ∃ c : ℕ, ∀ (x₁ x₂ z v w₀ : BitString),
      natCondK D v (pairCode x₁ z) ≤
        logSlack C₁ (natK D (pairCode (pairCode x₁ x₂) z)) →
      natCondK D v (pairCode x₂ z) ≤
        logSlack C₁ (natK D (pairCode (pairCode x₁ x₂) z)) →
      ProfileWithin
        (subKRel D
          (Fin.append (fun i : Fin 2 => if i.val = 0 then x₁ else x₂)
            (fun _ : Fin 1 => v)) z)
        (subK D
          (Fin.append (fun i : Fin 2 => if i.val = 0 then x₁ else x₂)
            (fun _ : Fin 1 => w₀)))
        (logSlack c₀ (natK D (pairCode (pairCode x₁ x₂) z))) →
      natCondK D w₀ x₁ ≤
        logSlack c (natK D (pairCode (pairCode x₁ x₂) z)) ∧
      natCondK D w₀ x₂ ≤
        logSlack c (natK D (pairCode (pairCode x₁ x₂) z)) := by
  obtain ⟨cProfile, hProfile⟩ :=
    conjecture2_of_conjecture3_profile_coordinates
      D hD c₀
  obtain ⟨b, hPairBound⟩ :=
    conjecture2_of_conjecture3_pair_bound
      D hD C₁
  obtain ⟨c, hSymmetry⟩ :=
    conjecture2_of_conjecture3_symmetry
      D hD C₁ cProfile b
  refine ⟨c, ?_⟩
  intro x₁ x₂ z v w₀ hv₁ hv₂ hProfile₀
  obtain ⟨⟨hs₁, hp₁⟩, ⟨hs₂, hp₂⟩⟩ := hProfile x₁ x₂ z v w₀ hProfile₀
  obtain ⟨hb₁, hb₂⟩ := hPairBound x₁ x₂ z v hv₁ hv₂
  constructor
  · exact hSymmetry x₁ z v w₀ (natK D (pairCode (pairCode x₁ x₂) z))
      hv₁ hs₁ hp₁ hb₁
  · exact hSymmetry x₂ z v w₀ (natK D (pairCode (pairCode x₁ x₂) z))
      hv₂ hs₂ hp₂ hb₂

/-- Conjecture 3 applied to the two-coordinate tuple and the extracted oracle
string gives a string with the desired conditional complexities and logarithmic
possible deficit in its plain complexity. -/
private theorem conjecture2_of_conjecture3_profile_witness
    (D : Map) (hD : isOptimalConditional D) (hC3 : Conjecture3 D) (C₁ : ℕ) :
    ∃ c : ℕ, ∀ (x₁ x₂ z : BitString) (q : ℕ),
      MutualInfoLe D (pairCode x₁ x₂) z
          (logSlack C₁ (natK D (pairCode (pairCode x₁ x₂) z))) →
      CommonInfoExtractableRel D x₁ x₂ z q
          (logSlack C₁ (natK D (pairCode (pairCode x₁ x₂) z))) →
      ∃ w₀ : BitString,
        q ≤ natK D w₀ + logSlack c (natK D (pairCode (pairCode x₁ x₂) z)) ∧
        natK D w₀ ≤ c * (natK D (pairCode (pairCode x₁ x₂) z) + 1) ∧
        natCondK D w₀ x₁ ≤ logSlack c (natK D (pairCode (pairCode x₁ x₂) z)) ∧
        natCondK D w₀ x₂ ≤ logSlack c (natK D (pairCode (pairCode x₁ x₂) z)) := by
  obtain ⟨c₀, hProfile⟩ :=
    conjecture2_of_conjecture3_c3_profile D hD hC3 C₁
  obtain ⟨c₁, hPlain⟩ :=
    conjecture2_of_conjecture3_profile_plain_complexity
      D hD C₁ c₀
  obtain ⟨c₂, hConditional⟩ :=
    conjecture2_of_conjecture3_conditional
      D hD C₁ c₀
  let c := max c₁ c₂
  refine ⟨c, ?_⟩
  intro x₁ x₂ z q hMI hExtract
  obtain ⟨v, w₀, hqv, hv1, hv2, hProfile₀⟩ :=
    hProfile x₁ x₂ z q hMI hExtract
  have hPlain := hPlain x₁ x₂ z v w₀ q hqv hv1 hProfile₀
  have hConditional := hConditional x₁ x₂ z v w₀ hv1 hv2 hProfile₀
  refine ⟨w₀, ?_, ?_, ?_, ?_⟩
  · exact hPlain.1.trans (Nat.add_le_add_left
      (logSlack_mono_left (Nat.le_max_left c₁ c₂)
        (natK D (pairCode (pairCode x₁ x₂) z))) _)
  · exact Nat.le_trans hPlain.2 (Nat.mul_le_mul_right _ (Nat.le_max_left c₁ c₂))
  · exact hConditional.1.trans (logSlack_mono_left (Nat.le_max_right c₁ c₂)
      (natK D (pairCode (pairCode x₁ x₂) z)))
  · exact hConditional.2.trans (logSlack_mono_left (Nat.le_max_right c₁ c₂)
      (natK D (pairCode (pairCode x₁ x₂) z)))

/-- There is a logarithmic padding coefficient that absorbs the symmetry
overhead at the complexity of the resulting pair. -/
private theorem conjecture2_of_conjecture3_absorb_log_overhead
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

/-- The plain complexity of a coded pair is bounded by the complexity of its
first component, the length of its second component, and an additive constant. -/
private theorem conjecture2_of_conjecture3_pair_upper
    (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ (w₀ s : BitString),
      natK D (pairCode w₀ s) ≤ 3 * natK D w₀ + s.length + c := by
  obtain ⟨cPair, hPair⟩ := plainK_pair_le_add_two_log D hD
  obtain ⟨cLen, hLen⟩ := plainK_le_length D hD
  have hPlainFinite (x : BitString) : plainK D x ≠ ⊤ := by
    exact Kolmogorov.ne_top_of_le_natCast_add (hLen x)
  have hPlainValue (x : BitString) : plainK D x = (natK D x : ℕ∞) := by
    change plainK D x = ((plainK D x).toNat : ℕ∞)
    exact (ENat.natCast_toNat (hPlainFinite x)).symm
  refine ⟨cPair + cLen, fun w₀ s => ?_⟩
  have hPairCast :
      (natK D (pairCode w₀ s) : ℕ∞) ≤
        (natK D w₀ : ℕ∞) + (natK D s : ℕ∞) +
          ((2 * Nat.log 2 (natK D w₀) + cPair : ℕ) : ℕ∞) := by
    simpa [Kolmogorov.cPair, Kolmogorov.cVal, hPlainValue] using hPair w₀ s
  have hPairNat :
      natK D (pairCode w₀ s) ≤ natK D w₀ + natK D s +
        (2 * Nat.log 2 (natK D w₀) + cPair) := by
    exact_mod_cast hPairCast
  have hLenCast : (natK D s : ℕ∞) ≤ (s.length + cLen : ℕ∞) := by
    have h := hLen s
    rw [hPlainValue s] at h
    simpa [programLength] using h
  have hLenNat : natK D s ≤ s.length + cLen := by
    exact_mod_cast hLenCast
  have hLog : Nat.log 2 (natK D w₀) ≤ natK D w₀ := Nat.log_le_self 2 _
  nlinarith [hPairNat, hLog, hLenNat]

/-- An incompressible padding string makes the coded pair reach the requested
plain-complexity threshold using logarithmically many bits. -/
private theorem conjecture2_of_conjecture3_plain_padding
    (D : Map) (hD : isOptimalConditional D) (a b : ℕ) :
    ∃ c : ℕ, ∀ (w₀ : BitString) (q N : ℕ),
      q ≤ natK D w₀ + logSlack a N →
      natK D w₀ ≤ b * (N + 1) →
      ∃ s : BitString,
        s.length ≤ logSlack c N ∧ q ≤ natK D (pairCode w₀ s) := by
  obtain ⟨cLower, hLower⟩ := pairPlainK_chain_lower_values D hD
  obtain ⟨cUpper, hUpper⟩ :=
    conjecture2_of_conjecture3_pair_upper D hD
  let M := 3 * b + cUpper + 1
  obtain ⟨cPad, hAbsorb⟩ :=
    conjecture2_of_conjecture3_absorb_log_overhead a cLower M
  refine ⟨cPad, fun w₀ q N hq hK => ?_⟩
  let r := logSlack cPad N
  obtain ⟨s, hsLen, hsIncomp⟩ := exists_incompressible_string D w₀ r
  have hsIncompNat : r ≤ natCondK D s w₀ := by
    rw [← ENat.natCast_toNat (condK_ne_top_of_optimal D hD s w₀)] at hsIncomp
    exact_mod_cast hsIncomp
  have hPairBound : natK D (pairCode w₀ s) ≤ M * (N + 1) + r := by
    have h0 := hUpper w₀ s
    have hK3 := Nat.mul_le_mul_left 3 hK
    have hN : 1 ≤ N + 1 := by omega
    dsimp [M]
    nlinarith [h0, hK3, hsLen]
  have hPairPlus :
      natK D (pairCode w₀ s) + 1 ≤ M * (N + 1) + r + 1 := by
    omega
  have hLowerNat :
      natK D w₀ + r ≤ natK D (pairCode w₀ s) +
        logSlack cLower (natK D (pairCode w₀ s) + 1) := by
    have hPlainFinite (x : BitString) : plainK D x ≠ ⊤ := by
      obtain ⟨c, hc⟩ := plainK_le_length D hD
      exact Kolmogorov.ne_top_of_le_natCast_add (hc x)
    have hPlainValue (x : BitString) : HasPlainComplexityValue D x (natK D x) := by
      unfold HasPlainComplexityValue natK
      exact (ENat.natCast_toNat (hPlainFinite x)).symm
    have h := hLower w₀ s
      (natK D w₀) (natCondK D s w₀) (natK D (pairCode w₀ s))
      (hPlainValue w₀)
      (condK_le_add_condMutualInfo_value D hD s w₀)
      (hPlainValue (pairCode w₀ s))
    omega
  have hError :
      logSlack cLower (natK D (pairCode w₀ s) + 1) ≤
        logSlack cLower (M * (N + 1) + r + 1) :=
    logSlack_mono_right cLower hPairPlus
  have hEnough := hAbsorb N
  refine ⟨s, ?_, ?_⟩
  · simpa [r] using hsLen.le
  · dsimp [r] at hPairBound hPairPlus hLowerNat hError hEnough hsIncompNat
    omega

/-- The conditional cost of adjoining a short literal string is logarithmic
under a linear bound on the complexity budget. -/
private theorem conjecture2_of_conjecture3_conditional_cost
    (D : Map) (hD : isOptimalConditional D) (a b : ℕ) :
    ∃ c : ℕ, ∀ (x w₀ s : BitString) (N : ℕ),
      natK D w₀ ≤ b * (N + 1) →
      s.length ≤ logSlack a N →
      natCondK D (pairCode w₀ s) x ≤ natCondK D w₀ x + logSlack c N := by
  obtain ⟨cPair, hPair⟩ :=
    conjecture2_of_conjecture3_pair_upper D hD
  obtain ⟨cChain, hChain⟩ := condK_pairCode_chain_upper_values D hD
  obtain ⟨cCond, hCond⟩ := condK_le_plainK D hD
  obtain ⟨cLen, hLen⟩ := plainK_le_length D hD
  let B := 3 * b + a + cPair + 1
  obtain ⟨cFold, hFold⟩ := logSlack_linear_bound cChain B (B + cCond + 1)
  refine ⟨a + (cFold + cLen + cCond), fun x w₀ s N hK hLenS => ?_⟩
  have hPairBound : natK D (pairCode w₀ s) ≤ B * N + B := by
    have h0 := hPair w₀ s
    have hS : s.length ≤ a * N + a :=
      hLenS.trans (logSlack_le_self_linear a N)
    have hK3 := Nat.mul_le_mul_left 3 hK
    dsimp [B]
    nlinarith [h0, hS, hK3]
  have hPairPlus :
      natK D (pairCode w₀ s) + 1 ≤ B * N + (B + 1) := by
    calc
      natK D (pairCode w₀ s) + 1 ≤ (B * N + B) + 1 := Nat.add_le_add_right hPairBound 1
      _ = B * N + (B + 1) := by omega
  have hPlainFinite (y : BitString) : plainK D y ≠ ⊤ := by
    exact Kolmogorov.ne_top_of_le_natCast_add (hLen y)
  have hPlainValue (y : BitString) : plainK D y = (natK D y : ℕ∞) := by
    change plainK D y = ((plainK D y).toNat : ℕ∞)
    exact (ENat.natCast_toNat (hPlainFinite y)).symm
  have hCondPairPlain :
      natCondK D (pairCode w₀ s) x ≤ natK D (pairCode w₀ s) + cCond := by
    have h := hCond (pairCode w₀ s) x
    rw [condK_le_add_condMutualInfo_value D hD (pairCode w₀ s) x,
      hPlainValue (pairCode w₀ s)] at h
    exact_mod_cast h
  have hCondPairPlus :
      natCondK D (pairCode w₀ s) x + 1 ≤ B * N + (B + cCond + 1) := by
    have h0 := Nat.add_le_add_right hCondPairPlain 1
    omega
  have hFolded :
      logSlack cChain (natCondK D (pairCode w₀ s) x + 1) ≤ logSlack cFold N :=
    logSlack_le_of_linear_bound hFold hCondPairPlus
  have hLiteral : natK D s ≤ s.length + cLen := by
    have h : (natK D s : ℕ∞) ≤ (s.length + cLen : ℕ∞) := by
      rw [← hPlainValue s]
      calc
        plainK D s ≤ (programLength s : ℕ∞) + cLen := hLen s
        _ = (s.length + cLen : ℕ∞) := by simp [programLength]
    exact_mod_cast h
  have hCondLiteral :
      natCondK D s (pairCode w₀ x) ≤ natK D s + cCond := by
    have h := hCond s (pairCode w₀ x)
    rw [
      condK_le_add_condMutualInfo_value D hD s (pairCode w₀ x),
      hPlainValue s] at h
    exact_mod_cast h
  have hCondLiteral' :
      natCondK D s (pairCode w₀ x) ≤ s.length + cLen + cCond := by
    calc
      natCondK D s (pairCode w₀ x) ≤ natK D s + cCond := hCondLiteral
      _ ≤ s.length + cLen + cCond := Nat.add_le_add_right hLiteral cCond
  have hChainResult := hChain w₀ s x
    (natCondK D w₀ x)
    (natCondK D s (pairCode w₀ x))
    (natCondK D (pairCode w₀ s) x)
    (condK_le_add_condMutualInfo_value D hD w₀ x)
    (condK_le_add_condMutualInfo_value D hD s (pairCode w₀ x))
    (condK_le_add_condMutualInfo_value D hD (pairCode w₀ s) x)
  have hBeforeFold :
      natCondK D (pairCode w₀ s) x ≤
        natCondK D w₀ x + s.length +
          cLen + cCond + logSlack cFold N := by
    omega
  calc
    natCondK D (pairCode w₀ s) x ≤
        natCondK D w₀ x + s.length + cLen + cCond + logSlack cFold N := hBeforeFold
    _ ≤ natCondK D w₀ x + logSlack a N + logSlack (cFold + cLen + cCond) N := by
      have hadd := logSlack_add_nat_le cFold (cLen + cCond) N
      have hadd' : logSlack cFold N + (cLen + cCond) ≤
          logSlack (cFold + cLen + cCond) N := by
        simpa [Nat.add_assoc] using hadd
      omega
    _ = natCondK D w₀ x + logSlack (a + (cFold + cLen + cCond)) N := by
      calc
        natCondK D w₀ x + logSlack a N + logSlack (cFold + cLen + cCond) N =
            natCondK D w₀ x +
              (logSlack a N + logSlack (cFold + cLen + cCond) N) := by ac_rfl
        _ = natCondK D w₀ x + logSlack (a + (cFold + cLen + cCond)) N := by
          rw [logSlack_add_const]

/-- A string can be padded by logarithmically many bits to reach the requested
plain-complexity threshold while keeping the conditional cost logarithmic. -/
private theorem conjecture2_of_conjecture3_pad
    (D : Map) (hD : isOptimalConditional D) (a b : ℕ) :
    ∃ c : ℕ, ∀ (x₁ x₂ w₀ : BitString) (q N : ℕ),
      q ≤ natK D w₀ + logSlack a N →
      natK D w₀ ≤ b * (N + 1) →
      ∃ w : BitString,
        q ≤ natK D w ∧
        natCondK D w x₁ ≤ natCondK D w₀ x₁ + logSlack c N ∧
        natCondK D w x₂ ≤ natCondK D w₀ x₂ + logSlack c N := by
  obtain ⟨cPad, hPad⟩ :=
    conjecture2_of_conjecture3_plain_padding D hD a b
  obtain ⟨cCond, hCond⟩ :=
    conjecture2_of_conjecture3_conditional_cost D hD cPad b
  refine ⟨cPad + cCond, fun x₁ x₂ w₀ q N hq hK => ?_⟩
  obtain ⟨s, hsLen, hq'⟩ := hPad w₀ q N hq hK
  have hCond₁ := hCond x₁ w₀ s N hK hsLen
  have hCond₂ := hCond x₂ w₀ s N hK hsLen
  refine ⟨pairCode w₀ s, hq', ?_, ?_⟩
  · calc
      natCondK D (pairCode w₀ s) x₁ ≤
          natCondK D w₀ x₁ + logSlack cCond N := hCond₁
      _ ≤ natCondK D w₀ x₁ + logSlack (cPad + cCond) N := by
        gcongr
        exact logSlack_mono_left (by omega) N
  · calc
      natCondK D (pairCode w₀ s) x₂ ≤
          natCondK D w₀ x₂ + logSlack cCond N := hCond₂
      _ ≤ natCondK D w₀ x₂ + logSlack (cPad + cCond) N := by
        gcongr
        exact logSlack_mono_left (by omega) N

/-- Conjecture 2 is a special case of Conjecture 3 (Section 2): apply Conjecture 3 to
`x̄ = ⟨x₁, x₂⟩` and `ȳ = ⟨v⟩`, and pad the string obtained by `O(log N)` random bits. -/
theorem conjecture2_of_conjecture3 (D : Map) (hD : isOptimalConditional D) :
    Conjecture3 D → Conjecture2 D := by
  intro hC3 C₁
  obtain ⟨c₁, hWitness⟩ :=
    conjecture2_of_conjecture3_profile_witness D hD hC3 C₁
  obtain ⟨c₂, hPad⟩ := conjecture2_of_conjecture3_pad D hD c₁ c₁
  refine ⟨c₁ + c₂, ?_⟩
  intro x₁ x₂ z q hMI hExtract
  have hN := hWitness x₁ x₂ z q hMI hExtract
  obtain ⟨w₀, hq₀, hw₀, hx₁₀, hx₂₀⟩ := hN
  have hPadResult := hPad x₁ x₂ w₀ q
    (natK D (pairCode (pairCode x₁ x₂) z)) hq₀ hw₀
  obtain ⟨w, hq, hx₁, hx₂⟩ := hPadResult
  refine ⟨w, hq, ?_, ?_⟩
  · calc
      natCondK D w x₁ ≤ natCondK D w₀ x₁ + logSlack c₂
          (natK D (pairCode (pairCode x₁ x₂) z)) := hx₁
      _ ≤ logSlack c₁ (natK D (pairCode (pairCode x₁ x₂) z)) + logSlack c₂
          (natK D (pairCode (pairCode x₁ x₂) z)) := Nat.add_le_add_right hx₁₀ _
      _ = logSlack (c₁ + c₂) (natK D (pairCode (pairCode x₁ x₂) z)) := by
        simp [logSlack]
        ring
  · calc
      natCondK D w x₂ ≤ natCondK D w₀ x₂ + logSlack c₂
          (natK D (pairCode (pairCode x₁ x₂) z)) := hx₂
      _ ≤ logSlack c₁ (natK D (pairCode (pairCode x₁ x₂) z)) + logSlack c₂
          (natK D (pairCode (pairCode x₁ x₂) z)) := Nat.add_le_add_right hx₂₀ _
      _ = logSlack (c₁ + c₂) (natK D (pairCode (pairCode x₁ x₂) z)) := by
        simp [logSlack]
        ring


end Kolmogorov.Relativization
