/-
Copyright (c) 2026 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Relativization.Definitions
import KolmogorovMathlib.CommonInformation.ConditionalIndependence.Part01
import KolmogorovMathlib.Complexity.Information.MutualInformation
import KolmogorovMathlib.Complexity.ConditionalComplexity.AverageBounds.Expectation
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.SlackArith
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.ProfileCardinality
import KolmogorovMathlib.Foundation.EnumerationComplexity

/-!
# Oracle Stability

This module proves that finite tuple profiles remain stable under relativization. Its main
result, `lemma3_relativized`, bounds changes in conditional profile coordinates by changes in
whole-tuple complexity and logarithmic slack, formalizing Lemma 3 of Muchnik and Romashchenko.
-/

namespace Kolmogorov.Relativization
open Finset
variable {n m : ℕ}

/-- A fixed list of positions gives a computable projection between list codes. -/
private def lemma3_relativized_lower_partition_projectListCode
    (positions : List ℕ) (w : BitString) : BitString :=
  listCode (positions.map fun i => (decodeListCode w).getD i [])

private lemma lemma3_relativized_lower_partition_projectListCode_primrec
    (positions : List ℕ) :
    Primrec (lemma3_relativized_lower_partition_projectListCode
      positions) := by
  induction positions with
  | nil => exact Primrec.const []
  | cons i positions ih =>
      have hget : Primrec (fun w : BitString => (decodeListCode w).getD i []) :=
        (Primrec.list_getD ([] : BitString)).comp decodeListCode_primrec (Primrec.const i)
      exact Primrec.of_eq (CodedFiniteDistribution.pairCode_primrec.comp hget ih) (by
        intro w
        unfold lemma3_relativized_lower_partition_projectListCode
        rfl)

private lemma lemma3_relativized_lower_partition_projectListCode_computable
    (positions : List ℕ) :
    Computable (lemma3_relativized_lower_partition_projectListCode
      positions) :=
  (lemma3_relativized_lower_partition_projectListCode_primrec
    positions).to_comp

private def lemma3_relativized_lower_partition_positionsIn
    {k : ℕ} (S T : Finset (Fin k)) : List ℕ :=
  (T.sort (· ≤ ·)).map fun i => (S.sort (· ≤ ·)).idxOf i

private lemma lemma3_relativized_lower_partition_project_subtuple
    {k : ℕ} (u : Fin k → BitString) {S T : Finset (Fin k)} (hTS : T ⊆ S) :
    lemma3_relativized_lower_partition_projectListCode
        (lemma3_relativized_lower_partition_positionsIn S T)
        (subtupleCode u S) = subtupleCode u T := by
  unfold lemma3_relativized_lower_partition_positionsIn
    subtupleCode lemma3_relativized_lower_partition_projectListCode
  simp only [decodeListCode_listCode, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hiT : i ∈ T := by simpa using hi
  have hiS : i ∈ S := hTS hiT
  have hiSort : i ∈ S.sort (· ≤ ·) := by simpa
  simp [Function.comp_apply, List.getD_eq_getElem?_getD, List.getElem?_idxOf hiSort]

private lemma lemma3_relativized_lower_partition_nat_of_cond
    (D : Map) (hD : isOptimalConditional D) (a b a' b' : BitString) (c : ℕ)
    (h : condK D a b ≤ condK D a' b' + (c : ℕ∞)) :
    natCondK D a b ≤ natCondK D a' b' + c := by
  have hne := avgCond_condK_ne_top D hD a b
  have hne' := avgCond_condK_ne_top D hD a' b'
  change (condK D a b).toNat ≤ (condK D a' b').toNat + c
  have h' : ((condK D a b).toNat : ℕ∞) ≤
      (((condK D a' b').toNat + c : ℕ) : ℕ∞) := by
    calc
      ((condK D a b).toNat : ℕ∞) = condK D a b := ENat.natCast_toNat hne
      _ ≤ condK D a' b' + (c : ℕ∞) := h
      _ = ((condK D a' b').toNat : ℕ∞) + (c : ℕ∞) := by
        rw [ENat.natCast_toNat hne']
      _ = (((condK D a' b').toNat + c : ℕ) : ℕ∞) := by push_cast; rfl
  exact_mod_cast h'

private lemma lemma3_relativized_lower_partition_pair_computable
    (f g : BitString → BitString) (hf : Computable f) (hg : Computable g) :
    Computable (fun w : BitString => pairCode (f w) (g w)) :=
  pairCode_computable.comp (hf.pair hg)

/-- the pair of subtuples on two disjoint blocks is computable from their union. -/
private theorem lemma3_relativized_pair_from_union
    (D : Map) (hD : isOptimalConditional D) (k : ℕ) :
    ∃ c : ℕ, ∀ (u : Fin k → BitString) (z : BitString)
      (V W : Finset (Fin k)), Disjoint V W →
      natCondK D (pairCode (subtupleCode u W) (subtupleCode u V)) z ≤
        natCondK D (subtupleCode u (V ∪ W)) z + c := by
  classical
  have hFor : ∀ (V W : Finset (Fin k)), ∃ c : ℕ,
      ∀ (u : Fin k → BitString) (z : BitString), Disjoint V W →
        natCondK D (pairCode (subtupleCode u W) (subtupleCode u V)) z ≤
          natCondK D (subtupleCode u (V ∪ W)) z + c := by
    intro V W
    let pW := lemma3_relativized_lower_partition_positionsIn
      (V ∪ W) W
    let pV := lemma3_relativized_lower_partition_positionsIn
      (V ∪ W) V
    let f := fun w : BitString => pairCode
      (lemma3_relativized_lower_partition_projectListCode pW w)
      (lemma3_relativized_lower_partition_projectListCode pV w)
    have hfW : Computable
        (lemma3_relativized_lower_partition_projectListCode
        pW) := lemma3_relativized_lower_partition_projectListCode_computable pW
    have hfV : Computable
        (lemma3_relativized_lower_partition_projectListCode
        pV) := lemma3_relativized_lower_partition_projectListCode_computable pV
    have hf : Computable f :=
      lemma3_relativized_lower_partition_pair_computable _ _ hfW hfV
    obtain ⟨c, hc⟩ := condK_map_le D hD f hf
    refine ⟨c, fun u z _ => ?_⟩
    have h := hc (subtupleCode u (V ∪ W)) z
    have hW : W ⊆ V ∪ W := Finset.subset_union_right
    have hV : V ⊆ V ∪ W := Finset.subset_union_left
    change condK D (pairCode
      (lemma3_relativized_lower_partition_projectListCode pW
        (subtupleCode u (V ∪ W)))
      (lemma3_relativized_lower_partition_projectListCode pV
        (subtupleCode u (V ∪ W)))) z ≤ _ at h
    rw [lemma3_relativized_lower_partition_project_subtuple
        u hW,
      lemma3_relativized_lower_partition_project_subtuple
        u hV] at h
    exact lemma3_relativized_lower_partition_nat_of_cond
      D hD _ _ _ _ c h
  choose cPair hPair using hFor
  let c := Finset.univ.sup fun p : Finset (Fin k) × Finset (Fin k) => cPair p.1 p.2
  refine ⟨c, fun u z V W hVW => ?_⟩
  have h := hPair V W u z hVW
  have hc : cPair V W ≤ c := by
    change cPair V W ≤ Finset.univ.sup
      (fun p : Finset (Fin k) × Finset (Fin k) => cPair p.1 p.2)
    exact Finset.le_sup (f := fun p : Finset (Fin k) × Finset (Fin k) => cPair p.1 p.2)
      (Finset.mem_univ (V, W))
  change natCondK D (pairCode (subtupleCode u W) (subtupleCode u V)) z ≤
    natCondK D (subtupleCode u (V ∪ W)) z + c
  omega

/-- the whole-tuple code computes a subtuple and the pair of that subtuple with its complement. -/
private theorem lemma3_relativized_pair_from_tuple
    (D : Map) (hD : isOptimalConditional D) (k : ℕ) :
    ∃ c : ℕ, ∀ (u : Fin k → BitString) (z : BitString) (S : Finset (Fin k)),
      natCondK D (subtupleCode u S) z ≤ natCondK D (tupleCode u) z + c ∧
      natCondK D (pairCode (subtupleCode u S)
        (subtupleCode u (Finset.univ \ S))) z ≤ natCondK D (tupleCode u) z + c := by
  classical
  have hFor : ∀ S : Finset (Fin k), ∃ c : ℕ,
      ∀ (u : Fin k → BitString) (z : BitString),
        natCondK D (subtupleCode u S) z ≤ natCondK D (tupleCode u) z + c ∧
        natCondK D (pairCode (subtupleCode u S)
          (subtupleCode u (Finset.univ \ S))) z ≤ natCondK D (tupleCode u) z + c := by
    intro S
    let all : Finset (Fin k) := Finset.univ
    let pS := lemma3_relativized_lower_partition_positionsIn all S
    let pR := lemma3_relativized_lower_partition_positionsIn all
      (Finset.univ \ S)
    let fS := lemma3_relativized_lower_partition_projectListCode pS
    let fR := lemma3_relativized_lower_partition_projectListCode pR
    have hfS : Computable fS :=
      lemma3_relativized_lower_partition_projectListCode_computable pS
    have hfR : Computable fR :=
      lemma3_relativized_lower_partition_projectListCode_computable pR
    have hfPair : Computable (fun w : BitString => pairCode (fS w) (fR w)) :=
      lemma3_relativized_lower_partition_pair_computable fS fR hfS hfR
    obtain ⟨cSingle, hcSingle⟩ := condK_map_le D hD fS hfS
    obtain ⟨cPair, hcPair⟩ := condK_map_le D hD (fun w => pairCode (fS w) (fR w)) hfPair
    refine ⟨cSingle + cPair, fun u z => ?_⟩
    have hSingle := hcSingle (tupleCode u) z
    have hPair := hcPair (tupleCode u) z
    change condK D
      (lemma3_relativized_lower_partition_projectListCode pS
        (tupleCode u)) z ≤ _ at hSingle
    change condK D (pairCode
      (lemma3_relativized_lower_partition_projectListCode pS
        (tupleCode u))
      (lemma3_relativized_lower_partition_projectListCode pR
        (tupleCode u))) z ≤ _ at hPair
    have hSingle' : condK D (subtupleCode u S) z ≤
        condK D (tupleCode u) z + (cSingle : ℕ∞) := by
      rw [← subtupleCode_univ u] at hSingle
      rw [lemma3_relativized_lower_partition_project_subtuple
        u (Finset.subset_univ S)] at hSingle
      rw [subtupleCode_univ u] at hSingle
      exact hSingle
    have hPair' : condK D (pairCode (subtupleCode u S)
        (subtupleCode u (Finset.univ \ S))) z ≤
        condK D (tupleCode u) z + (cPair : ℕ∞) := by
      rw [← subtupleCode_univ u] at hPair
      rw [lemma3_relativized_lower_partition_project_subtuple
          u (Finset.subset_univ S),
        lemma3_relativized_lower_partition_project_subtuple
          u (Finset.subset_univ (Finset.univ \ S))] at hPair
      rw [subtupleCode_univ u] at hPair
      exact hPair
    constructor
    · have h := lemma3_relativized_lower_partition_nat_of_cond
        D hD _ _ _ _ cSingle hSingle'
      omega
    · have h := lemma3_relativized_lower_partition_nat_of_cond
        D hD _ _ _ _ cPair hPair'
      omega
  choose cS hS using hFor
  let c := Finset.univ.sup cS
  refine ⟨c, fun u z S => ?_⟩
  have h := hS S u z
  have hc : cS S ≤ c := by
    change cS S ≤ Finset.univ.sup cS
    exact Finset.le_sup (f := cS) (Finset.mem_univ S)
  constructor <;> omega

/-- the lower
conditional chain inequality for the partition `W, V, (V ∪ W)ᶜ`. -/
private theorem lemma3_relativized_lower_partition
    (D : Map) (hD : isOptimalConditional D) (k : ℕ) :
    ∃ c : ℕ, ∀ (u : Fin k → BitString) (z : BitString)
      (V W : Finset (Fin k)), Disjoint V W →
      let R := Finset.univ \ (V ∪ W)
      natCondK D (subtupleCode u W) z + subCondKRel D u z V W +
          natCondK D (subtupleCode u R) (pairCode (subtupleCode u (V ∪ W)) z) ≤
        natCondK D (tupleCode u) z +
          logSlack c (natCondK D (tupleCode u) z + 1) := by
  classical
  obtain ⟨cChain, hChain⟩ := condK_pairCode_chain_lower_values D hD
  obtain ⟨cUnion, hUnion⟩ :=
    lemma3_relativized_pair_from_union
      D hD k
  obtain ⟨cTuple, hTuple⟩ :=
    lemma3_relativized_pair_from_tuple
      D hD k
  obtain ⟨cFold, hFold⟩ := logSlack_absorb_of_le_linear cChain 1
    (cUnion + cTuple + 1)
  let C := cFold + cFold + cUnion + cTuple
  refine ⟨C, ?_⟩
  intro u z V W hVW
  let S := V ∪ W
  let R := Finset.univ \ S
  let n := natCondK D (tupleCode u) z
  obtain ⟨kW, hkW⟩ := exists_plainConditionalComplexityValue D hD
    (subtupleCode u W) z
  obtain ⟨kV, hkV⟩ := exists_plainConditionalComplexityValue D hD
    (subtupleCode u V) (pairCode (subtupleCode u W) z)
  obtain ⟨kp1, hkp1⟩ := exists_plainConditionalComplexityValue D hD
    (pairCode (subtupleCode u W) (subtupleCode u V)) z
  have hChain1 := hChain (subtupleCode u W) (subtupleCode u V) z
    kW kV kp1 hkW hkV hkp1
  have hkWNat : natCondK D (subtupleCode u W) z = kW := by
    change (condK D (subtupleCode u W) z).toNat = kW
    change condK D (subtupleCode u W) z = (kW : ℕ∞) at hkW
    rw [hkW]
    rfl
  have hkVNat : natCondK D (subtupleCode u V)
      (pairCode (subtupleCode u W) z) = kV := by
    change (condK D (subtupleCode u V) (pairCode (subtupleCode u W) z)).toNat = kV
    change condK D (subtupleCode u V) (pairCode (subtupleCode u W) z) =
      (kV : ℕ∞) at hkV
    rw [hkV]
    rfl
  have hkp1Nat : natCondK D
      (pairCode (subtupleCode u W) (subtupleCode u V)) z = kp1 := by
    change (condK D (pairCode (subtupleCode u W) (subtupleCode u V)) z).toNat = kp1
    change condK D (pairCode (subtupleCode u W) (subtupleCode u V)) z =
      (kp1 : ℕ∞) at hkp1
    rw [hkp1]
    rfl
  have hChain1' : natCondK D (subtupleCode u W) z +
      natCondK D (subtupleCode u V) (pairCode (subtupleCode u W) z) ≤
        kp1 + logSlack cChain (kp1 + 1) := by
    rw [hkWNat, hkVNat]
    exact hChain1
  obtain ⟨kUValue, hkU⟩ := exists_plainConditionalComplexityValue D hD
    (subtupleCode u S) z
  obtain ⟨kRValue, hkR⟩ := exists_plainConditionalComplexityValue D hD
    (subtupleCode u R) (pairCode (subtupleCode u S) z)
  obtain ⟨kp2, hkp2⟩ := exists_plainConditionalComplexityValue D hD
    (pairCode (subtupleCode u S) (subtupleCode u R)) z
  have hChain2 := hChain (subtupleCode u S) (subtupleCode u R) z
    kUValue kRValue kp2 hkU hkR hkp2
  have hUNat : natCondK D (subtupleCode u S) z = kUValue := by
    change (condK D (subtupleCode u S) z).toNat = kUValue
    change condK D (subtupleCode u S) z = (kUValue : ℕ∞) at hkU
    rw [hkU]
    rfl
  have hRNat : natCondK D (subtupleCode u R)
      (pairCode (subtupleCode u S) z) = kRValue := by
    change (condK D (subtupleCode u R) (pairCode (subtupleCode u S) z)).toNat = kRValue
    change condK D (subtupleCode u R) (pairCode (subtupleCode u S) z) =
      (kRValue : ℕ∞) at hkR
    rw [hkR]
    rfl
  have hkp2Nat : natCondK D
      (pairCode (subtupleCode u S) (subtupleCode u R)) z = kp2 := by
    change (condK D (pairCode (subtupleCode u S) (subtupleCode u R)) z).toNat = kp2
    change condK D (pairCode (subtupleCode u S) (subtupleCode u R)) z =
      (kp2 : ℕ∞) at hkp2
    rw [hkp2]
    rfl
  have hChain2' : natCondK D (subtupleCode u S) z +
      natCondK D (subtupleCode u R) (pairCode (subtupleCode u S) z) ≤
        kp2 + logSlack cChain (kp2 + 1) := by
    rw [hUNat, hRNat]
    exact hChain2
  have hParts := hTuple u z S
  have hUbound : natCondK D (subtupleCode u S) z ≤ n + cTuple := by
    simpa [n] using hParts.1
  have hPair1bound : kp1 ≤ natCondK D (subtupleCode u S) z + cUnion := by
    simpa [hkp1Nat] using hUnion u z V W hVW
  have hPair2bound : kp2 ≤ n + cTuple := by
    simpa [hkp2Nat, R, n] using hParts.2
  have hArg1 : kp1 + 1 ≤ n + (cUnion + cTuple + 1) := by omega
  have hArg2 : kp2 + 1 ≤ n + (cUnion + cTuple + 1) := by omega
  have hSlack1 := hFold n (kp1 + 1) (by omega)
  have hSlack2 := hFold n (kp2 + 1) (by omega)
  have hFirst : natCondK D (subtupleCode u W) z +
      natCondK D (subtupleCode u V) (pairCode (subtupleCode u W) z) ≤
        natCondK D (subtupleCode u S) z + cUnion + logSlack cFold n := by omega
  have hSecond : natCondK D (subtupleCode u S) z +
      natCondK D (subtupleCode u R) (pairCode (subtupleCode u S) z) ≤
        n + cTuple + logSlack cFold n := by omega
  have hSum : natCondK D (subtupleCode u W) z +
      natCondK D (subtupleCode u V) (pairCode (subtupleCode u W) z) +
      natCondK D (subtupleCode u R) (pairCode (subtupleCode u S) z) ≤
        n + cUnion + cTuple + logSlack cFold n + logSlack cFold n := by omega
  have hSlack : logSlack cFold n + logSlack cFold n + (cUnion + cTuple) ≤
      logSlack C n := by
    calc
      logSlack cFold n + logSlack cFold n + (cUnion + cTuple)
          = logSlack (cFold + cFold) n + (cUnion + cTuple) := by
            rw [logSlack_add_const]
      _ ≤ logSlack (cFold + cFold + (cUnion + cTuple)) n :=
        logSlack_add_nat_le (cFold + cFold) (cUnion + cTuple) n
      _ = logSlack C n := by simp [C, Nat.add_left_comm, Nat.add_comm]
  have hSlack' : logSlack cFold n + logSlack cFold n + (cUnion + cTuple) ≤
      logSlack C (n + 1) := by
    exact hSlack.trans (logSlack_mono_right C (by omega))
  have hFinal : natCondK D (subtupleCode u W) z +
      natCondK D (subtupleCode u V) (pairCode (subtupleCode u W) z) +
      natCondK D (subtupleCode u R) (pairCode (subtupleCode u S) z) ≤
        n + logSlack C (n + 1) := by omega
  simpa [S, R, n, subCondKRel, C,
    Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hFinal

private def lemma3_relativized_upper_partition_projectCode
    {k : ℕ} (S : Finset (Fin k)) (w : BitString) : BitString :=
  listCode (((S.sort (· ≤ ·)).map Fin.val).map
    (fun i => (decodeListCode w).getD i []))

private theorem lemma3_relativized_upper_partition_projectCode_computable
    {k : ℕ} (S : Finset (Fin k)) :
    Computable (lemma3_relativized_upper_partition_projectCode S) := by
  classical
  unfold lemma3_relativized_upper_partition_projectCode
  let positions := (S.sort (· ≤ ·)).map Fin.val
  have hMap : Primrec (fun w : BitString => positions.map
      (fun i => (decodeListCode w).getD i [])) := by
    induction positions with
    | nil => exact Primrec.const []
    | cons head tail ih =>
      have hGet : Primrec (fun w : BitString => (decodeListCode w).getD head []) :=
        (Primrec.list_getD ([] : BitString)).comp decodeListCode_primrec (Primrec.const head)
      change Primrec (fun w => (decodeListCode w).getD head [] ::
        tail.map (fun i => (decodeListCode w).getD i []))
      exact Primrec₂.comp Primrec.list_cons hGet ih
  exact listCode_computable.comp hMap.to_comp

private theorem lemma3_relativized_upper_partition_projectCode_correct
    {k : ℕ} (S : Finset (Fin k)) (u : Fin k → BitString) :
    lemma3_relativized_upper_partition_projectCode S (tupleCode u) =
      subtupleCode u S := by
  simp only [lemma3_relativized_upper_partition_projectCode,
    tupleCode, decodeListCode_listCode]
  unfold subtupleCode
  congr 1
  rw [List.map_map]
  apply List.map_congr_left
  intro i hi
  change (List.ofFn u).getD i.val [] = u i
  rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact i.isLt),
    List.getElem_ofFn]

private def lemma3_relativized_upper_partition_pairProjectCode
    {k : ℕ} (A B : Finset (Fin k)) (w : BitString) : BitString :=
  pairCode
    (lemma3_relativized_upper_partition_projectCode A w)
    (lemma3_relativized_upper_partition_projectCode B w)

private theorem lemma3_relativized_upper_partition_pairProjectCode_computable
    {k : ℕ} (A B : Finset (Fin k)) :
    Computable (lemma3_relativized_upper_partition_pairProjectCode A B) := by
  exact lemma3_relativized_lower_partition_pair_computable _ _
    (lemma3_relativized_upper_partition_projectCode_computable A)
    (lemma3_relativized_upper_partition_projectCode_computable B)

private theorem lemma3_relativized_upper_partition_pairProjectCode_correct
    {k : ℕ} (A B : Finset (Fin k)) (u : Fin k → BitString) :
    lemma3_relativized_upper_partition_pairProjectCode A B
      (tupleCode u) = pairCode (subtupleCode u A) (subtupleCode u B) := by
  simp [lemma3_relativized_upper_partition_pairProjectCode,
    lemma3_relativized_upper_partition_projectCode_correct]

private def lemma3_relativized_upper_partition_mergeCode
    {k : ℕ} (T A B : Finset (Fin k)) (w : BitString) : BitString :=
  listCode ((T.sort (· ≤ ·)).map fun i =>
    if i ∈ A then
      (decodeListCode (decodeFirst w)).getD ((A.sort (· ≤ ·)).idxOf i) []
    else
      (decodeListCode (decodeSecond w)).getD ((B.sort (· ≤ ·)).idxOf i) [])

private theorem lemma3_relativized_upper_partition_mergeCode_computable
    {k : ℕ} (T A B : Finset (Fin k)) :
    Computable (lemma3_relativized_upper_partition_mergeCode T A B) :=
        by
  classical
  unfold lemma3_relativized_upper_partition_mergeCode
  let positions := T.sort (· ≤ ·)
  let decodeA : BitString → List BitString := decodeListCode ∘ decodeFirst
  let decodeB : BitString → List BitString := decodeListCode ∘ decodeSecond
  have hDecodeA : Primrec decodeA :=
    decodeListCode_primrec.comp CodedFiniteDistribution.decodeFirst_primrec
  have hDecodeB : Primrec decodeB :=
    decodeListCode_primrec.comp CodedFiniteDistribution.decodeSecond_primrec
  have hMap : Primrec (fun w : BitString => positions.map fun i =>
      if i ∈ A then decodeA w |>.getD ((A.sort (· ≤ ·)).idxOf i) []
      else decodeB w |>.getD ((B.sort (· ≤ ·)).idxOf i) []) := by
    induction positions with
    | nil => exact Primrec.const []
    | cons head tail ih =>
      have hHead : Primrec (fun w : BitString =>
          if head ∈ A then decodeA w |>.getD ((A.sort (· ≤ ·)).idxOf head) []
          else decodeB w |>.getD ((B.sort (· ≤ ·)).idxOf head) []) := by
        by_cases hhead : head ∈ A
        · simp only [ite_eq_left hhead]
          exact (Primrec.list_getD ([] : BitString)).comp hDecodeA
            (Primrec.const ((A.sort (· ≤ ·)).idxOf head))
        · simp only [ite_eq_right hhead]
          exact (Primrec.list_getD ([] : BitString)).comp hDecodeB
            (Primrec.const ((B.sort (· ≤ ·)).idxOf head))
      change Primrec (fun w =>
        (if head ∈ A then decodeA w |>.getD ((A.sort (· ≤ ·)).idxOf head) []
          else decodeB w |>.getD ((B.sort (· ≤ ·)).idxOf head) []) ::
        tail.map (fun i =>
          if i ∈ A then decodeA w |>.getD ((A.sort (· ≤ ·)).idxOf i) []
          else decodeB w |>.getD ((B.sort (· ≤ ·)).idxOf i) []))
      exact Primrec₂.comp Primrec.list_cons hHead ih
  exact listCode_computable.comp hMap.to_comp

private theorem lemma3_relativized_upper_partition_mergeCode_correct
    {k : ℕ} (T A B : Finset (Fin k)) (hcover : A ∪ B = T)
    (u : Fin k → BitString) :
    lemma3_relativized_upper_partition_mergeCode T A B
        (pairCode (subtupleCode u A) (subtupleCode u B)) = subtupleCode u T := by
  classical
  simp only [lemma3_relativized_upper_partition_mergeCode,
    decodeFirst_pairCode, decodeSecond_pairCode, subtupleCode, decodeListCode_listCode]
  apply congrArg listCode
  apply List.map_congr_left
  intro i hi
  by_cases hA : i ∈ A
  · have hsort : i ∈ A.sort (· ≤ ·) := (A.mem_sort (· ≤ ·)).mpr hA
    have hget : ((A.sort (· ≤ ·)).map u).getD ((A.sort (· ≤ ·)).idxOf i) [] = u i := by
      rw [List.getD_eq_getElem (l := (A.sort (· ≤ ·)).map u) (d := [])
        (hn := by simpa using List.idxOf_lt_length_iff.mpr hsort)]
      simp [List.getElem_map, List.getElem_idxOf]
    rw [ite_eq_left hA, hget]
  · have hiT : i ∈ T := (T.mem_sort (· ≤ ·)).mp hi
    have hiUnion : i ∈ A ∪ B := by rw [← hcover] at hiT; exact hiT
    have hB : i ∈ B := (Finset.mem_union.mp hiUnion).resolve_left hA
    have hsort : i ∈ B.sort (· ≤ ·) := (B.mem_sort (· ≤ ·)).mpr hB
    have hget : ((B.sort (· ≤ ·)).map u).getD ((B.sort (· ≤ ·)).idxOf i) [] = u i := by
      rw [List.getD_eq_getElem (l := (B.sort (· ≤ ·)).map u) (d := [])
        (hn := by simpa using List.idxOf_lt_length_iff.mpr hsort)]
      simp [List.getElem_map, List.getElem_idxOf]
    rw [ite_eq_right hA, hget]

/-- the code of any two fixed subtuples is a computable image of the whole tuple, with one constant
uniform over all pairs of index sets. -/
private theorem lemma3_relativized_pair_complexity
    (D : Map) (hD : isOptimalConditional D) (k : ℕ) :
    ∃ c : ℕ, ∀ (u : Fin k → BitString) (z : BitString)
      (A B : Finset (Fin k)),
      natCondK D
          (pairCode (subtupleCode u A) (subtupleCode u B)) z ≤
        natCondK D (tupleCode u) z + c := by
  classical
  have hNatOfCond (a b a' b' : BitString) (c : ℕ)
      (h : condK D a b ≤ condK D a' b' + (c : ℕ∞)) :
      natCondK D a b ≤ natCondK D a' b' + c := by
    have hne := condK_ne_top_of_optimal D hD a b
    have hne' := condK_ne_top_of_optimal D hD a' b'
    change (condK D a b).toNat ≤ (condK D a' b').toNat + c
    have h' : ((condK D a b).toNat : ℕ∞) ≤
        (((condK D a' b').toNat + c : ℕ) : ℕ∞) := by
      calc
        ((condK D a b).toNat : ℕ∞) = condK D a b := ENat.natCast_toNat hne
        _ ≤ condK D a' b' + (c : ℕ∞) := h
        _ = ((condK D a' b').toNat : ℕ∞) + (c : ℕ∞) := by rw [ENat.natCast_toNat hne']
        _ = (((condK D a' b').toNat + c : ℕ) : ℕ∞) := by push_cast; rfl
    exact_mod_cast h'
  have hFor (A B : Finset (Fin k)) :
      ∃ c : ℕ, ∀ u z,
        natCondK D (pairCode (subtupleCode u A) (subtupleCode u B)) z ≤
          natCondK D (tupleCode u) z + c := by
    obtain ⟨c, hc⟩ := condK_map_le D hD
      (lemma3_relativized_upper_partition_pairProjectCode A B)
      (lemma3_relativized_upper_partition_pairProjectCode_computable A B)
    refine ⟨c, fun u z => ?_⟩
    have h := hc (tupleCode u) z
    rw [lemma3_relativized_upper_partition_pairProjectCode_correct] at h
    exact hNatOfCond _ _ _ _ c h
  let overhead : Finset (Fin k) → Finset (Fin k) → ℕ :=
    fun A B => Classical.choose (hFor A B)
  let C := Finset.univ.sup fun A : Finset (Fin k) =>
    Finset.univ.sup fun B : Finset (Fin k) => overhead A B
  refine ⟨C, ?_⟩
  intro u z A B
  have h := Classical.choose_spec (hFor A B) u z
  have hB : overhead A B ≤ Finset.univ.sup (fun B : Finset (Fin k) => overhead A B) :=
    Finset.le_sup (Finset.mem_univ B)
  have hA : Finset.univ.sup (fun B : Finset (Fin k) => overhead A B) ≤ C :=
    Finset.le_sup (f := fun A : Finset (Fin k) =>
      Finset.univ.sup (fun B : Finset (Fin k) => overhead A B)) (Finset.mem_univ A)
  calc
    natCondK D (pairCode (subtupleCode u A) (subtupleCode u B)) z
        ≤ natCondK D (tupleCode u) z + overhead A B := h
    _ ≤ natCondK D (tupleCode u) z + C :=
      Nat.add_le_add_left (hB.trans hA) _

/-- if two blocks cover an index set, its subtuple code is a computable image of the pair of block
codes, with one constant uniform over all finite partitions. -/
private theorem lemma3_relativized_merge_complexity
    (D : Map) (hD : isOptimalConditional D) (k : ℕ) :
    ∃ c : ℕ, ∀ (u : Fin k → BitString) (z : BitString)
      (T A B : Finset (Fin k)), A ∪ B = T →
      natCondK D (subtupleCode u T) z ≤
        natCondK D (pairCode (subtupleCode u A) (subtupleCode u B)) z + c := by
  classical
  have hNatOfCond (a b a' b' : BitString) (c : ℕ)
      (h : condK D a b ≤ condK D a' b' + (c : ℕ∞)) :
      natCondK D a b ≤ natCondK D a' b' + c := by
    have hne := condK_ne_top_of_optimal D hD a b
    have hne' := condK_ne_top_of_optimal D hD a' b'
    change (condK D a b).toNat ≤ (condK D a' b').toNat + c
    have h' : ((condK D a b).toNat : ℕ∞) ≤
        (((condK D a' b').toNat + c : ℕ) : ℕ∞) := by
      calc
        ((condK D a b).toNat : ℕ∞) = condK D a b := ENat.natCast_toNat hne
        _ ≤ condK D a' b' + (c : ℕ∞) := h
        _ = ((condK D a' b').toNat : ℕ∞) + (c : ℕ∞) := by rw [ENat.natCast_toNat hne']
        _ = (((condK D a' b').toNat + c : ℕ) : ℕ∞) := by push_cast; rfl
    exact_mod_cast h'
  have hFor (T A B : Finset (Fin k)) (hcover : A ∪ B = T) :
      ∃ c : ℕ, ∀ u z,
        natCondK D (subtupleCode u T) z ≤
          natCondK D (pairCode (subtupleCode u A) (subtupleCode u B)) z + c := by
    obtain ⟨c, hc⟩ := condK_map_le D hD
      (lemma3_relativized_upper_partition_mergeCode T A B)
      (lemma3_relativized_upper_partition_mergeCode_computable T A B)
    refine ⟨c, fun u z => ?_⟩
    have h := hc (pairCode (subtupleCode u A) (subtupleCode u B)) z
    rw [lemma3_relativized_upper_partition_mergeCode_correct
      T A B hcover u] at h
    exact hNatOfCond _ _ _ _ c h
  let overhead (p : Finset (Fin k) × Finset (Fin k) × Finset (Fin k)) : ℕ :=
    if hcover : p.2.1 ∪ p.2.2 = p.1 then
      Classical.choose (hFor p.1 p.2.1 p.2.2 hcover)
    else 0
  let C := Finset.univ.sup overhead
  refine ⟨C, ?_⟩
  intro u z T A B hcover
  have h := Classical.choose_spec (hFor T A B hcover) u z
  have hOver : overhead (T, A, B) ≤ C := Finset.le_sup (Finset.mem_univ (T, A, B))
  have hOver' : Classical.choose (hFor T A B hcover) ≤ C := by
    simpa [overhead, hcover] using hOver
  calc
    natCondK D (subtupleCode u T) z
        ≤ natCondK D (pairCode (subtupleCode u A) (subtupleCode u B)) z +
          Classical.choose (hFor T A B hcover) := h
    _ ≤ natCondK D (pairCode (subtupleCode u A) (subtupleCode u B)) z + C :=
      Nat.add_le_add_left hOver' _

/-- the upper
conditional chain inequality for the partition `W, V, (V ∪ W)ᶜ`. -/
private theorem lemma3_relativized_upper_partition
    (D : Map) (hD : isOptimalConditional D) (k : ℕ) :
    ∃ c : ℕ, ∀ (u : Fin k → BitString) (z : BitString)
      (V W : Finset (Fin k)), Disjoint V W →
      let R := Finset.univ \ (V ∪ W)
      natCondK D (tupleCode u) z ≤
        natCondK D (subtupleCode u W) z + subCondKRel D u z V W +
          natCondK D (subtupleCode u R) (pairCode (subtupleCode u (V ∪ W)) z) +
          logSlack c (natCondK D (tupleCode u) z + 1) := by
  obtain ⟨cPair, hPair⟩ :=
    lemma3_relativized_pair_complexity
      D hD k
  obtain ⟨cMerge, hMerge⟩ :=
    lemma3_relativized_merge_complexity
      D hD k
  obtain ⟨cChain, hChain⟩ := condK_pairCode_chain_upper_values D hD
  obtain ⟨cFold, hFold⟩ := logSlack_linear_bound (2 * cChain) 1 cPair
  refine ⟨cFold + 2 * cMerge, ?_⟩
  intro u z V W hVW
  let R := Finset.univ \ (V ∪ W)
  let G := V ∪ W
  let n := natCondK D (tupleCode u) z
  let a := natCondK D (subtupleCode u W) z
  let b := natCondK D (subtupleCode u V) (pairCode (subtupleCode u W) z)
  let r := natCondK D (subtupleCode u R) (pairCode (subtupleCode u G) z)
  let pairGR := natCondK D (pairCode (subtupleCode u G) (subtupleCode u R)) z
  let pairWV := natCondK D (pairCode (subtupleCode u W) (subtupleCode u V)) z
  have hCoverGR : G ∪ R = Finset.univ := by
    ext i
    simp [G, R]
  have hCoverWV : W ∪ V = G := by
    change W ∪ V = V ∪ W
    exact Finset.union_comm W V
  have hM1 : n ≤ pairGR + cMerge := by
    simpa [n, pairGR, G, R, subtupleCode_univ] using
      hMerge u z Finset.univ G R hCoverGR
  have hM2 : natCondK D (subtupleCode u G) z ≤ pairWV + cMerge := by
    simpa [pairWV, G] using hMerge u z G W V hCoverWV
  have hP1 : pairGR ≤ n + cPair := by
    simpa [pairGR, n] using hPair u z G R
  have hP2 : pairWV ≤ n + cPair := by
    simpa [pairWV, n] using hPair u z W V
  have hVal (x y : BitString) :
      Kolmogorov.HasPlainConditionalComplexityValue D x y (natCondK D x y) := by
    change condK D x y = ((condK D x y).toNat : ℕ∞)
    exact (ENat.natCast_toNat (condK_ne_top_of_optimal D hD x y)).symm
  have hChainGR := hChain (subtupleCode u G) (subtupleCode u R) z
    (natCondK D (subtupleCode u G) z)
    (natCondK D (subtupleCode u R) (pairCode (subtupleCode u G) z)) pairGR
    (hVal _ _) (hVal _ _) (hVal _ _)
  have hChainWV := hChain (subtupleCode u W) (subtupleCode u V) z
    (natCondK D (subtupleCode u W) z) b pairWV
    (hVal _ _) (hVal _ _) (hVal _ _)
  have hArgGR : pairGR + 1 ≤ n + cPair + 1 := by omega
  have hArgWV : pairWV + 1 ≤ n + cPair + 1 := by omega
  have hSlack :
      logSlack cChain (pairGR + 1) + logSlack cChain (pairWV + 1) ≤
        logSlack (2 * cChain) (n + cPair + 1) := by
    calc
      logSlack cChain (pairGR + 1) + logSlack cChain (pairWV + 1)
          ≤ logSlack cChain (n + cPair + 1) + logSlack cChain (n + cPair + 1) :=
            Nat.add_le_add (logSlack_mono_right cChain hArgGR)
              (logSlack_mono_right cChain hArgWV)
      _ = logSlack (cChain + cChain) (n + cPair + 1) :=
        logSlack_add_const cChain cChain _
      _ = logSlack (2 * cChain) (n + cPair + 1) := by congr 1; omega
  have hSlackFold :
      logSlack (2 * cChain) (n + cPair + 1) ≤ logSlack cFold (n + 1) := by
    calc
      logSlack (2 * cChain) (n + cPair + 1)
          ≤ logSlack (2 * cChain) (1 * (n + 1) + cPair) :=
            logSlack_mono_right _ (by omega)
      _ ≤ logSlack cFold (n + 1) := by simpa using hFold (n + 1)
  have hSlackTotal :
      logSlack cChain (pairGR + 1) + logSlack cChain (pairWV + 1) + 2 * cMerge ≤
        logSlack (cFold + 2 * cMerge) (n + 1) := by
    calc
      logSlack cChain (pairGR + 1) + logSlack cChain (pairWV + 1) + 2 * cMerge
          ≤ logSlack (2 * cChain) (n + cPair + 1) + 2 * cMerge :=
            Nat.add_le_add_right hSlack _
      _ ≤ logSlack cFold (n + 1) + 2 * cMerge := Nat.add_le_add_right hSlackFold _
      _ ≤ logSlack (cFold + 2 * cMerge) (n + 1) := by
        simpa using logSlack_add_nat_le cFold (2 * cMerge) (n + 1)
  have hMain : n ≤ a + b + r +
      (logSlack cChain (pairGR + 1) + logSlack cChain (pairWV + 1)) + 2 * cMerge := by
    dsimp [a, b, r, n, pairGR, pairWV, G, R, subCondKRel]
      at hM1 hM2 hP1 hP2 hChainGR hChainWV ⊢
    omega
  have hResult : n ≤ a + b + r + logSlack (cFold + 2 * cMerge) (n + 1) := by
    omega
  change natCondK D (tupleCode u) z ≤
    natCondK D (subtupleCode u W) z + subCondKRel D u z V W +
      natCondK D (subtupleCode u R) (pairCode (subtupleCode u (V ∪ W)) z) +
      logSlack (cFold + 2 * cMerge) (natCondK D (tupleCode u) z + 1)
  simpa [n, a, b, r, G, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
    subCondKRel] using hResult

/-- the two auxiliary
partition terms for the primed tuple are bounded by those of the reference tuple using the profile
hypothesis; empty blocks are covered by their uniform constant descriptions. -/
private theorem lemma3_relativized_auxiliary_terms
    (D : Map) (hD : isOptimalConditional D) (k : ℕ) :
    ∃ c : ℕ, ∀ (u u' : Fin k → BitString) (z z' : BitString) (δ₁ : ℤ), 0 ≤ δ₁ →
      (∀ X Y : Finset (Fin k), X.Nonempty → Disjoint X Y →
        (subCondKRel D u' z' X Y : ℤ) ≤ subCondKRel D u z X Y + δ₁) →
      ∀ V W : Finset (Fin k), V.Nonempty → Disjoint V W →
      let R := Finset.univ \ (V ∪ W)
      natCondK D (subtupleCode u' W) z' +
          natCondK D (subtupleCode u' R) (pairCode (subtupleCode u' (V ∪ W)) z') ≤
        natCondK D (subtupleCode u W) z +
          natCondK D (subtupleCode u R) (pairCode (subtupleCode u (V ∪ W)) z) +
          2 * δ₁ + logSlack c
            (natCondK D (tupleCode u) z + natCondK D (tupleCode u') z' + 1) := by
  have hPair : Computable (fun b : BitString => pairCode [] b) :=
    pairCode_computable.comp ((Computable.const []).pair Computable.id)
  obtain ⟨cPair, hcPair⟩ := condK_cond_map_le D hD
    (fun b : BitString => pairCode [] b) hPair
  obtain ⟨cDrop, hcDrop⟩ := condK_cond_map_le D hD decodeSecond decodeSecond_computable
  obtain ⟨cEmpty, hcEmpty⟩ := condK_comp D hD (fun _ : BitString => []) (Computable.const [])
  have hNatOfCond (a b a' b' : BitString) (c : ℕ)
      (h : condK D a b ≤ condK D a' b' + (c : ℕ∞)) :
      natCondK D a b ≤ natCondK D a' b' + c := by
    have hne := avgCond_condK_ne_top D hD a b
    have hne' := avgCond_condK_ne_top D hD a' b'
    change (condK D a b).toNat ≤ (condK D a' b').toNat + c
    have h' : ((condK D a b).toNat : ℕ∞) ≤
        (((condK D a' b').toNat + c : ℕ) : ℕ∞) := by
      calc
        ((condK D a b).toNat : ℕ∞) = condK D a b := ENat.natCast_toNat hne
        _ ≤ condK D a' b' + (c : ℕ∞) := h
        _ = ((condK D a' b').toNat : ℕ∞) + (c : ℕ∞) := by
          rw [ENat.natCast_toNat hne']
        _ = (((condK D a' b').toNat + c : ℕ) : ℕ∞) := by push_cast; rfl
    exact_mod_cast h'
  refine ⟨cDrop + cPair + 2 * cEmpty, ?_⟩
  intro u u' z z' δ₁ hδ₁ hProfile V W hV hVW
  let R := Finset.univ \ (V ∪ W)
  let G := V ∪ W
  have hRG : Disjoint R G := by
    rw [Finset.disjoint_left]
    intro i hiR hiG
    exact (Finset.mem_sdiff.mp hiR).2 hiG
  have hNatEmpty (x : BitString) : natCondK D [] x ≤ cEmpty := by
    have hne := avgCond_condK_ne_top D hD [] x
    change (condK D [] x).toNat ≤ cEmpty
    have hcast : ((condK D [] x).toNat : ℕ∞) ≤ (cEmpty : ℕ∞) := by
      rw [ENat.natCast_toNat hne]
      exact hcEmpty x
    exact_mod_cast hcast
  have hA' : natCondK D (subtupleCode u' W) z' ≤
      natCondK D (subtupleCode u' W) (pairCode [] z') + cPair := by
    exact hNatOfCond _ _ _ _ cPair (hcPair (subtupleCode u' W) z')
  have hA : natCondK D (subtupleCode u W) (pairCode [] z) ≤
      natCondK D (subtupleCode u W) z + cDrop := by
    have h := hcDrop (subtupleCode u W) (pairCode [] z)
    exact hNatOfCond _ _ _ _ cDrop (by simpa [decodeSecond_pairCode] using h)
  have hAInt :
      (natCondK D (subtupleCode u' W) z' : ℤ) ≤
        natCondK D (subtupleCode u W) z + δ₁ + cDrop + cPair + cEmpty := by
    by_cases hW : W.Nonempty
    · have hprofW :
          (natCondK D (subtupleCode u' W) (pairCode [] z') : ℤ) ≤
            natCondK D (subtupleCode u W) (pairCode [] z) + δ₁ := by
        simpa [subCondKRel, subtupleCode_empty] using
          hProfile W ∅ hW (Finset.disjoint_empty_right W)
      have hA'int :
          (natCondK D (subtupleCode u' W) z' : ℤ) ≤
            natCondK D (subtupleCode u' W) (pairCode [] z') + cPair := by
        exact_mod_cast hA'
      have hAint :
          (natCondK D (subtupleCode u W) (pairCode [] z) : ℤ) ≤
            natCondK D (subtupleCode u W) z + cDrop := by
        exact_mod_cast hA
      omega
    · have hWempty : W = ∅ := by
        exact Finset.not_nonempty_iff_eq_empty.mp hW
      have hE : natCondK D (subtupleCode u' W) z' ≤ cEmpty := by
        simpa [hWempty, subtupleCode_empty] using hNatEmpty z'
      omega
  have hCInt :
      (natCondK D (subtupleCode u' R) (pairCode (subtupleCode u' G) z') : ℤ) ≤
        natCondK D (subtupleCode u R) (pairCode (subtupleCode u G) z) + δ₁ + cEmpty := by
    by_cases hR : R.Nonempty
    · have hprofR :
          (natCondK D (subtupleCode u' R) (pairCode (subtupleCode u' G) z') : ℤ) ≤
            natCondK D (subtupleCode u R) (pairCode (subtupleCode u G) z) + δ₁ := by
        simpa [subCondKRel, G] using hProfile R G hR hRG
      omega
    · have hRempty : R = ∅ := by
        exact Finset.not_nonempty_iff_eq_empty.mp hR
      have hE : natCondK D (subtupleCode u' R)
          (pairCode (subtupleCode u' G) z') ≤ cEmpty := by
        simpa [hRempty, subtupleCode_empty] using
          hNatEmpty (pairCode (subtupleCode u' G) z')
      omega
  have hslack :
      ((cDrop + cPair + 2 * cEmpty : ℕ) : ℤ) ≤
        logSlack (cDrop + cPair + 2 * cEmpty)
          (natCondK D (tupleCode u) z + natCondK D (tupleCode u') z' + 1) := by
    have hnat : cDrop + cPair + 2 * cEmpty ≤
        logSlack (cDrop + cPair + 2 * cEmpty)
          (natCondK D (tupleCode u) z + natCondK D (tupleCode u') z' + 1) := by
      unfold logSlack
      omega
    exact_mod_cast hnat
  change (natCondK D (subtupleCode u' W) z' : ℤ) +
      natCondK D (subtupleCode u' R) (pairCode (subtupleCode u' G) z') ≤
    natCondK D (subtupleCode u W) z +
      natCondK D (subtupleCode u R) (pairCode (subtupleCode u G) z) +
      2 * δ₁ + logSlack (cDrop + cPair + 2 * cEmpty)
        (natCondK D (tupleCode u) z + natCondK D (tupleCode u') z' + 1)
  omega

/-- combine the
three logarithmic errors, whose arguments are at most one more than the combined complexity. -/
private theorem lemma3_relativized_absorb_errors
    (c₁ c₂ c₃ : ℕ) :
    ∃ c : ℕ, ∀ n n' : ℕ,
      logSlack c₁ (n + 1) + logSlack c₂ (n' + 1) +
        logSlack c₃ (n + n' + 1) ≤ logSlack c (n + n') := by
  let s := c₁ + c₂ + c₃
  refine ⟨s + 2 * s, fun n n' => ?_⟩
  have hshift (c x : ℕ) : logSlack c (x + 1) ≤ logSlack c x + 2 * c := by
    unfold logSlack
    have hbits := length_natBits_add_le x 1
    have hone : (Nat.bits 1).length = 1 := by simp
    nlinarith [Nat.mul_le_mul_left c hbits]
  have h₁ : logSlack c₁ (n + 1) ≤ logSlack c₁ (n + n') + 2 * c₁ := by
    calc
      logSlack c₁ (n + 1) ≤ logSlack c₁ n + 2 * c₁ := hshift c₁ n
      _ ≤ logSlack c₁ (n + n') + 2 * c₁ := by
        exact Nat.add_le_add_right (logSlack_le_logSlack_add_right c₁ n n') _
  have h₂ : logSlack c₂ (n' + 1) ≤ logSlack c₂ (n + n') + 2 * c₂ := by
    calc
      logSlack c₂ (n' + 1) ≤ logSlack c₂ n' + 2 * c₂ := hshift c₂ n'
      _ ≤ logSlack c₂ (n + n') + 2 * c₂ := by
        exact Nat.add_le_add_right (logSlack_le_logSlack_add_left c₂ n' n) _
  have h₃ : logSlack c₃ (n + n' + 1) ≤ logSlack c₃ (n + n') + 2 * c₃ :=
    hshift c₃ (n + n')
  have hlogs : logSlack c₁ (n + n') + logSlack c₂ (n + n') +
      logSlack c₃ (n + n') = logSlack s (n + n') := by
    dsimp [s]
    rw [← logSlack_add_constants c₁ c₂ (n + n'),
      ← logSlack_add_constants (c₁ + c₂) c₃ (n + n')]
  have hfinal : logSlack s (n + n') + 2 * s ≤
      logSlack (s + 2 * s) (n + n') := by
    calc
      logSlack s (n + n') + 2 * s ≤
          logSlack s (n + n') + logSlack (2 * s) (n + n') := by
        exact Nat.add_le_add_left (by
          unfold logSlack
          exact Nat.le_add_left _ _) _
      _ = logSlack (s + 2 * s) (n + n') :=
        (logSlack_add_constants s (2 * s) (n + n')).symm
  calc
    logSlack c₁ (n + 1) + logSlack c₂ (n' + 1) +
        logSlack c₃ (n + n' + 1)
      ≤ (logSlack c₁ (n + n') + 2 * c₁) +
          (logSlack c₂ (n + n') + 2 * c₂) +
          (logSlack c₃ (n + n') + 2 * c₃) := by omega
    _ = logSlack s (n + n') + 2 * s := by omega
    _ ≤ logSlack (s + 2 * s) (n + n') := hfinal

/-- applying the conditional chain rule
to the partition `W, V, (V ∪ W)ᶜ` compares a profile coordinate with the difference of the two
whole-tuple conditional complexities.  The error is measured at the combined complexity scale. -/
private theorem lemma3_relativized_partition_chain (D : Map)
    (hD : isOptimalConditional D) (k : ℕ) :
    ∃ c : ℕ, ∀ (u u' : Fin k → BitString) (z z' : BitString) (δ₁ : ℤ), 0 ≤ δ₁ →
      (∀ X Y : Finset (Fin k), X.Nonempty → Disjoint X Y →
        (subCondKRel D u' z' X Y : ℤ) ≤ subCondKRel D u z X Y + δ₁) →
      ∀ V W : Finset (Fin k), V.Nonempty → Disjoint V W →
        (subCondKRel D u z V W : ℤ) ≤
          subCondKRel D u' z' V W +
            (2 * δ₁ +
              ((natCondK D (tupleCode u) z : ℤ) - natCondK D (tupleCode u') z') +
              logSlack c
                (natCondK D (tupleCode u) z + natCondK D (tupleCode u') z')) := by
  obtain ⟨cLow, hLow⟩ :=
    lemma3_relativized_lower_partition D hD k
  obtain ⟨cUpper, hUpper⟩ :=
    lemma3_relativized_upper_partition D hD k
  obtain ⟨cAux, hAux⟩ :=
    lemma3_relativized_auxiliary_terms D hD k
  obtain ⟨c, hAbsorb⟩ :=
    lemma3_relativized_absorb_errors cLow cUpper cAux
  refine ⟨c, ?_⟩
  intro u u' z z' δ₁ hδ₁ hProfile V W hV hVW
  let R := Finset.univ \ (V ∪ W)
  let n := natCondK D (tupleCode u) z
  let n' := natCondK D (tupleCode u') z'
  let a := natCondK D (subtupleCode u W) z
  let b := natCondK D (subtupleCode u V) (pairCode (subtupleCode u W) z)
  let r := natCondK D (subtupleCode u R) (pairCode (subtupleCode u (V ∪ W)) z)
  let a' := natCondK D (subtupleCode u' W) z'
  let b' := natCondK D (subtupleCode u' V) (pairCode (subtupleCode u' W) z')
  let r' := natCondK D (subtupleCode u' R)
    (pairCode (subtupleCode u' (V ∪ W)) z')
  have hLower := hLow u z V W hVW
  have hUpper' := hUpper u' z' V W hVW
  have hAux' := hAux u u' z z' δ₁ hδ₁ hProfile V W hV hVW
  have hLowerInt : (a + b + r : ℤ) ≤ n + logSlack cLow (n + 1) := by
    exact_mod_cast hLower
  have hUpperInt : (n' : ℤ) ≤ a' + b' + r' + logSlack cUpper (n' + 1) := by
    exact_mod_cast hUpper'
  have hAuxInt : (a' + r' : ℤ) ≤ a + r + 2 * δ₁ +
      logSlack cAux (n + n' + 1) := by
    exact_mod_cast hAux'
  have hSlack := hAbsorb n n'
  change (b : ℤ) ≤ (b' : ℤ) +
    (2 * δ₁ + ((n : ℤ) - n') + logSlack c (n + n'))
  omega

/-- the whole-tuple instance of the
profile hypothesis bounds the primed conditional complexity by the reference complexity plus
`δ₁` and a fixed coding overhead. -/
private theorem lemma3_relativized_total_complexity (D : Map)
    (hD : isOptimalConditional D) (k : ℕ) (hk : 0 < k) :
    ∃ c : ℕ, ∀ (u u' : Fin k → BitString) (z z' : BitString) (δ₁ : ℤ), 0 ≤ δ₁ →
      (∀ X Y : Finset (Fin k), X.Nonempty → Disjoint X Y →
        (subCondKRel D u' z' X Y : ℤ) ≤ subCondKRel D u z X Y + δ₁) →
      (natCondK D (tupleCode u') z' : ℤ) ≤
        natCondK D (tupleCode u) z + δ₁ + c := by
  have hPair : Computable (fun b : BitString => pairCode [] b) :=
    pairCode_computable.comp ((Computable.const []).pair Computable.id)
  obtain ⟨c₁, hc₁⟩ := condK_cond_map_le D hD (fun b : BitString => pairCode [] b) hPair
  obtain ⟨c₂, hc₂⟩ := condK_cond_map_le D hD decodeSecond decodeSecond_computable
  refine ⟨c₁ + c₂, ?_⟩
  intro u u' z z' δ₁ hδ₁ hprof
  let V : Finset (Fin k) := Finset.univ
  have hV : V.Nonempty := ⟨⟨0, hk⟩, Finset.mem_univ _⟩
  have hVW : Disjoint V (∅ : Finset (Fin k)) := Finset.disjoint_empty_right V
  have hprofile := hprof V ∅ hV hVW
  have hprofile' :
      (natCondK D (tupleCode u') (pairCode [] z') : ℤ) ≤
        natCondK D (tupleCode u) (pairCode [] z) + δ₁ := by
    simpa [V, subCondKRel, subtupleCode_univ, subtupleCode_empty] using hprofile
  have hNatOfCond (a b a' b' : BitString) (c : ℕ)
      (h : condK D a b ≤ condK D a' b' + (c : ℕ∞)) :
      natCondK D a b ≤ natCondK D a' b' + c := by
    have hne := avgCond_condK_ne_top D hD a b
    have hne' := avgCond_condK_ne_top D hD a' b'
    change (condK D a b).toNat ≤ (condK D a' b').toNat + c
    have h' : ((condK D a b).toNat : ℕ∞) ≤
        (((condK D a' b').toNat + c : ℕ) : ℕ∞) := by
      calc
        ((condK D a b).toNat : ℕ∞) = condK D a b := ENat.natCast_toNat hne
        _ ≤ condK D a' b' + (c : ℕ∞) := h
        _ = ((condK D a' b').toNat : ℕ∞) + (c : ℕ∞) := by rw [ENat.natCast_toNat hne']
        _ = (((condK D a' b').toNat + c : ℕ) : ℕ∞) := by push_cast; rfl
    exact_mod_cast h'
  have hUpper : natCondK D (tupleCode u') z' ≤
      natCondK D (tupleCode u') (pairCode [] z') + c₁ :=
    hNatOfCond _ _ _ _ c₁ (hc₁ (tupleCode u') z')
  have hLower : natCondK D (tupleCode u) (pairCode [] z) ≤
      natCondK D (tupleCode u) z + c₂ := by
    have h := hc₂ (tupleCode u) (pairCode [] z)
    simpa [decodeSecond_pairCode] using hNatOfCond _ _ _ _ c₂ h
  have hUpper' : (natCondK D (tupleCode u') z' : ℤ) ≤
      natCondK D (tupleCode u') (pairCode [] z') + c₁ := by exact_mod_cast hUpper
  have hLower' : (natCondK D (tupleCode u) (pairCode [] z) : ℤ) ≤
      natCondK D (tupleCode u) z + c₂ := by exact_mod_cast hLower
  have hmain : (natCondK D (tupleCode u') z' : ℤ) ≤
      natCondK D (tupleCode u) z + δ₁ + (c₁ + c₂) := by omega
  omega

/-- a conditional description of the
whole tuple also describes any one subtuple when the other coordinates and the oracle are
available. -/
private theorem lemma3_relativized_profile_below_total (D : Map)
    (hD : isOptimalConditional D) (k : ℕ) :
    ∃ c : ℕ, ∀ (u : Fin k → BitString) (z : BitString)
      (V W : Finset (Fin k)), V.Nonempty → Disjoint V W →
      (subCondKRel D u z V W : ℤ) ≤ natCondK D (tupleCode u) z + c := by
  classical
  have hNatOfCond (a b a' b' : BitString) (c : ℕ)
      (h : condK D a b ≤ condK D a' b' + (c : ℕ∞)) :
      natCondK D a b ≤ natCondK D a' b' + c := by
    have hne := avgCond_condK_ne_top D hD a b
    have hne' := avgCond_condK_ne_top D hD a' b'
    change (condK D a b).toNat ≤ (condK D a' b').toNat + c
    have h' : ((condK D a b).toNat : ℕ∞) ≤
        (((condK D a' b').toNat + c : ℕ) : ℕ∞) := by
      calc
        ((condK D a b).toNat : ℕ∞) = condK D a b := ENat.natCast_toNat hne
        _ ≤ condK D a' b' + (c : ℕ∞) := h
        _ = ((condK D a' b').toNat : ℕ∞) + (c : ℕ∞) := by rw [ENat.natCast_toNat hne']
        _ = (((condK D a' b').toNat + c : ℕ) : ℕ∞) := by push_cast; rfl
    exact_mod_cast h'
  have hProject (V : Finset (Fin k)) :
      Computable (fun w : BitString =>
        listCode (((V.sort (· ≤ ·)).map Fin.val).map
          (fun i => (decodeListCode w).getD i []))) := by
    let positions := (V.sort (· ≤ ·)).map Fin.val
    have hMap : Primrec (fun w : BitString =>
        positions.map (fun i => (decodeListCode w).getD i [])) := by
      induction positions with
      | nil => exact Primrec.const []
      | cons head tail ih =>
        have h_getD : Primrec (fun (w : BitString) => (decodeListCode w).getD head []) := by
          exact (Primrec.list_getD ([] : BitString)).comp decodeListCode_primrec
            (Primrec.const head)
        change Primrec (fun w =>
          (decodeListCode w).getD head [] ::
            tail.map (fun i => (decodeListCode w).getD i []))
        exact Primrec₂.comp Primrec.list_cons h_getD ih
    exact listCode_computable.comp hMap.to_comp
  have hProjectCorrect (V : Finset (Fin k)) (u : Fin k → BitString) :
      listCode (((V.sort (· ≤ ·)).map Fin.val).map
        (fun i => (decodeListCode (tupleCode u)).getD i [])) = subtupleCode u V := by
    simp only [tupleCode, decodeListCode_listCode]
    unfold subtupleCode
    apply congrArg listCode
    rw [List.map_map]
    apply List.map_congr_left
    intro i hi
    change (List.ofFn u).getD i.val [] = u i
    rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact i.isLt),
      List.getElem_ofFn]
  have hProjectionBound (V : Finset (Fin k)) :
      ∃ cV : ℕ, ∀ (u : Fin k → BitString) (z : BitString),
        natCondK D (subtupleCode u V) z ≤ natCondK D (tupleCode u) z + cV := by
    let f : BitString → BitString := fun w =>
      listCode (((V.sort (· ≤ ·)).map Fin.val).map
        (fun i => (decodeListCode w).getD i []))
    obtain ⟨cV, hcV⟩ := condK_map_le D hD f (hProject V)
    refine ⟨cV, fun u z => ?_⟩
    have h := hcV (tupleCode u) z
    rw [show f (tupleCode u) = subtupleCode u V from hProjectCorrect V u] at h
    exact hNatOfCond _ _ _ _ cV h
  let overhead : Finset (Fin k) → ℕ := fun V => Classical.choose (hProjectionBound V)
  let cProjection := Finset.univ.sup overhead
  obtain ⟨cCondition, hCondition⟩ :=
    condK_cond_map_le D hD decodeSecond decodeSecond_computable
  refine ⟨cProjection + cCondition, ?_⟩
  intro u z V W hV hVW
  have hProj := Classical.choose_spec (hProjectionBound V) u z
  have hOverhead : overhead V ≤ cProjection :=
    Finset.le_sup (Finset.mem_univ V)
  have hCondition' := hNatOfCond (subtupleCode u V)
    (pairCode (subtupleCode u W) z) (subtupleCode u V) z cCondition
    (by simpa [decodeSecond_pairCode] using
      hCondition (subtupleCode u V) (pairCode (subtupleCode u W) z))
  have hProj' : (natCondK D (subtupleCode u V) z : ℤ) ≤
      natCondK D (tupleCode u) z + overhead V := by exact_mod_cast hProj
  have hCondition'' : (subCondKRel D u z V W : ℤ) ≤
      natCondK D (subtupleCode u V) z + cCondition := by
    exact_mod_cast hCondition'
  change (subCondKRel D u z V W : ℤ) ≤
      natCondK D (tupleCode u) z + (cProjection + cCondition)
  omega

/-- absorb the chain-rule error at the
combined complexity scale into one logarithmic slack at the reference scale. -/
private theorem lemma3_relativized_absorb_slack (cTotal cProfile cChain : ℕ) :
    ∃ c : ℕ, ∀ (n n' p p' : ℕ) (δ₁ δ₂ : ℤ),
      (n : ℤ) ≤ n' + δ₂ →
      (n' : ℤ) ≤ n + δ₁ + cTotal →
      (p : ℤ) ≤ n + cProfile →
      (p : ℤ) ≤ p' +
        (2 * δ₁ + ((n : ℤ) - n') + logSlack cChain (n + n')) →
      (p : ℤ) ≤ p' + (2 * δ₁ + δ₂ + logSlack c n) := by
  obtain ⟨c, hc⟩ := logSlack_absorb_of_le_linear cChain 3
    (cProfile + 2 * cTotal)
  refine ⟨c, fun n n' p p' δ₁ δ₂ hnn' hn'n hp hchain => ?_⟩
  by_contra hnot
  have hnot' :
      (p' : ℤ) + (2 * δ₁ + δ₂ + logSlack c n) < (p : ℤ) := by omega
  have hslackNonneg : (0 : ℤ) ≤ logSlack c n := by
    exact_mod_cast Nat.zero_le (logSlack c n)
  have hp'Nonneg : (0 : ℤ) ≤ (p' : ℤ) := Int.natCast_nonneg p'
  have hdelta2Lower : -δ₁ - cTotal ≤ δ₂ := by omega
  have hR : 2 * δ₁ + δ₂ < (n : ℤ) + cProfile := by omega
  have hdelta1 : δ₁ ≤ (n : ℤ) + cProfile + cTotal := by omega
  have hbudget : n + n' ≤ 3 * n + (cProfile + 2 * cTotal) := by omega
  have hlog := hc n (n + n') hbudget
  have hlog' :
      (logSlack cChain (n + n') : ℤ) ≤ logSlack c n := by
    exact_mod_cast hlog
  have hdiff : (n : ℤ) - n' ≤ δ₂ := by omega
  have hout : (p : ℤ) ≤ (p' : ℤ) +
      (2 * δ₁ + δ₂ + logSlack c n) := by omega
  exact hnot hout

/-- **Lemma 3, with an oracle on either side.**  Let `u, u'` be `k`-tuples, `z, z'` oracles and
`δ₁ ≥ 0`.  If `K'(u' | z') ≤ K'(u | z) + δ₁ e` and `K(u' | z') ≥ K(u | z) − δ₂`, then
`K'(u' | z') ≥ K'(u | z) − (2δ₁ + δ₂ + O(log N)) e`, `N = K(u | z)`.  The proof is the one of
Lemma 3 in the Appendix (the chain rule for `u'` and for `u`).  With `z = z' = λ` this is part 1
of Lemma 3, with `z = λ` part 2; the proof of Theorem 5 uses it with `z' = λ`.  The lemma is
false for `δ₁ < 0`. -/
theorem lemma3_relativized (D : Map) (hD : isOptimalConditional D) (k : ℕ) :
    ∃ c : ℕ, ∀ (u u' : Fin k → BitString) (z z' : BitString) (δ₁ δ₂ : ℤ), 0 ≤ δ₁ →
      (∀ V W : Finset (Fin k), V.Nonempty → Disjoint V W →
        (subCondKRel D u' z' V W : ℤ) ≤ subCondKRel D u z V W + δ₁) →
      (natCondK D (tupleCode u) z : ℤ) ≤ natCondK D (tupleCode u') z' + δ₂ →
      ∀ V W : Finset (Fin k), V.Nonempty → Disjoint V W →
        (subCondKRel D u z V W : ℤ) ≤ subCondKRel D u' z' V W +
          (2 * δ₁ + δ₂ + logSlack c (natCondK D (tupleCode u) z)) := by
  by_cases hk : 0 < k
  · obtain ⟨cChain, hChain⟩ := lemma3_relativized_partition_chain D hD k
    obtain ⟨cTotal, hTotal⟩ := lemma3_relativized_total_complexity D hD k hk
    obtain ⟨cProfile, hProfile⟩ := lemma3_relativized_profile_below_total D hD k
    obtain ⟨c, hAbsorb⟩ := lemma3_relativized_absorb_slack cTotal cProfile cChain
    refine ⟨c, ?_⟩
    intro u u' z z' δ₁ δ₂ hδ₁ hProfileLe hTotalLe V W hV hVW
    exact hAbsorb
      (natCondK D (tupleCode u) z) (natCondK D (tupleCode u') z')
      (subCondKRel D u z V W) (subCondKRel D u' z' V W)
      δ₁ δ₂ hTotalLe
      (hTotal u u' z z' δ₁ hδ₁ hProfileLe)
      (hProfile u z V W hV hVW)
      (hChain u u' z z' δ₁ hδ₁ hProfileLe V W hV hVW)
  · refine ⟨0, ?_⟩
    intro u u' z z' δ₁ δ₂ hδ₁ hProfileLe hTotalLe V W hV hVW
    have hk' : 0 < k := by
      have hcard : 0 < V.card := Finset.card_pos.mpr hV
      have hcard' : V.card ≤ k := by simpa using Finset.card_le_univ V
      omega
    omega

private lemma lemma3_part1_condK_toNat_le (D : Map) (hD : isOptimalConditional D)
    (a b c : BitString) (k : ℕ)
    (h : condK D a b ≤ condK D a c + (k : ℕ∞)) :
    natCondK D a b ≤ natCondK D a c + k := by
  have hneB := avgCond_condK_ne_top D hD a b
  have hneC := avgCond_condK_ne_top D hD a c
  change (condK D a b).toNat ≤ (condK D a c).toNat + k
  have h' : ((condK D a b).toNat : ℕ∞) ≤
      (((condK D a c).toNat + k : ℕ) : ℕ∞) := by
    calc
      ((condK D a b).toNat : ℕ∞) = condK D a b :=
        ENat.natCast_toNat hneB
      _ ≤ condK D a c + (k : ℕ∞) := h
      _ = ((condK D a c).toNat : ℕ∞) + (k : ℕ∞) := by
        rw [ENat.natCast_toNat hneC]
      _ = (((condK D a c).toNat + k : ℕ) : ℕ∞) := by push_cast; rfl
  exact_mod_cast h'

private lemma lemma3_part1_pair_condition (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ a b : BitString,
      natCondK D a (pairCode b []) ≤ natCondK D a b + c ∧
      natCondK D a b ≤ natCondK D a (pairCode b []) + c := by
  have hPair : Computable (fun b : BitString => pairCode b []) :=
    pairCode_computable.comp (Computable.id.pair (Computable.const []))
  obtain ⟨c₁, hc₁⟩ := condK_cond_map_le D hD (fun b : BitString => pairCode b []) hPair
  obtain ⟨c₂, hc₂⟩ := condK_cond_map_le D hD decodeFirst decodeFirst_computable
  refine ⟨c₁ + c₂, ?_⟩
  intro a b
  constructor
  · have hcond : condK D a (pairCode b []) ≤ condK D a b + (c₂ : ℕ∞) := by
      simpa only [decodeFirst_pairCode] using hc₂ a (pairCode b [])
    have h := lemma3_part1_condK_toNat_le D hD a (pairCode b []) b c₂ hcond
    omega
  · have h := lemma3_part1_condK_toNat_le D hD a b (pairCode b []) c₁ (hc₁ a b)
    omega

/-- **Lemma 3, part 1.** If `K'(x̄', ȳ) ≤ K'(x̄, ȳ) + δ₁ e` with `δ₁ ≥ 0` and
`K(x̄', ȳ) ≥ K(x̄, ȳ) − δ₂`, then `K'(x̄', ȳ) ≥ K'(x̄, ȳ) − (2δ₁ + δ₂ + O(log N)) e`,
`N = K(x̄, ȳ)`.  Proof: Appendix. -/
theorem lemma3_part1 (D : Map) (hD : isOptimalConditional D) (n m : ℕ) :
    ∃ c : ℕ, ∀ (x x' : Fin n → BitString) (y : Fin m → BitString) (δ₁ δ₂ : ℤ), 0 ≤ δ₁ →
      (∀ V W : Finset (Fin (n + m)), V.Nonempty → Disjoint V W →
        (subCondK D (Fin.append x' y) V W : ℤ) ≤ subCondK D (Fin.append x y) V W + δ₁) →
      (natK D (tupleCode (Fin.append x y)) : ℤ) ≤ natK D (tupleCode (Fin.append x' y)) + δ₂ →
      ∀ V W : Finset (Fin (n + m)), V.Nonempty → Disjoint V W →
        (subCondK D (Fin.append x y) V W : ℤ) ≤ subCondK D (Fin.append x' y) V W +
          (2 * δ₁ + δ₂ + logSlack c (natK D (tupleCode (Fin.append x y)))) := by
  obtain ⟨cRel, hRel⟩ := lemma3_relativized D hD (n + m)
  obtain ⟨cPair, hPair⟩ := lemma3_part1_pair_condition D hD
  refine ⟨cRel + 6 * cPair, ?_⟩
  intro x x' y δ₁ δ₂ hδ₁ hprof hbase V W hV hdis
  let u : Fin (n + m) → BitString := Fin.append x y
  let u' : Fin (n + m) → BitString := Fin.append x' y
  have hδ₁' : 0 ≤ δ₁ + 2 * (cPair : ℤ) := by omega
  have hprof' : ∀ V W : Finset (Fin (n + m)), V.Nonempty → Disjoint V W →
      (subCondKRel D u' [] V W : ℤ) ≤ subCondKRel D u [] V W +
        (δ₁ + 2 * (cPair : ℤ)) := by
    intro V W hV hdis
    have hp := hPair (subtupleCode u' V) (subtupleCode u' W)
    have hp₁ : (subCondKRel D u' [] V W : ℤ) ≤ subCondK D u' V W + cPair := by
      change (natCondK D (subtupleCode u' V)
        (pairCode (subtupleCode u' W) []) : ℤ) ≤ _
      exact_mod_cast hp.1
    have hp₂ : (subCondK D u V W : ℤ) ≤ subCondKRel D u [] V W + cPair := by
      change (natCondK D (subtupleCode u V) (subtupleCode u W) : ℤ) ≤ _
      exact_mod_cast (hPair (subtupleCode u V) (subtupleCode u W)).2
    have h : (subCondK D u' V W : ℤ) ≤ subCondK D u V W + δ₁ := by
      simpa [u, u'] using hprof V W hV hdis
    omega
  have hbase' : (natCondK D (tupleCode u) [] : ℤ) ≤
      natCondK D (tupleCode u') [] + δ₂ := by
    simpa [natK, natCondK, plainK, u, u'] using hbase
  have hN : natCondK D (tupleCode u) [] = natK D (tupleCode u) := rfl
  have hRel' := hRel u u' [] [] (δ₁ + 2 * (cPair : ℤ)) δ₂ hδ₁' hprof' hbase'
  rw [hN] at hRel'
  have hleft := hPair (subtupleCode u V) (subtupleCode u W)
  have hright := hPair (subtupleCode u' V) (subtupleCode u' W)
  have hleft' : (subCondK D u V W : ℤ) ≤ subCondKRel D u [] V W + cPair := by
    change (natCondK D (subtupleCode u V) (subtupleCode u W) : ℤ) ≤ _
    exact_mod_cast hleft.2
  have hright' : (subCondKRel D u' [] V W : ℤ) ≤ subCondK D u' V W + cPair := by
    change (natCondK D (subtupleCode u' V)
      (pairCode (subtupleCode u' W) []) : ℤ) ≤ _
    exact_mod_cast hright.1
  have hraw : (subCondK D u V W : ℤ) ≤ subCondK D u' V W +
      (2 * δ₁ + δ₂ + logSlack cRel (natK D (tupleCode u)) + 6 * (cPair : ℤ)) := by
    have hR := hRel' V W hV hdis
    omega
  have hSlack : (logSlack cRel (natK D (tupleCode u)) : ℤ) +
      6 * (cPair : ℤ) ≤ logSlack (cRel + 6 * cPair) (natK D (tupleCode u)) := by
    exact_mod_cast (logSlack_add_nat_le cRel (6 * cPair) (natK D (tupleCode u)))
  have hfinal : (subCondK D u V W : ℤ) ≤ subCondK D u' V W +
      (2 * δ₁ + δ₂ + logSlack (cRel + 6 * cPair) (natK D (tupleCode u))) := by
    omega
  simpa [u, u'] using hfinal

private lemma lemma3_part2_cond_ne_top (D : Map) (hD : isOptimalConditional D)
    (a b : BitString) : condK D a b ≠ ⊤ := by
  obtain ⟨c, hc⟩ := condK_le_plainK D hD
  obtain ⟨d, hd⟩ := plainK_le_length D hD
  apply ne_top_of_le_natCast
  calc
    condK D a b ≤ plainK D a + c := hc a b
    _ ≤ ((programLength a : ℕ∞) + d) + c := by gcongr; exact hd a
    _ = ((programLength a + d + c : ℕ) : ℕ∞) := by push_cast; ring

private lemma lemma3_part2_extend_condition (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ a b w : BitString,
      natCondK D a (pairCode b w) ≤ natCondK D a b + c := by
  obtain ⟨c, hc⟩ := condK_condPair_left_le D hD
  refine ⟨c, fun a b w => ?_⟩
  have ha := lemma3_part2_cond_ne_top D hD a (pairCode b w)
  have hb := lemma3_part2_cond_ne_top D hD a b
  have hleft : condK D a (pairCode b w) = ((natCondK D a (pairCode b w) : ℕ) : ℕ∞) :=
    (ENat.natCast_toNat ha).symm
  have hright : condK D a b = ((natCondK D a b : ℕ) : ℕ∞) :=
    (ENat.natCast_toNat hb).symm
  have h := hc a b w
  rw [hleft, hright] at h
  exact_mod_cast h

private lemma lemma3_part2_shrink_nil (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ a b : BitString,
      natCondK D a b ≤ natCondK D a (pairCode b []) + c := by
  obtain ⟨c, hc⟩ := condK_cond_map_le D hD (fun w => pairCode w [])
    (pairCode_computable.comp (Computable.id.pair (Computable.const [])))
  refine ⟨c, fun a b => ?_⟩
  have ha := lemma3_part2_cond_ne_top D hD a b
  have hb := lemma3_part2_cond_ne_top D hD a (pairCode b [])
  have hleft : condK D a b = ((natCondK D a b : ℕ) : ℕ∞) :=
    (ENat.natCast_toNat ha).symm
  have hright : condK D a (pairCode b []) = ((natCondK D a (pairCode b []) : ℕ) : ℕ∞) :=
    (ENat.natCast_toNat hb).symm
  have h := hc a b
  rw [hleft, hright] at h
  exact_mod_cast h

/-- **Lemma 3, part 2.** If `K'(x̄', ȳ) ≤ K'(x̄, ȳ) + δ₁ e` with `δ₁ ≥ 0` and
`K(x̄', ȳ | z) ≥ K(x̄, ȳ) − δ₂`, then `K'(x̄', ȳ | z) ≥ K'(x̄, ȳ) − (2δ₁ + δ₂ + O(log N)) e`,
`N = K(x̄, ȳ)`.  Proof: Appendix. -/
theorem lemma3_part2 (D : Map) (hD : isOptimalConditional D) (n m : ℕ) :
    ∃ c : ℕ, ∀ (x x' : Fin n → BitString) (y : Fin m → BitString) (z : BitString) (δ₁ δ₂ : ℤ),
      0 ≤ δ₁ →
      (∀ V W : Finset (Fin (n + m)), V.Nonempty → Disjoint V W →
        (subCondK D (Fin.append x' y) V W : ℤ) ≤ subCondK D (Fin.append x y) V W + δ₁) →
      (natK D (tupleCode (Fin.append x y)) : ℤ) ≤
        natCondK D (tupleCode (Fin.append x' y)) z + δ₂ →
      ∀ V W : Finset (Fin (n + m)), V.Nonempty → Disjoint V W →
        (subCondK D (Fin.append x y) V W : ℤ) ≤ subCondKRel D (Fin.append x' y) z V W +
          (2 * δ₁ + δ₂ + logSlack c (natK D (tupleCode (Fin.append x y)))) := by
  obtain ⟨a, ha⟩ := lemma3_part2_extend_condition D hD
  obtain ⟨b, hb⟩ := lemma3_part2_shrink_nil D hD
  obtain ⟨c₀, hc₀⟩ := lemma3_relativized D hD (n + m)
  refine ⟨c₀ + (2 * a + 3 * b), fun x x' y z δ₁ δ₂ hδ hprof hK => ?_⟩
  let u := Fin.append x y
  let u' := Fin.append x' y
  intro V W hV hVW
  have hprof' : ∀ V W : Finset (Fin (n + m)), V.Nonempty → Disjoint V W →
      (subCondKRel D u' z V W : ℤ) ≤ subCondKRel D u [] V W + (δ₁ + a + b) := by
    intro V W hV hVW
    have hA := ha (subtupleCode u' V) (subtupleCode u' W) z
    have hB := hb (subtupleCode u V) (subtupleCode u W)
    have hA' : (subCondKRel D u' z V W : ℤ) ≤ subCondK D u' V W + a := by
      change (natCondK D (subtupleCode u' V) (pairCode (subtupleCode u' W) z) : ℤ) ≤ _
      exact_mod_cast hA
    have hB' : (subCondK D u V W : ℤ) ≤ subCondKRel D u [] V W + b := by
      change (natCondK D (subtupleCode u V) (subtupleCode u W) : ℤ) ≤
        natCondK D (subtupleCode u V) (pairCode (subtupleCode u W) []) + b
      exact_mod_cast hB
    have hmid := hprof V W hV hVW
    change (subCondK D u' V W : ℤ) ≤ subCondK D u V W + δ₁ at hmid
    omega
  have hK' : (natCondK D (tupleCode u) [] : ℤ) ≤ natCondK D (tupleCode u') z + δ₂ := by
    simpa [u, natK, natCondK, plainK] using hK
  have hout := hc₀ u u' [] z (δ₁ + a + b) δ₂ (by omega) hprof' hK' V W hV hVW
  have hleft := hb (subtupleCode u V) (subtupleCode u W)
  have hleft' : (subCondK D u V W : ℤ) ≤ subCondKRel D u [] V W + b := by
    change (natCondK D (subtupleCode u V) (subtupleCode u W) : ℤ) ≤
      natCondK D (subtupleCode u V) (pairCode (subtupleCode u W) []) + b
    exact_mod_cast hleft
  have hN : natCondK D (tupleCode u) [] = natK D (tupleCode u) := by
    simp [natK, natCondK, plainK]
  rw [hN] at hout
  have hslack : 2 * a + 3 * b ≤ logSlack (2 * a + 3 * b) (natK D (tupleCode u)) := by
    unfold logSlack
    omega
  have hout' : (subCondK D u V W : ℤ) ≤ subCondKRel D u' z V W +
      (2 * δ₁ + δ₂ + logSlack c₀ (natK D (tupleCode u)) + (2 * a + 3 * b)) := by
    omega
  rw [logSlack_add_constants c₀ (2 * a + 3 * b) (natK D (tupleCode u))]
  have hleft'' : (subCondK D (Fin.append x y) V W : ℤ) ≤
      subCondKRel D (Fin.append x y) [] V W + b := by
    simpa [u] using hleft'
  have hout'' : (subCondKRel D (Fin.append x y) [] V W : ℤ) ≤
      subCondKRel D (Fin.append x' y) z V W +
        (2 * (δ₁ + a + b) + δ₂ + logSlack c₀ (natK D (tupleCode (Fin.append x y)))) := by
    simpa [u, u'] using hout
  have hslackNat : 2 * a + 3 * b ≤
      logSlack (2 * a + 3 * b) (natK D (tupleCode (Fin.append x y))) := by
    simpa [u] using hslack
  have hslack' : (2 * a + 3 * b : ℤ) ≤
      logSlack (2 * a + 3 * b) (natK D (tupleCode (Fin.append x y))) := by
    exact_mod_cast hslackNat
  simp only [u, u'] at *
  omega

end Kolmogorov.Relativization
