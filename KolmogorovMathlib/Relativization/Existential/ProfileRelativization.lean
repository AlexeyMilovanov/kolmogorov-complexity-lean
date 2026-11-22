/-
Copyright (c) 2026 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Relativization.Definitions
import KolmogorovMathlib.Relativization.Typization
import KolmogorovMathlib.Relativization.CombinatorialEntropy
import KolmogorovMathlib.Relativization.QuantifierFree
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.LemmaOmpBlockCounting
import KolmogorovMathlib.CommonInformation.Splitting
import Mathlib.Logic.Equiv.Fin.Basic
import KolmogorovMathlib.MonotoneComplexity.REClosure
import KolmogorovMathlib.AlgorithmicRandomness.NatLogPrimrec
import KolmogorovMathlib.StoppingComplexity.CeilLog

/-!
# Profile Relativization

This module formalizes existential profile relativization, including extended forms of Theorems 4
and 5.
These results are from Muchnik and Romashchenko, “Stability of properties of Kolmogorov complexity
under relativization.”
-/

namespace Kolmogorov.Relativization

open Finset

/-- bound the number of
tuples with conditional complexity at most `k` by the standard compressible-string count. -/
private lemma theorem4_extended_count_bound
    (D : Map) (hD : isOptimalConditional D) (n : ℕ) (y : BitString) (k : ℕ)
    (A : Set (Fin n → BitString))
    (hBound : ∀ a, a ∈ A → natCondK D (tupleCode a) y ≤ k) :
    A.ncard ≤ 2 ^ (k + 1) := by
  classical
  let C := Kolmogorov.compressibleWords D y k
  have himage : tupleCode '' A ⊆ (C : Set BitString) := by
    intro z hz
    obtain ⟨a, ha, rfl⟩ := hz
    have hnat := hBound a ha
    have hne : condK D (tupleCode a) y ≠ ⊤ := by
      obtain ⟨c, hc⟩ := condK_le_plainK D hD
      obtain ⟨d, hd⟩ := plainK_le_length D hD
      apply ne_top_of_le_natCast_add
      calc
        condK D (tupleCode a) y ≤ plainK D (tupleCode a) + c := hc _ _
        _ ≤ (programLength (tupleCode a) : ENat) + d + c := by
          gcongr
          exact hd _
    have hcond : condK D (tupleCode a) y ≤ (k : ENat) := by
      rw [← ENat.natCast_toNat hne]
      exact_mod_cast hnat
    change tupleCode a ∈ Kolmogorov.compressibleWords D y k
    rw [Kolmogorov.compressibleWords, Finset.mem_filter]
    refine ⟨?_, hcond⟩
    obtain ⟨p, hpLen, hpProd⟩ := (Kolmogorov.condK_le_iff D (tupleCode a) y k).mp hcond
    rw [Kolmogorov.generatedWords, List.mem_toFinset, List.mem_filterMap]
    exact ⟨p, Kolmogorov.mem_programsLe k p hpLen,
      Kolmogorov.progToOut_eq_some.mpr hpProd⟩
  have himageFin : (tupleCode '' A).Finite := (C.finite_toSet).subset himage
  have htupleInj : Function.Injective (tupleCode : (Fin n → BitString) → BitString) := by
    intro a b hab
    apply List.ofFn_injective
    exact Kolmogorov.listCode_injective hab
  have himageCard : (tupleCode '' A).ncard = A.ncard :=
    Set.ncard_image_of_injective A htupleInj
  have hleC : (tupleCode '' A).ncard ≤ C.card := by
    calc
      (tupleCode '' A).ncard ≤ (C : Set BitString).ncard :=
        Set.ncard_le_ncard himage C.finite_toSet
      _ = C.card := Set.ncard_coe_finset C
  calc
    A.ncard = (tupleCode '' A).ncard := himageCard.symm
    _ ≤ C.card := hleC
    _ ≤ 2 ^ (k + 1) := Nat.le_of_lt (Kolmogorov.card_compressibleWordsLt D y k)

/-- choose a member of the
typization of `y` given `x` whose conditional complexity given `(x,z)` retains the complexity
of `y` given `x`, up to logarithmic slack. -/
private theorem theorem4_extended_typization_choice
    (D : Map) (hD : isOptimalConditional D) (n m : ℕ) :
    ∃ c : ℕ, ∀ (x : Fin n → BitString) (z : BitString) (y : Fin m → BitString),
      ∃ y', y' ∈ typization D y x ∧
        natCondK D (tupleCode y) (tupleCode x) ≤
          natCondK D (tupleCode y') (pairCode (tupleCode x) z) +
            logSlack c (natK D (tupleCode (Fin.append y x))) := by
  obtain ⟨cLemma, hLemma⟩ := lemma1 D hD m n
  refine ⟨cLemma + 1, ?_⟩
  intro x z y
  let T : Set (Fin m → BitString) := typization D y x
  have hLemmaXY := hLemma y x
  have hyT : y ∈ T := by
    change ExtProfileLe D (Fin.append y x) (Fin.append y x)
    intro V W hV hdis
    exact le_rfl
  have hTfin : T.Finite := hLemmaXY.1
  let F := hTfin.toFinset
  have hTnonempty : F.Nonempty := hTfin.toFinset_nonempty.mpr ⟨y, hyT⟩
  let cond : BitString := pairCode (tupleCode x) z
  obtain ⟨y', hy'F, hmax⟩ := F.exists_max_image
    (fun a => natCondK D (tupleCode a) cond) hTnonempty
  have hy'T : y' ∈ T := hTfin.mem_toFinset.mp (by simpa [F] using hy'F)
  have hmaxBound : ∀ a, a ∈ T → natCondK D (tupleCode a) cond ≤
      natCondK D (tupleCode y') cond := by
    intro a ha
    exact hmax a (by simpa [F] using hTfin.mem_toFinset.mpr ha)
  have hcount := theorem4_extended_count_bound D hD m cond
    (natCondK D (tupleCode y') cond) T hmaxBound
  let s := logSlack cLemma (natK D (tupleCode (Fin.append y x)))
  have hpow : 2 ^ natCondK D (tupleCode y) (tupleCode x) ≤
      2 ^ (natCondK D (tupleCode y') cond + 1 + s) := by
    calc
      2 ^ natCondK D (tupleCode y) (tupleCode x) ≤ T.ncard * 2 ^ s := by
        simpa [T, s, Nat.mul_comm] using hLemmaXY.2.2
      _ ≤ 2 ^ (natCondK D (tupleCode y') cond + 1) * 2 ^ s := by
        exact Nat.mul_le_mul_right (2 ^ s) (by simpa using hcount)
      _ = 2 ^ (natCondK D (tupleCode y') cond + 1 + s) := by
        simp only [Nat.pow_add, Nat.pow_succ]
  have hExp : natCondK D (tupleCode y) (tupleCode x) ≤
      natCondK D (tupleCode y') cond + 1 + s :=
    (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hpow
  have hSlackOne : 1 ≤ logSlack 1 (natK D (tupleCode (Fin.append y x))) := by
    unfold logSlack
    simp only [one_mul]
    omega
  have hSlackAbsorb : s + 1 ≤
      logSlack (cLemma + 1) (natK D (tupleCode (Fin.append y x))) := by
    calc
      s + 1 ≤ s + logSlack 1 (natK D (tupleCode (Fin.append y x))) :=
        Nat.add_le_add_left hSlackOne _
      _ = logSlack (cLemma + 1) (natK D (tupleCode (Fin.append y x))) := by
        dsimp [s]
        exact logSlack_add_const cLemma 1 _
  refine ⟨y', hy'T, ?_⟩
  change natCondK D (tupleCode y) (tupleCode x) ≤
    natCondK D (tupleCode y') cond +
      logSlack (cLemma + 1) (natK D (tupleCode (Fin.append y x)))
  omega

/-- coding the two tuple
blocks in the opposite order costs a constant, even when the original code also carries `z`. -/
private theorem theorem4_extended_swap_code_bound
    (D : Map) (hD : isOptimalConditional D) (n m : ℕ) :
    ∃ c : ℕ, ∀ (x : Fin n → BitString) (z : BitString) (y : Fin m → BitString),
      natK D (tupleCode (Fin.append y x)) ≤
        natK D (pairCode (tupleCode (Fin.append x y)) z) + c := by
  let swapTupleCode (w : BitString) : BitString :=
    listCode ((decodeListCode w).drop n ++ (decodeListCode w).take n)
  have hSwapComp : Computable swapTupleCode := by
    unfold swapTupleCode
    exact listCode_computable.comp
      ((Primrec.list_append.comp
        (Primrec.list_drop.comp (Primrec.const n) decodeListCode_primrec)
        (Primrec.list_take.comp (Primrec.const n) decodeListCode_primrec)).to_comp)
  let f (w : BitString) := swapTupleCode (decodeFirst w)
  have hf : Computable f := hSwapComp.comp decodeFirst_computable
  obtain ⟨c, hMap⟩ := plainK_map_le D hD f hf
  refine ⟨c, ?_⟩
  intro x z y
  let a := tupleCode (Fin.append x y)
  let b := tupleCode (Fin.append y x)
  let p := pairCode a z
  have hcode : swapTupleCode a = b := by
    dsimp [a, b, swapTupleCode, tupleCode]
    rw [decodeListCode_listCode, List.ofFn_fin_append]
    rw [List.drop_append_of_le_length (by simp),
      List.take_append_of_le_length (by simp)]
    have hlen : (List.ofFn x).length = n := List.length_ofFn
    have hdrop : (List.ofFn x).drop n = [] := by
      exact List.drop_eq_nil_of_le (by omega)
    have htake : (List.ofFn x).take n = List.ofFn x := by
      exact (List.take_eq_self_iff (List.ofFn x)).2 hlen.le
    rw [hdrop, htake]
    simp [List.ofFn_fin_append]
  have hRaw : plainK D b ≤ plainK D p + c := by
    simpa [f, p, a, b, hcode, decodeFirst_pairCode] using hMap p
  have hneB : plainK D b ≠ ⊤ := plainK_ne_top D hD b
  have hneP : plainK D p ≠ ⊤ := plainK_ne_top D hD p
  have hCast : ((plainK D b).toNat : ENat) ≤
      (((natK D p + c : ℕ) : ℕ) : ENat) := by
    calc
      ((plainK D b).toNat : ENat) = plainK D b := ENat.natCast_toNat hneB
      _ ≤ plainK D p + c := hRaw
      _ = (((natK D p + c : ℕ) : ℕ) : ENat) := by
        rw [← ENat.natCast_toNat hneP]
        push_cast
        rfl
  have hNat : natK D b ≤ natK D p + c := by exact_mod_cast hCast
  simpa [b, p] using hNat

private def theorem4_extended_typization_profile_swapIndex
    (n m : ℕ) : Fin (n + m) ≃ Fin (m + n) :=
  finAddFlip

/-- Reorder a list code by taking the entries at the specified positions. -/
private def theorem4_extended_typization_profile_reindexList
    (idxs : List ℕ) (w : BitString) : BitString :=
  listCode (idxs.map fun i => (decodeListCode w).getD i [])

private lemma theorem4_extended_typization_profile_reindexList_computable
    (idxs : List ℕ) :
    Computable (theorem4_extended_typization_profile_reindexList idxs) := by
  have hMap : Primrec (fun (w : BitString) => idxs.map fun i => (decodeListCode w).getD i []) := by
    induction idxs with
    | nil =>
        exact Primrec.const []
    | cons head tail ih =>
        have h_getD : Primrec (fun (w : BitString) => (decodeListCode w).getD head []) := by
          exact (Primrec.list_getD (α := BitString) ([] : BitString)).comp
            decodeListCode_primrec (Primrec.const head)
        change Primrec (fun w => (decodeListCode w).getD head [] ::
          tail.map fun i => (decodeListCode w).getD i [])
        exact Primrec₂.comp Primrec.list_cons h_getD ih
  exact listCode_computable.comp hMap.to_comp

private def theorem4_extended_typization_profile_reindexIndices
    {n m : ℕ} (σ : Fin n ≃ Fin m) (I : Finset (Fin n)) : List ℕ :=
  (I.sort (· ≤ ·)).map fun i =>
    List.findIdx (· == σ i) ((I.image σ).sort (· ≤ ·))

/-- The computable list reordering turns a subtuple in the permuted tuple back into the original
coordinate order. -/
private lemma theorem4_extended_typization_profile_reindexCode
    {n m : ℕ} (σ : Fin n ≃ Fin m) (I : Finset (Fin n))
    (u : Fin n → BitString) (v : Fin m → BitString) (h : v ∘ σ = u) :
    theorem4_extended_typization_profile_reindexList
        (theorem4_extended_typization_profile_reindexIndices σ I)
        (subtupleCode v (I.image σ)) = subtupleCode u I := by
  dsimp [theorem4_extended_typization_profile_reindexList,
    theorem4_extended_typization_profile_reindexIndices, subtupleCode]
  rw [decodeListCode_listCode]
  apply congrArg listCode
  rw [List.map_map]
  apply List.map_congr_left
  intro i hi
  have hiI : i ∈ I := by simpa only [Finset.mem_sort] using hi
  have hiImage : σ i ∈ (I.image σ).sort (· ≤ ·) := by
    rw [Finset.mem_sort, Finset.mem_image]
    exact ⟨i, hiI, rfl⟩
  let L := (I.image σ).sort (· ≤ ·)
  have hidx : List.findIdx (· == σ i) L < L.length := by
    apply List.findIdx_lt_length_of_exists
    exact ⟨σ i, by simpa [L] using hiImage, by simp⟩
  have hget : L.get ⟨List.findIdx (· == σ i) L, hidx⟩ = σ i := by
    have hfind := List.findIdx_getElem (p := (· == σ i)) (xs := L) (w := hidx)
    have hbeq : (L.get ⟨List.findIdx (· == σ i) L, hidx⟩ == σ i) = true := by
      simpa using hfind
    exact eq_of_beq hbeq
  have hidxMap : List.findIdx (· == σ i) L < (L.map v).length := by
    simpa using hidx
  have hvalue : (L.map v).getD (List.findIdx (· == σ i) L) [] = v (σ i) := by
    rw [List.getD_eq_get _ _ ⟨List.findIdx (· == σ i) L, hidxMap⟩]
    rw [show (L.map v).get ⟨List.findIdx (· == σ i) L, hidxMap⟩ =
      v (L.get ⟨List.findIdx (· == σ i) L, hidx⟩) by simp, hget]
  simpa [L, Function.comp_apply] using hvalue.trans (congrFun h i)

private lemma theorem4_extended_condK_toNat_le
    (D : Map) (hD : isOptimalConditional D) (a b c d : BitString) (k : ℕ)
    (h : condK D a b ≤ condK D c d + (k : ℕ∞)) :
    natCondK D a b ≤ natCondK D c d + k := by
  have hneB := avgCond_condK_ne_top D hD a b
  have hneD := avgCond_condK_ne_top D hD c d
  change (condK D a b).toNat ≤ (condK D c d).toNat + k
  have h' : ((condK D a b).toNat : ℕ∞) ≤
      (((condK D c d).toNat + k : ℕ) : ℕ∞) := by
    calc
      ((condK D a b).toNat : ℕ∞) = condK D a b := ENat.natCast_toNat hneB
      _ ≤ condK D c d + (k : ℕ∞) := h
      _ = ((condK D c d).toNat : ℕ∞) + (k : ℕ∞) := by rw [ENat.natCast_toNat hneD]
      _ = (((condK D c d).toNat + k : ℕ) : ℕ∞) := by push_cast; rfl
  exact_mod_cast h'

/-- A fixed coordinate equivalence changes a conditional subtuple complexity by a constant. -/
private theorem theorem4_extended_reindex_component
    (D : Map) (hD : isOptimalConditional D) {n m : ℕ} (σ : Fin n ≃ Fin m)
    (V W : Finset (Fin n)) :
    ∃ c : ℕ, ∀ (u : Fin n → BitString) (v : Fin m → BitString), v ∘ σ = u →
      natCondK D (subtupleCode u V) (subtupleCode u W) ≤
        natCondK D (subtupleCode v (V.image σ)) (subtupleCode v (W.image σ)) + c := by
  let f := theorem4_extended_typization_profile_reindexList
    (theorem4_extended_typization_profile_reindexIndices σ V)
  let g := theorem4_extended_typization_profile_reindexList
    (theorem4_extended_typization_profile_reindexIndices σ.symm
      (W.image σ))
  have hf : Computable f := by
    exact theorem4_extended_typization_profile_reindexList_computable _
  have hg : Computable g := by
    exact theorem4_extended_typization_profile_reindexList_computable _
  obtain ⟨cV, hcV⟩ := condK_map_le D hD f hf
  obtain ⟨cW, hcW⟩ := condK_cond_map_le D hD g hg
  refine ⟨cV + cW, ?_⟩
  intro u v huv
  have hReverse : u ∘ σ.symm = v := by
    funext i
    have h := congrFun huv (σ.symm i)
    simpa using h.symm
  have hCodeV := theorem4_extended_typization_profile_reindexCode
    σ V u v huv
  have hImageW : (W.image σ).image σ.symm = W := by
    ext i
    simp
  have hCodeW := theorem4_extended_typization_profile_reindexCode
    σ.symm (W.image σ) v u hReverse
  have hCodeW' : g (subtupleCode u W) = subtupleCode v (W.image σ) := by
    simpa [g, hImageW] using hCodeW
  have hOut : condK D (subtupleCode u V) (subtupleCode u W) ≤
      condK D (subtupleCode v (V.image σ)) (subtupleCode u W) + (cV : ℕ∞) := by
    rw [← show f (subtupleCode v (V.image σ)) = subtupleCode u V from hCodeV]
    exact hcV (subtupleCode v (V.image σ)) (subtupleCode u W)
  have hCondition : condK D (subtupleCode v (V.image σ)) (subtupleCode u W) ≤
      condK D (subtupleCode v (V.image σ)) (subtupleCode v (W.image σ)) + (cW : ℕ∞) := by
    rw [← hCodeW']
    exact hcW (subtupleCode v (V.image σ)) (subtupleCode u W)
  have hComplexity : condK D (subtupleCode u V) (subtupleCode u W) ≤
      condK D (subtupleCode v (V.image σ)) (subtupleCode v (W.image σ)) +
        ((cV + cW : ℕ) : ℕ∞) := by
    calc
      _ ≤ condK D (subtupleCode v (V.image σ)) (subtupleCode u W) + (cV : ℕ∞) := hOut
      _ ≤ (condK D (subtupleCode v (V.image σ)) (subtupleCode v (W.image σ)) +
          (cW : ℕ∞)) + (cV : ℕ∞) := by gcongr
      _ = _ := by push_cast; ac_rfl
  exact theorem4_extended_condK_toNat_le
    D hD (subtupleCode u V) (subtupleCode u W)
      (subtupleCode v (V.image σ)) (subtupleCode v (W.image σ)) (cV + cW) hComplexity

/-- A coordinate equivalence has one recoding constant valid for all extended-profile indices. -/
private theorem theorem4_extended_reindex_profile
    (D : Map) (hD : isOptimalConditional D) {n m : ℕ} (σ : Fin n ≃ Fin m) :
    ∃ c : ℕ, ∀ (u : Fin n → BitString) (v : Fin m → BitString), v ∘ σ = u →
      ∀ V W : Finset (Fin n),
        natCondK D (subtupleCode u V) (subtupleCode u W) ≤
          natCondK D (subtupleCode v (V.image σ)) (subtupleCode v (W.image σ)) + c := by
  classical
  have hEach : ∀ V W : Finset (Fin n),
      ∃ c : ℕ, ∀ (u : Fin n → BitString) (v : Fin m → BitString), v ∘ σ = u →
        natCondK D (subtupleCode u V) (subtupleCode u W) ≤
          natCondK D (subtupleCode v (V.image σ)) (subtupleCode v (W.image σ)) + c := by
    intro V W
    exact theorem4_extended_reindex_component
      D hD σ V W
  choose c hc using hEach
  let C := Finset.univ.sup fun p : Finset (Fin n) × Finset (Fin n) => c p.1 p.2
  refine ⟨C, ?_⟩
  intro u v huv V W
  have h := hc V W u v huv
  have hCost : c V W ≤ C := by
    change c V W ≤ Finset.univ.sup (fun p : Finset (Fin n) × Finset (Fin n) => c p.1 p.2)
    exact Finset.le_sup (f := fun p : Finset (Fin n) × Finset (Fin n) => c p.1 p.2)
      (Finset.mem_univ (V, W))
  exact h.trans (Nat.add_le_add_left hCost _)

/-- Repacking the two tuple blocks in the opposite order changes every unrelativized
extended profile component by a uniform constant. -/
private theorem theorem4_extended_reindex_plain_profile
    (D : Map) (hD : isOptimalConditional D) (n m : ℕ) :
    ∃ c : ℕ, ∀ (x : Fin n → BitString) (y : Fin m → BitString)
      (V W : Finset (Fin (n + m))), V.Nonempty → Disjoint V W →
      subCondK D (Fin.append x y) V W ≤
          subCondK D (Fin.append y x)
            (V.image (theorem4_extended_typization_profile_swapIndex n m))
            (W.image (theorem4_extended_typization_profile_swapIndex n m)) + c ∧
        subCondK D (Fin.append y x)
            (V.image (theorem4_extended_typization_profile_swapIndex n m))
            (W.image (theorem4_extended_typization_profile_swapIndex n m)) ≤
          subCondK D (Fin.append x y) V W + c := by
  obtain ⟨c₁, h₁⟩ := theorem4_extended_reindex_profile
    D hD (theorem4_extended_typization_profile_swapIndex n m)
  let σ := theorem4_extended_typization_profile_swapIndex n m
  obtain ⟨c₂, h₂⟩ := theorem4_extended_reindex_profile
    D hD σ.symm
  let C := c₁ + c₂
  refine ⟨C, ?_⟩
  intro x y V W hV hdis
  have hSwap : (Fin.append y x) ∘ σ = Fin.append x y := by
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simp [σ, theorem4_extended_typization_profile_swapIndex, finAddFlip]
    · intro j
      simp [σ, theorem4_extended_typization_profile_swapIndex, finAddFlip]
  have hSwapInv : (Fin.append x y) ∘ σ.symm = Fin.append y x := by
    funext i
    have h := congrFun hSwap (σ.symm i)
    simpa using h.symm
  have hImageV : (V.image σ).image σ.symm = V := by
    ext i
    simp
  have hImageW : (W.image σ).image σ.symm = W := by
    ext i
    simp
  have hForward := h₁ (Fin.append x y) (Fin.append y x) hSwap V W
  have hBackward := h₂ (Fin.append y x) (Fin.append x y) hSwapInv (V.image σ) (W.image σ)
  have hC₁ : c₁ ≤ C := by dsimp [C]; omega
  have hC₂ : c₂ ≤ C := by dsimp [C]; omega
  constructor
  · exact hForward.trans (Nat.add_le_add_left hC₁ _)
  · simpa [subCondK, hImageV, hImageW] using
      hBackward.trans (Nat.add_le_add_left hC₂ _)

/-- adding the oracle to a condition increases conditional complexity by at most a constant. -/
private theorem theorem4_extended_add_oracle
    (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ (a b z : BitString),
      natCondK D a (pairCode b z) ≤ natCondK D a b + c := by
  obtain ⟨c, hc⟩ := condK_cond_map_le D hD decodeFirst decodeFirst_computable
  refine ⟨c, ?_⟩
  intro a b z
  have h := hc a (pairCode b z)
  exact theorem4_extended_condK_toNat_le
    D hD a (pairCode b z) a b c (by simpa [decodeFirst_pairCode] using h)

/-- a tuple in the typization
of `y` given `x` preserves each extended profile component up to a constant after reindexing the
coordinates from `(y,x)` to `(x,y)` and adding the oracle to the condition. -/
private theorem theorem4_extended_typization_profile
    (D : Map) (hD : isOptimalConditional D) (n m : ℕ) :
    ∃ c : ℕ, ∀ (x : Fin n → BitString) (z : BitString) (y y' : Fin m → BitString),
      y' ∈ typization D y x →
      ∀ V W : Finset (Fin (n + m)), V.Nonempty → Disjoint V W →
        subCondKRel D (Fin.append x y') z V W ≤ subCondK D (Fin.append x y) V W + c := by
  obtain ⟨cReindex, hReindex⟩ :=
    theorem4_extended_reindex_plain_profile
      D hD n m
  obtain ⟨cOracle, hOracle⟩ :=
    theorem4_extended_add_oracle D hD
  refine ⟨cOracle + 2 * cReindex, ?_⟩
  intro x z y y' hTyp V W hV hdis
  let σ := theorem4_extended_typization_profile_swapIndex n m
  let V' := V.image σ
  let W' := W.image σ
  have hV' : V'.Nonempty := by
    rcases hV with ⟨i, hi⟩
    exact ⟨σ i, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩
  have hdis' : Disjoint V' W' := by
    rw [Finset.disjoint_left]
    intro i hiV hiW
    rcases Finset.mem_image.mp hiV with ⟨j, hj, rfl⟩
    rcases Finset.mem_image.mp hiW with ⟨k, hk, heq⟩
    have hEq : j = k := σ.injective heq.symm
    exact (Finset.disjoint_left.mp hdis) hj (hEq ▸ hk)
  change ExtProfileLe D (Fin.append y' x) (Fin.append y x) at hTyp
  have hProfile := hTyp V' W' hV' hdis'
  have hLeft := hReindex x y' V W hV hdis
  have hRight := hReindex x y V W hV hdis
  dsimp [V', W', σ] at hProfile hLeft hRight
  rcases hLeft with ⟨hLeft, _⟩
  rcases hRight with ⟨_, hRight⟩
  have hAddOracle := hOracle (subtupleCode (Fin.append x y') V)
    (subtupleCode (Fin.append x y') W) z
  change natCondK D (subtupleCode (Fin.append x y') V)
      (pairCode (subtupleCode (Fin.append x y') W) z) ≤
    natCondK D (subtupleCode (Fin.append x y) V) (subtupleCode (Fin.append x y) W) +
      (cOracle + 2 * cReindex)
  dsimp [subCondK] at hProfile hLeft hRight ⊢
  omega

/-- select a tuple whose relativized
extended profile is bounded above by the original profile up to logarithmic slack, while
retaining the varying block's conditional complexity given the fixed block and oracle. -/
private theorem theorem4_extended_select (D : Map) (hD : isOptimalConditional D)
    (n m : ℕ) :
    ∃ c : ℕ, ∀ (x : Fin n → BitString) (z : BitString) (y : Fin m → BitString),
        ∃ y',
          (∀ V W : Finset (Fin (n + m)), V.Nonempty → Disjoint V W →
            subCondKRel D (Fin.append x y') z V W ≤
              subCondK D (Fin.append x y) V W +
                logSlack c (natK D (pairCode (tupleCode (Fin.append x y)) z))) ∧
          natCondK D (tupleCode y) (tupleCode x) ≤
            natCondK D (tupleCode y') (pairCode (tupleCode x) z) +
              logSlack c (natK D (pairCode (tupleCode (Fin.append x y)) z)) := by
  obtain ⟨cSelect, hSelect⟩ :=
    theorem4_extended_typization_choice D hD n m
  obtain ⟨cSwap, hSwap⟩ :=
    theorem4_extended_swap_code_bound D hD n m
  obtain ⟨cBudget, hBudget⟩ := logSlack_absorb_of_le_linear cSelect 1 cSwap
  obtain ⟨cProfile, hProfile⟩ :=
    theorem4_extended_typization_profile D hD n m
  let C := cBudget + cProfile
  refine ⟨C, ?_⟩
  intro x z y
  obtain ⟨y', hTyp, hConditional⟩ := hSelect x z y
  have hNrev : natK D (tupleCode (Fin.append y x)) ≤
      natK D (pairCode (tupleCode (Fin.append x y)) z) + cSwap := by
    exact hSwap x z y
  have hConditionalBudget :
      logSlack cSelect (natK D (tupleCode (Fin.append y x))) ≤
        logSlack cBudget (natK D (pairCode (tupleCode (Fin.append x y)) z)) := by
    exact hBudget _ _ (by simpa using hNrev)
  refine ⟨y', ?_, ?_⟩
  · intro V W hV hdis
    have h := hProfile x z y y' hTyp V W hV hdis
    have hSlack : cProfile ≤ logSlack C
        (natK D (pairCode (tupleCode (Fin.append x y)) z)) := by
      unfold logSlack C
      omega
    omega
  · have hmono : logSlack cBudget
        (natK D (pairCode (tupleCode (Fin.append x y)) z)) ≤
        logSlack C (natK D (pairCode (tupleCode (Fin.append x y)) z)) := by
      exact logSlack_mono_left (by dsimp [C]; omega) _
    have hConditional' := hConditional.trans (Nat.add_le_add_left hConditionalBudget _)
    exact hConditional'.trans (Nat.add_le_add_left hmono _)

private def theorem4_extended_chain_joinTuple (w : BitString) : BitString :=
  listCode (decodeListCode (decodeFirst w) ++ decodeListCode (decodeSecond w))

private theorem theorem4_extended_chain_joinTuple_computable :
    Computable theorem4_extended_chain_joinTuple := by
  unfold theorem4_extended_chain_joinTuple
  exact listCode_computable.comp
    (Computable₂.comp Primrec.list_append.to_comp
      (decodeListCode_computable.comp decodeFirst_computable)
      (decodeListCode_computable.comp decodeSecond_computable))

private lemma theorem4_extended_chain_joinTuple_correct {n m : ℕ}
    (x : Fin n → BitString) (y : Fin m → BitString) :
    theorem4_extended_chain_joinTuple
        (pairCode (tupleCode x) (tupleCode y)) = tupleCode (Fin.append x y) := by
  simp only [theorem4_extended_chain_joinTuple, decodeFirst_pairCode,
    decodeSecond_pairCode, tupleCode, decodeListCode_listCode, List.ofFn_fin_append]

private def theorem4_extended_chain_splitTuple (n : ℕ) (w : BitString) : BitString :=
  pairCode (listCode ((decodeListCode w).take n))
    (listCode ((decodeListCode w).drop n))

private theorem theorem4_extended_chain_takeTuple_computable (n : ℕ) :
    Computable (fun w : BitString => listCode ((decodeListCode w).take n)) :=
  listCode_computable.comp
    ((Primrec.list_take.comp (Primrec.const n) decodeListCode_primrec).to_comp)

private theorem theorem4_extended_chain_dropTuple_computable (n : ℕ) :
    Computable (fun w : BitString => listCode ((decodeListCode w).drop n)) :=
  listCode_computable.comp
    ((Primrec.list_drop.comp (Primrec.const n) decodeListCode_primrec).to_comp)

private theorem theorem4_extended_chain_splitTuple_computable (n : ℕ) :
    Computable (theorem4_extended_chain_splitTuple n) := by
  have hPair : Computable₂ (fun (x y : BitString) => pairCode x y) :=
    pairCode_computable
  exact hPair.comp (theorem4_extended_chain_takeTuple_computable n)
    (theorem4_extended_chain_dropTuple_computable n)

private lemma theorem4_extended_chain_splitTuple_correct {n m : ℕ}
    (x : Fin n → BitString) (y : Fin m → BitString) :
    theorem4_extended_chain_splitTuple n (tupleCode (Fin.append x y)) =
      pairCode (tupleCode x) (tupleCode y) := by
  unfold theorem4_extended_chain_splitTuple
  rw [show decodeListCode (tupleCode (Fin.append x y)) =
      List.ofFn (Fin.append x y) by simp [tupleCode], List.ofFn_fin_append]
  change pairCode (listCode ((List.ofFn x ++ List.ofFn y).take n))
      (listCode ((List.ofFn x ++ List.ofFn y).drop n)) =
    pairCode (listCode (List.ofFn x)) (listCode (List.ofFn y))
  have hlen : (List.ofFn x).length = n := by simp
  rw [List.take_append_of_le_length hlen.symm.le,
    List.drop_append_of_le_length hlen.symm.le]
  have htake : (List.ofFn x).take n = List.ofFn x :=
    List.take_of_length_le (by omega)
  have hdrop : (List.ofFn x).drop n = [] := by
    apply List.drop_eq_nil_of_le
    omega
  rw [htake, hdrop, List.nil_append]

/-- the chain rule for joined tuples turns
the information bound for `x` and a lower bound on the complexity of `y'` given `(x,z)` into a
lower bound on the complexity of `(x,y')` given `z`. -/
private theorem theorem4_extended_chain (D : Map) (hD : isOptimalConditional D)
    (n m c₀ : ℕ) :
    ∃ c : ℕ, ∀ (x : Fin n → BitString) (z : BitString) (δ : ℕ),
      MutualInfoLe D (tupleCode x) z δ →
        ∀ (y y' : Fin m → BitString),
          natCondK D (tupleCode y) (tupleCode x) ≤
            natCondK D (tupleCode y') (pairCode (tupleCode x) z) +
              logSlack c₀ (natK D (pairCode (tupleCode (Fin.append x y)) z)) →
          natK D (tupleCode (Fin.append x y)) ≤
            natCondK D (tupleCode (Fin.append x y')) z + δ +
              logSlack c (natK D (pairCode (tupleCode (Fin.append x y)) z)) := by
  obtain ⟨cJoin, hJoin⟩ := plainK_map_le D hD
    theorem4_extended_chain_joinTuple theorem4_extended_chain_joinTuple_computable
  obtain ⟨cSplit, hSplit⟩ := plainK_map_le D hD
    (theorem4_extended_chain_splitTuple n)
    (theorem4_extended_chain_splitTuple_computable n)
  obtain ⟨cSplitCond, hSplitCond⟩ := condK_map_le D hD
    (theorem4_extended_chain_splitTuple n)
    (theorem4_extended_chain_splitTuple_computable n)
  obtain ⟨cFirst, hFirst⟩ := plainK_map_le D hD decodeFirst decodeFirst_computable
  obtain ⟨cPair, hPair⟩ := Kolmogorov.pairPlainK_symmetryOfInformation_values D hD
  obtain ⟨cRelPair, hRelPair⟩ :=
    Kolmogorov.condK_pairCode_symmetryOfInformation_values D hD
  obtain ⟨cFold, hFold⟩ := logSlack_absorb_of_le_linear
    (cPair + cRelPair) 1 (cFirst + cSplit + cSplitCond + 1)
  let C := c₀ + cFold + cJoin + cSplitCond
  refine ⟨C, ?_⟩
  intro x z δ hInfo y y' hY
  let X := tupleCode x
  let Y := tupleCode y
  let Y' := tupleCode y'
  let u := Fin.append x y
  let u' := Fin.append x y'
  let N := natK D (pairCode (tupleCode u) z)
  let kPair := natK D (pairCode X Y)
  let kRelPair := natCondK D (pairCode X Y') z
  have hJoinRaw := hJoin (pairCode X Y)
  rw [theorem4_extended_chain_joinTuple_correct x y] at hJoinRaw
  have hneU : plainK D (tupleCode u) ≠ ⊤ := plainK_ne_top D hD (tupleCode u)
  have hnePair : plainK D (pairCode X Y) ≠ ⊤ :=
    plainK_ne_top D hD (pairCode X Y)
  have hJoinNat : natK D (tupleCode u) ≤ kPair + cJoin := by
    rw [← ENat.natCast_toNat hneU, ← ENat.natCast_toNat hnePair] at hJoinRaw
    exact_mod_cast hJoinRaw
  have hSplitRaw := hSplit (tupleCode u)
  rw [theorem4_extended_chain_splitTuple_correct x y] at hSplitRaw
  have hSplitNat : kPair ≤ natK D (tupleCode u) + cSplit := by
    rw [← ENat.natCast_toNat hnePair, ← ENat.natCast_toNat hneU] at hSplitRaw
    exact_mod_cast hSplitRaw
  have hFirstRaw := hFirst (pairCode (tupleCode u) z)
  rw [decodeFirst_pairCode] at hFirstRaw
  have hneN : plainK D (pairCode (tupleCode u) z) ≠ ⊤ :=
    plainK_ne_top D hD (pairCode (tupleCode u) z)
  have hKBound : natK D (tupleCode u) ≤ N + cFirst := by
    rw [← ENat.natCast_toNat hneU, ← ENat.natCast_toNat hneN] at hFirstRaw
    exact_mod_cast hFirstRaw
  have hSplitCondRaw := hSplitCond (tupleCode u') z
  rw [theorem4_extended_chain_splitTuple_correct x y'] at hSplitCondRaw
  have hneRelPair : condK D (pairCode X Y') z ≠ ⊤ :=
    avgCond_condK_ne_top D hD (pairCode X Y') z
  have hneRelU : condK D (tupleCode u') z ≠ ⊤ :=
    avgCond_condK_ne_top D hD (tupleCode u') z
  have hSplitCondNat : kRelPair ≤ natCondK D (tupleCode u') z + cSplitCond := by
    rw [← ENat.natCast_toNat hneRelPair, ← ENat.natCast_toNat hneRelU] at hSplitCondRaw
    exact_mod_cast hSplitCondRaw
  have hxVal : Kolmogorov.HasPlainComplexityValue D X (natK D X) := by
    change plainK D X = ((plainK D X).toNat : ℕ∞)
    exact (ENat.natCast_toNat (plainK_ne_top D hD X)).symm
  have hyVal : Kolmogorov.HasPlainConditionalComplexityValue D Y X
      (natCondK D Y X) := by
    change condK D Y X = ((condK D Y X).toNat : ℕ∞)
    exact (ENat.natCast_toNat (avgCond_condK_ne_top D hD Y X)).symm
  have hpairVal : Kolmogorov.HasPlainComplexityValue D (pairCode X Y) kPair := by
    change plainK D (pairCode X Y) = ((plainK D (pairCode X Y)).toNat : ℕ∞)
    exact (ENat.natCast_toNat hnePair).symm
  have hPairChain := hPair X Y (natK D X) (natCondK D Y X) kPair
    hxVal hyVal hpairVal
  have hRelXVal : Kolmogorov.HasPlainConditionalComplexityValue D X z
      (natCondK D X z) := by
    change condK D X z = ((condK D X z).toNat : ℕ∞)
    exact (ENat.natCast_toNat (avgCond_condK_ne_top D hD X z)).symm
  have hRelYVal : Kolmogorov.HasPlainConditionalComplexityValue D Y'
      (pairCode X z) (natCondK D Y' (pairCode X z)) := by
    change condK D Y' (pairCode X z) =
      ((condK D Y' (pairCode X z)).toNat : ℕ∞)
    exact (ENat.natCast_toNat
      (avgCond_condK_ne_top D hD Y' (pairCode X z))).symm
  have hRelPairVal : Kolmogorov.HasPlainConditionalComplexityValue D
      (pairCode X Y') z kRelPair := by
    change condK D (pairCode X Y') z =
      ((condK D (pairCode X Y') z).toNat : ℕ∞)
    exact (ENat.natCast_toNat hneRelPair).symm
  have hRelSym := hRelPair X Y' z (natCondK D X z)
    (natCondK D Y' (pairCode X z)) kRelPair hRelXVal hRelYVal hRelPairVal
  have hInfo' : natK D X ≤ natCondK D X z + δ := by
    simpa only [MutualInfoLe, X] using hInfo
  have hY' : natCondK D Y X ≤
      natCondK D Y' (pairCode X z) + logSlack c₀ N := by
    simpa [X, Y, Y', u, N] using hY
  have hMainBudget : logSlack c₀ N + logSlack cFold N +
      (cJoin + cSplitCond) ≤ logSlack C N := by
    calc
      logSlack c₀ N + logSlack cFold N + (cJoin + cSplitCond) =
          logSlack (c₀ + cFold) N + (cJoin + cSplitCond) := by
            rw [logSlack_add_const]
      _ ≤ logSlack (c₀ + cFold) N + logSlack (cJoin + cSplitCond) N := by
        apply Nat.add_le_add_left
        unfold logSlack
        omega
      _ = logSlack ((c₀ + cFold) + (cJoin + cSplitCond)) N :=
        logSlack_add_const _ _ _
      _ = logSlack C N := by congr 1; omega
  by_cases hEasy : natK D (tupleCode u) ≤ natCondK D (tupleCode u') z
  · calc
      natK D (tupleCode u) ≤ natCondK D (tupleCode u') z := hEasy
      _ ≤ natCondK D (tupleCode u') z + δ +
          logSlack C (natK D (pairCode (tupleCode u) z)) := by omega
  · have hHard : natCondK D (tupleCode u') z < natK D (tupleCode u) := by omega
    have hPairArg : kPair + 1 ≤ N + (cFirst + cSplit + cSplitCond + 1) := by
      dsimp [kPair, N]
      omega
    have hRelPairArg : kRelPair + 1 ≤ N + (cFirst + cSplit + cSplitCond + 1) := by
      dsimp [kRelPair, N]
      omega
    have hSlackPair : logSlack cPair (kPair + 1) +
        logSlack cRelPair (kRelPair + 1) ≤ logSlack cFold N := by
      calc
        _ ≤ logSlack cPair (N + (cFirst + cSplit + cSplitCond + 1)) +
            logSlack cRelPair (N + (cFirst + cSplit + cSplitCond + 1)) := by
          exact Nat.add_le_add
            (logSlack_mono_right cPair hPairArg)
            (logSlack_mono_right cRelPair hRelPairArg)
        _ = logSlack (cPair + cRelPair)
            (N + (cFirst + cSplit + cSplitCond + 1)) :=
          logSlack_add_const cPair cRelPair _
        _ ≤ logSlack cFold N := hFold N _ (by omega)
    have hMain : natK D (tupleCode u) ≤ natCondK D (tupleCode u') z + δ +
        (logSlack c₀ N + logSlack cPair (kPair + 1) +
          logSlack cRelPair (kRelPair + 1) + cJoin + cSplitCond) := by
      have hPairChain' : kPair ≤ natK D X + natCondK D Y X +
          logSlack cPair (kPair + 1) := hPairChain.1
      have hRelSym' : natCondK D X z + natCondK D Y' (pairCode X z) ≤
          kRelPair + logSlack cRelPair (kRelPair + 1) := hRelSym.2
      omega
    have hCost' : logSlack c₀ N +
        (logSlack cPair (kPair + 1) +
          (logSlack cRelPair (kRelPair + 1) + cJoin + cSplitCond)) ≤
        logSlack C N := by omega
    calc
      natK D (tupleCode u) ≤ natCondK D (tupleCode u') z + δ +
          (logSlack c₀ N + logSlack cPair (kPair + 1) +
            logSlack cRelPair (kRelPair + 1) + cJoin + cSplitCond) := hMain
      _ ≤ natCondK D (tupleCode u') z + δ + logSlack C N := by
        have h := Nat.add_le_add_left hCost'
          (natCondK D (tupleCode u') z + δ)
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h

/-- convert conditional `ENat` complexity
bounds to the natural shadows used in the profile inequalities. -/
private lemma theorem4_extended_condK_toNat_le_same_condition
    (D : Map) (hD : isOptimalConditional D)
    (a b c : BitString) (k : ℕ)
    (h : condK D a b ≤ condK D a c + (k : ℕ∞)) :
    natCondK D a b ≤ natCondK D a c + k := by
  have hneB := avgCond_condK_ne_top D hD a b
  have hneC := avgCond_condK_ne_top D hD a c
  change (condK D a b).toNat ≤ (condK D a c).toNat + k
  have h' : ((condK D a b).toNat : ℕ∞) ≤
      (((condK D a c).toNat + k : ℕ) : ℕ∞) := by
    calc
      ((condK D a b).toNat : ℕ∞) = condK D a b := ENat.natCast_toNat hneB
      _ ≤ condK D a c + (k : ℕ∞) := h
      _ = ((condK D a c).toNat : ℕ∞) + (k : ℕ∞) := by rw [ENat.natCast_toNat hneC]
      _ = (((condK D a c).toNat + k : ℕ) : ℕ∞) := by push_cast; rfl
  exact_mod_cast h'

/-- express an unrelativized profile using
the empty-oracle condition encoding `pairCode b []`, at a uniform additive cost. -/
private lemma theorem4_extended_pair_condition_bound (D : Map)
    (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ a b : BitString,
      natCondK D a b ≤ natCondK D a (pairCode b []) + c ∧
      natCondK D a (pairCode b []) ≤ natCondK D a b + c := by
  obtain ⟨cPair, hPair⟩ := condK_cond_map_le D hD
    (fun b : BitString => pairCode b [])
    (pairCode_computable.comp (Computable.id.pair (Computable.const [])))
  obtain ⟨cFirst, hFirst⟩ := condK_cond_map_le D hD decodeFirst decodeFirst_computable
  refine ⟨cPair + cFirst, ?_⟩
  intro a b
  constructor
  · have hNat := theorem4_extended_condK_toNat_le_same_condition
      D hD a b (pairCode b []) cPair (hPair a b)
    omega
  · have h := hFirst a (pairCode b [])
    have hNat := theorem4_extended_condK_toNat_le_same_condition D hD a (pairCode b []) b cFirst (by
      simpa only [decodeFirst_pairCode] using h)
    omega

/-- **Theorem 4 for extended profiles.**  If `I(x̄ : z) ≤ δ`, then for every `ȳ` there is a `ȳ'`
with `ρ(K'(x̄, ȳ), K'(x̄, ȳ' | z)) ≤ δ + O(log K(x̄, ȳ, z))`.  This is what the proof of
Theorem 4 in Section 4 shows: `ȳ'` is an element of the typization of `ȳ` given `x̄` of the
largest complexity given `x̄, z` (Lemma 1), and Lemma 3 gives the bound. -/
theorem theorem4_extended (D : Map) (hD : isOptimalConditional D) (n m : ℕ) :
    ∃ c : ℕ, ∀ (x : Fin n → BitString) (z : BitString) (δ : ℕ),
      MutualInfoLe D (tupleCode x) z δ →
        ∀ y : Fin m → BitString, ∃ y' : Fin m → BitString,
          ExtProfileWithin (subCondK D (Fin.append x y)) (subCondKRel D (Fin.append x y') z)
            (δ + logSlack c (natK D (pairCode (tupleCode (Fin.append x y)) z))) := by
  obtain ⟨cSelect, hSelect⟩ := theorem4_extended_select D hD n m
  obtain ⟨cChain, hChain⟩ := theorem4_extended_chain D hD n m cSelect
  obtain ⟨cPair, hPair⟩ := theorem4_extended_pair_condition_bound D hD
  obtain ⟨cRel, hRel⟩ := lemma3_relativized D hD (n + m)
  obtain ⟨cMap, hMap⟩ := plainK_map_le D hD decodeFirst decodeFirst_computable
  obtain ⟨cFold, hFold⟩ := logSlack_absorb_of_le_linear cRel 1 cMap
  let C := 2 * cSelect + cChain + 3 * cPair + cFold
  refine ⟨C, ?_⟩
  intro x z δ hInfo y
  obtain ⟨y', hProfile, hConditional⟩ := hSelect x z y
  let u : Fin (n + m) → BitString := Fin.append x y
  let u' : Fin (n + m) → BitString := Fin.append x y'
  let N := natK D (pairCode (tupleCode u) z)
  let s := logSlack cSelect N
  let t := logSlack cChain N
  have hKBound : natK D (tupleCode u) ≤ N + cMap := by
    have hneU : plainK D (tupleCode u) ≠ ⊤ := plainK_ne_top D hD (tupleCode u)
    have hnePair : plainK D (pairCode (tupleCode u) z) ≠ ⊤ :=
      plainK_ne_top D hD (pairCode (tupleCode u) z)
    have hRaw := hMap (pairCode (tupleCode u) z)
    have hCast : ((plainK D (tupleCode u)).toNat : ℕ∞) ≤
        (((N + cMap : ℕ) : ℕ) : ℕ∞) := by
      calc
        ((plainK D (tupleCode u)).toNat : ℕ∞) = plainK D (tupleCode u) :=
          ENat.natCast_toNat hneU
        _ ≤ plainK D (pairCode (tupleCode u) z) + (cMap : ℕ∞) := by
          simpa only [decodeFirst_pairCode] using hRaw
        _ = (((N + cMap : ℕ) : ℕ) : ℕ∞) := by
          rw [← ENat.natCast_toNat hnePair]
          push_cast
          rfl
    exact_mod_cast hCast
  have hBase' : natK D (tupleCode u) ≤ natCondK D (tupleCode u') z + δ + t := by
    apply hChain x z δ hInfo y y'
    simpa [u, N, s] using hConditional
  have hProfileRel : ∀ V W : Finset (Fin (n + m)), V.Nonempty → Disjoint V W →
      (subCondKRel D u' z V W : ℤ) ≤
        subCondKRel D u [] V W + (s + cPair : ℤ) := by
    intro V W hV hdis
    have hGood := hProfile V W hV hdis
    have hCond := hPair (subtupleCode u V) (subtupleCode u W)
    have hCond' : subCondK D u V W ≤ subCondKRel D u [] V W + cPair := by
      simpa [subCondK, subCondKRel] using hCond.1
    have hGoodInt : (subCondKRel D u' z V W : ℤ) ≤
        (subCondK D u V W : ℤ) + s := by
      exact_mod_cast (by simpa [u, N, s] using hGood)
    have hCondInt : (subCondK D u V W : ℤ) ≤
        subCondKRel D u [] V W + cPair := by exact_mod_cast hCond'
    omega
  have hN : natCondK D (tupleCode u) [] = natK D (tupleCode u) := rfl
  have hBaseInt : (natCondK D (tupleCode u) [] : ℤ) ≤
      natCondK D (tupleCode u') z + (δ + t : ℤ) := by
    have h : natCondK D (tupleCode u) [] ≤ natCondK D (tupleCode u') z + (δ + t) := by
      simpa [hN, Nat.add_assoc] using hBase'
    exact_mod_cast h
  have hRel' := hRel u u' [] z (s + cPair : ℤ) (δ + t : ℤ) (by positivity)
    hProfileRel hBaseInt
  have hBudgetFold : logSlack cRel (natK D (tupleCode u)) ≤ logSlack cFold N :=
    hFold N (natK D (tupleCode u)) (by simpa [N] using hKBound)
  have hsMul : 2 * s = logSlack (2 * cSelect) N := by
    simpa [s] using (logSlack_nsmul 2 cSelect N)
  have hBudget : 2 * s + t + 3 * cPair + logSlack cRel (natK D (tupleCode u)) ≤
      logSlack C N := by
    dsimp [C]
    calc
      2 * s + t + 3 * cPair + logSlack cRel (natK D (tupleCode u)) =
          (logSlack (2 * cSelect) N + logSlack cChain N + 3 * cPair) +
            logSlack cRel (natK D (tupleCode u)) := by
              rw [hsMul]
      _ ≤ logSlack (2 * cSelect + cChain + 3 * cPair) N +
            logSlack cRel (natK D (tupleCode u)) := by
        have hSum := logSlack_add_const (2 * cSelect) cChain N
        rw [hSum]
        exact Nat.add_le_add_right
          (logSlack_add_nat_le (2 * cSelect + cChain) (3 * cPair) N) _
      _ ≤ logSlack (2 * cSelect + cChain + 3 * cPair) N + logSlack cFold N :=
        Nat.add_le_add_left hBudgetFold _
      _ = logSlack (2 * cSelect + cChain + 3 * cPair + cFold) N :=
        logSlack_add_const _ _ _
  refine ⟨y', ?_⟩
  intro V W hV hdis
  constructor
  · have hLower := hRel' V W hV hdis
    have hPairLeft' : (subCondK D u V W : ℤ) ≤
        subCondKRel D u [] V W + cPair := by
      have hCond := hPair (subtupleCode u V) (subtupleCode u W)
      have hCond' : subCondK D u V W ≤ subCondKRel D u [] V W + cPair := by
        simpa [subCondK, subCondKRel] using hCond.1
      exact_mod_cast hCond'
    have hLower' : (subCondK D u V W : ℤ) ≤
        subCondKRel D u' z V W +
          (δ + 2 * s + t + 3 * cPair + logSlack cRel (natK D (tupleCode u)) : ℤ) := by
      rw [hN] at hLower
      omega
    have hLowerNat : subCondK D u V W ≤ subCondKRel D u' z V W +
        (δ + 2 * s + t + 3 * cPair + logSlack cRel (natK D (tupleCode u))) := by
      exact_mod_cast hLower'
    calc
      subCondK D u V W ≤ subCondKRel D u' z V W +
          (δ + (2 * s + t + 3 * cPair + logSlack cRel (natK D (tupleCode u)))) := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hLowerNat
      _ ≤ subCondKRel D u' z V W + (δ + logSlack C N) := by
        exact Nat.add_le_add_left (Nat.add_le_add_left hBudget δ) _
  · have hUpper : subCondKRel D u' z V W ≤ subCondK D u V W + s := by
      simpa [u, N, s] using hProfile V W hV hdis
    have hsBound : s ≤ δ + logSlack C N := by
      have hmono : s ≤ logSlack C N := by
        exact logSlack_mono_left (by dsimp [C]; omega) N
      omega
    exact hUpper.trans (Nat.add_le_add_left hsBound _)

private lemma theorem4_condK_toNat_le (D : Map) (hD : isOptimalConditional D)
    (a b c : BitString) (k : ℕ)
    (h : condK D a b ≤ condK D a c + (k : ℕ∞)) :
    natCondK D a b ≤ natCondK D a c + k := by
  have hneB := condK_ne_top_of_optimal D hD a b
  have hneC := condK_ne_top_of_optimal D hD a c
  change (condK D a b).toNat ≤ (condK D a c).toNat + k
  have h' : ((condK D a b).toNat : ℕ∞) ≤
      (((condK D a c).toNat + k : ℕ) : ℕ∞) := by
    calc
      ((condK D a b).toNat : ℕ∞) = condK D a b := ENat.natCast_toNat hneB
      _ ≤ condK D a c + (k : ℕ∞) := h
      _ = ((condK D a c).toNat : ℕ∞) + (k : ℕ∞) := by rw [ENat.natCast_toNat hneC]
      _ = (((condK D a c).toNat + k : ℕ) : ℕ∞) := by push_cast; rfl
  exact_mod_cast h'

private lemma theorem4_condition_pair (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ a z : BitString,
      natCondK D a (pairCode [] z) ≤ natCondK D a z + c ∧
      natCondK D a z ≤ natCondK D a (pairCode [] z) + c := by
  have hpair : Computable (fun z : BitString => pairCode [] z) :=
    pairCode_computable.comp ((Computable.const []).pair Computable.id)
  obtain ⟨c₁, hc₁⟩ := condK_cond_map_le D hD (fun z => pairCode [] z) hpair
  obtain ⟨c₂, hc₂⟩ := condK_cond_map_le D hD decodeSecond decodeSecond_computable
  refine ⟨c₁ + c₂, ?_⟩
  intro a z
  constructor
  · have h := hc₂ a (pairCode [] z)
    have hnat := theorem4_condK_toNat_le D hD a (pairCode [] z) z c₂ (by
      simpa only [decodeSecond_pairCode] using h)
    omega
  · have h := hc₁ a z
    have hnat := theorem4_condK_toNat_le D hD a z (pairCode [] z) c₁ h
    omega

/-- **Theorem 4.** If `I(x̄ : z) ≤ δ`, then for every `ȳ` there is a `ȳ'` such that the profiles
`K(x̄, ȳ)` and `K(x̄, ȳ' | z)` differ componentwise by at most `δ + O(log K(x̄, ȳ, z))`.
Proof: Section 4. -/
theorem theorem4 (D : Map) (hD : isOptimalConditional D) (n m : ℕ) :
    ∃ c : ℕ, ∀ (x : Fin n → BitString) (z : BitString) (δ : ℕ),
      MutualInfoLe D (tupleCode x) z δ →
        ∀ y : Fin m → BitString, ∃ y' : Fin m → BitString,
          ProfileWithin (subK D (Fin.append x y)) (subKRel D (Fin.append x y') z)
            (δ + logSlack c (natK D (pairCode (tupleCode (Fin.append x y)) z))) := by
  obtain ⟨cExt, hExt⟩ := theorem4_extended D hD n m
  obtain ⟨cPair, hPair⟩ := theorem4_condition_pair D hD
  refine ⟨cExt + cPair, ?_⟩
  intro x z δ hInfo y
  obtain ⟨y', hProfile⟩ := hExt x z δ hInfo y
  refine ⟨y', ?_⟩
  intro V hV
  have hEmpty := hProfile V ∅ hV (Finset.disjoint_empty_right V)
  have hBase :
      subK D (Fin.append x y) V ≤
          natCondK D (subtupleCode (Fin.append x y') V) (pairCode [] z) +
            (δ + logSlack cExt
              (natK D (pairCode (tupleCode (Fin.append x y)) z))) ∧
        natCondK D (subtupleCode (Fin.append x y') V) (pairCode [] z) ≤
          subK D (Fin.append x y) V +
            (δ + logSlack cExt
              (natK D (pairCode (tupleCode (Fin.append x y)) z))) := by
    simpa [subCondK, subCondKRel, subK, subtupleCode_empty, natK, natCondK,
      Kolmogorov.plainK] using hEmpty
  have hPairV := hPair (subtupleCode (Fin.append x y') V) z
  have hSlack : cPair ≤ logSlack cPair
      (natK D (pairCode (tupleCode (Fin.append x y)) z)) := by
    unfold logSlack
    omega
  have hSlackAdd :
      logSlack cExt (natK D (pairCode (tupleCode (Fin.append x y)) z)) + cPair ≤
        logSlack (cExt + cPair) (natK D (pairCode (tupleCode (Fin.append x y)) z)) := by
    rw [← logSlack_add_const cExt cPair
      (natK D (pairCode (tupleCode (Fin.append x y)) z))]
    exact Nat.add_le_add_left hSlack _
  constructor
  · calc
      subK D (Fin.append x y) V ≤
          natCondK D (subtupleCode (Fin.append x y') V) (pairCode [] z) +
            (δ + logSlack cExt
              (natK D (pairCode (tupleCode (Fin.append x y)) z))) := hBase.1
      _ ≤ subKRel D (Fin.append x y') z V +
            (δ + logSlack cExt
              (natK D (pairCode (tupleCode (Fin.append x y)) z)) + cPair) := by
        unfold subKRel
        omega
      _ ≤ subKRel D (Fin.append x y') z V +
            (δ + logSlack (cExt + cPair)
              (natK D (pairCode (tupleCode (Fin.append x y)) z))) := by
        apply Nat.add_le_add_left
        calc
          δ + logSlack cExt (natK D (pairCode (tupleCode (Fin.append x y)) z)) + cPair =
              δ + (logSlack cExt (natK D (pairCode (tupleCode (Fin.append x y)) z)) + cPair) := by
                omega
          _ ≤ δ + logSlack (cExt + cPair)
              (natK D (pairCode (tupleCode (Fin.append x y)) z)) :=
                Nat.add_le_add_left hSlackAdd δ
  · calc
      subKRel D (Fin.append x y') z V ≤
          natCondK D (subtupleCode (Fin.append x y') V) (pairCode [] z) + cPair := by
        unfold subKRel
        exact hPairV.2
      _ ≤ subK D (Fin.append x y) V +
            (δ + logSlack cExt
              (natK D (pairCode (tupleCode (Fin.append x y)) z)) + cPair) := by
        calc
          _ ≤ (subK D (Fin.append x y) V +
                (δ + logSlack cExt
                  (natK D (pairCode (tupleCode (Fin.append x y)) z))) + cPair) :=
              Nat.add_le_add_right hBase.2 cPair
          _ = subK D (Fin.append x y) V +
                (δ + logSlack cExt
                  (natK D (pairCode (tupleCode (Fin.append x y)) z)) + cPair) := by
              omega
      _ ≤ subK D (Fin.append x y) V +
            (δ + logSlack (cExt + cPair)
              (natK D (pairCode (tupleCode (Fin.append x y)) z))) := by
        apply Nat.add_le_add_left
        calc
          δ + logSlack cExt (natK D (pairCode (tupleCode (Fin.append x y)) z)) + cPair =
              δ + (logSlack cExt (natK D (pairCode (tupleCode (Fin.append x y)) z)) + cPair) := by
                omega
          _ ≤ δ + logSlack (cExt + cPair)
              (natK D (pairCode (tupleCode (Fin.append x y)) z)) :=
                Nat.add_le_add_left hSlackAdd δ

private def theorem5_extended_stochastic_model_decodeTuple
    (n : ℕ) (w : BitString) : Fin n → BitString :=
  fun i => (decodeListCode w).getD i.val []

private def theorem5_extended_stochastic_model_decodeTupleCode
    (n : ℕ) (w : BitString) : BitString :=
  tupleCode (theorem5_extended_stochastic_model_decodeTuple n w)

private theorem theorem5_extended_stochastic_model_decodeTupleCode_computable
    (n : ℕ) : Primrec (theorem5_extended_stochastic_model_decodeTupleCode n) := by
  have hget : Primrec (fun q : BitString × Fin n => (decodeListCode q.1).getD q.2.val []) :=
    (Primrec.list_getD []).comp (decodeListCode_primrec.comp Primrec.fst)
      (Primrec.fin_val.comp Primrec.snd)
  have hmap : Primrec (fun w : BitString =>
      (List.finRange n).map fun i => (decodeListCode w).getD i.val []) :=
    Primrec.list_map (Primrec.const (List.finRange n)) hget.to₂
  have hcode : Primrec (fun w : BitString => listCode
      ((List.finRange n).map fun i => (decodeListCode w).getD i.val [])) :=
    listCode_primrec.comp hmap
  exact hcode.of_eq fun w => by
    rw [theorem5_extended_stochastic_model_decodeTupleCode, tupleCode,
      List.ofFn_eq_map]
    congr 1

private def theorem5_extended_stochastic_model_mapCode
    (n : ℕ) (w : BitString) : BitString :=
  finsetListCode (((decodeListCode w).filter fun s =>
    decide (theorem5_extended_stochastic_model_decodeTupleCode n s = s)).toFinset)

private theorem theorem5_extended_stochastic_model_mapCode_computable
    (n : ℕ) : Computable (theorem5_extended_stochastic_model_mapCode n) := by
  have hvalid : Primrec (fun q : BitString × BitString =>
      decide (theorem5_extended_stochastic_model_decodeTupleCode n q.2 = q.2)) :=
    (PrimrecRel.comp Primrec.eq
      ((theorem5_extended_stochastic_model_decodeTupleCode_computable n).comp Primrec.snd)
      Primrec.snd).decide
  have hfiltered : Primrec (fun w : BitString =>
      (decodeListCode w).filter fun s =>
        decide (theorem5_extended_stochastic_model_decodeTupleCode n s = s)) :=
    Primrec.list_filter (decodeListCode_primrec.comp Primrec.id) hvalid.to₂
  have hcode : Primrec (theorem5_extended_stochastic_model_mapCode n) := by
    unfold theorem5_extended_stochastic_model_mapCode finsetListCode
    exact listCode_primrec.comp (canonicalFinsetList_toFinset_primrec.comp hfiltered)
  exact hcode.to_comp

private lemma theorem5_extended_stochastic_model_mapCode_eq
    (n : ℕ) (A : Finset BitString) :
    theorem5_extended_stochastic_model_mapCode n (finsetListCode A) =
      tupleSetCode ((A.filter fun s =>
        theorem5_extended_stochastic_model_decodeTupleCode n s = s).image
          (theorem5_extended_stochastic_model_decodeTuple n)) := by
  let P : BitString → Prop := fun s =>
    theorem5_extended_stochastic_model_decodeTupleCode n s = s
  have hfilter : ((canonicalFinsetList A).filter fun s => decide (P s)).toFinset =
      A.filter P := by
    ext s
    simp [P]
  have himage : ((A.filter P).image
      (theorem5_extended_stochastic_model_decodeTuple n)).image tupleCode = A.filter P := by
    rw [Finset.image_image]
    calc
      (A.filter P).image
          (fun s => tupleCode (theorem5_extended_stochastic_model_decodeTuple n s)) =
          (A.filter P).image id := by
        apply Finset.image_congr
        intro s hs
        exact (Finset.mem_filter.mp hs).2
      _ = A.filter P := by simp
  simp only [theorem5_extended_stochastic_model_mapCode, finsetListCode,
    decodeListCode_listCode]
  rw [hfilter]
  change finsetListCode (A.filter P) =
    finsetListCode (((A.filter P).image
      (theorem5_extended_stochastic_model_decodeTuple n)).image tupleCode)
  exact congrArg finsetListCode himage.symm

private theorem theorem5_extended_stochastic_model_decodeTuple_tupleCode
    (n : ℕ) (x : Fin n → BitString) :
    theorem5_extended_stochastic_model_decodeTuple n (tupleCode x) = x := by
  funext i
  simp [theorem5_extended_stochastic_model_decodeTuple, tupleCode]

private lemma theorem5_extended_stochastic_model_condNat_bound (D : Map)
    (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ u z : BitString, natCondK D u z ≤ natK D u + c := by
  obtain ⟨c, hc⟩ := condK_le_plainK D hD
  refine ⟨c, ?_⟩
  intro u z
  have hRaw := hc u z
  have hCondFinite := condK_ne_top_of_optimal D hD u z
  have hPlainFinite := plainK_ne_top D hD u
  rw [← ENat.natCast_toNat hCondFinite, ← ENat.natCast_toNat hPlainFinite] at hRaw
  exact_mod_cast hRaw

/-- a stochastic tuple `x̄` has a simple
finite model `S ∋ x̄` of tuples, `K(S) = O(log K(x̄))` and `log |S| ≤ K(x̄) + O(log K(x̄))` (the
paper's `K(S) = O(log N)`, `log |S| = K(x̄) + O(log N)`).  The upper bound on `|S|` is where the
second parameter `β` of stochasticity is used: `|S| ≤ 2^(K(x̄ | list S) + β)` and
`K(x̄ | list S) ≤ K(x̄) + O(1)`.  (The code set `A` of `IsSetStochastic` is turned into a set of
`n`-tuples by keeping the elements that are codes of `n`-tuples.) -/
theorem theorem5_extended_stochastic_model (D : Map)
    (hD : isOptimalConditional D) (n a : ℕ) :
    ∃ c : ℕ, ∀ (x : Fin n → BitString),
      IsStochasticTuple D x (logSlack a (natK D (tupleCode x)))
          (logSlack a (natK D (tupleCode x))) →
        ∃ S : Finset (Fin n → BitString),
          x ∈ S ∧
          natK D (tupleSetCode S) ≤ logSlack c (natK D (tupleCode x)) ∧
          S.card ≤ 2 ^ (natK D (tupleCode x) + logSlack c (natK D (tupleCode x))) := by
  classical
  obtain ⟨cMap, hMap⟩ := plainK_map_le D hD
    (theorem5_extended_stochastic_model_mapCode n)
    (theorem5_extended_stochastic_model_mapCode_computable n)
  obtain ⟨cCond, hCond⟩ := theorem5_extended_stochastic_model_condNat_bound D hD
  let c := max (a + cMap) (a + cCond)
  refine ⟨c, fun x hx => ?_⟩
  change IsSetStochastic D (tupleCode x)
    (logSlack a (natK D (tupleCode x))) (logSlack a (natK D (tupleCode x))) at hx
  obtain ⟨A, hxA, hAcode, hAcard⟩ := hx
  let AValid := A.filter (fun s =>
    theorem5_extended_stochastic_model_decodeTupleCode n s = s)
  let S : Finset (Fin n → BitString) :=
    AValid.image (theorem5_extended_stochastic_model_decodeTuple n)
  have hxValid : theorem5_extended_stochastic_model_decodeTupleCode n (tupleCode x) =
      tupleCode x := by
    exact congrArg tupleCode
      (theorem5_extended_stochastic_model_decodeTuple_tupleCode n x)
  have hxS : x ∈ S := by
    change x ∈ AValid.image (theorem5_extended_stochastic_model_decodeTuple n)
    rw [Finset.mem_image]
    refine ⟨tupleCode x, ?_,
      theorem5_extended_stochastic_model_decodeTuple_tupleCode n x⟩
    change tupleCode x ∈ A.filter _
    exact Finset.mem_filter.mpr ⟨hxA, hxValid⟩
  have hScard : S.card ≤ A.card := by
    calc
      S.card ≤ AValid.card := Finset.card_image_le
      _ ≤ A.card := Finset.card_filter_le _ _
  have hCodeEq := theorem5_extended_stochastic_model_mapCode_eq n A
  have hMapRaw := hMap (finsetListCode A)
  rw [hCodeEq] at hMapRaw
  have hMapNat : natK D (tupleSetCode S) ≤ natK D (finsetListCode A) + cMap := by
    have hOutFinite := plainK_ne_top D hD (tupleSetCode S)
    have hInFinite := plainK_ne_top D hD (finsetListCode A)
    have hRaw : plainK D (tupleSetCode S) ≤
        plainK D (finsetListCode A) + (cMap : ℕ∞) := by
      simpa [S] using hMapRaw
    rw [← ENat.natCast_toNat hOutFinite, ← ENat.natCast_toNat hInFinite] at hRaw
    exact_mod_cast hRaw
  have hComplexity : natK D (tupleSetCode S) ≤
      logSlack c (natK D (tupleCode x)) := by
    let N := natK D (tupleCode x)
    have hMapSlack : cMap ≤ logSlack cMap N := by
      unfold logSlack
      omega
    calc
      natK D (tupleSetCode S) ≤ natK D (finsetListCode A) + cMap := hMapNat
      _ ≤ logSlack a N + cMap := Nat.add_le_add_right hAcode _
      _ ≤ logSlack a N + logSlack cMap N := Nat.add_le_add_left hMapSlack _
      _ = logSlack (a + cMap) N := logSlack_add_const _ _ _
      _ ≤ logSlack c N := logSlack_mono_left (by dsimp [c]; omega) N
  have hCard : S.card ≤ 2 ^ (natK D (tupleCode x) +
      logSlack c (natK D (tupleCode x))) := by
    let N := natK D (tupleCode x)
    have hCondNat := hCond (tupleCode x) (finsetListCode A)
    have hCondSlack : logSlack a N + cCond ≤ logSlack c N := by
      have hCondSlack' : cCond ≤ logSlack cCond N := by
        unfold logSlack
        omega
      calc
        logSlack a N + cCond ≤ logSlack a N + logSlack cCond N :=
          Nat.add_le_add_left hCondSlack' _
        _ = logSlack (a + cCond) N := logSlack_add_const _ _ _
        _ ≤ logSlack c N := logSlack_mono_left (by dsimp [c]; omega) N
    have hExponent : natCondK D (tupleCode x) (finsetListCode A) +
        logSlack a N ≤ N + logSlack c N := by
      calc
        natCondK D (tupleCode x) (finsetListCode A) + logSlack a N ≤
            (N + cCond) + logSlack a N := Nat.add_le_add_right hCondNat _
        _ = N + (logSlack a N + cCond) := by omega
        _ ≤ N + logSlack c N := Nat.add_le_add_left hCondSlack _
    calc
      S.card ≤ A.card := hScard
      _ ≤ 2 ^ (natCondK D (tupleCode x) (finsetListCode A) + logSlack a N) := hAcard
      _ ≤ 2 ^ (N + logSlack c N) := Nat.pow_le_pow_right (by decide) hExponent
  exact ⟨S, hxS, hComplexity, hCard⟩

/-- The section of a set `A` of `(n+m)`-tuples over an `n`-tuple `x̄`: the `m`-tuples `ȳ'` with
`⟨x̄, ȳ'⟩ ∈ A` (see `theorem5_extended_special_union_mem_section`). -/
private def theorem5_extended_special_union_section {n m : ℕ}
    (A : Finset (Fin (n + m) → BitString)) (x : Fin n → BitString) :
    Finset (Fin m → BitString) :=
  (A.filter fun u => u ∘ Fin.castAdd m = x).image fun u => u ∘ Fin.natAdd n

open Classical in
/-- The code of a finite family `G` of pairs `(C, B_C)` (a set of `(n+m)`-tuples and a set of
`n`-tuples): the ordered list of the codes `pairCode (list C) (list B_C)`. -/
private noncomputable def theorem5_extended_special_union_familyCode {n m : ℕ}
    (G : Finset (Finset (Fin (n + m) → BitString) × Finset (Fin n → BitString))) :
    BitString :=
  finsetListCode (G.image fun p => pairCode (tupleSetCode p.1) (tupleSetCode p.2))

private lemma theorem5_extended_special_union_mem_section {n m : ℕ}
    (A : Finset (Fin (n + m) → BitString)) (x : Fin n → BitString) (y' : Fin m → BitString) :
    y' ∈ theorem5_extended_special_union_section A x ↔ Fin.append x y' ∈ A := by
  unfold theorem5_extended_special_union_section
  constructor
  · intro h
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp h
    obtain ⟨huA, hux⟩ := Finset.mem_filter.mp hu
    have : Fin.append x (u ∘ Fin.natAdd n) = u := by
      rw [← hux]
      exact Fin.append_castAdd_natAdd
    rw [this]
    exact huA
  · intro h
    refine Finset.mem_image.mpr ⟨Fin.append x y', ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨h, ?_⟩
      funext i
      simp [Function.comp]
    · funext i
      simp [Function.comp]

/-- The finite set of the bit strings of length at most `N`. -/
private def theorem5_extended_special_union_shortStrings (N : ℕ) : Finset BitString :=
  (Kolmogorov.programsLe N).toFinset.filter fun s => s.length ≤ N

private lemma theorem5_extended_special_union_mem_shortStrings {N : ℕ} {s : BitString} :
    s ∈ theorem5_extended_special_union_shortStrings N ↔ s.length ≤ N := by
  unfold theorem5_extended_special_union_shortStrings
  simp only [Finset.mem_filter, List.mem_toFinset]
  exact ⟨fun h => h.2, fun h => ⟨Kolmogorov.mem_programsLe N s h, h⟩⟩

/-- The candidate set `S × (B^{≤N})^m` of the paper: the `(n+m)`-tuples `⟨x̄', ȳ'⟩` with `x̄' ∈ S`
and all components of `ȳ'` of length at most `N`. -/
private def theorem5_extended_special_union_candidates {n m : ℕ}
    (S : Finset (Fin n → BitString)) (N : ℕ) : Finset (Fin (n + m) → BitString) :=
  (S ×ˢ Fintype.piFinset (fun _ : Fin m => theorem5_extended_special_union_shortStrings
                                             N)).image
    fun p => Fin.append p.1 p.2

private lemma theorem5_extended_special_union_append_mem_candidates {n m : ℕ}
    {S : Finset (Fin n → BitString)} {N : ℕ} {x : Fin n → BitString} {y : Fin m → BitString}
    (hx : x ∈ S) (hy : ∀ i, (y i).length ≤ N) :
    Fin.append x y ∈ theorem5_extended_special_union_candidates S N := by
  unfold theorem5_extended_special_union_candidates
  refine Finset.mem_image.mpr ⟨(x, y), Finset.mem_product.mpr ⟨hx, ?_⟩, rfl⟩
  exact Fintype.mem_piFinset.mpr fun i =>
    theorem5_extended_special_union_mem_shortStrings.mpr (hy i)

private lemma theorem5_extended_special_union_length_of_mem_candidates {n m : ℕ}
    {S : Finset (Fin n → BitString)} {N : ℕ} {u : Fin (n + m) → BitString}
    (hu : u ∈ theorem5_extended_special_union_candidates S N) (i : Fin m) :
    (u (Fin.natAdd n i)).length ≤ N := by
  unfold theorem5_extended_special_union_candidates at hu
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hu
  have hp2 := (Finset.mem_product.mp hp).2
  rw [Fin.append_right]
  exact theorem5_extended_special_union_mem_shortStrings.mp (Fintype.mem_piFinset.mp hp2 i)

open Classical in
/-- The level set `A₀` of the paper for the tuple `u₀ = ⟨x̄, ȳ°⟩`: the candidates `u` (see
`theorem5_extended_special_union_candidates`) whose relativized extended profile is
componentwise at most that of `u₀`: `K(u_V | u_W, z) ≤ K(u₀_V | u₀_W, z)` for all disjoint
`V ≠ ∅, W`. -/
private noncomputable def theorem5_extended_special_union_levelSet {n m : ℕ} (D : Map)
    (S : Finset (Fin n → BitString)) (N : ℕ) (u₀ : Fin (n + m) → BitString) (z : BitString) :
    Finset (Fin (n + m) → BitString) :=
  (theorem5_extended_special_union_candidates S N).filter fun u =>
    ∀ V W : Finset (Fin (n + m)), V.Nonempty → Disjoint V W →
      subCondKRel D u z V W ≤ subCondKRel D u₀ z V W

open Classical in
/-- The strong projection `B_C` of a set `C` of `(n+m)`-tuples, with threshold `κ - s`: the
`x̄' ∈ S` whose section `C_{x̄'}` is nonempty with `κ ≤ log₂ |C_{x̄'}| + s`. -/
private noncomputable def theorem5_extended_special_union_strongProj {n m : ℕ}
    (S : Finset (Fin n → BitString)) (κ s : ℕ) (C : Finset (Fin (n + m) → BitString)) :
    Finset (Fin n → BitString) :=
  S.filter fun x' => (theorem5_extended_special_union_section C x').Nonempty ∧
    κ ≤ Nat.log2 (theorem5_extended_special_union_section C x').card + s

open Classical in
/-- The family of the pairs `(C, B_C)`, where `C` ranges over the *correct* sets (the subsets of
the candidate set `S × (B^{≤N})^m` with `ent_{V|W}(C) ≤ ent_{V|W}(A₀)` for all disjoint `V ≠ ∅, W`)
and `B_C` is the strong projection of `C` with threshold `κ - s`. -/
private noncomputable def theorem5_extended_special_union_family {n m : ℕ}
    (S : Finset (Fin n → BitString)) (N κ s : ℕ) (A₀ : Finset (Fin (n + m) → BitString)) :
    Finset (Finset (Fin (n + m) → BitString) × Finset (Fin n → BitString)) :=
  ((theorem5_extended_special_union_candidates S N).powerset.filter fun C =>
      ∀ V W : Finset (Fin (n + m)), V.Nonempty → Disjoint V W →
        combEnt C V W ≤ combEnt A₀ V W).image
    fun C => (C, theorem5_extended_special_union_strongProj S κ s C)

/-- The counting bound for the level set: `ent_{V|W}(A₀) ≤ K(u₀_V | u₀_W, z) + 1`, since all the
`V`-projections in a `W`-section of `A₀` have conditional complexity at most `K(u₀_V | u₀_W, z)`
given the common `W`-projection and `z`. -/
private lemma theorem5_extended_special_union_levelSet_combEnt {n m : ℕ} (D : Map)
    (hD : isOptimalConditional D) (S : Finset (Fin n → BitString)) (N : ℕ)
    (u₀ : Fin (n + m) → BitString) (z : BitString) (V W : Finset (Fin (n + m)))
    (hV : V.Nonempty) (hdis : Disjoint V W) :
    combEnt (theorem5_extended_special_union_levelSet D S N u₀ z) V W ≤
      subCondKRel D u₀ z V W + 1 := by
  classical
  have hcard : maxSectionCard (theorem5_extended_special_union_levelSet D S N u₀ z) V W ≤
      2 ^ (subCondKRel D u₀ z V W + 1) := by
    unfold maxSectionCard
    apply Finset.sup_le
    intro u _
    have hsub : sectionProjection (theorem5_extended_special_union_levelSet D S N u₀ z)
        V W u ⊆ Kolmogorov.compressibleWords D (pairCode (subtupleCode u W) z)
          (subCondKRel D u₀ z V W) := by
      intro s hs
      unfold sectionProjection at hs
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hs
      obtain ⟨haL, haW⟩ := Finset.mem_filter.mp ha
      have hle : subCondKRel D a z V W ≤ subCondKRel D u₀ z V W := by
        unfold theorem5_extended_special_union_levelSet at haL
        exact (Finset.mem_filter.mp haL).2 V W hV hdis
      have hnat : natCondK D (subtupleCode a V) (pairCode (subtupleCode u W) z) ≤
          subCondKRel D u₀ z V W := by
        unfold subCondKRel at hle
        rw [haW] at hle
        exact hle
      have hne := condK_ne_top_of_optimal D hD (subtupleCode a V)
        (pairCode (subtupleCode u W) z)
      have hcond : condK D (subtupleCode a V) (pairCode (subtupleCode u W) z) ≤
          ((subCondKRel D u₀ z V W : ℕ) : ENat) := by
        rw [← ENat.natCast_toNat hne]
        exact_mod_cast hnat
      rw [Kolmogorov.compressibleWords, Finset.mem_filter]
      refine ⟨?_, hcond⟩
      obtain ⟨p, hpLen, hpProd⟩ := (Kolmogorov.condK_le_iff D _ _ _).mp hcond
      rw [Kolmogorov.generatedWords, List.mem_toFinset, List.mem_filterMap]
      exact ⟨p, Kolmogorov.mem_programsLe _ p hpLen, Kolmogorov.progToOut_eq_some.mpr hpProd⟩
    calc (sectionProjection (theorem5_extended_special_union_levelSet D S N u₀ z)
          V W u).card ≤ (Kolmogorov.compressibleWords D (pairCode (subtupleCode u W) z)
            (subCondKRel D u₀ z V W)).card := Finset.card_le_card hsub
      _ ≤ 2 ^ (subCondKRel D u₀ z V W + 1) :=
        (Kolmogorov.card_compressibleWordsLt D _ _).le
  unfold combEnt
  exact Nat.clog_le_of_le_pow hcard

/-- Each component of `ȳ` has plain complexity at most the complexity of the coded pair
`(x̄, ȳ, z)`,
up to a constant depending on the tuple arities and the optimal machine. -/
private theorem theorem5_extended_component_bound
    (D : Map) (hD : isOptimalConditional D) (n m : ℕ) :
    ∃ c : ℕ, ∀ (x : Fin n → BitString) (z : BitString) (y : Fin m → BitString)
      (i : Fin m),
      natK D (y i) ≤ natK D (pairCode (tupleCode (Fin.append x y)) z) + c := by
  let extract : Fin m → BitString → BitString := fun i w =>
    ((decodeListCode (decodeFirst w)).drop n).getD i.val []
  have hDrop : ∀ i : Fin m, Computable (extract i) := by
    intro i
    dsimp [extract]
    exact (Primrec.list_getD ([] : BitString)).to_comp.comp
      ((Primrec.list_drop.comp (Primrec.const n) decodeListCode_primrec).to_comp.comp
        decodeFirst_computable)
      (Computable.const i.val)
  let cI : Fin m → ℕ := fun i =>
    Classical.choose (plainK_map_le D hD (extract i) (hDrop i))
  have hcI : ∀ i w, plainK D (extract i w) ≤ plainK D w + cI i := by
    intro i w
    exact Classical.choose_spec (plainK_map_le D hD (extract i) (hDrop i)) w
  let c := Finset.univ.sup cI
  refine ⟨c, ?_⟩
  intro x z y i
  let p := pairCode (tupleCode (Fin.append x y)) z
  have hExtract : extract i p = y i := by
    have hDecoded : decodeListCode (decodeFirst p) = List.ofFn x ++ List.ofFn y := by
      have hpFirst : decodeFirst p = tupleCode (Fin.append x y) := by
        dsimp [p]
        rw [decodeFirst_pairCode]
      rw [hpFirst, tupleCode, decodeListCode_listCode, List.ofFn_fin_append]
    have hTail : (decodeListCode (decodeFirst p)).drop n = List.ofFn y := by
      rw [hDecoded, List.drop_append_of_le_length (by simp)]
      rw [List.drop_eq_nil_of_le (by simp : (List.ofFn x).length ≤ n)]
      simp
    change ((decodeListCode (decodeFirst p)).drop n).getD i.val [] = y i
    rw [hTail, List.getD_eq_getElem _ _ (by simp)]
    simp
  have hci : cI i ≤ c := by
    dsimp [c]
    exact Finset.le_sup (Finset.mem_univ i)
  have hRaw : plainK D (y i) ≤ plainK D p + (c : ENat) := by
    rw [← hExtract]
    have hciE : (cI i : ENat) ≤ (c : ENat) := by exact_mod_cast hci
    exact (hcI i p).trans (by gcongr)
  have hOut := plainK_ne_top D hD (y i)
  have hIn := plainK_ne_top D hD p
  rw [← ENat.natCast_toNat hOut, ← ENat.natCast_toNat hIn] at hRaw
  exact_mod_cast hRaw

/-- truncate each shortest empty-condition description using the uniform component-complexity bound;
the dropped suffix recovers the original component with constant information, while its shortest
description length recovers the truncated string with logarithmic information. -/
private theorem theorem5_extended_shorten
    (D : Map) (hD : isOptimalConditional D) (n m cK : ℕ)
    (hK : ∀ (x : Fin n → BitString) (z : BitString) (y : Fin m → BitString) (i : Fin m),
      natK D (y i) ≤ natK D (pairCode (tupleCode (Fin.append x y)) z) + cK) :
    ∃ c : ℕ, ∀ (x : Fin n → BitString) (z : BitString) (y : Fin m → BitString),
      ∃ y₀ : Fin m → BitString,
        (∀ i : Fin m,
          (y₀ i).length ≤ natK D (pairCode (tupleCode (Fin.append x y)) z)) ∧
        (∀ i : Fin m, natCondK D (y i) (y₀ i) ≤ c) ∧
        (∀ i : Fin m,
          natCondK D (y₀ i) (y i) ≤
            logSlack c (natK D (pairCode (tupleCode (Fin.append x y)) z))) := by
  classical
  let trunc : BitString → BitString := fun p => p.take (p.length - cK)
  have hTrunc : Computable trunc := by
    exact (Primrec.list_take.comp
      (Primrec.nat_sub.comp (Primrec.list_length) (Primrec.const cK))
      Primrec.id).to_comp
  let suffixDecoder : Map := fun q => D (q.2 ++ q.1, [])
  have hSuffixDecoder : isDecompressor suffixDecoder :=
    Partrec.comp hD.1
      ((Computable.list_append.comp Computable.snd Computable.fst).pair
        (Computable.const []))
  obtain ⟨cSuffix, hSuffix⟩ := hD.2 suffixDecoder hSuffixDecoder
  obtain ⟨cMap, hMap⟩ := Kolmogorov.condK_map_le D hD trunc hTrunc
  obtain ⟨cShortest, hShortest⟩ := Kolmogorov.condK_shortestDescription_le D hD
  let cOver := logSlack cShortest (cK + 1) + cMap
  let cShorten := cShortest + cOver
  let c := max (cK + cSuffix) cShorten
  refine ⟨c, ?_⟩
  intro x z y
  let N := natK D (pairCode (tupleCode (Fin.append x y)) z)
  have hValue : ∀ i : Fin m,
      Kolmogorov.HasPlainComplexityValue D (y i) (natK D (y i)) := by
    intro i
    unfold Kolmogorov.HasPlainComplexityValue natK
    exact (ENat.natCast_toNat (plainK_ne_top D hD (y i))).symm
  have hPrograms : ∀ i : Fin m,
      ∃ p : BitString, p.length = natK D (y i) ∧ produces D p [] (y i) := by
    intro i
    have hAtMost : condK D (y i) [] ≤ (natK D (y i) : ENat) := by
      change plainK D (y i) ≤ (natK D (y i) : ENat)
      rw [hValue i]
    obtain ⟨p, hpLen, hpProd⟩ :=
      (Kolmogorov.condK_le_iff D (y i) [] (natK D (y i))).mp hAtMost
    change p.length ≤ natK D (y i) at hpLen
    have hLower : plainK D (y i) ≤ (p.length : ENat) := by
      change condK D (y i) [] ≤ (p.length : ENat)
      exact sInf_le ⟨p, hpProd, rfl⟩
    have hLowerCast : ((natK D (y i) : ℕ) : ENat) ≤ (p.length : ENat) := by
      rw [← hValue i]
      exact hLower
    have hLowerNat : natK D (y i) ≤ p.length := by exact_mod_cast hLowerCast
    exact ⟨p, Nat.le_antisymm hpLen hLowerNat, hpProd⟩
  choose p hpLen hpProd using hPrograms
  let y₀ : Fin m → BitString := fun i => trunc (p i)
  have hKBound : ∀ i : Fin m, natK D (y i) ≤ N + cK := by
    intro i
    dsimp [N]
    exact hK x z y i
  have hLen : ∀ i : Fin m, (y₀ i).length ≤ N := by
    intro i
    calc
      (y₀ i).length ≤ (p i).length - cK := by
        dsimp [y₀, trunc]
        rw [List.length_take]
        exact Nat.min_le_left _ _
      _ ≤ N := by
        have hkBoundI := hKBound i
        rw [hpLen i]
        omega
  have hDrop : ∀ i : Fin m, natCondK D (y i) (y₀ i) ≤ c := by
    intro i
    let a : BitString := y₀ i
    let b : BitString := (p i).drop ((p i).length - cK)
    have hsplit : a ++ b = p i := by
      dsimp [a, b, y₀, trunc]
      exact List.take_append_drop _ _
    have hEProd : produces suffixDecoder b a (y i) := by
      change y i ∈ D (a ++ b, [])
      rw [hsplit]
      exact hpProd i
    have hELe : condK suffixDecoder (y i) a ≤ (b.length : ENat) := by
      exact (Kolmogorov.condK_le_iff suffixDecoder (y i) a b.length).2
        ⟨b, le_rfl, hEProd⟩
    have hRaw : condK D (y i) a ≤ (b.length : ENat) + (cSuffix : ENat) := by
      calc
        condK D (y i) a ≤ condK suffixDecoder (y i) a + (cSuffix : ENat) :=
          hSuffix (y i) a
        _ ≤ (b.length : ENat) + (cSuffix : ENat) :=
          add_le_add_left hELe _
    have hNatCast : ((natCondK D (y i) a : ℕ) : ENat) ≤
        ((b.length + cSuffix : ℕ) : ENat) := by
      change ((condK D (y i) a).toNat : ENat) ≤ _
      calc
        ((condK D (y i) a).toNat : ENat) = condK D (y i) a :=
          ENat.natCast_toNat (Kolmogorov.condK_ne_top_of_optimal D hD (y i) a)
        _ ≤ (b.length : ENat) + (cSuffix : ENat) := hRaw
        _ = ((b.length + cSuffix : ℕ) : ENat) := by push_cast; rfl
    have hNat : natCondK D (y i) a ≤ b.length + cSuffix := by exact_mod_cast hNatCast
    have hbLen : b.length ≤ cK := by
      dsimp [b]
      rw [List.length_drop, hpLen i]
      omega
    have hcDrop : cK + cSuffix ≤ c := by
      dsimp [c]
      exact le_max_left _ _
    calc
      natCondK D (y i) (y₀ i) = natCondK D (y i) a := rfl
      _ ≤ b.length + cSuffix := hNat
      _ ≤ cK + cSuffix := Nat.add_le_add_right hbLen _
      _ ≤ c := hcDrop
  have hEncode : ∀ i : Fin m,
      natCondK D (y₀ i) (y i) ≤ logSlack c N := by
    intro i
    have hShortest := hShortest (y i) (p i) (natK D (y i))
      (hValue i) (hpProd i) (hpLen i)
    have hMapped : condK D (y₀ i) (y i) ≤
        condK D (p i) (y i) + (cMap : ENat) := by
      simpa [y₀, trunc] using hMap (p i) (y i)
    have hRaw : condK D (y₀ i) (y i) ≤
        ((logSlack cShortest (natK D (y i) + 1) + cMap : ℕ) : ENat) := by
      calc
        condK D (y₀ i) (y i) ≤ condK D (p i) (y i) + (cMap : ENat) := hMapped
        _ ≤ (logSlack cShortest (natK D (y i) + 1) : ENat) + (cMap : ENat) :=
          add_le_add_left hShortest _
        _ = ((logSlack cShortest (natK D (y i) + 1) + cMap : ℕ) : ENat) := by
          push_cast
          rfl
    have hNatCast : ((natCondK D (y₀ i) (y i) : ℕ) : ENat) ≤
        ((logSlack cShortest (natK D (y i) + 1) + cMap : ℕ) : ENat) := by
      change ((condK D (y₀ i) (y i)).toNat : ENat) ≤ _
      calc
        ((condK D (y₀ i) (y i)).toNat : ENat) = condK D (y₀ i) (y i) :=
          ENat.natCast_toNat (Kolmogorov.condK_ne_top_of_optimal D hD (y₀ i) (y i))
        _ ≤ ((logSlack cShortest (natK D (y i) + 1) + cMap : ℕ) : ENat) := hRaw
    have hNat : natCondK D (y₀ i) (y i) ≤
        logSlack cShortest (natK D (y i) + 1) + cMap := by exact_mod_cast hNatCast
    have hkBoundI := hKBound i
    have hArg : natK D (y i) + 1 ≤ N + (cK + 1) := by omega
    have hLog : logSlack cShortest (natK D (y i) + 1) ≤
        logSlack cShortest N + logSlack cShortest (cK + 1) := by
      calc
        logSlack cShortest (natK D (y i) + 1) ≤ logSlack cShortest (N + (cK + 1)) :=
          logSlack_mono_right cShortest hArg
        _ ≤ logSlack cShortest N + logSlack cShortest (cK + 1) :=
          logSlack_add_le cShortest N (cK + 1)
    have hBound : natCondK D (y₀ i) (y i) ≤ logSlack cShortest N + cOver := by
      dsimp [cOver]
      omega
    have hFold : logSlack cShortest N + cOver ≤ logSlack cShorten N := by
      dsimp [cShorten]
      exact logSlack_add_nat_le cShortest cOver N
    have hcEncode : cShorten ≤ c := by
      dsimp [c]
      exact le_max_right _ _
    exact hBound.trans (hFold.trans (logSlack_mono_left hcEncode N))
  exact ⟨y₀, hLen, hDrop, hEncode⟩

/-- collect
component descriptions into an ordered subtuple description, preserving constant cost in the
forward direction and logarithmic cost in the reverse direction. -/
private theorem theorem5_extended_collect_subtuple
    (D : Map) (hD : isOptimalConditional D) (k a b : ℕ) :
    ∃ cDrop' cEncode' : ℕ, ∀ (u u₀ : Fin k → BitString) (N : ℕ)
      (S : Finset (Fin k)),
      (∀ i : Fin k, natCondK D (u i) (u₀ i) ≤ a) →
      (∀ i : Fin k, natCondK D (u₀ i) (u i) ≤ logSlack b N) →
      natCondK D (subtupleCode u S) (subtupleCode u₀ S) ≤ cDrop' ∧
      natCondK D (subtupleCode u₀ S) (subtupleCode u S) ≤ logSlack cEncode' N := by
  classical
  let runAux : (List BitString × List BitString) → ℕ → Part (List BitString) :=
    fun input r => Nat.rec (Part.some [])
      (fun i state => state.bind fun ys =>
        (D (input.1.getD i [], input.2.getD i [])).map fun y => ys ++ [y]) r
  let run : (List BitString × List BitString) → Part (List BitString) :=
    fun input => runAux input input.1.length
  have hRunRec (input : List BitString × List BitString) (r : ℕ) :
      runAux input (r + 1) = (runAux input r).bind fun ys =>
        (D (input.1.getD r [], input.2.getD r [])).map fun y => ys ++ [y] := rfl
  have hCount : Computable (fun input : List BitString × List BitString => input.1.length) :=
    Computable.list_length.comp Computable.fst
  have hBase : Partrec (fun _ : List BitString × List BitString =>
      (Part.some ([] : List BitString))) :=
    (Computable.const ([] : List BitString)).partrec
  have hCall : Partrec
      (fun q : (List BitString × List BitString) × (ℕ × List BitString) =>
        D (q.1.1.getD q.2.1 [], q.1.2.getD q.2.1 [])) := by
    refine hD.1.comp ?_
    apply Primrec.to_comp
    exact Primrec.pair
      ((Primrec.list_getD []).comp
        (Primrec.fst.comp Primrec.fst)
        (Primrec.fst.comp Primrec.snd))
      ((Primrec.list_getD []).comp
        (Primrec.snd.comp Primrec.fst)
        (Primrec.fst.comp Primrec.snd))
  have hAppend : Computable₂
      (fun (q : (List BitString × List BitString) × (ℕ × List BitString))
          (y : BitString) => q.2.2 ++ [y]) := by
    apply Primrec.to_comp
    exact Primrec.list_append.comp
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.list_cons.comp Primrec.snd (Primrec.const []))
  have hNext : Partrec₂
      (fun input : List BitString × List BitString => fun indexed : ℕ × List BitString =>
        (D (input.1.getD indexed.1 [], input.2.getD indexed.1 [])).map
          fun y => indexed.2 ++ [y]) := Partrec.map hCall hAppend
  have hRun : Partrec run := by
    refine (Partrec.nat_rec hCount hBase hNext).of_eq ?_
    intro input
    rfl
  have hMapOutput : Computable₂
      (fun (_ : List BitString × List BitString) (ys : List BitString) => listCode ys) :=
    listCode_computable.comp Computable.snd
  have hRunOutput : Partrec
      (fun input : List BitString × List BitString => (run input).map listCode) :=
    Partrec.map hRun hMapOutput
  let M : Map := fun args =>
    (run (decodeListCode args.1, decodeListCode args.2)).map listCode
  have hM : isDecompressor M := by
    dsimp [isDecompressor, M]
    exact hRunOutput.comp (Computable.pair
        (decodeListCode_computable.comp Computable.fst)
        (decodeListCode_computable.comp Computable.snd))
  obtain ⟨cM, hMbound⟩ := hD.2 M hM
  have hListCodeLen : ∀ (xs : List BitString) (q : ℕ),
      (∀ p ∈ xs, p.length ≤ q) → (listCode xs).length ≤ xs.length * (2 * q + 1) := by
    intro xs
    induction xs with
    | nil =>
        intro q _
        simp
    | cons p xs ih =>
        intro q hq
        rw [length_listCode_cons, List.length_cons]
        have hp : p.length ≤ q := hq p (by simp)
        have htail : ∀ z ∈ xs, z.length ≤ q := by
          intro z hz
          exact hq z (by simp [hz])
        have ht := ih q htail
        calc
          2 * p.length + 1 + (listCode xs).length ≤
              (2 * q + 1) + xs.length * (2 * q + 1) := by omega
          _ = (xs.length + 1) * (2 * q + 1) := by
            rw [Nat.add_mul, Nat.one_mul]
            omega
  have hRunAuxMem : ∀ (ps cs ys : List BitString),
      cs.length = ps.length → ys.length = ps.length →
      (∀ i, i < ps.length →
        produces D (ps.getD i []) (cs.getD i []) (ys.getD i [])) →
      ∀ r, r ≤ ps.length → ys.take r ∈ runAux (ps, cs) r := by
    intro ps cs ys hcs hys hprod r
    induction r with
    | zero =>
        intro _
        simp [runAux]
    | succ r ih =>
        intro hr
        have hrp : r < ps.length := by omega
        have hrc : r < cs.length := by omega
        have hry : r < ys.length := by omega
        have hprev : ys.take r ∈ runAux (ps, cs) r := ih (by omega)
        have hp := hprod r hrp
        have htake : ys.take (r + 1) = ys.take r ++ [ys.getD r []] := by
          rw [List.take_add_one, List.getElem?_eq_getElem hry,
            List.getD_eq_getElem ys [] hry]
          rfl
        rw [hRunRec, Part.mem_bind_iff]
        refine ⟨ys.take r, hprev, ?_⟩
        exact (Part.mem_map_iff _).2 ⟨ys.getD r [], hp, htake.symm⟩
  refine ⟨2 * k * a + k + cM, 2 * k * b + k + cM, ?_⟩
  intro u u₀ N S hDrop hEncode
  have hCollect : ∀ (v v₀ : Fin k → BitString) (q : ℕ),
      (∀ i : Fin k, natCondK D (v i) (v₀ i) ≤ q) →
      natCondK D (subtupleCode v S) (subtupleCode v₀ S) ≤ 2 * k * q + k + cM := by
    intro v v₀ q hBound
    have hPrograms : ∀ i : Fin k,
        ∃ p : BitString, p.length ≤ q ∧ produces D p (v₀ i) (v i) := by
      intro i
      have hfinite := condK_ne_top_of_optimal D hD (v i) (v₀ i)
      have hcond : condK D (v i) (v₀ i) ≤ (q : ℕ∞) := by
        rw [← ENat.natCast_toNat hfinite]
        exact_mod_cast hBound i
      exact (condK_le_iff D (v i) (v₀ i) q).mp hcond
    choose p hpLen hpProd using hPrograms
    let I : List (Fin k) := S.sort (· ≤ ·)
    let ps := I.map p
    let cs := I.map v₀
    let ys := I.map v
    have hIlen : I.length ≤ k := by
      dsimp [I]
      rw [Finset.length_sort]
      simpa using Finset.card_le_univ S
    have hPsCodeLen : (listCode ps).length ≤ 2 * k * q + k := by
      calc
        (listCode ps).length ≤ ps.length * (2 * q + 1) := by
          apply hListCodeLen
          intro w hw
          rcases List.mem_map.mp hw with ⟨i, -, rfl⟩
          exact hpLen i
        _ = I.length * (2 * q + 1) := by simp [ps]
        _ ≤ k * (2 * q + 1) := Nat.mul_le_mul_right _ hIlen
        _ = 2 * k * q + k := by ring
    have hpslen : ps.length = I.length := by simp [ps]
    have hcslen : cs.length = ps.length := by simp [cs, ps]
    have hyslen : ys.length = ps.length := by simp [ys, ps]
    have hrel : ∀ i, i < ps.length →
        produces D (ps.getD i []) (cs.getD i []) (ys.getD i []) := by
      intro j hj
      have hjI : j < I.length := by simpa [ps] using hj
      let i : Fin k := I[j]'hjI
      have hji : j < ps.length := hj
      have hpget : ps.getD j [] = p i := by
        rw [List.getD_eq_getElem _ _ hji]
        simp [ps, i]
      have hcget : cs.getD j [] = v₀ i := by
        rw [List.getD_eq_getElem _ _ (by simpa [cs, ps] using hj)]
        simp [cs, i]
      have hyget : ys.getD j [] = v i := by
        rw [List.getD_eq_getElem _ _ (by simpa [ys, ps] using hj)]
        simp [ys, i]
      rw [hpget, hcget, hyget]
      exact hpProd i
    have hRunOut : ys ∈ run (ps, cs) := by
      have hmem := hRunAuxMem ps cs ys hcslen hyslen hrel ps.length le_rfl
      have htake : ys.take ps.length = ys := by rw [← hyslen, List.take_length]
      change ys ∈ runAux (ps, cs) ps.length
      rw [← htake]
      exact hmem
    have hOutputCode : listCode ys = subtupleCode v S := by
      simp [ys, subtupleCode, I]
    have hConditionList : decodeListCode (subtupleCode v₀ S) = cs := by
      simp [cs, subtupleCode, I]
    have hMprod : produces M (listCode ps) (subtupleCode v₀ S) (subtupleCode v S) := by
      change subtupleCode v S ∈
        (run (decodeListCode (listCode ps), decodeListCode (subtupleCode v₀ S))).map listCode
      rw [decodeListCode_listCode, hConditionList]
      exact (Part.mem_map_iff _).2 ⟨ys, hRunOut, hOutputCode.symm⟩
    have hMcomplexity : condK M (subtupleCode v S) (subtupleCode v₀ S) ≤
        ((listCode ps).length : ℕ∞) :=
      (condK_le_iff M (subtupleCode v S) (subtupleCode v₀ S) (listCode ps).length).2
        ⟨listCode ps, le_rfl, hMprod⟩
    have hRaw : condK D (subtupleCode v S) (subtupleCode v₀ S) ≤
        ((listCode ps).length : ℕ∞) + (cM : ℕ∞) := by
      calc
        condK D (subtupleCode v S) (subtupleCode v₀ S) ≤
            condK M (subtupleCode v S) (subtupleCode v₀ S) + (cM : ℕ∞) :=
          hMbound _ _
        _ ≤ ((listCode ps).length : ℕ∞) + (cM : ℕ∞) := by
          exact add_le_add_left hMcomplexity (cM : ℕ∞)
    have hRawCast :
        ((natCondK D (subtupleCode v S) (subtupleCode v₀ S) : ℕ) : ℕ∞) ≤
          ((listCode ps).length + cM : ℕ) := by
      calc
        ((natCondK D (subtupleCode v S) (subtupleCode v₀ S) : ℕ) : ℕ∞) =
            condK D (subtupleCode v S) (subtupleCode v₀ S) :=
          ENat.natCast_toNat (condK_ne_top_of_optimal D hD _ _)
        _ ≤ ((listCode ps).length : ℕ∞) + (cM : ℕ∞) := hRaw
        _ = ((listCode ps).length + cM : ℕ) := by push_cast; rfl
    have hRawNat : natCondK D (subtupleCode v S) (subtupleCode v₀ S) ≤
        (listCode ps).length + cM := by exact_mod_cast hRawCast
    omega
  constructor
  · exact hCollect u u₀ a hDrop
  · have hBase : 2 * k * logSlack b N + k ≤ logSlack (2 * k * b + k) N := by
      unfold logSlack
      nlinarith [Nat.zero_le (Nat.bits N).length]
    have hSlack : 2 * k * logSlack b N + k + cM ≤
        logSlack (2 * k * b + k + cM) N := by
      calc
        2 * k * logSlack b N + k + cM ≤ logSlack (2 * k * b + k) N + cM :=
          Nat.add_le_add_right hBase cM
        _ ≤ logSlack (2 * k * b + k + cM) N :=
          logSlack_add_nat_le (2 * k * b + k) cM N
    exact (hCollect u₀ u (logSlack b N) hEncode).trans hSlack

/-- splice two
auxiliary recoding programs ahead of the original shortest program, using pair-code length
headers to locate them while leaving the original program as the unparsed suffix. -/
private theorem theorem5_extended_splice_programs
    (D : Map) (hD : isOptimalConditional D) (cDrop : ℕ) :
    ∃ c : ℕ, ∀ (a a₀ b b₀ z : BitString) (q : ℕ),
      natCondK D b b₀ ≤ cDrop →
      natCondK D a₀ a ≤ q →
      natCondK D a₀ (pairCode b₀ z) ≤
        natCondK D a (pairCode b z) + 3 * q + c := by
  let firstLen : BitString → ℕ := fun p => bitsToNat (decodeFirst p)
  let rest1 : BitString → BitString := fun p => (decodeSecond p).drop (firstLen p)
  let secondLen : BitString → ℕ := fun p => bitsToNat (decodeFirst (rest1 p))
  let body2 : BitString → BitString := fun p => decodeSecond (rest1 p)
  let firstProg : BitString → BitString := fun p =>
    (decodeSecond p).take (firstLen p)
  let secondProg : BitString → BitString := fun p => (body2 p).take (secondLen p)
  let lastProg : BitString → BitString := fun p => (body2 p).drop (secondLen p)
  have hFirstLen : Computable firstLen :=
    bitsToNat_computable.comp decodeFirst_computable
  have hRest1 : Computable rest1 :=
    Primrec.list_drop.to_comp.comp hFirstLen decodeSecond_computable
  have hSecondLen : Computable secondLen :=
    bitsToNat_computable.comp (decodeFirst_computable.comp hRest1)
  have hBody2 : Computable body2 := decodeSecond_computable.comp hRest1
  have hFirstProg : Computable firstProg :=
    Primrec.list_take.to_comp.comp hFirstLen decodeSecond_computable
  have hSecondProg : Computable secondProg :=
    Primrec.list_take.to_comp.comp hSecondLen hBody2
  have hLastProg : Computable lastProg :=
    Primrec.list_drop.to_comp.comp hSecondLen hBody2
  let M : Map := fun pr =>
    (D (firstProg pr.1, decodeFirst pr.2)).bind fun b =>
      (D (lastProg pr.1, pairCode b (decodeSecond pr.2))).bind fun a =>
        D (secondProg pr.1, a)
  have hFirstArg : Computable (fun pr : BitString × BitString =>
      (firstProg pr.1, decodeFirst pr.2)) :=
    (hFirstProg.comp Computable.fst).pair
      (decodeFirst_computable.comp Computable.snd)
  have hFirst : Partrec (fun pr : BitString × BitString =>
      D (firstProg pr.1, decodeFirst pr.2)) :=
    Partrec.comp hD.1 hFirstArg
  have hLastArg : Computable (fun pr : (BitString × BitString) × BitString =>
      (lastProg pr.1.1, pairCode pr.2 (decodeSecond pr.1.2))) := by
    have hPair : Computable (fun pr : (BitString × BitString) × BitString =>
        pairCode pr.2 (decodeSecond pr.1.2)) :=
      Computable₂.comp pairCode_computable Computable.snd
        (decodeSecond_computable.comp (Computable.snd.comp Computable.fst))
    exact (hLastProg.comp (Computable.fst.comp Computable.fst)).pair hPair
  have hLast : Partrec (fun pr : (BitString × BitString) × BitString =>
      D (lastProg pr.1.1, pairCode pr.2 (decodeSecond pr.1.2))) :=
    Partrec.comp hD.1 hLastArg
  have hSecondArg : Computable
      (fun pr : ((BitString × BitString) × BitString) × BitString =>
        (secondProg pr.1.1.1, pr.2)) := by
    exact (hSecondProg.comp
      (Computable.fst.comp (Computable.fst.comp Computable.fst))).pair Computable.snd
  have hSecond : Partrec
      (fun pr : ((BitString × BitString) × BitString) × BitString =>
        D (secondProg pr.1.1.1, pr.2)) := Partrec.comp hD.1 hSecondArg
  have hInner : Partrec (fun pr : (BitString × BitString) × BitString =>
      (D (lastProg pr.1.1, pairCode pr.2 (decodeSecond pr.1.2))).bind
        (fun a => D (secondProg pr.1.1, a))) := by
    simpa only [Function.comp_apply] using Partrec.bind hLast hSecond.to₂
  have hM : isDecompressor M := by
    simpa only [M, Function.comp_apply] using Partrec.bind hFirst hInner.to₂
  obtain ⟨cM, hM⟩ := hD.2 M hM
  refine ⟨cM + 3 * cDrop + 2, ?_⟩
  intro a a₀ b b₀ z q hDrop hEncode
  have hDropEnat : condK D b b₀ ≤ (cDrop : ℕ∞) := by
    rw [← ENat.natCast_toNat (condK_ne_top_of_optimal D hD b b₀)]
    exact_mod_cast hDrop
  have hEncodeEnat : condK D a₀ a ≤ (q : ℕ∞) := by
    rw [← ENat.natCast_toNat (condK_ne_top_of_optimal D hD a₀ a)]
    exact_mod_cast hEncode
  have hMainBound : condK D a (pairCode b z) ≤
      (natCondK D a (pairCode b z) : ℕ∞) := by
    rw [← ENat.natCast_toNat (condK_ne_top_of_optimal D hD a (pairCode b z))]
    exact_mod_cast (le_rfl : natCondK D a (pairCode b z) ≤ natCondK D a (pairCode b z))
  obtain ⟨pDrop, hpDropLen, hpDrop⟩ :=
    (condK_le_iff D b b₀ cDrop).mp hDropEnat
  obtain ⟨pEncode, hpEncodeLen, hpEncode⟩ :=
    (condK_le_iff D a₀ a q).mp hEncodeEnat
  obtain ⟨pMain, hpMainLen, hpMain⟩ :=
    (condK_le_iff D a (pairCode b z) (natCondK D a (pairCode b z))).mp hMainBound
  let p := pairCode (Nat.bits pDrop.length)
    (pDrop ++ pairCode (Nat.bits pEncode.length) (pEncode ++ pMain))
  have hpRest : rest1 p = pairCode (Nat.bits pEncode.length) (pEncode ++ pMain) := by
    dsimp [rest1, firstLen, p]
    rw [decodeFirst_pairCode, decodeSecond_pairCode, bitsToNat_bits]
    exact List.drop_left
  have hpFirst : firstProg p = pDrop := by
    dsimp [firstProg, firstLen, p]
    rw [decodeFirst_pairCode, decodeSecond_pairCode, bitsToNat_bits]
    exact List.take_left
  have hpSecond : secondProg p = pEncode := by
    dsimp [secondProg, body2, secondLen]
    rw [hpRest, decodeFirst_pairCode, decodeSecond_pairCode, bitsToNat_bits]
    exact List.take_left
  have hpLast : lastProg p = pMain := by
    dsimp [lastProg, body2, secondLen]
    rw [hpRest, decodeFirst_pairCode, decodeSecond_pairCode, bitsToNat_bits]
    exact List.drop_left
  have hProd : produces M p (pairCode b₀ z) a₀ := by
    change a₀ ∈ (D (firstProg p, decodeFirst (pairCode b₀ z))).bind fun b =>
      (D (lastProg p, pairCode b (decodeSecond (pairCode b₀ z)))).bind fun a =>
        D (secondProg p, a)
    rw [hpFirst, hpLast, hpSecond, decodeFirst_pairCode, decodeSecond_pairCode]
    exact Part.mem_bind_iff.mpr ⟨b, hpDrop,
      Part.mem_bind_iff.mpr ⟨a, hpMain, hpEncode⟩⟩
  have hMbound : condK M a₀ (pairCode b₀ z) ≤ (p.length : ℕ∞) := by
    rw [condK_le_iff]
    exact ⟨p, le_rfl, hProd⟩
  have hBound : condK D a₀ (pairCode b₀ z) ≤ (p.length : ℕ∞) + cM := by
    calc
      condK D a₀ (pairCode b₀ z) ≤ condK M a₀ (pairCode b₀ z) + cM := hM _ _
      _ ≤ (p.length : ℕ∞) + cM := by gcongr
  have hBoundNat : natCondK D a₀ (pairCode b₀ z) ≤ p.length + cM :=
    ENat.toNat_le_of_le_natCast hBound
  have hBitsDrop : (Nat.bits pDrop.length).length ≤ cDrop :=
    (length_natBits_le pDrop.length).trans hpDropLen
  have hBitsEncode : (Nat.bits pEncode.length).length ≤ q :=
    (length_natBits_le pEncode.length).trans hpEncodeLen
  change pDrop.length ≤ cDrop at hpDropLen
  change pEncode.length ≤ q at hpEncodeLen
  change pMain.length ≤ natCondK D a (pairCode b z) at hpMainLen
  have hLength : p.length + cM ≤
      natCondK D a (pairCode b z) + 3 * q + (cM + 3 * cDrop + 2) := by
    dsimp [p]
    simp only [length_pairCode, List.length_append]
    omega
  calc
    natCondK D a₀ (pairCode b₀ z) ≤ p.length + cM := hBoundNat
    _ ≤ natCondK D a (pairCode b z) + 3 * q + (cM + 3 * cDrop + 2) := hLength

/-- Given componentwise short descriptions in both directions, recode a subtuple of the
changed tuple
from the original conditional subtuple description. -/
private theorem theorem5_extended_profile_recode
    (D : Map) (hD : isOptimalConditional D) (n m cDrop cEncode : ℕ) :
    ∃ c : ℕ, ∀ (x : Fin n → BitString) (z : BitString)
      (y y₀ : Fin m → BitString) (N : ℕ),
      (∀ i : Fin m, natCondK D (y i) (y₀ i) ≤ cDrop) →
      (∀ i : Fin m, natCondK D (y₀ i) (y i) ≤ logSlack cEncode N) →
      ∀ V W : Finset (Fin (n + m)), V.Nonempty → Disjoint V W →
        subCondKRel D (Fin.append x y₀) z V W ≤
          subCondKRel D (Fin.append x y) z V W + logSlack c N := by
  obtain ⟨cSelf, hSelf⟩ := Kolmogorov.condK_self D hD
  have hSelfNat : ∀ s : BitString, natCondK D s s ≤ cSelf := by
    intro s
    exact ENat.toNat_le_of_le_natCast (hSelf s)
  obtain ⟨cCollectDrop, cCollectEncode, hCollect⟩ :=
    theorem5_extended_collect_subtuple
      D hD (n + m) (max cDrop cSelf) (max cEncode cSelf)
  obtain ⟨cSplice, hSplice⟩ :=
    theorem5_extended_splice_programs
      D hD cCollectDrop
  refine ⟨cCollectEncode + cCollectEncode + cCollectEncode + cSplice, ?_⟩
  intro x z y y₀ N hDrop hEncode V W hV hDis
  let u : Fin (n + m) → BitString := Fin.append x y
  let u₀ : Fin (n + m) → BitString := Fin.append x y₀
  have hDropAll : ∀ j : Fin (n + m), natCondK D (u j) (u₀ j) ≤ max cDrop cSelf := by
    intro j
    by_cases hj : j.val < n
    · let i : Fin n := ⟨j.val, hj⟩
      have hj' : Fin.castAdd m i = j := by
        apply Fin.ext
        rfl
      rw [← hj']
      dsimp [u, u₀]
      rw [Fin.append_left, Fin.append_left]
      exact le_trans (hSelfNat (x i)) (Nat.le_max_right cDrop cSelf)
    · let i : Fin m := ⟨j.val - n, by omega⟩
      have hj' : Fin.natAdd n i = j := by
        apply Fin.ext
        simp [i]
        omega
      rw [← hj']
      dsimp [u, u₀]
      rw [Fin.append_right, Fin.append_right]
      exact le_trans (hDrop i) (Nat.le_max_left cDrop cSelf)
  have hEncodeAll : ∀ j : Fin (n + m),
      natCondK D (u₀ j) (u j) ≤ logSlack (max cEncode cSelf) N := by
    intro j
    by_cases hj : j.val < n
    · let i : Fin n := ⟨j.val, hj⟩
      have hj' : Fin.castAdd m i = j := by
        apply Fin.ext
        rfl
      rw [← hj']
      dsimp [u, u₀]
      rw [Fin.append_left, Fin.append_left]
      exact (hSelfNat (x i)).trans
        (Nat.le_trans (Nat.le_max_right cEncode cSelf) (by
          unfold logSlack
          omega))
    · let i : Fin m := ⟨j.val - n, by omega⟩
      have hj' : Fin.natAdd n i = j := by
        apply Fin.ext
        simp [i]
        omega
      rw [← hj']
      dsimp [u, u₀]
      rw [Fin.append_right, Fin.append_right]
      exact (hEncode i).trans (logSlack_mono_left (Nat.le_max_left cEncode cSelf) N)
  have hW := hCollect u u₀ N W hDropAll hEncodeAll
  have hV' := hCollect u u₀ N V hDropAll hEncodeAll
  have hProfile := hSplice (subtupleCode u V) (subtupleCode u₀ V)
    (subtupleCode u W) (subtupleCode u₀ W) z (logSlack cCollectEncode N)
    hW.1 hV'.2
  have hSlack : 3 * logSlack cCollectEncode N + cSplice ≤
      logSlack (cCollectEncode + cCollectEncode + cCollectEncode + cSplice) N := by
    calc
      3 * logSlack cCollectEncode N + cSplice =
          logSlack cCollectEncode N + logSlack cCollectEncode N +
            logSlack cCollectEncode N + cSplice := by omega
      _ = logSlack (cCollectEncode + cCollectEncode + cCollectEncode) N + cSplice := by
        rw [← logSlack_add_const, ← logSlack_add_const]
      _ ≤ logSlack
          (cCollectEncode + cCollectEncode + cCollectEncode + cSplice) N :=
        logSlack_add_nat_le _ _ _
  change natCondK D (subtupleCode u₀ V) (pairCode (subtupleCode u₀ W) z) ≤
    natCondK D (subtupleCode u V) (pairCode (subtupleCode u W) z) +
      logSlack (cCollectEncode + cCollectEncode + cCollectEncode + cSplice) N
  calc
    natCondK D (subtupleCode u₀ V) (pairCode (subtupleCode u₀ W) z) ≤
        natCondK D (subtupleCode u V) (pairCode (subtupleCode u W) z) +
          (3 * logSlack cCollectEncode N + cSplice) := by
      simpa [Nat.add_assoc] using hProfile
    _ ≤ natCondK D (subtupleCode u V) (pairCode (subtupleCode u W) z) +
        logSlack (cCollectEncode + cCollectEncode + cCollectEncode + cSplice) N :=
      Nat.add_le_add_left hSlack _

/-- build a fixed
partial recursive decoder that reads a tuple of component programs and a program for the
replacement tuple, then runs the component programs with the corresponding decoded components. -/
private theorem theorem5_extended_compiler
    (D : Map) (hD : isOptimalConditional D) (m : ℕ) :
    ∃ E : Map, isDecompressor E ∧
      ∀ (r : Fin m → BitString) (p : BitString) (b : BitString)
        (y₀ y : Fin m → BitString),
        (∀ i : Fin m, produces D (r i) (y₀ i) (y i)) →
        produces D p b (tupleCode y₀) →
        produces E (pairCode (tupleCode r) p) b (tupleCode y) := by
  let E : Map := fun q =>
    (D (decodeSecond q.1, q.2)).bind fun w =>
      (List.Vector.mOfFn (fun i : Fin m =>
        D (((decodeListCode (decodeFirst q.1)).getD i.val []),
          ((decodeListCode w).getD i.val [])))).map (fun v => listCode v.toList)
  have hFirst : Partrec (fun q : BitString × BitString => D (decodeSecond q.1, q.2)) :=
    Partrec.comp hD.1 ((decodeSecond_computable.comp Computable.fst).pair Computable.snd)
  let Args := (BitString × BitString) × BitString
  have hRList : Computable (fun a : Args => decodeListCode (decodeFirst a.1.1)) :=
    decodeListCode_computable.comp
      (decodeFirst_computable.comp (Computable.fst.comp Computable.fst))
  have hYList : Computable (fun a : Args => decodeListCode a.2) :=
    decodeListCode_computable.comp Computable.snd
  have hEach : ∀ i : Fin m, Partrec (fun a : Args =>
      D (((decodeListCode (decodeFirst a.1.1)).getD i.val []),
        ((decodeListCode a.2).getD i.val []))) := by
    intro i
    have hGetR : Computable (fun a : Args =>
        (decodeListCode (decodeFirst a.1.1)).getD i.val []) :=
      (Primrec.list_getD ([] : BitString)).to_comp.comp hRList (Computable.const i.val)
    have hGetY : Computable (fun a : Args => (decodeListCode a.2).getD i.val []) :=
      (Primrec.list_getD ([] : BitString)).to_comp.comp hYList (Computable.const i.val)
    exact Partrec.comp hD.1 (hGetR.pair hGetY)
  have hRuns : Partrec (fun a : Args =>
      List.Vector.mOfFn fun i : Fin m =>
        D (((decodeListCode (decodeFirst a.1.1)).getD i.val []),
          ((decodeListCode a.2).getD i.val []))) :=
    Partrec.vector_mOfFn hEach
  have hMap : Computable (fun a : Args × List.Vector BitString m => listCode a.2.toList) :=
    listCode_computable.comp (Computable.vector_toList.comp Computable.snd)
  have hSecond : Partrec₂ (fun (q : BitString × BitString) (w : BitString) =>
      (List.Vector.mOfFn (fun i : Fin m =>
        D (((decodeListCode (decodeFirst q.1)).getD i.val []),
          ((decodeListCode w).getD i.val [])))).map (fun v => listCode v.toList)) := by
    have hSecond' : Partrec (fun a : Args =>
        (List.Vector.mOfFn (fun i : Fin m =>
          D (((decodeListCode (decodeFirst a.1.1)).getD i.val []),
            ((decodeListCode a.2).getD i.val [])))).map (fun v => listCode v.toList)) :=
      Partrec.map hRuns hMap.to₂
    exact hSecond'.to₂
  refine ⟨E, ?_, ?_⟩
  · change Partrec (fun q : BitString × BitString =>
      (D (decodeSecond q.1, q.2)).bind fun w =>
        (List.Vector.mOfFn (fun i : Fin m =>
          D (((decodeListCode (decodeFirst q.1)).getD i.val []),
            ((decodeListCode w).getD i.val [])))).map (fun v => listCode v.toList))
    exact Partrec.bind hFirst hSecond
  · intro r p b y₀ y hr hp
    change tupleCode y ∈
      (D (decodeSecond (pairCode (tupleCode r) p), b)).bind fun w =>
        (List.Vector.mOfFn (fun i : Fin m =>
          D (((decodeListCode (decodeFirst (pairCode (tupleCode r) p))).getD i.val []),
            ((decodeListCode w).getD i.val [])))).map (fun v => listCode v.toList)
    rw [decodeSecond_pairCode]
    apply Part.mem_bind_iff.mpr
    refine ⟨tupleCode y₀, hp, ?_⟩
    rw [decodeFirst_pairCode]
    simp only [tupleCode, decodeListCode_listCode]
    have hGetR : ∀ i : Fin m, (List.ofFn r).getD i.val [] = r i := by
      intro i
      rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
    have hGetY : ∀ i : Fin m, (List.ofFn y₀).getD i.val [] = y₀ i := by
      intro i
      rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
    have hEq : (fun i : Fin m =>
        D (((List.ofFn r).getD i.val []), ((List.ofFn y₀).getD i.val []))) =
        fun i => Part.some (y i) := by
      funext i
      rw [hGetR i, hGetY i]
      exact (Part.eq_some_iff).2 (hr i)
    have hRun : (List.Vector.ofFn y) ∈
        (List.Vector.mOfFn (fun i : Fin m =>
          D (((List.ofFn r).getD i.val []), ((List.ofFn y₀).getD i.val [])))) := by
      rw [hEq]
      simp
    have hMapped := Part.mem_map (fun v : List.Vector BitString m => listCode v.toList) hRun
    simpa [tupleCode] using hMapped

/-- bound the extra
program length needed to pair the fixed-size component-program tuple with the replacement-tuple
program. -/
private lemma theorem5_extended_packet_length
    (m a : ℕ) (r : Fin m → BitString) (p : BitString)
    (hr : ∀ i : Fin m, (r i).length ≤ a) :
    (pairCode (tupleCode r) p).length ≤ p.length + (2 * (m * (2 * a + 1)) + 1) := by
  have hAppend : ∀ (l : List BitString) (s : BitString),
      (listCode (l ++ [s])).length = (listCode l).length + (2 * s.length + 1) := by
    intro l
    induction l with
    | nil =>
        intro s
        simp [listCode]
        omega
    | cons head tail ih =>
        intro s
        rw [List.cons_append, length_listCode_cons, length_listCode_cons, ih]
        omega
  have hTuple : (tupleCode r).length ≤ m * (2 * a + 1) := by
    induction m with
    | zero =>
        simp [tupleCode]
    | succ m ih =>
        rw [tupleCode, List.ofFn_succ', List.concat_eq_append, hAppend]
        have hHead : (r (Fin.last m)).length ≤ a := hr (Fin.last m)
        have hTail : ∀ i : Fin m, (r i.castSucc).length ≤ a := fun i => hr i.castSucc
        have hRest := ih (fun i => r i.castSucc) hTail
        have hRest' : (listCode (List.ofFn (fun i : Fin m => r i.castSucc))).length ≤
            m * (2 * a + 1) := by simpa [tupleCode] using hRest
        have hLast : 2 * (r (Fin.last m)).length + 1 ≤ 2 * a + 1 := by omega
        calc
          (listCode (List.ofFn (fun i : Fin m => r i.castSucc))).length +
              (2 * (r (Fin.last m)).length + 1) ≤
              m * (2 * a + 1) + (2 * a + 1) := Nat.add_le_add hRest' hLast
          _ = (m + 1) * (2 * a + 1) := by ring
  rw [length_pairCode]
  omega

/-- componentwise constant-cost recovery of `ȳ` from `ȳ₀` gives the same constant-cost recovery when
the whole tuples are conditioned on `(x̄, z)`. -/
private theorem theorem5_extended_cond_recode
    (D : Map) (hD : isOptimalConditional D) (n m cDrop : ℕ) :
    ∃ c : ℕ, ∀ (x : Fin n → BitString) (z : BitString)
      (y y₀ : Fin m → BitString),
      (∀ i : Fin m, natCondK D (y i) (y₀ i) ≤ cDrop) →
      natCondK D (tupleCode y) (pairCode (tupleCode x) z) ≤
        natCondK D (tupleCode y₀) (pairCode (tupleCode x) z) + c := by
  obtain ⟨E, hEdec, hE⟩ :=
    theorem5_extended_compiler
      D hD m
  obtain ⟨cOpt, hOpt⟩ := hD.2 E hEdec
  let cPacket := 2 * (m * (2 * cDrop + 1)) + 1
  refine ⟨cPacket + cOpt, ?_⟩
  intro x z y y₀ hDrop
  let b := pairCode (tupleCode x) z
  have hRecPrograms : ∀ i : Fin m,
      ∃ p, p.length ≤ cDrop ∧ produces D p (y₀ i) (y i) := by
    intro i
    have hfinite := condK_ne_top_of_optimal D hD (y i) (y₀ i)
    have hcost : condK D (y i) (y₀ i) ≤ (cDrop : ℕ∞) := by
      calc
        condK D (y i) (y₀ i) = (natCondK D (y i) (y₀ i) : ℕ∞) :=
          (ENat.natCast_toNat hfinite).symm
        _ ≤ cDrop := by exact_mod_cast hDrop i
    exact (condK_le_iff D (y i) (y₀ i) cDrop).mp hcost
  let r : Fin m → BitString := fun i => Classical.choose (hRecPrograms i)
  have hrLen : ∀ i : Fin m, (r i).length ≤ cDrop := by
    intro i
    exact (Classical.choose_spec (hRecPrograms i)).1
  have hrProd : ∀ i : Fin m, produces D (r i) (y₀ i) (y i) := by
    intro i
    exact (Classical.choose_spec (hRecPrograms i)).2
  have hbaseFinite := condK_ne_top_of_optimal D hD (tupleCode y₀) b
  have hbaseBound : condK D (tupleCode y₀) b ≤
      (natCondK D (tupleCode y₀) b : ℕ∞) := by
    simpa [natCondK] using (ENat.natCast_toNat hbaseFinite).symm.le
  obtain ⟨p, hpLen, hpProd⟩ :=
    (condK_le_iff D (tupleCode y₀) b (natCondK D (tupleCode y₀) b)).mp hbaseBound
  have hOutProd : produces E (pairCode (tupleCode r) p) b (tupleCode y) :=
    hE r p b y₀ y hrProd hpProd
  have hOutBound : condK E (tupleCode y) b ≤
      (programLength (pairCode (tupleCode r) p) : ℕ∞) :=
    (condK_le_iff E (tupleCode y) b (programLength (pairCode (tupleCode r) p))).2
      ⟨pairCode (tupleCode r) p, le_rfl, hOutProd⟩
  have hPacketLen : (pairCode (tupleCode r) p).length ≤ p.length + cPacket := by
    simpa [cPacket] using
      theorem5_extended_packet_length
        m cDrop r p hrLen
  have hRaw : condK D (tupleCode y) b ≤
      ((natCondK D (tupleCode y₀) b + cPacket + cOpt : ℕ) : ℕ∞) := by
    calc
      condK D (tupleCode y) b ≤ condK E (tupleCode y) b + cOpt := hOpt _ _
      _ ≤ (programLength (pairCode (tupleCode r) p) : ℕ∞) + cOpt :=
        add_le_add hOutBound le_rfl
      _ = ((programLength (pairCode (tupleCode r) p) + cOpt : ℕ) : ℕ∞) := by
        push_cast
        rfl
      _ ≤ ((natCondK D (tupleCode y₀) b + cPacket + cOpt : ℕ) : ℕ∞) := by
        have hLenBase : p.length ≤ natCondK D (tupleCode y₀) b := hpLen
        have hPacketNat : programLength (pairCode (tupleCode r) p) ≤ p.length + cPacket := by
          simpa [programLength] using hPacketLen
        exact_mod_cast (show programLength (pairCode (tupleCode r) p) + cOpt ≤
          natCondK D (tupleCode y₀) b + cPacket + cOpt by omega)
  have hOutFinite := condK_ne_top_of_optimal D hD (tupleCode y) b
  have hRaw' := hRaw
  rw [← ENat.natCast_toNat hOutFinite] at hRaw'
  have hNat : natCondK D (tupleCode y) b ≤
      natCondK D (tupleCode y₀) b + cPacket + cOpt := by
    exact_mod_cast hRaw'
  change natCondK D (tupleCode y) (pairCode (tupleCode x) z) ≤
    natCondK D (tupleCode y₀) (pairCode (tupleCode x) z) + (cPacket + cOpt)
  simpa [b, Nat.add_assoc] using hNat

/-- replace `ȳ` by a tuple `ȳ°` with components of length at most
`N = K(⟨x̄, ȳ⟩, z)`, changing the relativized extended profile by `O(log N)` upwards only, and
keeping `K(ȳ | x̄, z) ≤ K(ȳ° | x̄, z) + O(1)`.

Construction: `y°_i` is the first (in a fixed dovetailed enumeration of the computations of the
optimal machine `D`) program of length `K(y_i)` producing `y_i` with the empty condition, with its
last `c'` bits dropped, where `c'` is a constant with `K(y_i) ≤ N + c'` for all `x̄, ȳ, z, i`
(`y_i` is computable from `⟨tupleCode ⟨x̄, ȳ⟩, z⟩`); so `|y°_i| ≤ N`.  Then `y_i` is computable from
`y°_i` and the `≤ c'` dropped bits, and `y°_i` is computable from `y_i` and the number
`K(y_i) ≤ N + c'` (`O(log N)` bits).  Hence, for disjoint `V ≠ ∅, W`, a program for
`(x̄ ȳ°)_V` given `⟨(x̄ ȳ°)_W, z⟩` is: the dropped bits of the components in `W` (to recover
`(x̄ ȳ)_W`), the numbers `K(y_i)` for the components in `V`, and a shortest program for
`(x̄ ȳ)_V` given `⟨(x̄ ȳ)_W, z⟩`; this gives the profile bound with slack `c·(log N + 1)`.  The last
conjunct holds because `ȳ` is computable from `ȳ°` and the `O(1)` dropped bits. -/
private theorem theorem5_extended_short_programs
    (D : Map) (hD : isOptimalConditional D) (n m : ℕ) :
    ∃ c : ℕ, ∀ (x : Fin n → BitString) (z : BitString) (y : Fin m → BitString),
      ∃ y₀ : Fin m → BitString,
        (∀ i : Fin m, (y₀ i).length ≤ natK D (pairCode (tupleCode (Fin.append x y)) z)) ∧
        (∀ V W : Finset (Fin (n + m)), V.Nonempty → Disjoint V W →
          subCondKRel D (Fin.append x y₀) z V W ≤
            subCondKRel D (Fin.append x y) z V W +
              logSlack c (natK D (pairCode (tupleCode (Fin.append x y)) z))) ∧
        natCondK D (tupleCode y) (pairCode (tupleCode x) z) ≤
          natCondK D (tupleCode y₀) (pairCode (tupleCode x) z) + c := by
  obtain ⟨cK, hK⟩ :=
    theorem5_extended_component_bound D hD n m
  obtain ⟨cShort, hShort⟩ :=
    theorem5_extended_shorten D hD n m cK hK
  obtain ⟨cProfile, hProfile⟩ :=
    theorem5_extended_profile_recode
      D hD n m cShort cShort
  obtain ⟨cCond, hCond⟩ :=
    theorem5_extended_cond_recode
      D hD n m cShort
  let c := cShort + cProfile + cCond
  refine ⟨c, ?_⟩
  intro x z y
  let N := natK D (pairCode (tupleCode (Fin.append x y)) z)
  obtain ⟨y₀, hLen, hDrop, hEncode⟩ := hShort x z y
  have hProf := hProfile x z y y₀ N hDrop hEncode
  have hCond' := hCond x z y y₀ hDrop
  refine ⟨y₀, ?_, ?_, ?_⟩
  · intro i
    simpa [N] using hLen i
  · intro V W hV hDis
    have hBound := hProf V W hV hDis
    have hc : cProfile ≤ c := by dsimp [c]; omega
    exact hBound.trans (Nat.add_le_add_left (logSlack_mono_left hc N) _)
  · have hc : cCond ≤ c := by dsimp [c]; omega
    omega

/-- projecting a tuple code at fixed
coordinates
is the computable list reordering already used for extended profiles. -/
private lemma theorem5_extended_projection
    {k : ℕ} (V : Finset (Fin k)) (u : Fin k → BitString) :
    theorem4_extended_typization_profile_reindexList
      ((V.sort (· ≤ ·)).map Fin.val) (tupleCode u) = subtupleCode u V := by
  unfold theorem4_extended_typization_profile_reindexList subtupleCode
  simp only [tupleCode, decodeListCode_listCode, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp

/-- all profile thresholds of the
hybrid tuple
`(x,y₀)` are bounded by a fixed multiple of `N+1`. This includes empty and overlapping index
sets. Project a description of `(x,y,z)` to `x`, describe `y₀` literally, join the descriptions,
and then project to the requested output coordinates; the condition can be ignored. -/
private theorem theorem5_extended_threshold_bound
    (D : Map) (hD : isOptimalConditional D) (n m : ℕ) :
    ∃ b : ℕ, ∀ (x : Fin n → BitString) (z : BitString) (y y₀ : Fin m → BitString),
      (∀ i, (y₀ i).length ≤ natK D (pairCode (tupleCode (Fin.append x y)) z)) →
      ∀ V W : Finset (Fin (n + m)), subCondKRel D (Fin.append x y₀) z V W ≤
        b * (natK D (pairCode (tupleCode (Fin.append x y)) z) + 1) := by
  classical
  let firstTuple : BitString → BitString := fun w =>
    decodeFirst (theorem4_extended_chain_splitTuple n (decodeFirst w))
  have hFirstTuple : Computable firstTuple :=
    decodeFirst_computable.comp
      ((theorem4_extended_chain_splitTuple_computable n).comp decodeFirst_computable)
  obtain ⟨cX, hX⟩ := plainK_map_le D hD firstTuple hFirstTuple
  obtain ⟨cLit, hLit⟩ := plainK_le_length D hD
  obtain ⟨cPair, hPair⟩ := plainK_pair_le_add_two_log D hD
  obtain ⟨cCond, hCond⟩ := theorem5_extended_stochastic_model_condNat_bound D hD
  have hProjection (V : Finset (Fin (n + m))) :
      ∃ c : ℕ, ∀ x : Fin n → BitString, ∀ y₀ : Fin m → BitString,
        natK D (subtupleCode (Fin.append x y₀) V) ≤
          natK D (pairCode (tupleCode x) (tupleCode y₀)) + c := by
    let proj := theorem4_extended_typization_profile_reindexList
      ((V.sort (· ≤ ·)).map Fin.val)
    have hproj : Computable proj :=
      theorem4_extended_typization_profile_reindexList_computable _
    obtain ⟨c, hc⟩ := plainK_map_le D hD
      (proj ∘ theorem4_extended_chain_joinTuple)
      (hproj.comp theorem4_extended_chain_joinTuple_computable)
    refine ⟨c, fun x y₀ => ?_⟩
    have h := hc (pairCode (tupleCode x) (tupleCode y₀))
    change plainK D (proj (theorem4_extended_chain_joinTuple
      (pairCode (tupleCode x) (tupleCode y₀)))) ≤ _ at h
    rw [theorem4_extended_chain_joinTuple_correct] at h
    dsimp [proj] at h
    rw [theorem5_extended_projection] at h
    rw [← ENat.natCast_toNat (plainK_ne_top D hD (subtupleCode (Fin.append x y₀) V)),
      ← ENat.natCast_toNat (plainK_ne_top D hD (pairCode (tupleCode x) (tupleCode y₀)))] at h
    exact_mod_cast h
  choose cProj hcProj using hProjection
  let C := Finset.univ.sup cProj
  refine ⟨3 + 2 * m + (3 * cX + m + cLit + cPair + C + cCond), ?_⟩
  intro x z y y₀ hy₀ V W
  let N := natK D (pairCode (tupleCode (Fin.append x y)) z)
  have hXraw := hX (pairCode (tupleCode (Fin.append x y)) z)
  have hFirstEq : firstTuple (pairCode (tupleCode (Fin.append x y)) z) = tupleCode x := by
    simp only [firstTuple, decodeFirst_pairCode,
      theorem4_extended_chain_splitTuple_correct]
  rw [hFirstEq, ← ENat.natCast_toNat (plainK_ne_top D hD (tupleCode x)),
    ← ENat.natCast_toNat (plainK_ne_top D hD
      (pairCode (tupleCode (Fin.append x y)) z))] at hXraw
  have hXnat : natK D (tupleCode x) ≤ N + cX := by exact_mod_cast hXraw
  have hListLength : ∀ l : List BitString, (∀ s ∈ l, s.length ≤ N) →
      (listCode l).length ≤ l.length * (2 * N + 1) := by
    intro l
    induction l with
    | nil => simp
    | cons s l ih =>
      intro hs
      have hhead := hs s (by simp)
      have htail := ih (fun t ht => hs t (by simp [ht]))
      rw [length_listCode_cons, List.length_cons]
      nlinarith
  have hYlength : (tupleCode y₀).length ≤ m * (2 * N + 1) := by
    simpa [tupleCode] using hListLength (List.ofFn y₀) (by
      intro s hs
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hs
      exact hy₀ i)
  have hYraw := hLit (tupleCode y₀)
  have hYnat : natK D (tupleCode y₀) ≤ m * (2 * N + 1) + cLit := by
    have h : natK D (tupleCode y₀) ≤ (tupleCode y₀).length + cLit :=
      ENat.toNat_le_of_le_natCast (by simpa [programLength] using hYraw)
    omega
  have hPairRaw := hPair (tupleCode x) (tupleCode y₀)
  rw [Kolmogorov.cPair,
    ← ENat.natCast_toNat (plainK_ne_top D hD (pairCode (tupleCode x) (tupleCode y₀))),
    ← ENat.natCast_toNat (plainK_ne_top D hD (tupleCode x)),
    ← ENat.natCast_toNat (plainK_ne_top D hD (tupleCode y₀))] at hPairRaw
  have hPairNat : natK D (pairCode (tupleCode x) (tupleCode y₀)) ≤
      natK D (tupleCode x) + natK D (tupleCode y₀) +
        (2 * Nat.log 2 (natK D (tupleCode x)) + cPair) := by
    exact_mod_cast hPairRaw
  have hLog := Nat.log_le_self 2 (natK D (tupleCode x))
  have hProj := hcProj V x y₀
  have hC : cProj V ≤ C := Finset.le_sup (Finset.mem_univ V)
  have hCond := hCond (subtupleCode (Fin.append x y₀) V)
    (pairCode (subtupleCode (Fin.append x y₀) W) z)
  change natCondK D (subtupleCode (Fin.append x y₀) V)
    (pairCode (subtupleCode (Fin.append x y₀) W) z) ≤ _
  change _ ≤ (3 + 2 * m + (3 * cX + m + cLit + cPair + C + cCond)) * (N + 1)
  nlinarith

/-- a length limit and a fixed finite
table of
thresholds bounded by `b*(N+1)` have a code of length `O(log N)`. The returned readers are
computable and recover the entire table, with no restriction to valid profile indices. -/
private theorem theorem5_extended_advice
    (k b : ℕ) :
    ∃ R : BitString → ℕ,
    ∃ P : BitString → Finset (Fin k) → Finset (Fin k) → ℕ,
      Computable R ∧ (∀ V W, Computable (fun p => P p V W)) ∧
      ∃ c : ℕ, ∀ (N : ℕ) (T : Finset (Fin k) → Finset (Fin k) → ℕ),
        (∀ V W, T V W ≤ b * (N + 1)) →
        ∃ p : BitString, p.length ≤ logSlack c N ∧ R p = N ∧ ∀ V W, P p V W = T V W := by
  classical
  let coords := (Finset.univ : Finset (Finset (Fin k) × Finset (Fin k))).toList
  let read : BitString → ℕ → ℕ := fun p i => decodeBits ((decodeListCode p).getD i [])
  have hread (i : ℕ) : Computable (fun p => read p i) :=
    decodeBits_computable.comp
      ((Primrec.list_getD []).comp decodeListCode_primrec (Primrec.const i)).to_comp
  let R := fun p => read p 0
  let P := fun p V W => read p (coords.idxOf (V, W) + 1)
  refine ⟨R, P, hread 0, fun V W => hread _, ?_⟩
  obtain ⟨d, hd⟩ := logSlack_linear_bound 1 (b + 1) b
  let L := coords.length + 1
  refine ⟨2 * L * d + L, ?_⟩
  intro N T hT
  let values := N :: coords.map (fun q => T q.1 q.2)
  let p := listCode (values.map Nat.bits)
  have hvalue : ∀ v ∈ values, (Nat.bits v).length ≤ logSlack d N := by
    intro v hv
    have hle : v ≤ (b + 1) * N + b := by
      rcases List.mem_cons.mp hv with rfl | hv
      · nlinarith
      · obtain ⟨q, _, rfl⟩ := List.mem_map.mp hv
        have := hT q.1 q.2
        nlinarith
    have h := logSlack_le_of_linear_bound hd hle
    simp only [logSlack, one_mul] at h
    exact le_trans (Nat.le_add_right _ _) h
  have hlength : ∀ l : List ℕ, (∀ v ∈ l, (Nat.bits v).length ≤ logSlack d N) →
      (listCode (l.map Nat.bits)).length ≤ l.length * (2 * logSlack d N + 1) := by
    intro l
    induction l with
    | nil => simp
    | cons v l ih =>
      intro hl
      have hv := hl v (by simp)
      have ht := ih (fun w hw => hl w (by simp [hw]))
      simp only [List.map_cons, List.length_cons]
      rw [length_listCode_cons]
      nlinarith
  refine ⟨p, ?_, ?_, ?_⟩
  · have h := hlength values hvalue
    have hvlen : values.length = L := by simp [values, L]
    rw [hvlen] at h
    change p.length ≤ _
    dsimp [p]
    refine h.trans ?_
    unfold logSlack
    nlinarith
  · change decodeBits ((decodeListCode p).getD 0 []) = N
    rw [show p = listCode (values.map Nat.bits) from rfl, decodeListCode_listCode]
    simp [values, decodeBits_natBits]
  · intro V W
    have hmem : (V, W) ∈ coords := by simp [coords]
    have hi : coords.idxOf (V, W) < coords.length := List.idxOf_lt_length_iff.mpr hmem
    change decodeBits ((decodeListCode p).getD (coords.idxOf (V, W) + 1) []) = _
    simp only [p, decodeListCode_listCode, values, List.map_cons, List.getD_cons_succ]
    rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map,
      List.getElem_map, List.getElem_idxOf hi, decodeBits_natBits]

/-- over a member `x` of `S`,
membership in the
section is precisely the component length bounds and the explicit profile inequalities. -/
private lemma theorem5_extended_section_membership
    (D : Map) {n m : ℕ} (S : Finset (Fin n → BitString)) (N : ℕ)
    (x : Fin n → BitString) (hx : x ∈ S) (u₀ : Fin (n + m) → BitString)
    (z : BitString) (a : Fin m → BitString) :
    a ∈ theorem5_extended_special_union_section
        (theorem5_extended_special_union_levelSet D S N u₀ z) x ↔
      (∀ i, (a i).length ≤ N) ∧
      ∀ V W : Finset (Fin (n + m)), V.Nonempty → Disjoint V W →
        subCondKRel D (Fin.append x a) z V W ≤ subCondKRel D u₀ z V W := by
  classical
  rw [theorem5_extended_special_union_mem_section]
  unfold theorem5_extended_special_union_levelSet
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨hc, hp⟩
    exact ⟨fun i => by simpa using
      theorem5_extended_special_union_length_of_mem_candidates hc i, hp⟩
  · rintro ⟨hl, hp⟩
    exact ⟨theorem5_extended_special_union_append_mem_candidates hx hl, hp⟩

/-- a finite conjunction of
semidecidable
predicates is semidecidable, by running the finitely many searches successively. -/
private theorem theorem5_extended_finite_conjunction
    {α ι : Type*} [Primcodable α] [Finite ι] (F : ι → α → Prop)
    (hF : ∀ i, IsRE (F i)) : IsRE (fun a => ∀ i, F i a) := by
  classical
  let _ := Fintype.ofFinite ι
  have hList : ∀ l : List ι, IsRE (fun a => ∀ i ∈ l, F i a) := by
    intro l
    induction l with
    | nil =>
      exact isRE_of_computable_bool _ (fun _ => true) (by simp) (Computable.const true)
    | cons i l ih =>
      exact ((hF i).and ih).of_iff (by simp)
  exact (hList (Finset.univ : Finset ι).toList).of_iff (by simp)

/-- the upper graph of natural
conditional
complexity is enumerable for an optimal machine. Search for a program of at most the given
length and a halting computation producing the requested output. -/
private theorem theorem5_extended_complexity_upper_graph
    (D : Map) (hD : isOptimalConditional D) :
    IsRE (fun q : BitString × BitString × ℕ => natCondK D q.1 q.2.1 ≤ q.2.2) := by
  have hgraph : IsRE (fun t : (BitString × BitString × ℕ) × BitString =>
      t.1.1 ∈ D (t.2, t.1.2.1)) := by
    exact (Partrec.graphIsRe D hD.1).comp_computable
      ((Computable.snd.pair (Computable.fst.comp (Computable.snd.comp Computable.fst))).pair
        (Computable.fst.comp Computable.fst))
  have hlen : Computable (fun t : (BitString × BitString × ℕ) × BitString =>
      decide (t.2.length ≤ t.1.2.2)) :=
    Primrec.to_comp (PrimrecPred.decide
      (Primrec.nat_le.comp (Primrec.list_length.comp Primrec.snd)
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))
  refine (IsRE.exists_encodable (R := fun (q : BitString × BitString × ℕ) (p : BitString) =>
    decide (p.length ≤ q.2.2) = true ∧ q.1 ∈ D (p, q.2.1))
    (hgraph.and_computable hlen)).of_iff ?_
  intro q
  constructor
  · rintro ⟨p, hp, hout⟩
    exact ENat.toNat_le_of_le_natCast ((condK_le_iff D _ _ _).mpr
      ⟨p, of_decide_eq_true hp, hout⟩)
  · intro h
    have hc : condK D q.1 q.2.1 ≤ (q.2.2 : ℕ∞) := by
      rw [← ENat.natCast_toNat (condK_ne_top_of_optimal D hD _ _)]
      exact_mod_cast h
    obtain ⟨p, hp, hout⟩ := (condK_le_iff D _ _ _).mp hc
    exact ⟨p, decide_eq_true hp, hout⟩

/-- with computable readers for the
length
limit and explicit thresholds, membership in the bounded profile section is uniformly
semidecidable. No bound on the thresholds or on the advice length is assumed. The context is
parsed as `pairCode (tupleCode x) z`, and malformed tuple codes are padded by empty strings. -/
private theorem theorem5_extended_semidecidable
    (D : Map) (hD : isOptimalConditional D) (n m : ℕ)
    (R : BitString → ℕ) (hR : Computable R)
    (P : BitString → Finset (Fin (n + m)) → Finset (Fin (n + m)) → ℕ)
    (hP : ∀ V W, Computable (fun p => P p V W)) :
    IsRE (fun q : (BitString × BitString) × (Fin m → BitString) =>
      (∀ i, (q.2 i).length ≤ R q.1.1) ∧
      ∀ V W : Finset (Fin (n + m)), V.Nonempty → Disjoint V W →
        subCondKRel D
          (Fin.append (fun i : Fin n =>
            (decodeListCode (decodeFirst q.1.2)).getD i.val []) q.2)
          (decodeSecond q.1.2) V W ≤ P q.1.1 V W) := by
  classical
  let α := (BitString × BitString) × (Fin m → BitString)
  have hLengths : IsRE (fun q : α => ∀ i, (q.2 i).length ≤ R q.1.1) := by
    apply theorem5_extended_finite_conjunction
    intro i
    refine isRE_of_computable_bool _
      (fun q => decide ((q.2 i).length ≤ R q.1.1)) (by simp) ?_
    exact (Primrec.nat_le.decide.to_comp).comp
      (Computable.list_length.comp
        (Computable.fin_app.comp Computable.snd (Computable.const i)))
        (hR.comp (Computable.fst.comp Computable.fst))
  have hTuple : Computable (tupleCode : (Fin m → BitString) → BitString) := by
    unfold tupleCode
    exact listCode_computable.comp
      (Primrec.list_ofFn (fun i =>
        Primrec.fin_app.comp Primrec.id (Primrec.const i))).to_comp
  let u : α → Fin (n + m) → BitString := fun q =>
    Fin.append (fun i : Fin n =>
      (decodeListCode (decodeFirst q.1.2)).getD i.val []) q.2
  have hU : Computable (fun q : α => tupleCode (u q)) := by
    have hx : Computable (fun q : α =>
        theorem5_extended_stochastic_model_decodeTupleCode n (decodeFirst q.1.2)) :=
      (theorem5_extended_stochastic_model_decodeTupleCode_computable n).to_comp.comp
      (decodeFirst_computable.comp (Computable.snd.comp Computable.fst))
    have hy := hTuple.comp (Computable.snd : Computable (fun q : α => q.2))
    exact (theorem4_extended_chain_joinTuple_computable.comp
      (pairCode_computable.comp (hx.pair hy))).of_eq (fun q => by
        rw [theorem5_extended_stochastic_model_decodeTupleCode,
          theorem4_extended_chain_joinTuple_correct]
        rfl)
  have hSub (V : Finset (Fin (n + m))) : Computable (fun q : α => subtupleCode (u q) V) :=
    ((theorem4_extended_typization_profile_reindexList_computable
      ((V.sort (· ≤ ·)).map Fin.val)).comp hU).of_eq
        (fun q => theorem5_extended_projection V
                    (u q))
  have hOne (V W : Finset (Fin (n + m))) : IsRE (fun q : α =>
      V.Nonempty → Disjoint V W →
        subCondKRel D (u q) (decodeSecond q.1.2) V W ≤ P q.1.1 V W) := by
    by_cases hValid : V.Nonempty ∧ Disjoint V W
    · have hc : Computable (fun q : α =>
          (subtupleCode (u q) V,
            pairCode (subtupleCode (u q) W) (decodeSecond q.1.2), P q.1.1 V W)) :=
        (hSub V).pair ((pairCode_computable.comp
          ((hSub W).pair (decodeSecond_computable.comp
            (Computable.snd.comp Computable.fst)))).pair
          ((hP V W).comp (Computable.fst.comp Computable.fst)))
      exact ((theorem5_extended_complexity_upper_graph D hD).comp_computable hc).of_iff
        (by intro q; simp [subCondKRel, hValid.1, hValid.2])
    · exact isRE_of_computable_bool _ (fun _ => true)
        (by intro q; simp only [true_iff]; tauto) (Computable.const true)
  have hProfile : IsRE (fun q : α => ∀ V W : Finset (Fin (n + m)),
      V.Nonempty → Disjoint V W →
        subCondKRel D (u q) (decodeSecond q.1.2) V W ≤ P q.1.1 V W) := by
    apply theorem5_extended_finite_conjunction
    intro V
    exact theorem5_extended_finite_conjunction _
        (hOne V)
  exact hLengths.and hProfile

/-- dovetail candidate tuples and
stages of a
semidecision procedure. The finite lists grow by appending outputs, enumerate exactly the
predicate, and may contain repetitions. -/
private theorem theorem5_extended_staged_enumeration
    (m : ℕ) (A : (BitString × BitString) × (Fin m → BitString) → Prop)
    (hA : IsRE A) :
    ∃ E : (BitString × BitString) → ℕ → List BitString,
      Computable (fun q : (BitString × BitString) × ℕ => E q.1 q.2) ∧
      (∀ q t, E q t <+: E q (t + 1)) ∧
      (∀ q t w, w ∈ E q t → ∃ a, A (q, a) ∧ tupleCode a = w) ∧
      (∀ q a, A (q, a) → ∃ t, tupleCode a ∈ E q t) := by
  classical
  obtain ⟨chk, hchk, -, hiff⟩ := hA.exists_stageApprox
  let decodeTuple : ℕ → Fin m → BitString := fun i =>
    (@Encodable.decode (Fin m → BitString)
      (Primcodable.toEncodable (α := Fin m → BitString)) i).getD (fun _ => [])
  have hdecode : Computable decodeTuple :=
    Computable.option_getD Computable.decode (Computable.const (fun _ => []))
  have hTuple : Computable (tupleCode : (Fin m → BitString) → BitString) := by
    unfold tupleCode
    exact listCode_computable.comp
      (Primrec.list_ofFn (fun i =>
        Primrec.fin_app.comp Primrec.id (Primrec.const i))).to_comp
  let check : (BitString × BitString) → ℕ → Bool := fun q i =>
    chk (q, decodeTuple i.unpair.1) i.unpair.2
  have hcheck : Computable₂ check :=
    hchk.comp (Computable.fst.pair
      (hdecode.comp (Computable.fst.comp (Computable.unpair.comp Computable.snd))))
      (Computable.snd.comp (Computable.unpair.comp Computable.snd))
  let E : (BitString × BitString) → ℕ → List BitString := fun q t =>
    Nat.rec [] (fun i acc =>
      if check q i then acc ++ [tupleCode (decodeTuple i.unpair.1)] else acc) t
  have hstep : Computable₂ (fun (q : (BitString × BitString) × ℕ)
      (r : ℕ × List BitString) =>
      if check q.1 r.1 then r.2 ++ [tupleCode (decodeTuple r.1.unpair.1)] else r.2) := by
    have hc : Computable (fun z : ((BitString × BitString) × ℕ) × (ℕ × List BitString) =>
        check z.1.1 z.2.1) := hcheck.comp (Computable.fst.comp Computable.fst)
      (Computable.fst.comp Computable.snd)
    have hv : Computable (fun z : ((BitString × BitString) × ℕ) × (ℕ × List BitString) =>
        tupleCode (decodeTuple z.2.1.unpair.1)) :=
      hTuple.comp (hdecode.comp (Computable.fst.comp (Computable.unpair.comp
        (Computable.fst.comp Computable.snd))))
    have ha : Computable (fun z : ((BitString × BitString) × ℕ) × (ℕ × List BitString) =>
        z.2.2 ++ [tupleCode (decodeTuple z.2.1.unpair.1)]) :=
      Computable.list_append.comp (Computable.snd.comp Computable.snd)
        (Computable.list_cons.comp hv (Computable.const []))
    exact (Computable.cond hc ha (Computable.snd.comp Computable.snd)).of_eq
      (fun z => by cases hh : check z.1.1 z.2.1 <;> simp [hh])
  have hE : Computable (fun q : (BitString × BitString) × ℕ => E q.1 q.2) :=
    (Computable.nat_rec Computable.snd (Computable.const []) hstep).of_eq (fun _ => rfl)
  have hmono : ∀ q t, E q t <+: E q (t + 1) := by
    intro q t
    change E q t <+: if check q t then E q t ++ [_] else E q t
    by_cases hc : check q t = true
    · simp [hc, List.prefix_append]
    · simp [hc]
  have hSound : ∀ q t w, w ∈ E q t → ∃ a, A (q, a) ∧ tupleCode a = w := by
    intro q t
    induction t with
    | zero => simp [E]
    | succ t ih =>
      intro w hw
      change w ∈ (if check q t then E q t ++ [tupleCode (decodeTuple t.unpair.1)]
        else E q t) at hw
      by_cases hc : check q t = true
      · simp only [ite_eq_left hc, List.mem_append, List.mem_singleton] at hw
        rcases hw with hw | rfl
        · exact ih _ hw
        · exact ⟨decodeTuple t.unpair.1, (hiff _).mpr ⟨t.unpair.2, hc⟩, rfl⟩
      · exact ih _ (by simpa [hc] using hw)
  have hComplete : ∀ q a, A (q, a) → ∃ t, tupleCode a ∈ E q t := by
    intro q a ha
    obtain ⟨s, hs⟩ := (hiff (q, a)).mp ha
    let i := Nat.pair (@Encodable.encode (Fin m → BitString)
      (Primcodable.toEncodable (α := Fin m → BitString)) a) s
    have hi : check q i = true := by simpa [check, i, decodeTuple] using hs
    refine ⟨i + 1, ?_⟩
    change tupleCode a ∈ (if check q i then
      E q i ++ [tupleCode (decodeTuple i.unpair.1)] else E q i)
    simp [hi, decodeTuple, i]
  exact ⟨E, hE, hmono, hSound, hComplete⟩

/-- decoding the advice and context
of a staged enumeration is computable. -/
private theorem theorem5_extended_context_enumeration_computable
    (E : (BitString × BitString) → ℕ → List BitString)
    (hE : Computable (fun q : (BitString × BitString) × ℕ => E q.1 q.2)) :
    Computable (fun q : BitString × ℕ => E (decodeFirst q.1, decodeSecond q.1) q.2) := by
  have hFirst : Computable (fun q : BitString × ℕ => decodeFirst q.1) :=
    Computable.comp decodeFirst_computable Computable.fst
  have hSecond : Computable (fun q : BitString × ℕ => decodeSecond q.1) :=
    Computable.comp decodeSecond_computable Computable.fst
  have hInput : Computable (fun q : BitString × ℕ => ((decodeFirst q.1, decodeSecond q.1), q.2)) :=
    Computable.pair (Computable.pair hFirst hSecond) Computable.snd
  exact Computable.comp hE hInput

/-- the program parser computably
separates the binary index from the advice and
repackages the advice with the external condition. -/
private theorem theorem5_extended_program_input_computable :
    Computable (fun q : BitString × BitString =>
      (decodeSecond q.1, pairCode (decodeFirst q.1) q.2)) := by
  have hFirst : Computable (fun q : BitString × BitString => decodeFirst q.1) :=
    Computable.comp decodeFirst_computable Computable.fst
  have hSecond : Computable (fun q : BitString × BitString => decodeSecond q.1) :=
    Computable.comp decodeSecond_computable Computable.fst
  have hLen : Computable (fun q : BitString × BitString => (decodeFirst q.1).length) :=
    Computable.comp Computable.list_length hFirst
  have hTag : Computable (fun q : BitString × BitString => natCode (decodeFirst q.1).length) :=
    Computable.comp natCode_computable hLen
  have hTagAndFirst : Computable (fun q : BitString × BitString =>
      natCode (decodeFirst q.1).length ++ decodeFirst q.1) :=
    Computable₂.comp Computable.list_append hTag hFirst
  have hContext : Computable (fun q : BitString × BitString =>
      (natCode (decodeFirst q.1).length ++ decodeFirst q.1) ++ q.2) :=
    Computable₂.comp Computable.list_append hTagAndFirst Computable.snd
  exact Computable.pair hSecond hContext

/-- the fixed-length extractor of a
staged list reads a binary ordinal and the separately
encoded advice. Prefix monotonicity ensures that an ordinal present at a stage retains its value. -/
private theorem theorem5_extended_staged_decoder
    (E : (BitString × BitString) → ℕ → List BitString)
    (hE : Computable (fun q : (BitString × BitString) × ℕ => E q.1 q.2))
    (hmono : ∀ q t, E q t <+: E q (t + 1)) :
    ∃ g : BitString → BitString → Part BitString,
      Partrec (fun q : BitString × BitString => g q.2 q.1) ∧
      ∀ (p ctx : BitString) (t i : ℕ),
        i < ((E (p, ctx) t).eraseDups).length →
        ((E (p, ctx) t).eraseDups).getD i [] ∈ g ctx (pairCode p (Nat.bits i)) := by
  let enum : BitString → ℕ → List BitString := fun w t => E (decodeFirst w, decodeSecond w) t
  have hEnum : Computable (fun q : BitString × ℕ => enum q.1 q.2) :=
      theorem5_extended_context_enumeration_computable E hE
  let g : BitString → BitString → Part BitString := fun ctx w =>
    StagedEnumeration.condFFixedLength enum (pairCode (decodeFirst w) ctx) (decodeSecond w)
  have hExtractor := Partrec.comp (StagedEnumeration.condFFixedLength_partrec enum hEnum)
    theorem5_extended_program_input_computable
  have hg : Partrec (fun q : BitString × BitString => g q.2 q.1) :=
    hExtractor.of_eq (fun q => rfl)
  refine ⟨g, hg, ?_⟩
  intro p ctx t i hi
  have hDistinct : StagedEnumeration.condDistinctAt enum (pairCode p ctx) t =
      (E (p, ctx) t).eraseDups := by
    simp only [StagedEnumeration.condDistinctAt, enum, decodeFirst_pairCode, decodeSecond_pairCode]
  have hI : bitsToNat (Nat.bits i) <
      (StagedEnumeration.condDistinctAt enum (pairCode p ctx) t).length := by
    rw [bitsToNat_bits, hDistinct]
    exact hi
  have hev := StagedEnumeration.condFFixedLength_eval enum
    (fun w t => hmono (decodeFirst w, decodeSecond w) t)
    (pairCode p ctx) (Nat.bits i) t hI
  rw [bitsToNat_bits, hDistinct] at hev
  simpa only [g, decodeFirst_pairCode, decodeSecond_pairCode] using hev

/-- a uniformly enumerable finite
family has a
partial recursive ordinal decoder. Given advice `p`, context `ctx`, and any finite set `Q`
whose membership is exactly the supplied RE predicate, every member has an index below
`Q.card`. This step neither constructs advice nor bounds its length. -/
private theorem theorem5_extended_enumeration_index
    (m : ℕ) (A : (BitString × BitString) × (Fin m → BitString) → Prop)
    (hA : IsRE A) :
    ∃ g : BitString → BitString → Part BitString,
      Partrec (fun q : BitString × BitString => g q.2 q.1) ∧
      ∀ (p ctx : BitString) (Q : Finset (Fin m → BitString)),
        (∀ a, a ∈ Q ↔ A ((p, ctx), a)) → ∀ a ∈ Q,
          ∃ i < Q.card, tupleCode a ∈ g ctx (pairCode p (Nat.bits i)) := by
  classical
  obtain ⟨E, hE, hmono, hSound, hComplete⟩ :=
    theorem5_extended_staged_enumeration m A hA
  obtain ⟨g, hg, hdecode⟩ :=
      theorem5_extended_staged_decoder E hE
      hmono
  refine ⟨g, hg, ?_⟩
  intro p ctx Q hQ a ha
  obtain ⟨t, ht⟩ := hComplete (p, ctx) a ((hQ a).mp ha)
  let L := (E (p, ctx) t).eraseDups
  have hmem : tupleCode a ∈ L := by simpa [L] using ht
  let i := L.idxOf (tupleCode a)
  have hi : i < L.length := List.idxOf_lt_length_iff.mpr hmem
  have hget : L.getD i [] = tupleCode a := by
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_idxOf hi
  have hL : L.toFinset ⊆ Q.image tupleCode := by
    intro w hw
    have hw' : w ∈ E (p, ctx) t := by simpa [L] using hw
    obtain ⟨a', ha', rfl⟩ := hSound (p, ctx) t w hw'
    exact Finset.mem_image.mpr ⟨a', (hQ a').mpr ha', rfl⟩
  have hlen : L.length ≤ Q.card := by
    calc
      L.length = L.toFinset.card := (List.toFinset_card_of_nodup (nodup_eraseDups_list _)).symm
      _ ≤ (Q.image tupleCode).card := Finset.card_le_card hL
      _ ≤ Q.card := Finset.card_image_le
  refine ⟨i, hi.trans_le hlen, ?_⟩
  have hout := hdecode p ctx t i hi
  change L.getD i [] ∈ g ctx (pairCode p (Nat.bits i)) at hout
  rwa [hget] at hout

/-- optimality bounds the complexity
of an
indexed output by the logarithm of the number of indices, twice the advice length, and a
constant depending only on the fixed partial recursive decoder. -/
private theorem theorem5_extended_index_description
    (D : Map) (hD : isOptimalConditional D)
    (g : BitString → BitString → Part BitString)
    (hg : Partrec (fun q : BitString × BitString => g q.2 q.1)) :
    ∃ c : ℕ, ∀ (r i : ℕ) (a ctx p : BitString),
      i < r → a ∈ g ctx (pairCode p (Nat.bits i)) →
      natCondK D a ctx ≤ Nat.log2 r + 2 * p.length + c := by
  obtain ⟨C, hC⟩ := condK_partrec_cond_map_le_swapped D hD g hg
  refine ⟨C + 2, fun r i a ctx p hir hout => ?_⟩
  have hmachine := hC ctx (pairCode p (Nat.bits i)) a hout
  have hnat : natCondK D a ctx ≤ (pairCode p (Nat.bits i)).length + C :=
    ENat.toNat_le_of_le_natCast hmachine
  have hbits : (Nat.bits i).length ≤ Nat.log2 r + 1 := by
    rw [Nat.size_eq_bits_len, Nat.log2_eq_log_two]
    apply Nat.size_le.mpr
    exact lt_trans hir (by simpa [Nat.succ_eq_add_one] using
      Nat.lt_pow_succ_log_self (b := 2) (by decide) r)
  rw [length_pairCode] at hnat
  omega

/-- the first half of
Lemma 7 of the paper (`x̄` lies in the strong projection of the level set).  Let
`N = K(⟨x̄, ȳ⟩, z)`, let `ȳ°` (the `y₀` of the statement) be any `m`-tuple whose components have
length at most `N`, and let `A₀ = levelSet D S N ⟨x̄, ȳ°⟩ z`.  Then the section of `A₀` over `x̄`
is large: `K(ȳ° | x̄, z) ≤ log₂ |(A₀)_{x̄}| + O(log N)`.

Proof: as `x̄ ∈ S`, `(A₀)_{x̄}` is the set of the `ȳ' ∈ (B^{≤N})^m` with
`K(x̄_V ȳ'_V | x̄_W ȳ'_W, z) ≤ K(x̄_V ȳ°_V | x̄_W ȳ°_W, z)` for all disjoint `V ≠ ∅, W`. It contains
`ȳ°`, and it is enumerable given `⟨x̄, z⟩`, `N` and the finitely many numbers
`K(x̄_V ȳ°_V | x̄_W ȳ°_W, z)` (`K(·|·) ≤ k` is semi-decidable, `D` being partial computable).
These numbers are `O(N)` (as `K(x̄) ≤ N + O(1)` and `|y°_i| ≤ N`), so they take `O(log N)` bits in
self-delimiting form; then `ȳ°` is given by its index in the enumeration, a number below
`|(A₀)_{x̄}|`. -/
private theorem theorem5_extended_section_lower_bound
    (D : Map) (hD : isOptimalConditional D) (n m : ℕ) :
    ∃ c : ℕ, ∀ (x : Fin n → BitString) (z : BitString) (S : Finset (Fin n → BitString)),
      x ∈ S → ∀ y y₀ : Fin m → BitString,
        (∀ i : Fin m, (y₀ i).length ≤ natK D (pairCode (tupleCode (Fin.append x y)) z)) →
        natCondK D (tupleCode y₀) (pairCode (tupleCode x) z) ≤
          Nat.log2 (theorem5_extended_special_union_section
            (theorem5_extended_special_union_levelSet D S
              (natK D (pairCode (tupleCode (Fin.append x y)) z)) (Fin.append x y₀) z) x).card +
            logSlack c (natK D (pairCode (tupleCode (Fin.append x y)) z)) := by
  classical
  obtain ⟨b, hb⟩ :=
      theorem5_extended_threshold_bound D hD n m
  obtain ⟨R, P, hR, hP, cAdvice, hAdvice⟩ :=
      theorem5_extended_advice (n + m) b
  obtain ⟨g, hg, hEnum⟩ :=
      theorem5_extended_enumeration_index m _
    (theorem5_extended_semidecidable D hD n m R
        hR P hP)
  obtain ⟨cIndex, hIndex⟩ :=
      theorem5_extended_index_description D hD g
      hg
  refine ⟨2 * cAdvice + cIndex, ?_⟩
  intro x z S hxS y y₀ hy₀
  let N := natK D (pairCode (tupleCode (Fin.append x y)) z)
  let Q := theorem5_extended_special_union_section
    (theorem5_extended_special_union_levelSet D S N (Fin.append x y₀) z) x
  obtain ⟨p, hp, hpN, hpT⟩ := hAdvice N (subCondKRel D (Fin.append x y₀) z)
    (hb x z y y₀ hy₀)
  have hdecode : (fun i : Fin n =>
      (decodeListCode (decodeFirst (pairCode (tupleCode x) z))).getD i.val []) = x := by
    funext i
    simp [tupleCode, decodeFirst_pairCode]
  have hQ : ∀ a, a ∈ Q ↔
      (∀ i, (a i).length ≤ R p) ∧
      ∀ V W : Finset (Fin (n + m)), V.Nonempty → Disjoint V W →
        subCondKRel D
          (Fin.append (fun i : Fin n => (decodeListCode
            (decodeFirst (pairCode (tupleCode x) z))).getD i.val []) a)
          (decodeSecond (pairCode (tupleCode x) z)) V W ≤ P p V W := by
    intro a
    rw [hdecode, decodeSecond_pairCode, hpN]
    simp only [hpT]
    exact theorem5_extended_section_membership D
        S N x hxS (Fin.append x y₀) z a
  have hyQ : y₀ ∈ Q :=
    (theorem5_extended_section_membership D S N
        x hxS (Fin.append x y₀) z y₀).mpr
      ⟨hy₀, fun _ _ _ _ => le_rfl⟩
  obtain ⟨i, hi, hout⟩ := hEnum p (pairCode (tupleCode x) z) Q hQ y₀ hyQ
  have hbound := hIndex Q.card i (tupleCode y₀) (pairCode (tupleCode x) z) p hi hout
  have hslack : 2 * p.length + cIndex ≤ logSlack (2 * cAdvice + cIndex) N := by
    unfold logSlack at hp ⊢
    nlinarith
  change natCondK D (tupleCode y₀) (pairCode (tupleCode x) z) ≤
    Nat.log2 Q.card + logSlack (2 * cAdvice + cIndex) N
  omega

/-- The admissible coordinate pairs whose entropy values are supplied to the finite-search
decoder for the correct-set family. -/
private def theorem5_extended_finite_description_entropy_indices
    {n m : ℕ} :
    Finset (Finset (Fin (n + m)) × Finset (Fin (n + m))) :=
  Finset.univ.filter fun p => p.1.Nonempty ∧ Disjoint p.1 p.2

/-- A self-delimiting list containing the visible size parameter, projection threshold, slack,
and the entropy table at all admissible coordinate pairs. -/
private noncomputable def theorem5_extended_finite_description_numeric_code
    {n m : ℕ} (N κ s : ℕ) (A₀ : Finset (Fin (n + m) → BitString)) : BitString :=
  listCode
    (([N, κ, s].map Nat.bits) ++
      (theorem5_extended_finite_description_entropy_indices
        (n := n) (m := m)).toList.map fun p => Nat.bits (combEnt A₀ p.1 p.2))

/-- decode the canonical code of a finite tuple set into a list with exactly those members.
Malformed tuple codes are padded with empty strings or truncated to the fixed arity. -/
private theorem theorem5_extended_decode_set
    (n : ℕ) :
    ∃ decode : BitString → List (Fin n → BitString), Primrec decode ∧
      ∀ S : Finset (Fin n → BitString), (decode (tupleSetCode S)).toFinset = S := by
  classical
  let decode := fun w : BitString => (decodeListCode w).map
    (theorem5_extended_stochastic_model_decodeTuple n)
  have hTuple : Primrec (theorem5_extended_stochastic_model_decodeTuple n) := by
    apply Primrec.fin_curry.mpr
    exact (Primrec.list_getD []).comp (decodeListCode_primrec.comp Primrec.fst)
      (Primrec.fin_val.comp Primrec.snd)
  refine ⟨decode, Primrec.list_map decodeListCode_primrec (hTuple.comp Primrec.snd).to₂, ?_⟩
  intro S
  ext x
  simp only [decode, tupleSetCode, finsetListCode, decodeListCode_listCode,
    List.mem_toFinset, List.mem_map, mem_canonicalFinsetList, Finset.mem_image]
  constructor
  · rintro ⟨w, ⟨y, hy, rfl⟩, hxy⟩
    rw [theorem5_extended_stochastic_model_decodeTuple_tupleCode] at hxy
    exact hxy ▸ hy
  · intro hx
    exact ⟨tupleCode x, ⟨x, hx, rfl⟩,
      theorem5_extended_stochastic_model_decodeTuple_tupleCode n x⟩

/-- serialize a tuple, using the fixed ordering of its coordinates. -/
private theorem theorem5_extended_tuple_code
    (n : ℕ) : Primrec (tupleCode : (Fin n → BitString) → BitString) := by
  exact listCode_primrec.comp (Primrec.list_ofFn fun i =>
    Primrec.fin_app.comp Primrec.id (Primrec.const i))

/-- serialize a list of tuples as the canonical code of its underlying finite set. -/
private theorem theorem5_extended_set_code
    (n : ℕ) :
    Primrec (fun L : List (Fin n → BitString) => tupleSetCode L.toFinset) := by
  have hMap := Primrec.list_map Primrec.id
    ((theorem5_extended_tuple_code n).comp Primrec.snd).to₂
  apply (listCode_primrec.comp
    (canonicalFinsetList_toFinset_primrec.comp hMap)).of_eq
  intro L
  change listCode (canonicalFinsetList _) = listCode (canonicalFinsetList _)
  congr 2
  ext w
  simp

/-- enumerate all subsets of the finite candidate universe. The output consists of lists of
`(n+m)`-tuples; taking their underlying sets yields exactly the powerset, independently of
list order or repetitions. This step does not perform any entropy or projection tests. -/
private theorem theorem5_extended_candidate_subsets
    (n m : ℕ) :
    ∃ F : List (Fin n → BitString) × ℕ → List (List (Fin (n + m) → BitString)),
      Primrec F ∧ ∀ (L : List (Fin n → BitString)) (N : ℕ),
        (F (L, N)).toFinset.image List.toFinset =
          (theorem5_extended_special_union_candidates L.toFinset N).powerset := by
  classical
  have hBounded : Primrec Kolmogorov.boundedPrograms := by
    unfold Kolmogorov.boundedPrograms
    exact Primrec.list_flatMap
      (Primrec.list_range.comp (Primrec.succ.comp Primrec.id))
      (Kolmogorov.primrec_exactLengthPrograms.comp Primrec.snd).to₂
  have hTuples : ∀ k : ℕ, ∃ B : ℕ → List (Fin k → BitString), Primrec B ∧
      ∀ N y, y ∈ B N ↔ ∀ i, (y i).length ≤ N := by
    intro k
    induction k with
    | zero =>
      refine ⟨fun _ => [fun i => Fin.elim0 i], Primrec.const _, ?_⟩
      intro N y
      simp only [List.mem_singleton]
      constructor
      · intro _ i
        exact Fin.elim0 i
      · intro _
        funext i
        exact Fin.elim0 i
    | succ k ih =>
      obtain ⟨B, hB, hBmem⟩ := ih
      have hCons : Primrec (fun q : BitString × (Fin k → BitString) =>
          (Fin.cons q.1 q.2 : Fin (k + 1) → BitString)) := by
        apply Primrec.fin_curry.mpr
        have hSwitch : Primrec₂ (fun i : Fin (k + 1) =>
            fun q : BitString × (Fin k → BitString) => (Fin.cons q.1 q.2 : Fin (k + 1) → BitString)
                                                         i) := by
          apply Primrec.fin_curry₁.mpr
          intro i
          refine Fin.cases ?_ (fun j => ?_) i
          · simpa using (Primrec.fst : Primrec (fun q : BitString × (Fin k → BitString) => q.1))
          · simpa using (Primrec.fin_app.comp Primrec.snd (Primrec.const j) :
              Primrec (fun q : BitString × (Fin k → BitString) => q.2 j))
        exact hSwitch.comp Primrec.snd Primrec.fst
      let B' (N : ℕ) : List (Fin (k + 1) → BitString) := (Kolmogorov.boundedPrograms N).flatMap fun
          w =>
        (B N).map (fun z => (Fin.cons w z : Fin (k + 1) → BitString))
      have hMap : Primrec (fun r : ℕ × BitString =>
          (B r.1).map (fun z => (Fin.cons r.2 z : Fin (k + 1) → BitString))) :=
        Primrec.list_map (hB.comp Primrec.fst)
          (hCons.comp ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)).to₂
      refine ⟨B', Primrec.list_flatMap hBounded hMap.to₂, ?_⟩
      intro N y
      simp only [B', List.mem_flatMap, List.mem_map]
      constructor
      · rintro ⟨w, hw, z, hz, rfl⟩ i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa using (Kolmogorov.mem_boundedPrograms_iff w N).mp hw
        · simpa using (hBmem N z).mp hz j
      · intro hy
        refine ⟨y 0, (Kolmogorov.mem_boundedPrograms_iff _ _).mpr (hy 0),
          Fin.tail y, (hBmem _ _).mpr (fun i => hy i.succ), Fin.cons_self_tail y⟩
  obtain ⟨B, hB, hBmem⟩ := hTuples m
  have hAppend : Primrec (fun q : (Fin n → BitString) × (Fin m → BitString) =>
      Fin.append q.1 q.2) := by
    apply Primrec.fin_curry.mpr
    have hSwitch : Primrec₂ (fun i : Fin (n + m) =>
        fun q : (Fin n → BitString) × (Fin m → BitString) => Fin.append q.1 q.2 i) := by
      apply Primrec.fin_curry₁.mpr
      intro i
      induction i using Fin.addCases with
      | left j => simpa using (Primrec.fin_app.comp Primrec.fst (Primrec.const j))
      | right j => simpa using (Primrec.fin_app.comp Primrec.snd (Primrec.const j))
    exact hSwitch.comp Primrec.snd Primrec.fst
  let U (q : List (Fin n → BitString) × ℕ) := q.1.flatMap fun x =>
    (B q.2).map fun y => Fin.append x y
  have hMap : Primrec (fun r : (List (Fin n → BitString) × ℕ) ×
      (Fin n → BitString) => (B r.1.2).map fun y => Fin.append r.2 y) :=
    Primrec.list_map (hB.comp (Primrec.snd.comp Primrec.fst))
      (hAppend.comp ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)).to₂
  have hU : Primrec U := Primrec.list_flatMap Primrec.fst hMap.to₂
  have hUSet (L : List (Fin n → BitString)) (N : ℕ) :
      (U (L, N)).toFinset = theorem5_extended_special_union_candidates L.toFinset N := by
    ext u
    simp only [U, List.mem_toFinset, List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨x, hx, y, hy, rfl⟩
      exact theorem5_extended_special_union_append_mem_candidates
        (List.mem_toFinset.mpr hx) ((hBmem N y).mp hy)
    · intro hu
      obtain ⟨⟨x, y⟩, hxy, heq⟩ := Finset.mem_image.mp hu
      obtain ⟨hx, hy⟩ := Finset.mem_product.mp hxy
      refine ⟨x, List.mem_toFinset.mp hx, y, (hBmem _ _).mpr ?_, heq⟩
      intro i
      exact theorem5_extended_special_union_mem_shortStrings.mp
        (Fintype.mem_piFinset.mp hy i)
  refine ⟨fun q => (U q).sublists, Kolmogorov.primrec_sublists_gen hU, ?_⟩
  intro L N
  rw [← hUSet L N]
  ext C
  simp only [Finset.mem_image, List.mem_toFinset, List.mem_sublists, Finset.mem_powerset]
  constructor
  · rintro ⟨xs, hxs, rfl⟩ u hu
    exact List.mem_toFinset.mpr (hxs.subset (List.mem_toFinset.mp hu))
  · intro hC
    let xs := (U (L, N)).filter (fun u => decide (u ∈ C))
    refine ⟨xs, List.filter_sublist, ?_⟩
    ext u
    simp only [xs, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact ⟨And.right, fun hu => ⟨List.mem_toFinset.mp (hC hu), hu⟩⟩

/-- count distinct projected values in one section of a finite list. Both the projection and the
section key are supplied as primitive recursive string-valued maps. -/
private theorem theorem5_extended_section_card
    {α : Type*} [Primcodable α] [DecidableEq α]
    (f g : α → BitString) (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun q : List α × BitString =>
      ((q.1.toFinset.filter fun u => g u = q.2).image f).card) := by
  have hTest : Primrec (fun r : (List α × BitString) × α =>
      decide (g r.2 = r.1.2)) :=
    (Primrec.eq.comp (hg.comp Primrec.snd) (Primrec.snd.comp Primrec.fst)).decide
  have hFilter := Primrec.list_filter Primrec.fst hTest.to₂
  have hMap := Primrec.list_map hFilter (hf.comp Primrec.snd).to₂
  apply (Primrec.list_length.comp
    (canonicalFinsetList_toFinset_primrec.comp hMap)).of_eq
  intro q
  rw [length_canonicalFinsetList]
  congr 1
  ext w
  simp

/-- compute a single combinatorial entropy from a finite list of tuples, by filtering sections,
counting distinct projected tuples, taking the maximum, and applying the ceiling logarithm.
The coordinate sets are fixed parameters; the assertion includes empty lists and empty blocks. -/
private theorem theorem5_extended_entropy
    (d : ℕ) (V W : Finset (Fin d)) :
    Primrec (fun L : List (Fin d → BitString) => combEnt L.toFinset V W) := by
  classical
  have hSub (T : Finset (Fin d)) :
      Primrec (fun u : Fin d → BitString => subtupleCode u T) :=
    listCode_primrec.comp (Primrec.list_map (Primrec.const (T.sort (· ≤ ·))) Primrec.fin_app)
  have hCount : Primrec (fun q : List (Fin d → BitString) × (Fin d → BitString) =>
      (sectionProjection q.1.toFinset V W q.2).card) :=
    (theorem5_extended_section_card _ _ (hSub V) (hSub W)).comp
      (Primrec.fst.pair ((hSub W).comp Primrec.snd))
  let count (L : List (Fin d → BitString)) (u : Fin d → BitString) :=
    (sectionProjection L.toFinset V W u).card
  let maximum (L : List (Fin d → BitString)) :=
    L.foldr (fun u k => max (count L u) k) 0
  have hStep : Primrec₂ (fun (L : List (Fin d → BitString))
      (r : (Fin d → BitString) × ℕ) => max (count L r.1) r.2) :=
    (Primrec.nat_max.comp
      (hCount.comp (Primrec.fst.pair (Primrec.fst.comp Primrec.snd)))
      (Primrec.snd.comp Primrec.snd)).to₂
  have hMaximum : Primrec maximum := Primrec.list_foldr Primrec.id (Primrec.const 0) hStep
  apply (primrec_clogTwo.comp hMaximum).of_eq
  intro L
  have hFold : ∀ xs : List (Fin d → BitString),
      xs.foldr (fun u k => max (count L u) k) 0 = xs.toFinset.sup (count L) := by
    intro xs
    induction xs with
    | nil => simp
    | cons u xs ih => simp [ih]
  change Nat.clog 2 (L.foldr (fun u k => max (count L u) k) 0) = _
  rw [hFold]
  rfl

/-- compute the cardinality of one section over the first block of coordinates, by counting distinct
codes of the second block. -/
private theorem theorem5_extended_section_count
    (n m : ℕ) :
    Primrec (fun q : List (Fin (n + m) → BitString) × (Fin n → BitString) =>
      (theorem5_extended_special_union_section (n := n) (m := m) q.1.toFinset q.2).card) := by
  classical
  let front (u : Fin (n + m) → BitString) := tupleCode (u ∘ Fin.castAdd m)
  let back (u : Fin (n + m) → BitString) := tupleCode (u ∘ Fin.natAdd n)
  have hFrontTuple : Primrec (fun u : Fin (n + m) → BitString => u ∘ Fin.castAdd m) := by
    apply Primrec.fin_curry.mpr
    have hSwitch : Primrec₂ (fun i : Fin n =>
        fun u : Fin (n + m) → BitString => u (Fin.castAdd m i)) :=
      Primrec.fin_curry₁.mpr (fun i => Primrec.fin_app.comp Primrec.id
        (Primrec.const (Fin.castAdd m i)))
    exact hSwitch.comp Primrec.snd Primrec.fst
  have hBackTuple : Primrec (fun u : Fin (n + m) → BitString => u ∘ Fin.natAdd n) := by
    apply Primrec.fin_curry.mpr
    have hSwitch : Primrec₂ (fun i : Fin m =>
        fun u : Fin (n + m) → BitString => u (Fin.natAdd n i)) :=
      Primrec.fin_curry₁.mpr (fun i => Primrec.fin_app.comp Primrec.id
        (Primrec.const (Fin.natAdd n i)))
    exact hSwitch.comp Primrec.snd Primrec.fst
  have hFront : Primrec front := (theorem5_extended_tuple_code n).comp hFrontTuple
  have hBack : Primrec back := (theorem5_extended_tuple_code m).comp hBackTuple
  let count (C : List (Fin (n + m) → BitString)) (x : Fin n → BitString) :=
    ((C.toFinset.filter fun u => front u = tupleCode x).image back).card
  have hCount : Primrec (fun q : List (Fin (n + m) → BitString) ×
      (Fin n → BitString) => count q.1 q.2) :=
    (theorem5_extended_section_card back front hBack hFront).comp
      (Primrec.fst.pair ((theorem5_extended_tuple_code n).comp Primrec.snd))
  have hInj (k : ℕ) : Function.Injective (tupleCode : (Fin k → BitString) → BitString) := by
    intro u v h
    exact List.ofFn_injective (listCode_injective h)
  have hCountEq (C : List (Fin (n + m) → BitString)) (x : Fin n → BitString) :
      count C x = (theorem5_extended_special_union_section (n := n) (m := m) C.toFinset
          x).card := by
    have hFilter : (C.toFinset.filter fun u => front u = tupleCode x) =
        C.toFinset.filter (fun u => u ∘ Fin.castAdd m = x) := by
      ext u
      simp only [Finset.mem_filter]
      exact and_congr_right (fun _ => (hInj n).eq_iff)
    have hImage : (C.toFinset.filter fun u => front u = tupleCode x).image back =
        (theorem5_extended_special_union_section (n := n) (m := m) C.toFinset x).image
            tupleCode := by
      rw [hFilter]
      simp only [theorem5_extended_special_union_section, Finset.image_image]
      rfl
    dsimp only [count]
    rw [hImage, Finset.card_image_of_injective _ (hInj m)]
  exact hCount.of_eq (fun q => hCountEq q.1 q.2)

/-- compute and canonically serialize the strong projection of one supplied finite set. The input
lists represent `S` and `C`; the other two inputs are the threshold and slack. Empty sections
are excluded even when the numerical threshold is zero. -/
private theorem theorem5_extended_projection_code
    (n m : ℕ) :
    Primrec (fun q : (List (Fin n → BitString) × ℕ × ℕ) ×
        List (Fin (n + m) → BitString) =>
      tupleSetCode (theorem5_extended_special_union_strongProj (n := n) (m := m)
        q.1.1.toFinset q.1.2.1 q.1.2.2 q.2.toFinset)) := by
  let count (C : List (Fin (n + m) → BitString)) (x : Fin n → BitString) :=
    (theorem5_extended_special_union_section (n := n) (m := m) C.toFinset x).card
  have hCount : Primrec (fun q : List (Fin (n + m) → BitString) ×
      (Fin n → BitString) => count q.1 q.2) := theorem5_extended_section_count n m
  let Q := (List (Fin n → BitString) × ℕ × ℕ) × List (Fin (n + m) → BitString)
  have hCountInput : Primrec (fun r : Q × (Fin n → BitString) => (r.1.2, r.2)) :=
    (Primrec.snd.comp Primrec.fst).pair Primrec.snd
  have hCountArgRaw := hCount.comp hCountInput
  have hCountArg : Primrec (fun r : Q × (Fin n → BitString) => count r.1.2 r.2) :=
    hCountArgRaw.of_eq (fun r => rfl)
  have hKappa : Primrec (fun r : Q × (Fin n → BitString) => r.1.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have hSlack : Primrec (fun r : Q × (Fin n → BitString) => r.1.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have hLog : Primrec (fun r : Q × (Fin n → BitString) => Nat.log2 (count r.1.2 r.2)) :=
    NatLog.nat_log2_primrec.comp hCountArg
  have hBound : Primrec (fun r : Q × (Fin n → BitString) =>
      Nat.log2 (count r.1.2 r.2) + r.1.1.2.2) := Primrec.nat_add.comp hLog hSlack
  have hPos : PrimrecPred (fun r : Q × (Fin n → BitString) => 0 < count r.1.2 r.2) :=
    Primrec.nat_lt.comp (Primrec.const 0) hCountArg
  have hThreshold : PrimrecPred (fun r : Q × (Fin n → BitString) =>
      r.1.1.2.1 ≤ Nat.log2 (count r.1.2 r.2) + r.1.1.2.2) :=
    Primrec.nat_le.comp hKappa hBound
  have hTest : Primrec (fun r : Q × (Fin n → BitString) =>
      decide (0 < count r.1.2 r.2 ∧ r.1.1.2.1 ≤ Nat.log2 (count r.1.2 r.2) + r.1.1.2.2)) :=
    (hPos.and hThreshold).decide
  have hFilterRaw := Primrec.list_filter (Primrec.fst.comp Primrec.fst) hTest.to₂
  have hFilter : Primrec (fun q : Q => q.1.1.filter fun x =>
      decide (0 < count q.2 x ∧ q.1.2.1 ≤ Nat.log2 (count q.2 x) + q.1.2.2)) :=
    hFilterRaw.of_eq (fun q => rfl)
  apply ((theorem5_extended_set_code n).comp hFilter).of_eq
  intro q
  apply congrArg tupleSetCode
  ext x
  simp [theorem5_extended_special_union_strongProj, count, Finset.card_pos]

/-- a fixed
finite-search decoder produces the canonical family code from the code of `S` and the numerical
table consisting of `N`, `κ`, `s`, and the admissible entropies of `A₀`.  This is the algorithmic
part of the description argument; it does not bound the cost of supplying those inputs. -/
private theorem theorem5_extended_finite_search_description
    (D : Map) (hD : isOptimalConditional D) (n m : ℕ) :
    ∃ c : ℕ, ∀ (S : Finset (Fin n → BitString)) (N κ s : ℕ)
      (A₀ : Finset (Fin (n + m) → BitString)),
      natK D (theorem5_extended_special_union_familyCode
        (theorem5_extended_special_union_family S N κ s A₀)) ≤
        natK D (pairCode (tupleSetCode S)
          (theorem5_extended_finite_description_numeric_code
            N κ s A₀)) + c := by
  classical
  obtain ⟨decode, hDecode, hDecodeSet⟩ := theorem5_extended_decode_set n
  obtain ⟨enum, hEnum, hEnumSets⟩ := theorem5_extended_candidate_subsets n m
  let E :=
    (theorem5_extended_finite_description_entropy_indices
      (n := n) (m := m)).toList
  let num (w : BitString) (i : ℕ) : ℕ :=
    bitsToNat ((decodeListCode (decodeSecond w)).getD i [])
  have hNum (i : ℕ) : Primrec (fun w : BitString => num w i) :=
    bitsToNat_primrec.comp ((Primrec.list_getD []).comp
      (decodeListCode_primrec.comp CodedFiniteDistribution.decodeSecond_primrec)
      (Primrec.const i))
  let good (w : BitString) (L : List (Fin (n + m) → BitString)) : Prop :=
    ∀ p ∈ E, combEnt L.toFinset p.1 p.2 ≤ num w (3 + E.idxOf p)
  have hEach (V W : Finset (Fin (n + m))) :
      Primrec (fun q : BitString × List (Fin (n + m) → BitString) =>
        decide (combEnt q.2.toFinset V W ≤ num q.1 (3 + E.idxOf (V, W)))) :=
    (Primrec.nat_le.comp
      ((theorem5_extended_entropy (n + m) V W).comp Primrec.snd)
      ((hNum (3 + E.idxOf (V, W))).comp Primrec.fst)).decide
  have hAll : ∀ I : List (Finset (Fin (n + m)) × Finset (Fin (n + m))),
      Primrec (fun q : BitString × List (Fin (n + m) → BitString) =>
        decide (∀ p ∈ I, combEnt q.2.toFinset p.1 p.2 ≤ num q.1 (3 + E.idxOf p))) := by
    intro I
    induction I with
    | nil => simpa using (Primrec.const true : Primrec (fun _ :
        BitString × List (Fin (n + m) → BitString) => true))
    | cons p I ih =>
      exact (Primrec.and.comp (hEach p.1 p.2) ih).of_eq (fun q => by simp)
  have hGood : Primrec (fun q : BitString × List (Fin (n + m) → BitString) =>
      decide (good q.1 q.2)) := hAll E
  let sets (w : BitString) := enum (decode (decodeFirst w), num w 0)
  have hSets : Primrec sets :=
    hEnum.comp ((hDecode.comp CodedFiniteDistribution.decodeFirst_primrec).pair (hNum 0))
  let accepted (w : BitString) := (sets w).filter (fun L => decide (good w L))
  have hAccepted : Primrec accepted := Primrec.list_filter hSets hGood.to₂
  let projected (w : BitString) (L : List (Fin (n + m) → BitString)) :=
    tupleSetCode (theorem5_extended_special_union_strongProj (n := n) (m := m)
      (decode (decodeFirst w)).toFinset (num w 1) (num w 2) L.toFinset)
  have hSArg : Primrec (fun q : BitString × List (Fin (n + m) → BitString) =>
      decode (decodeFirst q.1)) :=
    hDecode.comp (CodedFiniteDistribution.decodeFirst_primrec.comp Primrec.fst)
  have hκArg : Primrec (fun q : BitString × List (Fin (n + m) → BitString) =>
      num q.1 1) := (hNum 1).comp Primrec.fst
  have hsArg : Primrec (fun q : BitString × List (Fin (n + m) → BitString) =>
      num q.1 2) := (hNum 2).comp Primrec.fst
  have hProjectArg : Primrec (fun q : BitString × List (Fin (n + m) → BitString) =>
      ((decode (decodeFirst q.1), num q.1 1, num q.1 2), q.2)) :=
    (hSArg.pair (hκArg.pair hsArg)).pair Primrec.snd
  have hProjectedRaw :=
    (theorem5_extended_projection_code n m).comp hProjectArg
  have hProjected : Primrec (fun q : BitString × List (Fin (n + m) → BitString) =>
      projected q.1 q.2) :=
    hProjectedRaw.of_eq (fun q => rfl)
  let codes (w : BitString) := (accepted w).map fun L =>
    pairCode (tupleSetCode L.toFinset) (projected w L)
  have hCCode : Primrec (fun q : BitString × List (Fin (n + m) → BitString) =>
      tupleSetCode q.2.toFinset) :=
    (theorem5_extended_set_code (n + m)).comp Primrec.snd
  have hPairCodes : Primrec (fun q : BitString × List (Fin (n + m) → BitString) =>
      pairCode (tupleSetCode q.2.toFinset) (projected q.1 q.2)) :=
    CodedFiniteDistribution.pairCode_primrec.comp hCCode hProjected
  have hCodesRaw := Primrec.list_map hAccepted hPairCodes.to₂
  have hCodes : Primrec codes := hCodesRaw.of_eq (fun w => rfl)
  let f (w : BitString) := finsetListCode (codes w).toFinset
  have hRawCode := listCode_primrec.comp (canonicalFinsetList_toFinset_primrec.comp hCodes)
  have hf : Computable f := hRawCode.to_comp.of_eq (fun w => rfl)
  obtain ⟨c, hc⟩ := plainK_map_le D hD f hf
  refine ⟨c, ?_⟩
  intro S N κ s A₀
  let q := pairCode (tupleSetCode S)
    (theorem5_extended_finite_description_numeric_code
      N κ s A₀)
  have hS : (decode (decodeFirst q)).toFinset = S := by
    rw [show decodeFirst q = tupleSetCode S from decodeFirst_pairCode _ _]
    exact hDecodeSet S
  have hN : num q 0 = N := by
    simp only [num, q, decodeSecond_pairCode,
      theorem5_extended_finite_description_numeric_code,
      decodeListCode_listCode, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      List.getD_cons_zero, bitsToNat_bits]
  have hκ : num q 1 = κ := by
    simp only [num, q, decodeSecond_pairCode,
      theorem5_extended_finite_description_numeric_code,
      decodeListCode_listCode, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      List.getD_cons_zero, List.getD_cons_succ, bitsToNat_bits]
  have hs : num q 2 = s := by
    simp only [num, q, decodeSecond_pairCode,
      theorem5_extended_finite_description_numeric_code,
      decodeListCode_listCode, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      List.getD_cons_zero, List.getD_cons_succ, bitsToNat_bits]
  have hEntropy (p : Finset (Fin (n + m)) × Finset (Fin (n + m))) (hp : p ∈ E) :
      num q (3 + E.idxOf p) = combEnt A₀ p.1 p.2 := by
    have hi : E.idxOf p < E.length := List.idxOf_lt_length_iff.mpr hp
    have hi' : E.idxOf p < (E.map fun p => Nat.bits (combEnt A₀ p.1 p.2)).length := by
      simpa using hi
    change bitsToNat ((decodeListCode (decodeSecond q)).getD (3 + E.idxOf p) []) = _
    rw [show decodeSecond q =
        theorem5_extended_finite_description_numeric_code
          N κ s A₀ from decodeSecond_pairCode _ _]
    unfold theorem5_extended_finite_description_numeric_code
    rw [decodeListCode_listCode, List.getD_append_right _ _ _ _ (by simp)]
    change bitsToNat ((E.map fun p => Nat.bits (combEnt A₀ p.1 p.2)).getD
      (3 + E.idxOf p - 3) []) = _
    rw [Nat.add_sub_cancel_left, List.getD_eq_getElem _ _ hi', List.getElem_map,
      List.getElem_idxOf hi, bitsToNat_bits]
  have hMemE (V W : Finset (Fin (n + m))) :
      (V, W) ∈ E ↔ V.Nonempty ∧ Disjoint V W := by
    simp [E,
      theorem5_extended_finite_description_entropy_indices]
  have hGoodEq (L : List (Fin (n + m) → BitString)) :
      good q L ↔ ∀ V W : Finset (Fin (n + m)), V.Nonempty → Disjoint V W →
        combEnt L.toFinset V W ≤ combEnt A₀ V W := by
    constructor
    · intro h V W hV hdis
      have hp := (hMemE V W).mpr ⟨hV, hdis⟩
      have hh := h (V, W) hp
      rwa [hEntropy (V, W) hp] at hh
    · intro h p hp
      have hp' := (hMemE p.1 p.2).mp hp
      rw [hEntropy p hp]
      exact h p.1 p.2 hp'.1 hp'.2
  have hSetsEq : (sets q).toFinset.image List.toFinset =
      (theorem5_extended_special_union_candidates S N).powerset := by
    dsimp only [sets]
    rw [hN, hEnumSets, hS]
  have hAcceptedEq : (accepted q).toFinset.image List.toFinset =
      (theorem5_extended_special_union_candidates S N).powerset.filter (fun C =>
        ∀ V W : Finset (Fin (n + m)), V.Nonempty → Disjoint V W →
          combEnt C V W ≤ combEnt A₀ V W) := by
    ext C
    constructor
    · intro h
      obtain ⟨L, hL, rfl⟩ := Finset.mem_image.mp h
      have hL' : L ∈ sets q ∧ good q L := by simpa [accepted] using hL
      refine Finset.mem_filter.mpr ⟨?_, (hGoodEq L).mp hL'.2⟩
      rw [← hSetsEq]
      exact Finset.mem_image.mpr ⟨L, by simpa using hL'.1, rfl⟩
    · intro h
      obtain ⟨hC, hCorrect⟩ := Finset.mem_filter.mp h
      rw [← hSetsEq] at hC
      obtain ⟨L, hL, rfl⟩ := Finset.mem_image.mp hC
      refine Finset.mem_image.mpr ⟨L, ?_, rfl⟩
      have hGood' := (hGoodEq L).mpr hCorrect
      simpa [accepted] using And.intro (List.mem_toFinset.mp hL) hGood'
  have hCodesEq : (codes q).toFinset =
      ((accepted q).toFinset.image List.toFinset).image (fun C =>
        pairCode (tupleSetCode C)
          (tupleSetCode (theorem5_extended_special_union_strongProj S κ s C))) := by
    ext w
    simp only [codes, List.mem_toFinset, List.mem_map, Finset.mem_image]
    simp only [projected, hS, hκ, hs]
    constructor
    · rintro ⟨L, hL, rfl⟩
      exact ⟨L.toFinset, ⟨L, hL, rfl⟩, rfl⟩
    · rintro ⟨C, ⟨L, hL, rfl⟩, rfl⟩
      exact ⟨L, hL, rfl⟩
  have hDecodeFamily : f q = theorem5_extended_special_union_familyCode
      (theorem5_extended_special_union_family S N κ s A₀) := by
    change finsetListCode _ = finsetListCode _
    congr 1
    rw [hCodesEq, hAcceptedEq]
    simp only [theorem5_extended_special_union_family, Finset.image_image,
      Function.comp_def]
  have hRaw := hc q
  rw [hDecodeFamily] at hRaw
  have hOut := plainK_ne_top D hD
    (theorem5_extended_special_union_familyCode
      (theorem5_extended_special_union_family S N κ s A₀))
  have hIn := plainK_ne_top D hD q
  rw [← ENat.natCast_toNat hOut, ← ENat.natCast_toNat hIn] at hRaw
  exact_mod_cast hRaw

/-- the
self-delimiting code of the fixed-size list of numerical inputs has logarithmic complexity when
each entry is bounded linearly in `N`.  The entropy table is ordered by the finite list of
admissible coordinate pairs in
`theorem5_extended_finite_description_entropy_indices`.
-/
private theorem theorem5_extended_numeric_data
    (D : Map) (hD : isOptimalConditional D) (n m b : ℕ) :
    ∃ c : ℕ, ∀ (N κ s : ℕ) (A₀ : Finset (Fin (n + m) → BitString)),
      κ ≤ b * (N + 1) →
      s ≤ b * (N + 1) →
      (∀ V W : Finset (Fin (n + m)), V.Nonempty → Disjoint V W →
        combEnt A₀ V W ≤ b * (N + 1)) →
      natK D
        (theorem5_extended_finite_description_numeric_code
          N κ s A₀) ≤ logSlack c N := by
  obtain ⟨cLiteral, hLiteral⟩ := plainK_le_length D hD
  obtain ⟨cFold, hFold⟩ := logSlack_linear_bound 1 b b
  let E := theorem5_extended_finite_description_entropy_indices
    (n := n) (m := m)
  let q := 3 + E.card
  refine ⟨2 * q * (cFold + 1) + q + cLiteral, ?_⟩
  intro N κ s A₀ hκ hs hEnt
  let qBound := b * (N + 1)
  let M := max (Nat.bits N).length (Nat.bits qBound).length
  let dataStrings := ([N, κ, s].map Nat.bits) ++
    E.toList.map (fun p => Nat.bits (combEnt A₀ p.1 p.2))
  have hPairDataLength : dataStrings.length = q := by
    simp [dataStrings, q, E,
      theorem5_extended_finite_description_entropy_indices]
    omega
  have hNBits : (Nat.bits N).length ≤ M := by
    dsimp [M]
    exact Nat.le_max_left _ _
  have hBoundBits : (Nat.bits qBound).length ≤ logSlack (cFold + 1) N := by
    have hq : qBound = b * N + b := by
      dsimp [qBound]
      ring
    have hlinear := hFold N
    have hlinear' : logSlack 1 qBound ≤ logSlack cFold N := by
      rw [hq]
      exact hlinear
    have hbits' : (Nat.bits qBound).length ≤ logSlack cFold N := by
      unfold logSlack at hlinear'
      unfold logSlack
      omega
    exact hbits'.trans (logSlack_mono_left (by omega) N)
  have hM : M ≤ logSlack (cFold + 1) N := by
    dsimp [M]
    apply max_le
    · exact (show (Nat.bits N).length ≤ logSlack (cFold + 1) N from by
        unfold logSlack
        nlinarith [Nat.zero_le ((Nat.bits N).length), Nat.zero_le cFold])
    · exact hBoundBits
  have hEveryCode : ∀ w, w ∈ dataStrings → w.length ≤ M := by
    intro w hw
    rcases List.mem_append.mp hw with hfirst | htable
    · rcases List.mem_map.mp hfirst with ⟨k, hk, rfl⟩
      simp only [List.mem_cons, List.not_mem_nil] at hk
      rcases hk with rfl | rfl | (rfl | hFalse)
      · exact hNBits
      · exact (length_natBits_mono hκ).trans (by
          dsimp [M, qBound]
          exact Nat.le_max_right _ _)
      · exact (length_natBits_mono hs).trans (by
          dsimp [M, qBound]
          exact Nat.le_max_right _ _)
      · simp at hFalse
    · rcases List.mem_map.mp htable with ⟨p, hp, rfl⟩
      have hpE : p ∈ E := Finset.mem_toList.mp hp
      have hpvalid := (Finset.mem_filter.mp hpE).2
      have hent := hEnt p.1 p.2 hpvalid.1 hpvalid.2
      exact (length_natBits_mono hent).trans (by
        dsimp [M, qBound]
        exact Nat.le_max_right _ _)
  have hListLength : ∀ l : List BitString, (∀ w, w ∈ l → w.length ≤ M) →
      (listCode l).length ≤ l.length * (2 * M + 1) := by
    intro l
    induction l with
    | nil => simp
    | cons w l ih =>
      intro hbound
      have hw := hbound w (by simp)
      have htail := ih (fun u hu => hbound u (by simp [hu]))
      rw [length_listCode_cons, List.length_cons]
      nlinarith
  have hCodeLength :
      (theorem5_extended_finite_description_numeric_code
        N κ s A₀).length ≤ q * (2 * M + 1) := by
    calc
      _ = (listCode dataStrings).length := by
        simp [theorem5_extended_finite_description_numeric_code,
          dataStrings, E]
      _ ≤ dataStrings.length * (2 * M + 1) := hListLength dataStrings hEveryCode
      _ = q * (2 * M + 1) := by rw [hPairDataLength]
  have hSlackFold : logSlack (cFold + 1) N = (cFold + 1) * ((Nat.bits N).length + 1) := by
    unfold logSlack
    ring
  have hListLength' :
      (theorem5_extended_finite_description_numeric_code
        N κ s A₀).length ≤
        (2 * q * (cFold + 1) + q) * ((Nat.bits N).length + 1) := by
    calc
      _ ≤ q * (2 * M + 1) := hCodeLength
      _ ≤ q * (2 * logSlack (cFold + 1) N + 1) := by
        exact Nat.mul_le_mul_left q (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hM) 1)
      _ = q * (2 * ((cFold + 1) * ((Nat.bits N).length + 1)) + 1) := by
        rw [hSlackFold]
      _ ≤ (2 * q * (cFold + 1) + q) * ((Nat.bits N).length + 1) := by
        have hL : 1 ≤ (Nat.bits N).length + 1 := by omega
        have hqL : q ≤ q * ((Nat.bits N).length + 1) := by
          calc
            q = q * 1 := by simp
            _ ≤ q * ((Nat.bits N).length + 1) := Nat.mul_le_mul_left q hL
        calc
          _ = q * (2 * ((cFold + 1) * ((Nat.bits N).length + 1))) + q := by ring
          _ ≤ q * (2 * ((cFold + 1) * ((Nat.bits N).length + 1))) + q *
              ((Nat.bits N).length + 1) := by
                exact Nat.add_le_add_left hqL _
          _ = (2 * q * (cFold + 1) + q) * ((Nat.bits N).length + 1) := by ring
  have hLiteralNat :
      natK D (theorem5_extended_finite_description_numeric_code
        N κ s A₀) ≤
        (theorem5_extended_finite_description_numeric_code
          N κ s A₀).length + cLiteral := by
    have hne := plainK_ne_top D hD
      (theorem5_extended_finite_description_numeric_code
        N κ s A₀)
    have hraw := hLiteral
      (theorem5_extended_finite_description_numeric_code
        N κ s A₀)
    have hcast :
        ((natK D (theorem5_extended_finite_description_numeric_code
          N κ s A₀) : ℕ) : ℕ∞) ≤
          (((theorem5_extended_finite_description_numeric_code
            N κ s A₀).length + cLiteral : ℕ) : ℕ∞) := by
      calc
        _ = plainK D
            (theorem5_extended_finite_description_numeric_code
              N κ s A₀) := ENat.natCast_toNat hne
        _ ≤ (programLength
            (theorem5_extended_finite_description_numeric_code
              N κ s A₀) : ℕ∞) + cLiteral := hraw
        _ = _ := by simp [programLength]
    exact_mod_cast hcast
  have hL : 1 ≤ (Nat.bits N).length + 1 := by omega
  have hLitConst : cLiteral ≤ cLiteral * ((Nat.bits N).length + 1) := by
    simpa using Nat.mul_le_mul_left cLiteral hL
  have hsum : natK D
      (theorem5_extended_finite_description_numeric_code
        N κ s A₀) ≤
      (2 * q * (cFold + 1) + q + cLiteral) * ((Nat.bits N).length + 1) := by
    calc
      _ ≤ (theorem5_extended_finite_description_numeric_code
        N κ s A₀).length + cLiteral := hLiteralNat
      _ ≤ (2 * q * (cFold + 1) + q) * ((Nat.bits N).length + 1) + cLiteral :=
        Nat.add_le_add_right hListLength' cLiteral
      _ ≤ (2 * q * (cFold + 1) + q) * ((Nat.bits N).length + 1) +
          cLiteral * ((Nat.bits N).length + 1) := Nat.add_le_add_left hLitConst _
      _ = (2 * q * (cFold + 1) + q + cLiteral) * ((Nat.bits N).length + 1) := by ring
  convert hsum using 1; unfold logSlack; ring

/-- pairing two
strings whose
complexities are logarithmic in the same visible parameter still has logarithmic complexity. -/
private theorem theorem5_extended_pair_inputs
    (D : Map) (hD : isOptimalConditional D) (a b : ℕ) :
    ∃ c : ℕ, ∀ (N : ℕ) (x y : BitString),
      natK D x ≤ logSlack a N → natK D y ≤ logSlack b N →
      natK D (pairCode x y) ≤ logSlack c N := by
  obtain ⟨k, hk⟩ := plainK_pair_le_add_two_log D hD
  refine ⟨a + b + 2 * a + k, fun N x y hx hy => ?_⟩
  have hneX : plainK D x ≠ ⊤ := plainK_ne_top D hD x
  have hneY : plainK D y ≠ ⊤ := plainK_ne_top D hD y
  have hneXY : plainK D (pairCode x y) ≠ ⊤ :=
    plainK_ne_top D hD (pairCode x y)
  have hXcast : ((natK D x : ℕ) : ℕ∞) = plainK D x :=
    ENat.natCast_toNat hneX
  have hYcast : ((natK D y : ℕ) : ℕ∞) = plainK D y :=
    ENat.natCast_toNat hneY
  have hXYcast : ((natK D (pairCode x y) : ℕ) : ℕ∞) =
      plainK D (pairCode x y) := ENat.natCast_toNat hneXY
  have hpair := hk x y
  change plainK D (pairCode x y) ≤
    plainK D x + plainK D y + ((2 * Nat.log 2 (cVal D x) + k : ℕ) : ℕ∞) at hpair
  rw [show cVal D x = natK D x by rfl, ← hXcast, ← hYcast] at hpair
  have hNat : natK D (pairCode x y) ≤
      natK D x + natK D y + (2 * Nat.log 2 (natK D x) + k) := by
    have hsumCast :
        ((natK D x : ℕ∞) + natK D y + (2 * Nat.log 2 (natK D x) + k : ℕ∞)) =
          ((natK D x + natK D y + (2 * Nat.log 2 (natK D x) + k) : ℕ) : ℕ∞) := by
      push_cast
      rfl
    have hcast : ((natK D (pairCode x y) : ℕ) : ℕ∞) ≤
        ((natK D x + natK D y + (2 * Nat.log 2 (natK D x) + k) : ℕ) : ℕ∞) := by
      rw [hXYcast]
      calc
        plainK D (pairCode x y) ≤
            (natK D x : ℕ∞) + natK D y + (2 * Nat.log 2 (natK D x) + k : ℕ∞) := hpair
        _ = ((natK D x + natK D y + (2 * Nat.log 2 (natK D x) + k) : ℕ) : ℕ∞) :=
          hsumCast
    exact_mod_cast hcast
  have hX : natK D x ≤ a * ((Nat.bits N).length + 1) := by
    simpa [logSlack, Nat.mul_add] using hx
  have hY : natK D y ≤ b * ((Nat.bits N).length + 1) := by
    simpa [logSlack, Nat.mul_add] using hy
  have hLog : Nat.log 2 (natK D x) ≤ a * ((Nat.bits N).length + 1) := by
    rw [← Nat.log2_eq_log_two]
    exact (Nat.log2_le_self _).trans hX
  have hL : 1 ≤ (Nat.bits N).length + 1 := by omega
  have hSum : natK D (pairCode x y) ≤
      (a + b + 2 * a) * ((Nat.bits N).length + 1) + k := by
    nlinarith
  have hAbsorb : (a + b + 2 * a) * ((Nat.bits N).length + 1) + k ≤
      (a + b + 2 * a + k) * ((Nat.bits N).length + 1) := by
    nlinarith
  calc
    natK D (pairCode x y) ≤
        (a + b + 2 * a) * ((Nat.bits N).length + 1) + k := hSum
    _ ≤ (a + b + 2 * a + k) * ((Nat.bits N).length + 1) := hAbsorb
    _ = logSlack (a + b + 2 * a + k) N := by
      unfold logSlack
      ring

/-- The family of correct sets is computed by finite search from the code of `S`, its size
parameter,
the strong-projection threshold, and the finitely many entropy bounds of `A₀`.  If the numeric
inputs are at most linear in `N`, all their self-delimiting codes have total length `O(log N)`. -/
private theorem theorem5_extended_finite_description
    (D : Map) (hD : isOptimalConditional D) (n m a b : ℕ) :
    ∃ c : ℕ, ∀ (S : Finset (Fin n → BitString)) (N κ s : ℕ)
      (A₀ : Finset (Fin (n + m) → BitString)),
      natK D (tupleSetCode S) ≤ logSlack a N →
      κ ≤ b * (N + 1) →
      s ≤ b * (N + 1) →
      (∀ V W : Finset (Fin (n + m)), V.Nonempty → Disjoint V W →
        combEnt A₀ V W ≤ b * (N + 1)) →
      natK D (theorem5_extended_special_union_familyCode
        (theorem5_extended_special_union_family S N κ s A₀)) ≤ logSlack c N := by
  obtain ⟨cSearch, hSearch⟩ :=
    theorem5_extended_finite_search_description
      D hD n m
  obtain ⟨cNumbers, hNumbers⟩ :=
    theorem5_extended_numeric_data
      D hD n m b
  obtain ⟨cPair, hPair⟩ :=
    theorem5_extended_pair_inputs
      D hD a cNumbers
  refine ⟨cPair + cSearch, ?_⟩
  intro S N κ s A₀ hS hκ hs hEnt
  have hNum := hNumbers N κ s A₀ hκ hs hEnt
  have hPacked := hPair N (tupleSetCode S)
    (theorem5_extended_finite_description_numeric_code
      N κ s A₀) hS hNum
  calc
    natK D (theorem5_extended_special_union_familyCode
        (theorem5_extended_special_union_family S N κ s A₀)) ≤
        natK D (pairCode (tupleSetCode S)
          (theorem5_extended_finite_description_numeric_code
            N κ s A₀)) + cSearch := hSearch S N κ s A₀
    _ ≤ logSlack cPair N + cSearch := Nat.add_le_add_right hPacked cSearch
    _ ≤ logSlack (cPair + cSearch) N := logSlack_add_nat_le cPair cSearch N

/-- the hypotheses bound the code of `S` logarithmically and bound `κ` and every entropy of `A₀`
linearly in `N`. -/
private theorem theorem5_extended_data_bounds
    (D : Map) (hD : isOptimalConditional D) (n m a : ℕ) :
    ∃ b : ℕ, ∀ (x : Fin n → BitString) (z : BitString)
      (S : Finset (Fin n → BitString)),
      x ∈ S →
      natK D (tupleSetCode S) ≤ logSlack a (natK D (tupleCode x)) →
      S.card ≤ 2 ^ (natK D (tupleCode x) + logSlack a (natK D (tupleCode x))) →
      ∀ y y₀ : Fin m → BitString,
        (∀ i : Fin m, (y₀ i).length ≤ natK D (pairCode (tupleCode (Fin.append x y)) z)) →
        let N := natK D (pairCode (tupleCode (Fin.append x y)) z)
        let A₀ := theorem5_extended_special_union_levelSet D S N (Fin.append x y₀) z
        natK D (tupleSetCode S) ≤ logSlack b N ∧
        natCondK D (tupleCode y₀) (pairCode (tupleCode x) z) ≤ b * (N + 1) ∧
        (∀ V W : Finset (Fin (n + m)), V.Nonempty → Disjoint V W →
          combEnt A₀ V W ≤ b * (N + 1)) := by
  classical
  let extractX : BitString → BitString := fun w =>
    decodeFirst (theorem4_extended_chain_splitTuple n (decodeFirst w))
  have hExtractX : Computable extractX :=
    decodeFirst_computable.comp
      ((theorem4_extended_chain_splitTuple_computable n).comp decodeFirst_computable)
  obtain ⟨cMap, hMap⟩ := plainK_map_le D hD extractX hExtractX
  obtain ⟨cFold, hFold⟩ := logSlack_linear_bound a 1 cMap
  obtain ⟨cLit, hLit⟩ := plainK_le_length D hD
  obtain ⟨cCond, hCond⟩ := theorem5_extended_stochastic_model_condNat_bound D hD
  obtain ⟨cProfile, hProfile⟩ :=
    theorem5_extended_threshold_bound
      D hD n m
  let cKappa := 2 * m + cLit + cCond
  let cEntropy := cProfile + 1
  let b := max cFold (max cKappa cEntropy)
  refine ⟨b, ?_⟩
  intro x z S hx hS hScard y y₀ hy₀
  let N := natK D (pairCode (tupleCode (Fin.append x y)) z)
  let A₀ := theorem5_extended_special_union_levelSet D S N (Fin.append x y₀) z
  have hExtract : extractX (pairCode (tupleCode (Fin.append x y)) z) = tupleCode x := by
    dsimp [extractX]
    rw [decodeFirst_pairCode, theorem4_extended_chain_splitTuple_correct,
      decodeFirst_pairCode]
  have hMapRaw := hMap (pairCode (tupleCode (Fin.append x y)) z)
  rw [hExtract] at hMapRaw
  have hMapNat : natK D (tupleCode x) ≤ N + cMap := by
    rw [← ENat.natCast_toNat (plainK_ne_top D hD (tupleCode x)),
      ← ENat.natCast_toNat (plainK_ne_top D hD
        (pairCode (tupleCode (Fin.append x y)) z))] at hMapRaw
    exact_mod_cast hMapRaw
  have hCodeSlack : logSlack a (natK D (tupleCode x)) ≤ logSlack cFold N := by
    calc
      logSlack a (natK D (tupleCode x)) ≤ logSlack a (N + cMap) :=
        logSlack_mono_right a hMapNat
      _ ≤ logSlack cFold N := by simpa using hFold N
  have hSCode : natK D (tupleSetCode S) ≤ logSlack b N := by
    exact hS.trans (hCodeSlack.trans (logSlack_mono_left (by dsimp [b]; omega) N))
  have hListLength : ∀ l : List BitString,
      (∀ s ∈ l, s.length ≤ N) → (listCode l).length ≤ l.length * (2 * N + 1) := by
    intro l
    induction l with
    | nil => simp
    | cons s l ih =>
        intro hs
        have hsN := hs s (by simp)
        have hlN : ∀ t ∈ l, t.length ≤ N := fun t ht => hs t (by simp [ht])
        have ht := ih hlN
        rw [length_listCode_cons, List.length_cons]
        nlinarith
  have hYlength : (tupleCode y₀).length ≤ m * (2 * N + 1) := by
    simpa [tupleCode] using hListLength (List.ofFn y₀) (by
      intro s hs
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hs
      exact hy₀ i)
  have hYnat : natK D (tupleCode y₀) ≤ (tupleCode y₀).length + cLit := by
    have h := hLit (tupleCode y₀)
    exact ENat.toNat_le_of_le_natCast (by simpa [programLength] using h)
  have hKappa : natCondK D (tupleCode y₀) (pairCode (tupleCode x) z) ≤
      cKappa * (N + 1) := by
    have hCondK := hCond (tupleCode y₀) (pairCode (tupleCode x) z)
    have hLinear : m * (2 * N + 1) + cLit + cCond ≤ cKappa * (N + 1) := by
      dsimp [cKappa]
      nlinarith
    calc
      natCondK D (tupleCode y₀) (pairCode (tupleCode x) z)
          ≤ natK D (tupleCode y₀) + cCond := hCondK
      _ ≤ (tupleCode y₀).length + cLit + cCond := Nat.add_le_add_right hYnat cCond
      _ ≤ m * (2 * N + 1) + cLit + cCond := by omega
      _ ≤ cKappa * (N + 1) := hLinear
  have hProfileAll := hProfile x z y y₀ (by simpa [N] using hy₀)
  have hEntropy : ∀ V W : Finset (Fin (n + m)), V.Nonempty → Disjoint V W →
      combEnt A₀ V W ≤ cEntropy * (N + 1) := by
    intro V W hV hdis
    have hEnt := theorem5_extended_special_union_levelSet_combEnt D hD S N
      (Fin.append x y₀) z V W hV hdis
    have hProfileVW : subCondKRel D (Fin.append x y₀) z V W ≤ cProfile * (N + 1) := by
      simpa [N] using hProfileAll V W
    calc
      combEnt A₀ V W ≤ subCondKRel D (Fin.append x y₀) z V W + 1 := by
        simpa [A₀] using hEnt
      _ ≤ cProfile * (N + 1) + 1 := Nat.add_le_add_right hProfileVW 1
      _ ≤ cProfile * (N + 1) + (N + 1) := by omega
      _ = cEntropy * (N + 1) := by
        dsimp [cEntropy]
        rw [Nat.add_mul, one_mul]
  refine ⟨hSCode, ?_, ?_⟩
  · exact hKappa.trans (Nat.mul_le_mul_right (N + 1) (by dsimp [b]; omega))
  · intro V W hV hdis
    exact (hEntropy V W hV hdis).trans
      (Nat.mul_le_mul_right (N + 1) (by dsimp [b]; omega))

/-- The correct sets are listed from simple data.  Let `N = K(⟨x̄, ȳ⟩, z)`, let `ȳ°` (the
`y₀` of the
statement) be any `m`-tuple whose components have length at most `N`, `A₀ = levelSet D S N ⟨x̄, ȳ°⟩
z`,
`κ = K(ȳ° | x̄, z)` and `s = logSlack c₁ N` for a fixed constant `c₁`.  Then the family
`G = family S N κ s A₀` of the pairs `(C, B_C)` (correct sets and their strong projections) has
`K(code G) = O(log N)`.

Proof: `G` is computed, by brute force over all subsets of the candidate set `S × (B^{≤N})^m`,
from `list S`, `N`, `κ`, `c₁` and the finitely many numbers `ent_{V|W}(A₀)`.  Here
`K(list S) ≤ a (log K(x̄) + 1) = O(log N)` as `K(x̄) ≤ N + O(1)`; the numbers are all `O(N)`:
`ent_{V|W}(A₀) ≤ log |S| + m (N + 1) + 1` with `log |S| ≤ K(x̄) + a (log K(x̄) + 1)`, and
`κ ≤ K(ȳ°) + O(1) = O(N)`; so all the data take `O(log N)` bits in self-delimiting form. -/
private theorem theorem5_extended_family_code
    (D : Map) (hD : isOptimalConditional D) (n m a c₁ : ℕ) :
    ∃ c : ℕ, ∀ (x : Fin n → BitString) (z : BitString) (S : Finset (Fin n → BitString)),
      x ∈ S →
      natK D (tupleSetCode S) ≤ logSlack a (natK D (tupleCode x)) →
      S.card ≤ 2 ^ (natK D (tupleCode x) + logSlack a (natK D (tupleCode x))) →
      ∀ y y₀ : Fin m → BitString,
        (∀ i : Fin m, (y₀ i).length ≤ natK D (pairCode (tupleCode (Fin.append x y)) z)) →
        natK D (theorem5_extended_special_union_familyCode
          (theorem5_extended_special_union_family S
            (natK D (pairCode (tupleCode (Fin.append x y)) z))
            (natCondK D (tupleCode y₀) (pairCode (tupleCode x) z))
            (logSlack c₁ (natK D (pairCode (tupleCode (Fin.append x y)) z)))
            (theorem5_extended_special_union_levelSet D S
              (natK D (pairCode (tupleCode (Fin.append x y)) z)) (Fin.append x y₀) z))) ≤
          logSlack c (natK D (pairCode (tupleCode (Fin.append x y)) z)) := by
  obtain ⟨cData, hData⟩ :=
    theorem5_extended_data_bounds D hD n m a
  let b := max cData c₁
  obtain ⟨cCode, hCode⟩ :=
    theorem5_extended_finite_description
      D hD n m b b
  refine ⟨cCode, ?_⟩
  intro x z S hx hS hScard y y₀ hy₀
  let N := natK D (pairCode (tupleCode (Fin.append x y)) z)
  let A₀ := theorem5_extended_special_union_levelSet D S N (Fin.append x y₀) z
  have hBounds := hData x z S hx hS hScard y y₀ hy₀
  have hSCode : natK D (tupleSetCode S) ≤ logSlack b N :=
    hBounds.1.trans (logSlack_mono_left (by dsimp [b]; omega) N)
  have hKappa : natCondK D (tupleCode y₀) (pairCode (tupleCode x) z) ≤ b * (N + 1) :=
    hBounds.2.1.trans (Nat.mul_le_mul_right (N + 1) (by dsimp [b]; omega))
  have hThreshold : logSlack c₁ N ≤ b * (N + 1) := by
    unfold logSlack
    have hbits := length_natBits_le N
    calc
      c₁ * (Nat.bits N).length + c₁ ≤ b * (Nat.bits N).length + b := by
        apply Nat.add_le_add
        · exact Nat.mul_le_mul_right _ (by dsimp [b]; omega)
        · dsimp [b]
          omega
      _ ≤ b * N + b := by
        exact Nat.add_le_add_right (Nat.mul_le_mul_left b hbits) b
      _ = b * (N + 1) := by ring
  have hEntropy : ∀ V W : Finset (Fin (n + m)), V.Nonempty → Disjoint V W →
      combEnt A₀ V W ≤ b * (N + 1) := fun V W hV hdis =>
    (hBounds.2.2 V W hV hdis).trans
      (Nat.mul_le_mul_right (N + 1) (by dsimp [b]; omega))
  have hFamily := hCode S N
    (natCondK D (tupleCode y₀) (pairCode (tupleCode x) z)) (logSlack c₁ N) A₀
    hSCode hKappa hThreshold hEntropy
  simpa [N, A₀] using hFamily

/-- encode the
finite numerical profile, the oracle, the set code, and the size parameter in logarithmic
conditional advice. The empty profile coordinate stores the strong-projection threshold. -/
private theorem theorem5_extended_advice_data
    (D : Map) (hD : isOptimalConditional D) (n m a _c₁ : ℕ) :
    ∃ R : BitString → ℕ,
    ∃ P : BitString → Finset (Fin (n + m)) → Finset (Fin (n + m)) → ℕ,
      Computable R ∧ (∀ V W, Computable (fun p => P p V W)) ∧
      ∃ c : ℕ, ∀ (x : Fin n → BitString) (z : BitString)
        (S : Finset (Fin n → BitString)),
        x ∈ S →
        natK D (tupleSetCode S) ≤ logSlack a (natK D (tupleCode x)) →
        ∀ y y₀ : Fin m → BitString,
          (∀ i : Fin m, (y₀ i).length ≤
            natK D (pairCode (tupleCode (Fin.append x y)) z)) →
          ∃ p : BitString,
            R p = natK D (pairCode (tupleCode (Fin.append x y)) z) ∧
            P p ∅ ∅ = natCondK D (tupleCode y₀) (pairCode (tupleCode x) z) ∧
            (∀ V W : Finset (Fin (n + m)), V.Nonempty → Disjoint V W →
              P p V W = subCondKRel D (Fin.append x y₀) z V W) ∧
            natCondK D (pairCode (pairCode (tupleSetCode S) p) z) z ≤
              logSlack c (natK D (pairCode (tupleCode (Fin.append x y)) z)) := by
  classical
  obtain ⟨bProfile, hProfileBound⟩ :=
    theorem5_extended_threshold_bound
      D hD n m
  obtain ⟨cLit, hLit⟩ := plainK_le_length D hD
  obtain ⟨cCond, hCond⟩ :=
    theorem5_extended_stochastic_model_condNat_bound D hD
  let cKappa := 2 * m + cLit + cCond
  let b := max bProfile cKappa
  obtain ⟨R, P, hR, hP, cTable, hTable⟩ :=
    theorem5_extended_advice
      (n + m) b
  let firstTuple : BitString → BitString := fun w =>
    decodeFirst (theorem4_extended_chain_splitTuple n (decodeFirst w))
  have hFirstTuple : Computable firstTuple :=
    decodeFirst_computable.comp
      ((theorem4_extended_chain_splitTuple_computable n).comp decodeFirst_computable)
  obtain ⟨cMap, hMap⟩ := plainK_map_le D hD firstTuple hFirstTuple
  obtain ⟨cFold, hFold⟩ := logSlack_linear_bound a 1 cMap
  obtain ⟨cPair, hPair⟩ := plainK_pair_le_add_two_log D hD
  obtain ⟨cNest, hNest⟩ := condK_pair_pair_le_condK D hD
  have hCtxComp : Computable (fun w : BitString => pairCode [] w) :=
    pairCode_computable.comp (Computable.pair (Computable.const ([] : BitString)) Computable.id)
  obtain ⟨cCtx, hCtx⟩ := condK_cond_map_le D hD (fun w => pairCode [] w) hCtxComp
  let c := 3 * cFold + cTable + cLit + cPair + cNest + cCtx + 3
  refine ⟨R, P, hR, hP, c, ?_⟩
  intro x z S hxS hSCode y y₀ hy₀
  let N := natK D (pairCode (tupleCode (Fin.append x y)) z)
  let κ := natCondK D (tupleCode y₀) (pairCode (tupleCode x) z)
  have hFirstEq : firstTuple (pairCode (tupleCode (Fin.append x y)) z) = tupleCode x := by
    simp only [firstTuple, decodeFirst_pairCode,
      theorem4_extended_chain_splitTuple_correct]
  have hMapRaw := hMap (pairCode (tupleCode (Fin.append x y)) z)
  rw [hFirstEq, ← ENat.natCast_toNat (plainK_ne_top D hD (tupleCode x)),
    ← ENat.natCast_toNat (plainK_ne_top D hD
      (pairCode (tupleCode (Fin.append x y)) z))] at hMapRaw
  have hKx : natK D (tupleCode x) ≤ N + cMap := by exact_mod_cast hMapRaw
  have hSCode' : natK D (tupleSetCode S) ≤ logSlack cFold N := by
    calc
      natK D (tupleSetCode S) ≤ logSlack a (natK D (tupleCode x)) := hSCode
      _ ≤ logSlack a (N + cMap) := logSlack_mono_right a hKx
      _ ≤ logSlack cFold N := by simpa using hFold N
  have hListLength : ∀ l : List BitString,
      (∀ s ∈ l, s.length ≤ N) → (listCode l).length ≤ l.length * (2 * N + 1) := by
    intro l
    induction l with
    | nil => simp
    | cons s l ih =>
        intro hs
        have hsN := hs s (by simp)
        have hlN : ∀ t ∈ l, t.length ≤ N := fun t ht => hs t (by simp [ht])
        have ht := ih hlN
        rw [length_listCode_cons, List.length_cons]
        nlinarith
  have hYlength : (tupleCode y₀).length ≤ m * (2 * N + 1) := by
    simpa [tupleCode] using hListLength (List.ofFn y₀) (by
      intro s hs
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hs
      exact hy₀ i)
  have hYnat : natK D (tupleCode y₀) ≤ m * (2 * N + 1) + cLit := by
    have hLitY : plainK D (tupleCode y₀) ≤
        ((List.length (tupleCode y₀) + cLit : ℕ) : ℕ∞) := by
      have h := hLit (tupleCode y₀)
      simpa [programLength, Nat.cast_add] using h
    have h := ENat.toNat_le_of_le_natCast hLitY
    change (plainK D (tupleCode y₀)).toNat ≤ _
    omega
  have hKappaRaw := hCond (tupleCode y₀) (pairCode (tupleCode x) z)
  have hKappaLinear : κ ≤ cKappa * (N + 1) := by
    dsimp [κ, cKappa]
    calc
      natCondK D (tupleCode y₀) (pairCode (tupleCode x) z)
          ≤ natK D (tupleCode y₀) + cCond := hKappaRaw
      _ ≤ m * (2 * N + 1) + cLit + cCond := by omega
      _ ≤ (2 * m + cLit + cCond) * (N + 1) := by nlinarith
  let T : Finset (Fin (n + m)) → Finset (Fin (n + m)) → ℕ := fun V W =>
    if V.Nonempty ∧ Disjoint V W then subCondKRel D (Fin.append x y₀) z V W
    else if V = ∅ ∧ W = ∅ then κ else 0
  have hT : ∀ V W, T V W ≤ b * (N + 1) := by
    intro V W
    by_cases hvalid : V.Nonempty ∧ Disjoint V W
    · have h := hProfileBound x z y y₀ (by simpa [N] using hy₀) V W
      dsimp [T]
      rw [ite_eq_left hvalid]
      exact (h.trans (Nat.mul_le_mul_right (N + 1) (le_max_left _ _)))
    · by_cases hempty : V = ∅ ∧ W = ∅
      · dsimp [T]
        rw [ite_eq_right hvalid, ite_eq_left hempty]
        exact hKappaLinear.trans
          (Nat.mul_le_mul_right (N + 1) (le_max_right _ _))
      · dsimp [T]
        rw [ite_eq_right hvalid, ite_eq_right hempty]
        exact Nat.zero_le _
  obtain ⟨p, hpLen, hpN, hpTable⟩ := hTable N T hT
  have hpK : natK D p ≤ p.length + cLit := by
    exact ENat.toNat_le_of_le_natCast (by simpa [programLength] using hLit p)
  have hPairRaw := hPair (tupleSetCode S) p
  rw [Kolmogorov.cPair,
    ← ENat.natCast_toNat (plainK_ne_top D hD (pairCode (tupleSetCode S) p)),
    ← ENat.natCast_toNat (plainK_ne_top D hD (tupleSetCode S)),
    ← ENat.natCast_toNat (plainK_ne_top D hD p)] at hPairRaw
  have hPairNat : natK D (pairCode (tupleSetCode S) p) ≤
      natK D (tupleSetCode S) + natK D p +
        (2 * Nat.log 2 (natK D (tupleSetCode S)) + cPair) := by
    exact_mod_cast hPairRaw
  have hLogS : Nat.log 2 (natK D (tupleSetCode S)) ≤ natK D (tupleSetCode S) :=
    Nat.log_le_self 2 _
  have hpLen' : p.length ≤ logSlack cTable N := by simpa [N] using hpLen
  have hPairBound : natK D (pairCode (tupleSetCode S) p) ≤
      3 * logSlack cFold N + logSlack cTable N + cLit + cPair := by
    calc
      natK D (pairCode (tupleSetCode S) p) ≤
          natK D (tupleSetCode S) + natK D p +
            (2 * Nat.log 2 (natK D (tupleSetCode S)) + cPair) := hPairNat
      _ ≤ 3 * natK D (tupleSetCode S) + p.length + cLit + cPair := by omega
      _ ≤ 3 * logSlack cFold N + logSlack cTable N + cLit + cPair := by
        nlinarith [Nat.mul_le_mul_left 3 hSCode', hpLen']
  have hNest' := hNest (pairCode (tupleSetCode S) p) [] z
  have hCtx' := hCtx (pairCode (pairCode (tupleSetCode S) p) z) z
  have hCondAdvice : condK D (pairCode (pairCode (tupleSetCode S) p) z) z ≤
      ((natK D (pairCode (tupleSetCode S) p) + cNest + cCtx : ℕ) : ℕ∞) := by
    calc
      condK D (pairCode (pairCode (tupleSetCode S) p) z) z ≤
          condK D (pairCode (pairCode (tupleSetCode S) p) z) (pairCode [] z) + cCtx := hCtx'
      _ ≤ condK D (pairCode (tupleSetCode S) p) [] + cNest + cCtx := by
          exact add_le_add hNest' (le_rfl : (cCtx : ℕ∞) ≤ cCtx)
      _ = (natK D (pairCode (tupleSetCode S) p) + cNest + cCtx : ℕ) := by
          have hPlain : condK D (pairCode (tupleSetCode S) p) [] =
              plainK D (pairCode (tupleSetCode S) p) := rfl
          rw [hPlain]
          rw [← ENat.natCast_toNat (plainK_ne_top D hD (pairCode (tupleSetCode S) p))]
          push_cast
          rfl
  have hCondNat := ENat.toNat_le_of_le_natCast hCondAdvice
  have hSlackBound :
      3 * logSlack cFold N + logSlack cTable N + cLit + cPair + cNest + cCtx ≤
        logSlack c N := by
    simp only [logSlack]
    dsimp [c]
    ring_nf
    have hbits : 1 ≤ (Nat.bits N).length + 1 := by omega
    nlinarith
  refine ⟨p, ?_, ?_, ?_, ?_⟩
  · simpa [N] using hpN
  · have hEmpty := hpTable ∅ ∅
    simpa [T, κ] using hEmpty
  · intro V W hV hdis
    have h := hpTable V W
    simpa [T, hV, hdis] using h
  · change natCondK D (pairCode (pairCode (tupleSetCode S) p) z) z ≤ logSlack c N
    calc
      natCondK D (pairCode (pairCode (tupleSetCode S) p) z) z ≤
          natK D (pairCode (tupleSetCode S) p) + cNest + cCtx := hCondNat
      _ ≤ 3 * logSlack cFold N + logSlack cTable N + cLit + cPair + cNest + cCtx := by
        omega
      _ ≤ logSlack c N := hSlackBound

/-- the positive cardinality and logarithmic threshold tests on a computable stage list are
semidecidable uniformly in computable parameters. Deduplication counts distinct witnesses. -/
private theorem theorem5_extended_threshold_re
    {α : Type*} [Primcodable α]
    (E : α → ℕ → List BitString)
    (hE : Computable (fun q : α × ℕ => E q.1 q.2))
    (κ s : α → ℕ) (hκ : Computable κ) (hs : Computable s) :
    IsRE (fun a => ∃ t, 0 < (E a t).dedup.length ∧
      κ a ≤ Nat.log2 (E a t).dedup.length + s a) := by
  have hCard : Computable (fun q : α × ℕ => (E q.1 q.2).dedup.length) :=
    Computable.list_length.comp (dedup_primrec.to_comp.comp hE)
  have hPositive : Computable (fun q : α × ℕ => decide (0 < (E q.1 q.2).dedup.length)) :=
    Primrec.nat_lt.decide.to_comp.comp (Computable.const 0) hCard
  have hBound : Computable (fun q : α × ℕ =>
      decide (κ q.1 ≤ Nat.log2 (E q.1 q.2).dedup.length + s q.1)) :=
    Primrec.nat_le.decide.to_comp.comp (hκ.comp Computable.fst)
      (Primrec.nat_add.to_comp.comp (NatLog.nat_log2_primrec.to_comp.comp hCard)
        (hs.comp Computable.fst))
  have hTest : IsRE (fun q : α × ℕ => 0 < (E q.1 q.2).dedup.length ∧
      κ q.1 ≤ Nat.log2 (E q.1 q.2).dedup.length + s q.1) := by
    exact (isRE_of_computable_bool _ _ (by simp) hPositive).and
      (isRE_of_computable_bool _ _ (by simp) hBound)
  exact IsRE.exists_encodable hTest

/-- an increasing enumeration of a finite set crosses a positive logarithmic cardinality threshold
exactly when the final set does. Every finite set of outputs occurs together at some stage. -/
private theorem theorem5_extended_finite_threshold
    (E : ℕ → List BitString) (hmono : ∀ t, E t <+: E (t + 1))
    (Q : Finset BitString) (hQ : ∀ w, w ∈ Q ↔ ∃ t, w ∈ E t) (κ s : ℕ) :
    (Q.Nonempty ∧ κ ≤ Nat.log2 Q.card + s) ↔
      ∃ t, 0 < (E t).dedup.length ∧ κ ≤ Nat.log2 (E t).dedup.length + s := by
  classical
  have hMono : Monotone (fun t => (E t).toFinset) := by
    apply monotone_nat_of_le_succ
    intro t w hw
    exact List.mem_toFinset.mpr ((hmono t).subset (List.mem_toFinset.mp hw))
  have hSub : ∀ t, (E t).toFinset ⊆ Q := by
    intro t w hw
    exact (hQ w).mpr ⟨t, List.mem_toFinset.mp hw⟩
  have hCover : ∀ A : Finset BitString, A ⊆ Q → ∃ t, A ⊆ (E t).toFinset := by
    intro A
    induction A using Finset.induction_on with
    | empty => exact fun _ => ⟨0, by simp⟩
    | @insert a A ha ih =>
      intro hAQ
      obtain ⟨t, ht⟩ := ih (fun w hw => hAQ (Finset.mem_insert_of_mem hw))
      obtain ⟨r, hr⟩ := (hQ a).mp (hAQ (Finset.mem_insert_self a A))
      refine ⟨max r t, ?_⟩
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact hMono (le_max_left r t) (List.mem_toFinset.mpr hr)
      · exact hMono (le_max_right r t) (ht hw)
  constructor
  · rintro ⟨hne, hbound⟩
    obtain ⟨t, ht⟩ := hCover Q (by rfl)
    have hEq : (E t).toFinset = Q := Finset.Subset.antisymm (hSub t) ht
    have hc : (E t).dedup.length = Q.card := by
      rw [← List.card_toFinset, hEq]
    exact ⟨t, by simpa [hc] using Finset.card_pos.mpr hne, by simpa [hc] using hbound⟩
  · rintro ⟨t, hpos, hbound⟩
    have hc : (E t).dedup.length ≤ Q.card := by
      rw [← List.card_toFinset]
      exact Finset.card_le_card (hSub t)
    refine ⟨Finset.card_pos.mp (lt_of_lt_of_le hpos hc), ?_⟩
    have hlog : Nat.log2 (E t).dedup.length ≤ Nat.log2 Q.card := by
      simp only [Nat.log2_eq_log_two]
      exact Nat.log_mono_right hc
    omega

/-- from a code
for the finite parameters and the profile thresholds, enumerate the level set and then emit each
tuple in its strong projection once it has enough distinct witnesses in its section. -/
private theorem theorem5_extended_uniform_enumeration
    (D : Map) (hD : isOptimalConditional D) (n m c₁ : ℕ)
    (R : BitString → ℕ) (hR : Computable R)
    (P : BitString → Finset (Fin (n + m)) → Finset (Fin (n + m)) → ℕ)
    (hP : ∀ V W, Computable (fun p => P p V W)) :
    ∃ F : BitString → BitString → Set BitString,
      IsRE (fun q : (BitString × BitString) × BitString =>
        q.2 ∈ F q.1.1 q.1.2) ∧
      ∀ (S : Finset (Fin n → BitString)) (p z : BitString)
        (B : Finset (Fin n → BitString)),
        F (pairCode (pairCode (tupleSetCode S) p) z) (tupleSetCode B) =
          ↑((theorem5_extended_special_union_strongProj S (P p ∅ ∅)
              (logSlack c₁ (R p))
              ((theorem5_extended_special_union_candidates S (R p)).filter fun u =>
                ∀ V W : Finset (Fin (n + m)), V.Nonempty → Disjoint V W →
                  subCondKRel D u z V W ≤ P p V W) \ B).image tupleCode) := by
  classical
  obtain ⟨E, hE, hmono, hSound, hComplete⟩ :=
    theorem5_extended_staged_enumeration
      m _ (theorem5_extended_semidecidable
        D hD n m R hR P hP)
  let α := (BitString × BitString) × BitString
  let param : BitString → BitString := fun t => decodeSecond (decodeFirst t)
  let ctx : α → BitString × BitString := fun q =>
    (param q.1.1, pairCode q.2 (decodeSecond q.1.1))
  let enum : α → ℕ → List BitString := fun q r => E (ctx q) r
  have hInput : Computable (fun q : α => q.1.1) :=
    (Computable.fst : Computable (fun q : BitString × BitString => q.1)).comp
      (Computable.fst : Computable (fun q : α => q.1))
  have hParam : Computable (fun q : α => param q.1.1) := by
    have h := decodeSecond_computable.comp (decodeFirst_computable.comp hInput)
    exact h.of_eq (fun q => rfl)
  have hZ : Computable (fun q : α => decodeSecond q.1.1) :=
    decodeSecond_computable.comp hInput
  have hPair : Computable (fun q : α => pairCode q.2 (decodeSecond q.1.1)) := by
    have h := pairCode_computable.comp
      ((Computable.snd : Computable (fun q : α => q.2)).pair hZ)
    exact h.of_eq (fun q => rfl)
  have hCtx : Computable ctx := by
    have h := hParam.pair hPair
    exact h.of_eq (fun q => rfl)
  have hEnumInput : Computable (fun q : α × ℕ => (ctx q.1, q.2)) := by
    have h := (hCtx.comp (Computable.fst : Computable (fun q : α × ℕ => q.1))).pair
      (Computable.snd : Computable (fun q : α × ℕ => q.2))
    exact h.of_eq (fun q => rfl)
  have hEnum : Computable (fun q : α × ℕ => enum q.1 q.2) := by
    have h := hE.comp hEnumInput
    exact h.of_eq (fun q => rfl)
  have hSlack : Computable (fun r : ℕ => logSlack c₁ r) := by
    unfold logSlack
    exact (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const c₁)
        (Primrec.list_length.comp primrec_natBits)) (Primrec.const c₁)).to_comp
  have hThreshold : IsRE (fun q : α => ∃ r,
      0 < (enum q r).dedup.length ∧
      P (param q.1.1) ∅ ∅ ≤ Nat.log2 (enum q r).dedup.length +
        logSlack c₁ (R (param q.1.1))) :=
    theorem5_extended_threshold_re
      enum hEnum _ _ ((hP ∅ ∅).comp hParam) (hSlack.comp (hR.comp hParam))
  have hInS : IsRE (fun q : α =>
      q.2 ∈ decodeListCode (decodeFirst (decodeFirst q.1.1))) := by
    refine isRE_of_computable_bool _
      (fun q => decide (q.2 ∈ decodeListCode (decodeFirst (decodeFirst q.1.1)))) (by simp) ?_
    exact bitString_mem_primrec.to_comp.comp Computable.snd
      (decodeListCode_computable.comp (decodeFirst_computable.comp
        (decodeFirst_computable.comp (Computable.fst.comp Computable.fst))))
  have hNotB : IsRE (fun q : α => q.2 ∉ decodeListCode q.1.2) := by
    have hm : Computable (fun q : α => decide (q.2 ∈ decodeListCode q.1.2)) :=
      bitString_mem_primrec.to_comp.comp Computable.snd
        (decodeListCode_computable.comp (Computable.snd.comp Computable.fst))
    refine isRE_of_computable_bool _ (fun q => !(decide (q.2 ∈ decodeListCode q.1.2)))
      (by simp) (Primrec.not.to_comp.comp hm)
  let F : BitString → BitString → Set BitString := fun t b =>
    {w | w ∈ decodeListCode (decodeFirst (decodeFirst t)) ∧
      w ∉ decodeListCode b ∧ ∃ r,
        0 < (E (param t, pairCode w (decodeSecond t)) r).dedup.length ∧
        P (param t) ∅ ∅ ≤
          Nat.log2 (E (param t, pairCode w (decodeSecond t)) r).dedup.length +
            logSlack c₁ (R (param t))}
  refine ⟨F, hInS.and (hNotB.and hThreshold), ?_⟩
  intro S p z B
  let A := (theorem5_extended_special_union_candidates S (R p)).filter fun u =>
    ∀ V W : Finset (Fin (n + m)), V.Nonempty → Disjoint V W →
      subCondKRel D u z V W ≤ P p V W
  let Q := fun x : Fin n → BitString => theorem5_extended_special_union_section A x
  have hTupleInj : Function.Injective (tupleCode : (Fin m → BitString) → BitString) := by
    intro a b hab
    apply List.ofFn_injective
    exact Kolmogorov.listCode_injective hab
  have hSection (x : Fin n → BitString) (hx : x ∈ S) (a : Fin m → BitString) :
      a ∈ Q x ↔ (∀ i, (a i).length ≤ R p) ∧
        ∀ V W : Finset (Fin (n + m)), V.Nonempty → Disjoint V W →
          subCondKRel D (Fin.append x a) z V W ≤ P p V W := by
    change a ∈ theorem5_extended_special_union_section A x ↔ _
    rw [theorem5_extended_special_union_mem_section]
    change Fin.append x a ∈ (theorem5_extended_special_union_candidates S (R p)).filter _ ↔ _
    rw [Finset.mem_filter]
    constructor
    · rintro ⟨hc, hp⟩
      exact ⟨fun i => by simpa using
        theorem5_extended_special_union_length_of_mem_candidates hc i, hp⟩
    · rintro ⟨hl, hp⟩
      exact ⟨theorem5_extended_special_union_append_mem_candidates hx hl, hp⟩
  have hEnumQ (x : Fin n → BitString) (hx : x ∈ S) (w : BitString) :
      w ∈ (Q x).image tupleCode ↔ ∃ r, w ∈ E (p, pairCode (tupleCode x) z) r := by
    have hDecode : (fun i : Fin n =>
        (decodeListCode (tupleCode x)).getD i.val []) = x := by
      funext i
      simp [tupleCode]
    constructor
    · intro hw
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hw
      apply hComplete (p, pairCode (tupleCode x) z) a
      simpa only [decodeFirst_pairCode, decodeSecond_pairCode, hDecode] using
        (hSection x hx a).mp ha
    · rintro ⟨r, hr⟩
      obtain ⟨a, ha, hcode⟩ := hSound (p, pairCode (tupleCode x) z) r w hr
      refine Finset.mem_image.mpr ⟨a, (hSection x hx a).mpr ?_, hcode⟩
      simpa only [decodeFirst_pairCode, decodeSecond_pairCode, hDecode] using ha
  have hThresholdQ (x : Fin n → BitString) (hx : x ∈ S) :
      ((Q x).Nonempty ∧ P p ∅ ∅ ≤ Nat.log2 (Q x).card + logSlack c₁ (R p)) ↔
        ∃ r, 0 < (E (p, pairCode (tupleCode x) z) r).dedup.length ∧
          P p ∅ ∅ ≤ Nat.log2 (E (p, pairCode (tupleCode x) z) r).dedup.length +
            logSlack c₁ (R p) := by
    have hc : ((Q x).image tupleCode).card = (Q x).card :=
      Finset.card_image_iff.mpr (fun a _ b _ hab => hTupleInj hab)
    simpa only [Finset.image_nonempty, hc] using
      (theorem5_extended_finite_threshold
        (E (p, pairCode (tupleCode x) z)) (hmono _) ((Q x).image tupleCode)
        (hEnumQ x hx) (P p ∅ ∅) (logSlack c₁ (R p)))
  have hCodeMem (C : Finset (Fin n → BitString)) (w : BitString) :
      w ∈ decodeListCode (tupleSetCode C) ↔ w ∈ C.image tupleCode := by
    simp [tupleSetCode, finsetListCode]
  have hTupleInjN : Function.Injective (tupleCode : (Fin n → BitString) → BitString) := by
    intro a b hab
    apply List.ofFn_injective
    exact Kolmogorov.listCode_injective hab
  apply Set.ext
  intro w
  simp only [F, Set.mem_ofPred_eq, param, decodeFirst_pairCode, decodeSecond_pairCode,
    hCodeMem, Finset.mem_coe]
  constructor
  · rintro ⟨hwS, hwB, he⟩
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hwS
    have hxQ := (hThresholdQ x hx).mpr he
    refine Finset.mem_image.mpr ⟨x, Finset.mem_sdiff.mpr ⟨?_, ?_⟩, rfl⟩
    · exact Finset.mem_filter.mpr ⟨hx, hxQ⟩
    · intro hxB
      exact hwB (Finset.mem_image.mpr ⟨x, hxB, rfl⟩)
  · intro hw
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨hxProj, hxB⟩ := Finset.mem_sdiff.mp hx
    obtain ⟨hxS, hxQ⟩ := Finset.mem_filter.mp hxProj
    refine ⟨Finset.mem_image.mpr ⟨x, hxS, rfl⟩, ?_, (hThresholdQ x hxS).mp hxQ⟩
    intro hwB
    obtain ⟨y, hyB, hxy⟩ := Finset.mem_image.mp hwB
    exact hxB (hTupleInjN hxy ▸ hyB)

/-- package the data determining the level
set in logarithmic advice and give a uniform enumeration of the strong projection with an
arbitrary finite set removed.  The second parameter of the enumerated family is the code of that
finite set. -/
private theorem theorem5_extended_advice_enumeration
    (D : Map) (hD : isOptimalConditional D) (n m a c₁ : ℕ) :
    ∃ c : ℕ, ∃ F : BitString → BitString → Set BitString,
      IsRE (fun q : (BitString × BitString) × BitString =>
        q.2 ∈ F q.1.1 q.1.2) ∧
      ∀ (x : Fin n → BitString) (z : BitString) (S : Finset (Fin n → BitString)),
      x ∈ S →
      natK D (tupleSetCode S) ≤ logSlack a (natK D (tupleCode x)) →
      ∀ y y₀ : Fin m → BitString,
        (∀ i : Fin m, (y₀ i).length ≤
          natK D (pairCode (tupleCode (Fin.append x y)) z)) →
        ∃ t : BitString,
          natCondK D t z ≤ logSlack c
            (natK D (pairCode (tupleCode (Fin.append x y)) z)) ∧
          ∀ B : Finset (Fin n → BitString),
            F t (tupleSetCode B) =
                ↑((theorem5_extended_special_union_strongProj S
                    (natCondK D (tupleCode y₀) (pairCode (tupleCode x) z))
                    (logSlack c₁
                      (natK D (pairCode (tupleCode (Fin.append x y)) z)))
                    (theorem5_extended_special_union_levelSet D S
                      (natK D (pairCode (tupleCode (Fin.append x y)) z))
                      (Fin.append x y₀) z) \ B).image tupleCode) ∧
              (F t (tupleSetCode B)).ncard =
                (theorem5_extended_special_union_strongProj S
                  (natCondK D (tupleCode y₀) (pairCode (tupleCode x) z))
                  (logSlack c₁
                    (natK D (pairCode (tupleCode (Fin.append x y)) z)))
                  (theorem5_extended_special_union_levelSet D S
                    (natK D (pairCode (tupleCode (Fin.append x y)) z))
                    (Fin.append x y₀) z) \ B).card := by
  classical
  obtain ⟨R, P, hR, hP, cAdvice, hAdvice⟩ :=
    theorem5_extended_advice_data
      D hD n m a c₁
  obtain ⟨F, hF, hEnum⟩ :=
    theorem5_extended_uniform_enumeration
      D hD n m c₁ R hR P hP
  refine ⟨cAdvice, F, hF, ?_⟩
  intro x z S hxS hSCode y y₀ hy₀
  let N := natK D (pairCode (tupleCode (Fin.append x y)) z)
  let κ := natCondK D (tupleCode y₀) (pairCode (tupleCode x) z)
  obtain ⟨p, hRp, hPκ, hProfile, hTBound⟩ :=
    hAdvice x z S hxS hSCode y y₀ (by simpa [N] using hy₀)
  refine ⟨pairCode (pairCode (tupleSetCode S) p) z, ?_, ?_⟩
  · simpa [N] using hTBound
  · intro B
    let A := theorem5_extended_special_union_strongProj S κ (logSlack c₁ N)
      (theorem5_extended_special_union_levelSet D S N (Fin.append x y₀) z) \ B
    have hLevel : theorem5_extended_special_union_levelSet D S N
        (Fin.append x y₀) z =
        (theorem5_extended_special_union_candidates S N).filter fun u =>
          ∀ V W : Finset (Fin (n + m)), V.Nonempty → Disjoint V W →
            subCondKRel D u z V W ≤ P p V W := by
      apply Finset.ext
      intro u
      simp only [theorem5_extended_special_union_levelSet, Finset.mem_filter]
      constructor
      · rintro ⟨hu, hp⟩
        refine ⟨hu, ?_⟩
        intro V W hV hdis
        rw [hProfile V W hV hdis]
        exact hp V W hV hdis
      · rintro ⟨hu, hp⟩
        refine ⟨hu, ?_⟩
        intro V W hV hdis
        rw [← hProfile V W hV hdis]
        exact hp V W hV hdis
    have hEq := hEnum S p z B
    have hFamily : F (pairCode (pairCode (tupleSetCode S) p) z) (tupleSetCode B) =
        ↑(A.image tupleCode) := by
      simpa [A, hRp, hPκ, hLevel] using hEq
    have hTupleInj : Function.Injective (tupleCode : (Fin n → BitString) → BitString) := by
      intro u v huv
      apply List.ofFn_injective
      exact Kolmogorov.listCode_injective huv
    have hImageCard : (A.image tupleCode).card = A.card :=
      Finset.card_image_iff.mpr (by
        intro u hu v hv huv
        exact hTupleInj huv)
    refine ⟨hFamily, ?_⟩
    rw [hFamily, Set.ncard_coe_finset]
    exact hImageCard

/-- construct a
computable staged enumeration of each fiber from its recursively enumerable membership relation. -/
private theorem theorem5_extended_index_description_staged_enumeration
    (F : BitString → BitString → Set BitString)
    (hF : IsRE (fun q : (BitString × BitString) × BitString =>
      q.2 ∈ F q.1.1 q.1.2)) :
    ∃ E : (BitString × BitString) → ℕ → List BitString,
      Computable (fun q : (BitString × BitString) × ℕ => E q.1 q.2) ∧
      (∀ q s, E q s <+: E q (s + 1)) ∧
      (∀ t b s w, w ∈ E (t, b) s → w ∈ F t b) ∧
      (∀ t b w, w ∈ F t b → ∃ s, w ∈ E (t, b) s) := by
  classical
  obtain ⟨chk, hchk, -, hiff⟩ := hF.exists_stageApprox
  let cand : ℕ → BitString := fun i =>
    (@Encodable.decode BitString (Primcodable.toEncodable (α := BitString)) i).getD []
  have hcand : Computable cand :=
    Computable.option_getD Computable.decode (Computable.const [])
  let check : (BitString × BitString) → ℕ → Bool := fun q i =>
    chk (q, cand i.unpair.1) i.unpair.2
  have hcheck : Computable₂ check :=
    hchk.comp (Computable.fst.pair
      (hcand.comp (Computable.fst.comp (Computable.unpair.comp Computable.snd))))
      (Computable.snd.comp (Computable.unpair.comp Computable.snd))
  let E : (BitString × BitString) → ℕ → List BitString := fun q s =>
    Nat.rec [] (fun i acc =>
      if check q i then acc ++ [cand i.unpair.1] else acc) s
  have hstep : Computable₂ (fun (q : (BitString × BitString) × ℕ)
      (r : ℕ × List BitString) =>
      if check q.1 r.1 then r.2 ++ [cand r.1.unpair.1] else r.2) := by
    have hc : Computable (fun z : ((BitString × BitString) × ℕ) × (ℕ × List BitString) =>
        check z.1.1 z.2.1) := hcheck.comp (Computable.fst.comp Computable.fst)
      (Computable.fst.comp Computable.snd)
    have hv : Computable (fun z : ((BitString × BitString) × ℕ) × (ℕ × List BitString) =>
        cand z.2.1.unpair.1) :=
      hcand.comp (Computable.fst.comp (Computable.unpair.comp
        (Computable.fst.comp Computable.snd)))
    have ha : Computable (fun z : ((BitString × BitString) × ℕ) × (ℕ × List BitString) =>
        z.2.2 ++ [cand z.2.1.unpair.1]) :=
      Computable.list_append.comp (Computable.snd.comp Computable.snd)
        (Computable.list_cons.comp hv (Computable.const []))
    exact (Computable.cond hc ha (Computable.snd.comp Computable.snd)).of_eq
      (fun z => by cases hh : check z.1.1 z.2.1 <;> simp [hh])
  have hE : Computable (fun q : (BitString × BitString) × ℕ => E q.1 q.2) :=
    (Computable.nat_rec Computable.snd (Computable.const []) hstep).of_eq (fun _ => rfl)
  have hmono : ∀ q s, E q s <+: E q (s + 1) := by
    intro q s
    change E q s <+: if check q s then E q s ++ [_] else E q s
    by_cases hc : check q s = true
    · simp [hc, List.prefix_append]
    · simp [hc]
  have hSound : ∀ q s w, w ∈ E q s → w ∈ F q.1 q.2 := by
    intro q s
    induction s with
    | zero => simp [E]
    | succ s ih =>
      intro w hw
      change w ∈ (if check q s then E q s ++ [cand s.unpair.1] else E q s) at hw
      by_cases hc : check q s = true
      · simp only [ite_eq_left hc, List.mem_append, List.mem_singleton] at hw
        rcases hw with hw | rfl
        · exact ih _ hw
        · exact (hiff (q, cand s.unpair.1)).mpr ⟨s.unpair.2, hc⟩
      · exact ih _ (by simpa [hc] using hw)
  have hComplete : ∀ q w, w ∈ F q.1 q.2 → ∃ s, w ∈ E q s := by
    intro q w hw
    obtain ⟨s, hs⟩ := (hiff (q, w)).mp hw
    let i := Nat.pair (Encodable.encode w) s
    have hi : check q i = true := by simpa [check, i, cand] using hs
    refine ⟨i + 1, ?_⟩
    change w ∈ (if check q i then E q i ++ [cand i.unpair.1] else E q i)
    simp [hi, cand, i]
  exact ⟨E, hE, hmono,
    (by intro t b s w hw; exact hSound (t, b) s w hw),
    (by intro t b w hw; exact hComplete (t, b) w hw)⟩

/-- parse the self-delimited programs, run them, and dispatch to the staged-enumeration decoder. -/
private theorem theorem5_extended_parameter_decoder
    (D : Map) (hD : isOptimalConditional D)
    (E : (BitString × BitString) → ℕ → List BitString)
    (hE : Computable (fun q : (BitString × BitString) × ℕ => E q.1 q.2)) :
    ∃ g : BitString → BitString → Part BitString,
      Partrec (fun q : BitString × BitString => g q.2 q.1) ∧
      ∀ (p q z t b : BitString) (i : ℕ) (w : BitString),
        produces D p z t → produces D q [] b →
        (w ∈ g z (pairCode (Nat.bits p.length)
            (p ++ pairCode (Nat.bits q.length) (q ++ Nat.bits i))) ↔
          w ∈ StagedEnumeration.condFFixedLength
            (fun a s => E (decodeFirst a, decodeSecond a) s)
            (pairCode t b) (Nat.bits i)) := by
  let pLen : BitString → ℕ := fun c => bitsToNat (decodeFirst c)
  let pPart : BitString → BitString := fun c => (decodeSecond c).take (pLen c)
  let tail : BitString → BitString := fun c => (decodeSecond c).drop (pLen c)
  let qLen : BitString → ℕ := fun c => bitsToNat (decodeFirst (tail c))
  let qTail : BitString → BitString := fun c => decodeSecond (tail c)
  let qPart : BitString → BitString := fun c => (qTail c).take (qLen c)
  let indexBits : BitString → BitString := fun c => (qTail c).drop (qLen c)
  have hpLen : Primrec pLen :=
    bitsToNat_primrec.comp CodedFiniteDistribution.decodeFirst_primrec
  have hpTail : Primrec decodeSecond := CodedFiniteDistribution.decodeSecond_primrec
  have hpPart : Primrec pPart := Primrec.list_take.comp hpLen hpTail
  have htail : Primrec tail := Primrec.list_drop.comp hpLen hpTail
  have hqLen : Primrec qLen :=
    bitsToNat_primrec.comp (CodedFiniteDistribution.decodeFirst_primrec.comp htail)
  have hqTail : Primrec qTail := CodedFiniteDistribution.decodeSecond_primrec.comp htail
  have hqPart : Primrec qPart := Primrec.list_take.comp hqLen hqTail
  have hindexBits : Primrec indexBits := Primrec.list_drop.comp hqLen hqTail
  have hpPartC : Computable pPart := hpPart.to_comp
  have hqPartC : Computable qPart := hqPart.to_comp
  have hindexBitsC : Computable indexBits := hindexBits.to_comp
  let enum : BitString → ℕ → List BitString := fun a s =>
    E (decodeFirst a, decodeSecond a) s
  have hEnum : Computable (fun r : BitString × ℕ => enum r.1 r.2) := by
    exact hE.comp (Computable.pair
      (Computable.pair (decodeFirst_computable.comp Computable.fst)
        (decodeSecond_computable.comp Computable.fst)) Computable.snd)
  have hIndexDecoder : Partrec (fun r : BitString × BitString =>
      StagedEnumeration.condFFixedLength enum r.2 r.1) :=
    StagedEnumeration.condFFixedLength_partrec enum hEnum
  have hRunP : Partrec (fun r : BitString × BitString => D (pPart r.1, r.2)) :=
    Partrec.comp hD.1 ((hpPartC.comp Computable.fst).pair Computable.snd)
  have hRunQ : Partrec (fun r : BitString × BitString => D (qPart r.1, [])) :=
    Partrec.comp hD.1 ((hqPartC.comp Computable.fst).pair (Computable.const []))
  have hRunQ' : Partrec
      (fun r : (BitString × BitString) × BitString => D (qPart r.1.1, [])) :=
    Partrec.comp hD.1
      ((hqPartC.comp (Computable.fst.comp Computable.fst)).pair (Computable.const []))
  have hPostInput : Computable
      (fun r : ((BitString × BitString) × BitString) × BitString =>
        (indexBits r.1.1.1, pairCode r.1.2 r.2)) := by
    exact (hindexBitsC.comp (Computable.fst.comp (Computable.fst.comp Computable.fst))).pair
      (Computable₂.comp CodedFiniteDistribution.pairCode_primrec.to_comp
        (Computable.snd.comp Computable.fst) Computable.snd)
  have hPost : Partrec₂ (fun r : (BitString × BitString) × BitString =>
      fun b => StagedEnumeration.condFFixedLength enum
        (pairCode r.2 b) (indexBits r.1.1)) := by
    have h := Partrec.comp hIndexDecoder hPostInput
    exact h.to₂
  have hAfterP : Partrec₂ (fun r : BitString × BitString =>
      fun t => (D (qPart r.1, [])).bind fun b =>
        StagedEnumeration.condFFixedLength enum (pairCode t b) (indexBits r.1)) := by
    have hQ : Partrec (fun r : (BitString × BitString) × BitString =>
        D (qPart r.1.1, [])) := hRunQ'
    exact Partrec.bind hQ hPost
  let g : BitString → BitString → Part BitString := fun z c =>
    (D (pPart c, z)).bind fun t =>
      (D (qPart c, [])).bind fun b =>
        StagedEnumeration.condFFixedLength enum (pairCode t b) (indexBits c)
  have hg : Partrec (fun r : BitString × BitString => g r.2 r.1) := by
    change Partrec (fun r : BitString × BitString =>
      (D (pPart r.1, r.2)).bind fun t =>
        (D (qPart r.1, [])).bind fun b =>
          StagedEnumeration.condFFixedLength enum (pairCode t b) (indexBits r.1))
    exact Partrec.bind hRunP hAfterP
  refine ⟨g, hg, ?_⟩
  intro p q z t b i w hp hq
  let code := pairCode (Nat.bits p.length)
    (p ++ pairCode (Nat.bits q.length) (q ++ Nat.bits i))
  have hTail : tail code = pairCode (Nat.bits q.length) (q ++ Nat.bits i) := by
    dsimp [tail, pLen, code]
    rw [decodeFirst_pairCode, bitsToNat_bits, decodeSecond_pairCode,
      List.drop_append_of_le_length (by simp)]
    have hd : p.drop p.length = [] := List.drop_eq_nil_of_le (by omega)
    simp [hd]
  have hPPart : pPart code = p := by
    dsimp [pPart, pLen, code]
    rw [decodeFirst_pairCode, bitsToNat_bits, decodeSecond_pairCode,
      List.take_append_of_le_length (by simp)]
    simp
  have hQLen : qLen code = q.length := by
    dsimp [qLen]
    rw [hTail, decodeFirst_pairCode, bitsToNat_bits]
  have hQTail : qTail code = q ++ Nat.bits i := by
    dsimp [qTail]
    rw [hTail, decodeSecond_pairCode]
  have hQPart : qPart code = q := by
    dsimp [qPart]
    rw [hQTail, hQLen, List.take_append_of_le_length (by simp)]
    simp
  have hIndexBits : indexBits code = Nat.bits i := by
    dsimp [indexBits]
    rw [hQTail, hQLen, List.drop_append_of_le_length (by simp)]
    have hd : q.drop q.length = [] := List.drop_eq_nil_of_le (by omega)
    simp [hd]
  change (w ∈ (D (pPart code, z)).bind fun t' =>
      (D (qPart code, [])).bind fun b' =>
        StagedEnumeration.condFFixedLength enum (pairCode t' b') (indexBits code)) ↔ _
  rw [hPPart, hQPart, hIndexBits]
  constructor
  · intro hw
    rw [Part.mem_bind_iff] at hw
    obtain ⟨t', ht', hw⟩ := hw
    have hteq : t' = t := Part.mem_unique ht' hp
    subst t'
    rw [Part.mem_bind_iff] at hw
    obtain ⟨b', hb', hw⟩ := hw
    have hbeq : b' = b := Part.mem_unique hb' hq
    simpa [hbeq] using hw
  · intro hw
    rw [Part.mem_bind_iff]
    refine ⟨t, hp, ?_⟩
    rw [Part.mem_bind_iff]
    exact ⟨b, hq, hw⟩

/-- compile a
staged enumeration into a partial recursive decoder with self-delimited parameter programs. -/
private theorem theorem5_extended_program_index_decoder
    (D : Map) (hD : isOptimalConditional D)
    (F : BitString → BitString → Set BitString)
    (E : (BitString × BitString) → ℕ → List BitString)
    (hE : Computable (fun q : (BitString × BitString) × ℕ => E q.1 q.2))
    (hmono : ∀ q s, E q s <+: E q (s + 1))
    (hSound : ∀ t b s w, w ∈ E (t, b) s → w ∈ F t b)
    (hComplete : ∀ t b w, w ∈ F t b → ∃ s, w ∈ E (t, b) s) :
    ∃ g : BitString → BitString → Part BitString,
      Partrec (fun q : BitString × BitString => g q.2 q.1) ∧
      ∀ (p q z t b : BitString), produces D p z t → produces D q [] b →
        (F t b).Finite → ∀ w ∈ F t b,
          ∃ i < (F t b).ncard,
            w ∈ g z (pairCode (Nat.bits p.length)
              (p ++ pairCode (Nat.bits q.length) (q ++ Nat.bits i))) := by
  classical
  obtain ⟨g, hg, hDecode⟩ :=
    theorem5_extended_parameter_decoder
      D hD E hE
  refine ⟨g, hg, ?_⟩
  intro p q z t b hp hq hFinite w hw
  obtain ⟨s, hs⟩ := hComplete t b w hw
  let L := (E (t, b) s).eraseDups
  have hmem : w ∈ L := by simpa [L] using hs
  let i := L.idxOf w
  have hi : i < L.length := List.idxOf_lt_length_iff.mpr hmem
  have hget : L.getD i [] = w := by
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_idxOf hi
  have hSubset : (L.toFinset : Set BitString) ⊆ F t b := by
    intro v hv
    have hv' : v ∈ E (t, b) s := by simpa [L] using hv
    exact hSound t b s v hv'
  have hlen : L.length ≤ (F t b).ncard := by
    calc
      L.length = L.toFinset.card :=
        (List.toFinset_card_of_nodup (nodup_eraseDups_list _)).symm
      _ = (L.toFinset : Set BitString).ncard := (Set.ncard_coe_finset _).symm
      _ ≤ (F t b).ncard := Set.ncard_le_ncard hSubset hFinite
  let enum : BitString → ℕ → List BitString := fun a s =>
    E (decodeFirst a, decodeSecond a) s
  have hI : bitsToNat (Nat.bits i) <
      (StagedEnumeration.condDistinctAt enum (pairCode t b) s).length := by
    rw [bitsToNat_bits]
    simpa [enum, StagedEnumeration.condDistinctAt, decodeFirst_pairCode,
      decodeSecond_pairCode, L] using hi
  have hEval := StagedEnumeration.condFFixedLength_eval enum
    (fun a s => hmono (decodeFirst a, decodeSecond a) s)
    (pairCode t b) (Nat.bits i) s hI
  have hEval' : L.getD i [] ∈
      StagedEnumeration.condFFixedLength enum (pairCode t b) (Nat.bits i) := by
    simpa [enum, StagedEnumeration.condDistinctAt, decodeFirst_pairCode,
      decodeSecond_pairCode, L, bitsToNat_bits] using hEval
  have hout : w ∈ g z (pairCode (Nat.bits p.length)
      (p ++ pairCode (Nat.bits q.length) (q ++ Nat.bits i))) := by
    apply (hDecode p q z t b i w hp hq).2
    rw [← hget]
    exact hEval'
  exact ⟨i, hi.trans_le hlen, hout⟩

/-- account for the
self-delimiting lengths of two programs and the binary ordinal in their combined code. -/
private lemma theorem5_extended_code_length
    (p q : BitString) (i r : ℕ) (hi : i < r) :
    (pairCode (Nat.bits p.length)
      (p ++ pairCode (Nat.bits q.length) (q ++ Nat.bits i))).length ≤
      p.length + 2 * Nat.log2 (p.length + 1) +
        q.length + 2 * Nat.log2 (q.length + 1) + Nat.log2 r + 7 := by
  have hbits (n : ℕ) : (Nat.bits n).length ≤ Nat.log2 (n + 1) + 1 := by
    rw [Nat.size_eq_bits_len, Nat.log2_eq_log_two]
    apply Nat.size_le.mpr
    exact lt_trans (Nat.lt_succ_self n) (by
      simpa [Nat.succ_eq_add_one] using
        Nat.lt_pow_succ_log_self (b := 2) (by decide) (n + 1))
  have hindex : (Nat.bits i).length ≤ Nat.log2 r + 1 := by
    rw [Nat.size_eq_bits_len, Nat.log2_eq_log_two]
    apply Nat.size_le.mpr
    exact lt_trans hi (by
      simpa [Nat.succ_eq_add_one] using
        Nat.lt_pow_succ_log_self (b := 2) (by decide) r)
  have hp := hbits p.length
  have hq := hbits q.length
  rw [length_pairCode, List.length_append, length_pairCode, List.length_append]
  omega

/-- describe an element by its index in a
uniformly enumerable finite family.  The advice and the finite-set code are self-delimited; the
remaining index costs at most the logarithm of the family size, up to an additive constant. -/
private theorem theorem5_extended_enumerate_index_description
    (D : Map) (hD : isOptimalConditional D)
    (F : BitString → BitString → Set BitString)
    (hF : IsRE (fun q : (BitString × BitString) × BitString =>
      q.2 ∈ F q.1.1 q.1.2)) :
    ∃ c : ℕ, ∀ (t b z w : BitString),
      (F t b).Finite → w ∈ F t b →
        natCondK D w z ≤ natCondK D t z + natK D b +
          2 * Nat.log2 (natK D b + 1) +
          2 * Nat.log2 (natCondK D t z + 1) + Nat.log2 (F t b).ncard + c := by
  classical
  obtain ⟨E, hE, hmono, hSound, hComplete⟩ :=
    theorem5_extended_index_description_staged_enumeration
      F hF
  obtain ⟨g, hg, hIndex⟩ :=
    theorem5_extended_program_index_decoder
      D hD F E hE hmono hSound hComplete
  obtain ⟨cMachine, hMachine⟩ := condK_partrec_cond_map_le_swapped D hD g hg
  refine ⟨cMachine + 7, ?_⟩
  intro t b z w hFinite hw
  obtain ⟨kt, hkt⟩ := exists_plainConditionalComplexityValue D hD t z
  obtain ⟨kb, hkb⟩ := exists_plainComplexityValue D hD b
  obtain ⟨p, hp, hplen⟩ := hkt.exists_program
  obtain ⟨q, hq, hqlen⟩ := hkb.exists_program
  have hktNat : kt = natCondK D t z := by
    have h := congrArg ENat.toNat hkt
    simpa [HasPlainConditionalComplexityValue, natCondK] using h.symm
  have hkbNat : kb = natK D b := by
    have h := congrArg ENat.toNat hkb
    simpa [HasPlainComplexityValue, natK] using h.symm
  obtain ⟨i, hi, hout⟩ := hIndex p q z t b hp hq hFinite w hw
  let code := pairCode (Nat.bits p.length)
    (p ++ pairCode (Nat.bits q.length) (q ++ Nat.bits i))
  have hcode :=
    theorem5_extended_code_length
      p q i (F t b).ncard hi
  have hcode' : code.length ≤ natCondK D t z +
      2 * Nat.log2 (natCondK D t z + 1) + natK D b +
        2 * Nat.log2 (natK D b + 1) + Nat.log2 (F t b).ncard + 7 := by
    calc
      code.length ≤ p.length + 2 * Nat.log2 (p.length + 1) +
          q.length + 2 * Nat.log2 (q.length + 1) + Nat.log2 (F t b).ncard + 7 := by
        change (pairCode (Nat.bits p.length)
          (p ++ pairCode (Nat.bits q.length) (q ++ Nat.bits i))).length ≤ _
        exact hcode
      _ = natCondK D t z + 2 * Nat.log2 (natCondK D t z + 1) +
          natK D b + 2 * Nat.log2 (natK D b + 1) +
          Nat.log2 (F t b).ncard + 7 := by
        rw [hplen, hktNat, hqlen, hkbNat]
  have hmachine := hMachine z code w hout
  have hmachine' : condK D w z ≤ ((code.length + cMachine : ℕ) : ℕ∞) := by
    calc
      condK D w z ≤ (code.length : ℕ∞) + (cMachine : ℕ∞) := hmachine
      _ = ((code.length + cMachine : ℕ) : ℕ∞) := by exact_mod_cast Nat.cast_add _ _
  have hnat : natCondK D w z ≤ code.length + cMachine := by
    exact ENat.toNat_le_of_le_natCast hmachine'
  change natCondK D w z ≤
    natCondK D t z + natK D b +
      2 * Nat.log2 (natK D b + 1) +
      2 * Nat.log2 (natCondK D t z + 1) + Nat.log2 (F t b).ncard +
      (cMachine + 7)
  omega

/-- the description in
the second half of Lemma 7 of the paper.  Let `N = K(⟨x̄, ȳ⟩, z)`, let `ȳ°` (the `y₀` of the
statement) be any `m`-tuple whose components have length at most `N`,
`A₀ = levelSet D S N ⟨x̄, ȳ°⟩ z`, `κ = K(ȳ° | x̄, z)`, `s = logSlack c₁ N` for a fixed constant
`c₁`,
and `B₀ = strongProj S κ s A₀`.  Then for every finite set `B` with `x̄ ∈ B₀ \ B`:
`K(x̄ | z) ≤ K(list B) + 2 log₂(K(list B) + 1) + log₂ |B₀ \ B| + O(log N)`.

Proof: the advice is `list S` (`O(log N)` bits as `K(x̄) ≤ N + O(1)`), `N`, `κ`, `c₁` and the
numbers `K(x̄_V ȳ°_V | x̄_W ȳ°_W, z)` (all `O(N)`).  Given `z` and the advice, `A₀` is enumerable
(the candidate set is computable, and `K(u_V | u_W, z) ≤ k` is semi-decidable, `D` being partial
computable), hence so is `B₀` (`x̄' ∈ B₀` as soon as the enumerated part of the section
`(A₀)_{x̄'}` is nonempty and has at least `2^(κ - s)` elements), and so is `B₀ \ B` given also
`list B`.  The program for `x̄` given `z` is a self-delimiting program for `list B`
(`K(list B) + 2 log₂(K(list B) + 1) + O(1)` bits), the self-delimiting advice, and the index of
`x̄` in the enumeration of `B₀ \ B` in binary (at most `log₂ |B₀ \ B| + 1` bits).  (`A₀` and `B₀`
need not be computable from `z` and the advice, and no bound on `K(list B₀ | z)` is claimed.) -/
private theorem theorem5_extended_enumerate
    (D : Map) (hD : isOptimalConditional D) (n m a c₁ : ℕ) :
    ∃ c : ℕ, ∀ (x : Fin n → BitString) (z : BitString) (S : Finset (Fin n → BitString)),
      x ∈ S →
      natK D (tupleSetCode S) ≤ logSlack a (natK D (tupleCode x)) →
      ∀ y y₀ : Fin m → BitString,
        (∀ i : Fin m, (y₀ i).length ≤ natK D (pairCode (tupleCode (Fin.append x y)) z)) →
        ∀ B : Finset (Fin n → BitString),
          x ∈ theorem5_extended_special_union_strongProj S
              (natCondK D (tupleCode y₀) (pairCode (tupleCode x) z))
              (logSlack c₁ (natK D (pairCode (tupleCode (Fin.append x y)) z)))
              (theorem5_extended_special_union_levelSet D S
                (natK D (pairCode (tupleCode (Fin.append x y)) z)) (Fin.append x y₀) z) \ B →
          natCondK D (tupleCode x) z ≤
            natK D (tupleSetCode B) + 2 * Nat.log2 (natK D (tupleSetCode B) + 1) +
              Nat.log2 (theorem5_extended_special_union_strongProj S
                (natCondK D (tupleCode y₀) (pairCode (tupleCode x) z))
                (logSlack c₁ (natK D (pairCode (tupleCode (Fin.append x y)) z)))
                (theorem5_extended_special_union_levelSet D S
                  (natK D (pairCode (tupleCode (Fin.append x y)) z)) (Fin.append x y₀) z) \
                    B).card +
              logSlack c (natK D (pairCode (tupleCode (Fin.append x y)) z)) := by
  classical
  obtain ⟨cAdvice, F, hF, hAdvice⟩ :=
    theorem5_extended_advice_enumeration
      D hD n m a c₁
  obtain ⟨cIndex, hIndex⟩ :=
    theorem5_extended_enumerate_index_description
      D hD F hF
  refine ⟨3 * cAdvice + cIndex + 2, ?_⟩
  intro x z S hxS hSCode y y₀ hy₀ B hxDiff
  set N := natK D (pairCode (tupleCode (Fin.append x y)) z)
  obtain ⟨t, hTBound, hFamily⟩ :=
    hAdvice x z S hxS hSCode y y₀ (by simpa [N] using hy₀)
  obtain ⟨hFeq, hFcard⟩ := hFamily B
  have hxDiff' : x ∈
      theorem5_extended_special_union_strongProj S
        (natCondK D (tupleCode y₀) (pairCode (tupleCode x) z))
        (logSlack c₁ N)
        (theorem5_extended_special_union_levelSet D S N
          (Fin.append x y₀) z) \ B := by
    simpa [N] using hxDiff
  have hxCode : tupleCode x ∈ F t (tupleSetCode B) := by
    rw [hFeq]
    exact Finset.mem_image.mpr ⟨x, hxDiff', rfl⟩
  have hFfinite : (F t (tupleSetCode B)).Finite := by
    rw [hFeq]
    exact Finset.finite_toSet ((
      theorem5_extended_special_union_strongProj S
        (natCondK D (tupleCode y₀) (pairCode (tupleCode x) z))
        (logSlack c₁ N)
        (theorem5_extended_special_union_levelSet D S N
          (Fin.append x y₀) z) \ B).image tupleCode)
  have hIndexBound := hIndex t (tupleSetCode B) z (tupleCode x) hFfinite hxCode
  rw [hFcard] at hIndexBound
  have hTBound' : natCondK D t z ≤ logSlack cAdvice N := by
    simpa [N] using hTBound
  have hLogT : 2 * Nat.log2 (natCondK D t z + 1) ≤
      2 * (natCondK D t z + 1) := by
    exact Nat.mul_le_mul_left 2 (Nat.log2_le_self (natCondK D t z + 1))
  have hSlackEq : logSlack (3 * cAdvice + cIndex + 2) N =
      3 * logSlack cAdvice N + (cIndex + 2) * ((Nat.bits N).length + 1) := by
    unfold logSlack
    ring
  have hSlack : natCondK D t z +
      2 * Nat.log2 (natCondK D t z + 1) + cIndex ≤
        logSlack (3 * cAdvice + cIndex + 2) N := by
    calc
      natCondK D t z + 2 * Nat.log2 (natCondK D t z + 1) + cIndex ≤
          3 * logSlack cAdvice N + cIndex + 2 := by omega
      _ ≤ 3 * logSlack cAdvice N +
          (cIndex + 2) * ((Nat.bits N).length + 1) := by
        have hmul := Nat.mul_le_mul_left (cIndex + 2)
          (show 1 ≤ (Nat.bits N).length + 1 by omega)
        have hmul' : cIndex + 2 ≤
            (cIndex + 2) * ((Nat.bits N).length + 1) := by simp
        calc
          3 * logSlack cAdvice N + cIndex + 2 =
              3 * logSlack cAdvice N + (cIndex + 2) := by omega
          _ ≤ 3 * logSlack cAdvice N +
              (cIndex + 2) * ((Nat.bits N).length + 1) :=
            Nat.add_le_add_left hmul' _
      _ = logSlack (3 * cAdvice + cIndex + 2) N := hSlackEq.symm
  calc
    natCondK D (tupleCode x) z ≤
        natCondK D t z + natK D (tupleSetCode B) +
          2 * Nat.log2 (natK D (tupleSetCode B) + 1) +
          2 * Nat.log2 (natCondK D t z + 1) +
          Nat.log2 (theorem5_extended_special_union_strongProj S
            (natCondK D (tupleCode y₀) (pairCode (tupleCode x) z))
            (logSlack c₁ N)
            (theorem5_extended_special_union_levelSet D S N
              (Fin.append x y₀) z) \ B).card + cIndex := hIndexBound
    _ = (natCondK D t z + 2 * Nat.log2 (natCondK D t z + 1) + cIndex) +
        (natK D (tupleSetCode B) +
          2 * Nat.log2 (natK D (tupleSetCode B) + 1) +
          Nat.log2 (theorem5_extended_special_union_strongProj S
            (natCondK D (tupleCode y₀) (pairCode (tupleCode x) z))
            (logSlack c₁ N)
            (theorem5_extended_special_union_levelSet D S N
              (Fin.append x y₀) z) \ B).card) := by omega
    _ ≤ logSlack (3 * cAdvice + cIndex + 2) N +
        (natK D (tupleSetCode B) +
          2 * Nat.log2 (natK D (tupleSetCode B) + 1) +
          Nat.log2 (theorem5_extended_special_union_strongProj S
            (natCondK D (tupleCode y₀) (pairCode (tupleCode x) z))
            (logSlack c₁ N)
            (theorem5_extended_special_union_levelSet D S N
              (Fin.append x y₀) z) \ B).card) :=
      Nat.add_le_add_right hSlack _
    _ = natK D (tupleSetCode B) +
        2 * Nat.log2 (natK D (tupleSetCode B) + 1) +
        Nat.log2 (theorem5_extended_special_union_strongProj S
          (natCondK D (tupleCode y₀) (pairCode (tupleCode x) z))
          (logSlack c₁ N)
          (theorem5_extended_special_union_levelSet D S N
            (Fin.append x y₀) z) \ B).card +
        logSlack (3 * cAdvice + cIndex + 2) N := by omega

/-- The level set, family of correct sets, and strong projection satisfy the bounds needed
for greedy selection and Lemma 7. Here `A₀ = levelSet D S N ⟨x̄, ȳ°⟩ z`,
`B₀ = strongProj S κ s A₀`, and `G = family S N κ s A₀`, with `κ = K(ȳ° | x̄, z)`
and `s = logSlack c₂ N`; these bounds follow from
`theorem5_extended_special_union_levelSet_combEnt`. -/
private theorem theorem5_extended_special_union_correct_family
    (D : Map) (hD : isOptimalConditional D) (n m a : ℕ) :
    ∃ c : ℕ, ∀ (x : Fin n → BitString) (z : BitString)
      (S : Finset (Fin n → BitString)),
      x ∈ S →
      natK D (tupleSetCode S) ≤ logSlack a (natK D (tupleCode x)) →
      S.card ≤ 2 ^ (natK D (tupleCode x) + logSlack a (natK D (tupleCode x))) →
      ∀ y y₀ : Fin m → BitString,
        (∀ i : Fin m, (y₀ i).length ≤ natK D (pairCode (tupleCode (Fin.append x y)) z)) →
        ∃ A₀ : Finset (Fin (n + m) → BitString),
        ∃ B₀ : Finset (Fin n → BitString),
        ∃ G : Finset (Finset (Fin (n + m) → BitString) × Finset (Fin n → BitString)),
          (A₀, B₀) ∈ G ∧
          x ∈ B₀ ∧
          (∀ p ∈ G, p.2 ⊆ S) ∧
          (∀ p ∈ G, ∀ V W : Finset (Fin (n + m)), V.Nonempty → Disjoint V W →
            combEnt p.1 V W ≤ combEnt A₀ V W) ∧
          (∀ V W : Finset (Fin (n + m)), V.Nonempty → Disjoint V W →
            (combEnt A₀ V W : ℤ) ≤
              subCondKRel D (Fin.append x y₀) z V W +
                logSlack c (natK D (pairCode (tupleCode (Fin.append x y)) z))) ∧
          natK D (theorem5_extended_special_union_familyCode G) ≤
            logSlack c (natK D (pairCode (tupleCode (Fin.append x y)) z)) ∧
          (∀ B : Finset (Fin n → BitString), x ∉ B →
            natCondK D (tupleCode x) z ≤
              natK D (tupleSetCode B) + 2 * Nat.log2 (natK D (tupleSetCode B) + 1) +
                Nat.log2 (B₀ \ B).card +
                logSlack c (natK D (pairCode (tupleCode (Fin.append x y)) z))) ∧
          (∀ p ∈ G, ∀ u ∈ p.1, ∀ i : Fin m,
            (u (Fin.natAdd n i)).length ≤ natK D (pairCode (tupleCode (Fin.append x y)) z)) ∧
          (∀ p ∈ G, ∀ x' ∈ p.2,
            (theorem5_extended_special_union_section p.1 x').Nonempty ∧
            natCondK D (tupleCode y₀) (pairCode (tupleCode x) z) ≤
              Nat.log2 (theorem5_extended_special_union_section p.1 x').card +
                logSlack c (natK D (pairCode (tupleCode (Fin.append x y)) z))) := by
  classical
  obtain ⟨c₂, h₂⟩ := theorem5_extended_section_lower_bound D hD n m
  obtain ⟨c₃, h₃⟩ := theorem5_extended_family_code D hD n m a c₂
  obtain ⟨c₄, h₄⟩ := theorem5_extended_enumerate D hD n m a c₂
  refine ⟨c₂ + c₃ + c₄ + 1, ?_⟩
  intro x z S hxS hSCode hSCard y y₀ hy₀
  have hmemA₀ : Fin.append x y₀ ∈ theorem5_extended_special_union_levelSet D S
      (natK D (pairCode (tupleCode (Fin.append x y)) z)) (Fin.append x y₀) z := by
    unfold theorem5_extended_special_union_levelSet
    exact Finset.mem_filter.mpr
      ⟨theorem5_extended_special_union_append_mem_candidates hxS hy₀,
        fun V W _ _ => le_rfl⟩
  have hxB₀ : x ∈ theorem5_extended_special_union_strongProj S
      (natCondK D (tupleCode y₀) (pairCode (tupleCode x) z))
      (logSlack c₂ (natK D (pairCode (tupleCode (Fin.append x y)) z)))
      (theorem5_extended_special_union_levelSet D S
        (natK D (pairCode (tupleCode (Fin.append x y)) z)) (Fin.append x y₀) z) := by
    unfold theorem5_extended_special_union_strongProj
    refine Finset.mem_filter.mpr ⟨hxS, ⟨y₀, ?_⟩, h₂ x z S hxS y y₀ hy₀⟩
    exact (theorem5_extended_special_union_mem_section _ x y₀).mpr hmemA₀
  have hc₂ : logSlack c₂ (natK D (pairCode (tupleCode (Fin.append x y)) z)) ≤
      logSlack (c₂ + c₃ + c₄ + 1) (natK D (pairCode (tupleCode (Fin.append x y)) z)) :=
    logSlack_mono_left (by omega) _
  have hc₃ : logSlack c₃ (natK D (pairCode (tupleCode (Fin.append x y)) z)) ≤
      logSlack (c₂ + c₃ + c₄ + 1) (natK D (pairCode (tupleCode (Fin.append x y)) z)) :=
    logSlack_mono_left (by omega) _
  have hc₄ : logSlack c₄ (natK D (pairCode (tupleCode (Fin.append x y)) z)) ≤
      logSlack (c₂ + c₃ + c₄ + 1) (natK D (pairCode (tupleCode (Fin.append x y)) z)) :=
    logSlack_mono_left (by omega) _
  have h1 : 1 ≤
      logSlack (c₂ + c₃ + c₄ + 1) (natK D (pairCode (tupleCode (Fin.append x y)) z)) := by
    unfold logSlack
    omega
  refine ⟨theorem5_extended_special_union_levelSet D S
      (natK D (pairCode (tupleCode (Fin.append x y)) z)) (Fin.append x y₀) z,
    theorem5_extended_special_union_strongProj S
      (natCondK D (tupleCode y₀) (pairCode (tupleCode x) z))
      (logSlack c₂ (natK D (pairCode (tupleCode (Fin.append x y)) z)))
      (theorem5_extended_special_union_levelSet D S
        (natK D (pairCode (tupleCode (Fin.append x y)) z)) (Fin.append x y₀) z),
    theorem5_extended_special_union_family S
      (natK D (pairCode (tupleCode (Fin.append x y)) z))
      (natCondK D (tupleCode y₀) (pairCode (tupleCode x) z))
      (logSlack c₂ (natK D (pairCode (tupleCode (Fin.append x y)) z)))
      (theorem5_extended_special_union_levelSet D S
        (natK D (pairCode (tupleCode (Fin.append x y)) z)) (Fin.append x y₀) z),
    ?_, hxB₀, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `(A₀, B₀) ∈ G`
    unfold theorem5_extended_special_union_family
    refine Finset.mem_image.mpr ⟨_, Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr ?_, fun V W _ _ => le_rfl⟩, rfl⟩
    unfold theorem5_extended_special_union_levelSet
    exact Finset.filter_subset _ _
  · -- every strong projection lies in `S`
    intro p hp
    unfold theorem5_extended_special_union_family at hp
    obtain ⟨C, _, rfl⟩ := Finset.mem_image.mp hp
    unfold theorem5_extended_special_union_strongProj
    exact Finset.filter_subset _ _
  · -- the sets of the family are correct
    intro p hp V W hV hdis
    unfold theorem5_extended_special_union_family at hp
    obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hp
    exact (Finset.mem_filter.mp hC).2 V W hV hdis
  · -- the entropies of the level set
    intro V W hV hdis
    have h := theorem5_extended_special_union_levelSet_combEnt D hD S
      (natK D (pairCode (tupleCode (Fin.append x y)) z)) (Fin.append x y₀) z V W hV hdis
    omega
  · -- the code of the family
    exact (h₃ x z S hxS hSCode hSCard y y₀ hy₀).trans hc₃
  · -- the enumerability consequence
    intro B hxB
    have h := h₄ x z S hxS hSCode y y₀ hy₀ B (Finset.mem_sdiff.mpr ⟨hxB₀, hxB⟩)
    omega
  · -- the length bound
    intro p hp u hu i
    unfold theorem5_extended_special_union_family at hp
    obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hp
    have hCsub := Finset.mem_powerset.mp (Finset.mem_filter.mp hC).1
    exact theorem5_extended_special_union_length_of_mem_candidates (hCsub hu) i
  · -- the section bounds over the strong projections
    intro p hp x' hx'
    unfold theorem5_extended_special_union_family at hp
    obtain ⟨C, _, rfl⟩ := Finset.mem_image.mp hp
    unfold theorem5_extended_special_union_strongProj at hx'
    obtain ⟨_, hne, hle⟩ := Finset.mem_filter.mp hx'
    exact ⟨hne, hle.trans (Nat.add_le_add_left hc₂ _)⟩

/-- The code used to put a pair in the canonical list of a family. -/
private def theorem5_extended_selection_code_pairCode
    {n m : ℕ}
    (p : Finset (Fin (n + m) → BitString) × Finset (Fin n → BitString)) : BitString :=
  pairCode (tupleSetCode p.1) (tupleSetCode p.2)

/-- a set of tuples
is recoverable from its canonical list code. -/
private lemma theorem5_extended_tupleSetCode_injective
    {n : ℕ} :
    Function.Injective (tupleSetCode : Finset (Fin n → BitString) → BitString) := by
  intro A B h
  have hLists : canonicalFinsetList (A.image tupleCode) =
      canonicalFinsetList (B.image tupleCode) := by
    apply Kolmogorov.listCode_injective
    exact h
  have hImages : A.image tupleCode = B.image tupleCode := by
    have h := congrArg List.toFinset hLists
    simpa only [canonicalFinsetList_toFinset] using h
  have hTuple : Function.Injective (tupleCode : (Fin n → BitString) → BitString) := by
    intro x y hxy
    apply List.ofFn_injective
    exact Kolmogorov.listCode_injective hxy
  apply Finset.ext
  intro x
  constructor
  · intro hx
    have hx' : tupleCode x ∈ A.image tupleCode :=
      Finset.mem_image.mpr ⟨x, hx, rfl⟩
    rw [hImages] at hx'
    obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hx'
    have : y = x := hTuple hxy
    simpa [this] using hy
  · intro hx
    have hx' : tupleCode x ∈ B.image tupleCode :=
      Finset.mem_image.mpr ⟨x, hx, rfl⟩
    rw [← hImages] at hx'
    obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hx'
    have : y = x := hTuple hxy
    simpa [this] using hy

/-- pair codes
preserve both components of a coded family element. -/
private lemma theorem5_extended_pairCode_injective
    {n m : ℕ} :
    Function.Injective
      (theorem5_extended_selection_code_pairCode
        (n := n) (m := m)) := by
  intro p q hpq
  have hpq' : (tupleSetCode p.1, tupleSetCode p.2) =
      (tupleSetCode q.1, tupleSetCode q.2) := pairCode_injective hpq
  cases p with
  | mk p₁ p₂ =>
    cases q with
    | mk q₁ q₂ =>
      simp only [Prod.mk.injEq] at hpq'
      exact Prod.ext
        (theorem5_extended_tupleSetCode_injective hpq'.1)
        (theorem5_extended_tupleSetCode_injective hpq'.2)

private noncomputable def theorem5_extended_selection_code_decodeFamilyKey
    {n m : ℕ}
    (G : Finset (Finset (Fin (n + m) → BitString) × Finset (Fin n → BitString)))
    (q : BitString) : Finset (Fin (n + m) → BitString) × Finset (Fin n → BitString) := by
  classical
  exact if hq : q ∈ G.image
      (theorem5_extended_selection_code_pairCode
        (n := n) (m := m)) then
    Classical.choose (Finset.mem_image.mp hq)
  else (∅, ∅)

private noncomputable def theorem5_extended_selection_code_selected
    {n m : ℕ}
    (G : Finset (Finset (Fin (n + m) → BitString) × Finset (Fin n → BitString)))
    (t : ℕ) : Finset
      (Finset (Fin (n + m) → BitString) × Finset (Fin n → BitString)) := by
  classical
  let L := (canonicalFinsetList (G.image
    (theorem5_extended_selection_code_pairCode
      (n := n) (m := m)))).map
      (theorem5_extended_selection_code_decodeFamilyKey G)
  exact L.foldl (fun H p =>
    if 2 ^ t ≤ (p.2 \ H.biUnion Prod.snd).card then insert p H else H) ∅

private lemma theorem5_extended_insert_invariant
    {n m : ℕ}
    (G : Finset (Finset (Fin (n + m) → BitString) × Finset (Fin n → BitString)))
    (S : Finset (Fin n → BitString)) (t : ℕ)
    (H : Finset (Finset (Fin (n + m) → BitString) × Finset (Fin n → BitString)))
    (p : Finset (Fin (n + m) → BitString) × Finset (Fin n → BitString))
    (hH : H ⊆ G)
    (hPack : H.card * 2 ^ t ≤ (H.biUnion Prod.snd).card)
    (hUnion : H.biUnion Prod.snd ⊆ S)
    (hp : p ∈ G) (hGS : ∀ p ∈ G, p.2 ⊆ S) :
    let H' := if 2 ^ t ≤ (p.2 \ H.biUnion Prod.snd).card then insert p H else H
    H' ⊆ G ∧ H'.card * 2 ^ t ≤ (H'.biUnion Prod.snd).card ∧
      H'.biUnion Prod.snd ⊆ S := by
  classical
  let U := H.biUnion Prod.snd
  by_cases htake : 2 ^ t ≤ (p.2 \ U).card
  · have htake' : 2 ^ t ≤ (p.2 \ H.biUnion Prod.snd).card := by
      simpa [U] using htake
    have hnot : p ∉ H := by
      intro hmem
      have hpU : p.2 ⊆ U := Finset.subset_biUnion_of_mem Prod.snd hmem
      have hempty : p.2 \ U = ∅ := Finset.sdiff_eq_empty_iff_subset.mpr hpU
      rw [hempty] at htake
      have hpos : 0 < 2 ^ t := Nat.pow_pos (by omega)
      simp only [Finset.card_empty] at htake
      omega
    have hnewDisj : Disjoint (p.2 \ U) U := Finset.sdiff_disjoint
    have hUnionInsert : (insert p H).biUnion Prod.snd = p.2 ∪ U := by
      simp [U, Finset.biUnion_insert]
    have hUnionParts : p.2 ∪ U = (p.2 \ U) ∪ U := by
      exact (Finset.sdiff_union_self_eq_union).symm
    simp only [ite_eq_left htake']
    refine ⟨?_, ?_, ?_⟩
    · exact Finset.insert_subset hp hH
    · calc
        (insert p H).card * 2 ^ t = H.card * 2 ^ t + 2 ^ t := by
          rw [Finset.card_insert_of_notMem hnot, Nat.add_mul]
          simp
        _ ≤ U.card + (p.2 \ U).card := Nat.add_le_add hPack htake
        _ = ((insert p H).biUnion Prod.snd).card := by
          rw [hUnionInsert, hUnionParts, Finset.card_union_of_disjoint hnewDisj]
          omega
    · rw [hUnionInsert]
      exact Finset.union_subset (hGS p hp) hUnion
  · have htake' : ¬ 2 ^ t ≤ (p.2 \ H.biUnion Prod.snd).card := by
      simpa [U] using htake
    simp only [ite_eq_right htake']
    exact ⟨hH, hPack, hUnion⟩

private lemma theorem5_extended_fold_invariant
    {n m : ℕ}
    (G : Finset (Finset (Fin (n + m) → BitString) × Finset (Fin n → BitString)))
    (S : Finset (Fin n → BitString)) (t : ℕ)
    (L : List (Finset (Fin (n + m) → BitString) × Finset (Fin n → BitString)))
    (hGS : ∀ p ∈ G, p.2 ⊆ S)
    (hL : ∀ p ∈ L, p ∈ G) :
    let H := L.foldl (fun H p =>
      if 2 ^ t ≤ (p.2 \ H.biUnion Prod.snd).card then insert p H else H) ∅
    H ⊆ G ∧ H.card * 2 ^ t ≤ (H.biUnion Prod.snd).card ∧
      H.biUnion Prod.snd ⊆ S := by
  classical
  let step := fun (H : Finset (Finset (Fin (n + m) → BitString) × Finset (Fin n → BitString)))
      (p : Finset (Fin (n + m) → BitString) × Finset (Fin n → BitString)) =>
    if 2 ^ t ≤ (p.2 \ H.biUnion Prod.snd).card then insert p H else H
  have hAux : ∀ (l : List (Finset (Fin (n + m) → BitString) × Finset (Fin n → BitString)))
      (H₀ : Finset (Finset (Fin (n + m) → BitString) × Finset (Fin n → BitString))),
      H₀ ⊆ G → H₀.card * 2 ^ t ≤ (H₀.biUnion Prod.snd).card →
      H₀.biUnion Prod.snd ⊆ S → (∀ p ∈ l, p ∈ G) →
      let H := l.foldl step H₀
      H ⊆ G ∧ H.card * 2 ^ t ≤ (H.biUnion Prod.snd).card ∧
        H.biUnion Prod.snd ⊆ S := by
    intro l
    induction l with
    | nil =>
        intro H₀ hH₀ hPack hUnion hmem
        simpa [step] using And.intro hH₀ (And.intro hPack hUnion)
    | cons p l ih =>
        intro H₀ hH₀ hPack hUnion hmem
        have hp : p ∈ G := hmem p List.mem_cons_self
        have hmemTail : ∀ q ∈ l, q ∈ G := fun q hq => hmem q (List.mem_cons_of_mem p hq)
        have hNext := theorem5_extended_insert_invariant
          G S t H₀ p hH₀ hPack hUnion hp hGS
        have hNext' : step H₀ p ⊆ G ∧
            (step H₀ p).card * 2 ^ t ≤ ((step H₀ p).biUnion Prod.snd).card ∧
            (step H₀ p).biUnion Prod.snd ⊆ S := by
          simpa [step] using hNext
        simpa [step, List.foldl_cons] using
          ih (step H₀ p) hNext'.1 hNext'.2.1 hNext'.2.2 hmemTail
  simpa [step] using hAux L ∅ (by simp) (by simp) (by simp) hL

private lemma theorem5_extended_fold_union_mono
    {n m : ℕ}
    (t : ℕ)
    (L : List (Finset (Fin (n + m) → BitString) × Finset (Fin n → BitString)))
    (H₀ : Finset (Finset (Fin (n + m) → BitString) × Finset (Fin n → BitString))) :
    H₀.biUnion Prod.snd ⊆
      (L.foldl (fun (H : Finset
          (Finset (Fin (n + m) → BitString) × Finset (Fin n → BitString)))
          (p : Finset (Fin (n + m) → BitString) × Finset (Fin n → BitString)) =>
        if 2 ^ t ≤ (p.2 \ H.biUnion Prod.snd).card then insert p H else H) H₀).biUnion
          Prod.snd := by
  classical
  let step := fun (H : Finset (Finset (Fin (n + m) → BitString) × Finset (Fin n → BitString)))
      (p : Finset (Fin (n + m) → BitString) × Finset (Fin n → BitString)) =>
    if 2 ^ t ≤ (p.2 \ H.biUnion Prod.snd).card then insert p H else H
  have hOne : ∀ H p, H.biUnion Prod.snd ⊆ (step H p).biUnion Prod.snd := by
    intro H p
    by_cases h : 2 ^ t ≤ (p.2 \ H.biUnion Prod.snd).card
    · simp [step, h, Finset.biUnion_insert]
    · simp [step, h]
  induction L generalizing H₀ with
  | nil => simp
  | cons p L ih =>
      simpa [step, List.foldl_cons] using (hOne H₀ p).trans (ih (step H₀ p))

private lemma theorem5_extended_fold_covers_distinguished
    {n m : ℕ}
    (t : ℕ)
    (L : List (Finset (Fin (n + m) → BitString) × Finset (Fin n → BitString)))
    (p₀ : Finset (Fin (n + m) → BitString) × Finset (Fin n → BitString))
    (hp₀ : p₀ ∈ L) :
    (p₀.2 \ (L.foldl (fun (H : Finset
      (Finset (Fin (n + m) → BitString) × Finset (Fin n → BitString)))
      (p : Finset (Fin (n + m) → BitString) × Finset (Fin n → BitString)) =>
      if 2 ^ t ≤ (p.2 \ H.biUnion Prod.snd).card then insert p H else H) ∅).biUnion
        Prod.snd).card < 2 ^ t := by
  classical
  let step := fun (H : Finset (Finset (Fin (n + m) → BitString) × Finset (Fin n → BitString)))
      (p : Finset (Fin (n + m) → BitString) × Finset (Fin n → BitString)) =>
    if 2 ^ t ≤ (p.2 \ H.biUnion Prod.snd).card then insert p H else H
  have hAux : ∀ (l : List
      (Finset (Fin (n + m) → BitString) × Finset (Fin n → BitString)))
      (H₀ : Finset
        (Finset (Fin (n + m) → BitString) × Finset (Fin n → BitString))),
      p₀ ∈ l →
      (p₀.2 \ (l.foldl step H₀).biUnion Prod.snd).card < 2 ^ t := by
    intro l
    induction l with
    | nil =>
        intro H₀ hp
        simp at hp
    | cons p l ih =>
        intro H₀ hp
        rcases List.mem_cons.mp hp with hEq | hTail
        · have hpEq : p = p₀ := hEq.symm
          subst p
          let Hmid := step H₀ p₀
          have hmid : (p₀.2 \ Hmid.biUnion Prod.snd).card < 2 ^ t := by
            by_cases htake : 2 ^ t ≤ (p₀.2 \ H₀.biUnion Prod.snd).card
            · have hmidUnion : Hmid.biUnion Prod.snd =
                  p₀.2 ∪ H₀.biUnion Prod.snd := by
                simp [Hmid, step, htake, Finset.biUnion_insert]
              have hpMid : p₀.2 ⊆ Hmid.biUnion Prod.snd := by
                rw [hmidUnion]
                exact Finset.subset_union_left
              have hdiff : p₀.2 \ Hmid.biUnion Prod.snd = ∅ :=
                Finset.sdiff_eq_empty_iff_subset.mpr hpMid
              have hpos : 0 < 2 ^ t := Nat.pow_pos (by omega)
              rw [hdiff, Finset.card_empty]
              exact hpos
            · have hlt : (p₀.2 \ H₀.biUnion Prod.snd).card < 2 ^ t := by omega
              simpa [Hmid, step, htake] using hlt
          have hmono := theorem5_extended_fold_union_mono
            (n := n) (m := m) t l Hmid
          have hsub : p₀.2 \ (l.foldl step Hmid).biUnion Prod.snd ⊆
              p₀.2 \ Hmid.biUnion Prod.snd := by
            intro x hx
            rcases Finset.mem_sdiff.mp hx with ⟨hx₀, hxnot⟩
            exact Finset.mem_sdiff.mpr ⟨hx₀, fun hxU => hxnot (hmono hxU)⟩
          exact (Finset.card_le_card hsub).trans_lt hmid
        · simpa [List.foldl_cons, step] using ih (step H₀ p) hTail
  simpa [step] using hAux L ∅ hp₀

/-- the greedy
selection's disjoint new parts bound its size, and processing the distinguished pair leaves fewer
than the threshold uncovered. -/
private theorem theorem5_extended_greedy_packing_coverage
    {n m : ℕ}
    (G : Finset (Finset (Fin (n + m) → BitString) × Finset (Fin n → BitString)))
    (S B₀ : Finset (Fin n → BitString))
    (p₀ : Finset (Fin (n + m) → BitString) × Finset (Fin n → BitString))
    (t : ℕ) (hp₀ : p₀ ∈ G) (hp₀second : p₀.2 = B₀)
    (hGS : ∀ p ∈ G, p.2 ⊆ S) :
    let H := theorem5_extended_selection_code_selected
        G t
    H ⊆ G ∧ H.card * 2 ^ t ≤ S.card ∧
      (B₀ \ H.biUnion (fun p => p.2)).card < 2 ^ t := by
  classical
  let key :
      (Finset (Fin (n + m) → BitString) × Finset (Fin n → BitString)) → BitString :=
    theorem5_extended_selection_code_pairCode
  let keys := G.image key
  let decode :=
    theorem5_extended_selection_code_decodeFamilyKey G
  let L := (canonicalFinsetList keys).map decode
  let step := fun (H : Finset
      (Finset (Fin (n + m) → BitString) × Finset (Fin n → BitString)))
      (p : Finset (Fin (n + m) → BitString) × Finset (Fin n → BitString)) =>
    if 2 ^ t ≤ (p.2 \ H.biUnion Prod.snd).card then insert p H else H
  have hKeyInjective : Function.Injective key := by
    simpa [key] using
      (theorem5_extended_pairCode_injective
        (n := n) (m := m))
  have hDecode : ∀ q, q ∈ keys → decode q ∈ G ∧ key (decode q) = q := by
    intro q hq
    have hq' : q ∈ G.image
        (theorem5_extended_selection_code_pairCode
          (n := n) (m := m)) := by
      simpa [keys, key] using hq
    dsimp [decode,
      theorem5_extended_selection_code_decodeFamilyKey]
    rw [dite_eq_left hq']
    simpa [key] using Classical.choose_spec (Finset.mem_image.mp hq')
  have hL : ∀ p ∈ L, p ∈ G := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    apply (hDecode q ?_).1
    exact mem_canonicalFinsetList.mp hq
  have hq₀ : key p₀ ∈ keys := Finset.mem_image.mpr ⟨p₀, hp₀, rfl⟩
  have hq₀L : key p₀ ∈ canonicalFinsetList keys :=
    mem_canonicalFinsetList.mpr hq₀
  have hDecode₀ : decode (key p₀) = p₀ := by
    apply hKeyInjective
    exact (hDecode (key p₀) hq₀).2
  have hp₀L : p₀ ∈ L := List.mem_map.mpr ⟨key p₀, hq₀L, hDecode₀⟩
  have hInv :=
    theorem5_extended_fold_invariant
      G S t L hGS hL
  have hCard : (L.foldl step ∅).card * 2 ^ t ≤ S.card := by
    calc
      (L.foldl step ∅).card * 2 ^ t ≤ ((L.foldl step ∅).biUnion Prod.snd).card := by
        simpa [step] using hInv.2.1
      _ ≤ S.card := Finset.card_le_card hInv.2.2
  have hCoverage :=
    theorem5_extended_fold_covers_distinguished
      t L p₀ hp₀L
  have hCoverage' :
      (B₀ \ (L.foldl step ∅).biUnion (fun p => p.2)).card < 2 ^ t := by
    simpa [hp₀second, step] using hCoverage
  change (L.foldl step ∅) ⊆ G ∧
    (L.foldl step ∅).card * 2 ^ t ≤ S.card ∧
    (B₀ \ (L.foldl step ∅).biUnion (fun p => p.2)).card < 2 ^ t
  exact ⟨hInv.1, hCard, hCoverage'⟩

/-- A total parser from a tuple-set code to a finite set of tuples. -/
private noncomputable def theorem5_extended_computable_decoder_decodeTupleSet
    (n : ℕ) (w : BitString) : Finset (Fin n → BitString) := by
  classical
  exact ((decodeListCode w).filter fun s =>
    decide (theorem5_extended_stochastic_model_decodeTupleCode n s = s)).toFinset.image
      (theorem5_extended_stochastic_model_decodeTuple n)

private noncomputable def theorem5_extended_computable_decoder_decodeFamilyKey
    (n m : ℕ) (q : BitString) :
    Finset (Fin (n + m) → BitString) × Finset (Fin n → BitString) :=
  (theorem5_extended_computable_decoder_decodeTupleSet
      (n + m) (decodeFirst q),
    theorem5_extended_computable_decoder_decodeTupleSet
      n (decodeSecond q))

private noncomputable def theorem5_extended_computable_decoder_decoderFunction
    (n m : ℕ) (w : BitString) : BitString × BitString := by
  classical
  let L := (decodeListCode (decodeFirst w)).map
    (theorem5_extended_computable_decoder_decodeFamilyKey
      n m)
  let t := bitsToNat (decodeSecond w)
  let H := L.foldl (fun
      (H : Finset (Finset (Fin (n + m) → BitString) × Finset (Fin n → BitString)))
      (p : Finset (Fin (n + m) → BitString) × Finset (Fin n → BitString)) =>
    if 2 ^ t ≤ (p.2 \ H.biUnion Prod.snd).card then insert p H else H) ∅
  exact (tupleSetCode (H.biUnion fun p => p.1),
    tupleSetCode (H.biUnion fun p => p.2))

private def theorem5_extended_decoder_computable_codeMember
    (p : BitString × List BitString) : Bool :=
  p.2.foldr (fun y b => decide (p.1 = y) || b) false

private def theorem5_extended_decoder_computable_codeDiffCount
    (p : List BitString × List BitString) : ℕ :=
  (p.1.filter fun x =>
    !(theorem5_extended_decoder_computable_codeMember
      (x, p.2))).length

private def theorem5_extended_decoder_computable_codeStep
    (t : ℕ) (s p : List BitString × List BitString) :
    List BitString × List BitString :=
  if 2 ^ t ≤
      theorem5_extended_decoder_computable_codeDiffCount
        (p.2, s.2) then
    (s.1 ++ p.1, s.2 ++ p.2)
  else s

private def theorem5_extended_decoder_computable_codeStepAcc
    (s : ℕ × (List BitString × List BitString))
    (p : List BitString × List BitString) :
    ℕ × (List BitString × List BitString) :=
  (s.1,
    theorem5_extended_decoder_computable_codeStep
      s.1 s.2 p)

private def theorem5_extended_decoder_computable_codeKey
    (n m : ℕ) (q : BitString) : List BitString × List BitString :=
  (decodeListCode
      (theorem5_extended_stochastic_model_mapCode (n + m) (decodeFirst q)),
    decodeListCode
      (theorem5_extended_stochastic_model_mapCode n (decodeSecond q)))

private def theorem5_extended_decoder_computable_codeFold
    (n m : ℕ) (w : BitString) : ℕ × (List BitString × List BitString) :=
  ((decodeListCode (decodeFirst w)).map
    (theorem5_extended_decoder_computable_codeKey
      n m)).foldl
    theorem5_extended_decoder_computable_codeStepAcc
    (bitsToNat (decodeSecond w), ([], []))

private def theorem5_extended_decoder_computable_codeFunction
    (n m : ℕ) (w : BitString) : BitString × BitString := by
  let S := (theorem5_extended_decoder_computable_codeFold
    n m w).2
  exact (listCode (canonicalFinsetList S.1.toFinset),
    listCode (canonicalFinsetList S.2.toFinset))

private theorem theorem5_extended_decoder_computable_parse_codes_toFinset
    (d : ℕ) (w : BitString) :
    (decodeListCode
      (theorem5_extended_stochastic_model_mapCode d w)).toFinset =
      (theorem5_extended_computable_decoder_decodeTupleSet
        d w).image tupleCode := by
  classical
  let F := ((decodeListCode w).filter fun s =>
    decide (theorem5_extended_stochastic_model_decodeTupleCode d s = s)).toFinset
  have hvalid : ∀ s ∈ F,
      tupleCode (theorem5_extended_stochastic_model_decodeTuple d s) = s := by
    intro s hs
    have hs' : theorem5_extended_stochastic_model_decodeTupleCode d s = s := by
      simp only [F, List.mem_toFinset, List.mem_filter] at hs
      exact of_decide_eq_true hs.2
    simpa [theorem5_extended_stochastic_model_decodeTupleCode] using hs'
  unfold theorem5_extended_stochastic_model_mapCode
    theorem5_extended_computable_decoder_decodeTupleSet
  simp only [finsetListCode, decodeListCode_listCode,
    canonicalFinsetList_toFinset]
  rw [Finset.image_image]
  calc
    F = F.image id := by simp
    _ = F.image
        (fun s => tupleCode
          (theorem5_extended_stochastic_model_decodeTuple d s)) := by
      apply Finset.image_congr
      intro s hs
      exact (hvalid s hs).symm

private theorem theorem5_extended_decoder_computable_codeMember_iff
    (x : BitString) (L : List BitString) :
    theorem5_extended_decoder_computable_codeMember
      (x, L) = true ↔ x ∈ L := by
  induction L with
  | nil => simp [theorem5_extended_decoder_computable_codeMember]
  | cons y L ih =>
      change (decide (x = y) ||
        theorem5_extended_decoder_computable_codeMember
          (x, L)) = true ↔ x ∈ y :: L
      simp only [Bool.or_eq_true, decide_eq_true_eq, ih, List.mem_cons]

private theorem theorem5_extended_decoder_computable_parse_codes_nodup
    (d : ℕ) (w : BitString) :
    (decodeListCode
      (theorem5_extended_stochastic_model_mapCode d w)).Nodup := by
  unfold theorem5_extended_stochastic_model_mapCode finsetListCode
  simp only [decodeListCode_listCode]
  exact canonicalFinsetList_nodup _

private theorem theorem5_extended_decoder_computable_codeDiffCount_eq_card
    (A B : List BitString) (hA : A.Nodup) :
    theorem5_extended_decoder_computable_codeDiffCount
      (A, B) = (A.toFinset \ B.toFinset).card := by
  classical
  let C := A.filter fun x =>
    !(theorem5_extended_decoder_computable_codeMember
      (x, B))
  have hC : C.toFinset = A.toFinset \ B.toFinset := by
    ext x
    change x ∈ (A.filter fun x =>
      !(theorem5_extended_decoder_computable_codeMember
        (x, B))).toFinset ↔ x ∈ A.toFinset \ B.toFinset
    simp only [List.mem_toFinset, List.mem_filter, Finset.mem_sdiff]
    constructor
    · rintro ⟨hxA, hxNotB⟩
      refine ⟨hxA, ?_⟩
      intro hxB
      have hxMem :=
        (theorem5_extended_decoder_computable_codeMember_iff
          x B).2 hxB
      simp [hxMem] at hxNotB
    · rintro ⟨hxA, hxNotB⟩
      refine ⟨hxA, ?_⟩
      have hmem :
          theorem5_extended_decoder_computable_codeMember
            (x, B) = false := by
        cases h : theorem5_extended_decoder_computable_codeMember
            (x, B) with
        | false => rfl
        | true => exact False.elim (hxNotB
            ((theorem5_extended_decoder_computable_codeMember_iff
              x B).1 h))
      simp [hmem]
  calc
    theorem5_extended_decoder_computable_codeDiffCount
        (A, B) = C.length := rfl
    _ = C.toFinset.card :=
      (List.toFinset_card_of_nodup (hA.filter _)).symm
    _ = (A.toFinset \ B.toFinset).card := congrArg Finset.card hC

private theorem theorem5_extended_decoder_computable_codeMember_primrec :
    Primrec
      theorem5_extended_decoder_computable_codeMember := by
  have hstep : Primrec₂ (fun (p : BitString × List BitString)
      (q : BitString × Bool) => decide (p.1 = q.1) || q.2) := by
    have heq : Primrec fun q :
        (BitString × List BitString) × (BitString × Bool) =>
          decide (q.1.1 = q.2.1) :=
      (PrimrecRel.decide Primrec.eq).comp
        (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)
    change Primrec fun q :
        (BitString × List BitString) × (BitString × Bool) =>
          decide (q.1.1 = q.2.1) || q.2.2
    exact (Primrec.dom_bool₂ (fun a b : Bool => a || b)).comp
      heq (Primrec.snd.comp Primrec.snd)
  have hf := Primrec.list_foldr Primrec.snd (Primrec.const false) hstep
  exact hf.of_eq fun p => rfl

private theorem theorem5_extended_decoder_computable_codeDiffCount_primrec :
    Primrec
      theorem5_extended_decoder_computable_codeDiffCount := by
  have hpred : Primrec₂ (fun (p : List BitString × List BitString)
      (x : BitString) =>
        !(theorem5_extended_decoder_computable_codeMember
          (x, p.2))) := by
    have harg : Primrec fun q :
        (List BitString × List BitString) × BitString => (q.2, q.1.2) :=
      Primrec.pair Primrec.snd (Primrec.snd.comp Primrec.fst)
    exact (Primrec.not.comp
      (theorem5_extended_decoder_computable_codeMember_primrec.comp
        harg)).to₂
  have hfilter := Primrec.list_filter Primrec.fst hpred
  exact (Primrec.list_length.comp hfilter).of_eq fun _ => rfl

private theorem theorem5_extended_decoder_computable_codeStepAcc_primrec :
    Primrec₂
      theorem5_extended_decoder_computable_codeStepAcc := by
  have hpow2 : Primrec₂ (fun a b : ℕ => a ^ b) :=
    Primrec.nat_iff.mpr Nat.Primrec.pow
  have hpow : Primrec fun q :
      (ℕ × (List BitString × List BitString)) ×
        (List BitString × List BitString) => 2 ^ q.1.1 :=
    hpow2.comp (Primrec.const 2) (Primrec.fst.comp Primrec.fst)
  have hcount : Primrec fun q :
      (ℕ × (List BitString × List BitString)) ×
        (List BitString × List BitString) =>
          theorem5_extended_decoder_computable_codeDiffCount
            (q.2.2, q.1.2.2) :=
    theorem5_extended_decoder_computable_codeDiffCount_primrec.comp
      (Primrec.pair (Primrec.snd.comp Primrec.snd)
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
  have haccept : PrimrecPred (fun q :
      (ℕ × (List BitString × List BitString)) ×
        (List BitString × List BitString) => 2 ^ q.1.1 ≤
          theorem5_extended_decoder_computable_codeDiffCount
            (q.2.2, q.1.2.2)) :=
    PrimrecRel.comp Primrec.nat_le hpow hcount
  have hfirst : Primrec fun q :
      (ℕ × (List BitString × List BitString)) ×
        (List BitString × List BitString) =>
          (q.1.2.1 ++ q.2.1, q.1.2.2 ++ q.2.2) :=
    Primrec.pair
      (Primrec.list_append.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.fst.comp Primrec.snd))
      (Primrec.list_append.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.snd.comp Primrec.snd))
  have hstay : Primrec fun q :
      (ℕ × (List BitString × List BitString)) ×
        (List BitString × List BitString) => (q.1.2.1, q.1.2.2) :=
    Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hfirstAcc : Primrec fun q :
      (ℕ × (List BitString × List BitString)) ×
        (List BitString × List BitString) =>
          (q.1.1, (q.1.2.1 ++ q.2.1, q.1.2.2 ++ q.2.2)) :=
    Primrec.pair (Primrec.fst.comp Primrec.fst) hfirst
  have hstayAcc : Primrec fun q :
      (ℕ × (List BitString × List BitString)) ×
        (List BitString × List BitString) =>
          (q.1.1, (q.1.2.1, q.1.2.2)) :=
    Primrec.pair (Primrec.fst.comp Primrec.fst) hstay
  have hstep : Primrec fun q :
      (ℕ × (List BitString × List BitString)) ×
        (List BitString × List BitString) =>
        if 2 ^ q.1.1 ≤
            theorem5_extended_decoder_computable_codeDiffCount
              (q.2.2, q.1.2.2)
        then (q.1.1, (q.1.2.1 ++ q.2.1, q.1.2.2 ++ q.2.2))
        else (q.1.1, (q.1.2.1, q.1.2.2)) :=
    Primrec.ite haccept hfirstAcc hstayAcc
  change Primrec₂ (fun (s : ℕ × (List BitString × List BitString))
    (p : List BitString × List BitString) =>
      theorem5_extended_decoder_computable_codeStepAcc
        s p)
  exact hstep.to₂.of_eq fun s p => by
    rcases s with ⟨t, ⟨a, b⟩⟩
    rcases p with ⟨c, d⟩
    by_cases hcond : 2 ^ t ≤
        theorem5_extended_decoder_computable_codeDiffCount
          (d, b) <;>
      simp [theorem5_extended_decoder_computable_codeStepAcc,
        theorem5_extended_decoder_computable_codeStep,
        hcond]

private theorem theorem5_extended_decoder_computable_codeFunction_eq_decoderFunction
    (n m : ℕ) (w : BitString) :
    theorem5_extended_decoder_computable_codeFunction
        n m w =
      theorem5_extended_computable_decoder_decoderFunction
        n m w := by
  classical
  let Q := decodeListCode (decodeFirst w)
  let t := bitsToNat (decodeSecond w)
  let pkey : BitString →
      Finset (Fin (n + m) → BitString) × Finset (Fin n → BitString) :=
    theorem5_extended_computable_decoder_decodeFamilyKey
      n m
  let ckey : BitString → List BitString × List BitString :=
    theorem5_extended_decoder_computable_codeKey
      n m
  let pstep :
      Finset (Finset (Fin (n + m) → BitString) × Finset (Fin n → BitString)) →
      Finset (Fin (n + m) → BitString) × Finset (Fin n → BitString) →
      Finset (Finset (Fin (n + m) → BitString) × Finset (Fin n → BitString)) :=
    fun H p => if 2 ^ t ≤ (p.2 \ H.biUnion Prod.snd).card then insert p H else H
  let Inv := fun
      (H : Finset
        (Finset (Fin (n + m) → BitString) × Finset (Fin n → BitString)))
      (S : List BitString × List BitString) =>
    S.1.toFinset = (H.biUnion fun p => p.1).image tupleCode ∧
      S.2.toFinset = (H.biUnion fun p => p.2).image tupleCode
  have hTupleInj (k : ℕ) :
      Function.Injective (tupleCode : (Fin k → BitString) → BitString) := by
    intro x y hxy
    apply List.ofFn_injective
    exact Kolmogorov.listCode_injective hxy
  have hKeySpec (q : BitString) :
      (ckey q).1.toFinset = (pkey q).1.image tupleCode ∧
      (ckey q).2.toFinset = (pkey q).2.image tupleCode := by
    constructor
    · simpa [ckey, pkey,
        theorem5_extended_computable_decoder_decodeFamilyKey,
        theorem5_extended_decoder_computable_codeKey] using
        theorem5_extended_decoder_computable_parse_codes_toFinset
          (n + m) (decodeFirst q)
    · simpa [ckey, pkey,
        theorem5_extended_computable_decoder_decodeFamilyKey,
        theorem5_extended_decoder_computable_codeKey] using
        theorem5_extended_decoder_computable_parse_codes_toFinset
          n (decodeSecond q)
  have hKeyNodup (q : BitString) :
      (ckey q).1.Nodup ∧ (ckey q).2.Nodup := by
    constructor
    · simpa [ckey,
        theorem5_extended_decoder_computable_codeKey] using
        theorem5_extended_decoder_computable_parse_codes_nodup
          (n + m) (decodeFirst q)
    · simpa [ckey,
        theorem5_extended_decoder_computable_codeKey] using
        theorem5_extended_decoder_computable_parse_codes_nodup
          n (decodeSecond q)
  have hOneStep (H : Finset
      (Finset (Fin (n + m) → BitString) × Finset (Fin n → BitString)))
      (S : List BitString × List BitString) (q : BitString)
      (hInv : Inv H S) : Inv (pstep H (pkey q))
        (theorem5_extended_decoder_computable_codeStep
          t S (ckey q)) := by
    have hTupleInjFirst := hTupleInj (n + m)
    have hTupleInjSecond := hTupleInj n
    have hDiffSet :
        (ckey q).2.toFinset \ S.2.toFinset =
          ((pkey q).2 \ H.biUnion Prod.snd).image tupleCode := by
      rw [hKeySpec q |>.2, hInv.2,
        ← Finset.image_sdiff _ _ hTupleInjSecond]
    have hCount :
        theorem5_extended_decoder_computable_codeDiffCount
            ((ckey q).2, S.2) =
          ((pkey q).2 \ H.biUnion Prod.snd).card := by
      calc
        _ = ((ckey q).2.toFinset \ S.2.toFinset).card :=
          theorem5_extended_decoder_computable_codeDiffCount_eq_card
            (ckey q).2 S.2 (hKeyNodup q).2
        _ = ((pkey q).2 \ H.biUnion Prod.snd).card := by
          rw [hDiffSet]
          exact Finset.card_image_of_injective _ hTupleInjSecond
    have hUnionFirst :
        (insert (pkey q) H).biUnion (fun p => p.1) =
          (H.biUnion fun p => p.1) ∪ (pkey q).1 := by
      rw [Finset.biUnion_insert]
      exact Finset.union_comm _ _
    have hUnionSecond :
        (insert (pkey q) H).biUnion (fun p => p.2) =
          (H.biUnion fun p => p.2) ∪ (pkey q).2 := by
      rw [Finset.biUnion_insert]
      exact Finset.union_comm _ _
    have hAppendFirst :
        (S.1 ++ (ckey q).1).toFinset =
          ((insert (pkey q) H).biUnion (fun p => p.1)).image tupleCode := by
      calc
        _ = S.1.toFinset ∪ (ckey q).1.toFinset := List.toFinset_append
        _ = (H.biUnion fun p => p.1).image tupleCode ∪
            (pkey q).1.image tupleCode := by rw [hInv.1, hKeySpec q |>.1]
        _ = ((insert (pkey q) H).biUnion (fun p => p.1)).image tupleCode := by
          rw [hUnionFirst, Finset.image_union]
    have hAppendSecond :
        (S.2 ++ (ckey q).2).toFinset =
          ((insert (pkey q) H).biUnion (fun p => p.2)).image tupleCode := by
      calc
        _ = S.2.toFinset ∪ (ckey q).2.toFinset := List.toFinset_append
        _ = (H.biUnion fun p => p.2).image tupleCode ∪
            (pkey q).2.image tupleCode := by rw [hInv.2, hKeySpec q |>.2]
        _ = ((insert (pkey q) H).biUnion (fun p => p.2)).image tupleCode := by
          rw [hUnionSecond, Finset.image_union]
    by_cases htake : 2 ^ t ≤ ((pkey q).2 \ H.biUnion Prod.snd).card
    · have htakeCode : 2 ^ t ≤
          theorem5_extended_decoder_computable_codeDiffCount
            ((ckey q).2, S.2) := by rw [hCount]; exact htake
      simp only [theorem5_extended_decoder_computable_codeStep,
        ite_eq_left htakeCode, pstep, ite_eq_left htake]
      exact ⟨hAppendFirst, hAppendSecond⟩
    · have htakeCode : ¬ 2 ^ t ≤
          theorem5_extended_decoder_computable_codeDiffCount
            ((ckey q).2, S.2) := by simpa [hCount] using htake
      simp only [theorem5_extended_decoder_computable_codeStep,
        ite_eq_right htakeCode, pstep, ite_eq_right htake]
      exact hInv
  have hFoldInv : ∀ (Q : List BitString) (H : Finset
      (Finset (Fin (n + m) → BitString) × Finset (Fin n → BitString)))
      (S : List BitString × List BitString), Inv H S →
      Inv ((Q.map pkey).foldl pstep H)
        ((Q.map ckey).foldl
          (theorem5_extended_decoder_computable_codeStep
            t) S) := by
    intro Q
    induction Q with
    | nil =>
        intro H S hInv
        simpa using hInv
    | cons q Q ih =>
        intro H S hInv
        simpa only [List.map_cons, List.foldl_cons] using
          ih (pstep H (pkey q))
            (theorem5_extended_decoder_computable_codeStep
              t S (ckey q))
            (hOneStep H S q hInv)
  have hInitial : Inv (∅ : Finset
      (Finset (Fin (n + m) → BitString) × Finset (Fin n → BitString))) ([], []) := by
    simp [Inv]
  have hFinal := hFoldInv Q ∅ ([], []) hInitial
  have hAccFold (S : List BitString × List BitString) :
      ((Q.map ckey).foldl
        theorem5_extended_decoder_computable_codeStepAcc
        (t, S)).2 =
      (Q.map ckey).foldl
        (theorem5_extended_decoder_computable_codeStep
          t) S := by
    induction Q generalizing S with
    | nil => rfl
    | cons q Q ih =>
        simpa only [List.map_cons, List.foldl_cons,
          theorem5_extended_decoder_computable_codeStepAcc,
          Prod.snd] using
          ih (theorem5_extended_decoder_computable_codeStep
            t S (ckey q))
  have hAccFinal := hAccFold (Prod.mk [] [])
  simp [theorem5_extended_decoder_computable_codeFunction,
    theorem5_extended_decoder_computable_codeFold,
    theorem5_extended_computable_decoder_decoderFunction,
    Q, t, pkey, ckey, pstep,
    hAccFinal, tupleSetCode, finsetListCode, hFinal.1, hFinal.2]

private theorem theorem5_extended_decoder_computable_codeCandidates_computable
    (n m : ℕ) :
    Computable fun w : BitString =>
      (decodeListCode (decodeFirst w)).map
        (theorem5_extended_decoder_computable_codeKey
          n m) := by
  have hLeft : Computable fun q : BitString =>
      decodeListCode (theorem5_extended_stochastic_model_mapCode
        (n + m) (decodeFirst q)) :=
    decodeListCode_computable.comp
      ((theorem5_extended_stochastic_model_mapCode_computable (n + m)).comp
        decodeFirst_computable)
  have hRight : Computable fun q : BitString =>
      decodeListCode (theorem5_extended_stochastic_model_mapCode
        n (decodeSecond q)) :=
    decodeListCode_computable.comp
      ((theorem5_extended_stochastic_model_mapCode_computable n).comp
        decodeSecond_computable)
  have hKey : Computable
      (theorem5_extended_decoder_computable_codeKey
        n m) := hLeft.pair hRight
  exact Computable.list_map
      (decodeListCode_computable.comp decodeFirst_computable)
      (hKey.comp Computable.snd).to₂

private theorem theorem5_extended_decoder_computable_codeFold_candidates_computable
    (n m : ℕ) :
    Computable fun w : BitString =>
      ((decodeListCode (decodeFirst w)).map
        (theorem5_extended_decoder_computable_codeKey n m)).foldl
        theorem5_extended_decoder_computable_codeStepAcc
        (bitsToNat (decodeSecond w), ([], [])) := by
  have hStep : Primrec₂
      theorem5_extended_decoder_computable_codeStepAcc :=
    theorem5_extended_decoder_computable_codeStepAcc_primrec
  have hCandidates :=
    theorem5_extended_decoder_computable_codeCandidates_computable n m
  have hInitial : Computable fun w : BitString =>
      (bitsToNat (decodeSecond w), ([], [])) :=
    (bitsToNat_primrec.to_comp.comp decodeSecond_computable).pair
      (Computable.const (([] : List BitString), ([] : List BitString)))
  have hStepPair : Computable fun z : BitString ×
      ((ℕ × (List BitString × List BitString)) ×
        (List BitString × List BitString)) =>
        theorem5_extended_decoder_computable_codeStepAcc z.2.1 z.2.2 :=
    hStep.to_comp.comp (Computable.fst.comp Computable.snd)
      (Computable.snd.comp Computable.snd)
  have hStepWrapped : Computable₂ fun (_w : BitString)
      (sp : (ℕ × (List BitString × List BitString)) ×
        (List BitString × List BitString)) =>
        theorem5_extended_decoder_computable_codeStepAcc sp.1 sp.2 :=
    Computable₂.mk hStepPair
  exact Computable.list_foldl
    (l := fun w : BitString =>
      (decodeListCode (decodeFirst w)).map
        (theorem5_extended_decoder_computable_codeKey n m))
    (g := fun w : BitString => (bitsToNat (decodeSecond w), ([], [])))
    (h := fun (_w : BitString)
      (sp : (ℕ × (List BitString × List BitString)) ×
        (List BitString × List BitString)) =>
          theorem5_extended_decoder_computable_codeStepAcc sp.1 sp.2)
    hCandidates hInitial hStepWrapped

private theorem theorem5_extended_decoder_computable_codeFold_computable
    (n m : ℕ) :
    Computable (theorem5_extended_decoder_computable_codeFold n m) := by
  exact (theorem5_extended_decoder_computable_codeFold_candidates_computable n m).of_eq
    fun _ => rfl

private theorem theorem5_extended_decoder_computable_codeOutput_computable :
    Computable fun p :
      ℕ × (List BitString × List BitString) =>
        (listCode (canonicalFinsetList p.2.1.toFinset),
          listCode (canonicalFinsetList p.2.2.toFinset)) := by
  have hfirst : Computable fun p : ℕ × (List BitString × List BitString) => p.2.1 :=
    Computable.fst.comp
      (Computable.snd : Computable fun p : ℕ × (List BitString × List BitString) => p.2)
  have hsecond : Computable fun p : ℕ × (List BitString × List BitString) => p.2.2 :=
    Computable.snd.comp
      (Computable.snd : Computable fun p : ℕ × (List BitString × List BitString) => p.2)
  have h1 := listCode_computable.comp
    (canonicalFinsetList_toFinset_primrec.to_comp.comp hfirst)
  have h2 := listCode_computable.comp
    (canonicalFinsetList_toFinset_primrec.to_comp.comp hsecond)
  exact h1.pair h2

private theorem theorem5_extended_decoder_computable_codeFunction_computable
    (n m : ℕ) :
    Computable
      (theorem5_extended_decoder_computable_codeFunction
        n m) := by
  have hFold :=
    theorem5_extended_decoder_computable_codeFold_computable
      n m
  have hOut :=
    theorem5_extended_decoder_computable_codeOutput_computable
  exact (hOut.comp hFold).of_eq fun w => by rfl

/-- The explicit parser and greedy fold form a total computable function on arbitrary
input strings. -/
private theorem theorem5_extended_decoder_computable
    (n m : ℕ) :
    Computable
      (theorem5_extended_computable_decoder_decoderFunction
        n m) := by
  exact (theorem5_extended_decoder_computable_codeFunction_computable n m).of_eq fun w =>
    theorem5_extended_decoder_computable_codeFunction_eq_decoderFunction n m w

/-- decoding a canonical tuple-set code recovers the original finite set. -/
private theorem theorem5_extended_tupleSet_roundtrip
    {n : ℕ} (A : Finset (Fin n → BitString)) :
    theorem5_extended_computable_decoder_decodeTupleSet
      n (tupleSetCode A) = A := by
  classical
  let C := A.image tupleCode
  let P : BitString → Prop := fun s =>
    theorem5_extended_stochastic_model_decodeTupleCode n s = s
  have hvalid : ∀ x : Fin n → BitString,
      theorem5_extended_stochastic_model_decodeTupleCode n (tupleCode x) = tupleCode x := by
    intro x
    simpa [theorem5_extended_stochastic_model_decodeTupleCode] using
      congrArg tupleCode (theorem5_extended_stochastic_model_decodeTuple_tupleCode n x)
  have hfilter : ((canonicalFinsetList C).filter fun s => decide (P s)).toFinset = C := by
    ext s
    simp only [List.mem_toFinset, List.mem_filter, mem_canonicalFinsetList]
    constructor
    · exact fun h => h.1
    · intro hs
      refine ⟨hs, ?_⟩
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hs
      simp [P, hvalid]
  have himage : C.image (theorem5_extended_stochastic_model_decodeTuple n) = A := by
    ext x
    constructor
    · intro hx
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hs
      simpa [theorem5_extended_stochastic_model_decodeTuple_tupleCode] using hy
    · intro hx
      refine Finset.mem_image.mpr ⟨tupleCode x, Finset.mem_image.mpr ⟨x, hx, rfl⟩, ?_⟩
      exact theorem5_extended_stochastic_model_decodeTuple_tupleCode n x
  unfold theorem5_extended_computable_decoder_decodeTupleSet
  simp only [tupleSetCode, finsetListCode, decodeListCode_listCode]
  rw [hfilter]
  exact himage

/-- The family code decodes, in canonical key order, to the same pairs as the selector's
key decoder. -/
private theorem theorem5_extended_family_list_roundtrip
    (n m : ℕ)
    (G : Finset (Finset (Fin (n + m) → BitString) × Finset (Fin n → BitString))) :
    (decodeListCode (theorem5_extended_special_union_familyCode G)).map
        (theorem5_extended_computable_decoder_decodeFamilyKey
          n m) =
      (canonicalFinsetList (G.image
        (theorem5_extended_selection_code_pairCode
          (n := n) (m := m)))).map
        (theorem5_extended_selection_code_decodeFamilyKey
          G) := by
  classical
  let key := theorem5_extended_selection_code_pairCode
    (n := n) (m := m)
  have hkey_inj : Function.Injective key := by
    simpa [key] using
      (theorem5_extended_pairCode_injective
        (n := n) (m := m))
  have hlist : decodeListCode (theorem5_extended_special_union_familyCode G) =
      canonicalFinsetList (G.image key) := by
    change decodeListCode (finsetListCode
      (G.image (fun p => pairCode (tupleSetCode p.1) (tupleSetCode p.2)))) = _
    have himage :
        G.image (fun p => pairCode (tupleSetCode p.1) (tupleSetCode p.2)) = G.image key := by
      apply Finset.image_congr
      intro p hp
      rfl
    simp only [finsetListCode, decodeListCode_listCode]
    rw [himage]
  rw [hlist]
  apply List.map_congr_left
  intro q hq
  have hqmem : q ∈ G.image key := mem_canonicalFinsetList.mp hq
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hqmem
  have hraw₁ := theorem5_extended_tupleSet_roundtrip
    (n := n + m) p.1
  have hraw₂ := theorem5_extended_tupleSet_roundtrip
    (n := n) p.2
  have hleft :
      theorem5_extended_computable_decoder_decodeFamilyKey
        n m (key p) = p := by
    cases p with
    | mk C B =>
      simp only [
        theorem5_extended_computable_decoder_decodeFamilyKey,
        key,
        theorem5_extended_selection_code_pairCode,
        decodeFirst_pairCode, decodeSecond_pairCode]
      rw [hraw₁, hraw₂]
  have hmem : key p ∈ G.image key := Finset.mem_image.mpr ⟨p, hp, rfl⟩
  have hchoose :
      theorem5_extended_selection_code_decodeFamilyKey
        G (key p) ∈ G ∧
      key (theorem5_extended_selection_code_decodeFamilyKey
        G (key p)) = key p := by
    unfold theorem5_extended_selection_code_decodeFamilyKey
    rw [dite_eq_left (by simpa [key] using hmem)]
    exact Classical.choose_spec (Finset.mem_image.mp hmem)
  have hright :
      theorem5_extended_selection_code_decodeFamilyKey
        G (key p) = p := hkey_inj hchoose.2
  exact hleft.trans hright.symm

/-- on a valid family code and threshold, the total decoder follows the defined greedy fold. -/
private theorem theorem5_extended_valid_input
    (n m : ℕ) :
    ∀ (G : Finset (Finset (Fin (n + m) → BitString) × Finset (Fin n → BitString)))
      (t : ℕ),
      theorem5_extended_computable_decoder_decoderFunction
          n m (pairCode (theorem5_extended_special_union_familyCode G) (Nat.bits t)) =
        (tupleSetCode
          ((theorem5_extended_selection_code_selected
            G t).biUnion fun p => p.1),
         tupleSetCode
          ((theorem5_extended_selection_code_selected
            G t).biUnion fun p => p.2)) := by
  intro G t
  classical
  have hL :=
    theorem5_extended_family_list_roundtrip
      n m G
  unfold theorem5_extended_computable_decoder_decoderFunction
  simp only [decodeFirst_pairCode, decodeSecond_pairCode, bitsToNat_bits]
  rw [hL]
  rfl

/-- The family code and binary threshold admit a computable decoder for the two selected
union codes. -/
private theorem theorem5_extended_computable_decoder
    (n m : ℕ) :
    ∃ f : BitString → BitString × BitString, Computable f ∧ ∀
      (G : Finset (Finset (Fin (n + m) → BitString) × Finset (Fin n → BitString)))
      (t : ℕ),
      f (pairCode (theorem5_extended_special_union_familyCode G) (Nat.bits t)) =
        (tupleSetCode
          ((theorem5_extended_selection_code_selected
            G t).biUnion fun p => p.1),
         tupleSetCode
          ((theorem5_extended_selection_code_selected
            G t).biUnion fun p => p.2)) := by
  refine ⟨
    theorem5_extended_computable_decoder_decoderFunction
      n m,
    theorem5_extended_decoder_computable
      n m,
    ?_⟩
  intro G t
  exact theorem5_extended_valid_input
    n m G t

/-- apply the computable decoder to the paired code to obtain constant-overhead descriptions of both
union codes. -/
private theorem theorem5_extended_paired_input_complexity
    (D : Map) (hD : isOptimalConditional D) (n m : ℕ) :
    ∃ cA : ℕ, ∃ cB : ℕ, ∀
      (G : Finset (Finset (Fin (n + m) → BitString) × Finset (Fin n → BitString)))
      (t : ℕ),
      natK D (tupleSetCode
        ((theorem5_extended_selection_code_selected
          G t).biUnion fun p => p.1)) ≤
          natK D (pairCode (theorem5_extended_special_union_familyCode G) (Nat.bits t)) + cA ∧
      natK D (tupleSetCode
        ((theorem5_extended_selection_code_selected
          G t).biUnion fun p => p.2)) ≤
          natK D (pairCode (theorem5_extended_special_union_familyCode G) (Nat.bits t)) +
              cB := by
  obtain ⟨f, hf, hDecode⟩ :=
    theorem5_extended_computable_decoder
      n m
  let fA : BitString → BitString := fun q => (f q).1
  let fB : BitString → BitString := fun q => (f q).2
  have hfA : Computable fA := Computable.fst.comp hf
  have hfB : Computable fB := Computable.snd.comp hf
  obtain ⟨cA, hA⟩ := plainK_map_le D hD fA hfA
  obtain ⟨cB, hB⟩ := plainK_map_le D hD fB hfB
  refine ⟨cA, cB, ?_⟩
  intro G t
  let Q := pairCode (theorem5_extended_special_union_familyCode G) (Nat.bits t)
  let A := tupleSetCode
    ((theorem5_extended_selection_code_selected
      G t).biUnion fun p => p.1)
  let B := tupleSetCode
    ((theorem5_extended_selection_code_selected
      G t).biUnion fun p => p.2)
  have hEq := hDecode G t
  have hARaw : plainK D A ≤ plainK D Q + (cA : ℕ∞) := by
    have h := hA Q
    change plainK D ((f Q).1) ≤ _ at h
    rw [show f Q = (A, B) from by simpa [Q, A, B] using hEq] at h
    simpa using h
  have hBRaw : plainK D B ≤ plainK D Q + (cB : ℕ∞) := by
    have h := hB Q
    change plainK D ((f Q).2) ≤ _ at h
    rw [show f Q = (A, B) from by simpa [Q, A, B] using hEq] at h
    simpa using h
  constructor
  · have h := hARaw
    rw [← ENat.natCast_toNat (plainK_ne_top D hD A),
      ← ENat.natCast_toNat (plainK_ne_top D hD Q)] at h
    exact_mod_cast h
  · have h := hBRaw
    rw [← ENat.natCast_toNat (plainK_ne_top D hD B),
      ← ENat.natCast_toNat (plainK_ne_top D hD Q)] at h
    exact_mod_cast h

/-- the two unions
produced by the explicit greedy selector are computable from the family code and the threshold. A
threshold bounded linearly by `N` therefore costs only logarithmic advice. -/
private theorem theorem5_extended_union_codes
    (D : Map) (hD : isOptimalConditional D) (n m b d : ℕ) :
    ∃ c₀ : ℕ, ∃ cCode : ℕ, ∀
      (G : Finset (Finset (Fin (n + m) → BitString) × Finset (Fin n → BitString)))
      (N t : ℕ),
      natK D (theorem5_extended_special_union_familyCode G) ≤ logSlack b N →
      t ≤ N + d →
      natK D (tupleSetCode ((theorem5_extended_selection_code_selected G t).biUnion
        fun p => p.1)) ≤ logSlack cCode N ∧
      natK D (tupleSetCode ((theorem5_extended_selection_code_selected G t).biUnion
        fun p => p.2)) ≤ logSlack c₀ N := by
  obtain ⟨cA, cB, hCode⟩ :=
    theorem5_extended_paired_input_complexity
      D hD n m
  obtain ⟨cPair, hPair⟩ := Kolmogorov.plainK_pair_le_add_logs D hD
  obtain ⟨cLen, hLen⟩ := Kolmogorov.plainK_le_length D hD
  obtain ⟨cFold, hFold⟩ := logSlack_linear_bound 1 1 d
  refine ⟨2 * b + 2 * cFold + cPair + 2 * cLen + cB,
    2 * b + 2 * cFold + cPair + 2 * cLen + cA, ?_⟩
  intro G N t hG ht
  let F := theorem5_extended_special_union_familyCode G
  let Q := pairCode F (Nat.bits t)
  have hQRaw : (natK D Q : ℕ∞) ≤
      (natK D F : ℕ∞) + (natK D (Nat.bits t) : ℕ∞) +
        ((Nat.log 2 (natK D F) + Nat.log 2 (natK D (Nat.bits t)) + cPair : ℕ) : ℕ∞) := by
    rw [show (natK D Q : ℕ∞) = plainK D Q from
      ENat.natCast_toNat (plainK_ne_top D hD Q)]
    calc
      plainK D Q ≤ Kolmogorov.cPair D F (Nat.bits t) := le_rfl
      _ ≤ plainK D F + plainK D (Nat.bits t) +
          ((Nat.log 2 (Kolmogorov.cVal D F) +
            Nat.log 2 (Kolmogorov.cVal D (Nat.bits t)) + cPair : ℕ) : ℕ∞) :=
          hPair F (Nat.bits t)
      _ = (natK D F : ℕ∞) + (natK D (Nat.bits t) : ℕ∞) +
          ((Nat.log 2 (natK D F) + Nat.log 2 (natK D (Nat.bits t)) + cPair : ℕ) : ℕ∞) := by
          rw [← ENat.natCast_toNat (plainK_ne_top D hD F),
            ← ENat.natCast_toNat (plainK_ne_top D hD (Nat.bits t))]
          simp [Kolmogorov.cVal, natK]
  have hQ : natK D Q ≤ natK D F + natK D (Nat.bits t) +
      Nat.log 2 (natK D F) + Nat.log 2 (natK D (Nat.bits t)) + cPair := by
    have hQ' : natK D Q ≤ natK D F + natK D (Nat.bits t) +
        (Nat.log 2 (natK D F) + Nat.log 2 (natK D (Nat.bits t)) + cPair) := by
      exact_mod_cast hQRaw
    omega
  have hLogF : Nat.log 2 (natK D F) ≤ natK D F := Nat.log_le_self 2 _
  have hLogT : Nat.log 2 (natK D (Nat.bits t)) ≤ natK D (Nat.bits t) :=
    Nat.log_le_self 2 _
  have hQsmall : natK D Q ≤ 2 * natK D F + 2 * natK D (Nat.bits t) + cPair := by
    omega
  have hTCode : natK D (Nat.bits t) ≤ (Nat.bits t).length + cLen := by
    have h := hLen (Nat.bits t)
    exact ENat.toNat_le_of_le_natCast (by simpa only [Nat.cast_add] using h)
  have hBitsFold : (Nat.bits t).length ≤ logSlack cFold N := by
    have hmono : (Nat.bits t).length ≤ (Nat.bits (N + d)).length :=
      Kolmogorov.length_natBits_mono ht
    have hSmall : (Nat.bits (N + d)).length ≤ logSlack 1 (N + d) := by
      unfold logSlack
      omega
    have hFoldN : logSlack 1 (N + d) ≤ logSlack cFold N := by
      simpa using hFold N
    exact hmono.trans (hSmall.trans hFoldN)
  have hQbound : natK D Q ≤
      2 * natK D F + 2 * (Nat.bits t).length + cPair + 2 * cLen := by
    calc
      natK D Q ≤ 2 * natK D F + 2 * natK D (Nat.bits t) + cPair := hQsmall
      _ ≤ 2 * natK D F + 2 * ((Nat.bits t).length + cLen) + cPair := by
        omega
      _ = 2 * natK D F + 2 * (Nat.bits t).length + cPair + 2 * cLen := by omega
  have hSlackA : 2 * logSlack b N + 2 * logSlack cFold N + cPair + 2 * cLen + cA ≤
      logSlack (2 * b + 2 * cFold + cPair + 2 * cLen + cA) N := by
    rw [logSlack_nsmul 2 b N, logSlack_nsmul 2 cFold N]
    rw [logSlack_add_const (2 * b) (2 * cFold) N]
    have h := logSlack_add_nat_le (2 * b + 2 * cFold) (cPair + 2 * cLen + cA) N
    simpa [Nat.add_assoc] using h
  have hSlackB : 2 * logSlack b N + 2 * logSlack cFold N + cPair + 2 * cLen + cB ≤
      logSlack (2 * b + 2 * cFold + cPair + 2 * cLen + cB) N := by
    rw [logSlack_nsmul 2 b N, logSlack_nsmul 2 cFold N]
    rw [logSlack_add_const (2 * b) (2 * cFold) N]
    have h := logSlack_add_nat_le (2 * b + 2 * cFold) (cPair + 2 * cLen + cB) N
    simpa [Nat.add_assoc] using h
  have hOutA := (hCode G t).1
  have hOutB := (hCode G t).2
  constructor
  · calc
      natK D (tupleSetCode
        ((theorem5_extended_selection_code_selected G t).biUnion
          fun p => p.1)) ≤ natK D Q + cA := by simpa [Q] using hOutA
      _ ≤ 2 * natK D F + 2 * (Nat.bits t).length + cPair + 2 * cLen + cA := by omega
      _ ≤ 2 * logSlack b N + 2 * logSlack cFold N + cPair + 2 * cLen + cA := by
        have hFam : natK D F ≤ logSlack b N := by simpa [F] using hG
        omega
      _ ≤ logSlack (2 * b + 2 * cFold + cPair + 2 * cLen + cA) N := hSlackA
  · calc
      natK D (tupleSetCode
        ((theorem5_extended_selection_code_selected G t).biUnion
          fun p => p.2)) ≤ natK D Q + cB := by simpa [Q] using hOutB
      _ ≤ 2 * natK D F + 2 * (Nat.bits t).length + cPair + 2 * cLen + cB := by omega
      _ ≤ 2 * logSlack b N + 2 * logSlack cFold N + cPair + 2 * cLen + cB := by
        have hFam : natK D F ≤ logSlack b N := by simpa [F] using hG
        omega
      _ ≤ logSlack (2 * b + 2 * cFold + cPair + 2 * cLen + cB) N := hSlackB

/-- the conditional
complexity threshold is bounded by the complexity of the whole encoded tuple up to a constant. -/
private theorem theorem5_extended_selection_code_threshold_bound
    (D : Map) (hD : isOptimalConditional D) (n m : ℕ) :
    ∃ c : ℕ, ∀ (x : Fin n → BitString) (z : BitString) (y : Fin m → BitString),
      natCondK D (tupleCode x) z ≤
        natK D (pairCode (tupleCode (Fin.append x y)) z) + c := by
  let extractX : BitString → BitString := fun w =>
    decodeFirst (theorem4_extended_chain_splitTuple n (decodeFirst w))
  have hExtractX : Computable extractX :=
    decodeFirst_computable.comp
      ((theorem4_extended_chain_splitTuple_computable n).comp decodeFirst_computable)
  obtain ⟨cMap, hMap⟩ := plainK_map_le D hD extractX hExtractX
  obtain ⟨cCond, hCond⟩ :=
    theorem5_extended_stochastic_model_condNat_bound D hD
  refine ⟨cMap + cCond, ?_⟩
  intro x z y
  let w := pairCode (tupleCode (Fin.append x y)) z
  have hExtract : extractX w = tupleCode x := by
    dsimp [extractX, w]
    rw [decodeFirst_pairCode, theorem4_extended_chain_splitTuple_correct,
      decodeFirst_pairCode]
  have hMapRaw := hMap w
  rw [hExtract] at hMapRaw
  have hMapNat : natK D (tupleCode x) ≤ natK D w + cMap := by
    rw [← ENat.natCast_toNat (plainK_ne_top D hD (tupleCode x)),
      ← ENat.natCast_toNat (plainK_ne_top D hD w)] at hMapRaw
    exact_mod_cast hMapRaw
  have hCond := hCond (tupleCode x) z
  have hMapNat' : natK D (tupleCode x) ≤
      natK D (pairCode (tupleCode (Fin.append x y)) z) + cMap := by
    simpa [w] using hMapNat
  omega

/-- the greedy selection, the count from its disjoint new parts, the uncovered-part bound, and the
complexity bounds for the two unions. -/
private theorem theorem5_extended_selection_code
    (D : Map) (hD : isOptimalConditional D) (n m a b : ℕ) :
    ∃ c₀ : ℕ, ∀ k : ℕ, ∃ cCode : ℕ, ∀ (x : Fin n → BitString) (z : BitString)
      (S : Finset (Fin n → BitString)) (y : Fin m → BitString) (κ : ℕ)
      (A₀ : Finset (Fin (n + m) → BitString)) (B₀ : Finset (Fin n → BitString))
      (G : Finset (Finset (Fin (n + m) → BitString) × Finset (Fin n → BitString))),
      S.card ≤ 2 ^ (natK D (tupleCode x) + logSlack a (natK D (tupleCode x))) →
      (A₀, B₀) ∈ G →
      (∀ p ∈ G, p.2 ⊆ S) →
      (∀ p ∈ G, ∀ V W : Finset (Fin (n + m)), V.Nonempty → Disjoint V W →
        combEnt p.1 V W ≤ combEnt A₀ V W) →
      natK D (theorem5_extended_special_union_familyCode G) ≤
        logSlack b (natK D (pairCode (tupleCode (Fin.append x y)) z)) →
      (∀ p ∈ G, ∀ u ∈ p.1, ∀ i : Fin m,
        (u (Fin.natAdd n i)).length ≤ natK D (pairCode (tupleCode (Fin.append x y)) z)) →
      (∀ p ∈ G, ∀ x' ∈ p.2,
        (theorem5_extended_special_union_section p.1 x').Nonempty ∧
        κ ≤ Nat.log2 (theorem5_extended_special_union_section p.1 x').card +
          logSlack b (natK D (pairCode (tupleCode (Fin.append x y)) z))) →
      ∃ H : Finset
          (Finset (Fin (n + m) → BitString) × Finset (Fin n → BitString)),
        ∃ A : Finset (Fin (n + m) → BitString), ∃ B : Finset (Fin n → BitString),
          H ⊆ G ∧
          A = H.biUnion (fun p => p.1) ∧
          B = H.biUnion (fun p => p.2) ∧
          H.card * 2 ^ (natCondK D (tupleCode x) z -
            logSlack k (natK D (pairCode (tupleCode (Fin.append x y)) z))) ≤ S.card ∧
          natK D (tupleSetCode A) ≤
            logSlack cCode (natK D (pairCode (tupleCode (Fin.append x y)) z)) ∧
          natK D (tupleSetCode B) ≤
            logSlack (c₀ + 2 * Nat.log2 (k + 1))
              (natK D (pairCode (tupleCode (Fin.append x y)) z)) ∧
          (B₀ \ B).card <
            2 ^ (natCondK D (tupleCode x) z -
              logSlack k (natK D (pairCode (tupleCode (Fin.append x y)) z))) := by
  obtain ⟨cThreshold, hThreshold⟩ :=
    theorem5_extended_selection_code_threshold_bound
      D hD n m
  obtain ⟨c₀, cCode, hCodes⟩ :=
    theorem5_extended_union_codes
      D hD n m b cThreshold
  refine ⟨c₀, ?_⟩
  intro k
  refine ⟨cCode, ?_⟩
  intro x z S y κ A₀ B₀ G hSCard hA₀G hGS hGEnt hGCode hGLen hGSec
  let N := natK D (pairCode (tupleCode (Fin.append x y)) z)
  let t := natCondK D (tupleCode x) z - logSlack k N
  have ht : t ≤ N + cThreshold := by
    dsimp [t, N]
    exact (Nat.sub_le _ _).trans (hThreshold x z y)
  have hCodes' := hCodes G N t (by simpa [N] using hGCode) ht
  let H := theorem5_extended_selection_code_selected G
      t
  let A := H.biUnion fun p => p.1
  let B := H.biUnion fun p => p.2
  have hGreedy :=
    theorem5_extended_greedy_packing_coverage
      G S B₀ (A₀, B₀) t hA₀G rfl hGS
  rcases hGreedy with ⟨hHSub, hCard, hUncCard⟩
  have hAUnion : A = H.biUnion (fun p => p.1) := rfl
  have hBUnion : B = H.biUnion (fun p => p.2) := rfl
  refine ⟨H, A, B, hHSub, hAUnion, hBUnion, ?_, ?_, ?_, ?_⟩
  · simpa [t, N] using hCard
  · simpa [A, H, N] using hCodes'.1
  · have hCodeB : natK D (tupleSetCode B) ≤ logSlack c₀ N := by
      simpa [B, H] using hCodes'.2
    exact hCodeB.trans (logSlack_mono_left (by omega) N)
  · simpa [B, t, N] using hUncCard

/-- the packing and size
bounds control the logarithm of the number of selected pieces. -/
private theorem theorem5_extended_packing
    (a k cProj cCond : ℕ) :
    ∃ c : ℕ, ∀ (P Q N s M : ℕ),
      P ≤ N + cProj → Q ≤ P + cCond →
      s ≤ 2 ^ (P + logSlack a P) →
      M * 2 ^ (Q - logSlack k N) ≤ s →
      (Nat.clog 2 M : ℤ) ≤ (P : ℤ) - Q + logSlack c N := by
  obtain ⟨cFold, hFold⟩ := logSlack_linear_bound a 1 cProj
  let c := max cCond (cFold + k + 1)
  refine ⟨c, ?_⟩
  intro P Q N s M hP hQ hS hPack
  let t := Q - logSlack k N
  let r := P + logSlack a P
  have hSlackA : logSlack a P ≤ logSlack cFold N := by
    calc
      logSlack a P ≤ logSlack a (N + cProj) := logSlack_mono_right a hP
      _ ≤ logSlack cFold N := by simpa using hFold N
  have hPow : M * 2 ^ t ≤ 2 ^ r := by
    dsimp [t, r]
    exact le_trans hPack hS
  have hResult : (Nat.clog 2 M : ℤ) ≤ (P : ℤ) - Q + logSlack c N := by
    by_cases hM : M = 0
    · simp [hM]
      have hc : cCond ≤ c := by dsimp [c]; omega
      have hSlack : cCond ≤ logSlack c N := by
        unfold logSlack
        omega
      omega
    · have hMpos : 1 ≤ M := Nat.one_le_iff_ne_zero.mpr hM
      have htPow : 2 ^ t ≤ M * 2 ^ t := by
        calc
          2 ^ t = 1 * 2 ^ t := by simp
          _ ≤ M * 2 ^ t := Nat.mul_le_mul_right _ hMpos
      have ht : t ≤ r :=
        (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (htPow.trans hPow)
      have hFactor : 2 ^ r = 2 ^ (r - t) * 2 ^ t := by
        rw [← Nat.pow_add, Nat.sub_add_cancel ht]
      have hMpow : M ≤ 2 ^ (r - t) := by
        rw [hFactor] at hPow
        exact (Nat.le_of_mul_le_mul_right hPow) (by positivity)
      have hLog : Nat.clog 2 M ≤ r - t := Nat.clog_le_of_le_pow hMpow
      have htQ : t + (Q - t) = Q := by
        dsimp [t]
        omega
      have hSlackQ : Q - t ≤ logSlack k N := by
        dsimp [t]
        omega
      have hNat : Nat.clog 2 M + Q ≤ P + logSlack cFold N + logSlack k N := by
        have hLog' : Nat.clog 2 M + t ≤ r := by
          calc
            Nat.clog 2 M + t ≤ (r - t) + t := Nat.add_le_add_right hLog t
            _ = r := Nat.sub_add_cancel ht
        have hLog'' : Nat.clog 2 M + t ≤ P + logSlack cFold N := by
          exact hLog'.trans (Nat.add_le_add_left hSlackA P)
        omega
      have hSlackSum : logSlack cFold N + logSlack k N =
          logSlack (cFold + k) N := logSlack_add_const _ _ _
      have hc : cFold + k ≤ c := by dsimp [c]; omega
      have hSlack : logSlack (cFold + k) N ≤ logSlack c N :=
        logSlack_mono_left hc N
      have hInt : (Nat.clog 2 M : ℤ) + Q ≤
          P + logSlack c N := by
        have hNat' : Nat.clog 2 M + Q ≤ P + logSlack (cFold + k) N := by
          have hSlack' : logSlack cFold N + logSlack k N ≤
              logSlack (cFold + k) N := by rw [hSlackSum]
          omega
        exact_mod_cast hNat'.trans (Nat.add_le_add_left hSlack P)
      omega
  exact hResult

/-- a union of at most
`H.card` correct sets increases each combinatorial entropy by at most `clog 2 H.card`. -/
private theorem theorem5_extended_union
    {n m : ℕ}
    (A₀ : Finset (Fin (n + m) → BitString))
    (H : Finset (Finset (Fin (n + m) → BitString) × Finset (Fin n → BitString)))
    (A : Finset (Fin (n + m) → BitString))
    (hA : A = H.biUnion (fun p => p.1))
    (hCorrect : ∀ p ∈ H, ∀ V W : Finset (Fin (n + m)), V.Nonempty → Disjoint V W →
      combEnt p.1 V W ≤ combEnt A₀ V W)
    (V W : Finset (Fin (n + m))) (hV : V.Nonempty) (hdis : Disjoint V W) :
    combEnt A V W ≤ combEnt A₀ V W + Nat.clog 2 H.card := by
  classical
  let e := combEnt A₀ V W
  have hpiece : ∀ p ∈ H, ∀ u : Fin (n + m) → BitString,
      (sectionProjection p.1 V W u).card ≤ 2 ^ e := by
    intro p hp u
    by_cases hne : (sectionProjection p.1 V W u).Nonempty
    · obtain ⟨q, hq⟩ := hne
      unfold sectionProjection at hq
      obtain ⟨v, hv, _⟩ := Finset.mem_image.mp hq
      have hv' := Finset.mem_filter.mp hv
      have heq : sectionProjection p.1 V W u = sectionProjection p.1 V W v := by
        ext q
        simp only [sectionProjection, Finset.mem_image, Finset.mem_filter]
        constructor
        · rintro ⟨w, ⟨hw, hwu⟩, rfl⟩
          exact ⟨w, ⟨hw, hwu.trans hv'.2.symm⟩, rfl⟩
        · rintro ⟨w, ⟨hw, hwv⟩, rfl⟩
          exact ⟨w, ⟨hw, hwv.trans hv'.2⟩, rfl⟩
      have hsup : (sectionProjection p.1 V W v).card ≤ maxSectionCard p.1 V W :=
        Finset.le_sup (f := fun w => (sectionProjection p.1 V W w).card) hv'.1
      have hent := hCorrect p hp V W hV hdis
      have hpow' : maxSectionCard p.1 V W ≤
          2 ^ Nat.clog 2 (maxSectionCard p.1 V W) :=
        Nat.le_pow_clog (by decide : 1 < 2) _
      have hpow'' : 2 ^ Nat.clog 2 (maxSectionCard p.1 V W) ≤ 2 ^ e :=
        Nat.pow_le_pow_right (by decide : 0 < 2) hent
      rw [heq]
      exact hsup.trans (hpow'.trans hpow'')
    · have hempty : sectionProjection p.1 V W u = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hne
      simp [hempty]
  have hsection (u : Fin (n + m) → BitString) :
      sectionProjection A V W u = H.biUnion (fun p => sectionProjection p.1 V W u) := by
    ext q
    constructor
    · intro h
      unfold sectionProjection at h
      obtain ⟨v, hv, hVeq⟩ := Finset.mem_image.mp h
      obtain ⟨hvA, hW⟩ := Finset.mem_filter.mp hv
      have hvA' : v ∈ H.biUnion (fun p => p.1) := by
        rw [← hA]
        exact hvA
      obtain ⟨p, hp, hvP⟩ := Finset.mem_biUnion.mp hvA'
      apply Finset.mem_biUnion.mpr
      refine ⟨p, hp, ?_⟩
      unfold sectionProjection
      apply Finset.mem_image.mpr
      exact ⟨v, Finset.mem_filter.mpr ⟨hvP, hW⟩, hVeq⟩
    · intro h
      obtain ⟨p, hp, hv⟩ := Finset.mem_biUnion.mp h
      unfold sectionProjection at hv
      obtain ⟨v, hv, hVeq⟩ := Finset.mem_image.mp hv
      obtain ⟨hvP, hW⟩ := Finset.mem_filter.mp hv
      unfold sectionProjection
      apply Finset.mem_image.mpr
      refine ⟨v, Finset.mem_filter.mpr ?_, hVeq⟩
      constructor
      · rw [hA]
        exact Finset.mem_biUnion.mpr ⟨p, hp, hvP⟩
      · exact hW
  have hcard (u : Fin (n + m) → BitString) :
      (sectionProjection A V W u).card ≤ H.card * 2 ^ e := by
    rw [hsection]
    calc
      (H.biUnion fun p => sectionProjection p.1 V W u).card ≤
          ∑ p ∈ H, (sectionProjection p.1 V W u).card := Finset.card_biUnion_le
      _ ≤ ∑ _p ∈ H, 2 ^ e := by
        apply Finset.sum_le_sum
        intro p hp
        exact hpiece p hp u
      _ = H.card * 2 ^ e := by simp
  have hmax : maxSectionCard A V W ≤ H.card * 2 ^ e := by
    unfold maxSectionCard
    apply Finset.sup_le
    intro u hu
    exact hcard u
  have hpowH : H.card ≤ 2 ^ Nat.clog 2 H.card :=
    Nat.le_pow_clog (by decide : 1 < 2) _
  have hpow : H.card * 2 ^ e ≤ 2 ^ (e + Nat.clog 2 H.card) := by
    rw [Nat.pow_add]
    calc
      H.card * 2 ^ e ≤ 2 ^ Nat.clog 2 H.card * 2 ^ e :=
        Nat.mul_le_mul_right _ hpowH
      _ = 2 ^ e * 2 ^ Nat.clog 2 H.card := Nat.mul_comm _ _
  have hent : Nat.clog 2 (maxSectionCard A V W) ≤ e + Nat.clog 2 H.card :=
    Nat.clog_le_of_le_pow (hmax.trans hpow)
  simpa [combEnt, e, Nat.add_comm] using hent

/-- Remark 3's entropy estimate.  A union of correct sets indexed by `H` has at most
`H.card` pieces;
the disjoint new-part count bounds this number, and hence the entropy increase, by the information
in `x̄` about `z` plus the threshold slack. -/
private theorem theorem5_extended_greedy_union_entropy
    (D : Map) (hD : isOptimalConditional D) (n m a k : ℕ) :
    ∃ cEnt : ℕ, ∀ (x : Fin n → BitString) (z : BitString)
      (S : Finset (Fin n → BitString)) (y : Fin m → BitString) (_κ : ℕ)
      (A₀ : Finset (Fin (n + m) → BitString)) (G : Finset
        (Finset (Fin (n + m) → BitString) × Finset (Fin n → BitString)))
      (H : Finset (Finset (Fin (n + m) → BitString) × Finset (Fin n → BitString)))
      (A : Finset (Fin (n + m) → BitString)),
      S.card ≤ 2 ^ (natK D (tupleCode x) + logSlack a (natK D (tupleCode x))) →
      (∀ p ∈ G, p.2 ⊆ S) →
      (∀ p ∈ G, ∀ V W : Finset (Fin (n + m)), V.Nonempty → Disjoint V W →
        combEnt p.1 V W ≤ combEnt A₀ V W) →
      H ⊆ G → A = H.biUnion (fun p => p.1) →
      H.card * 2 ^ (natCondK D (tupleCode x) z -
        logSlack k (natK D (pairCode (tupleCode (Fin.append x y)) z))) ≤ S.card →
      ∀ V W : Finset (Fin (n + m)), V.Nonempty → Disjoint V W →
        (combEnt A V W : ℤ) ≤ (combEnt A₀ V W : ℤ) +
          ((natK D (tupleCode x) : ℤ) - natCondK D (tupleCode x) z) +
          logSlack cEnt (natK D (pairCode (tupleCode (Fin.append x y)) z)) := by
  classical
  let extractX : BitString → BitString := fun w =>
    decodeFirst (theorem4_extended_chain_splitTuple n (decodeFirst w))
  have hExtractX : Computable extractX :=
    decodeFirst_computable.comp
      ((theorem4_extended_chain_splitTuple_computable n).comp decodeFirst_computable)
  obtain ⟨cProj, hProj⟩ := plainK_map_le D hD extractX hExtractX
  obtain ⟨cCond, hCond⟩ := theorem5_extended_stochastic_model_condNat_bound D hD
  obtain ⟨cEnt, hPacking⟩ :=
    theorem5_extended_packing
      a k cProj cCond
  refine ⟨cEnt, ?_⟩
  intro x z S y _κ A₀ G H A hS hGS hGEnt hHSub hAUnion hHCard V W hV hdis
  let P := natK D (tupleCode x)
  let Q := natCondK D (tupleCode x) z
  let N := natK D (pairCode (tupleCode (Fin.append x y)) z)
  have hExtract : extractX (pairCode (tupleCode (Fin.append x y)) z) = tupleCode x := by
    dsimp [extractX]
    rw [decodeFirst_pairCode, theorem4_extended_chain_splitTuple_correct,
      decodeFirst_pairCode]
  have hProjRaw := hProj (pairCode (tupleCode (Fin.append x y)) z)
  rw [hExtract] at hProjRaw
  rw [← ENat.natCast_toNat (plainK_ne_top D hD (tupleCode x)),
    ← ENat.natCast_toNat
      (plainK_ne_top D hD (pairCode (tupleCode (Fin.append x y)) z))] at hProjRaw
  have hP : P ≤ N + cProj := by exact_mod_cast hProjRaw
  have hQ : Q ≤ P + cCond := by
    simpa [P, Q] using hCond (tupleCode x) z
  have hCount := hPacking P Q N S.card H.card hP hQ hS hHCard
  have hUnion :=
    theorem5_extended_union
      A₀ H A hAUnion (by
        intro p hp V' W' hV' hdis'
        exact hGEnt p (hHSub hp) V' W' hV' hdis') V W hV hdis
  have hUnionZ : (combEnt A V W : ℤ) ≤
      (combEnt A₀ V W : ℤ) + (Nat.clog 2 H.card : ℤ) := by exact_mod_cast hUnion
  dsimp [P, Q, N] at hCount
  omega

/-- (Remark 3) the greedy selection of the special correct sets and their union.  The
hypotheses on `A₀, B₀, G` are the properties given by
`theorem5_extended_special_union_correct_family` that the selection uses (`b` bounds its
constant, and `κ` is an arbitrary number standing for `K(ȳ° | x̄, z)`).

Write `N = K(⟨x̄, ȳ⟩, z)`, `L = log N + 1` (so `logSlack c N = c·L`) and
`t = K(x̄ | z) - k·L` (truncated subtraction; `k` is a free threshold constant).  Process the pairs
`(C, B_C)` of `G` in the order of the canonical list in `familyCode G`; a pair is *special* if
`B_C` minus the union of the `B`'s of the earlier special pairs has at least `2^t` elements.  Let
`A` be the union of the special `C`'s and `B` the union of the special `B_C`'s.  Then:
* `A` and `B` are computed from `familyCode G` and the number `t ≤ K(x̄ | z) ≤ N + O(1)`, so
  `K(list A) = O(L)` and `K(list B) = O(L)`; the constant `c₀` in the bound on `K(list B)` does not
  depend on `k` (the bound even allows an extra `2 log₂(k + 1)·L`);
* the new parts of the special `B_C`'s are disjoint subsets of `S` with at least `2^t` elements
  each, so the number `M` of special pairs satisfies `M ≤ |S| / 2^t`, i.e.
  `log M ≤ K(x̄) - K(x̄ | z) + k·L + logSlack a (K x̄)`, and `logSlack a (K x̄) = O(L)` as
  `K(x̄) ≤ N + O(1)`; every `V`-projection of a `W`-section of `A` is the union of at most `M` such
  projections for correct sets, each of size `≤ 2^(ent_{V|W}(A₀))`, so
  `ent_{V|W}(A) ≤ ent_{V|W}(A₀) + log M + 1` (if no pair is special then `A = ∅`, and the bound
  holds because `K(x̄ | z) ≤ K(x̄) + O(1)`);
* `|B₀ \ B| < 2^t`: either `(A₀, B₀)` is special and `B₀ ⊆ B`, or the new part of `B₀` at its
  turn, which contains `B₀ \ B`, has fewer than `2^t` elements;
* the elements of `A` keep the bound `≤ N` on the lengths of their `ȳ`-components, and every
  `x̄' ∈ B` lies in `B_C` for some special pair, with `C ⊆ A`, so the section of `A` over `x̄'`
  contains that of `C` and inherits the section bounds. -/
private theorem theorem5_extended_greedy_union
    (D : Map) (hD : isOptimalConditional D) (n m a b : ℕ) :
    ∃ c₀ : ℕ, ∀ k : ℕ, ∃ c₁ : ℕ, ∀ (x : Fin n → BitString) (z : BitString)
      (S : Finset (Fin n → BitString)) (y : Fin m → BitString) (κ : ℕ)
      (A₀ : Finset (Fin (n + m) → BitString)) (B₀ : Finset (Fin n → BitString))
      (G : Finset (Finset (Fin (n + m) → BitString) × Finset (Fin n → BitString))),
      S.card ≤ 2 ^ (natK D (tupleCode x) + logSlack a (natK D (tupleCode x))) →
      (A₀, B₀) ∈ G →
      (∀ p ∈ G, p.2 ⊆ S) →
      (∀ p ∈ G, ∀ V W : Finset (Fin (n + m)), V.Nonempty → Disjoint V W →
        combEnt p.1 V W ≤ combEnt A₀ V W) →
      natK D (theorem5_extended_special_union_familyCode G) ≤
        logSlack b (natK D (pairCode (tupleCode (Fin.append x y)) z)) →
      (∀ p ∈ G, ∀ u ∈ p.1, ∀ i : Fin m,
        (u (Fin.natAdd n i)).length ≤ natK D (pairCode (tupleCode (Fin.append x y)) z)) →
      (∀ p ∈ G, ∀ x' ∈ p.2,
        (theorem5_extended_special_union_section p.1 x').Nonempty ∧
        κ ≤
          Nat.log2 (theorem5_extended_special_union_section p.1 x').card +
            logSlack b (natK D (pairCode (tupleCode (Fin.append x y)) z))) →
      ∃ A : Finset (Fin (n + m) → BitString), ∃ B : Finset (Fin n → BitString),
        natK D (tupleSetCode A) ≤
          logSlack c₁ (natK D (pairCode (tupleCode (Fin.append x y)) z)) ∧
        (∀ V W : Finset (Fin (n + m)), V.Nonempty → Disjoint V W →
          (combEnt A V W : ℤ) ≤
            (combEnt A₀ V W : ℤ) +
              ((natK D (tupleCode x) : ℤ) - natCondK D (tupleCode x) z) +
              logSlack c₁ (natK D (pairCode (tupleCode (Fin.append x y)) z))) ∧
        natK D (tupleSetCode B) ≤
          logSlack (c₀ + 2 * Nat.log2 (k + 1))
            (natK D (pairCode (tupleCode (Fin.append x y)) z)) ∧
        (B₀ \ B).card <
          2 ^ (natCondK D (tupleCode x) z -
            logSlack k (natK D (pairCode (tupleCode (Fin.append x y)) z))) ∧
        (∀ u ∈ A, ∀ i : Fin m,
          (u (Fin.natAdd n i)).length ≤ natK D (pairCode (tupleCode (Fin.append x y)) z)) ∧
        (∀ x' ∈ B,
          (theorem5_extended_special_union_section A x').Nonempty ∧
          κ ≤
            Nat.log2 (theorem5_extended_special_union_section A x').card +
              logSlack b (natK D (pairCode (tupleCode (Fin.append x y)) z))) := by
  classical
  obtain ⟨c₀, hSelection⟩ :=
    theorem5_extended_selection_code
      D hD n m a b
  refine ⟨c₀, ?_⟩
  intro k
  obtain ⟨cCode, hCode⟩ := hSelection k
  obtain ⟨cEnt, hEntropy⟩ :=
    theorem5_extended_greedy_union_entropy
      D hD n m a k
  let c₁ := max cCode cEnt
  refine ⟨c₁, ?_⟩
  intro x z S y κ A₀ B₀ G hSCard hA₀G hGS hGEnt hGCode hGLen hGSec
  obtain ⟨H, A, B, hHSub, hAUnion, hBUnion, hHCard, hACode, hBCode, hUncCard⟩ :=
    hCode x z S y κ A₀ B₀ G hSCard hA₀G hGS hGEnt hGCode hGLen hGSec
  have hEnt := hEntropy x z S y κ A₀ G H A hSCard hGS hGEnt hHSub hAUnion hHCard
  refine ⟨A, B, ?_, ?_, ?_, hUncCard, ?_, ?_⟩
  · exact hACode.trans (logSlack_mono_left (by dsimp [c₁]; omega) _)
  · intro V W hV hdis
    have hEnt' := hEnt V W hV hdis
    have hSlack : logSlack cEnt
        (natK D (pairCode (tupleCode (Fin.append x y)) z)) ≤
        logSlack c₁ (natK D (pairCode (tupleCode (Fin.append x y)) z)) := by
      exact logSlack_mono_left (by dsimp [c₁]; omega) _
    have hSlackInt : (logSlack cEnt
        (natK D (pairCode (tupleCode (Fin.append x y)) z)) : ℤ) ≤
        logSlack c₁ (natK D (pairCode (tupleCode (Fin.append x y)) z)) := by
      exact_mod_cast hSlack
    omega
  · exact hBCode
  · intro u hu i
    rw [hAUnion] at hu
    obtain ⟨p, hp, hup⟩ := Finset.mem_biUnion.mp hu
    exact hGLen p (hHSub hp) u hup i
  · intro x' hx'
    rw [hBUnion] at hx'
    obtain ⟨p, hp, hxp⟩ := Finset.mem_biUnion.mp hx'
    have hpG : p ∈ G := hHSub hp
    obtain ⟨hne, hsec⟩ := hGSec p hpG x' hxp
    have hSubSection : theorem5_extended_special_union_section p.1 x' ⊆
        theorem5_extended_special_union_section A x' := by
      intro y' hy'
      rw [theorem5_extended_special_union_mem_section] at hy' ⊢
      rw [hAUnion]
      exact Finset.mem_biUnion.mpr ⟨p, hp, hy'⟩
    have hCardSection := Finset.card_le_card hSubSection
    have hlog : Nat.log2
        (theorem5_extended_special_union_section p.1 x').card ≤
        Nat.log2 (theorem5_extended_special_union_section A x').card := by
      rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
      exact Nat.log_mono_right hCardSection
    exact ⟨(Finset.Nonempty.mono hSubSection hne), by omega⟩

/-- Arithmetic for the choice of the threshold constant `k`: for every `c₀, e`
there is `k` with `s + 2 log₂(s+1) + e < t` for `s = logSlack (c₀ + 2 log₂(k+1)) N` and
`t = logSlack k N`, uniformly in `N`. -/
private lemma theorem5_extended_special_union_pick_k (c₀ e : ℕ) :
    ∃ k : ℕ, ∀ N : ℕ,
      logSlack (c₀ + 2 * Nat.log2 (k + 1)) N +
          2 * Nat.log2 (logSlack (c₀ + 2 * Nat.log2 (k + 1)) N + 1) + e <
        logSlack k N := by
  set j := 3 * c₀ + e + 16 with hj
  have hpow : 8 * (j - 3 + 1) ≤ 2 ^ j := by
    have h1 : j - 3 < 2 ^ (j - 3) := Nat.lt_two_pow_self
    have h2 : (2 : ℕ) ^ j = 8 * 2 ^ (j - 3) := by
      rw [show j = (j - 3) + 3 by omega, pow_add]
      simp [mul_comm]
    omega
  refine ⟨2 ^ j - 1, fun N => ?_⟩
  have hk1 : 2 ^ j - 1 + 1 = 2 ^ j := by
    have : 0 < 2 ^ j := Nat.two_pow_pos j
    omega
  rw [hk1, Nat.log2_two_pow]
  set d := c₀ + 2 * j with hd
  set L := (Nat.bits N).length + 1 with hL
  have hLpos : 1 ≤ L := by omega
  have hslack : ∀ c : ℕ, logSlack c N = c * L := by
    intro c; unfold logSlack; rw [hL]; ring
  rw [hslack, hslack]
  have hlog : Nat.log2 (d * L + 1) ≤ d * L + 1 := by
    have := Nat.lt_two_pow_self (n := d * L + 1)
    exact ((Nat.log2_lt (by omega)).mpr this).le
  have hk : 3 * d + e + 3 ≤ 2 ^ j - 1 := by
    omega
  have hmul : (3 * d + e + 3) * L ≤ (2 ^ j - 1) * L := Nat.mul_le_mul_right _ hk
  nlinarith

/-- Given a simple model `S` containing `x̄` with `|S| ≤ 2^(K(x̄) + O(log N₀))`, the union
`Â` of the
special correct sets (correct sets of the extended profile `K'(x̄, ȳ | z)` inside
`S × (B^N)^m`, selected greedily by the size `2^(K(x̄|z) - C₂ log N)` of the new part of their
strong projections) is a simple set of `(n+m)`-tuples: `K(list Â) = O(log N)`; its combinatorial
entropies satisfy `ent_{V|W}(Â) ≤ K(x̄_V ȳ_V | x̄_W ȳ_W, z) + (K(x̄) - K(x̄ | z)) + O(log N)`
(Remark 3; the number of special correct sets is at most `|S| / 2^(K(x̄|z) - C₂ log N)`); and
(Lemma 7) the section `Q` of `Â` over `x̄` is nonempty with `K(ȳ | x̄, z) ≤ log |Q| + O(log N)`,
its elements being `m`-tuples of strings of length at most `N = K(x̄, ȳ, z)`.  (If `ȳ` itself has
long components it is first replaced by the tuple of shortest programs, which changes the
profile by `O(log N)`.) -/
private theorem theorem5_extended_special_union (D : Map)
    (hD : isOptimalConditional D) (n m a : ℕ) :
    ∃ c : ℕ, ∀ (x : Fin n → BitString) (z : BitString)
      (S : Finset (Fin n → BitString)),
      x ∈ S →
      natK D (tupleSetCode S) ≤ logSlack a (natK D (tupleCode x)) →
      S.card ≤ 2 ^ (natK D (tupleCode x) + logSlack a (natK D (tupleCode x))) →
      ∀ y : Fin m → BitString,
        ∃ A : Finset (Fin (n + m) → BitString), ∃ Q : Finset (Fin m → BitString),
          natK D (tupleSetCode A) ≤
            logSlack c (natK D (pairCode (tupleCode (Fin.append x y)) z)) ∧
          (∀ V W : Finset (Fin (n + m)), V.Nonempty → Disjoint V W →
            (combEnt A V W : ℤ) ≤
              subCondKRel D (Fin.append x y) z V W +
                ((natK D (tupleCode x) : ℤ) - natCondK D (tupleCode x) z) +
                logSlack c (natK D (pairCode (tupleCode (Fin.append x y)) z))) ∧
          Q.Nonempty ∧
          (∀ y' ∈ Q, Fin.append x y' ∈ A) ∧
          natCondK D (tupleCode y) (pairCode (tupleCode x) z) ≤
            Nat.log2 Q.card +
              logSlack c (natK D (pairCode (tupleCode (Fin.append x y)) z)) ∧
          (∀ y' ∈ Q, ∀ i : Fin m,
            (y' i).length ≤ natK D (pairCode (tupleCode (Fin.append x y)) z)) := by
  obtain ⟨cY, hY⟩ := theorem5_extended_short_programs D hD n m
  obtain ⟨cF, hF⟩ := theorem5_extended_special_union_correct_family D hD n m a
  obtain ⟨c₀, hGreedy⟩ :=
    theorem5_extended_greedy_union D hD n m a cF
  obtain ⟨k, hk⟩ := theorem5_extended_special_union_pick_k (c₀ + cF) 0
  obtain ⟨c₁, hG1⟩ := hGreedy k
  refine ⟨cF + c₁ + cY, ?_⟩
  intro x z S hxS hSCode hSCard y
  obtain ⟨y₀, hy₀Len, hy₀Prof, hy₀Cond⟩ := hY x z y
  obtain ⟨A₀, B₀, G, hA₀G, hxB₀, hGS, hGEnt, hA₀Ent, hGCode, hEnum, hGLen, hGSec⟩ :=
    hF x z S hxS hSCode hSCard y y₀ hy₀Len
  obtain ⟨A, B, hACode, hAEnt, hBCode, hUncCard, hALen, hBSec⟩ :=
    hG1 x z S y (natCondK D (tupleCode y₀) (pairCode (tupleCode x) z)) A₀ B₀ G hSCard hA₀G
      hGS hGEnt hGCode hGLen hGSec
  set N := natK D (pairCode (tupleCode (Fin.append x y)) z) with hN
  -- Lemma 7: `x̄` lies in the union `B` of the special strong projections.
  have hxB : x ∈ B := by
    by_contra hxB
    have hE := hEnum B hxB
    have hmem : x ∈ B₀ \ B := Finset.mem_sdiff.mpr ⟨hxB₀, hxB⟩
    have hpos : (B₀ \ B).card ≠ 0 := (Finset.card_pos.mpr ⟨x, hmem⟩).ne'
    have hlog : Nat.log2 (B₀ \ B).card < natCondK D (tupleCode x) z - logSlack k N :=
      (Nat.log2_lt hpos).mpr hUncCard
    have hsum : logSlack (c₀ + 2 * Nat.log2 (k + 1)) N + logSlack cF N =
        logSlack (c₀ + cF + 2 * Nat.log2 (k + 1)) N := by
      rw [logSlack_add_const]
      congr 1
      omega
    have hss : natK D (tupleSetCode B) + logSlack cF N ≤
        logSlack (c₀ + cF + 2 * Nat.log2 (k + 1)) N := by
      omega
    have hlogmono : Nat.log2 (natK D (tupleSetCode B) + 1) ≤
        Nat.log2 (logSlack (c₀ + cF + 2 * Nat.log2 (k + 1)) N + 1) := by
      rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
      exact Nat.log_mono_right (by omega)
    have hkN := hk N
    omega
  obtain ⟨hQne, hQK⟩ := hBSec x hxB
  have hslack3 : logSlack cF N + logSlack c₁ N + logSlack cY N =
      logSlack (cF + c₁ + cY) N := by
    rw [logSlack_add_const, logSlack_add_const]
  have hcY : cY ≤ logSlack cY N := by
    unfold logSlack
    omega
  refine ⟨A, theorem5_extended_special_union_section A x, ?_, ?_, hQne, ?_, ?_, ?_⟩
  · exact hACode.trans (logSlack_mono_left (by omega) _)
  · intro V W hV hdis
    have h1 := hA₀Ent V W hV hdis
    have h2 := hAEnt V W hV hdis
    have h3 := hy₀Prof V W hV hdis
    have h3' : (subCondKRel D (Fin.append x y₀) z V W : ℤ) ≤
        subCondKRel D (Fin.append x y) z V W + logSlack cY N := by
      exact_mod_cast h3
    have hslack : (logSlack cF N : ℤ) + logSlack c₁ N + logSlack cY N =
        logSlack (cF + c₁ + cY) N := by
      exact_mod_cast hslack3
    omega
  · intro y' hy'
    exact (theorem5_extended_special_union_mem_section A x y').mp hy'
  · omega
  · intro y' hy' i
    have hu := (theorem5_extended_special_union_mem_section A x y').mp hy'
    have := hALen _ hu i
    simpa [Fin.append_right] using this

/-- Lemma 4 and the second half of Remark 3 imply every
element `ū` of a finite set `A` of tuples satisfies
`K(ū_V | ū_W) ≤ ent_{V|W}(A) + 2 K(list A) + O(1)`; this is `lemma4` (which bounds
`K(ū_V | ū_W, list A)`) together with `K(u | w) ≤ K(u | w, l) + 2 K(l) + O(1)`
(`condK_le_condK_pair_add_two_plainK`, after commuting the pair). -/
private theorem theorem5_extended_element_profile (D : Map)
    (hD : isOptimalConditional D) (k : ℕ) :
    ∃ c : ℕ, ∀ (A : Finset (Fin k → BitString)) (u : Fin k → BitString), u ∈ A →
      ∀ V W : Finset (Fin k),
        subCondK D u V W ≤ combEnt A V W + 2 * natK D (tupleSetCode A) + c := by
  obtain ⟨cLemma, hLemma⟩ := lemma4 D hD k
  let swapPair : BitString → BitString := fun p => pairCode (decodeSecond p) (decodeFirst p)
  have hSwap : Computable swapPair := by
    have h : swapPair = (fun p : BitString × BitString => pairCode p.1 p.2) ∘
        (fun p : BitString => (decodeSecond p, decodeFirst p)) := by
      funext p
      rfl
    rw [h]
    exact pairCode_computable.comp (decodeSecond_computable.pair decodeFirst_computable)
  obtain ⟨cSwap, hSwap⟩ := condK_cond_map_le D hD swapPair hSwap
  obtain ⟨cDrop, hDrop⟩ := condK_le_condK_pair_add_two_plainK D hD
  refine ⟨cLemma + cSwap + cDrop, ?_⟩
  intro A u hu V W
  let a := subtupleCode u V
  let b := subtupleCode u W
  let l := tupleSetCode A
  have hSwapEq : swapPair (pairCode l b) = pairCode b l := by
    simp [swapPair, decodeFirst_pairCode, decodeSecond_pairCode]
  have hSwapNat : natCondK D a (pairCode l b) ≤ natCondK D a (pairCode b l) + cSwap := by
    apply theorem4_extended_condK_toNat_le_same_condition D hD a (pairCode l b) (pairCode b l) cSwap
    simpa only [hSwapEq] using hSwap a (pairCode l b)
  have hDropNat : natCondK D a b ≤ natCondK D a (pairCode l b) +
      (2 * natK D l + cDrop) := by
    apply theorem4_extended_condK_toNat_le_same_condition D hD a b (pairCode l b)
      (2 * natK D l + cDrop)
    simpa [natK, Kolmogorov.cVal] using hDrop a l b
  have hL := hLemma A u hu V W
  change natCondK D a b ≤ combEnt A V W + 2 * natK D l + (cLemma + cSwap + cDrop)
  dsimp [a, b, l] at hSwapNat hDropNat hL ⊢
  omega

/-- Under the stated complexity and cardinality bounds on `S`, there is a nonempty set `Q` of
tuples whose conditional complexity is bounded by `log₂ |Q| + O(log N)` and whose entries have
length at most `N`. Every `y' ∈ Q` satisfies the one-sided profile bound in terms of `y`, `z`,
and the complexity difference between `x` and `x` conditioned on `z`. -/
theorem theorem5_extended_aggregate_section (D : Map)
    (hD : isOptimalConditional D) (n m a : ℕ) :
    ∃ c : ℕ, ∀ (x : Fin n → BitString) (z : BitString)
      (S : Finset (Fin n → BitString)),
      x ∈ S →
      natK D (tupleSetCode S) ≤ logSlack a (natK D (tupleCode x)) →
      S.card ≤ 2 ^ (natK D (tupleCode x) + logSlack a (natK D (tupleCode x))) →
      ∀ y : Fin m → BitString,
        ∃ Q : Finset (Fin m → BitString),
          Q.Nonempty ∧
          natCondK D (tupleCode y) (pairCode (tupleCode x) z) ≤
            Nat.log2 Q.card +
              logSlack c (natK D (pairCode (tupleCode (Fin.append x y)) z)) ∧
          (∀ y' ∈ Q, ∀ i : Fin m,
            (y' i).length ≤ natK D (pairCode (tupleCode (Fin.append x y)) z)) ∧
          ∀ y' ∈ Q, ∀ V W : Finset (Fin (n + m)), V.Nonempty → Disjoint V W →
            (subCondK D (Fin.append x y') V W : ℤ) ≤
              subCondKRel D (Fin.append x y) z V W +
                ((natK D (tupleCode x) : ℤ) - natCondK D (tupleCode x) z) +
                logSlack c (natK D (pairCode (tupleCode (Fin.append x y)) z)) := by
  obtain ⟨c1, h1⟩ := theorem5_extended_special_union D hD n m a
  obtain ⟨cE, hE⟩ := theorem5_extended_element_profile D hD (n + m)
  refine ⟨c1 + 2 * c1 + cE, ?_⟩
  intro x z S hxS hSc hSCard y
  obtain ⟨A, Q, hAc, hEnt, hQne, hQA, hQK, hQlen⟩ := h1 x z S hxS hSc hSCard y
  refine ⟨Q, hQne, ?_, hQlen, ?_⟩
  · refine hQK.trans (Nat.add_le_add_left ?_ _)
    exact logSlack_mono_left (by omega) _
  · intro y' hy' V W hV hdis
    have hel := hE A _ (hQA y' hy') V W
    have he := hEnt V W hV hdis
    set N := natK D (pairCode (tupleCode (Fin.append x y)) z)
    have hs : (logSlack c1 N : ℤ) + 2 * logSlack c1 N + cE ≤
        logSlack (c1 + 2 * c1 + cE) N := by
      unfold logSlack
      push_cast
      nlinarith [Nat.zero_le (Nat.bits N).length]
    have hel' : (subCondK D (Fin.append x y') V W : ℤ) ≤
        combEnt A V W + 2 * logSlack c1 N + cE := by
      have : (subCondK D (Fin.append x y') V W : ℤ) ≤
          combEnt A V W + 2 * natK D (tupleSetCode A) + cE := by exact_mod_cast hel
      have h2 : (natK D (tupleSetCode A) : ℤ) ≤ logSlack c1 N := by exact_mod_cast hAc
      omega
    omega

end Kolmogorov.Relativization
