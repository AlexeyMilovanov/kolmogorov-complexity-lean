/-
Copyright (c) 2026 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Relativization.Typization.TypizationSize

/-!
# Clone Majority

This module proves the majority-clone conclusion of Lemma 2 for typizations under
relativization. It establishes complexity bounds for tuple partitions and derives stability of
extended profiles, formalizing Lemma 2 of Muchnik and Romashchenko.
-/

namespace Kolmogorov.Relativization
open Finset
variable {n m : ℕ}

/-- If the typization has the lower cardinality
bound from Lemma 1, then more than half of it consists of tuples whose conditional complexity
is at least the reference value minus `s + 1`. -/
private theorem lemma2_half_conditional_complexity
    (D : Map) (hD : isOptimalConditional D) (n m : ℕ)
    (x : Fin n → BitString) (y : Fin m → BitString) (k s : ℕ)
    (hT : (typization D x y).Finite)
    (hcard : 2 ^ k ≤ (typization D x y).ncard * 2 ^ s) :
    let H : Set (Fin n → BitString) :=
      {x' | x' ∈ typization D x y ∧
        k ≤ natCondK D (tupleCode x') (tupleCode y) + (s + 1)}
    H.Finite ∧ (typization D x y).ncard < 2 * H.ncard := by
  classical
  let H : Set (Fin n → BitString) :=
    {x' | x' ∈ typization D x y ∧
      k ≤ natCondK D (tupleCode x') (tupleCode y) + (s + 1)}
  let B : Set (Fin n → BitString) := typization D x y \ H
  let q := k - (s + 1)
  have hHsub : H ⊆ typization D x y := by
    intro x' hx'
    exact hx'.1
  have hHfin : H.Finite := hT.subset hHsub
  have hBfin : B.Finite := hT.subset (by
    intro x' hx'
    have hxparts : x' ∈ typization D x y ∧ x' ∉ H := by
      simpa only [B, Set.mem_sdiff] using hx'
    exact hxparts.1)
  have hdiff : B.ncard = (typization D x y).ncard - H.ncard := by
    dsimp [B]
    exact Set.ncard_sdiff hHsub hHfin
  have hBcard : B.ncard < 2 ^ q := by
    by_cases hq : q = 0
    · have hBempty : B = ∅ := by
        ext x'
        simp [B, H]
        omega
      simp [hBempty, hq]
    · have hqpos : 0 < q := Nat.pos_of_ne_zero hq
      let A : Finset BitString := hBfin.toFinset.image tupleCode
      have hcode_inj : Function.Injective (tupleCode : (Fin n → BitString) → BitString) := by
        intro x₁ x₂ hcode
        change listCode (List.ofFn x₁) = listCode (List.ofFn x₂) at hcode
        apply List.ofFn_injective
        exact listCode_injective hcode
      have hAcard : A.card = B.ncard := by
        calc
          A.card = (hBfin.toFinset.image tupleCode).card := rfl
          _ = hBfin.toFinset.card := Finset.card_image_iff.mpr (by
            intro x₁ hx₁ x₂ hx₂ hcode
            exact hcode_inj hcode)
          _ = B.ncard := (Set.ncard_eq_toFinset_card B hBfin).symm
      have hAcomplex : ∀ z ∈ A,
          condK D z (tupleCode y) ≤ ((q - 1 : ℕ) : ℕ∞) := by
        intro z hz
        rcases Finset.mem_image.mp hz with ⟨x', hx', rfl⟩
        have hx'B : x' ∈ B := hBfin.mem_toFinset.mp hx'
        have hxparts : x' ∈ typization D x y ∧ x' ∉ H := by
          simpa only [B, Set.mem_sdiff] using hx'B
        have hnotH : x' ∉ H := hxparts.2
        have hnot : ¬ k ≤ natCondK D (tupleCode x') (tupleCode y) + (s + 1) := by
          intro hbound
          exact hnotH ⟨hxparts.1, hbound⟩
        have hlow : natCondK D (tupleCode x') (tupleCode y) < q := by
          dsimp [q]
          omega
        have hne : condK D (tupleCode x') (tupleCode y) ≠ ⊤ := by
          obtain ⟨cLit, hLit⟩ := Kolmogorov.plainK_le_length D hD
          obtain ⟨cCond, hCond⟩ := Kolmogorov.condK_le_plainK D hD
          apply ne_top_of_le_natCast
          calc
            condK D (tupleCode x') (tupleCode y) ≤
                plainK D (tupleCode x') + cCond := hCond _ _
            _ ≤ (programLength (tupleCode x') : ℕ∞) + cLit + cCond := by
              gcongr
              exact hLit _
            _ = ((programLength (tupleCode x') + cLit + cCond : ℕ) : ℕ∞) := by
              push_cast
              ring
        have hEq : ((natCondK D (tupleCode x') (tupleCode y) : ℕ) : ℕ∞) =
            condK D (tupleCode x') (tupleCode y) := ENat.natCast_toNat hne
        rw [← hEq]
        exact_mod_cast (show natCondK D (tupleCode x') (tupleCode y) ≤ q - 1 by omega)
      have hAbound :=
        Kolmogorov.card_condK_le_boundedPrograms_length D (tupleCode y) (q - 1) A hAcomplex
      have hA_lt : A.card < 2 ^ q := by
        calc
          A.card ≤ (boundedPrograms (q - 1)).length := hAbound
          _ < 2 ^ ((q - 1) + 1) := length_boundedPrograms_lt (q - 1)
          _ = 2 ^ q := by congr 1; omega
      rw [hAcard] at hA_lt
      exact hA_lt
  have h2B_lt : 2 * B.ncard < (typization D x y).ncard := by
    by_cases hq : q = 0
    · have hBempty : B = ∅ := by
        ext x'
        simp [B, H]
        omega
      have hTpos : 0 < (typization D x y).ncard := by
        by_contra hnot
        have hz : (typization D x y).ncard = 0 := Nat.eq_zero_of_not_pos hnot
        rw [hz] at hcard
        simp at hcard
      rw [hBempty] at hdiff
      simp at hdiff
      simp [hBempty]
      omega
    · have hqpos : 0 < q := Nat.pos_of_ne_zero hq
      have hk : k = q + (s + 1) := by
        dsimp [q]
        omega
      have hpow_eq : 2 ^ (q + 1) * 2 ^ s = 2 ^ k := by
        calc
          2 ^ (q + 1) * 2 ^ s = 2 ^ q * 2 * 2 ^ s := by rw [Nat.pow_succ]
          _ = 2 ^ q * (2 ^ s * 2) := by ring
          _ = 2 ^ q * 2 ^ (s + 1) := by rw [Nat.pow_succ]
          _ = 2 ^ (q + (s + 1)) := (Nat.pow_add 2 q (s + 1)).symm
          _ = 2 ^ k := by rw [hk]
      have hpow_le : 2 ^ (q + 1) ≤ (typization D x y).ncard := by
        have hmul : 2 ^ (q + 1) * 2 ^ s ≤ (typization D x y).ncard * 2 ^ s := by
          rw [hpow_eq]
          exact hcard
        exact Nat.le_of_mul_le_mul_right hmul (Nat.pow_pos (by decide : 0 < 2))
      calc
        2 * B.ncard < 2 * (2 ^ q) :=
          Nat.mul_lt_mul_of_pos_left hBcard (by decide : 0 < 2)
        _ = 2 ^ (q + 1) := by rw [Nat.pow_succ]; ring
        _ ≤ (typization D x y).ncard := hpow_le
  have hfinal : (typization D x y).ncard < 2 * H.ncard := by
    omega
  exact ⟨hHfin, hfinal⟩

private def lemma2_total_complexity_lower_bound_joinPair
    (w : BitString) : BitString :=
  listCode (decodeListCode (decodeSecond w) ++ decodeListCode (decodeFirst w))

private theorem lemma2_total_complexity_lower_bound_joinPair_computable :
    Computable lemma2_total_complexity_lower_bound_joinPair := by
  unfold lemma2_total_complexity_lower_bound_joinPair
  exact listCode_computable.comp
    (Computable₂.comp Primrec.list_append.to_comp
      (decodeListCode_computable.comp decodeSecond_computable)
      (decodeListCode_computable.comp decodeFirst_computable))

private theorem lemma2_total_complexity_lower_bound_joinPair_correct
    {n m : ℕ} (x : Fin n → BitString) (y : Fin m → BitString) :
    lemma2_total_complexity_lower_bound_joinPair
        (pairCode (tupleCode y) (tupleCode x)) = tupleCode (Fin.append x y) := by
  simp only [lemma2_total_complexity_lower_bound_joinPair,
    decodeFirst_pairCode, decodeSecond_pairCode, tupleCode, decodeListCode_listCode,
    List.ofFn_fin_append]

private def lemma2_total_complexity_lower_bound_splitPair
    (n : ℕ) (w : BitString) : BitString :=
  pairCode (listCode ((decodeListCode w).drop n))
    (listCode ((decodeListCode w).take n))

private theorem lemma2_total_complexity_lower_bound_splitPair_computable
    (n : ℕ) :
    Computable (lemma2_total_complexity_lower_bound_splitPair n) := by
  change Computable (fun w : BitString =>
    pairCode (listCode ((decodeListCode w).drop n))
      (listCode ((decodeListCode w).take n)))
  have hTake : Primrec (fun w : BitString =>
      listCode ((decodeListCode w).take n)) :=
    Kolmogorov.listCode_primrec.comp
      (Primrec.list_take.comp (Primrec.const n) decodeListCode_primrec)
  have hDrop : Primrec (fun w : BitString =>
      listCode ((decodeListCode w).drop n)) :=
    Kolmogorov.listCode_primrec.comp
      (Primrec.list_drop.comp (Primrec.const n) decodeListCode_primrec)
  exact (CodedFiniteDistribution.pairCode_primrec.comp hDrop hTake).to_comp

private theorem lemma2_total_complexity_lower_bound_splitPair_correct
    {n m : ℕ} (x : Fin n → BitString) (y : Fin m → BitString) :
    lemma2_total_complexity_lower_bound_splitPair n
        (tupleCode (Fin.append x y)) = pairCode (tupleCode y) (tupleCode x) := by
  unfold lemma2_total_complexity_lower_bound_splitPair
  rw [show decodeListCode (tupleCode (Fin.append x y)) =
      List.ofFn (Fin.append x y) by simp [tupleCode], List.ofFn_fin_append]
  change pairCode (listCode ((List.ofFn x ++ List.ofFn y).drop n))
      (listCode ((List.ofFn x ++ List.ofFn y).take n)) =
    pairCode (listCode (List.ofFn y)) (listCode (List.ofFn x))
  have hlen : (List.ofFn x).length = n := by simp
  rw [List.drop_append_of_le_length hlen.symm.le,
    List.take_append_of_le_length hlen.symm.le]
  have hdrop : (List.ofFn x).drop n = [] := by
    apply List.drop_eq_nil_of_le
    omega
  have htake : (List.ofFn x).take n = List.ofFn x :=
    List.take_of_length_le (by omega)
  rw [htake, hdrop, List.nil_append]

/-- The
conditional-complexity lower bound, together with the typization bound on the whole tuple, gives
a lower bound on the primed whole-tuple complexity up to logarithmic slack. This is the total
complexity comparison used before applying Lemma 3. -/
private theorem lemma2_total_complexity_lower_bound
    (D : Map) (hD : isOptimalConditional D) (n m c : ℕ) :
    ∃ d : ℕ, ∀ (x : Fin n → BitString) (y : Fin m → BitString)
      (x' : Fin n → BitString),
      x' ∈ typization D x y →
      natCondK D (tupleCode x) (tupleCode y) ≤
        natCondK D (tupleCode x') (tupleCode y) +
          (logSlack c (natK D (tupleCode (Fin.append x y))) + 1) →
      natK D (tupleCode (Fin.append x y)) ≤
        natK D (tupleCode (Fin.append x' y)) +
          logSlack d (natK D (tupleCode (Fin.append x y))) := by
  obtain ⟨cPair, hPair⟩ := Kolmogorov.pairPlainK_symmetryOfInformation_values D hD
  obtain ⟨cJoin, hJoin⟩ := plainK_map_le D hD
    lemma2_total_complexity_lower_bound_joinPair
    lemma2_total_complexity_lower_bound_joinPair_computable
  obtain ⟨cSplit, hSplit⟩ := plainK_map_le D hD
    (lemma2_total_complexity_lower_bound_splitPair n)
    (lemma2_total_complexity_lower_bound_splitPair_computable n)
  obtain ⟨cSlack, hSlack⟩ := logSlack_absorb_of_le_linear cPair 1 (cSplit + 1)
  refine ⟨c + cSlack + cSlack + (cJoin + cSplit + 1), ?_⟩
  intro x y x' hx hcond
  change ExtProfileLe D (Fin.append x' y) (Fin.append x y) at hx
  let N := natK D (tupleCode (Fin.append x y))
  let N' := natK D (tupleCode (Fin.append x' y))
  let a := tupleCode y
  let b := tupleCode x
  let b' := tupleCode x'
  let p := pairCode a b
  let p' := pairCode a b'
  by_cases hzero : n + m = 0
  · have hn : n = 0 := by omega
    have hm : m = 0 := by omega
    subst n
    subst m
    have hEq : x' = x := by
      funext i
      exact Fin.elim0 i
    subst x'
    exact Nat.le_add_right _ _
  · have hpos : 0 < n + m := Nat.pos_of_ne_zero hzero
    have hUniv : (Finset.univ : Finset (Fin (n + m))).Nonempty := by
      refine ⟨⟨0, hpos⟩, Finset.mem_univ _⟩
    have hwhole : N' ≤ N := by
      have h := hx Finset.univ ∅ hUniv (Finset.disjoint_empty_right _)
      change natCondK D (subtupleCode (Fin.append x' y) Finset.univ)
          (subtupleCode (Fin.append x' y) ∅) ≤
        natCondK D (subtupleCode (Fin.append x y) Finset.univ)
          (subtupleCode (Fin.append x y) ∅) at h
      rw [subtupleCode_univ, subtupleCode_empty,
        subtupleCode_univ, subtupleCode_empty] at h
      change natK D (tupleCode (Fin.append x' y)) ≤ natK D (tupleCode (Fin.append x y))
      exact h
    have hJoinRaw := hJoin p
    rw [show lemma2_total_complexity_lower_bound_joinPair p =
        tupleCode (Fin.append x y) by simp [p, a, b,
          lemma2_total_complexity_lower_bound_joinPair_correct]] at hJoinRaw
    have hSplitRaw := hSplit (tupleCode (Fin.append x y))
    rw [lemma2_total_complexity_lower_bound_splitPair_correct x y] at hSplitRaw
    have hSplitRaw' := hSplit (tupleCode (Fin.append x' y))
    rw [lemma2_total_complexity_lower_bound_splitPair_correct x' y] at hSplitRaw'
    have hNfinite : plainK D (tupleCode (Fin.append x y)) ≠ ⊤ :=
      plainK_ne_top D hD _
    have hN'finite : plainK D (tupleCode (Fin.append x' y)) ≠ ⊤ :=
      plainK_ne_top D hD _
    have hpfinite : plainK D p ≠ ⊤ := plainK_ne_top D hD p
    have hp'finite : plainK D p' ≠ ⊤ := plainK_ne_top D hD p'
    have hJoinNat : N ≤ natK D p + cJoin := by
      change plainK D (tupleCode (Fin.append x y)) ≤ plainK D p + (cJoin : ℕ∞) at hJoinRaw
      rw [← ENat.natCast_toNat hNfinite, ← ENat.natCast_toNat hpfinite] at hJoinRaw
      change (plainK D (tupleCode (Fin.append x y))).toNat ≤ (plainK D p).toNat + cJoin
      exact_mod_cast hJoinRaw
    have hSplitNat : natK D p ≤ N + cSplit := by
      change plainK D p ≤ plainK D (tupleCode (Fin.append x y)) + (cSplit : ℕ∞) at hSplitRaw
      rw [← ENat.natCast_toNat hpfinite, ← ENat.natCast_toNat hNfinite] at hSplitRaw
      change (plainK D p).toNat ≤ (plainK D (tupleCode (Fin.append x y))).toNat + cSplit
      exact_mod_cast hSplitRaw
    have hSplitNat' : natK D p' ≤ N' + cSplit := by
      change plainK D p' ≤ plainK D (tupleCode (Fin.append x' y)) + (cSplit : ℕ∞) at hSplitRaw'
      rw [← ENat.natCast_toNat hp'finite, ← ENat.natCast_toNat hN'finite] at hSplitRaw'
      change (plainK D p').toNat ≤ (plainK D (tupleCode (Fin.append x' y))).toNat + cSplit
      exact_mod_cast hSplitRaw'
    have haVal : Kolmogorov.HasPlainComplexityValue D a (natK D a) := by
      change plainK D a = ((plainK D a).toNat : ℕ∞)
      exact (ENat.natCast_toNat (plainK_ne_top D hD a)).symm
    have hbVal : Kolmogorov.HasPlainConditionalComplexityValue D b a (natCondK D b a) := by
      change condK D b a = ((condK D b a).toNat : ℕ∞)
      exact (ENat.natCast_toNat (avgCond_condK_ne_top D hD b a)).symm
    have hb'Val : Kolmogorov.HasPlainConditionalComplexityValue D b' a (natCondK D b' a) := by
      change condK D b' a = ((condK D b' a).toNat : ℕ∞)
      exact (ENat.natCast_toNat (avgCond_condK_ne_top D hD b' a)).symm
    have hpVal : Kolmogorov.HasPlainComplexityValue D p (natK D p) := by
      change plainK D p = ((plainK D p).toNat : ℕ∞)
      exact (ENat.natCast_toNat hpfinite).symm
    have hp'Val : Kolmogorov.HasPlainComplexityValue D p' (natK D p') := by
      change plainK D p' = ((plainK D p').toNat : ℕ∞)
      exact (ENat.natCast_toNat hp'finite).symm
    have hsym := hPair a b (natK D a) (natCondK D b a) (natK D p) haVal hbVal hpVal
    have hsym' := hPair a b' (natK D a) (natCondK D b' a) (natK D p') haVal hb'Val hp'Val
    have harg : natK D p + 1 ≤ N + (cSplit + 1) := by omega
    have harg' : natK D p' + 1 ≤ N + (cSplit + 1) := by omega
    have hlog : logSlack cPair (natK D p + 1) ≤ logSlack cSlack N :=
      hSlack N _ (by simpa using harg)
    have hlog' : logSlack cPair (natK D p' + 1) ≤ logSlack cSlack N :=
      hSlack N _ (by simpa using harg')
    have hForward : natK D p ≤ natK D a + natCondK D b a + logSlack cSlack N := by
      calc
        natK D p ≤ natK D a + natCondK D b a + logSlack cPair (natK D p + 1) := hsym.1
        _ ≤ natK D a + natCondK D b a + logSlack cSlack N := by omega
    have hBackward : natK D a + natCondK D b' a ≤
        natK D p' + logSlack cSlack N := by
      calc
        natK D a + natCondK D b' a ≤
            natK D p' + logSlack cPair (natK D p' + 1) := hsym'.2
        _ ≤ natK D p' + logSlack cSlack N := by omega
    have hmain : N ≤ N' + (logSlack c N + 1 + cJoin + cSplit +
        logSlack cSlack N + logSlack cSlack N) := by
      dsimp [N, N', a, b, b', p, p'] at hcond hJoinNat hSplitNat hSplitNat' hwhole ⊢
      have hForward' : natK D (pairCode (tupleCode y) (tupleCode x)) ≤
          natK D (tupleCode y) + natCondK D (tupleCode x) (tupleCode y) +
            logSlack cSlack (natK D (tupleCode (Fin.append x y))) := by
        simpa [a, b, p, N] using hForward
      have hBackward' : natK D (tupleCode y) + natCondK D (tupleCode x') (tupleCode y) ≤
          natK D (pairCode (tupleCode y) (tupleCode x')) +
            logSlack cSlack (natK D (tupleCode (Fin.append x y))) := by
        simpa [a, b', p', N] using hBackward
      omega
    have hA : cJoin + cSplit + 1 ≤ logSlack (cJoin + cSplit + 1) N := by
      unfold logSlack
      omega
    have hLogCombine : logSlack c N + logSlack cSlack N + logSlack cSlack N =
        logSlack (c + cSlack + cSlack) N := by
      rw [logSlack_add_const c cSlack N, logSlack_add_const (c + cSlack) cSlack N]
    have hErr : logSlack c N + 1 + cJoin + cSplit +
        logSlack cSlack N + logSlack cSlack N ≤
        logSlack (c + cSlack + cSlack + (cJoin + cSplit + 1)) N := by
      calc
        _ = (logSlack c N + logSlack cSlack N + logSlack cSlack N) +
              (cJoin + cSplit + 1) := by omega
        _ = logSlack (c + cSlack + cSlack) N + (cJoin + cSplit + 1) := by rw [hLogCombine]
        _ ≤ logSlack (c + cSlack + cSlack) N + logSlack (cJoin + cSplit + 1) N :=
          Nat.add_le_add_left hA _
        _ = logSlack (c + cSlack + cSlack + (cJoin + cSplit + 1)) N :=
          logSlack_add_const _ _ _
    exact hmain.trans (Nat.add_le_add_left hErr _)

/-- A
`lemma2_partition_recode`:
a subtuple code computably projects to the code of any fixed subset of its coordinates. -/
private theorem lemma2_projection
    {k : ℕ} (S T : Finset (Fin k)) (hTS : T ⊆ S) :
    ∃ f : BitString → BitString, Computable f ∧
      ∀ u : Fin k → BitString, f (subtupleCode u S) = subtupleCode u T := by
  classical
  let positions := (T.sort (· ≤ ·)).map fun i => (S.sort (· ≤ ·)).idxOf i
  let f : BitString → BitString := fun w =>
    listCode (positions.map fun i => (decodeListCode w).getD i [])
  have hMap : Primrec (fun w : BitString =>
      positions.map fun i => (decodeListCode w).getD i []) := by
    induction positions with
    | nil => exact Primrec.const []
    | cons i positions ih =>
      have hget : Primrec (fun w : BitString => (decodeListCode w).getD i []) :=
        (Primrec.list_getD ([] : BitString)).comp decodeListCode_primrec (Primrec.const i)
      exact Primrec.list_cons.comp hget ih
  refine ⟨f, listCode_computable.comp hMap.to_comp, ?_⟩
  intro u
  dsimp [f, positions]
  unfold subtupleCode
  simp only [decodeListCode_listCode, List.map_map]
  apply congrArg listCode
  apply List.map_congr_left
  intro i hi
  have hiT : i ∈ T := by simpa using hi
  have hiS : i ∈ S := hTS hiT
  have hiSort : i ∈ S.sort (· ≤ ·) := by simpa
  simp [Function.comp_apply, List.getD_eq_getElem?_getD, List.getElem?_idxOf hiSort]

/-- The
`lemma2_partition_recode`:
if two fixed blocks cover an index set, their paired subtuple codes computably merge into its
subtuple code, by taking each coordinate from the first block that contains it. -/
private theorem lemma2_merge
    {k : ℕ} (T A B : Finset (Fin k)) (hcover : A ∪ B = T) :
    ∃ f : BitString → BitString, Computable f ∧
      ∀ u : Fin k → BitString,
        f (pairCode (subtupleCode u A) (subtupleCode u B)) = subtupleCode u T := by
  classical
  let f : BitString → BitString := fun w =>
    listCode ((T.sort (· ≤ ·)).map fun i =>
      if i ∈ A then
        (decodeListCode (decodeFirst w)).getD ((A.sort (· ≤ ·)).idxOf i) []
      else
        (decodeListCode (decodeSecond w)).getD ((B.sort (· ≤ ·)).idxOf i) [])
  let positions := T.sort (· ≤ ·)
  let decodeA : BitString → List BitString := decodeListCode ∘ decodeFirst
  let decodeB : BitString → List BitString := decodeListCode ∘ decodeSecond
  have hDecodeA : Primrec decodeA :=
    decodeListCode_primrec.comp CodedFiniteDistribution.decodeFirst_primrec
  have hDecodeB : Primrec decodeB :=
    decodeListCode_primrec.comp CodedFiniteDistribution.decodeSecond_primrec
  have hMap : Primrec (fun w : BitString => positions.map fun i =>
      if i ∈ A then (decodeA w).getD ((A.sort (· ≤ ·)).idxOf i) []
      else (decodeB w).getD ((B.sort (· ≤ ·)).idxOf i) []) := by
    induction positions with
    | nil => exact Primrec.const []
    | cons i positions ih =>
      have hget : Primrec (fun w : BitString =>
          if i ∈ A then (decodeA w).getD ((A.sort (· ≤ ·)).idxOf i) []
          else (decodeB w).getD ((B.sort (· ≤ ·)).idxOf i) []) := by
        by_cases hi : i ∈ A
        · simp only [ite_eq_left hi]
          exact (Primrec.list_getD ([] : BitString)).comp hDecodeA
            (Primrec.const ((A.sort (· ≤ ·)).idxOf i))
        · simp only [ite_eq_right hi]
          exact (Primrec.list_getD ([] : BitString)).comp hDecodeB
            (Primrec.const ((B.sort (· ≤ ·)).idxOf i))
      exact Primrec.list_cons.comp hget ih
  refine ⟨f, listCode_computable.comp hMap.to_comp, ?_⟩
  intro u
  simp only [f, decodeFirst_pairCode, decodeSecond_pairCode, subtupleCode,
    decodeListCode_listCode]
  apply congrArg listCode
  apply List.map_congr_left
  intro i hi
  have hget (S : Finset (Fin k)) (hiS : i ∈ S) :
      ((S.sort (· ≤ ·)).map u).getD ((S.sort (· ≤ ·)).idxOf i) [] = u i := by
    have hiSort : i ∈ S.sort (· ≤ ·) := by simpa
    simp [List.getD_eq_getElem?_getD, List.getElem?_idxOf hiSort]
  by_cases hiA : i ∈ A
  · rw [ite_eq_left hiA, hget A hiA]
  · have hiT : i ∈ T := by simpa using hi
    have hiAB : i ∈ A ∪ B := by rwa [hcover]
    have hiB : i ∈ B := (Finset.mem_union.mp hiAB).resolve_left hiA
    rw [ite_eq_right hiA, hget B hiB]

/-- The
`lemma2_partition_chain_rule`:
the tuple code and the nested code of its three blocks are computably interconvertible, and the
code of the union of the first two blocks is interconvertible with their paired code. -/
private theorem lemma2_partition_recode
    (D : Map) (hD : isOptimalConditional D) (k : ℕ) :
    ∃ c : ℕ, ∀ (u : Fin k → BitString) (V W : Finset (Fin k)), Disjoint V W →
      let R := Finset.univ \ (V ∪ W)
      let a := subtupleCode u W
      let b := subtupleCode u V
      let r := subtupleCode u R
      let g := subtupleCode u (V ∪ W)
      let p := pairCode a (pairCode b r)
      let q := pairCode b a
      (natK D (tupleCode u) ≤ natK D p + c ∧
        natK D p ≤ natK D (tupleCode u) + c) ∧
      (natCondK D r q ≤ natCondK D r g + c ∧
        natCondK D r g ≤ natCondK D r q + c) := by
  classical
  have hPair (f g : BitString → BitString) (hf : Computable f) (hg : Computable g) :
      Computable (fun w : BitString => pairCode (f w) (g w)) :=
    (show Computable₂ pairCode from pairCode_computable).comp hf hg
  have hNat (a b : ℕ∞) (c : ℕ) (hb : b ≠ ⊤) (h : a ≤ b + (c : ℕ∞)) :
      a.toNat ≤ b.toNat + c := by
    apply ENat.toNat_le_of_le_natCast
    calc
      a ≤ b + (c : ℕ∞) := h
      _ = ((b.toNat + c : ℕ) : ℕ∞) := by
        rw [Nat.cast_add, ENat.natCast_toNat hb]
  have hFor (V W : Finset (Fin k)) :
      ∃ c : ℕ, ∀ u : Fin k → BitString,
        let R := Finset.univ \ (V ∪ W)
        let a := subtupleCode u W
        let b := subtupleCode u V
        let r := subtupleCode u R
        let g := subtupleCode u (V ∪ W)
        let p := pairCode a (pairCode b r)
        let q := pairCode b a
        (natK D (tupleCode u) ≤ natK D p + c ∧
          natK D p ≤ natK D (tupleCode u) + c) ∧
        (natCondK D r q ≤ natCondK D r g + c ∧
          natCondK D r g ≤ natCondK D r q + c) := by
    let R := Finset.univ \ (V ∪ W)
    obtain ⟨fW, hfW, hW⟩ := lemma2_projection
      (Finset.univ : Finset (Fin k)) W (Finset.subset_univ W)
    obtain ⟨fV, hfV, hV⟩ := lemma2_projection
      (Finset.univ : Finset (Fin k)) V (Finset.subset_univ V)
    obtain ⟨fR, hfR, hR⟩ := lemma2_projection
      (Finset.univ : Finset (Fin k)) R (Finset.subset_univ R)
    let f : BitString → BitString := fun w => pairCode (fW w) (pairCode (fV w) (fR w))
    have hf : Computable f := hPair _ _ hfW (hPair _ _ hfV hfR)
    have hfCode (u : Fin k → BitString) :
        f (tupleCode u) = pairCode (subtupleCode u W)
          (pairCode (subtupleCode u V) (subtupleCode u R)) := by
      dsimp [f]
      rw [← subtupleCode_univ u, hW u, hV u, hR u]
    obtain ⟨mergeVR, hmergeVR, hVR⟩ := lemma2_merge
      (V ∪ R) V R rfl
    have hcover : W ∪ (V ∪ R) = Finset.univ := by
      ext i
      simp only [Finset.mem_union, Finset.mem_univ, iff_true]
      dsimp [R]
      simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_union, true_and]
      tauto
    obtain ⟨mergeAll, hmergeAll, hAll⟩ := lemma2_merge
      Finset.univ W (V ∪ R) hcover
    let f' : BitString → BitString := fun w =>
      mergeAll (pairCode (decodeFirst w) (mergeVR (decodeSecond w)))
    have hf' : Computable f' :=
      hmergeAll.comp (hPair _ _ decodeFirst_computable
        (hmergeVR.comp decodeSecond_computable))
    have hf'Code (u : Fin k → BitString) :
        f' (pairCode (subtupleCode u W)
          (pairCode (subtupleCode u V) (subtupleCode u R))) = tupleCode u := by
      dsimp [f']
      rw [decodeFirst_pairCode, decodeSecond_pairCode, hVR u, hAll u,
        subtupleCode_univ u]
    obtain ⟨sV, hsV, hSV⟩ := lemma2_projection
      (V ∪ W) V Finset.subset_union_left
    obtain ⟨sW, hsW, hSW⟩ := lemma2_projection
      (V ∪ W) W Finset.subset_union_right
    let s : BitString → BitString := fun w => pairCode (sV w) (sW w)
    have hs : Computable s := hPair _ _ hsV hsW
    have hsCode (u : Fin k → BitString) :
        s (subtupleCode u (V ∪ W)) = pairCode (subtupleCode u V) (subtupleCode u W) := by
      dsimp [s]
      rw [hSV u, hSW u]
    obtain ⟨s', hs', hs'Code⟩ := lemma2_merge
      (V ∪ W) V W rfl
    obtain ⟨cTo, hTo⟩ := plainK_map_le D hD f hf
    obtain ⟨cFrom, hFrom⟩ := plainK_map_le D hD f' hf'
    obtain ⟨cCondTo, hCondTo⟩ := condK_cond_map_le D hD s hs
    obtain ⟨cCondFrom, hCondFrom⟩ := condK_cond_map_le D hD s' hs'
    refine ⟨cTo + cFrom + cCondTo + cCondFrom, ?_⟩
    intro u
    have hTo' := hTo (tupleCode u)
    rw [hfCode u] at hTo'
    have hFrom' := hFrom (pairCode (subtupleCode u W)
      (pairCode (subtupleCode u V) (subtupleCode u R)))
    rw [hf'Code u] at hFrom'
    have hCondTo' := hCondTo (subtupleCode u R) (subtupleCode u (V ∪ W))
    rw [hsCode u] at hCondTo'
    have hCondFrom' := hCondFrom (subtupleCode u R)
      (pairCode (subtupleCode u V) (subtupleCode u W))
    rw [hs'Code u] at hCondFrom'
    have hToNat := hNat _ _ cTo (plainK_ne_top D hD _) hTo'
    have hFromNat := hNat _ _ cFrom (plainK_ne_top D hD _) hFrom'
    have hCondToNat := hNat _ _ cCondTo (condK_ne_top_of_optimal D hD _ _) hCondTo'
    have hCondFromNat := hNat _ _ cCondFrom (condK_ne_top_of_optimal D hD _ _) hCondFrom'
    dsimp only [natK, natCondK, R] at hToNat hFromNat hCondToNat hCondFromNat ⊢
    exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
  choose overhead hOverhead using hFor
  let c := Finset.univ.sup fun t : Finset (Fin k) × Finset (Fin k) => overhead t.1 t.2
  refine ⟨c, ?_⟩
  intro u V W hVW
  have h := hOverhead V W u
  have hc : overhead V W ≤ c :=
    Finset.le_sup (f := fun t : Finset (Fin k) × Finset (Fin k) => overhead t.1 t.2)
      (Finset.mem_univ (V, W))
  dsimp only at h ⊢
  exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩

/-- The
`lemma2_partition_chain_rule`:
apply plain symmetry of information to the outer split of three arbitrary strings. -/
private theorem lemma2_outer_plain_chain
    (D : Map) (hD : isOptimalConditional D) :
    ∃ e : ℕ, ∀ (a b r : BitString),
      natK D (pairCode a (pairCode b r)) ≤
          natK D a + natCondK D (pairCode b r) a +
            logSlack e (natK D (pairCode a (pairCode b r))) ∧
        natK D a + natCondK D (pairCode b r) a ≤
          natK D (pairCode a (pairCode b r)) +
            logSlack e (natK D (pairCode a (pairCode b r))) := by
  obtain ⟨cPair, hPair⟩ := Kolmogorov.pairPlainK_symmetryOfInformation_values D hD
  obtain ⟨cSlack, hSlack⟩ := logSlack_absorb_of_le_linear cPair 1 1
  refine ⟨cSlack, ?_⟩
  intro a b r
  let p := pairCode a (pairCode b r)
  let N := natK D p
  have ha : Kolmogorov.HasPlainComplexityValue D a (natK D a) := by
    change plainK D a = ((plainK D a).toNat : ℕ∞)
    exact (ENat.natCast_toNat (plainK_ne_top D hD a)).symm
  have hb : Kolmogorov.HasPlainConditionalComplexityValue D (pairCode b r) a
      (natCondK D (pairCode b r) a) := by
    change condK D (pairCode b r) a =
      ((condK D (pairCode b r) a).toNat : ℕ∞)
    exact (ENat.natCast_toNat
      (avgCond_condK_ne_top D hD (pairCode b r) a)).symm
  have hp : Kolmogorov.HasPlainComplexityValue D p N := by
    change plainK D p = ((plainK D p).toNat : ℕ∞)
    exact (ENat.natCast_toNat (plainK_ne_top D hD p)).symm
  have hraw := hPair a (pairCode b r) (natK D a)
    (natCondK D (pairCode b r) a) N ha hb hp
  have hlog : logSlack cPair (N + 1) ≤ logSlack cSlack N :=
    hSlack N (N + 1) (by omega)
  constructor
  · calc
      natK D p ≤ natK D a + natCondK D (pairCode b r) a +
          logSlack cPair (N + 1) := by simpa [p, N] using hraw.1
      _ ≤ natK D a + natCondK D (pairCode b r) a + logSlack cSlack N := by omega
  · calc
      natK D a + natCondK D (pairCode b r) a ≤
          natK D p + logSlack cPair (N + 1) := by simpa [p, N] using hraw.2
      _ ≤ natK D p + logSlack cSlack N := by omega

/-- The
`lemma2_partition_chain_rule`:
apply the conditional pair chain rule to the inner two strings, with the first string as condition.
-/
private theorem lemma2_inner_conditional_chain
    (D : Map) (hD : isOptimalConditional D) :
    ∃ e : ℕ, ∀ (a b r : BitString),
      natCondK D (pairCode b r) a ≤
          natCondK D b a + natCondK D r (pairCode b a) +
            logSlack e (natK D (pairCode a (pairCode b r))) ∧
        natCondK D b a + natCondK D r (pairCode b a) ≤
          natCondK D (pairCode b r) a +
            logSlack e (natK D (pairCode a (pairCode b r))) := by
  obtain ⟨cLower, hLower⟩ :=
    Kolmogorov.condK_pairCode_chain_lower_values D hD
  obtain ⟨cUpper, hUpper⟩ :=
    Kolmogorov.condK_pairCode_chain_upper_values D hD
  obtain ⟨cCond, hCond⟩ := condK_le_plainK D hD
  obtain ⟨cProj, hProj⟩ :=
    plainK_map_le D hD decodeSecond decodeSecond_computable
  let cArg := cCond + cProj + 1
  obtain ⟨cLowerSlack, hLowerSlack⟩ :=
    logSlack_absorb_of_le_linear cLower 1 cArg
  obtain ⟨cUpperSlack, hUpperSlack⟩ :=
    logSlack_absorb_of_le_linear cUpper 1 cArg
  let e := max cLowerSlack cUpperSlack
  refine ⟨e, ?_⟩
  intro a b r
  let p := pairCode a (pairCode b r)
  let N := natK D p
  let kx := natCondK D b a
  let kyx := natCondK D r (pairCode b a)
  let kxy := natCondK D (pairCode b r) a
  have hb : Kolmogorov.HasPlainConditionalComplexityValue D b a kx := by
    change condK D b a = ((condK D b a).toNat : ℕ∞)
    exact (ENat.natCast_toNat (avgCond_condK_ne_top D hD b a)).symm
  have hr : Kolmogorov.HasPlainConditionalComplexityValue D r (pairCode b a) kyx := by
    change condK D r (pairCode b a) =
      ((condK D r (pairCode b a)).toNat : ℕ∞)
    exact (ENat.natCast_toNat
      (avgCond_condK_ne_top D hD r (pairCode b a))).symm
  have hbr : Kolmogorov.HasPlainConditionalComplexityValue D (pairCode b r) a kxy := by
    change condK D (pairCode b r) a =
      ((condK D (pairCode b r) a).toNat : ℕ∞)
    exact (ENat.natCast_toNat
      (avgCond_condK_ne_top D hD (pairCode b r) a)).symm
  have hPairBound : condK D (pairCode b r) a ≤ plainK D p + (cCond + cProj : ℕ∞) := by
    calc
      condK D (pairCode b r) a ≤ plainK D (pairCode b r) + (cCond : ℕ∞) :=
        hCond (pairCode b r) a
      _ ≤ plainK D p + (cProj : ℕ∞) + (cCond : ℕ∞) := by
        gcongr
        simpa only [p, decodeSecond_pairCode] using hProj p
      _ = plainK D p + (cCond + cProj : ℕ∞) := by ring
  have hFinitePair := avgCond_condK_ne_top D hD (pairCode b r) a
  have hFiniteP := plainK_ne_top D hD p
  have hArgNat : kxy + 1 ≤ N + cArg := by
    have hCast : ((natCondK D (pairCode b r) a : ℕ) : ℕ∞) ≤
        ((natK D p : ℕ) : ℕ∞) + (cCond + cProj : ℕ∞) := by
      change ((condK D (pairCode b r) a).toNat : ℕ∞) ≤
        ((plainK D p).toNat : ℕ∞) + (cCond + cProj : ℕ∞)
      rw [ENat.natCast_toNat hFinitePair, ENat.natCast_toNat hFiniteP]
      exact hPairBound
    have hNat : kxy ≤ N + (cCond + cProj) := by
      simpa [kxy, N, p] using
        (show natCondK D (pairCode b r) a ≤ natK D p + (cCond + cProj) by
          exact_mod_cast hCast)
    dsimp [cArg]
    omega
  have hLowRaw := hLower b r a kx kyx kxy hb hr hbr
  have hUpRaw := hUpper b r a kx kyx kxy hb hr hbr
  have hLowLog : logSlack cLower (kxy + 1) ≤ logSlack cLowerSlack N := by
    exact hLowerSlack N (kxy + 1) (by dsimp [N, p] at hArgNat ⊢; omega)
  have hUpLog : logSlack cUpper (kxy + 1) ≤ logSlack cUpperSlack N := by
    exact hUpperSlack N (kxy + 1) (by dsimp [N, p] at hArgNat ⊢; omega)
  constructor
  · calc
      kxy ≤ kx + kyx + logSlack cUpper (kxy + 1) := by simpa [kx, kyx, kxy] using hUpRaw
      _ ≤ kx + kyx + logSlack cUpperSlack N := by omega
      _ ≤ kx + kyx + logSlack e N := by
        exact Nat.add_le_add_left
          (logSlack_mono_left (le_max_right cLowerSlack cUpperSlack) N) _
  · calc
      kx + kyx ≤ kxy + logSlack cLower (kxy + 1) := by simpa [kx, kyx, kxy] using hLowRaw
      _ ≤ kxy + logSlack cLowerSlack N := by omega
      _ ≤ kxy + logSlack e N := by
        exact Nat.add_le_add_left
          (logSlack_mono_left (le_max_left cLowerSlack cUpperSlack) N) _

/-- The
`lemma2_total_complexity_to_profile`: the
three-block chain rule, in both directions, for a tuple partitioned into `W`, `V`, and the
remaining coordinates. -/
private theorem lemma2_partition_chain_rule
    (D : Map) (hD : isOptimalConditional D) (k : ℕ) :
    ∃ e : ℕ, ∀ (u : Fin k → BitString) (V W : Finset (Fin k)),
      V.Nonempty → Disjoint V W →
      let R := Finset.univ \ (V ∪ W)
      natK D (tupleCode u) ≤
          subCondK D u W ∅ + subCondK D u V W + subCondK D u R (V ∪ W) +
            logSlack e (natK D (tupleCode u)) ∧
        subCondK D u W ∅ + subCondK D u V W + subCondK D u R (V ∪ W) ≤
          natK D (tupleCode u) + logSlack e (natK D (tupleCode u)) := by
  obtain ⟨cCode, hCode⟩ :=
    lemma2_partition_recode
      D hD k
  obtain ⟨cOuter, hOuter⟩ :=
    lemma2_outer_plain_chain
      D hD
  obtain ⟨cInner, hInner⟩ :=
    lemma2_inner_conditional_chain
      D hD
  let cChain := cOuter + cInner
  let cOffset := 2 * cCode + logSlack cChain cCode
  let e := cChain + cOffset
  refine ⟨e, ?_⟩
  intro u V W hV hVW
  let R := Finset.univ \ (V ∪ W)
  let a := subtupleCode u W
  let b := subtupleCode u V
  let r := subtupleCode u R
  let g := subtupleCode u (V ∪ W)
  let p := pairCode a (pairCode b r)
  let q := pairCode b a
  let N := natK D (tupleCode u)
  let Np := natK D p
  let S := natK D a + natCondK D b a + natCondK D r g
  let Sp := natK D a + natCondK D b a + natCondK D r q
  have hRec := hCode u V W hVW
  have hNnp : N ≤ Np + cCode := by simpa [N, Np, p, a, b, r, R] using hRec.1.1
  have hNpN : Np ≤ N + cCode := by simpa [N, Np, p, a, b, r, R] using hRec.1.2
  have hRtoG : natCondK D r q ≤ natCondK D r g + cCode := by
    simpa [r, q, g, a, b, R] using hRec.2.1
  have hGtoR : natCondK D r g ≤ natCondK D r q + cCode := by
    simpa [r, q, g, a, b, R] using hRec.2.2
  have hOuter' := hOuter a b r
  have hOuterUp : Np ≤ natK D a + natCondK D (pairCode b r) a +
      logSlack cOuter Np := by simpa [Np, p, a, b, r] using hOuter'.1
  have hOuterLow : natK D a + natCondK D (pairCode b r) a ≤
      Np + logSlack cOuter Np := by simpa [Np, p, a, b, r] using hOuter'.2
  have hInner' := hInner a b r
  have hInnerUp : natCondK D (pairCode b r) a ≤
      natCondK D b a + natCondK D r q + logSlack cInner Np := by
    simpa [Np, p, q, a, b, r] using hInner'.1
  have hInnerLow : natCondK D b a + natCondK D r q ≤
      natCondK D (pairCode b r) a + logSlack cInner Np := by
    simpa [Np, p, q, a, b, r] using hInner'.2
  have hSlackEq : logSlack cOuter Np + logSlack cInner Np =
      logSlack cChain Np := by
    dsimp [cChain]
    exact (logSlack_add_constants cOuter cInner Np).symm
  have hPartUp : Np ≤ Sp + logSlack cChain Np := by
    have hraw : Np ≤ Sp + (logSlack cOuter Np + logSlack cInner Np) := by
      dsimp [Sp]
      omega
    rw [hSlackEq] at hraw
    exact hraw
  have hPartLow : Sp ≤ Np + logSlack cChain Np := by
    have hraw : Sp ≤ Np + (logSlack cOuter Np + logSlack cInner Np) := by
      dsimp [Sp]
      omega
    rw [hSlackEq] at hraw
    exact hraw
  have hST : S = natK D a + natCondK D b a + natCondK D r g := rfl
  have hSpToS : Sp ≤ S + cCode := by
    dsimp [Sp, S]
    omega
  have hSToSp : S ≤ Sp + cCode := by
    dsimp [Sp, S]
    omega
  have hNraw : N ≤ S + (logSlack cChain Np + 2 * cCode) := by
    dsimp [S, Sp] at hPartUp hSpToS ⊢
    omega
  have hSraw : S ≤ N + (logSlack cChain Np + 2 * cCode) := by
    dsimp [S, Sp] at hPartLow hSToSp ⊢
    omega
  have hSlackNp : logSlack cChain Np ≤ logSlack cChain (N + cCode) :=
    logSlack_mono_right cChain hNpN
  have hSlackArg : logSlack cChain (N + cCode) ≤
      logSlack cChain N + logSlack cChain cCode :=
    logSlack_add_le cChain N cCode
  have hOffset : logSlack cChain N + cOffset ≤ logSlack e N := by
    have hconst : cOffset ≤ logSlack cOffset N := by
      unfold logSlack
      exact Nat.le_add_left _ _
    calc
      logSlack cChain N + cOffset ≤ logSlack cChain N + logSlack cOffset N :=
        Nat.add_le_add_left hconst _
      _ = logSlack e N := by
        dsimp [e]
        exact (logSlack_add_constants cChain cOffset N).symm
  have hFinalSlack : logSlack cChain Np + 2 * cCode ≤ logSlack e N := by
    calc
      logSlack cChain Np + 2 * cCode ≤
          logSlack cChain (N + cCode) + 2 * cCode :=
        Nat.add_le_add_right hSlackNp _
      _ ≤ logSlack cChain N + logSlack cChain cCode + 2 * cCode :=
        Nat.add_le_add_right hSlackArg _
      _ ≤ logSlack cChain N + cOffset := by
        dsimp [cOffset]
        omega
      _ ≤ logSlack e N := hOffset
  have hNfinal : N ≤ S + logSlack e N := by omega
  have hSfinal : S ≤ N + logSlack e N := by omega
  have hTerms : subCondK D u W ∅ + subCondK D u V W +
      subCondK D u R (V ∪ W) = S := by
    simp [subCondK, S, a, b, r, g, R, natK, plainK, subtupleCode_empty]
    rfl
  constructor
  · simpa [N] using (hTerms ▸ hNfinal)
  · simpa [N] using (hTerms ▸ hSfinal)

/-- A
typization member whose whole-tuple complexity is at most `δ` below the reference has each
extended-profile component bounded below up to the same loss and logarithmic chain-rule slack.
This is the unconditional total-complexity-to-profile comparison. -/
private theorem lemma2_total_complexity_to_profile
    (D : Map) (hD : isOptimalConditional D) (n m : ℕ) :
    ∃ e : ℕ, ∀ (x : Fin n → BitString) (y : Fin m → BitString)
      (x' : Fin n → BitString) (δ : ℕ),
      x' ∈ typization D x y →
      natK D (tupleCode (Fin.append x y)) ≤
        natK D (tupleCode (Fin.append x' y)) + δ →
      ∀ V W : Finset (Fin (n + m)), V.Nonempty → Disjoint V W →
        subCondK D (Fin.append x y) V W ≤
          subCondK D (Fin.append x' y) V W +
            (δ + logSlack e (natK D (tupleCode (Fin.append x y)))) := by
  obtain ⟨e, he⟩ :=
    lemma2_partition_chain_rule
      D hD (n + m)
  obtain ⟨cCond, hCond⟩ := condK_le_plainK D hD
  let cEmpty := natK D [] + cCond
  refine ⟨2 * e + cEmpty, ?_⟩
  intro x y x' δ hx htotal V W hV hdis
  let u : Fin (n + m) → BitString := Fin.append x y
  let u' : Fin (n + m) → BitString := Fin.append x' y
  let R : Finset (Fin (n + m)) := Finset.univ \ (V ∪ W)
  change ExtProfileLe D u' u at hx
  have hk : 0 < n + m := by
    have hcard : 0 < V.card := Finset.card_pos.mpr hV
    have hcardle : V.card ≤ n + m := by simpa using Finset.card_le_univ V
    omega
  have hfull : (Finset.univ : Finset (Fin (n + m))).Nonempty := by
    exact ⟨⟨0, hk⟩, Finset.mem_univ _⟩
  have htotal' : natK D (tupleCode u') ≤ natK D (tupleCode u) := by
    have h := hx Finset.univ ∅ hfull (Finset.disjoint_empty_right _)
    simpa [u, subCondK, subtupleCode_univ, subtupleCode_empty,
      natK, natCondK, plainK] using h
  let N := natK D (tupleCode u)
  let N' := natK D (tupleCode u')
  let L := logSlack e N
  have hNbound : N ≤ N' + δ := by
    simpa [N, N', u, u'] using htotal
  have hNmono : N' ≤ N := by
    simpa [N, N', u, u'] using htotal'
  have hL' : logSlack e N' ≤ L := by
    exact logSlack_mono_right e hNmono
  let a := subCondK D u W ∅
  let b := subCondK D u V W
  let c := subCondK D u R (V ∪ W)
  let a' := subCondK D u' W ∅
  let b' := subCondK D u' V W
  let c' := subCondK D u' R (V ∪ W)
  have hW : a' ≤ a := by
    by_cases hWempty : W = ∅
    · subst W
      simp [a, a', subCondK, subtupleCode_empty]
    · have hWne : W.Nonempty := Finset.nonempty_iff_ne_empty.mpr hWempty
      exact hx W ∅ hWne (Finset.disjoint_empty_right W)
  have hR : c' ≤ c + cEmpty := by
    by_cases hRempty : R = ∅
    · have hCondFinite :=
        condK_ne_top_of_optimal D hD [] (subtupleCode u' (V ∪ W))
      have hPlainFinite := plainK_ne_top D hD []
      have hEmptyENat := hCond [] (subtupleCode u' (V ∪ W))
      rw [← ENat.natCast_toNat hCondFinite,
        ← ENat.natCast_toNat hPlainFinite] at hEmptyENat
      have hEmptyNat : natCondK D [] (subtupleCode u' (V ∪ W)) ≤
          natK D [] + cCond := by
        exact_mod_cast hEmptyENat
      have hEmptyPrimed : c' ≤ cEmpty := by
        simpa [c', R, hRempty, subCondK, subtupleCode_empty, cEmpty] using hEmptyNat
      omega
    · have hRne : R.Nonempty := Finset.nonempty_iff_ne_empty.mpr hRempty
      have hdisR : Disjoint R (V ∪ W) := by
        exact disjoint_comm.mpr Finset.disjoint_sdiff
      have h := hx R (V ∪ W) hRne hdisR
      dsimp [c, c']
      omega
  have hRef := (he u V W hV hdis).2
  have hPrim := (he u' V W hV hdis).1
  have hRef' : a + b + c ≤ N + L := by
    simpa [a, b, c, R, u, N, L] using hRef
  have hPrim' : N' ≤ a' + b' + c' + logSlack e N' := by
    simpa [a', b', c', R, u', N'] using hPrim
  have hsum : a + b + c ≤ a' + b' + c' + δ + 2 * L := by
    calc
      a + b + c ≤ N + L := hRef'
      _ ≤ N' + δ + L := by omega
      _ ≤ a' + b' + c' + logSlack e N' + δ + L := by omega
      _ ≤ a' + b' + c' + δ + 2 * L := by omega
  have hresult : b ≤ b' + δ + 2 * L + cEmpty := by
    omega
  have hslack : 2 * L + cEmpty ≤ logSlack (2 * e + cEmpty) N := by
    have hsmall : cEmpty ≤ logSlack cEmpty N := by
      unfold logSlack
      exact Nat.le_add_left _ _
    have hdouble : 2 * L = logSlack (2 * e) N := by
      calc
        2 * L = logSlack e N + logSlack e N := by omega
        _ = logSlack (e + e) N := (logSlack_add_constants e e N).symm
        _ = logSlack (2 * e) N := by congr 1; omega
    calc
      2 * L + cEmpty ≤ 2 * L + logSlack cEmpty N := Nat.add_le_add_left hsmall _
      _ = logSlack (2 * e) N + logSlack cEmpty N := by rw [hdouble]
      _ = logSlack (2 * e + cEmpty) N := (logSlack_add_constants (2 * e) cEmpty N).symm
  have hresult' : b ≤ b' + δ + logSlack (2 * e + cEmpty) N := by
    calc
      b ≤ b' + δ + (2 * L + cEmpty) := by omega
      _ ≤ b' + δ + logSlack (2 * e + cEmpty) N := Nat.add_le_add_left hslack _
  simpa [u, u', N, b, b', Nat.add_assoc] using hresult'

/-- A member of the typization whose conditional
complexity is not much smaller than the reference value has every extended-profile component
bounded below by the reference component up to logarithmic slack. -/
private theorem lemma2_profile_from_conditional_complexity
    (D : Map) (hD : isOptimalConditional D) (n m c : ℕ) :
    ∃ C : ℕ, ∀ (x : Fin n → BitString) (y : Fin m → BitString)
      (x' : Fin n → BitString),
      x' ∈ typization D x y →
      natCondK D (tupleCode x) (tupleCode y) ≤
        natCondK D (tupleCode x') (tupleCode y) +
          (logSlack c (natK D (tupleCode (Fin.append x y))) + 1) →
      x' ∈ strongTypization D
        (logSlack C (natK D (tupleCode (Fin.append x y)))) x y := by
  obtain ⟨d, hd⟩ :=
    lemma2_total_complexity_lower_bound
      D hD n m c
  obtain ⟨e, he⟩ :=
    lemma2_total_complexity_to_profile
      D hD n m
  refine ⟨d + e, ?_⟩
  intro x y x' hx hcond
  change ExtProfileLe D (Fin.append x' y) (Fin.append x y) at hx
  let N := natK D (tupleCode (Fin.append x y))
  change ExtProfileLe D (Fin.append x' y) (Fin.append x y) ∧
    (∀ V W : Finset (Fin (n + m)), V.Nonempty → Disjoint V W →
      subCondK D (Fin.append x y) V W ≤
        subCondK D (Fin.append x' y) V W + logSlack (d + e) N)
  refine ⟨hx, ?_⟩
  have htotal := hd x y x' hx hcond
  have hprofile := he x y x' (logSlack d N) hx htotal
  intro V W hV hdis
  have hresult := hprofile V W hV hdis
  simpa [N, Kolmogorov.logSlack_add_const] using hresult

/-- **Lemma 2.** More than half of the typization consists of clones: there is `C = C(n, m)`
with `|ST_{C log N}(x̄ | ȳ)| > |T(x̄ | ȳ)| / 2`, `N = K(x̄, ȳ)`.  Proof: Appendix. -/
theorem lemma2 (D : Map) (hD : isOptimalConditional D) (n m : ℕ) :
    ∃ C : ℕ, ∀ (x : Fin n → BitString) (y : Fin m → BitString),
      (typization D x y).ncard <
        2 * (strongTypization D (logSlack C (natK D (tupleCode (Fin.append x y)))) x y).ncard := by
  obtain ⟨c, hc⟩ := lemma1 D hD n m
  obtain ⟨C, hprofile⟩ := lemma2_profile_from_conditional_complexity D hD n m c
  refine ⟨C, fun x y => ?_⟩
  let k := natCondK D (tupleCode x) (tupleCode y)
  let s := logSlack c (natK D (tupleCode (Fin.append x y)))
  let H : Set (Fin n → BitString) :=
    {x' | x' ∈ typization D x y ∧
      k ≤ natCondK D (tupleCode x') (tupleCode y) + (s + 1)}
  have hL := hc x y
  have hcount := lemma2_half_conditional_complexity D hD n m x y k s
    hL.1 hL.2.2
  have hHs : H ⊆ strongTypization D
      (logSlack C (natK D (tupleCode (Fin.append x y)))) x y := by
    intro x' hx'
    exact hprofile x y x' hx'.1 (by simpa [k, s] using hx'.2)
  have hSTfin :
      (strongTypization D (logSlack C (natK D (tupleCode (Fin.append x y)))) x y).Finite :=
    hL.1.subset (by
      intro x' hx'
      exact hx'.1)
  have hHle : H.ncard ≤
      (strongTypization D (logSlack C (natK D (tupleCode (Fin.append x y)))) x y).ncard :=
    Set.ncard_le_ncard hHs hSTfin
  calc
    (typization D x y).ncard < 2 * H.ncard := hcount.2
    _ ≤ 2 * (strongTypization D
        (logSlack C (natK D (tupleCode (Fin.append x y)))) x y).ncard :=
      Nat.mul_le_mul_left 2 hHle

end Kolmogorov.Relativization
