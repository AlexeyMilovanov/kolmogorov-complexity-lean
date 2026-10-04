/-
Copyright (c) 2025 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Authors
-/
import KolmogorovMathlib.Complexity.Tuples.ChainRule

/-!
# One-term inequalities for prefix complexity (Problem 284)

SUV Problem 284, p. 318.

For prefix complexity the one-term inequalities of Theorem 204 hold with `O(1)` precision
instead of `O(log N)` (`tuple_prefix_complexity_le_weighted_sum`): if every index is covered
with total coefficient at least `1`, then `K(x_1, …, x_n) ≤ ∑_I λ_I K(x_I) + O(1)` for all
tuples of strings, with no bound on their lengths.  The prefix complexity of a subtuple is
`tuplePrefixK`.  The proof follows the book's hint: the basic inequality
`K(a) + K(a,b,c) ≤ K(a,b) + K(a,c) + O(1)` shows that the marginal increment of a coordinate
after all earlier coordinates is at most its increment after the earlier coordinates in `I`,
and summing these ordered marginals over `I` and over the whole index set compares the two
sides.
-/

namespace Kolmogorov

open Finset

variable {n : ℕ}

/-- The prefix complexity `K(x_I)` of a subtuple of a tuple of strings.  This is the prefix
counterpart of `tuplePlainK`, used only for Problem 284.  The list encoding `subtupleCode` of
the subtuple is the one fixed in `Complexity/Tuples/Basic`; another computable encoding
changes `K` by `O(1)` only, which the statement absorbs.  SUV Problem 284, p. 318. -/
noncomputable def tuplePrefixK (U : Map) (x : Fin n → BitString) (I : Finset (Fin n)) : ℕ∞ :=
  KPPlain U (subtupleCode x I)
/- A fixed list of positions gives a computable projection between two list encodings.  This
is the coding device used below to regroup subtuples into the three blocks of the basic
prefix-complexity inequality. -/
private def projectListCode (positions : List ℕ) (w : BitString) : BitString :=
  listCode (positions.map fun k => (decodeListCode w).getD k [])
private lemma projectListCode_primrec (positions : List ℕ) :
    Primrec (projectListCode positions) := by
  induction positions with
  | nil => exact Primrec.const []
  | cons k positions ih =>
      have hget : Primrec (fun w : BitString => (decodeListCode w).getD k []) :=
        (Primrec.list_getD ([] : BitString)).comp decodeListCode_primrec (Primrec.const k)
      exact Primrec.of_eq (CodedFiniteDistribution.pairCode_primrec.comp hget ih) (by
        intro a
        unfold projectListCode
        rfl)
private lemma projectListCode_computable (positions : List ℕ) :
    Computable (projectListCode positions) :=
  (projectListCode_primrec positions).to_comp
private lemma projectListCode_listCode {m : ℕ} (s t : List (Fin m)) (x : Fin m → BitString)
    (ht : ∀ i ∈ t, i ∈ s) :
    projectListCode (t.map fun i => s.idxOf i) (listCode (s.map x)) = listCode (t.map x) := by
  simp only [projectListCode, decodeListCode_listCode, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i hi
  have his : i ∈ s := ht i hi
  simp [Function.comp_apply, List.getD_eq_getElem?_getD, List.getElem?_idxOf his]
private def positionsIn (S T : Finset (Fin n)) : List ℕ :=
  (T.sort (· ≤ ·)).map fun i => (S.sort (· ≤ ·)).idxOf i
@[simp] private lemma projectListCode_subtupleCode (x : Fin n → BitString)
    {S T : Finset (Fin n)} (hTS : T ⊆ S) :
    projectListCode (positionsIn S T) (subtupleCode x S) = subtupleCode x T := by
  unfold positionsIn subtupleCode
  apply projectListCode_listCode
  intro i hi
  rw [Finset.mem_sort] at hi ⊢
  exact hTS hi
/- Decode a list of list-codes and concatenate the decoded blocks. -/
private def flattenListCodes (w : BitString) : BitString :=
  listCode ((decodeListCode w).flatMap decodeListCode)
private lemma flattenListCodes_computable : Computable flattenListCodes := by
  exact (listCode_primrec.comp
    (Primrec.list_flatMap decodeListCode_primrec
      (decodeListCode_primrec.comp Primrec.snd).to₂)).to_comp
@[simp] private lemma flattenListCodes_listCode (blocks : List (List BitString)) :
    flattenListCodes (listCode (blocks.map listCode)) = listCode blocks.flatten := by
  simp only [flattenListCodes, decodeListCode_listCode]
  congr 1
  induction blocks with
  | nil => rfl
  | cons block blocks ih => simp [ih]
private lemma tripleCodeOfNestedPair_computable_here :
    Computable tripleCodeOfNestedPair := by
  apply Computable.of_eq
    (pairCode_computable.comp
      (decodeFirst_computable.pair
        (pairCode_computable.comp
          ((decodeFirst_computable.comp decodeSecond_computable).pair
            (pairCode_computable.comp
              ((decodeSecond_computable.comp decodeSecond_computable).pair
                (Computable.const [])))))))
  intro w
  rfl
/- The basic prefix-complexity inequality, in the three-block form used in the book's hint:
`K(a) + K(a,b,c) ≤ K(a,b) + K(a,c) + O(1)`. -/
private lemma prefix_basic_three_blocks (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ a b d : BitString,
      KPPlain U a + KPTriple U a b d ≤ KPPair U a b + KPPair U a d + (c : ℕ∞) := by
  obtain ⟨cMap, hMap⟩ :=
    KPPlain_map_le U hU tripleCodeOfNestedPair tripleCodeOfNestedPair_computable_here
  obtain ⟨cChain, hChain⟩ := KPPair_chain_upper U hU
  obtain ⟨cCond, hCond⟩ := KPCondPair_chain_upper U hU
  obtain ⟨cDrop, hDrop⟩ := KP_cond_drop_right_le U hU
  obtain ⟨cLower, hLower⟩ := KPPair_chain_lower U hU
  let c := 2 * cLower + cCond + cDrop + cChain + cMap
  refine ⟨c, fun a b d => ?_⟩
  have ha : KPPlain U a ≠ ⊤ := KPPlain_ne_top_of_optimal U hU a
  set ka := (KPPlain U a).toNat
  have hka : HasPrefixComplexityValue U a ka := ENat.natCast_toNat ha
  set w := prefixComplexityContext a ka
  by_cases hb : KP U b w = ⊤
  · have hab : KPPair U a b = ⊤ := by
      have h := hLower a b ka hka
      rw [hb, add_top] at h
      have heq : KPPair U a b + (cLower : ℕ∞) = ⊤ := top_unique h
      rcases WithTop.add_eq_top.mp heq with hp | hc
      · exact hp
      · exact False.elim (ENat.natCast_ne_top cLower hc)
    rw [hab]
    simp
  · set kb := (KP U b w).toNat
    have hkb : HasCondPrefixComplexityValue U b w kb := ENat.natCast_toNat hb
    have hcode : tripleCodeOfNestedPair (pairCode a (pairCode b d)) =
        listCode [a, b, d] := by
      unfold tripleCodeOfNestedPair
      rw [decodeFirst_pairCode, decodeSecond_pairCode, decodeFirst_pairCode,
        decodeSecond_pairCode]
      rfl
    have hTriple : KPTriple U a b d ≤
        KPPair U a (pairCode b d) + (cMap : ℕ∞) := by
      rw [KPTriple, ← hcode]
      exact hMap (pairCode a (pairCode b d))
    have hPair : KPPair U a (pairCode b d) ≤
        KPPlain U a + KPCondPair U b d w + (cChain : ℕ∞) :=
      hChain a (pairCode b d) ka hka
    have hCond' : KPCondPair U b d w ≤
        KP U b w + KP U d (prefixCondComplexityContext w b kb) + (cCond : ℕ∞) :=
      hCond b d w kb hkb
    have hDrop' : KP U d (prefixCondComplexityContext w b kb) ≤
        KP U d w + (cDrop : ℕ∞) :=
      hDrop d w (pairCode b (natCode kb))
    have hab : KPPlain U a + KP U b w ≤ KPPair U a b + (cLower : ℕ∞) :=
      hLower a b ka hka
    have had : KPPlain U a + KP U d w ≤ KPPair U a d + (cLower : ℕ∞) :=
      hLower a d ka hka
    calc
      KPPlain U a + KPTriple U a b d
          ≤ KPPlain U a + (KPPair U a (pairCode b d) + (cMap : ℕ∞)) := by
            gcongr
      _ ≤ KPPlain U a +
          ((KPPlain U a + KPCondPair U b d w + (cChain : ℕ∞)) +
            (cMap : ℕ∞)) := by gcongr
      _ ≤ KPPlain U a +
          ((KPPlain U a +
              (KP U b w + KP U d (prefixCondComplexityContext w b kb) +
                (cCond : ℕ∞)) + (cChain : ℕ∞)) + (cMap : ℕ∞)) := by
            gcongr
      _ ≤ KPPlain U a +
          ((KPPlain U a + (KP U b w + (KP U d w + (cDrop : ℕ∞)) +
            (cCond : ℕ∞)) + (cChain : ℕ∞)) + (cMap : ℕ∞)) := by
            gcongr
      _ = (KPPlain U a + KP U b w) + (KPPlain U a + KP U d w) +
          ((cCond + cDrop + cChain + cMap : ℕ) : ℕ∞) := by
            push_cast
            ring_nf
      _ ≤ (KPPair U a b + (cLower : ℕ∞)) +
          (KPPair U a d + (cLower : ℕ∞)) +
            ((cCond + cDrop + cChain + cMap : ℕ) : ℕ∞) := by gcongr
      _ = KPPair U a b + KPPair U a d + (c : ℕ∞) := by
            dsimp [c]
            push_cast
            ring_nf
private lemma tuplePrefixK_ne_top (U : Map) (hU : IsOptimalPrefixConditional U)
    (x : Fin n → BitString) (I : Finset (Fin n)) : tuplePrefixK U x I ≠ ⊤ :=
  KPPlain_ne_top_of_optimal U hU (subtupleCode x I)
private def groupedPairCode (p q : List ℕ) (w : BitString) : BitString :=
  pairCode (projectListCode p w) (projectListCode q w)
private lemma groupedPairCode_computable (p q : List ℕ) :
    Computable (groupedPairCode p q) := by
  exact (CodedFiniteDistribution.pairCode_primrec.comp
    (projectListCode_primrec p) (projectListCode_primrec q)).to_comp
private def ungroupCode (positions : List ℕ) (w : BitString) : BitString :=
  projectListCode positions (flattenListCodes w)
private lemma ungroupCode_computable (positions : List ℕ) :
    Computable (ungroupCode positions) := by
  unfold ungroupCode
  exact (projectListCode_computable positions).comp flattenListCodes_computable
/- A marginal obtained after seeing all earlier coordinates is no larger, up to a uniform
constant for fixed `i,I`, than the marginal obtained after seeing only the earlier coordinates
belonging to `I`.  This is precisely one basic inequality. -/
private lemma tuplePrefixK_marginal (U : Map) (hU : IsOptimalPrefixConditional U)
    (i : Fin n) (I : Finset (Fin n)) :
    ∃ c : ℕ, ∀ x : Fin n → BitString,
      ((tuplePrefixK U x (insert i (lowerIndices i))).toNat : ℝ) +
          ((tuplePrefixK U x (I ∩ lowerIndices i)).toNat : ℝ) ≤
        ((tuplePrefixK U x (lowerIndices i)).toNat : ℝ) +
          ((tuplePrefixK U x (insert i (I ∩ lowerIndices i))).toNat : ℝ) + c := by
  let L := lowerIndices i
  let A := I ∩ L
  let B := L \ I
  let C : Finset (Fin n) := {i}
  let Q := insert i L
  let R := A.sort (· ≤ ·) ++ B.sort (· ≤ ·) ++ C.sort (· ≤ ·)
  let pA := positionsIn L A
  let pB := positionsIn L B
  let pAL := positionsIn (insert i A) A
  let pC := positionsIn (insert i A) C
  let pQ := (Q.sort (· ≤ ·)).map fun j => R.idxOf j
  obtain ⟨cBasic, hBasic⟩ := prefix_basic_three_blocks U hU
  obtain ⟨cWhole, hWhole⟩ := KPPlain_map_le U hU (ungroupCode pQ)
    (ungroupCode_computable pQ)
  obtain ⟨cAB, hAB⟩ := KPPlain_map_le U hU (groupedPairCode pA pB)
    (groupedPairCode_computable pA pB)
  obtain ⟨cAC, hAC⟩ := KPPlain_map_le U hU (groupedPairCode pAL pC)
    (groupedPairCode_computable pAL pC)
  refine ⟨cWhole + cBasic + cAB + cAC, fun x => ?_⟩
  let a := subtupleCode x A
  let b := subtupleCode x B
  let d := subtupleCode x C
  have hA_L : A ⊆ L := by simp [A]
  have hB_L : B ⊆ L := by simp [B]
  have hA_Q : A ⊆ insert i A := subset_insert i A
  have hC_Q : C ⊆ insert i A := by simp [C]
  have eAB : groupedPairCode pA pB (subtupleCode x L) = pairCode a b := by
    simp [groupedPairCode, pA, pB, a, b, hA_L, hB_L]
  have eAC : groupedPairCode pAL pC (subtupleCode x (insert i A)) = pairCode a d := by
    simp [groupedPairCode, pAL, pC, a, d, hA_Q, hC_Q]
  have hQR : ∀ j ∈ Q.sort (· ≤ ·), j ∈ R := by
    intro j hj
    rw [Finset.mem_sort] at hj
    simp only [R, List.mem_append, Finset.mem_sort]
    rcases Finset.mem_insert.mp hj with rfl | hjL
    · exact Or.inr (by simp [C])
    · by_cases hji : j ∈ I
      · exact Or.inl (Or.inl (by simp [A, hji, hjL]))
      · exact Or.inl (Or.inr (by simp [B, hji, hjL]))
  have eWhole : ungroupCode pQ (listCode [a, b, d]) = subtupleCode x Q := by
    have hf : flattenListCodes (listCode [a, b, d]) = listCode (R.map x) := by
      calc
        flattenListCodes (listCode [a, b, d]) =
            flattenListCodes (listCode
              ([A.sort (· ≤ ·) |>.map x, B.sort (· ≤ ·) |>.map x,
                C.sort (· ≤ ·) |>.map x].map listCode)) := by
                  simp [a, b, d, subtupleCode]
        _ = listCode
            [A.sort (· ≤ ·) |>.map x, B.sort (· ≤ ·) |>.map x,
              C.sort (· ≤ ·) |>.map x].flatten :=
                flattenListCodes_listCode _
        _ = listCode (R.map x) := by simp [R]
    unfold ungroupCode
    rw [hf]
    unfold pQ subtupleCode
    exact projectListCode_listCode R (Q.sort (· ≤ ·)) x hQR
  have h1 : tuplePrefixK U x Q ≤ KPTriple U a b d + (cWhole : ℕ∞) := by
    rw [tuplePrefixK, KPTriple, ← eWhole]
    exact hWhole (listCode [a, b, d])
  have h2 : KPPair U a b ≤ tuplePrefixK U x L + (cAB : ℕ∞) := by
    rw [tuplePrefixK, KPPair, ← eAB]
    exact hAB (subtupleCode x L)
  have h3 : KPPair U a d ≤ tuplePrefixK U x (insert i A) + (cAC : ℕ∞) := by
    rw [tuplePrefixK, KPPair, ← eAC]
    exact hAC (subtupleCode x (insert i A))
  have hENat : tuplePrefixK U x Q + tuplePrefixK U x A ≤
      tuplePrefixK U x L + tuplePrefixK U x (insert i A) +
        ((cWhole + cBasic + cAB + cAC : ℕ) : ℕ∞) := by
    calc
      tuplePrefixK U x Q + tuplePrefixK U x A
          ≤ (KPTriple U a b d + (cWhole : ℕ∞)) + KPPlain U a := by
            simpa [a, tuplePrefixK] using add_le_add h1 (le_refl (tuplePrefixK U x A))
      _ = (KPPlain U a + KPTriple U a b d) + (cWhole : ℕ∞) := by
            simp only [add_comm, add_left_comm]
      _ ≤ (KPPair U a b + KPPair U a d + (cBasic : ℕ∞)) +
          (cWhole : ℕ∞) := by
            simpa only [add_assoc, add_comm, add_left_comm] using
              add_le_add_left (hBasic a b d) (cWhole : ℕ∞)
      _ ≤ (tuplePrefixK U x L + (cAB : ℕ∞)) +
          (tuplePrefixK U x (insert i A) + (cAC : ℕ∞)) +
            (cBasic : ℕ∞) + (cWhole : ℕ∞) := by gcongr
      _ = tuplePrefixK U x L + tuplePrefixK U x (insert i A) +
          ((cWhole + cBasic + cAB + cAC : ℕ) : ℕ∞) := by
            push_cast
            ring_nf
  have hQtop := tuplePrefixK_ne_top U hU x Q
  have hAtop := tuplePrefixK_ne_top U hU x A
  have hLtop := tuplePrefixK_ne_top U hU x L
  have hIAtop := tuplePrefixK_ne_top U hU x (insert i A)
  have hRightTop : tuplePrefixK U x L + tuplePrefixK U x (insert i A) +
      ((cWhole + cBasic + cAB + cAC : ℕ) : ℕ∞) ≠ ⊤ :=
    WithTop.add_ne_top.mpr
      ⟨WithTop.add_ne_top.mpr ⟨hLtop, hIAtop⟩,
        ENat.natCast_ne_top (cWhole + cBasic + cAB + cAC)⟩
  have hNat := ENat.toNat_le_toNat hENat hRightTop
  have hAddQ : (tuplePrefixK U x Q + tuplePrefixK U x A).toNat =
      (tuplePrefixK U x Q).toNat + (tuplePrefixK U x A).toNat :=
    ENat.toNat_add hQtop hAtop
  rw [hAddQ] at hNat
  have hRight1 : (tuplePrefixK U x L + tuplePrefixK U x (insert i A) +
      ((cWhole + cBasic + cAB + cAC : ℕ) : ℕ∞)).toNat =
        (tuplePrefixK U x L + tuplePrefixK U x (insert i A)).toNat +
          ((cWhole + cBasic + cAB + cAC : ℕ) : ℕ∞).toNat :=
    ENat.toNat_add (WithTop.add_ne_top.mpr ⟨hLtop, hIAtop⟩)
      (ENat.natCast_ne_top (cWhole + cBasic + cAB + cAC))
  rw [hRight1] at hNat
  have hRight2 : (tuplePrefixK U x L + tuplePrefixK U x (insert i A)).toNat =
      (tuplePrefixK U x L).toNat + (tuplePrefixK U x (insert i A)).toNat :=
    ENat.toNat_add hLtop hIAtop
  rw [hRight2] at hNat
  rw [ENat.toNat_natCast] at hNat
  exact_mod_cast hNat
private lemma tuplePrefixK_subset_le (U : Map) (hU : IsOptimalPrefixConditional U)
    {T S : Finset (Fin n)} (hTS : T ⊆ S) :
    ∃ c : ℕ, ∀ x : Fin n → BitString,
      ((tuplePrefixK U x T).toNat : ℝ) ≤ ((tuplePrefixK U x S).toNat : ℝ) + c := by
  obtain ⟨c, hc⟩ := KPPlain_map_le U hU (projectListCode (positionsIn S T))
    (projectListCode_computable _)
  refine ⟨c, fun x => ?_⟩
  have h := hc (subtupleCode x S)
  rw [projectListCode_subtupleCode x hTS] at h
  change tuplePrefixK U x T ≤ tuplePrefixK U x S + (c : ℕ∞) at h
  have hStop := tuplePrefixK_ne_top U hU x S
  have hRight : tuplePrefixK U x S + (c : ℕ∞) ≠ ⊤ :=
    WithTop.add_ne_top.mpr ⟨hStop, ENat.natCast_ne_top c⟩
  have hNat := ENat.toNat_le_toNat h hRight
  rw [ENat.toNat_add hStop (ENat.natCast_ne_top _)] at hNat
  rw [ENat.toNat_natCast] at hNat
  exact_mod_cast hNat
private lemma sum_ordered_marginals (f : Finset (Fin n) → ℝ) (S : Finset (Fin n)) :
    ∑ i ∈ S, (f (insert i (S ∩ lowerIndices i)) - f (S ∩ lowerIndices i)) =
      f S - f ∅ := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a s hlt ih =>
      have ha : a ∉ s := fun h => lt_irrefl a (hlt a h)
      have haa : insert a s ∩ lowerIndices a = s := by
        ext j
        simp only [mem_inter, mem_insert, lowerIndices, mem_filter, mem_univ, true_and]
        constructor
        · rintro ⟨hja | hj, hltj⟩
          · subst j
            exact False.elim (lt_irrefl _ hltj)
          · exact hj
        · intro hj
          exact ⟨Or.inr hj, hlt j hj⟩
      have hai : ∀ i ∈ s, insert a s ∩ lowerIndices i = s ∩ lowerIndices i := by
        intro i hi
        ext j
        simp only [mem_inter, mem_insert]
        constructor
        · rintro ⟨hja | hj, hji⟩
          · have hji' : j < i := by simpa [lowerIndices] using hji
            exact False.elim (lt_asymm (hlt i hi) (hja ▸ hji'))
          · exact ⟨hj, hji⟩
        · exact fun hj => ⟨Or.inr hj.1, hj.2⟩
      rw [sum_insert ha, haa]
      have hs : ∑ i ∈ s,
          (f (insert i (insert a s ∩ lowerIndices i)) -
            f (insert a s ∩ lowerIndices i)) =
          ∑ i ∈ s, (f (insert i (s ∩ lowerIndices i)) -
            f (s ∩ lowerIndices i)) := by
        exact sum_congr rfl fun i hi => by rw [hai i hi]
      rw [hs, ih]
      ring
/-- **Problem 284.**  For prefix complexity the inequalities of Theorem 204 hold with `O(1)`
precision instead of `O(log N)`: if every index is covered with total coefficient at least
`1`, then `K(x_1, …, x_n) ≤ ∑_I λ_I K(x_I) + O(1)` for all tuples of strings, with no bound on
their lengths.  SUV Problem 284, p. 318. -/
theorem tuple_prefix_complexity_le_weighted_sum (U : Map) (hU : IsOptimalPrefixConditional U)
    (lam : Finset (Fin n) → ℝ) (hnonneg : ∀ I, 0 ≤ lam I)
    (hproper : ∀ I : Finset (Fin n), I = ∅ ∨ I = Finset.univ → lam I = 0)
    (hcover : ∀ i : Fin n, 1 ≤ ∑ I ∈ Finset.univ.filter fun I : Finset (Fin n) => i ∈ I,
      lam I) :
    ∃ c : ℕ, ∀ x : Fin n → BitString,
      ((tuplePrefixK U x Finset.univ).toNat : ℝ)
        ≤ (∑ I : Finset (Fin n), lam I * ((tuplePrefixK U x I).toNat : ℝ)) + (c : ℝ) := by
  classical
  have hlamEmpty : lam ∅ = 0 := hproper ∅ (Or.inl rfl)
  cases n with
  | zero =>
      let x₀ : Fin 0 → BitString := fun i => Fin.elim0 i
      let c := (tuplePrefixK U x₀ Finset.univ).toNat
      refine ⟨c, fun x => ?_⟩
      have hx : x = x₀ := funext fun i => Fin.elim0 i
      subst x
      have hsum : 0 ≤ ∑ I : Finset (Fin 0),
          lam I * ((tuplePrefixK U x₀ I).toNat : ℝ) := by
        exact sum_nonneg fun I _ => mul_nonneg (hnonneg I) (Nat.cast_nonneg _)
      dsimp [c]
      linarith
  | succ k =>
      let cm : Fin (k + 1) → Finset (Fin (k + 1)) → ℕ := fun i I =>
        Classical.choose (tuplePrefixK_marginal U hU i I)
      have hcm : ∀ i I x,
          ((tuplePrefixK U x (insert i (lowerIndices i))).toNat : ℝ) +
              ((tuplePrefixK U x (I ∩ lowerIndices i)).toNat : ℝ) ≤
            ((tuplePrefixK U x (lowerIndices i)).toNat : ℝ) +
              ((tuplePrefixK U x (insert i (I ∩ lowerIndices i))).toNat : ℝ) +
                cm i I := fun i I =>
        Classical.choose_spec (tuplePrefixK_marginal U hU i I)
      let mm : Fin (k + 1) → ℕ := fun i => Classical.choose
        (tuplePrefixK_subset_le U hU (subset_insert i (lowerIndices i)))
      have hmm : ∀ i x,
          ((tuplePrefixK U x (lowerIndices i)).toNat : ℝ) ≤
            ((tuplePrefixK U x (insert i (lowerIndices i))).toNat : ℝ) + mm i :=
        fun i => Classical.choose_spec
          (tuplePrefixK_subset_le U hU (subset_insert i (lowerIndices i)))
      let q : Fin (k + 1) → ℝ := fun i =>
        ∑ I ∈ Finset.univ.filter fun I : Finset (Fin (k + 1)) => i ∈ I, lam I
      let err₁ : ℝ := ∑ I : Finset (Fin (k + 1)), lam I * ∑ i ∈ I, (cm i I : ℝ)
      let err₂ : ℝ := ∑ i : Fin (k + 1), (q i - 1) * (mm i : ℝ)
      obtain ⟨c, hc⟩ := exists_nat_ge (err₁ + err₂)
      refine ⟨c, fun x => ?_⟩
      let f : Finset (Fin (k + 1)) → ℝ := fun I => (tuplePrefixK U x I).toNat
      let d : Fin (k + 1) → ℝ := fun i =>
        f (insert i (lowerIndices i)) - f (lowerIndices i)
      let e : Finset (Fin (k + 1)) → Fin (k + 1) → ℝ := fun I i =>
        f (insert i (I ∩ lowerIndices i)) - f (I ∩ lowerIndices i)
      have hd_le : ∀ i I, d i ≤ e I i + cm i I := by
        intro i I
        dsimp [d, e, f]
        linarith [hcm i I x]
      have hset : ∀ I : Finset (Fin (k + 1)),
          ∑ i ∈ I, d i ≤ f I - f ∅ + ∑ i ∈ I, (cm i I : ℝ) := by
        intro I
        calc
          ∑ i ∈ I, d i ≤ ∑ i ∈ I, (e I i + cm i I) :=
            sum_le_sum fun i _ => hd_le i I
          _ = (∑ i ∈ I, e I i) + ∑ i ∈ I, (cm i I : ℝ) := by
            rw [sum_add_distrib]
          _ = f I - f ∅ + ∑ i ∈ I, (cm i I : ℝ) := by
            rw [show (∑ i ∈ I, e I i) = f I - f ∅ by
              simpa [e] using sum_ordered_marginals f I]
      have hweighted : ∑ I : Finset (Fin (k + 1)), lam I * ∑ i ∈ I, d i ≤
          ∑ I : Finset (Fin (k + 1)),
            lam I * (f I - f ∅ + ∑ i ∈ I, (cm i I : ℝ)) := by
        exact sum_le_sum fun I _ => mul_le_mul_of_nonneg_left (hset I) (hnonneg I)
      have hswap : (∑ I : Finset (Fin (k + 1)), lam I * ∑ i ∈ I, d i) =
          ∑ i : Fin (k + 1), q i * d i := by
        calc
          ∑ I : Finset (Fin (k + 1)), lam I * ∑ i ∈ I, d i =
              ∑ I : Finset (Fin (k + 1)), ∑ i ∈ I, lam I * d i := by
                apply sum_congr rfl
                intro I _
                rw [mul_sum]
          _ = ∑ i : Fin (k + 1),
              ∑ I ∈ Finset.univ.filter (fun I : Finset (Fin (k + 1)) => i ∈ I),
                lam I * d i := by
              simp only [sum_filter]
              rw [sum_comm]
              apply sum_congr rfl
              intro i _
              rw [sum_ite_mem, univ_inter]
          _ = ∑ i : Fin (k + 1), q i * d i := by
              apply sum_congr rfl
              intro i _
              rw [sum_mul]
      have hq : ∀ i, 1 ≤ q i := fun i => hcover i
      have hd_nonneg : ∀ i, 0 ≤ d i + mm i := by
        intro i
        dsimp [d, f]
        linarith [hmm i x]
      have hcoverStep : ∀ i, d i ≤ q i * d i + (q i - 1) * mm i := by
        intro i
        nlinarith [mul_nonneg (sub_nonneg.mpr (hq i)) (hd_nonneg i)]
      have hdsum : ∑ i : Fin (k + 1), d i ≤
          ∑ i : Fin (k + 1), q i * d i + err₂ := by
        calc
          ∑ i : Fin (k + 1), d i ≤
              ∑ i : Fin (k + 1), (q i * d i + (q i - 1) * mm i) :=
                sum_le_sum fun i _ => hcoverStep i
          _ = ∑ i : Fin (k + 1), q i * d i + err₂ := by
                rw [sum_add_distrib]
      have htotal : 1 ≤ ∑ I : Finset (Fin (k + 1)), lam I := by
        let i₀ : Fin (k + 1) := ⟨0, Nat.zero_lt_succ k⟩
        refine (hcover i₀).trans ?_
        exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          (fun I _ _ => hnonneg I)
      have htel : ∑ i : Fin (k + 1), d i = f Finset.univ - f ∅ := by
        simpa [d, Finset.univ_inter] using sum_ordered_marginals f Finset.univ
      have hfempty : 0 ≤ f ∅ := by positivity
      have halgebra :
          (∑ I : Finset (Fin (k + 1)),
              lam I * (f I - f ∅ + ∑ i ∈ I, (cm i I : ℝ))) =
            (∑ I : Finset (Fin (k + 1)), lam I * f I) -
              (∑ I : Finset (Fin (k + 1)), lam I) * f ∅ + err₁ := by
        dsimp [err₁]
        simp_rw [mul_add, mul_sub]
        rw [sum_add_distrib, sum_sub_distrib, ← sum_mul]
      rw [hswap, halgebra] at hweighted
      have hfinal : f Finset.univ ≤
          (∑ I : Finset (Fin (k + 1)), lam I * f I) + err₁ + err₂ := by
        rw [htel] at hdsum
        nlinarith [mul_nonneg (sub_nonneg.mpr htotal) hfempty]
      have _hproperUsed := hlamEmpty
      dsimp [f] at hfinal ⊢
      linarith

end Kolmogorov
