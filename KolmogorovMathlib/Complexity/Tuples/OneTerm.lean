/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Complexity.Tuples.ChainRule

/-!
# One-term inequalities for tuples of strings (Theorem 204)

SUV Section 10.1, pp. 313–318.

Section 10.1 answers completely the question "which linear inequalities
`∑_I λ_I C(x_I) ≤ O(log N)` are true?" in the special case where the left-hand side is the
single term `C(x_1, …, x_n)` and all the coefficients on the right are non-negative
(Theorem 204, `tuple_complexity_le_weighted_sum_iff`).  The proof is the chain rule for an
`n`-tuple (`Complexity/Tuples/ChainRule.lean`), applied in one fixed ordering of the indices on
both sides; the supporting fact that the complexity of a subtuple does not depend on the order
in which its components are packed is `tuplePlainK_reindex`.

All complexities in this file are **plain** complexities with respect to an explicit
decompressor `D`, quantified by `isOptimalConditional D`.

The coefficients are a family `lam : Finset (Fin n) → ℝ` that vanishes at `∅` and at the whole
index set; that is exactly the book's "the sum is taken over non-empty `I` except
`I = {1, …, n}`" (p. 317).
-/

namespace Kolmogorov

open Finset

variable {n : ℕ}

/-- Reorder a list code: the `k`-th entry of the result is the entry of the decoded list at
position `idxs[k]` (the empty string when that position does not exist). -/
private def reindexList (idxs : List ℕ) (w : BitString) : BitString :=
  listCode (idxs.map (fun i => (decodeListCode w).getD i []))
private lemma map_getD_primrec (idxs : List ℕ) :
    Primrec (fun (w : BitString) => idxs.map (fun i => (decodeListCode w).getD i [])) := by
  induction idxs with
  | nil =>
    exact Primrec.const []
  | cons head tail ih =>
    have h : (fun w => (head :: tail).map (fun i => (decodeListCode w).getD i [])) =
             (fun w => (decodeListCode w).getD head [] ::
               tail.map (fun i => (decodeListCode w).getD i [])) := rfl
    rw [h]
    have h_getD : Primrec (fun (w : BitString) => (decodeListCode w).getD head []) := by
      have h1 : Primrec decodeListCode := decodeListCode_primrec
      have h2 : Primrec (fun w : BitString => head) := Primrec.const head
      have h3 := Primrec.list_getD (α := BitString) ([] : BitString)
      exact h3.comp h1 h2
    exact Primrec₂.comp Primrec.list_cons h_getD ih
private lemma map_getD_computable (idxs : List ℕ) :
    Computable (fun (w : BitString) => idxs.map (fun i => (decodeListCode w).getD i [])) :=
  (map_getD_primrec idxs).to_comp
private lemma reindexList_computable (idxs : List ℕ) : Computable (reindexList idxs) := by
  have h_comp : Computable (fun w => idxs.map (fun i => (decodeListCode w).getD i [])) :=
    map_getD_computable idxs
  exact listCode_computable.comp h_comp
private def idxList {n : ℕ} (σ : Equiv.Perm (Fin n)) (I : Finset (Fin n)) : List ℕ :=
  ((I.image σ.symm).sort (· ≤ ·)).map (fun j => List.findIdx (· == σ j) (I.sort (· ≤ ·)))
private lemma list_findIdx_get_prop_go {α : Type} (p : α → Bool) (l : List α) (acc : ℕ)
    (hi : List.findIdx.go p l acc < l.length + acc) :
    ∃ n : ℕ, ∃ hn : n < l.length, List.findIdx.go p l acc = n + acc ∧
      p (l.get ⟨n, hn⟩) = true := by
  induction l generalizing acc with
  | nil =>
    dsimp [List.findIdx.go] at hi
    omega
  | cons a l ih =>
    unfold List.findIdx.go at hi ⊢
    cases h : p a
    · simp only [h, Bool.false_eq_true, ↓reduceIte] at hi ⊢
      have hi2 : List.findIdx.go p l (acc + 1) < l.length + (acc + 1) := by
        have h_len : (a :: l).length = l.length + 1 := by simp
        omega
      have ih_l := ih (acc + 1) hi2
      rcases ih_l with ⟨k, hk, heq, hget⟩
      refine ⟨k + 1, by omega, by omega, hget⟩
    · simp only [h, ↓reduceIte] at hi ⊢
      refine ⟨0, by omega, by omega, h⟩
private lemma list_findIdx_get_prop {α : Type} (p : α → Bool) (l : List α)
    (hi : List.findIdx p l < l.length) :
    p (l.get ⟨List.findIdx p l, hi⟩) = true := by
  have hi2 : List.findIdx.go p l 0 < l.length + 0 := by
    unfold List.findIdx at hi
    omega
  have h := list_findIdx_get_prop_go p l 0 hi2
  rcases h with ⟨k, hk, heq, hget⟩
  have heq2 : List.findIdx p l = k := by
    unfold List.findIdx
    omega
  have h_eq_get : l.get ⟨List.findIdx p l, hi⟩ = l.get ⟨k, hk⟩ := by
    congr
  rw [h_eq_get]
  exact hget
private lemma list_findIdx_eq_of_unique {α : Type} [BEq α] [LawfulBEq α] (l : List α) (a : α)
    (ha : a ∈ l) :
    l.get ⟨List.findIdx (· == a) l, by
      apply List.findIdx_lt_length_of_exists
      exact ⟨a, ha, by simp⟩
    ⟩ = a := by
  have hi := List.findIdx_lt_length_of_exists (p := (· == a)) (xs := l)
    (by exact ⟨a, ha, by simp⟩)
  have h_prop : (· == a) (l.get ⟨List.findIdx (· == a) l, hi⟩) = true :=
    list_findIdx_get_prop (· == a) l hi
  exact eq_of_beq h_prop
private lemma subtupleCode_eq_reindexList {n : ℕ} (σ : Equiv.Perm (Fin n))
    (x : Fin n → BitString) (I : Finset (Fin n)) :
    subtupleCode (x ∘ σ) (I.image σ.symm) = reindexList (idxList σ I) (subtupleCode x I) := by
  dsimp [subtupleCode, reindexList, idxList]
  rw [decodeListCode_listCode]
  congr 1
  rw [List.map_map]
  apply List.map_congr_left
  intro j hj
  have hj' : j ∈ (I.image σ.symm).sort (· ≤ ·) := hj
  rw [Finset.mem_sort, Finset.mem_image] at hj'
  rcases hj' with ⟨i, hi, heq⟩
  subst heq
  have h_eq : (x ∘ σ) (σ.symm i) = x i := by simp
  rw [h_eq]
  dsimp
  have h_find : List.findIdx (· == σ (σ.symm i)) (I.sort (· ≤ ·)) =
    List.findIdx (· == i) (I.sort (· ≤ ·)) := by simp
  rw [h_find]
  have hi_sort : i ∈ I.sort (· ≤ ·) := by rwa [Finset.mem_sort]
  have h_idx := List.findIdx_lt_length_of_exists (p := (· == i)) (xs := I.sort (· ≤ ·))
    (by exact ⟨i, hi_sort, by simp⟩)
  have h_getD : (List.map x (I.sort (· ≤ ·))).getD
    (List.findIdx (· == i) (I.sort (· ≤ ·))) [] = x i := by
    have h_idx2 : List.findIdx (· == i) (I.sort (· ≤ ·)) <
      (List.map x (I.sort (· ≤ ·))).length := by simpa using h_idx
    rw [List.getD_eq_get _ _ ⟨List.findIdx (· == i) (I.sort (· ≤ ·)), h_idx2⟩]
    have h_idx_eq : (List.map x (I.sort (· ≤ ·))).get
      ⟨List.findIdx (· == i) (I.sort (· ≤ ·)), h_idx2⟩ =
        x ((I.sort (· ≤ ·)).get ⟨List.findIdx (· == i) (I.sort (· ≤ ·)), h_idx⟩) := by simp
    rw [h_idx_eq]
    congr 1
    exact list_findIdx_eq_of_unique _ _ hi_sort
  exact h_getD.symm
/-- The complexity of a subtuple does not depend on the order in which its components are
packed: reindexing the tuple along a permutation `σ` and the index set along `σ⁻¹` changes the
complexity by at most an additive constant.  Applying the statement to `σ⁻¹` gives the reverse
inequality, so the two complexities agree up to `O(1)`.  SUV Section 10.1, p. 314. -/
theorem tuplePlainK_reindex (D : Map) (hD : isOptimalConditional D) (σ : Equiv.Perm (Fin n)) :
    ∃ c : ℕ, ∀ (x : Fin n → BitString) (I : Finset (Fin n)),
      tuplePlainK D (x ∘ σ) (I.image σ.symm) ≤ tuplePlainK D x I + (c : ℕ∞) := by
  have H : ∀ I, ∃ c_I : ℕ, ∀ x, tuplePlainK D (x ∘ σ) (I.image σ.symm) ≤
      tuplePlainK D x I + (c_I : ℕ∞) := by
    intro I
    have h_comp := reindexList_computable (idxList σ I)
    have h_bound := plainK_map_le D hD (reindexList (idxList σ I)) h_comp
    rcases h_bound with ⟨c_I, hc_I⟩
    use c_I
    intro x
    have h_sub := subtupleCode_eq_reindexList σ x I
    have h_K : tuplePlainK D (x ∘ σ) (I.image σ.symm) =
      plainK D (subtupleCode (x ∘ σ) (I.image σ.symm)) := rfl
    rw [h_K, h_sub]
    have h_K2 : tuplePlainK D x I = plainK D (subtupleCode x I) := rfl
    rw [h_K2]
    exact hc_I (subtupleCode x I)
  choose c_I hc_I using H
  use Finset.univ.sup c_I
  intro x I
  have h1 := hc_I I x
  have h2 : (c_I I : ℕ∞) ≤ ((Finset.univ.sup c_I : ℕ) : ℕ∞) :=
    ENat.natCast_le_natCast.mpr (Finset.le_sup (Finset.mem_univ I))
  exact le_trans h1 (add_le_add_right h2 _)
private def subsetPositions (S T : Finset (Fin n)) : List ℕ :=
  (T.sort (· ≤ ·)).map fun i => (S.sort (· ≤ ·)).idxOf i
@[simp] private lemma reindexList_subtupleCode (x : Fin n → BitString)
    {S T : Finset (Fin n)} (hTS : T ⊆ S) :
    reindexList (subsetPositions S T) (subtupleCode x S) = subtupleCode x T := by
  simp only [reindexList, subsetPositions, subtupleCode, decodeListCode_listCode,
    List.map_map]
  congr 1; apply List.map_congr_left
  intro i hi
  have hiT : i ∈ T := by simpa using hi
  have hiS : i ∈ S := hTS hiT
  have hiSort : i ∈ S.sort (· ≤ ·) := by simpa
  simp [Function.comp_apply, List.getD_eq_getElem?_getD, List.getElem?_idxOf hiSort]
private def paddedPositions (S T : Finset (Fin n)) : List ℕ :=
  (S.sort (· ≤ ·)).map fun i => if i ∈ T then (T.sort (· ≤ ·)).idxOf i else T.card
@[simp] private lemma reindexList_padded_subtupleCode (x : Fin n → BitString)
    (S T : Finset (Fin n)) :
    reindexList (paddedPositions S T) (subtupleCode x T) =
      subtupleCode (fun i => if i ∈ T then x i else []) S := by
  simp only [reindexList, paddedPositions, subtupleCode, decodeListCode_listCode,
    List.map_map]
  congr 1; apply List.map_congr_left
  intro i hi
  have hiS : i ∈ S := by simpa using hi
  by_cases hiT : i ∈ T
  · have hiSort : i ∈ T.sort (· ≤ ·) := by simpa
    simp [hiT, Function.comp_apply, List.getD_eq_getElem?_getD,
      List.getElem?_idxOf hiSort]
  · have hcard : (T.sort (· ≤ ·)).length = T.card := Finset.length_sort _
    simp [hiT, List.getD_eq_getElem?_getD, hcard]
private lemma nonpos_of_mul_le_logSlack_here (a : ℝ) (c : ℕ)
    (h : ∀ N : ℕ, (N : ℝ) * a ≤ (logSlack c N : ℝ)) : a ≤ 0 := by
  by_contra ha
  have ha_pos : 0 < a := lt_of_not_ge ha
  obtain ⟨k, hk⟩ := exists_nat_gt ((4 * c : ℝ) / a + 1)
  have hk_pos : 0 < k := by
    have : (0 : ℝ) < k := lt_of_le_of_lt (by positivity) (lt_trans (lt_add_one _) hk)
    exact_mod_cast this
  have hk_a : (4 * c : ℝ) < k * a := by
    exact (div_lt_iff₀ ha_pos).mp (lt_trans (lt_add_one _) hk)
  have hbits : (Nat.bits (k * k)).length ≤ k + 2 := by
    simpa using bits_length_le_sqrt_add_two (k * k)
  have hmain := h (k * k)
  have hlog : (logSlack c (k * k) : ℝ) ≤ (c : ℝ) * (k + 2) + c := by
    exact_mod_cast Nat.add_le_add_right (Nat.mul_le_mul_left c hbits) c
  have hk_one : (1 : ℝ) ≤ k := by exact_mod_cast hk_pos
  push_cast at hmain hlog hk_a hk_one
  nlinarith [show (0 : ℝ) ≤ c by positivity]
private lemma toNat_le_add_of_le {a b : ℕ∞} {c : ℕ} (h : a ≤ b + c) (hb : b ≠ ⊤) :
    a.toNat ≤ b.toNat + c := by
  have hn := ENat.toNat_le_toNat h (WithTop.add_ne_top.mpr ⟨hb, ENat.natCast_ne_top _⟩)
  simpa [ENat.toNat_add hb (ENat.natCast_ne_top _)] using hn
/-- **Theorem 204.**  For non-negative coefficients `λ_I` indexed by the non-empty proper
subsets of `{1, …, n}`, the inequality
`C(x_1, …, x_n) ≤ ∑_I λ_I C(x_I) + O(log N)` — for every `N` and all strings `x_i` of length
at most `N` — holds if and only if for every index `i` the sum of the coefficients of the terms
that contain `x_i` is at least `1`.  The constant hidden in `O(log N)` depends on `n` and on
the coefficients but not on the strings, which is why it is existentially quantified inside
the left-hand side of the equivalence.  SUV Theorem 204, p. 317. -/
theorem tuple_complexity_le_weighted_sum_iff (D : Map) (hD : isOptimalConditional D)
    (lam : Finset (Fin n) → ℝ) (hnonneg : ∀ I, 0 ≤ lam I)
    (hproper : ∀ I : Finset (Fin n), I = ∅ ∨ I = Finset.univ → lam I = 0) :
    (∃ c : ℕ, ∀ (N : ℕ) (x : Fin n → BitString), tupleMaxLength x ≤ N →
        ((tuplePlainK D x Finset.univ).toNat : ℝ)
          ≤ (∑ I : Finset (Fin n), lam I * ((tuplePlainK D x I).toNat : ℝ)) + (logSlack c N : ℝ))
      ↔ ∀ i : Fin n, 1 ≤ ∑ I ∈ Finset.univ.filter fun I : Finset (Fin n) => i ∈ I, lam I := by
  classical
  have _hproper := hproper; constructor
  · rintro ⟨c, hc⟩ i
    let q : ℝ := ∑ I ∈ Finset.univ.filter fun I : Finset (Fin n) => i ∈ I, lam I
    obtain ⟨cLen, hcLen⟩ := plainK_le_length D hD
    obtain ⟨cOne, hcOne⟩ := plainK_map_le D hD (fun s => listCode [s]) (listCode_computable.comp
        (Primrec₂.comp Primrec.list_cons Primrec.id (Primrec.const [])).to_comp)
    obtain ⟨cOut, hcOut⟩ := plainK_map_le D hD (fun w => (decodeListCode w).getD 0 [])
      ((Primrec.list_getD ([] : BitString)).comp decodeListCode_primrec (Primrec.const 0)).to_comp
    let cp : Finset (Fin n) → ℕ := fun I => Classical.choose
      (plainK_map_le D hD (reindexList (paddedPositions I {i})) (reindexList_computable _))
    have hcp : ∀ I w, plainK D (reindexList (paddedPositions I {i}) w) ≤
        plainK D w + (cp I : ℕ∞) := fun I => Classical.choose_spec
      (plainK_map_le D hD (reindexList (paddedPositions I {i})) (reindexList_computable _))
    obtain ⟨cProj, hcProj⟩ := plainK_map_le D hD
      (reindexList (subsetPositions Finset.univ {i})) (reindexList_computable _)
    let ce := fun I : Finset (Fin n) => (tuplePlainK D (fun _ => []) I).toNat
    let B : ℝ := ∑ I : Finset (Fin n), lam I * (if i ∈ I then cLen + cOne + cp I else ce I)
    obtain ⟨C, hC⟩ := exists_nat_ge (cOut + cProj + B + c)
    change 1 ≤ q; apply sub_nonpos.mp
    apply nonpos_of_mul_le_logSlack_here (1 - q) C; intro m
    obtain ⟨s, hslen, hs⟩ := exists_incompressible_string D [] m
    let x : Fin n → BitString := fun j => if j = i then s else []
    have hxlen : tupleMaxLength x ≤ m := by
      apply Finset.sup_le; intro j _; simp only [x]; split <;> simp_all
    have hsingle : subtupleCode x {i} = listCode [s] := by simp [subtupleCode, x]
    have hallLower : (m : ℝ) ≤ (tuplePlainK D x Finset.univ).toNat + cOut + cProj := by
      have hp := hcOut (subtupleCode x {i})
      rw [hsingle, decodeListCode_listCode, List.getD_cons_zero] at hp
      have hfin := tuplePlainK_ne_top D hD x Finset.univ
      have hproj := hcProj (subtupleCode x Finset.univ)
      rw [reindexList_subtupleCode x (by simp)] at hproj
      change tuplePlainK D x {i} ≤ tuplePlainK D x Finset.univ + (cProj : ℕ∞) at hproj
      have hn := toNat_le_add_of_le hproj hfin
      have hsNat : m ≤ (plainK D s).toNat := ENat.toNat_le_toNat hs (plainK_ne_top D hD s)
      have hone : plainK D (pairCode s []) ≠ ⊤ := plainK_ne_top D hD _
      have hpNat := toNat_le_add_of_le hp hone
      have hpNat' : (plainK D s).toNat ≤ (tuplePlainK D x {i}).toNat + cOut := by
        simpa [tuplePlainK, hsingle, ENat.toNat_add hone (ENat.natCast_ne_top _)] using hpNat
      norm_cast at hsNat hn ⊢
      linarith
    have hsub : ∀ I, ((tuplePlainK D x I).toNat : ℝ) ≤
        (if i ∈ I then m + cLen + cOne + cp I else ce I) := by
      intro I; by_cases hiI : i ∈ I
      · have hp := hcp I (subtupleCode x {i})
        rw [reindexList_padded_subtupleCode x I {i}, hsingle] at hp
        have heq : (fun j => if j ∈ ({i} : Finset (Fin n)) then x j else []) = x := by
          funext j; simp only [Finset.mem_singleton, x]
          split <;> simp_all
        rw [heq] at hp; have hk := hcLen s
        have hone : plainK D (pairCode s []) ≠ ⊤ := plainK_ne_top D hD _
        have hn := toNat_le_add_of_le hp hone
        have hk' := toNat_le_add_of_le hk (ENat.natCast_ne_top _)
        have ho := toNat_le_add_of_le (hcOne s) (plainK_ne_top D hD s)
        have hn' : (tuplePlainK D x I).toNat ≤ (plainK D (listCode [s])).toNat + cp I := by
          simpa [tuplePlainK, ENat.toNat_add hone (ENat.natCast_ne_top _)] using hn
        have hk'' : (plainK D s).toNat ≤ s.length + cLen := by
          simpa [ENat.toNat_add (ENat.natCast_ne_top _) (ENat.natCast_ne_top _)] using hk'
        have ho' : (plainK D (listCode [s])).toNat ≤ (plainK D s).toNat + cOne := by
          simpa [ENat.toNat_add (plainK_ne_top D hD s) (ENat.natCast_ne_top _)] using ho
        simp only [ite_eq_left hiI]
        norm_cast at hn' hk'' ho' ⊢; rw [hslen] at hk''
        omega
      · have heq : subtupleCode x I = subtupleCode (fun _ => ([] : BitString)) I := by
          unfold subtupleCode
          congr 1; apply List.map_congr_left
          intro j hj
          have hjI : j ∈ I := by simpa using hj
          simp [x, ne_of_mem_of_not_mem hjI hiI]
        simp [tuplePlainK, heq, ce, hiI]
    have hw := hc m x hxlen
    have hsum : ∑ I : Finset (Fin n), lam I * ((tuplePlainK D x I).toNat : ℝ) ≤ q * m + B := by
      calc
        _ ≤ ∑ I : Finset (Fin n), lam I * (if i ∈ I then m + cLen + cOne + cp I else ce I) :=
          sum_le_sum fun I _ => mul_le_mul_of_nonneg_left (hsub I) (hnonneg I)
        _ = q * m + B := by
          dsimp [q, B]; rw [sum_mul]
          rw [show (∑ I ∈ Finset.univ.filter (fun I : Finset (Fin n) => i ∈ I), lam I * (m : ℝ)) =
              ∑ I, if i ∈ I then lam I * m else 0 by rw [sum_filter]]
          rw [← sum_add_distrib]; apply sum_congr rfl
          intro I _; by_cases hi : i ∈ I
          · simp [hi]; ring
          · simp [hi]
    have hslack : (logSlack c m : ℝ) + cOut + cProj + B ≤ logSlack C m := by
      simp only [logSlack]; have hb : (0 : ℝ) ≤ (Nat.bits m).length := by positivity
      have hB : 0 ≤ B := sum_nonneg fun I _ => mul_nonneg (hnonneg I) (by positivity)
      push_cast at hC ⊢; nlinarith
    dsimp [q]; linarith
  · intro hcover
    obtain ⟨cu, hchain⟩ := tuple_chain_rule (n := n) D hD
    have hu : ∀ (N : ℕ) (x : Fin n → BitString), tupleMaxLength x ≤ N →
        ((tuplePlainK D x Finset.univ).toNat : ℝ)
          - ∑ i : Fin n, ((tupleCondK D x {i} (lowerIndices i)).toNat : ℝ)
        ≤ (logSlack cu N : ℝ) := fun N x hx => (abs_le.1 (hchain N x hx)).2
    obtain ⟨cl, hl⟩ : ∃ cl : ℕ, ∀ (N : ℕ) (x : Fin n → BitString), tupleMaxLength x ≤ N →
        (∑ i : Fin n, ((tupleCondK D x {i} (lowerIndices i)).toNat : ℝ))
          - ((tuplePlainK D x Finset.univ).toNat : ℝ)
        ≤ (logSlack cl N : ℝ) :=
      ⟨cu, fun N x hx => by linarith [(abs_le.1 (hchain N x hx)).1]⟩
    let cd : Fin n → Finset (Fin n) → ℕ := fun i I => Classical.choose
      (condK_cond_map_le D hD (reindexList (subsetPositions (lowerIndices i) (I ∩ lowerIndices i)))
          (reindexList_computable _))
    have hcd : ∀ i I z w, condK D z w ≤ condK D z
        (reindexList (subsetPositions (lowerIndices i) (I ∩ lowerIndices i)) w) +
          (cd i I : ℕ∞) := fun i I => Classical.choose_spec (condK_cond_map_le D hD (reindexList
        (subsetPositions (lowerIndices i) (I ∩ lowerIndices i))) (reindexList_computable _))
    let cp : Fin n → Finset (Fin n) → ℕ := fun i I => Classical.choose
      (condK_cond_map_le D hD (reindexList (paddedPositions (lowerIndices i) (I ∩ lowerIndices i)))
          (reindexList_computable _))
    have hcp : ∀ i I z w, condK D z w ≤ condK D z
        (reindexList (paddedPositions (lowerIndices i) (I ∩ lowerIndices i)) w) +
          (cp i I : ℕ∞) := fun i I => Classical.choose_spec (condK_cond_map_le D hD (reindexList
        (paddedPositions (lowerIndices i) (I ∩ lowerIndices i))) (reindexList_computable _))
    let ct : Finset (Fin n) → ℕ := fun I => Classical.choose
      (plainK_map_le D hD (reindexList (paddedPositions Finset.univ I)) (reindexList_computable _))
    have hct : ∀ I w, plainK D (reindexList (paddedPositions Finset.univ I) w) ≤
        plainK D w + (ct I : ℕ∞) := fun I => Classical.choose_spec
      (plainK_map_le D hD (reindexList (paddedPositions Finset.univ I)) (reindexList_computable _))
    let e : Finset (Fin n) → ℝ := fun I =>
      ∑ i ∈ I, ((cd i I : ℝ) + cp i I) + ct I
    let A : ℝ := ∑ I : Finset (Fin n), lam I
    let E : ℝ := ∑ I : Finset (Fin n), lam I * e I
    obtain ⟨c, hc⟩ := exists_nat_ge (cu + A * cl + E + A * cl)
    refine ⟨c, fun N x hx => ?_⟩
    let a : Fin n → ℝ := fun i =>
      (tupleCondK D x {i} (lowerIndices i)).toNat
    have hset : ∀ I : Finset (Fin n), ∑ i ∈ I, a i ≤
        ((tuplePlainK D x I).toNat : ℝ) + logSlack cl N + e I := by
      intro I; let y : Fin n → BitString := fun j => if j ∈ I then x j else []
      have hy : tupleMaxLength y ≤ N := by
        apply Finset.sup_le; intro j _
        by_cases hj : j ∈ I
        · simpa [y, hj] using (length_le_tupleMaxLength x j).trans hx
        · simp [y, hj]
      have hterm : ∀ i ∈ I, a i ≤
          ((tupleCondK D y {i} (lowerIndices i)).toNat : ℝ) + cd i I + cp i I := by
        intro i hi
        have h1 := hcd i I (subtupleCode x {i}) (subtupleCode x (lowerIndices i))
        rw [reindexList_subtupleCode x (by simp)] at h1
        have h2 := hcp i I (subtupleCode x {i}) (subtupleCode x (I ∩ lowerIndices i))
        rw [reindexList_padded_subtupleCode x (lowerIndices i) (I ∩ lowerIndices i)] at h2
        have hyone : subtupleCode y {i} = subtupleCode x {i} := by
          unfold subtupleCode; congr 1
          apply List.map_congr_left; intro j hj
          have : j = i := by simpa using hj
          subst j; simp [y, hi]
        have hylow : subtupleCode y (lowerIndices i) =
            subtupleCode (fun j => if j ∈ I ∩ lowerIndices i then x j else [])
              (lowerIndices i) := by
          unfold subtupleCode; congr 1
          apply List.map_congr_left; intro j hj
          have hjl : j ∈ lowerIndices i := by simpa using hj
          simp [y, hjl]
        have hyinter : subtupleCode y (I ∩ lowerIndices i) =
            subtupleCode x (I ∩ lowerIndices i) := by
          unfold subtupleCode; congr 1
          apply List.map_congr_left; intro j hj
          have hjmem : j ∈ I ∩ lowerIndices i := by simpa using hj
          have hjI : j ∈ I := (Finset.mem_inter.mp hjmem).1
          simp [y, hjI]
        rw [← hylow, ← hyone, ← hyinter] at h2
        have hf1 := tupleCondK_ne_top D hD x {i} (I ∩ lowerIndices i)
        have hf2 := tupleCondK_ne_top D hD y {i} (lowerIndices i)
        change tupleCondK D x {i} (lowerIndices i) ≤
          tupleCondK D x {i} (I ∩ lowerIndices i) + (cd i I : ℕ∞) at h1
        change tupleCondK D y {i} (I ∩ lowerIndices i) ≤
          tupleCondK D y {i} (lowerIndices i) + (cp i I : ℕ∞) at h2
        have hn1 := toNat_le_add_of_le h1 hf1
        have hn2 := toNat_le_add_of_le h2 hf2
        have hmid : tupleCondK D x {i} (I ∩ lowerIndices i) =
            tupleCondK D y {i} (I ∩ lowerIndices i) := by
          simp only [tupleCondK, hyone, hyinter]
        rw [hmid] at hn1
        have hn1R : ((tupleCondK D x {i} (lowerIndices i)).toNat : ℝ) ≤
            (tupleCondK D y {i} (I ∩ lowerIndices i)).toNat + cd i I := by
          exact_mod_cast hn1
        have hn2R : ((tupleCondK D y {i} (I ∩ lowerIndices i)).toNat : ℝ) ≤
            (tupleCondK D y {i} (lowerIndices i)).toNat + cp i I := by
          exact_mod_cast hn2
        dsimp [a]; linarith
      have hs : ∑ i ∈ I, a i ≤
          ∑ i : Fin n, ((tupleCondK D y {i} (lowerIndices i)).toNat : ℝ) +
            ∑ i ∈ I, ((cd i I : ℝ) + cp i I) := by
        calc
          _ ≤ ∑ i ∈ I, (((tupleCondK D y {i} (lowerIndices i)).toNat : ℝ) +
              ((cd i I : ℝ) + cp i I)) :=
            sum_le_sum fun i hi => by simpa [add_assoc] using hterm i hi
          _ = (∑ i ∈ I, ((tupleCondK D y {i} (lowerIndices i)).toNat : ℝ)) +
              ∑ i ∈ I, ((cd i I : ℝ) + cp i I) := by rw [sum_add_distrib]
          _ ≤ _ := by
            have hh : ∑ i ∈ I, ((tupleCondK D y {i} (lowerIndices i)).toNat : ℝ) ≤
                ∑ i : Fin n, ((tupleCondK D y {i} (lowerIndices i)).toNat : ℝ) :=
              sum_le_sum_of_subset_of_nonneg (subset_univ I) (fun _ _ _ => Nat.cast_nonneg _)
            linarith
      have ht := hct I (subtupleCode x I)
      rw [reindexList_padded_subtupleCode x Finset.univ I] at ht
      have hf := tuplePlainK_ne_top D hD x I
      change tuplePlainK D y Finset.univ ≤ tuplePlainK D x I + (ct I : ℕ∞) at ht
      have htn := toNat_le_add_of_le ht hf
      have htnR : ((tuplePlainK D y Finset.univ).toNat : ℝ) ≤
          (tuplePlainK D x I).toNat + ct I := by exact_mod_cast htn
      dsimp [e]; linarith [hl N y hy, htnR]
    have hcoverSum : ∑ i : Fin n, a i ≤
        ∑ I : Finset (Fin n), lam I * ∑ i ∈ I, a i := by
      calc
        _ ≤ ∑ i : Fin n, (∑ I ∈ Finset.univ.filter fun I : Finset (Fin n) => i ∈ I, lam I) * a i :=
          sum_le_sum fun i _ => (le_mul_of_one_le_left (by positivity) (hcover i))
        _ = ∑ i : Fin n, ∑ I ∈ Finset.univ.filter
              (fun I : Finset (Fin n) => i ∈ I), lam I * a i := by
          apply sum_congr rfl; intro i _
          rw [sum_mul]
        _ = _ := by
          simp only [sum_filter]; rw [sum_comm]
          apply sum_congr rfl; intro I _
          rw [sum_ite_mem, univ_inter, ← mul_sum]
    have hw := sum_le_sum fun I (_ : I ∈ Finset.univ) =>
      mul_le_mul_of_nonneg_left (hset I) (hnonneg I)
    have hmain := hu N x hx; simp_rw [mul_add] at hw
    rw [sum_add_distrib, sum_add_distrib, ← sum_mul] at hw
    change (∑ I : Finset (Fin n), lam I * ∑ i ∈ I, a i) ≤
      (∑ I, lam I * ((tuplePlainK D x I).toNat : ℝ)) + A * logSlack cl N + E at hw
    simp only [a] at hcoverSum
    simp only [logSlack] at hc hw hmain ⊢
    have hb : (0 : ℝ) ≤ (Nat.bits N).length := by positivity
    have hA : 0 ≤ A := sum_nonneg fun I _ => hnonneg I
    have hE : 0 ≤ E := sum_nonneg fun I _ =>
      mul_nonneg (hnonneg I) (by dsimp [e]; positivity)
    simp only [a] at hw
    push_cast at hc hw hmain ⊢
    have hcoef : (cu : ℝ) + A * cl ≤ c := by nlinarith
    have hconst : (cu : ℝ) + A * cl + E ≤ c := by nlinarith
    have hmul := mul_le_mul_of_nonneg_right hcoef hb
    have herr : (cu : ℝ) * (Nat.bits N).length + cu +
        A * ((cl : ℝ) * (Nat.bits N).length + cl) + E ≤ (c : ℝ) * (Nat.bits N).length + c := by
      nlinarith
    linarith

end Kolmogorov
