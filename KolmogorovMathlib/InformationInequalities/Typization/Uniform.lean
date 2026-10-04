import KolmogorovMathlib.InformationInequalities.Typization.Candidate

/-!
# The typization set is almost uniform (Theorem 211)

SUV Section 10.6, pp. 326–327, Theorem 211.

A typization candidate `A` for `x` already has `log |A| ≥ C(x) − O(log N)` and section sizes
bounded by `C(x_J | x_I) + O(log N)`.  Iterating the chain rule for complexities along every
ordering of the coordinates turns these bounds into the matching lower bounds on the sections
and into `N^d`-uniformity of `A`, which gives `exists_cUniform_typization`: an almost uniform set
whose projection and section sizes reproduce the complexities of the tuple up to `O(log N)`.
-/

namespace Kolmogorov

open Finset
open Kolmogorov.CodedFiniteDistribution

variable {n : ℕ}

/- Conditioning on the empty subtuple is the same as taking plain complexity. -/
private lemma tupleCondK_empty_eq_tuplePlainK (D : Map) (x : Fin n → BitString)
    (I : Finset (Fin n)) : tupleCondK D x I ∅ = tuplePlainK D x I := by
  simp [tupleCondK, tuplePlainK, plainK]

/- Packing any subtuple from descriptions of its coordinates costs at most a constant
multiple of the common complexity budget.  In particular this bounds every intermediate
prefix complexity which occurs while the binary chain rule is iterated. -/
private lemma exists_subtuple_complexity_linear_bound
    (D : Map) (hD : isOptimalConditional D) :
    ∃ b : ℕ, ∀ (N : ℕ), 1 < N → ∀ x : Fin n → BitString,
      (∀ i, plainK D (x i) ≤ (N : ℕ∞)) →
      ∀ I : Finset (Fin n), (tuplePlainK D x I).toNat ≤ b * N := by
  obtain ⟨a, b, hab⟩ := exists_listCode_complexity_linear (n := n) D hD
  refine ⟨a + b, fun N hN x hx I => ?_⟩
  have h_bound : plainK D (subtupleCode x I) ≤ ((a * N + b : ℕ) : ℕ∞) := by
    apply hab N ((I.sort (· ≤ ·)).map x)
    · simpa using Finset.card_le_univ I
    · intro z hz
      simp only [List.mem_map] at hz
      obtain ⟨i, _, rfl⟩ := hz
      exact hx i
  have h1 : (tuplePlainK D x I).toNat ≤ a * N + b := by
    simpa [tuplePlainK] using
      (ENat.toNat_le_toNat h_bound (ENat.natCast_ne_top _)).trans_eq (ENat.toNat_natCast _)
  have h2 : b ≤ b * N := Nat.le_mul_of_pos_right b (by omega)
  calc (tuplePlainK D x I).toNat ≤ a * N + b := h1
    _ ≤ a * N + b * N := by omega
    _ = (a + b) * N := (Nat.add_mul a b N).symm

/- Reindexing both subtuples in a conditional complexity changes only their packing order.
The resulting computable recoding has a fixed cost, made uniform over the finitely many
permutations and coordinates. -/
/-- Reindexing a list of strings by indices -/
private def typ_reindexList (idxs : List ℕ) (w : BitString) : BitString :=
  listCode (idxs.map (fun i => (decodeListCode w).getD i []))

/-- Reindexing a list of strings by indices is primrec -/
private lemma typ_map_getD_primrec (idxs : List ℕ) :
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

/-- Reindexing a list of strings by indices is computable -/
private lemma typ_map_getD_computable (idxs : List ℕ) :
    Computable (fun (w : BitString) => idxs.map (fun i => (decodeListCode w).getD i [])) :=
  (typ_map_getD_primrec idxs).to_comp

/-- Reindexing a list of strings by indices is computable -/
private lemma typ_reindexList_computable (idxs : List ℕ) : Computable (typ_reindexList idxs) := by
  have h_comp : Computable (fun w => idxs.map (fun i => (decodeListCode w).getD i [])) :=
    typ_map_getD_computable idxs
  exact listCode_computable.comp h_comp

/-- Indices to reindex a tuple -/
private def typ_idxList {n : ℕ} (σ : Equiv.Perm (Fin n)) (I : Finset (Fin n)) : List ℕ :=
  ((I.image σ.symm).sort (· ≤ ·)).map (fun j => List.findIdx (· == σ j) (I.sort (· ≤ ·)))

/-- Helper for finding index in a list -/
private lemma typ_list_findIdx_get_prop_go {α : Type} (p : α → Bool) (l : List α) (acc : ℕ)
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

/-- Element at found index satisfies the predicate -/
private lemma typ_list_findIdx_get_prop {α : Type} (p : α → Bool) (l : List α)
    (hi : List.findIdx p l < l.length) :
    p (l.get ⟨List.findIdx p l, hi⟩) = true := by
  have hi2 : List.findIdx.go p l 0 < l.length + 0 := by
    unfold List.findIdx at hi
    omega
  have h := typ_list_findIdx_get_prop_go p l 0 hi2
  rcases h with ⟨k, hk, heq, hget⟩
  have heq2 : List.findIdx p l = k := by
    unfold List.findIdx
    omega
  have h_eq_get : l.get ⟨List.findIdx p l, hi⟩ = l.get ⟨k, hk⟩ := by
    congr
  rw [h_eq_get]
  exact hget

/-- Element at found index by equality equals the search element -/
private lemma typ_list_findIdx_eq_of_unique {α : Type} [BEq α] [LawfulBEq α] (l : List α) (a : α)
    (ha : a ∈ l) :
    l.get ⟨List.findIdx (· == a) l, by
      apply List.findIdx_lt_length_of_exists
      exact ⟨a, ha, by simp⟩
    ⟩ = a := by
  have hi := List.findIdx_lt_length_of_exists (p := (· == a)) (xs := l)
    (by exact ⟨a, ha, by simp⟩)
  have h_prop : (· == a) (l.get ⟨List.findIdx (· == a) l, hi⟩) = true :=
    typ_list_findIdx_get_prop (· == a) l hi
  exact eq_of_beq h_prop

/-- Subtuple code equals reindexed subtuple code -/
private lemma typ_subtupleCode_eq_reindexList {n : ℕ} (σ : Equiv.Perm (Fin n))
    (x : Fin n → BitString) (I : Finset (Fin n)) :
    subtupleCode (x ∘ σ)
        (I.image σ.symm) = typ_reindexList (typ_idxList σ I) (subtupleCode x I) := by
  dsimp [subtupleCode, typ_reindexList, typ_idxList]
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
    exact typ_list_findIdx_eq_of_unique _ _ hi_sort
  exact h_getD.symm

private lemma exists_tupleCondK_reindex_bound
    (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ (x : Fin n → BitString) (σ : Equiv.Perm (Fin n)) (k : Fin n),
      tupleCondK D x {σ k} (earlierIndices σ k) ≤
        tupleCondK D (x ∘ σ) (({σ k} : Finset (Fin n)).image σ.symm)
          ((earlierIndices σ k).image σ.symm) + (c : ℕ∞) := by
  have H : ∀ σ k, ∃ c : ℕ, ∀ x, tupleCondK D x {σ k} (earlierIndices σ k) ≤
      tupleCondK D (x ∘ σ) (({σ k} : Finset (Fin n)).image σ.symm)
          ((earlierIndices σ k).image σ.symm) + (c : ℕ∞) := by
    intro σ k
    let J : Finset (Fin n) := {σ k}
    let I : Finset (Fin n) := earlierIndices σ k
    have h1 : Computable (typ_reindexList (typ_idxList σ.symm (J.image σ.symm))) :=
      typ_reindexList_computable _
    have h2 : Computable (typ_reindexList (typ_idxList σ I)) :=
      typ_reindexList_computable _
    obtain ⟨c1, hc1⟩ := condK_map_le D hD (typ_reindexList (typ_idxList σ.symm (J.image σ.symm))) h1
    obtain ⟨c2, hc2⟩ := condK_cond_map_le D hD (typ_reindexList (typ_idxList σ I)) h2
    use c1 + c2
    intro x
    have hj : subtupleCode x J = typ_reindexList (typ_idxList σ.symm (J.image σ.symm))
        (subtupleCode (x ∘ σ)
        (J.image σ.symm)) := by
      have h := typ_subtupleCode_eq_reindexList σ.symm (x ∘ σ) (J.image σ.symm)
      have heq1 : (x ∘ σ) ∘ σ.symm = x := by ext j; simp
      have heq2 : (J.image σ.symm).image σ = J := by ext j; simp
      rw [heq1] at h
      have h3 : (J.image σ.symm).image σ.symm.symm = (J.image σ.symm).image σ := rfl
      rw [h3] at h
      rw [heq2] at h
      exact h
    have hi : subtupleCode (x ∘ σ)
        (I.image σ.symm) = typ_reindexList (typ_idxList σ I) (subtupleCode x I) := by
      exact typ_subtupleCode_eq_reindexList σ x I
    unfold tupleCondK
    rw [hj]
    calc condK D (typ_reindexList (typ_idxList σ.symm (J.image σ.symm)) (subtupleCode (x ∘ σ)
        (J.image σ.symm))) (subtupleCode x I)
      _ ≤ condK D (subtupleCode (x ∘ σ) (J.image σ.symm)) (subtupleCode x I) + c1 := hc1 _ _
      _ ≤ (condK D (subtupleCode (x ∘ σ)
        (J.image σ.symm)) (typ_reindexList (typ_idxList σ I) (subtupleCode x I)) +
          (c2 : ℕ∞)) + (c1 : ℕ∞) := by
        have hc := hc2 (subtupleCode (x ∘ σ) (J.image σ.symm)) (subtupleCode x I)
        have h_add : condK D (subtupleCode (x ∘ σ)
        (J.image σ.symm)) (subtupleCode x I) + (c1 : ℕ∞) ≤ (condK D (subtupleCode (x ∘ σ)
        (J.image σ.symm)) (typ_reindexList (typ_idxList σ I) (subtupleCode x I)) +
          (c2 : ℕ∞)) + (c1 : ℕ∞) := by
          gcongr
        exact h_add
      _ = condK D (subtupleCode (x ∘ σ)
        (J.image σ.symm)) (subtupleCode (x ∘ σ) (I.image σ.symm)) + ((c1 : ℕ∞) + (c2 : ℕ∞)) := by
        rw [← hi, add_assoc, add_comm (c2 : ℕ∞)]
      _ = condK D (subtupleCode (x ∘ σ)
        (J.image σ.symm)) (subtupleCode (x ∘ σ) (I.image σ.symm)) + (c1 + c2 : ℕ∞) := by
        rw [← ENat.natCast_add]
  choose c_σ_k hc_σ_k using H
  use Finset.univ.sup (fun (pr : Equiv.Perm (Fin n) × Fin n) => c_σ_k pr.1 pr.2)
  intro x σ k
  have hc := hc_σ_k σ k x
  have hle : (c_σ_k σ k : ℕ∞) ≤ ((Finset.univ.sup (fun (pr : Equiv.Perm (Fin n) × Fin n) =>
      c_σ_k pr.1 pr.2)) : ℕ) := by
    norm_cast
    exact Finset.le_sup (f := fun (pr : Equiv.Perm (Fin n) × Fin n) =>
      c_σ_k pr.1 pr.2) (Finset.mem_univ (σ, k))
  exact hc.trans (add_le_add_right hle _)

/- The images under `σ⁻¹` of the current coordinate and its predecessors are respectively
the current natural coordinate and the natural initial segment below it. -/
private lemma permuted_chain_index_images (σ : Equiv.Perm (Fin n)) (k : Fin n) :
    (({σ k} : Finset (Fin n)).image σ.symm = {k}) ∧
      ((earlierIndices σ k).image σ.symm =
        Finset.univ.filter fun j => j < k) := by
  constructor
  · simp
  · ext j
    simp [earlierIndices]

/- Termwise conditional recoding, followed by summation over the fixed number of coordinates,
bounds the permuted conditional chain by the naturally ordered reindexed chain. -/
private lemma exists_permuted_conditional_sum_reindex_bound
    (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ (x : Fin n → BitString) (σ : Equiv.Perm (Fin n)),
      (∑ k : Fin n,
          ((tupleCondK D x {σ k} (earlierIndices σ k)).toNat : ℝ)) ≤
        (∑ k : Fin n,
          ((tupleCondK D (x ∘ σ) {k}
            (Finset.univ.filter fun j => j < k)).toNat : ℝ)) + c := by
  obtain ⟨a, ha⟩ := exists_tupleCondK_reindex_bound (n := n) D hD
  refine ⟨n * a, fun x σ => ?_⟩
  have hterm : ∀ k : Fin n,
      (tupleCondK D x {σ k} (earlierIndices σ k)).toNat ≤
        (tupleCondK D (x ∘ σ) {k}
          (Finset.univ.filter fun j => j < k)).toNat + a := by
    intro k
    have h := ha x σ k
    rw [(permuted_chain_index_images σ k).1,
      (permuted_chain_index_images σ k).2] at h
    have hfinite := tupleCondK_ne_top D hD (x ∘ σ) {k}
      (Finset.univ.filter fun j => j < k)
    have hnat := ENat.toNat_le_toNat h
      (WithTop.add_ne_top.mpr ⟨hfinite, ENat.natCast_ne_top _⟩)
    simpa [ENat.toNat_add hfinite (ENat.natCast_ne_top _)] using hnat
  calc
    _ ≤ ∑ k : Fin n,
        (((tupleCondK D (x ∘ σ) {k}
          (Finset.univ.filter fun j => j < k)).toNat : ℝ) + a) :=
      Finset.sum_le_sum fun k _ => by exact_mod_cast hterm k
    _ = _ := by simp [Finset.sum_add_distrib]

/- Repacking the complete tuple in permutation order has a uniformly bounded cost, since
there are only finitely many permutations. -/
private lemma exists_permuted_full_tuple_reindex_bound
    (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ (x : Fin n → BitString) (σ : Equiv.Perm (Fin n)),
      (tuplePlainK D (x ∘ σ) Finset.univ).toNat ≤
        (tuplePlainK D x Finset.univ).toNat + c := by
  classical
  choose c hc using fun σ : Equiv.Perm (Fin n) => tuplePlainK_reindex D hD σ
  refine ⟨Finset.univ.sup c, fun x σ => ?_⟩
  have h := hc σ x Finset.univ
  have hcost : c σ ≤ Finset.univ.sup c := Finset.le_sup (Finset.mem_univ σ)
  have hcostE : (c σ : ℕ∞) ≤ (↑(Finset.univ.sup c) : ℕ∞) := by
    exact_mod_cast hcost
  have h' : tuplePlainK D (x ∘ σ) Finset.univ ≤
      tuplePlainK D x Finset.univ + (↑(Finset.univ.sup c) : ℕ∞) := by
    simpa using h.trans (add_le_add_right hcostE _)
  have hfinite := tuplePlainK_ne_top D hD x Finset.univ
  have hnat := ENat.toNat_le_toNat h'
    (WithTop.add_ne_top.mpr ⟨hfinite, ENat.natCast_ne_top _⟩)
  simpa [ENat.toNat_add hfinite (ENat.natCast_ne_top _)] using hnat

/- Repacking the tuple in the order `σ` changes the complete chain expression by only a
constant.  Conditional terms and the full tuple are transported separately, and their two
fixed recoding costs are then combined. -/
private lemma exists_permuted_chain_reindex_bound
    (D : Map) (hD : isOptimalConditional D) :
    ∃ b : ℕ, ∀ (x : Fin n → BitString) (σ : Equiv.Perm (Fin n)),
      (∑ k : Fin n,
          ((tupleCondK D x {σ k} (earlierIndices σ k)).toNat : ℝ)) -
          ((tuplePlainK D x Finset.univ).toNat : ℝ)
        ≤ (∑ k : Fin n,
            ((tupleCondK D (x ∘ σ) {k}
              (Finset.univ.filter fun j => j < k)).toNat : ℝ)) -
            ((tuplePlainK D (x ∘ σ) Finset.univ).toNat : ℝ) + b := by
  obtain ⟨a, ha⟩ := exists_permuted_conditional_sum_reindex_bound (n := n) D hD
  obtain ⟨c, hc⟩ := exists_permuted_full_tuple_reindex_bound (n := n) D hD
  refine ⟨a + c, fun x σ => ?_⟩
  have hsum := ha x σ
  have hfull : ((tuplePlainK D (x ∘ σ) Finset.univ).toNat : ℝ) ≤
      (tuplePlainK D x Finset.univ).toNat + c := by
    exact_mod_cast hc x σ
  push_cast at hsum hfull ⊢
  linarith

/- A fixed additive recoding cost is absorbed by increasing the logarithmic allowance. -/
private lemma add_const_le_logSlack_add (a b N : ℕ) :
    (logSlack a N : ℝ) + b ≤ (logSlack (a + b) N : ℝ) := by
  have hb : (b : ℝ) ≤ logSlack b N := by
    have : b ≤ logSlack b N := by
      simp only [logSlack]
      omega
    exact_mod_cast this
  rw [show logSlack (a + b) N = logSlack a N + logSlack b N by
    exact logSlack_add_constants a b N]
  push_cast
  linarith

/- The binary chain rule for two disjoint subtuples, with its error measured by the
complexity budget of the individual coordinates.  Applying this successively to adjacent
blocks is the complexity-theoretic step used in the partition chain rule. -/
private lemma exists_disjoint_subtuple_chain_exponent
    (D : Map) (hD : isOptimalConditional D) :
    ∃ e : ℕ, ∀ (N : ℕ), 1 < N → ∀ x : Fin n → BitString,
      (∀ i, plainK D (x i) ≤ (N : ℕ∞)) →
      ∀ I J : Finset (Fin n), Disjoint I J →
        ((tupleCondK D x I ∅).toNat : ℝ) +
              ((tupleCondK D x J I).toNat : ℝ) -
            ((tupleCondK D x (I ∪ J) ∅).toNat : ℝ)
          ≤ (logSlack e N : ℝ) := by
  classical
  obtain ⟨U, hU⟩ := exists_isOptimalPrefixConditional
  obtain ⟨cChain, hChain⟩ := plainK_add_condK_le_plainK_pair D U hD hU
  obtain ⟨a, b, hprofile⟩ := exists_profile_component_linear_bound (n := n) D hD
  let positions (S T : Finset (Fin n)) : List ℕ :=
    (T.sort (· ≤ ·)).map fun i => (S.sort (· ≤ ·)).idxOf i
  let split (I J : Finset (Fin n)) (w : BitString) : BitString :=
    pairCode (typ_reindexList (positions (I ∪ J) I) w)
      (typ_reindexList (positions (I ∪ J) J) w)
  have hsplitComputable (I J : Finset (Fin n)) : Computable (split I J) := by
    exact CodedFiniteDistribution.pairCode_primrec.to_comp.comp
      (typ_reindexList_computable _) (typ_reindexList_computable _)
  have hproject (S T : Finset (Fin n)) (hTS : T ⊆ S) (x : Fin n → BitString) :
      typ_reindexList (positions S T) (subtupleCode x S) = subtupleCode x T := by
    simp only [typ_reindexList, positions, subtupleCode, decodeListCode_listCode,
      List.map_map]
    congr 1
    apply List.map_congr_left
    intro i hi
    have hiT : i ∈ T := by simpa using hi
    have hiS : i ∈ S.sort (· ≤ ·) := by simpa using hTS hiT
    simp [Function.comp_apply, List.getD_eq_getElem?_getD,
      List.getElem?_idxOf hiS]
  have hsplit (I J : Finset (Fin n)) (x : Fin n → BitString) :
      split I J (subtupleCode x (I ∪ J)) =
        pairCode (subtupleCode x I) (subtupleCode x J) := by
    simp only [split]
    rw [hproject (I ∪ J) I (Finset.subset_union_left) x,
      hproject (I ∪ J) J (Finset.subset_union_right) x]
  have hmapExists : ∀ I J : Finset (Fin n), ∃ c : ℕ, ∀ w : BitString,
      plainK D (split I J w) ≤ plainK D w + (c : ℕ∞) := by
    intro I J
    exact plainK_map_le D hD (split I J) (hsplitComputable I J)
  choose mapCost hmap using hmapExists
  let cMap := Finset.univ.sup fun p : Finset (Fin n) × Finset (Fin n) =>
    mapCost p.1 p.2
  have hmapCost (I J : Finset (Fin n)) : mapCost I J ≤ cMap := by
    exact Finset.le_sup (f := fun p : Finset (Fin n) × Finset (Fin n) =>
      mapCost p.1 p.2) (Finset.mem_univ (I, J))
  obtain ⟨cFold, hFold⟩ := logSlack_linear_bound cChain a (b + cMap)
  refine ⟨cMap + cFold, fun N hN x hx I J hIJ => ?_⟩
  have _ := hN
  have _ := hIJ
  let M := a * N + (b + cMap)
  have hcomplexity (K L : Finset (Fin n)) :
      tupleCondK D x K L ≤ (M : ℕ∞) := by
    rw [← ENat.natCast_toNat (tupleCondK_ne_top D hD x K L)]
    exact_mod_cast (hprofile N x hx L K).trans (by dsimp [M]; omega)
  have hplainI : plainK D (subtupleCode x I) ≤ (M : ℕ∞) := by
    simpa [tupleCondK, plainK] using hcomplexity I ∅
  have hpair : plainK D (pairCode (subtupleCode x I) (subtupleCode x J)) ≤
      plainK D (subtupleCode x (I ∪ J)) + (mapCost I J : ℕ∞) := by
    simpa only [hsplit I J x] using hmap I J (subtupleCode x (I ∪ J))
  have hpairBudget :
      plainK D (pairCode (subtupleCode x I) (subtupleCode x J)) ≤ (M : ℕ∞) := by
    calc
      plainK D (pairCode (subtupleCode x I) (subtupleCode x J))
          ≤ plainK D (subtupleCode x (I ∪ J)) + (mapCost I J : ℕ∞) := hpair
      _ ≤ tupleCondK D x (I ∪ J) ∅ + (cMap : ℕ∞) := by
        simpa [tupleCondK, plainK] using
          add_le_add_right (show (mapCost I J : ℕ∞) ≤ cMap by
            exact_mod_cast hmapCost I J) (plainK D (subtupleCode x (I ∪ J)))
      _ ≤ (((a * N + b : ℕ) : ℕ∞) + (cMap : ℕ∞)) := by
        gcongr
        rw [← ENat.natCast_toNat (tupleCondK_ne_top D hD x (I ∪ J) ∅)]
        exact_mod_cast hprofile N x hx ∅ (I ∪ J)
      _ = (M : ℕ∞) := by
        dsimp [M]
        push_cast
        ring
  have hbinary := hChain (subtupleCode x I) (subtupleCode x J) M hplainI hpairBudget
  have hENat :
      plainK D (subtupleCode x I) +
          condK D (subtupleCode x J) (subtupleCode x I) ≤
        plainK D (subtupleCode x (I ∪ J)) + (cMap : ℕ∞) +
          (logSlack cChain M : ℕ∞) := by
    exact hbinary.trans (by
      calc
        plainK D (pairCode (subtupleCode x I) (subtupleCode x J)) +
              (logSlack cChain M : ℕ∞)
            ≤ (plainK D (subtupleCode x (I ∪ J)) + (mapCost I J : ℕ∞)) +
              (logSlack cChain M : ℕ∞) := by gcongr
        _ ≤ (plainK D (subtupleCode x (I ∪ J)) + (cMap : ℕ∞)) +
              (logSlack cChain M : ℕ∞) := by
            gcongr
            exact_mod_cast hmapCost I J)
  have hplainIFinite := plainK_ne_top D hD (subtupleCode x I)
  have hcondFinite := condK_ne_top_of_optimal D hD
    (subtupleCode x J) (subtupleCode x I)
  have hunionFinite := plainK_ne_top D hD (subtupleCode x (I ∪ J))
  have hNat :
      (plainK D (subtupleCode x I)).toNat +
          (condK D (subtupleCode x J) (subtupleCode x I)).toNat ≤
        (plainK D (subtupleCode x (I ∪ J))).toNat + cMap +
          logSlack cChain M := by
    rw [← ENat.natCast_toNat hplainIFinite, ← ENat.natCast_toNat hcondFinite,
      ← ENat.natCast_toNat hunionFinite] at hENat
    exact_mod_cast hENat
  have herror : cMap + logSlack cChain M ≤ logSlack (cMap + cFold) N := by
    calc
      cMap + logSlack cChain M ≤ cMap + logSlack cFold N := by
        exact Nat.add_le_add_left (by simpa [M] using hFold N) cMap
      _ ≤ logSlack cMap N + logSlack cFold N := by
        have : cMap ≤ logSlack cMap N := by simp [logSlack]
        omega
      _ = logSlack (cMap + cFold) N :=
        (logSlack_add_constants cMap cFold N).symm
  have hfinalNat :
      (plainK D (subtupleCode x I)).toNat +
          (condK D (subtupleCode x J) (subtupleCode x I)).toNat ≤
        (plainK D (subtupleCode x (I ∪ J))).toNat +
          logSlack (cMap + cFold) N := by
    omega
  have hfinalReal :
      ((plainK D (subtupleCode x I)).toNat : ℝ) +
            ((condK D (subtupleCode x J) (subtupleCode x I)).toNat : ℝ) -
          ((plainK D (subtupleCode x (I ∪ J))).toNat : ℝ) ≤
        (logSlack (cMap + cFold) N : ℝ) := by
    have hfinalCast :
        ((plainK D (subtupleCode x I)).toNat : ℝ) +
            ((condK D (subtupleCode x J) (subtupleCode x I)).toNat : ℝ) ≤
          ((plainK D (subtupleCode x (I ∪ J))).toNat : ℝ) +
            (logSlack (cMap + cFold) N : ℝ) := by
      exact_mod_cast hfinalNat
    linarith
  simpa [tupleCondK, plainK] using hfinalReal

/- Telescoping the binary chain inequality along the prefixes `{j | j < m}` of the natural
coordinate order: each step loses at most the binary allowance `L`. -/
private lemma natural_chain_prefix_excess (D : Map) (x : Fin n → BitString) (L : ℝ)
    (he : ∀ I J : Finset (Fin n), Disjoint I J →
        ((tupleCondK D x I ∅).toNat : ℝ) + ((tupleCondK D x J I).toNat : ℝ) -
            ((tupleCondK D x (I ∪ J) ∅).toNat : ℝ) ≤ L) :
    ∀ m : ℕ, m ≤ n →
      (∑ k ∈ Finset.range m, (if hk : k < n then
          ((tupleCondK D x {⟨k, hk⟩} (Finset.univ.filter fun j : Fin n => j.1 < k)).toNat : ℝ)
          else 0)) +
        ((tupleCondK D x (Finset.univ.filter fun j : Fin n => j.1 < 0) ∅).toNat : ℝ) -
        ((tupleCondK D x (Finset.univ.filter fun j : Fin n => j.1 < m) ∅).toNat : ℝ)
        ≤ m * L := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    have hm_lt : m < n := by omega
    have h1 := ih (by omega)
    have hdisj : Disjoint (Finset.univ.filter fun j : Fin n => j.1 < m) {⟨m, hm_lt⟩} := by
      rw [Finset.disjoint_singleton_right]
      simp
    have h2 := he _ _ hdisj
    have hunion : (Finset.univ.filter fun j : Fin n => j.1 < m) ∪ {⟨m, hm_lt⟩} =
        Finset.univ.filter fun j : Fin n => j.1 < m + 1 := by
      ext y
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton, Fin.ext_iff]
      omega
    rw [hunion] at h2
    rw [Finset.sum_range_succ, dite_eq_left hm_lt]
    push_cast
    linarith

/- The lower binary chain inequality, iterated through the natural coordinate order.  The
shared bound on all intermediate subtuple complexities makes every binary logarithmic loss
at most one `logSlack`, and the fixed number of coordinates is absorbed in its constant. -/
private lemma exists_natural_chain_excess_of_subtuple_budget
    (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ (B : ℕ) (x : Fin n → BitString),
      (∀ I : Finset (Fin n), (tuplePlainK D x I).toNat ≤ B) →
      (∑ k : Fin n,
          ((tupleCondK D x {k} (Finset.univ.filter fun j => j < k)).toNat : ℝ)) -
          ((tuplePlainK D x Finset.univ).toNat : ℝ)
        ≤ (logSlack c B : ℝ) := by
  obtain ⟨e, he⟩ := exists_disjoint_subtuple_chain_exponent (n := n) D hD
  let f : BitString → BitString := fun w => (decodeListCode w).getD 0 []
  have hf : Computable f :=
    ((Primrec.list_getD ([] : BitString)).comp decodeListCode_primrec
      (Primrec.const 0)).to_comp
  obtain ⟨cx, hcx⟩ := plainK_map_le D hD f hf
  obtain ⟨C, hC⟩ := logSlack_linear_bound (n * e) 1 (cx + 2)
  refine ⟨C, fun B x hB => ?_⟩
  have hN : 1 < 1 * B + (cx + 2) := by omega
  have hx : ∀ i, plainK D (x i) ≤ ((1 * B + (cx + 2) : ℕ) : ℕ∞) := by
    intro i
    have hfi : f (subtupleCode x {i}) = x i := by
      simp only [f, subtupleCode, Finset.sort_singleton, List.map_cons, List.map_nil,
        decodeListCode_listCode]
      rfl
    have h1 := hcx (subtupleCode x {i})
    rw [hfi] at h1
    have hne := tuplePlainK_ne_top D hD x {i}
    have h2 : tuplePlainK D x {i} ≤ (B : ℕ∞) := by
      rw [← ENat.natCast_toNat hne]
      exact_mod_cast hB {i}
    have h3 : plainK D (subtupleCode x {i}) ≤ (B : ℕ∞) := h2
    calc plainK D (x i) ≤ plainK D (subtupleCode x {i}) + (cx : ℕ∞) := h1
      _ ≤ (B : ℕ∞) + (cx : ℕ∞) := by gcongr
      _ ≤ ((1 * B + (cx + 2) : ℕ) : ℕ∞) := by norm_cast; omega
  have haux := natural_chain_prefix_excess D x _ (he _ hN x hx) n le_rfl
  have hsum : (∑ k : Fin n,
      ((tupleCondK D x {k} (Finset.univ.filter fun j => j < k)).toNat : ℝ)) =
      ∑ k ∈ Finset.range n,
        (if hk : k < n then
        ((tupleCondK D x {⟨k, hk⟩} (Finset.univ.filter fun (j : Fin n) => j.1 < k)).toNat : ℝ)
        else 0) := by
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [dite_eq_left k.2]
    rfl
  have huniv : (Finset.univ.filter fun j : Fin n => j.1 < n) = Finset.univ :=
    Finset.filter_true_of_mem fun j _ => j.2
  rw [huniv, tupleCondK_empty_eq_tuplePlainK D x Finset.univ] at haux
  have hnonneg : (0 : ℝ) ≤
      ((tupleCondK D x (Finset.univ.filter fun (j : Fin n) => j.1 < 0) ∅).toNat : ℝ) :=
    Nat.cast_nonneg _
  have hslack : (n : ℝ) * (logSlack e (1 * B + (cx + 2)) : ℝ) =
      (logSlack (n * e) (1 * B + (cx + 2)) : ℝ) := by
    simp only [logSlack]
    push_cast
    ring
  have hfold : (logSlack (n * e) (1 * B + (cx + 2)) : ℝ) ≤ (logSlack C B : ℝ) := by
    exact_mod_cast hC B
  rw [hsum]
  linarith

/- A logarithmic loss evaluated at a fixed linear multiple of `N` is still a logarithmic
loss in `N`; this is the numerical absorption used after bounding the prefix complexities. -/
private lemma exists_logSlack_mul_bound (c b : ℕ) :
    ∃ a : ℕ, ∀ N : ℕ, logSlack c (b * N) ≤ logSlack a N := by
  exact logSlack_linear_bound c b 0

/- The lower half of the tuple chain rule in the natural coordinate order, with its error
measured by a bound on the component complexities.  This is obtained by iterating the binary
plain-complexity chain rule; all intermediate tuple complexities are bounded by a constant
multiple of `N`, so every logarithmic error is absorbed by one `logSlack`. -/
private lemma exists_natural_chain_excess_bound
    (D : Map) (hD : isOptimalConditional D) :
    ∃ a : ℕ, ∀ (N : ℕ), 1 < N → ∀ x : Fin n → BitString,
      (∀ i, plainK D (x i) ≤ (N : ℕ∞)) →
      (∑ k : Fin n,
          ((tupleCondK D x {k} (Finset.univ.filter fun j => j < k)).toNat : ℝ)) -
          ((tuplePlainK D x Finset.univ).toNat : ℝ)
        ≤ (logSlack a N : ℝ) := by
  obtain ⟨b, hb⟩ := exists_subtuple_complexity_linear_bound (n := n) D hD
  obtain ⟨c, hc⟩ := exists_natural_chain_excess_of_subtuple_budget (n := n) D hD
  obtain ⟨a, ha⟩ := exists_logSlack_mul_bound c b
  refine ⟨a, fun N hN x hx => ?_⟩
  have hbudget : ∀ I : Finset (Fin n), (tuplePlainK D x I).toNat ≤ b * N :=
    hb N hN x hx
  exact (hc (b * N) x hbudget).trans (by exact_mod_cast ha N)

/- The chain rule in the ordering imposed by `σ`, with the error measured by the complexity
budget rather than by the lengths of the strings.  This is the complexity-theoretic step in
the proof of typization: the sum of the successive conditional complexities differs from the
complexity of the whole tuple by `O(log N)`. -/
private lemma exists_permuted_chain_excess_bound
    (D : Map) (hD : isOptimalConditional D) :
    ∃ a : ℕ, ∀ (N : ℕ), 1 < N → ∀ x : Fin n → BitString,
      (∀ i, plainK D (x i) ≤ (N : ℕ∞)) →
      ∀ σ : Equiv.Perm (Fin n),
        (∑ k : Fin n,
            ((tupleCondK D x {σ k} (earlierIndices σ k)).toNat : ℝ)) -
            ((tupleCondK D x Finset.univ ∅).toNat : ℝ)
          ≤ (logSlack a N : ℝ) := by
  obtain ⟨a, ha⟩ := exists_natural_chain_excess_bound (n := n) D hD
  obtain ⟨b, hb⟩ := exists_permuted_chain_reindex_bound (n := n) D hD
  refine ⟨a + b, fun N hN x hx σ => ?_⟩
  have hxσ : ∀ i, plainK D ((x ∘ σ) i) ≤ (N : ℕ∞) := fun i => hx (σ i)
  have hnatural := ha N hN (x ∘ σ) hxσ
  have hreindex := hb x σ
  rw [tupleCondK_empty_eq_tuplePlainK]
  exact (hreindex.trans (by linarith)).trans (add_const_le_logSlack_add a b N)

/- Candidate section bounds, summed along a coordinate ordering and combined with the lower
bound for the cardinality, bound the logarithmic excess of every chain product. -/
private lemma exists_log_chainBound_excess_of_candidate
    (D : Map) (hD : isOptimalConditional D) (c : ℕ) :
    ∃ e : ℕ, ∀ (N : ℕ), 1 < N → ∀ x : Fin n → BitString,
      (∀ i, plainK D (x i) ≤ (N : ℕ∞)) →
      ∀ (m : ℕ) (A : Finset (Fin n → Fin m)),
        IsTypizationCandidate D x N c A →
        ∀ σ : Equiv.Perm (Fin n),
          Real.logb 2 (chainBound A σ) - Real.logb 2 A.card
            ≤ (logSlack e N : ℝ) := by
  obtain ⟨a, ha⟩ := exists_permuted_chain_excess_bound (n := n) D hD
  refine ⟨a + n * c + c, fun N hN x hx m A hA σ => ?_⟩
  have hcardpos : 0 < A.card := Finset.card_pos.2 hA.1
  have hchainpos : 0 < chainBound A σ :=
    lt_of_lt_of_le hcardpos (card_le_chainBound A σ)
  have hfactor : ∀ k : Fin n,
      maxSection A {σ k} (earlierIndices σ k) ≠ 0 := by
    intro k hk
    rw [chainBound, Finset.prod_eq_zero (Finset.mem_univ k) hk] at hchainpos
    omega
  have hdisjoint : ∀ k : Fin n, Disjoint (earlierIndices σ k) {σ k} := by
    intro k
    rw [Finset.disjoint_singleton_right]
    simp [earlierIndices]
  have hlogchain :
      Real.logb 2 (chainBound A σ) =
        ∑ k : Fin n, Real.logb 2 (maxSection A {σ k} (earlierIndices σ k)) := by
    rw [chainBound, Nat.cast_prod, Real.logb_prod]
    intro k _
    exact_mod_cast hfactor k
  have hsections : ∀ k : Fin n,
      Real.logb 2 (maxSection A {σ k} (earlierIndices σ k)) ≤
        ((tupleCondK D x {σ k} (earlierIndices σ k)).toNat : ℝ) +
          (logSlack c N : ℝ) := by
    intro k
    exact hA.2.2 (earlierIndices σ k) {σ k} (hdisjoint k)
  have hsum :
      Real.logb 2 (chainBound A σ) ≤
        (∑ k : Fin n,
          ((tupleCondK D x {σ k} (earlierIndices σ k)).toNat : ℝ)) +
            (n : ℝ) * logSlack c N := by
    rw [hlogchain]
    calc
      (∑ k : Fin n, Real.logb 2 (maxSection A {σ k} (earlierIndices σ k)))
          ≤ ∑ k : Fin n,
              (((tupleCondK D x {σ k} (earlierIndices σ k)).toNat : ℝ) +
                (logSlack c N : ℝ)) := Finset.sum_le_sum fun k _ => hsections k
      _ = (∑ k : Fin n,
            ((tupleCondK D x {σ k} (earlierIndices σ k)).toNat : ℝ)) +
              (n : ℝ) * logSlack c N := by
        rw [Finset.sum_add_distrib]
        simp
  have hchain := ha N hN x hx σ
  have hcard := hA.2.1
  calc
    Real.logb 2 (chainBound A σ) - Real.logb 2 A.card
        ≤ (logSlack a N : ℝ) + (n : ℝ) * logSlack c N + logSlack c N := by
          linarith
    _ = (logSlack (a + n * c + c) N : ℝ) := by
      simp only [logSlack]
      push_cast
      ring

/- A logarithmic slack is at most a constant multiple of `log₂ N` once `N > 1`; exponentiating
therefore turns an additive `O(log N)` loss into a polynomial factor. -/
private lemma logSlack_le_three_mul_logb (e N : ℕ) (hN : 1 < N) :
    (logSlack e N : ℝ) ≤ (3 * e : ℝ) * Real.logb 2 N := by
  have hsizepos : 0 < Nat.size N := Nat.size_pos.mpr (by omega)
  have hpow : 2 ^ (Nat.size N - 1) ≤ N := by
    rw [← Nat.lt_size]
    omega
  have hpowR : (2 : ℝ) ^ (Nat.size N - 1) ≤ N := by
    exact_mod_cast hpow
  have hNR : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlog : ((Nat.size N - 1 : ℕ) : ℝ) ≤ Real.logb 2 N := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) hNR, Real.rpow_natCast]
    exact hpowR
  have hone : (1 : ℝ) ≤ Real.logb 2 N := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) hNR, Real.rpow_one]
    exact_mod_cast hN
  have hsize : (Nat.size N : ℝ) ≤ Real.logb 2 N + 1 := by
    have hs : Nat.size N - 1 + 1 = Nat.size N := Nat.sub_add_cancel hsizepos
    have hsR : (Nat.size N : ℝ) = ((Nat.size N - 1 : ℕ) : ℝ) + 1 := by
      exact_mod_cast hs.symm
    rw [hsR]
    linarith
  have hbits : ((Nat.bits N).length : ℝ) ≤ Real.logb 2 N + 1 := by
    simpa [Nat.size_eq_bits_len] using hsize
  simp only [logSlack]
  push_cast
  have hmul := mul_le_mul_of_nonneg_left hbits (show (0 : ℝ) ≤ e by positivity)
  nlinarith

/- Exponentiating a uniform logarithmic bound for all chain products gives `c`-uniformity. -/
private lemma isCUniform_of_log_chainBound_excess {m e N : ℕ}
    (hN : 1 < N) {A : Finset (Fin n → Fin m)} (hA : A.Nonempty)
    (hlog : ∀ σ : Equiv.Perm (Fin n),
      Real.logb 2 (chainBound A σ) - Real.logb 2 A.card
        ≤ (logSlack e N : ℝ)) :
    IsCUniform ((N : ℝ) ^ (3 * e)) A := by
  intro σ
  have hcardpos : (0 : ℝ) < A.card := by exact_mod_cast Finset.card_pos.2 hA
  have hchainpos : (0 : ℝ) < chainBound A σ := by
    exact_mod_cast lt_of_lt_of_le (Finset.card_pos.2 hA) (card_le_chainBound A σ)
  apply (Real.logb_le_logb (b := 2) (by norm_num) hchainpos (by positivity)).mp
  rw [Real.logb_mul (by positivity) hcardpos.ne', Real.logb_pow]
  have hslack := logSlack_le_three_mul_logb e N hN
  have hgap := hlog σ
  push_cast at hslack ⊢
  nlinarith

private lemma exists_cUniform_exponent_of_candidate
    (D : Map) (hD : isOptimalConditional D) (c : ℕ) :
    ∃ d : ℕ, ∀ (N : ℕ), 1 < N → ∀ x : Fin n → BitString,
      (∀ i, plainK D (x i) ≤ (N : ℕ∞)) →
      ∀ (m : ℕ) (A : Finset (Fin n → Fin m)),
        IsTypizationCandidate D x N c A → IsCUniform ((N : ℝ) ^ d) A := by
  obtain ⟨e, he⟩ := exists_log_chainBound_excess_of_candidate (n := n) D hD c
  refine ⟨3 * e, fun N hN x hx m A hA => ?_⟩
  exact isCUniform_of_log_chainBound_excess hN hA.1 (he N hN x hx m A hA)

/- A set of coordinates and its complement are disjoint and together exhaust all
coordinates.  This supplies the second pair of adjacent blocks in the partition chain. -/
private lemma union_complement_partition (S : Finset (Fin n)) :
    Disjoint S (Finset.univ \ S) ∧ S ∪ (Finset.univ \ S) = Finset.univ := by
  constructor
  · exact Finset.disjoint_sdiff
  · exact Finset.union_sdiff_of_subset (Finset.subset_univ S)

/- The logarithmic chain rule in the ordering obtained by first listing `I`, then `J`, and
finally the remaining coordinates.  This is the complexity-theoretic step in the lower
section estimate of the typization proof. -/
private lemma exists_partition_chain_exponent (D : Map) (hD : isOptimalConditional D) :
    ∃ e : ℕ, ∀ (N : ℕ), 1 < N → ∀ x : Fin n → BitString,
      (∀ i, plainK D (x i) ≤ (N : ℕ∞)) →
      ∀ I J : Finset (Fin n), Disjoint I J →
        let K := Finset.univ \ (I ∪ J)
        ((tupleCondK D x I ∅).toNat : ℝ) +
              ((tupleCondK D x J I).toNat : ℝ) +
              ((tupleCondK D x K (I ∪ J)).toNat : ℝ) -
            ((tupleCondK D x Finset.univ ∅).toNat : ℝ)
          ≤ (logSlack e N : ℝ) := by
  obtain ⟨e, he⟩ := exists_disjoint_subtuple_chain_exponent (n := n) D hD
  refine ⟨e + e, fun N hN x hx I J hIJ => ?_⟩
  let K := Finset.univ \ (I ∪ J)
  have hpartition := union_complement_partition (I ∪ J)
  have hfirst := he N hN x hx I J hIJ
  have hsecond := he N hN x hx (I ∪ J) K hpartition.1
  have hsecond' :
      ((tupleCondK D x (I ∪ J) ∅).toNat : ℝ) +
            ((tupleCondK D x K (I ∪ J)).toNat : ℝ) -
          ((tupleCondK D x Finset.univ ∅).toNat : ℝ)
        ≤ (logSlack e N : ℝ) := by
    rw [hpartition.2] at hsecond
    exact hsecond
  dsimp [K]
  calc
    ((tupleCondK D x I ∅).toNat : ℝ) +
            ((tupleCondK D x J I).toNat : ℝ) +
            ((tupleCondK D x (Finset.univ \ (I ∪ J)) (I ∪ J)).toNat : ℝ) -
          ((tupleCondK D x Finset.univ ∅).toNat : ℝ)
        ≤ (logSlack e N : ℝ) + logSlack e N := by
          dsimp [K] at hsecond'
          linarith
    _ = (logSlack (e + e) N : ℝ) := by
      exact_mod_cast (logSlack_add_constants e e N).symm

/- Splitting the coordinates into `I`, `J`, and their complement bounds the size of a set by
the product of the three successive maximal sections. -/
private lemma card_le_partition_sections {m : ℕ} (A : Finset (Fin n → Fin m))
    (I J : Finset (Fin n)) (hIJ : Disjoint I J) :
    let K := Finset.univ \ (I ∪ J)
    A.card ≤ maxSection A I ∅ *
      (maxSection A J I * maxSection A K (I ∪ J)) := by
  let K := Finset.univ \ (I ∪ J)
  have hrest : Disjoint (I ∪ J) K := Finset.disjoint_sdiff
  have hIK : Disjoint I K := (Finset.disjoint_union_left.mp hrest).1
  have hJK : Disjoint J K := (Finset.disjoint_union_left.mp hrest).2
  have hIJK : Disjoint I (J ∪ K) := Finset.disjoint_union_right.2 ⟨hIJ, hIK⟩
  have hunion : I ∪ (J ∪ K) = Finset.univ := by
    rw [← Finset.union_assoc, Finset.union_sdiff_of_subset (Finset.subset_univ (I ∪ J))]
  have hfirst := maxSection_union_le A ∅ I (J ∪ K)
    (Finset.disjoint_empty_left _) (Finset.disjoint_empty_left _) hIJK
  have hsecond := maxSection_union_le A I J K hIJ hIK hJK
  calc
    A.card = maxSection A Finset.univ ∅ := by rw [maxSection_empty, projCard_univ]
    _ = maxSection A (I ∪ (J ∪ K)) ∅ := by rw [hunion]
    _ ≤ maxSection A I ∅ * maxSection A (J ∪ K) I := by simpa using hfirst
    _ ≤ maxSection A I ∅ *
        (maxSection A J I * maxSection A K (I ∪ J)) :=
      Nat.mul_le_mul_left _ hsecond

/- The full-cardinality lower bound for a candidate, the two unused section upper bounds,
and the partition chain rule give the reverse estimate for the selected section. -/
private lemma exists_candidate_section_lower_exponent
    (D : Map) (hD : isOptimalConditional D) (c : ℕ) :
    ∃ d : ℕ, ∀ (N : ℕ), 1 < N → ∀ x : Fin n → BitString,
      (∀ i, plainK D (x i) ≤ (N : ℕ∞)) →
      ∀ (m : ℕ) (A : Finset (Fin n → Fin m)),
        IsTypizationCandidate D x N c A →
        ∀ I J : Finset (Fin n), Disjoint I J →
          ((tupleCondK D x J I).toNat : ℝ) - Real.logb 2 (maxSection A J I)
            ≤ (logSlack d N : ℝ) := by
  obtain ⟨e, he⟩ := exists_partition_chain_exponent (n := n) D hD
  refine ⟨e + 3 * c, fun N hN x hx m A hA I J hIJ => ?_⟩
  let K := Finset.univ \ (I ∪ J)
  have hrest : Disjoint (I ∪ J) K := Finset.disjoint_sdiff
  have hcard := card_le_partition_sections A I J hIJ
  have hcardPos : 0 < A.card := Finset.card_pos.2 hA.1
  have hprodPos : 0 < maxSection A I ∅ *
      (maxSection A J I * maxSection A K (I ∪ J)) := hcardPos.trans_le hcard
  have hmI : 0 < maxSection A I ∅ := Nat.pos_of_mul_pos_right hprodPos
  have hmJK : 0 < maxSection A J I * maxSection A K (I ∪ J) :=
    Nat.pos_of_mul_pos_left hprodPos
  have hmJ : 0 < maxSection A J I := Nat.pos_of_mul_pos_right hmJK
  have hmK : 0 < maxSection A K (I ∪ J) := Nat.pos_of_mul_pos_left hmJK
  have hcardLog : Real.logb 2 A.card ≤
      Real.logb 2 (maxSection A I ∅) + Real.logb 2 (maxSection A J I) +
        Real.logb 2 (maxSection A K (I ∪ J)) := by
    have hcardPosR : (0 : ℝ) < A.card := by exact_mod_cast hcardPos
    have hcardR : (A.card : ℝ) ≤ (maxSection A I ∅ : ℝ) *
        ((maxSection A J I : ℝ) * maxSection A K (I ∪ J)) := by
      exact_mod_cast hcard
    have hlog := Real.logb_le_logb_of_le (b := (2 : ℝ)) (by norm_num) hcardPosR
      hcardR
    rw [Real.logb_mul (by exact_mod_cast hmI.ne')
        (mul_ne_zero (by exact_mod_cast hmJ.ne') (by exact_mod_cast hmK.ne')),
      Real.logb_mul (by exact_mod_cast hmJ.ne') (by exact_mod_cast hmK.ne')] at hlog
    simpa [add_assoc] using hlog
  have hfull := hA.2.1
  have hupperI := hA.2.2 ∅ I (Finset.disjoint_empty_left _)
  have hupperK := hA.2.2 (I ∪ J) K hrest
  have hchain := he N hN x hx I J hIJ
  have hbound : ((tupleCondK D x J I).toNat : ℝ) -
      Real.logb 2 (maxSection A J I) ≤
        (logSlack e N : ℝ) + 3 * (logSlack c N : ℝ) := by
    dsimp [K] at hchain hupperK ⊢
    linarith
  calc
    ((tupleCondK D x J I).toNat : ℝ) - Real.logb 2 (maxSection A J I)
        ≤ (logSlack e N : ℝ) + 3 * (logSlack c N : ℝ) := hbound
    _ = (logSlack (e + 3 * c) N : ℝ) := by
      dsimp [logSlack]
      push_cast
      ring

private lemma exists_section_exponent_of_candidate
    (D : Map) (hD : isOptimalConditional D) (c : ℕ) :
    ∃ d : ℕ, ∀ (N : ℕ), 1 < N → ∀ x : Fin n → BitString,
      (∀ i, plainK D (x i) ≤ (N : ℕ∞)) →
      ∀ (m : ℕ) (A : Finset (Fin n → Fin m)),
        IsTypizationCandidate D x N c A →
        ∀ I J : Finset (Fin n), Disjoint I J →
          |Real.logb 2 (maxSection A J I) - ((tupleCondK D x J I).toNat : ℝ)|
            ≤ (logSlack d N : ℝ) := by
  obtain ⟨dLower, hLower⟩ := exists_candidate_section_lower_exponent (n := n) D hD c
  refine ⟨dLower + c, fun N hN x hx m A hA I J hIJ => ?_⟩
  rw [abs_le]
  have hlower := hLower N hN x hx m A hA I J hIJ
  have hupper := hA.2.2 I J hIJ
  have hslackLower : (logSlack dLower N : ℝ) ≤ logSlack (dLower + c) N := by
    exact_mod_cast logSlack_mono_left (Nat.le_add_right dLower c) N
  have hslackUpper : (logSlack c N : ℝ) ≤ logSlack (dLower + c) N := by
    exact_mod_cast logSlack_mono_left (Nat.le_add_left c dLower) N
  constructor <;> linarith

private lemma isCUniform_mono {m : ℕ} {c c' : ℝ}
    {A : Finset (Fin n → Fin m)} (hcc : c ≤ c') (hA : IsCUniform c A) :
    IsCUniform c' A := by
  intro σ
  exact (hA σ).trans (mul_le_mul_of_nonneg_right hcc (by positivity))

/-- **Theorem 211 (A. Romashchenko; typization).**  For every `n` there is a constant `d`
such that for every `N > 1` and every tuple `x_1, …, x_n` of strings of complexity at most `N`
there is an `N^d`-uniform set `A` whose section sizes reproduce the conditional complexities of
the tuple: `|log m_A(J | I) − C(x_J | x_I)| ≤ d log N` for all disjoint `I, J`
(with `m(J | ∅) = m(J)` and `C(x_J | x_∅) = C(x_J)`).

The restriction to **disjoint** `I, J` is the book's own: the printed theorem says "for all
disjoint subsets `I, J ⊂ {1, …, n}`", and `m_A(J | I)` is defined on p. 318 only for disjoint
`I` and `J` (the Lean `maxSection A J I` is total, but for overlapping `I, J` it is not the
book's `m_A(J | I)`).  The complexity vector of the proof is likewise indexed by the pairs of
disjoint subsets.

The book's finite sets `X_1, …, X_n` are "not really relevant" (p. 326); here all coordinates
take values in one `Fin m`, and the `O(log N)` bound is written with `logSlack d N`.  The
constant `d` depends on `n` only — it is quantified after `n` and `D` and before `N` and the
strings; the book remarks that it grows exponentially with `n`.
SUV Theorem 211, p. 326. -/
theorem exists_cUniform_typization (D : Map) (hD : isOptimalConditional D) :
    ∃ d : ℕ, ∀ (N : ℕ), 1 < N → ∀ x : Fin n → BitString,
      (∀ i, plainK D (x i) ≤ (N : ℕ∞)) →
      ∃ (m : ℕ) (A : Finset (Fin n → Fin m)), A.Nonempty ∧
        IsCUniform ((N : ℝ) ^ d) A ∧
        ∀ I J : Finset (Fin n), Disjoint I J →
          |Real.logb 2 (maxSection A J I) - ((tupleCondK D x J I).toNat : ℝ)|
            ≤ (logSlack d N : ℝ) := by
  obtain ⟨c, hc⟩ := exists_isTypizationCandidate (n := n) D hD
  obtain ⟨dUniform, hUniform⟩ :=
    exists_cUniform_exponent_of_candidate (n := n) D hD c
  obtain ⟨dSection, hSection⟩ :=
    exists_section_exponent_of_candidate (n := n) D hD c
  refine ⟨dUniform + dSection, fun N hN x hx => ?_⟩
  obtain ⟨m, A, hA⟩ := hc N hN x hx
  have hU := hUniform N hN x hx m A hA
  have hbase : (1 : ℝ) ≤ N := by exact_mod_cast hN.le
  have hpow : (N : ℝ) ^ dUniform ≤ (N : ℝ) ^ (dUniform + dSection) :=
    pow_le_pow_right₀ hbase (by omega)
  refine ⟨m, A, hA.1, isCUniform_mono hpow hU, fun I J hIJ => ?_⟩
  exact (hSection N hN x hx m A hA I J hIJ).trans (by
    exact_mod_cast logSlack_mono_left (by omega : dSection ≤ dUniform + dSection) N)

end Kolmogorov
