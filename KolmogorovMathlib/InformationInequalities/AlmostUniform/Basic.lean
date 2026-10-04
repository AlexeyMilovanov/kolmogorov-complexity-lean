import Mathlib.Data.Fin.Tuple.Sort
import KolmogorovMathlib.InformationInequalities.UniformSetsTheorems

/-!
# Almost uniform sets: sections, projections and subsets

SUV Section 10.5, Theorem 210(a)–(c), p. 324.

A set `A ⊆ X_1 × ⋯ × X_n` is `c`-uniform (`IsCUniform`) when, for every ordering of the
coordinates, the chain product bounding `|A|` exceeds `|A|` by a factor at most `c`.  For such
sets the two-step section inequality is tight up to `c` (Theorem 210(a),
`maxSection_mul_le_of_isCUniform`), projections stay `c`-uniform (Theorem 210(b),
`isCUniform_image_of_injective`), and a subset holding an `ε`-fraction is `c/ε`-uniform
(Theorem 210(c), `isCUniform_of_subset`).  The three-block form of the chain inequality,
`three_block_maxSection_le_of_isCUniform`, is also used for Theorem 210(e).
-/

namespace Kolmogorov

open Finset

variable {n : ℕ}

section General

variable {X : Fin n → Type} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]

private def my_rankOf_b (I J K : Finset (Fin n)) (i : Fin n) : ℕ :=
  if i ∈ I then 0 else if i ∈ J then 1 else if i ∈ K then 2 else 3

private theorem my_filter_rankOf_le_zero_b (I J K : Finset (Fin n)) :
    (Finset.univ.filter fun i => my_rankOf_b I J K i ≤ 0) = I := by
  ext i
  unfold my_rankOf_b
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  split_ifs <;> simp [*]

private theorem my_filter_rankOf_le_one_b (I J K : Finset (Fin n)) :
    (Finset.univ.filter fun i => my_rankOf_b I J K i ≤ 1) = I ∪ J := by
  ext i
  unfold my_rankOf_b
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
  split_ifs <;> simp [*]

private theorem my_filter_rankOf_le_two_b (I J K : Finset (Fin n)) :
    (Finset.univ.filter fun i => my_rankOf_b I J K i ≤ 2) = I ∪ J ∪ K := by
  ext i
  unfold my_rankOf_b
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
  split_ifs <;> simp [*]

private def my_prefixSet_b (σ : Equiv.Perm (Fin n)) (l : ℕ) : Finset (Fin n) :=
  (Finset.univ.filter fun j : Fin n => j.val < l).image σ

private theorem my_mem_prefixSet_b {σ : Equiv.Perm (Fin n)} {l : ℕ} {i : Fin n} :
    i ∈ my_prefixSet_b σ l ↔ (σ.symm i).val < l := by
  simp only [my_prefixSet_b, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj, rfl⟩
    simpa using hj
  · intro h
    exact ⟨σ.symm i, by simpa using h, by simp⟩

private theorem my_earlierIndices_eq_prefixSet_b (σ : Equiv.Perm (Fin n)) (k : Fin n) :
    earlierIndices σ k = my_prefixSet_b σ k.val := rfl

private theorem my_prefixSet_zero_b (σ : Equiv.Perm (Fin n)) : my_prefixSet_b σ 0 = ∅ := by
  ext i
  simp [my_mem_prefixSet_b]

private theorem my_prefixSet_of_le_b (σ : Equiv.Perm (Fin n)) {l : ℕ} (hl : n ≤ l) :
    my_prefixSet_b σ l = Finset.univ := by
  ext i
  simp only [my_mem_prefixSet_b, Finset.mem_univ, iff_true]
  exact lt_of_lt_of_le (σ.symm i).isLt hl

private theorem my_prefixSet_mono_b (σ : Equiv.Perm (Fin n)) {k l : ℕ} (hkl : k ≤ l) :
    my_prefixSet_b σ k ⊆ my_prefixSet_b σ l := fun _ hi =>
  my_mem_prefixSet_b.2 (lt_of_lt_of_le (my_mem_prefixSet_b.1 hi) hkl)

private theorem my_prefixSet_succ_b (σ : Equiv.Perm (Fin n)) {l : ℕ} (hl : l < n) :
    my_prefixSet_b σ (l + 1) = insert (σ ⟨l, hl⟩) (my_prefixSet_b σ l) := by
  ext i
  simp only [my_mem_prefixSet_b, Finset.mem_insert, ← Equiv.symm_apply_eq, Fin.ext_iff]
  omega

private theorem my_apply_notMem_prefixSet_b (σ : Equiv.Perm (Fin n)) {l : ℕ} (hl : l < n) :
    σ ⟨l, hl⟩ ∉ my_prefixSet_b σ l := by
  simp [my_mem_prefixSet_b]

private theorem my_prefixSet_succ_sdiff_b (σ : Equiv.Perm (Fin n)) {k l : ℕ} (hkl : k ≤ l)
    (hl : l < n) :
    my_prefixSet_b σ (l + 1) \ my_prefixSet_b σ k =
      (my_prefixSet_b σ l \ my_prefixSet_b σ k) ∪ {σ ⟨l, hl⟩} := by
  rw [my_prefixSet_succ_b σ hl, Finset.insert_sdiff_of_notMem _
    (fun h => my_apply_notMem_prefixSet_b σ hl (my_prefixSet_mono_b σ hkl h)),
      Finset.insert_eq, Finset.union_comm]

private theorem my_disjoint_prefixSet_singleton_b (σ : Equiv.Perm (Fin n)) {k l : ℕ} (hkl : k ≤ l)
    (hl : l < n) : Disjoint (my_prefixSet_b σ k) {σ ⟨l, hl⟩} :=
  Finset.disjoint_singleton_right.2
    fun h => my_apply_notMem_prefixSet_b σ hl (my_prefixSet_mono_b σ hkl h)

private theorem my_disjoint_sdiff_prefixSet_singleton_b (σ : Equiv.Perm (Fin n)) {k l : ℕ}
    (hl : l < n) : Disjoint (my_prefixSet_b σ l \ my_prefixSet_b σ k) {σ ⟨l, hl⟩} :=
  Finset.disjoint_singleton_right.2
    fun h => my_apply_notMem_prefixSet_b σ hl (Finset.sdiff_subset h)

private def my_segmentBound_b (A : Finset (∀ i, X i)) (σ : Equiv.Perm (Fin n)) (k l : ℕ) : ℕ :=
  ∏ j ∈ Finset.univ.filter (fun j : Fin n => k ≤ j.val ∧ j.val < l),
    maxSection A {σ j} (earlierIndices σ j)

private theorem my_segmentBound_self_b (A : Finset (∀ i, X i)) (σ : Equiv.Perm (Fin n)) (k : ℕ) :
    my_segmentBound_b A σ k k = 1 := by
  refine Finset.prod_eq_one fun j hj => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
  omega

private theorem my_segmentBound_succ_b (A : Finset (∀ i, X i)) (σ : Equiv.Perm (Fin n)) {k l : ℕ}
    (hkl : k ≤ l) (hl : l < n) :
    my_segmentBound_b A σ k (l + 1)
      = my_segmentBound_b A σ k l * maxSection A {σ ⟨l, hl⟩} (my_prefixSet_b σ l) := by
  have hfilter : (Finset.univ.filter fun j : Fin n => k ≤ j.val ∧ j.val < l + 1)
      = insert ⟨l, hl⟩
        (Finset.univ.filter fun j : Fin n => k ≤ j.val ∧ j.val < l) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  have hnot : (⟨l, hl⟩ : Fin n) ∉ Finset.univ.filter fun j : Fin n => k ≤ j.val ∧ j.val < l := by
    simp
  rw [my_segmentBound_b, hfilter, Finset.prod_insert hnot, mul_comm,
    my_earlierIndices_eq_prefixSet_b]
  rfl

private theorem my_segmentBound_mul_b (A : Finset (∀ i, X i)) (σ : Equiv.Perm (Fin n)) {k l m : ℕ}
    (hkl : k ≤ l) (hlm : l ≤ m) :
    my_segmentBound_b A σ k l * my_segmentBound_b A σ l m = my_segmentBound_b A σ k m := by
  have hfilter : (Finset.univ.filter fun j : Fin n => k ≤ j.val ∧ j.val < m)
      = (Finset.univ.filter fun j : Fin n => k ≤ j.val ∧ j.val < l)
        ∪ Finset.univ.filter fun j : Fin n => l ≤ j.val ∧ j.val < m := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    omega
  have hdisj : Disjoint (Finset.univ.filter fun j : Fin n => k ≤ j.val ∧ j.val < l)
      (Finset.univ.filter fun j : Fin n => l ≤ j.val ∧ j.val < m) := by
    rw [Finset.disjoint_filter]
    intro j _ h1 h2
    omega
  rw [my_segmentBound_b, my_segmentBound_b, my_segmentBound_b, hfilter, Finset.prod_union hdisj]

private theorem my_segmentBound_zero_n_b (A : Finset (∀ i, X i)) (σ : Equiv.Perm (Fin n)) :
    my_segmentBound_b A σ 0 n = chainBound A σ := by
  rw [my_segmentBound_b, chainBound]
  refine Finset.prod_congr (Finset.filter_true_of_mem fun j _ => ?_) fun _ _ => rfl
  exact ⟨Nat.zero_le _, j.isLt⟩

private theorem my_maxSection_empty_left_le_b (A : Finset (∀ i, X i)) (I : Finset (Fin n)) :
    maxSection A ∅ I ≤ 1 :=
  Finset.sup_le fun _ _ => Finset.card_le_one.2 fun _ _ _ _ =>
    funext fun i => (Finset.notMem_empty i.val i.2).elim

private theorem my_maxSection_prefixSet_le_b (A : Finset (∀ i, X i)) (σ : Equiv.Perm (Fin n))
    (k : ℕ) : ∀ l, k ≤ l → l ≤ n →
      maxSection A (my_prefixSet_b σ l \ my_prefixSet_b σ k) (my_prefixSet_b σ k) ≤
        my_segmentBound_b A σ k l := by
  intro l
  induction l with
  | zero =>
    intro hk _
    rw [Nat.eq_zero_of_le_zero hk, Finset.sdiff_self, my_segmentBound_self_b]
    exact my_maxSection_empty_left_le_b A _
  | succ l ih =>
    intro hk hl
    rcases Nat.eq_or_lt_of_le hk with hk' | hk'
    · rw [← hk', Finset.sdiff_self, my_segmentBound_self_b]
      exact my_maxSection_empty_left_le_b A _
    have hkl : k ≤ l := Nat.lt_succ_iff.1 hk'
    have hln : l < n := hl
    rw [my_prefixSet_succ_sdiff_b σ hkl hln, my_segmentBound_succ_b A σ hkl hln]
    refine (maxSection_union_le A _ _ _ Finset.disjoint_sdiff
      (my_disjoint_prefixSet_singleton_b σ hkl hln)
        (my_disjoint_sdiff_prefixSet_singleton_b σ hln)).trans ?_
    rw [Finset.union_sdiff_of_subset (my_prefixSet_mono_b σ hkl)]
    exact Nat.mul_le_mul_right _ (ih hkl hln.le)

private theorem my_prefixSet_eq_of_monotone_b (σ : Equiv.Perm (Fin n)) {r : Fin n → ℕ}
    (hmono : Monotone (r ∘ σ)) (t : ℕ) :
    my_prefixSet_b σ (Finset.univ.filter fun i => r i ≤ t).card
      = Finset.univ.filter fun i => r i ≤ t := by
  have hcard : (Finset.univ.filter fun j : Fin n => r (σ j) ≤ t).card
      = (Finset.univ.filter fun i => r i ≤ t).card :=
    Finset.card_equiv σ fun j => by simp
  ext i
  rw [my_mem_prefixSet_b, Finset.mem_filter, ← hcard]
  have hij : r i = (r ∘ σ) (σ.symm i) := by simp
  rw [hij]
  simp only [Finset.mem_univ, true_and]
  constructor
  · intro hlt
    have h_le_card : (σ.symm i).val < (Finset.univ.filter fun j : Fin n => (r ∘ σ) j ≤ t).card
        := hlt
    have h_le_t : (r ∘ σ) (σ.symm i) ≤ t := by
      by_contra hc
      have hsub : Finset.univ.filter fun j : Fin n => (r ∘ σ) j ≤ t ⊆ Finset.Iio (σ.symm i) :=
        fun j' hj' => Finset.mem_Iio.2 (lt_of_not_ge fun hle =>
          hc ((hmono hle).trans (Finset.mem_filter.1 hj').2))
      have := Finset.card_le_card hsub
      rw [Fin.card_Iio] at this
      omega
    exact h_le_t
  · intro hle
    have hsub : Finset.Iic (σ.symm i) ⊆ Finset.univ.filter fun j : Fin n => r (σ j) ≤ t :=
      fun j' hj' => Finset.mem_filter.2
        ⟨Finset.mem_univ _, (hmono (Finset.mem_Iic.1 hj')).trans hle⟩
    have := Finset.card_le_card hsub
    rw [Fin.card_Iic] at this
    omega

private theorem my_four_block_le_chainBound_b (A : Finset (∀ i, X i))
    (I J K : Finset (Fin n)) (hIJ : Disjoint I J) (hIK : Disjoint I K)
    (hJK : Disjoint J K) :
    maxSection A I ∅ * (maxSection A J I * maxSection A K (I ∪ J))
        * maxSection A (univ \ (I ∪ J ∪ K)) (I ∪ J ∪ K)
      ≤ chainBound A (Tuple.sort (my_rankOf_b I J K)) := by
  set σ := Tuple.sort (my_rankOf_b I J K)
  have hT := my_prefixSet_eq_of_monotone_b σ (Tuple.monotone_sort (my_rankOf_b I J K))
  have hpa : my_prefixSet_b σ I.card = I := by
    have := hT 0
    rwa [my_filter_rankOf_le_zero_b] at this
  have hpb : my_prefixSet_b σ (I ∪ J).card = I ∪ J := by
    have := hT 1
    rwa [my_filter_rankOf_le_one_b] at this
  have hpc : my_prefixSet_b σ (I ∪ J ∪ K).card = I ∪ J ∪ K := by
    have := hT 2
    rwa [my_filter_rankOf_le_two_b] at this
  have hab : I.card ≤ (I ∪ J).card := Finset.card_le_card Finset.subset_union_left
  have hbc : (I ∪ J).card ≤ (I ∪ J ∪ K).card :=
    Finset.card_le_card Finset.subset_union_left
  have hcn : (I ∪ J ∪ K).card ≤ n :=
    (Finset.card_le_card (Finset.subset_univ _)).trans_eq (by simp)
  have hIJK : Disjoint (I ∪ J) K := Finset.disjoint_union_left.2 ⟨hIK, hJK⟩
  have s1 : maxSection A I ∅ ≤ my_segmentBound_b A σ 0 I.card := by
    have := my_maxSection_prefixSet_le_b A σ 0 I.card (Nat.zero_le _)
      (hab.trans (hbc.trans hcn))
    rwa [my_prefixSet_zero_b, hpa, Finset.sdiff_empty] at this
  have s2 : maxSection A J I ≤ my_segmentBound_b A σ I.card (I ∪ J).card := by
    have := my_maxSection_prefixSet_le_b A σ I.card (I ∪ J).card hab (hbc.trans hcn)
    rwa [hpa, hpb, Finset.union_sdiff_cancel_left hIJ] at this
  have s3 : maxSection A K (I ∪ J) ≤
      my_segmentBound_b A σ (I ∪ J).card (I ∪ J ∪ K).card := by
    have := my_maxSection_prefixSet_le_b A σ (I ∪ J).card (I ∪ J ∪ K).card hbc hcn
    rwa [hpb, hpc, Finset.union_sdiff_cancel_left hIJK] at this
  have s4 : maxSection A (univ \ (I ∪ J ∪ K)) (I ∪ J ∪ K)
      ≤ my_segmentBound_b A σ (I ∪ J ∪ K).card n := by
    have := my_maxSection_prefixSet_le_b A σ (I ∪ J ∪ K).card n hcn le_rfl
    rwa [hpc, my_prefixSet_of_le_b σ le_rfl] at this
  have hprod : my_segmentBound_b A σ 0 I.card
      * (my_segmentBound_b A σ I.card (I ∪ J).card
        * my_segmentBound_b A σ (I ∪ J).card (I ∪ J ∪ K).card)
      * my_segmentBound_b A σ (I ∪ J ∪ K).card n = chainBound A σ := by
    rw [my_segmentBound_mul_b A σ hab hbc,
      my_segmentBound_mul_b A σ (Nat.zero_le _) (hab.trans hbc),
      my_segmentBound_mul_b A σ (Nat.zero_le _) hcn, my_segmentBound_zero_n_b]
  calc
    maxSection A I ∅ * (maxSection A J I * maxSection A K (I ∪ J))
          * maxSection A (univ \ (I ∪ J ∪ K)) (I ∪ J ∪ K)
      ≤ my_segmentBound_b A σ 0 I.card
          * (my_segmentBound_b A σ I.card (I ∪ J).card
            * my_segmentBound_b A σ (I ∪ J).card (I ∪ J ∪ K).card)
          * my_segmentBound_b A σ (I ∪ J ∪ K).card n :=
        Nat.mul_le_mul (Nat.mul_le_mul s1 (Nat.mul_le_mul s2 s3)) s4
    _ = chainBound A σ := hprod

private theorem my_maxSection_pos_b (A : Finset (∀ i, X i)) (hA : A.Nonempty)
    (J I : Finset (Fin n)) : 0 < (maxSection A J I : ℝ) := by
  obtain ⟨a, ha⟩ := hA
  have hmem : restrictTo J a ∈ sectionOver A J I (restrictTo I a) :=
    Finset.mem_image.2 ⟨a, Finset.mem_filter.2 ⟨ha, rfl⟩, rfl⟩
  have hone : 1 ≤ (sectionOver A J I (restrictTo I a)).card :=
    Finset.card_pos.2 ⟨_, hmem⟩
  exact Nat.cast_pos.mpr (hone.trans (Finset.le_sup
    (f := fun p => (sectionOver A J I p).card) (Finset.mem_univ _)))


/-- **Theorem 210(a).**  In a `c`-uniform set the right-hand side of the two-step section
inequality `m(J ∪ K | I) ≤ m(J | I) · m(K | I ∪ J)` exceeds the left-hand side at most by the
factor `c`, for all pairwise disjoint `I, J, K`.  SUV Theorem 210(a), p. 324. -/
theorem maxSection_mul_le_of_isCUniform {c : ℝ} (A : Finset (∀ i, X i)) (hA : IsCUniform c A)
    (I J K : Finset (Fin n)) (hIJ : Disjoint I J) (hIK : Disjoint I K) (hJK : Disjoint J K) :
    ((maxSection A J I * maxSection A K (I ∪ J) : ℕ) : ℝ) ≤ c * maxSection A (J ∪ K) I := by
  have hc_case : A = ∅ ∨ A.Nonempty := A.eq_empty_or_nonempty
  rcases hc_case with rfl | hAne
  · have h1 : maxSection (X := X) ∅ J I = 0 := by
      dsimp [maxSection, sectionOver]
      have hzero : (fun p : (i : I) → X i.val =>
          (Finset.image (restrictTo J) (Finset.filter (fun a => restrictTo I a = p) ∅)).card)
          = fun p => 0 := by
        ext p
        simp
      rw [hzero]
      apply le_antisymm
      · apply Finset.sup_le
        intro p _
        rfl
      · exact Nat.zero_le _
    have hz : ((maxSection (X := X) ∅ J I * maxSection (X := X) ∅ K (I ∪ J) : ℕ) : ℝ) = 0 := by
      rw [h1, zero_mul]
      exact Nat.cast_zero
    rw [hz]
    have hz2 : (c * ↑(maxSection (X := X) ∅ (J ∪ K) I) : ℝ) = 0 := by
      have h1' : maxSection (X := X) ∅ (J ∪ K) I = 0 := by
        dsimp [maxSection, sectionOver]
        have hzero : (fun p : (i : I) → X i.val =>
            (Finset.image (restrictTo (J ∪ K))
              (Finset.filter (fun a => restrictTo I a = p) ∅)).card)
            = fun p => 0 := by
          ext p
          simp
        rw [hzero]
        apply le_antisymm
        · apply Finset.sup_le
          intro p _
          rfl
        · exact Nat.zero_le _
      rw [h1']
      have hz3 : ((0 : ℕ) : ℝ) = 0 := Nat.cast_zero
      rw [hz3, mul_zero]
    rw [hz2]
  let σ := Tuple.sort (my_rankOf_b I J K)
  have hend2 := my_four_block_le_chainBound_b A I J K hIJ hIK hJK
  have hcard : A.card = maxSection A (I ∪ J ∪ K ∪ univ \ (I ∪ J ∪ K)) ∅ := by
    have h_union : I ∪ J ∪ K ∪ univ \ (I ∪ J ∪ K) = univ :=
        Finset.union_sdiff_of_subset (Finset.subset_univ _)
    rw [h_union]
    have hsec : maxSection A univ ∅ = projCard A univ := by
      exact @maxSection_empty n X _ _ A univ
    have hAcard : A.card = projCard A univ := by
      exact projCard_univ A |>.symm
    omega
  have t1 := maxSection_union_le A ∅ (I ∪ J ∪ K) (univ \ (I ∪ J ∪ K))
    (Finset.disjoint_empty_left _) (Finset.disjoint_empty_left _) Finset.disjoint_sdiff
  have t2 := maxSection_union_le A ∅ I (J ∪ K) (Finset.disjoint_empty_left _)
    (Finset.disjoint_empty_left _) (Finset.disjoint_union_right.2 ⟨hIJ, hIK⟩)
  rw [Finset.empty_union] at t1
  rw [Finset.empty_union, ← Finset.union_assoc] at t2
  have hchain : A.card ≤ maxSection A I ∅ * maxSection A (J ∪ K) I
      * maxSection A (univ \ (I ∪ J ∪ K)) (I ∪ J ∪ K) := by
    rw [hcard]
    exact t1.trans (Nat.mul_le_mul_right _ t2)
  have h_max_I := my_maxSection_pos_b A hAne I ∅
  have h_max_end := my_maxSection_pos_b A hAne
    (univ \ (I ∪ J ∪ K)) (I ∪ J ∪ K)
  have h_c_pos : 0 ≤ c := by
    have hc : (0 : ℝ) ≤ c * A.card := le_trans (by positivity) (hA σ)
    have hcard_pos : (0 : ℝ) < A.card := Nat.cast_pos.mpr (Finset.card_pos.2 hAne)
    have hc2 : (0 : ℝ) * A.card ≤ c * A.card := by linarith
    exact (mul_le_mul_iff_of_pos_right hcard_pos).mp hc2
  have h_bound : ((maxSection A I ∅ * (maxSection A J I * maxSection A K (I ∪ J))
      * maxSection A (univ \ (I ∪ J ∪ K)) (I ∪ J ∪ K) : ℕ) : ℝ) ≤ c * A.card := by
    exact le_trans (Nat.cast_le.mpr hend2) (hA σ)
  have hc_bound : c * A.card ≤ c * (maxSection A I ∅ * maxSection A (J ∪ K) I
      * maxSection A (univ \ (I ∪ J ∪ K)) (I ∪ J ∪ K) : ℕ) := by
    exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hchain) h_c_pos
  have h_final : ((maxSection A I ∅ * (maxSection A J I * maxSection A K (I ∪ J))
      * maxSection A (univ \ (I ∪ J ∪ K)) (I ∪ J ∪ K) : ℕ) : ℝ) ≤
      c * (maxSection A I ∅ * maxSection A (J ∪ K) I
        * maxSection A (univ \ (I ∪ J ∪ K)) (I ∪ J ∪ K) : ℕ) := h_bound.trans hc_bound
  have h_rewrite_left : ((maxSection A I ∅ * (maxSection A J I * maxSection A K (I ∪ J))
      * maxSection A (univ \ (I ∪ J ∪ K)) (I ∪ J ∪ K) : ℕ) : ℝ)
    = (maxSection A I ∅ : ℝ) * ((maxSection A J I * maxSection A K (I ∪ J) : ℕ) : ℝ)
      * (maxSection A (univ \ (I ∪ J ∪ K)) (I ∪ J ∪ K) : ℝ) := by
    push_cast
    ring
  have h_rewrite_right : c * ((maxSection A I ∅ * maxSection A (J ∪ K) I
      * maxSection A (univ \ (I ∪ J ∪ K)) (I ∪ J ∪ K) : ℕ) : ℝ)
    = c * (maxSection A (J ∪ K) I : ℝ) * (maxSection A I ∅ : ℝ)
      * (maxSection A (univ \ (I ∪ J ∪ K)) (I ∪ J ∪ K) : ℝ) := by
    push_cast
    ring
  rw [h_rewrite_left, h_rewrite_right] at h_final
  have h_pos : (0 : ℝ) < (maxSection A I ∅ : ℝ)
      * (maxSection A (univ \ (I ∪ J ∪ K)) (I ∪ J ∪ K) : ℝ) := by
    exact mul_pos h_max_I h_max_end
  have h_final2 : ((maxSection A J I * maxSection A K (I ∪ J) : ℕ) : ℝ) * ((maxSection A I ∅ : ℝ)
      * (maxSection A (univ \ (I ∪ J ∪ K)) (I ∪ J ∪ K) : ℝ)) ≤
      c * (maxSection A (J ∪ K) I : ℝ) * ((maxSection A I ∅ : ℝ)
        * (maxSection A (univ \ (I ∪ J ∪ K)) (I ∪ J ∪ K) : ℝ)) := by
    calc
      ((maxSection A J I * maxSection A K (I ∪ J) : ℕ) : ℝ) * ((maxSection A I ∅ : ℝ)
          * (maxSection A (univ \ (I ∪ J ∪ K)) (I ∪ J ∪ K) : ℝ))
        = (maxSection A I ∅ : ℝ) * ((maxSection A J I * maxSection A K (I ∪ J) : ℕ) : ℝ)
          * (maxSection A (univ \ (I ∪ J ∪ K)) (I ∪ J ∪ K) : ℝ) := by ring
      _ ≤ c * (maxSection A (J ∪ K) I : ℝ) * (maxSection A I ∅ : ℝ)
          * (maxSection A (univ \ (I ∪ J ∪ K)) (I ∪ J ∪ K) : ℝ) := h_final
      _ = c * (maxSection A (J ∪ K) I : ℝ) * ((maxSection A I ∅ : ℝ)
          * (maxSection A (univ \ (I ∪ J ∪ K)) (I ∪ J ∪ K) : ℝ)) := by ring
  exact (mul_le_mul_iff_of_pos_right h_pos).1 h_final2

/-- In a `c`-uniform set the three-block chain product along `I`, then `J`, then the rest of
the coordinates is at most `c · |A|`: it is bounded by the chain product of an ordering that
lists `I` first and `J` next.  This is the block form of the chain inequality used in the
proof of Theorem 210(e). -/
theorem three_block_maxSection_le_of_isCUniform {c : ℝ} (A : Finset (∀ i, X i))
    (hA : IsCUniform c A) (I J : Finset (Fin n)) (hIJ : Disjoint I J) :
    ((maxSection A I ∅ * maxSection A J I * maxSection A (univ \ (I ∪ J)) (I ∪ J) : ℕ) : ℝ)
      ≤ c * A.card := by
  set K := univ \ (I ∪ J) with hKdef
  have hIK : Disjoint I K := Finset.disjoint_sdiff.mono_left Finset.subset_union_left
  have hJK : Disjoint J K := Finset.disjoint_sdiff.mono_left Finset.subset_union_right
  have hU : I ∪ J ∪ K = univ := Finset.union_sdiff_of_subset (Finset.subset_univ _)
  have hn : (I ∪ J ∪ K).card = n := by rw [hU, Finset.card_univ, Fintype.card_fin]
  set σ := Tuple.sort (my_rankOf_b I J K)
  have hT := my_prefixSet_eq_of_monotone_b σ (Tuple.monotone_sort (my_rankOf_b I J K))
  have hpa : my_prefixSet_b σ I.card = I := by
    have := hT 0
    rwa [my_filter_rankOf_le_zero_b] at this
  have hpb : my_prefixSet_b σ (I ∪ J).card = I ∪ J := by
    have := hT 1
    rwa [my_filter_rankOf_le_one_b] at this
  have hpc : my_prefixSet_b σ (I ∪ J ∪ K).card = I ∪ J ∪ K := by
    have := hT 2
    rwa [my_filter_rankOf_le_two_b] at this
  have hab : I.card ≤ (I ∪ J).card := Finset.card_le_card Finset.subset_union_left
  have hbc : (I ∪ J).card ≤ (I ∪ J ∪ K).card := Finset.card_le_card Finset.subset_union_left
  have hcn : (I ∪ J ∪ K).card ≤ n := hn.le
  have hIJK : Disjoint (I ∪ J) K := Finset.disjoint_union_left.2 ⟨hIK, hJK⟩
  have s1 : maxSection A I ∅ ≤ my_segmentBound_b A σ 0 I.card := by
    have := my_maxSection_prefixSet_le_b A σ 0 I.card (Nat.zero_le _) (hab.trans (hbc.trans hcn))
    rwa [my_prefixSet_zero_b, hpa, Finset.sdiff_empty] at this
  have s2 : maxSection A J I ≤ my_segmentBound_b A σ I.card (I ∪ J).card := by
    have := my_maxSection_prefixSet_le_b A σ I.card (I ∪ J).card hab (hbc.trans hcn)
    rwa [hpa, hpb, Finset.union_sdiff_cancel_left hIJ] at this
  have s3 : maxSection A K (I ∪ J) ≤ my_segmentBound_b A σ (I ∪ J).card (I ∪ J ∪ K).card := by
    have := my_maxSection_prefixSet_le_b A σ (I ∪ J).card (I ∪ J ∪ K).card hbc hcn
    rwa [hpb, hpc, Finset.union_sdiff_cancel_left hIJK] at this
  have hprod : my_segmentBound_b A σ 0 I.card * my_segmentBound_b A σ I.card (I ∪ J).card
      * my_segmentBound_b A σ (I ∪ J).card (I ∪ J ∪ K).card = chainBound A σ := by
    rw [my_segmentBound_mul_b A σ (Nat.zero_le _) hab,
      my_segmentBound_mul_b A σ (Nat.zero_le _) hbc, hn, my_segmentBound_zero_n_b]
  have hle : maxSection A I ∅ * maxSection A J I * maxSection A K (I ∪ J) ≤ chainBound A σ := by
    rw [← hprod]
    exact Nat.mul_le_mul (Nat.mul_le_mul s1 s2) s3
  calc ((maxSection A I ∅ * maxSection A J I * maxSection A K (I ∪ J) : ℕ) : ℝ)
      ≤ chainBound A σ := by exact_mod_cast hle
    _ ≤ c * A.card := hA σ

/-- Maximal section sizes commute with projection along an injection. -/
private theorem my_maxSection_image_comp_b {m : ℕ} (A : Finset (∀ i, X i))
    (e : Fin m → Fin n) (he : Function.Injective e) (J' I' : Finset (Fin m)) :
    maxSection (A.image fun a (j : Fin m) => a (e j)) J' I' =
      maxSection A (J'.map ⟨e, he⟩) (I'.map ⟨e, he⟩) := by
  set π : (∀ i, X i) → ∀ j : Fin m, X (e j) := fun a j => a (e j) with hπ
  set ρ : ((i : (J'.map ⟨e, he⟩ : Finset (Fin n))) → X i.val) →
      (j : J') → X (e j.val) :=
    fun q j => q ⟨e j.val, Finset.mem_map_of_mem _ j.2⟩ with hρ
  have hρinj : Function.Injective ρ := by
    intro q₁ q₂ h
    funext i
    obtain ⟨j, hj, hji⟩ := Finset.mem_map.1 i.2
    have hq := congrFun h ⟨j, hj⟩
    simp only [hρ] at hq
    have hi : i = ⟨e j, Finset.mem_map_of_mem _ hj⟩ := Subtype.ext hji.symm
    rw [hi]
    exact hq
  rw [maxSection_eq_sup_proj, maxSection_eq_sup_proj, proj, proj, Finset.image_image,
    Finset.sup_image, Finset.sup_image]
  refine Finset.sup_congr rfl fun a _ => ?_
  simp only [Function.comp]
  have hfil : (A.image π).filter (fun b => restrictTo I' b = restrictTo I' (π a)) =
      (A.filter fun a' => restrictTo (I'.map ⟨e, he⟩) a' =
        restrictTo (I'.map ⟨e, he⟩) a).image π := by
    rw [Finset.filter_image]
    congr 1
    ext a'
    simp only [Finset.mem_filter, and_congr_right_iff]
    intro _
    constructor
    · intro h
      funext i
      obtain ⟨j, hj, hji⟩ := Finset.mem_map.1 i.2
      have hi : i = ⟨e j, Finset.mem_map_of_mem _ hj⟩ := Subtype.ext hji.symm
      rw [hi]
      exact congrFun h ⟨j, hj⟩
    · intro h
      funext j
      exact congrFun h ⟨e j.val, Finset.mem_map_of_mem _ j.2⟩
  rw [sectionOver, sectionOver, hfil, Finset.image_image]
  have hcomp : restrictTo J' ∘ π = ρ ∘ restrictTo (J'.map ⟨e, he⟩) := rfl
  rw [hcomp, ← Finset.image_image, Finset.card_image_of_injective _ hρinj]

/-- An ordering of injected coordinates extends to an ordering of all coordinates, with the
injected coordinates occupying the initial positions. -/
private theorem exists_perm_extending_injection {m : ℕ} (e : Fin m → Fin n)
    (he : Function.Injective e) (σ : Equiv.Perm (Fin m)) :
    ∃ τ : Equiv.Perm (Fin n), ∀ k : Fin m,
      τ (Fin.castLE (by simpa using Fintype.card_le_of_injective e he) k) = e (σ k) := by
  let s : Finset (Fin n) := Finset.univ.filter fun i => i.val < m
  let f : Fin n → Fin n := fun i =>
    if hi : i.val < m then e (σ ⟨i.val, hi⟩) else i
  have hf : Set.InjOn f s := by
    intro i hi j hj hij
    simp [s] at hi hj
    simp only [f, dite_eq_left hi, dite_eq_left hj] at hij
    apply Fin.ext
    exact congrArg (fun x : Fin m => x.val) (σ.injective (he hij))
  obtain ⟨g, hg⟩ := Finset.exists_equiv_extend_of_card_eq
    (α := Fin n) (t := (Finset.univ : Finset (Fin n))) (by simp) (by simp) hf
  let τ : Equiv.Perm (Fin n) :=
    { toFun := fun i => (g i).val
      invFun := fun i => g.symm ⟨i, Finset.mem_univ i⟩
      left_inv := fun i => by simp
      right_inv := fun i => by simp }
  refine ⟨τ, fun k => ?_⟩
  have hk : Fin.castLE (by simpa using Fintype.card_le_of_injective e he) k ∈ s := by
    simp [s]
  have hgf := hg _ hk
  simpa [τ, f, k.isLt] using hgf

/-- **Theorem 210(b).**  A projection of a `c`-uniform set onto any set of coordinates is
`c`-uniform.  The projection onto the coordinates listed by an injection `e : Fin m → Fin n` is
the image of `A` under `a ↦ (j ↦ a (e j))`.

`A` is non-empty, as everywhere in Sections 10.2 and 10.5 (the standing assumption of
p. 318): without it the empty subset of a one-coordinate product would be `c`-uniform for
every `c` while its projection onto no coordinate is `c`-uniform for no `c`.
SUV Theorem 210(b), p. 324. -/
theorem isCUniform_image_of_injective {c : ℝ} {m : ℕ} (A : Finset (∀ i, X i))
    (hAne : A.Nonempty) (hA : IsCUniform c A) (e : Fin m → Fin n)
    (he : Function.Injective e) :
    IsCUniform c (A.image fun a (j : Fin m) => a (e j)) := by
  intro σ
  let B := A.image fun a (j : Fin m) => a (e j)
  let emb : Fin m ↪ Fin n := ⟨e, he⟩
  have hmn : m ≤ n := by simpa using Fintype.card_le_of_injective e he
  obtain ⟨τ, hτ⟩ := exists_perm_extending_injection e he σ
  have hprefix (k : Fin m) :
      my_prefixSet_b τ k.val = (earlierIndices σ k).map emb := by
    ext i
    constructor
    · intro hi
      rw [my_prefixSet_b] at hi
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hi
      have hqv : q.val < k.val := (Finset.mem_filter.1 hq).2
      let j : Fin m := ⟨q.val, lt_trans hqv k.isLt⟩
      have hqcast : q = Fin.castLE hmn j := Fin.ext rfl
      rw [hqcast, hτ]
      apply Finset.mem_map.2
      refine ⟨σ j, ?_, rfl⟩
      apply Finset.mem_image.2
      exact ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ _, hqv⟩, rfl⟩
    · intro hi
      obtain ⟨x, hx, hxi⟩ := Finset.mem_map.1 hi
      rw [← hxi]
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hx
      have hjv : j.val < k.val := (Finset.mem_filter.1 hj).2
      rw [my_prefixSet_b]
      apply Finset.mem_image.2
      refine ⟨Fin.castLE hmn j, ?_, hτ j⟩
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hjv⟩
  have hseg : ∀ l, l ≤ m →
      my_segmentBound_b A τ 0 l = my_segmentBound_b B σ 0 l := by
    intro l hl
    induction l with
    | zero => rw [my_segmentBound_self_b, my_segmentBound_self_b]
    | succ l ih =>
      have hlm : l < m := hl
      have hln : l < n := lt_of_lt_of_le hlm hmn
      rw [my_segmentBound_succ_b A τ (Nat.zero_le l) hln,
        my_segmentBound_succ_b B σ (Nat.zero_le l) hlm, ih hlm.le,
        my_maxSection_image_comp_b A e he]
      have hcast : (⟨l, hln⟩ : Fin n) = Fin.castLE hmn ⟨l, hlm⟩ := Fin.ext rfl
      rw [hcast, hτ]
      congr 2
      rw [← my_earlierIndices_eq_prefixSet_b σ ⟨l, hlm⟩]
      exact hprefix ⟨l, hlm⟩
  let R := my_segmentBound_b A τ m n
  have hfactor : chainBound A τ = chainBound B σ * R := by
    calc
      chainBound A τ = my_segmentBound_b A τ 0 n :=
        (my_segmentBound_zero_n_b A τ).symm
      _ = my_segmentBound_b A τ 0 m * my_segmentBound_b A τ m n :=
        (my_segmentBound_mul_b A τ (Nat.zero_le m) hmn).symm
      _ = my_segmentBound_b B σ 0 m * R := by rw [hseg m le_rfl]
      _ = chainBound B σ * R := by rw [my_segmentBound_zero_n_b]
  have hprefix_all : my_prefixSet_b τ m = Finset.univ.map emb := by
    ext i
    constructor
    · intro hi
      rw [my_prefixSet_b] at hi
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hi
      have hqm : q.val < m := (Finset.mem_filter.1 hq).2
      let j : Fin m := ⟨q.val, hqm⟩
      have hqcast : q = Fin.castLE hmn j := Fin.ext rfl
      rw [hqcast, hτ]
      exact Finset.mem_map.2 ⟨σ j, Finset.mem_univ _, rfl⟩
    · intro hi
      obtain ⟨j, _, hji⟩ := Finset.mem_map.1 hi
      rw [← hji, my_prefixSet_b]
      apply Finset.mem_image.2
      refine ⟨Fin.castLE hmn (σ.symm j), ?_, ?_⟩
      · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (σ.symm j).isLt⟩
      · exact (hτ (σ.symm j)).trans (by simp [emb])
  have hproj : maxSection A (my_prefixSet_b τ m) ∅ = B.card := by
    have h := my_maxSection_image_comp_b A e he Finset.univ ∅
    rw [maxSection_empty, projCard_univ] at h
    rw [hprefix_all]
    simpa [B, emb] using h.symm
  have htail : maxSection A (Finset.univ \ my_prefixSet_b τ m)
      (my_prefixSet_b τ m) ≤ R := by
    have h := my_maxSection_prefixSet_le_b A τ m n hmn le_rfl
    rw [my_prefixSet_of_le_b τ le_rfl] at h
    exact h
  have hgroup : A.card ≤ B.card * R := by
    have h := maxSection_union_le A ∅ (my_prefixSet_b τ m)
      (Finset.univ \ my_prefixSet_b τ m) (Finset.disjoint_empty_left _)
      (Finset.disjoint_empty_left _) Finset.disjoint_sdiff
    rw [Finset.empty_union,
      Finset.union_sdiff_of_subset (Finset.subset_univ (my_prefixSet_b τ m)),
      maxSection_empty, projCard_univ] at h
    calc
      A.card ≤ maxSection A (my_prefixSet_b τ m) ∅ *
          maxSection A (Finset.univ \ my_prefixSet_b τ m) (my_prefixSet_b τ m) := h
      _ ≤ B.card * R := by
        rw [hproj]
        exact Nat.mul_le_mul_left _ htail
  have hRpos : 0 < R := by
    by_contra hR
    have hRzero : R = 0 := Nat.eq_zero_of_not_pos hR
    have hcardpos : 0 < A.card := Finset.card_pos.2 hAne
    rw [hRzero, mul_zero] at hgroup
    omega
  have hc : 0 ≤ c := by
    have hcA := hA τ
    have hnonneg : (0 : ℝ) ≤ c * A.card := (Nat.cast_nonneg _).trans hcA
    have hcardpos : (0 : ℝ) < A.card := Nat.cast_pos.mpr (Finset.card_pos.2 hAne)
    nlinarith
  have hcancel : (chainBound B σ : ℝ) * R ≤ (c * B.card) * R := by
    calc
      (chainBound B σ : ℝ) * R = ((chainBound B σ * R : ℕ) : ℝ) :=
        (Nat.cast_mul _ _).symm
      _ = (chainBound A τ : ℝ) := by rw [hfactor]
      _ ≤ c * A.card := hA τ
      _ ≤ c * (B.card * R) := by
        apply mul_le_mul_of_nonneg_left _ hc
        exact_mod_cast hgroup
      _ = (c * B.card) * R := by ring
  change (chainBound B σ : ℝ) ≤ c * B.card
  exact (mul_le_mul_iff_of_pos_right (Nat.cast_pos.mpr hRpos)).1 hcancel

private lemma maxSection_mono_A {A A' : Finset (∀ i, X i)} (h : A' ⊆ A)
    (J I : Finset (Fin n)) : maxSection A' J I ≤ maxSection A J I :=
  Finset.sup_mono_fun fun _ _ =>
    Finset.card_le_card (Finset.image_subset_image (Finset.filter_subset_filter _ h))

/-- **Theorem 210(c).**  If `A` is `c`-uniform and `A' ⊆ A` contains at least an `ε`-fraction
of the elements of `A`, then `A'` is `c/ε`-uniform: its sections are no larger than those of
`A`, and its size is at least `ε |A|`.  SUV Theorem 210(c), p. 324. -/
theorem isCUniform_of_subset {c ε : ℝ} (hε : 0 < ε) {A A' : Finset (∀ i, X i)}
    (hA : IsCUniform c A) (hsub : A' ⊆ A) (hcard : ε * A.card ≤ A'.card) :
    IsCUniform (c / ε) A' := by
  intro σ
  have h_mono : chainBound A' σ ≤ chainBound A σ := by
    dsimp [chainBound]
    apply Finset.prod_le_prod₀
    · intro i _
      exact Nat.cast_nonneg _
    · intro i _
      have h2 := maxSection_mono_A hsub {σ i} (earlierIndices σ i)
      exact Nat.cast_le.mpr h2
  have h_bound2 : (chainBound A' σ : ℝ) ≤ c * A.card := by
    have h1 : (chainBound A' σ : ℝ) ≤ (chainBound A σ : ℝ) := Nat.cast_le.mpr h_mono
    exact le_trans h1 (hA σ)
  by_cases hA_empty : A.card = 0
  · have hA' : A'.card = 0 := by
      have h_card_le := Finset.card_le_card hsub
      omega
    have h_c_A : c * (A.card : ℝ) = 0 := by rw [hA_empty, Nat.cast_zero, mul_zero]
    have h_c_A' : (c / ε) * (A'.card : ℝ) = 0 := by rw [hA', Nat.cast_zero, mul_zero]
    rw [h_c_A']
    rw [h_c_A] at h_bound2
    exact h_bound2
  · have hA_pos : (0 : ℝ) < A.card := by
      exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero hA_empty)
    have hc_pos : 0 ≤ c := by
      have h_nonneg : (0 : ℝ) ≤ (chainBound A σ : ℝ) := Nat.cast_nonneg _
      have h_le := hA σ
      nlinarith
    have h_ineq : c * (A.card : ℝ) ≤ (c / ε) * (A'.card : ℝ) := by
      have : c * (A.card : ℝ) = (c / ε) * (ε * A.card) := by
        calc
          c * (A.card : ℝ) = (c / ε * ε) * A.card := by
            rw [div_mul_cancel₀ _ (ne_of_gt hε)]
        _ = (c / ε) * (ε * A.card) := by ring
      rw [this]
      apply mul_le_mul_of_nonneg_left hcard
      exact div_nonneg hc_pos (le_of_lt hε)
    exact le_trans h_bound2 h_ineq

end General

end Kolmogorov
