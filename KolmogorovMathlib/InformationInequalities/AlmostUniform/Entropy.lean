import KolmogorovMathlib.Entropy.Coding
import KolmogorovMathlib.Entropy.Inequalities
import KolmogorovMathlib.InformationInequalities.AlmostUniform.Basic

/-!
# Almost uniform sets: entropies of a uniformly random point

SUV Section 10.5, Theorem 210(d)–(e) and its corollary, pp. 324–325.

If `ξ` is uniformly distributed in a `c`-uniform set `A`, the entropies of its projections and
conditional projections are within `log c` of the log-sizes of the corresponding projections
and maximal sections (Theorem 210(d), `entropySub_uniformProbOn_bounds_of_isCUniform`, and
Theorem 210(e), `condEntropySub_uniformProbOn_bounds_of_isCUniform`).  The unnumbered
corollary after the proof transfers entropy inequalities to `c`-uniform sets with error
`λ log c` (`evalLogSize_le_of_isCUniform`).

Parts (d) and (e) mention entropies, so there the coordinate sets are one finite type `α`
(see the module docstring of `UniformSetsTheorems` for why this is no loss).  Logarithms and
entropies are base two.
-/

namespace Kolmogorov

open Finset

variable {n : ℕ}

section General

variable {X : Fin n → Type} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]

private theorem my_maxSection_empty_left_le (A : Finset (∀ i, X i)) (I : Finset (Fin n)) :
    maxSection A ∅ I ≤ 1 :=
  Finset.sup_le fun _ _ => Finset.card_le_one.2 fun _ _ _ _ =>
    funext fun i => (Finset.notMem_empty i.val i.2).elim

/-- The coordinates listed in the first `l` positions of the ordering `σ`; `earlierIndices`
with a natural-number cut-off, so that `l = n` (all coordinates) is allowed. -/
private def my_prefixSet (σ : Equiv.Perm (Fin n)) (l : ℕ) : Finset (Fin n) :=
  (Finset.univ.filter fun j : Fin n => j.val < l).image σ

private theorem my_mem_prefixSet {σ : Equiv.Perm (Fin n)} {l : ℕ} {i : Fin n} :
    i ∈ my_prefixSet σ l ↔ (σ.symm i).val < l := by
  simp only [my_prefixSet, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj, rfl⟩
    simpa using hj
  · intro h
    exact ⟨σ.symm i, h, by simp⟩

private theorem my_earlierIndices_eq_prefixSet (σ : Equiv.Perm (Fin n)) (k : Fin n) :
    earlierIndices σ k = my_prefixSet σ k.val := rfl

private theorem my_prefixSet_zero (σ : Equiv.Perm (Fin n)) : my_prefixSet σ 0 = ∅ := by
  ext i
  simp [my_mem_prefixSet]

private theorem my_prefixSet_of_le (σ : Equiv.Perm (Fin n)) {l : ℕ} (hl : n ≤ l) :
    my_prefixSet σ l = Finset.univ := by
  ext i
  simp only [my_mem_prefixSet, Finset.mem_univ, iff_true]
  exact lt_of_lt_of_le (σ.symm i).isLt hl

private theorem my_prefixSet_mono (σ : Equiv.Perm (Fin n)) {k l : ℕ} (hkl : k ≤ l) :
    my_prefixSet σ k ⊆ my_prefixSet σ l := fun _ hi =>
  my_mem_prefixSet.2 (lt_of_lt_of_le (my_mem_prefixSet.1 hi) hkl)

private theorem my_prefixSet_succ (σ : Equiv.Perm (Fin n)) {l : ℕ} (hl : l < n) :
    my_prefixSet σ (l + 1) = insert (σ ⟨l, hl⟩) (my_prefixSet σ l) := by
  ext i
  simp only [my_mem_prefixSet, Finset.mem_insert, ← Equiv.symm_apply_eq, Fin.ext_iff]
  omega

private theorem my_apply_notMem_prefixSet (σ : Equiv.Perm (Fin n)) {l : ℕ} (hl : l < n) :
    σ ⟨l, hl⟩ ∉ my_prefixSet σ l := by
  simp [my_mem_prefixSet]

private theorem my_prefixSet_succ_sdiff (σ : Equiv.Perm (Fin n)) {k l : ℕ} (hkl : k ≤ l)
    (hl : l < n) :
    my_prefixSet σ (l + 1) \ my_prefixSet σ k =
      (my_prefixSet σ l \ my_prefixSet σ k) ∪ {σ ⟨l, hl⟩} := by
  rw [my_prefixSet_succ σ hl, Finset.insert_sdiff_of_notMem _
    (fun h => my_apply_notMem_prefixSet σ hl (my_prefixSet_mono σ hkl h)), Finset.insert_eq,
    Finset.union_comm]

private theorem my_disjoint_prefixSet_singleton (σ : Equiv.Perm (Fin n)) {k l : ℕ} (hkl : k ≤ l)
    (hl : l < n) : Disjoint (my_prefixSet σ k) {σ ⟨l, hl⟩} :=
  Finset.disjoint_singleton_right.2
    fun h => my_apply_notMem_prefixSet σ hl (my_prefixSet_mono σ hkl h)

private theorem my_disjoint_sdiff_prefixSet_singleton (σ : Equiv.Perm (Fin n)) {k l : ℕ}
    (hl : l < n) : Disjoint (my_prefixSet σ l \ my_prefixSet σ k) {σ ⟨l, hl⟩} :=
  Finset.disjoint_singleton_right.2
    fun h => my_apply_notMem_prefixSet σ hl (Finset.sdiff_subset h)

/-- The product of the chain factors `m(k_j | k_1, …, k_{j-1})` over the positions
`k ≤ j < l` of the ordering `σ`. -/
private def my_segmentBound (A : Finset (∀ i, X i)) (σ : Equiv.Perm (Fin n)) (k l : ℕ) : ℕ :=
  ∏ j ∈ Finset.univ.filter (fun j : Fin n => k ≤ j.val ∧ j.val < l),
    maxSection A {σ j} (earlierIndices σ j)

private theorem my_segmentBound_self (A : Finset (∀ i, X i)) (σ : Equiv.Perm (Fin n)) (k : ℕ) :
    my_segmentBound A σ k k = 1 := by
  refine Finset.prod_eq_one fun j hj => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
  omega

private theorem my_segmentBound_succ (A : Finset (∀ i, X i)) (σ : Equiv.Perm (Fin n)) {k l : ℕ}
    (hkl : k ≤ l) (hl : l < n) :
    my_segmentBound A σ k (l + 1)
      = my_segmentBound A σ k l * maxSection A {σ ⟨l, hl⟩} (my_prefixSet σ l) := by
  have hfilter : (Finset.univ.filter fun j : Fin n => k ≤ j.val ∧ j.val < l + 1)
      = insert ⟨l, hl⟩ (Finset.univ.filter fun j : Fin n => k ≤ j.val ∧ j.val < l) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  have hnot : (⟨l, hl⟩ : Fin n) ∉ Finset.univ.filter fun j : Fin n => k ≤ j.val ∧ j.val < l := by
    simp
  rw [my_segmentBound, hfilter, Finset.prod_insert hnot, mul_comm, my_earlierIndices_eq_prefixSet]
  rfl

private theorem my_segmentBound_mul (A : Finset (∀ i, X i)) (σ : Equiv.Perm (Fin n)) {k l m : ℕ}
    (hkl : k ≤ l) (hlm : l ≤ m) :
    my_segmentBound A σ k l * my_segmentBound A σ l m = my_segmentBound A σ k m := by
  have hfilter : (Finset.univ.filter fun j : Fin n => k ≤ j.val ∧ j.val < m)
      = (Finset.univ.filter fun j : Fin n => k ≤ j.val ∧ j.val < l)
        ∪ (Finset.univ.filter fun j : Fin n => l ≤ j.val ∧ j.val < m) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    omega
  have hdisj : Disjoint (Finset.univ.filter fun j : Fin n => k ≤ j.val ∧ j.val < l)
      (Finset.univ.filter fun j : Fin n => l ≤ j.val ∧ j.val < m) := by
    rw [Finset.disjoint_left]
    intro j hj hj'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj hj'
    omega
  rw [my_segmentBound, my_segmentBound, my_segmentBound, hfilter, Finset.prod_union hdisj]

private theorem my_segmentBound_zero_n (A : Finset (∀ i, X i)) (σ : Equiv.Perm (Fin n)) :
    my_segmentBound A σ 0 n = chainBound A σ := by
  rw [my_segmentBound, chainBound]
  refine Finset.prod_congr (Finset.filter_true_of_mem fun j _ => ?_) fun _ _ => rfl
  exact ⟨Nat.zero_le _, j.isLt⟩

/-- Grouping the chain factors of the positions `k ≤ j < l`: they bound the section of the
coordinates listed there over the coordinates listed before position `k`.
SUV Section 10.2, p. 320 (the grouping argument). -/
private theorem my_maxSection_prefixSet_le (A : Finset (∀ i, X i)) (σ : Equiv.Perm (Fin n))
    (k : ℕ) : ∀ l, k ≤ l → l ≤ n →
      maxSection A (my_prefixSet σ l \ my_prefixSet σ k) (my_prefixSet σ k) ≤
        my_segmentBound A σ k l := by
  intro l
  induction l with
  | zero =>
    intro hk _
    obtain rfl : k = 0 := by omega
    rw [Finset.sdiff_self, my_segmentBound_self]
    exact my_maxSection_empty_left_le A _
  | succ l ih =>
    intro hk hl
    rcases Nat.eq_or_lt_of_le hk with hk' | hk'
    · rw [← hk', Finset.sdiff_self, my_segmentBound_self]
      exact my_maxSection_empty_left_le A _
    have hkl : k ≤ l := Nat.lt_succ_iff.1 hk'
    have hln : l < n := hl
    rw [my_prefixSet_succ_sdiff σ hkl hln, my_segmentBound_succ A σ hkl hln]
    refine (maxSection_union_le A _ _ _ Finset.disjoint_sdiff
      (my_disjoint_prefixSet_singleton σ hkl hln)
      (my_disjoint_sdiff_prefixSet_singleton σ hln)).trans ?_
    rw [Finset.union_sdiff_of_subset (my_prefixSet_mono σ hkl)]
    exact Nat.mul_le_mul_right _ (ih hkl hln.le)

/-- The chain inequality for an ordering `σ` of the coordinates:
`|A| = m(k_1, …, k_n) ≤ m(k_1) · m(k_2 | k_1) ⋯ m(k_n | k_1, …, k_{n-1})`.  For each value of
the earlier coordinates there are at most `m(· | ·)` values of the next one.
SUV Section 10.2, p. 319 (unnumbered). -/
private theorem my_card_le_chainBound (A : Finset (∀ i, X i)) (σ : Equiv.Perm (Fin n)) :
    A.card ≤ chainBound A σ := by
  have h := my_maxSection_prefixSet_le A σ 0 n (Nat.zero_le n) le_rfl
  rwa [my_prefixSet_zero, my_prefixSet_of_le σ le_rfl, Finset.sdiff_empty, maxSection_empty,
    projCard_univ, my_segmentBound_zero_n] at h

/-- `m_A(∅ | I) = 1` for a non-empty `A`: the section over no coordinates of a point of the
projection is a single point.  SUV Section 10.2, p. 319. -/
private theorem my_maxSection_empty_left (A : Finset (∀ i, X i)) (hA : A.Nonempty)
    (I : Finset (Fin n)) : maxSection A ∅ I = 1 := by
  refine le_antisymm (my_maxSection_empty_left_le A I) ?_
  obtain ⟨a, ha⟩ := hA
  have h1 : 1 ≤ (sectionOver A ∅ I (restrictTo I a)).card :=
    Finset.card_pos.2 ⟨restrictTo ∅ a,
      Finset.mem_image.2 ⟨a, Finset.mem_filter.2 ⟨ha, rfl⟩, rfl⟩⟩
  exact h1.trans (Finset.le_sup (f := fun p => (sectionOver A ∅ I p).card) (Finset.mem_univ _))

/-- If the two-step section inequality is an equality for all disjoint triples, every grouping
of a chain is an equality.  SUV Section 10.2, p. 320. -/
private theorem my_maxSection_prefixSet_eq (A : Finset (∀ i, X i)) (hA : A.Nonempty)
    (σ : Equiv.Perm (Fin n))
    (h : ∀ I J K : Finset (Fin n), Disjoint I J → Disjoint I K → Disjoint J K →
      maxSection A (J ∪ K) I = maxSection A J I * maxSection A K (I ∪ J))
    (k : ℕ) : ∀ l, k ≤ l → l ≤ n →
      maxSection A (my_prefixSet σ l \ my_prefixSet σ k) (my_prefixSet σ k) =
        my_segmentBound A σ k l := by
  intro l
  induction l with
  | zero =>
    intro hk _
    obtain rfl : k = 0 := by omega
    rw [Finset.sdiff_self, my_segmentBound_self, my_maxSection_empty_left A hA]
  | succ l ih =>
    intro hk hl
    rcases Nat.eq_or_lt_of_le hk with hk' | hk'
    · rw [← hk', Finset.sdiff_self, my_segmentBound_self, my_maxSection_empty_left A hA]
    have hkl : k ≤ l := Nat.lt_succ_iff.1 hk'
    have hln : l < n := hl
    rw [my_prefixSet_succ_sdiff σ hkl hln, my_segmentBound_succ A σ hkl hln,
      h _ _ _ Finset.disjoint_sdiff (my_disjoint_prefixSet_singleton σ hkl hln)
        (my_disjoint_sdiff_prefixSet_singleton σ hln),
      Finset.union_sdiff_of_subset (my_prefixSet_mono σ hkl), ih hkl hln.le]

/-- The rank of a coordinate: `0` on `I`, `1` on `J`, `2` on `K` and `3` elsewhere.  Sorting
the coordinates by rank lists `I` first, then `J`, then `K`. -/
private def my_rankOf (I J K : Finset (Fin n)) (i : Fin n) : ℕ :=
  if i ∈ I then 0 else if i ∈ J then 1 else if i ∈ K then 2 else 3

private theorem my_filter_rankOf_le_zero (I J K : Finset (Fin n)) :
    (Finset.univ.filter fun i => my_rankOf I J K i ≤ 0) = I := by
  ext i
  unfold my_rankOf
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hiI : i ∈ I <;> by_cases hiJ : i ∈ J <;> by_cases hiK : i ∈ K <;> simp [hiI, hiJ, hiK]

private theorem my_filter_rankOf_le_one (I J K : Finset (Fin n)) :
    (Finset.univ.filter fun i => my_rankOf I J K i ≤ 1) = I ∪ J := by
  ext i
  unfold my_rankOf
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
  by_cases hiI : i ∈ I <;> by_cases hiJ : i ∈ J <;> by_cases hiK : i ∈ K <;> simp [hiI, hiJ, hiK]

private theorem my_filter_rankOf_le_two (I J K : Finset (Fin n)) :
    (Finset.univ.filter fun i => my_rankOf I J K i ≤ 2) = I ∪ J ∪ K := by
  ext i
  unfold my_rankOf
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
  by_cases hiI : i ∈ I <;> by_cases hiJ : i ∈ J <;> by_cases hiK : i ∈ K <;> simp [hiI, hiJ, hiK]

/-- If the ordering `σ` sorts the coordinates by a rank `r`, the coordinates of rank at most
`t` are exactly the ones listed first, i.e. a prefix of the ordering. -/
private theorem my_prefixSet_eq_of_monotone (σ : Equiv.Perm (Fin n)) {r : Fin n → ℕ}
    (hmono : Monotone (r ∘ σ)) (t : ℕ) :
    my_prefixSet σ (Finset.univ.filter fun i => r i ≤ t).card
      = Finset.univ.filter fun i => r i ≤ t := by
  have hcard : (Finset.univ.filter fun j : Fin n => r (σ j) ≤ t).card
      = (Finset.univ.filter fun i => r i ≤ t).card :=
    Finset.card_equiv σ fun j => by simp
  ext i
  rw [my_mem_prefixSet, Finset.mem_filter, ← hcard]
  have hij : r i = (r ∘ σ) (σ.symm i) := by simp
  rw [hij]
  simp only [Finset.mem_univ, true_and]
  constructor
  · intro hlt
    by_contra hgt
    push Not at hgt
    have hsub : (Finset.univ.filter fun j : Fin n => r (σ j) ≤ t) ⊆ Finset.Iio (σ.symm i) := by
      intro j' hj'
      rw [Finset.mem_Iio]
      by_contra hle
      push Not at hle
      exact absurd (Finset.mem_filter.1 hj').2 (not_le.2 (lt_of_lt_of_le hgt (hmono hle)))
    have := Finset.card_le_card hsub
    rw [Fin.card_Iio] at this
    omega
  · intro hle
    have hsub : Finset.Iic (σ.symm i) ⊆ Finset.univ.filter fun j : Fin n => r (σ j) ≤ t :=
      fun j' hj' => Finset.mem_filter.2
        ⟨Finset.mem_univ _, (hmono (Finset.mem_Iic.1 hj')).trans hle⟩
    have := Finset.card_le_card hsub
    rw [Fin.card_Iic] at this
    omega

private theorem maxSection_mul_projCard_le_c_mul_card_helper (A : Finset (∀ i, X i)) {c : ℝ}
    (hA : IsCUniform c A) (I : Finset (Fin n)) :
    (maxSection A (univ \ I) I : ℝ) * projCard A I ≤ c * A.card := by
  set σ := Tuple.sort (my_rankOf I ∅ ∅)
  have hT := my_prefixSet_eq_of_monotone σ (Tuple.monotone_sort (my_rankOf I ∅ ∅))
  have hpa : my_prefixSet σ I.card = I := by
    have := hT 0
    rwa [my_filter_rankOf_le_zero] at this
  have hpc : my_prefixSet σ n = univ := by
    exact my_prefixSet_of_le σ le_rfl
  have h_I_card : I.card ≤ n := by
    have h1 := Finset.card_le_card (Finset.subset_univ I)
    have h2 : (Finset.univ : Finset (Fin n)).card = n := Fintype.card_fin n
    rwa [h2] at h1
  have s1 := my_maxSection_prefixSet_le A σ 0 I.card (Nat.zero_le _) h_I_card
  rw [my_prefixSet_zero, hpa, Finset.sdiff_empty] at s1
  have s2 := my_maxSection_prefixSet_le A σ I.card n h_I_card le_rfl
  rw [hpa, hpc] at s2
  have hchain := hA σ
  have hchain2 : my_segmentBound A σ 0 I.card * my_segmentBound A σ I.card n = chainBound A σ := by
    exact (my_segmentBound_mul A σ (Nat.zero_le _) h_I_card).trans (my_segmentBound_zero_n A σ)
  have hmul : (maxSection A I ∅ : ℝ) * maxSection A (univ \ I) I ≤
    my_segmentBound A σ 0 I.card * my_segmentBound A σ I.card n := by
    have h1 : (maxSection A I ∅ : ℝ) ≤ my_segmentBound A σ 0 I.card := Nat.cast_le.mpr s1
    have h2 : (maxSection A (univ \ I) I : ℝ) ≤ my_segmentBound A σ I.card n := Nat.cast_le.mpr s2
    exact mul_le_mul h1 h2 (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hmul2 : (maxSection A I ∅ : ℝ) * maxSection A (univ \ I) I ≤ chainBound A σ := by
    calc
      (maxSection A I ∅ : ℝ) * maxSection A (univ \ I) I ≤
        my_segmentBound A σ 0 I.card * my_segmentBound A σ I.card n := hmul
      _ = chainBound A σ := by exact_mod_cast hchain2
  rw [maxSection_empty] at hmul2
  have h_comm : (maxSection A (univ \ I) I * projCard A I : ℝ) =
    projCard A I * maxSection A (univ \ I) I := mul_comm _ _
  rw [h_comm]
  exact le_trans hmul2 hchain

omit [(i : Fin n) → Fintype (X i)] in
private lemma my_entropy_le_logb_card_rangeFinset {Ω : Type*} [Fintype Ω]
    {α : Type*} [DecidableEq α]
    (μ : FiniteProbSpace Ω) (X : Ω → α) :
    entropy μ X ≤ Real.logb 2 (rangeFinset X).card := by
  let X' : Ω → {a // a ∈ rangeFinset X} := fun ω => ⟨X ω, mem_rangeFinset.2 ⟨ω, rfl⟩⟩
  have heq : entropy μ X = entropy μ X' := by
    have h := entropy_comp_of_injective μ X' Subtype.val_injective
    simpa [X', Function.comp_def] using h
  rw [heq, entropy_eq_entropyDist]
  have hsum : ∑ a, μ.dist X' a = 1 := by
    rw [← μ.sum_dist_eq_one X']
    exact (Finset.sum_subset (Finset.subset_univ _) fun a _ ha =>
      μ.dist_eq_zero_of_not_mem_range ha).symm
  simpa using Kolmogorov.entropyDist_le_logb_card (μ.dist_nonneg X') hsum

omit [(i : Fin n) → Fintype (X i)] in
private theorem my_dist_restrictTo_uniformProbOn (A : Finset (∀ i, X i)) (hA : A.Nonempty)
    (I : Finset (Fin n)) (q : (i : I) → X i.val) :
    (uniformProbOn A hA).dist (fun ω : {a // a ∈ A} => restrictTo I ω.val) q
      = ((A.filter fun a => restrictTo I a = q).card : ℝ) * (A.card : ℝ)⁻¹ := by
  have hcard : (Finset.univ.filter fun ω : {a // a ∈ A} => restrictTo I ω.val = q).card
      = (A.filter fun a => restrictTo I a = q).card := by
    rw [Finset.univ_eq_attach, Finset.filter_attach (fun a => restrictTo I a = q) A,
      Finset.card_map, Finset.card_attach]
  simp only [FiniteProbSpace.dist, FiniteProbSpace.probOf, uniformProbOn, Finset.sum_const,
    nsmul_eq_mul]
  congr 1
  exact_mod_cast hcard

omit [(i : Fin n) → Fintype (X i)] in
private theorem my_card_filter_restrictTo_eq (A : Finset (∀ i, X i)) (I : Finset (Fin n))
    (p : (i : I) → X i.val) :
    (A.filter fun a => restrictTo I a = p).card = (sectionOver A (univ \ I) I p).card := by
  rw [sectionOver, Finset.card_image_of_injOn]
  intro a ha b hb h
  simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ha hb
  funext i
  by_cases hi : i ∈ I
  · exact (congrFun ha.2 ⟨i, hi⟩).trans (congrFun hb.2 ⟨i, hi⟩).symm
  · exact congrFun h ⟨i, Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hi⟩⟩

omit [(i : Fin n) → Fintype (X i)] in
private theorem my_entropy_ge_of_prob_le {Ω : Type*} [Fintype Ω]
    {α : Type*} [DecidableEq α] (μ : FiniteProbSpace Ω) (X : Ω → α) {bound : ℝ}
    (hbound : ∀ a ∈ rangeFinset X, μ.dist X a ≤ bound)
    (h_pos : 0 < bound) :
    - Real.logb 2 bound ≤ entropy μ X := by
  have _ := h_pos
  have hsum : ∑ a ∈ rangeFinset X, μ.dist X a = 1 := μ.sum_dist_eq_one X
  unfold entropy
  have h_ineq : ∀ a ∈ rangeFinset X, μ.dist X a * - Real.logb 2 bound ≤
    negMulLog2 (μ.dist X a) := by
    intro a ha
    have hd : μ.dist X a ≤ bound := hbound a ha
    by_cases h0 : μ.dist X a = 0
    · rw [h0]
      simp
    have hp : 0 < μ.dist X a := lt_of_le_of_ne (μ.dist_nonneg X a) (Ne.symm h0)
    have h1 : Real.logb 2 (μ.dist X a) ≤ Real.logb 2 bound := by
      exact Real.logb_le_logb_of_le (by norm_num) hp hd
    have h2 : - Real.logb 2 bound ≤ - Real.logb 2 (μ.dist X a) := neg_le_neg h1
    have h3 : μ.dist X a * - Real.logb 2 bound ≤ μ.dist X a * - Real.logb 2 (μ.dist X a) :=
      mul_le_mul_of_nonneg_left h2 (μ.dist_nonneg X a)
    have h_negMulLog2 : μ.dist X a * - Real.logb 2 (μ.dist X a) = negMulLog2 (μ.dist X a) := by
      unfold negMulLog2 Real.negMulLog Real.logb
      ring
    rwa [← h_negMulLog2]
  have h2 : ∑ a ∈ rangeFinset X, μ.dist X a * - Real.logb 2 bound ≤
    ∑ a ∈ rangeFinset X, negMulLog2 (μ.dist X a) := Finset.sum_le_sum h_ineq
  rw [← Finset.sum_mul, hsum, one_mul] at h2
  exact h2

/-- Theorem 210(d), in the dependent-alphabet form needed by its corollary: after injectively
recoding every coordinate into `ℕ`, the entropy of each projection of a uniformly chosen point
is between its log-size minus `log c` and its log-size. -/
private theorem entropySub_uniformProbOn_enc_bounds_of_isCUniform {c : ℝ}
    (A : Finset (∀ i, X i)) (hA : A.Nonempty) (hU : IsCUniform c A)
    (enc : ∀ i, X i → ℕ) (henc : ∀ i, Function.Injective (enc i))
    (I : Finset (Fin n)) :
    Real.logb 2 (projCard A I) - Real.logb 2 c ≤
        entropySub (uniformProbOn A hA) (fun i ω => enc i (ω.val i)) I ∧
      entropySub (uniformProbOn A hA) (fun i ω => enc i (ω.val i)) I ≤
        Real.logb 2 (projCard A I) := by
  set Z : Fin n → {a // a ∈ A} → ℕ := fun i ω => enc i (ω.val i)
  have h_entropy : entropySub (uniformProbOn A hA) (fun i ω => enc i (ω.val i)) I =
      entropy (uniformProbOn A hA) (subtuple Z I) := rfl
  have h_range : rangeFinset (subtuple Z I) =
      (proj A I).image (fun p => fun i => enc i.val (p i)) := by
    ext p
    simp only [rangeFinset, proj, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨ω, rfl⟩
      exact ⟨restrictTo I ω.val, ⟨ω.val, ω.2, rfl⟩, rfl⟩
    · rintro ⟨q, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩
  have h_card : (rangeFinset (subtuple Z I)).card = projCard A I := by
    rw [h_range, Finset.card_image_of_injOn]
    · exact rfl
    · intro p1 hp1 p2 hp2 h
      funext i
      exact henc i.val (congrFun h i)
  constructor
  · have hA0_pos : (0 : ℝ) < A.card := by exact_mod_cast (Finset.card_pos.2 hA)
    have h_ineq := maxSection_mul_projCard_le_c_mul_card_helper A hU I
    have h_c_pos : 0 ≤ c := by
      have hc : (0 : ℝ) ≤ c * A.card := by
        exact le_trans (by positivity) h_ineq
      nlinarith
    have hc_pos_strict : 0 < c := by
      by_contra hc0
      push Not at hc0
      have hc_eq_zero : c = 0 := le_antisymm hc0 h_c_pos
      rw [hc_eq_zero, zero_mul] at h_ineq
      have hp : 0 < projCard A I := Finset.card_pos.2 (Finset.Nonempty.image hA (restrictTo I))
      have hms : 0 < maxSection A (univ \ I) I := by
        obtain ⟨a, ha⟩ := hA
        have h1 : 1 ≤ (sectionOver A (univ \ I) I (restrictTo I a)).card :=
          Finset.card_pos.2 ⟨restrictTo (univ \ I) a,
            Finset.mem_image.2 ⟨a, Finset.mem_filter.2 ⟨ha, rfl⟩, rfl⟩⟩
        exact lt_of_lt_of_le (by norm_num) (h1.trans (Finset.le_sup (f :=
          fun p => (sectionOver A (univ \ I) I p).card) (Finset.mem_univ _)))
      have h_mul_pos : (0 : ℝ) < (maxSection A (univ \ I) I : ℝ) * projCard A I :=
        mul_pos (Nat.cast_pos.mpr hms) (Nat.cast_pos.mpr hp)
      linarith
    have hp : (0 : ℝ) < projCard A I :=
      Nat.cast_pos.mpr (Finset.card_pos.2 (Finset.Nonempty.image hA (restrictTo I)))
    have h_bound : ∀ q ∈ rangeFinset (subtuple Z I),
        (uniformProbOn A hA).dist (subtuple Z I) q ≤ c / projCard A I := by
      intro q hq
      obtain ⟨q', hq', rfl⟩ := Finset.mem_image.1 (by rwa [← h_range])
      have h1 : (uniformProbOn A hA).dist (subtuple Z I) (fun i => enc i.val (q' i)) =
          ((A.filter fun a => restrictTo I a = q').card : ℝ) / A.card := by
        have hd := my_dist_restrictTo_uniformProbOn A hA I q'
        have h_filter : (A.filter fun a => (fun i => enc i.val (a i.val)) =
          fun i => enc i.val (q' i)) =
            A.filter fun a => restrictTo I a = q' := by
          apply Finset.filter_congr
          intro a ha
          constructor
          · intro h
            funext i
            exact henc i.val (congrFun h i)
          · intro h
            funext i
            exact congrArg (enc i.val) (congrFun h i)
        have h_dist_eq : (uniformProbOn A hA).dist (subtuple Z I) (fun i => enc i.val (q' i)) =
            (uniformProbOn A hA).dist (fun ω : {a // a ∈ A} => restrictTo I ω.val) q' := by
          unfold FiniteProbSpace.dist FiniteProbSpace.probOf
          congr 1
          ext ω
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · intro h
            funext i
            exact henc i.val (congrFun h i)
          · intro h
            funext i
            exact congrArg (enc i.val) (congrFun h i)
        rw [h_dist_eq, hd, div_eq_mul_inv]
      rw [h1]
      have h2 : ((A.filter fun a => restrictTo I a = q').card : ℝ) ≤
        (maxSection A (univ \ I) I : ℝ) := by
        rw [my_card_filter_restrictTo_eq]
        exact Nat.cast_le.mpr (Finset.le_sup (f :=
          fun p => (sectionOver A (univ \ I) I p).card) (Finset.mem_univ _))
      have h3 : ((A.filter fun a => restrictTo I a = q').card : ℝ) * projCard A I ≤
        c * A.card := by
        calc
          ((A.filter fun a => restrictTo I a = q').card : ℝ) * projCard A I ≤
            (maxSection A (univ \ I) I : ℝ) * projCard A I := by
            exact mul_le_mul h2 le_rfl (Nat.cast_nonneg _) (Nat.cast_nonneg _)
          _ ≤ c * A.card := h_ineq
      rw [div_le_div_iff₀ hA0_pos hp]
      exact h3
    have h_lower :=
      my_entropy_ge_of_prob_le (uniformProbOn A hA) (subtuple Z I) h_bound (by positivity)
    have h_log_div : - Real.logb 2 (c / projCard A I) =
      Real.logb 2 (projCard A I) - Real.logb 2 c := by
      rw [Real.logb_div hc_pos_strict.ne' hp.ne']
      ring
    rw [h_entropy]
    have _ := hp
    rwa [h_log_div] at h_lower
  · rw [h_entropy, ← h_card]
    exact my_entropy_le_logb_card_rangeFinset _ _


omit [∀ i, Fintype (X i)] in
/-- Summing coordinatewise entropy approximations costs at most the sum of the absolute
coefficients times their common error.  This is the linear-error step in the corollary to
Theorem 210. -/
private theorem evalLogSize_le_of_entropy_approx (f : LinearForm n)
    (A : Finset (∀ i, X i)) {Ω : Type} [Fintype Ω] (μ : FiniteProbSpace Ω)
    (Z : Fin n → Ω → ℕ) (hentropy : f.evalEntropy μ Z ≤ 0) (r : ℝ)
    (happrox : ∀ I ∈ nonemptyParts n,
      |Real.logb 2 (projCard A I) - entropySub μ Z I| ≤ r) :
    f.evalLogSize A ≤ (∑ I ∈ nonemptyParts n, |f I|) * r := by
  have hdiff : |f.evalLogSize A - f.evalEntropy μ Z| ≤
      (∑ I ∈ nonemptyParts n, |f I|) * r := by
    dsimp [LinearForm.evalLogSize, LinearForm.evalEntropy]
    rw [← Finset.sum_sub_distrib]
    calc
      |∑ I ∈ nonemptyParts n,
          (f I * Real.logb 2 (projCard A I) - f I * entropySub μ Z I)|
          ≤ ∑ I ∈ nonemptyParts n,
              |f I * Real.logb 2 (projCard A I) - f I * entropySub μ Z I| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ I ∈ nonemptyParts n,
          |f I| * |Real.logb 2 (projCard A I) - entropySub μ Z I| := by
        apply Finset.sum_congr rfl
        intro I _
        rw [← mul_sub, abs_mul]
      _ ≤ ∑ I ∈ nonemptyParts n, |f I| * r := by
        apply Finset.sum_le_sum
        intro I hI
        exact mul_le_mul_of_nonneg_left (happrox I hI) (abs_nonneg _)
      _ = (∑ I ∈ nonemptyParts n, |f I|) * r := by
        rw [← Finset.sum_mul]
  have hle : f.evalLogSize A - f.evalEntropy μ Z ≤
      (∑ I ∈ nonemptyParts n, |f I|) * r :=
    (le_abs_self _).trans hdiff
  linarith

/-- The unnumbered corollary of Theorem 210: a linear inequality that is true for entropies is
true for the log-sizes of the projections of a `c`-uniform set up to the error `λ log c`, where
`λ = ∑_I |λ_I|` is the sum of the absolute values of the coefficients.
SUV Section 10.5, p. 325 (unnumbered corollary of Theorem 210). -/
theorem evalLogSize_le_of_isCUniform (f : LinearForm n) (hf : HoldsForEntropies f) {c : ℝ}
    (A : Finset (∀ i, X i)) (hA : A.Nonempty) (hU : IsCUniform c A) :
    f.evalLogSize A ≤ (∑ I ∈ nonemptyParts n, |f I|) * Real.logb 2 c := by
  let enc : ∀ i, X i → ℕ := fun i x => (Fintype.equivFin (X i) x).val
  have henc : ∀ i, Function.Injective (enc i) := fun i =>
    Fin.val_injective.comp (Fintype.equivFin (X i)).injective
  let Z : Fin n → {a // a ∈ A} → ℕ := fun i ω => enc i (ω.val i)
  have hentropy : f.evalEntropy (uniformProbOn A hA) Z ≤ 0 :=
    hf {a // a ∈ A} (uniformProbOn A hA) Z
  have hcardpos : (0 : ℝ) < A.card := by
    exact_mod_cast Finset.card_pos.2 hA
  have hcardchain : (A.card : ℝ) ≤ chainBound A (Equiv.refl (Fin n)) := by
    exact_mod_cast card_le_chainBound A (Equiv.refl (Fin n))
  have hc : 1 ≤ c := by
    have hu := hU (Equiv.refl (Fin n))
    nlinarith
  have hlog : 0 ≤ Real.logb 2 c := by
    exact (Real.logb_nonneg_iff one_lt_two (lt_of_lt_of_le zero_lt_one hc)).2 hc
  apply evalLogSize_le_of_entropy_approx f A (uniformProbOn A hA) Z hentropy
    (Real.logb 2 c)
  intro I hI
  have hb := entropySub_uniformProbOn_enc_bounds_of_isCUniform A hA hU enc henc I
  apply abs_le.2
  constructor <;> dsimp [Z] at hb ⊢ <;> linarith

end General

section Entropies

variable {α : Type} [Fintype α] [DecidableEq α]

/-- **Theorem 210(d).**  If `ξ` is uniformly distributed in a `c`-uniform set `A`, the entropy
of its projection onto the coordinates `I` lies between `log m(I) − log c` and `log m(I)`.
SUV Theorem 210(d), p. 324. -/
theorem entropySub_uniformProbOn_bounds_of_isCUniform {c : ℝ} (A : Finset (Fin n → α))
    (hA : A.Nonempty) (hU : IsCUniform c A) (I : Finset (Fin n)) :
    Real.logb 2 (projCard A I) - Real.logb 2 c
        ≤ entropySub (uniformProbOn A hA) (uniformCoords A) I ∧
      entropySub (uniformProbOn A hA) (uniformCoords A) I ≤ Real.logb 2 (projCard A I) := by
  let enc : ∀ i : Fin n, α → ℕ := fun _ x => (Fintype.equivFin α x).val
  have henc : ∀ i, Function.Injective (enc i) := fun _ =>
    Fin.val_injective.comp (Fintype.equivFin α).injective
  have h := entropySub_uniformProbOn_enc_bounds_of_isCUniform A hA hU enc henc I
  have h_eq : entropySub (uniformProbOn A hA) (fun i ω => enc i (ω.val i)) I =
      entropySub (uniformProbOn A hA) (uniformCoords A) I := by
    unfold entropySub
    let g : (I → α) → (I → ℕ) := fun p i => enc i.val (p i)
    have hg : Function.Injective g := by
      intro p1 p2 h_eq2
      funext i
      exact henc i.val (congrFun h_eq2 i)
    have h_comp : subtuple (fun i ω => enc i (ω.val i)) I = g ∘ subtuple (uniformCoords A) I := rfl
    rw [h_comp]
    exact entropy_comp_of_injective (uniformProbOn A hA) _ hg
  rwa [h_eq] at h

private theorem condEntropyGiven_le_logb_card_eventRange {Ω β : Type*} [Fintype Ω]
    [DecidableEq β] (μ : FiniteProbSpace Ω) (X : Ω → β) (E : Finset Ω) :
    condEntropyGiven μ X E ≤ Real.logb 2 ((E.image X).card : ℝ) := by
  by_cases hE : 0 < μ.probOf E
  · let S := E.image X
    let p : S → ℝ := fun a => μ.condDist X E a.1
    have hp : ∀ a, 0 ≤ p a := fun a => μ.condDist_nonneg X E a.1
    have hsum_finset : ∑ a ∈ S, μ.condDist X E a = 1 := by
      simp only [FiniteProbSpace.condDist, ← Finset.sum_div]
      rw [div_eq_one_iff_eq hE.ne']
      simp only [FiniteProbSpace.probOf]
      exact Finset.sum_fiberwise_of_maps_to
        (fun ω hω => Finset.mem_image.2 ⟨ω, hω, rfl⟩) μ.prob
    have hsum : ∑ a : S, p a = 1 := by
      rw [← hsum_finset]
      exact Finset.sum_attach S (fun a => μ.condDist X E a)
    have hsubset : S ⊆ rangeFinset X := by
      intro a ha
      obtain ⟨ω, _, rfl⟩ := Finset.mem_image.1 ha
      exact mem_rangeFinset.2 ⟨ω, rfl⟩
    have hzero : ∀ a ∈ rangeFinset X, a ∉ S → μ.condDist X E a = 0 := by
      intro a _ ha
      have hempty : E.filter (fun ω => X ω = a) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro ω hω hXa
        exact ha (Finset.mem_image.2 ⟨ω, hω, hXa⟩)
      simp [FiniteProbSpace.condDist, hempty, FiniteProbSpace.probOf]
    have h_entropy : condEntropyGiven μ X E = ∑ a : S, negMulLog2 (p a) := by
      unfold condEntropyGiven
      rw [← Finset.sum_subset hsubset]
      · simpa [p] using
          (Finset.sum_attach S (fun a => negMulLog2 (μ.condDist X E a))).symm
      · intro a ha_range haS
        rw [hzero a ha_range haS, negMulLog2_zero]
    rw [h_entropy]
    have hs : (S.card : ℝ) = (Fintype.card S : ℝ) := by norm_cast; exact (Fintype.card_coe S).symm
    rw [hs]
    exact entropyDist_le_logb_card hp hsum
  · have hprob : μ.probOf E = 0 := le_antisymm (not_lt.1 hE) (μ.probOf_nonneg E)
    have hzero : condEntropyGiven μ X E = 0 := by
      unfold condEntropyGiven
      apply Finset.sum_eq_zero
      intro a _
      simp [FiniteProbSpace.condDist, hprob, negMulLog2_zero]
    rw [hzero]
    by_cases hcard : (E.image X).card = 0
    · simp [hcard, Real.logb_zero]
    · apply Real.logb_nonneg
      · norm_num
      · exact_mod_cast Nat.one_le_iff_ne_zero.2 hcard

private theorem condEntropySub_uniformProbOn_le_logb_maxSection
    (A : Finset (Fin n → α)) (hA : A.Nonempty) (I J : Finset (Fin n)) :
    condEntropySub (uniformProbOn A hA) (uniformCoords A) J I ≤
      Real.logb 2 (maxSection A J I) := by
  let μ := uniformProbOn A hA
  let X := subtuple (uniformCoords A) J
  let Y := subtuple (uniformCoords A) I
  have hsection : ∀ b,
      ((Finset.univ.filter fun ω : {a // a ∈ A} => Y ω = b).image X).card ≤
        maxSection A J I := by
    intro b
    have heq : (Finset.univ.filter fun ω : {a // a ∈ A} => Y ω = b).image X =
        sectionOver A J I b := by
      ext q
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
        sectionOver]
      constructor
      · rintro ⟨ω, hω, rfl⟩
        exact ⟨ω.val, ⟨ω.property, hω⟩, rfl⟩
      · rintro ⟨a, ⟨ha, hIa⟩, rfl⟩
        exact ⟨⟨a, ha⟩, hIa, rfl⟩
    rw [heq]
    exact Finset.le_sup (f := fun p => (sectionOver A J I p).card) (Finset.mem_univ b)
  have hone : 1 ≤ maxSection A J I := by
    obtain ⟨a, ha⟩ := hA
    have hmem : restrictTo J a ∈ sectionOver A J I (restrictTo I a) :=
      Finset.mem_image.2 ⟨a, Finset.mem_filter.2 ⟨ha, rfl⟩, rfl⟩
    exact (Finset.card_pos.2 ⟨_, hmem⟩).trans_le
      (Finset.le_sup (f := fun p => (sectionOver A J I p).card) (Finset.mem_univ _))
  have hlog : ∀ b, Real.logb 2
      (((Finset.univ.filter fun ω : {a // a ∈ A} => Y ω = b).image X).card : ℝ) ≤
        Real.logb 2 (maxSection A J I) := by
    intro b
    by_cases hcard :
        ((Finset.univ.filter fun ω : {a // a ∈ A} => Y ω = b).image X).card = 0
    · rw [hcard]
      simp only [Nat.cast_zero, Real.logb_zero]
      apply Real.logb_nonneg
      · norm_num
      · exact_mod_cast hone
    · apply Real.logb_le_logb_of_le
      · norm_num
      · exact_mod_cast Nat.pos_of_ne_zero hcard
      · exact_mod_cast hsection b
  unfold condEntropySub condEntropy
  change (∑ b ∈ rangeFinset Y,
      μ.dist Y b * condEntropyGiven μ X (Finset.univ.filter fun ω => Y ω = b)) ≤ _
  calc
    _ ≤ ∑ b ∈ rangeFinset Y, μ.dist Y b * Real.logb 2 (maxSection A J I) := by
      apply Finset.sum_le_sum
      intro b hb
      apply mul_le_mul_of_nonneg_left _ (μ.dist_nonneg Y b)
      exact (condEntropyGiven_le_logb_card_eventRange μ X _).trans (hlog b)
    _ = Real.logb 2 (maxSection A J I) := by
      rw [← Finset.sum_mul, μ.sum_dist_eq_one, one_mul]

private theorem condEntropySub_defect_le_logb_of_isCUniform {c : ℝ}
    (A : Finset (Fin n → α)) (hA : A.Nonempty) (hU : IsCUniform c A)
    (I J : Finset (Fin n)) (hIJ : Disjoint I J) :
    Real.logb 2 (maxSection A J I) -
        condEntropySub (uniformProbOn A hA) (uniformCoords A) J I ≤ Real.logb 2 c := by
  classical
  set μ := uniformProbOn A hA
  set Z := uniformCoords A
  set K : Finset (Fin n) := univ \ (I ∪ J) with hKdef
  have hone : ∀ J' I' : Finset (Fin n), 1 ≤ maxSection A J' I' := by
    intro J' I'
    obtain ⟨a, ha⟩ := hA
    have hmem : restrictTo J' a ∈ sectionOver A J' I' (restrictTo I' a) :=
      Finset.mem_image.2 ⟨a, Finset.mem_filter.2 ⟨ha, rfl⟩, rfl⟩
    exact (Finset.card_pos.2 ⟨_, hmem⟩).trans_le
      (Finset.le_sup (f := fun p => (sectionOver A J' I' p).card) (Finset.mem_univ _))
  -- the chain rule, twice
  have hc1 : condEntropySub μ Z J I = entropySub μ Z (I ∪ J) - entropySub μ Z I := by
    rw [condEntropySub, condEntropy_eq_sub, ← entropySub_union, Finset.union_comm]
    rfl
  have hc2 : condEntropySub μ Z K (I ∪ J) = entropySub μ Z univ - entropySub μ Z (I ∪ J) := by
    rw [condEntropySub, condEntropy_eq_sub, ← entropySub_union,
      Finset.sdiff_union_of_subset (Finset.subset_univ _)]
    rfl
  have hK := condEntropySub_uniformProbOn_le_logb_maxSection A hA (I ∪ J) K
  have hI := (entropySub_uniformProbOn_bounds_of_isCUniform A hA hU I).2
  -- the whole tuple is uniformly distributed on `A`
  have hcardpos : (0 : ℝ) < A.card := by exact_mod_cast Finset.card_pos.2 hA
  have hfull : Real.logb 2 A.card ≤ entropySub μ Z univ := by
    have hb : ∀ q ∈ rangeFinset (subtuple Z univ),
        μ.dist (subtuple Z univ) q ≤ (A.card : ℝ)⁻¹ := by
      intro q _
      have hd := my_dist_restrictTo_uniformProbOn (X := fun _ => α) A hA univ q
      have hle : ((A.filter fun a => restrictTo (X := fun _ => α) univ a = q).card : ℝ) ≤ 1 := by
        have hc1 : (A.filter fun a => restrictTo (X := fun _ => α) univ a = q).card ≤ 1 := by
          apply Finset.card_le_one.2
          intro a ha b hb
          rw [Finset.mem_filter] at ha hb
          exact restrictTo_univ_injective (X := fun _ => α) (ha.2.trans hb.2.symm)
        exact_mod_cast hc1
      change μ.dist (fun ω : {a // a ∈ A} => restrictTo (X := fun _ => α) univ ω.val) q ≤ _
      rw [hd]
      calc ((A.filter fun a => restrictTo (X := fun _ => α) univ a = q).card : ℝ) * (A.card : ℝ)⁻¹
          ≤ 1 * (A.card : ℝ)⁻¹ := by gcongr
        _ = (A.card : ℝ)⁻¹ := one_mul _
    have h := my_entropy_ge_of_prob_le μ (subtuple Z univ) hb (inv_pos.2 hcardpos)
    rw [Real.logb_inv, neg_neg] at h
    exact h
  -- the block chain inequality
  have hblock := three_block_maxSection_le_of_isCUniform (X := fun _ => α) A hU I J hIJ
  rw [maxSection_empty] at hblock
  have h1 : (1 : ℝ) ≤ projCard A I := by
    have := hone I ∅
    rw [maxSection_empty] at this
    exact_mod_cast this
  have h2 : (1 : ℝ) ≤ maxSection A J I := by exact_mod_cast hone J I
  have h3 : (1 : ℝ) ≤ maxSection A K (I ∪ J) := by exact_mod_cast hone K (I ∪ J)
  have hprodpos : (0 : ℝ) < (projCard A I : ℝ) * maxSection A J I * maxSection A K (I ∪ J) := by
    positivity
  push_cast at hblock
  have hcpos : 0 < c := by
    by_contra hc
    push Not at hc
    have : c * A.card ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc hcardpos.le
    linarith
  have hlog := Real.logb_le_logb_of_le (b := 2) (by norm_num) hprodpos hblock
  rw [Real.logb_mul (by positivity) (by positivity), Real.logb_mul (by positivity)
    (by positivity), Real.logb_mul hcpos.ne' hcardpos.ne'] at hlog
  linarith


/-- **Theorem 210(e).**  If `ξ` is uniformly distributed in a `c`-uniform set `A` and `I, J`
are disjoint sets of coordinates, the conditional entropy `H(ξ_J | ξ_I)` lies between
`log m(J | I) − log c` and `log m(J | I)`.  SUV Theorem 210(e), p. 324. -/
theorem condEntropySub_uniformProbOn_bounds_of_isCUniform {c : ℝ} (A : Finset (Fin n → α))
    (hA : A.Nonempty) (hU : IsCUniform c A) (I J : Finset (Fin n)) (hIJ : Disjoint I J) :
    Real.logb 2 (maxSection A J I) - Real.logb 2 c
        ≤ condEntropySub (uniformProbOn A hA) (uniformCoords A) J I ∧
      condEntropySub (uniformProbOn A hA) (uniformCoords A) J I
        ≤ Real.logb 2 (maxSection A J I) := by
  constructor
  · have hdefect := condEntropySub_defect_le_logb_of_isCUniform A hA hU I J hIJ
    linarith
  · exact condEntropySub_uniformProbOn_le_logb_maxSection A hA I J

end Entropies

end Kolmogorov
