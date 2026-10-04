/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.InformationInequalities.UniformSets
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Uniform sets: the chain inequalities, and entropies of a uniform point

SUV Section 10.2, pp. 318–321.

For every finite `A ⊆ X_1 × ⋯ × X_n` and every ordering `k_1, …, k_n` of the coordinates the
chain inequality
`m(k_1, …, k_n) ≤ m(k_1) · m(k_2 | k_1) ⋯ m(k_n | k_1, …, k_{n-1})`
holds, with `|A|` on the left; the set is **uniform** when all `n!` of these are equalities.
The grouping argument of p. 320 turns uniformity into the single equation
`m(J ∪ K | I) = m(J | I) · m(K | I ∪ J)` for all disjoint `I, J, K` (Problem 285), from which
uniformity of projections and of sections follows (Problems 286 and 287).

Theorem 205 identifies uniformity with a probabilistic property: `A` is uniform exactly when
every subtuple of a uniformly random point of `A` is uniformly distributed on its range.  Its
corollary `H(ξ_I) = log m_A(I)` is what makes the whole chapter work, and Theorem 206 is the
one-line consequence: every entropy inequality holds for the log-sizes of the projections of a
uniform set.

Non-empty sets.  Section 10.2 fixes a **non-empty** `A ⊆ X_1 × ⋯ × X_n` once and for all
(p. 318).  The predicates `IsUniform` and `IsCUniform` of `InformationInequalities/UniformSets`
do not carry that condition — `∅` satisfies the chain equalities in every positive dimension —
so the statements below that would otherwise be false for `A = ∅` carry it as a hypothesis
`A.Nonempty` (Problems 285 and 286 here, Theorem 210(b) in `AlmostUniform`).

Deviation from the printed text: in the statements that mention entropies the coordinate sets
`X_1, …, X_n` are taken to be one and the same finite type `α`, because the entropy layer
indexes a tuple of random variables by a single value type.  This is no loss — replace every
`X_i` by a common finite type containing all of them — and `projCard`, `maxSection`,
`IsUniform` are still the general dependent-product notions, specialised at
`X := fun _ => α`.
-/

namespace Kolmogorov

open Finset

variable {n : ℕ}

/-! ### The chain inequalities -/

section Chain

variable {X : Fin n → Type} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]

/-- The restriction of a point of `∏_{i ∈ T} X_i` to the coordinates of a subset `S ⊆ T`. -/
private def restrictSub {S T : Finset (Fin n)} (h : S ⊆ T) (q : (i : T) → X i.val) :
    (i : S) → X i.val :=
  fun i => q ⟨i.val, h i.2⟩

/-- The two-step section inequality `m(J ∪ K | I) ≤ m(J | I) · m(K | I ∪ J)`, valid for every
set `A` and all pairwise disjoint `I, J, K`: for each combination of `I`-coordinates there are
at most `m(J | I)` combinations of `J`-coordinates, and for each of them at most
`m(K | I ∪ J)` combinations of `K`-coordinates.
SUV Section 10.2, p. 319 (unnumbered). -/
theorem maxSection_union_le (A : Finset (∀ i, X i)) (I J K : Finset (Fin n))
    (hIJ : Disjoint I J) (hIK : Disjoint I K) (hJK : Disjoint J K) :
    maxSection A (J ∪ K) I ≤ maxSection A J I * maxSection A K (I ∪ J) := by
  -- The inequality needs no disjointness; the hypotheses are part of the book's statement.
  have _ := hIJ
  have _ := hIK
  have _ := hJK
  refine Finset.sup_le fun p _ => ?_
  set S := sectionOver A (J ∪ K) I p with hS
  set φ : ((i : (J ∪ K : Finset (Fin n))) → X i.val) → (i : J) → X i.val :=
    restrictSub Finset.subset_union_left with hφ
  set ψ : ((i : (J ∪ K : Finset (Fin n))) → X i.val) → (i : K) → X i.val :=
    restrictSub Finset.subset_union_right with hψ
  have himage : S.image φ = sectionOver A J I p := by
    simp only [hS, sectionOver, Finset.image_image]
    rfl
  rw [mul_comm]
  refine (Finset.card_le_mul_card_image (f := φ) S (maxSection A K (I ∪ J))
    fun q hq => ?_).trans ?_
  · obtain ⟨s, hsS, rfl⟩ := Finset.mem_image.1 hq
    obtain ⟨a₀, ha₀, rfl⟩ := Finset.mem_image.1 hsS
    rw [Finset.mem_filter] at ha₀
    refine (Finset.card_le_card_of_injOn ψ ?_ ?_).trans
      (Finset.le_sup (f := fun r => (sectionOver A K (I ∪ J) r).card)
        (Finset.mem_univ (restrictTo (I ∪ J) a₀)))
    · intro s hs
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hs
      obtain ⟨hsS', hsq⟩ := hs
      rw [hS, sectionOver] at hsS'
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hsS'
      rw [Finset.mem_filter] at ha
      refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨a, Finset.mem_filter.2 ⟨ha.1, ?_⟩, rfl⟩)
      funext i
      rcases Finset.mem_union.1 i.2 with hi | hi
      · exact congrFun (ha.2.trans ha₀.2.symm) ⟨i.1, hi⟩
      · exact congrFun hsq ⟨i.1, hi⟩
    · intro s₁ hs₁ s₂ hs₂ h
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hs₁ hs₂
      funext i
      rcases Finset.mem_union.1 i.2 with hi | hi
      · exact congrFun (hs₁.2.trans hs₂.2.symm) ⟨i.1, hi⟩
      · exact congrFun h ⟨i.1, hi⟩
  · rw [himage]
    exact Nat.mul_le_mul_left _
      (Finset.le_sup (f := fun q => (sectionOver A J I q).card) (Finset.mem_univ p))

/-- `m_A(∅ | I) ≤ 1`: a section over no coordinates is at most a single point. -/
private theorem maxSection_empty_left_le (A : Finset (∀ i, X i)) (I : Finset (Fin n)) :
    maxSection A ∅ I ≤ 1 :=
  Finset.sup_le fun _ _ => Finset.card_le_one.2 fun _ _ _ _ =>
    funext fun i => (Finset.notMem_empty i.val i.2).elim

/-- The coordinates listed in the first `l` positions of the ordering `σ`; `earlierIndices`
with a natural-number cut-off, so that `l = n` (all coordinates) is allowed. -/
private def prefixSet (σ : Equiv.Perm (Fin n)) (l : ℕ) : Finset (Fin n) :=
  (Finset.univ.filter fun j : Fin n => j.val < l).image σ

private theorem mem_prefixSet {σ : Equiv.Perm (Fin n)} {l : ℕ} {i : Fin n} :
    i ∈ prefixSet σ l ↔ (σ.symm i).val < l := by
  simp only [prefixSet, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj, rfl⟩
    simpa using hj
  · intro h
    exact ⟨σ.symm i, h, by simp⟩

private theorem earlierIndices_eq_prefixSet (σ : Equiv.Perm (Fin n)) (k : Fin n) :
    earlierIndices σ k = prefixSet σ k.val := rfl

private theorem prefixSet_zero (σ : Equiv.Perm (Fin n)) : prefixSet σ 0 = ∅ := by
  ext i
  simp [mem_prefixSet]

private theorem prefixSet_of_le (σ : Equiv.Perm (Fin n)) {l : ℕ} (hl : n ≤ l) :
    prefixSet σ l = Finset.univ := by
  ext i
  simp only [mem_prefixSet, Finset.mem_univ, iff_true]
  exact lt_of_lt_of_le (σ.symm i).isLt hl

private theorem prefixSet_mono (σ : Equiv.Perm (Fin n)) {k l : ℕ} (hkl : k ≤ l) :
    prefixSet σ k ⊆ prefixSet σ l := fun _ hi =>
  mem_prefixSet.2 (lt_of_lt_of_le (mem_prefixSet.1 hi) hkl)

private theorem prefixSet_succ (σ : Equiv.Perm (Fin n)) {l : ℕ} (hl : l < n) :
    prefixSet σ (l + 1) = insert (σ ⟨l, hl⟩) (prefixSet σ l) := by
  ext i
  simp only [mem_prefixSet, Finset.mem_insert, ← Equiv.symm_apply_eq, Fin.ext_iff]
  omega

private theorem apply_notMem_prefixSet (σ : Equiv.Perm (Fin n)) {l : ℕ} (hl : l < n) :
    σ ⟨l, hl⟩ ∉ prefixSet σ l := by
  simp [mem_prefixSet]

private theorem prefixSet_succ_sdiff (σ : Equiv.Perm (Fin n)) {k l : ℕ} (hkl : k ≤ l)
    (hl : l < n) :
    prefixSet σ (l + 1) \ prefixSet σ k = (prefixSet σ l \ prefixSet σ k) ∪ {σ ⟨l, hl⟩} := by
  rw [prefixSet_succ σ hl, Finset.insert_sdiff_of_notMem _
    (fun h => apply_notMem_prefixSet σ hl (prefixSet_mono σ hkl h)), Finset.insert_eq,
    Finset.union_comm]

private theorem disjoint_prefixSet_singleton (σ : Equiv.Perm (Fin n)) {k l : ℕ} (hkl : k ≤ l)
    (hl : l < n) : Disjoint (prefixSet σ k) {σ ⟨l, hl⟩} :=
  Finset.disjoint_singleton_right.2
    fun h => apply_notMem_prefixSet σ hl (prefixSet_mono σ hkl h)

private theorem disjoint_sdiff_prefixSet_singleton (σ : Equiv.Perm (Fin n)) {k l : ℕ}
    (hl : l < n) : Disjoint (prefixSet σ l \ prefixSet σ k) {σ ⟨l, hl⟩} :=
  Finset.disjoint_singleton_right.2
    fun h => apply_notMem_prefixSet σ hl (Finset.sdiff_subset h)

/-- The product of the chain factors `m(k_j | k_1, …, k_{j-1})` over the positions
`k ≤ j < l` of the ordering `σ`. -/
private def segmentBound (A : Finset (∀ i, X i)) (σ : Equiv.Perm (Fin n)) (k l : ℕ) : ℕ :=
  ∏ j ∈ Finset.univ.filter (fun j : Fin n => k ≤ j.val ∧ j.val < l),
    maxSection A {σ j} (earlierIndices σ j)

private theorem segmentBound_self (A : Finset (∀ i, X i)) (σ : Equiv.Perm (Fin n)) (k : ℕ) :
    segmentBound A σ k k = 1 := by
  refine Finset.prod_eq_one fun j hj => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
  omega

private theorem segmentBound_succ (A : Finset (∀ i, X i)) (σ : Equiv.Perm (Fin n)) {k l : ℕ}
    (hkl : k ≤ l) (hl : l < n) :
    segmentBound A σ k (l + 1)
      = segmentBound A σ k l * maxSection A {σ ⟨l, hl⟩} (prefixSet σ l) := by
  have hfilter : (Finset.univ.filter fun j : Fin n => k ≤ j.val ∧ j.val < l + 1)
      = insert ⟨l, hl⟩ (Finset.univ.filter fun j : Fin n => k ≤ j.val ∧ j.val < l) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  have hnot : (⟨l, hl⟩ : Fin n) ∉ Finset.univ.filter fun j : Fin n => k ≤ j.val ∧ j.val < l := by
    simp
  rw [segmentBound, hfilter, Finset.prod_insert hnot, mul_comm, earlierIndices_eq_prefixSet]
  rfl

private theorem segmentBound_mul (A : Finset (∀ i, X i)) (σ : Equiv.Perm (Fin n)) {k l m : ℕ}
    (hkl : k ≤ l) (hlm : l ≤ m) :
    segmentBound A σ k l * segmentBound A σ l m = segmentBound A σ k m := by
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
  rw [segmentBound, segmentBound, segmentBound, hfilter, Finset.prod_union hdisj]

private theorem segmentBound_zero_n (A : Finset (∀ i, X i)) (σ : Equiv.Perm (Fin n)) :
    segmentBound A σ 0 n = chainBound A σ := by
  rw [segmentBound, chainBound]
  refine Finset.prod_congr (Finset.filter_true_of_mem fun j _ => ?_) fun _ _ => rfl
  exact ⟨Nat.zero_le _, j.isLt⟩

/-- Grouping the chain factors of the positions `k ≤ j < l`: they bound the section of the
coordinates listed there over the coordinates listed before position `k`.
SUV Section 10.2, p. 320 (the grouping argument). -/
private theorem maxSection_prefixSet_le (A : Finset (∀ i, X i)) (σ : Equiv.Perm (Fin n))
    (k : ℕ) : ∀ l, k ≤ l → l ≤ n →
      maxSection A (prefixSet σ l \ prefixSet σ k) (prefixSet σ k) ≤ segmentBound A σ k l := by
  intro l
  induction l with
  | zero =>
    intro hk _
    obtain rfl : k = 0 := by omega
    rw [Finset.sdiff_self, segmentBound_self]
    exact maxSection_empty_left_le A _
  | succ l ih =>
    intro hk hl
    rcases Nat.eq_or_lt_of_le hk with hk' | hk'
    · rw [← hk', Finset.sdiff_self, segmentBound_self]
      exact maxSection_empty_left_le A _
    have hkl : k ≤ l := Nat.lt_succ_iff.1 hk'
    have hln : l < n := hl
    rw [prefixSet_succ_sdiff σ hkl hln, segmentBound_succ A σ hkl hln]
    refine (maxSection_union_le A _ _ _ Finset.disjoint_sdiff
      (disjoint_prefixSet_singleton σ hkl hln) (disjoint_sdiff_prefixSet_singleton σ hln)).trans ?_
    rw [Finset.union_sdiff_of_subset (prefixSet_mono σ hkl)]
    exact Nat.mul_le_mul_right _ (ih hkl hln.le)

/-- The chain inequality for an ordering `σ` of the coordinates:
`|A| = m(k_1, …, k_n) ≤ m(k_1) · m(k_2 | k_1) ⋯ m(k_n | k_1, …, k_{n-1})`.  For each value of
the earlier coordinates there are at most `m(· | ·)` values of the next one.
SUV Section 10.2, p. 319 (unnumbered). -/
theorem card_le_chainBound (A : Finset (∀ i, X i)) (σ : Equiv.Perm (Fin n)) :
    A.card ≤ chainBound A σ := by
  have h := maxSection_prefixSet_le A σ 0 n (Nat.zero_le n) le_rfl
  rwa [prefixSet_zero, prefixSet_of_le σ le_rfl, Finset.sdiff_empty, maxSection_empty,
    projCard_univ, segmentBound_zero_n] at h

/-- `m_A(∅ | I) = 1` for a non-empty `A`: the section over no coordinates of a point of the
projection is a single point.  SUV Section 10.2, p. 319. -/
private theorem maxSection_empty_left (A : Finset (∀ i, X i)) (hA : A.Nonempty)
    (I : Finset (Fin n)) : maxSection A ∅ I = 1 := by
  refine le_antisymm (maxSection_empty_left_le A I) ?_
  obtain ⟨a, ha⟩ := hA
  have h1 : 1 ≤ (sectionOver A ∅ I (restrictTo I a)).card :=
    Finset.card_pos.2 ⟨restrictTo ∅ a,
      Finset.mem_image.2 ⟨a, Finset.mem_filter.2 ⟨ha, rfl⟩, rfl⟩⟩
  exact h1.trans (Finset.le_sup (f := fun p => (sectionOver A ∅ I p).card) (Finset.mem_univ _))

/-- If the two-step section inequality is an equality for all disjoint triples, every grouping
of a chain is an equality.  SUV Section 10.2, p. 320. -/
private theorem maxSection_prefixSet_eq (A : Finset (∀ i, X i)) (hA : A.Nonempty)
    (σ : Equiv.Perm (Fin n))
    (h : ∀ I J K : Finset (Fin n), Disjoint I J → Disjoint I K → Disjoint J K →
      maxSection A (J ∪ K) I = maxSection A J I * maxSection A K (I ∪ J))
    (k : ℕ) : ∀ l, k ≤ l → l ≤ n →
      maxSection A (prefixSet σ l \ prefixSet σ k) (prefixSet σ k) = segmentBound A σ k l := by
  intro l
  induction l with
  | zero =>
    intro hk _
    obtain rfl : k = 0 := by omega
    rw [Finset.sdiff_self, segmentBound_self, maxSection_empty_left A hA]
  | succ l ih =>
    intro hk hl
    rcases Nat.eq_or_lt_of_le hk with hk' | hk'
    · rw [← hk', Finset.sdiff_self, segmentBound_self, maxSection_empty_left A hA]
    have hkl : k ≤ l := Nat.lt_succ_iff.1 hk'
    have hln : l < n := hl
    rw [prefixSet_succ_sdiff σ hkl hln, segmentBound_succ A σ hkl hln,
      h _ _ _ Finset.disjoint_sdiff (disjoint_prefixSet_singleton σ hkl hln)
        (disjoint_sdiff_prefixSet_singleton σ hln),
      Finset.union_sdiff_of_subset (prefixSet_mono σ hkl), ih hkl hln.le]

/-- The rank of a coordinate: `0` on `I`, `1` on `J`, `2` on `K` and `3` elsewhere.  Sorting
the coordinates by rank lists `I` first, then `J`, then `K`. -/
private def rankOf (I J K : Finset (Fin n)) (i : Fin n) : ℕ :=
  if i ∈ I then 0 else if i ∈ J then 1 else if i ∈ K then 2 else 3

private theorem filter_rankOf_le_zero (I J K : Finset (Fin n)) :
    (Finset.univ.filter fun i => rankOf I J K i ≤ 0) = I := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hi : i ∈ I <;> by_cases hj : i ∈ J <;> by_cases hk : i ∈ K <;>
    simp [rankOf, hi, hj, hk]

private theorem filter_rankOf_le_one (I J K : Finset (Fin n)) :
    (Finset.univ.filter fun i => rankOf I J K i ≤ 1) = I ∪ J := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hi : i ∈ I
  · simp [rankOf, hi]
  · by_cases hj : i ∈ J
    · simp [rankOf, hi, hj]
    · by_cases hk : i ∈ K <;> simp [rankOf, hi, hj, hk]

private theorem filter_rankOf_le_two (I J K : Finset (Fin n)) :
    (Finset.univ.filter fun i => rankOf I J K i ≤ 2) = I ∪ J ∪ K := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hi : i ∈ I <;> by_cases hj : i ∈ J <;> by_cases hk : i ∈ K <;>
    simp [rankOf, hi, hj, hk]

/-- If the ordering `σ` sorts the coordinates by a rank `r`, the coordinates of rank at most
`t` are exactly the ones listed first, i.e. a prefix of the ordering. -/
private theorem prefixSet_eq_of_monotone (σ : Equiv.Perm (Fin n)) {r : Fin n → ℕ}
    (hmono : Monotone (r ∘ σ)) (t : ℕ) :
    prefixSet σ (Finset.univ.filter fun i => r i ≤ t).card
      = Finset.univ.filter fun i => r i ≤ t := by
  have hcard : (Finset.univ.filter fun j : Fin n => r (σ j) ≤ t).card
      = (Finset.univ.filter fun i => r i ≤ t).card :=
    Finset.card_equiv σ fun j => by simp
  ext i
  rw [mem_prefixSet, Finset.mem_filter, ← hcard]
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

/-- **Problem 285.**  A set is uniform if and only if the two-step section inequality is an
equality for all pairwise disjoint index sets: `m(J ∪ K | I) = m(J | I) · m(K | I ∪ J)`.  One
direction groups the factors of a chain through the triple `I, J, K`; the other observes that
if a whole chain is an equality then every grouping step is.

`A` is non-empty, as everywhere in Section 10.2 (the standing assumption of p. 318): the
empty set satisfies every section equation, but `IsUniform ∅` is false for `n = 0`, where the
empty product on the right of the chain inequality is `1` and `|A|` is `0`.
SUV Problem 285, p. 320. -/
theorem isUniform_iff_maxSection_union_eq (A : Finset (∀ i, X i)) (hA : A.Nonempty) :
    IsUniform A ↔ ∀ I J K : Finset (Fin n), Disjoint I J → Disjoint I K → Disjoint J K →
      maxSection A (J ∪ K) I = maxSection A J I * maxSection A K (I ∪ J) := by
  constructor
  · intro hU I J K hIJ hIK hJK
    set σ := Tuple.sort (rankOf I J K) with hσ
    have hT := prefixSet_eq_of_monotone σ (Tuple.monotone_sort (rankOf I J K))
    have hpa : prefixSet σ I.card = I := by
      have := hT 0
      rwa [filter_rankOf_le_zero] at this
    have hpb : prefixSet σ (I ∪ J).card = I ∪ J := by
      have := hT 1
      rwa [filter_rankOf_le_one] at this
    have hpc : prefixSet σ (I ∪ J ∪ K).card = I ∪ J ∪ K := by
      have := hT 2
      rwa [filter_rankOf_le_two] at this
    have hab : I.card ≤ (I ∪ J).card := Finset.card_le_card Finset.subset_union_left
    have hbc : (I ∪ J).card ≤ (I ∪ J ∪ K).card := Finset.card_le_card Finset.subset_union_left
    have hcn : (I ∪ J ∪ K).card ≤ n :=
      (Finset.card_le_card (Finset.subset_univ _)).trans_eq (by simp)
    have hIJK : Disjoint (I ∪ J) K := Finset.disjoint_union_left.2 ⟨hIK, hJK⟩
    -- the four grouped segments of the chain
    have s1 : maxSection A I ∅ ≤ segmentBound A σ 0 I.card := by
      have := maxSection_prefixSet_le A σ 0 I.card (Nat.zero_le _) (hab.trans (hbc.trans hcn))
      rwa [prefixSet_zero, hpa, Finset.sdiff_empty] at this
    have s2 : maxSection A J I ≤ segmentBound A σ I.card (I ∪ J).card := by
      have := maxSection_prefixSet_le A σ I.card (I ∪ J).card hab (hbc.trans hcn)
      rwa [hpa, hpb, Finset.union_sdiff_cancel_left hIJ] at this
    have s3 : maxSection A K (I ∪ J) ≤ segmentBound A σ (I ∪ J).card (I ∪ J ∪ K).card := by
      have := maxSection_prefixSet_le A σ (I ∪ J).card (I ∪ J ∪ K).card hbc hcn
      rwa [hpb, hpc, Finset.union_sdiff_cancel_left hIJK] at this
    have s4 : maxSection A (univ \ (I ∪ J ∪ K)) (I ∪ J ∪ K)
        ≤ segmentBound A σ (I ∪ J ∪ K).card n := by
      have := maxSection_prefixSet_le A σ (I ∪ J ∪ K).card n hcn le_rfl
      rwa [hpc, prefixSet_of_le σ le_rfl] at this
    have hprod : segmentBound A σ 0 I.card * (segmentBound A σ I.card (I ∪ J).card
        * segmentBound A σ (I ∪ J).card (I ∪ J ∪ K).card)
        * segmentBound A σ (I ∪ J ∪ K).card n = A.card := by
      rw [segmentBound_mul A σ hab hbc, segmentBound_mul A σ (Nat.zero_le _) (hab.trans hbc),
        segmentBound_mul A σ (Nat.zero_le _) hcn, segmentBound_zero_n, hU σ]
    -- the chain through `I`, `J ∪ K` and the remaining coordinates
    have hcard : A.card = maxSection A (I ∪ J ∪ K ∪ univ \ (I ∪ J ∪ K)) ∅ := by
      rw [Finset.union_sdiff_of_subset (Finset.subset_univ _), maxSection_empty, projCard_univ]
    have t1 := maxSection_union_le A ∅ (I ∪ J ∪ K) (univ \ (I ∪ J ∪ K))
      (Finset.disjoint_empty_left _) (Finset.disjoint_empty_left _) Finset.disjoint_sdiff
    have t2 := maxSection_union_le A ∅ I (J ∪ K) (Finset.disjoint_empty_left _)
      (Finset.disjoint_empty_left _) (Finset.disjoint_union_right.2 ⟨hIJ, hIK⟩)
    have t3 := maxSection_union_le A I J K hIJ hIK hJK
    rw [Finset.empty_union] at t1
    rw [Finset.empty_union, ← Finset.union_assoc] at t2
    have hchain : A.card ≤ maxSection A I ∅ * maxSection A (J ∪ K) I
        * maxSection A (univ \ (I ∪ J ∪ K)) (I ∪ J ∪ K) := by
      rw [hcard]
      exact t1.trans (Nat.mul_le_mul_right _ t2)
    have hmid : maxSection A I ∅ * maxSection A (J ∪ K) I
        * maxSection A (univ \ (I ∪ J ∪ K)) (I ∪ J ∪ K)
        ≤ maxSection A I ∅ * (maxSection A J I * maxSection A K (I ∪ J))
          * maxSection A (univ \ (I ∪ J ∪ K)) (I ∪ J ∪ K) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ t3)
    have hup : maxSection A I ∅ * (maxSection A J I * maxSection A K (I ∪ J))
        * maxSection A (univ \ (I ∪ J ∪ K)) (I ∪ J ∪ K) ≤ A.card := by
      rw [← hprod]
      exact Nat.mul_le_mul (Nat.mul_le_mul s1 (Nat.mul_le_mul s2 s3)) s4
    have heq : maxSection A I ∅ * maxSection A (J ∪ K) I
        * maxSection A (univ \ (I ∪ J ∪ K)) (I ∪ J ∪ K)
        = maxSection A I ∅ * (maxSection A J I * maxSection A K (I ∪ J))
          * maxSection A (univ \ (I ∪ J ∪ K)) (I ∪ J ∪ K) :=
      le_antisymm hmid (hup.trans hchain)
    have hA0 : 0 < A.card := Finset.card_pos.2 hA
    have hmI : 0 < maxSection A I ∅ := by
      rcases Nat.eq_zero_or_pos (maxSection A I ∅) with h0 | h0
      · rw [h0, zero_mul, zero_mul] at hchain
        omega
      · exact h0
    have hmR : 0 < maxSection A (univ \ (I ∪ J ∪ K)) (I ∪ J ∪ K) := by
      rcases Nat.eq_zero_or_pos (maxSection A (univ \ (I ∪ J ∪ K)) (I ∪ J ∪ K)) with h0 | h0
      · rw [h0, mul_zero] at hchain
        omega
      · exact h0
    exact Nat.eq_of_mul_eq_mul_left hmI (Nat.eq_of_mul_eq_mul_right hmR heq)
  · intro h σ
    have := maxSection_prefixSet_eq A hA σ h 0 n (Nat.zero_le n) le_rfl
    rw [prefixSet_zero, prefixSet_of_le σ le_rfl, Finset.sdiff_empty, maxSection_empty,
      projCard_univ, segmentBound_zero_n] at this
    exact this.symm

/-- The maximal section sizes of the projection onto the coordinates listed by an injection
`e` are the maximal section sizes of the set itself over the corresponding coordinates:
`m_{A ∘ e}(J' | I') = m_A(e(J') | e(I'))`. -/
private theorem maxSection_image_comp {m : ℕ} (A : Finset (∀ i, X i)) (e : Fin m → Fin n)
    (he : Function.Injective e) (J' I' : Finset (Fin m)) :
    maxSection (A.image fun a (j : Fin m) => a (e j)) J' I'
      = maxSection A (J'.map ⟨e, he⟩) (I'.map ⟨e, he⟩) := by
  set π : (∀ i, X i) → ∀ j : Fin m, X (e j) := fun a j => a (e j) with hπ
  set ρ : ((i : (J'.map ⟨e, he⟩ : Finset (Fin n))) → X i.val) → (j : J') → X (e j.val) :=
    fun q j => q ⟨e j.val, Finset.mem_map_of_mem _ j.2⟩ with hρ
  have hρinj : Function.Injective ρ := by
    intro q₁ q₂ h
    funext i
    obtain ⟨j, hj, hji⟩ := Finset.mem_map.1 i.2
    have := congrFun h ⟨j, hj⟩
    simp only [hρ] at this
    have hi : i = ⟨e j, Finset.mem_map_of_mem _ hj⟩ := Subtype.ext hji.symm
    rw [hi]
    exact this
  rw [maxSection_eq_sup_proj, maxSection_eq_sup_proj, proj, proj, Finset.image_image,
    Finset.sup_image, Finset.sup_image]
  refine Finset.sup_congr rfl fun a _ => ?_
  simp only [Function.comp]
  have hfil : (A.image π).filter (fun b => restrictTo I' b = restrictTo I' (π a))
      = (A.filter fun a' => restrictTo (I'.map ⟨e, he⟩) a'
          = restrictTo (I'.map ⟨e, he⟩) a).image π := by
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

/-- **Problem 286.**  A projection of a uniform set is uniform.  The projection onto the
coordinates listed by an injection `e : Fin m → Fin n` is the image of `A` under
`a ↦ (j ↦ a (e j))`, a subset of the product of the corresponding coordinate sets.

`A` is non-empty, as everywhere in Section 10.2 (the standing assumption of p. 318): without
it the empty subset of a one-coordinate product would be uniform while its projection onto no
coordinate — the empty subset of a zero-coordinate product — is not.
SUV Problem 286, p. 320. -/
theorem isUniform_image_of_injective {m : ℕ} (A : Finset (∀ i, X i)) (hAne : A.Nonempty)
    (hA : IsUniform A) (e : Fin m → Fin n) (he : Function.Injective e) :
    IsUniform (A.image fun a (j : Fin m) => a (e j)) := by
  rw [isUniform_iff_maxSection_union_eq _ (hAne.image _)]
  intro I' J' K' hIJ hIK hJK
  rw [maxSection_image_comp A e he, maxSection_image_comp A e he, maxSection_image_comp A e he,
    Finset.map_union, Finset.map_union]
  exact (isUniform_iff_maxSection_union_eq A hAne).1 hA _ _ _ ((Finset.disjoint_map _).2 hIJ)
    ((Finset.disjoint_map _).2 hIK) ((Finset.disjoint_map _).2 hJK)

omit [∀ i, Fintype (X i)] in
/-- Fixing the `I ∪ J`-coordinates to those of `a₀` is fixing the `I`-coordinates and the
`J`-coordinates separately. -/
private theorem filter_restrictTo_union_eq (A : Finset (∀ i, X i)) (I J : Finset (Fin n))
    (a₀ : ∀ i, X i) :
    (A.filter fun a => restrictTo (I ∪ J) a = restrictTo (I ∪ J) a₀)
      = A.filter fun a =>
          restrictTo I a = restrictTo I a₀ ∧ restrictTo J a = restrictTo J a₀ := by
  ext a
  simp only [Finset.mem_filter, and_congr_right_iff]
  intro _
  constructor
  · intro h
    exact ⟨funext fun i => congrFun h ⟨i.1, Finset.mem_union_left J i.2⟩,
      funext fun i => congrFun h ⟨i.1, Finset.mem_union_right I i.2⟩⟩
  · rintro ⟨hI, hJ⟩
    funext i
    rcases Finset.mem_union.1 i.2 with hi | hi
    · exact congrFun hI ⟨i.1, hi⟩
    · exact congrFun hJ ⟨i.1, hi⟩

omit [∀ i, Fintype (X i)] in
/-- The points of `A` with `I`-coordinates `p`, counted according to their `J`-coordinates:
one fiber for each point of the `J`-section over `p`. -/
private theorem card_filter_restrictTo_eq_sum (A : Finset (∀ i, X i)) (I J : Finset (Fin n))
    (p : (i : I) → X i.val) :
    (A.filter fun a => restrictTo I a = p).card
      = ∑ s ∈ sectionOver A J I p,
          (A.filter fun a => restrictTo I a = p ∧ restrictTo J a = s).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := restrictTo J) (t := sectionOver A J I p)
    fun a ha => by rw [sectionOver]; exact Finset.mem_image_of_mem _ ha]
  exact Finset.sum_congr rfl fun s _ => by rw [Finset.filter_filter]

omit [∀ i, Fintype (X i)] in
/-- The points of `A` with `I`-coordinates `p` are counted by their remaining coordinates:
`|{a ∈ A : a_I = p}|` is the size of the section over `p` of the coordinates outside `I`. -/
private theorem card_filter_restrictTo_eq (A : Finset (∀ i, X i)) (I : Finset (Fin n))
    (p : (i : I) → X i.val) :
    (A.filter fun a => restrictTo I a = p).card = (sectionOver A (univ \ I) I p).card := by
  rw [sectionOver, Finset.card_image_of_injOn]
  intro a ha b hb h
  simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ha hb
  funext i
  by_cases hi : i ∈ I
  · exact (congrFun ha.2 ⟨i, hi⟩).trans (congrFun hb.2 ⟨i, hi⟩).symm
  · exact congrFun h ⟨i, Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hi⟩⟩

/-- `|A| = m_A(I) · m_A(Iᶜ | I)` for a non-empty uniform set: the section equation of
Problem 285 with `∅, I, Iᶜ`.  SUV Theorem 205, p. 321 (the proof). -/
private theorem card_eq_projCard_mul_maxSection_of_isUniform (A : Finset (∀ i, X i))
    (hA : A.Nonempty) (hU : IsUniform A) (I : Finset (Fin n)) :
    A.card = projCard A I * maxSection A (univ \ I) I := by
  have h := (isUniform_iff_maxSection_union_eq A hA).1 hU ∅ I (univ \ I)
    (Finset.disjoint_empty_left _) (Finset.disjoint_empty_left _) Finset.disjoint_sdiff
  rwa [Finset.union_sdiff_of_subset (Finset.subset_univ _), maxSection_empty, maxSection_empty,
    projCard_univ, Finset.empty_union] at h

/-- In a non-empty uniform set every non-empty section over `I` has the maximal size
`m_A(Iᶜ | I)`: the average size `|A| / m_A(I)` of the non-empty sections equals the maximal
size, so all of them are maximal.  SUV Theorem 205, p. 321 (the proof). -/
private theorem card_sectionOver_of_isUniform (A : Finset (∀ i, X i)) (hA : A.Nonempty)
    (hU : IsUniform A) (I : Finset (Fin n)) {p : (i : I) → X i.val} (hp : p ∈ proj A I) :
    (sectionOver A (univ \ I) I p).card = maxSection A (univ \ I) I := by
  have hsum : ∑ q ∈ proj A I, (sectionOver A (univ \ I) I q).card = A.card := by
    rw [proj, Finset.card_eq_sum_card_image (restrictTo I) A]
    exact Finset.sum_congr rfl fun q _ => (card_filter_restrictTo_eq A I q).symm
  have hle : ∀ q ∈ proj A I,
      (sectionOver A (univ \ I) I q).card ≤ maxSection A (univ \ I) I := fun q _ =>
    Finset.le_sup (f := fun q => (sectionOver A (univ \ I) I q).card) (Finset.mem_univ q)
  have hsum' : ∑ q ∈ proj A I, (sectionOver A (univ \ I) I q).card
      = ∑ _q ∈ proj A I, maxSection A (univ \ I) I := by
    rw [hsum, Finset.sum_const, smul_eq_mul,
      card_eq_projCard_mul_maxSection_of_isUniform A hA hU I, projCard]
  exact (Finset.sum_eq_sum_iff_of_le hle).1 hsum' p hp

/-- `1 ≤ m_A(J | I)` for a non-empty `A`: the section over the `I`-coordinates of any point
of `A` contains its `J`-coordinates. -/
private theorem one_le_maxSection (A : Finset (∀ i, X i)) (hA : A.Nonempty)
    (J I : Finset (Fin n)) : 1 ≤ maxSection A J I := by
  obtain ⟨a, ha⟩ := hA
  have h1 : 1 ≤ (sectionOver A J I (restrictTo I a)).card :=
    Finset.card_pos.2 ⟨restrictTo J a,
      Finset.mem_image.2 ⟨a, Finset.mem_filter.2 ⟨ha, rfl⟩, rfl⟩⟩
  exact h1.trans (Finset.le_sup (f := fun p => (sectionOver A J I p).card) (Finset.mem_univ _))

/-- In a non-empty uniform set every non-empty `J`-section over `I` (with `I, J` disjoint) has
the maximal size `m_A(J | I)`: the section over `p` of the remaining coordinates has the
maximal size `m(J | I) · m(K | I ∪ J)` with `K` the rest, and splits into at most
`m(K | I ∪ J)` points for each point of the `J`-section over `p`.
SUV Problem 287, p. 320 (the proof). -/
private theorem card_sectionOver_eq_maxSection_of_isUniform (A : Finset (∀ i, X i))
    (hA : A.Nonempty) (hU : IsUniform A) {I J : Finset (Fin n)} (hIJ : Disjoint I J)
    {p : (i : I) → X i.val} (hp : p ∈ proj A I) :
    (sectionOver A J I p).card = maxSection A J I := by
  have hJK : J ∪ univ \ (I ∪ J) = univ \ I := by
    ext i
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and]
    constructor
    · rintro (h | h)
      · exact Finset.disjoint_right.1 hIJ h
      · exact fun hi => h (Or.inl hi)
    · intro h
      by_cases hj : i ∈ J
      · exact Or.inl hj
      · exact Or.inr fun hi => hi.elim h hj
  have h285 := (isUniform_iff_maxSection_union_eq A hA).1 hU I J (univ \ (I ∪ J)) hIJ
    (Finset.disjoint_of_subset_left Finset.subset_union_left Finset.disjoint_sdiff)
    (Finset.disjoint_of_subset_left Finset.subset_union_right Finset.disjoint_sdiff)
  have hle : (sectionOver A J I p).card ≤ maxSection A J I :=
    Finset.le_sup (f := fun q => (sectionOver A J I q).card) (Finset.mem_univ _)
  have hmK : 0 < maxSection A (univ \ (I ∪ J)) (I ∪ J) := one_le_maxSection A hA _ _
  refine le_antisymm hle (Nat.le_of_mul_le_mul_right ?_ hmK)
  have hterm : ∀ s ∈ sectionOver A J I p,
      (A.filter fun a => restrictTo I a = p ∧ restrictTo J a = s).card
        ≤ maxSection A (univ \ (I ∪ J)) (I ∪ J) := by
    intro s hs
    obtain ⟨a₁, ha₁, rfl⟩ := Finset.mem_image.1 hs
    have ha₁' := Finset.mem_filter.1 ha₁
    rw [← ha₁'.2, ← filter_restrictTo_union_eq, card_filter_restrictTo_eq]
    exact Finset.le_sup (f := fun q => (sectionOver A (univ \ (I ∪ J)) (I ∪ J) q).card)
      (Finset.mem_univ _)
  calc maxSection A J I * maxSection A (univ \ (I ∪ J)) (I ∪ J)
      = maxSection A (J ∪ univ \ (I ∪ J)) I := h285.symm
    _ = maxSection A (univ \ I) I := by rw [hJK]
    _ = (sectionOver A (univ \ I) I p).card := (card_sectionOver_of_isUniform A hA hU I hp).symm
    _ = (A.filter fun a => restrictTo I a = p).card := (card_filter_restrictTo_eq A I p).symm
    _ = ∑ s ∈ sectionOver A J I p,
          (A.filter fun a => restrictTo I a = p ∧ restrictTo J a = s).card :=
        card_filter_restrictTo_eq_sum A I J p
    _ ≤ ∑ _s ∈ sectionOver A J I p, maxSection A (univ \ (I ∪ J)) (I ∪ J) :=
        Finset.sum_le_sum hterm
    _ = (sectionOver A J I p).card * maxSection A (univ \ (I ∪ J)) (I ∪ J) := by
        rw [Finset.sum_const, smul_eq_mul]

/-- The maximal section sizes of a non-empty section `{a ∈ A : a_I = p}` of a uniform set are
those of `A` with the fixed coordinates added to the condition:
`m_{A_p}(J | I') = m_A(J | I ∪ I')` for `J` disjoint from `I ∪ I'`.  Every section of `A_p`
over `I'` is a section of `A` over `I ∪ I'`, and in a uniform set all non-empty sections are
maximal.  SUV Problem 287, p. 320 (the proof). -/
private theorem maxSection_filter_restrictTo_eq (A : Finset (∀ i, X i)) (hU : IsUniform A)
    (I : Finset (Fin n)) (p : (i : I) → X i.val)
    (hp : (A.filter fun a => restrictTo I a = p).Nonempty) {I' J : Finset (Fin n)}
    (hIJ : Disjoint (I ∪ I') J) :
    maxSection (A.filter fun a => restrictTo I a = p) J I' = maxSection A J (I ∪ I') := by
  have hA : A.Nonempty := ⟨hp.choose, (Finset.mem_filter.1 hp.choose_spec).1⟩
  have hsec : ∀ a₀ ∈ A.filter (fun a => restrictTo I a = p),
      sectionOver (A.filter fun a => restrictTo I a = p) J I' (restrictTo I' a₀)
        = sectionOver A J (I ∪ I') (restrictTo (I ∪ I') a₀) := by
    intro a₀ ha₀
    have ha₀' := Finset.mem_filter.1 ha₀
    rw [sectionOver, sectionOver, Finset.filter_filter, filter_restrictTo_union_eq, ha₀'.2]
  apply le_antisymm
  · refine Finset.sup_le fun q _ => ?_
    by_cases hq : (sectionOver (A.filter fun a => restrictTo I a = p) J I' q).Nonempty
    · obtain ⟨s, hs⟩ := hq
      obtain ⟨a₀, ha₀, rfl⟩ := Finset.mem_image.1 hs
      have ha₀' := Finset.mem_filter.1 ha₀
      rw [← ha₀'.2, hsec a₀ ha₀'.1]
      exact Finset.le_sup (f := fun r => (sectionOver A J (I ∪ I') r).card) (Finset.mem_univ _)
    · rw [Finset.not_nonempty_iff_eq_empty.1 hq, Finset.card_empty]
      exact Nat.zero_le _
  · obtain ⟨a₀, ha₀⟩ := hp
    have hmem : restrictTo (I ∪ I') a₀ ∈ proj A (I ∪ I') :=
      Finset.mem_image_of_mem _ (Finset.mem_filter.1 ha₀).1
    rw [← card_sectionOver_eq_maxSection_of_isUniform A hA hU hIJ hmem, ← hsec a₀ ha₀]
    exact Finset.le_sup
      (f := fun q => (sectionOver (A.filter fun a => restrictTo I a = p) J I' q).card)
      (Finset.mem_univ _)

/-- **Problem 287.**  A section of a uniform set is uniform: fix the coordinates in `I` to a
value `p` that occurs in `A`, and take the coordinates listed by an injection `e` avoiding `I`;
the resulting set is uniform.  The book fixes "some coordinate"; the statement below allows an
arbitrary set of fixed coordinates, which is the same result.
SUV Problem 287, p. 320. -/
theorem isUniform_section {m : ℕ} (A : Finset (∀ i, X i)) (hA : IsUniform A)
    (I : Finset (Fin n)) (p : (i : I) → X i.val)
    (hp : (A.filter fun a => restrictTo I a = p).Nonempty)
    (e : Fin m → Fin n) (he : Function.Injective e) (heI : ∀ j, e j ∉ I) :
    IsUniform ((A.filter fun a => restrictTo I a = p).image fun a (j : Fin m) => a (e j)) := by
  have hAne : A.Nonempty := ⟨hp.choose, (Finset.mem_filter.1 hp.choose_spec).1⟩
  rw [isUniform_iff_maxSection_union_eq _ (hp.image _)]
  intro I' J' K' hIJ hIK hJK
  have hdisj : ∀ S : Finset (Fin m), Disjoint I (S.map ⟨e, he⟩) := fun S =>
    Finset.disjoint_right.2 fun i hi => by
      obtain ⟨j, _, rfl⟩ := Finset.mem_map.1 hi
      exact heI j
  have hIJ' : Disjoint (I ∪ I'.map ⟨e, he⟩) (J'.map ⟨e, he⟩) :=
    Finset.disjoint_union_left.2 ⟨hdisj _, (Finset.disjoint_map _).2 hIJ⟩
  have hIK' : Disjoint (I ∪ I'.map ⟨e, he⟩) (K'.map ⟨e, he⟩) :=
    Finset.disjoint_union_left.2 ⟨hdisj _, (Finset.disjoint_map _).2 hIK⟩
  have hJK' : Disjoint (J'.map ⟨e, he⟩) (K'.map ⟨e, he⟩) := (Finset.disjoint_map _).2 hJK
  have hIJK' : Disjoint (I ∪ (I'.map ⟨e, he⟩ ∪ J'.map ⟨e, he⟩)) (K'.map ⟨e, he⟩) := by
    rw [← Finset.union_assoc]
    exact Finset.disjoint_union_left.2 ⟨hIK', hJK'⟩
  rw [maxSection_image_comp _ e he, maxSection_image_comp _ e he, maxSection_image_comp _ e he,
    Finset.map_union, Finset.map_union,
    maxSection_filter_restrictTo_eq A hA I p hp (Finset.disjoint_union_right.2 ⟨hIJ', hIK'⟩),
    maxSection_filter_restrictTo_eq A hA I p hp hIJ',
    maxSection_filter_restrictTo_eq A hA I p hp hIJK', ← Finset.union_assoc]
  exact (isUniform_iff_maxSection_union_eq A hAne).1 hA _ _ _ hIJ' hIK' hJK'

end Chain

/-! ### Theorem 205 and its corollary -/

/-- The entropy of a uniformly distributed random variable is the log-size of its range:
`H(ξ) = log₂ |range ξ|`.  SUV Section 7.1, p. 215. -/
private theorem entropy_eq_logb_card_of_isUniformlyDistributed {Ω : Type} [Fintype Ω]
    {β : Type} [DecidableEq β] (μ : FiniteProbSpace Ω) (X : Ω → β)
    (h : IsUniformlyDistributed μ X) :
    entropy μ X = Real.logb 2 (rangeFinset X).card := by
  have hne : (rangeFinset X).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have := μ.sum_dist_eq_one X
    rw [hempty, Finset.sum_empty] at this
    exact zero_ne_one this
  have hN : ((rangeFinset X).card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_pos.2 hne).ne'
  have hlog2 : Real.log 2 ≠ 0 := by positivity
  rw [entropy, Finset.sum_congr rfl fun a ha => by rw [h a ha], Finset.sum_const, nsmul_eq_mul]
  simp only [negMulLog2, Real.negMulLog, Real.log_inv, Real.logb]
  field_simp

section Distribution

variable {X : Fin n → Type} [∀ i, DecidableEq (X i)]

/-- The range of the `I`-coordinates of a uniformly random point of `A` is the projection of
`A` onto `I`.  For `X = fun _ => α` this random variable is the subtuple `ξ_I` of
`uniformCoords A`. -/
private theorem rangeFinset_restrictTo_val (A : Finset (∀ i, X i)) (I : Finset (Fin n)) :
    rangeFinset (fun ω : {a // a ∈ A} => restrictTo I ω.val) = proj A I := by
  ext q
  simp only [rangeFinset, proj, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨ω, rfl⟩
    exact ⟨ω.val, ω.2, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩

/-- The probability that a uniformly random point of `A` has `I`-coordinates `q` is
`|{a ∈ A : a_I = q}| / |A|`. -/
private theorem dist_restrictTo_uniformProbOn (A : Finset (∀ i, X i)) (hA : A.Nonempty)
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

/-- Uniform distribution of the `K`-coordinates of a random point of `A` on their range means
that every non-empty section over `K` holds `|A| / m_A(K)` points:
`|{a ∈ A : a_K = q}| · m_A(K) = |A|`. -/
private theorem card_filter_mul_projCard_of_isUniformlyDistributed (A : Finset (∀ i, X i))
    (hA : A.Nonempty) (K : Finset (Fin n))
    (h : IsUniformlyDistributed (uniformProbOn A hA)
      fun ω : {a // a ∈ A} => restrictTo K ω.val)
    {q : (i : K) → X i.val} (hq : q ∈ proj A K) :
    (A.filter fun a => restrictTo K a = q).card * projCard A K = A.card := by
  have hd := h q (by rwa [rangeFinset_restrictTo_val])
  rw [dist_restrictTo_uniformProbOn, rangeFinset_restrictTo_val] at hd
  have hA0 : (A.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_pos.2 hA).ne'
  have hP : ((proj A K).card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.2 ⟨q, hq⟩).ne'
  have key : ((A.filter fun a => restrictTo K a = q).card : ℝ) * (proj A K).card = A.card := by
    field_simp at hd
    linarith
  rw [projCard]
  exact_mod_cast key

/-- If the `I`-coordinates and the `I ∪ J`-coordinates of a uniformly random point of `A` are
both uniformly distributed on their ranges, every non-empty `J`-section over `I` has the size
`m_A(I ∪ J) / m_A(I)`: `|A_J(p)| · m_A(I) = m_A(I ∪ J)`.  Count the points with
`I`-coordinates `p` fiberwise over the section.  SUV Theorem 205, p. 321 (the proof). -/
private theorem card_sectionOver_mul_projCard (A : Finset (∀ i, X i)) (hA : A.Nonempty)
    (I J : Finset (Fin n))
    (hI : IsUniformlyDistributed (uniformProbOn A hA)
      fun ω : {a // a ∈ A} => restrictTo I ω.val)
    (hIJ : IsUniformlyDistributed (uniformProbOn A hA)
      fun ω : {a // a ∈ A} => restrictTo (I ∪ J) ω.val)
    {p : (i : I) → X i.val} (hp : p ∈ proj A I) :
    (sectionOver A J I p).card * projCard A I = projCard A (I ∪ J) := by
  have hN := card_filter_mul_projCard_of_isUniformlyDistributed A hA I hI hp
  have hsum := card_filter_restrictTo_eq_sum A I J p
  have hterm : ∀ s ∈ sectionOver A J I p,
      (A.filter fun a => restrictTo I a = p ∧ restrictTo J a = s).card * projCard A (I ∪ J)
        = A.card := by
    intro s hs
    obtain ⟨a₁, ha₁, rfl⟩ := Finset.mem_image.1 hs
    have ha₁' := Finset.mem_filter.1 ha₁
    rw [← ha₁'.2, ← filter_restrictTo_union_eq]
    exact card_filter_mul_projCard_of_isUniformlyDistributed A hA (I ∪ J) hIJ
      (Finset.mem_image_of_mem _ ha₁'.1)
  have hsum' : (A.filter fun a => restrictTo I a = p).card * projCard A (I ∪ J)
      = (sectionOver A J I p).card * A.card := by
    rw [hsum, Finset.sum_mul, Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul]
  have hpos : 0 < A.card := Finset.card_pos.2 hA
  refine Nat.eq_of_mul_eq_mul_left hpos ?_
  calc A.card * ((sectionOver A J I p).card * projCard A I)
      = (sectionOver A J I p).card * A.card * projCard A I := by ring
    _ = (A.filter fun a => restrictTo I a = p).card * projCard A (I ∪ J) * projCard A I := by
        rw [hsum']
    _ = (A.filter fun a => restrictTo I a = p).card * projCard A I * projCard A (I ∪ J) := by
        ring
    _ = A.card * projCard A (I ∪ J) := by rw [hN]

variable [∀ i, Fintype (X i)]

/-- The forward half of Theorem 205: in a uniform set the `I`-coordinates of a uniformly
random point are uniformly distributed on their range, because every non-empty section has
the same size `m_A(Iᶜ | I)`.  SUV Theorem 205, p. 321. -/
private theorem isUniformlyDistributed_restrictTo_of_isUniform (A : Finset (∀ i, X i))
    (hA : A.Nonempty) (hU : IsUniform A) (I : Finset (Fin n)) :
    IsUniformlyDistributed (uniformProbOn A hA)
      (fun ω : {a // a ∈ A} => restrictTo I ω.val) := by
  intro q hq
  rw [rangeFinset_restrictTo_val] at hq ⊢
  have hA0 : A.card = projCard A I * maxSection A (univ \ I) I :=
    card_eq_projCard_mul_maxSection_of_isUniform A hA hU I
  have hpos : 0 < A.card := Finset.card_pos.2 hA
  have hP : (projCard A I : ℝ) ≠ 0 := by
    have : projCard A I ≠ 0 := fun h => by rw [hA0, h, zero_mul] at hpos; omega
    exact_mod_cast this
  have hM : (maxSection A (univ \ I) I : ℝ) ≠ 0 := by
    have : maxSection A (univ \ I) I ≠ 0 := fun h => by rw [hA0, h, mul_zero] at hpos; omega
    exact_mod_cast this
  have h1 : (A.filter fun a => restrictTo I a = q).card = maxSection A (univ \ I) I :=
    (card_filter_restrictTo_eq A I q).trans (card_sectionOver_of_isUniform A hA hU I hq)
  rw [dist_restrictTo_uniformProbOn, h1, hA0]
  change _ = ((projCard A I : ℕ) : ℝ)⁻¹
  push_cast
  field_simp

/-- The corollary to Theorem 205 for a set in a dependent product, read through injective
recodings `enc i : X i → ℕ` of the coordinates: the `ℕ`-valued coordinates `enc i (ξ_i)` of a
uniformly random point of the uniform set `A` satisfy `H(ξ_I) = log₂ m_A(I)`, because an
injective recoding preserves entropy.  SUV Corollary to Theorem 205, p. 321. -/
private theorem entropySub_uniformProbOn_enc_eq_logb_projCard (A : Finset (∀ i, X i))
    (hA : A.Nonempty) (hU : IsUniform A) (enc : ∀ i, X i → ℕ)
    (henc : ∀ i, Function.Injective (enc i)) (I : Finset (Fin n)) :
    entropySub (uniformProbOn A hA) (fun i (ω : {a // a ∈ A}) => enc i (ω.val i)) I
      = Real.logb 2 (projCard A I) := by
  set g : ((i : I) → X i.val) → (I → ℕ) := fun q i => enc i.val (q i) with hg
  have hginj : Function.Injective g := by
    intro q₁ q₂ h
    funext i
    exact henc i.val (congrFun h i)
  have hcomp : subtuple (fun i (ω : {a // a ∈ A}) => enc i (ω.val i)) I
      = g ∘ fun ω : {a // a ∈ A} => restrictTo I ω.val := rfl
  rw [entropySub, hcomp, entropy_comp_of_injective _ _ hginj,
    entropy_eq_logb_card_of_isUniformlyDistributed _ _
      (isUniformlyDistributed_restrictTo_of_isUniform A hA hU I),
    rangeFinset_restrictTo_val, projCard]

/-- If every subtuple of a uniformly random point of `A` is uniformly distributed on its
range, then `m_A(J | I) · m_A(I) = m_A(I ∪ J)`: all non-empty `J`-sections over `I` have the
same size, which is therefore the maximal one.  SUV Theorem 205, p. 321 (the proof). -/
private theorem maxSection_mul_projCard_of_uniformlyDistributed (A : Finset (∀ i, X i))
    (hA : A.Nonempty)
    (h : ∀ I : Finset (Fin n), IsUniformlyDistributed (uniformProbOn A hA)
      fun ω : {a // a ∈ A} => restrictTo I ω.val)
    (I J : Finset (Fin n)) : maxSection A J I * projCard A I = projCard A (I ∪ J) := by
  obtain ⟨a₀, ha₀⟩ := id hA
  have hp : restrictTo I a₀ ∈ proj A I := Finset.mem_image_of_mem _ ha₀
  have hPpos : 0 < projCard A I := Finset.card_pos.2 ⟨_, hp⟩
  have hall : ∀ p ∈ proj A I,
      (sectionOver A J I p).card = (sectionOver A J I (restrictTo I a₀)).card := fun p hp' =>
    Nat.eq_of_mul_eq_mul_right hPpos
      ((card_sectionOver_mul_projCard A hA I J (h I) (h (I ∪ J)) hp').trans
        (card_sectionOver_mul_projCard A hA I J (h I) (h (I ∪ J)) hp).symm)
  rw [maxSection_eq_sup_proj, Finset.sup_congr rfl hall, Finset.sup_const ⟨_, hp⟩]
  exact card_sectionOver_mul_projCard A hA I J (h I) (h (I ∪ J)) hp

end Distribution

/-- The backward half of Theorem 205: if every subtuple of a uniformly random point of `A`
is uniformly distributed on its range, then `A` is uniform.  The book's argument is an
induction on `n`: uniformity of `ξ_{1..n-1}` gives `m(1, …, n) = m(n | 1, …, n-1) · m(1, …, n-1)`,
the projection onto the first `n − 1` coordinates inherits the hypothesis, and the same
argument applies to every ordering.  SUV Theorem 205, p. 321. -/
private theorem isUniform_of_uniformlyDistributed {α : Type} [Fintype α] [DecidableEq α]
    (A : Finset (Fin n → α)) (hA : A.Nonempty)
    (h : ∀ I : Finset (Fin n),
      IsUniformlyDistributed (uniformProbOn A hA) (subtuple (uniformCoords A) I)) :
    IsUniform A := by
  rw [isUniform_iff_maxSection_union_eq A hA]
  intro I J K _ _ _
  have hm := maxSection_mul_projCard_of_uniformlyDistributed (X := fun _ => α) A hA h
  have hPpos : 0 < projCard A I := by
    unfold projCard proj
    exact Finset.card_pos.2 (hA.image _)
  refine Nat.eq_of_mul_eq_mul_right hPpos ?_
  calc maxSection A (J ∪ K) I * projCard A I = projCard A (I ∪ (J ∪ K)) := hm I (J ∪ K)
    _ = projCard A (I ∪ J ∪ K) := by rw [Finset.union_assoc]
    _ = maxSection A K (I ∪ J) * projCard A (I ∪ J) := (hm (I ∪ J) K).symm
    _ = maxSection A K (I ∪ J) * (maxSection A J I * projCard A I) := by rw [hm I J]
    _ = maxSection A J I * maxSection A K (I ∪ J) * projCard A I := by ring

/-- **Theorem 205.**  A non-empty finite set `A` is uniform if and only if, for a point
`⟨ξ_1, …, ξ_n⟩` chosen uniformly at random in `A`, every subtuple `ξ_I` is uniformly
distributed on its range (the projection of `A` onto `I`).  The equation
`m(1, …, n) = m(I) · m(J | I)` with `J` the complement of `I` says exactly that the average
size of a non-empty section equals its maximal size, so all sections have the same size.
SUV Theorem 205, p. 321. -/
theorem isUniform_iff_uniformlyDistributed {α : Type} [Fintype α] [DecidableEq α]
    (A : Finset (Fin n → α)) (hA : A.Nonempty) :
    IsUniform A ↔ ∀ I : Finset (Fin n),
      IsUniformlyDistributed (uniformProbOn A hA) (subtuple (uniformCoords A) I) :=
  ⟨fun hU I => isUniformlyDistributed_restrictTo_of_isUniform A hA hU I,
    fun h => isUniform_of_uniformlyDistributed A hA h⟩

/-- **Corollary to Theorem 205.**  For a uniform set `A` and a uniformly random point of `A`,
the entropy of every subtuple is the log-size of the corresponding projection:
`H(ξ_I) = log₂ m_A(I)`.  Entropies here are base two, as everywhere in this library.
SUV Corollary to Theorem 205, p. 321. -/
theorem entropySub_uniformProbOn_eq_logb_projCard {α : Type} [Fintype α] [DecidableEq α]
    (A : Finset (Fin n → α)) (hA : A.Nonempty) (hU : IsUniform A) (I : Finset (Fin n)) :
    entropySub (uniformProbOn A hA) (uniformCoords A) I = Real.logb 2 (projCard A I) := by
  have h := entropy_eq_logb_card_of_isUniformlyDistributed _ _
    (isUniformlyDistributed_restrictTo_of_isUniform A hA hU I)
  rw [rangeFinset_restrictTo_val (X := fun _ => α) A I] at h
  exact h

/-- **Theorem 206.**  Every linear inequality that is true for the entropies of all tuples of
random variables is true for the log-sizes of the projections of every uniform set.  Apply the
entropy inequality to the uniform distribution on `A` and use the corollary to Theorem 205.
SUV Theorem 206, p. 321. -/
theorem holdsForUniformSets_of_holdsForEntropies (f : LinearForm n)
    (h : HoldsForEntropies f) : HoldsForUniformSets f := by
  intro Y _ _ A hA hU
  have henc : ∀ i, Function.Injective fun y : Y i => (Fintype.equivFin (Y i) y).val :=
    fun i => Fin.val_injective.comp (Fintype.equivFin (Y i)).injective
  have h' := h {a // a ∈ A} (uniformProbOn A hA)
    fun i (ω : {a // a ∈ A}) => (Fintype.equivFin (Y i) (ω.val i)).val
  rw [LinearForm.evalEntropy] at h'
  rw [LinearForm.evalLogSize]
  refine le_of_eq_of_le (Finset.sum_congr rfl fun I _ => ?_) h'
  rw [entropySub_uniformProbOn_enc_eq_logb_projCard A hA hU _ henc I]

end Kolmogorov
