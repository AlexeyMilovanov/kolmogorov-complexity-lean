/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Complexity.Applications.LovaszLocalLemma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Set.Finite.List
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.Field.GeomSum

/-!
# Restriction Bounds

Restrictions `(F, X)` on infinite binary sequences, as used in the chapter on applications of
Kolmogorov complexity in Shen, Uspensky and Vereshchagin.  A sequence `ω` is forbidden by `(F, X)`
when the bits of `ω` at the positions of `F` spell `X`.

## Main declarations

* `restrictBits`, `Restriction`, `Restriction.Forbids`: the restricted string and the restrictions.
* `IsBoundedRestrictions`: the hypothesis of Theorem 161, at most `2^{αn}` restrictions of size
  `n` cover any given position.
* `exists_not_forbidden`: Theorem 161, a sequence avoiding all restrictions of large size, proved
  by the direct counting argument of Muchnik and Semenov.
-/

namespace Kolmogorov.Applications

/-- **SUV p. 249.**  The string `ω(F)`: the bits of `ω` at the indices of `F`, in increasing
order. -/
def restrictBits (w : ℕ → Bool) (F : Finset ℕ) : List Bool := (F.sort (· ≤ ·)).map w

/-- **SUV p. 249.**  A restriction `(F, X)`: a finite set of indices and a string with
`|X| = |F|`. -/
structure Restriction where
  /-- The indices covered by the restriction. -/
  indices : Finset ℕ
  /-- The forbidden values at these indices. -/
  values : List Bool
  /-- The string has one bit for each index. -/
  length_eq : values.length = indices.card

/-- The size of a restriction: the number of elements of `X`. -/
def Restriction.size (r : Restriction) : ℕ := r.values.length

/-- The sequence `ω` is forbidden by the restriction `(F, X)`: `ω(F) = X`. -/
def Restriction.Forbids (r : Restriction) (w : ℕ → Bool) : Prop :=
  restrictBits w r.indices = r.values

/-- **SUV Theorem 161, hypothesis.**  For every position `i` and every positive `n` there are at
most `2^{αn}` restrictions of size `n` covering `i`. -/
def IsBoundedRestrictions (α : ℝ) (R : Set Restriction) : Prop :=
  ∀ (i n : ℕ), 0 < n →
    {r ∈ R | r.size = n ∧ i ∈ r.indices}.Finite ∧
      (({r ∈ R | r.size = n ∧ i ∈ r.indices} : Set Restriction).ncard : ℝ) ≤ (2 : ℝ) ^ (α * n)

/-! ### Helpers for Theorem 161: the direct proof of Muchnik and Semenov -/

/-- The indicator sequence of a finite set of positions. -/
private def exists_not_forbidden_ind (S : Finset ℕ) : ℕ → Bool := fun j => decide (j ∈ S)

open Classical in
/-- The valid partial assignments on `I`, written as the sets `S ⊆ I` of positions carrying
`true`: no restriction of `R` of size `> N` with indices inside `I` is violated by `S`. -/
private noncomputable def exists_not_forbidden_valid (R : Set Restriction) (N : ℕ)
    (I : Finset ℕ) : Finset (Finset ℕ) :=
  I.powerset.filter (fun S => ∀ r ∈ R, N < r.size → r.indices ⊆ I →
    ¬ r.Forbids (exists_not_forbidden_ind S))

/-- The extension of the pair `(S, b)` by the position `i`: add `i` exactly when `b` is `true`. -/
private def exists_not_forbidden_ext (i : ℕ) (p : Finset ℕ × Bool) : Finset ℕ :=
  if p.2 then insert i p.1 else p.1

private theorem exists_not_forbidden_mem_valid {R : Set Restriction} {N : ℕ} {I S : Finset ℕ} :
    S ∈ exists_not_forbidden_valid R N I ↔
      S ⊆ I ∧ ∀ r ∈ R, N < r.size → r.indices ⊆ I →
        ¬ r.Forbids (exists_not_forbidden_ind S) := by
  simp only [exists_not_forbidden_valid, Finset.mem_filter, Finset.mem_powerset]

/-- The strings `ω(F)` and `ω'(F)` coincide exactly when `ω` and `ω'` agree on every index of
`F`. -/
theorem exists_not_forbidden_restrictBits_eq_iff {w w' : ℕ → Bool} {F : Finset ℕ} :
    restrictBits w F = restrictBits w' F ↔ ∀ j ∈ F, w j = w' j := by
  unfold restrictBits
  constructor
  · intro h j hj
    exact List.map_inj_left.1 h j ((Finset.mem_sort (· ≤ ·)).2 hj)
  · intro h
    exact List.map_inj_left.2 fun j hj => h j ((Finset.mem_sort (· ≤ ·)).1 hj)

/-- Forbiddenness depends only on the values at the indices of the restriction. -/
private theorem exists_not_forbidden_forbids_congr {r : Restriction} {w w' : ℕ → Bool}
    (h : ∀ j ∈ r.indices, w j = w' j) : r.Forbids w ↔ r.Forbids w' := by
  unfold Restriction.Forbids
  rw [exists_not_forbidden_restrictBits_eq_iff.2 h]

/-- Two sequences forbidden by the same restriction agree on its indices. -/
private theorem exists_not_forbidden_forbids_unique {r : Restriction} {w w' : ℕ → Bool}
    (h : r.Forbids w) (h' : r.Forbids w') : ∀ j ∈ r.indices, w j = w' j :=
  exists_not_forbidden_restrictBits_eq_iff.1 (h.trans h'.symm)

private theorem exists_not_forbidden_aux_term (α β : ℝ) (n : ℕ) :
    (2 : ℝ) ^ (α * (n : ℝ)) * (2 : ℝ) ^ (-(β * ((n : ℝ) - 1))) =
      (2 : ℝ) ^ β * ((2 : ℝ) ^ (α - β)) ^ n := by
  rw [← Real.rpow_natCast ((2 : ℝ) ^ (α - β)) n, ← Real.rpow_mul (by norm_num),
    ← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]
  congr 1
  ring

private theorem exists_not_forbidden_aux_geom {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (m n : ℕ) : ∑ i ∈ Finset.Ico m n, q ^ i ≤ q ^ m / (1 - q) := by
  have h1q : 0 < 1 - q := by linarith
  rcases le_or_gt m n with hmn | hmn
  · rw [geom_sum_Ico' hq1.ne hmn]
    exact div_le_div_of_nonneg_right (by linarith [pow_nonneg hq0 n]) h1q.le
  · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]
    positivity

/-- Step 1 of the proof of `exists_not_forbidden`: the tail of the geometric series.  For
`α < β < 1` there is `N` such that every partial sum over `n ∈ (N, M]` of
`2^{αn} · 2^{-β(n-1)}` is at most `2 - 2^β`. -/
private theorem exists_not_forbidden_tail {α β : ℝ} (hαβ : α < β) (hβ : β < 1) :
    ∃ N : ℕ, ∀ M : ℕ, ∑ n ∈ Finset.Ioc N M,
      (2 : ℝ) ^ (α * (n : ℝ)) * (2 : ℝ) ^ (-(β * ((n : ℝ) - 1))) ≤ 2 - (2 : ℝ) ^ β := by
  have hq0 : 0 < (2 : ℝ) ^ (α - β) := Real.rpow_pos_of_pos (by norm_num) _
  have hq1 : (2 : ℝ) ^ (α - β) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hb0 : 0 < (2 : ℝ) ^ β := Real.rpow_pos_of_pos (by norm_num) _
  have hb2 : (2 : ℝ) ^ β < 2 := by
    calc (2 : ℝ) ^ β < (2 : ℝ) ^ (1 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hβ
      _ = 2 := Real.rpow_one 2
  have hsum : ∀ N M : ℕ, ∑ n ∈ Finset.Ioc N M,
      (2 : ℝ) ^ (α * (n : ℝ)) * (2 : ℝ) ^ (-(β * ((n : ℝ) - 1))) =
        (2 : ℝ) ^ β * ∑ n ∈ Finset.Ico (N + 1) (M + 1), ((2 : ℝ) ^ (α - β)) ^ n := by
    intro N M
    have hI : Finset.Ioc N M = Finset.Ico (N + 1) (M + 1) := by
      ext x
      simp only [Finset.mem_Ioc, Finset.mem_Ico]
      omega
    rw [hI, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun n _ => exists_not_forbidden_aux_term α β n)
  set q : ℝ := (2 : ℝ) ^ (α - β) with hq
  have hq1' : 0 < 1 - q := by linarith
  have hb2' : 0 < 2 - (2 : ℝ) ^ β := by linarith
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one
    (show 0 < (2 - (2 : ℝ) ^ β) * (1 - q) / (2 : ℝ) ^ β by positivity) hq1
  refine ⟨N, fun M => ?_⟩
  rw [hsum]
  have h1 : q ^ N * (2 : ℝ) ^ β < (2 - (2 : ℝ) ^ β) * (1 - q) := (lt_div_iff₀ hb0).1 hN
  have h2 : ∑ n ∈ Finset.Ico (N + 1) (M + 1), q ^ n ≤ q ^ (N + 1) / (1 - q) :=
    exists_not_forbidden_aux_geom hq0.le hq1 (N + 1) (M + 1)
  have h3 : q ^ (N + 1) ≤ q ^ N := by
    rw [pow_succ]
    nlinarith [pow_pos hq0 N]
  have h4 : q ^ (N + 1) / (1 - q) * (2 : ℝ) ^ β ≤ 2 - (2 : ℝ) ^ β := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hq1']
    calc q ^ (N + 1) * (2 : ℝ) ^ β ≤ q ^ N * (2 : ℝ) ^ β :=
          mul_le_mul_of_nonneg_right h3 hb0.le
      _ ≤ (2 - (2 : ℝ) ^ β) * (1 - q) := h1.le
  calc (2 : ℝ) ^ β * ∑ n ∈ Finset.Ico (N + 1) (M + 1), q ^ n
      ≤ (2 : ℝ) ^ β * (q ^ (N + 1) / (1 - q)) := mul_le_mul_of_nonneg_left h2 hb0.le
    _ = q ^ (N + 1) / (1 - q) * (2 : ℝ) ^ β := mul_comm _ _
    _ ≤ 2 - (2 : ℝ) ^ β := h4

/-- The set of the sequences forbidden by a restriction is open in the product topology of
`ℕ → Bool`: it contains the finite cylinder over the indices of the restriction around each of its
points. -/
private theorem exists_not_forbidden_aux_isOpen (r : Restriction) :
    IsOpen {w : ℕ → Bool | r.Forbids w} := by
  rw [isOpen_iff_mem_nhds]
  intro w hw
  have hcyl : IsOpen (⋂ j ∈ r.indices, (fun w' : ℕ → Bool => w' j) ⁻¹' {w j}) := by
    refine isOpen_biInter_finset fun j _ => ?_
    exact (isOpen_discrete _).preimage (continuous_apply j)
  refine Filter.mem_of_superset (hcyl.mem_nhds ?_) ?_
  · simp
  · intro w' hw'
    simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff] at hw'
    exact (exists_not_forbidden_forbids_congr (fun j hj => (hw' j hj).symm)).1 hw

/-- Step 2 of the proof of `exists_not_forbidden`: compactness.  If every finite set `I`
of positions carries a valid assignment (a set `S ⊆ I` that violates no restriction of `R` of size
`> N` with indices inside `I`), then there is a sequence not forbidden by any restriction of `R` of
size `> N`. -/
private theorem exists_not_forbidden_compactness {R : Set Restriction} {N : ℕ}
    (h : ∀ I : Finset ℕ, (exists_not_forbidden_valid R N I).Nonempty) :
    ∃ w : ℕ → Bool, ∀ r ∈ R, N < r.size → ¬ r.Forbids w := by
  let D : ℕ → Set (ℕ → Bool) := fun n =>
    {w | ∀ r ∈ R, N < r.size → r.indices ⊆ Finset.range n → ¬ r.Forbids w}
  have hclosed : ∀ n, IsClosed (D n) := by
    intro n
    have hD : D n = ⋂ r ∈ R, ⋂ (_ : N < r.size), ⋂ (_ : r.indices ⊆ Finset.range n),
        {w : ℕ → Bool | r.Forbids w}ᶜ := by
      ext w
      simp only [Set.mem_iInter, Set.mem_compl_iff]
      exact Iff.rfl
    rw [hD]
    exact isClosed_biInter fun r _ => isClosed_iInter fun _ => isClosed_iInter fun _ =>
      (exists_not_forbidden_aux_isOpen r).isClosed_compl
  have hanti : ∀ n, D (n + 1) ⊆ D n := by
    intro n w hw r hr hNr hsub
    exact hw r hr hNr (hsub.trans (Finset.range_subset_range.2 (Nat.le_succ n)))
  have hne : ∀ n, (D n).Nonempty := by
    intro n
    obtain ⟨S, hS⟩ := h (Finset.range n)
    rw [exists_not_forbidden_mem_valid] at hS
    exact ⟨exists_not_forbidden_ind S, hS.2⟩
  obtain ⟨w, hw⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed D hanti hne
    (hclosed 0).isCompact hclosed
  refine ⟨w, fun r hr hNr => ?_⟩
  obtain ⟨n, hn⟩ := Finset.exists_nat_subset_range r.indices
  exact (Set.mem_iInter.1 hw n) r hr hNr hn

/-- The extension map is injective on the pairs whose set lies inside `I`, when `i ∉ I`. -/
private theorem exists_not_forbidden_aux_ext_inj {I : Finset ℕ} {i : ℕ} (hi : i ∉ I)
    {p q : Finset ℕ × Bool} (hp : p.1 ⊆ I) (hq : q.1 ⊆ I)
    (h : exists_not_forbidden_ext i p = exists_not_forbidden_ext i q) : p = q := by
  obtain ⟨S, b⟩ := p
  obtain ⟨S', b'⟩ := q
  simp only at hp hq
  have hiS : i ∉ S := fun h => hi (hp h)
  have hiS' : i ∉ S' := fun h => hi (hq h)
  cases b <;> cases b' <;> simp only [exists_not_forbidden_ext, Bool.false_eq_true, ite_false,
    ite_true] at h
  · rw [h]
  · exact absurd (by rw [h]; exact Finset.mem_insert_self i S') hiS
  · exact absurd (by rw [← h]; exact Finset.mem_insert_self i S) hiS'
  · have h2 := congrArg (fun T => T.erase i) h
    simp only [Finset.erase_insert hiS, Finset.erase_insert hiS'] at h2
    rw [h2]

/-- Step 3 of the proof of `exists_not_forbidden`: counting the extensions.  Every valid
set `S` on `I` has the two extensions `S` and `insert i S` to `insert i I` (`i ∉ I`); at least
`2 · c(I) - #bad` of the `2 · c(I)` extensions are valid on `insert i I`, where `bad` is the set of
extensions that are not. -/
private theorem exists_not_forbidden_count_ext {R : Set Restriction} {N : ℕ}
    {I : Finset ℕ} {i : ℕ} (hi : i ∉ I) :
    2 * (exists_not_forbidden_valid R N I).card ≤
      (exists_not_forbidden_valid R N (insert i I)).card +
        ((exists_not_forbidden_valid R N I ×ˢ (Finset.univ : Finset Bool)).filter
          (fun p => exists_not_forbidden_ext i p ∉
            exists_not_forbidden_valid R N (insert i I))).card := by
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := exists_not_forbidden_valid R N I ×ˢ (Finset.univ : Finset Bool))
    (fun p => exists_not_forbidden_ext i p ∈ exists_not_forbidden_valid R N (insert i I))
  have hcard : (exists_not_forbidden_valid R N I ×ˢ (Finset.univ : Finset Bool)).card
      = 2 * (exists_not_forbidden_valid R N I).card := by
    rw [Finset.card_product, Finset.card_univ, Fintype.card_bool, mul_comm]
  have hinj : ((exists_not_forbidden_valid R N I ×ˢ (Finset.univ : Finset Bool)).filter
      (fun p => exists_not_forbidden_ext i p ∈
        exists_not_forbidden_valid R N (insert i I))).card
      ≤ (exists_not_forbidden_valid R N (insert i I)).card := by
    apply Finset.card_le_card_of_injOn (exists_not_forbidden_ext i)
    · intro p hp
      exact Finset.mem_coe.2 (Finset.mem_filter.1 (Finset.mem_coe.1 hp)).2
    · intro p hp q hq hpq
      have hp' := (Finset.mem_filter.1 (Finset.mem_coe.1 hp)).1
      have hq' := (Finset.mem_filter.1 (Finset.mem_coe.1 hq)).1
      have hp1 := ((exists_not_forbidden_mem_valid.1 (Finset.mem_product.1 hp').1)).1
      have hq1 := ((exists_not_forbidden_mem_valid.1 (Finset.mem_product.1 hq').1)).1
      exact exists_not_forbidden_aux_ext_inj hi hp1 hq1 hpq
  omega

/-- Removing a set `K` of positions from a valid set keeps it valid on `I \ K`. -/
private theorem exists_not_forbidden_aux_sdiff_mem {R : Set Restriction} {N : ℕ}
    {I S K : Finset ℕ} (hS : S ∈ exists_not_forbidden_valid R N I) :
    S \ K ∈ exists_not_forbidden_valid R N (I \ K) := by
  rw [exists_not_forbidden_mem_valid] at hS ⊢
  obtain ⟨hSI, hS⟩ := hS
  refine ⟨Finset.sdiff_subset_sdiff hSI (Finset.Subset.refl K), fun r' hr' hN hsub => ?_⟩
  have hsubI : r'.indices ⊆ I := hsub.trans Finset.sdiff_subset
  rw [exists_not_forbidden_forbids_congr (w' := exists_not_forbidden_ind S)]
  · exact hS r' hr' hN hsubI
  · intro j hj
    have hj' := Finset.mem_sdiff.1 (hsub hj)
    simp [exists_not_forbidden_ind, hj'.2]

/-- The new position `i` belongs to the extension of `p` exactly when the bit of `p` is `true`. -/
private theorem exists_not_forbidden_aux_ext_self {i : ℕ} {I : Finset ℕ}
    {p : Finset ℕ × Bool} (hp : p.1 ⊆ I) (hi : i ∉ I) :
    i ∈ exists_not_forbidden_ext i p ↔ p.2 = true := by
  unfold exists_not_forbidden_ext
  cases p.2
  · simp only [Bool.false_eq_true, ite_false, iff_false]
    exact fun h' => hi (hp h')
  · simp

/-- Every other position belongs to the extension of `p` exactly when it belongs to `p.1`. -/
private theorem exists_not_forbidden_aux_ext_other {i j : ℕ} {p : Finset ℕ × Bool}
    (hj : j ≠ i) : j ∈ exists_not_forbidden_ext i p ↔ j ∈ p.1 := by
  unfold exists_not_forbidden_ext
  split_ifs <;> simp [hj]

open Classical in
/-- Step 4 of the proof of `exists_not_forbidden`: the extensions violating one fixed
restriction `r` with `i ∈ r.indices ⊆ insert i I`.  The map `(S, b) ↦ S \ K`, `K = r.indices \ {i}`,
is injective on them (they agree with the values of `r` on `K` and at `i`) and lands in the valid
sets on `I \ K`. -/
private theorem exists_not_forbidden_count_viol {R : Set Restriction} {N : ℕ}
    {I : Finset ℕ} {i : ℕ} (hi : i ∉ I) {r : Restriction} (hri : i ∈ r.indices) :
    ((exists_not_forbidden_valid R N I ×ˢ (Finset.univ : Finset Bool)).filter
        (fun p => r.Forbids (exists_not_forbidden_ind (exists_not_forbidden_ext i p)))).card ≤
      (exists_not_forbidden_valid R N (I \ r.indices.erase i)).card := by
  refine Finset.card_le_card_of_injOn (fun p => p.1 \ r.indices.erase i) ?_ ?_
  · intro p hp
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp
    exact exists_not_forbidden_aux_sdiff_mem hp.1.1
  · intro p hp p' hp' hpp
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp hp'
    have hpI : p.1 ⊆ I := (exists_not_forbidden_mem_valid.1 hp.1.1).1
    have hpI' : p'.1 ⊆ I := (exists_not_forbidden_mem_valid.1 hp'.1.1).1
    have huniq := exists_not_forbidden_forbids_unique hp.2 hp'.2
    -- the bits agree: look at the position `i`
    have hbit : p.2 = p'.2 := by
      have h := huniq i hri
      simp only [exists_not_forbidden_ind, decide_eq_decide,
        exists_not_forbidden_aux_ext_self hpI hi,
        exists_not_forbidden_aux_ext_self hpI' hi] at h
      cases h1 : p.2 <;> cases h2 : p'.2 <;> simp_all
    -- the sets agree: on `K` by the values of `r`, off `K` by hypothesis
    have hset : p.1 = p'.1 := by
      ext j
      by_cases hjK : j ∈ r.indices.erase i
      · have hji : j ≠ i := Finset.ne_of_mem_erase hjK
        have h := huniq j (Finset.mem_of_mem_erase hjK)
        simp only [exists_not_forbidden_ind, decide_eq_decide,
          exists_not_forbidden_aux_ext_other hji] at h
        exact h
      · have h := congrArg (fun s => j ∈ s) hpp
        simpa [hjK] using h
    exact Prod.ext hset hbit

open Classical in
/-- A bad extension violates some restriction of the family `T`. -/
private theorem exists_not_forbidden_aux_bad_subset {R : Set Restriction} {N : ℕ}
    {I : Finset ℕ} {i : ℕ} (T : Finset Restriction)
    (hT : ∀ r ∈ R, N < r.size → i ∈ r.indices → r.indices ⊆ insert i I → r ∈ T) :
    ((exists_not_forbidden_valid R N I ×ˢ (Finset.univ : Finset Bool)).filter
        (fun p => exists_not_forbidden_ext i p ∉
          exists_not_forbidden_valid R N (insert i I))) ⊆
      T.biUnion (fun r =>
        (exists_not_forbidden_valid R N I ×ˢ (Finset.univ : Finset Bool)).filter
          (fun p => r.Forbids (exists_not_forbidden_ind (exists_not_forbidden_ext i p)))) := by
  intro p hp
  obtain ⟨hpA, hpB⟩ := Finset.mem_filter.1 hp
  have hS : p.1 ∈ exists_not_forbidden_valid R N I := (Finset.mem_product.1 hpA).1
  obtain ⟨hSI, hSv⟩ := exists_not_forbidden_mem_valid.1 hS
  have hext_sub : exists_not_forbidden_ext i p ⊆ insert i I := by
    unfold exists_not_forbidden_ext
    split_ifs
    · exact Finset.insert_subset_insert i hSI
    · exact hSI.trans (Finset.subset_insert i I)
  have hex : ∃ r ∈ R, N < r.size ∧ r.indices ⊆ insert i I ∧
      r.Forbids (exists_not_forbidden_ind (exists_not_forbidden_ext i p)) := by
    by_contra hcon
    apply hpB
    rw [exists_not_forbidden_mem_valid]
    exact ⟨hext_sub, fun r hrR hNr hrsub hrF => hcon ⟨r, hrR, hNr, hrsub, hrF⟩⟩
  obtain ⟨r, hrR, hNr, hrsub, hrF⟩ := hex
  have hir : i ∈ r.indices := by
    by_contra hir
    have hrI : r.indices ⊆ I := by
      intro j hj
      have hj' := hrsub hj
      rw [Finset.mem_insert] at hj'
      rcases hj' with rfl | h
      · exact absurd hj hir
      · exact h
    have hagree : ∀ j ∈ r.indices, exists_not_forbidden_ind (exists_not_forbidden_ext i p) j =
        exists_not_forbidden_ind p.1 j := by
      intro j hj
      have hji : j ≠ i := fun h => hir (h ▸ hj)
      unfold exists_not_forbidden_ind exists_not_forbidden_ext
      split_ifs
      · simp [hji]
      · rfl
    exact hSv r hrR hNr hrI ((exists_not_forbidden_forbids_congr hagree).1 hrF)
  rw [Finset.mem_biUnion]
  exact ⟨r, hT r hrR hNr hir hrsub, Finset.mem_filter.2 ⟨hpA, hrF⟩⟩

open Classical in
/-- Step 5 of the proof of `exists_not_forbidden`: a bad extension violates a restriction
`r ∈ R` of size `> N` with `i ∈ r.indices ⊆ insert i I` (otherwise its restriction to `I` would be
invalid); the union bound and step 4 give
`2 c(I) ≤ c(insert i I) + ∑_{r ∈ T} c(I \ (r.indices \ {i}))`. -/
private theorem exists_not_forbidden_count {R : Set Restriction} {N : ℕ}
    {I : Finset ℕ} {i : ℕ} (hi : i ∉ I) (T : Finset Restriction)
    (hT : ∀ r ∈ R, N < r.size → i ∈ r.indices → r.indices ⊆ insert i I → r ∈ T)
    (hT' : ∀ r ∈ T, i ∈ r.indices ∧ r.indices ⊆ insert i I) :
    2 * (exists_not_forbidden_valid R N I).card ≤
      (exists_not_forbidden_valid R N (insert i I)).card +
        ∑ r ∈ T, (exists_not_forbidden_valid R N (I \ r.indices.erase i)).card := by
  have h3 := exists_not_forbidden_count_ext (R := R) (N := N) hi
  have hsub := exists_not_forbidden_aux_bad_subset (R := R) (N := N) (I := I) (i := i) T hT
  have hcard : ((exists_not_forbidden_valid R N I ×ˢ (Finset.univ : Finset Bool)).filter
        (fun p => exists_not_forbidden_ext i p ∉
          exists_not_forbidden_valid R N (insert i I))).card ≤
      ∑ r ∈ T, (exists_not_forbidden_valid R N (I \ r.indices.erase i)).card := by
    calc _ ≤ (T.biUnion (fun r =>
          (exists_not_forbidden_valid R N I ×ˢ (Finset.univ : Finset Bool)).filter
            (fun p => r.Forbids (exists_not_forbidden_ind (exists_not_forbidden_ext i p))))).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ r ∈ T, ((exists_not_forbidden_valid R N I ×ˢ (Finset.univ : Finset Bool)).filter
            (fun p => r.Forbids (exists_not_forbidden_ind (exists_not_forbidden_ext i p)))).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ r ∈ T, (exists_not_forbidden_valid R N (I \ r.indices.erase i)).card :=
          Finset.sum_le_sum fun r hr =>
            exists_not_forbidden_count_viol hi (hT' r hr).1
  exact h3.trans (Nat.add_le_add_left hcard _)

/-- Step 6 of the proof of `exists_not_forbidden`: the family of the restrictions that can
be violated by an extension by `i` is finite, and weighted by the size it is bounded by the
hypothesis `IsBoundedRestrictions`: `T = {r ∈ R | N < |r|, i ∈ r.indices ⊆ insert i I}` satisfies
`∑_{r ∈ T} g |r| ≤ ∑_{n ∈ (N, |I|+1]} 2^{αn} g n` for every nonnegative weight `g`. -/
private theorem exists_not_forbidden_family {α : ℝ} {R : Set Restriction}
    (hR : IsBoundedRestrictions α R) (N : ℕ) (I : Finset ℕ) (i : ℕ) :
    ∃ T : Finset Restriction,
      (∀ r : Restriction,
        r ∈ T ↔ (r ∈ R ∧ N < r.size ∧ i ∈ r.indices ∧ r.indices ⊆ insert i I)) ∧
      ∀ g : ℕ → ℝ, (∀ n, 0 ≤ g n) →
        ∑ r ∈ T, g r.size ≤ ∑ n ∈ Finset.Ioc N (I.card + 1), (2 : ℝ) ^ (α * (n : ℝ)) * g n := by
  classical
  -- the restrictions of size `n` covering `i`
  let E : ℕ → Set Restriction := fun n => {r | r ∈ R ∧ r.size = n ∧ i ∈ r.indices}
  have hn0 : ∀ n ∈ Finset.Ioc N (I.card + 1), 0 < n := by
    intro n hn
    have := (Finset.mem_Ioc.1 hn).1
    omega
  have hEfin : ∀ n ∈ Finset.Ioc N (I.card + 1), (E n).Finite := fun n hn => (hR i n (hn0 n hn)).1
  have hEcard : ∀ n ∈ Finset.Ioc N (I.card + 1),
      ((E n).ncard : ℝ) ≤ (2 : ℝ) ^ (α * (n : ℝ)) := fun n hn => (hR i n (hn0 n hn)).2
  let Tset : Set Restriction :=
    {r | r ∈ R ∧ N < r.size ∧ i ∈ r.indices ∧ r.indices ⊆ insert i I}
  -- the sizes of the elements of `Tset` lie in `(N, |I| + 1]`
  have hsize : ∀ r ∈ Tset, r.size ∈ Finset.Ioc N (I.card + 1) := by
    intro r hr
    obtain ⟨_, hNr, _, hrI⟩ := hr
    rw [Finset.mem_Ioc]
    refine ⟨hNr, ?_⟩
    have h1 : r.size = r.indices.card := r.length_eq
    have h2 : r.indices.card ≤ (insert i I).card := Finset.card_le_card hrI
    have h3 : (insert i I).card ≤ I.card + 1 := Finset.card_insert_le i I
    omega
  have hsub : Tset ⊆ ⋃ n ∈ (Finset.Ioc N (I.card + 1) : Set ℕ), E n := by
    intro r hr
    have hs := hsize r hr
    obtain ⟨hrR, _, hir, _⟩ := hr
    simp only [Set.mem_iUnion]
    exact ⟨r.size, hs, hrR, rfl, hir⟩
  have hfin : Tset.Finite :=
    Set.Finite.subset (Set.Finite.biUnion (Finset.finite_toSet _) hEfin) hsub
  refine ⟨hfin.toFinset, fun r => hfin.mem_toFinset, ?_⟩
  intro g hg
  have hmaps : ∀ r ∈ hfin.toFinset, r.size ∈ Finset.Ioc N (I.card + 1) :=
    fun r hr => hsize r (hfin.mem_toFinset.1 hr)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_le_sum fun n hn => ?_
  have h1 : ∑ r ∈ hfin.toFinset.filter (fun r => r.size = n), g r.size =
      ((hfin.toFinset.filter (fun r => r.size = n)).card : ℝ) * g n := by
    rw [Finset.sum_congr rfl (fun r hr => by rw [(Finset.mem_filter.1 hr).2]),
      Finset.sum_const, nsmul_eq_mul]
  rw [h1]
  refine mul_le_mul_of_nonneg_right ?_ (hg n)
  have hsubE : ((hfin.toFinset.filter (fun r => r.size = n) : Finset Restriction) :
      Set Restriction) ⊆ E n := by
    intro r hr
    have hr' := Finset.mem_filter.1 (Finset.mem_coe.1 hr)
    obtain ⟨hrR, _, hir, _⟩ := hfin.mem_toFinset.1 hr'.1
    exact ⟨hrR, hr'.2, hir⟩
  have hcard := Set.ncard_le_ncard hsubE (hEfin n hn)
  rw [Set.ncard_coe_finset] at hcard
  exact le_trans (by exact_mod_cast hcard) (hEcard n hn)

/-- Step 7 of the proof of `exists_not_forbidden`: adding a point multiplies the number of
valid assignments by at least `2^β`, provided the removal of any subset `K ⊆ I` divides it by at
most
`2^{β|K|}` (the induction hypothesis). -/
private theorem exists_not_forbidden_growth {α β : ℝ} {R : Set Restriction}
    (hR : IsBoundedRestrictions α R) {N : ℕ}
    (hN : ∀ M : ℕ, ∑ n ∈ Finset.Ioc N M,
      (2 : ℝ) ^ (α * (n : ℝ)) * (2 : ℝ) ^ (-(β * ((n : ℝ) - 1))) ≤ 2 - (2 : ℝ) ^ β)
    {I : Finset ℕ} {i : ℕ} (hi : i ∉ I)
    (hQ : ∀ K ⊆ I, (2 : ℝ) ^ (β * (K.card : ℝ)) *
      ((exists_not_forbidden_valid R N (I \ K)).card : ℝ) ≤
        (exists_not_forbidden_valid R N I).card) :
    (2 : ℝ) ^ β * ((exists_not_forbidden_valid R N I).card : ℝ) ≤
      (exists_not_forbidden_valid R N (insert i I)).card := by
  obtain ⟨T, hTmem, hTsum⟩ := exists_not_forbidden_family hR N I i
  have hcount := exists_not_forbidden_count (R := R) (N := N) hi T
    (fun r hrR hNr hir hsub => (hTmem r).2 ⟨hrR, hNr, hir, hsub⟩)
    (fun r hr => ⟨((hTmem r).1 hr).2.2.1, ((hTmem r).1 hr).2.2.2⟩)
  have hcount' := (Nat.cast_le (α := ℝ)).2 hcount
  push_cast at hcount'
  have hc0 : (0 : ℝ) ≤ ((exists_not_forbidden_valid R N I).card : ℝ) := Nat.cast_nonneg _
  have hterm : ∀ r ∈ T, ((exists_not_forbidden_valid R N (I \ r.indices.erase i)).card : ℝ) ≤
      (2 : ℝ) ^ (-(β * ((r.size : ℝ) - 1))) * ((exists_not_forbidden_valid R N I).card : ℝ) := by
    intro r hr
    obtain ⟨_, _, hir, hsub⟩ := (hTmem r).1 hr
    have hKI : r.indices.erase i ⊆ I := by
      intro x hx
      rw [Finset.mem_erase] at hx
      have hx2 := hsub hx.2
      rw [Finset.mem_insert] at hx2
      exact hx2.resolve_left hx.1
    have hcard : ((r.indices.erase i).card : ℝ) = (r.size : ℝ) - 1 := by
      have h1 : 1 ≤ r.indices.card := Finset.card_pos.2 ⟨i, hir⟩
      have h2 : r.size = r.indices.card := r.length_eq
      rw [Finset.card_erase_of_mem hir, Nat.cast_sub h1, h2]
      simp
    have h1 := hQ _ hKI
    rw [hcard] at h1
    have hpos : (0 : ℝ) < (2 : ℝ) ^ (β * ((r.size : ℝ) - 1)) := by positivity
    rw [Real.rpow_neg (by norm_num), inv_mul_eq_div, le_div_iff₀ hpos]
    linarith
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.sum_mul] at hsum
  have hg : ∑ r ∈ T, (2 : ℝ) ^ (-(β * ((r.size : ℝ) - 1))) ≤
      ∑ n ∈ Finset.Ioc N (I.card + 1),
        (2 : ℝ) ^ (α * (n : ℝ)) * (2 : ℝ) ^ (-(β * ((n : ℝ) - 1))) :=
    hTsum (fun n => (2 : ℝ) ^ (-(β * ((n : ℝ) - 1)))) (fun n => by positivity)
  have hS : ∑ r ∈ T, ((exists_not_forbidden_valid R N (I \ r.indices.erase i)).card : ℝ) ≤
      (2 - (2 : ℝ) ^ β) * ((exists_not_forbidden_valid R N I).card : ℝ) :=
    hsum.trans (mul_le_mul_of_nonneg_right (hg.trans (hN (I.card + 1))) hc0)
  linarith

/-- Step 8 of the proof of `exists_not_forbidden`: by induction on `|I|`, removing a
subset
`K ⊆ I` divides the number of valid assignments by at most `2^{β|K|}`. -/
private theorem exists_not_forbidden_Q {α β : ℝ} {R : Set Restriction}
    (hR : IsBoundedRestrictions α R) {N : ℕ}
    (hN : ∀ M : ℕ, ∑ n ∈ Finset.Ioc N M,
      (2 : ℝ) ^ (α * (n : ℝ)) * (2 : ℝ) ^ (-(β * ((n : ℝ) - 1))) ≤ 2 - (2 : ℝ) ^ β) :
    ∀ (I K : Finset ℕ), K ⊆ I → (2 : ℝ) ^ (β * (K.card : ℝ)) *
      ((exists_not_forbidden_valid R N (I \ K)).card : ℝ) ≤
        (exists_not_forbidden_valid R N I).card := by
  suffices h : ∀ n : ℕ, ∀ I : Finset ℕ, I.card = n → ∀ K : Finset ℕ, K ⊆ I →
      (2 : ℝ) ^ (β * (K.card : ℝ)) * ((exists_not_forbidden_valid R N (I \ K)).card : ℝ) ≤
        (exists_not_forbidden_valid R N I).card from fun I K hK => h _ I rfl K hK
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro I hI K
    induction K using Finset.induction_on with
    | empty => intro _; simp
    | insert k K' hk ihK =>
      intro hKI
      have hK'I : K' ⊆ I := fun x hx => hKI (Finset.mem_insert_of_mem hx)
      have hkI : k ∈ I := hKI (Finset.mem_insert_self k K')
      have ih1 := ihK hK'I
      have hkJ : k ∉ I \ insert k K' := by simp
      have hJcard : (I \ insert k K').card < n := by
        rw [← hI]
        refine Finset.card_lt_card ⟨Finset.sdiff_subset, fun h => hkJ (h hkI)⟩
      have hQJ : ∀ K'' ⊆ I \ insert k K',
          (2 : ℝ) ^ (β * (K''.card : ℝ)) *
            ((exists_not_forbidden_valid R N ((I \ insert k K') \ K'')).card : ℝ) ≤
              (exists_not_forbidden_valid R N (I \ insert k K')).card :=
        fun K'' hK'' => ih _ hJcard (I \ insert k K') rfl K'' hK''
      have hgrow := exists_not_forbidden_growth hR hN hkJ hQJ
      have hins : insert k (I \ insert k K') = I \ K' := by
        ext x
        simp only [Finset.mem_insert, Finset.mem_sdiff]
        constructor
        · rintro (rfl | ⟨hxI, hx⟩)
          · exact ⟨hkI, hk⟩
          · exact ⟨hxI, fun h => hx (Or.inr h)⟩
        · rintro ⟨hxI, hx⟩
          by_cases hxk : x = k
          · exact Or.inl hxk
          · exact Or.inr ⟨hxI, by
              rintro (h | h)
              · exact hxk h
              · exact hx h⟩
      rw [hins] at hgrow
      calc (2 : ℝ) ^ (β * ((insert k K').card : ℝ)) *
            ((exists_not_forbidden_valid R N (I \ insert k K')).card : ℝ)
          = (2 : ℝ) ^ (β * (K'.card : ℝ)) *
              ((2 : ℝ) ^ β * ((exists_not_forbidden_valid R N (I \ insert k K')).card : ℝ)) := by
            rw [Finset.card_insert_of_notMem hk]
            push_cast
            rw [mul_add, mul_one, Real.rpow_add (by norm_num)]
            ring
        _ ≤ (2 : ℝ) ^ (β * (K'.card : ℝ)) *
              ((exists_not_forbidden_valid R N (I \ K')).card : ℝ) := by
            gcongr
        _ ≤ (exists_not_forbidden_valid R N I).card := ih1

/-- **SUV Theorem 161, p. 249.**  Let `α ∈ (0, 1)` and let `R` be a set of restrictions with the
bound above.  Then there are a number `N` and a sequence that is not forbidden by any restriction of
size greater than `N`. -/
theorem exists_not_forbidden {α : ℝ} (_hα0 : 0 < α) (hα1 : α < 1) {R : Set Restriction}
    (hR : IsBoundedRestrictions α R) :
    ∃ (N : ℕ) (w : ℕ → Bool), ∀ r ∈ R, N < r.size → ¬ r.Forbids w := by
  obtain ⟨β, hαβ, hβ⟩ := exists_between hα1
  obtain ⟨N, hN⟩ := exists_not_forbidden_tail hαβ hβ
  have hQ := exists_not_forbidden_Q hR hN
  have hne : ∀ I : Finset ℕ, (exists_not_forbidden_valid R N I).Nonempty := by
    intro I
    have h1 := hQ I I (Finset.Subset.refl I)
    rw [Finset.sdiff_self] at h1
    have h2 : (∅ : Finset ℕ) ∈ exists_not_forbidden_valid R N ∅ := by
      rw [exists_not_forbidden_mem_valid]
      refine ⟨Finset.Subset.refl _, fun r _ hNr hrI => ?_⟩
      have h0 : r.indices = ∅ := Finset.subset_empty.1 hrI
      have hsz : r.size = 0 := by
        change r.values.length = 0
        rw [r.length_eq, h0]
        rfl
      omega
    have h3 : 1 ≤ (exists_not_forbidden_valid R N ∅).card := Finset.card_pos.2 ⟨∅, h2⟩
    have h4 : (0 : ℝ) < ((exists_not_forbidden_valid R N I).card : ℝ) := by
      calc (0 : ℝ) < (2 : ℝ) ^ (β * (I.card : ℝ)) * 1 := by positivity
        _ ≤ (2 : ℝ) ^ (β * (I.card : ℝ)) * ((exists_not_forbidden_valid R N ∅).card : ℝ) := by
          gcongr
          exact_mod_cast h3
        _ ≤ _ := h1
    exact Finset.card_pos.1 (by exact_mod_cast h4)
  obtain ⟨w, hw⟩ := exists_not_forbidden_compactness hne
  exact ⟨N, w, hw⟩

/-- Step 1 of the proof of `exists_threshold_restrictions`: 1 - y * x ≤ (1 - x) ^ y -/
private theorem exists_threshold_restrictions_bernoulli
    {x y : ℝ} (_hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy : 1 ≤ y) :
    1 - y * x ≤ (1 - x) ^ y := by
  have h_sub : -1 ≤ -x := by linarith
  have h_apply := one_add_mul_self_le_rpow_one_add h_sub hy
  have h1 : 1 + y * -x = 1 - y * x := by ring
  have h2 : 1 + -x = 1 - x := by ring
  rw [h1, h2] at h_apply
  exact h_apply

private theorem exists_threshold_restrictions_bernoulli_prod_weierstrass
    {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (hx0 : ∀ a ∈ s, 0 ≤ x a) (hx1 : ∀ a ∈ s, x a ≤ 1) :
    1 - ∑ a ∈ s, x a ≤ ∏ a ∈ s, (1 - x a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have ih_le := ih (fun b hb => hx0 b (Finset.mem_insert_of_mem hb))
                      (fun b hb => hx1 b (Finset.mem_insert_of_mem hb))
    have ha_le1 : 1 - x a ≥ 0 := by linarith [hx1 a (Finset.mem_insert_self a s)]
    have step1 : (1 - x a) * (1 - ∑ b ∈ s, x b) ≤ (1 - x a) * ∏ b ∈ s, (1 - x b) :=
        mul_le_mul_of_nonneg_left ih_le ha_le1
    have hsum_nonneg : 0 ≤ ∑ b ∈ s, x b := Finset.sum_nonneg (fun b hb => hx0 b
        (Finset.mem_insert_of_mem hb))
    have hxa_nonneg : 0 ≤ x a := hx0 a (Finset.mem_insert_self a s)
    have step2 : 1 - (x a + ∑ b ∈ s, x b) ≤ (1 - x a) * (1 - ∑ b ∈ s, x b) := by nlinarith
    exact le_trans step2 step1

/-- Step 2 of the proof of `exists_threshold_restrictions`: product bound -/
private theorem exists_threshold_restrictions_bernoulli_prod
    {ι : Type*} (s : Finset ι) (f g : ι → ℝ)
    (hf0 : ∀ a ∈ s, 0 ≤ f a) (hf1 : ∀ a ∈ s, f a ≤ 1)
    (hg0 : ∀ a ∈ s, 0 ≤ g a) (hg1 : ∀ a ∈ s, 1 ≤ g a)
    (hsum : ∑ a ∈ s, g a * f a ≤ 1) :
    1 - ∑ a ∈ s, g a * f a ≤ ∏ a ∈ s, (1 - f a) ^ g a := by
  let x a := g a * f a
  have hx0 : ∀ a ∈ s, 0 ≤ x a := fun a ha => mul_nonneg (hg0 a ha) (hf0 a ha)
  have hxsum : ∀ a ∈ s, x a ≤ ∑ b ∈ s, x b := fun a ha => Finset.single_le_sum (fun b hb => hx0 b
      hb) ha
  have hx1 : ∀ a ∈ s, x a ≤ 1 := fun a ha => le_trans (hxsum a ha) hsum
  
  have weierstrass : 1 - ∑ a ∈ s, x a ≤ ∏ a ∈ s, (1 - x a) :=
      exists_threshold_restrictions_bernoulli_prod_weierstrass s x hx0 hx1
  
  have prod_le_prod : ∏ a ∈ s, (1 - x a) ≤ ∏ a ∈ s, (1 - f a) ^ g a := by
    apply Finset.prod_le_prod₀
    · intro a ha
      linarith [hx1 a ha]
    · intro a ha
      apply exists_threshold_restrictions_bernoulli (hf0 a ha) (hf1 a ha) (hg1 a ha)
  
  exact le_trans weierstrass prod_le_prod

/-- Step 3 of the proof of `exists_threshold_restrictions`: tail bound -/
private theorem exists_threshold_restrictions_tail
    {α β : ℝ} (hαβ : α < β) (hβ : β < 1) :
    ∃ N : ℕ, ∑' m : ℕ,
      (2 : ℝ) ^ (α * (m + N + 1 : ℝ)) *
        (2 : ℝ) ^ (-(β * (m + N + 1 : ℝ))) ≤
      1 - (2 : ℝ) ^ (β - 1) := by
  set r := (2 : ℝ) ^ (α - β)
  have hr0 : 0 < r := Real.rpow_pos_of_pos zero_lt_two _
  have hr1 : r < 1 := by
    rw [Real.rpow_lt_one_iff_of_pos zero_lt_two]
    left
    exact ⟨by norm_num, by linarith⟩
  have heps : 0 < 1 - (2 : ℝ) ^ (β - 1) := by
    have h1 : (2 : ℝ) ^ (β - 1) < 1 := by
      rw [Real.rpow_lt_one_iff_of_pos zero_lt_two]
      left
      exact ⟨by norm_num, by linarith⟩
    linarith
  have h_mul_pos : 0 < (1 - (2 : ℝ) ^ (β - 1)) * (1 - r) := mul_pos heps (by linarith)
  have h_bound : ∃ N : ℕ, r ^ N < (1 - (2 : ℝ) ^ (β - 1)) * (1 - r) :=
    exists_pow_lt_of_lt_one h_mul_pos hr1
  rcases h_bound with ⟨N, hN⟩
  use N
  have h_eq : ∀ m : ℕ, (2 : ℝ) ^ (α * (m + N + 1 : ℝ)) * (2 : ℝ) ^ (-(β * (m + N + 1 : ℝ))) = r ^ (N
      + 1) * r ^ m := by
    intro m
    dsimp [r]
    have h1 : (2 : ℝ) ^ (α * (m + N + 1 : ℝ)) * (2 : ℝ) ^ (-(β * (m + N + 1 : ℝ))) = (2 : ℝ) ^ ((α -
        β) * (m + N + 1 : ℝ)) := by
      rw [← Real.rpow_add zero_lt_two]; congr 1; ring
    rw [h1]
    have h2 : (N + 1 + m : ℝ) = (m + N + 1 : ℝ) := by ring
    rw [← h2]
    have h3 : (2 : ℝ) ^ ((α - β) * (N + 1 + m : ℝ)) = (2 : ℝ) ^ ((α - β) * (N + 1 : ℝ) + (α - β) *
        (m : ℝ)) := by
      congr 1; ring
    rw [h3, Real.rpow_add zero_lt_two, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by
        norm_num), ← Real.rpow_mul (by norm_num)]
    congr 1
    push_cast
    ring
  have h_sum : ∑' m : ℕ, (2 : ℝ) ^ (α * (m + N + 1 : ℝ)) * (2 : ℝ) ^ (-(β * (m + N + 1 : ℝ))) = r ^
      (N + 1) / (1 - r) := by
    calc ∑' m : ℕ, (2 : ℝ) ^ (α * (m + N + 1 : ℝ)) * (2 : ℝ) ^ (-(β * (m + N + 1 : ℝ)))
      _ = ∑' m : ℕ, r ^ (N + 1) * r ^ m := by congr 1; ext m; exact h_eq m
      _ = r ^ (N + 1) * ∑' m : ℕ, r ^ m := by rw [tsum_mul_left]
      _ = r ^ (N + 1) * (1 - r)⁻¹ := by rw [tsum_geometric_of_lt_one (by linarith) hr1]
      _ = r ^ (N + 1) / (1 - r) := by ring
  rw [h_sum]
  have h_le : r ^ (N + 1) ≤ r ^ N := by apply pow_le_pow_of_le_one hr0.le hr1.le; linarith
  have h_le2 : r ^ (N + 1) / (1 - r) ≤ r ^ N / (1 - r) := by gcongr
  have h_le3 : r ^ N / (1 - r) ≤ 1 - (2 : ℝ) ^ (β - 1) := by rw [div_le_iff₀ (by linarith)]; exact
      hN.le
  exact h_le2.trans h_le3

/-- Step 4 of the proof of `exists_threshold_restrictions`: sum comparison -/
private theorem exists_threshold_restrictions_sum_comp
    {α β : ℝ} (_hα : 0 < α) (hαβ : α < β) (N M : ℕ) (hNM : N < M)
    (hN : ∑' m : ℕ, (2 : ℝ) ^ (α * (m + N + 1 : ℝ)) * (2 : ℝ) ^ (-(β * (m + N + 1 : ℝ))) ≤ 1 - (2 :
        ℝ) ^ (β - 1)) :
    ∑ m ∈ Finset.Ico (N + 1) (M + 1), (2 : ℝ) ^ (α * (m : ℝ)) * (2 : ℝ) ^ (-(β * (m : ℝ))) ≤ 1 - (2
        : ℝ) ^ (β - 1) := by
  have h_shift : ∑ m ∈ Finset.Ico (N + 1) (M + 1), (2 : ℝ) ^ (α * (m : ℝ)) * (2 : ℝ) ^ (-(β * (m :
      ℝ))) = 
                 ∑ m ∈ Finset.range (M - N), (2 : ℝ) ^ (α * (m + N + 1 : ℝ)) * (2 : ℝ) ^ (-(β * (m +
                     N + 1 : ℝ))) := by
    rw [Finset.sum_Ico_eq_sum_range]
    have h_sub : M + 1 - (N + 1) = M - N := by omega
    rw [h_sub]
    congr 1
    ext m
    congr 1
    · congr 1
      push_cast
      ring
    · congr 1
      push_cast
      ring
  rw [h_shift]
  have h_f : ∀ (m : ℕ), 0 ≤ (2 : ℝ) ^ (α * (m + N + 1 : ℝ)) * (2 : ℝ) ^ (-(β * (m + N + 1 : ℝ))) :=
      by
    intro m
    have h_nonneg1 : 0 ≤ (2 : ℝ) ^ (α * (m + N + 1 : ℝ)) := Real.rpow_nonneg (by linarith) _
    have h_nonneg2 : 0 ≤ (2 : ℝ) ^ (-(β * (m + N + 1 : ℝ))) := Real.rpow_nonneg (by linarith) _
    exact mul_nonneg h_nonneg1 h_nonneg2
  have h_summable : Summable (fun (m : ℕ) => (2 : ℝ) ^ (α * (m + N + 1 : ℝ)) * (2 : ℝ) ^ (-(β * (m +
      N + 1 : ℝ)))) := by
    have h_eq : (fun (m : ℕ) => (2 : ℝ) ^ (α * (m + N + 1 : ℝ)) * (2 : ℝ) ^ (-(β * (m + N + 1 :
        ℝ)))) = 
                (fun (m : ℕ) => ((2 : ℝ) ^ (α - β)) ^ (m + N + 1)) := by
      ext m
      have h1 : (2 : ℝ) ^ (α * (m + N + 1 : ℝ)) * (2 : ℝ) ^ (-(β * (m + N + 1 : ℝ))) = (2 : ℝ) ^ ((α
          - β) * (m + N + 1 : ℝ)) := by
        rw [← Real.rpow_add zero_lt_two]
        congr 1
        ring
      rw [h1]
      have h_nat : (m + N + 1 : ℝ) = (m + N + 1 : ℕ) := by norm_cast
      rw [h_nat, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    rw [h_eq]
    have h_shift2 : (fun (m : ℕ) => ((2 : ℝ) ^ (α - β)) ^ (m + N + 1)) = 
                    (fun (m : ℕ) => ((2 : ℝ) ^ (α - β)) ^ (N + 1) * ((2 : ℝ) ^ (α - β)) ^ m) := by
      ext m
      have h_add : m + N + 1 = N + 1 + m := by omega
      rw [h_add, pow_add]
    rw [h_shift2]
    apply Summable.mul_left
    have h_abs_lt_one : (2 : ℝ) ^ (α - β) < 1 := by
      rw [Real.rpow_lt_one_iff_of_pos zero_lt_two]
      left
      exact ⟨by norm_num, by linarith⟩
    exact summable_geometric_of_lt_one (Real.rpow_nonneg (by linarith) _) h_abs_lt_one
  have h_le_tsum : ∑ m ∈ Finset.range (M - N), (2 : ℝ) ^ (α * (m + N + 1 : ℝ)) * (2 : ℝ) ^ (-(β * (m
      + N + 1 : ℝ))) ≤ 
                   ∑' m : ℕ, (2 : ℝ) ^ (α * (m + N + 1 : ℝ)) * (2 : ℝ) ^ (-(β * (m + N + 1 : ℝ))) :=
                       by
    apply sum_le_hasSum (Finset.range (M - N)) (fun i _hi => h_f i) h_summable.hasSum
  linarith

/-- **SUV p. 249**, the inequality of the proof of Theorem 161.  For `α < β < 1` there is a
threshold `N` such that `2^{β-1} ≤ ∏_{m>N} (1 - 2^{-βm})^{2^{αm}}`, on every finite range of `m`,
where the exponent is the exact bound of the hypothesis. -/
theorem exists_threshold_restrictions {α β : ℝ} (hα : 0 < α) (hαβ : α < β) (hβ : β < 1) :
    ∃ N : ℕ, ∀ M : ℕ, (2 : ℝ) ^ (β - 1) ≤
      ∏ m ∈ Finset.Ioc N M, (1 - (2 : ℝ) ^ (-(β * m))) ^ (2 : ℝ) ^ (α * m) := by
  rcases exists_threshold_restrictions_tail hαβ hβ with ⟨N, hN⟩
  use N
  intro M
  by_cases hNM : N < M
  · have h_Ico_Ioc : Finset.Ioc N M = Finset.Ico (N + 1) (M + 1) := by
      ext x
      simp only [Finset.mem_Ioc, Finset.mem_Ico]
      omega
    rw [h_Ico_Ioc]
    have h_sum_le_tail : ∑ m ∈ Finset.Ico (N + 1) (M + 1), (2 : ℝ) ^ (α * (m : ℝ)) * (2 : ℝ) ^ (-(β
        * (m : ℝ))) ≤ 1 - (2 : ℝ) ^ (β - 1) := 
      exists_threshold_restrictions_sum_comp hα hαβ N M hNM hN
    have h1 : 1 - ∑ m ∈ Finset.Ico (N + 1) (M + 1), (2 : ℝ) ^ (α * (m : ℝ)) * (2 : ℝ) ^ (-(β * (m :
        ℝ))) ≤ 
              ∏ m ∈ Finset.Ico (N + 1) (M + 1), (1 - (2 : ℝ) ^ (-(β * (m : ℝ)))) ^ ((2 : ℝ) ^ (α *
                  (m : ℝ))) := by
      apply exists_threshold_restrictions_bernoulli_prod
      · intro m _hm
        apply Real.rpow_nonneg
        linarith
      · intro m _hm
        apply Real.rpow_le_one_of_one_le_of_nonpos
        · linarith
        · have hm0 : 0 ≤ m := by omega
          have hm0_real : 0 ≤ (m : ℝ) := by exact_mod_cast hm0
          have h_mul_nonneg : 0 ≤ β * (m : ℝ) := mul_nonneg (by linarith) hm0_real
          linarith
      · intro m hm
        apply Real.rpow_nonneg
        linarith
      · intro m hm
        have h_m : 1 ≤ m := by
          have hm1 : N + 1 ≤ m := Finset.mem_Ico.1 hm |>.1
          omega
        have _h_m_real : 1 ≤ (m : ℝ) := by exact_mod_cast h_m
        have h_pow_bound : (2 : ℝ) ^ (0 : ℝ) ≤ (2 : ℝ) ^ (α * (m : ℝ)) := by
          apply Real.rpow_le_rpow_of_exponent_le
          · linarith
          · have h_mul_nonneg : 0 ≤ α * (m : ℝ) := mul_nonneg (by linarith) (by positivity)
            exact h_mul_nonneg
        rw [Real.rpow_zero] at h_pow_bound
        exact h_pow_bound
      · have h_tsum_le_one : ∑ m ∈ Finset.Ico (N + 1) (M + 1), (2 : ℝ) ^ (α * (m : ℝ)) * (2 : ℝ) ^
          (-(β * (m : ℝ))) ≤ 1 := by
          calc ∑ m ∈ Finset.Ico (N + 1) (M + 1), (2 : ℝ) ^ (α * (m : ℝ)) * (2 : ℝ) ^ (-(β * (m :
              ℝ)))
            _ ≤ 1 - (2 : ℝ) ^ (β - 1) := h_sum_le_tail
            _ ≤ 1 := by
              have h_pow_nonneg : 0 ≤ (2 : ℝ) ^ (β - 1) := Real.rpow_nonneg (by linarith) _
              linarith
        exact h_tsum_le_one
    have h2 : (2 : ℝ) ^ (β - 1) ≤ 1 - ∑ m ∈ Finset.Ico (N + 1) (M + 1), (2 : ℝ) ^ (α * (m : ℝ)) * (2
        : ℝ) ^ (-(β * (m : ℝ))) := by
      linarith
    linarith
  · push Not at hNM
    have h_Ioc_empty : Finset.Ioc N M = ∅ := by
      apply Finset.Ioc_eq_empty
      linarith
    rw [h_Ioc_empty]
    simp only [Finset.prod_empty]
    have h_beta_minus_one : β - 1 < 0 := by linarith
    have h_2_pow_lt_1 : (2 : ℝ) ^ (β - 1) ≤ 1 := by
      apply le_of_lt
      rw [Real.rpow_lt_one_iff_of_pos zero_lt_two]
      left
      exact ⟨by norm_num, h_beta_minus_one⟩
    exact h_2_pow_lt_1

end Kolmogorov.Applications
