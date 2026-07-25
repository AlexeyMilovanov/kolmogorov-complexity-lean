import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Greedy running-window version count (Vereshchagin–Vitányi core)

This module isolates the purely combinatorial heart of the Vereshchagin–Vitányi
finite greedy-window construction used for the Section 3 arbitrary-curve
realization theorem (`stat-any-curve`).

We model the finite deletion process abstractly, over an arbitrary finite ground
set `G : Finset α`.  A *running window* of size `W` is maintained: as deletions
`d₀, d₁, …` arrive (each merged into the accumulated `deleted` set), whenever the
current window is fully deleted it is *refreshed* to a fresh block
`first (G \ deleted)` of the still-undeleted elements, and a refresh counter is
incremented.

The key quantitative fact (`fold_count_mul_le` / `fold_count_le`) is that, as long
as there is always room for a full window (final `deleted.card + W ≤ G.card`), the
number of refreshes is at most `deleted.card / W`.  This is exactly the
"version count" bound: successive refreshed windows are pairwise disjoint blocks of
`W` freshly-deleted elements, so `count · W ≤ deleted.card`.

The `first` window selector is kept abstract (any function returning a size-`min W`
sub-block); the concrete Section 3 instance sorts length-`n` strings by a canonical
`ℕ` encoding.
-/

namespace Kolmogorov.GreedyWindow

variable {α : Type*} [DecidableEq α]

/-- One step of the greedy running-window process over a finite ground set `G`
with window size `W` (implicit through `first`) and window selector `first`.

The state is `(deleted, window, count)`:
* `deleted` — the accumulated deleted set,
* `window`  — the current running window,
* `count`   — the number of refreshes performed so far.

A new deletion `d` is merged into `deleted` (intersected with `G`); if that empties
the current window (`window ⊆ deleted`), the window is refreshed to a fresh block
`first (G \ deleted)` of undeleted elements and `count` is incremented. -/
def step (G : Finset α) (first : Finset α → Finset α)
    (st : Finset α × Finset α × ℕ) (d : Finset α) : Finset α × Finset α × ℕ :=
  let deleted := st.1 ∪ (d ∩ G)
  if st.2.1 ⊆ deleted then (deleted, first (G \ deleted), st.2.2 + 1)
  else (deleted, st.2.1, st.2.2)

/-- The greedy running-window fold: process the whole list `L` of deletions starting
from an empty deleted set and the initial window `first G`. -/
def fold (G : Finset α) (first : Finset α → Finset α) (L : List (Finset α)) :
    Finset α × Finset α × ℕ :=
  L.foldl (step G first) (∅, first G, 0)

/-- A concrete window selector: the `W` elements of `S` with smallest `key` value.
This is the canonical instance of the abstract selector required by
`fold_count_mul_le`: it satisfies both `firstBlock_subset` and `firstBlock_card`
for *any* key function (the cardinality spec needs no injectivity, since sorting a
`Finset`'s underlying `Nodup` list preserves nodup-ness and truncation preserves
lengths). -/
noncomputable def firstBlock (key : α → ℕ) (W : ℕ) (S : Finset α) : Finset α :=
  ((S.toList.mergeSort (fun a b => decide (key a ≤ key b))).take W).toFinset

theorem firstBlock_subset (key : α → ℕ) (W : ℕ) (S : Finset α) :
    firstBlock key W S ⊆ S := by
  intro x hx
  rw [firstBlock, List.mem_toFinset] at hx
  have hx' : x ∈ S.toList.mergeSort (fun a b => decide (key a ≤ key b)) :=
    List.take_subset _ _ hx
  rw [List.mem_mergeSort] at hx'
  simpa using hx'

/-- `firstBlock` is monotone in the window size: a smaller block is contained in a
larger one (both are prefixes of the same sorted list). -/
theorem firstBlock_mono_size (key : α → ℕ) {m W : ℕ} (hmW : m ≤ W) (S : Finset α) :
    firstBlock key m S ⊆ firstBlock key W S := by
  intro x hx
  rw [firstBlock, List.mem_toFinset] at hx ⊢
  exact (List.take_prefix_take_left hmW).subset hx

theorem firstBlock_card (key : α → ℕ) (W : ℕ) (S : Finset α) :
    (firstBlock key W S).card = min W S.card := by
  have hnodup_sort : (S.toList.mergeSort (fun a b => decide (key a ≤ key b))).Nodup :=
    (List.mergeSort_perm _ _).symm.nodup S.nodup_toList
  have hnodup_take :
      ((S.toList.mergeSort (fun a b => decide (key a ≤ key b))).take W).Nodup :=
    (List.take_sublist W _).nodup hnodup_sort
  rw [firstBlock, List.toFinset_card_of_nodup hnodup_take, List.length_take,
    (List.mergeSort_perm _ _).length_eq, Finset.length_toList]

/-- Value of the deleted component after one step (it is always `st.1 ∪ (d ∩ G)`). -/
theorem step_deleted_eq (G : Finset α) (first : Finset α → Finset α)
    (st : Finset α × Finset α × ℕ) (d : Finset α) :
    (step G first st d).1 = st.1 ∪ (d ∩ G) := by
  unfold step
  by_cases h : st.2.1 ⊆ st.1 ∪ (d ∩ G) <;> simp only [h, if_true, if_false]

/-- The deleted component is always a subset of the ground set. -/
theorem step_deleted_subset (G : Finset α) (first : Finset α → Finset α)
    (st : Finset α × Finset α × ℕ) (hst : st.1 ⊆ G) (d : Finset α) :
    (step G first st d).1 ⊆ G := by
  rw [step_deleted_eq]
  exact Finset.union_subset hst Finset.inter_subset_right

/-- The deleted component only grows through one step. -/
theorem step_deleted_mono (G : Finset α) (first : Finset α → Finset α)
    (st : Finset α × Finset α × ℕ) (d : Finset α) :
    st.1 ⊆ (step G first st d).1 := by
  rw [step_deleted_eq]
  exact Finset.subset_union_left

/-- Monotonicity of the deleted component along a `foldl`. -/
theorem foldl_deleted_mono (G : Finset α) (first : Finset α → Finset α)
    (L : List (Finset α)) (st : Finset α × Finset α × ℕ) :
    st.1 ⊆ (L.foldl (step G first) st).1 := by
  induction L generalizing st with
  | nil => simp
  | cons d L ih =>
    simp only [List.foldl_cons]
    exact (step_deleted_mono G first st d).trans (ih (step G first st d))

/-- Cardinal subadditivity for the part of one set lying in a binary union. -/
theorem card_inter_union_le (A B C : Finset α) :
    (A ∩ (B ∪ C)).card ≤ (A ∩ B).card + (A ∩ C).card := by
  have hsub : A ∩ (B ∪ C) ⊆ (A ∩ B) ∪ (A ∩ C) := by
    intro x hx
    simp only [Finset.mem_inter, Finset.mem_union] at hx ⊢
    rcases hx with ⟨hxA, hxB | hxC⟩
    · exact Or.inl ⟨hxA, hxB⟩
    · exact Or.inr ⟨hxA, hxC⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

/-- Cardinal subadditivity with an external bound on the right-hand intersection. -/
theorem card_inter_union_le_add_bound (A B C : Finset α) {n : ℕ}
    (hC : (A ∩ C).card ≤ n) :
    (A ∩ (B ∪ C)).card ≤ (A ∩ B).card + n :=
  (card_inter_union_le A B C).trans (Nat.add_le_add_left hC _)

/-- Split-credit accounting after exposing the head deletion. -/
theorem splitCredit_cons (G : Finset α) (W c : ℕ) (p : Finset α → Bool)
    (d : Finset α) (L : List (Finset α)) :
    c + ((d :: L).filter p).length * W +
        (((d :: L).filter (fun d => !p d)).map (fun d => (d ∩ G).card)).sum
      = (c + (if p d then W else 0) + (if !p d then (d ∩ G).card else 0)) +
          (L.filter p).length * W +
          ((L.filter (fun d => !p d)).map (fun d => (d ∩ G).card)).sum := by
  by_cases hd : p d <;>
    simp [hd, List.length_cons, List.map_cons, List.sum_cons] <;> ring

/-- If every deletion, restricted to `G`, lands inside a fixed set `D`, then the
accumulated deleted component of the fold stays inside `D`. -/
theorem fold_deleted_subset (G : Finset α) (first : Finset α → Finset α)
    (L : List (Finset α)) (D : Finset α) (hD : ∀ d ∈ L, d ∩ G ⊆ D) :
    (fold G first L).1 ⊆ D := by
  have gen : ∀ (M : List (Finset α)) (st : Finset α × Finset α × ℕ),
      st.1 ⊆ D → (∀ d ∈ M, d ∩ G ⊆ D) → (M.foldl (step G first) st).1 ⊆ D := by
    intro M
    induction M with
    | nil => intro st hst _; simpa using hst
    | cons d M ih =>
      intro st hst hM
      simp only [List.foldl_cons]
      refine ih (step G first st d) ?_ (fun d' hd' => hM d' (List.mem_cons_of_mem _ hd'))
      rw [step_deleted_eq]
      exact Finset.union_subset hst (hM d (by simp))
  exact gen L (∅, first G, 0) (by simp) hD

/-- A covered deletion leaves the running-window state unchanged, provided the window is not
already a subset of the deleted set. -/
theorem step_eq_of_covered_of_not_subset (G : Finset α) (first : Finset α → Finset α)
    (st : Finset α × Finset α × ℕ) (d : Finset α)
    (h_cov : d ∩ G ⊆ st.1) (h_not_sub : ¬(st.2.1 ⊆ st.1)) :
    step G first st d = st := by
  unfold step
  have h_union : st.1 ∪ (d ∩ G) = st.1 := Finset.union_eq_left.mpr h_cov
  rw [h_union]
  simp only [h_not_sub, if_false]

/-- **Version-count bound (multiplicative form).**  If every window along the process
is a *full* block of size `W` — guaranteed here by the room hypothesis
`(fold G first L).1.card + W ≤ G.card` together with the selector spec — then the
number of refreshes times `W` is at most the size of the final deleted set:
successive refreshed windows are pairwise-disjoint blocks of `W` freshly deleted
elements. -/
theorem fold_count_mul_le
    (G : Finset α) (W : ℕ) (first : Finset α → Finset α)
    (hsub : ∀ S : Finset α, first S ⊆ S)
    (hcard : ∀ S : Finset α, (first S).card = min W S.card)
    (L : List (Finset α))
    (hroom : (fold G first L).1.card + W ≤ G.card) :
    (fold G first L).2.2 * W ≤ (fold G first L).1.card := by
  -- Invariant carried along the fold.  `P` is the (pairwise-disjoint) union of the
  -- windows abandoned so far; it accounts for `count · W` deleted elements, and the
  -- current window is a full block of size `W` disjoint from `P`.
  set INV := fun (st : Finset α × Finset α × ℕ) =>
    ∃ P : Finset α, P ⊆ st.1 ∧ Disjoint st.2.1 P ∧ st.2.2 * W ≤ P.card ∧
      st.1 ⊆ G ∧ st.2.1 ⊆ G ∧ st.2.1.card = W with hINV
  have h_inv : ∀ (L : List (Finset α)) (st : Finset α × Finset α × ℕ), INV st →
      (L.foldl (step G first) st).1.card + W ≤ G.card →
      INV (L.foldl (step G first) st) := by
    intro L
    induction L with
    | nil => intro st hst _; simpa using hst
    | cons d L ih =>
      intro st hst hroom
      simp only [List.foldl_cons] at hroom ⊢
      apply ih
      · rw [hINV] at hst ⊢
        obtain ⟨P, hP₁, hP₂, hP₃, hP₄, hP₅, hP₆⟩ := hst
        have he : (step G first st d).1 = st.1 ∪ (d ∩ G) := step_deleted_eq G first st d
        have hmono : (st.1 ∪ (d ∩ G)) ⊆ (L.foldl (step G first) (step G first st d)).1 := by
          have h1 := foldl_deleted_mono G first L (step G first st d); rwa [he] at h1
        have hsubG : (st.1 ∪ (d ∩ G)) ⊆ G := by
          have h2 := step_deleted_subset G first st hP₄ d; rwa [he] at h2
        have hcardle : (st.1 ∪ (d ∩ G)).card + W ≤ G.card :=
          le_trans (Nat.add_le_add_right (Finset.card_le_card hmono) W) hroom
        have hcard_eq : (G \ (st.1 ∪ (d ∩ G))).card + (st.1 ∪ (d ∩ G)).card = G.card :=
          Finset.card_sdiff_add_card_eq_card hsubG
        have hwin : W ≤ (G \ (st.1 ∪ (d ∩ G))).card := by omega
        by_cases h : st.2.1 ⊆ st.1 ∪ (d ∩ G)
        · -- refresh: the current window is fully deleted and is abandoned into `P`.
          have hPunion : (P ∪ st.2.1) ⊆ st.1 ∪ (d ∩ G) :=
            Finset.union_subset (hP₁.trans Finset.subset_union_left) h
          simp only [step, if_pos h]
          refine ⟨P ∪ st.2.1, hPunion, ?_, ?_, hsubG,
            (hsub _).trans Finset.sdiff_subset, ?_⟩
          · exact Finset.disjoint_of_subset_left (hsub _)
              (Finset.disjoint_of_subset_right hPunion Finset.sdiff_disjoint)
          · rw [Finset.card_union_of_disjoint hP₂.symm, Nat.succ_mul, hP₆]
            exact Nat.add_le_add_right hP₃ W
          · rw [hcard, min_eq_left hwin]
        · -- no refresh: state's deleted grows, window and count unchanged.
          simp only [step, if_neg h]
          exact ⟨P, hP₁.trans Finset.subset_union_left, hP₂, hP₃, hsubG, hP₅, hP₆⟩
      · exact hroom
  -- Initial invariant and conclusion.
  have hinit : INV (∅, first G, 0) := by
    rw [hINV]
    refine ⟨∅, Finset.empty_subset _, Finset.disjoint_empty_right _, by simp,
      Finset.empty_subset _, hsub G, ?_⟩
    rw [hcard, min_eq_left (le_trans (Nat.le_add_left W _) hroom)]
  have hroom' : (L.foldl (step G first) (∅, first G, 0)).1.card + W ≤ G.card := hroom
  have hfin := h_inv L (∅, first G, 0) hinit hroom'
  rw [hINV] at hfin
  obtain ⟨P, hP₁, -, hP₃, -, -, -⟩ := hfin
  exact hP₃.trans (Finset.card_le_card hP₁)

/-- **Version-count bound (division form).**  Under the room hypothesis, the number of
refreshes is at most `deleted.card / W`. -/
theorem fold_count_le
    (G : Finset α) (W : ℕ) (hW : 0 < W) (first : Finset α → Finset α)
    (hsub : ∀ S : Finset α, first S ⊆ S)
    (hcard : ∀ S : Finset α, (first S).card = min W S.card)
    (L : List (Finset α))
    (hroom : (fold G first L).1.card + W ≤ G.card) :
    (fold G first L).2.2 ≤ (fold G first L).1.card / W := by
  rw [Nat.le_div_iff_mul_le hW]
  exact fold_count_mul_le G W first hsub hcard L hroom

/-- **Version-count bound (survivor multiplicative form).**
If the final survivor set is nonempty, then no abandoned window was created in the
low-survivor regime, so every abandoned window was full. Thus the version count times W
is bounded by the final deleted set. -/
theorem fold_count_mul_le_of_survivor
    (G : Finset α) (W : ℕ) (first : Finset α → Finset α)
    (hsub : ∀ S : Finset α, first S ⊆ S)
    (hcard : ∀ S : Finset α, (first S).card = min W S.card)
    (L : List (Finset α))
    (hsurv : (G \ (fold G first L).1).Nonempty) :
    (fold G first L).2.2 * W ≤ (fold G first L).1.card := by
  set INV := fun (st : Finset α × Finset α × ℕ) =>
    ∃ P : Finset α, P ⊆ st.1 ∧ Disjoint st.2.1 P ∧ st.2.2 * W ≤ P.card ∧
      st.1 ⊆ G ∧ st.2.1 ⊆ G ∧
      (st.2.1.card = W ∨ ∃ D ⊆ st.1, st.2.1 = G \ D) with hINV
  have h_inv : ∀ (L' : List (Finset α)) (st : Finset α × Finset α × ℕ), INV st →
      st.1 ⊆ (L'.foldl (step G first) st).1 →
      (G \ (L'.foldl (step G first) st).1).Nonempty →
      INV (L'.foldl (step G first) st) := by
    intro L'
    induction L' with
    | nil => intro st hst _ _; simpa using hst
    | cons d L' ih =>
      intro st hst hmono hsurv_local
      simp only [List.foldl_cons] at hmono hsurv_local ⊢
      apply ih
      · rw [hINV] at hst ⊢
        obtain ⟨P, hP₁, hP₂, hP₃, hP₄, hP₅, hP₆⟩ := hst
        have he : (step G first st d).1 = st.1 ∪ (d ∩ G) := step_deleted_eq G first st d
        have hsubG : (st.1 ∪ (d ∩ G)) ⊆ G := by
          have h2 := step_deleted_subset G first st hP₄ d; rwa [he] at h2
        have h_final_mono : (st.1 ∪ (d ∩ G)) ⊆ (L'.foldl (step G first) (step G first st d)).1 := by
          have h1 := foldl_deleted_mono G first L' (step G first st d); rwa [he] at h1
        by_cases h : st.2.1 ⊆ st.1 ∪ (d ∩ G)
        · -- refresh
          have hw : st.2.1.card = W := by
            rcases hP₆ with hw' | ⟨D, hD₁, hD₂⟩
            · exact hw'
            · exfalso
              have hG : G ⊆ st.1 ∪ (d ∩ G) := by
                have h1 : G \ D ⊆ st.1 ∪ (d ∩ G) := by rw [← hD₂]; exact h
                intro x hx
                by_cases hxD : x ∈ D
                · exact Finset.subset_union_left (hD₁ hxD)
                · exact h1 (Finset.mem_sdiff.mpr ⟨hx, hxD⟩)
              have h_empty : G \ (L'.foldl (step G first) (step G first st d)).1 = ∅ := by
                refine Finset.sdiff_eq_empty_iff_subset.mpr ?_
                exact Finset.Subset.trans hG h_final_mono
              rw [h_empty] at hsurv_local
              exact Finset.not_nonempty_empty hsurv_local
          have hPunion : (P ∪ st.2.1) ⊆ st.1 ∪ (d ∩ G) :=
            Finset.union_subset (hP₁.trans Finset.subset_union_left) h
          simp only [step, if_pos h]
          refine ⟨P ∪ st.2.1, hPunion, ?_, ?_, hsubG, (hsub _).trans Finset.sdiff_subset, ?_⟩
          · exact Finset.disjoint_of_subset_left (hsub _)
              (Finset.disjoint_of_subset_right hPunion Finset.sdiff_disjoint)
          · rw [Finset.card_union_of_disjoint hP₂.symm, Nat.succ_mul, hw]
            exact Nat.add_le_add_right hP₃ W
          · by_cases hw2 : (first (G \ (st.1 ∪ d ∩ G))).card = W
            · exact Or.inl hw2
            · right
              refine ⟨st.1 ∪ d ∩ G, Finset.Subset.refl _, ?_⟩
              have hc : (first (G \ (st.1 ∪ d ∩ G))).card = min W (G \ (st.1 ∪ d ∩ G)).card :=
                  hcard _
              rw [Nat.min_def] at hc
              split_ifs at hc with hle
              · exact (hw2 hc).elim
              · have hc' : (first (G \ (st.1 ∪ d ∩ G))).card = (G \ (st.1 ∪ d ∩ G)).card := hc
                exact Finset.eq_of_subset_of_card_le (hsub _) hc'.ge
        · -- no refresh
          simp only [step, if_neg h]
          refine ⟨P, hP₁.trans Finset.subset_union_left, hP₂, hP₃, hsubG, hP₅, ?_⟩
          rcases hP₆ with hw | ⟨D, hD₁, hD₂⟩
          · exact Or.inl hw
          · right
            refine ⟨D, hD₁.trans Finset.subset_union_left, hD₂⟩
      · exact foldl_deleted_mono G first L' (step G first st d)
      · exact hsurv_local
  have hinit : INV (∅, first G, 0) := by
    rw [hINV]
    refine ⟨∅, Finset.empty_subset _, Finset.disjoint_empty_right _, by simp,
      Finset.empty_subset _, hsub G, ?_⟩
    have hc : (first G).card = min W G.card := hcard G
    by_cases hw : (first G).card = W
    · exact Or.inl hw
    · right
      refine ⟨∅, Finset.empty_subset _, ?_⟩
      rw [Nat.min_def] at hc
      split_ifs at hc with hle
      · exact (hw hc).elim
      · have hc' : (first G).card = G.card := hc
        exact (Finset.eq_of_subset_of_card_le (hsub G) hc'.ge).trans Finset.sdiff_empty.symm
  have hmono : ∅ ⊆ (L.foldl (step G first) (∅, first G, 0)).1 := Finset.empty_subset _
  have hfin := h_inv L (∅, first G, 0) hinit hmono hsurv
  rw [hINV] at hfin
  obtain ⟨P, hP₁, -, hP₃, -, -, -⟩ := hfin
  exact hP₃.trans (Finset.card_le_card hP₁)

/-- **Version-count bound (survivor division form).** -/
theorem fold_count_le_of_survivor
    (G : Finset α) (W : ℕ) (hW : 0 < W) (first : Finset α → Finset α)
    (hsub : ∀ S : Finset α, first S ⊆ S)
    (hcard : ∀ S : Finset α, (first S).card = min W S.card)
    (L : List (Finset α))
    (hsurv : (G \ (fold G first L).1).Nonempty) :
    (fold G first L).2.2 ≤ (fold G first L).1.card / W := by
  rw [Nat.le_div_iff_mul_le hW]
  exact fold_count_mul_le_of_survivor G W first hsub hcard L hsurv

/-- **Version-count bound (split list form).** We can bound the number of refreshes by
splitting the deletions into two types. Type 1 deletions (where `p d` is true) can
trigger at most one refresh each. Type 2 deletions (where `p d` is false) delete at
most `|d ∩ G|` elements from windows. The total number of refreshes times `W` is
bounded by the number of Type 1 deletions times `W` plus the sum of `|d ∩ G|` for
Type 2 deletions.

The proof refines `fold_count_mul_le` by carrying the same abandoned-window invariant
while charging refreshes either to a type-1 event or to newly deleted type-2 elements.
This is the abstract combinatorial form of the VV two-bucket version-count estimate. -/
theorem fold_count_split_le
    (G : Finset α) (W : ℕ) (first : Finset α → Finset α)
    (hsub : ∀ S : Finset α, first S ⊆ S)
    (hcard : ∀ S : Finset α, (first S).card = min W S.card)
    (L : List (Finset α)) (p : Finset α → Bool)
    (hroom : (fold G first L).1.card + W ≤ G.card) :
    (fold G first L).2.2 * W ≤
      (L.filter p).length * W + ((L.filter (fun d => !p d)).map (fun d => (d ∩ G).card)).sum := by
  have h_inv : ∀ (L : List (Finset α)) (st : Finset α × Finset α × ℕ) (c : ℕ),
      (∃ P : Finset α, P ⊆ st.1 ∧ Disjoint st.2.1 P ∧ st.2.2 * W ≤ P.card ∧
        st.1 ⊆ G ∧ st.2.1 ⊆ G ∧ st.2.1.card = W ∧ P.card + (st.2.1 ∩ st.1).card ≤ c) →
      (L.foldl (step G first) st).1.card + W ≤ G.card →
      (∃ P' : Finset α, P' ⊆ (L.foldl (step G first) st).1 ∧
        Disjoint (L.foldl (step G first) st).2.1 P' ∧
        (L.foldl (step G first) st).2.2 * W ≤ P'.card ∧
        (L.foldl (step G first) st).1 ⊆ G ∧ (L.foldl (step G first) st).2.1 ⊆ G ∧
        (L.foldl (step G first) st).2.1.card = W ∧
        P'.card + ((L.foldl (step G first) st).2.1 ∩ (L.foldl (step G first) st).1).card ≤
          c + (L.filter p).length * W +
            ((L.filter (fun d => !p d)).map (fun d => (d ∩ G).card)).sum) := by
    intro L
    induction L with
    | nil => intro st c hP _; simpa using hP
    | cons d L ih =>
      intro st c hP hroom
      obtain ⟨P, hP₁, hP₂, hP₃, hP₄, hP₅, hP₆, hP₇⟩ := hP
      have h_step : ∃ P' : Finset α, P' ⊆ (step G first st d).1 ∧
          Disjoint (step G first st d).2.1 P' ∧ (step G first st d).2.2 * W ≤ P'.card ∧
          (step G first st d).1 ⊆ G ∧ (step G first st d).2.1 ⊆ G ∧
          (step G first st d).2.1.card = W ∧
          P'.card + ((step G first st d).2.1 ∩ (step G first st d).1).card ≤
            c + (if p d then W else 0) + (if !p d then (d ∩ G).card else 0) := by
        by_cases h : st.2.1 ⊆ st.1 ∪ ( d ∩ G )
        · have hroom' := hroom
          simp only [List.foldl_cons] at hroom'
          simp only [step, if_pos h] at hroom' ⊢
          refine ⟨ P ∪ st.2.1, ?_, ?_, ?_, ?_, ?_, ?_ ⟩
          · exact Finset.union_subset (Finset.Subset.trans hP₁ Finset.subset_union_left) h
          · simp only [Finset.disjoint_left]
            intro a ha₁ ha₂
            have ha_diff := hsub _ ha₁
            have ha_in : a ∈ st.1 ∪ d ∩ G := by
              rw [Finset.mem_union] at ha₂
              cases ha₂ with
              | inl h1 => exact Finset.mem_union_left _ (hP₁ h1)
              | inr h2 => exact h h2
            exact Finset.disjoint_left.mp Finset.sdiff_disjoint ha_diff ha_in
          · rw [Finset.card_union_of_disjoint hP₂.symm]
            linarith
          · exact Finset.union_subset hP₄ Finset.inter_subset_right
          · exact Finset.Subset.trans (hsub _) Finset.sdiff_subset
          · constructor
            · have h_card_min : (first (G \ (st.1 ∪ d ∩ G))).card =
                  min W (G \ (st.1 ∪ d ∩ G)).card := hcard _
              have h_card_foldl :
                  (List.foldl (step G first)
                    (st.1 ∪ d ∩ G, first (G \ (st.1 ∪ d ∩ G)), st.2.2 + 1) L).1.card ≥
                    (st.1 ∪ d ∩ G).card :=
                Finset.card_le_card (foldl_deleted_mono G first L
                  (st.1 ∪ d ∩ G, first (G \ (st.1 ∪ d ∩ G)), st.2.2 + 1))
              have h_sub_G : st.1 ∪ d ∩ G ⊆ G := Finset.union_subset hP₄ Finset.inter_subset_right
              have h_card_sdiff : (G \ (st.1 ∪ d ∩ G)).card =
                  G.card - (st.1 ∪ d ∩ G).card :=
                Finset.card_sdiff_of_subset h_sub_G
              rw [h_card_min, min_eq_left (by omega)]
            · have h_inter_zero : (first (G \ (st.1 ∪ d ∩ G)) ∩ (st.1 ∪ d ∩ G)).card = 0 := by
                apply Finset.card_eq_zero.mpr
                exact Finset.disjoint_iff_inter_eq_empty.mp
                  (Finset.disjoint_of_subset_left (hsub _) Finset.sdiff_disjoint)
              rw [h_inter_zero]
              have h_card_P : (P ∪ st.2.1).card = P.card + W := by
                rw [Finset.card_union_of_disjoint hP₂.symm, hP₆]
              rw [h_card_P]
              by_cases hp : p d
              · have h_rhs : c + (if p d then W else 0) +
                    (if !p d then (d ∩ G).card else 0) = c + W := by simp [hp]
                rw [h_rhs]
                linarith
              · have hp_false : p d = false := eq_false_of_ne_true hp
                have h_rhs : c + (if p d then W else 0) +
                    (if !p d then (d ∩ G).card else 0) = c + (d ∩ G).card := by
                  simp [hp_false]
                rw [h_rhs]
                have h_union := card_inter_union_le_add_bound st.2.1 st.1 (d ∩ G)
                  (Finset.card_le_card Finset.inter_subset_right)
                rw [Finset.inter_eq_left.mpr h, hP₆] at h_union
                linarith
        · simp only [step, if_neg h] at hroom ⊢
          refine ⟨ P, ?_, ?_, ?_, ?_, ?_, ?_, ?_ ⟩
          · exact Finset.Subset.trans hP₁ Finset.subset_union_left
          · exact hP₂
          · exact hP₃
          · exact Finset.union_subset hP₄ Finset.inter_subset_right
          · exact hP₅
          · exact hP₆
          · by_cases hp : p d
            · have hdel : (st.2.1 ∩ (d ∩ G)).card ≤ W :=
                le_trans (Finset.card_le_card Finset.inter_subset_left) hP₆.le
              have hnew :
                  (st.2.1 ∩ (st.1 ∪ d ∩ G)).card ≤
                    (st.2.1 ∩ st.1).card + W :=
                card_inter_union_le_add_bound _ _ _ hdel
              have h_rhs : c + (if p d then W else 0) +
                  (if !p d then (d ∩ G).card else 0) = c + W := by simp [hp]
              rw [h_rhs]
              omega
            · have hdel : (st.2.1 ∩ (d ∩ G)).card ≤ (d ∩ G).card :=
                Finset.card_le_card Finset.inter_subset_right
              have hnew :
                  (st.2.1 ∩ (st.1 ∪ d ∩ G)).card ≤
                    (st.2.1 ∩ st.1).card + (d ∩ G).card :=
                card_inter_union_le_add_bound _ _ _ hdel
              have hp_false : p d = false := eq_false_of_ne_true hp
              have h_rhs : c + (if p d then W else 0) +
                  (if !p d then (d ∩ G).card else 0) = c + (d ∩ G).card := by
                simp [hp_false]
              rw [h_rhs]
              omega
      have hcredit :
          c + ((d :: L).filter p).length * W +
              (((d :: L).filter (fun d => !p d)).map (fun d => (d ∩ G).card)).sum
            = (c + (if p d then W else 0) + (if !p d then (d ∩ G).card else 0)) +
                (L.filter p).length * W +
                ((L.filter (fun d => !p d)).map (fun d => (d ∩ G).card)).sum :=
        splitCredit_cons G W c p d L
      simp only [List.foldl_cons] at hroom ⊢
      rw [hcredit]
      exact ih (step G first st d)
        (c + (if p d then W else 0) + (if !p d then (d ∩ G).card else 0)) h_step hroom
  have hWleG : W ≤ G.card :=
    (Nat.le_add_left W (fold G first L).1.card).trans (by simpa [Nat.add_comm] using hroom)
  have hinit : ∃ P : Finset α, P ⊆ ∅ ∧ Disjoint (first G) P ∧ 0 * W ≤ P.card ∧
      ∅ ⊆ G ∧ first G ⊆ G ∧ (first G).card = W ∧ P.card + (first G ∩ ∅).card ≤ 0 := by
    refine ⟨∅, Finset.empty_subset _, Finset.disjoint_empty_right _, by simp,
      Finset.empty_subset _, hsub G, ?_, by simp⟩
    rw [hcard, min_eq_left hWleG]
  have hfin := h_inv L (∅, first G, 0) 0 hinit (by simpa [fold] using hroom)
  obtain ⟨P, -, -, hP_count, -, -, -, hP_credit⟩ := hfin
  have hP_le_credit :
      P.card ≤ (L.filter p).length * W +
          ((L.filter (fun d => !p d)).map (fun d => (d ∩ G).card)).sum := by
    exact (Nat.le_add_right P.card _).trans (by simpa using hP_credit)
  exact hP_count.trans hP_le_credit

/-- **Version-count bound (split division form).**  The division-form companion of
`fold_count_split_le`, mirroring how `fold_count_le` sharpens `fold_count_mul_le`.
Dividing the `count · W ≤ …` estimate through by the window size `W`, the number of
refreshes is bounded by the number of type-1 deletions (each triggering at most one
refresh) plus the total type-2 deletion mass divided by `W`.  This is exactly the
Vereshchagin–Vitányi two-bucket version-count estimate in the form the concrete
Section 3 gate `greedyWindow_version_count_le` consumes: bucket 1 is the count of
low-complexity ("small") sets, bucket 2 is the deletion mass of the higher levels
divided by the window size. -/
theorem fold_count_split_div_le
    (G : Finset α) (W : ℕ) (hW : 0 < W) (first : Finset α → Finset α)
    (hsub : ∀ S : Finset α, first S ⊆ S)
    (hcard : ∀ S : Finset α, (first S).card = min W S.card)
    (L : List (Finset α)) (p : Finset α → Bool)
    (hroom : (fold G first L).1.card + W ≤ G.card) :
    (fold G first L).2.2 ≤
      (L.filter p).length +
        ((L.filter (fun d => !p d)).map (fun d => (d ∩ G).card)).sum / W := by
  have h := fold_count_split_le G W first hsub hcard L p hroom
  rw [mul_comm ((L.filter p).length) W] at h
  calc (fold G first L).2.2
      ≤ (W * (L.filter p).length +
          ((L.filter (fun d => !p d)).map (fun d => (d ∩ G).card)).sum) / W :=
        (Nat.le_div_iff_mul_le hW).mpr h
    _ = (L.filter p).length +
          ((L.filter (fun d => !p d)).map (fun d => (d ∩ G).card)).sum / W :=
        Nat.mul_add_div hW _ _

theorem fold_count_split_le_of_survivor
    (G : Finset α) (W : ℕ) (first : Finset α → Finset α)
    (hsub : ∀ S : Finset α, first S ⊆ S)
    (hcard : ∀ S : Finset α, (first S).card = min W S.card)
    (L : List (Finset α)) (p : Finset α → Bool)
    (hsurv : (G \ (fold G first L).1).Nonempty) :
    (fold G first L).2.2 * W ≤
      (L.filter p).length * W + ((L.filter (fun d => !p d)).map (fun d => (d ∩ G).card)).sum := by
  have h_inv : ∀ (L' : List (Finset α)) (st : Finset α × Finset α × ℕ) (c : ℕ),
      (∃ P : Finset α, P ⊆ st.1 ∧ Disjoint st.2.1 P ∧ st.2.2 * W ≤ P.card ∧
        st.1 ⊆ G ∧ st.2.1 ⊆ G ∧
        (st.2.1.card = W ∨ ∃ D ⊆ st.1, st.2.1 = G \ D ∧ st.2.1.card ≤ W) ∧
        P.card + (st.2.1 ∩ st.1).card ≤ c) →
      st.1 ⊆ (L'.foldl (step G first) st).1 →
      (G \ (L'.foldl (step G first) st).1).Nonempty →
      (∃ P' : Finset α, P' ⊆ (L'.foldl (step G first) st).1 ∧
        Disjoint (L'.foldl (step G first) st).2.1 P' ∧
        (L'.foldl (step G first) st).2.2 * W ≤ P'.card ∧
        (L'.foldl (step G first) st).1 ⊆ G ∧ (L'.foldl (step G first) st).2.1 ⊆ G ∧
        ((L'.foldl (step G first) st).2.1.card = W ∨ ∃ D ⊆ (L'.foldl (step G first) st).1,
            (L'.foldl (step G first) st).2.1 = G \ D ∧ (L'.foldl (step G first) st).2.1.card ≤ W) ∧
        P'.card + ((L'.foldl (step G first) st).2.1 ∩ (L'.foldl (step G first) st).1).card ≤
          c + (L'.filter p).length * W +
            ((L'.filter (fun d => !p d)).map (fun d => (d ∩ G).card)).sum) := by
    intro L'
    induction L' with
    | nil =>
      intro st c hst _ _
      simpa using hst
    | cons d L' ih =>
      intro st c hst hmono hsurv_local
      simp only [List.foldl_cons] at hmono hsurv_local ⊢
      obtain ⟨P, hP₁, hP₂, hP₃, hP₄, hP₅, hP₆, hP₇⟩ := hst
      have he : (step G first st d).1 = st.1 ∪ (d ∩ G) := step_deleted_eq G first st d
      have hsubG : (st.1 ∪ (d ∩ G)) ⊆ G := by
        have h2 := step_deleted_subset G first st hP₄ d; rwa [he] at h2
      have h_final_mono : (st.1 ∪ (d ∩ G)) ⊆ (L'.foldl (step G first) (step G first st d)).1 := by
        have h1 := foldl_deleted_mono G first L' (step G first st d); rwa [he] at h1
      have h_step : ∃ P' : Finset α, P' ⊆ (step G first st d).1 ∧
          Disjoint (step G first st d).2.1 P' ∧ (step G first st d).2.2 * W ≤ P'.card ∧
          (step G first st d).1 ⊆ G ∧ (step G first st d).2.1 ⊆ G ∧
          ((step G first st d).2.1.card = W ∨ ∃ D ⊆ (step G first st d).1,
              (step G first st d).2.1 = G \ D ∧ (step G first st d).2.1.card ≤ W) ∧
          P'.card + ((step G first st d).2.1 ∩ (step G first st d).1).card ≤
            c + (if p d then W else 0) + (if !p d then (d ∩ G).card else 0) := by
        by_cases h : st.2.1 ⊆ st.1 ∪ (d ∩ G)
        · -- refresh
          have hw : st.2.1.card = W := by
            rcases hP₆ with hw' | ⟨D, hD₁, hD₂, -⟩
            · exact hw'
            · exfalso
              have hG : G ⊆ st.1 ∪ (d ∩ G) := by
                have h1 : G \ D ⊆ st.1 ∪ (d ∩ G) := by rw [← hD₂]; exact h
                intro x hx
                by_cases hxD : x ∈ D
                · exact Finset.subset_union_left (hD₁ hxD)
                · exact h1 (Finset.mem_sdiff.mpr ⟨hx, hxD⟩)
              have h_empty : G \ (L'.foldl (step G first) (step G first st d)).1 = ∅ := by
                refine Finset.sdiff_eq_empty_iff_subset.mpr ?_
                exact Finset.Subset.trans hG h_final_mono
              rw [h_empty] at hsurv_local
              exact Finset.not_nonempty_empty hsurv_local
          have hPunion : (P ∪ st.2.1) ⊆ st.1 ∪ (d ∩ G) :=
            Finset.union_subset (hP₁.trans Finset.subset_union_left) h
          simp only [step, if_pos h]
          refine ⟨P ∪ st.2.1, hPunion, ?_, ?_, hsubG, (hsub _).trans Finset.sdiff_subset, ?_, ?_⟩
          · exact Finset.disjoint_of_subset_left (hsub _)
              (Finset.disjoint_of_subset_right hPunion Finset.sdiff_disjoint)
          · rw [Finset.card_union_of_disjoint hP₂.symm, Nat.succ_mul, hw]
            exact Nat.add_le_add_right hP₃ W
          · by_cases hw2 : (first (G \ (st.1 ∪ d ∩ G))).card = W
            · exact Or.inl hw2
            · right
              refine ⟨st.1 ∪ d ∩ G, Finset.Subset.refl _, ?_⟩
              have hc : (first (G \ (st.1 ∪ d ∩ G))).card = min W (G \ (st.1 ∪ d ∩ G)).card :=
                  hcard _
              rw [Nat.min_def] at hc
              split_ifs at hc with hle
              · exact (hw2 hc).elim
              · have hc' : (first (G \ (st.1 ∪ d ∩ G))).card = (G \ (st.1 ∪ d ∩ G)).card := hc
                exact ⟨Finset.eq_of_subset_of_card_le (hsub _) hc'.ge, by linarith⟩
          · have h_card : (first (G \ (st.1 ∪ d ∩ G)) ∩ (st.1 ∪ d ∩ G)).card = 0 := by
              simp +decide [Finset.ext_iff]
              grind
            have h_P_card : (P ∪ st.2.1).card = P.card + W := by
              rw [Finset.card_union_of_disjoint hP₂.symm, hw]
            rw [h_card, add_zero, h_P_card]
            have h_st21 : st.2.1 ∩ (st.1 ∪ d ∩ G) = st.2.1 := by
              exact Finset.inter_eq_left.mpr h
            by_cases hp : p d
            · have h_rhs : c + (if p d then W else 0) +
                  (if !p d then (d ∩ G).card else 0) = c + W := by simp [hp]
              rw [h_rhs]
              omega
            · have hdel : (st.2.1 ∩ (d ∩ G)).card ≤ (d ∩ G).card :=
                Finset.card_le_card Finset.inter_subset_right
              have h_inter := card_inter_union_le_add_bound st.2.1 st.1 (d ∩ G) hdel
              rw [h_st21] at h_inter
              have hnew : W ≤ (st.2.1 ∩ st.1).card + (d ∩ G).card := by
                rw [← hw]
                exact h_inter
              have hp_false : p d = false := eq_false_of_ne_true hp
              have h_rhs : c + (if p d then W else 0) +
                  (if !p d then (d ∩ G).card else 0) = c + (d ∩ G).card := by
                simp [hp_false]
              rw [h_rhs]
              omega
        · -- no refresh
          simp only [step, if_neg h]
          refine ⟨P, hP₁.trans Finset.subset_union_left, hP₂, hP₃, hsubG, hP₅, ?_, ?_⟩
          · rcases hP₆ with hw | ⟨D, hD₁, hD₂, hw'⟩
            · exact Or.inl hw
            · right
              refine ⟨D, hD₁.trans Finset.subset_union_left, hD₂, hw'⟩
          · by_cases hp : p d
            · have hwin : st.2.1.card ≤ W := by
                rcases hP₆ with hw | ⟨D, hD₁, hD₂, hw'⟩
                · exact hw.le
                · exact hw'
              have hdel : (st.2.1 ∩ (d ∩ G)).card ≤ W :=
                le_trans (Finset.card_le_card Finset.inter_subset_left) hwin
              have hnew :
                  (st.2.1 ∩ (st.1 ∪ d ∩ G)).card ≤
                    (st.2.1 ∩ st.1).card + W :=
                card_inter_union_le_add_bound _ _ _ hdel
              have h_rhs : c + (if p d then W else 0) +
                  (if !p d then (d ∩ G).card else 0) = c + W := by simp [hp]
              rw [h_rhs]
              omega
            · have hdel : (st.2.1 ∩ (d ∩ G)).card ≤ (d ∩ G).card :=
                Finset.card_le_card Finset.inter_subset_right
              have hnew :
                  (st.2.1 ∩ (st.1 ∪ d ∩ G)).card ≤
                    (st.2.1 ∩ st.1).card + (d ∩ G).card :=
                card_inter_union_le_add_bound _ _ _ hdel
              have hp_false : p d = false := eq_false_of_ne_true hp
              have h_rhs : c + (if p d then W else 0) +
                  (if !p d then (d ∩ G).card else 0) = c + (d ∩ G).card := by
                simp [hp_false]
              rw [h_rhs]
              omega
      have hcredit :
          c + ((d :: L').filter p).length * W +
              (((d :: L').filter (fun d => !p d)).map (fun d => (d ∩ G).card)).sum
            = (c + (if p d then W else 0) + (if !p d then (d ∩ G).card else 0)) +
                (L'.filter p).length * W +
                ((L'.filter (fun d => !p d)).map (fun d => (d ∩ G).card)).sum :=
        splitCredit_cons G W c p d L'
      rw [hcredit]
      have h_fin_mono_2 : (step G first st d).1 ⊆ (L'.foldl (step G first) (step G first st d)).1
          := by
        rwa [he]
      exact ih (step G first st d)
        (c + (if p d then W else 0) + (if !p d then (d ∩ G).card else 0)) h_step h_fin_mono_2
            hsurv_local
  have hinit : ∃ P : Finset α, P ⊆ ∅ ∧ Disjoint (first G) P ∧ 0 * W ≤ P.card ∧
        ∅ ⊆ G ∧ first G ⊆ G ∧
        ((first G).card = W ∨ ∃ D ⊆ ∅, first G = G \ D ∧ (first G).card ≤ W) ∧
        P.card + (first G ∩ ∅).card ≤ 0 := by
    refine ⟨∅, Finset.empty_subset _, Finset.disjoint_empty_right _, by simp,
      Finset.empty_subset _, hsub G, ?_, by simp⟩
    have hc : (first G).card = min W G.card := hcard G
    by_cases hw : (first G).card = W
    · exact Or.inl hw
    · right
      refine ⟨∅, Finset.empty_subset _, ?_⟩
      rw [Nat.min_def] at hc
      split_ifs at hc with hle
      · exact (hw hc).elim
      · have hc' : (first G).card = G.card := hc
        exact ⟨(Finset.eq_of_subset_of_card_le (hsub G) hc'.ge).trans Finset.sdiff_empty.symm,
                by linarith⟩
  have hmono : ∅ ⊆ (L.foldl (step G first) (∅, first G, 0)).1 := Finset.empty_subset _
  have hfin := h_inv L (∅, first G, 0) 0 hinit hmono hsurv
  obtain ⟨P, hP₁, -, hP₃, -, -, -, hP₈⟩ := hfin
  have hz : (L.filter p).length * W + ((L.filter (fun d => !p d)).map (fun d => (d ∩ G).card)).sum =
    0 + (L.filter p).length * W + ((L.filter (fun d => !p d)).map (fun d => (d ∩ G).card)).sum :=
        by ring
  rw [hz]
  exact hP₃.trans (hP₈.trans' (by linarith))

theorem fold_count_split_div_le_of_survivor
    (G : Finset α) (W : ℕ) (hW : 0 < W) (first : Finset α → Finset α)
    (hsub : ∀ S : Finset α, first S ⊆ S)
    (hcard : ∀ S : Finset α, (first S).card = min W S.card)
    (L : List (Finset α)) (p : Finset α → Bool)
    (hsurv : (G \ (fold G first L).1).Nonempty) :
    (fold G first L).2.2 ≤
      (L.filter p).length +
        ((L.filter (fun d => !p d)).map (fun d => (d ∩ G).card)).sum / W := by
  have h := fold_count_split_le_of_survivor G W first hsub hcard L p hsurv
  rw [mul_comm ((L.filter p).length) W] at h
  calc (fold G first L).2.2
      ≤ (W * (L.filter p).length +
          ((L.filter (fun d => !p d)).map (fun d => (d ∩ G).card)).sum) / W :=
        (Nat.le_div_iff_mul_le hW).mpr h
    _ = (L.filter p).length +
          ((L.filter (fun d => !p d)).map (fun d => (d ∩ G).card)).sum / W :=
        Nat.mul_add_div hW _ _

theorem fold_count_split_div_le_of_survivor_toFinset
    (G : Finset α) (W : ℕ) (hW : 0 < W) (first : Finset α → Finset α)
    (hsub : ∀ S : Finset α, first S ⊆ S)
    (hcard : ∀ S : Finset α, (first S).card = min W S.card)
    (L : List (Finset α)) (p : Finset α → Bool) (hnodup : L.Nodup)
    (hsurv : (G \ (fold G first L).1).Nonempty) :
    (fold G first L).2.2 ≤
      (L.toFinset.filter (fun d => p d = true)).card +
        (((L.toFinset.filter (fun d => !(p d) = true)).toList).map (fun d => (d ∩ G).card)).sum / W
            := by
  -- On a duplicate-free list the `toFinset`-based counts equal the list-based ones,
  -- so this reduces to `fold_count_split_div_le_of_survivor`.
  have hcard_eq :
      (L.toFinset.filter (fun d => p d = true)).card = (L.filter p).length := by
    rw [← List.toFinset_filter, List.toFinset_card_of_nodup (hnodup.filter p)]
  have hsum_eq :
      (((L.toFinset.filter (fun d => !(p d) = true)).toList).map (fun d => (d ∩ G).card)).sum
        = ((L.filter (fun d => !p d)).map (fun d => (d ∩ G).card)).sum := by
    rw [Finset.sum_map_toList, ← List.toFinset_filter,
      List.sum_toFinset _ (hnodup.filter _)]
    simp
  rw [hcard_eq, hsum_eq]
  exact fold_count_split_div_le_of_survivor G W hW first hsub hcard L p hsurv

/-
If a nonempty `Surv ⊆ G` is disjoint from every deletion (restricted to `G`), and
`first` sends nonempty sets to nonempty sets, then the running-window component of the
fold is always nonempty.  Invariant: the deleted set stays disjoint from `Surv`, so at
every refresh the window is a `first`-block of `G \ deleted ⊇ Surv ≠ ∅`.
-/
theorem fold_window_nonempty (G : Finset α) (first : Finset α → Finset α)
    (hfirst_ne : ∀ S : Finset α, S.Nonempty → (first S).Nonempty)
    (Surv : Finset α) (hSurv : Surv.Nonempty) (hSurvG : Surv ⊆ G)
    (L : List (Finset α)) (hdisj : ∀ d ∈ L, Disjoint Surv (d ∩ G)) :
    (fold G first L).2.1.Nonempty := by
  have h_foldl_nonempty :
      ∀ (M : List (Finset α)) (st : Finset α × Finset α × ℕ), st.2.1.Nonempty →
        Disjoint Surv st.1 → (∀ d ∈ M, Disjoint Surv (d ∩ G)) →
          (M.foldl (step G first) st).2.1.Nonempty ∧
            Disjoint Surv (M.foldl (step G first) st).1 := by
    intro M st hst h_disj_st hdisj; induction M using List.reverseRecOn generalizing st with
    | nil => exact ⟨hst, h_disj_st⟩
    | append_singleton M' d hd =>
      have hd_pre : ∀ d_1 ∈ M', Disjoint Surv (d_1 ∩ G) := fun d_1 hd_1 =>
        hdisj d_1 (List.mem_append.mpr (Or.inl hd_1))
      specialize hd st hst h_disj_st hd_pre
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, step]
      split_ifs
      · refine ⟨?_, ?_⟩
        · apply hfirst_ne
          apply Finset.Nonempty.mono _ hSurv
          intro x hx
          rw [Finset.mem_sdiff, Finset.mem_union]
          refine ⟨hSurvG hx, ?_⟩
          push_neg
          constructor
          · exact Finset.disjoint_left.mp hd.2 hx
          · have hd_disj := hdisj d (List.mem_append_right M' (List.mem_singleton_self d))
            exact Finset.disjoint_left.mp hd_disj hx
        · simp only [Finset.disjoint_left]
          intro a ha₁ ha₂
          rw [Finset.mem_union] at ha₂
          cases ha₂ with
          | inl h1 => exact Finset.disjoint_left.mp hd.2 ha₁ h1
          | inr h2 =>
            have hd_disj := hdisj d (List.mem_append_right M' (List.mem_singleton_self d))
            exact Finset.disjoint_left.mp hd_disj ha₁ h2
      · refine ⟨hd.1, ?_⟩
        simp only [Finset.disjoint_left] at hd hdisj ⊢
        intro a ha₁ ha₂
        rw [Finset.mem_union, Finset.mem_inter] at ha₂
        cases ha₂ with
        | inl h1 => exact hd.2 ha₁ h1
        | inr h2 =>
          have hd_disj := hdisj d (List.mem_append_right M' (List.mem_singleton_self d))
          exact hd_disj ha₁ (Finset.mem_inter.mpr h2)
  exact h_foldl_nonempty L ( ∅, first G,
                             0 ) ( hfirst_ne G ( hSurv.mono hSurvG ) ) ( by simp +decide
                                                                         ) hdisj |>.1

theorem fold_window_sdiff_deleted_nonempty (G : Finset α) (first : Finset α → Finset α)
    (hfirst_ne : ∀ S : Finset α, S.Nonempty → (first S).Nonempty)
    (hsub : ∀ S : Finset α, first S ⊆ S)
    (Surv : Finset α) (hSurv : Surv.Nonempty) (hSurvG : Surv ⊆ G)
    (L : List (Finset α)) (hdisj : ∀ d ∈ L, Disjoint Surv (d ∩ G)) :
    ((fold G first L).2.1 \ (fold G first L).1).Nonempty := by
  have h_foldl_nonempty : ∀ (M : List (Finset α)) (st : Finset α × Finset α × ℕ),
      (st.2.1 \ st.1).Nonempty → Disjoint Surv st.1 → (∀ d ∈ M, Disjoint Surv (d ∩ G)) →
      ((M.foldl (step G first) st).2.1 \ (M.foldl (step G first) st).1).Nonempty ∧ Disjoint Surv
          (M.foldl (step G first) st).1 := by
    intro M
    induction M with
    | nil =>
      intro st h_ne h_disj _
      exact ⟨h_ne, h_disj⟩
    | cons d M ih =>
      intro st h_ne h_disj hdisj_M
      have hd : Disjoint Surv (d ∩ G) := hdisj_M d List.mem_cons_self
      have hdisj_M' : ∀ d' ∈ M, Disjoint Surv (d' ∩ G) :=
          fun d' hd' => hdisj_M d' (List.mem_cons_of_mem d hd')
      have h_surv_del' : Disjoint Surv (st.1 ∪ (d ∩ G)) :=
          Finset.disjoint_union_right.mpr ⟨h_disj, hd⟩
      have he : (step G first st d).1 = st.1 ∪ (d ∩ G) := step_deleted_eq G first st d
      have h_ne' : ((step G first st d).2.1 \ (step G first st d).1).Nonempty := by
        unfold step
        by_cases h : st.2.1 ⊆ st.1 ∪ (d ∩ G)
        · simp only [h, if_true]
          have h_G_sdiff_ne : (G \ (st.1 ∪ (d ∩ G))).Nonempty :=
            hSurv.mono (Finset.subset_sdiff.mpr ⟨hSurvG, h_surv_del'⟩)
          have h_first_ne := hfirst_ne _ h_G_sdiff_ne
          have h_first_sub := hsub (G \ (st.1 ∪ (d ∩ G)))
          have h_disj_first : Disjoint (first (G \ (st.1 ∪ (d ∩ G)))) (st.1 ∪ (d ∩ G)) :=
            Finset.disjoint_of_subset_left h_first_sub Finset.sdiff_disjoint
          have heq : first (G \ (st.1 ∪ d ∩ G)) \ (st.1 ∪ d ∩ G) = first (G \ (st.1 ∪ d ∩ G)) :=
              Finset.sdiff_eq_self_iff_disjoint.mpr h_disj_first
          rw [heq]
          exact h_first_ne
        · simp only [h, if_false]
          exact Finset.sdiff_nonempty.mpr h
      exact ih (step G first st d) (he ▸ h_ne') (he ▸ h_surv_del') hdisj_M'
  have h_init_ne : ((first G) \ ∅).Nonempty := by
    have h_disj_first : Disjoint (first G) ∅ := Finset.disjoint_empty_right _
    have heq : first G \ ∅ = first G := Finset.sdiff_eq_self_iff_disjoint.mpr h_disj_first
    rw [heq]
    exact hfirst_ne G (hSurv.mono hSurvG)
  exact (h_foldl_nonempty L (∅, first G, 0) h_init_ne (Finset.disjoint_empty_right _) hdisj).1

theorem step_count_mono {α : Type} [DecidableEq α] (G : Finset α) (first : Finset α → Finset α)
    (st : Finset α × Finset α × ℕ) (d : Finset α) :
    st.2.2 ≤ (step G first st d).2.2 := by
  unfold step
  dsimp only
  split_ifs
  · exact Nat.le_add_right _ _
  · exact le_rfl

theorem foldl_count_mono {α : Type} [DecidableEq α] (G : Finset α) (first : Finset α → Finset α)
    (L : List (Finset α)) :
    ∀ st : Finset α × Finset α × ℕ, st.2.2 ≤ (L.foldl (step G first) st).2.2 := by
  intro st
  induction L generalizing st with
  | nil => exact le_rfl
  | cons d L ih =>
    exact (step_count_mono G first st d).trans (ih (step G first st d))

theorem fold_no_refresh_window {α : Type} [DecidableEq α] (G : Finset α)
    (first : Finset α → Finset α) (L : List (Finset α)) :
    ∀ st : Finset α × Finset α × ℕ,
      (L.foldl (step G first) st).2.2 = st.2.2 →
      (L.foldl (step G first) st).2.1 = st.2.1 := by
  intro st h_eq
  induction L generalizing st with
  | nil => rfl
  | cons d L ih =>
    have h_eq' : (L.foldl (step G first) (step G first st d)).2.2 = st.2.2 := h_eq
    have h_eq2 : (step G first st d).2.2 = st.2.2 := by
      have h_ge : (L.foldl (step G first) (step G first st d)).2.2 ≥ (step G first st d).2.2 :=
          foldl_count_mono _ _ _ _
      have h1 : st.2.2 ≤ (step G first st d).2.2 := step_count_mono _ _ _ _
      linarith
    have h_ih := ih (step G first st d) (by linarith)
    have hd_eq : (step G first st d).2.1 = st.2.1 := by
      unfold step at h_eq2 ⊢
      dsimp only at h_eq2 ⊢
      split_ifs at h_eq2 ⊢ with h_ref
      · linarith
      · rfl
    rw [← hd_eq]
    exact h_ih

theorem fold_deleted_mono {α : Type} [DecidableEq α] (G : Finset α) (first : Finset α → Finset α)
    (L : List (Finset α)) :
    ∀ st : Finset α × Finset α × ℕ, st.1 ⊆ (L.foldl (step G first) st).1 := by
  intro st
  exact foldl_deleted_mono G first L st

theorem firstBlock_nonempty {α : Type} [DecidableEq α] (key : α → ℕ) (K : ℕ) (hK : 0 < K)
    (S : Finset α) (hS : S.Nonempty) :
    (firstBlock key K S).Nonempty := by
  rw [← Finset.card_pos, firstBlock_card]
  exact lt_min hK (Finset.card_pos.mpr hS)

theorem fold_final_not_subset {α : Type} [DecidableEq α] (G : Finset α) (key : α → ℕ) (K : ℕ)
    (hK : 0 < K) (L : List (Finset α)) :
    ∀ st : Finset α × Finset α × ℕ,
      (G \ (L.foldl (step G (firstBlock key K)) st).1).Nonempty →
      ¬ (st.2.1 ⊆ st.1) →
      ¬ ((L.foldl (step G (firstBlock key K)) st).2.1 ⊆ (L.foldl (step G (firstBlock key K)) st).1)
          := by
  intro st h_surv
  induction L generalizing st with
  | nil =>
    intro h_not
    exact h_not
  | cons d L ih =>
    intro h_not
    have h_surv' :
        (G \ (L.foldl (step G (firstBlock key K)) (step G (firstBlock key K) st d)).1).Nonempty :=
            h_surv
    apply ih (step G (firstBlock key K) st d) h_surv'
    unfold step
    dsimp only
    split_ifs with h_ref
    · intro h_sub
      have h_mono :=
          fold_deleted_mono G (firstBlock key K) L (st.1 ∪ d ∩ G,
                                                     firstBlock key K (G \ (st.1 ∪ d ∩ G)), st.2.2
                                                         + 1)
      have h_surv_sub : G \ (L.foldl (step G (firstBlock key K)) (st.1 ∪ d ∩ G,
                                                                   firstBlock key K
                                                                       (G \ (st.1 ∪ d ∩ G)), st.2.2
                                                                           + 1)).1 ⊆ G \ (st.1 ∪ d
                                                                                           ∩ G) :=
                                                                                               by
        apply Finset.sdiff_subset_sdiff subset_rfl h_mono
      have h_surv_eq : (step G (firstBlock key K) st d) = (st.1 ∪ d ∩ G,
                                                            firstBlock key K (G \ (st.1 ∪ d ∩ G)),
                                                                st.2.2 + 1) := by
        unfold step
        dsimp only
        rw [if_pos h_ref]
      have h_nonempty : (G \ (st.1 ∪ d ∩ G)).Nonempty := by
        rw [← h_surv_eq] at h_surv_sub
        obtain ⟨y, hy⟩ := h_surv
        use y
        exact h_surv_sub hy
      have h_first_ne := firstBlock_nonempty key K hK (G \ (st.1 ∪ d ∩ G)) h_nonempty
      have h_first_sub := firstBlock_subset key K (G \ (st.1 ∪ d ∩ G))
      obtain ⟨x, hx_in⟩ := h_first_ne
      have hx_diff := h_first_sub hx_in
      have hx_sub := h_sub hx_in
      rw [Finset.mem_sdiff] at hx_diff
      exact hx_diff.2 hx_sub
    · intro h_sub
      exact h_ref h_sub

theorem fold_deleted_not_mem {α : Type} [DecidableEq α] (G : Finset α)
    (first : Finset α → Finset α) (L : List (Finset α)) :
    ∀ st : Finset α × Finset α × ℕ, ∀ y,
      y ∉ st.1 → (∀ d ∈ L, y ∉ d) → y ∉ (L.foldl (step G first) st).1 := by
  intro st y h_init h_surv
  induction L generalizing st with
  | nil => exact h_init
  | cons d_head L ih =>
    have h_surv_tail : ∀ d' ∈ L, y ∉ d' := fun d' hd' => h_surv d' (List.mem_cons_of_mem _ hd')
    apply ih (step G first st d_head) _ h_surv_tail
    have hy_d : y ∉ d_head := h_surv d_head (by simp)
    unfold step
    dsimp only
    split_ifs
    · intro h_in
      rw [Finset.mem_union] at h_in
      cases h_in with
      | inl h1 => exact h_init h1
      | inr h2 =>
        rw [Finset.mem_inter] at h2
        exact hy_d h2.1
    · intro h_in
      rw [Finset.mem_union] at h_in
      cases h_in with
      | inl h1 => exact h_init h1
      | inr h2 =>
        rw [Finset.mem_inter] at h2
        exact hy_d h2.1

theorem fold_deleted_mem {α : Type} [DecidableEq α] (G : Finset α) (first : Finset α → Finset α)
    (L : List (Finset α)) :
    ∀ st : Finset α × Finset α × ℕ, ∀ d_elem ∈ L, ∀ y,
      y ∈ d_elem → y ∈ G → y ∈ (L.foldl (step G first) st).1 := by
  intro st d_elem hd y hy_d hy_G
  induction L generalizing st with
  | nil => cases hd
  | cons d_head L ih =>
    cases List.mem_cons.mp hd with
    | inl h_eq =>
      have h_mono := fold_deleted_mono G first L (step G first st d_head)
      apply h_mono
      unfold step
      dsimp only
      split_ifs
      · apply Finset.mem_union.mpr
        apply Or.inr
        apply Finset.mem_inter.mpr ⟨by rwa [←h_eq], hy_G⟩
      · apply Finset.mem_union.mpr
        apply Or.inr
        apply Finset.mem_inter.mpr ⟨by rwa [←h_eq], hy_G⟩
    | inr h_in =>
      exact ih (step G first st d_head) h_in

theorem fold_window_eq_firstBlock {α : Type} [DecidableEq α] (G : Finset α) (key : α → ℕ) (K : ℕ)
    (L : List (Finset α)) :
    ∀ st : Finset α × Finset α × ℕ,
      (∃ D, D ⊆ st.1 ∧ st.2.1 = firstBlock key K (G \ D)) →
      ∃ D, D ⊆ (L.foldl (step G (firstBlock key K)) st).1 ∧
           (L.foldl (step G (firstBlock key K)) st).2.1 = firstBlock key K (G \ D) := by
  intro st h_init
  induction L generalizing st with
  | nil => exact h_init
  | cons d_head L ih =>
    apply ih (step G (firstBlock key K) st d_head)
    unfold step
    dsimp only
    split_ifs with h_ref
    · exact ⟨st.1 ∪ d_head ∩ G, subset_rfl, rfl⟩
    · obtain ⟨D, hD_sub, hD_eq⟩ := h_init
      exact ⟨D, hD_sub.trans Finset.subset_union_left, hD_eq⟩

theorem list_key_le_of_mem_take_of_mem_not_mem_take {α : Type} (key : α → ℕ)
    (L : List α) (K : ℕ) :
    L.Pairwise (fun a b => key a ≤ key b) →
      ∀ {y x : α}, y ∈ L.take K → x ∈ L → x ∉ L.take K → key y ≤ key x := by
  induction L generalizing K with
  | nil =>
      intro _ y x hy
      simp at hy
  | cons a L ih =>
      intro hsort y x hy hx hx_not
      cases K with
      | zero =>
          simp at hy
      | succ K =>
          simp only [List.take_succ_cons, List.mem_cons] at hy hx hx_not
          rcases hy with rfl | hy
          · rcases hx with rfl | hx
            · exact False.elim (hx_not (Or.inl rfl))
            · exact L.rel_of_pairwise_cons hsort hx
          · rcases hx with rfl | hx
            · exact False.elim (hx_not (Or.inl rfl))
            · exact ih K (List.Pairwise.of_cons hsort) hy hx
                (fun hx_take => hx_not (Or.inr hx_take))

theorem firstBlock_le_of_mem_of_not_mem {α : Type} [DecidableEq α] (key : α → ℕ) (K : ℕ)
    (S : Finset α) :
    ∀ y ∈ firstBlock key K S, ∀ x ∈ S, x ∉ firstBlock key K S → key y ≤ key x := by
  intro y hy x hx hx_not
  unfold firstBlock at hy hx_not
  rw [List.mem_toFinset] at hy hx_not
  set L := S.toList.mergeSort (fun a b => decide (key a ≤ key b)) with hL
  have hxL : x ∈ L := by
    rw [hL, List.mem_mergeSort]
    exact Finset.mem_toList.mpr hx
  have htot :
      ∀ a b : α,
        ((fun a b => decide (key a ≤ key b)) a b ||
          (fun a b => decide (key a ≤ key b)) b a) = true := by
    intro a b
    by_cases h : key a ≤ key b
    · simp [h]
    · simp [h, Nat.le_of_not_le h]
  have htrans :
      ∀ a b c : α,
        (fun a b => decide (key a ≤ key b)) a b = true →
          (fun a b => decide (key a ≤ key b)) b c = true →
            (fun a b => decide (key a ≤ key b)) a c = true := by
    intro a b c hab hbc
    exact decide_eq_true (le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc))
  have hsort_bool := List.pairwise_mergeSort htrans htot S.toList
  have hsort : L.Pairwise (fun a b => key a ≤ key b) := by
    rw [hL]
    exact hsort_bool.imp (fun h => of_decide_eq_true h)
  exact list_key_le_of_mem_take_of_mem_not_mem_take key L K hsort hy hxL hx_not

theorem temporalWindow_contains_survivor_aux {α : Type} [DecidableEq α] (G : Finset α)
    (key : α → ℕ) (K : ℕ) (hK : 0 < K)
    (L_T L_rest : List (Finset α))
    (x : α) (hx_surv : ∀ d ∈ L_T ++ L_rest, x ∉ d)
    (hxG : x ∈ G)
    (h_no_refresh : ((L_T ++ L_rest).foldl (step G (firstBlock key K)) (∅, firstBlock key K G,
                                                                         0)).2.2 =
                    (L_T.foldl (step G (firstBlock key K)) (∅, firstBlock key K G, 0)).2.2)
    (hle : ∀ y, y ∈ G → (∀ d ∈ L_T ++ L_rest, y ∉ d) → key x ≤ key y)
    (hinj : ∀ a b, a ∈ G → b ∈ G → key a = key b → a = b) :
    x ∈ (L_T.foldl (step G (firstBlock key K)) (∅, firstBlock key K G, 0)).2.1 := by
  set st_init := ((∅ : Finset α), firstBlock key K G, 0)
  set L_total := L_T ++ L_rest
  have h_foldl_append : (L_total.foldl (step G (firstBlock key K)) st_init) =
    L_rest.foldl (step G (firstBlock key K)) (L_T.foldl (step G (firstBlock key K)) st_init) :=
        by apply List.foldl_append
  have h_no_refresh' :
      (L_rest.foldl (step G (firstBlock key K)) (L_T.foldl (step G (firstBlock key K))
                                                  st_init)).2.2 =
    (L_T.foldl (step G (firstBlock key K)) st_init).2.2 := by
    rw [← h_foldl_append]
    exact h_no_refresh
  have h_win_eq : (L_total.foldl (step G (firstBlock key K)) st_init).2.1 =
      (L_T.foldl (step G (firstBlock key K)) st_init).2.1 := by
    rw [h_foldl_append]
    exact fold_no_refresh_window G (firstBlock key K) L_rest
        (L_T.foldl (step G (firstBlock key K)) st_init) h_no_refresh'
  have h_surv_total : (G \ (L_total.foldl (step G (firstBlock key K)) st_init).1).Nonempty := by
    use x
    rw [Finset.mem_sdiff]
    constructor
    · exact hxG
    · have hx_not_st : x ∉ st_init.1 := by
        change x ∉ (∅ : Finset α)
        simp
      exact fold_deleted_not_mem G (firstBlock key K) L_total st_init x hx_not_st hx_surv
  have h_init_not_sub : ¬ (st_init.2.1 ⊆ st_init.1) := by
    intro h_sub
    have hy_ex : (firstBlock key K G).Nonempty := by
      rw [← Finset.card_pos, firstBlock_card]
      exact lt_min hK (Finset.card_pos.mpr ⟨x, hxG⟩)
    obtain ⟨y, hy_in⟩ := hy_ex
    have hy_sub := h_sub hy_in
    change y ∈ (∅ : Finset α) at hy_sub
    exact (by simp : y ∉ (∅ : Finset α)) hy_sub
  have h_not_sub_total :=
      fold_final_not_subset G key K hK L_total st_init h_surv_total h_init_not_sub
  have h_win_total_ne :
      ((L_total.foldl (step G (firstBlock key K)) st_init).2.1 \ (L_total.foldl (step G (firstBlock
                                                                                          key K))
          st_init).1).Nonempty := by
    rw [← Finset.sdiff_nonempty] at h_not_sub_total
    exact h_not_sub_total
  obtain ⟨y, hy_sdiff⟩ := h_win_total_ne
  have hy_win_total := (Finset.mem_sdiff.mp hy_sdiff).1
  have hy_not_del := (Finset.mem_sdiff.mp hy_sdiff).2
  have hy_win_T : y ∈ (L_T.foldl (step G (firstBlock key K)) st_init).2.1 := by
    rw [← h_win_eq]
    exact hy_win_total
  have h_init' : ∃ D, D ⊆ st_init.1 ∧ st_init.2.1 = firstBlock key K (G \ D) := by
    use ∅
    constructor
    · exact subset_rfl
    · change firstBlock key K G = firstBlock key K (G \ ∅)
      rw [Finset.sdiff_empty]
  obtain ⟨D_T, hDT_sub, hDT_eq⟩ := fold_window_eq_firstBlock G key K L_T st_init h_init'
  have hy_WT : y ∈ firstBlock key K (G \ D_T) := by
    rw [← hDT_eq]
    exact hy_win_T
  have hy_diff := firstBlock_subset key K (G \ D_T) hy_WT
  have hy_G : y ∈ G := (Finset.mem_sdiff.mp hy_diff).1
  have hy_surv : ∀ d ∈ L_total, y ∉ d := by
    intro d hd hy_d
    have h_contra : y ∈ (L_total.foldl (step G (firstBlock key K)) st_init).1 :=
        fold_deleted_mem G (firstBlock key K) L_total st_init d hd y hy_d hy_G
    exact hy_not_del h_contra
  have h_key_le : key x ≤ key y := hle y hy_G hy_surv
  have hx_DT : x ∉ D_T := by
    intro hx_in
    have hx_sub : x ∈ (L_T.foldl (step G (firstBlock key K)) st_init).1 := hDT_sub hx_in
    have hx_not_del : x ∉ (L_T.foldl (step G (firstBlock key K)) st_init).1 := by
      have hx_init : x ∉ st_init.1 := by
        change x ∉ (∅ : Finset α)
        simp
      have h_surv_T : ∀ d ∈ L_T, x ∉ d := fun d hd => hx_surv d (List.mem_append_left L_rest hd)
      exact fold_deleted_not_mem G (firstBlock key K) L_T st_init x hx_init h_surv_T
    exact hx_not_del hx_sub
  have hx_diff : x ∈ G \ D_T := Finset.mem_sdiff.mpr ⟨hxG, hx_DT⟩
  by_contra hx_not_WT
  have hx_not_WT' : x ∉ firstBlock key K (G \ D_T) := by
    rw [← hDT_eq]
    exact hx_not_WT
  have h_le_yx := firstBlock_le_of_mem_of_not_mem key K (G \ D_T) y hy_WT x hx_diff hx_not_WT'
  -- now we have key y ≤ key x and key x ≤ key y.
  -- Thus key x = key y.
  have h_key_eq : key x = key y := le_antisymm h_key_le h_le_yx
  -- by hinj, x = y.
  have h_xy : x = y := hinj x y hxG hy_G h_key_eq
  -- but x ∉ W_T and y ∈ W_T, contradiction.
  rw [h_xy] at hx_not_WT
  exact hx_not_WT hy_win_T

end Kolmogorov.GreedyWindow
