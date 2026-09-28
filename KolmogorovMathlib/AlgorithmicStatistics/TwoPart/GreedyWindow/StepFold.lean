import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# The greedy running window

An abstract process on a finite ground set `G`: keep a window of `W` elements; when a deletion
arrives, remove the deleted elements and, if the window has been emptied, refresh it by taking
the `W` surviving elements of least key.  `step` is one deletion, `fold` the whole list, and
`firstBlock` the canonical window selector (`firstBlock_subset`, `firstBlock_card`,
`firstBlock_mono_size`).

The point of the process is that it refreshes rarely, and the bounds are proved here:
`fold_count_mul_le` and `fold_count_le` in multiplicative and division form,
`fold_count_mul_le_of_survivor` and `fold_count_le_of_survivor` when a survivor is known, and
`fold_count_split_le`, which bounds the refreshes by splitting the deletions along a
predicate.  Curve realization uses the window as the model whose *version number* has to stay
short, so these counts are what bound the version.
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

/-- The block selected by `firstBlock` is a subset of the set it is taken from. -/
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

/-- The block selected by `firstBlock` has `W` elements, or all of `S` when `S` is smaller. -/
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

end Kolmogorov.GreedyWindow
