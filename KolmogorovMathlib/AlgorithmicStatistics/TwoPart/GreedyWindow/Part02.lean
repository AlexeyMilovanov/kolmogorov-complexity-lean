import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.GreedyWindow.StepFold
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.GreedyWindow.CountInvariants

/-!
# Which elements the window holds

`fold_window_eq_firstBlock`: along the greedy fold the current window is always the first
block, by key, of the surviving ground set.  With `firstBlock_le_of_mem_of_not_mem` and
`list_key_le_of_mem_take_of_mem_not_mem_take` this gives
`temporalWindow_contains_survivor_aux`: a survivor of minimal key is in the window at every
earlier time at which no refresh has happened — the fact that lets the realization argument
address a survivor by the version number alone.  `fold_deleted_mem` and
`fold_deleted_not_mem` characterise the deleted set.
-/

namespace Kolmogorov.GreedyWindow
variable {α : Type*} [DecidableEq α]

/-- An element missing from the deleted set and from every set of the list is still not deleted
after the greedy fold. -/
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

/-- An element of the ground set occurring in one of the sets of the list is deleted by the
greedy fold. -/
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

/-- The greedy fold keeps the invariant that the current window is the first block of the ground
set minus the deleted elements. -/
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

/-- In a list sorted by `key`, every entry of the first `K` has key at most that of any entry
outside them. -/
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

/-- Every element of the first block has key at most that of any element of the set outside the
block. -/
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

/-- A survivor of minimal key stays in the window at the earlier time whenever no refresh happens
in between. -/
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
