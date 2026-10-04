import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.GreedyWindow.StepFold

/-!
# Invariants of the greedy window

The bookkeeping behind the refresh counts.  `step_preserves_window_invariant` is the invariant
one step preserves; `step_count_mono`, `foldl_count_mono`, `fold_deleted_mono` and
`fold_no_refresh_window` say the counter and the deleted set only grow and that the window
changes only when the counter does.

`fold_count_split_le_of_survivor`, its division form and its `toFinset` form are the split
refresh bounds used when a survivor is available; `fold_window_nonempty`,
`fold_window_sdiff_deleted_nonempty` and `fold_final_not_subset` say the window never empties
while something survives.
-/

namespace Kolmogorov.GreedyWindow
variable {α : Type*} [DecidableEq α]

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

/-- One deletion step preserves the window invariant: if the paid-for part `P` of the state `st`
carries credit `c`, then the state after deleting `d` carries the same invariant with the credit
raised by `W` for a `p`-deletion and by the number of ground elements removed otherwise. -/
private lemma step_preserves_window_invariant (G : Finset α) (W : ℕ)
    (first : Finset α → Finset α) (hsub : ∀ S : Finset α, first S ⊆ S)
    (hcard : ∀ S : Finset α, (first S).card = min W S.card) (p : Finset α → Bool)
    (st : Finset α × Finset α × ℕ) (d : Finset α) (c : ℕ) (P : Finset α)
    (hP₁ : P ⊆ st.1) (hP₂ : Disjoint st.2.1 P) (hP₃ : st.2.2 * W ≤ P.card)
    (hP₄ : st.1 ⊆ G) (hP₅ : st.2.1 ⊆ G)
    (hP₆ : st.2.1.card = W ∨ ∃ D ⊆ st.1, st.2.1 = G \ D ∧ st.2.1.card ≤ W)
    (hP₇ : P.card + (st.2.1 ∩ st.1).card ≤ c)
    (hsurv : (G \ (step G first st d).1).Nonempty) :
    ∃ P' : Finset α, P' ⊆ (step G first st d).1 ∧
      Disjoint (step G first st d).2.1 P' ∧ (step G first st d).2.2 * W ≤ P'.card ∧
      (step G first st d).1 ⊆ G ∧ (step G first st d).2.1 ⊆ G ∧
      ((step G first st d).2.1.card = W ∨ ∃ D ⊆ (step G first st d).1,
          (step G first st d).2.1 = G \ D ∧ (step G first st d).2.1.card ≤ W) ∧
      P'.card + ((step G first st d).2.1 ∩ (step G first st d).1).card ≤
        c + (if p d then W else 0) + (if !p d then (d ∩ G).card else 0) := by
  have he : (step G first st d).1 = st.1 ∪ (d ∩ G) := step_deleted_eq G first st d
  have hsubG : (st.1 ∪ (d ∩ G)) ⊆ G := by
    have h2 := step_deleted_subset G first st hP₄ d; rwa [he] at h2
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
        rw [he, Finset.sdiff_eq_empty_iff_subset.mpr hG] at hsurv
        exact Finset.not_nonempty_empty hsurv
    have hPunion : (P ∪ st.2.1) ⊆ st.1 ∪ (d ∩ G) :=
      Finset.union_subset (hP₁.trans Finset.subset_union_left) h
    simp only [step, ite_eq_left h]
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
      have h_st21 : st.2.1 ∩ (st.1 ∪ d ∩ G) = st.2.1 := Finset.inter_eq_left.mpr h
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
        have hp_false : p d = false := Bool.eq_false_of_ne_true hp
        have h_rhs : c + (if p d then W else 0) +
            (if !p d then (d ∩ G).card else 0) = c + (d ∩ G).card := by
          simp [hp_false]
        rw [h_rhs]
        omega
  · -- no refresh
    simp only [step, ite_eq_right h]
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
        have hnew : (st.2.1 ∩ (st.1 ∪ d ∩ G)).card ≤ (st.2.1 ∩ st.1).card + W :=
          card_inter_union_le_add_bound _ _ _ hdel
        have h_rhs : c + (if p d then W else 0) +
            (if !p d then (d ∩ G).card else 0) = c + W := by simp [hp]
        rw [h_rhs]
        omega
      · have hdel : (st.2.1 ∩ (d ∩ G)).card ≤ (d ∩ G).card :=
          Finset.card_le_card Finset.inter_subset_right
        have hnew :
            (st.2.1 ∩ (st.1 ∪ d ∩ G)).card ≤ (st.2.1 ∩ st.1).card + (d ∩ G).card :=
          card_inter_union_le_add_bound _ _ _ hdel
        have hp_false : p d = false := Bool.eq_false_of_ne_true hp
        have h_rhs : c + (if p d then W else 0) +
            (if !p d then (d ∩ G).card else 0) = c + (d ∩ G).card := by
          simp [hp_false]
        rw [h_rhs]
        omega

/-- Splitting the deletions by a predicate `p` bounds the number of window refreshes: as long as
some ground element survives, the refresh count times `W` is at most `W` per `p`-deletion plus
the total number of ground elements removed by the remaining deletions. -/
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
      have hsurvStep : (G \ (step G first st d).1).Nonempty := by
        rw [he]
        obtain ⟨x, hx⟩ := hsurv_local
        rw [Finset.mem_sdiff] at hx
        exact ⟨x, Finset.mem_sdiff.mpr ⟨hx.1, fun hmem => hx.2 (h_final_mono hmem)⟩⟩
      have h_step := step_preserves_window_invariant G W first hsub hcard p st d c P
        hP₁ hP₂ hP₃ hP₄ hP₅ hP₆ hP₇ hsurvStep
      have hcredit :
          c + ((d :: L').filter p).length * W +
              (((d :: L').filter (fun d => !p d)).map (fun d => (d ∩ G).card)).sum
            = (c + (if p d then W else 0) + (if !p d then (d ∩ G).card else 0)) +
                (L'.filter p).length * W +
                ((L'.filter (fun d => !p d)).map (fun d => (d ∩ G).card)).sum :=
        splitCredit_cons G W c p d L'
      rw [hcredit]
      have h_fin_mono_2 :
          (step G first st d).1 ⊆ (L'.foldl (step G first) (step G first st d)).1 := by rwa [he]
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
  obtain ⟨P, hP₁, -, hP₃, -, -, -, hP₈⟩ :=
    h_inv L (∅, first G, 0) 0 hinit (Finset.empty_subset _) hsurv
  have hz : (L.filter p).length * W + ((L.filter (fun d => !p d)).map (fun d => (d ∩ G).card)).sum =
    0 + (L.filter p).length * W + ((L.filter (fun d => !p d)).map (fun d => (d ∩ G).card)).sum :=
        by ring
  rw [hz]
  exact hP₃.trans (hP₈.trans' (by linarith))

/-- The division form of the split refresh bound: the refresh count is at most the number of
`p`-deletions plus the ground elements removed by the other deletions divided by the window
size. -/
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

/-- The split refresh bound stated with the deletions counted as a finite set, valid when the list
of deletions has no duplicates. -/
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
          push Not
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

/-- If a nonempty subset of the ground set is untouched by every deletion, then the final window
still contains an undeleted element. -/
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
        · simp only [h, ite_true]
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
        · simp only [h, ite_false]
          exact Finset.sdiff_nonempty.mpr h
      exact ih (step G first st d) (he ▸ h_ne') (he ▸ h_surv_del') hdisj_M'
  have h_init_ne : ((first G) \ ∅).Nonempty := by
    have h_disj_first : Disjoint (first G) ∅ := Finset.disjoint_empty_right _
    have heq : first G \ ∅ = first G := Finset.sdiff_eq_self_iff_disjoint.mpr h_disj_first
    rw [heq]
    exact hfirst_ne G (hSurv.mono hSurvG)
  exact (h_foldl_nonempty L (∅, first G, 0) h_init_ne (Finset.disjoint_empty_right _) hdisj).1

/-- A single greedy step never decreases the refresh counter. -/
theorem step_count_mono {α : Type} [DecidableEq α] (G : Finset α) (first : Finset α → Finset α)
    (st : Finset α × Finset α × ℕ) (d : Finset α) :
    st.2.2 ≤ (step G first st d).2.2 := by
  unfold step
  dsimp only
  split_ifs
  · exact Nat.le_add_right _ _
  · exact le_rfl

/-- Processing a list of deletions never decreases the refresh counter. -/
theorem foldl_count_mono {α : Type} [DecidableEq α] (G : Finset α) (first : Finset α → Finset α)
    (L : List (Finset α)) :
    ∀ st : Finset α × Finset α × ℕ, st.2.2 ≤ (L.foldl (step G first) st).2.2 := by
  intro st
  induction L generalizing st with
  | nil => exact le_rfl
  | cons d L ih =>
    exact (step_count_mono G first st d).trans (ih (step G first st d))

/-- If the refresh counter is unchanged over a run, the window is unchanged as well. -/
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

/-- The deleted set only grows along a run. -/
theorem fold_deleted_mono {α : Type} [DecidableEq α] (G : Finset α) (first : Finset α → Finset α)
    (L : List (Finset α)) :
    ∀ st : Finset α × Finset α × ℕ, st.1 ⊆ (L.foldl (step G first) st).1 := by
  intro st
  exact foldl_deleted_mono G first L st

/-- A block of positive size taken from a nonempty set is nonempty. -/
theorem firstBlock_nonempty {α : Type} [DecidableEq α] (key : α → ℕ) (K : ℕ) (hK : 0 < K)
    (S : Finset α) (hS : S.Nonempty) :
    (firstBlock key K S).Nonempty := by
  rw [← Finset.card_pos, firstBlock_card]
  exact lt_min hK (Finset.card_pos.mpr hS)

/-- If some ground element survives the run and the initial window is not already deleted, then the
final window is not contained in the final deleted set either. -/
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
        rw [ite_eq_left h_ref]
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

end Kolmogorov.GreedyWindow
