import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Rel
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.Density

/-!
# Rectangle Covers and No-Four-Cycle Bound

This file defines combinatorial rectangles, their coverage semantics over finite
bipartite edge sets, and proves the coarse density bound for bipartite graphs
containing no 4-cycles.
-/

namespace Kolmogorov

variable {α β : Type*}

noncomputable section

/-- A combinatorial rectangle is a pair of finite sets of vertices. -/
abbrev CombinatorialRectangle (α β : Type*) :=
  Finset α × Finset β

open Classical in
/-- The set of edges in a family of rectangles under relation `r`. -/
def rectangleFamilyEdges
    (r : α → β → Prop)
    (𝓡 : Finset (CombinatorialRectangle α β)) :
    Finset (α × β) :=
  𝓡.biUnion fun R => Rel.interedges r R.1 R.2

/-- A rectangle family covers a set of edges `E` if `E` is contained in the family's edges. -/
def RectangleFamilyCovers
    (r : α → β → Prop)
    (𝓡 : Finset (CombinatorialRectangle α β))
    (E : Finset (α × β)) : Prop :=
  E ⊆ rectangleFamilyEdges r 𝓡

/-- The relation `r` has no 4-cycles if any two distinct left vertices share at
most one right neighbor. -/
def NoFourCycle (r : α → β → Prop) : Prop :=
  ∀ ⦃a₁ a₂ b₁ b₂⦄,
    r a₁ b₁ → r a₁ b₂ → r a₂ b₁ → r a₂ b₂ →
      a₁ = a₂ ∨ b₁ = b₂

open Classical in
lemma card_interedges_eq_sum_card_neighbors (r : α → β → Prop) (A : Finset α) (B : Finset β) :
  (Rel.interedges r A B).card =
    ∑ a ∈ A, (B.filter (r a)).card := by
  rw [Rel.interedges_eq_biUnion]
  rw [Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro a ha
    simp
  · intro a ha a' ha' haa'
    rw [Function.onFun, Finset.disjoint_left]
    intro e he he'
    rw [Finset.mem_map] at he he'
    obtain ⟨b, _, rfl⟩ := he
    obtain ⟨b', _, hbb'⟩ := he'
    exact haa' (congrArg Prod.fst hbb').symm

open Classical in
lemma noFourCycle_neighbor_inter_card_le_one
    (r : α → β → Prop) {B : Finset β} {a₁ a₂ : α} :
  NoFourCycle r →
  a₁ ≠ a₂ →
  ((B.filter (r a₁)) ∩ (B.filter (r a₂))).card ≤ 1 := by
  intro hfour hne
  rw [Finset.card_le_one_iff]
  intro b₁ b₂ hb₁ hb₂
  simp only [Finset.mem_inter, Finset.mem_filter] at hb₁ hb₂
  exact (hfour hb₁.1.2 hb₂.1.2 hb₁.2.2 hb₂.2.2).resolve_left hne

open Classical in
lemma card_inter_biUnion_le {A : Finset α} {N : α → Finset β} {a₀ : α} :
  (∀ a ∈ A, ((N a₀) ∩ (N a)).card ≤ 1) →
  ((N a₀) ∩ A.biUnion N).card ≤ A.card := by
  intro hinter
  rw [Finset.inter_biUnion]
  calc
    (A.biUnion fun a => N a₀ ∩ N a).card
        ≤ ∑ a ∈ A, ((N a₀) ∩ (N a)).card := Finset.card_biUnion_le
    _ ≤ ∑ _ ∈ A, 1 := Finset.sum_le_sum fun a ha => hinter a ha
    _ = A.card := by simp

open Classical in
lemma sum_card_le_card_biUnion_add_choose_two {A : Finset α} {N : α → Finset β} :
  (∀ a ∈ A, ∀ a' ∈ A, a ≠ a' →
    ((N a) ∩ (N a')).card ≤ 1) →
  ∑ a ∈ A, (N a).card ≤
    (A.biUnion N).card + Nat.choose A.card 2 := by
  induction A using Finset.induction_on with
  | empty => simp
  | @insert a A ha ih =>
      intro hinter
      have hrest : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → ((N x) ∩ (N y)).card ≤ 1 := by
        intro x hx y hy hxy
        exact hinter x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy) hxy
      have hi := ih hrest
      have hinter_union : ((N a) ∩ A.biUnion N).card ≤ A.card := by
        apply card_inter_biUnion_le
        intro x hx
        exact hinter a (Finset.mem_insert_self a A) x (Finset.mem_insert_of_mem hx)
          (fun hax => ha (hax.symm ▸ hx))
      have hunion := Finset.card_union_add_card_inter (N a) (A.biUnion N)
      rw [Finset.sum_insert ha, Finset.biUnion_insert, Finset.card_insert_of_notMem ha]
      rw [Nat.choose_succ_succ]
      simp only [Nat.reduceSucc, Nat.choose_one_right]
      omega

open Classical in
lemma card_rectangleFamilyEdges_le_sum
    (r : α → β → Prop) (𝓡 : Finset (CombinatorialRectangle α β)) :
  (rectangleFamilyEdges r 𝓡).card ≤
    ∑ R ∈ 𝓡, (Rel.interedges r R.1 R.2).card := by
  exact Finset.card_biUnion_le

open Classical in
lemma card_of_rectangleFamilyCovers_le_sum
    (r : α → β → Prop) {𝓡 : Finset (CombinatorialRectangle α β)}
    {E : Finset (α × β)} :
  RectangleFamilyCovers r 𝓡 E →
  E.card ≤ ∑ R ∈ 𝓡, (Rel.interedges r R.1 R.2).card := by
  intro hcover
  exact (Finset.card_le_card hcover).trans (card_rectangleFamilyEdges_le_sum r 𝓡)

open Classical in
lemma exists_card_subset_retaining_weight
    (A : Finset α) (w : α → Nat) {s : Nat} (hs : s ≤ A.card) :
  ∃ S : Finset α,
    S ⊆ A ∧
    S.card = s ∧
    s * (∑ a ∈ A, w a) ≤
      A.card * (∑ a ∈ S, w a) := by
  -- We prove by strong induction on the "slack" = A.card - s
  have aux : ∀ n, ∀ (A : Finset α) {s : Nat}, s ≤ A.card → A.card - s = n →
    ∃ S : Finset α, S ⊆ A ∧ S.card = s ∧ s * (∑ a ∈ A, w a) ≤ A.card * (∑ a ∈ S, w a) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro A s hs hn
      by_cases hzero : n = 0
      · -- slack = 0 means s = A.card, so S = A works
        have heq : A.card = s := by omega
        exact ⟨A, Finset.Subset.refl _, heq, by simp [heq]⟩
      · -- n > 0 means A.card > s
        have hlt : s < A.card := by omega
        by_cases hs0 : s = 0
        · -- s = 0 case: empty set works
          subst hs0
          exact ⟨∅, Finset.empty_subset _, by simp, by simp⟩
        · -- Find an element with weight at least the average
          -- There must exist such an element (otherwise sum would be < n * average)
          have hA_nonempty : A.Nonempty := Finset.card_pos.mp (by omega : 0 < A.card)
          -- We'll use the element with maximum weight
          obtain ⟨a, ha, hwa⟩ := Finset.exists_min_image A w hA_nonempty
          -- Remove a from A
          let A' := A.erase a
          have hA'_card : A'.card = A.card - 1 := Finset.card_erase_of_mem ha
          -- We need s ≤ A'.card, i.e., s ≤ A.card - 1
          have hsA' : s ≤ A'.card := by omega
          -- Apply IH to A'
          have hn' : A'.card - s = n - 1 := by omega
          have hn_pos : n - 1 < n := by omega
          obtain ⟨S', hS'_sub, hS'_card, hS'_ineq⟩ := ih (n - 1) hn_pos A' hsA' hn'
          use S'
          refine ⟨hS'_sub.trans (Finset.erase_subset _ _), hS'_card, ?_⟩
          -- We need: s * (∑ a ∈ A, w a) ≤ A.card * (∑ a ∈ S', w a)
          -- We have: s * (∑ a ∈ A', w a) ≤ A'.card * (∑ a ∈ S', w a)
          -- Note: ∑ a ∈ A, w a = ∑ a ∈ A', w a + w a  and  A.card = A'.card + 1
          -- Since a is minimum, s * w a ≤ ∑ a' ∈ S', w a'
          have hs_min : s * w a ≤ ∑ a' ∈ S', w a' := by
            calc s * w a = S'.card * w a := by rw [hS'_card]
              _ = ∑ _ ∈ S', w a := by simp
              _ ≤ ∑ a' ∈ S', w a' := Finset.sum_le_sum fun x' hx' =>
                hwa x' (A.mem_of_mem_erase (hS'_sub hx'))
          -- The key algebraic step
          have hsum_eq : ∑ a ∈ A, w a = ∑ a ∈ A', w a + w a := by
            rw [← Finset.sum_erase_add _ _ ha]
          have hcard_eq : A.card = A'.card + 1 := by omega
          calc s * ∑ a ∈ A, w a
              = s * (∑ a ∈ A', w a + w a) := by rw [hsum_eq]
            _ = s * ∑ a ∈ A', w a + s * w a := by ring
            _ ≤ A'.card * ∑ a ∈ S', w a + ∑ a' ∈ S', w a' := add_le_add hS'_ineq hs_min
            _ = (A'.card + 1) * ∑ a ∈ S', w a := by ring
            _ = A.card * ∑ a ∈ S', w a := by rw [hcard_eq]
  exact aux _ A hs rfl

open Classical in
lemma card_interedges_le_card_right_add_choose_two_left
    (r : α → β → Prop) (A : Finset α) (B : Finset β) :
  NoFourCycle r →
  (Rel.interedges r A B).card ≤ B.card + Nat.choose A.card 2 := by
  intro hfour
  rw [card_interedges_eq_sum_card_neighbors]
  refine (sum_card_le_card_biUnion_add_choose_two ?_).trans ?_
  · intro a ha a' ha' hne
    exact noFourCycle_neighbor_inter_card_le_one r hfour hne
  · gcongr
    exact Finset.biUnion_subset.mpr fun a ha => Finset.filter_subset _ _

open Classical in
lemma noFourCycle_sampled_interedges_bound
    (r : α → β → Prop) (A : Finset α) (B : Finset β) {s : Nat} :
  NoFourCycle r →
  s ≤ A.card →
  s * (Rel.interedges r A B).card ≤
    A.card * (B.card + Nat.choose s 2) := by
  intro hfour hs
  obtain ⟨S, _, hS_card, hS_ineq⟩ :=
    exists_card_subset_retaining_weight A (fun a => (B.filter (r a)).card) hs
  rw [card_interedges_eq_sum_card_neighbors]
  have hbound_S := card_interedges_le_card_right_add_choose_two_left r S B hfour
  rw [hS_card, card_interedges_eq_sum_card_neighbors] at hbound_S
  exact hS_ineq.trans (Nat.mul_le_mul_left A.card hbound_S)

end

end Kolmogorov
