/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Combinatorics.Bipartite
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Induction
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# On-line matching in bipartite graphs

The adversary presents distinct left vertices one by one; after each of them we must pick a
right neighbour immediately, and all picked neighbours must be different.  A strategy sees the
list of the vertices presented so far (its own earlier answers are a function of that list),
so it is a map `List L → L → R`; `onlineRun` replays it along a list of presented vertices.

`AllowsOnlineMatching g k` is the book's "`E` allows on-line matching of size `k`", and
`exists_onlineMatching_graph` is the graph whose existence is proved on SUV pp. 375–376.

The proof follows the book.  A graph with the expansion property of Section 12.3 admits a
*weak* strategy — "pick an unused neighbour if there is one, otherwise skip the vertex" — that
skips at most half of `2^m` presented vertices (`skippedList_length_le`); the skipped
vertices are forwarded to a graph for `m - 1` on a disjoint right part
(`allowsOnlineMatching_sumGraph`), and the recursion ends at `m = 0` (`exists_levelGraph`).
The resulting graph is relabelled onto `Fin (2^a) × Fin (2^m * a^c)` by `relabel`.

SUV Section 12.5, pp. 375–376.
-/

namespace Kolmogorov

variable {L R : Type*} [DecidableEq L] [DecidableEq R]

/-- The answers of an on-line strategy `s` along the list `vs` of presented left vertices: the
`i`-th answer is the strategy applied to the first `i` presented vertices and to the `i`-th
one.

SUV Section 12.5, p. 375. -/
def onlineRun (s : List L → L → R) (vs : List L) : List R :=
  vs.mapIdx fun i v => s (vs.take i) v

/-- `g` allows on-line matching of size `k`: some strategy answers every sequence of at most
`k` distinct left vertices with neighbours of them that are pairwise distinct.

SUV Section 12.5, p. 375. -/
def AllowsOnlineMatching (g : Finset (L × R)) (k : ℕ) : Prop :=
  ∃ s : List L → L → R, ∀ vs : List L, vs.Nodup → vs.length ≤ k →
    (∀ p ∈ vs.zip (onlineRun s vs), p ∈ g) ∧ (onlineRun s vs).Nodup

private theorem mapIdx_congr_left {α β : Type*} (l : List α) (f g : ℕ → α → β)
    (h : ∀ i (hi : i < l.length), f i l[i] = g i l[i]) : l.mapIdx f = l.mapIdx g := by
  apply List.ext_getElem (by simp)
  intro i h1 _
  simp only [List.getElem_mapIdx]
  exact h i (by simpa using h1)

omit [DecidableEq L] [DecidableEq R] in
/-- Presenting one more vertex appends the strategy's answer on the previous list.

SUV Section 12.5, p. 375. -/
theorem onlineRun_append_singleton (s : List L → L → R) (vs : List L) (v : L) :
    onlineRun s (vs ++ [v]) = onlineRun s vs ++ [s vs v] := by
  unfold onlineRun
  rw [List.mapIdx_concat, List.take_left]
  congr 1
  apply mapIdx_congr_left
  intro i hi
  rw [List.take_append_of_le_length hi.le]

omit [DecidableEq L] [DecidableEq R] in
/-- The run of a strategy has one answer per presented vertex.

SUV Section 12.5, p. 375. -/
@[simp] theorem length_onlineRun (s : List L → L → R) (vs : List L) :
    (onlineRun s vs).length = vs.length := by
  simp [onlineRun]

private theorem nodup_append_singleton {α : Type*} (l : List α) (a : α) :
    (l ++ [a]).Nodup ↔ a ∉ l ∧ l.Nodup := by
  rw [List.nodup_append_comm]
  exact List.nodup_cons

/-! ### The greedy weak strategy and the disjoint union of two graphs -/

section Combine

variable {R₁ R₂ : Type*} [DecidableEq R₁] [DecidableEq R₂]

/-- The disjoint union of two graphs on the same left part: the right part is `R₁ ⊕ R₂`. -/
private def sumGraph (g₁ : Finset (L × R₁)) (g₂ : Finset (L × R₂)) :
    Finset (L × (R₁ ⊕ R₂)) :=
  g₁.image (fun e => (e.1, Sum.inl e.2)) ∪ g₂.image (fun e => (e.1, Sum.inr e.2))

private theorem mem_sumGraph_inl (g₁ : Finset (L × R₁)) (g₂ : Finset (L × R₂)) (l : L)
    (r : R₁) : (l, Sum.inl r) ∈ sumGraph g₁ g₂ ↔ (l, r) ∈ g₁ := by
  simp [sumGraph, Prod.ext_iff]

private theorem mem_sumGraph_inr (g₁ : Finset (L × R₁)) (g₂ : Finset (L × R₂)) (l : L)
    (r : R₂) : (l, Sum.inr r) ∈ sumGraph g₁ g₂ ↔ (l, r) ∈ g₂ := by
  simp [sumGraph, Prod.ext_iff]

private theorem mem_neighbors (g : Finset (L × R)) (l : L) (r : R) :
    r ∈ neighbors g l ↔ (l, r) ∈ g := by
  simp only [neighbors, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨⟨l', r'⟩, ⟨he, rfl⟩, rfl⟩
    exact he
  · intro h
    exact ⟨(l, r), ⟨h, rfl⟩, rfl⟩

private theorem leftDegree_sumGraph_le (g₁ : Finset (L × R₁)) (g₂ : Finset (L × R₂))
    (l : L) : leftDegree (sumGraph g₁ g₂) l ≤ leftDegree g₁ l + leftDegree g₂ l := by
  have h : neighbors (sumGraph g₁ g₂) l ⊆
      (neighbors g₁ l).image Sum.inl ∪ (neighbors g₂ l).image Sum.inr := by
    intro r hr
    rcases r with r | r
    · rw [mem_neighbors, mem_sumGraph_inl] at hr
      exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ ((mem_neighbors _ _ _).2 hr))
    · rw [mem_neighbors, mem_sumGraph_inr] at hr
      exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ ((mem_neighbors _ _ _).2 hr))
  unfold leftDegree
  exact (Finset.card_le_card h).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add Finset.card_image_le Finset.card_image_le))

/-- One move of the greedy weak strategy on `g₁`: the state is the set of used right vertices
together with the list of skipped left vertices.  A vertex with an unused neighbour is served
by one of them, a vertex without is skipped. -/
private noncomputable def greedyStep (g₁ : Finset (L × R₁)) (st : Finset R₁ × List L)
    (v : L) : Finset R₁ × List L :=
  if h : (neighbors g₁ v \ st.1).Nonempty then (insert (Classical.choose h) st.1, st.2)
  else (st.1, st.2 ++ [v])

private noncomputable def greedyState (g₁ : Finset (L × R₁)) (vs : List L) :
    Finset R₁ × List L :=
  vs.foldl (greedyStep g₁) (∅, [])

private theorem greedyState_append (g₁ : Finset (L × R₁)) (vs : List L) (v : L) :
    greedyState g₁ (vs ++ [v]) = greedyStep g₁ (greedyState g₁ vs) v := by
  simp [greedyState, List.foldl_append]

/-- The strategy on the disjoint union: play greedily on `g₁`, and forward the skipped vertices
to the strategy `s₂` on `g₂`. -/
private noncomputable def combineStrategy (g₁ : Finset (L × R₁)) (s₂ : List L → L → R₂)
    (vs : List L) (v : L) : R₁ ⊕ R₂ :=
  if h : (neighbors g₁ v \ (greedyState g₁ vs).1).Nonempty then Sum.inl (Classical.choose h)
  else Sum.inr (s₂ (greedyState g₁ vs).2 v)

/-- The bookkeeping invariant of the greedy strategy: the skipped vertices form a sublist of
the presented ones, served plus skipped equals presented, and every neighbour of a skipped
vertex is used. -/
private structure GreedyInv (g₁ : Finset (L × R₁)) (vs : List L) : Prop where
  sub : List.Sublist (greedyState g₁ vs).2 vs
  count : (greedyState g₁ vs).1.card + (greedyState g₁ vs).2.length = vs.length
  covered : ∀ v ∈ (greedyState g₁ vs).2, neighbors g₁ v ⊆ (greedyState g₁ vs).1

private theorem greedyInv (g₁ : Finset (L × R₁)) (vs : List L) : GreedyInv g₁ vs := by
  induction vs using List.reverseRecOn with
  | nil => exact ⟨by simp [greedyState], by simp [greedyState], by simp [greedyState]⟩
  | append_singleton vs v ih =>
    by_cases h : (neighbors g₁ v \ (greedyState g₁ vs).1).Nonempty
    · have hst : greedyState g₁ (vs ++ [v]) =
          (insert (Classical.choose h) (greedyState g₁ vs).1, (greedyState g₁ vs).2) := by
        rw [greedyState_append, greedyStep, dite_eq_left h]
      have hmem := Classical.choose_spec h
      rw [Finset.mem_sdiff] at hmem
      refine ⟨?_, ?_, ?_⟩
      · rw [hst]; exact ih.sub.trans (List.sublist_append_left _ _)
      · rw [hst]
        simp only [List.length_append, List.length_singleton]
        rw [Finset.card_insert_of_notMem hmem.2]
        have := ih.count
        omega
      · rw [hst]
        intro w hw
        exact (ih.covered w hw).trans (Finset.subset_insert _ _)
    · have hst : greedyState g₁ (vs ++ [v]) =
          ((greedyState g₁ vs).1, (greedyState g₁ vs).2 ++ [v]) := by
        rw [greedyState_append, greedyStep, dite_eq_right h]
      rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at h
      refine ⟨?_, ?_, ?_⟩
      · rw [hst]; exact ih.sub.append (List.Sublist.refl _)
      · rw [hst]
        simp only [List.length_append, List.length_singleton]
        have := ih.count
        omega
      · rw [hst]
        intro w hw
        rw [List.mem_append, List.mem_singleton] at hw
        rcases hw with hw | rfl
        · exact ih.covered w hw
        · exact h

/-- The counting argument of SUV p. 376: on an expanding graph, among at most `2k` distinct
presented vertices the greedy strategy skips at most `k`.  Otherwise `k` skipped vertices have
all their (more than `k`) neighbours among fewer than `k` used ones. -/
private theorem skippedList_length_le {k : ℕ} (hk : 0 < k) (g₁ : Finset (L × R₁))
    (hexp : IsExpanding g₁ k) (vs : List L) (hnd : vs.Nodup) (hlen : vs.length ≤ 2 * k) :
    (greedyState g₁ vs).2.length ≤ k := by
  have inv := greedyInv g₁ vs
  by_contra h
  push Not at h
  have hsknd : (greedyState g₁ vs).2.Nodup := inv.sub.nodup hnd
  set T := ((greedyState g₁ vs).2.take k).toFinset with hTdef
  have hT : T.card = k := by
    rw [hTdef, List.toFinset_card_of_nodup ((List.take_sublist _ _).nodup hsknd)]
    simp only [List.length_take]
    omega
  have hTne : T.Nonempty := by
    rw [← Finset.card_pos, hT]
    exact hk
  have hsub : neighborSet g₁ T ⊆ (greedyState g₁ vs).1 := by
    intro r hr
    rw [neighborSet, Finset.mem_biUnion] at hr
    obtain ⟨v, hv, hr⟩ := hr
    exact inv.covered v (List.mem_of_mem_take (List.mem_toFinset.1 hv)) hr
  have h1 := hexp T hTne hT.le
  have h2 := Finset.card_le_card hsub
  have h3 := inv.count
  omega

/-- The invariant of the combined run: all answers are edges, they are pairwise distinct,
the `inl` answers are used vertices of the greedy state, and the `inr` answers are exactly the
run of `s₂` on the skipped vertices. -/
private structure RunInv (g₁ : Finset (L × R₁)) (g₂ : Finset (L × R₂))
    (s₂ : List L → L → R₂) (vs : List L) : Prop where
  edges : ∀ p ∈ vs.zip (onlineRun (combineStrategy g₁ s₂) vs), p ∈ sumGraph g₁ g₂
  nodup : (onlineRun (combineStrategy g₁ s₂) vs).Nodup
  left : ∀ r, Sum.inl r ∈ onlineRun (combineStrategy g₁ s₂) vs → r ∈ (greedyState g₁ vs).1
  right : (onlineRun (combineStrategy g₁ s₂) vs).filterMap Sum.getRight? =
    onlineRun s₂ (greedyState g₁ vs).2

private theorem runInv_nil (g₁ : Finset (L × R₁)) (g₂ : Finset (L × R₂))
    (s₂ : List L → L → R₂) : RunInv g₁ g₂ s₂ [] :=
  ⟨by simp [onlineRun], by simp [onlineRun], by simp [onlineRun], by simp [onlineRun, greedyState]⟩

private theorem runInv_append {k : ℕ} (hk : 0 < k) (g₁ : Finset (L × R₁))
    (hexp : IsExpanding g₁ k) (g₂ : Finset (L × R₂)) (s₂ : List L → L → R₂)
    (hs₂ : ∀ vs : List L, vs.Nodup → vs.length ≤ k →
      (∀ p ∈ vs.zip (onlineRun s₂ vs), p ∈ g₂) ∧ (onlineRun s₂ vs).Nodup)
    (vs : List L) (v : L) (hnd : (vs ++ [v]).Nodup) (hlen : (vs ++ [v]).length ≤ 2 * k)
    (inv : RunInv g₁ g₂ s₂ vs) : RunInv g₁ g₂ s₂ (vs ++ [v]) := by
  have hrun := onlineRun_append_singleton (combineStrategy g₁ s₂) vs v
  have hzip : (vs ++ [v]).zip (onlineRun (combineStrategy g₁ s₂) vs ++
      [combineStrategy g₁ s₂ vs v]) =
      vs.zip (onlineRun (combineStrategy g₁ s₂) vs) ++ [(v, combineStrategy g₁ s₂ vs v)] :=
    List.zip_append (by simp)
  by_cases h : (neighbors g₁ v \ (greedyState g₁ vs).1).Nonempty
  · have hst : greedyState g₁ (vs ++ [v]) =
        (insert (Classical.choose h) (greedyState g₁ vs).1, (greedyState g₁ vs).2) := by
      rw [greedyState_append, greedyStep, dite_eq_left h]
    have hans : combineStrategy g₁ s₂ vs v = Sum.inl (Classical.choose h) := by
      rw [combineStrategy, dite_eq_left h]
    have hmem := Classical.choose_spec h
    rw [Finset.mem_sdiff] at hmem
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hrun, hzip]
      intro p hp
      rw [List.mem_append, List.mem_singleton] at hp
      rcases hp with hp | rfl
      · exact inv.edges p hp
      · rw [hans, mem_sumGraph_inl]
        exact (mem_neighbors _ _ _).1 hmem.1
    · rw [hrun, hans, nodup_append_singleton]
      refine ⟨fun hin => hmem.2 (inv.left _ hin), inv.nodup⟩
    · rw [hrun, hans, hst]
      intro r hr
      rw [List.mem_append, List.mem_singleton, Sum.inl.injEq] at hr
      rcases hr with hr | rfl
      · exact Finset.mem_insert_of_mem (inv.left r hr)
      · exact Finset.mem_insert_self _ _
    · rw [hrun, hans, hst, List.filterMap_append, inv.right]
      simp [Sum.getRight?]
  · have hst : greedyState g₁ (vs ++ [v]) =
        ((greedyState g₁ vs).1, (greedyState g₁ vs).2 ++ [v]) := by
      rw [greedyState_append, greedyStep, dite_eq_right h]
    have hans : combineStrategy g₁ s₂ vs v = Sum.inr (s₂ (greedyState g₁ vs).2 v) := by
      rw [combineStrategy, dite_eq_right h]
    have hsk : (greedyState g₁ (vs ++ [v])).2.length ≤ k :=
      skippedList_length_le hk g₁ hexp (vs ++ [v]) hnd hlen
    rw [hst] at hsk
    have hsknd : ((greedyState g₁ vs).2 ++ [v]).Nodup :=
      ((greedyInv g₁ vs).sub.append (List.Sublist.refl _)).nodup hnd
    obtain ⟨hedges₂, hnodup₂⟩ := hs₂ _ hsknd hsk
    rw [onlineRun_append_singleton] at hedges₂ hnodup₂
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hrun, hzip]
      intro p hp
      rw [List.mem_append, List.mem_singleton] at hp
      rcases hp with hp | rfl
      · exact inv.edges p hp
      · rw [hans, mem_sumGraph_inr]
        apply hedges₂
        rw [List.zip_append (by simp)]
        exact List.mem_append_right _ (List.mem_singleton_self _)
    · rw [hrun, hans, nodup_append_singleton]
      refine ⟨fun hin => ?_, inv.nodup⟩
      have : s₂ (greedyState g₁ vs).2 v ∈ onlineRun s₂ (greedyState g₁ vs).2 := by
        rw [← inv.right, List.mem_filterMap]
        exact ⟨_, hin, rfl⟩
      exact ((nodup_append_singleton _ _).1 hnodup₂).1 this
    · rw [hrun, hans, hst]
      intro r hr
      rw [List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | hr
      · exact inv.left r hr
      · cases hr
    · rw [hrun, hans, hst, List.filterMap_append, inv.right, onlineRun_append_singleton]
      simp [Sum.getRight?]

/-- The combination step of SUV p. 376: an expanding graph for `k` (the weak strategy) and a
graph allowing on-line matching of size `k` (for the skipped vertices) give, on the disjoint
union of their right parts, on-line matching of size `2k`. -/
private theorem allowsOnlineMatching_sumGraph {k : ℕ} (hk : 0 < k) (g₁ : Finset (L × R₁))
    (hexp : IsExpanding g₁ k) (g₂ : Finset (L × R₂)) (h₂ : AllowsOnlineMatching g₂ k) :
    AllowsOnlineMatching (sumGraph g₁ g₂) (2 * k) := by
  obtain ⟨s₂, hs₂⟩ := h₂
  refine ⟨combineStrategy g₁ s₂, fun vs => ?_⟩
  suffices h : vs.Nodup → vs.length ≤ 2 * k → RunInv g₁ g₂ s₂ vs from
    fun hnd hlen => ⟨(h hnd hlen).edges, (h hnd hlen).nodup⟩
  induction vs using List.reverseRecOn with
  | nil => intro _ _; exact runInv_nil g₁ g₂ s₂
  | append_singleton vs v ih =>
    intro hnd hlen
    have hlen' : vs.length ≤ 2 * k := by simp at hlen; omega
    exact runInv_append hk g₁ hexp g₂ s₂ hs₂ vs v hnd hlen (ih hnd.of_append_left hlen')

end Combine


/-! ### Relabelling the parts, the two trivial graphs, and the recursion on `m` -/

section Relabel

variable {L' R' : Type*} [DecidableEq L'] [DecidableEq R']

/-- The image of a graph under maps of its two parts. -/
private def relabel (e : L → L') (f : R → R') (g : Finset (L × R)) : Finset (L' × R') :=
  g.image (Prod.map e f)

omit [DecidableEq L] [DecidableEq R] [DecidableEq L'] [DecidableEq R'] in
private theorem onlineRun_relabel (e : L ≃ L') (f : R → R') (s : List L → L → R)
    (vs' : List L') :
    onlineRun (fun ws v => f (s (ws.map e.symm) (e.symm v))) vs' =
      (onlineRun s (vs'.map e.symm)).map f := by
  unfold onlineRun
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.map_take]

omit [DecidableEq L] [DecidableEq R] in
private theorem allowsOnlineMatching_relabel (e : L ≃ L') {f : R → R'} (hf : f.Injective)
    (g : Finset (L × R)) (k : ℕ) (h : AllowsOnlineMatching g k) :
    AllowsOnlineMatching (relabel e f g) k := by
  obtain ⟨s, hs⟩ := h
  refine ⟨fun ws v => f (s (ws.map e.symm) (e.symm v)), fun vs' hnd hlen => ?_⟩
  obtain ⟨vs, rfl⟩ : ∃ vs : List L, vs' = vs.map e := ⟨vs'.map e.symm, by simp⟩
  have hvs : (vs.map e).map e.symm = vs := by simp
  rw [onlineRun_relabel, hvs]
  have hnd' : vs.Nodup := List.Nodup.of_map e hnd
  have hlen' : vs.length ≤ k := by simpa using hlen
  obtain ⟨hedges, hnodup⟩ := hs vs hnd' hlen'
  refine ⟨?_, hnodup.map hf⟩
  intro p hp
  rw [List.zip_map, List.mem_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  exact Finset.mem_image_of_mem _ (hedges q hq)

private theorem leftDegree_relabel_le (e : L ≃ L') (f : R → R') (g : Finset (L × R))
    (l : L) : leftDegree (relabel e f g) (e l) ≤ leftDegree g l := by
  have h : neighbors (relabel e f g) (e l) ⊆ (neighbors g l).image f := by
    intro r' hr'
    rw [mem_neighbors] at hr'
    simp only [relabel, Finset.mem_image] at hr'
    obtain ⟨⟨l₀, r₀⟩, he, hp⟩ := hr'
    simp only [Prod.map, Prod.mk.injEq, e.apply_eq_iff_eq] at hp
    obtain ⟨rfl, rfl⟩ := hp
    exact Finset.mem_image_of_mem f ((mem_neighbors _ _ _).2 he)
  unfold leftDegree
  exact (Finset.card_le_card h).trans Finset.card_image_le

end Relabel

private theorem leftDegree_le_card [Fintype R] (g : Finset (L × R)) (l : L) :
    leftDegree g l ≤ Fintype.card R :=
  Finset.card_le_univ _

omit [DecidableEq L] [DecidableEq R] in
/-- The complete bipartite graph allows on-line matching of size `1`: the last level of the
book's recursion, where "the matching task is trivial". -/
private theorem allowsOnlineMatching_univ_one [Fintype L] [Fintype R] [Inhabited R] :
    AllowsOnlineMatching (Finset.univ : Finset (L × R)) 1 := by
  refine ⟨fun _ _ => default, fun vs _ hlen => ⟨fun p _ => Finset.mem_univ p, ?_⟩⟩
  match vs with
  | [] => simp [onlineRun]
  | [v] => simp [onlineRun]
  | _ :: _ :: _ => simp at hlen

/-- The graph of a function `L → R`: each left vertex has the single neighbour `f l`. -/
private def graphOf [Fintype L] (f : L → R) : Finset (L × R) :=
  Finset.univ.image fun l => (l, f l)

private theorem leftDegree_graphOf_le [Fintype L] (f : L → R) (l : L) :
    leftDegree (graphOf f) l ≤ 1 := by
  have h : neighbors (graphOf f) l ⊆ {f l} := by
    intro r hr
    rw [mem_neighbors] at hr
    simp only [graphOf, Finset.mem_image, Finset.mem_univ, true_and, Prod.mk.injEq] at hr
    obtain ⟨l', rfl, rfl⟩ := hr
    exact Finset.mem_singleton_self _
  unfold leftDegree
  exact (Finset.card_le_card h).trans (by simp)

private theorem snd_eq_of_mem_zip_map {α β : Type*} (f : α → β) (vs : List α) (p : α × β)
    (hp : p ∈ vs.zip (vs.map f)) : p.2 = f p.1 := by
  induction vs with
  | nil => simp at hp
  | cons v vs ih =>
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at hp
    rcases hp with rfl | hp
    · rfl
    · exact ih hp

omit [DecidableEq L] [DecidableEq R] in
private theorem onlineRun_const (f : L → R) (vs : List L) :
    onlineRun (fun _ v => f v) vs = vs.map f := by
  unfold onlineRun
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp

private theorem allowsOnlineMatching_graphOf [Fintype L] {f : L → R} (hf : f.Injective)
    (k : ℕ) : AllowsOnlineMatching (graphOf f) k := by
  refine ⟨fun _ v => f v, fun vs hnd _ => ?_⟩
  rw [onlineRun_const]
  refine ⟨fun p hp => ?_, hnd.map hf⟩
  have := snd_eq_of_mem_zip_map f vs p hp
  simp only [graphOf, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨p.1, Prod.ext rfl this.symm⟩

private theorem card_boolVec (n : ℕ) : Fintype.card (BoolVec n) = 2 ^ n := by
  change Fintype.card (Fin n → Bool) = _
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

/-- The recursion of SUV p. 376: for `m ≤ a` there is a graph on `𝔹ᵃ` with fewer than
`2^(m+1)` right vertices, left degree at most `1 + m (a + m + 2)`, allowing on-line matching
of size `2^m`.  Level `m + 1` is the disjoint union of the expander of Section 12.3 for
`m + 1` and the graph of level `m`. -/
private theorem exists_levelGraph (a : ℕ) : ∀ m : ℕ, m ≤ a →
    ∃ (R : Type) (_ : Fintype R) (_ : DecidableEq R) (g : Finset (BoolVec a × R)),
      Fintype.card R + 1 ≤ 2 ^ (m + 1) ∧ (∀ l, leftDegree g l ≤ 1 + m * (a + m + 2)) ∧
      AllowsOnlineMatching g (2 ^ m) := by
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨Unit, inferInstance, inferInstance, Finset.univ, by simp, fun l => ?_, ?_⟩
    · simpa using leftDegree_le_card (Finset.univ : Finset (BoolVec a × Unit)) l
    · exact allowsOnlineMatching_univ_one
  | succ m ih =>
    intro hma
    obtain ⟨R₂, _, _, g₂, hcard₂, hdeg₂, hmatch₂⟩ := ih (Nat.le_of_succ_le hma)
    obtain ⟨g₁, hdeg₁, hexp₁⟩ :=
      exists_expanding_bipartiteGraph a (m + 1) (Nat.succ_pos m) hma
    rw [Nat.add_sub_cancel] at hexp₁
    refine ⟨BoolVec (m + 1) ⊕ R₂, inferInstance, inferInstance, sumGraph g₁ g₂, ?_, ?_, ?_⟩
    · rw [Fintype.card_sum, card_boolVec]
      have : 2 ^ (m + 2) = 2 * 2 ^ (m + 1) := pow_succ' 2 (m + 1)
      omega
    · intro l
      refine (leftDegree_sumGraph_le g₁ g₂ l).trans ?_
      have h1 := hdeg₁ l
      have h2 := hdeg₂ l
      nlinarith
    · rw [pow_succ']
      exact allowsOnlineMatching_sumGraph (by positivity) g₁ hexp₁ g₂ hmatch₂

/-- For some constant `c` and all `m ≤ a` there is a bipartite graph with `2^a` left vertices,
`2^m * a^c` right vertices and left degree at most `a^c` that allows on-line matching of size
`2^m`.

The hypothesis `0 < a` is ours: the book writes "for all `a` and `m` such that `a ≥ m`", which
is false as printed: `c = 0` fails at `a = 2`, `m = 1` (four left vertices of degree one
cannot be matched on-line into two right vertices), and for `c > 0` the right part
`2^0 * 0^c` at `a = m = 0` is empty.  The proof only concerns positive `a`.  The case `m = 0`
is kept, as in the book, where it is the trivial last level of the proof's recursion.

SUV Theorem 231, pp. 375–376. -/
theorem exists_onlineMatching_graph :
    ∃ c : ℕ, ∀ a m : ℕ, 0 < a → m ≤ a →
      ∃ g : Finset (Fin (2 ^ a) × Fin (2 ^ m * a ^ c)),
        (∀ l, leftDegree g l ≤ a ^ c) ∧ AllowsOnlineMatching g (2 ^ m) := by
  refine ⟨5, fun a m ha hma => ?_⟩
  rcases Nat.lt_or_ge a 2 with ha2 | ha2
  · obtain rfl : a = 1 := by omega
    interval_cases m
    · have : Inhabited (Fin (2 ^ 0 * 1 ^ 5)) := ⟨⟨0, by norm_num⟩⟩
      refine ⟨Finset.univ, fun l => ?_, ?_⟩
      · exact (leftDegree_le_card _ _).trans (by simp)
      · rw [pow_zero]
        exact allowsOnlineMatching_univ_one
    · refine ⟨graphOf (Fin.cast (by norm_num) : Fin (2 ^ 1) → Fin (2 ^ 1 * 1 ^ 5)),
        fun l => ?_, ?_⟩
      · exact (leftDegree_graphOf_le _ _).trans (by norm_num)
      · exact allowsOnlineMatching_graphOf (Fin.cast_injective _) _
  · obtain ⟨R, _, _, g, hcard, hdeg, hmatch⟩ := exists_levelGraph a m hma
    have ha5 : 2 ≤ a ^ 5 := le_trans ha2 (Nat.le_self_pow (by norm_num) a)
    have hcardR : Fintype.card R ≤ Fintype.card (Fin (2 ^ m * a ^ 5)) := by
      rw [Fintype.card_fin]
      calc Fintype.card R ≤ 2 ^ (m + 1) := by omega
        _ = 2 ^ m * 2 := pow_succ 2 m
        _ ≤ 2 ^ m * a ^ 5 := Nat.mul_le_mul_left _ ha5
    obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le hcardR
    let e : BoolVec a ≃ Fin (2 ^ a) := Fintype.equivFinOfCardEq (card_boolVec a)
    refine ⟨relabel e f g, fun l' => ?_, allowsOnlineMatching_relabel e f.injective g _ hmatch⟩
    have h1 := leftDegree_relabel_le e f g (e.symm l')
    rw [e.apply_symm_apply] at h1
    refine h1.trans ((hdeg _).trans ?_)
    have h2 : m * (a + m + 2) ≤ a * (a + a + 2) := Nat.mul_le_mul hma (by omega)
    have h3 : 8 * (a * a) ≤ a ^ 5 := by
      have : 8 ≤ a * a * a := by nlinarith
      calc 8 * (a * a) ≤ (a * a * a) * (a * a) := Nat.mul_le_mul_right _ this
        _ = a ^ 5 := by ring
    nlinarith

end Kolmogorov
