/-
Copyright (c) 2025 The Kolmogorov Project Developers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Kolmogorov Project Developers
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.LeastGreatest
import Mathlib.Logic.Relation
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite flow networks and the max-flow min-cut theorem

Capacities and flows are natural numbers, so a flow produced by the max-flow min-cut theorem
is automatically integral — which is what the routing argument of SUV Section 12.9 ("moving
envelopes along the edges") needs.  The value of a flow and the capacity of a cut are integers
so that the source's net outflow is an honest difference.

The max-flow min-cut theorem is proved by the Ford–Fulkerson argument: a flow of maximal value
exists because values are bounded integers; if the sink were reachable from the source in the
residual graph of a maximal flow, pushing one unit along the residual path would give a larger
flow; and for the set `S` of vertices reachable in the residual graph, every edge leaving `S`
is saturated and every edge entering `S` is empty, so the value of the flow equals the
capacity of the cut `S`.

SUV Section 12.9, p. 385 (Ford–Fulkerson, quoted from [45]).
-/

namespace Kolmogorov

/-- A finite flow network: a capacity for every ordered pair of vertices, a source and a
sink.

SUV Section 12.9, p. 385. -/
structure FlowNetwork (V : Type*) [Fintype V] [DecidableEq V] where
  /-- The capacity of the edge from `u` to `v` (zero when there is no edge). -/
  capacity : V → V → ℕ
  /-- The source vertex. -/
  source : V
  /-- The sink vertex. -/
  sink : V
  /-- Source and sink are distinct. -/
  source_ne_sink : source ≠ sink

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A flow in `N`: a natural number on every edge, bounded by the capacity and conserved at
every vertex other than the source and the sink.

SUV Section 12.9, p. 385. -/
structure Flow (N : FlowNetwork V) where
  /-- The amount carried by the edge from `u` to `v`. -/
  value : V → V → ℕ
  /-- No edge carries more than its capacity. -/
  le_capacity : ∀ u v, value u v ≤ N.capacity u v
  /-- Kirchhoff's law at every internal vertex. -/
  conservation : ∀ v, v ≠ N.source → v ≠ N.sink → ∑ u, value u v = ∑ w, value v w

/-- The value of a flow: the net amount leaving the source.

SUV Section 12.9, p. 385. -/
def Flow.netValue {N : FlowNetwork V} (f : Flow N) : ℤ :=
  (∑ w, (f.value N.source w : ℤ)) - ∑ u, (f.value u N.source : ℤ)

/-- The capacity of the cut given by a set `S` of vertices: the total capacity of the edges
leaving `S`.

SUV Section 12.9, p. 385. -/
def FlowNetwork.cutValue (N : FlowNetwork V) (S : Finset V) : ℤ :=
  ∑ u ∈ S, ∑ v ∈ Sᶜ, (N.capacity u v : ℤ)

/-- The excess of an edge function at a vertex: the amount leaving minus the amount entering. -/
private def excess (g : V → V → ℕ) (x : V) : ℤ :=
  (∑ w, (g x w : ℤ)) - ∑ u, (g u x : ℤ)

omit [DecidableEq V] in
private lemma excess_eq_zero_iff (g : V → V → ℕ) (x : V) :
    excess g x = 0 ↔ ∑ u, g u x = ∑ w, g x w := by
  unfold excess
  rw [sub_eq_zero, ← Nat.cast_sum, ← Nat.cast_sum, Nat.cast_inj, eq_comm]

/-- The total excess of a set of vertices is the flow leaving the set minus the flow entering
it: the internal edges cancel. -/
private lemma sum_excess_eq (g : V → V → ℕ) (S : Finset V) :
    ∑ u ∈ S, excess g u =
      ∑ u ∈ S, ∑ w ∈ Sᶜ, (g u w : ℤ) - ∑ u ∈ S, ∑ w ∈ Sᶜ, (g w u : ℤ) := by
  have h1 : ∀ u, excess g u = (∑ w ∈ S, (g u w : ℤ) + ∑ w ∈ Sᶜ, (g u w : ℤ))
      - (∑ v ∈ S, (g v u : ℤ) + ∑ v ∈ Sᶜ, (g v u : ℤ)) := by
    intro u
    simp only [excess, Finset.sum_add_sum_compl]
  have h2 : ∑ u ∈ S, ∑ w ∈ S, (g u w : ℤ) = ∑ u ∈ S, ∑ w ∈ S, (g w u : ℤ) :=
    Finset.sum_comm
  simp only [h1, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  linarith

/-- For a flow, the total excess of a set containing the source but not the sink is the value
of the flow. -/
private lemma netValue_eq_sum_excess {N : FlowNetwork V} (f : Flow N) (S : Finset V)
    (hsource : N.source ∈ S) (hsink : N.sink ∉ S) :
    f.netValue = ∑ u ∈ S, excess f.value u := by
  rw [Finset.sum_eq_single N.source]
  · rfl
  · intro u huS hu
    have hu' : u ≠ N.sink := fun h => hsink (h ▸ huS)
    exact (excess_eq_zero_iff _ _).2 (f.conservation u hu hu')
  · intro h
    exact absurd hsource h

/-- Weak duality: the value of any flow is at most the capacity of any cut separating the
source from the sink.

SUV Section 12.9, p. 385. -/
theorem Flow.netValue_le_cutValue {N : FlowNetwork V} (f : Flow N) (S : Finset V)
    (hsource : N.source ∈ S) (hsink : N.sink ∉ S) :
    f.netValue ≤ N.cutValue S := by
  rw [netValue_eq_sum_excess f S hsource hsink, sum_excess_eq]
  have h1 : ∑ u ∈ S, ∑ w ∈ Sᶜ, (f.value u w : ℤ) ≤ N.cutValue S := by
    unfold FlowNetwork.cutValue
    gcongr with u _ w _
    exact_mod_cast f.le_capacity u w
  have h2 : 0 ≤ ∑ u ∈ S, ∑ w ∈ Sᶜ, (f.value w u : ℤ) :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  linarith

/-- The residual relation of an edge function: one more unit can be pushed from `x` to `y`,
either along a non-saturated edge or by cancelling a unit on the reverse edge. -/
private def Resid (N : FlowNetwork V) (g : V → V → ℕ) (x y : V) : Prop :=
  g x y < N.capacity x y ∨ 0 < g y x

/-- Pushing one unit from `c` to `b` along a residual edge: the excess of `c` grows by one, the
excess of `b` drops by one, and every other residual edge survives. -/
private lemma exists_push (N : FlowNetwork V) (g : V → V → ℕ)
    (hg : ∀ x y, g x y ≤ N.capacity x y) {c b : V} (hcb : Resid N g c b) :
    ∃ g' : V → V → ℕ, (∀ x y, g' x y ≤ N.capacity x y) ∧
      (∀ x, excess g' x = excess g x + (if x = c then 1 else 0) - (if x = b then 1 else 0)) ∧
      (∀ x y, (x, y) ≠ (c, b) → Resid N g x y → Resid N g' x y) := by
  by_cases hbc : 0 < g b c
  · refine ⟨fun x y => if x = b ∧ y = c then g x y - 1 else g x y, ?_, ?_, ?_⟩
    · intro x y
      dsimp only
      split_ifs with h
      · exact (Nat.sub_le _ _).trans (hg x y)
      · exact hg x y
    · have hcast : ∀ x y, ((if x = b ∧ y = c then g x y - 1 else g x y : ℕ) : ℤ)
          = g x y - if x = b ∧ y = c then 1 else 0 := by
        intro x y
        split_ifs with h
        · obtain ⟨rfl, rfl⟩ := h
          rw [Nat.cast_sub hbc]
          simp
        · simp
      intro x
      simp only [excess, hcast, Finset.sum_sub_distrib]
      have e1 : ∑ w, (if x = b ∧ w = c then (1 : ℤ) else 0) = if x = b then 1 else 0 := by
        by_cases hx : x = b
        · subst hx
          simp
        · simp [hx]
      have e2 : ∑ u, (if u = b ∧ x = c then (1 : ℤ) else 0) = if x = c then 1 else 0 := by
        by_cases hx : x = c
        · subst hx
          simp
        · simp [hx]
      rw [e1, e2]
      ring
    · intro x y hxy hres
      unfold Resid at hres ⊢
      dsimp only
      rcases hres with h | h
      · left
        split_ifs with h'
        · exact lt_of_le_of_lt (Nat.sub_le _ _) h
        · exact h
      · right
        have hne : ¬ (y = b ∧ x = c) := fun h' => hxy (Prod.ext h'.2 h'.1)
        rw [ite_eq_right hne]
        exact h
  · have hbc0 : g b c = 0 := by omega
    have hlt : g c b < N.capacity c b := by
      rcases hcb with h | h
      · exact h
      · omega
    refine ⟨fun x y => if x = c ∧ y = b then g x y + 1 else g x y, ?_, ?_, ?_⟩
    · intro x y
      dsimp only
      split_ifs with h
      · obtain ⟨rfl, rfl⟩ := h
        omega
      · exact hg x y
    · have hcast : ∀ x y, ((if x = c ∧ y = b then g x y + 1 else g x y : ℕ) : ℤ)
          = g x y + if x = c ∧ y = b then 1 else 0 := by
        intro x y
        split_ifs <;> simp
      intro x
      simp only [excess, hcast, Finset.sum_add_distrib]
      have e1 : ∑ w, (if x = c ∧ w = b then (1 : ℤ) else 0) = if x = c then 1 else 0 := by
        by_cases hx : x = c
        · subst hx
          simp
        · simp [hx]
      have e2 : ∑ u, (if u = c ∧ x = b then (1 : ℤ) else 0) = if x = b then 1 else 0 := by
        by_cases hx : x = b
        · subst hx
          simp
        · simp [hx]
      rw [e1, e2]
      ring
    · intro x y hxy hres
      have hne : ¬ (x = c ∧ y = b) := fun h' => hxy (Prod.ext h'.1 h'.2)
      unfold Resid at hres ⊢
      dsimp only
      rcases hres with h | h
      · left
        rw [ite_eq_right hne]
        exact h
      · right
        split_ifs with h'
        · omega
        · exact h

/-- A reachable vertex is reachable without ever leaving it: the edges out of the target can be
dropped from the relation. -/
private lemma reflTransGen_avoid {α : Type*} {R : α → α → Prop} {s t : α}
    (h : Relation.ReflTransGen R s t) :
    Relation.ReflTransGen (fun x y => x ≠ t ∧ R x y) s t := by
  suffices H : ∀ b, Relation.ReflTransGen R s b →
      Relation.ReflTransGen (fun x y => x ≠ t ∧ R x y) s b ∨
        Relation.ReflTransGen (fun x y => x ≠ t ∧ R x y) s t by
    rcases H t h with h' | h' <;> exact h'
  intro b hb
  induction hb with
  | refl => exact Or.inl Relation.ReflTransGen.refl
  | @tail c b _ hcb ih =>
    rcases ih with ih | ih
    · by_cases hct : c = t
      · exact Or.inr (hct ▸ ih)
      · exact Or.inl (ih.tail ⟨hct, hcb⟩)
    · exact Or.inr ih

/-- Ford–Fulkerson augmentation: if `t` is reachable from `s` through edges of `E`, all of them
residual for `g`, then one unit can be moved from `s` to `t` within the capacities.  The
induction is on the edge set: after pushing one unit along the last edge `(c, t)` of the path,
the remaining path from `s` to `c` avoids that edge, so it lies in a smaller edge set. -/
private lemma exists_augment (N : FlowNetwork V) (E : Finset (V × V)) :
    ∀ (g : V → V → ℕ) (s t : V), (∀ x y, g x y ≤ N.capacity x y) →
      (∀ p ∈ E, Resid N g p.1 p.2) →
      Relation.ReflTransGen (fun x y => (x, y) ∈ E) s t →
      ∃ g' : V → V → ℕ, (∀ x y, g' x y ≤ N.capacity x y) ∧
        ∀ x, excess g' x = excess g x + (if x = s then 1 else 0) - (if x = t then 1 else 0) := by
  induction E using Finset.strongInduction with
  | H E ih =>
  intro g s t hg hE hst
  have h1 := reflTransGen_avoid hst
  rcases h1.cases_tail with rfl | ⟨c, hsc, hct, hcE⟩
  · exact ⟨g, hg, fun x => by simp⟩
  · obtain ⟨g1, hg1, hex1, hres1⟩ := exists_push N g hg (hE _ hcE)
    have h2 := reflTransGen_avoid hsc
    set E' := E.filter (fun p => p.1 ≠ c ∧ p.1 ≠ t) with hE'
    have hsub : E' ⊂ E := Finset.filter_ssubset.2 ⟨(c, t), hcE, fun h => h.1 rfl⟩
    have hpath : Relation.ReflTransGen (fun x y => (x, y) ∈ E') s c := by
      exact @Relation.ReflTransGen.mono V _ _ (fun x y h =>
        Finset.mem_filter.2 ⟨h.2.2, h.1, h.2.1⟩) s c h2
    have hE'' : ∀ p ∈ E', Resid N g1 p.1 p.2 := by
      intro p hp
      rw [Finset.mem_filter] at hp
      refine hres1 p.1 p.2 ?_ (hE p hp.1)
      intro h
      exact hp.2.1 (congrArg Prod.fst h)
    obtain ⟨g', hg', hex'⟩ := ih E' hsub g1 s c hg1 hE'' hpath
    refine ⟨g', hg', fun x => ?_⟩
    rw [hex', hex1]
    ring

/-- A flow of maximal value exists: values are integers bounded above by the capacity leaving
the source, and the zero flow is a flow. -/
private lemma exists_max_flow (N : FlowNetwork V) :
    ∃ f : Flow N, ∀ g : Flow N, g.netValue ≤ f.netValue := by
  have hbdd : ∃ b : ℤ, ∀ z : ℤ, (∃ f : Flow N, f.netValue = z) → z ≤ b := by
    refine ⟨∑ w, (N.capacity N.source w : ℤ), ?_⟩
    rintro z ⟨g, rfl⟩
    unfold Flow.netValue
    have h1 : ∑ w, (g.value N.source w : ℤ) ≤ ∑ w, (N.capacity N.source w : ℤ) :=
      Finset.sum_le_sum fun w _ => by exact_mod_cast g.le_capacity _ w
    have h2 : 0 ≤ ∑ u, (g.value u N.source : ℤ) :=
      Finset.sum_nonneg fun _ _ => by positivity
    linarith
  have hinh : ∃ z : ℤ, ∃ f : Flow N, f.netValue = z :=
    ⟨0, ⟨fun _ _ => 0, fun _ _ => Nat.zero_le _, fun _ _ _ => rfl⟩, by simp [Flow.netValue]⟩
  obtain ⟨ub, ⟨f, hf⟩, hub⟩ := Int.exists_greatest_of_bdd hbdd hinh
  exact ⟨f, fun g => hf ▸ hub _ ⟨g, rfl⟩⟩

/-- Max-flow min-cut for finite networks with natural-number capacities: some flow attains the
capacity of some cut, hence the maximal flow value equals the minimal cut capacity, and the
maximal flow is integral because flows are `ℕ`-valued by definition.

SUV Section 12.9, p. 385. -/
theorem exists_maxFlow_eq_minCut (N : FlowNetwork V) :
    ∃ (f : Flow N) (S : Finset V), N.source ∈ S ∧ N.sink ∉ S ∧ f.netValue = N.cutValue S := by
  classical
  obtain ⟨f, hf⟩ := exists_max_flow N
  set S : Finset V :=
    Finset.univ.filter (fun v => Relation.ReflTransGen (Resid N f.value) N.source v) with hS
  have hmem : ∀ v, v ∈ S ↔ Relation.ReflTransGen (Resid N f.value) N.source v := by
    intro v
    simp [hS]
  have hsource : N.source ∈ S := (hmem _).2 Relation.ReflTransGen.refl
  have hsink : N.sink ∉ S := by
    intro h
    have hreach := (hmem _).1 h
    set E : Finset (V × V) := Finset.univ.filter (fun p => Resid N f.value p.1 p.2) with hE
    have hpath : Relation.ReflTransGen (fun x y => (x, y) ∈ E) N.source N.sink :=
      @Relation.ReflTransGen.mono V _ _ (fun x y hxy => by simp [hE, hxy])
        N.source N.sink hreach
    obtain ⟨g, hg, hex⟩ := exists_augment N E f.value N.source N.sink f.le_capacity
      (fun p hp => by simpa [hE] using hp) hpath
    let g' : Flow N :=
      { value := g
        le_capacity := hg
        conservation := fun v hv1 hv2 => by
          rw [← excess_eq_zero_iff, hex, ite_eq_right hv1, ite_eq_right hv2, add_zero, sub_zero,
            excess_eq_zero_iff]
          exact f.conservation v hv1 hv2 }
    have h1 : g'.netValue = f.netValue + 1 := by
      change excess g N.source = excess f.value N.source + 1
      rw [hex, ite_eq_left rfl, ite_eq_right N.source_ne_sink]
      ring
    have h2 := hf g'
    omega
  refine ⟨f, S, hsource, hsink, ?_⟩
  rw [netValue_eq_sum_excess f S hsource hsink, sum_excess_eq]
  have hnot : ∀ u ∈ S, ∀ w ∈ Sᶜ, ¬ Resid N f.value u w := by
    intro u hu w hw hR
    rw [Finset.mem_compl] at hw
    exact hw ((hmem w).2 (((hmem u).1 hu).tail hR))
  have h1 : ∑ u ∈ S, ∑ w ∈ Sᶜ, (f.value u w : ℤ) = N.cutValue S := by
    unfold FlowNetwork.cutValue
    refine Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun w hw => ?_
    have h := hnot u hu w hw
    simp only [Resid, not_or, not_lt] at h
    exact_mod_cast le_antisymm (f.le_capacity u w) h.1
  have h2 : ∑ u ∈ S, ∑ w ∈ Sᶜ, (f.value w u : ℤ) = 0 := by
    refine Finset.sum_eq_zero fun u hu => Finset.sum_eq_zero fun w hw => ?_
    have h := hnot u hu w hw
    simp only [Resid, not_or, not_lt] at h
    have : f.value w u = 0 := by omega
    simp [this]
  rw [h1, h2, sub_zero]

end Kolmogorov
