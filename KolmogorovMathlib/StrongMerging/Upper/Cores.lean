import KolmogorovMathlib.StrongMerging.Upper.Hierarchy

/-!
# Minimum-cardinality cores: components and the core family (blueprint M01, M02)

`sublinear-merging.tex`, subsection "Finite minimum-core profiles" (tex ~676–728) and appendix
"Minimum-cardinality cores: a separate refinement layer" (`bp-upper-mincores`, tex ~3816–3860).

* **Components (M01, mathematical part).**  Two edge labels are adjacent when they share a row or
  a column (`EdgeAdj`).  `shapeComponent P G v` is the connected edge component of `G` at the
  vertex `v`, computed by `|G|` finite traversal steps (`compGrow`) from the edges at `v`
  (`vertexEdges`); it is `∅` at a nonvertex (`shapeComponent_eq_empty`).  It is adjacency-closed
  (`isAdjClosed_shapeComponent`) and the least closed set containing the edges at `v`, so the two
  endpoints of an edge have the same component (`shapeComponent_src_eq_tgt`).  No infinite-graph
  API is used.
* **The minimum-core family (M02, `UpperMinCoreFamily`).**  At the integer budget `s` an edge set
  is eligible (`CoreElig`) when it is nonempty and every incident row/column has degree in it at
  least `2^(a - s)`, resp. `2^(b - s)`.  `minCoreSel P s M rem` selects, among the eligible subsets
  of `rem` with at most `M` edges, one of minimum cardinality, breaking ties by the first sublist
  of the canonical sorted list (`firstCoreOfCard`).  `coreRunAux` repeats selection and removal
  (fuel `|S| + 1`); `coreFamily P s M S` is the capped family and `coreResidual P s M S` its
  residual; the full family is the cap `M = |S|`.  `upperMinCoreFamily`: members are eligible,
  disjoint, of nondecreasing size and connected; the capped family is exactly the prefix
  (`List.filter`) of the full family with sizes `≤ M`, proved with the actual tie rule
  (`minCoreSel_cap`); the capped residual has no eligible set of size `≤ M` and the full residual
  none at all.
* **Selected cores.**  `vertexCores P s v` is the full family in the component of `v`;
  `coreOf P s z` is the optional selected core containing `z` (`F_s`), computed from `z`'s own
  component.  `coreOf_eq_some_of_mem` gives uniqueness; `length_incidentCores_lt` gives fewer than
  `2^(s+1)` cores at any vertex (the local rank).  Consecutive budgets are unrelated: nothing here
  asserts nesting between `coreOf P s z` and `coreOf P s' z`.
-/

namespace Kolmogorov.StrongMerging.Upper

/-! ### M01: connected edge components by finite traversal -/

/-- Two edge labels are adjacent when they share an endpoint: the same row output or the same
column output.  (Endpoints are tagged, so a row is never a column.) -/
def EdgeAdj (P : ShapeParams) (z y : BitString) : Prop :=
  P.outA z = P.outA y ∨ P.outB z = P.outB y

instance (P : ShapeParams) (z y : BitString) : Decidable (EdgeAdj P z y) := by
  unfold EdgeAdj
  infer_instance

/-- The edges of `G` incident to the vertex `v`. -/
def vertexEdges (P : ShapeParams) (G : Finset BitString) (v : BitString ⊕ BitString) :
    Finset BitString :=
  G.filter fun z => shapeSrc P z = v ∨ shapeTgt P z = v

/-- One traversal step: add to `S` the edges of `G` adjacent to an edge of `S`. -/
def compGrow (P : ShapeParams) (G S : Finset BitString) : Finset BitString :=
  S ∪ G.filter fun y => ∃ z ∈ S, EdgeAdj P z y

/-- **The connected edge component** of `G` at the vertex `v` (`C_0` when `v` is an endpoint of
`x`): `|G|` traversal steps from the edges at `v`.  At a nonvertex it is `∅`. -/
def shapeComponent (P : ShapeParams) (G : Finset BitString) (v : BitString ⊕ BitString) :
    Finset BitString :=
  (compGrow P G)^[G.card] (vertexEdges P G v)

/-- `S` is closed in `G` under adjacency: every edge of `G` adjacent to an edge of `S` is in `S`. -/
def IsAdjClosed (P : ShapeParams) (G S : Finset BitString) : Prop :=
  ∀ z ∈ S, ∀ y ∈ G, EdgeAdj P z y → y ∈ S

/-- A traversal step only adds edges. -/
theorem subset_compGrow (P : ShapeParams) (G S : Finset BitString) : S ⊆ compGrow P G S :=
  Finset.subset_union_left

/-- A traversal step stays inside `G`. -/
theorem compGrow_subset {P : ShapeParams} {G S : Finset BitString} (hS : S ⊆ G) :
    compGrow P G S ⊆ G :=
  Finset.union_subset hS (Finset.filter_subset _ _)

/-- A traversal step from a subset of a closed set stays in it. -/
theorem compGrow_subset_of_closed {P : ShapeParams} {G S T : Finset BitString} (hST : S ⊆ T)
    (hT : IsAdjClosed P G T) : compGrow P G S ⊆ T := by
  intro y hy
  rcases Finset.mem_union.mp hy with h | h
  · exact hST h
  · obtain ⟨hyG, z, hz, hzy⟩ := Finset.mem_filter.mp h
    exact hT z (hST hz) y hyG hzy

/-- Iterated traversal stays inside `G`. -/
theorem iterate_compGrow_subset {P : ShapeParams} {G : Finset BitString} :
    ∀ (k : ℕ) {S : Finset BitString}, S ⊆ G → (compGrow P G)^[k] S ⊆ G
  | 0, _, hS => hS
  | k + 1, _, hS => by
    rw [Function.iterate_succ_apply]
    exact iterate_compGrow_subset k (compGrow_subset hS)

/-- Iterated traversal only adds edges. -/
theorem subset_iterate_compGrow (P : ShapeParams) (G : Finset BitString) :
    ∀ (k : ℕ) (S : Finset BitString), S ⊆ (compGrow P G)^[k] S
  | 0, _ => subset_rfl
  | k + 1, S => by
    rw [Function.iterate_succ_apply]
    exact (subset_compGrow P G S).trans (subset_iterate_compGrow P G k _)

/-- Iterated traversal from a subset of a closed set stays in it. -/
theorem iterate_compGrow_subset_of_closed {P : ShapeParams} {G T : Finset BitString}
    (hT : IsAdjClosed P G T) : ∀ (k : ℕ) {S : Finset BitString}, S ⊆ T → (compGrow P G)^[k] S ⊆ T
  | 0, _, hS => hS
  | k + 1, _, hS => by
    rw [Function.iterate_succ_apply]
    exact iterate_compGrow_subset_of_closed hT k (compGrow_subset_of_closed hS hT)

/-- **Stabilization of the traversal.**  For `S ⊆ G`, after `|G|` steps the traversal has reached
a fixed point of `compGrow`.

Proof sketch: the iterates `S_k = (compGrow P G)^[k] S` increase (`subset_compGrow`) inside `G`
(`iterate_compGrow_subset`).  If `S_{k+1} = S_k` for some `k ≤ |G|`, then `S_m = S_k` for all
`m ≥ k` (`Function.iterate_fixed`), in particular `S_{|G|+1} = S_{|G|}`.  Otherwise every step
`k ≤ |G|` is strict, so `|S_{|G|+1}| ≥ |G| + 1` (`Finset.card_lt_card`, induction), contradicting
`S_{|G|+1} ⊆ G`.  (Tex ~3822: "connectedness is finite reachability".) -/
theorem compGrow_iterate_card_fixed (P : ShapeParams) (G S : Finset BitString) (hS : S ⊆ G) :
    compGrow P G ((compGrow P G)^[G.card] S) = (compGrow P G)^[G.card] S := by
  by_contra hne
  have hfix : ∀ k ≤ G.card, (compGrow P G)^[k + 1] S ≠ (compGrow P G)^[k] S := by
    intro k hk heq
    apply hne
    have hk' : compGrow P G ((compGrow P G)^[k] S) = (compGrow P G)^[k] S := by
      rw [← Function.iterate_succ_apply' (compGrow P G) k S]
      exact heq
    have hmk : (compGrow P G)^[G.card] S = (compGrow P G)^[k] S := by
      have : G.card = (G.card - k) + k := by omega
      rw [this, Function.iterate_add_apply, Function.iterate_fixed hk']
    rw [hmk, hk']
  have hgrow : ∀ k, k ≤ G.card + 1 → k + S.card ≤ ((compGrow P G)^[k] S).card := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      have hsub : (compGrow P G)^[k] S ⊆ (compGrow P G)^[k + 1] S := by
        rw [Function.iterate_succ_apply']
        exact subset_compGrow P G _
      have hss : (compGrow P G)^[k] S ⊂ (compGrow P G)^[k + 1] S :=
        Finset.ssubset_iff_subset_ne.mpr ⟨hsub, (hfix k (by omega)).symm⟩
      have h2 := Finset.card_lt_card hss
      omega
  have h1 := hgrow (G.card + 1) le_rfl
  have h2 := Finset.card_le_card (iterate_compGrow_subset (P := P) (G.card + 1) hS)
  omega

/-- A fixed point of the traversal is adjacency-closed. -/
theorem isAdjClosed_of_fixed {P : ShapeParams} {G T : Finset BitString}
    (h : compGrow P G T = T) : IsAdjClosed P G T := by
  intro z hz y hy hzy
  rw [← h]
  exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hy, z, hz, hzy⟩)

/-- The component is a set of edges of `G`. -/
theorem shapeComponent_subset (P : ShapeParams) (G : Finset BitString)
    (v : BitString ⊕ BitString) : shapeComponent P G v ⊆ G :=
  iterate_compGrow_subset _ (Finset.filter_subset _ _)

/-- The component contains the edges at its vertex. -/
theorem vertexEdges_subset_shapeComponent (P : ShapeParams) (G : Finset BitString)
    (v : BitString ⊕ BitString) : vertexEdges P G v ⊆ shapeComponent P G v :=
  subset_iterate_compGrow P G _ _

/-- The component is adjacency-closed in `G`. -/
theorem isAdjClosed_shapeComponent (P : ShapeParams) (G : Finset BitString)
    (v : BitString ⊕ BitString) : IsAdjClosed P G (shapeComponent P G v) :=
  isAdjClosed_of_fixed (compGrow_iterate_card_fixed P G _ (Finset.filter_subset _ _))

/-- The component is the least adjacency-closed set containing the edges at its vertex. -/
theorem shapeComponent_subset_of_closed {P : ShapeParams} {G T : Finset BitString}
    {v : BitString ⊕ BitString} (hv : vertexEdges P G v ⊆ T) (hT : IsAdjClosed P G T) :
    shapeComponent P G v ⊆ T :=
  iterate_compGrow_subset_of_closed hT _ hv

/-- **Default at a nonvertex.**  If no edge of `G` is incident to `v`, the component is empty. -/
theorem shapeComponent_eq_empty {P : ShapeParams} {G : Finset BitString}
    {v : BitString ⊕ BitString} (hv : vertexEdges P G v = ∅) : shapeComponent P G v = ∅ := by
  have hfix : compGrow P G ∅ = ∅ := by
    unfold compGrow
    simp
  unfold shapeComponent
  rw [hv]
  exact Function.iterate_fixed hfix _

/-- A closed set containing an edge contains all edges at both endpoints of that edge. -/
theorem vertexEdges_subset_of_mem_closed {P : ShapeParams} {G T : Finset BitString}
    {x : BitString} (hxT : x ∈ T) (hT : IsAdjClosed P G T) :
    vertexEdges P G (shapeSrc P x) ⊆ T ∧ vertexEdges P G (shapeTgt P x) ⊆ T := by
  constructor
  · intro y hy
    obtain ⟨hyG, h⟩ := Finset.mem_filter.mp hy
    refine hT x hxT y hyG (Or.inl ?_)
    rcases h with h | h
    · exact (Sum.inl_injective h).symm
    · exact absurd h (by simp [shapeSrc, shapeTgt])
  · intro y hy
    obtain ⟨hyG, h⟩ := Finset.mem_filter.mp hy
    refine hT x hxT y hyG (Or.inr ?_)
    rcases h with h | h
    · exact absurd h (by simp [shapeSrc, shapeTgt])
    · exact (Sum.inr_injective h).symm

/-- An edge lies in the component of its row endpoint. -/
theorem mem_shapeComponent_src {P : ShapeParams} {G : Finset BitString} {x : BitString}
    (hx : x ∈ G) : x ∈ shapeComponent P G (shapeSrc P x) :=
  vertexEdges_subset_shapeComponent P G _ (Finset.mem_filter.mpr ⟨hx, Or.inl rfl⟩)

/-- An edge lies in the component of its column endpoint. -/
theorem mem_shapeComponent_tgt {P : ShapeParams} {G : Finset BitString} {x : BitString}
    (hx : x ∈ G) : x ∈ shapeComponent P G (shapeTgt P x) :=
  vertexEdges_subset_shapeComponent P G _ (Finset.mem_filter.mpr ⟨hx, Or.inr rfl⟩)

/-- **Both endpoints compute the same component** (blueprint M01). -/
theorem shapeComponent_src_eq_tgt {P : ShapeParams} {G : Finset BitString} {x : BitString}
    (hx : x ∈ G) : shapeComponent P G (shapeSrc P x) = shapeComponent P G (shapeTgt P x) := by
  apply Finset.Subset.antisymm
  · exact shapeComponent_subset_of_closed
      (vertexEdges_subset_of_mem_closed (mem_shapeComponent_tgt hx)
        (isAdjClosed_shapeComponent P G _)).1 (isAdjClosed_shapeComponent P G _)
  · exact shapeComponent_subset_of_closed
      (vertexEdges_subset_of_mem_closed (mem_shapeComponent_src hx)
        (isAdjClosed_shapeComponent P G _)).2 (isAdjClosed_shapeComponent P G _)

/-- **Congruence of components.**  The component only reads the outputs on the edges of `G`.

Proof sketch: `vertexEdges P G v = vertexEdges Q G v` by `Finset.filter_congr` (the endpoints of
`z ∈ G` agree); for `S ⊆ G`, `compGrow P G S = compGrow Q G S` by `Finset.filter_congr` on `G`
(adjacency of `z ∈ S ⊆ G` and `y ∈ G` only reads their outputs); induct on the number of steps
using `iterate_compGrow_subset`. -/
theorem shapeComponent_congr {P Q : ShapeParams} {G : Finset BitString}
    (hG : ∀ z ∈ G, P.outA z = Q.outA z ∧ P.outB z = Q.outB z) (v : BitString ⊕ BitString) :
    shapeComponent P G v = shapeComponent Q G v := by
  have hv : vertexEdges P G v = vertexEdges Q G v := by
    unfold vertexEdges
    refine Finset.filter_congr fun z hz => ?_
    simp only [shapeSrc, shapeTgt, (hG z hz).1, (hG z hz).2]
  have hstep : ∀ S ⊆ G, compGrow P G S = compGrow Q G S := by
    intro S hS
    unfold compGrow
    congr 1
    refine Finset.filter_congr fun y hy => ?_
    constructor
    · rintro ⟨z, hz, hzy⟩
      refine ⟨z, hz, ?_⟩
      unfold EdgeAdj at hzy ⊢
      rw [← (hG z (hS hz)).1, ← (hG y hy).1, ← (hG z (hS hz)).2, ← (hG y hy).2]
      exact hzy
    · rintro ⟨z, hz, hzy⟩
      refine ⟨z, hz, ?_⟩
      unfold EdgeAdj at hzy ⊢
      rw [(hG z (hS hz)).1, (hG y hy).1, (hG z (hS hz)).2, (hG y hy).2]
      exact hzy
  have key : ∀ (k : ℕ) (S : Finset BitString), S ⊆ G →
      (compGrow P G)^[k] S = (compGrow Q G)^[k] S := by
    intro k
    induction k with
    | zero => intro S _; rfl
    | succ k ih =>
      intro S hS
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, hstep S hS]
      exact ih _ (compGrow_subset hS)
  unfold shapeComponent
  rw [hv]
  exact key _ _ (Finset.filter_subset _ _)

/-! ### M02: eligibility and the deterministic minimum-cardinality selection -/

/-- **Eligibility at the integer budget `s`** (blueprint M02): `T` is nonempty and every row and
column incident to `T` has degree in `T` at least `2^(a - s)`, resp. `2^(b - s)`.  Eligibility
does not refer to the current remainder. -/
def CoreElig (P : ShapeParams) (s : ℕ) (T : Finset BitString) : Prop :=
  T.Nonempty ∧ ∀ z ∈ T, 2 ^ (P.a - s) ≤ rowDeg P T (P.outA z) ∧
    2 ^ (P.b - s) ≤ colDeg P T (P.outB z)

instance (P : ShapeParams) (s : ℕ) : DecidablePred (CoreElig P s) := fun T => by
  unfold CoreElig
  infer_instance

/-- The capacities of the budget-`s` thresholds: rows `2^(a - s)`, columns `2^(b - s)`. -/
def coreCap (P : ShapeParams) (s : ℕ) : BitString ⊕ BitString → ℕ :=
  Sum.elim (fun _ => 2 ^ (P.a - s)) (fun _ => 2 ^ (P.b - s))

/-- The tie rule: the first sublist of length `k` of the canonical sorted list of `rem` whose set
is eligible. -/
def firstCoreOfCard (P : ShapeParams) (s k : ℕ) (rem : Finset BitString) :
    Option (Finset BitString) :=
  (((canonicalFinsetList rem).sublistsLen k).find? fun l => decide (CoreElig P s l.toFinset)).map
    List.toFinset

/-- **The deterministic capped minimum-cardinality selection**: the smallest `k ≤ min M |rem|` at
which `firstCoreOfCard` finds an eligible subset of `rem`, and that subset. -/
def minCoreSel (P : ShapeParams) (s M : ℕ) (rem : Finset BitString) :
    Option (Finset BitString) :=
  (List.range (min M rem.card + 1)).findSome? fun k => firstCoreOfCard P s k rem

/-- `findSome?` over a range is `none` exactly when every index has no value. -/
theorem findSome?_range_eq_none_iff {α : Type*} (f : ℕ → Option α) (m : ℕ) :
    (List.range m).findSome? f = none ↔ ∀ k < m, f k = none := by
  rw [List.findSome?_eq_none_iff]
  simp only [List.mem_range]

/-- **`findSome?` over a range** returns the value at the first index with a value.

Proof sketch: induction on `m` with `List.range_succ` and `List.findSome?_append`
(`Option.or`); the `none` case of the prefix gives `∀ k' < m, f k' = none` by
`List.findSome?_eq_none_iff`.  The converse direction is the same computation. -/
theorem findSome?_range_eq_some_iff {α : Type*} (f : ℕ → Option α) (m : ℕ) (a : α) :
    (List.range m).findSome? f = some a ↔ ∃ k < m, f k = some a ∧ ∀ k' < k, f k' = none := by
  induction m generalizing a with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.findSome?_append]
    cases hm : (List.range m).findSome? f with
    | none =>
      have hall := (findSome?_range_eq_none_iff f m).mp hm
      rw [Option.none_or]
      constructor
      · intro h
        refine ⟨m, Nat.lt_succ_self m, ?_, hall⟩
        simpa using h
      · rintro ⟨k, hk, hka, -⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
        · rw [hall k hk] at hka
          exact absurd hka (by simp)
        · simpa using hka
    | some b =>
      rw [Option.some_or]
      obtain ⟨k, hk, hkb, hlt⟩ := (ih b).mp hm
      constructor
      · intro h
        obtain rfl : b = a := Option.some_inj.mp h
        exact ⟨k, Nat.lt_succ_of_lt hk, hkb, hlt⟩
      · rintro ⟨k', -, hk'a, hlt'⟩
        rcases lt_trichotomy k k' with h | rfl | h
        · rw [hlt' k h] at hkb
          exact absurd hkb (by simp)
        · rw [hkb] at hk'a
          exact hk'a
        · rw [hlt k' h] at hk'a
          exact absurd hk'a (by simp)

/-- A sublist found by `firstCoreOfCard` is an eligible subset of size `k`.

Proof sketch: `Option.map_eq_some_iff` gives `l` with `find? = some l` and `T = l.toFinset`;
`List.find?_some` gives eligibility; `List.mem_of_find?_eq_some` and `List.mem_sublistsLen` give
`l <+ canonicalFinsetList rem` and `l.length = k`; `l` is duplicate-free
(`(canonicalFinsetList_nodup rem).sublist`), so `T.card = k` (`List.toFinset_card_of_nodup`) and
`T ⊆ rem` (`mem_canonicalFinsetList`). -/
theorem firstCoreOfCard_some {P : ShapeParams} {s k : ℕ} {rem T : Finset BitString}
    (h : firstCoreOfCard P s k rem = some T) : CoreElig P s T ∧ T ⊆ rem ∧ T.card = k := by
  unfold firstCoreOfCard at h
  obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.mp h
  have h1 := List.find?_some hl
  have h2 := List.mem_sublistsLen.mp (List.mem_of_find?_eq_some hl)
  have hnd : l.Nodup := (canonicalFinsetList_nodup rem).sublist h2.1
  refine ⟨by simpa using h1, fun z hz => ?_, ?_⟩
  · rw [List.mem_toFinset] at hz
    simpa using h2.1.subset hz
  · rw [List.toFinset_card_of_nodup hnd, h2.2]

/-- If `firstCoreOfCard` finds nothing, no subset of `rem` of size `k` is eligible.

Proof sketch: as `firstEligible_none`: for `T ⊆ rem` the filtered list
`(canonicalFinsetList rem).filter (· ∈ T)` is a sublist with set `T` and length `T.card = k`
(duplicate-free), hence in `sublistsLen k` (`List.mem_sublistsLen`); `List.find?_eq_none` then
gives `¬ CoreElig P s T`. -/
theorem firstCoreOfCard_none {P : ShapeParams} {s k : ℕ} {rem : Finset BitString}
    (h : firstCoreOfCard P s k rem = none) : ∀ T ⊆ rem, T.card = k → ¬ CoreElig P s T := by
  intro T hT hk hel
  unfold firstCoreOfCard at h
  rw [Option.map_eq_none_iff] at h
  have hsub : List.Sublist ((canonicalFinsetList rem).filter (fun z => decide (z ∈ T)))
      (canonicalFinsetList rem) := List.filter_sublist
  have hset : ((canonicalFinsetList rem).filter (fun z => decide (z ∈ T))).toFinset = T := by
    ext z
    simp only [List.mem_toFinset, List.mem_filter, mem_canonicalFinsetList, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨hT h, h⟩⟩
  have hnd : ((canonicalFinsetList rem).filter (fun z => decide (z ∈ T))).Nodup :=
    (canonicalFinsetList_nodup rem).filter _
  have hlen : ((canonicalFinsetList rem).filter (fun z => decide (z ∈ T))).length = k := by
    rw [← List.toFinset_card_of_nodup hnd, hset, hk]
  have hmem : (canonicalFinsetList rem).filter (fun z => decide (z ∈ T)) ∈
      (canonicalFinsetList rem).sublistsLen k := List.mem_sublistsLen.mpr ⟨hsub, hlen⟩
  have := List.find?_eq_none.mp h _ hmem
  simp only [hset, decide_eq_true_eq] at this
  exact this hel

/-- **The selection is a minimum-cardinality eligible subset within the cap.** -/
theorem minCoreSel_some {P : ShapeParams} {s M : ℕ} {rem T : Finset BitString}
    (h : minCoreSel P s M rem = some T) :
    CoreElig P s T ∧ T ⊆ rem ∧ T.card ≤ M ∧ ∀ T' ⊆ rem, CoreElig P s T' → T.card ≤ T'.card := by
  obtain ⟨k, hk, hkT, hlt⟩ := (findSome?_range_eq_some_iff _ _ _).mp h
  obtain ⟨hel, hsub, hcard⟩ := firstCoreOfCard_some hkT
  refine ⟨hel, hsub, by omega, fun T' hT' hel' => ?_⟩
  by_contra hcon
  exact firstCoreOfCard_none (hlt _ (by omega)) T' hT' rfl hel'

/-- **An empty selection means no eligible subset fits the cap.** -/
theorem minCoreSel_none {P : ShapeParams} {s M : ℕ} {rem : Finset BitString}
    (h : minCoreSel P s M rem = none) : ∀ T' ⊆ rem, CoreElig P s T' → M < T'.card := by
  intro T' hT' hel'
  have hall := (findSome?_range_eq_none_iff _ _).mp h
  by_contra hcon
  have hle : T'.card ≤ rem.card := Finset.card_le_card hT'
  exact firstCoreOfCard_none (hall T'.card (by omega)) T' hT' rfl hel'

/-- **The capped selection is the larger-cap selection, kept only if it fits** (the actual tie
rule, blueprint M02 item 3).

Proof sketch: put `m = min M |rem| + 1 ≤ m' = min M' |rem| + 1`.  If the `M'` selection is `none`,
every index `< m'` has no value, hence every index `< m` (`findSome?_range_eq_none_iff`).  If it is
`some T` at the first index `k < m'` (`findSome?_range_eq_some_iff`), then `T.card = k`
(`firstCoreOfCard_some`); if `k ≤ M` then `k < m` and the same first index gives `some T` for the
cap `M`; if `k > M` then all indices `< m ≤ k` are empty and the filter drops `T`. -/
theorem minCoreSel_cap {P : ShapeParams} {s M M' : ℕ} (hMM' : M ≤ M') (rem : Finset BitString) :
    minCoreSel P s M rem = (minCoreSel P s M' rem).filter fun T => decide (T.card ≤ M) := by
  cases h' : minCoreSel P s M' rem with
  | none =>
    have hall := (findSome?_range_eq_none_iff _ _).mp h'
    have hM : minCoreSel P s M rem = none :=
      (findSome?_range_eq_none_iff _ _).mpr fun k hk => hall k (by omega)
    rw [hM]
    rfl
  | some T =>
    obtain ⟨k, hk, hkT, hlt⟩ := (findSome?_range_eq_some_iff _ _ _).mp h'
    obtain ⟨-, hsub, hcard⟩ := firstCoreOfCard_some hkT
    have hkrem : k ≤ rem.card := hcard ▸ Finset.card_le_card hsub
    by_cases hkM : k ≤ M
    · have hM : minCoreSel P s M rem = some T :=
        (findSome?_range_eq_some_iff _ _ _).mpr ⟨k, by omega, hkT, hlt⟩
      rw [hM, Option.filter_some, hcard]
      simp [hkM]
    · have hM : minCoreSel P s M rem = none :=
        (findSome?_range_eq_none_iff _ _).mpr fun k' hk' => hlt k' (by omega)
      rw [hM, Option.filter_some, hcard]
      simp [hkM]

/-! ### M02: the extraction run -/

/-- **The extraction run with fuel**: select a capped minimum-cardinality eligible subset of the
remainder, record it, remove it, repeat; stop when the selection is empty. -/
def coreRunAux (P : ShapeParams) (s M : ℕ) :
    ℕ → Finset BitString → List (Finset BitString) × Finset BitString
  | 0, rem => ([], rem)
  | fuel + 1, rem =>
    match minCoreSel P s M rem with
    | none => ([], rem)
    | some T => (T :: (coreRunAux P s M fuel (rem \ T)).1, (coreRunAux P s M fuel (rem \ T)).2)

/-- **The capped core family** `𝓕_s` restricted to sizes `≤ M`, extracted from the start set `S`
(the component `C_0` in the application); fuel `|S| + 1`.  The full family is `M = |S|`. -/
def coreFamily (P : ShapeParams) (s M : ℕ) (S : Finset BitString) : List (Finset BitString) :=
  (coreRunAux P s M (S.card + 1) S).1

/-- **The capped residual**: the edges of `S` in no member of `coreFamily P s M S`. -/
def coreResidual (P : ShapeParams) (s M : ℕ) (S : Finset BitString) : Finset BitString :=
  (coreRunAux P s M (S.card + 1) S).2

/-- Members of the run are eligible subsets of the remainder within the cap, and minimum among
eligible subsets of themselves. -/
theorem coreRunAux_mem (P : ShapeParams) (s M : ℕ) :
    ∀ (fuel : ℕ) (rem : Finset BitString), ∀ T ∈ (coreRunAux P s M fuel rem).1,
      CoreElig P s T ∧ T ⊆ rem ∧ T.card ≤ M ∧
        ∀ T' ⊆ T, CoreElig P s T' → T.card ≤ T'.card
  | 0, rem => by simp [coreRunAux]
  | fuel + 1, rem => by
    simp only [coreRunAux]
    split
    · simp
    · rename_i T hT
      intro T' hT'
      rcases List.mem_cons.mp hT' with rfl | hT'
      · obtain ⟨h1, h2, h3, h4⟩ := minCoreSel_some hT
        exact ⟨h1, h2, h3, fun T'' hT'' hel => h4 T'' (hT''.trans h2) hel⟩
      · obtain ⟨h1, h2, h3, h4⟩ := coreRunAux_mem P s M fuel (rem \ T) T' hT'
        exact ⟨h1, h2.trans Finset.sdiff_subset, h3, h4⟩

/-- The run partitions the remainder: members pairwise disjoint and disjoint from the residual,
the residual is a subset, and every element is in the residual or in a member.

Proof sketch: verbatim the proof of `extractAux_partition` (Hierarchy), with `minCoreSel` and
`coreRunAux_mem` in place of `firstEligible` and `extractAux_children`. -/
theorem coreRunAux_partition (P : ShapeParams) (s M fuel : ℕ) (rem : Finset BitString) :
    (coreRunAux P s M fuel rem).1.Pairwise Disjoint ∧
      (∀ T ∈ (coreRunAux P s M fuel rem).1, Disjoint T (coreRunAux P s M fuel rem).2) ∧
      (coreRunAux P s M fuel rem).2 ⊆ rem ∧
      ∀ z ∈ rem, z ∈ (coreRunAux P s M fuel rem).2 ∨
        ∃ T ∈ (coreRunAux P s M fuel rem).1, z ∈ T := by
  induction fuel generalizing rem with
  | zero => simp [coreRunAux]
  | succ fuel ih =>
    simp only [coreRunAux]
    split
    · simp
    · rename_i T hT
      obtain ⟨h1, h2, h3, h4⟩ := ih (rem \ T)
      have hchild := coreRunAux_mem P s M fuel (rem \ T)
      refine ⟨List.pairwise_cons.mpr ⟨fun T' hT' => ?_, h1⟩, ?_, h3.trans Finset.sdiff_subset, ?_⟩
      · exact Finset.disjoint_of_subset_right (hchild T' hT').2.1 Finset.disjoint_sdiff
      · intro T' hT'
        rcases List.mem_cons.mp hT' with rfl | hT'
        · exact Finset.disjoint_of_subset_right h3 Finset.disjoint_sdiff
        · exact h2 T' hT'
      · intro z hz
        by_cases hzT : z ∈ T
        · exact Or.inr ⟨T, List.mem_cons_self, hzT⟩
        · rcases h4 z (Finset.mem_sdiff.mpr ⟨hz, hzT⟩) with h | ⟨T', hT', hzT'⟩
          · exact Or.inl h
          · exact Or.inr ⟨T', List.mem_cons_of_mem _ hT', hzT'⟩

/-- With enough fuel the residual has no eligible subset within the cap.

Proof sketch: verbatim `extractAux_residual`: in the `none` branch use `minCoreSel_none`; in the
`some T` branch `T` is nonempty and `T ⊆ rem` (`minCoreSel_some`), so `|rem \ T| < |rem|` and the
induction hypothesis applies. -/
theorem coreRunAux_residual (P : ShapeParams) (s M fuel : ℕ) (rem : Finset BitString)
    (hfuel : rem.card < fuel) :
    ∀ T ⊆ (coreRunAux P s M fuel rem).2, CoreElig P s T → M < T.card := by
  induction fuel generalizing rem with
  | zero => omega
  | succ fuel ih =>
    simp only [coreRunAux]
    split
    · rename_i h
      exact minCoreSel_none h
    · rename_i T hT
      obtain ⟨hel, hsub, -, -⟩ := minCoreSel_some hT
      apply ih (rem \ T)
      have hlt : (rem \ T).card < rem.card :=
        Finset.card_lt_card (Finset.sdiff_ssubset hsub hel.1)
      omega

/-- **Sizes are nondecreasing.**  Deleting edges cannot create a new eligible subset, so each later
member, an eligible subset of a smaller remainder, is at least as large as an earlier one. -/
theorem coreRunAux_sorted (P : ShapeParams) (s M : ℕ) :
    ∀ (fuel : ℕ) (rem : Finset BitString),
      (coreRunAux P s M fuel rem).1.Pairwise fun T T' => T.card ≤ T'.card
  | 0, rem => by simp [coreRunAux]
  | fuel + 1, rem => by
    simp only [coreRunAux]
    split
    · exact List.Pairwise.nil
    · rename_i T hT
      refine List.pairwise_cons.mpr ⟨fun T' hT' => ?_, coreRunAux_sorted P s M fuel (rem \ T)⟩
      obtain ⟨h1, h2, -, -⟩ := coreRunAux_mem P s M fuel (rem \ T) T' hT'
      exact (minCoreSel_some hT).2.2.2 T' (h2.trans Finset.sdiff_subset) h1

/-- **The capped run is the prefix of the larger-cap run** with sizes `≤ M` (blueprint M02
item 3, with the actual deterministic tie rule).

Proof sketch: induction on the fuel generalizing `rem`; rewrite the capped selection by
`minCoreSel_cap`.  If the `M'` selection is `none` both runs are empty.  If it is `some T` with
`T.card ≤ M`, both runs start with `T` and continue on `rem \ T` (induction hypothesis; the
filter keeps `T`).  If `T.card > M`, the capped run is empty, and every later member `T'` of the
`M'` run is an eligible subset of `rem \ T ⊆ rem` (`coreRunAux_mem`), so
`M < T.card ≤ T'.card` (`minCoreSel_some`) and the filter drops everything. -/
theorem coreRunAux_cap (P : ShapeParams) (s : ℕ) {M M' : ℕ} (hMM' : M ≤ M') (fuel : ℕ)
    (rem : Finset BitString) :
    (coreRunAux P s M fuel rem).1 =
      (coreRunAux P s M' fuel rem).1.filter fun T => decide (T.card ≤ M) := by
  induction fuel generalizing rem with
  | zero => simp [coreRunAux]
  | succ fuel ih =>
    have hsel := minCoreSel_cap (P := P) (s := s) hMM' rem
    cases h' : minCoreSel P s M' rem with
    | none =>
      rw [h', Option.filter_none] at hsel
      simp only [coreRunAux, h', hsel, List.filter_nil]
    | some T =>
      rw [h', Option.filter_some] at hsel
      by_cases hT : T.card ≤ M
      · simp only [hT, decide_true, ↓reduceIte] at hsel
        simp only [coreRunAux, h', hsel]
        rw [List.filter_cons_of_pos (by simpa using hT), ih]
      · simp only [hT, decide_false, Bool.false_eq_true, ↓reduceIte] at hsel
        simp only [coreRunAux, h', hsel]
        rw [List.filter_cons_of_neg (by simpa using hT), eq_comm, List.filter_eq_nil_iff]
        intro T' hT'
        obtain ⟨h1, h2, -, -⟩ := coreRunAux_mem P s M' fuel (rem \ T) T' hT'
        have := (minCoreSel_some h').2.2.2 T' (h2.trans Finset.sdiff_subset) h1
        simp only [decide_eq_true_eq]
        omega

/-! ### M02: connectedness of minimum cores -/

/-- An edge set is connected: the component inside it of any of its edges is all of it. -/
def IsEdgeConnected (P : ShapeParams) (T : Finset BitString) : Prop :=
  ∀ z ∈ T, shapeComponent P T (shapeSrc P z) = T

/-- **A connected component of an eligible set is eligible.**

Proof sketch: put `C = shapeComponent P T (shapeSrc P z) ⊆ T` (`shapeComponent_subset`), which
contains `z` (`mem_shapeComponent_src`) and is adjacency-closed in `T`
(`isAdjClosed_shapeComponent`).  For `y ∈ C` every edge of `T` with the row `outA y` is adjacent
to `y`, hence in `C`; so the filters defining `rowDeg P C (outA y)` and `rowDeg P T (outA y)`
coincide (`Finset.filter_congr`, `Finset.Subset.antisymm`), and likewise for columns.  The
thresholds hold in `T` because `y ∈ T`. -/
theorem coreElig_shapeComponent {P : ShapeParams} {s : ℕ} {T : Finset BitString}
    (hT : CoreElig P s T) {z : BitString} (hz : z ∈ T) :
    CoreElig P s (shapeComponent P T (shapeSrc P z)) := by
  have hCT : shapeComponent P T (shapeSrc P z) ⊆ T := shapeComponent_subset P T _
  have hcl := isAdjClosed_shapeComponent P T (shapeSrc P z)
  refine ⟨⟨z, mem_shapeComponent_src hz⟩, fun y hy => ?_⟩
  have hrow : rowDeg P (shapeComponent P T (shapeSrc P z)) (P.outA y) = rowDeg P T (P.outA y) := by
    unfold rowDeg
    congr 1
    ext w
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hw, hwy⟩
      exact ⟨hCT hw, hwy⟩
    · rintro ⟨hw, hwy⟩
      exact ⟨hcl y hy w hw (Or.inl hwy.symm), hwy⟩
  have hcol : colDeg P (shapeComponent P T (shapeSrc P z)) (P.outB y) = colDeg P T (P.outB y) := by
    unfold colDeg
    congr 1
    ext w
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hw, hwy⟩
      exact ⟨hCT hw, hwy⟩
    · rintro ⟨hw, hwy⟩
      exact ⟨hcl y hy w hw (Or.inr hwy.symm), hwy⟩
  rw [hrow, hcol]
  exact hT.2 y (hCT hy)

/-- **A minimum-cardinality eligible set is connected** (blueprint M02 item 2): each of its
components is eligible, and minimality forbids a proper eligible subset. -/
theorem isEdgeConnected_of_min {P : ShapeParams} {s : ℕ} {T : Finset BitString}
    (hT : CoreElig P s T) (hmin : ∀ T' ⊆ T, CoreElig P s T' → T.card ≤ T'.card) :
    IsEdgeConnected P T := by
  intro z hz
  have hsub := shapeComponent_subset P T (shapeSrc P z)
  exact Finset.eq_of_subset_of_card_le hsub (hmin _ hsub (coreElig_shapeComponent hT hz))

/-! ### M02: the family theorem -/

/-- Membership in the residual: the edges of the start set in no member of the family. -/
theorem mem_coreResidual_iff (P : ShapeParams) (s M : ℕ) (S : Finset BitString) (z : BitString) :
    z ∈ coreResidual P s M S ↔ z ∈ S ∧ ∀ T ∈ coreFamily P s M S, z ∉ T := by
  obtain ⟨-, h2, h3, h4⟩ := coreRunAux_partition P s M (S.card + 1) S
  constructor
  · intro hz
    exact ⟨h3 hz, fun T hT hzT => Finset.disjoint_left.mp (h2 T hT) hzT hz⟩
  · rintro ⟨hzS, hno⟩
    rcases h4 z hzS with h | ⟨T, hT, hzT⟩
    · exact h
    · exact absurd hzT (hno T hT)

/-- The capped family is the filter of the full family (every cap, also above `|S|`). -/
theorem coreFamily_cap (P : ShapeParams) (s M : ℕ) (S : Finset BitString) :
    coreFamily P s M S = (coreFamily P s S.card S).filter fun T => decide (T.card ≤ M) := by
  rcases le_total M S.card with h | h
  · exact coreRunAux_cap P s h (S.card + 1) S
  · have h1 := coreRunAux_cap P s h (S.card + 1) S
    have hall : ∀ T ∈ coreFamily P s M S, T.card ≤ S.card := fun T hT =>
      Finset.card_le_card (coreRunAux_mem P s M (S.card + 1) S T hT).2.1
    have hall' : ∀ T ∈ coreFamily P s S.card S, T.card ≤ M := fun T hT =>
      (Finset.card_le_card (coreRunAux_mem P s S.card (S.card + 1) S T hT).2.1).trans h
    have e1 : coreFamily P s S.card S = coreFamily P s M S := by
      unfold coreFamily
      rw [h1, List.filter_eq_self]
      intro T hT
      exact decide_eq_true (hall T hT)
    have e2 : (coreFamily P s S.card S).filter (fun T => decide (T.card ≤ M)) =
        coreFamily P s S.card S :=
      List.filter_eq_self.mpr fun T hT => decide_eq_true (hall' T hT)
    rw [e2, e1]

/-- **The minimum-core family (blueprint M02, `UpperMinCoreFamily`).**  For a budget `s`, a start
set `S` and a cap `M`:
1. members are eligible subsets of `S` with at most `M` edges, pairwise disjoint, of
   nondecreasing size; removing edges only shrinks the eligible candidates;
2. every member is connected (a minimum-cardinality eligible set is connected);
3. the capped family is exactly the filter (the prefix, sizes being sorted) of the full family
   `coreFamily P s |S| S` by size `≤ M`, for the actual deterministic tie rule;
4. the residual consists of the edges of `S` in no member; the capped residual has no eligible
   set of size `≤ M`, and the full residual has no eligible set at all. -/
theorem upperMinCoreFamily (P : ShapeParams) (s M : ℕ) (S : Finset BitString) :
    (∀ T ∈ coreFamily P s M S, CoreElig P s T ∧ T ⊆ S ∧ T.card ≤ M) ∧
      (coreFamily P s M S).Pairwise Disjoint ∧
      (coreFamily P s M S).Pairwise (fun T T' => T.card ≤ T'.card) ∧
      (∀ rem rem' T : Finset BitString, rem' ⊆ rem → T ⊆ rem' → CoreElig P s T →
        T ⊆ rem ∧ CoreElig P s T) ∧
      (∀ T ∈ coreFamily P s M S, IsEdgeConnected P T) ∧
      coreFamily P s M S = (coreFamily P s S.card S).filter (fun T => decide (T.card ≤ M)) ∧
      (∀ z, z ∈ coreResidual P s M S ↔ z ∈ S ∧ ∀ T ∈ coreFamily P s M S, z ∉ T) ∧
      (∀ T ⊆ coreResidual P s M S, CoreElig P s T → M < T.card) ∧
      ∀ T ⊆ coreResidual P s S.card S, ¬ CoreElig P s T := by
  refine ⟨fun T hT => ?_, (coreRunAux_partition P s M _ S).1, coreRunAux_sorted P s M _ S,
    fun _ _ _ h1 h2 h3 => ⟨h2.trans h1, h3⟩, fun T hT => ?_, coreFamily_cap P s M S,
    mem_coreResidual_iff P s M S, coreRunAux_residual P s M _ S (Nat.lt_succ_self _),
    fun T hT hel => ?_⟩
  · obtain ⟨h1, h2, h3, -⟩ := coreRunAux_mem P s M _ S T hT
    exact ⟨h1, h2, h3⟩
  · obtain ⟨h1, -, -, h4⟩ := coreRunAux_mem P s M _ S T hT
    exact isEdgeConnected_of_min h1 h4
  · have h := coreRunAux_residual P s S.card _ S (Nat.lt_succ_self _) T hT hel
    have hT' : T ⊆ S := hT.trans (coreRunAux_partition P s S.card _ S).2.2.1
    have := Finset.card_le_card hT'
    omega

/-! ### Selected cores in the component of an endpoint -/

/-- The full minimum-core family at budget `s` in the component of the vertex `v` of the shape
graph (`𝓕_s` when `v` is an endpoint of `x`). -/
noncomputable def vertexCores (P : ShapeParams) (s : ℕ) (v : BitString ⊕ BitString) :
    List (Finset BitString) :=
  coreFamily P s (shapeComponent P (shapeEdges P) v).card (shapeComponent P (shapeEdges P) v)

/-- The capped family at budget `s` and cap `M` in the component of `v`. -/
noncomputable def vertexCappedCores (P : ShapeParams) (s M : ℕ) (v : BitString ⊕ BitString) :
    List (Finset BitString) :=
  coreFamily P s M (shapeComponent P (shapeEdges P) v)

/-- The capped residual at budget `s` and cap `M` in the component of `v` (the full residual for
`M = |C_0|`). -/
noncomputable def vertexResidual (P : ShapeParams) (s M : ℕ) (v : BitString ⊕ BitString) :
    Finset BitString :=
  coreResidual P s M (shapeComponent P (shapeEdges P) v)

/-- **The selected core containing `z`** (`F_s`, an optional value): the member of the full family
of `z`'s own component that contains `z`, if any. -/
noncomputable def coreOf (P : ShapeParams) (s : ℕ) (z : BitString) : Option (Finset BitString) :=
  (vertexCores P s (shapeSrc P z)).find? fun T => decide (z ∈ T)

/-- A selected core is a member of the family containing `z`. -/
theorem coreOf_spec {P : ShapeParams} {s : ℕ} {z : BitString} {F : Finset BitString}
    (h : coreOf P s z = some F) : F ∈ vertexCores P s (shapeSrc P z) ∧ z ∈ F := by
  unfold coreOf at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

/-- Without a selected core, `z` lies in no member of the family. -/
theorem coreOf_eq_none {P : ShapeParams} {s : ℕ} {z : BitString} (h : coreOf P s z = none) :
    ∀ T ∈ vertexCores P s (shapeSrc P z), z ∉ T := by
  unfold coreOf at h
  intro T hT hzT
  have := List.find?_eq_none.mp h T hT
  simp [hzT] at this

/-- **Uniqueness of the containing core**: the members are pairwise disjoint, so a member
containing `z` is the selected core. -/
theorem coreOf_eq_some_of_mem {P : ShapeParams} {s : ℕ} {z : BitString} {F : Finset BitString}
    (hF : F ∈ vertexCores P s (shapeSrc P z)) (hz : z ∈ F) : coreOf P s z = some F := by
  have hdisj : (vertexCores P s (shapeSrc P z)).Pairwise Disjoint :=
    (coreRunAux_partition P s _ _ _).1
  cases h : coreOf P s z with
  | none => exact absurd hz (coreOf_eq_none h F hF)
  | some F' =>
    obtain ⟨hF', hzF'⟩ := coreOf_spec h
    by_contra hne
    have hne' : F' ≠ F := fun e => hne (by rw [e])
    exact Finset.disjoint_left.mp (hdisj.forall hF' hF hne') hzF' hz

/-- **Without a selected core the edge is in the full residual** of its component. -/
theorem mem_vertexResidual_of_coreOf_eq_none {P : ShapeParams} {s : ℕ} {z : BitString}
    (hz : z ∈ shapeEdges P) (h : coreOf P s z = none) :
    z ∈ vertexResidual P s (shapeComponent P (shapeEdges P) (shapeSrc P z)).card (shapeSrc P z) :=
  (mem_coreResidual_iff P s _ _ z).mpr ⟨mem_shapeComponent_src hz, coreOf_eq_none h⟩

/-- **The capped prefix.**  If the selected core of `z` has more than `M` edges, then `z` lies in
the capped residual with cap `M` (blueprint, proof of `UpperInitialFactorCap`). -/
theorem mem_vertexResidual_of_lt_card {P : ShapeParams} {s M : ℕ} {z : BitString}
    {F : Finset BitString} (h : coreOf P s z = some F) (hM : M < F.card) :
    z ∈ vertexResidual P s M (shapeSrc P z) := by
  obtain ⟨hF, hzF⟩ := coreOf_spec h
  have hzC : z ∈ shapeComponent P (shapeEdges P) (shapeSrc P z) :=
    (coreRunAux_mem P s _ _ _ F hF).2.1 hzF
  refine (mem_coreResidual_iff P s M _ z).mpr ⟨hzC, fun T hT hzT => ?_⟩
  rw [coreFamily_cap, List.mem_filter] at hT
  have hTF : T = F := by
    by_contra hne
    have hdisj : (vertexCores P s (shapeSrc P z)).Pairwise Disjoint :=
      (coreRunAux_partition P s _ _ _).1
    exact Finset.disjoint_left.mp (hdisj.forall hT.1 hF hne) hzT hzF
  rw [hTF] at hT
  have := of_decide_eq_true hT.2
  omega

/-- The cores of a list incident to the vertex `v`, in list order. -/
def incidentCores (P : ShapeParams) (l : List (Finset BitString)) (v : BitString ⊕ BitString) :
    List (Finset BitString) :=
  l.filter fun T => decide (∃ z ∈ T, shapeSrc P z = v ∨ shapeTgt P z = v)

/-- **Fewer than `2^(s+1)` cores at a vertex** (tex ~703–707): one local rank of `s + 1` bits.

Proof sketch: for a row vertex `Sum.inl w`, each incident member `T` contains some `z` with
`outA z = w` (the tag rules out `shapeTgt`), so `2^(a - s) ≤ rowDeg P T w` by eligibility
(`upperMinCoreFamily`); the members are pairwise disjoint subsets of the shape edges
(`shapeComponent_subset`), so `|list| · 2^(a - s) ≤ ∑ rowDeg P T w ≤ rowDeg P G w < 2^(a+1)`
(`List.length_nsmul_le_sum`, `sum_rowDeg_le`, `rowDeg_shapeEdges_lt`); conclude by
`lt_pow_of_mul_pow_le` with `s ≤ a`.  Columns likewise with `s ≤ b`.  This repeats
`card_rowIncidentBlocks_lt`. -/
theorem length_incidentCores_lt (P : ShapeParams) (s : ℕ) (hsa : s ≤ P.a) (hsb : s ≤ P.b)
    (u v : BitString ⊕ BitString) :
    (incidentCores P (vertexCores P s u) v).length < 2 ^ (s + 1) := by
  have hfam := upperMinCoreFamily P s (shapeComponent P (shapeEdges P) u).card
    (shapeComponent P (shapeEdges P) u)
  have hsubl : (incidentCores P (vertexCores P s u) v).Sublist (vertexCores P s u) :=
    List.filter_sublist
  have hdisj : (incidentCores P (vertexCores P s u) v).Pairwise Disjoint :=
    hfam.2.1.sublist hsubl
  have hG : ∀ F ∈ incidentCores P (vertexCores P s u) v, F ⊆ shapeEdges P := fun F hF =>
    (hfam.1 F (hsubl.subset hF)).2.1.trans (shapeComponent_subset _ _ _)
  have hel : ∀ F ∈ incidentCores P (vertexCores P s u) v, CoreElig P s F := fun F hF =>
    (hfam.1 F (hsubl.subset hF)).1
  have hinc : ∀ F ∈ incidentCores P (vertexCores P s u) v,
      ∃ z ∈ F, shapeSrc P z = v ∨ shapeTgt P z = v := fun F hF =>
    of_decide_eq_true (List.mem_filter.mp hF).2
  cases v with
  | inl w =>
    have hthr : ∀ F ∈ incidentCores P (vertexCores P s u) (Sum.inl w),
        2 ^ (P.a - s) ≤ rowDeg P F w := by
      intro F hF
      obtain ⟨z, hz, hzv⟩ := hinc F hF
      have hzw : P.outA z = w := by
        rcases hzv with h | h
        · exact Sum.inl_injective h
        · exact absurd h (by simp [shapeTgt])
      have := ((hel F hF).2 z hz).1
      rwa [hzw] at this
    have hsum : (incidentCores P (vertexCores P s u) (Sum.inl w)).length * 2 ^ (P.a - s) ≤
        ((incidentCores P (vertexCores P s u) (Sum.inl w)).map fun F => rowDeg P F w).sum := by
      have := List.length_nsmul_le_sum
        ((incidentCores P (vertexCores P s u) (Sum.inl w)).map fun F => rowDeg P F w)
        (2 ^ (P.a - s)) (fun x hx => by
          obtain ⟨F, hF, rfl⟩ := List.mem_map.mp hx
          exact hthr F hF)
      simpa using this
    exact lt_pow_of_mul_pow_le hsa
      (hsum.trans (sum_rowDeg_le P (shapeEdges P) w _ hdisj hG)) (rowDeg_shapeEdges_lt P w)
  | inr w =>
    have hthr : ∀ F ∈ incidentCores P (vertexCores P s u) (Sum.inr w),
        2 ^ (P.b - s) ≤ colDeg P F w := by
      intro F hF
      obtain ⟨z, hz, hzv⟩ := hinc F hF
      have hzw : P.outB z = w := by
        rcases hzv with h | h
        · exact absurd h (by simp [shapeSrc])
        · exact Sum.inr_injective h
      have := ((hel F hF).2 z hz).2
      rwa [hzw] at this
    have hsum : (incidentCores P (vertexCores P s u) (Sum.inr w)).length * 2 ^ (P.b - s) ≤
        ((incidentCores P (vertexCores P s u) (Sum.inr w)).map fun F => colDeg P F w).sum := by
      have := List.length_nsmul_le_sum
        ((incidentCores P (vertexCores P s u) (Sum.inr w)).map fun F => colDeg P F w)
        (2 ^ (P.b - s)) (fun x hx => by
          obtain ⟨F, hF, rfl⟩ := List.mem_map.mp hx
          exact hthr F hF)
      simpa using this
    exact lt_pow_of_mul_pow_le hsb
      (hsum.trans (sum_colDeg_le P (shapeEdges P) w _ hdisj hG)) (colDeg_shapeEdges_lt P w)

/-- **Congruence of the core families.**  Parameter sets that agree at the data length have the
same full families, capped families and residuals at every vertex.

Proof sketch: the shape edges agree (`shapeEdges_congr`) and consist of strings of length `n`, so
the components agree (`shapeComponent_congr`); eligibility of `T ⊆ C_0` only reads outputs on `T`
and the buckets `a, b` (as in `children_residual_congr`), so `firstCoreOfCard`, `minCoreSel` and
the run agree on every remainder inside `C_0` (induction on the fuel, as `extract_congr`). -/
theorem vertexCores_congr {P Q : ShapeParams} (h : P.AgreeOn Q) (s M : ℕ)
    (v : BitString ⊕ BitString) :
    shapeComponent P (shapeEdges P) v = shapeComponent Q (shapeEdges Q) v ∧
      vertexCores P s v = vertexCores Q s v ∧
      vertexCappedCores P s M v = vertexCappedCores Q s M v ∧
      vertexResidual P s M v = vertexResidual Q s M v := by
  have hE : shapeEdges P = shapeEdges Q := shapeEdges_congr h
  have hlen : ∀ z ∈ shapeEdges P, z.length = P.n := fun z hz =>
    (mem_stringsOfLength _ _).mp (Finset.mem_filter.mp hz).1
  have hout : ∀ z ∈ shapeEdges P, P.outA z = Q.outA z ∧ P.outB z = Q.outB z :=
    fun z hz => h.2.2.2 z (hlen z hz)
  have hC : shapeComponent P (shapeEdges P) v = shapeComponent Q (shapeEdges Q) v := by
    rw [← hE]
    exact shapeComponent_congr hout v
  have hCsub : shapeComponent P (shapeEdges P) v ⊆ shapeEdges P := shapeComponent_subset _ _ _
  have hel : ∀ T ⊆ shapeComponent P (shapeEdges P) v, (CoreElig P s T ↔ CoreElig Q s T) := by
    intro T hT
    have hrow : ∀ z ∈ T, rowDeg P T (P.outA z) = rowDeg Q T (Q.outA z) := by
      intro z hz
      unfold rowDeg
      rw [← (hout z (hCsub (hT hz))).1]
      congr 1
      exact Finset.filter_congr fun y hy => by rw [(hout y (hCsub (hT hy))).1]
    have hcol : ∀ z ∈ T, colDeg P T (P.outB z) = colDeg Q T (Q.outB z) := by
      intro z hz
      unfold colDeg
      rw [← (hout z (hCsub (hT hz))).2]
      congr 1
      exact Finset.filter_congr fun y hy => by rw [(hout y (hCsub (hT hy))).2]
    unfold CoreElig
    rw [h.2.1, h.2.2.1]
    constructor
    · rintro ⟨h1, h3⟩
      exact ⟨h1, fun z hz => ⟨by rw [← hrow z hz]; exact (h3 z hz).1,
        by rw [← hcol z hz]; exact (h3 z hz).2⟩⟩
    · rintro ⟨h1, h3⟩
      exact ⟨h1, fun z hz => ⟨by rw [hrow z hz]; exact (h3 z hz).1,
        by rw [hcol z hz]; exact (h3 z hz).2⟩⟩
  have hfirst : ∀ rem ⊆ shapeComponent P (shapeEdges P) v, ∀ k,
      firstCoreOfCard P s k rem = firstCoreOfCard Q s k rem := by
    intro rem hrem k
    unfold firstCoreOfCard
    rw [find?_congr_of_mem (q := fun l => decide (CoreElig Q s l.toFinset))]
    intro l hl
    refine decide_eq_decide.mpr (hel _ fun z hz => hrem ?_)
    rw [List.mem_toFinset] at hz
    exact mem_canonicalFinsetList.mp ((List.mem_sublistsLen.mp hl).1.subset hz)
  have hsel : ∀ rem ⊆ shapeComponent P (shapeEdges P) v, ∀ M',
      minCoreSel P s M' rem = minCoreSel Q s M' rem := by
    intro rem hrem M'
    unfold minCoreSel
    simp only [hfirst rem hrem]
  have hrun : ∀ M' fuel, ∀ rem ⊆ shapeComponent P (shapeEdges P) v,
      coreRunAux P s M' fuel rem = coreRunAux Q s M' fuel rem := by
    intro M' fuel
    induction fuel with
    | zero => intro rem _; rfl
    | succ fuel ih =>
      intro rem hrem
      simp only [coreRunAux]
      rw [hsel rem hrem M']
      split
      · rfl
      · rename_i T _
        rw [ih (rem \ T) (Finset.sdiff_subset.trans hrem)]
  refine ⟨hC, ?_, ?_, ?_⟩
  · unfold vertexCores coreFamily
    rw [← hC, hrun _ _ _ subset_rfl]
  · unfold vertexCappedCores coreFamily
    rw [← hC, hrun _ _ _ subset_rfl]
  · unfold vertexResidual coreResidual
    rw [← hC, hrun _ _ _ subset_rfl]

/-- The capacities `coreCap` are positive. -/
theorem coreCap_pos (P : ShapeParams) (s : ℕ) (v : BitString ⊕ BitString) : 0 < coreCap P s v := by
  cases v <;> simp only [coreCap, Sum.elim_inl, Sum.elim_inr] <;> positivity

/-- The capacities `coreCap` are at most `2^(max a b)`. -/
theorem coreCap_le (P : ShapeParams) (s : ℕ) (v : BitString ⊕ BitString) :
    coreCap P s v ≤ 2 ^ max P.a P.b := by
  cases v
  · simp only [coreCap, Sum.elim_inl]
    exact Nat.pow_le_pow_right (by norm_num) ((Nat.sub_le _ _).trans (le_max_left _ _))
  · simp only [coreCap, Sum.elim_inr]
    exact Nat.pow_le_pow_right (by norm_num) ((Nat.sub_le _ _).trans (le_max_right _ _))

/-- **Small sets without small eligible subsets are core-free** for the budget-`s` capacities: the
hypothesis of the online orientation lemma in the coverage and cap arguments. -/
theorem coreFree_of_noSmallElig {P : ShapeParams} {s M : ℕ} {E : Finset BitString}
    (h : ∀ T ⊆ E, CoreElig P s T → M < T.card) (hE : E.card ≤ M) :
    CoreFree (shapeSrc P) (shapeTgt P) (coreCap P s) E := by
  intro T hT hcore
  have hel : CoreElig P s T := by
    refine ⟨hcore.1, fun z hz => ⟨?_, ?_⟩⟩
    · have hv : Sum.inl (P.outA z) ∈ incidentVerts (shapeSrc P) (shapeTgt P) T :=
        mem_incidentVerts.mpr ⟨z, hz, Or.inl rfl⟩
      have := hcore.2 _ hv
      rw [degIn_shape_inl] at this
      exact this
    · have hv : Sum.inr (P.outB z) ∈ incidentVerts (shapeSrc P) (shapeTgt P) T :=
        mem_incidentVerts.mpr ⟨z, hz, Or.inr rfl⟩
      have := hcore.2 _ hv
      rw [degIn_shape_inr] at this
      exact this
  have h1 := h T hT hel
  have h2 := Finset.card_le_card hT
  omega

end Kolmogorov.StrongMerging.Upper
