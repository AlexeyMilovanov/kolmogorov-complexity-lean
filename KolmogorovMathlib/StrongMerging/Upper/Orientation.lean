import Mathlib.Computability.Partrec
import KolmogorovMathlib.StrongMerging.Upper.Graph

/-!
# The online orientation lemma and its event stream (blueprint G02, G03)

`sublinear-merging.tex`, Lemma `lem:orientation` (tex ~238) and the paragraph "What the online
condition contributes"; appendix `bp-upper-graph-orientation`, "Orientation interface".

* **G02 (`UpperOnlineOrientation`).**  The streaming update `orientStep` assigns an arriving edge
  to the endpoint of smaller normalized load `load v / d v`, comparing `load u * d v` with
  `load v * d u` and breaking ties towards `src`.  It records the owner of every edge and its
  `rank`, the owner's load just before the assignment (so the edges owned by `v` have ranks
  `0, 1, …, load v - 1` in arrival order).  `orient` runs the update along an arrival list.
  `upperOnlineOrientation`: for a duplicate-free arrival list of a `d`-core-free edge set with
  positive capacities, every final load satisfies `load v < 3 q d v`, where
  `q = ⌊log₂ W⌋ + 1` and `W = ∑_{v incident} d v`.  The proof follows the paper: the invariant
  `OrientInv` of the run, the final-load layers `V_t` (`loadLayer`), the counting bound
  `2 w(V_{t+3}) ≤ |E[V_t]|`, the peeling density bound `|E[V_t]| ≤ w(V_t)` (in `Graph`), and the
  halving iteration.
* **G03 (`UpperOrientationStream`).**  For an enumeration `en : ℕ → Option α` of a c.e. edge
  set, `arrivals en s` is the duplicate-free arrival list at stage `s` (prefix-monotone in `s`).
  `decodeOwned … v i` is the *partial* decoder of the `i`-th edge owned by `v`: it searches for
  the first stage at which such an edge has arrived.  `upperOrientationStream`: it halts on the
  actual (owner, rank) of every arrived edge and returns that edge; it never needs a completion
  time of the enumeration.  Prefix consistency (`orient_stable_of_prefix`) transfers the final
  load bound to the eventual stream.
-/

namespace Kolmogorov.StrongMerging.Upper

section Orientation

variable {α V : Type*} [DecidableEq α] [DecidableEq V]

/-- The state of the online orientation: current loads, the recorded owner of each processed
edge, and its rank (the owner's load just before the assignment). -/
structure OrientState (α V : Type*) where
  /-- The number of edges assigned so far to each vertex. -/
  load : V → ℕ
  /-- The endpoint to which each processed edge was assigned. -/
  owner : α → V
  /-- The rank of each processed edge in its owner's assignment list. -/
  rank : α → ℕ

/-- The owner chosen for an arriving edge `e`: the endpoint with smaller normalized load
`load / d`, compared by cross-multiplication `load (src e) * d (tgt e) ≤ load (tgt e) * d (src e)`;
ties go to `src e`. -/
def chooseOwner (src tgt : α → V) (d : V → ℕ) (load : V → ℕ) (e : α) : V :=
  if load (src e) * d (tgt e) ≤ load (tgt e) * d (src e) then src e else tgt e

/-- The initial state: all loads zero (the owner and rank of unprocessed edges are defaults). -/
def orientInit (src : α → V) : OrientState α V :=
  ⟨fun _ => 0, src, fun _ => 0⟩

/-- One irrevocable streaming update: assign the arriving edge `e` to `chooseOwner`, record its
rank, and increment the owner's load. -/
def orientStep (src tgt : α → V) (d : V → ℕ) (s : OrientState α V) (e : α) :
    OrientState α V :=
  ⟨Function.update s.load (chooseOwner src tgt d s.load e)
      (s.load (chooseOwner src tgt d s.load e) + 1),
    Function.update s.owner e (chooseOwner src tgt d s.load e),
    Function.update s.rank e (s.load (chooseOwner src tgt d s.load e))⟩

/-- The online orientation run along an arrival list (first element arrives first). -/
def orient (src tgt : α → V) (d : V → ℕ) (l : List α) : OrientState α V :=
  l.foldl (orientStep src tgt d) (orientInit src)

/-- The invariant of the orientation run after processing the edge set `P`. -/
structure OrientInv (src tgt : α → V) (d : V → ℕ) (P : Finset α) (s : OrientState α V) :
    Prop where
  /-- The load of `v` is the number of processed edges owned by `v`. -/
  load_eq : ∀ v, s.load v = (P.filter fun e => s.owner e = v).card
  /-- Owners are endpoints. -/
  owner_mem : ∀ e ∈ P, s.owner e = src e ∨ s.owner e = tgt e
  /-- Ranks are smaller than the owner's load. -/
  rank_lt : ∀ e ∈ P, s.rank e < s.load (s.owner e)
  /-- An edge is determined by its owner and rank. -/
  rank_inj : ∀ e ∈ P, ∀ e' ∈ P, s.owner e = s.owner e' → s.rank e = s.rank e' → e = e'
  /-- At its assignment the other endpoint had normalized load at least the owner's
  pre-assignment normalized load; loads only grow afterwards. -/
  balance : ∀ e ∈ P, ∀ u, (u = src e ∨ u = tgt e) → u ≠ s.owner e →
    s.rank e * d u ≤ s.load u * d (s.owner e)

variable (src tgt : α → V) (d : V → ℕ)

omit [DecidableEq α] in
/-- The invariant holds for the initial state and the empty edge set. -/
theorem orientInv_init : OrientInv src tgt d ∅ (orientInit src) := by
  exact ⟨fun v => by rw [Finset.filter_empty, Finset.card_empty]; rfl, by simp, by simp, by simp,
    by simp⟩

omit [DecidableEq α] [DecidableEq V] in
/-- The chosen owner is an endpoint, and the other endpoint has normalized load at least the
owner's: `load o * d u ≤ load u * d o` for `o = chooseOwner …` and the other endpoint `u ≠ o`.

Proof sketch: unfold `chooseOwner` and split on the comparison; in the `else` branch use
`lt_of_not_le` and weaken to `≤`. -/
theorem chooseOwner_spec (load : V → ℕ) (e : α) :
    (chooseOwner src tgt d load e = src e ∨ chooseOwner src tgt d load e = tgt e) ∧
      ∀ u, (u = src e ∨ u = tgt e) → u ≠ chooseOwner src tgt d load e →
        load (chooseOwner src tgt d load e) * d u ≤ load u * d (chooseOwner src tgt d load e) := by
  unfold chooseOwner
  split_ifs with hc
  · refine ⟨Or.inl rfl, fun u hu hne => ?_⟩
    rcases hu with rfl | rfl
    · exact absurd rfl hne
    · exact hc
  · refine ⟨Or.inr rfl, fun u hu hne => ?_⟩
    rcases hu with rfl | rfl
    · exact le_of_lt (not_le.mp hc)
    · exact absurd rfl hne

/-- Step preservation of `OrientInv.load_eq`.

Proof sketch: the new owner map agrees with the old one on `P` (as `e ∉ P`) and sends `e` to the
chosen owner `o`; split `v = o` (load `+1`, filter gains `e`) and `v ≠ o` (both unchanged). -/
theorem orientInv_step_load_eq {P : Finset α} {s : OrientState α V} {e : α}
    (h : OrientInv src tgt d P s) (he : e ∉ P) :
    ∀ v, (orientStep src tgt d s e).load v =
      ((insert e P).filter fun e' => (orientStep src tgt d s e).owner e' = v).card := by
  intro v
  have hset : ((insert e P).filter fun e' => (orientStep src tgt d s e).owner e' = v) =
      if chooseOwner src tgt d s.load e = v then insert e (P.filter fun e' => s.owner e' = v)
      else P.filter fun e' => s.owner e' = v := by
    ext x
    rw [Finset.mem_filter]
    by_cases hxe : x = e
    · rw [hxe]
      split_ifs with hv
      · simp [orientStep, hv]
      · simp [orientStep, hv, he]
    · have hown : (orientStep src tgt d s e).owner x = s.owner x := by simp [orientStep, hxe]
      rw [hown]
      split_ifs with hv
      · simp [Finset.mem_filter, hxe]
      · simp [Finset.mem_filter, hxe]
  rw [hset]
  split_ifs with hv
  · have hnot : e ∉ P.filter fun e' => s.owner e' = v := fun hm => he (Finset.mem_filter.mp hm).1
    rw [Finset.card_insert_of_notMem hnot, ← h.load_eq v, ← hv]
    simp [orientStep]
  · rw [← h.load_eq v]
    simp [orientStep, Ne.symm hv]

/-- Step preservation of `OrientInv.owner_mem`, `rank_lt` and `rank_inj`.

Proof sketch: for old edges owner and rank are unchanged (`Function.update_of_ne`) and loads only
grow.  The new edge has owner `o = chooseOwner …` (an endpoint by `chooseOwner_spec`) and rank
`load o < load o + 1`; it cannot collide with an old edge of owner `o`, whose rank is
`< load o` by `rank_lt`. -/
theorem orientInv_step_owner_rank {P : Finset α} {s : OrientState α V} {e : α}
    (h : OrientInv src tgt d P s) :
    (∀ x ∈ insert e P, (orientStep src tgt d s e).owner x = src x ∨
        (orientStep src tgt d s e).owner x = tgt x) ∧
      (∀ x ∈ insert e P, (orientStep src tgt d s e).rank x <
        (orientStep src tgt d s e).load ((orientStep src tgt d s e).owner x)) ∧
      ∀ x ∈ insert e P, ∀ y ∈ insert e P,
        (orientStep src tgt d s e).owner x = (orientStep src tgt d s e).owner y →
        (orientStep src tgt d s e).rank x = (orientStep src tgt d s e).rank y → x = y := by
  have hown : ∀ x, x ≠ e → (orientStep src tgt d s e).owner x = s.owner x := fun x hx => by
    simp [orientStep, hx]
  have hrank : ∀ x, x ≠ e → (orientStep src tgt d s e).rank x = s.rank x := fun x hx => by
    simp [orientStep, hx]
  have hown_e : (orientStep src tgt d s e).owner e = chooseOwner src tgt d s.load e := by
    simp [orientStep]
  have hrank_e : (orientStep src tgt d s e).rank e = s.load (chooseOwner src tgt d s.load e) := by
    simp [orientStep]
  have hload_ge : ∀ u, s.load u ≤ (orientStep src tgt d s e).load u := fun u => by
    simp only [orientStep]
    by_cases hu : u = chooseOwner src tgt d s.load e
    · rw [hu, Function.update_self]
      omega
    · rw [Function.update_of_ne hu]
  have hload_o : (orientStep src tgt d s e).load (chooseOwner src tgt d s.load e) =
      s.load (chooseOwner src tgt d s.load e) + 1 := by
    simp [orientStep]
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    by_cases hxe : x = e
    · rw [hxe, hown_e]
      exact (chooseOwner_spec src tgt d s.load e).1
    · rw [hown x hxe]
      exact h.owner_mem x ((Finset.mem_insert.mp hx).resolve_left hxe)
  · intro x hx
    by_cases hxe : x = e
    · rw [hxe, hown_e, hrank_e, hload_o]
      omega
    · rw [hown x hxe, hrank x hxe]
      exact lt_of_lt_of_le (h.rank_lt x ((Finset.mem_insert.mp hx).resolve_left hxe))
        (hload_ge _)
  · intro x hx y hy hxy hrxy
    by_cases hxe : x = e <;> by_cases hye : y = e
    · rw [hxe, hye]
    · exfalso
      have hy' : y ∈ P := (Finset.mem_insert.mp hy).resolve_left hye
      rw [hxe, hown_e, hown y hye] at hxy
      rw [hxe, hrank_e, hrank y hye] at hrxy
      have := h.rank_lt y hy'
      rw [← hxy, ← hrxy] at this
      exact lt_irrefl _ this
    · exfalso
      have hx' : x ∈ P := (Finset.mem_insert.mp hx).resolve_left hxe
      rw [hye, hown_e, hown x hxe] at hxy
      rw [hye, hrank_e, hrank x hxe] at hrxy
      have := h.rank_lt x hx'
      rw [hxy, hrxy] at this
      exact lt_irrefl _ this
    · have hx' : x ∈ P := (Finset.mem_insert.mp hx).resolve_left hxe
      have hy' : y ∈ P := (Finset.mem_insert.mp hy).resolve_left hye
      rw [hown x hxe, hown y hye] at hxy
      rw [hrank x hxe, hrank y hye] at hrxy
      exact h.rank_inj x hx' y hy' hxy hrxy

/-- Step preservation of `OrientInv.balance`.

Proof sketch: for an old edge, rank and owner are unchanged and the load of `u` can only grow.
For the new edge with owner `o` and an endpoint `u ≠ o`, the new load of `u` equals the old one
(`Function.update_of_ne`), and `chooseOwner_spec` gives `load o * d u ≤ load u * d o`, where
`load o` is the recorded rank. -/
theorem orientInv_step_balance {P : Finset α} {s : OrientState α V} {e : α}
    (h : OrientInv src tgt d P s) :
    ∀ x ∈ insert e P, ∀ u, (u = src x ∨ u = tgt x) → u ≠ (orientStep src tgt d s e).owner x →
      (orientStep src tgt d s e).rank x * d u ≤
        (orientStep src tgt d s e).load u * d ((orientStep src tgt d s e).owner x) := by
  intro x hx u hu hne
  by_cases hxe : x = e
  · rw [hxe] at hu hne ⊢
    have hown_e : (orientStep src tgt d s e).owner e = chooseOwner src tgt d s.load e := by
      simp [orientStep]
    have hrank_e : (orientStep src tgt d s e).rank e = s.load (chooseOwner src tgt d s.load e) := by
      simp [orientStep]
    rw [hown_e] at hne ⊢
    have hload_u : (orientStep src tgt d s e).load u = s.load u := by
      simp [orientStep, hne]
    rw [hrank_e, hload_u]
    exact (chooseOwner_spec src tgt d s.load e).2 u hu hne
  · have hx' : x ∈ P := (Finset.mem_insert.mp hx).resolve_left hxe
    have hown : (orientStep src tgt d s e).owner x = s.owner x := by simp [orientStep, hxe]
    have hrank : (orientStep src tgt d s e).rank x = s.rank x := by simp [orientStep, hxe]
    rw [hown] at hne ⊢
    rw [hrank]
    have hb := h.balance x hx' u hu hne
    have hload_ge : s.load u ≤ (orientStep src tgt d s e).load u := by
      simp only [orientStep]
      by_cases hu' : u = chooseOwner src tgt d s.load e
      · rw [hu', Function.update_self]
        omega
      · rw [Function.update_of_ne hu']
    exact hb.trans (Nat.mul_le_mul_right _ hload_ge)

/-- One streaming update preserves the invariant. -/
theorem orientInv_step {P : Finset α} {s : OrientState α V} {e : α}
    (h : OrientInv src tgt d P s) (he : e ∉ P) :
    OrientInv src tgt d (insert e P) (orientStep src tgt d s e) := by
  obtain ⟨h1, h2, h3⟩ := orientInv_step_owner_rank (e := e) src tgt d h
  exact ⟨orientInv_step_load_eq src tgt d h he, h1, h2, h3,
    orientInv_step_balance (e := e) src tgt d h⟩

/-- The invariant along a list of fresh arrivals. -/
theorem orientInv_foldl : ∀ (l : List α) (P : Finset α) (s : OrientState α V), l.Nodup →
    (∀ e ∈ l, e ∉ P) → OrientInv src tgt d P s →
    OrientInv src tgt d (P ∪ l.toFinset) (l.foldl (orientStep src tgt d) s)
  | [], P, s, _, _, h => by simpa using h
  | e :: l, P, s, hnd, hP, h => by
    rw [List.foldl_cons]
    have hstep := orientInv_step src tgt d h (hP e List.mem_cons_self)
    have hrest := orientInv_foldl l (insert e P) (orientStep src tgt d s e)
      (List.nodup_cons.mp hnd).2
      (fun x hx hxP => by
        rcases Finset.mem_insert.mp hxP with rfl | hxP
        · exact (List.nodup_cons.mp hnd).1 hx
        · exact hP x (List.mem_cons_of_mem _ hx) hxP) hstep
    have hset : insert e P ∪ l.toFinset = P ∪ (e :: l).toFinset := by
      ext x
      simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset, List.mem_cons]
      tauto
    rw [← hset]
    exact hrest

/-- The orientation run of a duplicate-free arrival list satisfies the invariant. -/
theorem orientInv_orient (l : List α) (hnd : l.Nodup) :
    OrientInv src tgt d l.toFinset (orient src tgt d l) := by
  have h := orientInv_foldl src tgt d l ∅ (orientInit src) hnd (fun _ _ h => by simp at h)
    (orientInv_init src tgt d)
  rw [Finset.empty_union] at h
  exact h

/-- The final-load layer `V_t = {v incident to E : load v ≥ t · d v}`. -/
def loadLayer (E : Finset α) (s : OrientState α V) (t : ℕ) : Finset V :=
  (incidentVerts src tgt E).filter fun v => t * d v ≤ s.load v

/-- The rank window of `v`: the edges of `E` owned by `v` with rank in `[k₁, k₂)`. -/
def rankWindow (E : Finset α) (s : OrientState α V) (v : V) (k₁ k₂ : ℕ) : Finset α :=
  E.filter fun e => s.owner e = v ∧ k₁ ≤ s.rank e ∧ s.rank e < k₂

variable {src tgt d}

omit [DecidableEq α] in
/-- **Rank windows.**  Under the invariant, for `k₂ ≤ load v` exactly `k₂ - k₁` (truncated) edges
owned by `v` have rank in `[k₁, k₂)`.

Proof sketch: by `load_eq`, `rank_lt` and `rank_inj`, the rank map is a bijection from the edges
owned by `v` onto `Finset.range (load v)` (injective with values `< load v` on a set of
cardinality `load v`); the preimage of `Finset.Ico k₁ k₂` therefore has `k₂ - k₁` elements. -/
theorem card_rankWindow {E : Finset α} {s : OrientState α V} (h : OrientInv src tgt d E s)
    (v : V) {k₁ k₂ : ℕ} (hk₂ : k₂ ≤ s.load v) :
    (rankWindow E s v k₁ k₂).card = k₂ - k₁ := by
  have hinj : Set.InjOn s.rank (rankWindow E s v k₁ k₂ : Set α) := by
    intro x hx y hy hxy
    have hx' := Finset.mem_filter.mp (Finset.mem_coe.mp hx)
    have hy' := Finset.mem_filter.mp (Finset.mem_coe.mp hy)
    exact h.rank_inj x hx'.1 y hy'.1 (hx'.2.1.trans hy'.2.1.symm) hxy
  have hinj' : Set.InjOn s.rank ((E.filter fun e => s.owner e = v : Finset α) : Set α) := by
    intro x hx y hy hxy
    have hx' := Finset.mem_filter.mp (Finset.mem_coe.mp hx)
    have hy' := Finset.mem_filter.mp (Finset.mem_coe.mp hy)
    exact h.rank_inj x hx'.1 y hy'.1 (hx'.2.trans hy'.2.symm) hxy
  have hsub : (rankWindow E s v k₁ k₂).image s.rank ⊆ Finset.Ico k₁ k₂ := by
    intro r hr
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hr
    have hx' := Finset.mem_filter.mp hx
    exact Finset.mem_Ico.mpr ⟨hx'.2.2.1, hx'.2.2.2⟩
  have hall : (E.filter fun e => s.owner e = v).image s.rank = Finset.range (s.load v) := by
    apply Finset.eq_of_subset_of_card_le
    · intro r hr
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hr
      have hx' := Finset.mem_filter.mp hx
      rw [Finset.mem_range, ← hx'.2]
      exact h.rank_lt x hx'.1
    · apply le_of_eq
      rw [Finset.card_range, Finset.card_image_of_injOn hinj', h.load_eq v]
  have hsup : Finset.Ico k₁ k₂ ⊆ (rankWindow E s v k₁ k₂).image s.rank := by
    intro r hr
    have hr' := Finset.mem_Ico.mp hr
    have hmem : r ∈ (E.filter fun e => s.owner e = v).image s.rank := by
      rw [hall, Finset.mem_range]
      omega
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hmem
    have hx' := Finset.mem_filter.mp hx
    exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx'.1, hx'.2, hr'.1, hr'.2⟩, rfl⟩
  rw [← Finset.card_image_of_injOn hinj, Finset.Subset.antisymm hsub hsup, Nat.card_Ico]

omit [DecidableEq α] in
/-- **Late edges stay in the layer.**  If `v ∈ V_{t+3}` owns `e ∈ E` with rank at least
`(t+1) d v`, then both endpoints of `e` lie in `V_t`.

Proof sketch: the owner `v` satisfies `t d v ≤ (t+3) d v ≤ load v`.  For the other endpoint `u`
(an endpoint `≠ v`), `balance` gives `rank e * d u ≤ load u * d v`, hence
`(t+1) d v d u ≤ load u d v`, and cancelling `d v > 0` (positivity at the incident vertex `v`)
gives `t d u ≤ (t+1) d u ≤ load u`.  Both endpoints are incident to `E`. -/
theorem mem_inducedEdges_of_late {E : Finset α} {s : OrientState α V}
    (h : OrientInv src tgt d E s) (hpos : ∀ v ∈ incidentVerts src tgt E, 0 < d v) {t : ℕ}
    {v : V} (hv : v ∈ loadLayer src tgt d E s (t + 3)) {e : α} (he : e ∈ E)
    (hown : s.owner e = v) (hrk : (t + 1) * d v ≤ s.rank e) :
    e ∈ inducedEdges src tgt E (loadLayer src tgt d E s t) := by
  have hv' := Finset.mem_filter.mp hv
  have hdv : 0 < d v := hpos v hv'.1
  have hgood : ∀ u, (u = src e ∨ u = tgt e) → u ∈ loadLayer src tgt d E s t := by
    intro u hu
    have hinc : u ∈ incidentVerts src tgt E :=
      mem_incidentVerts.mpr ⟨e, he, hu.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)⟩
    refine Finset.mem_filter.mpr ⟨hinc, ?_⟩
    by_cases huv : u = v
    · rw [huv]
      exact le_trans (Nat.mul_le_mul_right _ (by omega)) hv'.2
    · have hb := h.balance e he u hu (by rw [hown]; exact huv)
      rw [hown] at hb
      have h1 : (t + 1) * d u * d v ≤ s.load u * d v := by
        nlinarith [Nat.mul_le_mul_right (d u) hrk, hb]
      have h2 : (t + 1) * d u ≤ s.load u := Nat.le_of_mul_le_mul_right h1 hdv
      exact le_trans (Nat.mul_le_mul_right _ (Nat.le_succ t)) h2
  exact Finset.mem_filter.mpr ⟨he, hgood _ (Or.inl rfl), hgood _ (Or.inr rfl)⟩

omit [DecidableEq α] in
/-- **Layer counting** `2 w(V_{t+3}) ≤ |E[V_t]|` (`lem:orientation`, proof).

Proof sketch: for `v ∈ V_{t+3}` the window of edges owned by `v` with rank in
`[(t+1) d v, (t+3) d v)` has exactly `2 d v` elements (`card_rankWindow`, as
`(t+3) d v ≤ load v`); these windows lie in `E[V_t]` (`mem_inducedEdges_of_late`) and are pairwise
disjoint (different owners).  Sum with `Finset.card_biUnion`. -/
theorem two_mul_sum_loadLayer_le {E : Finset α} {s : OrientState α V}
    (h : OrientInv src tgt d E s) (hpos : ∀ v ∈ incidentVerts src tgt E, 0 < d v) (t : ℕ) :
    2 * ∑ v ∈ loadLayer src tgt d E s (t + 3), d v ≤
      (inducedEdges src tgt E (loadLayer src tgt d E s t)).card := by
  classical
  have hcard : ∀ v ∈ loadLayer src tgt d E s (t + 3),
      (rankWindow E s v ((t + 1) * d v) ((t + 3) * d v)).card = 2 * d v := by
    intro v hv
    have hv' := (Finset.mem_filter.mp hv).2
    rw [card_rankWindow h v hv']
    have e1 : (t + 3) * d v = 2 * d v + (t + 1) * d v := by ring
    rw [e1, Nat.add_sub_cancel]
  have hdisj : ∀ x ∈ loadLayer src tgt d E s (t + 3), ∀ y ∈ loadLayer src tgt d E s (t + 3),
      x ≠ y → Disjoint (rankWindow E s x ((t + 1) * d x) ((t + 3) * d x))
        (rankWindow E s y ((t + 1) * d y) ((t + 3) * d y)) := by
    intro x _ y _ hxy
    rw [Finset.disjoint_left]
    intro e hex hey
    exact hxy (((Finset.mem_filter.mp hex).2.1).symm.trans (Finset.mem_filter.mp hey).2.1)
  have hsub : ((loadLayer src tgt d E s (t + 3)).biUnion fun v =>
      rankWindow E s v ((t + 1) * d v) ((t + 3) * d v)) ⊆
      inducedEdges src tgt E (loadLayer src tgt d E s t) := by
    intro e he
    obtain ⟨v, hv, hev⟩ := Finset.mem_biUnion.mp he
    have hev' := Finset.mem_filter.mp hev
    exact mem_inducedEdges_of_late h hpos hv hev'.1 hev'.2.1 hev'.2.2.1
  calc 2 * ∑ v ∈ loadLayer src tgt d E s (t + 3), d v
      = ∑ v ∈ loadLayer src tgt d E s (t + 3),
          (rankWindow E s v ((t + 1) * d v) ((t + 3) * d v)).card := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun v hv => (hcard v hv).symm
    _ = ((loadLayer src tgt d E s (t + 3)).biUnion fun v =>
          rankWindow E s v ((t + 1) * d v) ((t + 3) * d v)).card :=
        (Finset.card_biUnion hdisj).symm
    _ ≤ _ := Finset.card_le_card hsub

/-- The halving iteration: if `2 w(t + 3) ≤ w(t)` for all `t`, then `2^q w(3q) ≤ w(0)`. -/
theorem pow_mul_le_of_halving (w : ℕ → ℕ) (h : ∀ t, 2 * w (t + 3) ≤ w t) :
    ∀ q, 2 ^ q * w (3 * q) ≤ w 0
  | 0 => by simp
  | q + 1 => by
    have ih := pow_mul_le_of_halving w h q
    have h1 := h (3 * q)
    calc 2 ^ (q + 1) * w (3 * (q + 1)) = 2 ^ q * (2 * w (3 * q + 3)) := by
          rw [show 3 * (q + 1) = 3 * q + 3 by ring, pow_succ]
          ring
      _ ≤ 2 ^ q * w (3 * q) := Nat.mul_le_mul_left _ h1
      _ ≤ w 0 := ih

/-- **Online orientation lemma (blueprint G02, `UpperOnlineOrientation`; `lem:orientation`).**
Let `l` be a duplicate-free arrival list of the edge set `E = l.toFinset`, with positive
capacities at the incident vertices, and `d`-core-free.  The online run satisfies the invariant
`OrientInv` and every incident vertex has final load `load v < 3 (⌊log₂ W⌋ + 1) d v`, where
`W = ∑_{v incident to E} d v`.  Looplessness (assumed in the paper; the shape graph is loopless by
`shapeSrc_ne_shapeTgt`) is not needed in this formulation: a loop's other endpoint is its
owner. -/
theorem upperOnlineOrientation (l : List α) (hnd : l.Nodup)
    (hpos : ∀ v ∈ incidentVerts src tgt l.toFinset, 0 < d v)
    (hfree : CoreFree src tgt d l.toFinset) :
    OrientInv src tgt d l.toFinset (orient src tgt d l) ∧
      ∀ v ∈ incidentVerts src tgt l.toFinset, (orient src tgt d l).load v <
        3 * (Nat.log 2 (∑ u ∈ incidentVerts src tgt l.toFinset, d u) + 1) * d v := by
  have hinv := orientInv_orient src tgt d l hnd
  refine ⟨hinv, ?_⟩
  have hhalf : ∀ t, 2 * ∑ v ∈ loadLayer src tgt d l.toFinset (orient src tgt d l) (t + 3), d v ≤
      ∑ v ∈ loadLayer src tgt d l.toFinset (orient src tgt d l) t, d v := fun t =>
    (two_mul_sum_loadLayer_le hinv hpos t).trans (card_inducedEdges_le_of_coreFree hfree _)
  have hiter : 2 ^ (Nat.log 2 (∑ u ∈ incidentVerts src tgt l.toFinset, d u) + 1) *
      ∑ v ∈ loadLayer src tgt d l.toFinset (orient src tgt d l)
        (3 * (Nat.log 2 (∑ u ∈ incidentVerts src tgt l.toFinset, d u) + 1)), d v ≤
      ∑ v ∈ loadLayer src tgt d l.toFinset (orient src tgt d l) 0, d v :=
    pow_mul_le_of_halving
      (fun t => ∑ v ∈ loadLayer src tgt d l.toFinset (orient src tgt d l) t, d v) hhalf _
  have h0 : loadLayer src tgt d l.toFinset (orient src tgt d l) 0 =
      incidentVerts src tgt l.toFinset := by
    simp [loadLayer]
  rw [h0] at hiter
  have hW := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2)
    (∑ u ∈ incidentVerts src tgt l.toFinset, d u)
  intro v hv
  by_contra hcon
  have hmem : v ∈ loadLayer src tgt d l.toFinset (orient src tgt d l)
      (3 * (Nat.log 2 (∑ u ∈ incidentVerts src tgt l.toFinset, d u) + 1)) :=
    Finset.mem_filter.mpr ⟨hv, not_lt.mp hcon⟩
  have hle := Finset.single_le_sum (fun i _ => Nat.zero_le (d i)) hmem
  have hpv := hpos v hv
  have hsum_pos : 0 < ∑ v ∈ loadLayer src tgt d l.toFinset (orient src tgt d l)
      (3 * (Nat.log 2 (∑ u ∈ incidentVerts src tgt l.toFinset, d u) + 1)), d v := by omega
  have := Nat.le_mul_of_pos_right
    (2 ^ (Nat.log 2 (∑ u ∈ incidentVerts src tgt l.toFinset, d u) + 1)) hsum_pos
  omega

/-- **Rank bound for the decoder.**  Every edge of the run has an incident owner and rank
`< 3 (⌊log₂ W⌋ + 1) d (owner)`: the ordinal of an edge in its owner's assignment list fits in
`⌈log₂ (3 q)⌉ + log₂ d` bits. -/
theorem rank_lt_of_orientation (l : List α) (hnd : l.Nodup)
    (hpos : ∀ v ∈ incidentVerts src tgt l.toFinset, 0 < d v)
    (hfree : CoreFree src tgt d l.toFinset) {e : α} (he : e ∈ l) :
    (orient src tgt d l).rank e <
      3 * (Nat.log 2 (∑ u ∈ incidentVerts src tgt l.toFinset, d u) + 1) *
        d ((orient src tgt d l).owner e) := by
  obtain ⟨hinv, hload⟩ := upperOnlineOrientation l hnd hpos hfree
  have he' : e ∈ l.toFinset := List.mem_toFinset.mpr he
  have hinc : (orient src tgt d l).owner e ∈ incidentVerts src tgt l.toFinset := by
    refine mem_incidentVerts.mpr ⟨e, he', ?_⟩
    rcases hinv.owner_mem e he' with h | h
    · exact Or.inl h.symm
    · exact Or.inr h.symm
  exact (hinv.rank_lt e he').trans (hload _ hinc)

/-! ### G03: the event stream and the partial owner-rank decoder -/

/-- Folding updates over arrivals other than `e` changes neither the owner nor the rank of `e`. -/
theorem foldl_orientStep_stable {e : α} : ∀ (t : List α) (s : OrientState α V), e ∉ t →
    (t.foldl (orientStep src tgt d) s).owner e = s.owner e ∧
      (t.foldl (orientStep src tgt d) s).rank e = s.rank e
  | [], _, _ => ⟨rfl, rfl⟩
  | x :: t, s, h => by
    rw [List.foldl_cons]
    have hx : e ≠ x := fun hex => h (by rw [hex]; exact List.mem_cons_self)
    have hrest := foldl_orientStep_stable t (orientStep src tgt d s x)
      (fun ht => h (List.mem_cons_of_mem _ ht))
    refine ⟨hrest.1.trans ?_, hrest.2.trans ?_⟩
    · simp [orientStep, hx]
    · simp [orientStep, hx]

/-- **Prefix consistency.**  Extending a duplicate-free arrival list changes no earlier owner or
rank.

Proof sketch: write `l₂ = l₁ ++ t` (`List.IsPrefix`); `orient (l₁ ++ t)` is the fold of
`orientStep` over `t` from `orient l₁` (`List.foldl_append`); `e ∉ t` by `Nodup`, and each step
updates `owner`/`rank` only at the arriving edge (`Function.update_of_ne`). -/
theorem orient_stable_of_prefix {l₁ l₂ : List α} (hpre : l₁ <+: l₂) (hnd : l₂.Nodup) {e : α}
    (he : e ∈ l₁) :
    (orient src tgt d l₂).owner e = (orient src tgt d l₁).owner e ∧
      (orient src tgt d l₂).rank e = (orient src tgt d l₁).rank e := by
  obtain ⟨t, rfl⟩ := hpre
  have het : e ∉ t := fun het => List.disjoint_of_nodup_append hnd he het
  unfold orient
  rw [List.foldl_append]
  exact foldl_orientStep_stable t _ het

/-- The duplicate-free arrival list of an enumeration `en` at stage `s`: the values `en 0, …,
en (s - 1)` in order of first appearance. -/
def arrivals (en : ℕ → Option α) : ℕ → List α
  | 0 => []
  | s + 1 =>
    match en s with
    | none => arrivals en s
    | some e => if e ∈ arrivals en s then arrivals en s else arrivals en s ++ [e]

/-- Arrival lists are duplicate-free. -/
theorem arrivals_nodup (en : ℕ → Option α) (s : ℕ) : (arrivals en s).Nodup := by
  induction s with
  | zero => exact List.nodup_nil
  | succ s ih =>
    simp only [arrivals]
    split
    · exact ih
    · split_ifs with h
      · exact ih
      · refine ih.append (List.nodup_singleton _) fun x hx hx' => h ?_
        rw [List.mem_singleton] at hx'
        rw [← hx']
        exact hx

/-- Arrival lists grow by extension: `arrivals en s` is a prefix of `arrivals en s'` for
`s ≤ s'`. -/
theorem arrivals_prefix (en : ℕ → Option α) {s s' : ℕ} (h : s ≤ s') :
    arrivals en s <+: arrivals en s' := by
  induction h with
  | refl => exact List.prefix_refl _
  | step _ ih =>
    refine ih.trans ?_
    simp only [arrivals]
    split
    · exact List.prefix_refl _
    · split_ifs
      · exact List.prefix_refl _
      · exact List.prefix_append _ _

/-- An edge has arrived by stage `s` exactly when it was enumerated before `s`. -/
theorem mem_arrivals_iff (en : ℕ → Option α) (s : ℕ) (e : α) :
    e ∈ arrivals en s ↔ ∃ i < s, en i = some e := by
  induction s with
  | zero => simp [arrivals]
  | succ s ih =>
    have hstep : e ∈ arrivals en (s + 1) ↔ e ∈ arrivals en s ∨ en s = some e := by
      simp only [arrivals]
      split
      · rename_i h
        simp [h]
      · rename_i e' h
        split_ifs with hmem
        · constructor
          · exact Or.inl
          · rintro (h1 | h1)
            · exact h1
            · have he' : e' = e := Option.some_inj.mp (h.symm.trans h1)
              rw [← he']
              exact hmem
        · rw [List.mem_append, List.mem_singleton, h, Option.some_inj]
          exact or_congr_right eq_comm
    rw [hstep, ih]
    constructor
    · rintro (⟨i, hi, h⟩ | h)
      · exact ⟨i, by omega, h⟩
      · exact ⟨s, by omega, h⟩
    · rintro ⟨i, hi, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact Or.inl ⟨i, hi, h⟩
      · exact Or.inr h

variable (src tgt d)

/-- The edge owned by `v` with rank `i` among the arrivals at stage `s`, if it has arrived. -/
def ownedHit (en : ℕ → Option α) (v : V) (i : ℕ) (s : ℕ) : Option α :=
  (arrivals en s).find? fun e =>
    decide ((orient src tgt d (arrivals en s)).owner e = v ∧
      (orient src tgt d (arrivals en s)).rank e = i)

/-- **The partial owner-rank decoder.**  Search for the first stage at which an edge owned by `v`
with rank `i` has arrived, and return it.  It may diverge on an unavailable rank; it never uses a
completion time of the enumeration. -/
def decodeOwned (en : ℕ → Option α) (v : V) (i : ℕ) : Part α :=
  (Nat.rfind fun s => Part.some (ownedHit src tgt d en v i s).isSome).bind fun s =>
    Part.ofOption (ownedHit src tgt d en v i s)

variable {src tgt d}

/-- A hit is an arrived edge with the requested owner and rank.

Proof sketch: `List.find?_some` and `List.mem_of_find?_eq_some`, then `decide_eq_true_iff`. -/
theorem ownedHit_spec {en : ℕ → Option α} {v : V} {i s : ℕ} {e : α}
    (h : ownedHit src tgt d en v i s = some e) :
    e ∈ arrivals en s ∧ (orient src tgt d (arrivals en s)).owner e = v ∧
      (orient src tgt d (arrivals en s)).rank e = i := by
  unfold ownedHit at h
  have h1 := List.find?_some h
  have h2 := List.mem_of_find?_eq_some h
  simp only [decide_eq_true_eq] at h1
  exact ⟨h2, h1.1, h1.2⟩

/-- An arrived edge produces a hit at its own owner and rank.

Proof sketch: `List.find?_isSome` with the witness `e`. -/
theorem ownedHit_isSome_of_mem {en : ℕ → Option α} {s : ℕ} {e : α} (he : e ∈ arrivals en s) :
    (ownedHit src tgt d en ((orient src tgt d (arrivals en s)).owner e)
      ((orient src tgt d (arrivals en s)).rank e) s).isSome := by
  unfold ownedHit
  rw [List.find?_isSome]
  exact ⟨e, he, by simp⟩

/-- **The search halts at the first hit.**  If there is a hit at stage `s`, the decoder halts and
returns the hit at the least such stage `s₁ ≤ s`.

Proof sketch: `Nat.rfind` of a total Boolean predicate with a true value at `s` is defined
(`Nat.rfind_dom'`/`Nat.rfind_dom`), returns some `s₁` with a true value (`Nat.rfind_spec`) and
`s₁ ≤ s` by `Nat.rfind_min'`; then `Part.mem_bind_iff` and `Part.mem_ofOption`. -/
theorem exists_mem_decodeOwned {en : ℕ → Option α} {v : V} {i s : ℕ}
    (h : (ownedHit src tgt d en v i s).isSome) :
    ∃ s₁ ≤ s, ∃ e', ownedHit src tgt d en v i s₁ = some e' ∧
      e' ∈ decodeOwned src tgt d en v i := by
  obtain ⟨s₁, hs₁, hle⟩ := Nat.rfind_min' (p := fun s => (ownedHit src tgt d en v i s).isSome) h
  have hspec := Nat.rfind_spec hs₁
  have hsome : (ownedHit src tgt d en v i s₁).isSome = true := (Part.mem_some_iff.mp hspec).symm
  obtain ⟨e', he'⟩ := Option.isSome_iff_exists.mp hsome
  refine ⟨s₁, hle, e', he', ?_⟩
  unfold decodeOwned
  rw [Part.mem_bind_iff]
  refine ⟨s₁, hs₁, ?_⟩
  show e' ∈ Part.ofOption (ownedHit src tgt d en v i s₁)
  rw [he']
  exact Part.mem_ofOption.mpr rfl

/-- **The orientation stream (blueprint G03, `UpperOrientationStream`).**  For an enumeration of
edges, every edge `e` that has arrived by some stage `s₀` is returned by the partial decoder at
its owner and rank computed at stage `s₀` (equivalently at any later stage, by prefix
consistency).  The decoder halts at the actual ordinal without knowing when the enumeration is
complete. -/
theorem upperOrientationStream (en : ℕ → Option α) {s₀ : ℕ} {e : α}
    (he : e ∈ arrivals en s₀) :
    e ∈ decodeOwned src tgt d en ((orient src tgt d (arrivals en s₀)).owner e)
      ((orient src tgt d (arrivals en s₀)).rank e) := by
  obtain ⟨s₁, hs₁, e', hhit, hmem⟩ := exists_mem_decodeOwned (src := src) (tgt := tgt) (d := d)
    (ownedHit_isSome_of_mem (src := src) (tgt := tgt) (d := d) he)
  obtain ⟨he'1, he'2, he'3⟩ := ownedHit_spec hhit
  have hpre : arrivals en s₁ <+: arrivals en s₀ := arrivals_prefix en hs₁
  have hnd : (arrivals en s₀).Nodup := arrivals_nodup en s₀
  obtain ⟨hown, hrk⟩ := orient_stable_of_prefix (src := src) (tgt := tgt) (d := d) hpre hnd he'1
  have hinv := orientInv_orient src tgt d (arrivals en s₀) hnd
  have he'₀ : e' ∈ arrivals en s₀ := hpre.subset he'1
  have heq : e' = e := hinv.rank_inj e' (List.mem_toFinset.mpr he'₀) e (List.mem_toFinset.mpr he)
    (hown.trans he'2) (hrk.trans he'3)
  rw [heq] at hmem
  exact hmem

/-- The load of a vertex in a recorded history of `(edge, owner, rank)` triples: the number of
recorded triples whose owner is that vertex. -/
def decodePRLoad {α' V' : Type*} [DecidableEq V'] (h : List (α' × V' × ℕ)) (v : V') : ℕ :=
  h.countP fun t => decide (t.2.1 = v)

/-- One step of the history simulation of `orientStep`: append the triple `(e, o, load o)`, where
the owner `o` is chosen by `chooseOwner` from the loads of the history. -/
def decodePRStep {α' V' : Type*} [DecidableEq V'] (s₁ t₁ : α' → V') (c₁ : V' → ℕ)
    (h : List (α' × V' × ℕ)) (e : α') : List (α' × V' × ℕ) :=
  h ++ [(e, chooseOwner s₁ t₁ c₁ (decodePRLoad h) e,
    decodePRLoad h (chooseOwner s₁ t₁ c₁ (decodePRLoad h) e))]

/-- The history of the orientation run along an arrival list: the list of triples
`(edge, owner, rank)` in arrival order. -/
def decodePRHist {α' V' : Type*} [DecidableEq V'] (s₁ t₁ : α' → V') (c₁ : V' → ℕ)
    (l : List α') : List (α' × V' × ℕ) :=
  l.foldl (decodePRStep s₁ t₁ c₁) []

/-- Appending one arrival appends one step to the history. -/
theorem decodePRHist_concat {α' V' : Type*} [DecidableEq V'] (s₁ t₁ : α' → V')
    (c₁ : V' → ℕ) (l : List α') (e : α') :
    decodePRHist s₁ t₁ c₁ (l ++ [e]) = decodePRStep s₁ t₁ c₁ (decodePRHist s₁ t₁ c₁ l) e := by
  simp only [decodePRHist, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- Appending one arrival performs one `orientStep` on the orientation run. -/
theorem decodePR_orient_concat {α' V' : Type*} [DecidableEq α'] [DecidableEq V']
    (s₁ t₁ : α' → V') (c₁ : V' → ℕ) (l : List α') (e : α') :
    orient s₁ t₁ c₁ (l ++ [e]) = orientStep s₁ t₁ c₁ (orient s₁ t₁ c₁ l) e := by
  simp only [orient, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- The history step, written with a load function equal to the history loads. -/
theorem decodePRStep_eq {α' V' : Type*} [DecidableEq V'] (s₁ t₁ : α' → V') (c₁ : V' → ℕ)
    (h : List (α' × V' × ℕ)) (e : α') (ld : V' → ℕ) (hld : decodePRLoad h = ld) :
    decodePRStep s₁ t₁ c₁ h e =
      h ++ [(e, chooseOwner s₁ t₁ c₁ ld e, ld (chooseOwner s₁ t₁ c₁ ld e))] := by
  subst hld
  rfl

/-- The load after appending one triple. -/
theorem decodePRLoad_concat {α' V' : Type*} [DecidableEq V'] (h : List (α' × V' × ℕ))
    (x : α' × V' × ℕ) (v : V') :
    decodePRLoad (h ++ [x]) v = decodePRLoad h v + if x.2.1 = v then 1 else 0 := by
  simp only [decodePRLoad, List.countP_append, List.countP_singleton, decide_eq_true_eq]

/-- **The history simulates the orientation run.**  For a duplicate-free arrival list, the history
loads are the loads of the run, and the history lists every arrival with its owner and rank. -/
theorem decodePR_hist_spec {α' V' : Type*} [DecidableEq α'] [DecidableEq V'] (s₁ t₁ : α' → V')
    (c₁ : V' → ℕ) (l : List α') (hl : l.Nodup) :
    decodePRLoad (decodePRHist s₁ t₁ c₁ l) = (orient s₁ t₁ c₁ l).load ∧
      decodePRHist s₁ t₁ c₁ l =
        l.map fun e => (e, (orient s₁ t₁ c₁ l).owner e, (orient s₁ t₁ c₁ l).rank e) := by
  induction l using List.reverseRecOn with
  | nil =>
    refine ⟨?_, ?_⟩
    · funext v
      simp [decodePRHist, decodePRLoad, orient, orientInit]
    · simp [decodePRHist]
  | append_singleton l e ih =>
    have hnd := List.nodup_append.mp hl
    have hel : e ∉ l := fun h => hnd.2.2 e h e (List.mem_singleton_self e) rfl
    obtain ⟨ih1, ih2⟩ := ih hnd.1
    rw [decodePRHist_concat, decodePR_orient_concat,
      decodePRStep_eq s₁ t₁ c₁ _ e _ ih1]
    refine ⟨?_, ?_⟩
    · funext v
      rw [decodePRLoad_concat, congrFun ih1 v]
      simp only [orientStep, Function.update_apply]
      by_cases hv : v = chooseOwner s₁ t₁ c₁ (orient s₁ t₁ c₁ l).load e
      · subst hv
        simp
      · simp [hv, Ne.symm hv]
    · rw [ih2, List.map_append, List.map_cons, List.map_nil]
      congr 1
      · refine List.map_congr_left fun x hx => ?_
        have hxe : x ≠ e := fun h => hel (h ▸ hx)
        simp [orientStep, hxe]
      · simp [orientStep]

/-- **The hit via the history.**  The owned hit at stage `k` is the first history triple with the
requested owner and rank. -/
theorem decodePR_ownedHit_eq {α' V' : Type*} [DecidableEq α'] [DecidableEq V'] (s₁ t₁ : α' → V')
    (c₁ : V' → ℕ) (en : ℕ → Option α') (v : V') (i k : ℕ) :
    ownedHit s₁ t₁ c₁ en v i k = ((decodePRHist s₁ t₁ c₁ (arrivals en k)).find?
      fun t => decide (t.2.1 = v ∧ t.2.2 = i)).map Prod.fst := by
  rw [(decodePR_hist_spec s₁ t₁ c₁ (arrivals en k) (arrivals_nodup en k)).2, List.find?_map,
    Option.map_map]
  unfold ownedHit
  exact (Option.map_id' (x := _)).symm

/-- One stage of the simulated arrival process on the pair (arrival list, history): a fresh
enumerated edge is appended to both, a repeated or missing one changes nothing. -/
def decodePRRunStep {α' V' : Type*} [DecidableEq α'] [DecidableEq V'] (s₁ t₁ : α' → V')
    (c₁ : V' → ℕ) (o : Option α') (st : List α' × List (α' × V' × ℕ)) :
    List α' × List (α' × V' × ℕ) :=
  match o with
  | none => st
  | some e => if e ∈ st.1 then st else (st.1 ++ [e], decodePRStep s₁ t₁ c₁ st.2 e)

/-- The `Nat.rec` run of `decodePRRunStep` computes the arrival list and its history. -/
theorem decodePR_rec_eq {α' V' : Type*} [DecidableEq α'] [DecidableEq V'] (s₁ t₁ : α' → V')
    (c₁ : V' → ℕ) (en : ℕ → Option α') (k : ℕ) :
    Nat.rec (motive := fun _ => List α' × List (α' × V' × ℕ)) ([], [])
      (fun y IH => decodePRRunStep s₁ t₁ c₁ (en y) IH) k =
      (arrivals en k, decodePRHist s₁ t₁ c₁ (arrivals en k)) := by
  induction k with
  | zero => simp only [Nat.rec_zero, arrivals, decodePRHist, List.foldl_nil]
  | succ k ih =>
    rw [Nat.rec_add_one, ih]
    simp only [arrivals]
    split
    · rename_i h
      simp only [h, decodePRRunStep]
    · rename_i e h
      simp only [h, decodePRRunStep]
      split_ifs with hm
      · rfl
      · rw [decodePRHist_concat]

/-- The history load is primitive recursive. -/
theorem decodePRLoad_primrec {α' V' : Type} [Primcodable α'] [Primcodable V'] [DecidableEq V'] :
    Primrec₂ (decodePRLoad : List (α' × V' × ℕ) → V' → ℕ) := by
  have hp : Primrec₂ fun (a : List (α' × V' × ℕ) × V') (t : α' × V' × ℕ) =>
      decide (t.2.1 = a.2) :=
    (Primrec.eq (α := V')).decide.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.snd.comp Primrec.fst)
  have h := list_countP_primrec (f := fun a : List (α' × V' × ℕ) × V' => a.1) Primrec.fst hp
  exact h

/-- The owner chosen from the history loads is computable in the parameter. -/
theorem decodePR_choose_computable {β α' V' : Type} [Primcodable β] [Primcodable α']
    [Primcodable V'] [DecidableEq V'] {s₁ t₁ : β → α' → V'} {c₁ : β → V' → ℕ}
    (hs : Computable₂ s₁) (ht : Computable₂ t₁) (hc : Computable₂ c₁) :
    Computable fun x : β × (List (α' × V' × ℕ) × α') =>
      chooseOwner (s₁ x.1) (t₁ x.1) (c₁ x.1) (decodePRLoad x.2.1) x.2.2 := by
  have hse : Computable fun x : β × (List (α' × V' × ℕ) × α') => s₁ x.1 x.2.2 :=
    hs.comp Computable.fst (Computable.snd.comp Computable.snd)
  have hte : Computable fun x : β × (List (α' × V' × ℕ) × α') => t₁ x.1 x.2.2 :=
    ht.comp Computable.fst (Computable.snd.comp Computable.snd)
  have hH : Computable fun x : β × (List (α' × V' × ℕ) × α') => x.2.1 :=
    Computable.fst.comp Computable.snd
  have hls : Computable fun x : β × (List (α' × V' × ℕ) × α') =>
      decodePRLoad x.2.1 (s₁ x.1 x.2.2) :=
    decodePRLoad_primrec.to_comp.comp hH hse
  have hlt : Computable fun x : β × (List (α' × V' × ℕ) × α') =>
      decodePRLoad x.2.1 (t₁ x.1 x.2.2) :=
    decodePRLoad_primrec.to_comp.comp hH hte
  have hcs : Computable fun x : β × (List (α' × V' × ℕ) × α') => c₁ x.1 (s₁ x.1 x.2.2) :=
    hc.comp Computable.fst hse
  have hct : Computable fun x : β × (List (α' × V' × ℕ) × α') => c₁ x.1 (t₁ x.1 x.2.2) :=
    hc.comp Computable.fst hte
  have hcmp : Computable fun x : β × (List (α' × V' × ℕ) × α') =>
      decide (decodePRLoad x.2.1 (s₁ x.1 x.2.2) * c₁ x.1 (t₁ x.1 x.2.2) ≤
        decodePRLoad x.2.1 (t₁ x.1 x.2.2) * c₁ x.1 (s₁ x.1 x.2.2)) :=
    Primrec.nat_le.decide.to_comp.comp (Primrec.nat_mul.to_comp.comp hls hct)
      (Primrec.nat_mul.to_comp.comp hlt hcs)
  have hcond := Computable.cond hcmp hse hte
  refine hcond.of_eq fun x => ?_
  simp only [chooseOwner, Bool.cond_decide]

/-- The history step is computable in the parameter, the history and the arriving edge. -/
theorem decodePR_step_computable {β α' V' : Type} [Primcodable β] [Primcodable α']
    [Primcodable V'] [DecidableEq V'] {s₁ t₁ : β → α' → V'} {c₁ : β → V' → ℕ}
    (hs : Computable₂ s₁) (ht : Computable₂ t₁) (hc : Computable₂ c₁) :
    Computable fun x : β × (List (α' × V' × ℕ) × α') =>
      decodePRStep (s₁ x.1) (t₁ x.1) (c₁ x.1) x.2.1 x.2.2 := by
  have ho := decodePR_choose_computable hs ht hc
  have hH : Computable fun x : β × (List (α' × V' × ℕ) × α') => x.2.1 :=
    Computable.fst.comp Computable.snd
  have he : Computable fun x : β × (List (α' × V' × ℕ) × α') => x.2.2 :=
    Computable.snd.comp Computable.snd
  have hr : Computable fun x : β × (List (α' × V' × ℕ) × α') =>
      decodePRLoad x.2.1 (chooseOwner (s₁ x.1) (t₁ x.1) (c₁ x.1) (decodePRLoad x.2.1) x.2.2) :=
    decodePRLoad_primrec.to_comp.comp hH ho
  have hcat : Computable fun x : β × (List (α' × V' × ℕ) × α') =>
      x.2.1 ++ [(x.2.2, chooseOwner (s₁ x.1) (t₁ x.1) (c₁ x.1) (decodePRLoad x.2.1) x.2.2,
        decodePRLoad x.2.1 (chooseOwner (s₁ x.1) (t₁ x.1) (c₁ x.1) (decodePRLoad x.2.1) x.2.2))] :=
    Primrec.list_concat.to_comp.comp hH (Computable.pair he (Computable.pair ho hr))
  exact hcat.of_eq fun x => rfl

/-- One stage of the simulated arrival process is computable. -/
theorem decodePR_runStep_computable {β α' V' : Type} [Primcodable β] [Primcodable α']
    [Primcodable V'] [DecidableEq α'] [DecidableEq V'] {s₁ t₁ : β → α' → V'}
    {c₁ : β → V' → ℕ} {en' : β → ℕ → Option α'} (hs : Computable₂ s₁) (ht : Computable₂ t₁)
    (hc : Computable₂ c₁) (hen : Computable₂ en') :
    Computable₂ fun (q : β) (yIH : ℕ × (List α' × List (α' × V' × ℕ))) =>
      decodePRRunStep (s₁ q) (t₁ q) (c₁ q) (en' q yIH.1) yIH.2 := by
  have hA : Computable fun x : β × (ℕ × (List α' × List (α' × V' × ℕ))) => en' x.1 x.2.1 :=
    hen.comp Computable.fst (Computable.fst.comp Computable.snd)
  have hB : Computable fun x : β × (ℕ × (List α' × List (α' × V' × ℕ))) => x.2.2 :=
    Computable.snd.comp Computable.snd
  have hst : Computable fun x : (β × (ℕ × (List α' × List (α' × V' × ℕ)))) × α' =>
      decodePRStep (s₁ x.1.1) (t₁ x.1.1) (c₁ x.1.1) x.1.2.2.2 x.2 :=
    (decodePR_step_computable hs ht hc).comp (Computable.pair (Computable.fst.comp Computable.fst)
      (Computable.pair (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp
        Computable.fst))) Computable.snd))
  have hl : Computable fun x : (β × (ℕ × (List α' × List (α' × V' × ℕ)))) × α' => x.1.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))
  have hmem : Computable fun x : (β × (ℕ × (List α' × List (α' × V' × ℕ)))) × α' =>
      decide (x.2 ∈ x.1.2.2.1) :=
    Kolmogorov.listMemDecide_primrec.to_comp.comp Computable.snd hl
  have hnew : Computable fun x : (β × (ℕ × (List α' × List (α' × V' × ℕ)))) × α' =>
      (x.1.2.2.1 ++ [x.2], decodePRStep (s₁ x.1.1) (t₁ x.1.1) (c₁ x.1.1) x.1.2.2.2 x.2) :=
    Computable.pair (Primrec.list_concat.to_comp.comp hl Computable.snd) hst
  have hold : Computable fun x : (β × (ℕ × (List α' × List (α' × V' × ℕ)))) × α' => x.1.2.2 :=
    Computable.snd.comp (Computable.snd.comp Computable.fst)
  have hg : Computable₂ fun (x : β × (ℕ × (List α' × List (α' × V' × ℕ)))) (e : α') =>
      bif decide (e ∈ x.2.2.1) then x.2.2
        else (x.2.2.1 ++ [e], decodePRStep (s₁ x.1) (t₁ x.1) (c₁ x.1) x.2.2.2 e) :=
    Computable.cond hmem hold hnew
  have hcase := Computable.option_casesOn hA hB hg
  refine hcase.of_eq fun x => ?_
  cases h : en' x.1 x.2.1 with
  | none => simp only [decodePRRunStep, h]
  | some e => simp only [decodePRRunStep, h, Bool.cond_decide]

/-- The arrival list together with its history is computable in the parameter and the stage. -/
theorem decodePR_hist_computable {β α' V' : Type} [Primcodable β] [Primcodable α']
    [Primcodable V'] [DecidableEq α'] [DecidableEq V'] {s₁ t₁ : β → α' → V'}
    {c₁ : β → V' → ℕ} {en' : β → ℕ → Option α'} (hs : Computable₂ s₁) (ht : Computable₂ t₁)
    (hc : Computable₂ c₁) (hen : Computable₂ en') :
    Computable fun x : β × ℕ =>
      decodePRHist (s₁ x.1) (t₁ x.1) (c₁ x.1) (arrivals (en' x.1) x.2) := by
  have hrs := decodePR_runStep_computable hs ht hc hen
  have hrs' : Computable₂ fun (x : β × ℕ) (yIH : ℕ × (List α' × List (α' × V' × ℕ))) =>
      decodePRRunStep (s₁ x.1) (t₁ x.1) (c₁ x.1) (en' x.1 yIH.1) yIH.2 :=
    hrs.comp (Computable.fst.comp Computable.fst) Computable.snd
  have hrun := Computable.nat_rec (f := fun x : β × ℕ => x.2)
    (g := fun _ => (([], []) : List α' × List (α' × V' × ℕ))) Computable.snd
    (Computable.const _) hrs'
  have h2 := Computable.snd.comp hrun
  refine h2.of_eq fun x => ?_
  exact congrArg Prod.snd (decodePR_rec_eq (s₁ x.1) (t₁ x.1) (c₁ x.1) (en' x.1) x.2)

/-- The owned hit is computable in the parameter, the query `(v, i)` and the stage. -/
theorem decodePR_hit_computable {β α' V' : Type} [Primcodable β] [Primcodable α']
    [Primcodable V'] [DecidableEq α'] [DecidableEq V'] {s₁ t₁ : β → α' → V'}
    {c₁ : β → V' → ℕ} {en' : β → ℕ → Option α'} (hs : Computable₂ s₁) (ht : Computable₂ t₁)
    (hc : Computable₂ c₁) (hen : Computable₂ en') :
    Computable fun x : (β × V' × ℕ) × ℕ =>
      ownedHit (s₁ x.1.1) (t₁ x.1.1) (c₁ x.1.1) (en' x.1.1) x.1.2.1 x.1.2.2 x.2 := by
  have hp1 : Computable fun x : (β × V' × ℕ) × ℕ => (x.1.1, x.2) :=
    Computable.pair (Computable.fst.comp Computable.fst) Computable.snd
  have hH0 := (decodePR_hist_computable hs ht hc hen).comp hp1
  have hH : Computable fun x : (β × V' × ℕ) × ℕ =>
      decodePRHist (s₁ x.1.1) (t₁ x.1.1) (c₁ x.1.1) (arrivals (en' x.1.1) x.2) := hH0
  have h1 : Primrec fun p : ((V' × ℕ) × List (α' × V' × ℕ)) × (α' × V' × ℕ) =>
      decide (p.2.2.1 = p.1.1.1) :=
    (Primrec.eq (α := V')).decide.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have h2 : Primrec fun p : ((V' × ℕ) × List (α' × V' × ℕ)) × (α' × V' × ℕ) =>
      decide (p.2.2.2 = p.1.1.2) :=
    (Primrec.eq (α := ℕ)).decide.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have hp : Primrec₂ fun (a : (V' × ℕ) × List (α' × V' × ℕ)) (t : α' × V' × ℕ) =>
      decide (t.2.1 = a.1.1 ∧ t.2.2 = a.1.2) :=
    (Primrec.and.comp h1 h2).of_eq fun p => by simp only [Bool.decide_and]
  have hf : Primrec fun a : (V' × ℕ) × List (α' × V' × ℕ) =>
      (a.2.find? fun t => decide (t.2.1 = a.1.1 ∧ t.2.2 = a.1.2)).map Prod.fst :=
    Primrec.option_map (list_find?_primrec Primrec.snd hp) (Primrec.fst.comp Primrec.snd).to₂
  have hc' := hf.to_comp.comp (Computable.pair (Computable.snd.comp Computable.fst) hH)
  refine hc'.of_eq fun x => ?_
  rw [decodePR_ownedHit_eq]

/-- **The decoder is partial recursive (blueprint G03, computability).**  If the endpoint maps,
the capacities and the enumeration depend computably on a parameter `p : β`, the partial decoder
`(p, v, i) ↦ decodeOwned … v i` is partial recursive.  In the application `en` dovetails the plain
machine on programs of length `≤ K` and keeps the residual edges; that instance is H04's.  The
endpoint maps there come from the total witnesses: take `p` to contain the finite output table of
the shape (`tableOut`, `ShapeParams.AgreeOn`), so that they are total computable in `p`.

Proof: the function-valued state of `orient` is simulated by the history list of
`(edge, owner, rank)` triples (`decodePRHist`, `decodePR_hist_spec`), which turns `ownedHit` into a
`find?` over the history (`decodePR_ownedHit_eq`); arrivals and history are computed together by
`Computable.nat_rec` (`decodePR_hist_computable`), and `Nat.rfind`/`Part.bind` preserve
partial recursiveness (`Partrec.rfind`, `Partrec.bind`). -/
theorem decodeOwned_partrec {β α' V' : Type} [Primcodable β] [Primcodable α'] [Primcodable V']
    [DecidableEq α'] [DecidableEq V'] (src' tgt' : β → α' → V') (d' : β → V' → ℕ)
    (en : β → ℕ → Option α') (hsrc : Computable₂ src') (htgt : Computable₂ tgt')
    (hd : Computable₂ d') (hen : Computable₂ en) :
    Partrec fun q : β × V' × ℕ =>
      decodeOwned (src' q.1) (tgt' q.1) (d' q.1) (en q.1) q.2.1 q.2.2 := by
  have hhit := decodePR_hit_computable hsrc htgt hd hen
  have hsome : Computable fun x : (β × V' × ℕ) × ℕ =>
      (ownedHit (src' x.1.1) (tgt' x.1.1) (d' x.1.1) (en x.1.1) x.1.2.1 x.1.2.2 x.2).isSome :=
    Primrec.option_isSome.to_comp.comp hhit
  have hrf : Partrec₂ fun (q : β × V' × ℕ) (s : ℕ) =>
      Part.some (ownedHit (src' q.1) (tgt' q.1) (d' q.1) (en q.1) q.2.1 q.2.2 s).isSome :=
    hsome.partrec
  have hbind : Partrec₂ fun (q : β × V' × ℕ) (s : ℕ) =>
      Part.ofOption (ownedHit (src' q.1) (tgt' q.1) (d' q.1) (en q.1) q.2.1 q.2.2 s) :=
    Computable.ofOption hhit
  have h := Partrec.bind (Partrec.rfind hrf) hbind
  exact h.of_eq fun q => rfl

end Orientation

end Kolmogorov.StrongMerging.Upper
