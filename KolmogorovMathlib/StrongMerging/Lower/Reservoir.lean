import KolmogorovMathlib.StrongMerging.Lower.Reservoir.Choice

/-!
# The moving-sphere reservoir game: availability, invariants, counting and stabilization

Blueprint nodes L14 and L16–L21 of `sublinear-merging.tex` (paper: "A finite game producing a
dense reservoir", lines ~1363–1506; blueprint: "An exact finite combinatorial game with an
effective event stream", lines ~4604–4806).  The executable game is defined in
`KolmogorovMathlib.StrongMerging.Lower.ReservoirGame`; this module proves its properties for an
abstract cube.

The hypotheses of the generic game are collected in `GameHyp`:

* geometry, as hypotheses: the centers are a duplicate-free nonempty list (the cube), every sphere
  around a center has `N` points, and every point lies in at most `N` spheres (sphere incidence,
  node L06);
* the heavy-cell bound of node L09, as a hypothesis (`GameHyp.heavy_bound`), with an arbitrary
  real constant `θ ≥ 0`; in the instance `θ = 2^δ (V(M, h - 1) 2^(-ℓ) + β^h)`;
* the four game inequalities of the paper, in integer form where they are integer statements
  (`density`, `charge`, `arrivals`) and in the paper's real form for `heavy`; the equivalences
  with the paper's displayed real forms are `density_iff_div`, `heavy_iff`, `charge_iff_zpow`
  and `arrivals_iff_div`.

The effectivity of the stream and of the transitions (for points coded by naturals) is in
`KolmogorovMathlib.StrongMerging.Lower.ReservoirComputable`, and the transport of the game along
an embedding of point types (binary words to their natural-number codes) in
`KolmogorovMathlib.StrongMerging.Lower.ReservoirTransport`; both are imported here.

The event history enters through `ValidHistory`, the count/certificate invariants that the
effective stream of L14 satisfies at every stage (`reservoirEventEnumeration`).

Main statements: `reservoirEventEnumeration` (L14), `chooseReservoir_spec` (L16),
`reservoirTransition_spec` (L17), `reservoirInvariants` (L18), `deletionChargeBound` (L19),
`reservoirChoiceCount` (L20) and `reservoirStabilizes` (L21).

The earlier parts of the development are in
`KolmogorovMathlib.StrongMerging.Lower.Reservoir.Stream`,
`KolmogorovMathlib.StrongMerging.Lower.Reservoir.Choice`, imported here.
-/

namespace Kolmogorov.StrongMerging.Lower

open Finset

variable {α : Type*} [DecidableEq α]

/-! ### L18: invariants -/

/-- Bookkeeping invariants of the state `st` reached by processing the history `evs` (part of
node L18): known tables and stored sets are exactly those of the processed events; marks come
from processed point and set events and contain all processed point outputs; every stored set
that is a cell of a known table is marked as a whole, and marked cells are stored cells of known
tables contained in the marks; the output tape starts with the current center and has
`1 + #ordinary resets + #tables` entries. -/
structure InvBook (G : ResGame α) (evs : List (ResEvent α)) (st : ReservoirState α) : Prop where
  /-- The known tables are the processed table events. -/
  tables_mem : ∀ P, P ∈ st.tables ↔ ResEvent.table P ∈ evs
  /-- One known table per processed table event. -/
  tables_length : st.tables.length = tableCount evs
  /-- The stored sets are the processed set events. -/
  stored_mem : ∀ Q i, (Q, i) ∈ st.stored ↔ ResEvent.set Q i ∈ evs
  /-- Every mark comes from a processed point or set event. -/
  marks_sub : ∀ u ∈ st.marks, ResEvent.point u ∈ evs ∨ ∃ Q i, ResEvent.set Q i ∈ evs ∧ u ∈ Q
  /-- Every processed point output is marked. -/
  point_marked : ∀ u, ResEvent.point u ∈ evs → u ∈ st.marks
  /-- Every stored set that is a cell of a known table is marked as a whole. -/
  cell_marked : ∀ Q i P, ResEvent.set Q i ∈ evs → ResEvent.table P ∈ evs → Q ∈ P →
    Q ∈ st.markedCells
  /-- Marked cells are stored cells of known tables. -/
  markedCells_known : ∀ Q ∈ st.markedCells, (∃ i, ResEvent.set Q i ∈ evs) ∧ ∃ P ∈ st.tables, Q ∈ P
  /-- The points of marked cells are marked. -/
  markedCells_sub : ∀ Q ∈ st.markedCells, Q ⊆ st.marks
  /-- The output tape starts with the current center. -/
  emitted_head : st.emitted.head? = some st.center
  /-- The tape has `1 + #ordinary resets + #tables` entries. -/
  emitted_length : st.emitted.length = 1 + st.ordinaryResets + tableCount evs

/-- Invariants of the live reservoir (part of node L18): it lies in the current sphere, avoids
all permanent marks, lies in the epoch's initial reservoir, and meets every large cell of a known
table lightly. -/
structure InvLive (G : ResGame α) (st : ReservoirState α) : Prop where
  /-- The reservoir lies in the current sphere. -/
  live_sphere : st.live ⊆ G.sphere st.center
  /-- The reservoir avoids all permanent marks. -/
  live_disjoint : Disjoint st.live st.marks
  /-- The reservoir lies in the epoch's initial reservoir. -/
  live_epoch : st.live ⊆ st.epochLive
  /-- Every large cell of a known table meets the reservoir lightly. -/
  light : ∀ P ∈ st.tables, ∀ Q ∈ P, 2 ^ G.ell ≤ Q.card →
    2 ^ G.delta * (Q ∩ st.live).card ≤ Q.card

/-- Size invariants (part of node L18): the center is a cube point, the epoch started with
`32 |W₀| ≥ 31 N`, and after every completed transition `8 |W| ≥ 7 N`. -/
structure InvSize (G : ResGame α) (st : ReservoirState α) : Prop where
  /-- The center is a cube point. -/
  center_mem : st.center ∈ G.centers
  /-- The epoch started with `32 |W₀| ≥ 31 N`. -/
  epoch_big : 31 * G.N ≤ 32 * st.epochLive.card
  /-- After every completed transition `8 |W| ≥ 7 N`. -/
  live_big : 7 * G.N ≤ 8 * st.live.card

/-- The charge ledger invariants (part of node L18, input of L19/L20): the potential
`3 N · #ordinary resets + 32 |W₀| ≤ 32 (point charge + cell charge) + 32 |W|`, the point charge
is at most the number of point events, and `2^δ` times the cell charge is at most the set
mass. -/
structure InvCharge (G : ResGame α) (evs : List (ResEvent α)) (st : ReservoirState α) :
    Prop where
  /-- The potential inequality of the charge ledger. -/
  potential : 3 * (G.N * st.ordinaryResets) + 32 * st.epochLive.card ≤
    32 * (st.pointCharge + st.cellCharge) + 32 * st.live.card
  /-- The point charge is at most the number of point events. -/
  point_charge : st.pointCharge ≤ pointCount evs
  /-- `2^δ` times the cell charge is at most the set mass. -/
  cell_charge : 2 ^ G.delta * st.cellCharge ≤ setMass evs

/-- **The invariants of node L18**, for the state `st` reached by processing `evs`. -/
structure ReservoirInv (G : ResGame α) (evs : List (ResEvent α)) (st : ReservoirState α) :
    Prop where
  /-- Bookkeeping invariants. -/
  book : InvBook G evs st
  /-- Live-set invariants. -/
  live : InvLive G st
  /-- Size invariants. -/
  size : InvSize G st
  /-- Charge-ledger invariants. -/
  charge : InvCharge G evs st

omit [DecidableEq α] in
/-- **Marked-set bound.**  The marks have at most `#point events + set mass` elements.
Proof: by `marks_sub`, `marks ⊆ {u | point u ∈ evs} ∪ ⋃_{set Q i ∈ evs} Q`; bound the first part
by `pointCount` (`List.toFinset_card_le` on the `filterMap`ped points) and the second by
`setMass` (`card_biUnion_le`, then compare the sum over distinct events with the sum with
multiplicity).  Reference: paper ("The globally marked union has cardinality at most");
L16, L18. -/
theorem card_marks_le {G : ResGame α} {evs : List (ResEvent α)} {st : ReservoirState α}
    (h : InvBook G evs st) : st.marks.card ≤ pointCount evs + setMass evs := by
  classical
  have key : ∀ (l : List (ResEvent α)) (M : Finset α),
      (∀ u ∈ M, ResEvent.point u ∈ l ∨ ∃ Q i, ResEvent.set Q i ∈ l ∧ u ∈ Q) →
      M.card ≤ pointCount l + setMass l := by
    intro l
    induction l with
    | nil =>
      intro M hM
      have hM0 : M = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro u hu
        rcases hM u hu with h | ⟨Q, i, h, -⟩ <;> simp at h
      simp [hM0]
    | cons e l ih =>
      intro M hM
      cases e with
      | point v =>
        have h1 : (M.erase v).card ≤ pointCount l + setMass l := by
          apply ih
          intro u hu
          rw [Finset.mem_erase] at hu
          rcases hM u hu.2 with h | ⟨Q, i, h, hQ⟩
          · left
            rcases List.mem_cons.mp h with h' | h'
            · exact absurd (ResEvent.point.inj h') hu.1
            · exact h'
          · right
            rcases List.mem_cons.mp h with h' | h'
            · cases h'
            · exact ⟨Q, i, h', hQ⟩
        have h2 := Finset.pred_card_le_card_erase (s := M) (a := v)
        have h3 : pointCount (ResEvent.point v :: l) = pointCount l + 1 := by
          simp [pointCount, List.countP_cons, ResEvent.isPoint]
        have h4 : setMass (ResEvent.point v :: l) = setMass l := by
          simp [setMass, ResEvent.setCard]
        rw [h3, h4]
        omega
      | set Q j =>
        have h1 : (M \ Q).card ≤ pointCount l + setMass l := by
          apply ih
          intro u hu
          rw [Finset.mem_sdiff] at hu
          rcases hM u hu.1 with h | ⟨Q', i, h, hQ'⟩
          · left
            rcases List.mem_cons.mp h with h' | h'
            · cases h'
            · exact h'
          · right
            rcases List.mem_cons.mp h with h' | h'
            · obtain ⟨rfl, -⟩ := ResEvent.set.inj h'
              exact absurd hQ' hu.2
            · exact ⟨Q', i, h', hQ'⟩
        have h2 := Finset.card_le_card_sdiff_add_card (s := M) (t := Q)
        have h3 : pointCount (ResEvent.set Q j :: l) = pointCount l := by
          simp [pointCount, ResEvent.isPoint]
        have h4 : setMass (ResEvent.set Q j :: l) = Q.card + setMass l := by
          simp [setMass, ResEvent.setCard]
        rw [h3, h4]
        omega
      | table P =>
        have h1 : M.card ≤ pointCount l + setMass l := by
          apply ih
          intro u hu
          rcases hM u hu with h | ⟨Q, i, h, hQ⟩
          · left
            rcases List.mem_cons.mp h with h' | h'
            · cases h'
            · exact h'
          · right
            rcases List.mem_cons.mp h with h' | h'
            · cases h'
            · exact ⟨Q, i, h', hQ⟩
        have h3 : pointCount (ResEvent.table P :: l) = pointCount l := by
          simp [pointCount, ResEvent.isPoint]
        have h4 : setMass (ResEvent.table P :: l) = setMass l := by
          simp [setMass, ResEvent.setCard]
        rw [h3, h4]
        exact h1
  exact key evs st.marks h.marks_sub

/-- The density inequality bounds the marks of every reachable state by `|cube| / 256`. -/
theorem marks_bound {G : ResGame α} {K τ S : ℕ} {θ : ℝ} (hG : GameHyp G K τ S θ)
    {evs : List (ResEvent α)} {st : ReservoirState α} (hb : InvBook G evs st)
    (hv : ValidHistory G K τ S evs) : 256 * st.marks.card ≤ G.centers.length :=
  calc 256 * st.marks.card ≤ 256 * (pointCount evs + setMass evs) :=
        Nat.mul_le_mul_left _ (card_marks_le hb)
    _ ≤ 256 * (2 ^ K + (K + τ + 1) * 2 ^ (K + τ)) :=
        Nat.mul_le_mul_left _ (Nat.add_le_add hv.point_count.le (setMass_le hv))
    _ ≤ G.centers.length := hG.density

/-- **A choice re-establishes the size invariants**, under the availability hypotheses of
`chooseReservoir_spec`. -/
theorem reselect_invSize {G : ResGame α} {K τ S : ℕ} {θ : ℝ} (hG : GameHyp G K τ S θ)
    (st : ReservoirState α) (hmarks : 256 * st.marks.card ≤ G.centers.length)
    (htab : st.tables.length ≤ 2 ^ (S + 1))
    (hvalid : ∀ P ∈ st.tables, IsCellPartition G.cube P) : InvSize G (st.reselect G) := by
  obtain ⟨hmem, -, -, hbig, -⟩ := chooseReservoir_spec hG st.marks st.tables hmarks htab hvalid
  refine ⟨hmem, hbig, ?_⟩
  change 7 * G.N ≤ 8 * (chooseReservoir G st.marks st.tables).2.card
  omega

/-- **A choice establishes the live-set invariants** (for any marks and tables).
Proof: `reselect` keeps `marks` and `tables`, and sets `live = epochLive` to the chosen
reservoir; apply `chooseReservoir_subset_sphere`, `chooseReservoir_disjoint_marks` and
`chooseReservoir_light`. -/
theorem reselect_invLive (G : ResGame α) (st : ReservoirState α) : InvLive G (st.reselect G) :=
  ⟨chooseReservoir_subset_sphere G st.marks st.tables,
    chooseReservoir_disjoint_marks G st.marks st.tables, subset_rfl,
    chooseReservoir_light G st.marks st.tables⟩

/-- Bookkeeping invariants of the initial state.
Proof: the history is empty, all lists and sets of the empty board are empty, and the initial
choice writes one center to the tape. -/
theorem invBook_init (G : ResGame α) : InvBook G [] (initState G) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [initState, emptyState, ReservoirState.reselect, tableCount]

/-- Charge invariants of the initial state.
Proof: all counters are `0` and `epochLive = live` after the initial choice. -/
theorem invCharge_init (G : ResGame α) : InvCharge G [] (initState G) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [initState, emptyState, ReservoirState.reselect, pointCount, setMass]

/-- The invariants hold for the initial state. -/
theorem inv_init {G : ResGame α} {K τ S : ℕ} {θ : ℝ} (hG : GameHyp G K τ S θ) :
    ReservoirInv G [] (initState G) :=
  ⟨invBook_init G, reselect_invLive G _,
    reselect_invSize hG _ (by simp [emptyState]) (by simp [emptyState])
      (by simp [emptyState]), invCharge_init G⟩

/-- Bookkeeping after a point event.
Proof: unfold `pointStep`/`ordinaryCheck`; `marks` gains `u`, the other board fields are
unchanged, a reset conses the new center and increments the reset counter; `tableCount` and the
membership statements of `evs ++ [point u]` are computed with `List.mem_append`,
`List.countP_append`. -/
theorem invBook_point {G : ResGame α} {evs : List (ResEvent α)} {st : ReservoirState α}
    (hinv : ReservoirInv G evs st) (u : α) :
    InvBook G (evs ++ [.point u]) (st.pointStep G u) := by
  have hb := hinv.book
  have hoc : ∀ st' : ReservoirState α, InvBook G (evs ++ [.point u]) st' →
      InvBook G (evs ++ [.point u]) (st'.ordinaryCheck G) := by
    intro st' h
    unfold ReservoirState.ordinaryCheck
    split_ifs
    · refine ⟨h.tables_mem, h.tables_length, h.stored_mem, h.marks_sub, h.point_marked,
        h.cell_marked, h.markedCells_known, h.markedCells_sub, rfl, ?_⟩
      change st'.emitted.length + 1 =
        1 + (st'.ordinaryResets + 1) + tableCount (evs ++ [.point u])
      rw [h.emitted_length]
      omega
    · exact h
  have htc : tableCount (evs ++ [ResEvent.point u]) = tableCount evs := by
    simp [tableCount, List.countP_append, ResEvent.isTable]
  unfold ReservoirState.pointStep
  apply hoc
  refine ⟨fun P => ?_, ?_, fun Q i => ?_, fun v hv => ?_, fun v hv => ?_,
    fun Q i P hQ hP hQP => ?_, fun Q hQ => ?_, fun Q hQ => ?_, hb.emitted_head, ?_⟩
  · simpa using hb.tables_mem P
  · rw [htc]
    exact hb.tables_length
  · simpa using hb.stored_mem Q i
  · change v ∈ insert u st.marks at hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact Or.inl (by simp)
    · rcases hb.marks_sub v hv with h | ⟨Q, i, hQ, hvQ⟩
      · exact Or.inl (List.mem_append_left _ h)
      · exact Or.inr ⟨Q, i, List.mem_append_left _ hQ, hvQ⟩
  · change v ∈ insert u st.marks
    simp only [List.mem_append, List.mem_singleton, ResEvent.point.injEq] at hv
    rcases hv with hv | rfl
    · exact Finset.mem_insert.mpr (Or.inr (hb.point_marked v hv))
    · exact Finset.mem_insert.mpr (Or.inl rfl)
  · simp only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at hQ hP
    exact hb.cell_marked Q i P hQ hP hQP
  · obtain ⟨⟨i, hi⟩, hP⟩ := hb.markedCells_known Q hQ
    exact ⟨⟨i, List.mem_append_left _ hi⟩, hP⟩
  · change Q ⊆ insert u st.marks
    exact (hb.markedCells_sub Q hQ).trans (Finset.subset_insert _ _)
  · change st.emitted.length = 1 + st.ordinaryResets + tableCount (evs ++ [.point u])
    rw [htc]
    exact hb.emitted_length

/-- Bookkeeping after a set event.
Proof: unfold `setStep`; `stored` gains `(Q, i)`; if `Q` is a cell of a known table and not yet
marked, it becomes a marked cell and `Q ⊆ marks`; if it is already marked, `cell_marked` and
`markedCells_sub` are inherited; reset bookkeeping as for points. -/
theorem invBook_set {G : ResGame α} {evs : List (ResEvent α)} {st : ReservoirState α}
    (hinv : ReservoirInv G evs st) (Q : Finset α) (i : ℕ) :
    InvBook G (evs ++ [.set Q i]) (st.setStep G Q i) := by
  have hb := hinv.book
  have hoc : ∀ st' : ReservoirState α, InvBook G (evs ++ [.set Q i]) st' →
      InvBook G (evs ++ [.set Q i]) (st'.ordinaryCheck G) := by
    intro st' h
    unfold ReservoirState.ordinaryCheck
    split_ifs
    · refine ⟨h.tables_mem, h.tables_length, h.stored_mem, h.marks_sub, h.point_marked,
        h.cell_marked, h.markedCells_known, h.markedCells_sub, rfl, ?_⟩
      change st'.emitted.length + 1 =
        1 + (st'.ordinaryResets + 1) + tableCount (evs ++ [.set Q i])
      rw [h.emitted_length]
      omega
    · exact h
  have htc : tableCount (evs ++ [ResEvent.set Q i]) = tableCount evs := by
    simp [tableCount, List.countP_append, ResEvent.isTable]
  have hstored : ∀ Q' i', (Q', i') ∈ (Q, i) :: st.stored ↔
      ResEvent.set Q' i' ∈ evs ++ [ResEvent.set Q i] := by
    intro Q' i'
    rw [List.mem_cons, hb.stored_mem Q' i']
    simp only [Prod.mk.injEq, List.mem_append, List.mem_singleton, ResEvent.set.injEq]
    tauto
  have hset : ∀ Q' i', ResEvent.set Q' i' ∈ evs ++ [ResEvent.set Q i] →
      ResEvent.set Q' i' ∈ evs ∨ (Q' = Q ∧ i' = i) := by
    intro Q' i' h
    simpa using h
  have htab : ∀ P, ResEvent.table P ∈ evs ++ [ResEvent.set Q i] ↔ ResEvent.table P ∈ evs := by
    intro P
    simp
  have hpt : ∀ v, ResEvent.point v ∈ evs ++ [ResEvent.set Q i] ↔ ResEvent.point v ∈ evs := by
    intro v
    simp
  unfold ReservoirState.setStep
  split_ifs with hcond
  · apply hoc
    refine ⟨fun P => ?_, ?_, hstored, fun v hv => ?_, fun v hv => ?_,
      fun Q' i' P hQ hP hQP => ?_, fun Q' hQ => ?_, fun Q' hQ => ?_, hb.emitted_head, ?_⟩
    · rw [htab]
      exact hb.tables_mem P
    · rw [htc]
      exact hb.tables_length
    · change v ∈ st.marks ∪ Q at hv
      rcases Finset.mem_union.mp hv with hv | hv
      · rcases hb.marks_sub v hv with h | ⟨Q', i', hQ', hvQ'⟩
        · exact Or.inl (List.mem_append_left _ h)
        · exact Or.inr ⟨Q', i', List.mem_append_left _ hQ', hvQ'⟩
      · exact Or.inr ⟨Q, i, by simp, hv⟩
    · change v ∈ st.marks ∪ Q
      rw [hpt] at hv
      exact Finset.mem_union_left _ (hb.point_marked v hv)
    · change Q' ∈ Q :: st.markedCells
      rw [htab] at hP
      rcases hset Q' i' hQ with hQ | ⟨rfl, rfl⟩
      · exact List.mem_cons.mpr (Or.inr (hb.cell_marked Q' i' P hQ hP hQP))
      · exact List.mem_cons.mpr (Or.inl rfl)
    · change Q' ∈ Q :: st.markedCells at hQ
      rcases List.mem_cons.mp hQ with rfl | hQ
      · exact ⟨⟨i, by simp⟩, hcond.1⟩
      · obtain ⟨⟨i', hi'⟩, hP⟩ := hb.markedCells_known Q' hQ
        exact ⟨⟨i', List.mem_append_left _ hi'⟩, hP⟩
    · change Q' ∈ Q :: st.markedCells at hQ
      change Q' ⊆ st.marks ∪ Q
      rcases List.mem_cons.mp hQ with rfl | hQ
      · exact Finset.subset_union_right
      · exact (hb.markedCells_sub Q' hQ).trans Finset.subset_union_left
    · change st.emitted.length = 1 + st.ordinaryResets + tableCount (evs ++ [.set Q i])
      rw [htc]
      exact hb.emitted_length
  · apply hoc
    refine ⟨fun P => ?_, ?_, hstored, fun v hv => ?_, fun v hv => ?_,
      fun Q' i' P hQ hP hQP => ?_, fun Q' hQ => ?_, fun Q' hQ => ?_, hb.emitted_head, ?_⟩
    · rw [htab]
      exact hb.tables_mem P
    · rw [htc]
      exact hb.tables_length
    · rcases hb.marks_sub v hv with h | ⟨Q', i', hQ', hvQ'⟩
      · exact Or.inl (List.mem_append_left _ h)
      · exact Or.inr ⟨Q', i', List.mem_append_left _ hQ', hvQ'⟩
    · rw [hpt] at hv
      exact hb.point_marked v hv
    · rw [htab] at hP
      rcases hset Q' i' hQ with hQ | ⟨rfl, rfl⟩
      · exact hb.cell_marked Q' i' P hQ hP hQP
      · by_contra hnot
        exact hcond ⟨⟨P, (hb.tables_mem P).mpr hP, hQP⟩, hnot⟩
    · obtain ⟨⟨i', hi'⟩, hP⟩ := hb.markedCells_known Q' hQ
      exact ⟨⟨i', List.mem_append_left _ hi'⟩, hP⟩
    · exact hb.markedCells_sub Q' hQ
    · change st.emitted.length = 1 + st.ordinaryResets + tableCount (evs ++ [.set Q i])
      rw [htc]
      exact hb.emitted_length

/-- Bookkeeping after a table event.
Proof: unfold `tableStep`; the table is added; the activated cells (`activated`, the stored sets
that are cells of `P`) are marked as wholes, their points added to the marks (`mem_listUnion`);
for a stored `Q` and the new table `P` with `Q ∈ P`, `Q` is activated by `stored_mem`; the forced
choice conses one center and `tableCount` grows by one. -/
theorem invBook_table {G : ResGame α} {evs : List (ResEvent α)} {st : ReservoirState α}
    (hinv : ReservoirInv G evs st) (P : List (Finset α)) :
    InvBook G (evs ++ [.table P]) (st.tableStep G P) := by
  have hb := hinv.book
  have htc : tableCount (evs ++ [ResEvent.table P]) = tableCount evs + 1 := by
    simp [tableCount, List.countP_append, ResEvent.isTable]
  have hact : ∀ Q, Q ∈ st.activated P ↔ (∃ i, ResEvent.set Q i ∈ evs) ∧ Q ∈ P := by
    intro Q
    simp only [ReservoirState.activated, List.mem_filter, List.mem_map, decide_eq_true_eq]
    constructor
    · rintro ⟨⟨⟨Q', i⟩, hmem, rfl⟩, hQP⟩
      exact ⟨⟨i, (hb.stored_mem _ i).mp hmem⟩, hQP⟩
    · rintro ⟨⟨i, hi⟩, hQP⟩
      exact ⟨⟨(Q, i), (hb.stored_mem Q i).mpr hi, rfl⟩, hQP⟩
  unfold ReservoirState.tableStep
  refine ⟨fun P' => ?_, ?_, fun Q i => ?_, fun v hv => ?_, fun v hv => ?_,
    fun Q i P' hQ hP' hQP' => ?_, fun Q hQ => ?_, fun Q hQ => ?_, rfl, ?_⟩
  · change P' ∈ P :: st.tables ↔ _
    rw [List.mem_cons, hb.tables_mem P']
    simp only [List.mem_append, List.mem_singleton, ResEvent.table.injEq]
    tauto
  · change (P :: st.tables).length = _
    rw [htc, List.length_cons, hb.tables_length]
  · change (Q, i) ∈ st.stored ↔ _
    rw [hb.stored_mem]
    simp
  · change v ∈ st.marks ∪ listUnion (st.activated P) at hv
    rcases Finset.mem_union.mp hv with hv | hv
    · rcases hb.marks_sub v hv with h | ⟨Q', i', hQ', hvQ'⟩
      · exact Or.inl (List.mem_append_left _ h)
      · exact Or.inr ⟨Q', i', List.mem_append_left _ hQ', hvQ'⟩
    · obtain ⟨Q, hQ, hvQ⟩ := mem_listUnion.mp hv
      obtain ⟨⟨i, hi⟩, -⟩ := (hact Q).mp hQ
      exact Or.inr ⟨Q, i, List.mem_append_left _ hi, hvQ⟩
  · change v ∈ st.marks ∪ listUnion (st.activated P)
    simp only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at hv
    exact Finset.mem_union_left _ (hb.point_marked v hv)
  · change Q ∈ st.activated P ++ st.markedCells
    simp only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at hQ
    simp only [List.mem_append, List.mem_singleton, ResEvent.table.injEq] at hP'
    rcases hP' with hP' | rfl
    · exact List.mem_append.mpr (Or.inr (hb.cell_marked Q i P' hQ hP' hQP'))
    · exact List.mem_append.mpr (Or.inl ((hact Q).mpr ⟨⟨i, hQ⟩, hQP'⟩))
  · change Q ∈ st.activated P ++ st.markedCells at hQ
    change (∃ i, ResEvent.set Q i ∈ evs ++ [ResEvent.table P]) ∧ ∃ P' ∈ P :: st.tables, Q ∈ P'
    rcases List.mem_append.mp hQ with hQ | hQ
    · obtain ⟨⟨i, hi⟩, hQP⟩ := (hact Q).mp hQ
      exact ⟨⟨i, List.mem_append_left _ hi⟩, P, List.mem_cons.mpr (Or.inl rfl), hQP⟩
    · obtain ⟨⟨i, hi⟩, P', hP', hQP'⟩ := hb.markedCells_known Q hQ
      exact ⟨⟨i, List.mem_append_left _ hi⟩, P', List.mem_cons.mpr (Or.inr hP'), hQP'⟩
  · change Q ∈ st.activated P ++ st.markedCells at hQ
    change Q ⊆ st.marks ∪ listUnion (st.activated P)
    rcases List.mem_append.mp hQ with hQ | hQ
    · intro v hv
      exact Finset.mem_union_right _ (mem_listUnion.mpr ⟨Q, hQ, hv⟩)
    · exact (hb.markedCells_sub Q hQ).trans Finset.subset_union_left
  · change st.emitted.length + 1 = 1 + st.ordinaryResets + tableCount (evs ++ [.table P])
    rw [htc, hb.emitted_length]
    omega

/-- Live-set invariants after a point event.
Proof: without reset, `live.erase u ⊆ live` keeps sphere containment, the epoch containment and
lightness, and `u` is now marked; with reset use `reselect_invLive`. -/
theorem invLive_point {G : ResGame α} {evs : List (ResEvent α)} {st : ReservoirState α}
    (hinv : ReservoirInv G evs st) (u : α) : InvLive G (st.pointStep G u) := by
  have hl := hinv.live
  have hOC : ∀ s : ReservoirState α, InvLive G s → InvLive G (s.ordinaryCheck G) := by
    intro s hs
    unfold ReservoirState.ordinaryCheck
    split_ifs
    · have H := reselect_invLive G s
      exact ⟨H.1, H.2, H.3, H.4⟩
    · exact hs
  unfold ReservoirState.pointStep
  apply hOC
  refine ⟨(Finset.erase_subset u st.live).trans hl.live_sphere, ?_,
    (Finset.erase_subset u st.live).trans hl.live_epoch, ?_⟩
  · refine Finset.disjoint_left.mpr fun x hx hm => ?_
    rcases Finset.mem_insert.mp hm with rfl | hm'
    · exact Finset.notMem_erase x st.live hx
    · exact Finset.disjoint_left.mp hl.live_disjoint (Finset.mem_of_mem_erase hx) hm'
  · intro P hP Q hQ hℓ
    exact (Nat.mul_le_mul_left _ (Finset.card_le_card (Finset.inter_subset_inter
      (subset_refl _) (Finset.erase_subset u st.live)))).trans (hl.light P hP Q hQ hℓ)

/-- Live-set invariants after a set event.
Proof: as for `invLive_point`, with `live \ Q` and `marks ∪ Q` (or no change). -/
theorem invLive_set {G : ResGame α} {evs : List (ResEvent α)} {st : ReservoirState α}
    (hinv : ReservoirInv G evs st) (Q : Finset α) (i : ℕ) : InvLive G (st.setStep G Q i) := by
  have hl := hinv.live
  have hOC : ∀ s : ReservoirState α, InvLive G s → InvLive G (s.ordinaryCheck G) := by
    intro s hs
    unfold ReservoirState.ordinaryCheck
    split_ifs
    · have H := reselect_invLive G s
      exact ⟨H.1, H.2, H.3, H.4⟩
    · exact hs
  unfold ReservoirState.setStep
  split_ifs with hmark
  · apply hOC
    refine ⟨Finset.sdiff_subset.trans hl.live_sphere, ?_,
      Finset.sdiff_subset.trans hl.live_epoch, ?_⟩
    · refine Finset.disjoint_left.mpr fun x hx hm => ?_
      rw [Finset.mem_sdiff] at hx
      rcases Finset.mem_union.mp hm with hm' | hm'
      · exact Finset.disjoint_left.mp hl.live_disjoint hx.1 hm'
      · exact hx.2 hm'
    · intro P hP Q' hQ' hℓ
      exact (Nat.mul_le_mul_left _ (Finset.card_le_card (Finset.inter_subset_inter
        (subset_refl _) Finset.sdiff_subset))).trans (hl.light P hP Q' hQ' hℓ)
  · exact hOC _ ⟨hl.1, hl.2, hl.3, hl.4⟩

/-- Live-set invariants after a table event: the forced choice, `reselect_invLive`. -/
theorem invLive_table {G : ResGame α} (st : ReservoirState α) (P : List (Finset α)) :
    InvLive G (st.tableStep G P) := by
  exact reselect_invLive G _

/-- Size invariants after a point event.
Proof: without reset, the center and the epoch are unchanged and the failed test gives
`7 N ≤ 8 |W|`; with reset apply `reselect_invSize`, whose marks bound is `marks_bound` for the
new history (`hbook`, `hv`; `reselect` does not change the marks), with the tables unchanged. -/
theorem invSize_point {G : ResGame α} {K τ S : ℕ} {θ : ℝ} (hG : GameHyp G K τ S θ)
    {evs : List (ResEvent α)} {st : ReservoirState α} (hinv : ReservoirInv G evs st) (u : α)
    (hv : ValidHistory G K τ S (evs ++ [.point u]))
    (hbook : InvBook G (evs ++ [.point u]) (st.pointStep G u)) :
    InvSize G (st.pointStep G u) := by
  have hOC : ∀ s : ReservoirState α, (s.ordinaryCheck G).marks = s.marks ∧
      (s.ordinaryCheck G).tables = s.tables := by
    intro s
    unfold ReservoirState.ordinaryCheck
    split_ifs <;> exact ⟨rfl, rfl⟩
  have hOCsize : ∀ s : ReservoirState α, 256 * s.marks.card ≤ G.centers.length →
      s.tables.length ≤ 2 ^ (S + 1) → (∀ P ∈ s.tables, IsCellPartition G.cube P) →
      s.center ∈ G.centers → 31 * G.N ≤ 32 * s.epochLive.card →
      InvSize G (s.ordinaryCheck G) := by
    intro s h1 h2 h3 h4 h5
    unfold ReservoirState.ordinaryCheck
    split_ifs with hreset
    · have H := reselect_invSize hG s h1 h2 h3
      exact ⟨H.1, H.2, H.3⟩
    · exact ⟨h4, h5, not_lt.mp hreset⟩
  have hm := marks_bound hG hbook hv
  have ht : (st.pointStep G u).tables.length ≤ 2 ^ (S + 1) := by
    rw [hbook.tables_length]; exact hv.table_count.le
  have hval : ∀ P ∈ (st.pointStep G u).tables, IsCellPartition G.cube P :=
    fun P hP => hv.table_valid P ((hbook.tables_mem P).mp hP)
  unfold ReservoirState.pointStep at hm ht hval ⊢
  rw [(hOC _).1] at hm
  rw [(hOC _).2] at ht hval
  exact hOCsize _ hm ht hval hinv.size.center_mem hinv.size.epoch_big

/-- Size invariants after a set event.  Proof: as for `invSize_point`. -/
theorem invSize_set {G : ResGame α} {K τ S : ℕ} {θ : ℝ} (hG : GameHyp G K τ S θ)
    {evs : List (ResEvent α)} {st : ReservoirState α} (hinv : ReservoirInv G evs st)
    (Q : Finset α) (i : ℕ) (hv : ValidHistory G K τ S (evs ++ [.set Q i]))
    (hbook : InvBook G (evs ++ [.set Q i]) (st.setStep G Q i)) :
    InvSize G (st.setStep G Q i) := by
  have hOC : ∀ s : ReservoirState α, (s.ordinaryCheck G).marks = s.marks ∧
      (s.ordinaryCheck G).tables = s.tables := by
    intro s
    unfold ReservoirState.ordinaryCheck
    split_ifs <;> exact ⟨rfl, rfl⟩
  have hOCsize : ∀ s : ReservoirState α, 256 * s.marks.card ≤ G.centers.length →
      s.tables.length ≤ 2 ^ (S + 1) → (∀ P ∈ s.tables, IsCellPartition G.cube P) →
      s.center ∈ G.centers → 31 * G.N ≤ 32 * s.epochLive.card →
      InvSize G (s.ordinaryCheck G) := by
    intro s h1 h2 h3 h4 h5
    unfold ReservoirState.ordinaryCheck
    split_ifs with hreset
    · have H := reselect_invSize hG s h1 h2 h3
      exact ⟨H.1, H.2, H.3⟩
    · exact ⟨h4, h5, not_lt.mp hreset⟩
  have hm := marks_bound hG hbook hv
  have ht : (st.setStep G Q i).tables.length ≤ 2 ^ (S + 1) := by
    rw [hbook.tables_length]; exact hv.table_count.le
  have hval : ∀ P ∈ (st.setStep G Q i).tables, IsCellPartition G.cube P :=
    fun P hP => hv.table_valid P ((hbook.tables_mem P).mp hP)
  unfold ReservoirState.setStep at hm ht hval ⊢
  split_ifs at hm ht hval ⊢ with hmark
  · rw [(hOC _).1] at hm
    rw [(hOC _).2] at ht hval
    exact hOCsize _ hm ht hval hinv.size.center_mem hinv.size.epoch_big
  · rw [(hOC _).1] at hm
    rw [(hOC _).2] at ht hval
    exact hOCsize _ hm ht hval hinv.size.center_mem hinv.size.epoch_big

/-- Size invariants after a table event.
Proof: the forced choice; `reselect_invSize` with `marks_bound` for the new history, the table
count `< 2^(S+1)` (`tables_length`) and the validity of all known tables (`tables_mem`,
`ValidHistory.table_valid`). -/
theorem invSize_table {G : ResGame α} {K τ S : ℕ} {θ : ℝ} (hG : GameHyp G K τ S θ)
    {evs : List (ResEvent α)} {st : ReservoirState α} (P : List (Finset α))
    (hv : ValidHistory G K τ S (evs ++ [.table P]))
    (hbook : InvBook G (evs ++ [.table P]) (st.tableStep G P)) :
    InvSize G (st.tableStep G P) := by
  have hm := marks_bound hG hbook hv
  have ht : (st.tableStep G P).tables.length ≤ 2 ^ (S + 1) := by
    rw [hbook.tables_length]; exact hv.table_count.le
  have hval : ∀ P' ∈ (st.tableStep G P).tables, IsCellPartition G.cube P' :=
    fun P' hP' => hv.table_valid P' ((hbook.tables_mem P').mp hP')
  exact reselect_invSize hG _ hm ht hval

/-- Charge invariants after a point event.
Proof: the deletion `d = [u ∈ W]` is added to the point charge and removed from `|W|`, so the
potential is unchanged; at an ordinary reset, `32 |W₀| ≥ 31 N` and `32 |W| < 28 N` give
`3 N (r + 1) ≤ 32 (charges)`, and the new epoch has `W₀ = W`. -/
theorem invCharge_point {G : ResGame α} {evs : List (ResEvent α)} {st : ReservoirState α}
    (hinv : ReservoirInv G evs st) (u : α) :
    InvCharge G (evs ++ [.point u]) (st.pointStep G u) := by
  have hpot := hinv.charge.potential
  have hpc := hinv.charge.point_charge
  have hcc := hinv.charge.cell_charge
  have hep := hinv.size.epoch_big
  have hcount : pointCount (evs ++ [ResEvent.point u]) = pointCount evs + 1 := by
    simp [pointCount, List.countP_append, ResEvent.isPoint]
  have hmass : setMass (evs ++ [ResEvent.point u]) = setMass evs := by
    simp [setMass, ResEvent.setCard]
  have hdel : (st.live.erase u).card + (if u ∈ st.live then 1 else 0) = st.live.card := by
    split_ifs with h
    · exact Finset.card_erase_add_one h
    · rw [Finset.erase_eq_of_notMem h, Nat.add_zero]
  have key : ∀ st' : ReservoirState α,
      3 * (G.N * st'.ordinaryResets) + 32 * st'.epochLive.card ≤
        32 * (st'.pointCharge + st'.cellCharge) + 32 * st'.live.card →
      31 * G.N ≤ 32 * st'.epochLive.card →
      st'.pointCharge ≤ pointCount (evs ++ [.point u]) →
      2 ^ G.delta * st'.cellCharge ≤ setMass (evs ++ [.point u]) →
      InvCharge G (evs ++ [.point u]) (st'.ordinaryCheck G) := by
    intro st' hpot' hep' hpc' hcc'
    unfold ReservoirState.ordinaryCheck
    split_ifs with hr
    · refine ⟨?_, hpc', hcc'⟩
      simp only [ReservoirState.reselect]
      have hY : G.N * (st'.ordinaryResets + 1) = G.N * st'.ordinaryResets + G.N :=
        Nat.mul_succ _ _
      rw [hY]
      generalize G.N * st'.ordinaryResets = X at hpot' ⊢
      omega
    · exact ⟨hpot', hpc', hcc'⟩
  unfold ReservoirState.pointStep
  apply key
  · dsimp only
    generalize G.N * st.ordinaryResets = X at hpot ⊢
    generalize (if u ∈ st.live then 1 else 0) = d at hdel ⊢
    omega
  · exact hep
  · dsimp only
    rw [hcount]
    split_ifs <;> omega
  · rw [hmass]
    exact hcc

/-- Charge invariants after a set event.
Proof: a whole-cell mark deletes `d = |W ∩ Q|`; `Q` is a cell of a known table with
`2^ℓ ≤ |Q|` (`ValidHistory.set_elig`), so `2^δ d ≤ |Q|` by `InvLive.light`, and
`setMass (evs ++ [set Q i]) = setMass evs + |Q|`; the potential is handled as for points.
Reference: paper ("Its contribution is therefore at most min{N, 2^-δ |Q|}"); L19. -/
theorem invCharge_set {G : ResGame α} {K τ S : ℕ} {evs : List (ResEvent α)}
    {st : ReservoirState α} (hinv : ReservoirInv G evs st) (Q : Finset α) (i : ℕ)
    (hv : ValidHistory G K τ S (evs ++ [.set Q i])) :
    InvCharge G (evs ++ [.set Q i]) (st.setStep G Q i) := by
  have hpot := hinv.charge.potential
  have hpc := hinv.charge.point_charge
  have hcc := hinv.charge.cell_charge
  have hep := hinv.size.epoch_big
  have hcount : pointCount (evs ++ [ResEvent.set Q i]) = pointCount evs := by
    simp [pointCount, List.countP_append, ResEvent.isPoint]
  have hmass : setMass (evs ++ [ResEvent.set Q i]) = setMass evs + Q.card := by
    simp [setMass, ResEvent.setCard]
  have key : ∀ st' : ReservoirState α,
      3 * (G.N * st'.ordinaryResets) + 32 * st'.epochLive.card ≤
        32 * (st'.pointCharge + st'.cellCharge) + 32 * st'.live.card →
      31 * G.N ≤ 32 * st'.epochLive.card →
      st'.pointCharge ≤ pointCount (evs ++ [.set Q i]) →
      2 ^ G.delta * st'.cellCharge ≤ setMass (evs ++ [.set Q i]) →
      InvCharge G (evs ++ [.set Q i]) (st'.ordinaryCheck G) := by
    intro st' hpot' hep' hpc' hcc'
    unfold ReservoirState.ordinaryCheck
    split_ifs with hr
    · refine ⟨?_, hpc', hcc'⟩
      simp only [ReservoirState.reselect]
      have hY : G.N * (st'.ordinaryResets + 1) = G.N * st'.ordinaryResets + G.N :=
        Nat.mul_succ _ _
      rw [hY]
      generalize G.N * st'.ordinaryResets = X at hpot' ⊢
      omega
    · exact ⟨hpot', hpc', hcc'⟩
  unfold ReservoirState.setStep
  split_ifs with hmark
  · obtain ⟨⟨P, hP, hQP⟩, -⟩ := hmark
    have hell : 2 ^ G.ell ≤ Q.card := (hv.set_elig Q i (by simp)).2.1
    have hlight := hinv.live.light P hP Q hQP hell
    have hdel : (st.live \ Q).card + (st.live ∩ Q).card = st.live.card :=
      Finset.card_sdiff_add_card_inter _ _
    apply key
    · dsimp only
      generalize G.N * st.ordinaryResets = X at hpot ⊢
      omega
    · exact hep
    · rw [hcount]
      exact hpc
    · rw [hmass]
      dsimp only
      rw [Nat.mul_add, Finset.inter_comm]
      exact Nat.add_le_add hcc hlight
  · apply key
    · exact hpot
    · exact hep
    · rw [hcount]
      exact hpc
    · rw [hmass]
      exact hcc.trans (Nat.le_add_right _ _)

/-- Charge invariants after a table event.
Proof: the activation deletions are not charged (they belong to the forced reset); the forced
choice starts a new epoch with `W₀ = W`, and `3 N r ≤ 32 (charges)` follows from the old
potential and `|W| ≤ |W₀|`; the ledger counters are unchanged. -/
theorem invCharge_table {G : ResGame α} {evs : List (ResEvent α)} {st : ReservoirState α}
    (hinv : ReservoirInv G evs st) (P : List (Finset α)) :
    InvCharge G (evs ++ [.table P]) (st.tableStep G P) := by
  have hpot := hinv.charge.potential
  have hpc := hinv.charge.point_charge
  have hcc := hinv.charge.cell_charge
  have hsub : st.live.card ≤ st.epochLive.card := Finset.card_le_card hinv.live.live_epoch
  have hcount : pointCount (evs ++ [ResEvent.table P]) = pointCount evs := by
    simp [pointCount, List.countP_append, ResEvent.isPoint]
  have hmass : setMass (evs ++ [ResEvent.table P]) = setMass evs := by
    simp [setMass, ResEvent.setCard]
  refine ⟨?_, ?_, ?_⟩
  · simp only [ReservoirState.tableStep, ReservoirState.reselect]
    generalize G.N * st.ordinaryResets = X at hpot ⊢
    omega
  · rw [hcount]
    exact hpc
  · rw [hmass]
    exact hcc

/-- The invariants are preserved by every transition along a valid history. -/
theorem inv_step {G : ResGame α} {K τ S : ℕ} {θ : ℝ} (hG : GameHyp G K τ S θ)
    {evs : List (ResEvent α)} {st : ReservoirState α} (hinv : ReservoirInv G evs st)
    (e : ResEvent α) (hv : ValidHistory G K τ S (evs ++ [e])) :
    ReservoirInv G (evs ++ [e]) (reservoirTransition G st e) := by
  cases e with
  | point u =>
    have hb := invBook_point hinv u
    exact ⟨hb, invLive_point hinv u, invSize_point hG hinv u hv hb, invCharge_point hinv u⟩
  | set Q i =>
    have hb := invBook_set hinv Q i
    exact ⟨hb, invLive_set hinv Q i, invSize_set hG hinv Q i hv hb, invCharge_set hinv Q i hv⟩
  | table P =>
    have hb := invBook_table hinv P
    exact ⟨hb, invLive_table st P, invSize_table hG P hv hb, invCharge_table hinv P⟩

/-- **Reservoir invariants** (blueprint node L18).  Under the game hypotheses, along every valid
history (the L14 count/certificate invariants), starting from the initial choice: known tables
are the validated table events, stored sets the set events; marked vertices contain all processed
point outputs and all marked cells, and every stored set that is a cell of a known table is
marked; the live reservoir lies in the current sphere, outside all permanent marks, inside its
epoch's initial reservoir (of size `≥ 31N/32`), meets large known cells lightly, and has
`8 |W| ≥ 7 N` after every completed transition; the charge ledger satisfies the potential
inequality. -/
theorem reservoirInvariants {G : ResGame α} {K τ S : ℕ} {θ : ℝ} (hG : GameHyp G K τ S θ)
    (evs : List (ResEvent α)) (hv : ValidHistory G K τ S evs) :
    ReservoirInv G evs (run G evs) := by
  induction evs using List.reverseRecOn with
  | nil => exact inv_init hG
  | append_singleton evs e ih =>
    rw [run_append_singleton]
    exact inv_step hG (ih hv.of_append) e hv

/-! ### L19: deletion charges -/

/-- **Deletion charge bound** (blueprint node L19).  Along a valid history, the live points
deleted by ordinary point events number fewer than `2^K`; the live points deleted by whole-cell
marks between table arrivals satisfy `2^δ · charge ≤ (K+τ+1) 2^(K+τ) ≤ 2^(K+δ)`, hence number at
most `2^K`; in rational form `(K+τ+1) 2^(K+τ-δ) ≤ 2^K` (the exponent may be negative).  Cells
activated by table events are not charged here. -/
theorem deletionChargeBound {G : ResGame α} {K τ S : ℕ} {θ : ℝ} (hG : GameHyp G K τ S θ)
    (evs : List (ResEvent α)) (hv : ValidHistory G K τ S evs) :
    (run G evs).pointCharge < 2 ^ K ∧
      2 ^ G.delta * (run G evs).cellCharge ≤ (K + τ + 1) * 2 ^ (K + τ) ∧
      (K + τ + 1) * 2 ^ (K + τ) ≤ 2 ^ (K + G.delta) ∧
      (run G evs).cellCharge ≤ 2 ^ K ∧
      ((K + τ + 1 : ℕ) : ℝ) * (2 : ℝ) ^ ((K : ℤ) + τ - G.delta) ≤ 2 ^ K := by
  have hinv := reservoirInvariants hG evs hv
  have hcell : 2 ^ G.delta * (run G evs).cellCharge ≤ (K + τ + 1) * 2 ^ (K + τ) :=
    hinv.charge.cell_charge.trans (setMass_le hv)
  refine ⟨hinv.charge.point_charge.trans_lt hv.point_count, hcell, hG.charge, ?_,
    charge_rational hG.charge⟩
  have h2 : 2 ^ G.delta * (run G evs).cellCharge ≤ 2 ^ G.delta * 2 ^ K := by
    rw [← pow_add, Nat.add_comm]; exact hcell.trans hG.charge
  exact Nat.le_of_mul_le_mul_left h2 (by positivity)

/-! ### L20: the number of choices -/

/-- **Reservoir choice count** (blueprint node L20).  Along a valid history, the number of
emitted centers (the initial choice, the ordinary resets and the forced resets) satisfies
`N · #choices ≤ 32 · 2^K`: each ordinary reset follows at least `3N/32` charged deletions, the
charges total less than `2^(K+1)`, and the fewer than `2^(S+1)` forced resets cost at most `2^K`
by the arrival inequality. -/
theorem reservoirChoiceCount {G : ResGame α} {K τ S : ℕ} {θ : ℝ} (hG : GameHyp G K τ S θ)
    (evs : List (ResEvent α)) (hv : ValidHistory G K τ S evs) :
    G.N * (emittedCenters G evs).length ≤ 32 * 2 ^ K := by
  have hinv := reservoirInvariants hG evs hv
  obtain ⟨hpc, -, -, hcc, -⟩ := deletionChargeBound hG evs hv
  have hlen : (emittedCenters G evs).length =
      1 + (run G evs).ordinaryResets + tableCount evs := by
    rw [emittedCenters, List.length_reverse, hinv.book.emitted_length]
  have hpot := hinv.charge.potential
  have hsub : (run G evs).live.card ≤ (run G evs).epochLive.card :=
    card_le_card hinv.live.live_epoch
  have htc : G.N * tableCount evs + G.N ≤ 2 ^ K :=
    calc G.N * tableCount evs + G.N = G.N * (tableCount evs + 1) := by ring
      _ ≤ G.N * 2 ^ (S + 1) := Nat.mul_le_mul_left _ hv.table_count
      _ ≤ 2 ^ K := hG.arrivals
  rw [hlen, show G.N * (1 + (run G evs).ordinaryResets + tableCount evs) =
    G.N * (run G evs).ordinaryResets + (G.N * tableCount evs + G.N) by ring]
  generalize G.N * (run G evs).ordinaryResets = x at hpot ⊢
  generalize G.N * tableCount evs + G.N = y at htc ⊢
  generalize 2 ^ K = p at hpc hcc htc ⊢
  omega

/-! ### L21: stabilization -/

/-- **Bounded growing histories stabilize.**  A family of histories growing by appending, with
uniformly bounded length, is eventually constant.
Proof: the lengths form a monotone bounded sequence of naturals, eventually constant from some
`s₀` (take `s₀` maximizing the length among `s ≤ B + 1`, or use `Nat.find` on
`∀ t ≥ s, length t = length s`); a prefix of equal length is equal
(`List.IsPrefix.eq_of_length`).
Reference: L21 ("the maximum of this finite family exists"). -/
theorem exists_stable_of_prefix_of_length_le {β : Type*} (hist : ℕ → List β)
    (hmono : ∀ s, hist s <+: hist (s + 1)) (B : ℕ) (hB : ∀ s, (hist s).length ≤ B) :
    ∃ s₀, ∀ s, s₀ ≤ s → hist s = hist s₀ := by
  have hmono' : ∀ s t, s ≤ t → hist s <+: hist t := fun s t hst => by
    induction t, hst using Nat.le_induction with
    | base => exact List.prefix_refl _
    | succ t _ ih => exact ih.trans (hmono t)
  have key : ∀ n s, B - (hist s).length ≤ n → ∃ s₀, ∀ t, s₀ ≤ t → hist t = hist s₀ := by
    intro n
    induction n with
    | zero =>
      intro s hs
      refine ⟨s, fun t hst => ?_⟩
      have h1 := hmono' s t hst
      have h2 := hB t
      have h3 := h1.length_le
      exact (h1.eq_of_length (by omega)).symm
    | succ n ih =>
      intro s hs
      by_cases h : ∀ t, s ≤ t → (hist t).length = (hist s).length
      · exact ⟨s, fun t hst => ((hmono' s t hst).eq_of_length (h t hst).symm).symm⟩
      · simp only [not_forall] at h
        obtain ⟨t, hst, hne⟩ := h
        have h3 := (hmono' s t hst).length_le
        have h2 := hB t
        exact ih t (by omega)
  exact key B 0 (by omega)

/-- A family of lists growing by appending at each step grows by appending between any two
stages. -/
theorem prefix_of_le {β : Type*} (hist : ℕ → List β) (hmono : ∀ s, hist s <+: hist (s + 1))
    {s t : ℕ} (hst : s ≤ t) : hist s <+: hist t := by
  induction t, hst using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ t _ ih => exact ih.trans (hmono t)

/-- The head of a list is a member of it. -/
theorem mem_of_head?_eq_some {β : Type*} {l : List β} {a : β} (h : l.head? = some a) :
    a ∈ l := by
  cases l with
  | nil => simp at h
  | cons b l =>
    simp only [List.head?_cons, Option.some.injEq] at h
    simp [h]

/-- **Reservoir stabilizes** (blueprint node L21).  For a history growing by appending and valid
at every stage (e.g. the effective stream of L14), there is a stage `s₀` after which no event
arrives; every event of every stage has arrived by `s₀`.  The final state has a center `z` in the
cube, emitted by the game (with `N · #emitted ≤ 32 · 2^K`), and a reservoir `W ⊆ S_z` with
`8 |W| ≥ 7 N` that avoids every point event and every cell `Q` of a table event for which a set
event `(Q, i)` occurs, whichever of the two arrives first.  The stage `s₀` is obtained
classically; it is not computed. -/
theorem reservoirStabilizes {G : ResGame α} {K τ S : ℕ} {θ : ℝ} (hG : GameHyp G K τ S θ)
    (hist : ℕ → List (ResEvent α)) (hmono : ∀ s, hist s <+: hist (s + 1))
    (hv : ∀ s, ValidHistory G K τ S (hist s)) :
    ∃ s₀, (∀ s, s₀ ≤ s → hist s = hist s₀) ∧ (∀ s e, e ∈ hist s → e ∈ hist s₀) ∧
      (run G (hist s₀)).center ∈ G.centers ∧
      (run G (hist s₀)).center ∈ emittedCenters G (hist s₀) ∧
      G.N * (emittedCenters G (hist s₀)).length ≤ 32 * 2 ^ K ∧
      (run G (hist s₀)).live ⊆ G.sphere (run G (hist s₀)).center ∧
      7 * G.N ≤ 8 * (run G (hist s₀)).live.card ∧
      (∀ s u, ResEvent.point u ∈ hist s → u ∉ (run G (hist s₀)).live) ∧
      (∀ s s' Q i P, ResEvent.set Q i ∈ hist s → ResEvent.table P ∈ hist s' → Q ∈ P →
        Disjoint Q (run G (hist s₀)).live) := by
  obtain ⟨s₀, hs₀⟩ := exists_stable_of_prefix_of_length_le hist hmono _
    (fun s => length_le_of_validHistory (hv s))
  have hall : ∀ s e, e ∈ hist s → e ∈ hist s₀ := by
    intro s e he
    rcases le_total s s₀ with h | h
    · exact (prefix_of_le hist hmono h).subset he
    · rwa [← hs₀ s h]
  have hinv := reservoirInvariants hG (hist s₀) (hv s₀)
  refine ⟨s₀, hs₀, hall, hinv.size.center_mem, ?_, reservoirChoiceCount hG _ (hv s₀),
    hinv.live.live_sphere, hinv.size.live_big, ?_, ?_⟩
  · rw [emittedCenters, List.mem_reverse]
    exact mem_of_head?_eq_some hinv.book.emitted_head
  · intro s u hu hlive
    have hm := hinv.book.point_marked u (hall s _ hu)
    exact Finset.disjoint_left.mp hinv.live.live_disjoint hlive hm
  · intro s s' Q i P hQ hP hQP
    have hc := hinv.book.cell_marked Q i P (hall s _ hQ) (hall s' _ hP) hQP
    have hsub := hinv.book.markedCells_sub Q hc
    exact Finset.disjoint_left.mpr fun x hxQ hxW =>
      Finset.disjoint_left.mp hinv.live.live_disjoint hxW (hsub hxQ)

/-- **Stability of the emitted centers** (for the occurrence decoder of node L22).  Along a
history growing by appending, once the `j`th emitted center exists it never changes: the decoder
may output the `j`th entry at any stage at which it exists. -/
theorem emittedCenters_getElem?_stable (G : ResGame α) (hist : ℕ → List (ResEvent α))
    (hmono : ∀ s, hist s <+: hist (s + 1)) {s t j : ℕ} (hst : s ≤ t) {z : α}
    (h : (emittedCenters G (hist s))[j]? = some z) :
    (emittedCenters G (hist t))[j]? = some z := by
  obtain ⟨u, hu⟩ := emittedCenters_prefix G (prefix_of_le hist hmono hst)
  have hj : j < (emittedCenters G (hist s)).length := by
    by_contra hcon
    rw [List.getElem?_eq_none (by omega)] at h
    exact absurd h (by simp)
  rw [← hu, List.getElem?_append_left hj, h]

end Kolmogorov.StrongMerging.Lower
