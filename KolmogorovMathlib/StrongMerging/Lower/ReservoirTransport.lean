import KolmogorovMathlib.StrongMerging.Lower.ReservoirGame

/-!
# Transport of the reservoir game along an embedding of points

The generic reservoir game commutes with every embedding `φ : α ↪ β` of point types: if the game
`G'` on `β` is the image of `G` (`IsGameImage`), then running `G'` on the image of a history gives
the image of the run of `G`; in particular the emitted centers are the images of the emitted
centers (`emittedCenters_map`), and the effective event stream of image sources is the image of
the stream (`eventHistory_map`).

This lets the instance (nodes L22–L23) prove the combinatorial statements for points that are
binary words (the cube of the geometry cluster) while executing the game on natural-number codes
(for which `Finset` is `Primcodable`, see `ReservoirComputable`).
-/

namespace Kolmogorov.StrongMerging.Lower

open Finset

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- The image of an event under an embedding of points. -/
def ResEvent.map (φ : α ↪ β) : ResEvent α → ResEvent β
  | .point u => .point (φ u)
  | .set Q i => .set (Q.map φ) i
  | .table P => .table (P.map (Finset.map φ))

/-- The image of a board under an embedding of points; counters are unchanged. -/
def ReservoirState.map (φ : α ↪ β) (st : ReservoirState α) : ReservoirState β where
  tables := st.tables.map (List.map (Finset.map φ))
  stored := st.stored.map (Prod.map (Finset.map φ) id)
  marks := st.marks.map φ
  markedCells := st.markedCells.map (Finset.map φ)
  center := φ st.center
  live := st.live.map φ
  epochLive := st.epochLive.map φ
  emitted := st.emitted.map φ
  ordinaryResets := st.ordinaryResets
  pointCharge := st.pointCharge
  cellCharge := st.cellCharge

/-- `G'` is the image of the game `G` under the embedding `φ`: same integer parameters, mapped
centers (in the same order), mapped spheres and mapped fallback. -/
structure IsGameImage (φ : α ↪ β) (G : ResGame α) (G' : ResGame β) : Prop where
  /-- The centers are mapped, in the same order. -/
  centers : G'.centers = G.centers.map φ
  /-- Spheres are mapped. -/
  sphere : ∀ z, G'.sphere (φ z) = (G.sphere z).map φ
  /-- Same sphere size. -/
  N : G'.N = G.N
  /-- Same size exponent. -/
  ell : G'.ell = G.ell
  /-- Same density exponent. -/
  delta : G'.delta = G.delta
  /-- The fallback center is mapped. -/
  fallback : G'.fallback = φ G.fallback

variable {φ : α ↪ β} {G : ResGame α} {G' : ResGame β}

/-- **The bad set commutes with `φ`.**
Proof: `Finset.map_filter`-style extensionality: for `u' = φ u` in `S'_{φ z} = (S_z).map φ`,
`φ u ∈ marks.map φ ↔ u ∈ marks` (`Finset.mem_map'`), a mapped cell `Q.map φ` has the same
cardinality (`Finset.card_map`) and `Q.map φ ∩ (S_z).map φ = (Q ∩ S_z).map φ`
(`Finset.map_inter`), so heaviness is preserved; cells of mapped tables are mapped cells
(`List.mem_map`) and `Finset.map φ` is injective on finsets (`Finset.map_inj`). -/
theorem badSet_map (hG : IsGameImage φ G G') (marks : Finset α)
    (tables : List (List (Finset α))) (z : α) :
    badSet G' (marks.map φ) (tables.map (List.map (Finset.map φ))) (φ z) =
      (badSet G marks tables z).map φ := by
  have hheavy : ∀ Q : Finset α, IsHeavyCell G' (φ z) (Q.map φ) ↔ IsHeavyCell G z Q := by
    intro Q
    unfold IsHeavyCell
    rw [hG.sphere, ← Finset.map_inter, Finset.card_map, Finset.card_map, hG.ell, hG.delta]
  have hpred : ∀ u : α, (φ u ∈ marks.map φ ∨ ∃ P' ∈ tables.map (List.map (Finset.map φ)),
      ∃ Q' ∈ P', φ u ∈ Q' ∧ IsHeavyCell G' (φ z) Q') ↔
      (u ∈ marks ∨ ∃ P ∈ tables, ∃ Q ∈ P, u ∈ Q ∧ IsHeavyCell G z Q) := by
    intro u
    rw [Finset.mem_map' φ]
    refine or_congr Iff.rfl ⟨?_, ?_⟩
    · rintro ⟨P', hP', Q', hQ', hu, hh⟩
      obtain ⟨P, hP, rfl⟩ := List.mem_map.mp hP'
      obtain ⟨Q, hQ, rfl⟩ := List.mem_map.mp hQ'
      exact ⟨P, hP, Q, hQ, (Finset.mem_map' φ).mp hu, (hheavy Q).mp hh⟩
    · rintro ⟨P, hP, Q, hQ, hu, hh⟩
      exact ⟨P.map (Finset.map φ), List.mem_map.mpr ⟨P, hP, rfl⟩, Q.map φ,
        List.mem_map.mpr ⟨Q, hQ, rfl⟩, (Finset.mem_map' φ).mpr hu, (hheavy Q).mpr hh⟩
  unfold badSet
  rw [hG.sphere, Finset.filter_map]
  exact congrArg (Finset.map φ) (Finset.filter_congr fun u _ => hpred u)

/-- **The center search commutes with `φ`.**
Proof: `chooseCenter` is `List.find?` over the centers; rewrite the centers with `hG.centers`,
use `List.find?_map`, and `badSet_map` with `Finset.card_map` and `hG.N` to identify the
predicates. -/
theorem chooseCenter_map (hG : IsGameImage φ G G') (marks : Finset α)
    (tables : List (List (Finset α))) :
    chooseCenter G' (marks.map φ) (tables.map (List.map (Finset.map φ))) =
      (chooseCenter G marks tables).map φ := by
  unfold chooseCenter
  rw [hG.centers, List.find?_map]
  congr 2
  funext z
  simp only [Function.comp_apply, badSet_map hG, Finset.card_map, hG.N]

/-- **The reservoir choice commutes with `φ`.**
Proof: unfold `chooseReservoir`, rewrite with `chooseCenter_map`, case on
`chooseCenter G marks tables`; the `some` case uses `hG.sphere`, `badSet_map` and
`Finset.map_sdiff`; the fallback uses `hG.fallback`. -/
theorem chooseReservoir_map (hG : IsGameImage φ G G') (marks : Finset α)
    (tables : List (List (Finset α))) :
    chooseReservoir G' (marks.map φ) (tables.map (List.map (Finset.map φ))) =
      (φ (chooseReservoir G marks tables).1, (chooseReservoir G marks tables).2.map φ) := by
  unfold chooseReservoir
  rw [chooseCenter_map hG]
  cases h : chooseCenter G marks tables with
  | none => simp [hG.fallback]
  | some z => simp [hG.sphere, badSet_map hG, Finset.map_sdiff]

/-- **The initial state commutes with `φ`.**
Proof: `initState = (emptyState _).reselect _`; the empty boards correspond (`hG.fallback`,
`Finset.map_empty`), and `chooseReservoir_map` with empty marks and tables. -/
theorem initState_map (hG : IsGameImage φ G G') : initState G' = (initState G).map φ := by
  have h1 : chooseReservoir G' ∅ [] =
      (φ (chooseReservoir G ∅ []).1, (chooseReservoir G ∅ []).2.map φ) := by
    simpa using chooseReservoir_map hG (∅ : Finset α) []
  simp only [initState, ReservoirState.reselect, emptyState, ReservoirState.map, h1,
    hG.fallback, Finset.map_empty, List.map_nil, List.map_cons]

/-- **One transition commutes with `φ`.**
Proof: case on the event; unfold the step; every board operation commutes with the injective
`Finset.map φ` (`Finset.map_insert`, `Finset.map_erase`, `Finset.map_union`, `Finset.map_sdiff`,
`Finset.map_inter`, `Finset.card_map`, membership by `Finset.mem_map'` and `Finset.map_inj`),
`activated` and `listUnion` commute (`List.filter_map`, `mem_listUnion`), the tests have equal
truth values, and `reselect` commutes by `chooseReservoir_map`. -/
theorem reservoirTransition_map (hG : IsGameImage φ G G') (st : ReservoirState α)
    (e : ResEvent α) :
    reservoirTransition G' (st.map φ) (e.map φ) = (reservoirTransition G st e).map φ := by
  have hres : ∀ st : ReservoirState α, (st.map φ).reselect G' = (st.reselect G).map φ := by
    intro st
    have h := chooseReservoir_map hG st.marks st.tables
    simp only [ReservoirState.reselect, ReservoirState.map, h, List.map_cons]
  have hord : ∀ st : ReservoirState α,
      (st.map φ).ordinaryCheck G' = (st.ordinaryCheck G).map φ := by
    intro st
    unfold ReservoirState.ordinaryCheck
    have hc : (st.map φ).live.card = st.live.card := Finset.card_map _
    by_cases h : 8 * st.live.card < 7 * G.N
    · have h' : 8 * (st.map φ).live.card < 7 * G'.N := by rw [hc, hG.N]; exact h
      simp only [h, h', ↓reduceIte]
      rw [hres]
      rfl
    · have h' : ¬ 8 * (st.map φ).live.card < 7 * G'.N := by rw [hc, hG.N]; exact h
      simp only [h, h', ↓reduceIte]
  have hinj : Function.Injective (Finset.map φ) := Finset.map_injective φ
  have hlu : ∀ l : List (Finset α), listUnion (l.map (Finset.map φ)) = (listUnion l).map φ := by
    intro l
    induction l with
    | nil => simp [listUnion]
    | cons Q l ih =>
      change Q.map φ ∪ listUnion (l.map (Finset.map φ)) = (Q ∪ listUnion l).map φ
      rw [ih, Finset.map_union]
  cases e with
  | point u =>
    change (st.map φ).pointStep G' (φ u) = (st.pointStep G u).map φ
    unfold ReservoirState.pointStep
    rw [← hord]
    congr 1
    simp [ReservoirState.map, Finset.map_insert, Finset.map_erase]
  | set Q i =>
    change (st.map φ).setStep G' (Q.map φ) i = (st.setStep G Q i).map φ
    unfold ReservoirState.setStep
    have hcond : ((∃ P ∈ (st.map φ).tables, Q.map φ ∈ P) ∧ Q.map φ ∉ (st.map φ).markedCells) ↔
        ((∃ P ∈ st.tables, Q ∈ P) ∧ Q ∉ st.markedCells) := by
      change ((∃ P ∈ st.tables.map (List.map (Finset.map φ)), Q.map φ ∈ P) ∧
          Q.map φ ∉ st.markedCells.map (Finset.map φ)) ↔ _
      rw [List.mem_map_of_injective hinj]
      refine and_congr ⟨?_, ?_⟩ Iff.rfl
      · rintro ⟨P', hP', hQ⟩
        obtain ⟨P, hP, rfl⟩ := List.mem_map.mp hP'
        exact ⟨P, hP, (List.mem_map_of_injective hinj).mp hQ⟩
      · rintro ⟨P, hP, hQ⟩
        exact ⟨P.map (Finset.map φ), List.mem_map.mpr ⟨P, hP, rfl⟩,
          (List.mem_map_of_injective hinj).mpr hQ⟩
    have hcard : (st.live.map φ ∩ Q.map φ).card = (st.live ∩ Q).card := by
      rw [← Finset.map_inter, Finset.card_map]
    by_cases h : (∃ P ∈ st.tables, Q ∈ P) ∧ Q ∉ st.markedCells
    · have h' := hcond.mpr h
      simp only [h, h', ↓reduceIte, not_false_eq_true, and_self]
      rw [← hord]
      congr 1
      simp [ReservoirState.map, Finset.map_union, Finset.map_sdiff, hcard]
    · have h' := mt hcond.mp h
      simp only [h, h', ↓reduceIte]
      rw [← hord]
      congr 1
  | table P =>
    change (st.map φ).tableStep G' (P.map (Finset.map φ)) = (st.tableStep G P).map φ
    have hact : ReservoirState.activated (st.map φ) (P.map (Finset.map φ)) =
        (ReservoirState.activated st P).map (Finset.map φ) := by
      unfold ReservoirState.activated
      change ((st.stored.map (Prod.map (Finset.map φ) id)).map Prod.fst).filter
          (fun Q' => decide (Q' ∈ P.map (Finset.map φ))) = _
      rw [List.map_map, List.filter_map]
      have hfst : (Prod.fst ∘ Prod.map (Finset.map φ) (id : ℕ → ℕ)) =
          (Finset.map φ ∘ Prod.fst) := rfl
      rw [hfst, ← List.map_map, List.filter_map]
      congr 2
      apply List.filter_congr
      intro x _
      simp
    unfold ReservoirState.tableStep
    rw [hact, hlu, ← hres]
    congr 1
    simp [ReservoirState.map, Finset.map_union, Finset.map_sdiff]

/-- **The run commutes with `φ`**: running the image game on the image history gives the image
of the run. -/
theorem run_map (hG : IsGameImage φ G G') (evs : List (ResEvent α)) :
    run G' (evs.map (ResEvent.map φ)) = (run G evs).map φ := by
  induction evs using List.reverseRecOn with
  | nil => exact initState_map hG
  | append_singleton evs e ih =>
    rw [List.map_append, List.map_singleton, run_append_singleton, run_append_singleton, ih,
      reservoirTransition_map hG]

/-- **The emitted centers commute with `φ`.** -/
theorem emittedCenters_map (hG : IsGameImage φ G G') (evs : List (ResEvent α)) :
    emittedCenters G' (evs.map (ResEvent.map φ)) = (emittedCenters G evs).map φ := by
  rw [emittedCenters, emittedCenters, run_map hG, List.map_reverse]
  rfl

/-- `src'` is the image of the event sources `src` under `φ`: same candidate families and costs,
mapped outputs, and the table evaluators agree on mapped points. -/
structure IsSourceImage (φ : α ↪ β) (src : EventSources α) (src' : EventSources β) : Prop where
  /-- Same number of point candidates. -/
  numPt : src'.numPt = src.numPt
  /-- Point outputs are mapped. -/
  ptEval : ∀ c s, src'.ptEval c s = (src.ptEval c s).map φ
  /-- Same number of set candidates. -/
  numSet : src'.numSet = src.numSet
  /-- Set outputs are mapped. -/
  setEval : ∀ c s, src'.setEval c s = (src.setEval c s).map (Finset.map φ)
  /-- Same certificate lengths. -/
  setCost : ∀ c, src'.setCost c = src.setCost c
  /-- Same number of table candidates. -/
  numTab : src'.numTab = src.numTab
  /-- Table outputs on mapped points are mapped. -/
  tabEval : ∀ c u s, src'.tabEval c (φ u) s = (src.tabEval c u s).map (Finset.map φ)

/-- **The event stream commutes with `φ`**: the history of the image sources on the image game is
the image of the history.
Proof: unfold `eventHistory`, `stageEvents` and the three `…EventAt`; `List.map_flatMap`; every
test has the same truth value on corresponding data: `firstAt` (`Option.isSome_map`,
`Option.isNone_map`), cube membership (`G'.cube = G.cube.map φ` from `hG.centers`,
`List.toFinset_map`), `SetEligible` (`Finset.map_subset_map`, `Finset.card_map`, `hG.ell`),
`tableDone` and `tableEntryOk` (`List.all_map`, `hsrc.tabEval`, `Finset.mem_map'`), and
`tableCells` maps cell by cell. -/
theorem eventHistory_map {src : EventSources α} {src' : EventSources β}
    (hG : IsGameImage φ G G') (hsrc : IsSourceImage φ src src') (K τ s : ℕ) :
    eventHistory G' K τ src' s = (eventHistory G K τ src s).map (ResEvent.map φ) := by
  have hcube : G'.cube = G.cube.map φ := by
    ext x
    simp [ResGame.cube, hG.centers]
  have hpt : ∀ t c, ptEventAt G' src' t c = (ptEventAt G src t c).map (ResEvent.map φ) := by
    intro t c
    have hf : src'.ptEval c = fun s => (src.ptEval c s).map φ := funext fun s => hsrc.ptEval c s
    simp only [ptEventAt, hf, firstAt, Option.isSome_map, Option.isNone_map, hcube]
    rcases Option.eq_none_or_eq_some (src.ptEval c t) with hn | ⟨u, hu⟩
    · simp only [hn, Option.map_none, List.map_nil]
    · simp only [hu, Option.map_some, Finset.mem_map' φ]
      split_ifs <;> rfl
  have hset : ∀ t c, setEventAt G' K τ src' t c =
      (setEventAt G K τ src t c).map (ResEvent.map φ) := by
    intro t c
    have hf : src'.setEval c = fun s => (src.setEval c s).map (Finset.map φ) :=
      funext fun s => hsrc.setEval c s
    have hel : ∀ Q : Finset α, SetEligible G' K τ (Q.map φ) (src.setCost c) ↔
        SetEligible G K τ Q (src.setCost c) := by
      intro Q
      simp only [SetEligible, hcube, Finset.map_subset_map, Finset.card_map, hG.ell]
    simp only [setEventAt, hf, firstAt, Option.isSome_map, Option.isNone_map]
    rcases Option.eq_none_or_eq_some (src.setEval c t) with hn | ⟨Q, hQ⟩
    · simp only [hn, Option.map_none, List.map_nil]
    · simp only [hQ, Option.map_some, hsrc.setCost, hel]
      split_ifs <;> rfl
  have htab : ∀ t c, tabEventAt G' src' t c = (tabEventAt G src t c).map (ResEvent.map φ) := by
    intro t c
    have hdone : ∀ s, tableDone G' src' c s = tableDone G src c s := by
      intro s
      simp only [tableDone, hG.centers, List.all_map]
      congr 1
      funext u
      simp only [Function.comp_def, hsrc.tabEval, Option.isSome_map]
    have hok : G'.centers.all (tableEntryOk G' src' c t) =
        G.centers.all (tableEntryOk G src c t) := by
      rw [hG.centers, List.all_map]
      congr 1
      funext u
      simp only [Function.comp, tableEntryOk, hsrc.tabEval]
      rcases Option.eq_none_or_eq_some (src.tabEval c u t) with hn | ⟨Q, hQ⟩
      · simp only [hn, Option.map_none]
      · simp only [hQ, Option.map_some, hcube, Finset.map_subset_map, Finset.mem_map' φ]
        congr 1
        apply propext
        refine and_congr_right fun _ => and_congr_right fun _ => ?_
        constructor
        · intro h v hv
          have := h (φ v) (Finset.mem_map_of_mem φ hv)
          rw [hsrc.tabEval] at this
          exact Option.map_injective (Finset.map_injective φ) this
        · intro h v' hv'
          obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hv'
          rw [hsrc.tabEval, h v hv]
          rfl
    have hcells : tableCells G' src' c t = (tableCells G src c t).map (Finset.map φ) := by
      simp only [tableCells, hG.centers, List.map_map]
      congr 1
      funext u
      simp only [Function.comp, hsrc.tabEval]
      rcases Option.eq_none_or_eq_some (src.tabEval c u t) with hn | ⟨Q, hQ⟩
      · simp only [hn, Option.map_none, Option.getD_none, Finset.map_empty]
      · simp only [hQ, Option.map_some, Option.getD_some]
    simp only [tabEventAt, hdone, hok, hcells]
    split_ifs <;> rfl
  unfold eventHistory
  rw [List.map_flatMap]
  congr 1
  funext t
  have e1 : ptEventAt G' src' t = fun c => (ptEventAt G src t c).map (ResEvent.map φ) :=
    funext (hpt t)
  have e2 : setEventAt G' K τ src' t =
      fun c => (setEventAt G K τ src t c).map (ResEvent.map φ) :=
    funext (hset t)
  have e3 : tabEventAt G' src' t = fun c => (tabEventAt G src t c).map (ResEvent.map φ) :=
    funext (htab t)
  simp only [stageEvents, List.map_append, List.map_flatMap, hsrc.numPt, hsrc.numSet,
    hsrc.numTab, e1, e2, e3]

end Kolmogorov.StrongMerging.Lower
