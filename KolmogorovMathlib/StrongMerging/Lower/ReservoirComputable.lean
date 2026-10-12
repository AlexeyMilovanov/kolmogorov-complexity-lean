import KolmogorovMathlib.StrongMerging.Lower.ReservoirComputable.Toolkit

/-!
# Effectivity of the reservoir game

The computability half of blueprint nodes L14 (the event stream is effective) and L17 (the
transitions are executable), for the instance in which cube points are coded by natural numbers.
Points must be coded by a type `α` for which `Finset α` is `Primcodable`; Mathlib provides
`Primcodable (Finset ℕ)` (through `Denumerable`), so this module fixes `α = ℕ`.  The instance
(node L22) codes the cube `{0,1}^M` by naturals below `2^M`.

* `resEventEquiv`, `reservoirStateEquiv`: codes of events and boards, giving `Primcodable`
  instances;
* `IsComputableGame`, `IsComputableSources`: the game data and the event sources are computable,
  uniformly in a parameter `p : π` (the numeric header of L22);
* `run_computable`, `emittedCenters_eventHistory_computable`: the board after any history, and the
  sequence of centers emitted up to stage `s`, are computable in `(p, s)`.  The ordinary partial
  decoder of L22 searches the least `s` with more than `j` emitted centers and outputs the `j`th
  one (`emittedCenters_prefix` makes the answer independent of `s`).

No totality test and no oracle occurs: every stage is a finite computation.  The noncomputable
part of the construction is only the final stage of `reservoirStabilizes`.

The first part of the development is in
`KolmogorovMathlib.StrongMerging.Lower.ReservoirComputable.Toolkit`, imported here.
-/

namespace Kolmogorov.StrongMerging.Lower

variable {π : Type*} [Primcodable π]

/-! ### The center search -/

/-- **The heaviness test is computable**: `2^ℓ ≤ |Q| ∧ |Q| < 2^δ |Q ∩ S_z|` is an integer
test. -/
theorem computable_isHeavyCell {G : π → ResGame ℕ} (hG : IsComputableGame G) :
    Computable fun x : π × ℕ × Finset ℕ => decide (IsHeavyCell (G x.1) x.2.1 x.2.2) := by
  have hpow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) := Primrec₂.unpaired'.1 Nat.Primrec.pow
  have hQ : Computable fun x : π × ℕ × Finset ℕ => x.2.2.card :=
    computable_finsetCard.comp (Computable.snd.comp Computable.snd)
  have h1 : Computable fun x : π × ℕ × Finset ℕ => decide (2 ^ (G x.1).ell ≤ x.2.2.card) :=
    (Primrec.nat_le.decide.to_comp.comp (hpow.to_comp.comp (Computable.const 2)
      (hG.ell.comp Computable.fst)) hQ).of_eq fun _ => rfl
  have hI : Computable fun x : π × ℕ × Finset ℕ => (x.2.2 ∩ (G x.1).sphere x.2.1).card :=
    (computable_finsetCard.comp (computable_finsetInter.comp (Computable.pair
      (Computable.snd.comp Computable.snd)
      (hG.sphere.comp Computable.fst (Computable.fst.comp Computable.snd))))).of_eq fun _ => rfl
  have h2 : Computable fun x : π × ℕ × Finset ℕ =>
      decide (x.2.2.card < 2 ^ (G x.1).delta * (x.2.2 ∩ (G x.1).sphere x.2.1).card) :=
    (Primrec.nat_lt.decide.to_comp.comp hQ (Primrec.nat_mul.to_comp.comp
      (hpow.to_comp.comp (Computable.const 2) (hG.delta.comp Computable.fst)) hI)).of_eq
      fun _ => rfl
  refine (Primrec.and.to_comp.comp h1 h2).of_eq fun x => ?_
  rw [Bool.eq_iff_iff, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff,
    decide_eq_true_iff]
  rfl

/-- **The bad set is computable**: a filter of the sphere by the Boolean
`decide (u ∈ marks) || tables.any (fun P => P.any (fun Q => decide (u ∈ Q) && heavy z Q))`. -/
theorem computable_badSet {G : π → ResGame ℕ} (hG : IsComputableGame G) :
    Computable fun x : π × Finset ℕ × List (List (Finset ℕ)) × ℕ =>
      badSet (G x.1) x.2.1 x.2.2.1 x.2.2.2 := by
  have hheavy := computable_isHeavyCell hG
  have hin : Computable fun w : ((π × Finset ℕ × List (List (Finset ℕ)) × ℕ) × ℕ) ×
      List (Finset ℕ) =>
      w.2.any fun Q => decide (w.1.2 ∈ Q) && decide (IsHeavyCell (G w.1.1.1) w.1.1.2.2.2 Q) := by
    have hp : Computable fun v : (((π × Finset ℕ × List (List (Finset ℕ)) × ℕ) × ℕ) ×
        List (Finset ℕ)) × Finset ℕ =>
        decide (v.1.1.2 ∈ v.2) && decide (IsHeavyCell (G v.1.1.1.1) v.1.1.1.2.2.2 v.2) :=
      (Primrec.and.to_comp.comp (computable_finsetMem.comp (Computable.pair
        (Computable.snd.comp (Computable.fst.comp Computable.fst)) Computable.snd))
        (hheavy.comp (Computable.pair
          (Computable.fst.comp (Computable.fst.comp (Computable.fst.comp Computable.fst)))
          (Computable.pair (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp
            (Computable.fst.comp (Computable.fst.comp Computable.fst))))) Computable.snd)))).of_eq
        fun _ => rfl
    exact (Kolmogorov.computable_list_any Computable.snd hp.to₂).of_eq fun _ => rfl
  have hout : Computable fun y : (π × Finset ℕ × List (List (Finset ℕ)) × ℕ) × ℕ =>
      decide (y.2 ∈ y.1.2.1) || y.1.2.2.1.any fun P =>
        P.any fun Q => decide (y.2 ∈ Q) && decide (IsHeavyCell (G y.1.1) y.1.2.2.2 Q) :=
    (Primrec.or.to_comp.comp (computable_finsetMem.comp (Computable.pair Computable.snd
      (Computable.fst.comp (Computable.snd.comp Computable.fst))))
      (Kolmogorov.computable_list_any (Computable.fst.comp (Computable.snd.comp
        (Computable.snd.comp Computable.fst))) hin.to₂)).of_eq fun _ => rfl
  refine (computable_finsetFilter (hG.sphere.comp Computable.fst
    (Computable.snd.comp (Computable.snd.comp Computable.snd))) hout.to₂).of_eq fun x => ?_
  unfold badSet
  refine Finset.filter_congr fun u _ => ?_
  simp [List.any_eq_true]

/-- The bad set as a computable function of the board data and the center. -/
theorem computable_badSet₂ {G : π → ResGame ℕ} (hG : IsComputableGame G) :
    Computable fun y : (π × Finset ℕ × List (List (Finset ℕ))) × ℕ =>
      badSet (G y.1.1) y.1.2.1 y.1.2.2 y.2 :=
  ((computable_badSet hG).comp (Computable.pair (Computable.fst.comp Computable.fst)
    (Computable.pair (Computable.fst.comp (Computable.snd.comp Computable.fst))
      (Computable.pair (Computable.snd.comp (Computable.snd.comp Computable.fst))
        Computable.snd)))).of_eq fun _ => rfl

/-- **The first passing center is computable**: `List.find?` is the head of a computable
filter. -/
theorem computable_chooseCenter {G : π → ResGame ℕ} (hG : IsComputableGame G) :
    Computable fun x : π × Finset ℕ × List (List (Finset ℕ)) =>
      chooseCenter (G x.1) x.2.1 x.2.2 := by
  have hp : Computable fun y : (π × Finset ℕ × List (List (Finset ℕ))) × ℕ =>
      decide (32 * (badSet (G y.1.1) y.1.2.1 y.1.2.2 y.2).card ≤ (G y.1.1).N) :=
    (Primrec.nat_le.decide.to_comp.comp
      (Primrec.nat_mul.to_comp.comp (Computable.const 32)
        (computable_finsetCard.comp (computable_badSet₂ hG)))
      (hG.N.comp (Computable.fst.comp Computable.fst))).of_eq fun _ => rfl
  refine (Primrec.list_head?.to_comp.comp (Kolmogorov.computable_list_filter
    (hG.centers.comp Computable.fst) hp.to₂)).of_eq fun x => ?_
  exact List.head?_filter

/-- **The center search is computable.**  `(p, marks, tables) ↦ chooseReservoir (G p) marks
tables` is computable for a computable game family (node L16: "No real-number computation occurs
in the search"). -/
theorem chooseReservoir_computable {G : π → ResGame ℕ} (hG : IsComputableGame G) :
    Computable fun x : π × Finset ℕ × List (List (Finset ℕ)) =>
      chooseReservoir (G x.1) x.2.1 x.2.2 := by
  have hsome : Computable fun y : (π × Finset ℕ × List (List (Finset ℕ))) × ℕ =>
      (y.2, (G y.1.1).sphere y.2 \ badSet (G y.1.1) y.1.2.1 y.1.2.2 y.2) :=
    (Computable.pair Computable.snd (computable_finsetSdiff.comp (Computable.pair
      (hG.sphere.comp (Computable.fst.comp Computable.fst) Computable.snd)
      (computable_badSet₂ hG)))).of_eq fun _ => rfl
  have hnone : Computable fun x : π × Finset ℕ × List (List (Finset ℕ)) =>
      ((G x.1).fallback, (∅ : Finset ℕ)) :=
    (Computable.pair (hG.fallback.comp Computable.fst) (Computable.const ∅)).of_eq fun _ => rfl
  refine (Computable.option_casesOn (computable_chooseCenter hG) hnone hsome.to₂).of_eq
    fun x => ?_
  unfold chooseReservoir
  cases chooseCenter (G x.1) x.2.1 x.2.2 <;> rfl

/-- Membership of a finite set in a list of finite sets is decidable by a computable test. -/
theorem computable_listMemFinset :
    Computable fun x : Finset ℕ × List (Finset ℕ) => decide (x.1 ∈ x.2) := by
  have hp : Computable fun y : (Finset ℕ × List (Finset ℕ)) × Finset ℕ => decide (y.2 = y.1.1) :=
    (Kolmogorov.primrec_decideEq.to_comp.comp Computable.snd
      (Computable.fst.comp Computable.fst)).of_eq fun _ => rfl
  refine (Kolmogorov.computable_list_any Computable.snd hp.to₂).of_eq fun x => ?_
  rw [Bool.eq_iff_iff, List.any_eq_true, decide_eq_true_iff]
  constructor
  · rintro ⟨b, hb, hbx⟩
    rw [decide_eq_true_iff] at hbx
    have hb' : b = x.1 := hbx
    rw [← hb']
    exact hb
  · intro h
    exact ⟨x.1, h, by simp⟩

/-- The union of a list of finite sets is the finite set of the concatenated sorted lists. -/
theorem listUnion_eq_toFinset_flatMap (l : List (Finset ℕ)) :
    listUnion l = (l.flatMap fun Q => Q.sort (· ≤ ·)).toFinset := by
  ext u
  rw [mem_listUnion]
  simp

/-- The union of a list of finite sets is computable. -/
theorem computable_listUnion : Computable fun l : List (Finset ℕ) => listUnion l := by
  have hs : Computable fun y : List (Finset ℕ) × Finset ℕ => y.2.sort (· ≤ ·) :=
    computable_finsetSort.comp Computable.snd
  exact (computable_listToFinset.comp (computable_flatMap Computable.id hs.to₂)).of_eq
    fun l => (listUnion_eq_toFinset_flatMap l).symm

/-! ### Boards as tuples -/

/-- A board is computable from its tuple of fields (`Primrec.of_equiv_symm`). -/
theorem computable_boardMk : Computable fun x : BoardTuple => reservoirStateEquiv.symm x :=
  Primrec.of_equiv_symm.to_comp

/-- The tuple of fields of a board is computable (`Primrec.of_equiv`). -/
theorem computable_boardTuple :
    Computable fun st : ReservoirState ℕ => reservoirStateEquiv st :=
  Primrec.of_equiv.to_comp

/-- The known tables of a board, computably. -/
theorem computable_boardTables : Computable fun st : ReservoirState ℕ => st.tables :=
  (Computable.fst.comp computable_boardTuple).of_eq fun _ => rfl

/-- The stored sets of a board, computably. -/
theorem computable_boardStored : Computable fun st : ReservoirState ℕ => st.stored :=
  ((Primrec.fst.comp Primrec.snd).to_comp.comp computable_boardTuple).of_eq fun _ => rfl

/-- The marks of a board, computably. -/
theorem computable_boardMarks : Computable fun st : ReservoirState ℕ => st.marks :=
  ((Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).to_comp.comp
    computable_boardTuple).of_eq fun _ => rfl

/-- The marked cells of a board, computably. -/
theorem computable_boardMarkedCells : Computable fun st : ReservoirState ℕ => st.markedCells :=
  ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))).to_comp.comp
    computable_boardTuple).of_eq fun _ => rfl

/-- The center of a board, computably. -/
theorem computable_boardCenter : Computable fun st : ReservoirState ℕ => st.center :=
  ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
    Primrec.snd)))).to_comp.comp computable_boardTuple).of_eq fun _ => rfl

/-- The epoch record of a board, computably. -/
theorem computable_boardEpochLive : Computable fun st : ReservoirState ℕ => st.epochLive :=
  ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
    (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))).to_comp.comp
    computable_boardTuple).of_eq fun _ => rfl

/-- The live reservoir of a board, computably. -/
theorem computable_boardLive : Computable fun st : ReservoirState ℕ => st.live :=
  ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
    (Primrec.snd.comp Primrec.snd))))).to_comp.comp computable_boardTuple).of_eq fun _ => rfl

/-- The output tape of a board, computably. -/
theorem computable_boardEmitted : Computable fun st : ReservoirState ℕ => st.emitted :=
  ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))))).to_comp.comp
    computable_boardTuple).of_eq fun _ => rfl

/-- The ordinary reset counter of a board, computably. -/
theorem computable_boardOrdinaryResets :
    Computable fun st : ReservoirState ℕ => st.ordinaryResets :=
  ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
      Primrec.snd)))))))).to_comp.comp computable_boardTuple).of_eq fun _ => rfl

/-- The point charge of a board, computably. -/
theorem computable_boardPointCharge : Computable fun st : ReservoirState ℕ => st.pointCharge :=
  ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.snd.comp Primrec.snd))))))))).to_comp.comp computable_boardTuple).of_eq
    fun _ => rfl

/-- The cell charge of a board, computably. -/
theorem computable_boardCellCharge : Computable fun st : ReservoirState ℕ => st.cellCharge :=
  ((Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.snd.comp Primrec.snd))))))))).to_comp.comp computable_boardTuple).of_eq
    fun _ => rfl

/-! ### The transitions -/

/-- **A reservoir choice is computable**: through `reservoirStateEquiv` a board is a tuple, and
`reselect` replaces the center, live, epoch and tape fields by components of
`chooseReservoir_computable`. -/
theorem reselect_computable {G : π → ResGame ℕ} (hG : IsComputableGame G) :
    Computable fun x : π × ReservoirState ℕ => x.2.reselect (G x.1) := by
  have hc : Computable fun x : π × ReservoirState ℕ =>
      chooseReservoir (G x.1) x.2.marks x.2.tables :=
    ((chooseReservoir_computable hG).comp (Computable.pair Computable.fst (Computable.pair
      (computable_boardMarks.comp Computable.snd)
      (computable_boardTables.comp Computable.snd)))).of_eq fun _ => rfl
  have htuple : Computable fun x : π × ReservoirState ℕ =>
      ((x.2.tables, x.2.stored, x.2.marks, x.2.markedCells,
        (chooseReservoir (G x.1) x.2.marks x.2.tables).1,
        (chooseReservoir (G x.1) x.2.marks x.2.tables).2,
        (chooseReservoir (G x.1) x.2.marks x.2.tables).2,
        (chooseReservoir (G x.1) x.2.marks x.2.tables).1 :: x.2.emitted,
        x.2.ordinaryResets, x.2.pointCharge, x.2.cellCharge) : BoardTuple) :=
    ((computable_boardTables.comp Computable.snd).pair
      ((computable_boardStored.comp Computable.snd).pair
      ((computable_boardMarks.comp Computable.snd).pair
      ((computable_boardMarkedCells.comp Computable.snd).pair
      ((Computable.fst.comp hc).pair ((Computable.snd.comp hc).pair
      ((Computable.snd.comp hc).pair
      ((Computable.list_cons.comp (Computable.fst.comp hc)
        (computable_boardEmitted.comp Computable.snd)).pair
      ((computable_boardOrdinaryResets.comp Computable.snd).pair
      ((computable_boardPointCharge.comp Computable.snd).pair
      (computable_boardCellCharge.comp Computable.snd))))))))))).of_eq fun _ => rfl
  exact (computable_boardMk.comp htuple).of_eq fun _ => rfl

/-- **The ordinary reset test is computable**: `Computable.cond` on `8 |W| < 7 N`, with
`reselect_computable` and the counter update in the reset branch. -/
theorem ordinaryCheck_computable {G : π → ResGame ℕ} (hG : IsComputableGame G) :
    Computable fun x : π × ReservoirState ℕ => x.2.ordinaryCheck (G x.1) := by
  have hr := reselect_computable hG
  have htest : Computable fun x : π × ReservoirState ℕ =>
      decide (8 * x.2.live.card < 7 * (G x.1).N) :=
    (Primrec.nat_lt.decide.to_comp.comp (Primrec.nat_mul.to_comp.comp (Computable.const 8)
      (computable_finsetCard.comp (computable_boardLive.comp Computable.snd)))
      (Primrec.nat_mul.to_comp.comp (Computable.const 7) (hG.N.comp Computable.fst))).of_eq
      fun _ => rfl
  have htuple : Computable fun x : π × ReservoirState ℕ =>
      (((x.2.reselect (G x.1)).tables, (x.2.reselect (G x.1)).stored,
        (x.2.reselect (G x.1)).marks, (x.2.reselect (G x.1)).markedCells,
        (x.2.reselect (G x.1)).center, (x.2.reselect (G x.1)).live,
        (x.2.reselect (G x.1)).epochLive, (x.2.reselect (G x.1)).emitted,
        x.2.ordinaryResets + 1, (x.2.reselect (G x.1)).pointCharge,
        (x.2.reselect (G x.1)).cellCharge) : BoardTuple) :=
    ((computable_boardTables.comp hr).pair ((computable_boardStored.comp hr).pair
      ((computable_boardMarks.comp hr).pair ((computable_boardMarkedCells.comp hr).pair
      ((computable_boardCenter.comp hr).pair ((computable_boardLive.comp hr).pair
      ((computable_boardEpochLive.comp hr).pair ((computable_boardEmitted.comp hr).pair
      ((Computable.succ.comp (computable_boardOrdinaryResets.comp Computable.snd)).pair
      ((computable_boardPointCharge.comp hr).pair
      (computable_boardCellCharge.comp hr))))))))))).of_eq fun _ => rfl
  have hreset : Computable fun x : π × ReservoirState ℕ =>
      ({ x.2.reselect (G x.1) with ordinaryResets := x.2.ordinaryResets + 1 } :
        ReservoirState ℕ) :=
    (computable_boardMk.comp htuple).of_eq fun _ => rfl
  refine (Computable.cond htest hreset Computable.snd).of_eq fun x => ?_
  unfold ReservoirState.ordinaryCheck
  by_cases h : 8 * x.2.live.card < 7 * (G x.1).N <;> simp [h]

/-- **A point event is computable**: a record update by `insert`, `erase` and the charge
test, then the reset test. -/
theorem pointStep_computable {G : π → ResGame ℕ} (hG : IsComputableGame G) :
    Computable fun x : π × ReservoirState ℕ × ℕ => x.2.1.pointStep (G x.1) x.2.2 := by
  have hst : Computable fun x : π × ReservoirState ℕ × ℕ => x.2.1 :=
    Computable.fst.comp Computable.snd
  have hu : Computable fun x : π × ReservoirState ℕ × ℕ => x.2.2 :=
    Computable.snd.comp Computable.snd
  have hmem : Computable fun x : π × ReservoirState ℕ × ℕ => decide (x.2.2 ∈ x.2.1.live) :=
    (computable_finsetMem.comp (hu.pair (computable_boardLive.comp hst))).of_eq fun _ => rfl
  have hcharge : Computable fun x : π × ReservoirState ℕ × ℕ =>
      x.2.1.pointCharge + (if x.2.2 ∈ x.2.1.live then 1 else 0) :=
    (Primrec.nat_add.to_comp.comp (computable_boardPointCharge.comp hst)
      (Computable.cond hmem (Computable.const 1) (Computable.const 0))).of_eq fun x => by
        by_cases h : x.2.2 ∈ x.2.1.live <;> simp [h]
  have htuple : Computable fun x : π × ReservoirState ℕ × ℕ =>
      ((x.2.1.tables, x.2.1.stored, insert x.2.2 x.2.1.marks, x.2.1.markedCells, x.2.1.center,
        x.2.1.live.erase x.2.2, x.2.1.epochLive, x.2.1.emitted, x.2.1.ordinaryResets,
        x.2.1.pointCharge + (if x.2.2 ∈ x.2.1.live then 1 else 0), x.2.1.cellCharge) :
        BoardTuple) :=
    ((computable_boardTables.comp hst).pair ((computable_boardStored.comp hst).pair
      ((computable_finsetInsert.comp (hu.pair (computable_boardMarks.comp hst))).pair
      ((computable_boardMarkedCells.comp hst).pair ((computable_boardCenter.comp hst).pair
      ((computable_finsetErase.comp ((computable_boardLive.comp hst).pair hu)).pair
      ((computable_boardEpochLive.comp hst).pair ((computable_boardEmitted.comp hst).pair
      ((computable_boardOrdinaryResets.comp hst).pair (hcharge.pair
      (computable_boardCellCharge.comp hst))))))))))).of_eq fun _ => rfl
  exact ((ordinaryCheck_computable hG).comp (Computable.fst.pair
    (computable_boardMk.comp htuple))).of_eq fun _ => rfl

/-- **A set event is computable**: `Computable.cond` on the marking test, record updates, then
the reset test. -/
theorem setStep_computable {G : π → ResGame ℕ} (hG : IsComputableGame G) :
    Computable fun x : π × ReservoirState ℕ × (Finset ℕ × ℕ) =>
      x.2.1.setStep (G x.1) x.2.2.1 x.2.2.2 := by
  have hst : Computable fun x : π × ReservoirState ℕ × (Finset ℕ × ℕ) => x.2.1 :=
    Computable.fst.comp Computable.snd
  have hQ : Computable fun x : π × ReservoirState ℕ × (Finset ℕ × ℕ) => x.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hi : Computable fun x : π × ReservoirState ℕ × (Finset ℕ × ℕ) => x.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp Computable.snd)
  have hknown : Computable fun x : π × ReservoirState ℕ × (Finset ℕ × ℕ) =>
      x.2.1.tables.any fun P => decide (x.2.2.1 ∈ P) := by
    have hp : Computable fun w : (π × ReservoirState ℕ × (Finset ℕ × ℕ)) × List (Finset ℕ) =>
        decide (w.1.2.2.1 ∈ w.2) :=
      (computable_listMemFinset.comp ((hQ.comp Computable.fst).pair Computable.snd)).of_eq
        fun _ => rfl
    exact (Kolmogorov.computable_list_any (computable_boardTables.comp hst) hp.to₂).of_eq
      fun _ => rfl
  have hmarked : Computable fun x : π × ReservoirState ℕ × (Finset ℕ × ℕ) =>
      decide (x.2.2.1 ∈ x.2.1.markedCells) :=
    (computable_listMemFinset.comp (hQ.pair (computable_boardMarkedCells.comp hst))).of_eq
      fun _ => rfl
  have htest : Computable fun x : π × ReservoirState ℕ × (Finset ℕ × ℕ) =>
      decide ((∃ P ∈ x.2.1.tables, x.2.2.1 ∈ P) ∧ x.2.2.1 ∉ x.2.1.markedCells) := by
    refine (Primrec.and.to_comp.comp hknown (Primrec.not.to_comp.comp hmarked)).of_eq
      fun x => ?_
    rw [Bool.eq_iff_iff]
    simp [List.any_eq_true]
  have hA : Computable fun x : π × ReservoirState ℕ × (Finset ℕ × ℕ) =>
      ({ x.2.1 with
        stored := (x.2.2.1, x.2.2.2) :: x.2.1.stored
        markedCells := x.2.2.1 :: x.2.1.markedCells
        marks := x.2.1.marks ∪ x.2.2.1
        live := x.2.1.live \ x.2.2.1
        cellCharge := x.2.1.cellCharge + (x.2.1.live ∩ x.2.2.1).card } : ReservoirState ℕ) := by
    have htuple : Computable fun x : π × ReservoirState ℕ × (Finset ℕ × ℕ) =>
        ((x.2.1.tables, (x.2.2.1, x.2.2.2) :: x.2.1.stored, x.2.1.marks ∪ x.2.2.1,
          x.2.2.1 :: x.2.1.markedCells, x.2.1.center, x.2.1.live \ x.2.2.1, x.2.1.epochLive,
          x.2.1.emitted, x.2.1.ordinaryResets, x.2.1.pointCharge,
          x.2.1.cellCharge + (x.2.1.live ∩ x.2.2.1).card) : BoardTuple) :=
      ((computable_boardTables.comp hst).pair
        ((Computable.list_cons.comp (hQ.pair hi) (computable_boardStored.comp hst)).pair
        ((computable_finsetUnion.comp ((computable_boardMarks.comp hst).pair hQ)).pair
        ((Computable.list_cons.comp hQ (computable_boardMarkedCells.comp hst)).pair
        ((computable_boardCenter.comp hst).pair
        ((computable_finsetSdiff.comp ((computable_boardLive.comp hst).pair hQ)).pair
        ((computable_boardEpochLive.comp hst).pair ((computable_boardEmitted.comp hst).pair
        ((computable_boardOrdinaryResets.comp hst).pair
        ((computable_boardPointCharge.comp hst).pair
        (Primrec.nat_add.to_comp.comp (computable_boardCellCharge.comp hst)
          (computable_finsetCard.comp (computable_finsetInter.comp
            ((computable_boardLive.comp hst).pair hQ)))))))))))))).of_eq fun _ => rfl
    exact (computable_boardMk.comp htuple).of_eq fun _ => rfl
  have hB : Computable fun x : π × ReservoirState ℕ × (Finset ℕ × ℕ) =>
      ({ x.2.1 with stored := (x.2.2.1, x.2.2.2) :: x.2.1.stored } : ReservoirState ℕ) := by
    have htuple : Computable fun x : π × ReservoirState ℕ × (Finset ℕ × ℕ) =>
        ((x.2.1.tables, (x.2.2.1, x.2.2.2) :: x.2.1.stored, x.2.1.marks, x.2.1.markedCells,
          x.2.1.center, x.2.1.live, x.2.1.epochLive, x.2.1.emitted, x.2.1.ordinaryResets,
          x.2.1.pointCharge, x.2.1.cellCharge) : BoardTuple) :=
      ((computable_boardTables.comp hst).pair
        ((Computable.list_cons.comp (hQ.pair hi) (computable_boardStored.comp hst)).pair
        ((computable_boardMarks.comp hst).pair ((computable_boardMarkedCells.comp hst).pair
        ((computable_boardCenter.comp hst).pair ((computable_boardLive.comp hst).pair
        ((computable_boardEpochLive.comp hst).pair ((computable_boardEmitted.comp hst).pair
        ((computable_boardOrdinaryResets.comp hst).pair
        ((computable_boardPointCharge.comp hst).pair
        (computable_boardCellCharge.comp hst))))))))))).of_eq fun _ => rfl
    exact (computable_boardMk.comp htuple).of_eq fun _ => rfl
  have hoc := ordinaryCheck_computable hG
  refine (Computable.cond htest (hoc.comp (Computable.fst.pair hA))
    (hoc.comp (Computable.fst.pair hB))).of_eq fun x => ?_
  unfold ReservoirState.setStep
  split_ifs with h
  · rw [decide_eq_true h]
    rfl
  · rw [decide_eq_false h]
    rfl

/-- **A table event is computable**: the activated cells are a computable list filter, their
union is computable, then the record update and the forced choice. -/
theorem tableStep_computable {G : π → ResGame ℕ} (hG : IsComputableGame G) :
    Computable fun x : π × ReservoirState ℕ × List (Finset ℕ) => x.2.1.tableStep (G x.1) x.2.2 := by
  have hst : Computable fun x : π × ReservoirState ℕ × List (Finset ℕ) => x.2.1 :=
    Computable.fst.comp Computable.snd
  have hP : Computable fun x : π × ReservoirState ℕ × List (Finset ℕ) => x.2.2 :=
    Computable.snd.comp Computable.snd
  have hact : Computable fun x : π × ReservoirState ℕ × List (Finset ℕ) =>
      x.2.1.activated x.2.2 := by
    have hmap : Computable fun x : π × ReservoirState ℕ × List (Finset ℕ) =>
        x.2.1.stored.map Prod.fst :=
      ((Primrec.list_map Primrec.id (Primrec.fst.comp Primrec.snd).to₂).to_comp.comp
        (computable_boardStored.comp hst)).of_eq fun _ => rfl
    have hp : Computable fun w : (π × ReservoirState ℕ × List (Finset ℕ)) × Finset ℕ =>
        decide (w.2 ∈ w.1.2.2) :=
      (computable_listMemFinset.comp (Computable.snd.pair (hP.comp Computable.fst))).of_eq
        fun _ => rfl
    exact (Kolmogorov.computable_list_filter hmap hp.to₂).of_eq fun _ => rfl
  have hU : Computable fun x : π × ReservoirState ℕ × List (Finset ℕ) =>
      listUnion (x.2.1.activated x.2.2) :=
    computable_listUnion.comp hact
  have htuple : Computable fun x : π × ReservoirState ℕ × List (Finset ℕ) =>
      ((x.2.2 :: x.2.1.tables, x.2.1.stored, x.2.1.marks ∪ listUnion (x.2.1.activated x.2.2),
        x.2.1.activated x.2.2 ++ x.2.1.markedCells, x.2.1.center,
        x.2.1.live \ listUnion (x.2.1.activated x.2.2), x.2.1.epochLive, x.2.1.emitted,
        x.2.1.ordinaryResets, x.2.1.pointCharge, x.2.1.cellCharge) : BoardTuple) :=
    ((Computable.list_cons.comp hP (computable_boardTables.comp hst)).pair
      ((computable_boardStored.comp hst).pair
      ((computable_finsetUnion.comp ((computable_boardMarks.comp hst).pair hU)).pair
      ((Computable.list_append.comp hact (computable_boardMarkedCells.comp hst)).pair
      ((computable_boardCenter.comp hst).pair
      ((computable_finsetSdiff.comp ((computable_boardLive.comp hst).pair hU)).pair
      ((computable_boardEpochLive.comp hst).pair ((computable_boardEmitted.comp hst).pair
      ((computable_boardOrdinaryResets.comp hst).pair
      ((computable_boardPointCharge.comp hst).pair
      (computable_boardCellCharge.comp hst))))))))))).of_eq fun _ => rfl
  exact ((reselect_computable hG).comp (Computable.fst.pair
    (computable_boardMk.comp htuple))).of_eq fun _ => rfl

/-- **The transition function is computable.**  `(p, st, e) ↦ reservoirTransition (G p) st e`
is computable for a computable game family (node L17): case analysis on the event through
`resEventEquiv`. -/
theorem reservoirTransition_computable {G : π → ResGame ℕ} (hG : IsComputableGame G) :
    Computable fun x : π × ReservoirState ℕ × ResEvent ℕ =>
      reservoirTransition (G x.1) x.2.1 x.2.2 := by
  have he : Computable fun x : π × ReservoirState ℕ × ResEvent ℕ => resEventEquiv x.2.2 :=
    ((Primrec.of_equiv (e := resEventEquiv)).to_comp.comp
      (Computable.snd.comp Computable.snd)).of_eq fun _ => rfl
  have hpt : Computable fun y : (π × ReservoirState ℕ × ResEvent ℕ) × ℕ =>
      y.1.2.1.pointStep (G y.1.1) y.2 :=
    ((pointStep_computable hG).comp (Computable.pair (Computable.fst.comp Computable.fst)
      (Computable.pair (Computable.fst.comp (Computable.snd.comp Computable.fst))
        Computable.snd))).of_eq fun _ => rfl
  have hset : Computable fun z : ((π × ReservoirState ℕ × ResEvent ℕ) ×
      ((Finset ℕ × ℕ) ⊕ List (Finset ℕ))) × (Finset ℕ × ℕ) =>
      z.1.1.2.1.setStep (G z.1.1.1) z.2.1 z.2.2 :=
    ((setStep_computable hG).comp (Computable.pair (Computable.fst.comp (Computable.fst.comp
      Computable.fst)) (Computable.pair (Computable.fst.comp (Computable.snd.comp
        (Computable.fst.comp Computable.fst))) Computable.snd))).of_eq fun _ => rfl
  have htab : Computable fun z : ((π × ReservoirState ℕ × ResEvent ℕ) ×
      ((Finset ℕ × ℕ) ⊕ List (Finset ℕ))) × List (Finset ℕ) =>
      z.1.1.2.1.tableStep (G z.1.1.1) z.2 :=
    ((tableStep_computable hG).comp (Computable.pair (Computable.fst.comp (Computable.fst.comp
      Computable.fst)) (Computable.pair (Computable.fst.comp (Computable.snd.comp
        (Computable.fst.comp Computable.fst))) Computable.snd))).of_eq fun _ => rfl
  have hrest : Computable fun y : (π × ReservoirState ℕ × ResEvent ℕ) ×
      ((Finset ℕ × ℕ) ⊕ List (Finset ℕ)) =>
      (Sum.casesOn y.2 (fun Qi => y.1.2.1.setStep (G y.1.1) Qi.1 Qi.2)
        (fun P => y.1.2.1.tableStep (G y.1.1) P) : ReservoirState ℕ) :=
    (Computable.sumCasesOn Computable.snd hset.to₂ htab.to₂).of_eq fun _ => rfl
  refine (Computable.sumCasesOn he hpt.to₂ hrest.to₂).of_eq fun x => ?_
  rcases x with ⟨p, st, e⟩
  cases e <;> rfl

/-- **The empty board is computable**: a constant record except for the fallback center. -/
theorem emptyState_computable {G : π → ResGame ℕ} (hG : IsComputableGame G) :
    Computable fun p => emptyState (G p) := by
  have htuple : Computable fun p : π =>
      ((([] : List (List (Finset ℕ))), ([] : List (Finset ℕ × ℕ)), (∅ : Finset ℕ),
        ([] : List (Finset ℕ)), (G p).fallback, (∅ : Finset ℕ), (∅ : Finset ℕ), ([] : List ℕ),
        (0 : ℕ), (0 : ℕ), (0 : ℕ)) : BoardTuple) :=
    ((Computable.const _).pair ((Computable.const _).pair ((Computable.const _).pair
      ((Computable.const _).pair (hG.fallback.pair ((Computable.const _).pair
      ((Computable.const _).pair ((Computable.const _).pair ((Computable.const _).pair
      ((Computable.const _).pair (Computable.const _))))))))))).of_eq fun _ => rfl
  exact (computable_boardMk.comp htuple).of_eq fun _ => rfl

/-- **The initial state is computable**: the empty board followed by the initial choice. -/
theorem initState_computable {G : π → ResGame ℕ} (hG : IsComputableGame G) :
    Computable fun p => initState (G p) :=
  ((reselect_computable hG).comp (Computable.pair Computable.id
    (emptyState_computable hG))).of_eq fun _ => rfl

/-- **Reading the output tape is computable**: `st ↦ st.emitted.reverse`. -/
theorem emittedReverse_computable :
    Computable fun st : ReservoirState ℕ => st.emitted.reverse := by
  have he : Primrec fun st : ReservoirState ℕ => reservoirStateEquiv st :=
    Primrec.of_equiv
  have hproj : Primrec fun x : BoardTuple => x.2.2.2.2.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))))
  exact (Primrec.list_reverse.comp (hproj.comp he)).to_comp.of_eq fun _ => rfl

/-- **The game run is computable** (node L17, effectivity): `(p, evs) ↦ run (G p) evs`. -/
theorem run_computable {G : π → ResGame ℕ} (hG : IsComputableGame G) :
    Computable fun x : π × List (ResEvent ℕ) => run (G x.1) x.2 := by
  have hstep : Computable₂ fun (x : π × List (ResEvent ℕ)) (y : ReservoirState ℕ × ResEvent ℕ) =>
      reservoirTransition (G x.1) y.1 y.2 :=
    ((reservoirTransition_computable hG).comp
      (Computable.pair (Computable.fst.comp Computable.fst) Computable.snd)).to₂
  exact (Kolmogorov.computable_list_foldl Computable.snd
    ((initState_computable hG).comp Computable.fst) hstep).of_eq fun _ => rfl

/-! ### The event stream -/

/-- The first-availability test `firstAt` is computable along a computable stage-indexed
evaluation. -/
theorem computable_firstAt {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → ℕ → Option β} (hf : Computable₂ f) {s : α → ℕ} (hs : Computable s) :
    Computable fun a => firstAt (f a) (s a) := by
  have h1 : Computable fun a => (f a (s a)).isSome :=
    (Primrec.option_isSome.to_comp.comp (hf.comp Computable.id hs)).of_eq fun _ => rfl
  have hin : Computable fun w : α × ℕ => (f w.1 w.2).isSome :=
    (Primrec.option_isSome.to_comp.comp hf).of_eq fun _ => rfl
  have h2 : Computable fun a => (List.range (s a)).any fun t => (f a t).isSome :=
    (Kolmogorov.computable_list_any (Primrec.list_range.to_comp.comp hs) hin.to₂).of_eq
      fun _ => rfl
  refine (Primrec.and.to_comp.comp h1 (Primrec.not.to_comp.comp h2)).of_eq fun a => ?_
  unfold firstAt
  congr 1
  rw [Bool.eq_iff_iff]
  simp [List.all_eq_true]

/-- A point event is computable from its point (`resEventEquiv`). -/
theorem computable_pointEvent : Computable fun u : ℕ => (ResEvent.point u : ResEvent ℕ) :=
  ((Primrec.of_equiv_symm (e := resEventEquiv)).to_comp.comp
    Primrec.sumInl.to_comp).of_eq fun _ => rfl

/-- Membership in the cube of a computable game is computable. -/
theorem computable_memCube {G : π → ResGame ℕ} (hG : IsComputableGame G) :
    Computable fun x : π × ℕ => decide (x.2 ∈ (G x.1).cube) :=
  (computable_finsetMem.comp (Computable.snd.pair
    (computable_listToFinset.comp (hG.centers.comp Computable.fst)))).of_eq fun _ => rfl


/-- The eligibility test of a set event is computable. -/
theorem computable_setEligible {G : π → ResGame ℕ} (hG : IsComputableGame G) {K τ : π → ℕ}
    (hK : Computable K) (hτ : Computable τ) :
    Computable fun x : π × Finset ℕ × ℕ =>
      decide (SetEligible (G x.1) (K x.1) (τ x.1) x.2.1 x.2.2) := by
  have hpow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) := Primrec₂.unpaired'.1 Nat.Primrec.pow
  have hQ : Computable fun x : π × Finset ℕ × ℕ => x.2.1 := Computable.fst.comp Computable.snd
  have hi : Computable fun x : π × Finset ℕ × ℕ => x.2.2 := Computable.snd.comp Computable.snd
  have hKτ : Computable fun x : π × Finset ℕ × ℕ => K x.1 + τ x.1 :=
    (Primrec.nat_add.to_comp.comp (hK.comp Computable.fst) (hτ.comp Computable.fst)).of_eq
      fun _ => rfl
  have h1 : Computable fun x : π × Finset ℕ × ℕ => decide (x.2.1 ⊆ (G x.1).cube) :=
    (computable_finsetSubset.comp (hQ.pair (computable_listToFinset.comp
      (hG.centers.comp Computable.fst)))).of_eq fun _ => rfl
  have h2 : Computable fun x : π × Finset ℕ × ℕ => decide (x.2.2 ≤ K x.1 + τ x.1) :=
    (Primrec.nat_le.decide.to_comp.comp hi hKτ).of_eq fun _ => rfl
  have h3 : Computable fun x : π × Finset ℕ × ℕ => decide (2 ^ (G x.1).ell ≤ x.2.1.card) :=
    (Primrec.nat_le.decide.to_comp.comp (hpow.to_comp.comp (Computable.const 2)
      (hG.ell.comp Computable.fst)) (computable_finsetCard.comp hQ)).of_eq fun _ => rfl
  have h4 : Computable fun x : π × Finset ℕ × ℕ =>
      decide (x.2.1.card * 2 ^ x.2.2 ≤ 2 ^ (K x.1 + τ x.1)) :=
    (Primrec.nat_le.decide.to_comp.comp (Primrec.nat_mul.to_comp.comp
      (computable_finsetCard.comp hQ) (hpow.to_comp.comp (Computable.const 2) hi))
      (hpow.to_comp.comp (Computable.const 2) hKτ)).of_eq fun _ => rfl
  refine (Primrec.and.to_comp.comp h1 (Primrec.and.to_comp.comp h2
    (Primrec.and.to_comp.comp h3 h4))).of_eq fun x => ?_
  rw [Bool.eq_iff_iff, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_iff,
    decide_eq_true_iff, decide_eq_true_iff, decide_eq_true_iff, decide_eq_true_iff]
  rfl

/-- A set event is computable from its set and certificate length (`resEventEquiv`). -/
theorem computable_setEvent :
    Computable fun x : Finset ℕ × ℕ => (ResEvent.set x.1 x.2 : ResEvent ℕ) :=
  ((Primrec.of_equiv_symm (e := resEventEquiv)).to_comp.comp
    (Primrec.sumInr.comp Primrec.sumInl).to_comp).of_eq fun _ => rfl

/-- **Point events of one stage are computable**: an `Option.casesOn` of the evaluator with the
first-availability and cube-membership tests. -/
theorem ptEventAt_computable {G : π → ResGame ℕ} (hG : IsComputableGame G)
    {src : π → EventSources ℕ} (hsrc : IsComputableSources src) :
    Computable₂ fun (x : π × ℕ) (c : ℕ) => ptEventAt (G x.1) (src x.1) x.2 c := by
  have hev : Computable fun y : (π × ℕ) × ℕ => (src y.1.1).ptEval y.2 y.1.2 :=
    (hsrc.ptEval.comp ((Computable.fst.comp Computable.fst).pair
      (Computable.snd.pair (Computable.snd.comp Computable.fst)))).of_eq fun _ => rfl
  have hev₂ : Computable fun w : ((π × ℕ) × ℕ) × ℕ => (src w.1.1.1).ptEval w.1.2 w.2 :=
    (hsrc.ptEval.comp ((Computable.fst.comp (Computable.fst.comp Computable.fst)).pair
      ((Computable.snd.comp Computable.fst).pair Computable.snd))).of_eq fun _ => rfl
  have hfirst : Computable fun y : (π × ℕ) × ℕ => firstAt ((src y.1.1).ptEval y.2) y.1.2 :=
    computable_firstAt hev₂.to₂ (Computable.snd.comp Computable.fst)
  have hsome : Computable fun w : ((π × ℕ) × ℕ) × ℕ =>
      cond (firstAt ((src w.1.1.1).ptEval w.1.2) w.1.1.2 && decide (w.2 ∈ (G w.1.1.1).cube))
        [ResEvent.point w.2] [] :=
    (Computable.cond (Primrec.and.to_comp.comp (hfirst.comp Computable.fst)
      (computable_memCube hG |>.comp ((Computable.fst.comp (Computable.fst.comp
        Computable.fst)).pair Computable.snd)))
      (Computable.list_cons.comp (computable_pointEvent.comp Computable.snd)
        (Computable.const [])) (Computable.const [])).of_eq fun _ => rfl
  refine (Computable.option_casesOn hev (Computable.const []) hsome.to₂).to₂.of_eq ?_
  intro y
  simp only [ptEventAt]
  cases (src y.1.1).ptEval y.2 y.1.2 with
  | none => rfl
  | some u =>
    by_cases h : firstAt ((src y.1.1).ptEval y.2) y.1.2 = true ∧ u ∈ (G y.1.1).cube <;>
      simp [h]

/-- **Set events of one stage are computable**: an `Option.casesOn` of the evaluator with the
first-availability and eligibility tests. -/
theorem setEventAt_computable {G : π → ResGame ℕ} (hG : IsComputableGame G)
    {src : π → EventSources ℕ} (hsrc : IsComputableSources src) {K τ : π → ℕ}
    (hK : Computable K) (hτ : Computable τ) :
    Computable₂ fun (x : π × ℕ) (c : ℕ) => setEventAt (G x.1) (K x.1) (τ x.1) (src x.1) x.2 c := by
  have hev : Computable fun y : (π × ℕ) × ℕ => (src y.1.1).setEval y.2 y.1.2 :=
    (hsrc.setEval.comp ((Computable.fst.comp Computable.fst).pair
      (Computable.snd.pair (Computable.snd.comp Computable.fst)))).of_eq fun _ => rfl
  have hev₂ : Computable fun w : ((π × ℕ) × ℕ) × ℕ => (src w.1.1.1).setEval w.1.2 w.2 :=
    (hsrc.setEval.comp ((Computable.fst.comp (Computable.fst.comp Computable.fst)).pair
      ((Computable.snd.comp Computable.fst).pair Computable.snd))).of_eq fun _ => rfl
  have hfirst : Computable fun y : (π × ℕ) × ℕ => firstAt ((src y.1.1).setEval y.2) y.1.2 :=
    computable_firstAt hev₂.to₂ (Computable.snd.comp Computable.fst)
  have hcost : Computable fun y : (π × ℕ) × ℕ => (src y.1.1).setCost y.2 :=
    (hsrc.setCost.comp (Computable.fst.comp Computable.fst) Computable.snd).of_eq fun _ => rfl
  have helig : Computable fun w : ((π × ℕ) × ℕ) × Finset ℕ =>
      decide (SetEligible (G w.1.1.1) (K w.1.1.1) (τ w.1.1.1) w.2 ((src w.1.1.1).setCost w.1.2)) :=
    ((computable_setEligible hG hK hτ).comp ((Computable.fst.comp (Computable.fst.comp
      Computable.fst)).pair (Computable.snd.pair (hcost.comp Computable.fst)))).of_eq
      fun _ => rfl
  have hsome : Computable fun w : ((π × ℕ) × ℕ) × Finset ℕ =>
      cond (firstAt ((src w.1.1.1).setEval w.1.2) w.1.1.2 &&
          decide (SetEligible (G w.1.1.1) (K w.1.1.1) (τ w.1.1.1) w.2
            ((src w.1.1.1).setCost w.1.2)))
        [ResEvent.set w.2 ((src w.1.1.1).setCost w.1.2)] [] :=
    (Computable.cond (Primrec.and.to_comp.comp (hfirst.comp Computable.fst) helig)
      (Computable.list_cons.comp (computable_setEvent.comp
        (Computable.snd.pair (hcost.comp Computable.fst))) (Computable.const []))
      (Computable.const [])).of_eq fun _ => rfl
  refine (Computable.option_casesOn hev (Computable.const []) hsome.to₂).to₂.of_eq ?_
  intro y
  simp only [setEventAt]
  cases (src y.1.1).setEval y.2 y.1.2 with
  | none => rfl
  | some Q =>
    by_cases h : firstAt ((src y.1.1).setEval y.2) y.1.2 = true ∧
        SetEligible (G y.1.1) (K y.1.1) (τ y.1.1) Q ((src y.1.1).setCost y.2) <;>
      simp [h]

/-- `List.all` along a computable list with a computable predicate is computable. -/
theorem computable_list_all {α β : Type*} [Primcodable α] [Primcodable β] [Inhabited β]
    {f : α → List β} {p : α → β → Bool} (hf : Computable f) (hp : Computable₂ p) :
    Computable fun a => (f a).all (p a) := by
  have hnp : Computable fun w : α × β => !p w.1 w.2 :=
    (Primrec.not.to_comp.comp hp).of_eq fun _ => rfl
  refine (Primrec.not.to_comp.comp (Kolmogorov.computable_list_any hf hnp.to₂)).of_eq
    fun a => ?_
  rw [Bool.eq_iff_iff]
  simp [List.all_eq_true]

/-- A table event is computable from its list of cells (`resEventEquiv`). -/
theorem computable_tableEvent :
    Computable fun P : List (Finset ℕ) => (ResEvent.table P : ResEvent ℕ) :=
  ((Primrec.of_equiv_symm (e := resEventEquiv)).to_comp.comp
    (Primrec.sumInr.comp Primrec.sumInr).to_comp).of_eq fun _ => rfl

/-- `List.map` along a computable list with a computable function is computable. -/
theorem computable_list_map' {α β γ : Type*} [Primcodable α] [Primcodable β] [Inhabited β]
    [Primcodable γ] {f : α → List β} {g : α → β → γ} (hf : Computable f)
    (hg : Computable₂ g) : Computable fun a => (f a).map (g a) := by
  have hs : Computable fun w : α × β => [g w.1 w.2] :=
    (Computable.list_cons.comp hg (Computable.const [])).of_eq fun _ => rfl
  refine (computable_flatMap hf hs.to₂).of_eq fun a => ?_
  induction f a with
  | nil => rfl
  | cons b l ih => simp only [List.flatMap_cons, List.map_cons] at ih ⊢; rw [← ih]; rfl

/-- **Table events of one stage are computable**: the completion test, its first stage, the
finite partition-map test and the list of cells are computable. -/
theorem tabEventAt_computable {G : π → ResGame ℕ} (hG : IsComputableGame G)
    {src : π → EventSources ℕ} (hsrc : IsComputableSources src) :
    Computable₂ fun (x : π × ℕ) (c : ℕ) => tabEventAt (G x.1) (src x.1) x.2 c := by
  have hp : Computable fun y : (π × ℕ) × ℕ => y.1.1 := Computable.fst.comp Computable.fst
  have hdone : Computable fun w : ((π × ℕ) × ℕ) × ℕ =>
      tableDone (G w.1.1.1) (src w.1.1.1) w.1.2 w.2 := by
    have hq : Computable fun v : (((π × ℕ) × ℕ) × ℕ) × ℕ =>
        ((src v.1.1.1.1).tabEval v.1.1.2 v.2 v.1.2).isSome :=
      (Primrec.option_isSome.to_comp.comp (hsrc.tabEval.comp
        ((Computable.fst.comp (Computable.fst.comp (Computable.fst.comp Computable.fst))).pair
        ((Computable.snd.comp (Computable.fst.comp Computable.fst)).pair
        (Computable.snd.pair (Computable.snd.comp Computable.fst)))))).of_eq fun _ => rfl
    exact (computable_list_all (hG.centers.comp (Computable.fst.comp (Computable.fst.comp
      Computable.fst))) hq.to₂).of_eq fun _ => rfl
  have hopt : Computable fun w : ((π × ℕ) × ℕ) × ℕ =>
      (if tableDone (G w.1.1.1) (src w.1.1.1) w.1.2 w.2 then some () else none : Option Unit) :=
    (Computable.cond hdone (Computable.const (some ())) (Computable.const none)).of_eq
      fun w => by cases tableDone (G w.1.1.1) (src w.1.1.1) w.1.2 w.2 <;> rfl
  have hfirst : Computable fun y : (π × ℕ) × ℕ =>
      firstAt (fun t => if tableDone (G y.1.1) (src y.1.1) y.2 t then some () else none) y.1.2 :=
    (computable_firstAt hopt.to₂ (Computable.snd.comp Computable.fst)).of_eq fun _ => rfl
  have hval : Computable fun v : ((π × ℕ) × ℕ) × ℕ =>
      (src v.1.1.1).tabEval v.1.2 v.2 v.1.1.2 :=
    (hsrc.tabEval.comp ((Computable.fst.comp (Computable.fst.comp Computable.fst)).pair
      ((Computable.snd.comp Computable.fst).pair (Computable.snd.pair
        (Computable.snd.comp (Computable.fst.comp Computable.fst)))))).of_eq fun _ => rfl
  have hcheck : Computable fun z : (((π × ℕ) × ℕ) × ℕ) × Finset ℕ =>
      decide (z.2 ⊆ (G z.1.1.1.1).cube ∧ z.1.2 ∈ z.2 ∧
        ∀ v ∈ z.2, (src z.1.1.1.1).tabEval z.1.1.2 v z.1.1.1.2 = some z.2) := by
    have hsub : Computable fun z : (((π × ℕ) × ℕ) × ℕ) × Finset ℕ =>
        decide (z.2 ⊆ (G z.1.1.1.1).cube) :=
      (computable_finsetSubset.comp (Computable.snd.pair (computable_listToFinset.comp
        (hG.centers.comp (Computable.fst.comp (Computable.fst.comp (Computable.fst.comp
          Computable.fst))))))).of_eq fun _ => rfl
    have hmem : Computable fun z : (((π × ℕ) × ℕ) × ℕ) × Finset ℕ => decide (z.1.2 ∈ z.2) :=
      (computable_finsetMem.comp ((Computable.snd.comp Computable.fst).pair
        Computable.snd)).of_eq fun _ => rfl
    have hall : Computable fun z : (((π × ℕ) × ℕ) × ℕ) × Finset ℕ =>
        (z.2.sort (· ≤ ·)).all fun v =>
          decide ((src z.1.1.1.1).tabEval z.1.1.2 v z.1.1.1.2 = some z.2) := by
      have hq : Computable fun r : ((((π × ℕ) × ℕ) × ℕ) × Finset ℕ) × ℕ =>
          decide ((src r.1.1.1.1.1).tabEval r.1.1.1.2 r.2 r.1.1.1.1.2 = some r.1.2) :=
        (Kolmogorov.primrec_decideEq.to_comp.comp (hsrc.tabEval.comp
          ((Computable.fst.comp (Computable.fst.comp (Computable.fst.comp (Computable.fst.comp
            Computable.fst)))).pair
          ((Computable.snd.comp (Computable.fst.comp (Computable.fst.comp Computable.fst))).pair
          (Computable.snd.pair (Computable.snd.comp (Computable.fst.comp (Computable.fst.comp
            (Computable.fst.comp Computable.fst))))))))
          (Computable.option_some.comp (Computable.snd.comp Computable.fst))).of_eq fun _ => rfl
      exact (computable_list_all (computable_finsetSort.comp Computable.snd) hq.to₂).of_eq
        fun _ => rfl
    refine (Primrec.and.to_comp.comp hsub (Primrec.and.to_comp.comp hmem hall)).of_eq
      fun z => ?_
    rw [Bool.eq_iff_iff]
    simp [List.all_eq_true]
  have hentry : Computable fun v : ((π × ℕ) × ℕ) × ℕ =>
      tableEntryOk (G v.1.1.1) (src v.1.1.1) v.1.2 v.1.1.2 v.2 := by
    refine (Computable.option_casesOn hval (Computable.const false) hcheck.to₂).of_eq
      fun v => ?_
    unfold tableEntryOk
    cases (src v.1.1.1).tabEval v.1.2 v.2 v.1.1.2 <;> rfl
  have hallok : Computable fun y : (π × ℕ) × ℕ =>
      (G y.1.1).centers.all (tableEntryOk (G y.1.1) (src y.1.1) y.2 y.1.2) :=
    (computable_list_all (hG.centers.comp hp) hentry.to₂).of_eq fun _ => rfl
  have hgetD : Computable fun v : ((π × ℕ) × ℕ) × ℕ =>
      ((src v.1.1.1).tabEval v.1.2 v.2 v.1.1.2).getD ∅ := by
    refine (Computable.option_casesOn hval (Computable.const ∅)
      (Computable.snd : Computable fun r : (((π × ℕ) × ℕ) × ℕ) × Finset ℕ => r.2).to₂).of_eq
      fun v => ?_
    cases (src v.1.1.1).tabEval v.1.2 v.2 v.1.1.2 <;> rfl
  have hcells : Computable fun y : (π × ℕ) × ℕ => tableCells (G y.1.1) (src y.1.1) y.2 y.1.2 :=
    (computable_list_map' (hG.centers.comp hp) hgetD.to₂).of_eq fun _ => rfl
  refine (Computable.cond (Primrec.and.to_comp.comp hfirst hallok)
    (Computable.list_cons.comp (computable_tableEvent.comp hcells) (Computable.const []))
    (Computable.const [])).to₂.of_eq ?_
  intro y
  simp only [tabEventAt]
  by_cases h : firstAt (fun t => if tableDone (G y.1.1) (src y.1.1) y.2 t then some () else none)
      y.1.2 = true ∧ (G y.1.1).centers.all (tableEntryOk (G y.1.1) (src y.1.1) y.2 y.1.2) = true <;>
    simp [h]

/-- **The events of one stage are computable**: three `flatMap`s over candidate ranges. -/
theorem stageEvents_computable {G : π → ResGame ℕ} (hG : IsComputableGame G)
    {src : π → EventSources ℕ} (hsrc : IsComputableSources src) {K τ : π → ℕ}
    (hK : Computable K) (hτ : Computable τ) :
    Computable fun x : π × ℕ => stageEvents (G x.1) (K x.1) (τ x.1) (src x.1) x.2 := by
  have h1 := computable_flatMap (Primrec.list_range.to_comp.comp
    (hsrc.numPt.comp Computable.fst)) (ptEventAt_computable hG hsrc)
  have h2 := computable_flatMap (Primrec.list_range.to_comp.comp
    (hsrc.numSet.comp Computable.fst)) (setEventAt_computable hG hsrc hK hτ)
  have h3 := computable_flatMap (Primrec.list_range.to_comp.comp
    (hsrc.numTab.comp Computable.fst)) (tabEventAt_computable hG hsrc)
  exact (Computable.list_append.comp (Computable.list_append.comp h1 h2) h3).of_eq fun _ => rfl

/-- **The event stream is computable** (node L14, effectivity):
`(p, s) ↦ eventHistory (G p) (K p) (τ p) (src p) s`. -/
theorem eventHistory_computable {G : π → ResGame ℕ} (hG : IsComputableGame G)
    {src : π → EventSources ℕ} (hsrc : IsComputableSources src) {K τ : π → ℕ}
    (hK : Computable K) (hτ : Computable τ) :
    Computable fun x : π × ℕ => eventHistory (G x.1) (K x.1) (τ x.1) (src x.1) x.2 := by
  have hg : Computable fun y : (π × ℕ) × ℕ =>
      stageEvents (G y.1.1) (K y.1.1) (τ y.1.1) (src y.1.1) y.2 :=
    ((stageEvents_computable hG hsrc hK hτ).comp
      (Computable.pair (Computable.fst.comp Computable.fst) Computable.snd)).of_eq fun _ => rfl
  exact (computable_flatMap (Primrec.list_range.to_comp.comp Computable.snd) hg.to₂).of_eq
    fun _ => rfl

/-- **The emitted centers up to stage `s` are computable** in `(p, s)`: the effective output
sequence of the game (nodes L17, L22). -/
theorem emittedCenters_eventHistory_computable {G : π → ResGame ℕ} (hG : IsComputableGame G)
    {src : π → EventSources ℕ} (hsrc : IsComputableSources src) {K τ : π → ℕ}
    (hK : Computable K) (hτ : Computable τ) :
    Computable fun x : π × ℕ =>
      emittedCenters (G x.1) (eventHistory (G x.1) (K x.1) (τ x.1) (src x.1) x.2) := by
  have h1 := (run_computable hG).comp
    (Computable.pair Computable.fst (eventHistory_computable hG hsrc hK hτ))
  exact (emittedReverse_computable.comp h1).of_eq fun _ => rfl

end Kolmogorov.StrongMerging.Lower
