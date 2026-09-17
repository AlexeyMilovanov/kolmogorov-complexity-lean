import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedController
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailRaw

/-!
# An index-erased mirror of the charged advantage-and-spend controller

`GacsDayLadderTailRaw.lean` mirrors the *robust* tail controller by an
index-erased state `RawState`.  The charged controller of
`GacsDayChargedController.lean` differs from it in three places only:

* the acceptance test is `grayChargedTailGoalAtB` instead of
  `familyRobustGrayGoalAtB`, and the advantage phase stops after
  `grayChargedAdvantageRoundCount` rounds;
* the controller carries a finite syntactic phase `GrayChargedPhase`;
* the displayed move is `grayChargedTailFamilyMove`, whose spare sons show the
  honest recursive sum instead of the reserve raise.

This file mirrors exactly those three additions.  The phase is erased to a
natural tag, the charged state to `RawChargedState = ℕ × RawState`, and every
mirror is certified by a displayed bridge lemma; the key one,
`rawChargedStepWith_eq`, connects the raw transition with the actual
`grayChargedStep`.  All mirror types are built from `ℕ`, `Bool`, `ℚ` and lists,
so they are primitive codable; computability lives in
`GacsDayChargedRawComputable.lean`.
-/

namespace Kolmogorov

/-! ### The erased phase and state -/

/-- Erase a controller phase to a natural tag: `0` is the advantage phase, `1`
is the terminal phase, and `pass + 2` is the `pass`-th spend phase. -/
def chargedPhaseTag : GrayChargedPhase → ℕ
  | .advantage => 0
  | .done => 1
  | .spend pass => pass + 2

/-- Decode a phase tag back to a controller phase: the inverse of `chargedPhaseTag`. -/
def chargedPhaseOfTag : ℕ → GrayChargedPhase
  | 0 => .advantage
  | 1 => .done
  | (pass + 2) => .spend pass

/-- Decoding the numeric tag of a phase returns that phase. -/
@[simp] theorem chargedPhaseOfTag_chargedPhaseTag (p : GrayChargedPhase) :
    chargedPhaseOfTag (chargedPhaseTag p) = p := by
  cases p <;> rfl

/-- The tag `0` marks exactly the `advantage` phase. -/
theorem chargedPhaseTag_eq_zero_iff (p : GrayChargedPhase) :
    chargedPhaseTag p = 0 ↔ p = .advantage := by
  cases p <;> simp [chargedPhaseTag]

/-- The tag `1` marks exactly the `done` phase. -/
theorem chargedPhaseTag_eq_one_iff (p : GrayChargedPhase) :
    chargedPhaseTag p = 1 ↔ p = .done := by
  cases p <;> simp [chargedPhaseTag]

/-- An index-erased charged controller state: the phase tag together with the
erased tail state. -/
abbrev RawChargedState := ℕ × RawState

instance instPrimcodableRawChargedState : Primcodable RawChargedState :=
  inferInstance

/-- Erase a charged controller state. -/
def toRawChargedState {n b : ℕ} (st : GrayChargedState n b) : RawChargedState :=
  (chargedPhaseTag st.phase, toRawState st.core)

/-! ### Erased spend layout -/

/-- Erased foreign test: `grayNodeForeignB` on index-erased slots. -/
def rawGrayNodeForeignB (slots : List RawSlot) (i : ℕ) (x : GacsDayNode) : Bool :=
  slots.all fun s =>
    decide (i ≠ s.1) ||
      !(decide (x <+: [s.2.1, s.2.2] ∨ [s.2.1, s.2.2] <+: x))

/-- Erased foreign-union harvest: `grayHarvest` on index-erased slots. -/
def rawGrayHarvest (δ b : ℕ) (slots : List RawSlot) (nn : ℕ)
    (sm : FamilyServerMove) : Allocation :=
  (List.range nn).flatMap fun i =>
    ((familyServerMoveAt sm i).map Prod.fst).flatMap fun x =>
      if grayNodeValidB b x && rawGrayNodeForeignB slots i x then
        (getAlloc (familyServerMoveAt sm i) x).map fun c => c.take δ
      else []

/-- The raw foreignness test on encoded slots agrees with the structured one. -/
theorem rawGrayNodeForeignB_eq {n b : ℕ} (slots : List (GrayTailSlot n b))
    (i : ℕ) (x : GacsDayNode) :
    rawGrayNodeForeignB (slots.map toRawSlot) i x =
      grayNodeForeignB slots i x := by
  unfold rawGrayNodeForeignB grayNodeForeignB
  rw [List.all_map]
  rfl

/-- The raw harvest on encoded slots agrees with the structured harvest. -/
theorem rawGrayHarvest_eq {n b : ℕ} (δ : ℕ) (slots : List (GrayTailSlot n b))
    (nn : ℕ) (sm : FamilyServerMove) :
    rawGrayHarvest δ b (slots.map toRawSlot) nn sm =
      grayHarvest (n := n) (b := b) δ slots nn sm := by
  unfold rawGrayHarvest grayHarvest
  simp only [rawGrayNodeForeignB_eq]

/-- Erased form of `grayChargedSparePairs`. -/
def rawSparePairs (b source : ℕ) : List (ℕ × ℕ) :=
  ((List.range b).drop source).flatMap fun c => (List.range b).map fun d => (c, d)

/-- Erased form of `grayChargedSpendPairs`. -/
def rawSpendPairs (b source count pass : ℕ) : List (ℕ × ℕ) :=
  ((rawSparePairs b source).drop (pass * count)).take count

/-- Erased form of `grayChargedSonRequest`. -/
def rawChargedSonRequest (source : ℕ) (threshold eps : ℚ)
    (entries : List (RawSlot × ClientMove)) (i c : ℕ) : ℚ :=
  if c < source then rawSonRequest threshold eps entries i c else rawSonBase entries i c

/-- Erased form of `grayChargedRootRequest`. -/
def rawChargedRootRequest (source : ℕ) (threshold eps : ℚ) (b : ℕ)
    (entries : List (RawSlot × ClientMove)) (i : ℕ) : ℚ :=
  ((List.range b).map fun c => rawChargedSonRequest source threshold eps entries i c).sum

/-- Erased form of `grayChargedDeficientRoots`. -/
def rawChargedDeficientRoots (n b source : ℕ) (threshold eps alpha : ℚ)
    (frozen : List RawRound) : List ℕ :=
  (List.range n).filter fun i =>
    decide (rawChargedRootRequest source threshold eps b (rawFrozenEntries frozen) i < alpha / 2)

/-- Erased form of `grayChargedSpendSlots`. -/
def rawChargedSpendSlots (n b source count pass : ℕ) (threshold eps alpha : ℚ)
    (frozen : List RawRound) : List RawSlot :=
  (rawChargedDeficientRoots n b source threshold eps alpha frozen).flatMap fun i =>
    (rawSpendPairs b source count pass).map fun p => (i, p.1, p.2)

/-- Erased form of `grayChargedSlotsForPass`. -/
def rawChargedSlotsForPass (q a e n b pass : ℕ) (frozen : List RawRound) : List RawSlot :=
  rawChargedSpendSlots n b (grayChargedSourceCount a e) (grayChargedSpendCount q a e) pass
    (grayChargedThreshold q e) (dyadicScale e) (dyadicScale a) frozen

/-- Erased form of `grayChargedTailFamilyMove`. -/
def rawChargedFamilyMove (source : ℕ) (threshold eps : ℚ) (n b : ℕ)
    (frozen : List RawRound) (slots : List RawSlot) (current : FamilyClientMove) :
    FamilyClientMove :=
  let entries := rawEntries frozen slots current
  (List.range n).map fun i =>
    graftTwoLevel (rawChargedRootRequest source threshold eps b entries i) b
      (fun c => if c < b then rawChargedSonRequest source threshold eps entries i c else 0)
      (fun c c' => if c < b then (if c' < b then rawEntryMove entries (i, c, c') else []) else [])

/-! ### Bridge lemmas for the spend layout -/

/-- The raw son request on encoded entries agrees with the structured son request. -/
theorem rawChargedSonRequest_eq {n b : ℕ} (source : ℕ) (threshold eps : ℚ)
    (entries : List (GrayTailSlot n b × ClientMove)) (i : Fin n) (c : Fin b) :
    rawChargedSonRequest source threshold eps (toRawEntries entries) i.val c.val =
      grayChargedSonRequest source threshold eps entries i c := by
  unfold rawChargedSonRequest grayChargedSonRequest
  by_cases hc : c.val < source
  · rw [if_pos hc, if_pos hc, rawSonRequest_eq]
  · rw [if_neg hc, if_neg hc, rawSonBase_eq]

/-- The raw root request on encoded entries agrees with the structured root request. -/
theorem rawChargedRootRequest_eq {n b : ℕ} (source : ℕ) (threshold eps : ℚ)
    (entries : List (GrayTailSlot n b × ClientMove)) (i : Fin n) :
    rawChargedRootRequest source threshold eps b (toRawEntries entries) i.val =
      grayChargedRootRequest source threshold eps entries i := by
  unfold rawChargedRootRequest grayChargedRootRequest
  rw [sum_map_range_eq,
    ← Fin.sum_univ_eq_sum_range
      (fun c => rawChargedSonRequest source threshold eps (toRawEntries entries) i.val c) b]
  exact Finset.sum_congr rfl fun c _ => rawChargedSonRequest_eq source threshold eps entries i c

/-- The raw list of deficient roots is the structured one, read as numbers. -/
theorem rawChargedDeficientRoots_eq {n b : ℕ} (source : ℕ) (threshold eps alpha : ℚ)
    (frozen : GrayTailFrozen n b) :
    rawChargedDeficientRoots n b source threshold eps alpha (frozen.map toRawRound) =
      (grayChargedDeficientRoots source threshold eps alpha frozen).map Fin.val := by
  unfold rawChargedDeficientRoots grayChargedDeficientRoots
  rw [rawFrozenEntries_eq]
  rw [← filter_finRange_map_val n fun i =>
    decide (rawChargedRootRequest source threshold eps b
      (toRawEntries (grayTailFrozenEntries frozen)) i < alpha / 2)]
  congr 1
  refine List.filter_congr fun i _ => ?_
  rw [rawChargedRootRequest_eq]

/-- The raw spare pairs are the structured spare pairs, read as numbers. -/
theorem rawSparePairs_eq (b source : ℕ) :
    rawSparePairs b source =
      (grayChargedSparePairs b source).map fun p => (p.1.val, p.2.val) := by
  unfold rawSparePairs grayChargedSparePairs
  have hrange : List.range b = (List.finRange b).map Fin.val := by simp
  rw [hrange, ← List.map_drop, List.flatMap_map, List.map_flatMap]
  refine List.flatMap_congr fun c _ => ?_
  simp only [List.map_map]
  rfl

/-- The raw spend pairs of a pass are the structured spend pairs, read as numbers. -/
theorem rawSpendPairs_eq (b source count pass : ℕ) :
    rawSpendPairs b source count pass =
      (grayChargedSpendPairs b source count pass).map fun p => (p.1.val, p.2.val) := by
  unfold rawSpendPairs grayChargedSpendPairs
  rw [rawSparePairs_eq, ← List.map_drop, ← List.map_take]

/-- The raw spend slots of a pass are the encodings of the structured spend slots. -/
theorem rawChargedSpendSlots_eq {n b : ℕ} (source count pass : ℕ) (threshold eps alpha : ℚ)
    (frozen : GrayTailFrozen n b) :
    rawChargedSpendSlots n b source count pass threshold eps alpha (frozen.map toRawRound) =
      (grayChargedSpendSlots source count pass threshold eps alpha frozen).map toRawSlot := by
  unfold rawChargedSpendSlots grayChargedSpendSlots
  rw [rawChargedDeficientRoots_eq, List.map_flatMap, List.flatMap_map]
  refine List.flatMap_congr fun i _ => ?_
  rw [rawSpendPairs_eq, List.map_map, List.map_map]
  rfl

/-- The raw slots of a pass are the encodings of the structured slots of that pass. -/
theorem rawChargedSlotsForPass_eq {n b : ℕ} (q a e pass : ℕ)
    (frozen : GrayTailFrozen n b) :
    rawChargedSlotsForPass q a e n b pass (frozen.map toRawRound) =
      (grayChargedSlotsForPass q a e pass frozen).map toRawSlot := by
  unfold rawChargedSlotsForPass grayChargedSlotsForPass
  exact rawChargedSpendSlots_eq _ _ _ _ _ _ frozen

/-- The raw displayed family move on encoded rounds and slots agrees with the structured one. -/
theorem rawChargedFamilyMove_eq {n b : ℕ} (source : ℕ) (threshold eps : ℚ)
    (frozen : GrayTailFrozen n b) (slots : List (GrayTailSlot n b))
    (current : FamilyClientMove) :
    rawChargedFamilyMove source threshold eps n b (frozen.map toRawRound)
        (slots.map toRawSlot) current =
      grayChargedTailFamilyMove source threshold eps frozen slots current := by
  unfold rawChargedFamilyMove grayChargedTailFamilyMove
  simp only [rawEntries_eq]
  set entries := grayTailEntries frozen slots current with hentries
  rw [List.ofFn_eq_map]
  refine (map_finRange_eq_map_range n _ _ ?_).symm
  intro i
  have h1 : grayChargedRootRequest source threshold eps entries i =
      rawChargedRootRequest source threshold eps b (toRawEntries entries) i.val :=
    (rawChargedRootRequest_eq source threshold eps entries i).symm
  have h2 : (fun c => if hc : c < b then
        grayChargedSonRequest source threshold eps entries i ⟨c, hc⟩ else 0) =
      fun c => if c < b then
        rawChargedSonRequest source threshold eps (toRawEntries entries) i.val c else 0 := by
    funext c
    by_cases hc : c < b
    · rw [dif_pos hc, if_pos hc]
      exact (rawChargedSonRequest_eq source threshold eps entries i ⟨c, hc⟩).symm
    · rw [dif_neg hc, if_neg hc]
  have h3 : (fun c c' => if hc : c < b then
        (if hc' : c' < b then grayTailEntryMove entries (i, ⟨c, hc⟩, ⟨c', hc'⟩) else []) else []) =
      fun c c' => if c < b then
        (if c' < b then rawEntryMove (toRawEntries entries) (i.val, c, c') else []) else [] := by
    funext c c'
    by_cases hc : c < b
    · rw [dif_pos hc, if_pos hc]
      by_cases hc' : c' < b
      · rw [dif_pos hc', if_pos hc']
        exact (rawEntryMove_eq entries (i, ⟨c, hc⟩, ⟨c', hc'⟩)).symm
      · rw [dif_neg hc', if_neg hc']
    · rw [dif_neg hc, if_neg hc]
  rw [h1, h2, h3]

/-! ### The erased advantage transition -/

/-- Erased form of `grayChargedTailStep`, with the answer of the recursive call
supplied as an ordinary argument.  It differs from `rawStepWith` only in the
acceptance test and in the advantage round budget. -/
def rawChargedTailStepWith (q L a e n b : ℕ) (A : Allocation) (st : RawState)
    (sm : FamilyServerMove) (current : FamilyClientMove) : RawState :=
  if st.1.2.2 then
    ((st.1.1 + 1, st.1.2.1, st.1.2.2), st.2)
  else if st.2.2.2.1.isEmpty then
    ((st.1.1 + 1, st.1.2.1, st.1.2.2), st.2)
  else
    let epsRound := grayTailRoundEps q L e st.2.1.length
    let deltaRound := grayTailRoundDelta q L e st.2.1.length
    let localSM := rawLocalServerMove deltaRound b st.2.2.2.1 sm
    if grayChargedTailGoalAtB q e epsRound deltaRound st.2.2.2.1.length st.2.2.1
        current localSM then
      let allocated := grayTailLocalAllocatedList localSM
      let frozen' := st.2.1 ++
        [((st.2.1.length, st.1.1, epsRound),
          (st.2.2.2.1, current, allocated, st.2.2.1))]
      let candidates :=
        rawNextSlots n b e (grayChargedSourceCount a e) frozen'.length
          (grayChargedThreshold q e) A frozen' sm
      let unavailable' := A ++
        rawGrayHarvest (grayTailRoundDelta q L e frozen'.length) b candidates
          n sm
      ((st.1.1 + 1, st.1.1 + 1,
          rawGlobalQuarterB n (grayChargedSourceCount a e) candidates ||
            decide (grayChargedAdvantageRoundCount q ≤ frozen'.length)),
        (frozen', unavailable', candidates, [], ([], [])))
    else
      ((st.1.1 + 1, st.1.2.1, st.1.2.2),
        (st.2.1, st.2.2.1, st.2.2.2.1, st.2.2.2.2.1,
          (st.2.2.2.2.2.1 ++ [current], st.2.2.2.2.2.2 ++ [localSM])))

/-- The frozen round appended by one winning spend pass. -/
def grayChargedSpendStepRound {n b : ℕ} (q L a e pass : ℕ)
    (sigma : FamilyStrategyScheme)
    (st : GrayTailState n b) (sm : FamilyServerMove) : GrayTailRound n b where
  roundIndex := st.frozen.length
  serverTime := st.time
  epsDepth := grayChargedSpendEps a L e pass
  slots := st.slots
  move := grayChargedSpendMove q L a e pass sigma st
  allocated := grayTailLocalAllocatedList
    (grayTailLocalServerMove (grayChargedSpendDelta a L e pass) st.slots sm)
  unavailable := st.unavailable

/-- The frozen round appended by one winning charged advantage step. -/
def grayChargedTailStepRound {n b : ℕ} (q L e : ℕ) (sigma : FamilyStrategyScheme)
    (st : GrayTailState n b) (sm : FamilyServerMove) : GrayTailRound n b where
  roundIndex := st.frozen.length
  serverTime := st.time
  epsDepth := grayTailRoundEps q L e st.frozen.length
  slots := st.slots
  move := grayTailCurrentMove q L e sigma st
  allocated := grayTailLocalAllocatedList
    (grayTailLocalServerMove (grayTailRoundDelta q L e st.frozen.length) st.slots sm)
  unavailable := st.unavailable

/-- The raw tail step, fed the current move, computes the encoding of the structured tail step. -/
theorem rawChargedTailStepWith_eq {n b : ℕ} (q L a e : ℕ) (sigma : FamilyStrategyScheme)
    (A : Allocation) (st : GrayTailState n b) (sm : FamilyServerMove) :
    rawChargedTailStepWith q L a e n b A (toRawState st) sm
        (grayTailCurrentMove q L e sigma st) =
      toRawState (grayChargedTailStep q L a e sigma A st sm) := by
  rw [grayChargedTailStep_eq]
  unfold rawChargedTailStepWith
  simp only [toRawState, List.isEmpty_map, List.length_map]
  by_cases hd : st.done = true
  · rw [if_pos hd]
    simp [hd]
  · rw [if_neg hd]
    by_cases hs : st.slots.isEmpty = true
    · rw [if_pos hs]
      simp [hd, hs]
    · rw [if_neg hs]
      simp only [hd, hs, Bool.or_self]
      rw [rawLocalServerMove_eq]
      by_cases hgoal : grayChargedTailGoalAtB q e
          (grayTailRoundEps q L e st.frozen.length)
          (grayTailRoundDelta q L e st.frozen.length)
          st.slots.length st.unavailable
          (grayTailCurrentMove q L e sigma st)
          (grayTailLocalServerMove
            (grayTailRoundDelta q L e st.frozen.length) st.slots sm) = true
      · rw [if_pos hgoal, if_pos hgoal]
        have hfr : (st.frozen.map toRawRound ++
              [((st.frozen.length, st.time,
                  grayTailRoundEps q L e st.frozen.length),
                (st.slots.map toRawSlot,
                  grayTailCurrentMove q L e sigma st,
                  grayTailLocalAllocatedList
                    (grayTailLocalServerMove
                      (grayTailRoundDelta q L e st.frozen.length) st.slots sm),
                  st.unavailable))]) =
            (st.frozen ++ [grayChargedTailStepRound q L e sigma st sm]).map toRawRound := by
          simp [grayChargedTailStepRound, toRawRound]
        rw [hfr, rawNextSlots_eq, rawGrayHarvest_eq, rawGlobalQuarterB_eq]
        simp [grayChargedTailStepRound, grayChargedThreshold,
          grayChargedSourceCount]
      · rw [if_neg hgoal, if_neg hgoal]
        simp

/-! ### The erased phase-tagged transition -/

/-- Erased form of `grayChargedStartSpend`. -/
def rawChargedStartSpend (q L a e n b : ℕ) (A : Allocation) (core : RawState)
    (sm : FamilyServerMove) : RawChargedState :=
  if (rawChargedSlotsForPass q a e n b 0 core.2.1).isEmpty then
    (1, ((core.1.1, core.1.2.1, true),
      (core.2.1, core.2.2.1, [], core.2.2.2.2.1, ([], []))))
  else
    (2, ((core.1.1, core.1.2.1, false),
      (core.2.1,
        A ++ rawGrayHarvest (grayChargedSpendDelta a L e 0) b
          (rawChargedSlotsForPass q a e n b 0 core.2.1) n sm,
        rawChargedSlotsForPass q a e n b 0 core.2.1,
        core.2.2.2.2.1, ([], []))))

/-- Erased form of `grayChargedStep`, with the answer of the recursive call
supplied as an ordinary argument. -/
def rawChargedStepWith (q L a e n b : ℕ) (A : Allocation) (tag : ℕ) (st : RawState)
    (sm : FamilyServerMove) (current : FamilyClientMove) : RawChargedState :=
  if tag = 1 then
    (1, ((st.1.1 + 1, st.1.2.1, st.1.2.2), st.2))
  else if tag = 0 then
    if (rawChargedTailStepWith q L a e n b A st sm current).1.2.2 then
      rawChargedStartSpend q L a e n b A
        (rawChargedTailStepWith q L a e n b A st sm current) sm
    else (0, rawChargedTailStepWith q L a e n b A st sm current)
  else
    if st.2.2.2.1.isEmpty then
      (1, ((st.1.1 + 1, st.1.2.1, true), st.2))
    else
      let epsRound := grayChargedSpendEps a L e (tag - 2)
      let deltaRound := grayChargedSpendDelta a L e (tag - 2)
      let localSM := rawLocalServerMove deltaRound b st.2.2.2.1 sm
      if grayChargedSpendGoalAtB q L a e (tag - 2) st.2.2.2.1.length st.2.2.1
          current localSM then
        let allocated := grayTailLocalAllocatedList localSM
        let frozen' := st.2.1 ++
          [((st.2.1.length, st.1.1, epsRound),
            (st.2.2.2.1, current, allocated, st.2.2.1))]
        let unavailable' := A ++
          rawGrayHarvest (grayChargedSpendDelta a L e (tag - 2 + 1)) b
            (rawChargedSlotsForPass q a e n b (tag - 2 + 1) frozen') n sm
        if tag - 2 + 1 < 8 then
          if (rawChargedSlotsForPass q a e n b (tag - 2 + 1) frozen').isEmpty then
            ((1 : ℕ), ((st.1.1 + 1, st.1.1 + 1, true),
              (frozen', unavailable', [], [], ([], []))))
          else
            (tag - 2 + 3, ((st.1.1 + 1, st.1.1 + 1, false),
              (frozen', unavailable',
                rawChargedSlotsForPass q a e n b (tag - 2 + 1) frozen', [], ([], []))))
        else
          ((1 : ℕ), ((st.1.1 + 1, st.1.1 + 1, true),
            (frozen', unavailable', [], [], ([], []))))
      else
        (tag, ((st.1.1 + 1, st.1.2.1, st.1.2.2),
          (st.2.1, st.2.2.1, st.2.2.2.1, st.2.2.2.2.1,
            (st.2.2.2.2.2.1 ++ [current], st.2.2.2.2.2.2 ++ [localSM]))))

/-- Erased form of `grayChargedInitialState`.  The charged initial state is the
source-only tail initial state, which `rawInitialState` already mirrors. -/
theorem rawInitialState_grayChargedTail (n b a e : ℕ) (A : Allocation) :
    rawInitialState n b a e A = toRawState (grayChargedTailInitialState n b a e A) := by
  unfold rawInitialState toRawState grayChargedTailInitialState
  simp [rawSlots_eq, grayChargedSourceCount]

/-- The raw opening of a spend pass computes the encoding of the structured one. -/
theorem rawChargedStartSpend_eq {n b : ℕ} (q L a e : ℕ) (A : Allocation)
    (core : GrayTailState n b) (sm : FamilyServerMove) :
    rawChargedStartSpend q L a e n b A (toRawState core) sm =
      toRawChargedState (grayChargedStartSpend q L a e A core sm) := by
  unfold rawChargedStartSpend grayChargedStartSpend toRawChargedState
  simp only [toRawState]
  simp only [rawChargedSlotsForPass_eq, rawGrayHarvest_eq, List.isEmpty_map]
  by_cases hemp : (grayChargedSlotsForPass q a e 0 core.frozen).isEmpty = true
  · rw [if_pos hemp, if_pos hemp]
    simp [chargedPhaseTag]
  · rw [if_neg hemp, if_neg hemp]
    simp [chargedPhaseTag]

/-- **The charged transition commutes with erasure.**  This is the theorem that
connects the raw phase-tagged transition with the actual `grayChargedStep`. -/
theorem rawChargedStepWith_eq {n b : ℕ} (q L a e : ℕ) (sigma : FamilyStrategyScheme)
    (A : Allocation) (st : GrayChargedState n b) (sm : FamilyServerMove) :
    rawChargedStepWith q L a e n b A (chargedPhaseTag st.phase) (toRawState st.core) sm
        (match st.phase with
          | .spend pass => grayChargedSpendMove q L a e pass sigma st.core
          | _ => grayTailCurrentMove q L e sigma st.core) =
      toRawChargedState (grayChargedStep q L a e sigma A st sm) := by
  unfold rawChargedStepWith grayChargedStep
  cases hph : st.phase with
  | done =>
    simp only [chargedPhaseTag]
    simp [toRawChargedState, toRawState, chargedPhaseTag]
  | advantage =>
    simp only [chargedPhaseTag]
    norm_num
    rw [rawChargedTailStepWith_eq q L a e sigma A st.core sm]
    by_cases hdone : (grayChargedTailStep q L a e sigma A st.core sm).done = true
    · rw [if_pos (by simpa [toRawState] using hdone), if_pos hdone]
      exact rawChargedStartSpend_eq q L a e A _ sm
    · rw [if_neg (by simpa [toRawState] using hdone), if_neg hdone]
      simp [toRawChargedState, chargedPhaseTag]
  | spend pass =>
    have h1 : chargedPhaseTag (GrayChargedPhase.spend pass) = pass + 2 := rfl
    rw [h1]
    rw [if_neg (by omega), if_neg (by omega)]
    have hsub : pass + 2 - 2 = pass := by omega
    simp only [hsub, toRawState, List.isEmpty_map, List.length_map]
    by_cases hs : st.core.slots.isEmpty = true
    · rw [if_pos hs, if_pos hs]
      simp [toRawChargedState, toRawState, chargedPhaseTag]
    · rw [if_neg hs, if_neg hs]
      rw [rawLocalServerMove_eq]
      by_cases hgoal : grayChargedSpendGoalAtB q L a e pass
          st.core.slots.length st.core.unavailable
          (grayChargedSpendMove q L a e pass sigma st.core)
          (grayTailLocalServerMove
            (grayChargedSpendDelta a L e pass) st.core.slots sm) = true
      · rw [if_pos hgoal, if_pos hgoal]
        have hfr : (st.core.frozen.map toRawRound ++
              [((st.core.frozen.length, st.core.time,
                  grayChargedSpendEps a L e pass),
                (st.core.slots.map toRawSlot,
                  grayChargedSpendMove q L a e pass sigma st.core,
                  grayTailLocalAllocatedList
                    (grayTailLocalServerMove
                      (grayChargedSpendDelta a L e pass) st.core.slots sm),
                  st.core.unavailable))]) =
            (st.core.frozen ++
              [grayChargedSpendStepRound q L a e pass sigma st.core sm]).map toRawRound := by
          simp [grayChargedSpendStepRound, toRawRound]
        have hpr : ({ roundIndex := st.core.frozen.length
                      serverTime := st.core.time
                      epsDepth := grayChargedSpendEps a L e pass
                      slots := st.core.slots
                      move := grayChargedSpendMove q L a e pass sigma st.core
                      allocated := grayTailLocalAllocatedList
                        (grayTailLocalServerMove
                          (grayChargedSpendDelta a L e pass) st.core.slots sm)
                      unavailable := st.core.unavailable } : GrayTailRound n b) =
            grayChargedSpendStepRound q L a e pass sigma st.core sm := rfl
        rw [hpr, hfr, rawChargedSlotsForPass_eq, rawGrayHarvest_eq, List.isEmpty_map]
        by_cases hp : pass + 1 < 8
        · by_cases hemp : (grayChargedSlotsForPass q a e (pass + 1)
              (st.core.frozen
                ++ [grayChargedSpendStepRound q L a e pass sigma st.core sm])).isEmpty = true
          · simp only [if_pos hp, if_pos hemp]
            simp [toRawChargedState, toRawState, chargedPhaseTag,
              grayChargedSpendStepRound, toRawRound]
          · simp only [if_pos hp, if_neg hemp]
            simp [toRawChargedState, toRawState, chargedPhaseTag,
              grayChargedSpendStepRound, toRawRound]
        · simp only [if_neg hp]
          simp [toRawChargedState, toRawState, chargedPhaseTag,
            grayChargedSpendStepRound, toRawRound]
      · rw [if_neg hgoal, if_neg hgoal]
        simp [toRawChargedState, toRawState, chargedPhaseTag]

/-! ### The erased displayed move -/

/-- Erased form of the displayed move of `grayChargedStrategy`. -/
def rawChargedOutput (q a e n b : ℕ) (tag : ℕ) (st : RawState)
    (current : FamilyClientMove) : FamilyClientMove :=
  rawChargedFamilyMove (grayChargedSourceCount a e) (grayChargedThreshold q e)
    (dyadicScale e) n b st.2.1 st.2.2.2.1
    (if tag = 1 then [] else if st.2.2.2.1.isEmpty then [] else current)

/-- The raw output of a charged state, fed the move of its phase, is the family move the
structured controller displays. -/
theorem rawChargedOutput_eq {n b : ℕ} (q L a e : ℕ) (sigma : FamilyStrategyScheme)
    (st : GrayChargedState n b) :
    rawChargedOutput q a e n b (chargedPhaseTag st.phase) (toRawState st.core)
        (match st.phase with
          | .spend pass => grayChargedSpendMove q L a e pass sigma st.core
          | _ => grayTailCurrentMove q L e sigma st.core) =
      grayChargedTailFamilyMove (grayChargedSourceCount a e) (grayChargedThreshold q e)
        (dyadicScale e) st.core.frozen st.core.slots
        (match st.phase with
          | .done => []
          | .advantage => if st.core.slots.isEmpty then []
            else grayTailCurrentMove q L e sigma st.core
          | .spend pass => if st.core.slots.isEmpty then []
            else grayChargedSpendMove q L a e pass sigma st.core) := by
  unfold rawChargedOutput
  simp only [toRawState, List.isEmpty_map]
  rw [rawChargedFamilyMove_eq]
  congr 1
  cases st.phase <;> simp [chargedPhaseTag]

/-- The scheme input of the recursive call made in a charged state: the
advantage phase queries the descending fine schedule, spend pass `p` queries
the coarse spend scales. -/
def rawChargedQuery (q L a e : ℕ) (tag : ℕ) (st : RawState) : SchemeInput :=
  if tag < 2 then rawQuery q L e st
  else ((grayChargedSpendAlphaDepth a, grayChargedSpendEps a L e (tag - 2)),
    (st.2.2.1, (st.2.2.2.1.length, st.2.2.2.2.2)))

/-- On a tag below `2`, the raw query hands the scheme exactly the arguments that produce the
current advantage move. -/
theorem rawChargedQuery_eq_advantage {n b : ℕ} (q L a e : ℕ)
    (st : GrayTailState n b) (sigma : FamilyStrategyScheme)
    {tag : ℕ} (htag : tag < 2) :
    sigma (rawChargedQuery q L a e tag (toRawState st)).1.1
        (rawChargedQuery q L a e tag (toRawState st)).1.2
        (rawChargedQuery q L a e tag (toRawState st)).2.1
        (rawChargedQuery q L a e tag (toRawState st)).2.2.1
        (rawChargedQuery q L a e tag (toRawState st)).2.2.2 =
      grayTailCurrentMove q L e sigma st := by
  unfold rawChargedQuery
  rw [if_pos htag]
  exact rawQuery_eq q L e st sigma

/-- On the tag `pass + 2`, the raw query hands the scheme exactly the arguments that produce the
spend move of that pass. -/
theorem rawChargedQuery_eq_spend {n b : ℕ} (q L a e pass : ℕ)
    (st : GrayTailState n b) (sigma : FamilyStrategyScheme) :
    sigma (rawChargedQuery q L a e (pass + 2) (toRawState st)).1.1
        (rawChargedQuery q L a e (pass + 2) (toRawState st)).1.2
        (rawChargedQuery q L a e (pass + 2) (toRawState st)).2.1
        (rawChargedQuery q L a e (pass + 2) (toRawState st)).2.2.1
        (rawChargedQuery q L a e (pass + 2) (toRawState st)).2.2.2 =
      grayChargedSpendMove q L a e pass sigma st := by
  unfold rawChargedQuery grayChargedSpendMove toRawState
  rw [if_neg (by omega)]
  simp

/-- On the tag of a state's phase, the raw query hands the scheme the arguments that produce the
move of that phase. -/
theorem rawChargedQuery_eq_phase {n b : ℕ} (q L a e : ℕ)
    (st : GrayChargedState n b) (sigma : FamilyStrategyScheme) :
    sigma (rawChargedQuery q L a e (chargedPhaseTag st.phase)
          (toRawState st.core)).1.1
        (rawChargedQuery q L a e (chargedPhaseTag st.phase)
          (toRawState st.core)).1.2
        (rawChargedQuery q L a e (chargedPhaseTag st.phase)
          (toRawState st.core)).2.1
        (rawChargedQuery q L a e (chargedPhaseTag st.phase)
          (toRawState st.core)).2.2.1
        (rawChargedQuery q L a e (chargedPhaseTag st.phase)
          (toRawState st.core)).2.2.2 =
      (match st.phase with
        | .spend pass => grayChargedSpendMove q L a e pass sigma st.core
        | _ => grayTailCurrentMove q L e sigma st.core) := by
  cases hph : st.phase with
  | advantage =>
      simpa [chargedPhaseTag] using
        rawChargedQuery_eq_advantage q L a e st.core sigma
          (tag := 0) (by omega)
  | done =>
      simpa [chargedPhaseTag] using
        rawChargedQuery_eq_advantage q L a e st.core sigma
          (tag := 1) (by omega)
  | spend pass =>
      simpa [chargedPhaseTag] using
        rawChargedQuery_eq_spend q L a e pass st.core sigma

/-! ### The erased fold -/

/-- The erased charged fold, driven by a supplied family of answers. -/
def rawChargedFoldWith (q L a e n b : ℕ) (A : Allocation)
    (cur : ℕ → RawState → FamilyClientMove) (history : List FamilyServerMove) :
    RawChargedState :=
  history.foldl
    (fun stc sm => rawChargedStepWith q L a e n b A stc.1 stc.2 sm (cur stc.1 stc.2))
    (0, rawInitialState n b a e A)

/-- Folding the raw step over a history computes the encoding of the structured controller state. -/
theorem rawChargedFoldWith_eq {n b : ℕ} (q L a e : ℕ) (sigma : FamilyStrategyScheme)
    (A : Allocation) (history : List FamilyServerMove) :
    rawChargedFoldWith q L a e n b A
        (fun tag st => sigma (rawChargedQuery q L a e tag st).1.1
          (rawChargedQuery q L a e tag st).1.2
          (rawChargedQuery q L a e tag st).2.1
          (rawChargedQuery q L a e tag st).2.2.1
          (rawChargedQuery q L a e tag st).2.2.2)
        history =
      toRawChargedState (grayChargedFold (n := n) (b := b) q L a e sigma A history) := by
  unfold rawChargedFoldWith grayChargedFold
  have hinit : ((0 : ℕ), rawInitialState n b a e A) =
      toRawChargedState (grayChargedInitialState n b a e A) := by
    rw [rawInitialState_grayChargedTail]
    rfl
  rw [hinit]
  generalize grayChargedInitialState n b a e A = st0
  induction history generalizing st0 with
  | nil => simp
  | cons sm t ih =>
    have hstep :
        rawChargedStepWith q L a e n b A (toRawChargedState st0).1 (toRawChargedState st0).2 sm
            (sigma (rawChargedQuery q L a e (toRawChargedState st0).1
                (toRawChargedState st0).2).1.1
              (rawChargedQuery q L a e (toRawChargedState st0).1
                (toRawChargedState st0).2).1.2
              (rawChargedQuery q L a e (toRawChargedState st0).1
                (toRawChargedState st0).2).2.1
              (rawChargedQuery q L a e (toRawChargedState st0).1
                (toRawChargedState st0).2).2.2.1
              (rawChargedQuery q L a e (toRawChargedState st0).1
                (toRawChargedState st0).2).2.2.2) =
          toRawChargedState (grayChargedStep q L a e sigma A st0 sm) := by
      change rawChargedStepWith q L a e n b A (chargedPhaseTag st0.phase) (toRawState st0.core) sm
          (sigma (rawChargedQuery q L a e (chargedPhaseTag st0.phase)
              (toRawState st0.core)).1.1
            (rawChargedQuery q L a e (chargedPhaseTag st0.phase)
              (toRawState st0.core)).1.2
            (rawChargedQuery q L a e (chargedPhaseTag st0.phase)
              (toRawState st0.core)).2.1
            (rawChargedQuery q L a e (chargedPhaseTag st0.phase)
              (toRawState st0.core)).2.2.1
            (rawChargedQuery q L a e (chargedPhaseTag st0.phase)
              (toRawState st0.core)).2.2.2) =
          toRawChargedState (grayChargedStep q L a e sigma A st0 sm)
      cases hph : st0.phase with
      | advantage =>
          rw [rawChargedQuery_eq_advantage q L a e st0.core sigma
            (by simp [chargedPhaseTag])]
          have h := rawChargedStepWith_eq q L a e sigma A st0 sm
          rw [hph] at h
          simpa [hph] using h
      | done =>
          rw [rawChargedQuery_eq_advantage q L a e st0.core sigma
            (by simp [chargedPhaseTag])]
          have h := rawChargedStepWith_eq q L a e sigma A st0 sm
          rw [hph] at h
          simpa [hph] using h
      | spend pass =>
          change rawChargedStepWith q L a e n b A (pass + 2) (toRawState st0.core) sm
              (sigma (rawChargedQuery q L a e (pass + 2)
                  (toRawState st0.core)).1.1
                (rawChargedQuery q L a e (pass + 2)
                  (toRawState st0.core)).1.2
                (rawChargedQuery q L a e (pass + 2)
                  (toRawState st0.core)).2.1
                (rawChargedQuery q L a e (pass + 2)
                  (toRawState st0.core)).2.2.1
                (rawChargedQuery q L a e (pass + 2)
                  (toRawState st0.core)).2.2.2) =
            toRawChargedState (grayChargedStep q L a e sigma A st0 sm)
          rw [rawChargedQuery_eq_spend q L a e pass st0.core sigma]
          have h := rawChargedStepWith_eq q L a e sigma A st0 sm
          rw [hph] at h
          simpa [hph, chargedPhaseTag] using h
    simp only [List.foldl_cons, hstep]
    exact ih _

end Kolmogorov
