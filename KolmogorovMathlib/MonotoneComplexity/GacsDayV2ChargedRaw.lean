import KolmogorovMathlib.MonotoneComplexity.GacsDayV2ChargedController
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedRaw

/-!
# An index-erased mirror of the V2 advantage-and-spend controller

`GacsDayLadderTailRaw.lean` mirrors the robust tail controller by an
index-erased state `RawState`, and `GacsDayChargedRaw.lean` extends the mirror
to the V1 charged controller (`RawChargedState = ℕ × RawState`).  The V2 block
controller of `GacsDayV2ChargedController.lean` stores a *wider* record:

* a round is a `GrayTailRoundV2 n b` with the three split scale fields
  `blockAnchor` / `childEps` / `fineEnd` instead of the single `epsDepth`
  (nine fields instead of seven);
* the core state is `GrayTailStateV2 n b`, which differs from `GrayTailState`
  only by carrying `List (GrayTailRoundV2 n b)` in `frozen`;
* the charged state is `GrayChargedStateV2 n b`, a `GrayChargedPhase` tag over
  that core — the phase type itself is **shared** with V1, so the tag mirror
  `chargedPhaseTag` of `GacsDayChargedRaw.lean` is reused verbatim.

This file mirrors those types by
`RawRoundV2` / `RawStateV2` / `RawChargedStateV2`, all built from `ℕ`, `Bool`,
`ℚ` and lists only (hence primitive codable), erases the V2-specific slot
geometry (`grayAdvBlockGrandsons`, `grayAdvBlockSlots`, `grayBlockNextSlots`,
`grayBlockSpendPairs`, `grayBlockSpendSlotsV2`, `grayChargedSlotsForPassV2`)
and the v15.1 raised-service wait (`grayChargedRaisedServedB`,
`grayChargedWaitServedB`), and finally mirrors the two transitions
(`grayChargedBlockTailStepV2`, `grayChargedStepV2`) with the answer of the
recursive child call supplied as an ordinary argument — exactly V1's device
for the oracle call.  Every mirror is certified by a displayed bridge lemma;
the key ones are `rawChargedBlockTailStepV2_eq` and `rawChargedStepV2With_eq`.

Everything record-agnostic (the harvest `rawGrayHarvest`, the narrow next
slots `rawNextSlots`, the frozen son base `rawFrozenSonBase`, the deficient
roots `rawChargedDeficientRoots`, the local server move `rawLocalServerMove`,
the quarter test `rawGlobalQuarterB`, the spare pairs `rawSparePairs`) is
reused from the V1 mirrors through the V1 view `rawRoundV2ToV1` of a raw V2
round, which mirrors `GrayTailRoundV2.toV1`.

No definition here is a new mathematical assumption: each is a transcription
of the corresponding V2 controller definition, verified by its bridge lemma.
Computability of these mirrors lives in
`GacsDayV2ChargedRawComputable.lean`.
-/

namespace Kolmogorov

/-! ### Erased V2 types -/

/-- An index-erased V2 frozen round:
`(roundIndex, serverTime, blockAnchor, childEps, fineEnd)` together with
`(slots, move, allocated, unavailable)`.  The two extra scale fields are the
only difference from V1's `RawRound`. -/
abbrev RawRoundV2 :=
  (ℕ × ℕ × ℕ × ℕ × ℕ) × List RawSlot × FamilyClientMove × List BitString × Allocation

/-- An index-erased V2 core state: `(time, roundStart, done)` together with
`(frozen, unavailable, slots, anchoringSlots, history)`. -/
abbrev RawStateV2 :=
  (ℕ × ℕ × Bool) × List RawRoundV2 × Allocation × List RawSlot ×
    List RawSlot × FamilyGameHistory

/-- An index-erased V2 charged state: the phase tag together with the erased
V2 core.  The phase tag encoding `chargedPhaseTag` is shared with V1. -/
abbrev RawChargedStateV2 := ℕ × RawStateV2

-- As for the V1 erased types: naming these instances keeps the later
-- `Primcodable` searches over the wide V2 products shallow.
instance instPrimcodableRawRoundV2 : Primcodable RawRoundV2 := inferInstance

instance instPrimcodableRawStateV2 : Primcodable RawStateV2 := inferInstance

instance instPrimcodableRawChargedStateV2 : Primcodable RawChargedStateV2 :=
  inferInstance

/-! ### Erasure maps -/

/-- Erase the indices of a V2 frozen round. -/
def toRawRoundV2 {n b : ℕ} (p : GrayTailRoundV2 n b) : RawRoundV2 :=
  ((p.roundIndex, p.serverTime, p.blockAnchor, p.childEps, p.fineEnd),
    (p.slots.map toRawSlot, p.move, p.allocated, p.unavailable))

/-- The erased V1 view of an erased V2 round: mirror of
`GrayTailRoundV2.toV1` (the block anchor plays the role of `epsDepth`). -/
def rawRoundV2ToV1 (p : RawRoundV2) : RawRound :=
  ((p.1.1, p.1.2.1, p.1.2.2.1), p.2)

/-- The erased V1 view of an erased V2 frozen ledger: mirror of
`frozenV1OfV2`. -/
def rawFrozenV1OfV2 (frozen : List RawRoundV2) : List RawRound :=
  frozen.map rawRoundV2ToV1

/-- Erase the indices of a V2 core state. -/
def toRawStateV2 {n b : ℕ} (st : GrayTailStateV2 n b) : RawStateV2 :=
  ((st.time, st.roundStart, st.done),
    (st.frozen.map toRawRoundV2, st.unavailable, st.slots.map toRawSlot,
      st.anchoringSlots.map toRawSlot, st.history))

/-- Erase a V2 charged controller state. -/
def toRawChargedStateV2 {n b : ℕ} (st : GrayChargedStateV2 n b) :
    RawChargedStateV2 :=
  (chargedPhaseTag st.phase, toRawStateV2 st.core)

/-- Erasure commutes with the V1 view of a round. -/
@[simp] theorem rawRoundV2ToV1_toRawRoundV2 {n b : ℕ} (p : GrayTailRoundV2 n b) :
    rawRoundV2ToV1 (toRawRoundV2 p) = toRawRound p.toV1 := rfl

/-- Erasure commutes with the V1 view of a frozen ledger. -/
theorem rawFrozenV1OfV2_map {n b : ℕ} (frozen : List (GrayTailRoundV2 n b)) :
    rawFrozenV1OfV2 (frozen.map toRawRoundV2) =
      (frozen.map GrayTailRoundV2.toV1).map toRawRound := by
  unfold rawFrozenV1OfV2
  simp [List.map_map, Function.comp_def]

/-- Erasure commutes with the V1 view of a state's frozen ledger. -/
theorem rawFrozenV1OfV2_toRawStateV2 {n b : ℕ} (st : GrayTailStateV2 n b) :
    rawFrozenV1OfV2 (toRawStateV2 st).2.1 = (frozenV1OfV2 st).map toRawRound := by
  unfold toRawStateV2 frozenV1OfV2
  exact rawFrozenV1OfV2_map st.frozen

/-- The encoding of V2 rounds is injective. -/
theorem toRawRoundV2_injective {n b : ℕ} :
    Function.Injective (toRawRoundV2 (n := n) (b := b)) := by
  rintro ⟨s1, r1, ba1, ce1, fe1, sl1, m1, al1, un1⟩
    ⟨s2, r2, ba2, ce2, fe2, sl2, m2, al2, un2⟩ h
  simp only [toRawRoundV2, Prod.mk.injEq] at h
  obtain ⟨⟨h1, h2, h3, h4, h5⟩, h6, h7, h8, h9⟩ := h
  have hsl : sl1 = sl2 :=
    List.map_injective_iff.mpr (toRawSlot_injective (n := n) (b := b)) h6
  subst h1; subst h2; subst h3; subst h4; subst h5
  subst hsl; subst h7; subst h8; subst h9
  rfl

/-! ### Erased V2 advantage block geometry -/

/-- The erased form of `grayAdvBlockGrandsons`: the slice `[grayAdvBlockOffset q L r, +
grayAdvBlockMult q L r)` of `List.range b`. -/
def rawAdvBlockGrandsons (b q L r : ℕ) : List ℕ :=
  ((List.range b).drop (grayAdvBlockOffset q L r)).take (grayAdvBlockMult q L r)

/-- The raw grandchildren of an adversary block are the structured ones, read as numbers. -/
theorem rawAdvBlockGrandsons_eq (b q L r : ℕ) :
    rawAdvBlockGrandsons b q L r =
      (grayAdvBlockGrandsons b q L r).map Fin.val := by
  unfold rawAdvBlockGrandsons grayAdvBlockGrandsons
  have hrange : List.range b = (List.finRange b).map Fin.val := by simp
  rw [hrange, ← List.map_drop, ← List.map_take]

/-- The erased form of `grayAdvBlockSlots`: all triples `(i, c, g)` with `i < n`, `c < used` a
source son and `g` in the grandson block of round `r`. -/
def rawAdvBlockSlots (n b used q L r : ℕ) : List RawSlot :=
  (List.range n).flatMap fun i =>
    ((List.range b).filter fun c => decide (c < used)).flatMap fun c =>
      (rawAdvBlockGrandsons b q L r).map fun g => (i, c, g)

/-- The raw slots of an adversary block are the encodings of the structured slots. -/
theorem rawAdvBlockSlots_eq (n b used q L r : ℕ) :
    rawAdvBlockSlots n b used q L r =
      (grayAdvBlockSlots n b used q L r).map toRawSlot := by
  unfold rawAdvBlockSlots grayAdvBlockSlots
  rw [List.map_flatMap]
  refine (flatMap_finRange_eq_flatMap_range n _ _ ?_).symm
  intro i
  rw [List.map_flatMap,
    ← filter_finRange_map_val b (fun c => decide (c < used)), List.flatMap_map]
  refine List.flatMap_congr fun c _ => ?_
  rw [rawAdvBlockGrandsons_eq, List.map_map, List.map_map]
  rfl

/-- Erased form of `grayBlockNextSlots`: the wide advantage next-slots. -/
def rawBlockNextSlots (n b q L e used round : ℕ) (threshold : ℚ) (A : Allocation)
    (frozen : List RawRound) (sm : FamilyServerMove) : List RawSlot :=
  (List.range n).flatMap fun i =>
    ((List.range b).filter fun c =>
      decide (c < used) &&
      !(decide (threshold < rawFrozenSonBase frozen i c)) &&
      !(getTailFamilyReserve e b A n i sm [c]).isSome).flatMap fun c =>
        (rawAdvBlockGrandsons b q L round).map fun g => (i, c, g)

/-- The raw slots of the next block round are the encodings of the structured ones. -/
theorem rawBlockNextSlots_eq {n b : ℕ} (q L e used round : ℕ) (threshold : ℚ)
    (A : Allocation) (frozen : GrayTailFrozen n b) (sm : FamilyServerMove) :
    rawBlockNextSlots n b q L e used round threshold A (frozen.map toRawRound) sm =
      (grayBlockNextSlots q L e used round threshold A frozen sm).map toRawSlot := by
  unfold rawBlockNextSlots grayBlockNextSlots
  rw [List.map_flatMap]
  refine (flatMap_finRange_eq_flatMap_range n _ _ ?_).symm
  intro i
  rw [List.map_flatMap,
    ← filter_finRange_map_val b (fun c =>
      decide (c < used) &&
      !(decide (threshold < rawFrozenSonBase (frozen.map toRawRound) i.val c)) &&
      !(getTailFamilyReserve e b A n i.val sm [c]).isSome),
    List.flatMap_map]
  have hpred : (fun c : Fin b =>
      decide (c.val < used) &&
      !(decide (threshold < rawFrozenSonBase (frozen.map toRawRound) i.val c.val)) &&
      !(getTailFamilyReserve e b A n i.val sm [c.val]).isSome) =
      fun c : Fin b =>
        decide (c.val < used) &&
        !(decide (threshold < grayTailFrozenSonBase frozen i c)) &&
        !(getTailFamilyReserve e b A n i.val sm [c.val]).isSome := by
    funext c
    rw [rawFrozenSonBase_eq]
  simp only [hpred]
  refine List.flatMap_congr fun c _ => ?_
  rw [rawAdvBlockGrandsons_eq, List.map_map, List.map_map]
  rfl

/-! ### Erased V2 spend block geometry -/

/-- The erased form of `grayBlockSpendPairs`: the `graySpendMult L pass` spare pairs of
`rawSparePairs b source` starting at the cumulative offset `grayBlockSpendOffset L pass`. -/
def rawBlockSpendPairs (b source L pass : ℕ) : List (ℕ × ℕ) :=
  ((rawSparePairs b source).drop (grayBlockSpendOffset L pass)).take
    (graySpendMult L pass)

/-- The raw spend pairs of a block pass are the structured ones, read as numbers. -/
theorem rawBlockSpendPairs_eq (b source L pass : ℕ) :
    rawBlockSpendPairs b source L pass =
      (grayBlockSpendPairs b source L pass).map fun p => (p.1.val, p.2.val) := by
  unfold rawBlockSpendPairs grayBlockSpendPairs
  rw [rawSparePairs_eq, ← List.map_drop, ← List.map_take]

/-- The erased form of `grayBlockSpendSlotsV2`: for every deficient root `i`, the slots `(i, c, g)`
over the spare pairs `(c, g)` of the pass. -/
def rawBlockSpendSlotsV2 (n b source L pass : ℕ) (threshold eps alpha : ℚ)
    (frozen : List RawRound) : List RawSlot :=
  (rawChargedDeficientRoots n b source threshold eps alpha frozen).flatMap fun i =>
    (rawBlockSpendPairs b source L pass).map fun p => (i, p.1, p.2)

/-- The raw spend slots of a block pass are the encodings of the structured ones. -/
theorem rawBlockSpendSlotsV2_eq {n b : ℕ} (source L pass : ℕ)
    (threshold eps alpha : ℚ) (frozen : GrayTailFrozen n b) :
    rawBlockSpendSlotsV2 n b source L pass threshold eps alpha
        (frozen.map toRawRound) =
      (grayBlockSpendSlotsV2 source L pass threshold eps alpha frozen).map
        toRawSlot := by
  unfold rawBlockSpendSlotsV2 grayBlockSpendSlotsV2
  rw [rawChargedDeficientRoots_eq, List.map_flatMap, List.flatMap_map]
  refine List.flatMap_congr fun i _ => ?_
  rw [rawBlockSpendPairs_eq, List.map_map, List.map_map]
  rfl

/-- The erased form of `grayChargedSlotsForPassV2`: `rawBlockSpendSlotsV2` at the source count
`grayChargedSourceCount a e`, the threshold `grayChargedThreshold q e` and the scales
`dyadicScale e`, `dyadicScale a`, over the V1 view of the frozen ledger. -/
def rawChargedSlotsForPassV2 (q L a e n b pass : ℕ) (frozen : List RawRoundV2) :
    List RawSlot :=
  rawBlockSpendSlotsV2 n b (grayChargedSourceCount a e) L pass
    (grayChargedThreshold q e) (dyadicScale e) (dyadicScale a)
    (rawFrozenV1OfV2 frozen)

/-- The raw slots of a V2 pass are the encodings of the structured slots of that pass. -/
theorem rawChargedSlotsForPassV2_eq {n b : ℕ} (q L a e pass : ℕ)
    (frozen : List (GrayTailRoundV2 n b)) :
    rawChargedSlotsForPassV2 q L a e n b pass (frozen.map toRawRoundV2) =
      (grayChargedSlotsForPassV2 q L a e pass frozen).map toRawSlot := by
  unfold rawChargedSlotsForPassV2 grayChargedSlotsForPassV2
  rw [rawFrozenV1OfV2_map]
  exact rawBlockSpendSlotsV2_eq _ _ _ _ _ _ _

/-! ### The erased raised-service wait (v15.1 A3) -/

/-- Erased form of `grayChargedRaisedServedB`.  `servesB` is already index
free, so only the two `finRange` quantifiers are erased. -/
def rawChargedRaisedServedB (n b e used : ℕ) (threshold : ℚ)
    (frozen : List RawRound) (sm : FamilyServerMove) : Bool :=
  (List.range n).all fun i => (List.range b).all fun j =>
    if j < used ∧ threshold < rawFrozenSonBase frozen i j then
      servesB (getFamilyAlloc sm i [j]) (dyadicScale e)
    else true

/-- The raw test for a served raised child agrees with the structured one. -/
theorem rawChargedRaisedServedB_eq {n b : ℕ} (e used : ℕ) (threshold : ℚ)
    (frozen : GrayTailFrozen n b) (sm : FamilyServerMove) :
    rawChargedRaisedServedB n b e used threshold (frozen.map toRawRound) sm =
      grayChargedRaisedServedB e used threshold frozen sm := by
  unfold rawChargedRaisedServedB grayChargedRaisedServedB
  rw [← all_finRange_eq_all_range]
  congr 1
  funext i
  rw [← all_finRange_eq_all_range]
  congr 1
  funext j
  rw [rawFrozenSonBase_eq]

/-- The erased form of `grayChargedWaitServedB`: the raised-service test at scale `e` for the source
sons of the V1 view of the core's frozen ledger. -/
def rawChargedWaitServedB (q a e n b : ℕ) (core : RawStateV2)
    (sm : FamilyServerMove) : Bool :=
  rawChargedRaisedServedB n b e (grayChargedSourceCount a e)
    (grayChargedThreshold q e) (rawFrozenV1OfV2 core.2.1) sm

/-- The raw test for a served waiting round agrees with the structured one. -/
theorem rawChargedWaitServedB_eq {n b : ℕ} (q a e : ℕ)
    (core : GrayTailStateV2 n b) (sm : FamilyServerMove) :
    rawChargedWaitServedB q a e n b (toRawStateV2 core) sm =
      grayChargedWaitServedB q a e core sm := by
  unfold rawChargedWaitServedB grayChargedWaitServedB
  rw [rawFrozenV1OfV2_toRawStateV2]
  exact rawChargedRaisedServedB_eq _ _ _ _ _

/-! ### The erased V2 advantage transition -/

/-- Erased form of `grayChargedBlockTailStepV2`, with the answer of the
recursive child call supplied as an ordinary argument. -/
def rawChargedBlockTailStepV2 (q L a e n b : ℕ) (A : Allocation) (st : RawStateV2)
    (sm : FamilyServerMove) (current : FamilyClientMove) : RawStateV2 :=
  if st.1.2.2 then
    ((st.1.1 + 1, st.1.2.1, st.1.2.2), st.2)
  else if st.2.2.2.1.isEmpty then
    ((st.1.1 + 1, st.1.2.1, st.1.2.2), st.2)
  else
    let epsRound := grayTailRoundEps q L e st.2.1.length
    let deltaRound := grayTailRoundDelta q L e st.2.1.length
    let localSM := rawLocalServerMove deltaRound b st.2.2.2.1 sm
    if grayChargedBlockGoalAtB q L e st.2.1.length st.2.2.2.1.length st.2.2.1
        current localSM then
      let allocated := grayTailLocalAllocatedList localSM
      let frozen' := st.2.1 ++
        [((st.2.1.length, st.1.1, epsRound, epsRound + graySpendSpan q,
            deltaRound),
          (st.2.2.2.1, current, allocated, st.2.2.1))]
      let frozenV1 := rawFrozenV1OfV2 frozen'
      let threshold := dyadicScale e -
        dyadicScale e / (6 * halfAmplification q)
      let source := grayChargedSourceCount a e
      let candidates := rawBlockNextSlots n b q L e source frozen'.length
        threshold A frozenV1 sm
      let unavailable' := A ++
        rawGrayHarvest (grayTailRoundDelta q L e frozen'.length) b candidates n sm
      let done' :=
        rawGlobalQuarterB n source
            (rawNextSlots n b e source frozen'.length threshold A frozenV1 sm) ||
          decide (grayChargedAdvantageRoundCount q ≤ frozen'.length)
      ((st.1.1 + 1, st.1.1 + 1, done'),
        (frozen', unavailable', candidates, [], ([], [])))
    else
      ((st.1.1 + 1, st.1.2.1, st.1.2.2),
        (st.2.1, st.2.2.1, st.2.2.2.1, st.2.2.2.2.1,
          (st.2.2.2.2.2.1 ++ [current], st.2.2.2.2.2.2 ++ [localSM])))

/-- The V2 round appended by one winning advantage step. -/
def grayChargedBlockStepRoundV2 {n b : ℕ} (q L e : ℕ)
    (sigma : FamilyStrategyScheme) (st : GrayTailStateV2 n b)
    (sm : FamilyServerMove) : GrayTailRoundV2 n b where
  serverTime := st.time
  roundIndex := st.frozen.length
  blockAnchor := grayTailRoundEps q L e st.frozen.length
  childEps := grayTailRoundEps q L e st.frozen.length + graySpendSpan q
  fineEnd := grayTailRoundDelta q L e st.frozen.length
  slots := st.slots
  move := grayBlockCurrentMoveV2 q L e sigma st
  allocated := grayTailLocalAllocatedList
    (grayTailLocalServerMove (grayTailRoundDelta q L e st.frozen.length)
      st.slots sm)
  unavailable := st.unavailable

/-- **The V2 advantage transition commutes with erasure.** -/
theorem rawChargedBlockTailStepV2_eq {n b : ℕ} (q L a e : ℕ)
    (sigma : FamilyStrategyScheme) (A : Allocation) (st : GrayTailStateV2 n b)
    (sm : FamilyServerMove) :
    rawChargedBlockTailStepV2 q L a e n b A (toRawStateV2 st) sm
        (grayBlockCurrentMoveV2 q L e sigma st) =
      toRawStateV2 (grayChargedBlockTailStepV2 q L a e sigma A st sm) := by
  unfold rawChargedBlockTailStepV2 grayChargedBlockTailStepV2
  simp only [toRawStateV2, List.isEmpty_map, List.length_map]
  by_cases hd : st.done = true
  · rw [if_pos hd]
    simp [hd]
  · rw [if_neg hd]
    by_cases hs : st.slots.isEmpty = true
    · rw [if_pos hs]
      simp [hd, hs]
    · rw [if_neg hs]
      simp only [hd, hs]
      rw [rawLocalServerMove_eq]
      by_cases hgoal : grayChargedBlockGoalAtB q L e st.frozen.length
          st.slots.length st.unavailable
          (grayBlockCurrentMoveV2 q L e sigma st)
          (grayTailLocalServerMove
            (grayTailRoundDelta q L e st.frozen.length) st.slots sm) = true
      · rw [if_pos hgoal, if_pos hgoal]
        have hfr : (st.frozen.map toRawRoundV2 ++
              [((st.frozen.length, st.time,
                  grayTailRoundEps q L e st.frozen.length,
                  grayTailRoundEps q L e st.frozen.length + graySpendSpan q,
                  grayTailRoundDelta q L e st.frozen.length),
                (st.slots.map toRawSlot,
                  grayBlockCurrentMoveV2 q L e sigma st,
                  grayTailLocalAllocatedList
                    (grayTailLocalServerMove
                      (grayTailRoundDelta q L e st.frozen.length) st.slots sm),
                  st.unavailable))]) =
            (st.frozen ++
              [grayChargedBlockStepRoundV2 q L e sigma st sm]).map toRawRoundV2 := by
          simp [grayChargedBlockStepRoundV2, toRawRoundV2]
        rw [hfr, rawFrozenV1OfV2_map, rawBlockNextSlots_eq, rawNextSlots_eq,
          rawGrayHarvest_eq, rawGlobalQuarterB_eq]
        simp [grayChargedBlockStepRoundV2, grayChargedSourceCount]
      · rw [if_neg hgoal, if_neg hgoal]
        simp

/-! ### The erased phase-tagged V2 transition -/

/-- Erased form of `grayChargedStartSpendV2`. -/
def rawChargedStartSpendV2 (q L a e n b : ℕ) (A : Allocation) (core : RawStateV2)
    (sm : FamilyServerMove) : RawChargedStateV2 :=
  if (rawChargedSlotsForPassV2 q L a e n b 0 core.2.1).isEmpty then
    (1, ((core.1.1, core.1.2.1, true),
      (core.2.1, core.2.2.1, [], core.2.2.2.2.1, ([], []))))
  else
    (2, ((core.1.1, core.1.1, false),
      (core.2.1,
        A ++ rawGrayHarvest (grayChargedSpendDelta a L e 0) b
          (rawChargedSlotsForPassV2 q L a e n b 0 core.2.1) n sm,
        rawChargedSlotsForPassV2 q L a e n b 0 core.2.1,
        core.2.2.2.2.1, ([], []))))

/-- The raw opening of a V2 spend pass computes the encoding of the structured one. -/
theorem rawChargedStartSpendV2_eq {n b : ℕ} (q L a e : ℕ) (A : Allocation)
    (core : GrayTailStateV2 n b) (sm : FamilyServerMove) :
    rawChargedStartSpendV2 q L a e n b A (toRawStateV2 core) sm =
      toRawChargedStateV2 (grayChargedStartSpendV2 q L a e A core sm) := by
  unfold rawChargedStartSpendV2 grayChargedStartSpendV2 toRawChargedStateV2
  simp only [toRawStateV2]
  simp only [rawChargedSlotsForPassV2_eq, rawGrayHarvest_eq, List.isEmpty_map]
  by_cases hemp : (grayChargedSlotsForPassV2 q L a e 0 core.frozen).isEmpty = true
  · simp only [if_pos hemp]
    simp [chargedPhaseTag]
  · simp only [if_neg hemp]
    simp [chargedPhaseTag]

/-- Erased form of `grayChargedStepV2`, with the answer of the recursive child
call supplied as an ordinary argument. -/
def rawChargedStepV2With (q L a e n b : ℕ) (A : Allocation) (tag : ℕ)
    (st : RawStateV2) (sm : FamilyServerMove) (current : FamilyClientMove) :
    RawChargedStateV2 :=
  if tag = 1 then
    (1, ((st.1.1 + 1, st.1.2.1, st.1.2.2), st.2))
  else if tag = 0 then
    if (rawChargedBlockTailStepV2 q L a e n b A st sm current).1.2.2 then
      if rawChargedWaitServedB q a e n b
          (rawChargedBlockTailStepV2 q L a e n b A st sm current) sm then
        rawChargedStartSpendV2 q L a e n b A
          (rawChargedBlockTailStepV2 q L a e n b A st sm current) sm
      else (0, rawChargedBlockTailStepV2 q L a e n b A st sm current)
    else (0, rawChargedBlockTailStepV2 q L a e n b A st sm current)
  else
    if st.2.2.2.1.isEmpty then
      (1, ((st.1.1 + 1, st.1.2.1, true), st.2))
    else
      let epsRound := grayChargedSpendEps a L e (tag - 2)
      let deltaRound := grayChargedSpendDelta a L e (tag - 2)
      let localSM := rawLocalServerMove deltaRound b st.2.2.2.1 sm
      if grayChargedBlockSpendGoalAtB q L a e (tag - 2) st.2.2.2.1.length
          st.2.2.1 current localSM then
        let allocated := grayTailLocalAllocatedList localSM
        let frozen' := st.2.1 ++
          [((st.2.1.length, st.1.1, epsRound, epsRound + graySpendSpan q,
              deltaRound),
            (st.2.2.2.1, current, allocated, st.2.2.1))]
        let unavailable' := A ++
          rawGrayHarvest (grayChargedSpendDelta a L e (tag - 2 + 1)) b
            (rawChargedSlotsForPassV2 q L a e n b (tag - 2 + 1) frozen') n sm
        if tag - 2 + 1 < 8 then
          if (rawChargedSlotsForPassV2 q L a e n b (tag - 2 + 1) frozen').isEmpty then
            ((1 : ℕ), ((st.1.1 + 1, st.1.1 + 1, true),
              (frozen', unavailable', [], [], ([], []))))
          else
            (tag - 2 + 3, ((st.1.1 + 1, st.1.1 + 1, false),
              (frozen', unavailable',
                rawChargedSlotsForPassV2 q L a e n b (tag - 2 + 1) frozen',
                [], ([], []))))
        else
          ((1 : ℕ), ((st.1.1 + 1, st.1.1 + 1, true),
            (frozen', unavailable', [], [], ([], []))))
      else
        (tag, ((st.1.1 + 1, st.1.2.1, st.1.2.2),
          (st.2.1, st.2.2.1, st.2.2.2.1, st.2.2.2.2.1,
            (st.2.2.2.2.2.1 ++ [current], st.2.2.2.2.2.2 ++ [localSM]))))

/-- The V2 round appended by one winning spend pass. -/
def grayChargedSpendStepRoundV2 {n b : ℕ} (q L a e pass : ℕ)
    (sigma : FamilyStrategyScheme) (st : GrayTailStateV2 n b)
    (sm : FamilyServerMove) : GrayTailRoundV2 n b where
  serverTime := st.time
  roundIndex := st.frozen.length
  blockAnchor := grayChargedSpendEps a L e pass
  childEps := grayChargedSpendEps a L e pass + graySpendSpan q
  fineEnd := grayChargedSpendDelta a L e pass
  slots := st.slots
  move := grayBlockSpendMoveV2 q L a e pass sigma st
  allocated := grayTailLocalAllocatedList
    (grayTailLocalServerMove (grayChargedSpendDelta a L e pass) st.slots sm)
  unavailable := st.unavailable

/-- **The V2 charged transition commutes with erasure.**  This is the theorem
that connects the raw phase-tagged transition with the actual
`grayChargedStepV2`, including the v15.1 raised-service wait. -/
theorem rawChargedStepV2With_eq {n b : ℕ} (q L a e : ℕ)
    (sigma : FamilyStrategyScheme) (A : Allocation) (st : GrayChargedStateV2 n b)
    (sm : FamilyServerMove) :
    rawChargedStepV2With q L a e n b A (chargedPhaseTag st.phase)
        (toRawStateV2 st.core) sm
        (match st.phase with
          | .spend pass => grayBlockSpendMoveV2 q L a e pass sigma st.core
          | _ => grayBlockCurrentMoveV2 q L e sigma st.core) =
      toRawChargedStateV2 (grayChargedStepV2 q L a e sigma A st sm) := by
  unfold rawChargedStepV2With grayChargedStepV2
  cases hph : st.phase with
  | done =>
    simp only [chargedPhaseTag]
    simp [toRawChargedStateV2, toRawStateV2, chargedPhaseTag]
  | advantage =>
    simp only [chargedPhaseTag]
    norm_num
    rw [rawChargedBlockTailStepV2_eq q L a e sigma A st.core sm]
    by_cases hdone :
        (grayChargedBlockTailStepV2 q L a e sigma A st.core sm).done = true
    · rw [if_pos (by simpa [toRawStateV2] using hdone), if_pos hdone]
      rw [rawChargedWaitServedB_eq]
      by_cases hserved : grayChargedWaitServedB q a e
          (grayChargedBlockTailStepV2 q L a e sigma A st.core sm) sm = true
      · rw [if_pos hserved, if_pos hserved]
        exact rawChargedStartSpendV2_eq q L a e A _ sm
      · rw [if_neg hserved, if_neg hserved]
        simp [toRawChargedStateV2, chargedPhaseTag]
    · rw [if_neg (by simpa [toRawStateV2] using hdone), if_neg hdone]
      simp [toRawChargedStateV2, chargedPhaseTag]
  | spend pass =>
    have h1 : chargedPhaseTag (GrayChargedPhase.spend pass) = pass + 2 := rfl
    rw [h1]
    rw [if_neg (by omega), if_neg (by omega)]
    have hsub : pass + 2 - 2 = pass := by omega
    simp only [hsub, toRawStateV2, List.isEmpty_map, List.length_map]
    by_cases hs : st.core.slots.isEmpty = true
    · rw [if_pos hs, if_pos hs]
      simp [toRawChargedStateV2, toRawStateV2, chargedPhaseTag]
    · rw [if_neg hs, if_neg hs]
      rw [rawLocalServerMove_eq]
      by_cases hgoal : grayChargedBlockSpendGoalAtB q L a e pass
          st.core.slots.length st.core.unavailable
          (grayBlockSpendMoveV2 q L a e pass sigma st.core)
          (grayTailLocalServerMove
            (grayChargedSpendDelta a L e pass) st.core.slots sm) = true
      · rw [if_pos hgoal, if_pos hgoal]
        have hfr : (st.core.frozen.map toRawRoundV2 ++
              [((st.core.frozen.length, st.core.time,
                  grayChargedSpendEps a L e pass,
                  grayChargedSpendEps a L e pass + graySpendSpan q,
                  grayChargedSpendDelta a L e pass),
                (st.core.slots.map toRawSlot,
                  grayBlockSpendMoveV2 q L a e pass sigma st.core,
                  grayTailLocalAllocatedList
                    (grayTailLocalServerMove
                      (grayChargedSpendDelta a L e pass) st.core.slots sm),
                  st.core.unavailable))]) =
            (st.core.frozen ++
              [grayChargedSpendStepRoundV2 q L a e pass sigma st.core sm]).map
                toRawRoundV2 := by
          simp [grayChargedSpendStepRoundV2, toRawRoundV2]
        have hpr : ({ serverTime := st.core.time
                      roundIndex := st.core.frozen.length
                      blockAnchor := grayChargedSpendEps a L e pass
                      childEps := grayChargedSpendEps a L e pass + graySpendSpan q
                      fineEnd := grayChargedSpendDelta a L e pass
                      slots := st.core.slots
                      move := grayBlockSpendMoveV2 q L a e pass sigma st.core
                      allocated := grayTailLocalAllocatedList
                        (grayTailLocalServerMove
                          (grayChargedSpendDelta a L e pass) st.core.slots sm)
                      unavailable := st.core.unavailable } :
                    GrayTailRoundV2 n b) =
            grayChargedSpendStepRoundV2 q L a e pass sigma st.core sm := rfl
        rw [hpr, hfr, rawChargedSlotsForPassV2_eq, rawGrayHarvest_eq,
          List.isEmpty_map]
        by_cases hp : pass + 1 < 8
        · by_cases hemp : (grayChargedSlotsForPassV2 q L a e (pass + 1)
              (st.core.frozen ++
                [grayChargedSpendStepRoundV2 q L a e pass sigma st.core sm])).isEmpty
              = true
          · simp only [if_pos hp, if_pos hemp]
            simp [toRawChargedStateV2, toRawStateV2, chargedPhaseTag,
              grayChargedSpendStepRoundV2, toRawRoundV2]
          · simp only [if_pos hp, if_neg hemp]
            simp [toRawChargedStateV2, toRawStateV2, chargedPhaseTag,
              grayChargedSpendStepRoundV2, toRawRoundV2]
        · simp only [if_neg hp]
          simp [toRawChargedStateV2, toRawStateV2, chargedPhaseTag,
            grayChargedSpendStepRoundV2, toRawRoundV2]
      · rw [if_neg hgoal, if_neg hgoal]
        simp [toRawChargedStateV2, toRawStateV2, chargedPhaseTag]

/-! ### The erased child query -/

/-- The scheme input of the single recursive child call made in a V2 charged
state: the advantage phase queries the block anchor `ε_r` with child bin
`ε_r + graySpendSpan q`, spend pass `p` queries the pass anchor with the same
schedule-correct child offset. -/
def rawChargedQueryV2 (q L a e : ℕ) (tag : ℕ) (st : RawStateV2) : SchemeInput :=
  if tag < 2 then
    ((grayTailRoundEps q L e st.2.1.length,
        grayTailRoundEps q L e st.2.1.length + graySpendSpan q),
      (st.2.2.1, (st.2.2.2.1.length, st.2.2.2.2.2)))
  else
    ((grayChargedSpendEps a L e (tag - 2),
        grayChargedSpendEps a L e (tag - 2) + graySpendSpan q),
      (st.2.2.1, (st.2.2.2.1.length, st.2.2.2.2.2)))

/-- On a tag below `2`, the raw V2 query hands the scheme the arguments that produce the current
block move. -/
theorem rawChargedQueryV2_eq_advantage {n b : ℕ} (q L a e : ℕ)
    (st : GrayTailStateV2 n b) (sigma : FamilyStrategyScheme)
    {tag : ℕ} (htag : tag < 2) :
    sigma (rawChargedQueryV2 q L a e tag (toRawStateV2 st)).1.1
        (rawChargedQueryV2 q L a e tag (toRawStateV2 st)).1.2
        (rawChargedQueryV2 q L a e tag (toRawStateV2 st)).2.1
        (rawChargedQueryV2 q L a e tag (toRawStateV2 st)).2.2.1
        (rawChargedQueryV2 q L a e tag (toRawStateV2 st)).2.2.2 =
      grayBlockCurrentMoveV2 q L e sigma st := by
  unfold rawChargedQueryV2 grayBlockCurrentMoveV2 toRawStateV2
  rw [if_pos htag]
  simp

/-- On the tag `pass + 2`, the raw V2 query hands the scheme the arguments that produce the block
spend move of that pass. -/
theorem rawChargedQueryV2_eq_spend {n b : ℕ} (q L a e pass : ℕ)
    (st : GrayTailStateV2 n b) (sigma : FamilyStrategyScheme) :
    sigma (rawChargedQueryV2 q L a e (pass + 2) (toRawStateV2 st)).1.1
        (rawChargedQueryV2 q L a e (pass + 2) (toRawStateV2 st)).1.2
        (rawChargedQueryV2 q L a e (pass + 2) (toRawStateV2 st)).2.1
        (rawChargedQueryV2 q L a e (pass + 2) (toRawStateV2 st)).2.2.1
        (rawChargedQueryV2 q L a e (pass + 2) (toRawStateV2 st)).2.2.2 =
      grayBlockSpendMoveV2 q L a e pass sigma st := by
  unfold rawChargedQueryV2 grayBlockSpendMoveV2 toRawStateV2
  rw [if_neg (by omega)]
  simp

/-- On the tag of a state's phase, the raw V2 query hands the scheme the arguments that produce
the move of that phase. -/
theorem rawChargedQueryV2_eq_phase {n b : ℕ} (q L a e : ℕ)
    (st : GrayChargedStateV2 n b) (sigma : FamilyStrategyScheme) :
    sigma (rawChargedQueryV2 q L a e (chargedPhaseTag st.phase)
          (toRawStateV2 st.core)).1.1
        (rawChargedQueryV2 q L a e (chargedPhaseTag st.phase)
          (toRawStateV2 st.core)).1.2
        (rawChargedQueryV2 q L a e (chargedPhaseTag st.phase)
          (toRawStateV2 st.core)).2.1
        (rawChargedQueryV2 q L a e (chargedPhaseTag st.phase)
          (toRawStateV2 st.core)).2.2.1
        (rawChargedQueryV2 q L a e (chargedPhaseTag st.phase)
          (toRawStateV2 st.core)).2.2.2 =
      (match st.phase with
        | .spend pass => grayBlockSpendMoveV2 q L a e pass sigma st.core
        | _ => grayBlockCurrentMoveV2 q L e sigma st.core) := by
  cases hph : st.phase with
  | advantage =>
      simpa [chargedPhaseTag] using
        rawChargedQueryV2_eq_advantage q L a e st.core sigma
          (tag := 0) (by omega)
  | done =>
      simpa [chargedPhaseTag] using
        rawChargedQueryV2_eq_advantage q L a e st.core sigma
          (tag := 1) (by omega)
  | spend pass =>
      simpa [chargedPhaseTag] using
        rawChargedQueryV2_eq_spend q L a e pass st.core sigma

/-! ### The erased initial state and fold -/

/-- The erased form of `grayChargedBlockTailInitialStateV2`: time and round start `0`, not done, no
frozen round, unavailable set `A`, the wide block `rawAdvBlockSlots n b (grayChargedSourceCount
a e) q L 0`, no anchoring slot and the empty history. -/
def rawInitialStateV2 (n b a e q L : ℕ) (A : Allocation) : RawStateV2 :=
  ((0, 0, false),
    ([], A, rawAdvBlockSlots n b (grayChargedSourceCount a e) q L 0, [],
      ([], [])))

/-- The raw initial V2 state is the encoding of the structured initial state. -/
theorem rawInitialStateV2_eq (n b a e q L : ℕ) (A : Allocation) :
    rawInitialStateV2 n b a e q L A =
      toRawStateV2 (grayChargedBlockTailInitialStateV2 n b a e q L A) := by
  unfold rawInitialStateV2 toRawStateV2 grayChargedBlockTailInitialStateV2
  simp [rawAdvBlockSlots_eq]

/-- The erased V2 charged fold, driven by a supplied family of answers. -/
def rawChargedFoldV2With (q L a e n b : ℕ) (A : Allocation)
    (cur : ℕ → RawStateV2 → FamilyClientMove) (history : List FamilyServerMove) :
    RawChargedStateV2 :=
  history.foldl
    (fun stc sm => rawChargedStepV2With q L a e n b A stc.1 stc.2 sm (cur stc.1 stc.2))
    (0, rawInitialStateV2 n b a e q L A)

/-- Folding the raw V2 step over a history computes the encoding of the structured V2 controller
state. -/
theorem rawChargedFoldV2With_eq {n b : ℕ} (q L a e : ℕ)
    (sigma : FamilyStrategyScheme) (A : Allocation)
    (history : List FamilyServerMove) :
    rawChargedFoldV2With q L a e n b A
        (fun tag st => sigma (rawChargedQueryV2 q L a e tag st).1.1
          (rawChargedQueryV2 q L a e tag st).1.2
          (rawChargedQueryV2 q L a e tag st).2.1
          (rawChargedQueryV2 q L a e tag st).2.2.1
          (rawChargedQueryV2 q L a e tag st).2.2.2)
        history =
      toRawChargedStateV2
        (grayChargedFoldV2 (n := n) (b := b) q L a e sigma A history) := by
  unfold rawChargedFoldV2With grayChargedFoldV2
  have hinit : ((0 : ℕ), rawInitialStateV2 n b a e q L A) =
      toRawChargedStateV2 (grayChargedInitialStateV2 n b a e q L A) := by
    rw [rawInitialStateV2_eq]
    rfl
  rw [hinit]
  generalize grayChargedInitialStateV2 n b a e q L A = st0
  induction history generalizing st0 with
  | nil => simp
  | cons sm t ih =>
    have hstep :
        rawChargedStepV2With q L a e n b A (toRawChargedStateV2 st0).1
            (toRawChargedStateV2 st0).2 sm
            (sigma (rawChargedQueryV2 q L a e (toRawChargedStateV2 st0).1
                (toRawChargedStateV2 st0).2).1.1
              (rawChargedQueryV2 q L a e (toRawChargedStateV2 st0).1
                (toRawChargedStateV2 st0).2).1.2
              (rawChargedQueryV2 q L a e (toRawChargedStateV2 st0).1
                (toRawChargedStateV2 st0).2).2.1
              (rawChargedQueryV2 q L a e (toRawChargedStateV2 st0).1
                (toRawChargedStateV2 st0).2).2.2.1
              (rawChargedQueryV2 q L a e (toRawChargedStateV2 st0).1
                (toRawChargedStateV2 st0).2).2.2.2) =
          toRawChargedStateV2 (grayChargedStepV2 q L a e sigma A st0 sm) := by
      change rawChargedStepV2With q L a e n b A (chargedPhaseTag st0.phase)
          (toRawStateV2 st0.core) sm
          (sigma (rawChargedQueryV2 q L a e (chargedPhaseTag st0.phase)
              (toRawStateV2 st0.core)).1.1
            (rawChargedQueryV2 q L a e (chargedPhaseTag st0.phase)
              (toRawStateV2 st0.core)).1.2
            (rawChargedQueryV2 q L a e (chargedPhaseTag st0.phase)
              (toRawStateV2 st0.core)).2.1
            (rawChargedQueryV2 q L a e (chargedPhaseTag st0.phase)
              (toRawStateV2 st0.core)).2.2.1
            (rawChargedQueryV2 q L a e (chargedPhaseTag st0.phase)
              (toRawStateV2 st0.core)).2.2.2) =
          toRawChargedStateV2 (grayChargedStepV2 q L a e sigma A st0 sm)
      cases hph : st0.phase with
      | advantage =>
          rw [rawChargedQueryV2_eq_advantage q L a e st0.core sigma
            (by simp [chargedPhaseTag])]
          have h := rawChargedStepV2With_eq q L a e sigma A st0 sm
          rw [hph] at h
          simpa [hph] using h
      | done =>
          rw [rawChargedQueryV2_eq_advantage q L a e st0.core sigma
            (by simp [chargedPhaseTag])]
          have h := rawChargedStepV2With_eq q L a e sigma A st0 sm
          rw [hph] at h
          simpa [hph] using h
      | spend pass =>
          change rawChargedStepV2With q L a e n b A (pass + 2)
              (toRawStateV2 st0.core) sm
              (sigma (rawChargedQueryV2 q L a e (pass + 2)
                  (toRawStateV2 st0.core)).1.1
                (rawChargedQueryV2 q L a e (pass + 2)
                  (toRawStateV2 st0.core)).1.2
                (rawChargedQueryV2 q L a e (pass + 2)
                  (toRawStateV2 st0.core)).2.1
                (rawChargedQueryV2 q L a e (pass + 2)
                  (toRawStateV2 st0.core)).2.2.1
                (rawChargedQueryV2 q L a e (pass + 2)
                  (toRawStateV2 st0.core)).2.2.2) =
            toRawChargedStateV2 (grayChargedStepV2 q L a e sigma A st0 sm)
          rw [rawChargedQueryV2_eq_spend q L a e pass st0.core sigma]
          have h := rawChargedStepV2With_eq q L a e sigma A st0 sm
          rw [hph] at h
          simpa [hph, chargedPhaseTag] using h
    simp only [List.foldl_cons, hstep]
    exact ih _

/-! ### The erased displayed move -/

/-- The erased slots displayed by `grayChargedStrategyV2`: none over a done core, the open slots
otherwise; the next wide block, which has never been run, is not displayed. -/
def rawChargedDisplaySlotsV2 (st : RawStateV2) : List RawSlot :=
  cond st.1.2.2 [] st.2.2.2.1

/-- The erased current move displayed by `grayChargedStrategyV2`: the terminal phase displays
nothing, the advantage phase displays nothing over a done core (the raised-service wait repeats
the terminal display) or over an empty slot list, and a spend pass displays nothing over an
empty slot list. -/
def rawChargedDisplayCurrentV2 (tag : ℕ) (st : RawStateV2)
    (current : FamilyClientMove) : FamilyClientMove :=
  cond (decide (tag = 1)) []
    (cond (decide (tag = 0))
      (cond (st.1.2.2 || st.2.2.2.1.isEmpty) [] current)
      (cond st.2.2.2.1.isEmpty [] current))

/-- The erased displayed move of `grayChargedStrategyV2`: `rawChargedFamilyMove` at the source count
and threshold of the stage, over the V1 view of the frozen ledger and the displayed slots and
current move of the state. -/
def rawChargedOutputV2 (q a e n b : ℕ) (tag : ℕ) (st : RawStateV2)
    (current : FamilyClientMove) : FamilyClientMove :=
  rawChargedFamilyMove (grayChargedSourceCount a e) (grayChargedThreshold q e)
    (dyadicScale e) n b (rawFrozenV1OfV2 st.2.1)
    (rawChargedDisplaySlotsV2 st)
    (rawChargedDisplayCurrentV2 tag st current)

/-- **The displayed V2 move commutes with erasure.** -/
theorem rawChargedOutputV2_eq {n b : ℕ} (q L a e : ℕ)
    (sigma : FamilyStrategyScheme) (st : GrayChargedStateV2 n b) :
    rawChargedOutputV2 q a e n b (chargedPhaseTag st.phase)
        (toRawStateV2 st.core)
        (match st.phase with
          | .spend pass => grayBlockSpendMoveV2 q L a e pass sigma st.core
          | _ => grayBlockCurrentMoveV2 q L e sigma st.core) =
      grayChargedTailFamilyMove (grayChargedSourceCount a e)
        (grayChargedThreshold q e) (dyadicScale e) (frozenV1OfV2 st.core)
        (if st.core.done then [] else st.core.slots)
        (match st.phase with
          | .done => []
          | .advantage => if st.core.done || st.core.slots.isEmpty then []
            else grayBlockCurrentMoveV2 q L e sigma st.core
          | .spend pass => if st.core.slots.isEmpty then []
            else grayBlockSpendMoveV2 q L a e pass sigma st.core) := by
  have hslots : rawChargedDisplaySlotsV2 (toRawStateV2 st.core) =
      (if st.core.done then [] else st.core.slots).map toRawSlot := by
    unfold rawChargedDisplaySlotsV2
    by_cases hd : st.core.done = true <;> simp [toRawStateV2, hd]
  unfold rawChargedOutputV2
  rw [hslots, rawFrozenV1OfV2_toRawStateV2, rawChargedFamilyMove_eq]
  congr 1
  unfold rawChargedDisplayCurrentV2
  cases hph : st.phase with
  | done => simp [chargedPhaseTag]
  | advantage => simp [chargedPhaseTag, toRawStateV2]
  | spend pass => simp [chargedPhaseTag, toRawStateV2]

/-! ### Packed parameters

The oracle assembly of the next module trades in a single packed parameter, as
V1's `RawParam` does, to keep the projection chains of the computability
statements shallow. -/

/-- The static parameters of the erased V2 controller: `((q, L, a, e), (n, b), A)`
(the same shape as V1's `RawParam`). -/
abbrev RawParamV2 := (ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ) × Allocation

instance instPrimcodableRawParamV2 : Primcodable RawParamV2 := inferInstance

/-- `rawChargedQueryV2` in packed form. -/
def rawQueryOfV2 (P : RawParamV2) (stc : RawChargedStateV2) : SchemeInput :=
  rawChargedQueryV2 P.1.1 P.1.2.1 P.1.2.2.1 P.1.2.2.2 stc.1 stc.2

/-- `rawChargedStepV2With` in packed form. -/
def rawStepOfV2 (P : RawParamV2) (stc : RawChargedStateV2)
    (sm : FamilyServerMove) (cur : FamilyClientMove) : RawChargedStateV2 :=
  rawChargedStepV2With P.1.1 P.1.2.1 P.1.2.2.1 P.1.2.2.2 P.2.1.1 P.2.1.2 P.2.2
    stc.1 stc.2 sm cur

/-- `rawChargedOutputV2` in packed form. -/
def rawOutputOfV2 (P : RawParamV2) (stc : RawChargedStateV2)
    (cur : FamilyClientMove) : FamilyClientMove :=
  rawChargedOutputV2 P.1.1 P.1.2.2.1 P.1.2.2.2 P.2.1.1 P.2.1.2 stc.1 stc.2 cur

/-- The initial erased V2 charged state in packed form. -/
def rawInitialStateOfV2 (P : RawParamV2) : RawChargedStateV2 :=
  (0, rawInitialStateV2 P.2.1.1 P.2.1.2 P.1.2.2.1 P.1.2.2.2 P.1.1 P.1.2.1 P.2.2)

/-- The `Encodable` code of the displayed move of the raw charged controller at a state. -/
def rawOutputEncV2 (P : RawParamV2) (stc : RawChargedStateV2)
    (cur : FamilyClientMove) : ℕ :=
  @Encodable.encode FamilyClientMove Primcodable.toEncodable
    (rawOutputOfV2 P stc cur)

/-- The packed initial state is the erasure of the V2 charged initial state. -/
theorem rawInitialStateOfV2_eq (P : RawParamV2) :
    rawInitialStateOfV2 P =
      toRawChargedStateV2
        (grayChargedInitialStateV2 P.2.1.1 P.2.1.2 P.1.2.2.1 P.1.2.2.2 P.1.1
          P.1.2.1 P.2.2) := by
  unfold rawInitialStateOfV2
  rw [rawInitialStateV2_eq]
  rfl

end Kolmogorov
