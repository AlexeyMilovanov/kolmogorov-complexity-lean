import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailController

/-!
# An index-erased mirror of the tail controller

The executable tail controller of `GacsDayLadderTailController.lean` stores its
slots as elements of `Fin n × Fin b × Fin b`, so its state type
`GrayTailState n b` *depends* on two runtime numbers.  Dependent types of that
shape carry no uniform `Primcodable` structure, so the controller cannot be fed
to the computability library directly.

This file mirrors every controller construction by an *index-erased* version
which stores slots as plain natural triples and receives `n` and `b` as
ordinary arguments, and proves that the mirror computes exactly the same data
(`rawState_grayTailStep`, `rawOutput_grayTailOutput`, `rawFold_grayTailFold`).
The mirror types are built from `ℕ`, `Bool`, `ℚ` and lists only, so they are
primitive codable; the computability proofs live in
`GacsDayLadderTailRawComputable.lean`.

No definition here is a new mathematical assumption: each is a transcription of
the corresponding controller definition, and each transcription is verified by
the displayed bridge lemma.
-/

namespace Kolmogorov

/-! ### Erased types -/

/-- An index-erased slot: the outer root, the root son and the grandson. -/
abbrev RawSlot := ℕ × ℕ × ℕ

/-- An index-erased frozen round: `(roundIndex, serverTime, epsDepth)` together
with `(slots, move, allocated, unavailable)`. -/
abbrev RawRound := (ℕ × ℕ × ℕ) × List RawSlot × FamilyClientMove × List BitString × Allocation

/-- An index-erased controller state: `(time, roundStart, done)` together with
`(frozen, unavailable, slots, anchoringSlots, history)`. -/
abbrev RawState :=
  (ℕ × ℕ × Bool) × List RawRound × Allocation × List RawSlot ×
    List RawSlot × FamilyGameHistory

-- The erased types are wide nested products.  Naming their `Primcodable`
-- instances keeps every later instance search shallow: a search that meets
-- `RawRound` or `RawState` finds a single constant instead of re-deriving the
-- whole product each time.
instance instPrimcodableRawSlot : Primcodable RawSlot := inferInstance

instance instPrimcodableRawRound : Primcodable RawRound := inferInstance

instance instPrimcodableRawState : Primcodable RawState := inferInstance

/-! ### Erasure maps -/

/-- Erase the indices of a slot. -/
def toRawSlot {n b : ℕ} (s : GrayTailSlot n b) : RawSlot := (s.1.val, s.2.1.val, s.2.2.val)

/-- Erase the indices of a frozen round. -/
def toRawRound {n b : ℕ} (p : GrayTailRound n b) : RawRound :=
  ((p.roundIndex, p.serverTime, p.epsDepth),
    (p.slots.map toRawSlot, p.move, p.allocated, p.unavailable))

/-- Erase the indices of a controller state. -/
def toRawState {n b : ℕ} (st : GrayTailState n b) : RawState :=
  ((st.time, st.roundStart, st.done),
    (st.frozen.map toRawRound, st.unavailable, st.slots.map toRawSlot,
      st.anchoringSlots.map toRawSlot, st.history))

/-- Erase the indices of a slot-indexed entry list. -/
def toRawEntries {n b : ℕ} (entries : List (GrayTailSlot n b × ClientMove)) :
    List (RawSlot × ClientMove) :=
  entries.map fun p => (toRawSlot p.1, p.2)

/-- Erasing the indices of a slot loses no information. -/
theorem toRawSlot_injective {n b : ℕ} : Function.Injective (toRawSlot (n := n) (b := b)) := by
  rintro ⟨i, c, d⟩ ⟨i', c', d'⟩ h
  simp only [toRawSlot, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  simp [Fin.val_inj.mp h1, Fin.val_inj.mp h2, Fin.val_inj.mp h3]

/-! ### Erased controller constructions -/

/-- The erased form of `grayTailSlotEntries`: pairs the `j`-th erased slot with `familyClientMoveAt
move j`, for every `j < slots.length`. -/
def rawSlotEntries (slots : List RawSlot) (move : FamilyClientMove) :
    List (RawSlot × ClientMove) :=
  (List.range slots.length).map fun j => (slots.getD j (0, 0, 0), familyClientMoveAt move j)

/-- The erased form of `grayTailSlots`: for `r < b`, all triples `(i, c, r)` with `i < n` and `c <
b` a son below `used`; the empty list when `b ≤ r`. -/
def rawSlots (n b used r : ℕ) : List RawSlot :=
  if r < b then
    (List.range n).flatMap fun i =>
      ((List.range b).filter fun c => decide (c < used)).map fun c => (i, c, r)
  else
    []

/-- The erased form of `grayTailFrozenEntries`: the concatenation of the slot entries of every
frozen round of the list. -/
def rawFrozenEntries (frozen : List RawRound) : List (RawSlot × ClientMove) :=
  frozen.flatMap fun p => rawSlotEntries p.2.1 p.2.2.1

/-- The erased form of `grayTailEntries`: the frozen entries followed by the slot entries of the
current move. -/
def rawEntries (frozen : List RawRound) (slots : List RawSlot)
    (current : FamilyClientMove) : List (RawSlot × ClientMove) :=
  rawFrozenEntries frozen ++ rawSlotEntries slots current

/-- The erased form of `grayTailEntryMove`: the client move of the first entry whose slot equals
`slot`, and the empty move when there is none. -/
def rawEntryMove (entries : List (RawSlot × ClientMove)) (slot : RawSlot) : ClientMove :=
  ((entries.find? fun p => decide (p.1 = slot)).map Prod.snd).getD []

/-- The erased form of `grayTailSonBase`: the sum of the root requests `getReq · []` over the
entries whose slot has outer root `i` and son `c`. -/
def rawSonBase (entries : List (RawSlot × ClientMove)) (i c : ℕ) : ℚ :=
  entries.foldr (fun p acc =>
    if p.1.1 = i ∧ p.1.2.1 = c then getReq p.2 [] + acc else acc) 0

/-- The erased form of `grayTailSonRequest`: `eps` when `threshold < rawSonBase entries i c`, and
`rawSonBase entries i c` otherwise. -/
def rawSonRequest (threshold eps : ℚ) (entries : List (RawSlot × ClientMove))
    (i c : ℕ) : ℚ :=
  if threshold < rawSonBase entries i c then eps else rawSonBase entries i c

/-- The erased form of `grayTailRootRequest`: the sum of `rawSonRequest threshold eps entries i c`
over the sons `c < b`, replaced by its maximum with `targetFloor` once `done` is true. -/
def rawRootRequest (done : Bool) (targetFloor threshold eps : ℚ) (b : ℕ)
    (entries : List (RawSlot × ClientMove)) (i : ℕ) : ℚ :=
  let q := (((List.range b).map fun c => rawSonRequest threshold eps entries i c).sum)
  if done then max q targetFloor else q

/-- The erased form of `grayTailFamilyMove`: for each outer root `i < n`, the two-level graft of the
root request `rawRootRequest`, the son requests `rawSonRequest` at sons `c < b` and the grandson
moves `rawEntryMove entries (i, c, c')`, with all indices outside the ranges sent to `0` and the
empty move. -/
def rawFamilyMove (done : Bool) (targetFloor threshold eps : ℚ) (n b : ℕ)
    (frozen : List RawRound) (slots : List RawSlot) (current : FamilyClientMove) :
    FamilyClientMove :=
  let entries := rawEntries frozen slots current
  (List.range n).map fun i =>
    graftTwoLevel (rawRootRequest done targetFloor threshold eps b entries i) b
      (fun c => if c < b then rawSonRequest threshold eps entries i c else 0)
      (fun c c' => if c < b then if c' < b then rawEntryMove entries (i, c, c') else [] else [])

/-- The erased form of `extractGrandchildFamilyMove`: for each slot, the server move of its outer
root restricted first to the son subtree and then to the grandson subtree. -/
def rawExtractGrandchildFamilyMove (slots : List RawSlot) (sm : FamilyServerMove) :
    FamilyServerMove :=
  slots.map fun slot =>
    extractSubtreeServerMove slot.2.2 (extractSubtreeServerMove slot.2.1
      (familyServerMoveAt sm slot.1))

/-- The erased form of `grayTailLocalServerMove`: the grandchild-extracted play, restricted to the
tree of branching `b` and truncated at depth `truncDepth`. -/
def rawLocalServerMove (truncDepth b : ℕ) (slots : List RawSlot) (sm : FamilyServerMove) :
    FamilyServerMove :=
  truncFamilyServerMove truncDepth
    (inTreeFamilyServerMove b (rawExtractGrandchildFamilyMove slots sm))

/-- The erased form of `grayTailFrozenSonBase`: `rawSonBase` evaluated on the entries of the frozen
rounds. -/
def rawFrozenSonBase (frozen : List RawRound) (i c : ℕ) : ℚ :=
  rawSonBase (rawFrozenEntries frozen) i c

/-- The erased form of `grayTailNextSlots`: for `round < b`, the slots `(i, c, round)` with `i < n`
and `c < used` whose frozen son base does not exceed `threshold` and which hold no tail-family
reserve under `sm`; the empty list when `b ≤ round`. -/
def rawNextSlots (n b e used round : ℕ) (threshold : ℚ) (A : Allocation)
    (frozen : List RawRound) (sm : FamilyServerMove) : List RawSlot :=
  if round < b then
    (List.range n).flatMap fun i =>
      ((List.range b).filter fun c =>
        decide (c < used) &&
        !(decide (threshold < rawFrozenSonBase frozen i c)) &&
        !(getTailFamilyReserve e b A n i sm [c]).isSome).map fun c => (i, c, round)
  else
    []

/-- The erased form of `grayTailSameSonB`: decides whether two erased slots have the same outer root
and the same son. -/
def rawSameSonB (s t : RawSlot) : Bool :=
  decide (s.1 = t.1 ∧ s.2.1 = t.2.1)

/-- The erased form of `grayTailRetainedSlots`: the candidates whose outer root and son already
occur among the current slots. -/
def rawRetainedSlots (current candidates : List RawSlot) : List RawSlot :=
  candidates.filter fun s => current.any (rawSameSonB s)

/-- Erased form of the waiting flag of the tail controller; the controller never waits. -/
def rawWaitingB (_st : RawState) : Bool :=
  false

/-- Erased form of the flag saying the controller is done and still holds anchoring slots. -/
def rawAnchoringOutputB (st : RawState) : Bool :=
  st.1.2.2 && !st.2.2.2.2.1.isEmpty

/-- Erased form of the test that some slot still has a reserve available for its son. -/
def rawHasUnanchoredReserveB (e n b : ℕ) (A : Allocation)
    (slots : List RawSlot) (sm : FamilyServerMove) : Bool :=
  slots.any fun s =>
    (getTailFamilyReserve e b A n s.1 sm [s.2.1]).isSome

/-- Erased form of the test that every slot has an anchored reserve for its son. -/
def rawAllAnchoredB (e n b : ℕ) (A : Allocation)
    (slots : List RawSlot) (sm : FamilyServerMove) : Bool :=
  slots.all fun s =>
    (getAnchoredTailFamilyReserve e b A n s.1 sm [s.2.1]).isSome

/-- Erased form of the request made at a son during a waiting round: the forcing value `eps` on
forced slots and the ordinary son request elsewhere. -/
def rawWaitingSonRequest (forceSlots : List RawSlot)
    (threshold eps : ℚ) (entries : List (RawSlot × ClientMove))
    (i c : ℕ) : ℚ :=
  if forceSlots.any fun s => rawSameSonB s (i, c, s.2.2) then
    eps
  else
    rawSonRequest threshold eps entries i c

/-- Erased form of the root request during a waiting round: the sum of the son requests, raised to
the target floor once the round is done. -/
def rawWaitingRootRequest (done : Bool)
    (targetFloor threshold eps : ℚ) (b : ℕ)
    (forceSlots : List RawSlot) (entries : List (RawSlot × ClientMove))
    (i : ℕ) : ℚ :=
  let value := ((List.range b).map fun c =>
    rawWaitingSonRequest forceSlots threshold eps entries i c).sum
  if done then max value targetFloor else value

/-- The erased family move played during a waiting round: for each outer root `i < n`, the two-level
graft of `rawWaitingRootRequest`, the son requests `rawWaitingSonRequest` at sons `c < b` and
the grandson moves `rawEntryMove entries (i, c, c')`, all computed from the frozen entries only. -/
def rawWaitingFamilyMove (done : Bool)
    (targetFloor threshold eps : ℚ) (n b : ℕ)
    (frozen : List RawRound) (forceSlots : List RawSlot) :
    FamilyClientMove :=
  let entries := rawFrozenEntries frozen
  (List.range n).map fun i =>
    graftTwoLevel
      (rawWaitingRootRequest done targetFloor threshold eps b
        forceSlots entries i)
      b
      (fun c => if c < b then
        rawWaitingSonRequest forceSlots threshold eps entries i c
        else 0)
      (fun c c' => if c < b then if c' < b then
        rawEntryMove entries (i, c, c') else [] else [])

/-- The number of erased slots whose outer root is `i`: the unresolved son count of that root. -/
def rawRootSlotCount (slots : List RawSlot) (i : ℕ) : ℕ :=
  (slots.filter fun s => decide (s.1 = i)).length

/-- The erased per-root stopping test: `4 * rawRootSlotCount slots i ≤ used` holds for every root `i
< n`, that is every root keeps at most a quarter of its source sons open. -/
def rawPerRootQuarterB (n used : ℕ) (slots : List RawSlot) : Bool :=
  (List.range n).all fun i => decide (4 * rawRootSlotCount slots i ≤ used)

/-- The erased global stopping test `4 * slots.length ≤ n * used`: at most a quarter of all source
sons of the family are still open. -/
def rawGlobalQuarterB (n used : ℕ) (slots : List RawSlot) : Bool :=
  decide (4 * slots.length ≤ n * used)

/-- The erased form of `grayTailInitialState`: time and round start `0`, not done, no frozen round,
unavailable set `A`, the full slot list `rawSlots n b (2 ^ (e - a)) 0`, no anchoring slot and
the empty history. -/
def rawInitialState (n b a e : ℕ) (A : Allocation) : RawState :=
  ((0, 0, false),
    ([], A, rawSlots n b (2 ^ (e - a)) 0, [], ([], [])))

/-- Erased form of `grayTailStep`, with the answer of the recursive call
supplied as an ordinary argument. -/
def rawStepWith (q L a e n b : ℕ) (A : Allocation) (st : RawState)
    (sm : FamilyServerMove) (current : FamilyClientMove) : RawState :=
  if rawWaitingB st then
    if rawAllAnchoredB e n b A st.2.2.2.2.1 sm then
      ((st.1.1 + 1, st.1.1 + 1, true),
        (st.2.1, st.2.2.1, [], st.2.2.2.2.1, ([], [])))
    else
      ((st.1.1 + 1, st.1.1 + 1, st.1.2.2),
        (st.2.1, st.2.2.1, st.2.2.2.1, st.2.2.2.2.1, ([], [])))
  else if st.1.2.2 then
    ((st.1.1 + 1, st.1.2.1, st.1.2.2), st.2)
  else if st.2.2.2.1.isEmpty then
    ((st.1.1 + 1, st.1.2.1, st.1.2.2), st.2)
  else
    let r := st.2.1.length
    let epsRound := grayTailRoundEps q L e r
    let deltaRound := grayTailRoundDelta q L e r
    let localSM := rawLocalServerMove deltaRound b st.2.2.2.1 sm
    if familyRobustGrayGoalAtB (halfAmplification q)
        ((3 / 4 : ℚ) * dyadicScale (grayCallDepth q e))
        epsRound deltaRound st.2.2.2.1.length st.2.2.1 current localSM then
      let allocated := grayTailLocalAllocatedList localSM
      let frozen' := st.2.1 ++
        [((r, st.1.1, epsRound),
          (st.2.2.2.1, current, allocated, st.2.2.1))]
      let unavailable' := st.2.2.1 ++ neighborhoodCellsList epsRound allocated
      let threshold := dyadicScale e -
        dyadicScale e / (6 * halfAmplification q)
      let candidates :=
        rawNextSlots n b e (2 ^ (e - a)) frozen'.length
          threshold A frozen' sm
      let next := candidates
      let done' := rawGlobalQuarterB n (2 ^ (e - a)) next ||
        decide (grayTailRoundCount q ≤ frozen'.length)
      ((st.1.1 + 1, st.1.1 + 1, done'),
        (frozen', unavailable', next, [], ([], [])))
    else
      ((st.1.1 + 1, st.1.2.1, st.1.2.2),
        (st.2.1, st.2.2.1, st.2.2.2.1, st.2.2.2.2.1,
          (st.2.2.2.2.2.1 ++ [current],
            st.2.2.2.2.2.2 ++ [localSM])))

/-- Erased form of `grayTailOutput`, with the answer of the recursive call
supplied as an ordinary argument. -/
def rawOutput (q _L a e n b : ℕ) (st : RawState)
    (current : FamilyClientMove) : FamilyClientMove :=
  rawFamilyMove st.1.2.2 (grayTailTargetFloor q a)
    (dyadicScale e - dyadicScale e / (6 * halfAmplification q))
    (dyadicScale e) n b st.2.1 st.2.2.2.1
    (if st.1.2.2 then [] else current)

/-- The scheme input of the single recursive call made in a state: the call depth `grayCallDepth q
e` and the round precision `grayTailRoundEps q L e` at the current round number, together with
the unavailable set, the number of open slots and the stored history. -/
def rawQuery (q L e : ℕ) (st : RawState) : SchemeInput :=
  ((grayCallDepth q e, grayTailRoundEps q L e st.2.1.length),
    (st.2.2.1, (st.2.2.2.1.length, st.2.2.2.2.2)))

/-! ### List helpers used by the bridge -/

/-- Mapping over `Fin n` and over `range n` agree when the two functions agree on the underlying
naturals. -/
theorem map_finRange_eq_map_range {γ : Type*} (n : ℕ) (F : Fin n → γ) (G : ℕ → γ)
    (h : ∀ i : Fin n, F i = G i.val) :
    (List.finRange n).map F = (List.range n).map G := by
  rw [← List.map_coe_finRange_eq_range, List.map_map]
  exact List.map_congr_left fun i _ => h i

/-- Flat-mapping over `Fin n` and over `range n` agree when the two functions agree on the
underlying
naturals. -/
theorem flatMap_finRange_eq_flatMap_range {γ : Type*} (n : ℕ) (F : Fin n → List γ)
    (G : ℕ → List γ) (h : ∀ i : Fin n, F i = G i.val) :
    (List.finRange n).flatMap F = (List.range n).flatMap G := by
  rw [← List.map_coe_finRange_eq_range, List.flatMap_map]
  exact List.flatMap_congr fun i _ => h i

/-- Filtering `Fin b` by a predicate on values and then forgetting the bound gives the filtered
`range b`. -/
theorem filter_finRange_map_val (b : ℕ) (p : ℕ → Bool) :
    ((List.finRange b).filter fun c => p c.val).map Fin.val = (List.range b).filter p := by
  rw [← List.map_coe_finRange_eq_range, List.filter_map]
  rfl

/-- Summing a list built from `range n` is the same as the corresponding `Finset.range` sum. -/
theorem sum_map_range_eq {n : ℕ} (g : ℕ → ℚ) :
    (((List.range n).map g).sum) = ∑ i ∈ Finset.range n, g i := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

/-! ### The bridge -/

/-- The erased slot-entry list is the erasure of the indexed one. -/
theorem rawSlotEntries_eq {n b : ℕ} (slots : List (GrayTailSlot n b))
    (move : FamilyClientMove) :
    rawSlotEntries (slots.map toRawSlot) move =
      toRawEntries (grayTailSlotEntries slots move) := by
  unfold rawSlotEntries toRawEntries grayTailSlotEntries
  rw [List.map_ofFn, List.ofFn_eq_map, List.length_map]
  refine (map_finRange_eq_map_range slots.length _ _ ?_).symm
  intro j
  have hj : j.val < (slots.map toRawSlot).length := by simp
  simp [Function.comp]

/-- The erased slot list is the erasure of the indexed slot list. -/
theorem rawSlots_eq (n b used r : ℕ) :
    rawSlots n b used r = (grayTailSlots n b used r).map toRawSlot := by
  unfold rawSlots grayTailSlots
  by_cases hr : r < b
  · rw [dif_pos hr, if_pos hr, List.map_flatMap]
    refine (flatMap_finRange_eq_flatMap_range n _ _ ?_).symm
    intro i
    rw [List.map_map, ← filter_finRange_map_val b (fun c => decide (c < used)), List.map_map]
    rfl
  · rw [dif_neg hr, if_neg hr, List.map_nil]

/-- The erased entries of the frozen rounds are the erasure of the indexed ones. -/
theorem rawFrozenEntries_eq {n b : ℕ} (frozen : GrayTailFrozen n b) :
    rawFrozenEntries (frozen.map toRawRound) =
      toRawEntries (grayTailFrozenEntries frozen) := by
  unfold rawFrozenEntries grayTailFrozenEntries toRawEntries
  rw [List.flatMap_map, List.map_flatMap]
  exact List.flatMap_congr fun p _ => by
    simpa [toRawRound] using rawSlotEntries_eq p.slots p.move

/-- The erased entry list of a controller state is the erasure of the indexed one. -/
theorem rawEntries_eq {n b : ℕ} (frozen : GrayTailFrozen n b)
    (slots : List (GrayTailSlot n b)) (current : FamilyClientMove) :
    rawEntries (frozen.map toRawRound) (slots.map toRawSlot) current =
      toRawEntries (grayTailEntries frozen slots current) := by
  unfold rawEntries grayTailEntries toRawEntries
  rw [List.map_append, rawFrozenEntries_eq, rawSlotEntries_eq]
  rfl

/-- Looking up the move of a slot commutes with erasure. -/
theorem rawEntryMove_eq {n b : ℕ} (entries : List (GrayTailSlot n b × ClientMove))
    (slot : GrayTailSlot n b) :
    rawEntryMove (toRawEntries entries) (toRawSlot slot) =
      grayTailEntryMove entries slot := by
  unfold rawEntryMove grayTailEntryMove toRawEntries
  rw [List.find?_map]
  have hp : ((fun p : RawSlot × ClientMove => decide (p.1 = toRawSlot slot)) ∘
      fun p : GrayTailSlot n b × ClientMove => (toRawSlot p.1, p.2)) =
      fun p => decide (p.1 = slot) := by
    funext p
    simp only [Function.comp_apply, decide_eq_decide]
    exact ⟨fun h => toRawSlot_injective h, fun h => by rw [h]⟩
  rw [hp, Option.map_map]
  rfl

/-- The erased base request at a son agrees with the indexed one. -/
theorem rawSonBase_eq {n b : ℕ} (entries : List (GrayTailSlot n b × ClientMove))
    (i : Fin n) (c : Fin b) :
    rawSonBase (toRawEntries entries) i.val c.val = grayTailSonBase entries i c := by
  unfold rawSonBase grayTailSonBase toRawEntries
  rw [List.foldr_map]
  have hfun : (fun (p : GrayTailSlot n b × ClientMove) (acc : ℚ) =>
      if (toRawSlot p.1).1 = i.val ∧ (toRawSlot p.1).2.1 = c.val then getReq p.2 [] + acc
        else acc) =
      fun p acc => if p.1.1 = i ∧ p.1.2.1 = c then getReq p.2 [] + acc else acc := by
    funext p acc
    have hiff : ((toRawSlot p.1).1 = i.val ∧ (toRawSlot p.1).2.1 = c.val) ↔
        (p.1.1 = i ∧ p.1.2.1 = c) := by
      simp [toRawSlot, Fin.val_inj]
    exact if_congr hiff rfl rfl
  rw [hfun]

/-- The erased son request agrees with the indexed one. -/
theorem rawSonRequest_eq {n b : ℕ} (threshold eps : ℚ)
    (entries : List (GrayTailSlot n b × ClientMove)) (i : Fin n) (c : Fin b) :
    rawSonRequest threshold eps (toRawEntries entries) i.val c.val =
      grayTailSonRequest threshold eps entries i c := by
  unfold rawSonRequest grayTailSonRequest
  rw [rawSonBase_eq]

/-- The erased root request agrees with the indexed one. -/
theorem rawRootRequest_eq {n b : ℕ} (done : Bool) (targetFloor threshold eps : ℚ)
    (entries : List (GrayTailSlot n b × ClientMove)) (i : Fin n) :
    rawRootRequest done targetFloor threshold eps b (toRawEntries entries) i.val =
      grayTailRootRequest done targetFloor threshold eps entries i := by
  unfold rawRootRequest grayTailRootRequest
  have hsum : (((List.range b).map fun c =>
      rawSonRequest threshold eps (toRawEntries entries) i.val c).sum) =
      ∑ c : Fin b, grayTailSonRequest threshold eps entries i c := by
    rw [sum_map_range_eq,
      ← Fin.sum_univ_eq_sum_range
        (fun c => rawSonRequest threshold eps (toRawEntries entries) i.val c) b]
    exact Finset.sum_congr rfl fun c _ => rawSonRequest_eq threshold eps entries i c
  simp only [hsum]

/-- The erased family move agrees with the indexed one. -/
theorem rawFamilyMove_eq {n b : ℕ} (done : Bool) (targetFloor threshold eps : ℚ)
    (frozen : GrayTailFrozen n b) (slots : List (GrayTailSlot n b))
    (current : FamilyClientMove) :
    rawFamilyMove done targetFloor threshold eps n b (frozen.map toRawRound)
        (slots.map toRawSlot) current =
      grayTailFamilyMove done targetFloor threshold eps frozen slots current := by
  unfold rawFamilyMove grayTailFamilyMove
  simp only [rawEntries_eq]
  set entries := grayTailEntries frozen slots current with hentries
  rw [List.ofFn_eq_map]
  refine (map_finRange_eq_map_range n _ _ ?_).symm
  intro i
  have h1 : grayTailRootRequest done targetFloor threshold eps entries i =
      rawRootRequest done targetFloor threshold eps b (toRawEntries entries) i.val :=
    (rawRootRequest_eq done targetFloor threshold eps entries i).symm
  have h2 : (fun c => if hc : c < b then
        grayTailSonRequest threshold eps entries i ⟨c, hc⟩ else 0) =
      fun c => if c < b then rawSonRequest threshold eps (toRawEntries entries) i.val c else 0 := by
    funext c
    by_cases hc : c < b
    · rw [dif_pos hc, if_pos hc]
      exact (rawSonRequest_eq threshold eps entries i ⟨c, hc⟩).symm
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

/-- The erased localisation of a server move agrees with the indexed one. -/
theorem rawLocalServerMove_eq {n b : ℕ} (truncDepth : ℕ)
    (slots : List (GrayTailSlot n b)) (sm : FamilyServerMove) :
    rawLocalServerMove truncDepth b (slots.map toRawSlot) sm =
      grayTailLocalServerMove truncDepth slots sm := by
  unfold rawLocalServerMove grayTailLocalServerMove rawExtractGrandchildFamilyMove
    extractGrandchildFamilyMove
  rw [List.map_map]
  rfl

/-- The erased base request read off the frozen rounds agrees with the indexed one. -/
theorem rawFrozenSonBase_eq {n b : ℕ} (frozen : GrayTailFrozen n b) (i : Fin n) (c : Fin b) :
    rawFrozenSonBase (frozen.map toRawRound) i.val c.val =
      grayTailFrozenSonBase frozen i c := by
  unfold rawFrozenSonBase grayTailFrozenSonBase
  rw [rawFrozenEntries_eq, rawSonBase_eq]

/-- The erased slot list of the next round is the erasure of the indexed one. -/
theorem rawNextSlots_eq {n b : ℕ} (e used round : ℕ) (threshold : ℚ) (A : Allocation)
    (frozen : GrayTailFrozen n b) (sm : FamilyServerMove) :
    rawNextSlots n b e used round threshold A (frozen.map toRawRound) sm =
      (grayTailNextSlots e used round threshold A frozen sm).map toRawSlot := by
  unfold rawNextSlots grayTailNextSlots
  by_cases hr : round < b
  · rw [dif_pos hr, if_pos hr, List.map_flatMap]
    refine (flatMap_finRange_eq_flatMap_range n _ _ ?_).symm
    intro i
    rw [List.map_map,
      ← filter_finRange_map_val b (fun c =>
        decide (c < used) &&
        !(decide (threshold < rawFrozenSonBase (frozen.map toRawRound) i.val c)) &&
        !(getTailFamilyReserve e b A n i.val sm [c]).isSome),
      List.map_map]
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
    simp only [Function.comp_def, hpred]
    rfl
  · rw [dif_neg hr, if_neg hr, List.map_nil]
/-- The erased retained slots are the erasure of the indexed retained slots. -/
theorem rawRetainedSlots_eq {n b : ℕ}
    (current candidates : List (GrayTailSlot n b)) :
    rawRetainedSlots (current.map toRawSlot) (candidates.map toRawSlot) =
      (grayTailRetainedSlots current candidates).map toRawSlot := by
  unfold rawRetainedSlots grayTailRetainedSlots
  induction candidates with
  | nil => rfl
  | cons s rest ih =>
      have hpred :
          (current.map toRawSlot).any (rawSameSonB (toRawSlot s)) =
            current.any (grayTailSameSonB s) := by
        rw [List.any_map]
        congr 1
        funext t
        simp [rawSameSonB, grayTailSameSonB, toRawSlot, Fin.val_inj]
      simp only [List.map_cons, List.filter_cons, hpred, ih]
      split <;> rfl
/-- The erased waiting flag agrees with the indexed one. -/
@[simp] theorem rawWaitingB_eq {n b : ℕ} (st : GrayTailState n b) :
    rawWaitingB (toRawState st) = grayTailWaitingB st := by
  simp [rawWaitingB, grayTailWaitingB]

/-- The erased anchoring-output flag agrees with the indexed one. -/
@[simp] theorem rawAnchoringOutputB_eq {n b : ℕ}
    (st : GrayTailState n b) :
    rawAnchoringOutputB (toRawState st) = grayTailAnchoringOutputB st := by
  simp [rawAnchoringOutputB, grayTailAnchoringOutputB, toRawState]

/-- The erased unanchored-reserve test agrees with the indexed one. -/
@[simp] theorem rawHasUnanchoredReserveB_eq {n b : ℕ}
    (e : ℕ) (A : Allocation) (slots : List (GrayTailSlot n b))
    (sm : FamilyServerMove) :
    rawHasUnanchoredReserveB e n b A (slots.map toRawSlot) sm =
      grayTailHasUnanchoredReserveB e A slots sm := by
  unfold rawHasUnanchoredReserveB grayTailHasUnanchoredReserveB
  rw [List.any_map]
  congr 1

/-- The erased all-anchored test agrees with the indexed one. -/
@[simp] theorem rawAllAnchoredB_eq {n b : ℕ}
    (e : ℕ) (A : Allocation) (slots : List (GrayTailSlot n b))
    (sm : FamilyServerMove) :
    rawAllAnchoredB e n b A (slots.map toRawSlot) sm =
      grayTailAllAnchoredB e A slots sm := by
  unfold rawAllAnchoredB grayTailAllAnchoredB
  rw [List.all_map]
  congr 1

/-- The erased waiting son request agrees with the indexed one. -/
theorem rawWaitingSonRequest_eq {n b : ℕ}
    (forceSlots : List (GrayTailSlot n b))
    (threshold eps : ℚ)
    (entries : List (GrayTailSlot n b × ClientMove))
    (i : Fin n) (c : Fin b) :
    rawWaitingSonRequest (forceSlots.map toRawSlot)
        threshold eps (toRawEntries entries) i.val c.val =
      grayTailWaitingSonRequest forceSlots threshold eps entries i c := by
  simp [rawWaitingSonRequest, grayTailWaitingSonRequest,
    rawSameSonB, grayTailSameSonB, toRawSlot, Fin.val_inj,
    rawSonRequest_eq]

/-- The erased waiting root request agrees with the indexed one. -/
theorem rawWaitingRootRequest_eq {n b : ℕ}
    (done : Bool) (targetFloor threshold eps : ℚ)
    (forceSlots : List (GrayTailSlot n b))
    (entries : List (GrayTailSlot n b × ClientMove))
    (i : Fin n) :
    rawWaitingRootRequest done targetFloor threshold eps b
        (forceSlots.map toRawSlot) (toRawEntries entries) i.val =
      grayTailWaitingRootRequest done targetFloor threshold eps
        forceSlots entries i := by
  unfold rawWaitingRootRequest grayTailWaitingRootRequest
  have hsum :
      (((List.range b).map fun c =>
        rawWaitingSonRequest (forceSlots.map toRawSlot)
          threshold eps (toRawEntries entries) i.val c).sum) =
        ∑ c : Fin b,
          grayTailWaitingSonRequest forceSlots threshold eps entries i c := by
    rw [sum_map_range_eq,
      ← Fin.sum_univ_eq_sum_range
        (fun c => rawWaitingSonRequest (forceSlots.map toRawSlot)
          threshold eps (toRawEntries entries) i.val c) b]
    exact Finset.sum_congr rfl fun c _ =>
      rawWaitingSonRequest_eq forceSlots threshold eps entries i c
  simp only [hsum]

/-- The erased waiting family move agrees with the indexed one. -/
theorem rawWaitingFamilyMove_eq {n b : ℕ}
    (done : Bool) (targetFloor threshold eps : ℚ)
    (frozen : GrayTailFrozen n b)
    (forceSlots : List (GrayTailSlot n b)) :
    rawWaitingFamilyMove done targetFloor threshold eps n b
        (frozen.map toRawRound) (forceSlots.map toRawSlot) =
      grayTailWaitingFamilyMove done targetFloor threshold eps
        frozen forceSlots := by
  unfold rawWaitingFamilyMove grayTailWaitingFamilyMove
  simp only [rawFrozenEntries_eq]
  set entries := grayTailFrozenEntries frozen
  rw [List.ofFn_eq_map]
  refine (map_finRange_eq_map_range n _ _ ?_).symm
  intro i
  have h1 := rawWaitingRootRequest_eq done targetFloor threshold eps
    forceSlots entries i
  have h2 : (fun c => if hc : c < b then
        grayTailWaitingSonRequest forceSlots threshold eps
          entries i ⟨c, hc⟩ else 0) =
      fun c => if c < b then
        rawWaitingSonRequest (forceSlots.map toRawSlot)
          threshold eps (toRawEntries entries) i.val c else 0 := by
    funext c
    by_cases hc : c < b
    · rw [dif_pos hc, if_pos hc]
      exact (rawWaitingSonRequest_eq forceSlots threshold eps
        entries i ⟨c, hc⟩).symm
    · rw [dif_neg hc, if_neg hc]
  have h3 : (fun c c' => if hc : c < b then
        (if hc' : c' < b then
          grayTailEntryMove entries (i, ⟨c, hc⟩, ⟨c', hc'⟩)
        else []) else []) =
      fun c c' => if c < b then
        (if c' < b then
          rawEntryMove (toRawEntries entries) (i.val, c, c')
        else []) else [] := by
    funext c c'
    by_cases hc : c < b
    · rw [dif_pos hc, if_pos hc]
      by_cases hc' : c' < b
      · rw [dif_pos hc', if_pos hc']
        exact (rawEntryMove_eq entries
          (i, ⟨c, hc⟩, ⟨c', hc'⟩)).symm
      · rw [dif_neg hc', if_neg hc']
    · rw [dif_neg hc, if_neg hc]
  rw [h1, h2, h3]

/-- The erased count of slots at a root agrees with the indexed one. -/
theorem rawRootSlotCount_eq {n b : ℕ} (slots : List (GrayTailSlot n b)) (i : Fin n) :
    rawRootSlotCount (slots.map toRawSlot) i.val = grayTailRootSlotCount slots i := by
  unfold rawRootSlotCount grayTailRootSlotCount
  rw [List.filter_map, List.length_map]
  have hpred : ((fun s : RawSlot => decide (s.1 = i.val)) ∘ toRawSlot (n := n) (b := b)) =
      fun s => decide (s.1 = i) := by
    funext s
    simp [toRawSlot, Fin.val_inj]
  rw [hpred]

/-- Universal quantification over `Fin n` and over `range n` give the same Boolean value. -/
theorem all_finRange_eq_all_range (n : ℕ) (p : ℕ → Bool) :
    ((List.finRange n).all fun i => p i.val) = (List.range n).all p := by
  rw [← List.map_coe_finRange_eq_range, List.all_map]
  rfl

/-- The erased per-root quarter test agrees with the indexed one. -/
theorem rawPerRootQuarterB_eq {n b : ℕ} (used : ℕ) (slots : List (GrayTailSlot n b)) :
    rawPerRootQuarterB n used (slots.map toRawSlot) = grayTailPerRootQuarterB used slots := by
  unfold rawPerRootQuarterB grayTailPerRootQuarterB
  rw [← all_finRange_eq_all_range]
  congr 1
  funext i
  rw [rawRootSlotCount_eq slots i]

/-- The erased global quarter test agrees with the indexed one. -/
theorem rawGlobalQuarterB_eq {n b : ℕ} (used : ℕ) (slots : List (GrayTailSlot n b)) :
    rawGlobalQuarterB n used (slots.map toRawSlot) =
      grayTailGlobalQuarterB (n := n) used slots := by
  unfold rawGlobalQuarterB grayTailGlobalQuarterB
  rw [List.length_map]

/-- The erased initial state is the erasure of the indexed initial state. -/
theorem rawInitialState_eq (n b a e : ℕ) (A : Allocation) :
    rawInitialState n b a e A = toRawState (grayTailInitialState n b a e A) := by
  unfold rawInitialState toRawState grayTailInitialState
  simp [rawSlots_eq]

/-- Feeding the erased query to the family strategy scheme returns the same move the indexed
controller would play. -/
theorem rawQuery_eq {n b : ℕ} (q L e : ℕ) (st : GrayTailState n b)
    (sigma : FamilyStrategyScheme) :
    sigma (rawQuery q L e (toRawState st)).1.1 (rawQuery q L e (toRawState st)).1.2
        (rawQuery q L e (toRawState st)).2.1 (rawQuery q L e (toRawState st)).2.2.1
        (rawQuery q L e (toRawState st)).2.2.2 =
      grayTailCurrentMove q L e sigma st := by
  unfold rawQuery grayTailCurrentMove toRawState
  simp

/-- The frozen round appended by one winning controller step. -/
def grayTailStepRound {n b : ℕ} (q L e : ℕ) (sigma : FamilyStrategyScheme)
    (st : GrayTailState n b) (sm : FamilyServerMove) : GrayTailRound n b where
  roundIndex := st.frozen.length
  serverTime := st.time
  epsDepth := grayTailRoundEps q L e st.frozen.length
  slots := st.slots
  move := grayTailCurrentMove q L e sigma st
  allocated := grayTailLocalAllocatedList
    (grayTailLocalServerMove (grayTailRoundDelta q L e st.frozen.length) st.slots sm)
  unavailable := st.unavailable

/-- One erased controller step is the erasure of one indexed controller step. -/
theorem rawStepWith_eq {n b : ℕ} (q L a e : ℕ) (sigma : FamilyStrategyScheme)
    (A : Allocation) (st : GrayTailState n b) (sm : FamilyServerMove) :
    rawStepWith q L a e n b A (toRawState st) sm
        (grayTailCurrentMove q L e sigma st) =
      toRawState (grayTailStep q L a e sigma A st sm) := by
  unfold rawStepWith grayTailStep
  rw [rawWaitingB_eq]
  by_cases hw : grayTailWaitingB st = true
  · rw [if_pos hw, if_pos hw]
    simp only [toRawState]
    rw [rawAllAnchoredB_eq]
    by_cases ha : grayTailAllAnchoredB e A st.anchoringSlots sm = true
    · rw [if_pos ha, if_pos ha]
      rfl
    · rw [if_neg ha, if_neg ha]
  · rw [if_neg hw, if_neg hw]
    simp only [toRawState, List.isEmpty_map]
    by_cases hd : st.done = true
    · rw [if_pos hd, if_pos hd]
    · rw [if_neg hd, if_neg hd]
      by_cases hs : st.slots.isEmpty = true
      · rw [if_pos hs, if_pos hs]
      · rw [if_neg hs, if_neg hs]
        simp only [List.length_map]
        rw [rawLocalServerMove_eq]
        by_cases hgoal : familyRobustGrayGoalAtB (halfAmplification q)
            ((3 / 4 : ℚ) * dyadicScale (grayCallDepth q e))
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
                        (grayTailRoundDelta q L e st.frozen.length)
                        st.slots sm),
                    st.unavailable))]) =
              (st.frozen ++
                [grayTailStepRound q L e sigma st sm]).map toRawRound := by
            simp [grayTailStepRound, toRawRound]
          rw [hfr, rawNextSlots_eq, rawGlobalQuarterB_eq]
          simp [grayTailStepRound]
        · rw [if_neg hgoal, if_neg hgoal]

/-- The erased controller output agrees with the indexed one. -/
theorem rawOutput_eq {n b : ℕ} (q L a e : ℕ) (sigma : FamilyStrategyScheme)
    (st : GrayTailState n b) :
    rawOutput q L a e n b (toRawState st)
        (grayTailCurrentMove q L e sigma st) =
      grayTailOutput q L a e sigma st := by
  unfold rawOutput grayTailOutput
  simp only [toRawState]
  rw [rawFamilyMove_eq]

/-- The erased fold, driven by a supplied family of answers. -/
def rawFoldWith (q L a e n b : ℕ) (A : Allocation)
    (cur : RawState → FamilyClientMove) (history : List FamilyServerMove) : RawState :=
  history.foldl (fun st sm => rawStepWith q L a e n b A st sm (cur st))
    (rawInitialState n b a e A)

/-- Folding the erased controller over a history gives the erasure of the indexed fold, so the
index-erased mirror computes exactly the same run. -/
theorem rawFoldWith_eq {n b : ℕ} (q L a e : ℕ) (sigma : FamilyStrategyScheme)
    (A : Allocation) (history : List FamilyServerMove) :
    rawFoldWith q L a e n b A
        (fun st => sigma (rawQuery q L e st).1.1 (rawQuery q L e st).1.2
          (rawQuery q L e st).2.1 (rawQuery q L e st).2.2.1 (rawQuery q L e st).2.2.2)
        history =
      toRawState (grayTailFold (n := n) (b := b) q L a e sigma A history) := by
  unfold rawFoldWith grayTailFold
  rw [rawInitialState_eq]
  generalize grayTailInitialState n b a e A = st0
  induction history generalizing st0 with
  | nil => simp
  | cons sm t ih =>
    simp only [List.foldl_cons]
    rw [rawQuery_eq q L e st0 sigma, rawStepWith_eq, ih]

/-! ### Packed parameter form

The controller parameters are collected into a single tuple.  This keeps the
computability statements -- and, more importantly, the projection chains in
their proofs -- shallow. -/

/-- The static parameters of the erased controller: `((q, L, a, e), (n, b), A)`. -/
abbrev RawParam := (ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ) × Allocation

instance instPrimcodableRawParam : Primcodable RawParam := inferInstance

/-- `rawQuery` in packed form. -/
def rawQueryOf (P : RawParam) (st : RawState) : SchemeInput :=
  rawQuery P.1.1 P.1.2.1 P.1.2.2.2 st

/-- `rawStepWith` in packed form. -/
def rawStepOf (P : RawParam) (st : RawState) (sm : FamilyServerMove)
    (cur : FamilyClientMove) : RawState :=
  rawStepWith P.1.1 P.1.2.1 P.1.2.2.1 P.1.2.2.2 P.2.1.1 P.2.1.2 P.2.2 st sm cur

/-- `rawOutput` in packed form. -/
def rawOutputOf (P : RawParam) (st : RawState) (cur : FamilyClientMove) :
    FamilyClientMove :=
  rawOutput P.1.1 P.1.2.1 P.1.2.2.1 P.1.2.2.2 P.2.1.1 P.2.1.2 st cur

/-- `rawInitialState` in packed form. -/
def rawInitialStateOf (P : RawParam) : RawState :=
  rawInitialState P.2.1.1 P.2.1.2 P.1.2.2.1 P.1.2.2.2 P.2.2

/-- The `Encodable` code of the displayed move of the raw controller at a state. -/
def rawOutputEnc (P : RawParam) (st : RawState) (cur : FamilyClientMove) : ℕ :=
  @Encodable.encode FamilyClientMove Primcodable.toEncodable (rawOutputOf P st cur)

end Kolmogorov
