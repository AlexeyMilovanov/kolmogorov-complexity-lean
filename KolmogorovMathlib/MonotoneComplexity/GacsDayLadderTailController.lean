import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailAnchor
import KolmogorovMathlib.MonotoneComplexity.GacsDayRoundCounting
import KolmogorovMathlib.MonotoneComplexity.GacsDayRobustFamily

/-!
# The bounded controller for Day's gray-ladder tail

The controller in this file is the executable part of SUV pp. 142--143.  A
round runs the preceding family strategy on one fresh grandson of every
currently unresolved root son.  Finished rounds are frozen and their gray cells
are added to the unavailable allocation of the next round.
-/

namespace Kolmogorov

/-- A slot of the tail: a client together with a child and a grandchild of that client's root. -/
abbrev GrayTailSlot (n b : ℕ) := Fin n × Fin b × Fin b

/-- The certificate retained when one recursive round fires: the round index and server time at
which it fired, the coarse depth it used, the slots it played, the client move it produced, the
strings it allocated and the region it made unavailable. -/
structure GrayTailRound (n b : ℕ) where
  /-- The index of the round in the round schedule. -/
  roundIndex : ℕ
  /-- The server time at which the round fired. -/
  serverTime : ℕ
  /-- The coarse depth of the round. -/
  epsDepth : ℕ
  /-- The slots played in the round. -/
  slots : List (GrayTailSlot n b)
  /-- The client move produced by the round. -/
  move : FamilyClientMove
  /-- The strings allocated in the round. -/
  allocated : List BitString
  /-- The region made unavailable to later rounds. -/
  unavailable : Allocation

/-- The region made unavailable after a completed round: `neighborhoodCellsList p.epsDepth
p.allocated`, the coarse neighbourhood of the strings the round allocated. Keeping the whole
neighbourhood, rather than only the raw root allocation, is what makes gray mass from distinct
recursive rounds disjoint. -/
def grayTailRoundUnavailable {n b : ℕ}
    (p : GrayTailRound n b) : Allocation :=
  neighborhoodCellsList p.epsDepth p.allocated

/-! ### Foreign-union harvest primitives (relocated upstream for the per-call
snapshot; the legality lemma `grayHarvest_untouchable` stays in `GacsDayHarvest`). -/

/-- The node a slot names, namely the grandchild `[c, c']` of the client's root. -/
def grayTailSlotNode {n b : Nat} (s : GrayTailSlot n b) : GacsDayNode :=
  [s.2.1.val, s.2.2.val]

/-- A `(tree, node)` pair is foreign to a slot list iff it is incomparable
with every slot's address: a different tree, or a prefix-incomparable node
of the same tree. -/
def grayNodeForeignB {n b : Nat} (slots : List (GrayTailSlot n b))
    (i : Nat) (x : GacsDayNode) : Bool :=
  slots.all fun s =>
    decide (i ≠ s.1.val) ||
      !(decide (x <+: grayTailSlotNode s ∨ grayTailSlotNode s <+: x))

/-- The valid-range test for a node tag: every digit below the branching. -/
def grayNodeValidB (b : Nat) (x : GacsDayNode) : Bool :=
  x.all fun d => decide (d < b)

/-- **The foreign-union harvest** of a snapshot server move, truncated at
the component's fine end `δ`. -/
def grayHarvest {n b : Nat} (δ : Nat)
    (slots : List (GrayTailSlot n b)) (nn : Nat)
    (sm : FamilyServerMove) : Allocation :=
  (List.range nn).flatMap fun i =>
    ((familyServerMoveAt sm i).map Prod.fst).flatMap fun x =>
      if grayNodeValidB b x && grayNodeForeignB slots i x then
        (getAlloc (familyServerMoveAt sm i) x).map fun c => c.take δ
      else []

/-- Membership in the harvest: exactly the `δ`-truncations of effective
allocations at valid foreign tags of the snapshot. -/
lemma mem_grayHarvest {n b : Nat} {δ nn : Nat}
    {slots : List (GrayTailSlot n b)} {sm : FamilyServerMove}
    {u : BitString} :
    u ∈ grayHarvest (n := n) (b := b) δ slots nn sm ↔
      ∃ i x c, i < nn ∧
        grayNodeValidB b x = true ∧
        grayNodeForeignB slots i x = true ∧
        x ∈ (familyServerMoveAt sm i).map Prod.fst ∧
        c ∈ getAlloc (familyServerMoveAt sm i) x ∧
        u = c.take δ := by
  unfold grayHarvest
  simp only [List.mem_flatMap, List.mem_range, List.mem_map]
  constructor
  · rintro ⟨i, hi, x, hx, hu⟩
    by_cases hcond : (grayNodeValidB b x && grayNodeForeignB slots i x) = true
    · rw [if_pos hcond] at hu
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hu
      rw [Bool.and_eq_true] at hcond
      exact ⟨i, x, c, hi, hcond.1, hcond.2, hx, hc, rfl⟩
    · rw [if_neg hcond] at hu
      exact absurd hu (List.not_mem_nil)
  · rintro ⟨i, x, c, hi, hvalid, hforeign, hx, hc, rfl⟩
    refine ⟨i, hi, x, hx, ?_⟩
    rw [if_pos (by rw [Bool.and_eq_true]; exact ⟨hvalid, hforeign⟩)]
    exact List.mem_map.mpr ⟨c, hc, rfl⟩

/-- A nonempty effective allocation only occurs at a listed tag. -/
lemma grayLookup_mem_fst {m : ServerMove} {x : GacsDayNode} {c : BitString}
    (hc : c ∈ getAlloc m x) : x ∈ m.map Prod.fst := by
  unfold getAlloc at hc
  induction m with
  | nil => simp [List.lookup] at hc
  | cons p l ih =>
      simp only [List.lookup] at hc
      by_cases hpx : (x == p.1) = true
      · have hx : x = p.1 := beq_iff_eq.mp hpx
        simp [hx]
      · rw [Bool.not_eq_true] at hpx
        rw [hpx] at hc
        exact List.mem_cons_of_mem _ (ih hc)

/-- Effective allocations at unlisted tags are empty, so harvest coverage
loses nothing by enumerating listed tags only. -/
lemma mem_grayHarvest_of_getAlloc {n b : Nat} {δ nn : Nat}
    {slots : List (GrayTailSlot n b)} {sm : FamilyServerMove}
    {i : Nat} {x : GacsDayNode} {c : BitString}
    (hi : i < nn)
    (hvalid : grayNodeValidB b x = true)
    (hforeign : grayNodeForeignB slots i x = true)
    (hc : c ∈ getAlloc (familyServerMoveAt sm i) x) :
    c.take δ ∈ grayHarvest (n := n) (b := b) δ slots nn sm := by
  rw [mem_grayHarvest]
  refine ⟨i, x, c, hi, hvalid, hforeign, ?_, hc, rfl⟩
  exact grayLookup_mem_fst hc


/-- The rounds a tail state has already frozen, in the order they were closed. -/
abbrev GrayTailFrozen (n b : ℕ) := List (GrayTailRound n b)

/-- The snapshot of a round: `none` for the initial round (the empty
server move), `some t` for a round whose first client move follows the
server move at time `t` (proof doc v14 §9.2: the client at stage `t + 1`
sees server moves through stage `t`). -/
def grayHarvestSnapshot (sm : ℕ → FamilyServerMove) :
    Option ℕ → FamilyServerMove
  | none => []
  | some t => sm t

/-- The empty snapshot harvests nothing. -/
lemma grayHarvest_nil {n b : ℕ} (δ : ℕ)
    (slots : List (GrayTailSlot n b)) (nn : ℕ) :
    grayHarvest (n := n) (b := b) δ slots nn ([] : FamilyServerMove) = [] := by
  simp [grayHarvest, familyServerMoveAt]

/-- **The harvest chain** (proof doc v14 §9.2): every frozen round's stored
`unavailable` is exactly the ambient list plus the foreign-union harvest of
its own snapshot, truncated at its own fine end `epsDepth + L`; the
snapshot of round `k` is the previous round's `serverTime` (`none`, the
empty server move, for `k = 0`). -/
def GrayTailHarvestChain {n b : ℕ} (L nn : ℕ) (A : Allocation)
    (sm : ℕ → FamilyServerMove) (frozen : GrayTailFrozen n b) : Prop :=
  ∀ k : ℕ, ∀ hk : k < frozen.length,
    frozen[k].unavailable =
      A ++ grayHarvest (n := n) (b := b) (frozen[k].epsDepth + L)
        frozen[k].slots nn
        (grayHarvestSnapshot sm
          (if _h : k = 0 then none
           else some (frozen[k - 1]'(by omega)).serverTime))

/-- The empty harvest chain. -/
lemma grayTailHarvestChain_nil {n b : ℕ} (L nn : ℕ) (A : Allocation)
    (sm : ℕ → FamilyServerMove) :
    GrayTailHarvestChain (n := n) (b := b) L nn A sm [] := by
  intro k hk
  simp at hk

/-- Appending a freshly frozen round to the harvest chain: the new round's
stored `unavailable` must be the harvest of its own snapshot — taken at the
previous round's `serverTime` (`none`, the empty move, for the first
round). -/
lemma grayTailHarvestChain_append {n b : ℕ} {L nn : ℕ} {A : Allocation}
    {sm : ℕ → FamilyServerMove} {frozen : GrayTailFrozen n b}
    {p : GrayTailRound n b}
    (hchain : GrayTailHarvestChain L nn A sm frozen)
    (hp : p.unavailable =
      A ++ grayHarvest (n := n) (b := b) (p.epsDepth + L) p.slots nn
        (grayHarvestSnapshot sm
          (Option.map GrayTailRound.serverTime frozen.getLast?))) :
    GrayTailHarvestChain L nn A sm (frozen ++ [p]) := by
  intro k hk
  have hklen : k < frozen.length + 1 := by
    simpa using hk
  by_cases hkf : k < frozen.length
  · have hget : (frozen ++ [p])[k]'hk = frozen[k]'hkf :=
      List.getElem_append_left hkf
    rw [hget]
    have := hchain k hkf
    rw [this]
    congr 1
    congr 1
    by_cases hk0 : k = 0
    · simp [hk0]
    · have hk1 : k - 1 < frozen.length := by omega
      have hget1 : (frozen ++ [p])[k - 1]'(by
          rw [List.length_append, List.length_singleton]; omega) =
          frozen[k - 1]'hk1 :=
        List.getElem_append_left hk1
      simp only [hk0, dite_false, hget1]
  · have hke : k = frozen.length := by omega
    subst hke
    have hget : (frozen ++ [p])[frozen.length]'hk = p := by
      rw [List.getElem_append_right (Nat.le_refl _)]
      simp
    rw [hget, hp]
    congr 2
    by_cases hf0 : frozen.length = 0
    · have hfe : frozen = [] := List.length_eq_zero_iff.mp hf0
      simp [hfe]
    · have hlt : frozen.length - 1 < frozen.length := by omega
      have hget1 : (frozen ++ [p])[frozen.length - 1]'(by
          rw [List.length_append, List.length_singleton]; omega) =
          frozen[frozen.length - 1]'hlt :=
        List.getElem_append_left hlt
      rw [dif_neg hf0, hget1]
      have hlast : frozen.getLast? = some (frozen[frozen.length - 1]'hlt) := by
        rw [List.getLast?_eq_getElem?]
        exact List.getElem?_eq_getElem hlt
      rw [hlast]
      simp

/-- The state of the tail controller: its clock and round start, the finished flag, the frozen
rounds, the unavailable allocation, the open and anchoring slots, and the history of the
current round. -/
structure GrayTailState (n b : ℕ) where
  /-- The controller clock. -/
  time : ℕ
  /-- The time at which the current round started. -/
  roundStart : ℕ
  /-- Whether the controller has finished. -/
  done : Bool
  /-- The rounds already frozen, in the order they were closed. -/
  frozen : GrayTailFrozen n b
  /-- The allocation made unavailable by the frozen rounds. -/
  unavailable : Allocation
  /-- The slots of the current round. -/
  slots : List (GrayTailSlot n b)
  /-- The slots still forced during the anchoring phase. -/
  anchoringSlots : List (GrayTailSlot n b) := []
  /-- The client and server moves of the current round. -/
  history : FamilyGameHistory

/-- Whether the tail is waiting rather than playing; in the present construction it never is. -/
def grayTailWaitingB {n b : Nat} (_st : GrayTailState n b) : Bool :=
  false

/-- Whether the state is in its anchoring phase: `st.done` and `st.anchoringSlots` nonempty. A
terminal state may keep forcing the owner-round sons while the external server play advances to
a common anchoring horizon; the controller state itself is already stable during that phase. -/
def grayTailAnchoringOutputB {n b : Nat} (st : GrayTailState n b) : Bool :=
  st.done && !st.anchoringSlots.isEmpty

/-- Pair every slot with the move seen at that family index.  The family-game
semantics uses a default empty move beyond the returned list, so this must use
`familyClientMoveAt` rather than `List.zip`. -/
def grayTailSlotEntries {n b : ℕ}
    (slots : List (GrayTailSlot n b)) (move : FamilyClientMove) :
    List (GrayTailSlot n b × ClientMove) :=
  List.ofFn fun j : Fin slots.length =>
    (slots.get j, familyClientMoveAt move j.val)

/-- The slots of round `r`: all triples `(i, c, r)` with `i < n` a client and `c < used` a used root
son, planted at the grandson `r`; the empty list when `r` is not below the branching `b`. -/
def grayTailSlots (n b used r : ℕ) : List (GrayTailSlot n b) :=
  if hr : r < b then
    (List.finRange n).flatMap fun i =>
      ((List.finRange b).filter fun c => c.val < used).map fun c =>
        (i, c, ⟨r, hr⟩)
  else
    []

/-- The frozen recursive moves, indexed by their outer grandson slots. -/
def grayTailFrozenEntries {n b : ℕ}
    (frozen : GrayTailFrozen n b) :
    List (GrayTailSlot n b × ClientMove) :=
  frozen.flatMap fun p => grayTailSlotEntries p.slots p.move

/-- The frozen rounds as calls `(p.epsDepth, p.allocated.toFinset)`: each round contributes its
coarse depth and the finite set of strings it allocated. -/
def grayTailFrozenCalls {n b : ℕ}
    (frozen : GrayTailFrozen n b) : List (ℕ × Finset BitString) :=
  frozen.map fun p => (p.epsDepth, p.allocated.toFinset)

/-- Add the currently running recursive family move to the frozen entries. -/
def grayTailEntries {n b : ℕ}
    (frozen : GrayTailFrozen n b) (slots : List (GrayTailSlot n b))
    (current : FamilyClientMove) :
    List (GrayTailSlot n b × ClientMove) :=
  grayTailFrozenEntries frozen ++ grayTailSlotEntries slots current

/-- The recursive move planted at one outer grandson: the move of the first entry whose slot is
`slot`, and the empty move if there is none. -/
def grayTailEntryMove {n b : ℕ}
    (entries : List (GrayTailSlot n b × ClientMove))
    (slot : GrayTailSlot n b) : ClientMove :=
  ((entries.find? fun p => decide (p.1 = slot)).map Prod.snd).getD []

/-- Sum of the recursive root requests already planted under one root son. -/
def grayTailSonBase {n b : ℕ}
    (entries : List (GrayTailSlot n b × ClientMove))
    (i : Fin n) (c : Fin b) : ℚ :=
  entries.foldr (fun p acc =>
    if p.1.1 = i ∧ p.1.2.1 = c then getReq p.2 [] + acc else acc) 0

/-- The request of one root son: its base `grayTailSonBase entries i c` when that base does not
exceed `threshold`, and `eps` when it does. -/
def grayTailSonRequest {n b : ℕ}
    (threshold eps : ℚ)
    (entries : List (GrayTailSlot n b × ClientMove))
    (i : Fin n) (c : Fin b) : ℚ :=
  let q := grayTailSonBase entries i c
  if threshold < q then eps else q

/-- The request of one root: the sum of `grayTailSonRequest` over the `b` sons, raised to `max q
targetFloor` once `done` is set. -/
def grayTailRootRequest {n b : ℕ}
    (done : Bool) (targetFloor threshold eps : ℚ)
    (entries : List (GrayTailSlot n b × ClientMove))
    (i : Fin n) : ℚ :=
  let q := ∑ c : Fin b, grayTailSonRequest threshold eps entries i c
  if done then max q targetFloor else q

/-- The outer family client move that grafts all frozen and current recursive calls back into the
family: client `i` plays `graftTwoLevel` of the root request `grayTailRootRequest done
targetFloor threshold eps entries i`, the son requests `grayTailSonRequest threshold eps entries
i c` and the grandson moves `grayTailEntryMove entries (i, c, c')`, where `entries =
grayTailEntries frozen slots current`. -/
def grayTailFamilyMove {n b : ℕ}
    (done : Bool) (targetFloor threshold eps : ℚ)
    (frozen : GrayTailFrozen n b) (slots : List (GrayTailSlot n b))
    (current : FamilyClientMove) : FamilyClientMove :=
  let entries := grayTailEntries frozen slots current
  List.ofFn fun i : Fin n =>
    graftTwoLevel (grayTailRootRequest done targetFloor threshold eps entries i) b
      (fun c =>
        if hc : c < b then
          grayTailSonRequest threshold eps entries i ⟨c, hc⟩
        else 0)
      (fun c c' =>
        if hc : c < b then
          if hc' : c' < b then
            grayTailEntryMove entries (i, ⟨c, hc⟩, ⟨c', hc'⟩)
          else []
        else [])

/-- Restrict every tree of a family move to the actual outer branching. -/
def inTreeFamilyServerMove (b : ℕ) (sm : FamilyServerMove) :
    FamilyServerMove :=
  sm.map (inTreeServerMove b)

/-- The server move seen by the recursive family game in one round: the grandchild extraction
`extractGrandchildFamilyMove slots sm`, restricted to the outer branching by
`inTreeFamilyServerMove b` and truncated at depth `truncDepth`. The selected grandson slots are
globally fresh, so outer coherence separates their raw allocations from earlier rounds;
filtering at the current fine depth then removes precisely the cylinders that could enter an
earlier gray neighbourhood, and since recursive positive requests are all at least that fine
scale, `serves_truncAlloc_iff` shows that the filtering does not change service. -/
def grayTailLocalServerMove {n b : ℕ} (truncDepth : ℕ)
    (slots : List (GrayTailSlot n b)) (sm : FamilyServerMove) :
    FamilyServerMove :=
  truncFamilyServerMove truncDepth
    (inTreeFamilyServerMove b (extractGrandchildFamilyMove slots sm))

/-- Root allocations of a local family server move, in list form for the
decidable gray-goal test. -/
def grayTailLocalAllocatedList (m : FamilyServerMove) : List BitString :=
  (List.range m.length).flatMap fun i => getFamilyAlloc m i []

/-- The move of the recursive strategy in the current round: `sigma` applied at the call depth
`grayCallDepth q e`, the round depth `grayTailRoundEps q L e r` for `r` the number of frozen
rounds, the state's unavailable allocation, its slot count and its history. -/
def grayTailCurrentMove {n b : ℕ}
    (q L e : ℕ) (sigma : FamilyStrategyScheme)
    (st : GrayTailState n b) : FamilyClientMove :=
  let r := st.frozen.length
  sigma (grayCallDepth q e) (grayTailRoundEps q L e r)
    st.unavailable st.slots.length st.history

/-- Request accumulated at a son after freezing a completed round. -/
def grayTailFrozenSonBase {n b : ℕ}
    (frozen : GrayTailFrozen n b) (i : Fin n) (c : Fin b) : ℚ :=
  grayTailSonBase (grayTailFrozenEntries frozen) i c

/-- The unresolved slots for round `round`: all triples `(i, c, round)` with `c < used` whose frozen
son base does not exceed `threshold` and which currently hold no family reserve; the empty list
when `round` is not below the branching `b`. The chronological search is the ordinary exhaustive
reserve search; an unanchored hit is handled by the terminal anchoring phase before this list is
used. -/
def grayTailNextSlots {n b : ℕ}
    (e used round : ℕ) (threshold : ℚ) (A : Allocation)
    (frozen : GrayTailFrozen n b) (sm : FamilyServerMove) :
    List (GrayTailSlot n b) :=
  if hr : round < b then
    (List.finRange n).flatMap fun i =>
      ((List.finRange b).filter fun c =>
        c.val < used &&
        !(decide (threshold < grayTailFrozenSonBase frozen i c)) &&
        !(getTailFamilyReserve e b A n i.val sm [c.val]).isSome).map fun c =>
          (i, c, ⟨round, hr⟩)
  else
    []

/-- Two slots belong to the same outer root son; their last coordinate merely
records the recursive round in which that son is planted. -/
def grayTailSameSonB {n b : ℕ}
    (s t : GrayTailSlot n b) : Bool :=
  decide (s.1 = t.1 ∧ s.2.1 = t.2.1)

/-- Keep only candidates descending from a slot which was active in the
preceding round.  This helper is retained for the older monotone-set lemmas;
the source-faithful controller below deliberately uses the full freshly
recomputed candidate list, because a reserve may disappear and its son must
then be probed again. -/
def grayTailRetainedSlots {n b : ℕ}
    (current candidates : List (GrayTailSlot n b)) :
    List (GrayTailSlot n b) :=
  candidates.filter fun s => current.any (grayTailSameSonB s)

/-- Some currently active son has an ordinary reserve and requires the anchoring phase. -/
def grayTailHasUnanchoredReserveB {n b : ℕ}
    (e : ℕ) (A : Allocation) (slots : List (GrayTailSlot n b))
    (sm : FamilyServerMove) : Bool :=
  slots.any fun s =>
    (getTailFamilyReserve e b A n s.1.val sm [s.2.1.val]).isSome

/-- Every son represented by the waiting slots has acquired an anchored
epsilon-reserve. -/
def grayTailAllAnchoredB {n b : ℕ}
    (e : ℕ) (A : Allocation) (slots : List (GrayTailSlot n b))
    (sm : FamilyServerMove) : Bool :=
  slots.all fun s =>
    (getAnchoredTailFamilyReserve e b A n s.1.val sm [s.2.1.val]).isSome

/-- The son request displayed while waiting: `eps` for a son of a forced slot, and the ordinary
`grayTailSonRequest threshold eps entries i c` otherwise. During the terminal anchoring phase
the sons of the owner round therefore stay at `eps`. -/
def grayTailWaitingSonRequest {n b : ℕ}
    (forceSlots : List (GrayTailSlot n b))
    (threshold eps : ℚ)
    (entries : List (GrayTailSlot n b × ClientMove))
    (i : Fin n) (c : Fin b) : ℚ :=
  if forceSlots.any fun s => grayTailSameSonB s (i, c, s.2.2) then
    eps
  else
    grayTailSonRequest threshold eps entries i c

/-- The root request displayed while waiting: the sum of the waiting son requests, raised to the
target floor once the tail is finished. -/
def grayTailWaitingRootRequest {n b : ℕ}
    (done : Bool) (targetFloor threshold eps : ℚ)
    (forceSlots : List (GrayTailSlot n b))
    (entries : List (GrayTailSlot n b × ClientMove))
    (i : Fin n) : ℚ :=
  let value := ∑ c : Fin b,
    grayTailWaitingSonRequest forceSlots threshold eps entries i c
  if done then max value targetFloor else value

/-- The stable outer move used while the final anchored reserves are being served: client `i` plays
`graftTwoLevel` of `grayTailWaitingRootRequest`, the waiting son requests and the grandson moves
of the frozen entries. No new recursive call is displayed. -/
def grayTailWaitingFamilyMove {n b : ℕ}
    (done : Bool) (targetFloor threshold eps : ℚ)
    (frozen : GrayTailFrozen n b)
    (forceSlots : List (GrayTailSlot n b)) : FamilyClientMove :=
  let entries := grayTailFrozenEntries frozen
  List.ofFn fun i : Fin n =>
    graftTwoLevel
      (grayTailWaitingRootRequest done targetFloor threshold eps
        forceSlots entries i)
      b
      (fun c => if hc : c < b then
        grayTailWaitingSonRequest forceSlots threshold eps entries i ⟨c, hc⟩
        else 0)
      (fun c c' => if hc : c < b then if hc' : c' < b then
        grayTailEntryMove entries (i, ⟨c, hc⟩, ⟨c', hc'⟩)
        else [] else [])

/-- Number of currently unresolved source sons belonging to one outer root. -/
def grayTailRootSlotCount {n b : ℕ}
    (slots : List (GrayTailSlot n b)) (i : Fin n) : ℕ :=
  (slots.filter fun s => decide (s.1 = i)).length

/-- The hereditary stopping condition: every outer root has at most one
quarter of its source sons unresolved.  Unlike the old global count, this is
stable under passage to an arbitrary selected subfamily. -/
def grayTailPerRootQuarterB {n b : ℕ}
    (used : ℕ) (slots : List (GrayTailSlot n b)) : Bool :=
  (List.finRange n).all fun i =>
    decide (4 * grayTailRootSlotCount slots i ≤ used)

/-- Every client has lost at least three quarters of its `used` children. -/
def GrayTailPerRootQuarter {n b : ℕ}
    (used : ℕ) (slots : List (GrayTailSlot n b)) : Prop :=
  grayTailPerRootQuarterB used slots = true

/-- The SUV global stopping condition (p. 143): at most one quarter of *all*
source sons is still unresolved right now.  The global form is what makes the
round budget independent of the family size: while the test fails, more than
a quarter of the whole source family participates in the next round, so the
total accumulated request grows by a fixed fraction of its ceiling. -/
def grayTailGlobalQuarterB {n b : ℕ}
    (used : ℕ) (slots : List (GrayTailSlot n b)) : Bool :=
  decide (4 * slots.length ≤ n * used)

/-- At most a quarter of the whole slab of `n * used` coordinates is still open. -/
def GrayTailGlobalQuarter {n b : ℕ}
    (used : ℕ) (slots : List (GrayTailSlot n b)) : Prop :=
  4 * slots.length ≤ n * used

/-- The decidable global quarter test agrees with the predicate. -/
lemma grayTailGlobalQuarterB_eq_true_iff {n b : ℕ}
    (used : ℕ) (slots : List (GrayTailSlot n b)) :
    grayTailGlobalQuarterB (n := n) used slots = true ↔
      GrayTailGlobalQuarter (n := n) (b := b) used slots := by
  simp [grayTailGlobalQuarterB, GrayTailGlobalQuarter]

/-- The initial controller state: clock and round start `0`, not done, no frozen round, the ambient
allocation `A` unavailable, the round-`0` slots `grayTailSlots n b (2 ^ (e - a)) 0` open, no
anchoring slot and an empty history. -/
def grayTailInitialState (n b a e : ℕ) (A : Allocation) :
    GrayTailState n b where
  time := 0
  roundStart := 0
  done := false
  frozen := []
  unavailable := A
  slots := grayTailSlots n b (2 ^ (e - a)) 0
  anchoringSlots := []
  history := ([], [])

/-- One transition of the bounded parallel controller. A finished state, or one with no open slot,
only advances the clock. Otherwise the current recursive move and the local server move of the
round are computed; if the robust gray goal holds, the round is frozen (its allocation is added
to the unavailable region, the next slots are recomputed and the global quarter test or the
round cap may set `done`), and if it does not, the move and the server move are appended to the
history of the running round. -/
def grayTailStep {n b : ℕ}
    (q L a e : ℕ) (sigma : FamilyStrategyScheme) (A : Allocation)
    (st : GrayTailState n b) (sm : FamilyServerMove) : GrayTailState n b :=
  if grayTailWaitingB st then
    if grayTailAllAnchoredB e A st.anchoringSlots sm then
      { st with
        time := st.time + 1
        roundStart := st.time + 1
        done := true
        slots := []
        history := ([], []) }
    else
      { st with
        time := st.time + 1
        roundStart := st.time + 1
        history := ([], []) }
  else if st.done then { st with time := st.time + 1 }
  else if st.slots.isEmpty then
    { st with time := st.time + 1 }
  else
    let r := st.frozen.length
    let epsRound := grayTailRoundEps q L e r
    let deltaRound := grayTailRoundDelta q L e r
    let current := grayTailCurrentMove q L e sigma st
    let localSM := grayTailLocalServerMove deltaRound st.slots sm
    if familyRobustGrayGoalAtB (halfAmplification q)
        ((3 / 4 : ℚ) * dyadicScale (grayCallDepth q e))
        epsRound deltaRound st.slots.length st.unavailable current
        localSM then
      let allocated := grayTailLocalAllocatedList localSM
      let frozen' := st.frozen ++
        [{ serverTime := st.time
           roundIndex := r
           epsDepth := epsRound
           slots := st.slots
           move := current
           allocated := allocated
           unavailable := st.unavailable }]
      let unavailable' := st.unavailable ++
        neighborhoodCellsList epsRound allocated
      let threshold := dyadicScale e -
        dyadicScale e / (6 * halfAmplification q)
      let candidates := grayTailNextSlots e (2 ^ (e - a)) frozen'.length
        threshold A frozen' sm
      -- SUV p. 143: the *freshly recomputed* candidate list continues.  A son
      -- is skipped exactly while it currently holds a reserved interval or has
      -- crossed the threshold, and it re-enters when its reserve disappears.
      let next := candidates
      -- Stop globally: at most a quarter of all source sons is unresolved
      -- right now, so at least three quarters hold a reserve *at this very
      -- recheck* or have crossed the threshold.  The former yield persistent
      -- reserve exits (the reserve time dominates every frozen round), the
      -- latter threshold exits served at the horizon.
      let stop := grayTailGlobalQuarterB (2 ^ (e - a)) next
      -- The cap is only a totality guard.  The width-budget estimate shows it
      -- is unreachable: while the global stop is false, every round carries
      -- more than a quarter of the source family, and each carried son gains
      -- at least (3/4)·callScale/kappa of request, against the total budget
      -- of one epsilon per son.
      let done' := stop ||
        decide (grayTailRoundCount q ≤ frozen'.length)
      { time := st.time + 1
        roundStart := st.time + 1
        done := done'
        frozen := frozen'
        unavailable := unavailable'
        slots := next
        anchoringSlots := []
        history := ([], []) }
    else
      { st with
        time := st.time + 1
        history :=
          (st.history.1 ++ [current], st.history.2 ++ [localSM]) }

/-- The two-way form of one transition: `grayTailWaitingB` is identically
false and the `done` / empty-slot ticks agree, so the step is a stalled tick,
an accepted (frozen) round, or a rejected round.  Downstream case analyses use
this rather than reopening the nested guards. -/
lemma grayTailStep_eq {n b : ℕ}
    (q L a e : ℕ) (sigma : FamilyStrategyScheme) (A : Allocation)
    (st : GrayTailState n b) (sm : FamilyServerMove) :
    grayTailStep q L a e sigma A st sm =
      if (st.done || st.slots.isEmpty) then { st with time := st.time + 1 }
      else
        let r := st.frozen.length
        let epsRound := grayTailRoundEps q L e r
        let deltaRound := grayTailRoundDelta q L e r
        let current := grayTailCurrentMove q L e sigma st
        let localSM := grayTailLocalServerMove deltaRound st.slots sm
        if familyRobustGrayGoalAtB (halfAmplification q)
            ((3 / 4 : ℚ) * dyadicScale (grayCallDepth q e))
            epsRound deltaRound st.slots.length st.unavailable current
            localSM then
          let allocated := grayTailLocalAllocatedList localSM
          let frozen' := st.frozen ++
            [{ serverTime := st.time
               roundIndex := r
               epsDepth := epsRound
               slots := st.slots
               move := current
               allocated := allocated
               unavailable := st.unavailable }]
          let unavailable' := st.unavailable ++
            neighborhoodCellsList epsRound allocated
          let threshold := dyadicScale e -
            dyadicScale e / (6 * halfAmplification q)
          let candidates := grayTailNextSlots e (2 ^ (e - a)) frozen'.length
            threshold A frozen' sm
          { time := st.time + 1
            roundStart := st.time + 1
            done := grayTailGlobalQuarterB (n := n) (2 ^ (e - a)) candidates ||
              decide (grayTailRoundCount q ≤ frozen'.length)
            frozen := frozen'
            unavailable := unavailable'
            slots := candidates
            anchoringSlots := []
            history := ([], []) }
        else
          { st with
            time := st.time + 1
            history :=
              (st.history.1 ++ [current], st.history.2 ++ [localSM]) } := by
  by_cases hd : st.done = true
  · simp [grayTailStep, grayTailWaitingB, hd]
  · by_cases hs : st.slots.isEmpty = true
    · simp [grayTailStep, grayTailWaitingB, hd, hs]
    · simp [grayTailStep, grayTailWaitingB, hd, hs]

/-- State reconstructed from the finite outer server history. -/
def grayTailFold {n b : ℕ}
    (q L a e : ℕ) (sigma : FamilyStrategyScheme) (A : Allocation)
    (history : List FamilyServerMove) : GrayTailState n b :=
  history.foldl (grayTailStep q L a e sigma A)
    (grayTailInitialState n b a e A)

/-- The source target floor for one outer root: `(3 / 4) * dyadicScale a / halfAmplification (q +
1)`. -/
def grayTailTargetFloor (q a : ℕ) : ℚ :=
  ((3 / 4 : ℚ) * dyadicScale a) / halfAmplification (q + 1)

/-- The move displayed by a reconstructed controller state: `grayTailFamilyMove` at the target floor
`grayTailTargetFloor q a`, the threshold `dyadicScale e - dyadicScale e / (6 * halfAmplification
q)` and the step `dyadicScale e`, over the frozen rounds and the open slots, with the current
recursive move (empty once the state is done). -/
def grayTailOutput {n b : ℕ} (q L a e : ℕ)
    (sigma : FamilyStrategyScheme) (st : GrayTailState n b) :
    FamilyClientMove :=
  let current :=
    if st.done then [] else grayTailCurrentMove q L e sigma st
  grayTailFamilyMove st.done (grayTailTargetFloor q a)
    (dyadicScale e - dyadicScale e / (6 * halfAmplification q))
    (dyadicScale e) st.frozen st.slots current

/-- The executable half-step strategy: fold the server history with `grayTailFold` at the branching
`ladderBranching (grayTailBaseBranch q L) a e` and display `grayTailOutput` of the resulting
state. -/
def grayTailStrategy (q L a e : ℕ) (sigma : FamilyStrategyScheme) :
    ClientFamilyStrategy :=
  fun A n history =>
    let st : GrayTailState n
        (ladderBranching
          (grayTailBaseBranch q L) a e) :=
      grayTailFold q L a e sigma A history.2
    grayTailOutput q L a e sigma st

end Kolmogorov
