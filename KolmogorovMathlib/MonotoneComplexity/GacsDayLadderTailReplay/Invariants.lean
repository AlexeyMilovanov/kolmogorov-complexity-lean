import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailController

/-!
# The invariants a tail controller state carries

The properties every reachable state of the tail controller satisfies, and their preservation
under the operations that build a round. The slot lists stay repetition-free — freshly generated,
computed for the next round, or retained from candidates (`grayTailSlots_nodup`,
`grayTailNextSlots_nodup`, `grayTailRetainedSlots_nodup`,
`mem_candidates_of_mem_grayTailRetainedSlots`) — and every slot carries the round index it was
generated for (`grayTailSlots_round`), with `grayTailFrozenSlots` collecting the slots of the
frozen rounds. The certification invariant holds initially and survives freezing a round whose
recorded data meet the round conditions (`grayTailCertified_initial`, `grayTailCertified_freeze`).
`GrayTailSonPresent` names the condition that some current slot sits at a given root and son.
-/



namespace Kolmogorov

/-- The freshly generated slot list of a round has no repetitions. -/
lemma grayTailSlots_nodup (n b used r : ℕ) :
    (grayTailSlots n b used r).Nodup := by
  unfold grayTailSlots
  split
  · refine List.nodup_flatMap.mpr ⟨?_, ?_⟩
    · intro i hi
      exact ((List.nodup_finRange b).filter _).map fun c d h => by
        exact congrArg (fun p => p.2.1) h
    · refine (List.nodup_finRange n).imp ?_
      intro i j hij x hxi hxj
      simp only [List.mem_map, List.mem_filter, List.mem_finRange] at hxi hxj
      obtain ⟨ci, _, rfl⟩ := hxi
      obtain ⟨cj, _, h⟩ := hxj
      exact hij (congrArg Prod.fst h).symm
  · exact List.nodup_nil

/-- The slot list computed for the next round has no repetitions. -/
lemma grayTailNextSlots_nodup {n b : ℕ}
    (e used round : ℕ) (threshold : ℚ) (A : Allocation)
    (frozen : GrayTailFrozen n b) (sm : FamilyServerMove) :
    (grayTailNextSlots e used round threshold A frozen sm).Nodup := by
  unfold grayTailNextSlots
  split
  · refine List.nodup_flatMap.mpr ⟨?_, ?_⟩
    · intro i hi
      exact (((List.nodup_finRange b).filter _).map fun c d h => by
        exact congrArg (fun p => p.2.1) h)
    · refine (List.nodup_finRange n).imp ?_
      intro i j hij x hxi hxj
      simp only [List.mem_map, List.mem_filter, List.mem_finRange] at hxi hxj
      obtain ⟨ci, _, rfl⟩ := hxi
      obtain ⟨cj, _, h⟩ := hxj
      exact hij (congrArg Prod.fst h).symm
  · exact List.nodup_nil

/-- Retaining slots from a repetition-free candidate list leaves it repetition-free. -/
lemma grayTailRetainedSlots_nodup {n b : ℕ}
    (current candidates : List (GrayTailSlot n b))
    (h : candidates.Nodup) :
    (grayTailRetainedSlots current candidates).Nodup := by
  exact h.filter _

/-- Retained slots come from the candidate list. -/
lemma mem_candidates_of_mem_grayTailRetainedSlots {n b : ℕ}
    {current candidates : List (GrayTailSlot n b)}
    {s : GrayTailSlot n b}
    (hs : s ∈ grayTailRetainedSlots current candidates) :
    s ∈ candidates := by
  exact (List.mem_filter.mp hs).1

/-- All slots used in the already frozen rounds. -/
def grayTailFrozenSlots {n b : ℕ}
    (frozen : GrayTailFrozen n b) : List (GrayTailSlot n b) :=
  frozen.flatMap fun p => p.slots

/-- Every freshly generated slot carries the round index it was generated for. -/
lemma grayTailSlots_round {n b used r : ℕ}
    {s : GrayTailSlot n b} (hs : s ∈ grayTailSlots n b used r) :
    s.2.2.val = r := by
  unfold grayTailSlots at hs
  split at hs
  · simp only [List.mem_flatMap, List.mem_map, List.mem_filter,
      List.mem_finRange] at hs
    obtain ⟨i, -, c, -, rfl⟩ := hs
    rfl
  · simp at hs

/-- Every slot computed for the next round carries that round's index. -/
lemma grayTailNextSlots_round {n b e used round : ℕ}
    {threshold : ℚ} {A : Allocation} {frozen : GrayTailFrozen n b}
    {sm : FamilyServerMove} {s : GrayTailSlot n b}
    (hs : s ∈ grayTailNextSlots e used round threshold A frozen sm) :
    s.2.2.val = round := by
  unfold grayTailNextSlots at hs
  split at hs
  · simp only [List.mem_flatMap, List.mem_map, List.mem_filter,
      List.mem_finRange] at hs
    obtain ⟨i, -, c, -, rfl⟩ := hs
    rfl
  · simp at hs

/-- The slot layout invariant of the dynamic parallel controller: the frozen slots are pairwise
distinct and all carry a round index below the number of frozen rounds, and the open slots are
pairwise distinct and all carry the current round index `st.frozen.length`. -/
structure GrayTailShape {n b : ℕ} (st : GrayTailState n b) : Prop where
  frozen_nodup : (grayTailFrozenSlots st.frozen).Nodup
  frozen_round_lt : ∀ s ∈ grayTailFrozenSlots st.frozen,
    s.2.2.val < st.frozen.length
  slots_nodup : st.slots.Nodup
  slots_round : ∀ s ∈ st.slots, s.2.2.val = st.frozen.length

/-- All cylinders made unavailable by the already frozen rounds. -/
def grayTailFrozenAllocated {n b : ℕ}
    (frozen : GrayTailFrozen n b) : Allocation :=
  frozen.flatMap grayTailRoundUnavailable

/-- The frozen rounds form a chain: each round's unavailable set is the initial one extended by the
cylinders of all earlier rounds. -/
def GrayTailFrozenChain {n b : ℕ} :
    Allocation → GrayTailFrozen n b → Prop
  | _, [] => True
  | unavailable, p :: frozen =>
      p.unavailable = unavailable ∧
        GrayTailFrozenChain
          (unavailable ++ grayTailRoundUnavailable p) frozen

/-- Appending a round whose unavailable set is the accumulated one extends the chain. -/
lemma grayTailFrozenChain_append {n b : ℕ}
    {A : Allocation} {frozen : GrayTailFrozen n b}
    (hchain : GrayTailFrozenChain A frozen)
    (p : GrayTailRound n b)
    (hp : p.unavailable = A ++ grayTailFrozenAllocated frozen) :
    GrayTailFrozenChain A (frozen ++ [p]) := by
  induction frozen generalizing A with
  | nil =>
      simpa [GrayTailFrozenChain, grayTailFrozenAllocated] using hp
  | cons q frozen ih =>
      rcases hchain with ⟨hq, hchain⟩
      constructor
      · exact hq
      · apply ih hchain
        simpa [grayTailFrozenAllocated, List.append_assoc] using hp

/-- The certificate carried by the controller state reconstructed at time `t`: the slot layout
`GrayTailShape`, the recorded time is `t`, the frozen rounds form a `GrayTailFrozenChain` over
`A` and `st.unavailable` is `A` extended by their cylinders, and every frozen round has an index
below the chain length, the precision `grayTailRoundEps q L e` of its index, a server time
strictly below `t`, the allocation list of its localised server move, a true robust gray goal
test, pairwise distinct slots and slots all carrying its own round index. -/
structure GrayTailCertified {n b : ℕ}
    (q L e : ℕ) (A : Allocation) (sm : ℕ → FamilyServerMove)
    (t : ℕ) (st : GrayTailState n b) : Prop where
  shape : GrayTailShape st
  time_eq : st.time = t
  frozen_chain : GrayTailFrozenChain A st.frozen
  unavailable_eq :
    st.unavailable = A ++ grayTailFrozenAllocated st.frozen
  round_valid : ∀ p ∈ st.frozen,
    p.roundIndex < st.frozen.length ∧
    p.epsDepth = grayTailRoundEps q L e p.roundIndex ∧
    p.serverTime < t ∧
    p.allocated =
      grayTailLocalAllocatedList
        (grayTailLocalServerMove (p.epsDepth + L) p.slots
          (sm p.serverTime)) ∧
    familyRobustGrayGoalAtB (halfAmplification q)
      ((3 / 4 : ℚ) * dyadicScale (grayCallDepth q e))
      p.epsDepth (p.epsDepth + L) p.slots.length p.unavailable
      p.move
        (grayTailLocalServerMove (p.epsDepth + L) p.slots
          (sm p.serverTime)) = true ∧
    p.slots.Nodup ∧
    ∀ s ∈ p.slots, s.2.2.val = p.roundIndex

/-- The finite local server history is the exact relocated segment of the
outer play starting at the recorded round start. -/
structure GrayTailTrace {n b : ℕ}
    (q L e : ℕ) (sm : ℕ → FamilyServerMove)
    (t : ℕ) (st : GrayTailState n b) : Prop where
  time_eq : st.time = t
  active_time :
    (st.done || st.slots.isEmpty) ≠ true →
      st.roundStart + st.history.2.length = t
  servers_eq :
    st.history.2 =
      List.ofFn fun j : Fin st.history.2.length =>
        grayTailLocalServerMove
          (grayTailRoundDelta q L e st.frozen.length) st.slots
          (sm (st.roundStart + j.val))
  frozen_before :
    ∀ p ∈ st.frozen, p.serverTime < st.roundStart
  terminal_empty :
    (st.done || st.slots.isEmpty) = true →
      st.history = ([], [])

/-- The server play reading its moves off a finite list, repeating the last move afterwards. -/
def grayTailServerOfList (history : List FamilyServerMove) :
    ℕ → FamilyServerMove :=
  fun t => history.getD t (history.getLastD [])

/-- The client move at time `t` depends only on the server moves before `t`. -/
lemma playClientFamily_congr_before
    (A : Allocation) (n : ℕ) (tau : ClientFamilyStrategy)
    (sm₁ sm₂ : ℕ → FamilyServerMove) (t : ℕ)
    (hsm : ∀ i, i < t → sm₁ i = sm₂ i) :
    playClientFamily A n tau sm₁ t =
      playClientFamily A n tau sm₂ t := by
  exact playClientFamily_congr A n tau t hsm

/-- The inner family strategy the controller uses in the current round: the scheme instantiated at
the call depth and the round's `epsilon` depth. -/
def grayTailRoundStrategy {n b : ℕ}
    (q L e : ℕ) (sigma : FamilyStrategyScheme)
    (st : GrayTailState n b) : ClientFamilyStrategy :=
  sigma (grayCallDepth q e)
    (grayTailRoundEps q L e st.frozen.length)

/-- The client half of the stored history is exactly the replay of the round strategy against the
stored server moves. -/
def GrayTailHistoryOK {n b : ℕ}
    (q L e : ℕ) (sigma : FamilyStrategyScheme)
    (st : GrayTailState n b) : Prop :=
  st.history.1 =
    List.ofFn fun j : Fin st.history.2.length =>
      playClientFamily st.unavailable st.slots.length
        (grayTailRoundStrategy q L e sigma st)
        (grayTailServerOfList st.history.2) j.val

/-- A state with empty stored history satisfies the replay invariant. -/
lemma grayTailHistoryOK_empty {n b : ℕ}
    (q L e : ℕ) (sigma : FamilyStrategyScheme)
    (time roundStart : ℕ) (done : Bool) (frozen : GrayTailFrozen n b)
    (unavailable : Allocation) (slots anchoringSlots : List (GrayTailSlot n b)) :
    GrayTailHistoryOK q L e sigma
      ({ time := time
         roundStart := roundStart
         done := done
         frozen := frozen
         unavailable := unavailable
         slots := slots
         anchoringSlots := anchoringSlots
         history := ([], []) } : GrayTailState n b) := by
  simp [GrayTailHistoryOK]

/-- Reading a finite list back as a server play and truncating to its length returns the list. -/
lemma grayTailServerOfList_ofFn (history : List FamilyServerMove) :
    List.ofFn
        (fun i : Fin history.length =>
          grayTailServerOfList history i.val) =
      history := by
  apply List.ext_get
  · simp
  · intro i hi₁ hi₂
    simp only [List.length_ofFn] at hi₁
    simp only [List.get_eq_getElem, List.getElem_ofFn]
    unfold grayTailServerOfList
    exact List.getD_eq_getElem history (history.getLastD []) hi₁

/-- Appending a move to the recorded list does not change the earlier moves of the derived play. -/
lemma grayTailServerOfList_append_before
    (history : List FamilyServerMove) (m : FamilyServerMove)
    (i : ℕ) (hi : i < history.length) :
    grayTailServerOfList (history ++ [m]) i =
      grayTailServerOfList history i := by
  unfold grayTailServerOfList
  rw [List.getD_eq_getElem _ _
    (by
      simpa using lt_trans hi (Nat.lt_succ_self history.length))]
  rw [List.getD_eq_getElem _ _ hi]
  exact List.getElem_append_left hi

/-- The appended move is the one the derived play makes at the old length. -/
lemma grayTailServerOfList_append_last
    (history : List FamilyServerMove) (m : FamilyServerMove) :
    grayTailServerOfList (history ++ [m]) history.length = m := by
  unfold grayTailServerOfList
  rw [List.getD_eq_getElem _ _ (by simp)]
  rw [List.getElem_append_right (le_refl _)]
  simp

/-- The client move at time `t` is the strategy applied to the list of the first `t` client and
server moves. -/
lemma playClientFamily_eq_canonicalHistory
    (A : Allocation) (n : ℕ) (tau : ClientFamilyStrategy)
    (sm : ℕ → FamilyServerMove) (t : ℕ) :
    playClientFamily A n tau sm t =
      tau A n
        (List.ofFn fun j : Fin t =>
            playClientFamily A n tau sm j.val,
          List.ofFn fun j : Fin t => sm j.val) := by
  cases t with
  | zero => simp [playClientFamily]
  | succ t => simp only [playClientFamily]

/-- A list of `t + 1` values built from a function on naturals splits as the first `t` values
followed by the last. -/
lemma grayTail_ofFn_succ_last_nat {α : Type*} (t : ℕ)
    (f : ℕ → α) :
    List.ofFn (fun i : Fin (t + 1) => f i.val) =
      List.ofFn (fun i : Fin t => f i.val) ++ [f t] := by
  rw [List.ofFn_succ_last]
  rfl

/-- Under the replay invariant the controller's current move is the move the round strategy would
play at the stored history length. -/
lemma grayTailCurrentMove_eq_play {n b : ℕ}
    (q L e : ℕ) (sigma : FamilyStrategyScheme)
    (st : GrayTailState n b)
    (hst : GrayTailHistoryOK q L e sigma st) :
    grayTailCurrentMove q L e sigma st =
      playClientFamily st.unavailable st.slots.length
        (grayTailRoundStrategy q L e sigma st)
        (grayTailServerOfList st.history.2) st.history.2.length := by
  rw [playClientFamily_eq_canonicalHistory]
  unfold grayTailCurrentMove grayTailRoundStrategy
  apply congrArg
  unfold GrayTailHistoryOK at hst
  exact Prod.ext hst (grayTailServerOfList_ofFn st.history.2).symm

/-- Appending the current move and a new server move preserves the replay invariant. -/
lemma grayTailHistoryOK_append {n b : ℕ}
    (q L e : ℕ) (sigma : FamilyStrategyScheme)
    (st : GrayTailState n b)
    (hst : GrayTailHistoryOK q L e sigma st)
    (m : FamilyServerMove) (time : ℕ) :
    GrayTailHistoryOK q L e sigma
      { st with
        time := time
        history :=
          (st.history.1 ++ [grayTailCurrentMove q L e sigma st],
            st.history.2 ++ [m]) } := by
  have hcurrent := grayTailCurrentMove_eq_play q L e sigma st hst
  have hfirst :
      (List.ofFn fun i : Fin st.history.2.length =>
        playClientFamily st.unavailable st.slots.length
          (grayTailRoundStrategy q L e sigma st)
          (grayTailServerOfList (st.history.2 ++ [m])) i.val) =
        List.ofFn fun i : Fin st.history.2.length =>
          playClientFamily st.unavailable st.slots.length
            (grayTailRoundStrategy q L e sigma st)
            (grayTailServerOfList st.history.2) i.val := by
    apply congrArg List.ofFn
    funext i
    apply playClientFamily_congr_before
    intro j hj
    apply grayTailServerOfList_append_before
    omega
  have hlast :
      playClientFamily st.unavailable st.slots.length
          (grayTailRoundStrategy q L e sigma st)
          (grayTailServerOfList (st.history.2 ++ [m]))
          st.history.2.length =
        grayTailCurrentMove q L e sigma st := by
    rw [hcurrent]
    apply playClientFamily_congr_before
    intro j hj
    apply grayTailServerOfList_append_before
    exact hj
  unfold GrayTailHistoryOK at hst ⊢
  change st.history.1 ++ [grayTailCurrentMove q L e sigma st] =
    List.ofFn (fun j : Fin (st.history.2 ++ [m]).length =>
      playClientFamily st.unavailable st.slots.length
        (grayTailRoundStrategy q L e sigma st)
        (grayTailServerOfList (st.history.2 ++ [m])) j.val)
  rw [show (st.history.2 ++ [m]).length = st.history.2.length + 1 by simp]
  rw [grayTail_ofFn_succ_last_nat, hfirst, ← hst, hlast]

/-- The initial controller state has the required slot bookkeeping shape. -/
lemma grayTailShape_initial (n b a e : ℕ) (A : Allocation) :
    GrayTailShape (grayTailInitialState n b a e A) := by
  refine ⟨?_, ?_, grayTailSlots_nodup _ _ _ _, ?_⟩
  · simp [grayTailFrozenSlots, grayTailInitialState]
  · simp [grayTailFrozenSlots, grayTailInitialState]
  · intro s hs
    change s ∈ grayTailSlots n b (2 ^ (e - a)) 0 at hs
    exact grayTailSlots_round hs

/-- Freezing one more round appends that round's slots to the frozen slot list. -/
lemma grayTailFrozenSlots_append {n b : ℕ}
    (frozen : GrayTailFrozen n b) (round : GrayTailRound n b) :
    grayTailFrozenSlots (frozen ++ [round]) =
      grayTailFrozenSlots frozen ++ round.slots := by
  simp [grayTailFrozenSlots]

/-- Freezing the current round and installing a fresh repetition-free slot list preserves the shape
invariant. -/
lemma grayTailShape_freeze {n b : ℕ} {st : GrayTailState n b}
    (hst : GrayTailShape st)
    (time roundStart roundIndex serverTime epsDepth : ℕ)
    (move : FamilyClientMove) (allocated unavailable : Allocation)
    (roundUnavailable : Allocation)
    (next : List (GrayTailSlot n b))
    (hnext : next.Nodup)
    (hnextRound : ∀ s ∈ next, s.2.2.val = st.frozen.length + 1)
    (anchoringSlots : List (GrayTailSlot n b))
    (done : Bool) (history : FamilyGameHistory) :
    GrayTailShape
      ({ time := time
         roundStart := roundStart
         done := done
         frozen := st.frozen ++
           [{ serverTime := serverTime
              roundIndex := roundIndex
              epsDepth := epsDepth
              slots := st.slots
              move := move
              allocated := allocated
              unavailable := roundUnavailable }]
         unavailable := unavailable
         slots := next
         anchoringSlots := anchoringSlots
         history := history } : GrayTailState n b) := by
  have hfrozen :
      (grayTailFrozenSlots st.frozen ++ st.slots).Nodup := by
    rw [List.nodup_append]
    refine ⟨hst.frozen_nodup, hst.slots_nodup, ?_⟩
    intro s hs t ht hstEq
    have hslt := hst.frozen_round_lt s hs
    have hteq := hst.slots_round t ht
    rw [hstEq] at hslt
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [grayTailFrozenSlots_append] using hfrozen
  · intro s hs
    rw [grayTailFrozenSlots_append] at hs
    rcases List.mem_append.mp hs with hs | hs
    · have := hst.frozen_round_lt s hs
      simp only [List.length_append, List.length_singleton]
      omega
    · have := hst.slots_round s hs
      simp only [List.length_append, List.length_singleton]
      omega
  · exact hnext
  · intro s hs
    simpa using hnextRound s hs

/-- Appending a round that records the current slots and installing a fresh slot list preserves the
shape invariant. -/
lemma grayTailShape_appendRound {n b : ℕ} {st : GrayTailState n b}
    (hst : GrayTailShape st) (time roundStart : ℕ) (done : Bool)
    (p : GrayTailRound n b) (hpSlots : p.slots = st.slots)
    (unavailable : Allocation) (next : List (GrayTailSlot n b))
    (hnext : next.Nodup)
    (hnextRound : ∀ s ∈ next, s.2.2.val = st.frozen.length + 1)
    (anchoringSlots : List (GrayTailSlot n b))
    (history : FamilyGameHistory) :
    GrayTailShape
      ({ time := time
         roundStart := roundStart
         done := done
         frozen := st.frozen ++ [p]
         unavailable := unavailable
         slots := next
         anchoringSlots := anchoringSlots
         history := history } : GrayTailState n b) := by
  have hfrozen :
      (grayTailFrozenSlots st.frozen ++ p.slots).Nodup := by
    rw [hpSlots]
    rw [List.nodup_append]
    refine ⟨hst.frozen_nodup, hst.slots_nodup, ?_⟩
    intro s hs t ht hEq
    have hslt := hst.frozen_round_lt s hs
    have hteq := hst.slots_round t ht
    rw [hEq, hteq] at hslt
    omega
  refine ⟨?_, ?_, hnext, ?_⟩
  · simpa [grayTailFrozenSlots_append] using hfrozen
  · intro s hs
    rw [grayTailFrozenSlots_append] at hs
    rcases List.mem_append.mp hs with hs | hs
    · have := hst.frozen_round_lt s hs
      simp only [List.length_append, List.length_singleton]
      omega
    · rw [hpSlots] at hs
      have := hst.slots_round s hs
      simp only [List.length_append, List.length_singleton]
      omega
  · intro s hs
    simpa using hnextRound s hs

/-- The initial state satisfies the certification invariant at time zero. -/
lemma grayTailCertified_initial {n b : ℕ}
    (q L a e : ℕ) (A : Allocation) (sm : ℕ → FamilyServerMove) :
    GrayTailCertified q L e A sm 0
      (grayTailInitialState n b a e A) := by
  refine ⟨grayTailShape_initial n b a e A, rfl, ?_, ?_, ?_⟩
  · simp [GrayTailFrozenChain, grayTailInitialState]
  · simp [grayTailFrozenAllocated, grayTailInitialState]
  · simp [grayTailInitialState]

/-- Freezing a round whose recorded data meet the round conditions preserves the certification
invariant. -/
lemma grayTailCertified_freeze {n b q L e t : ℕ}
    {A : Allocation} {sm : ℕ → FamilyServerMove}
    {st : GrayTailState n b}
    (hst : GrayTailCertified q L e A sm t st)
    (done : Bool) (p : GrayTailRound n b)
    (hpSlots : p.slots = st.slots)
    (hpIndex : p.roundIndex = st.frozen.length)
    (hpTime : p.serverTime = t)
    (hpDepth : p.epsDepth = grayTailRoundEps q L e p.roundIndex)
    (hpAllocated : p.allocated =
      grayTailLocalAllocatedList
        (grayTailLocalServerMove (p.epsDepth + L) p.slots
          (sm p.serverTime)))
    (hpUnavailable : p.unavailable = st.unavailable)
    (hpGoal : familyRobustGrayGoalAtB (halfAmplification q)
      ((3 / 4 : ℚ) * dyadicScale (grayCallDepth q e))
      p.epsDepth (p.epsDepth + L) p.slots.length p.unavailable
      p.move
        (grayTailLocalServerMove (p.epsDepth + L) p.slots
          (sm p.serverTime)) = true)
    (hpNodup : p.slots.Nodup)
    (hpRound : ∀ s ∈ p.slots, s.2.2.val = p.roundIndex)
    (next : List (GrayTailSlot n b)) (hnext : next.Nodup)
    (hnextRound : ∀ s ∈ next, s.2.2.val = st.frozen.length + 1)
    (anchoringSlots : List (GrayTailSlot n b))
    (history : FamilyGameHistory) :
    GrayTailCertified q L e A sm (t + 1)
      ({ time := t + 1
         roundStart := t + 1
         done := done
         frozen := st.frozen ++ [p]
         unavailable := st.unavailable ++ grayTailRoundUnavailable p
         slots := next
         anchoringSlots := anchoringSlots
         history := history } : GrayTailState n b) := by
  refine ⟨grayTailShape_appendRound hst.shape (t + 1) (t + 1)
      done p hpSlots
      _ next hnext hnextRound anchoringSlots history, rfl, ?_, ?_, ?_⟩
  · apply grayTailFrozenChain_append hst.frozen_chain
    calc
      p.unavailable = st.unavailable := hpUnavailable
      _ = A ++ grayTailFrozenAllocated st.frozen := hst.unavailable_eq
  · simp only [grayTailFrozenAllocated, List.flatMap_append,
      List.flatMap_singleton]
    rw [hst.unavailable_eq]
    simp [grayTailFrozenAllocated, List.append_assoc]
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · rcases hst.round_valid r hr with
        ⟨hindex, hdepth, htime, halloc, hgoal, hnodup, hround⟩
      refine ⟨?_, hdepth, ?_, halloc, hgoal, hnodup, hround⟩
      · simp only [List.length_append, List.length_singleton]
        omega
      · omega
    · have hrp : r = p := by simpa using hr
      subst r
      refine ⟨?_, hpDepth, ?_, hpAllocated, hpGoal, hpNodup, hpRound⟩
      · simp only [List.length_append, List.length_singleton, hpIndex]
        omega
      · omega

/-- Some current slot has root `i` and son `c`. -/
def GrayTailSonPresent {n b : ℕ} (slots : List (GrayTailSlot n b))
    (i : Fin n) (c : Fin b) : Prop :=
  ∃ s ∈ slots, s.1 = i ∧ s.2.1 = c

/- The historical-participation invariant of the retained controller is
retired: the source-faithful controller reuses the freshly recomputed
candidate list, so a son skipped while it held a reserve re-enters when the
reserve disappears.  The round budget is instead controlled by the global
width invariant of `GacsDayLadderTailGlobalProgress`. -/

end Kolmogorov
