import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedSpendArithmetic
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailPointwise

/-!
# The charged tail only uses its own sources

The invariant that keeps the recursive calls of the charged controller apart:
`grayChargedSourceInvariant_initial` and `grayChargedSourceInvariant_step` say the initial tail
state uses only the first block of sources and that a tail step preserves this.
`grayChargedRoundDelta` is the round-local fine depth of a phase — spend passes run at the coarse
spend telescope, advantage rounds at the fine one — and `grayChargedRoundStrategy` the strategy
answering the round-local recursive call. `GrayTailTraceAt` abstracts the trace relation over that
depth (`GrayTailTraceAt.ofTrace`), and the closing lemmas certify the initial state
(`grayChargedCertified_initial`) and carry certification across a frozen spend pass
(`grayChargedSpendLayout_advance`, `grayChargedCore_with_next`).
-/



namespace Kolmogorov

/-- The initial charged tail state satisfies the source invariant: it only uses the first
`grayChargedSourceCount a e` children. -/
lemma grayChargedSourceInvariant_initial (n b a e : Nat)
    (A : Allocation) :
    GrayTailSourceInvariant (grayChargedSourceCount a e)
      (grayChargedTailInitialState n b a e A) := by
  constructor
  · intro s hs
    exact grayTailSlots_used hs
  · simp [grayChargedTailInitialState]

/-- A charged tail step preserves the source invariant. -/
lemma grayChargedSourceInvariant_step {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (st : GrayTailState n b) (sm : FamilyServerMove)
    (hst : GrayTailSourceInvariant (grayChargedSourceCount a e) st) :
    GrayTailSourceInvariant (grayChargedSourceCount a e)
      (grayChargedTailStep q L a e sigma A st sm) := by
  unfold grayChargedTailStep
  simp only [grayTailWaitingB, Bool.false_eq_true, if_false]
  split
  · exact ⟨hst.current, hst.frozen⟩
  · split
    · exact ⟨hst.current, hst.frozen⟩
    · split
      · constructor
        · intro s hs
          exact grayTailNextSlots_used hs
        · intro p hp
          rcases List.mem_append.mp hp with hp | hp
          · exact hst.frozen p hp
          · simp only [List.mem_singleton] at hp
            subst p
            simpa using hst.current
      · exact ⟨hst.current, hst.frozen⟩

/-- The round-local fine depth of a charged phase: spend passes run at the
coarse spend telescope, everything else at the descending advantage
schedule. -/
def grayChargedRoundDelta {n b : Nat} (q L a e : Nat)
    (phase : GrayChargedPhase) (st : GrayTailState n b) : Nat :=
  match phase with
  | .spend pass => grayChargedSpendDelta a L e pass
  | _ => grayTailRoundDelta q L e st.frozen.length

/-- The strategy answering the round-local recursive call of a charged
phase. -/
def grayChargedRoundStrategy {n b : Nat} (q L a e : Nat)
    (phase : GrayChargedPhase) (sigma : FamilyStrategyScheme)
    (st : GrayTailState n b) : ClientFamilyStrategy :=
  match phase with
  | .spend pass => sigma (grayChargedSpendAlphaDepth a)
      (grayChargedSpendEps a L e pass)
  | _ => grayTailRoundStrategy q L e sigma st

/-- `GrayTailTrace` with the round-local fine depth abstracted. -/
structure GrayTailTraceAt {n b : Nat}
    (delta : Nat) (sm : Nat -> FamilyServerMove)
    (t : Nat) (st : GrayTailState n b) : Prop where
  time_eq : st.time = t
  active_time :
    (st.done || st.slots.isEmpty) ≠ true →
      st.roundStart + st.history.2.length = t
  servers_eq :
    st.history.2 =
      List.ofFn fun j : Fin st.history.2.length =>
        grayTailLocalServerMove delta st.slots
          (sm (st.roundStart + j.val))
  frozen_before :
    ∀ p ∈ st.frozen, p.serverTime < st.roundStart
  terminal_empty :
    (st.done || st.slots.isEmpty) = true →
      st.history = ([], [])

/-- A traced tail state is traced at the delta of its current round. -/
lemma GrayTailTraceAt.ofTrace {n b q L e t : Nat}
    {sm : Nat -> FamilyServerMove} {st : GrayTailState n b}
    (h : GrayTailTrace q L e sm t st) :
    GrayTailTraceAt (grayTailRoundDelta q L e st.frozen.length) sm t st :=
  ⟨h.time_eq, h.active_time, h.servers_eq, h.frozen_before, h.terminal_empty⟩

/-- A tail state traced at the delta of its current round is traced. -/
lemma GrayTailTraceAt.toTrace {n b q L e t : Nat}
    {sm : Nat -> FamilyServerMove} {st : GrayTailState n b}
    (h : GrayTailTraceAt (grayTailRoundDelta q L e st.frozen.length) sm t st) :
    GrayTailTrace q L e sm t st :=
  ⟨h.time_eq, h.active_time, h.servers_eq, h.frozen_before, h.terminal_empty⟩

/-- The phase-aware trace of the charged controller. -/
def GrayChargedTrace {n b : Nat} (q L a e : Nat)
    (sm : Nat -> FamilyServerMove) (t : Nat)
    (stc : GrayChargedState n b) : Prop :=
  GrayTailTraceAt (grayChargedRoundDelta q L a e stc.phase stc.core)
    sm t stc.core

/-- The phase-aware history invariant of the charged controller. -/
def GrayChargedHistoryOK {n b : Nat} (q L a e : Nat)
    (sigma : FamilyStrategyScheme) (stc : GrayChargedState n b) : Prop :=
  stc.core.history.1 =
    List.ofFn fun j : Fin stc.core.history.2.length =>
      playClientFamily stc.core.unavailable stc.core.slots.length
        (grayChargedRoundStrategy q L a e stc.phase sigma stc.core)
        (grayTailServerOfList stc.core.history.2) j.val

/-- A tail state with a well-formed history gives a well-formed charged history in the
`advantage` phase. -/
lemma grayChargedHistoryOK_advantage {n b : Nat} {q L a e : Nat}
    {sigma : FamilyStrategyScheme} {st : GrayTailState n b}
    (h : GrayTailHistoryOK q L e sigma st) :
    GrayChargedHistoryOK q L a e sigma
      (n := n) (b := b) { phase := .advantage, core := st } := h

/-- Along a well-formed spend history, the spend move is the move of the recursive family play at
the current history length. -/
lemma grayChargedSpendMove_eq_play {n b : Nat} (q L a e pass : Nat)
    (sigma : FamilyStrategyScheme) (st : GrayTailState n b)
    (hst : GrayChargedHistoryOK q L a e sigma
      (n := n) (b := b) { phase := .spend pass, core := st }) :
    grayChargedSpendMove q L a e pass sigma st =
      playClientFamily st.unavailable st.slots.length
        (grayChargedRoundStrategy q L a e (.spend pass) sigma st)
        (grayTailServerOfList st.history.2) st.history.2.length := by
  rw [playClientFamily_eq_canonicalHistory]
  unfold grayChargedSpendMove grayChargedRoundStrategy
  apply congrArg
  unfold GrayChargedHistoryOK at hst
  exact Prod.ext hst (grayTailServerOfList_ofFn st.history.2).symm

/-- Extending a spend-round history by one rejected exchange preserves the
canonical-replay equation at the coarse spend scale. -/
lemma grayChargedHistoryOK_spendAppend {n b : Nat}
    (q L a e pass : Nat) (sigma : FamilyStrategyScheme)
    (st : GrayTailState n b)
    (hst : st.history.1 =
      List.ofFn fun j : Fin st.history.2.length =>
        playClientFamily st.unavailable st.slots.length
          (grayChargedRoundStrategy q L a e (.spend pass) sigma st)
          (grayTailServerOfList st.history.2) j.val)
    (m : FamilyServerMove) :
    st.history.1 ++ [grayChargedSpendMove q L a e pass sigma st] =
      List.ofFn fun j : Fin (st.history.2 ++ [m]).length =>
        playClientFamily st.unavailable st.slots.length
          (grayChargedRoundStrategy q L a e (.spend pass) sigma st)
          (grayTailServerOfList (st.history.2 ++ [m])) j.val := by
  have hcurrent := grayChargedSpendMove_eq_play q L a e pass sigma st hst
  have hfirst :
      (List.ofFn fun i : Fin st.history.2.length =>
        playClientFamily st.unavailable st.slots.length
          (grayChargedRoundStrategy q L a e (.spend pass) sigma st)
          (grayTailServerOfList (st.history.2 ++ [m])) i.val) =
        List.ofFn fun i : Fin st.history.2.length =>
          playClientFamily st.unavailable st.slots.length
            (grayChargedRoundStrategy q L a e (.spend pass) sigma st)
            (grayTailServerOfList st.history.2) i.val := by
    apply congrArg List.ofFn
    funext i
    apply playClientFamily_congr_before
    intro j hj
    apply grayTailServerOfList_append_before
    omega
  have hlast :
      playClientFamily st.unavailable st.slots.length
          (grayChargedRoundStrategy q L a e (.spend pass) sigma st)
          (grayTailServerOfList (st.history.2 ++ [m]))
          st.history.2.length =
        grayChargedSpendMove q L a e pass sigma st := by
    rw [hcurrent]
    apply playClientFamily_congr_before
    intro j hj
    apply grayTailServerOfList_append_before
    exact hj
  rw [show (st.history.2 ++ [m]).length = st.history.2.length + 1 by simp]
  rw [grayTail_ofFn_succ_last_nat, hfirst, <- hst, hlast]

/-- The slot `s` is one of the slots that spend pass `pass` may open. -/
def GrayChargedSpendSlot (n b source count pass : Nat)
    (s : GrayTailSlot n b) : Prop :=
  (s.2.1, s.2.2) ∈ grayChargedSpendPairs b source count pass

/-- The phase-tagged shape of one frozen charged round: an advantage round on
the descending fine schedule, or one of the eight coarse spend rounds. -/
def GrayChargedRoundShape {n b : Nat}
    (q L a e : Nat) (sm : Nat -> FamilyServerMove)
    (p : GrayTailRound n b) : Prop :=
  (p.epsDepth = grayTailRoundEps q L e p.roundIndex ∧
      grayChargedTailGoalAtB q e p.epsDepth (p.epsDepth + L)
        p.slots.length p.unavailable p.move
          (grayTailLocalServerMove (p.epsDepth + L) p.slots
            (sm p.serverTime)) = true ∧
      (forall s, s ∈ p.slots -> s.2.2.val = p.roundIndex) ∧
      p.roundIndex < grayChargedAdvantageRoundCount q ∧
      (forall s, s ∈ p.slots ->
        s.2.1.val < grayChargedSourceCount a e)) ∨
    (∃ pass, pass < 8 ∧ p.epsDepth = grayChargedSpendEps a L e pass ∧
      grayChargedSpendGoalAtB q L a e pass
        p.slots.length p.unavailable p.move
          (grayTailLocalServerMove (p.epsDepth + L) p.slots
            (sm p.serverTime)) = true ∧
      (∀ s ∈ p.slots, GrayChargedSpendSlot n b
        (grayChargedSourceCount a e) (grayChargedSpendCount q a e) pass s) ∧
      p.slots ≠ [])

/-- Replay data shared by all three phases.  Unlike `GrayTailShape`, it records
global freshness without prescribing a particular grandson coordinate. -/
structure GrayChargedCoreCertified {n b : Nat}
    (q L a e : Nat) (A : Allocation) (sm : Nat -> FamilyServerMove)
    (t : Nat) (st : GrayTailState n b) : Prop where
  time_eq : st.time = t
  frozen_chain : GrayTailHarvestChain L n A sm st.frozen
  all_slots_nodup : (grayTailFrozenSlots st.frozen ++ st.slots).Nodup
  round_valid : forall p, p ∈ st.frozen ->
    p.roundIndex < st.frozen.length ∧
    p.serverTime < t ∧
    p.allocated =
      grayTailLocalAllocatedList
        (grayTailLocalServerMove (p.epsDepth + L) p.slots
          (sm p.serverTime)) ∧
    p.slots.Nodup ∧
    GrayChargedRoundShape q L a e sm p
  frozen_index : forall k, forall hk : k < st.frozen.length,
    (st.frozen[k]'hk).roundIndex = k
  frozen_chrono : forall i j, forall hi : i < st.frozen.length,
    forall hj : j < st.frozen.length, i < j ->
      (st.frozen[i]'hi).serverTime < (st.frozen[j]'hj).serverTime

/-- A certified tail state satisfying the source invariant is a certified charged core. -/
lemma GrayChargedTailCertified.toCore {n b q L a e t : Nat}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    {st : GrayTailState n b}
    (hst : GrayChargedTailCertified q L e A sm t st)
    (hsource : GrayTailSourceInvariant (grayChargedSourceCount a e) st) :
    GrayChargedCoreCertified q L a e A sm t st := by
  refine ⟨hst.time_eq, hst.frozen_chain,
    hst.shape.allSlots_nodup, ?_, hst.frozen_index, hst.frozen_chrono⟩
  intro p hp
  rcases hst.round_valid p hp with
    ⟨hindex, hdepth, htime, halloc, hgoal, hnodup, hround⟩
  exact ⟨hindex, htime, halloc, hnodup,
    Or.inl ⟨hdepth, hgoal, hround,
      lt_of_lt_of_le hindex hst.frozen_bound.1,
      fun s hs => hsource.frozen p hp s hs⟩⟩

/-- Every frozen slot is either a source child or a slot of an earlier spend pass. -/
def GrayChargedFrozenLayout {n b : Nat}
    (source count pass : Nat) (frozen : GrayTailFrozen n b) : Prop :=
  forall s, s ∈ grayTailFrozenSlots frozen ->
    s.2.1.val < source ∨
      ∃ oldPass, oldPass < pass ∧
        GrayChargedSpendSlot n b source count oldPass s

/-- The invariants a tail state carries during spend pass `pass`: a certified core, a pass index
below `8`, the snapshot of the unavailable set, the slots of the pass, an active nonempty slot
list, the frozen layout of the pass and the round bound. -/
structure GrayChargedSpendCertified {n b : Nat}
    (q L a e : Nat) (A : Allocation) (sm : Nat -> FamilyServerMove)
    (t pass : Nat) (st : GrayTailState n b) : Prop where
  core : GrayChargedCoreCertified q L a e A sm t st
  pass_lt : pass < 8
  unavailable_snap : st.unavailable =
    A ++ grayHarvest (grayChargedSpendDelta a L e pass) st.slots n
      (grayHarvestSnapshot sm
        (Option.map GrayTailRound.serverTime st.frozen.getLast?))
  slots_eq : st.slots = grayChargedSlotsForPass q a e pass st.frozen
  slots_nonempty : st.slots.isEmpty = false
  done_false : st.done = false
  frozen_layout : GrayChargedFrozenLayout
    (grayChargedSourceCount a e) (grayChargedSpendCount q a e)
    pass st.frozen
  frozen_bound : st.frozen.length <= grayChargedAdvantageRoundCount q + pass

/-- The invariants a tail state carries once the run is finished: a certified core, no slots, an
empty history, the frozen layout of all eight passes and the round bound. -/
structure GrayChargedDoneCertified {n b : Nat}
    (q L a e : Nat) (A : Allocation) (sm : Nat -> FamilyServerMove)
    (t : Nat) (st : GrayTailState n b) : Prop where
  core : GrayChargedCoreCertified q L a e A sm t st
  slots_empty : st.slots = []
  done_true : st.done = true
  history_empty : st.history = ([], [])
  frozen_layout : GrayChargedFrozenLayout
    (grayChargedSourceCount a e) (grayChargedSpendCount q a e)
    8 st.frozen
  frozen_bound : st.frozen.length <= grayChargedAdvantageRoundCount q + 8

/-- The invariant carried by a charged controller state, one clause per phase: the certified tail
with the source invariant in `advantage`, the spend certificate in a spend pass, and the done
certificate in `done`. -/
inductive GrayChargedCertified {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme)
    (A : Allocation) (sm : Nat -> FamilyServerMove) (t : Nat) :
    GrayChargedState n b -> Prop
  | advantage (st : GrayTailState n b)
      (hcore : GrayChargedTailCertified q L e A sm t st)
      (hsource : GrayTailSourceInvariant (grayChargedSourceCount a e) st)
      (hdone : st.done = false) :
      GrayChargedCertified q L a e sigma A sm t
        { phase := .advantage, core := st }
  | spend (pass : Nat) (st : GrayTailState n b)
      (hspend : GrayChargedSpendCertified q L a e A sm t pass st) :
      GrayChargedCertified q L a e sigma A sm t
        { phase := .spend pass, core := st }
  | done (st : GrayTailState n b)
      (hdone : GrayChargedDoneCertified q L a e A sm t st) :
      GrayChargedCertified q L a e sigma A sm t
        { phase := .done, core := st }

/-- Under the source invariant every frozen slot uses a child below `used`. -/
lemma grayChargedFrozenSlots_source {n b used : Nat}
    {st : GrayTailState n b} (hst : GrayTailSourceInvariant used st) :
    forall s, s ∈ grayTailFrozenSlots st.frozen -> s.2.1.val < used := by
  intro s hs
  rw [grayTailFrozenSlots, List.mem_flatMap] at hs
  obtain ⟨p, hp, hsp⟩ := hs
  exact hst.frozen p hp s hsp

/-- A certified core stays certified when its slots are replaced by any distinct list disjoint
from the frozen slots and its history is reset. -/
lemma GrayChargedCoreCertified.withSlots {n b q L a e t : Nat}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    {st : GrayTailState n b}
    (hst : GrayChargedCoreCertified q L a e A sm t st)
    (done : Bool) (slots : List (GrayTailSlot n b))
    (hslots : slots.Nodup)
    (hdisjoint : (grayTailFrozenSlots st.frozen).Disjoint slots) :
    GrayChargedCoreCertified q L a e A sm t
      { st with done := done, slots := slots, history := ([], []) } := by
  refine ⟨hst.time_eq, hst.frozen_chain, ?_, ?_, hst.frozen_index,
    hst.frozen_chrono⟩
  · rw [List.nodup_append]
    exact ⟨(List.nodup_append.mp hst.all_slots_nodup).1,
      hslots, List.disjoint_iff_ne.mp hdisjoint⟩
  · intro p hp
    exact hst.round_valid p hp

/-- As `withSlots`, additionally replacing the (uncertified) state
`unavailable`; the core certificate constrains only the frozen rounds'
recorded snapshots. -/
lemma GrayChargedCoreCertified.withSlotsUnavailable {n b q L a e t : Nat}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    {st : GrayTailState n b}
    (hst : GrayChargedCoreCertified q L a e A sm t st)
    (done : Bool) (slots : List (GrayTailSlot n b))
    (hslots : slots.Nodup)
    (hdisjoint : (grayTailFrozenSlots st.frozen).Disjoint slots)
    (unavailable' : Allocation) :
    GrayChargedCoreCertified q L a e A sm t
      { st with done := done, slots := slots, history := ([], []),
                unavailable := unavailable' } := by
  refine ⟨hst.time_eq, hst.frozen_chain, ?_, ?_, hst.frozen_index,
    hst.frozen_chrono⟩
  · rw [List.nodup_append]
    exact ⟨(List.nodup_append.mp hst.all_slots_nodup).1,
      hslots, List.disjoint_iff_ne.mp hdisjoint⟩
  · intro p hp
    exact hst.round_valid p hp

/-- Under the source invariant the frozen rounds satisfy the layout condition of every pass. -/
lemma grayCharged_source_frozen_layout {n b source count pass : Nat}
    {st : GrayTailState n b} (hst : GrayTailSourceInvariant source st) :
    GrayChargedFrozenLayout source count pass st.frozen := by
  intro s hs
  left
  exact grayChargedFrozenSlots_source hst s hs

/-- A just-finished advantage phase records its last round at the
transition time, so the exit snapshot is the pass-0 snapshot. -/
lemma grayChargedTailStep_done_getLast {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (st : GrayTailState n b) (m : FamilyServerMove)
    (hactive : st.done = false)
    (hslots : st.slots.isEmpty = false)
    (hdone : (grayChargedTailStep q L a e sigma A st m).done = true) :
    Option.map GrayTailRound.serverTime
        (grayChargedTailStep q L a e sigma A st m).frozen.getLast? =
      some st.time := by
  by_cases hg : grayChargedTailGoalAtB q e
      (grayTailRoundEps q L e st.frozen.length)
      (grayTailRoundDelta q L e st.frozen.length)
      st.slots.length st.unavailable
      (grayTailCurrentMove q L e sigma st)
      (grayTailLocalServerMove
        (grayTailRoundDelta q L e st.frozen.length) st.slots m) = true
  · simp only [grayChargedTailStep, grayTailWaitingB, hactive, hslots,
      Bool.false_eq_true, ↓reduceIte, hg, List.getLast?_concat,
      Option.map_some]
  · exfalso
    simp only [grayChargedTailStep, grayTailWaitingB, hactive, hslots,
      Bool.false_eq_true, ↓reduceIte, hg] at hdone

/-- Opening the first spend pass from a certified tail state yields a certified charged state. -/
lemma grayChargedStartSpend_certified {n b q L a e t : Nat}
    {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove} {st : GrayTailState n b}
    {m : FamilyServerMove}
    (hcert : GrayChargedTailCertified q L e A sm t st)
    (hsource : GrayTailSourceInvariant (grayChargedSourceCount a e) st)
    (hm : m = grayHarvestSnapshot sm
      (Option.map GrayTailRound.serverTime st.frozen.getLast?)) :
    GrayChargedCertified q L a e sigma A sm t
      (grayChargedStartSpend q L a e A st m) := by
  let slots := grayChargedSlotsForPass q a e 0 st.frozen
  have hslotsNodup : slots.Nodup := by
    dsimp [slots, grayChargedSlotsForPass]
    exact grayChargedSpendSlots_nodup _ _ _ _ _ _ _
  have hdisjoint : (grayTailFrozenSlots st.frozen).Disjoint slots := by
    dsimp [slots, grayChargedSlotsForPass]
    exact grayChargedFrozenSlots_source_disjoint_spend hsource.frozen
  have hcore := (hcert.toCore (a := a) hsource).withSlots false slots hslotsNodup hdisjoint
  have hlayout := grayCharged_source_frozen_layout
    (count := grayChargedSpendCount q a e) (pass := 0) hsource
  change GrayChargedCertified q L a e sigma A sm t
    (if slots.isEmpty then
      { phase := .done
        core := { st with done := true, slots := [], history := ([], []) } }
    else
      { phase := .spend 0
        core :=
          { st with done := false, slots := slots, history := ([], []),
                    unavailable := A ++ grayHarvest (grayChargedSpendDelta a L e 0) slots n m } })
  by_cases hempty : slots.isEmpty = true
  · have hnil : slots = [] := by simpa using hempty
    rw [if_pos hempty]
    apply GrayChargedCertified.done
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [grayChargedStartSpend, slots, hempty] using
        ((hcert.toCore (a := a) hsource).withSlots true ([] : List (GrayTailSlot n b)))
          List.nodup_nil (List.disjoint_nil_right _)
    · simp
    · simp
    · simp
    · simpa [grayChargedStartSpend, slots, hempty] using
        (grayCharged_source_frozen_layout (count := grayChargedSpendCount q a e)
          (pass := 8) hsource)
    · dsimp [grayChargedStartSpend, slots, hempty]
      exact le_trans hcert.frozen_bound.1 (by omega)
  · have hnonempty : slots.isEmpty = false := by
      cases h : slots.isEmpty <;> simp_all
    rw [if_neg (by simpa using hnonempty)]
    apply GrayChargedCertified.spend 0
    refine ⟨?_, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (hcert.toCore (a := a) hsource).withSlotsUnavailable false slots
        hslotsNodup hdisjoint _
    · change A ++ grayHarvest (grayChargedSpendDelta a L e 0) slots n m = _
      rw [hm]
    · rfl
    · exact hnonempty
    · rfl
    · exact hlayout
    · exact hcert.frozen_bound.1

/-- A certified core stays certified at time `t + 1` after a tick that only changes the time,
round start, done flag and history. -/
lemma GrayChargedCoreCertified.tick {n b q L a e t : Nat}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    {st : GrayTailState n b}
    (hst : GrayChargedCoreCertified q L a e A sm t st)
    (roundStart : Nat) (done : Bool) (history : FamilyGameHistory) :
    GrayChargedCoreCertified q L a e A sm (t + 1)
      { st with time := st.time + 1, roundStart := roundStart, done := done,
                history := history } := by
  refine ⟨congrArg (fun u => u + 1) hst.time_eq, hst.frozen_chain,
    hst.all_slots_nodup, ?_, hst.frozen_index, hst.frozen_chrono⟩
  intro p hp
  rcases hst.round_valid p hp with
    ⟨hindex, htime, halloc, hnodup, hphase⟩
  exact ⟨hindex, by omega, halloc, hnodup, hphase⟩

/-- Every slot delivered for a pass is a pass-tagged spare slot. -/
lemma grayChargedSlotsForPass_spendSlot {n b : Nat}
    {q a e pass : Nat} {frozen : GrayTailFrozen n b}
    {s : GrayTailSlot n b}
    (hs : s ∈ grayChargedSlotsForPass q a e pass frozen) :
    GrayChargedSpendSlot n b (grayChargedSourceCount a e)
      (grayChargedSpendCount q a e) pass s := by
  unfold grayChargedSlotsForPass grayChargedSpendSlots at hs
  simp only [List.mem_flatMap, List.mem_map] at hs
  obtain ⟨i, -, p', hp', rfl⟩ := hs
  simpa [GrayChargedSpendSlot] using hp'

/-- Freeze one accepted coarse spend round. -/
lemma GrayChargedCoreCertified.freezeSpend {n b q L a e t pass : Nat}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    {st : GrayTailState n b}
    (hst : GrayChargedCoreCertified q L a e A sm t st)
    (p : GrayTailRound n b)
    (hpSlots : p.slots = st.slots)
    (hpIndex : p.roundIndex = st.frozen.length)
    (hpTime : p.serverTime = t)
    (hpass : pass < 8)
    (hpDepth : p.epsDepth = grayChargedSpendEps a L e pass)
    (hpAllocated : p.allocated =
      grayTailLocalAllocatedList
        (grayTailLocalServerMove (p.epsDepth + L) p.slots
          (sm p.serverTime)))
    (hpSnap : p.unavailable =
      A ++ grayHarvest (p.epsDepth + L) p.slots n
        (grayHarvestSnapshot sm
          (Option.map GrayTailRound.serverTime st.frozen.getLast?)))
    (hpGoal : grayChargedSpendGoalAtB q L a e pass
      p.slots.length p.unavailable p.move
        (grayTailLocalServerMove (p.epsDepth + L) p.slots
          (sm p.serverTime)) = true)
    (hpSpendSlots : ∀ s ∈ p.slots, GrayChargedSpendSlot n b
      (grayChargedSourceCount a e) (grayChargedSpendCount q a e) pass s)
    (hpNe : p.slots ≠ [])
    (unavailable' : Allocation) :
    GrayChargedCoreCertified q L a e A sm (t + 1)
      { time := st.time + 1
        roundStart := st.time + 1
        done := false
        frozen := st.frozen ++ [p]
        unavailable := unavailable'
        slots := []
        anchoringSlots := []
        history := ([], []) } := by
  refine ⟨congrArg (fun u => u + 1) hst.time_eq, ?_, ?_, ?_, ?_, ?_⟩
  · exact grayTailHarvestChain_append hst.frozen_chain hpSnap
  · simpa [grayTailFrozenSlots_append, hpSlots] using hst.all_slots_nodup
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · rcases hst.round_valid r hr with
        ⟨hindex, htime, halloc, hnodup, hphase⟩
      refine ⟨?_, ?_, halloc, hnodup, hphase⟩
      · simp only [List.length_append, List.length_singleton]
        omega
      · omega
    · have hrp : r = p := by simpa using hr
      subst r
      refine ⟨?_, ?_, hpAllocated, ?_,
        Or.inr ⟨pass, hpass, hpDepth, hpGoal, hpSpendSlots, hpNe⟩⟩
      · simp only [List.length_append, List.length_singleton, hpIndex]
        omega
      · omega
      · rw [hpSlots]
        exact (List.nodup_append.mp hst.all_slots_nodup).2.1
  · intro k hk
    have hklen : k < st.frozen.length + 1 := by simpa using hk
    by_cases hkf : k < st.frozen.length
    · rw [List.getElem_append_left hkf]
      exact hst.frozen_index k hkf
    · have hke : k = st.frozen.length := by omega
      subst hke
      have hgetp : (st.frozen ++ [p])[st.frozen.length]'hk = p := by
        rw [List.getElem_append_right (Nat.le_refl _)]
        simp
      rw [hgetp, hpIndex]
  · intro i j hi hj hij
    have hjlen : j < st.frozen.length + 1 := by simpa using hj
    by_cases hjf : j < st.frozen.length
    · have hif : i < st.frozen.length := by omega
      rw [List.getElem_append_left hif, List.getElem_append_left hjf]
      exact hst.frozen_chrono i j hif hjf hij
    · have hje : j = st.frozen.length := by omega
      subst hje
      have hif : i < st.frozen.length := by omega
      rw [List.getElem_append_left hif]
      have hgetp : (st.frozen ++ [p])[st.frozen.length]'hj = p := by
        rw [List.getElem_append_right (Nat.le_refl _)]
        simp
      rw [hgetp, hpTime]
      have hmem : st.frozen[i]'hif ∈ st.frozen := List.getElem_mem hif
      exact (hst.round_valid _ hmem).2.1

/-- The frozen layout condition weakens as the pass index grows. -/
lemma GrayChargedFrozenLayout.mono {n b source count pass pass' : Nat}
    {frozen : GrayTailFrozen n b}
    (h : GrayChargedFrozenLayout source count pass frozen)
    (hle : pass <= pass') :
    GrayChargedFrozenLayout source count pass' frozen := by
  intro s hs
  rcases h s hs with hs | ⟨oldPass, hold, hslot⟩
  · exact Or.inl hs
  · exact Or.inr ⟨oldPass, lt_of_lt_of_le hold hle, hslot⟩

/-- Freezing a round whose slots belong to pass `pass` yields the layout of pass `pass + 1`. -/
lemma grayChargedFrozenLayout_append {n b source count pass : Nat}
    {frozen : GrayTailFrozen n b} {p : GrayTailRound n b}
    (hlayout : GrayChargedFrozenLayout source count pass frozen)
    (hp : forall s, s ∈ p.slots ->
      GrayChargedSpendSlot n b source count pass s) :
    GrayChargedFrozenLayout source count (pass + 1) (frozen ++ [p]) := by
  intro s hs
  rw [grayTailFrozenSlots_append] at hs
  rcases List.mem_append.mp hs with hs | hs
  · rcases hlayout s hs with hs | ⟨oldPass, hold, hslot⟩
    · exact Or.inl hs
    · exact Or.inr ⟨oldPass, by omega, hslot⟩
  · exact Or.inr ⟨pass, by omega, hp s hs⟩

/-- Under the layout of a pass, the frozen slots are disjoint from the slots that pass opens. -/
lemma grayChargedFrozenLayout_disjoint_current {n b source count pass : Nat}
    {frozen frozen' : GrayTailFrozen n b}
    {threshold eps alpha : Rat}
    (hlayout : GrayChargedFrozenLayout source count pass frozen) :
    (grayTailFrozenSlots frozen).Disjoint
      (grayChargedSpendSlots source count pass threshold eps alpha frozen') := by
  rw [List.disjoint_iff_ne]
  intro s hs t ht heq
  rcases hlayout s hs with hsource | ⟨oldPass, hold, hslot⟩
  · have hge := grayChargedSpendSlots_son_ge ht
    rw [heq] at hsource
    omega
  · have htSlot := grayChargedSpendSlots_pair ht
    have hdisj := grayChargedSpendPairs_disjoint
      (b := b) (source := source) (count := count) hold
    rw [List.disjoint_iff_ne] at hdisj
    exact hdisj (s.2.1, s.2.2) hslot (t.2.1, t.2.2) htSlot
      (congrArg Prod.snd heq)

/-- Freezing the round of a certified spend pass yields the layout of the next pass. -/
lemma grayChargedSpendLayout_advance {n b q L a e t pass : Nat}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    {st : GrayTailState n b} {p : GrayTailRound n b}
    (hst : GrayChargedSpendCertified q L a e A sm t pass st)
    (hpSlots : p.slots = st.slots) :
    GrayChargedFrozenLayout (grayChargedSourceCount a e)
      (grayChargedSpendCount q a e) (pass + 1) (st.frozen ++ [p]) := by
  apply grayChargedFrozenLayout_append hst.frozen_layout
  intro s hs
  rw [hpSlots, hst.slots_eq] at hs
  simpa [GrayChargedSpendSlot] using grayChargedSpendSlots_pair hs

/-- A certified core stays certified when its slots are replaced by those of the next spend pass. -/
lemma grayChargedCore_with_next {n b q L a e t pass : Nat}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    {st : GrayTailState n b}
    (hcore : GrayChargedCoreCertified q L a e A sm t st)
    (hlayout : GrayChargedFrozenLayout
      (grayChargedSourceCount a e) (grayChargedSpendCount q a e)
      pass st.frozen)
    (_hpass : pass < 8) :
    GrayChargedCoreCertified q L a e A sm t
      { st with done := false, slots := grayChargedSlotsForPass q a e pass st.frozen,
                history := ([], []) } := by
  apply hcore.withSlots
  · dsimp [grayChargedSlotsForPass]
    exact grayChargedSpendSlots_nodup _ _ _ _ _ _ _
  · dsimp [grayChargedSlotsForPass]
    exact grayChargedFrozenLayout_disjoint_current hlayout

/-- The initial charged state is certified. -/
lemma grayChargedCertified_initial {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme)
    (A : Allocation) (sm : Nat -> FamilyServerMove) :
    GrayChargedCertified q L a e sigma A sm 0
      (grayChargedInitialState n b a e A) := by
  exact GrayChargedCertified.advantage _
    (grayChargedTailCertified_initial q L a e A sm)
    (grayChargedSourceInvariant_initial n b a e A)
    rfl

end Kolmogorov
