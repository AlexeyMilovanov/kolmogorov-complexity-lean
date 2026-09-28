import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailFlow
import KolmogorovMathlib.MonotoneComplexity.GacsDayGrayCompositionSelected

/-!
# Exact reserve exits

For mass accounting it is not enough to know that a reserve appeared at some
time.  We retain the last recursive round of a low-request son, the reserve
seen at that round, and the fact that the son never occurs later.
-/

namespace Kolmogorov

/-- A child was closed by a reserve: some frozen round held it and got a reserve, no earlier
round had one, and no later round holds it again. -/
def GrayTailReserveExit {n b : Nat} (e : Nat) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (frozen : GrayTailFrozen n b)
    (i : Fin n) (c : Fin b) : Prop :=
  exists pre p post R,
    frozen = pre ++ p :: post ∧
      GrayTailRoundHasSon p i c ∧
      IsTailFamilyReserve e b A n i.val (sm p.serverTime) [c.val] R ∧
      (pre = [] ∨ exists T,
        (forall q, q ∈ pre -> q.serverTime <= T) ∧
        T <= p.serverTime ∧
        (getTailFamilyReserve e b A n i.val (sm T) [c.val]).isNone) ∧
      forall q, q ∈ post -> ¬ GrayTailRoundHasSon q i c

/-- A reserve exit whose witness is refreshed after every later successful
controller round.  The owner remains the last round containing the son, while
`reserveTime` dominates every frozen round.  This is the formal version of the
SUV requirement that the interval "continued to be a reserved interval" after
the last recursive call of the son. -/
def GrayTailPersistentReserveExit {n b : Nat} (e : Nat) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (frozen : GrayTailFrozen n b)
    (i : Fin n) (c : Fin b) : Prop :=
  exists pre p post reserveTime R,
    frozen = pre ++ p :: post ∧
      GrayTailRoundHasSon p i c ∧
      IsTailFamilyReserve e b A n i.val (sm reserveTime) [c.val] R ∧
      (forall q, q ∈ frozen -> q.serverTime <= reserveTime) ∧
      (pre = [] ∨ exists T,
        (forall q, q ∈ pre -> q.serverTime <= T) ∧
        T <= p.serverTime ∧
        (getTailFamilyReserve e b A n i.val (sm T) [c.val]).isNone) ∧
      forall q, q ∈ post -> ¬ GrayTailRoundHasSon q i c

/-- At the last recorded server time no reserve was available at this child; vacuously true
before the first round. -/
def GrayTailFreshCheckpoint {n b : Nat} (e : Nat) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (frozen : GrayTailFrozen n b)
    (i : Fin n) (c : Fin b) : Prop :=
  frozen = [] ∨ exists last,
    last ∈ frozen ∧
      (forall q, q ∈ frozen -> q.serverTime <= last.serverTime) ∧
      (getTailFamilyReserve e b A n i.val
        (sm last.serverTime) [c.val]).isNone

/-- A son which leaves because its accumulated request crosses the threshold,
together with the last recursive round and a checkpoint before that round at
which no reserve existed.  The last call is the only call which may overlap a
reserve created after the terminal request is served. -/
def GrayTailThresholdExit {n b : Nat} (e : Nat) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (frozen : GrayTailFrozen n b)
    (i : Fin n) (c : Fin b) : Prop :=
  exists pre p post,
    frozen = pre ++ p :: post ∧
      GrayTailRoundHasSon p i c ∧
      (pre = [] ∨ exists T,
        (forall q, q ∈ pre -> q.serverTime <= T) ∧
        T <= p.serverTime ∧
        (getTailFamilyReserve e b A n i.val (sm T) [c.val]).isNone) ∧
      forall q, q ∈ post -> ¬ GrayTailRoundHasSon q i c

/-- Freezing a round that does not hold the child preserves closure by the threshold. -/
lemma GrayTailThresholdExit.append {n b e : Nat} {A : Allocation}
    {sm : Nat -> FamilyServerMove} {frozen : GrayTailFrozen n b}
    {i : Fin n} {c : Fin b} {p : GrayTailRound n b}
    (h : GrayTailThresholdExit e A sm frozen i c)
    (hp : ¬ GrayTailRoundHasSon p i c) :
    GrayTailThresholdExit e A sm (frozen ++ [p]) i c := by
  obtain ⟨pre, last, post, hsplit, hlast, hfresh, hpost⟩ := h
  refine ⟨pre, last, post ++ [p], ?_, hlast, hfresh, ?_⟩
  · simp [hsplit, List.append_assoc]
  · intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hpost q hq
    · simp only [List.mem_singleton] at hq
      subst q
      exact hp

/-- A child no open slot sits at has son base zero. -/
lemma grayTailSonBase_eq_zero_of_not_hasSon {n b : Nat}
    {slots : List (GrayTailSlot n b)} {move : FamilyClientMove}
    (i : Fin n) (c : Fin b)
    (h : ¬ GrayTailHasSon slots i c) :
    grayTailSonBase (grayTailSlotEntries slots move) i c = 0 := by
  apply grayTailSonBase_eq_zero_of_no_match
  intro z hz
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hz
  by_contra hsame
  push_neg at hsame
  apply h
  exact ⟨slots.get j, List.get_mem slots j, hsame.1, hsame.2⟩

/-- The frozen son base is additive over concatenation of frozen rounds. -/
lemma grayTailFrozenSonBase_append_list {n b : Nat}
    (left right : GrayTailFrozen n b) (i : Fin n) (c : Fin b) :
    grayTailFrozenSonBase (left ++ right) i c =
      grayTailFrozenSonBase left i c +
        grayTailFrozenSonBase right i c := by
  unfold grayTailFrozenSonBase grayTailFrozenEntries
  rw [List.flatMap_append]
  exact grayTailSonBase_append_globalEntries _ _ i c

/-- A child no frozen round holds has frozen son base zero. -/
lemma grayTailFrozenSonBase_eq_zero_of_no_round {n b : Nat}
    {frozen : GrayTailFrozen n b} (i : Fin n) (c : Fin b)
    (h : forall p, p ∈ frozen -> ¬ GrayTailRoundHasSon p i c) :
    grayTailFrozenSonBase frozen i c = 0 := by
  induction frozen with
  | nil => rfl
  | cons p rest ih =>
      have hp : ¬ GrayTailRoundHasSon p i c := h p (by simp)
      have hrest : forall q, q ∈ rest ->
          ¬ GrayTailRoundHasSon q i c := by
        intro q hq
        exact h q (by simp [hq])
      unfold grayTailFrozenSonBase grayTailFrozenEntries
      simp only [List.flatMap_cons]
      rw [grayTailSonBase_append_globalEntries,
        grayTailSonBase_eq_zero_of_not_hasSon i c hp]
      simpa [grayTailFrozenSonBase, grayTailFrozenEntries] using ih hrest

/-- When a child is closed by a reserve, its frozen son base splits as the base before the
closing round plus that round's contribution. -/
lemma GrayTailReserveExit.base_eq_prefix_add_last
    {n b e : Nat} {A : Allocation} {sm : Nat -> FamilyServerMove}
    {frozen : GrayTailFrozen n b} {i : Fin n} {c : Fin b}
    (h : GrayTailReserveExit e A sm frozen i c) :
    exists pre p R,
      GrayTailRoundHasSon p i c ∧
      IsTailFamilyReserve e b A n i.val (sm p.serverTime) [c.val] R ∧
      grayTailFrozenSonBase frozen i c =
        grayTailFrozenSonBase pre i c +
          grayTailSonBase (grayTailSlotEntries p.slots p.move) i c := by
  obtain ⟨pre, p, post, R, hsplit, hp, hR, _hfresh, hpost⟩ := h
  refine ⟨pre, p, R, hp, hR, ?_⟩
  rw [hsplit, show p :: post = [p] ++ post by rfl,
    grayTailFrozenSonBase_append_list,
    grayTailFrozenSonBase_append_list,
    grayTailFrozenSonBase_eq_zero_of_no_round i c hpost]
  have hone : grayTailFrozenSonBase ([p] : GrayTailFrozen n b) i c =
      grayTailSonBase (grayTailSlotEntries p.slots p.move) i c := by
    simp [grayTailFrozenSonBase, grayTailFrozenEntries, grayTailSonBase]
  rw [hone]
  ring

/-- Freezing a round that does not hold the child preserves closure by a reserve. -/
lemma GrayTailReserveExit.append {n b e : Nat} {A : Allocation}
    {sm : Nat -> FamilyServerMove} {frozen : GrayTailFrozen n b}
    {i : Fin n} {c : Fin b} {p : GrayTailRound n b}
    (h : GrayTailReserveExit e A sm frozen i c)
    (hp : ¬ GrayTailRoundHasSon p i c) :
    GrayTailReserveExit e A sm (frozen ++ [p]) i c := by
  obtain ⟨pre, last, post, R, hsplit, hlast, hR, hfresh, hpost⟩ := h
  refine ⟨pre, last, post ++ [p], R, ?_, hlast, hR, hfresh, ?_⟩
  · simp [hsplit, List.append_assoc]
  · intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hpost q hq
    · simp only [List.mem_singleton] at hq
      subst q
      exact hp

/-- The exit threshold of the tail controller at amplification parameter `q` and depth `e`:
`dyadicScale e` less one sixth of a half-amplification unit.  A child whose frozen base
request is above this value has spent its budget and leaves. -/
def grayTailExitThreshold (q e : Nat) : Rat :=
  dyadicScale e - dyadicScale e / (6 * halfAmplification q)

/-- The child `(i, c)` is still open in the state `(frozen, slots)`: it occupies a slot and
its last recorded checkpoint carries no reserve. -/
def GrayTailChildOpen {n b : Nat} (e : Nat) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (frozen : GrayTailFrozen n b)
    (slots : List (GrayTailSlot n b)) (i : Fin n) (c : Fin b) : Prop :=
  GrayTailHasSon slots i c ∧ GrayTailFreshCheckpoint e A sm frozen i c

/-- The child `(i, c)` is closed by the threshold: its frozen base request is above
`grayTailExitThreshold q e`, it has a threshold exit, and it holds no slot. -/
def GrayTailChildThresholdClosed {n b : Nat} (q e : Nat) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (frozen : GrayTailFrozen n b)
    (slots : List (GrayTailSlot n b)) (i : Fin n) (c : Fin b) : Prop :=
  grayTailExitThreshold q e < grayTailFrozenSonBase frozen i c ∧
    GrayTailThresholdExit e A sm frozen i c ∧ ¬ GrayTailHasSon slots i c

/-- The child `(i, c)` is closed by a persistent reserve: it has a persistent reserve exit,
its frozen base request is still at most `grayTailExitThreshold q e`, and it holds no slot. -/
def GrayTailChildReserveClosed {n b : Nat} (q e : Nat) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (frozen : GrayTailFrozen n b)
    (slots : List (GrayTailSlot n b)) (i : Fin n) (c : Fin b) : Prop :=
  GrayTailPersistentReserveExit e A sm frozen i c ∧
    grayTailFrozenSonBase frozen i c <= grayTailExitThreshold q e ∧
    ¬ GrayTailHasSon slots i c

/-- The round `p` is the round the state `st` accepts at server time `t`: it is stamped with
the time of `st`, displays the slots of `st`, strictly follows every frozen round, and still
fits into the `b` rounds of the ledger. -/
def GrayTailAcceptedRound {n b : Nat} (st : GrayTailState n b)
    (p : GrayTailRound n b) (t : Nat) : Prop :=
  p.serverTime = st.time ∧ p.slots = st.slots ∧ st.time = t ∧
    (forall q, q ∈ st.frozen -> q.serverTime < t) ∧ (st.frozen ++ [p]).length < b

/-- Every used child is in exactly one of three states: still open with a fresh checkpoint,
closed by exceeding the service threshold, or closed with a persistent reserve below the
threshold. -/
def GrayTailExactResolutionInvariant {n b : Nat} (q e a : Nat)
    (A : Allocation) (sm : Nat -> FamilyServerMove)
    (st : GrayTailState n b) : Prop :=
  forall i c, c.val < 2 ^ (e - a) ->
    (GrayTailHasSon st.slots i c ∧
      GrayTailFreshCheckpoint e A sm st.frozen i c) ∨
      ((dyadicScale e - dyadicScale e / (6 * halfAmplification q) <
          grayTailFrozenSonBase st.frozen i c) ∧
        GrayTailThresholdExit e A sm st.frozen i c ∧
        ¬ GrayTailHasSon st.slots i c) ∨
      (GrayTailPersistentReserveExit e A sm st.frozen i c ∧
        grayTailFrozenSonBase st.frozen i c <=
          dyadicScale e - dyadicScale e /
            (6 * halfAmplification q) ∧
        ¬ GrayTailHasSon st.slots i c)

/-- An active child in a tail step transitions either to remaining active with a fresh
checkpoint or to being closed by a threshold exit or persistent reserve exit. -/
private lemma grayTailStep_active_child
    {n b : Nat} (q a e t : Nat)
    (A : Allocation) (sm : Nat -> FamilyServerMove)
    (st : GrayTailState n b) (i : Fin n) (c : Fin b) (p : GrayTailRound n b)
    (hused : c.val < 2 ^ (e - a))
    (haccept : GrayTailAcceptedRound st p t)
    (hopen : GrayTailChildOpen e A sm st.frozen st.slots i c) :
    let frozen' : GrayTailFrozen n b := st.frozen ++ [p]
    let threshold := grayTailExitThreshold q e
    let candidates := grayTailNextSlots e (2 ^ (e - a))
      frozen'.length threshold A frozen' (sm t)
    GrayTailChildOpen e A sm frozen' candidates i c ∨
      GrayTailChildThresholdClosed q e A sm frozen' candidates i c ∨
      GrayTailChildReserveClosed q e A sm frozen' candidates i c := by
  intro frozen' threshold candidates
  obtain ⟨hp_time, hp_slots, htime, hbefore, hr⟩ := haccept
  obtain ⟨hcurrent, hfresh⟩ := hopen
  by_cases hnext : GrayTailHasSon candidates i c
  · have hnone := ((grayTailHasSon_next_iff hr i c).1 hnext).2.2
    refine Or.inl ⟨hnext, Or.inr ?_⟩
    refine ⟨p, by simp [frozen'], ?_, ?_⟩
    · intro old hold
      rcases List.mem_append.mp hold with hold | hold
      · have := hbefore old hold
        rw [hp_time, htime]
        exact this.le
      · simp only [List.mem_singleton] at hold
        subst old
        exact le_rfl
    · rw [hp_time, htime]
      exact by simpa using hnone
  · right
    have hremoved := grayTail_missing_after_freeze hr i c hused hnext
    by_cases hbase : threshold < grayTailFrozenSonBase frozen' i c
    · left
      refine ⟨hbase, ?_, hnext⟩
      refine ⟨st.frozen, p, [], by simp [frozen'], ?_, ?_, by simp⟩
      · change GrayTailHasSon p.slots i c
        rw [hp_slots]
        exact hcurrent
      · rcases hfresh with hempty | ⟨last, hlast, hmax, hnone⟩
        · exact Or.inl hempty
        · refine Or.inr ⟨last.serverTime, hmax, ?_, hnone⟩
          have := hbefore last hlast
          rw [hp_time, htime]
          exact this.le
    · right
      have hreserve := hremoved.resolve_left hbase
      obtain ⟨R, hR⟩ :=
        (getTailFamilyReserve_isSome_iff e b A n i.val (sm t) [c.val]).mp hreserve
      refine ⟨?_, le_of_not_gt hbase, hnext⟩
      refine ⟨st.frozen, p, [], t, R, by simp [frozen'], ?_, hR, ?_, ?_, ?_⟩
      · change GrayTailHasSon p.slots i c
        rw [hp_slots]
        exact hcurrent
      · intro old hold
        rcases List.mem_append.mp hold with hold | hold
        · exact (hbefore old hold).le
        · simp only [List.mem_singleton] at hold
          subst old
          rw [hp_time, htime]
      · rcases hfresh with hempty | ⟨last, hlast, hmax, hnone⟩
        · exact Or.inl hempty
        · refine Or.inr ⟨last.serverTime, hmax, ?_, hnone⟩
          have := hbefore last hlast
          rw [hp_time, htime]
          exact this.le
      · simp

/-- A child already closed by a threshold exit remains closed by a threshold exit when freezing
a round that does not hold the child. -/
private lemma grayTailStep_threshold_child
    {a n b : Nat} (q e t : Nat) (A : Allocation) (sm : Nat -> FamilyServerMove)
    (st : GrayTailState n b) (i : Fin n) (c : Fin b) (p : GrayTailRound n b)
    (hp_slots : p.slots = st.slots) (hr : (st.frozen ++ [p]).length < b)
    (hnonneg : forall z, z ∈ grayTailSlotEntries p.slots p.move -> 0 <= getReq z.2 [])
    (hclosed : GrayTailChildThresholdClosed q e A sm st.frozen st.slots i c) :
    let frozen' : GrayTailFrozen n b := st.frozen ++ [p]
    let threshold := grayTailExitThreshold q e
    let candidates := grayTailNextSlots e (2 ^ (e - a))
      frozen'.length threshold A frozen' (sm t)
    GrayTailChildThresholdClosed q e A sm frozen' candidates i c := by
  intro frozen' threshold candidates
  obtain ⟨hthreshold, htexit, hinactive⟩ := hclosed
  have hpnonneg : 0 <= grayTailSonBase (grayTailSlotEntries p.slots p.move) i c :=
    grayTailSonBase_nonneg_global hnonneg
  have hthreshold' : threshold < grayTailFrozenSonBase frozen' i c := by
    rw [grayTailFrozenSonBase_append_global]
    have : threshold < grayTailFrozenSonBase st.frozen i c +
        grayTailSonBase (grayTailSlotEntries p.slots p.move) i c := by linarith
    exact this
  have hpnone : ¬ GrayTailRoundHasSon p i c := by
    change ¬ GrayTailHasSon p.slots i c
    rw [hp_slots]
    exact hinactive
  refine ⟨hthreshold', ?_, ?_⟩
  · exact htexit.append hpnone
  · intro hn
    have hbelow := ((grayTailHasSon_next_iff hr i c).1 hn).2.1
    exact hbelow hthreshold'

/-- A child already closed by a persistent reserve exit either becomes active again with a fresh
checkpoint or remains closed by a persistent reserve exit when freezing a round that does not
hold the child. -/
private lemma grayTailStep_reserve_child
    {n b : Nat} (q a e t : Nat) (A : Allocation) (sm : Nat -> FamilyServerMove)
    (st : GrayTailState n b) (i : Fin n) (c : Fin b) (p : GrayTailRound n b)
    (hused : c.val < 2 ^ (e - a))
    (haccept : GrayTailAcceptedRound st p t)
    (hclosed : GrayTailChildReserveClosed q e A sm st.frozen st.slots i c) :
    let frozen' : GrayTailFrozen n b := st.frozen ++ [p]
    let threshold := grayTailExitThreshold q e
    let candidates := grayTailNextSlots e (2 ^ (e - a))
      frozen'.length threshold A frozen' (sm t)
    GrayTailChildOpen e A sm frozen' candidates i c ∨
      GrayTailChildReserveClosed q e A sm frozen' candidates i c := by
  intro frozen' threshold candidates
  obtain ⟨hp_time, hp_slots, htime, hbefore, hr⟩ := haccept
  obtain ⟨hexit, hbasecap, hinactive⟩ := hclosed
  have hpnone : ¬ GrayTailRoundHasSon p i c := by
    change ¬ GrayTailHasSon p.slots i c
    rw [hp_slots]
    exact hinactive
  have hbasecap' : grayTailFrozenSonBase frozen' i c <= threshold := by
    rw [grayTailFrozenSonBase_append_global,
      grayTailSonBase_eq_zero_of_not_hasSon i c hpnone, add_zero]
    exact hbasecap
  by_cases hnext : GrayTailHasSon candidates i c
  · have hnone := ((grayTailHasSon_next_iff hr i c).1 hnext).2.2
    left
    refine ⟨hnext, Or.inr ?_⟩
    refine ⟨p, by simp [frozen'], ?_, ?_⟩
    · intro old hold
      rcases List.mem_append.mp hold with hold | hold
      · have := hbefore old hold
        rw [hp_time, htime]
        exact this.le
      · simp only [List.mem_singleton] at hold
        subst old
        exact le_rfl
    · rw [hp_time, htime]
      exact by simpa using hnone
  · right
    have hremoved := grayTail_missing_after_freeze hr i c hused hnext
    have hreserve := hremoved.resolve_left (not_lt_of_ge hbasecap')
    obtain ⟨R, hR⟩ :=
      (getTailFamilyReserve_isSome_iff e b A n i.val (sm t) [c.val]).mp hreserve
    obtain ⟨pre, last, post, reserveTime, oldR, hsplit, hlast,
      _holdR, _holdmax, hfresh, hpost⟩ := hexit
    refine ⟨?_, hbasecap', hnext⟩
    refine ⟨pre, last, post ++ [p], t, R, ?_, hlast, hR, ?_, hfresh, ?_⟩
    · simp [frozen', hsplit, List.append_assoc]
    · intro old hold
      rcases List.mem_append.mp hold with hold | hold
      · exact (hbefore old hold).le
      · simp only [List.mem_singleton] at hold
        subst old
        rw [hp_time, htime]
    · intro old hold
      rcases List.mem_append.mp hold with hold | hold
      · exact hpost old hold
      · simp only [List.mem_singleton] at hold
        subst old
        exact hpnone

/-- A tail step preserves the exact resolution invariant. -/
lemma grayTailExactResolutionInvariant_step
    {n b q L a e t : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    (st : GrayTailState n b) (htime : st.time = t)
    (hbefore : forall p, p ∈ st.frozen -> p.serverTime < t)
    (hround : (st.done || st.slots.isEmpty) ≠ true ->
      st.frozen.length + 1 < b)
    (hprev : GrayTailExactResolutionInvariant q e a A sm st) :
    GrayTailExactResolutionInvariant q e a A sm
      (grayTailStep q L a e sigma A st (sm t)) := by
  intro i c hused
  unfold grayTailStep
  simp only [grayTailWaitingB, Bool.false_eq_true, if_false]
  split
  next _ => exact hprev i c hused
  next hnotdone =>
    split
    next _ => exact hprev i c hused
    next hnotslots =>
      have hactive : (st.done || st.slots.isEmpty) ≠ true := by
        simp [hnotdone, hnotslots]
      split
      next hgoal =>
        let p : GrayTailRound n b :=
          { serverTime := st.time
            roundIndex := st.frozen.length
            epsDepth := grayTailRoundEps q L e st.frozen.length
            slots := st.slots
            move := grayTailCurrentMove q L e sigma st
            allocated := grayTailLocalAllocatedList
              (grayTailLocalServerMove
                (grayTailRoundDelta q L e st.frozen.length) st.slots (sm t))
            unavailable := st.unavailable }
        let frozen' := st.frozen ++ [p]
        let threshold := dyadicScale e -
          dyadicScale e / (6 * halfAmplification q)
        let candidates := grayTailNextSlots e (2 ^ (e - a))
          frozen'.length threshold A frozen' (sm t)
        have hr : frozen'.length < b := by
          dsimp [frozen']
          simpa using hround hactive
        have hpoint := familyRobustGrayGoalAtB.to_pointwise hgoal
        have hnonneg : forall z, z ∈ grayTailSlotEntries p.slots p.move ->
            0 <= getReq z.2 [] := by
          apply grayTailSlotEntries_root_nonneg
            (kappa := halfAmplification q)
            (beta := (3 / 4 : Rat) * dyadicScale (grayCallDepth q e))
            (epsDepth := grayTailRoundEps q L e st.frozen.length)
            (deltaDepth := grayTailRoundDelta q L e st.frozen.length)
            (A := st.unavailable) (slots := p.slots) (move := p.move)
            (server := grayTailLocalServerMove
              (grayTailRoundDelta q L e st.frozen.length) st.slots (sm t))
            (halfAmplification_pos q)
            (mul_nonneg (by norm_num) (dyadicScale_pos _).le)
          simpa [p] using hpoint
        change (GrayTailHasSon candidates i c ∧
            GrayTailFreshCheckpoint e A sm frozen' i c) ∨
          (threshold < grayTailFrozenSonBase frozen' i c ∧
            GrayTailThresholdExit e A sm frozen' i c ∧
            ¬ GrayTailHasSon candidates i c) ∨
            (GrayTailPersistentReserveExit e A sm frozen' i c ∧
              grayTailFrozenSonBase frozen' i c <= threshold ∧
              ¬ GrayTailHasSon candidates i c)
        rcases hprev i c hused with ⟨hcurrent, hfresh⟩ | hresolved
        · exact grayTailStep_active_child q a e t A sm st i c p hused
            ⟨rfl, rfl, htime, hbefore, hr⟩ ⟨hcurrent, hfresh⟩
        · rcases hresolved with ⟨hthreshold, htexit, hinactive⟩ |
              ⟨hexit, hbasecap, hinactive⟩
          · right; left
            exact grayTailStep_threshold_child q e t A sm st i c p rfl hr
              hnonneg ⟨hthreshold, htexit, hinactive⟩
          · rcases grayTailStep_reserve_child q a e t A sm st i c p hused
              ⟨rfl, rfl, htime, hbefore, hr⟩ ⟨hexit, hbasecap, hinactive⟩ with hfresh' | hres'
            · left; exact hfresh'
            · right; right; exact hres'
      next _ => simpa using hprev i c hused

/-- Every state of a tail run satisfies the exact resolution invariant. -/
theorem grayTailExactResolutionInvariant_stateAt
    {n q L a e : Nat} (sigma : FamilyStrategyScheme)
    (A : Allocation) (sm : Nat -> FamilyServerMove) (t : Nat) :
    GrayTailExactResolutionInvariant q e a A sm
      (grayTailStateAt
        (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t) := by
  induction t with
  | zero =>
      intro i c hused
      left
      refine ⟨?_, Or.inl rfl⟩
      apply grayTailHasSon_slots
      · have hb : 2 <= grayTailBranch q L a e :=
          two_le_ladderBranching
            (by unfold grayTailBaseBranch; exact le_max_left _ _) a e
        omega
      · exact hused
  | succ t ih =>
      rw [grayTailStateAt_succ]
      apply grayTailExactResolutionInvariant_step
        (t := t) (sm := sm) _
      · exact (grayTailCertified_stateAt
          (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).time_eq
      · intro p hp
        exact (grayTailCertified_stateAt
          (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).round_valid p hp |>.2.2.1
      · intro hactive
        have hlen : (grayTailStateAt
            (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm t).frozen.length <
            grayTailRoundCount q := by
          by_contra h
          push_neg at h
          have hdone := grayTail_done_of_roundCount_stateAt_core
            (q := q) (L := L) (a := a) (e := e)
            (sigma := sigma) (A := A) (sm := sm) (t := t) h
          apply hactive
          simp [hdone]
        have hbranch : grayTailRoundCount q < grayTailBranch q L a e :=
          lt_of_lt_of_le (grayTailRoundCount_lt_baseBranch q L)
            (le_max_right _ _)
        omega
      · exact ih

/-- In a terminal tail state, every used child without an open slot either exceeds the service
threshold or carries a persistent reserve. -/
theorem grayTail_terminal_exact_resolution
    {n q L a e t : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    (_hterminal : ((grayTailStateAt
      (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).done ||
        (grayTailStateAt
          (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).slots.isEmpty) = true) :
    forall (i : Fin n) (c : Fin (grayTailBranch q L a e)),
      c.val < 2 ^ (e - a) ->
      ¬ GrayTailHasSon
        (grayTailStateAt
          (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).slots i c ->
      (dyadicScale e - dyadicScale e / (6 * halfAmplification q) <
        grayTailFrozenSonBase
          (grayTailStateAt
            (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm t).frozen i c) ∨
      GrayTailPersistentReserveExit e A sm
        (grayTailStateAt
          (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).frozen i c := by
  intro i c hused hinactive
  have hinv := grayTailExactResolutionInvariant_stateAt
    (n := n) sigma A sm t i c hused
  rcases hinv with hactive | hresolved
  · exact (hinactive hactive.1).elim
  · rcases hresolved with ⟨hthreshold, _htexit, _⟩ |
      ⟨hexit, _hbasecap, _⟩
    · exact Or.inl hthreshold
    · exact Or.inr hexit

/-- Terminal resolution retaining the last-call certificate required by the
geometric accounting. -/
theorem grayTail_terminal_detailed_resolution
    {n q L a e t : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    (_hterminal : ((grayTailStateAt
      (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).done ||
        (grayTailStateAt
          (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).slots.isEmpty) = true) :
    forall (i : Fin n) (c : Fin (grayTailBranch q L a e)),
      c.val < 2 ^ (e - a) ->
      ¬ GrayTailHasSon
        (grayTailStateAt
          (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).slots i c ->
      ((dyadicScale e - dyadicScale e / (6 * halfAmplification q) <
          grayTailFrozenSonBase
            (grayTailStateAt
              (n := n) (b := grayTailBranch q L a e)
              q L a e sigma A sm t).frozen i c) ∧
        GrayTailThresholdExit e A sm
          (grayTailStateAt
            (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm t).frozen i c) ∨
      (GrayTailPersistentReserveExit e A sm
          (grayTailStateAt
            (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm t).frozen i c ∧
        grayTailFrozenSonBase
            (grayTailStateAt
              (n := n) (b := grayTailBranch q L a e)
              q L a e sigma A sm t).frozen i c <=
          dyadicScale e - dyadicScale e /
            (6 * halfAmplification q)) := by
  intro i c hused hinactive
  have hinv := grayTailExactResolutionInvariant_stateAt
    (n := n) sigma A sm t i c hused
  rcases hinv with hactive | hresolved
  · exact (hinactive hactive.1).elim
  · rcases hresolved with ⟨hthreshold, htexit, _⟩ |
      ⟨hexit, hbasecap, _⟩
    · exact Or.inl ⟨hthreshold, htexit⟩
    · exact Or.inr ⟨hexit, hbasecap⟩

end Kolmogorov
