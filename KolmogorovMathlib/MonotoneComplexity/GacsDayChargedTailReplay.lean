import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedTailController
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailReplay.Invariants
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailReplay.StateAt
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailReplay

/-!
# Replay invariants for the designated-gray advantage controller

All static slot, frozen-chain and history lemmas are reused from the established
controller.  This file proves only the transition-dependent invariants and
records the charged Boolean certificate for every accepted round.
-/

namespace Kolmogorov

/-- The invariants a charged tail state carries at time `t`: its shape and clock, the harvest
chain of its frozen rounds, the snapshot of the unavailable set, the round budget, and for
each frozen round its index, depth, server time, allocation, met goal and distinct slots, with
indices and server times increasing. -/
structure GrayChargedTailCertified {n b : Nat}
    (q L e : Nat) (A : Allocation) (sm : Nat -> FamilyServerMove)
    (t : Nat) (st : GrayTailState n b) : Prop where
  shape : GrayTailShape st
  time_eq : st.time = t
  frozen_chain : GrayTailHarvestChain L n A sm st.frozen
  unavailable_snap :
    st.unavailable =
      A ++ grayHarvest (grayTailRoundDelta q L e st.frozen.length)
        st.slots n
        (grayHarvestSnapshot sm
          (Option.map GrayTailRound.serverTime st.frozen.getLast?))
  frozen_bound : st.frozen.length <= grayChargedAdvantageRoundCount q ∧
    (st.done = false -> st.frozen.length < grayChargedAdvantageRoundCount q)
  round_valid : forall p, p ∈ st.frozen ->
    p.roundIndex < st.frozen.length ∧
    p.epsDepth = grayTailRoundEps q L e p.roundIndex ∧
    p.serverTime < t ∧
    p.allocated =
      grayTailLocalAllocatedList
        (grayTailLocalServerMove (p.epsDepth + L) p.slots
          (sm p.serverTime)) ∧
    grayChargedTailGoalAtB q e p.epsDepth (p.epsDepth + L)
      p.slots.length p.unavailable p.move
        (grayTailLocalServerMove (p.epsDepth + L) p.slots
          (sm p.serverTime)) = true ∧
    p.slots.Nodup ∧
    forall s, s ∈ p.slots -> s.2.2.val = p.roundIndex
  frozen_index : forall k, forall hk : k < st.frozen.length,
    (st.frozen[k]'hk).roundIndex = k
  frozen_chrono : forall i j, forall hi : i < st.frozen.length,
    forall hj : j < st.frozen.length, i < j ->
      (st.frozen[i]'hi).serverTime < (st.frozen[j]'hj).serverTime

/-- The initial charged tail state is certified at time `0`. -/
lemma grayChargedTailCertified_initial {n b : Nat}
    (q L a e : Nat) (A : Allocation) (sm : Nat -> FamilyServerMove) :
    GrayChargedTailCertified q L e A sm 0
      (grayChargedTailInitialState n b a e A) := by
  have hshape : GrayTailShape (grayChargedTailInitialState n b a e A) := by
    refine ⟨?_, ?_, grayTailSlots_nodup _ _ _ _, ?_⟩
    · simp [grayTailFrozenSlots, grayChargedTailInitialState]
    · simp [grayTailFrozenSlots, grayChargedTailInitialState]
    · intro s hs
      change s ∈ grayTailSlots n b (grayChargedSourceCount a e) 0 at hs
      exact grayTailSlots_round hs
  have hbound : (grayChargedTailInitialState n b a e A).frozen.length
    <= grayChargedAdvantageRoundCount q ∧
      ((grayChargedTailInitialState n b a e A).done = false ->
        (grayChargedTailInitialState n b a e A).frozen.length
          < grayChargedAdvantageRoundCount q) := by
    dsimp [grayChargedTailInitialState]
    refine ⟨Nat.zero_le _, fun _ => ?_⟩
    simp only [grayChargedAdvantageRoundCount]
    unfold grayTailRoundCount
    have hq1 : 1 ≤ q + 1 := by omega
    have hsq : 1 ≤ (q + 1) ^ 2 := by
      simp [pow_two]
    have hlarge : 256 ≤ 256 * (q + 1) ^ 2 := by
      simpa using Nat.mul_le_mul_left 256 hsq
    omega
  refine ⟨hshape, rfl, ?_, ?_, hbound, ?_, ?_, ?_⟩
  · intro k hk
    simp [grayChargedTailInitialState] at hk
  · simp [grayChargedTailInitialState, grayHarvestSnapshot, grayHarvest_nil]
  · simp [grayChargedTailInitialState]
  · intro k hk
    simp [grayChargedTailInitialState] at hk
  · intro i j hi hj hij
    simp [grayChargedTailInitialState] at hj

/-- Freezing the round the controller closes at time `t`, and moving on to a fresh list of
distinct slots, keeps the charged tail state certified one tick later.  The round that is frozen
is the one the state itself determines: its index, server time, depth, slots, allocation and
unavailable region all come from `st`, so the client move it played is its only free datum. -/
lemma grayChargedTailCertified_freeze {n b q L e t : Nat}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    {st : GrayTailState n b}
    (hst : GrayChargedTailCertified q L e A sm t st)
    (hlimit : st.frozen.length < grayChargedAdvantageRoundCount q)
    (done : Bool) (move : FamilyClientMove)
    (hpGoal : grayChargedTailGoalAtB q e (grayTailRoundEps q L e st.frozen.length)
      (grayTailRoundDelta q L e st.frozen.length) st.slots.length st.unavailable move
        (grayTailLocalServerMove (grayTailRoundDelta q L e st.frozen.length) st.slots
          (sm t)) = true)
    (next : List (GrayTailSlot n b)) (hnext : next.Nodup)
    (hnextRound : forall s, s ∈ next ->
      s.2.2.val = st.frozen.length + 1)
    (anchoringSlots : List (GrayTailSlot n b))
    (history : FamilyGameHistory)
    (hdone_bound : done = false ->
      st.frozen.length + 1 < grayChargedAdvantageRoundCount q) :
    GrayChargedTailCertified q L e A sm (t + 1)
      ({ time := t + 1
         roundStart := t + 1
         done := done
         frozen := st.frozen ++
           [{ roundIndex := st.frozen.length
              serverTime := t
              epsDepth := grayTailRoundEps q L e st.frozen.length
              slots := st.slots
              move := move
              allocated := grayTailLocalAllocatedList
                (grayTailLocalServerMove (grayTailRoundDelta q L e st.frozen.length)
                  st.slots (sm t))
              unavailable := st.unavailable }]
         unavailable := A ++
           grayHarvest (grayTailRoundDelta q L e (st.frozen.length + 1)) next n (sm t)
         slots := next
         anchoringSlots := anchoringSlots
         history := history } : GrayTailState n b) := by
  set rd : GrayTailRound n b :=
    { roundIndex := st.frozen.length
      serverTime := t
      epsDepth := grayTailRoundEps q L e st.frozen.length
      slots := st.slots
      move := move
      allocated := grayTailLocalAllocatedList
        (grayTailLocalServerMove (grayTailRoundDelta q L e st.frozen.length)
          st.slots (sm t))
      unavailable := st.unavailable } with hrd
  have hpSlots : rd.slots = st.slots := by simp [hrd]
  have hpIndex : rd.roundIndex = st.frozen.length := by simp [hrd]
  have hpTime : rd.serverTime = t := by simp [hrd]
  have hpDepth : rd.epsDepth = grayTailRoundEps q L e rd.roundIndex := by simp [hrd]
  have hpUnavailable : rd.unavailable = st.unavailable := by simp [hrd]
  have hpAllocated : rd.allocated =
      grayTailLocalAllocatedList
        (grayTailLocalServerMove (rd.epsDepth + L) rd.slots (sm rd.serverTime)) := by
    simp only [hrd, grayTailRoundDelta]
  have hpGoal' : grayChargedTailGoalAtB q e rd.epsDepth (rd.epsDepth + L)
      rd.slots.length rd.unavailable rd.move
        (grayTailLocalServerMove (rd.epsDepth + L) rd.slots (sm rd.serverTime)) = true := by
    rw [hrd]; exact hpGoal
  have hpNodup : rd.slots.Nodup := by rw [hrd]; exact hst.shape.slots_nodup
  have hpRound : forall s, s ∈ rd.slots -> s.2.2.val = rd.roundIndex := by
    rw [hrd]; exact fun s hs => hst.shape.slots_round s hs
  have hbound_next : (st.frozen ++ [rd]).length <= grayChargedAdvantageRoundCount q ∧
      (done = false -> (st.frozen ++ [rd]).length < grayChargedAdvantageRoundCount q) := by
    rw [List.length_append, List.length_singleton]
    exact ⟨by omega, hdone_bound⟩
  refine ⟨grayTailShape_appendRound hst.shape (t + 1) (t + 1)
      done rd hpSlots _ next hnext hnextRound anchoringSlots history,
    rfl, ?_, ?_, hbound_next, ?_, ?_, ?_⟩
  · apply grayTailHarvestChain_append hst.frozen_chain
    rw [hpUnavailable, hpDepth, hpIndex, hpSlots]
    exact hst.unavailable_snap
  · simp only [List.getLast?_concat, Option.map_some, grayHarvestSnapshot,
      hpTime, List.length_append, List.length_singleton]
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · rcases hst.round_valid r hr with
        ⟨hindex, hdepth, htime, halloc, hgoal, hnodup, hround⟩
      refine ⟨?_, hdepth, ?_, halloc, hgoal, hnodup, hround⟩
      · simp only [List.length_append, List.length_singleton]
        omega
      · omega
    · have hrp : r = rd := by simpa using hr
      subst r
      refine ⟨?_, hpDepth, ?_, hpAllocated, hpGoal', hpNodup, hpRound⟩
      · simp only [List.length_append, List.length_singleton, hpIndex]
        omega
      · omega
  · intro k hk
    have hklen : k < st.frozen.length + 1 := by simpa using hk
    by_cases hkf : k < st.frozen.length
    · rw [List.getElem_append_left hkf]
      exact hst.frozen_index k hkf
    · have hke : k = st.frozen.length := by omega
      subst hke
      have hgetp : (st.frozen ++ [rd])[st.frozen.length]'hk = rd := by
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
      have hgetp : (st.frozen ++ [rd])[st.frozen.length]'hj = rd := by
        rw [List.getElem_append_right (Nat.le_refl _)]
        simp
      rw [hgetp, hpTime]
      have hmem : st.frozen[i]'hif ∈ st.frozen := List.getElem_mem hif
      exact (hst.round_valid _ hmem).2.2.1

/-- A charged tail step preserves the shape invariant of the state. -/
lemma grayChargedTailShape_step {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (st : GrayTailState n b) (sm : FamilyServerMove)
    (hst : GrayTailShape st) :
    GrayTailShape (grayChargedTailStep q L a e sigma A st sm) := by
  by_cases hd : st.done = true
  · simp only [grayChargedTailStep, grayTailWaitingB, Bool.false_eq_true,
      hd, ↓reduceIte]
    exact ⟨hst.frozen_nodup, hst.frozen_round_lt,
      hst.slots_nodup, hst.slots_round⟩
  · by_cases hs : st.slots.isEmpty = true
    · simp only [grayChargedTailStep, grayTailWaitingB, Bool.false_eq_true,
        hd, hs, ↓reduceIte]
      exact ⟨hst.frozen_nodup, hst.frozen_round_lt,
        hst.slots_nodup, hst.slots_round⟩
    · by_cases hg : grayChargedTailGoalAtB q e
        (grayTailRoundEps q L e st.frozen.length)
        (grayTailRoundDelta q L e st.frozen.length)
        st.slots.length st.unavailable
        (grayTailCurrentMove q L e sigma st)
        (grayTailLocalServerMove
          (grayTailRoundDelta q L e st.frozen.length) st.slots sm) = true
      · simp only [grayChargedTailStep, grayTailWaitingB,
          Bool.false_eq_true, hd, hs, hg, ↓reduceIte]
        apply grayTailShape_freeze hst
        · exact grayTailNextSlots_nodup _ _ _ _ _ _ _
        · intro s hs'
          simpa using grayTailNextSlots_round hs'
      · simp only [grayChargedTailStep, grayTailWaitingB,
          Bool.false_eq_true, hd, hs, hg, ↓reduceIte]
        exact ⟨hst.frozen_nodup, hst.frozen_round_lt,
          hst.slots_nodup, hst.slots_round⟩

/-- A charged tail step preserves well-formedness of the round history. -/
lemma grayChargedTailHistoryOK_step {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (st : GrayTailState n b) (sm : FamilyServerMove)
    (hst : GrayTailHistoryOK q L e sigma st) :
    GrayTailHistoryOK q L e sigma
      (grayChargedTailStep q L a e sigma A st sm) := by
  by_cases hd : st.done = true
  · simp only [grayChargedTailStep, grayTailWaitingB, Bool.false_eq_true,
      hd, ↓reduceIte]
    exact hst
  · by_cases hs : st.slots.isEmpty = true
    · simp only [grayChargedTailStep, grayTailWaitingB, Bool.false_eq_true,
        hd, hs, ↓reduceIte]
      exact hst
    · by_cases hg : grayChargedTailGoalAtB q e
        (grayTailRoundEps q L e st.frozen.length)
        (grayTailRoundDelta q L e st.frozen.length)
        st.slots.length st.unavailable
        (grayTailCurrentMove q L e sigma st)
        (grayTailLocalServerMove
          (grayTailRoundDelta q L e st.frozen.length) st.slots sm) = true
      · simp [grayChargedTailStep, grayTailWaitingB, hd, hs, hg,
          GrayTailHistoryOK]
      · simpa [grayChargedTailStep, grayTailWaitingB, hd, hs, hg] using
          grayTailHistoryOK_append q L e sigma st hst _ _

/-- A charged tail step turns a certified state at time `t` into a certified state at time
`t + 1`. -/
lemma grayChargedTailCertified_step {n b q L a e t : Nat}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    {st : GrayTailState n b} (sigma : FamilyStrategyScheme)
    (hst : GrayChargedTailCertified q L e A sm t st) :
    GrayChargedTailCertified q L e A sm (t + 1)
      (grayChargedTailStep q L a e sigma A st (sm t)) := by
  have hrestate (done : Bool) (hdone_eq : done = st.done) (history : FamilyGameHistory) :
      GrayChargedTailCertified q L e A sm (t + 1)
        ({ time := st.time + 1
           roundStart := st.roundStart
           done := done
           frozen := st.frozen
           unavailable := st.unavailable
           slots := st.slots
           anchoringSlots := st.anchoringSlots
           history := history } : GrayTailState n b) := by
    have hbound : st.frozen.length <= grayChargedAdvantageRoundCount q ∧
        (done = false -> st.frozen.length < grayChargedAdvantageRoundCount q) := by
      refine ⟨hst.frozen_bound.1, fun hnotdone => ?_⟩
      subst done
      exact hst.frozen_bound.2 hnotdone
    refine ⟨?_, by simp [hst.time_eq], hst.frozen_chain,
      hst.unavailable_snap, hbound, ?_, hst.frozen_index,
      hst.frozen_chrono⟩
    · exact ⟨hst.shape.frozen_nodup, hst.shape.frozen_round_lt,
        hst.shape.slots_nodup, hst.shape.slots_round⟩
    intro p hp
    rcases hst.round_valid p hp with
      ⟨hindex, hdepth, htime, halloc, hgoal, hnodup, hround⟩
    exact ⟨hindex, hdepth, by omega, halloc, hgoal, hnodup, hround⟩
  by_cases hd : st.done = true
  · simpa [grayChargedTailStep, grayTailWaitingB, hd] using
      hrestate st.done rfl st.history
  · by_cases hs : st.slots.isEmpty = true
    · simpa [grayChargedTailStep, grayTailWaitingB, hd, hs] using
        hrestate st.done rfl st.history
    · by_cases hg : grayChargedTailGoalAtB q e
        (grayTailRoundEps q L e st.frozen.length)
        (grayTailRoundDelta q L e st.frozen.length)
        st.slots.length st.unavailable
        (grayTailCurrentMove q L e sigma st)
        (grayTailLocalServerMove
          (grayTailRoundDelta q L e st.frozen.length)
          st.slots (sm t)) = true
      · have hlimit : st.frozen.length < grayChargedAdvantageRoundCount q :=
          hst.frozen_bound.2 (Bool.eq_false_of_not_eq_true hd)
        let p : GrayTailRound n b :=
          { roundIndex := List.length st.frozen
            serverTime := t
            epsDepth := grayTailRoundEps q L e (List.length st.frozen)
            slots := st.slots
            move := grayTailCurrentMove q L e sigma st
            allocated :=
              grayTailLocalAllocatedList (grayTailLocalServerMove (grayTailRoundDelta q L e
              (List.length st.frozen)) st.slots (sm t))
            unavailable := st.unavailable }
        let done :=
          grayTailGlobalQuarterB (grayChargedSourceCount a e) (grayTailNextSlots e
          (grayChargedSourceCount a e) (st.frozen ++ [p]).length (dyadicScale e - dyadicScale e / (6
          * halfAmplification q)) A (st.frozen ++ [p]) (sm t))
          || decide (grayChargedAdvantageRoundCount q <= (st.frozen ++ [p]).length)
        let candidates :=
          grayTailNextSlots e (grayChargedSourceCount a e) (st.frozen ++ [p]).length (dyadicScale e
          - dyadicScale e / (6 * halfAmplification q)) A (st.frozen ++ [p]) (sm t)
        have hdone_bound : done = false -> st.frozen.length + 1
          < grayChargedAdvantageRoundCount q := by
          intro hnext_not_done
          have htr := (Bool.or_eq_false_iff.mp hnext_not_done).2
          have hge := of_decide_eq_false htr
          rw [List.length_append, List.length_singleton] at hge
          omega
        have hstep : grayChargedTailStep q L a e sigma A st (sm t) =
          { time := t + 1
            roundStart := t + 1
            done := done
            frozen := st.frozen ++ [p]
            unavailable := A ++
              grayHarvest (grayTailRoundDelta q L e (st.frozen ++ [p]).length)
                candidates n (sm t)
            slots := candidates
            anchoringSlots := []
            history := ([], []) } := by
          dsimp [grayChargedTailStep, grayTailWaitingB, p, done, candidates]
          rw [show st.done = false from Bool.eq_false_of_not_eq_true hd]
          rw [show st.slots.isEmpty = false from Bool.eq_false_of_not_eq_true hs]
          rw [hst.time_eq]
          dsimp
          rw [hg]
          dsimp
        rw [hstep]
        rw [show (st.frozen ++ [p]).length = st.frozen.length + 1 by simp]
        exact grayChargedTailCertified_freeze hst hlimit done
          (grayTailCurrentMove q L e sigma st) hg
          candidates (grayTailNextSlots_nodup _ _ _ _ _ _ _)
          (fun s hs' => by
            have := grayTailNextSlots_round hs'
            rw [List.length_append, List.length_singleton] at this
            exact this)
          []
          ([], [])
          hdone_bound
      · simpa [grayChargedTailStep, grayTailWaitingB, hd, hs, hg] using
          hrestate st.done rfl
            (st.history.1 ++ [grayTailCurrentMove q L e sigma st],
              st.history.2 ++
                [grayTailLocalServerMove
                  (grayTailRoundDelta q L e st.frozen.length)
                  st.slots (sm t)])

/-- A charged tail step preserves the trace relation against the server play. -/
lemma grayChargedTailTrace_step {n b q L a e t : Nat}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    {st : GrayTailState n b} (sigma : FamilyStrategyScheme)
    (hst : GrayTailTrace q L e sm t st) :
    GrayTailTrace q L e sm (t + 1)
      (grayChargedTailStep q L a e sigma A st (sm t)) := by
  by_cases hd : st.done = true
  · have hterminal : (st.done || st.slots.isEmpty) = true := by simp [hd]
    simp only [grayChargedTailStep, grayTailWaitingB, Bool.false_eq_true,
      hd, ↓reduceIte]
    refine ⟨by simp [hst.time_eq], ?_, hst.servers_eq,
      hst.frozen_before, ?_⟩
    · intro hactive
      simp at hactive
    · intro _
      exact hst.terminal_empty hterminal
  · by_cases hs : st.slots.isEmpty = true
    · have hterminal : (st.done || st.slots.isEmpty) = true := by simp [hs]
      simp only [grayChargedTailStep, grayTailWaitingB, Bool.false_eq_true,
        hd, hs, ↓reduceIte]
      refine ⟨by simp [hst.time_eq], ?_, hst.servers_eq,
        hst.frozen_before, ?_⟩
      · intro hactive
        exact (hactive (by simp [hs])).elim
      · intro _
        exact hst.terminal_empty hterminal
    · have hactive : (st.done || st.slots.isEmpty) ≠ true := by
        simp [hd, hs]
      have hbefore : forall p, p ∈ st.frozen ->
          p.serverTime < st.time + 1 := by
        intro p hp
        have htime := hst.active_time hactive
        have hpStart := hst.frozen_before p hp
        rw [hst.time_eq]
        omega
      by_cases hg : grayChargedTailGoalAtB q e
          (grayTailRoundEps q L e st.frozen.length)
          (grayTailRoundDelta q L e st.frozen.length)
          st.slots.length st.unavailable
          (grayTailCurrentMove q L e sigma st)
          (grayTailLocalServerMove
            (grayTailRoundDelta q L e st.frozen.length)
            st.slots (sm t)) = true
      · simp only [grayChargedTailStep, grayTailWaitingB,
          Bool.false_eq_true, hd, hs, hg, ↓reduceIte]
        refine ⟨by simp [hst.time_eq], ?_, by simp, ?_, ?_⟩
        · intro _
          simp [hst.time_eq]
        · intro p hp
          rcases List.mem_append.mp hp with hp | hp
          · exact hbefore p hp
          · have hpEq : p =
                { roundIndex := st.frozen.length
                  serverTime := st.time
                  epsDepth := grayTailRoundEps q L e st.frozen.length
                  slots := st.slots
                  move := grayTailCurrentMove q L e sigma st
                  allocated :=
                    grayTailLocalAllocatedList
                      (grayTailLocalServerMove
                        (grayTailRoundDelta q L e st.frozen.length)
                        st.slots (sm t))
                  unavailable := st.unavailable } := by
                simpa using hp
            subst p
            simp [hst.time_eq]
        · intro _
          rfl
      · simp only [grayChargedTailStep, grayTailWaitingB,
          Bool.false_eq_true, hd, hs, hg, ↓reduceIte]
        refine ⟨by simp [hst.time_eq], ?_, ?_, hst.frozen_before, ?_⟩
        · intro _
          have htime := hst.active_time hactive
          simp only [List.length_append, List.length_singleton]
          omega
        · simp only [List.length_append, List.length_singleton]
          change
            st.history.2 ++
                [grayTailLocalServerMove
                  (grayTailRoundDelta q L e st.frozen.length)
                  st.slots (sm t)] =
              List.ofFn
                (fun j : Fin (st.history.2.length + 1) =>
                  grayTailLocalServerMove
                    (grayTailRoundDelta q L e st.frozen.length)
                    st.slots (sm (st.roundStart + j.val)))
          have hdecomp :
              List.ofFn
                  (fun j : Fin (st.history.2.length + 1) =>
                    grayTailLocalServerMove
                      (grayTailRoundDelta q L e st.frozen.length)
                      st.slots (sm (st.roundStart + j.val))) =
                (List.ofFn
                  (fun j : Fin st.history.2.length =>
                    grayTailLocalServerMove
                      (grayTailRoundDelta q L e st.frozen.length)
                      st.slots (sm (st.roundStart + j.val)))) ++
                  [grayTailLocalServerMove
                    (grayTailRoundDelta q L e st.frozen.length)
                    st.slots
                    (sm (st.roundStart + st.history.2.length))] := by
            simpa only using
              (grayTail_ofFn_succ_last_nat st.history.2.length
                (fun u =>
                  grayTailLocalServerMove
                    (grayTailRoundDelta q L e st.frozen.length)
                    st.slots (sm (st.roundStart + u))))
          rw [hdecomp, <- hst.servers_eq]
          congr 2
          rw [hst.active_time hactive]
        · intro hterminal
          simp [hs] at hterminal

/-- The charged tail state after replaying the first `t` moves of the server play `sm`. -/
def grayChargedTailStateAt {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (t : Nat) : GrayTailState n b :=
  grayChargedTailFold q L a e sigma A (grayTailServerPrefix sm t)

/-- The tail state at time `t + 1` is one charged tail step applied to the state at time `t`. -/
lemma grayChargedTailStateAt_succ {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (t : Nat) :
    grayChargedTailStateAt (n := n) (b := b) q L a e sigma A sm (t + 1) =
      grayChargedTailStep q L a e sigma A
        (grayChargedTailStateAt q L a e sigma A sm t) (sm t) := by
  simp [grayChargedTailStateAt, grayChargedTailFold,
    grayTailServerPrefix_succ]

/-- Every state of a charged tail run is certified. -/
lemma grayChargedTailCertified_stateAt {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (t : Nat) :
    GrayChargedTailCertified q L e A sm t
      (grayChargedTailStateAt (n := n) (b := b) q L a e sigma A sm t) := by
  induction t with
  | zero => exact grayChargedTailCertified_initial q L a e A sm
  | succ t ih =>
      rw [grayChargedTailStateAt_succ]
      exact grayChargedTailCertified_step sigma ih

/-- Every state of a charged tail run satisfies the shape invariant. -/
lemma grayChargedTailShape_stateAt {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (t : Nat) :
    GrayTailShape
      (grayChargedTailStateAt (n := n) (b := b)
        q L a e sigma A sm t) :=
  (grayChargedTailCertified_stateAt q L a e sigma A sm t).shape

/-- Every state of a charged tail run carries a well-formed history. -/
lemma grayChargedTailHistoryOK_stateAt {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (t : Nat) :
    GrayTailHistoryOK q L e sigma
      (grayChargedTailStateAt (n := n) (b := b)
        q L a e sigma A sm t) := by
  induction t with
  | zero =>
      exact grayTailHistoryOK_empty q L e sigma 0 0 false [] A
        (grayTailSlots n b (grayChargedSourceCount a e) 0) []
  | succ t ih =>
      rw [grayChargedTailStateAt_succ]
      exact grayChargedTailHistoryOK_step q L a e sigma A _ (sm t) ih

/-- Every state of a charged tail run is traced against the server play it was replayed from. -/
lemma grayChargedTailTrace_stateAt {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (t : Nat) :
    GrayTailTrace q L e sm t
      (grayChargedTailStateAt (n := n) (b := b)
        q L a e sigma A sm t) := by
  induction t with
  | zero =>
      refine ⟨rfl, ?_, ?_, ?_, ?_⟩
      · simp [grayChargedTailStateAt, grayChargedTailFold,
          grayChargedTailInitialState]
      · simp [grayChargedTailStateAt, grayChargedTailFold,
          grayChargedTailInitialState]
      · simp [grayChargedTailStateAt, grayChargedTailFold,
          grayChargedTailInitialState]
      · simp [grayChargedTailStateAt, grayChargedTailFold,
          grayChargedTailInitialState]
  | succ t ih =>
      rw [grayChargedTailStateAt_succ]
      exact grayChargedTailTrace_step sigma ih

end Kolmogorov
