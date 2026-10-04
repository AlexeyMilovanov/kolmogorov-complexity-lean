import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Shape
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedTailReplay

/-!
# V2 block certificate (Reading C)

The wide-block analogue of `GrayChargedTailCertified`.  Three clauses differ:
the shape is `GrayBlockTailShape`, the per-round acceptance goal is
`grayChargedBlockGoalAtB` (α-depth `ε_r`), and the round's slot invariant is
`grayInAdvBlock` (grandson in the round's block range) instead of
`grandson = roundIndex`.  Everything else — the per-round snapshot harvest
chain, the frozen bound, the chronology, and the position/index link — is
identical to the committed certificate.
-/

namespace Kolmogorov

/-- The invariants a block tail state carries at time `t`: its block shape and clock, the harvest
chain of its frozen rounds, the snapshot of the unavailable set, the round budget, and for
each frozen round its index, depth, server time, allocation, met block goal and distinct slots
inside its adversary block, with indices and server times increasing. -/
structure GrayChargedBlockTailCertified {n b : Nat}
    (q L e : Nat) (A : Allocation) (sm : Nat -> FamilyServerMove)
    (t : Nat) (st : GrayTailState n b) : Prop where
  shape : GrayBlockTailShape q L st
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
    grayChargedBlockGoalAtB q L e p.roundIndex
      p.slots.length p.unavailable p.move
        (grayTailLocalServerMove (p.epsDepth + L) p.slots
          (sm p.serverTime)) = true ∧
    p.slots.Nodup ∧
    forall s, s ∈ p.slots -> grayInAdvBlock q L p.roundIndex s.2.2.val
  frozen_index : forall k, forall hk : k < st.frozen.length,
    (st.frozen[k]'hk).roundIndex = k
  frozen_chrono : forall i j, forall hi : i < st.frozen.length,
    forall hj : j < st.frozen.length, i < j ->
      (st.frozen[i]'hi).serverTime < (st.frozen[j]'hj).serverTime

/-- The V2 initial state carries the block certificate at time 0. -/
lemma grayChargedBlockTailCertified_initial {n b : Nat}
    (q L a e : Nat) (A : Allocation) (sm : Nat -> FamilyServerMove) :
    GrayChargedBlockTailCertified q L e A sm 0
      (grayChargedBlockTailInitialState n b a e q L A) := by
  have hbound : (grayChargedBlockTailInitialState n b a e q L A).frozen.length
        <= grayChargedAdvantageRoundCount q ∧
      ((grayChargedBlockTailInitialState n b a e q L A).done = false ->
        (grayChargedBlockTailInitialState n b a e q L A).frozen.length
          < grayChargedAdvantageRoundCount q) := by
    dsimp [grayChargedBlockTailInitialState]
    exact ⟨Nat.zero_le _, fun _ => grayChargedAdvantageRoundCount_pos q⟩
  refine ⟨grayBlockTailShape_initial n b a e q L A, rfl, ?_, ?_, hbound, ?_, ?_, ?_⟩
  · intro k hk
    simp [grayChargedBlockTailInitialState] at hk
  · simp [grayChargedBlockTailInitialState, grayHarvestSnapshot, grayHarvest_nil]
  · intro p hp
    simp [grayChargedBlockTailInitialState] at hp
  · intro k hk
    simp [grayChargedBlockTailInitialState] at hk
  · intro i j hi hj hij
    simp [grayChargedBlockTailInitialState] at hj

/-- Freeze one accepted wide-block advantage round into the V2 certificate. -/
lemma grayChargedBlockTailCertified_freeze {n b q L e t : Nat}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    {st : GrayTailState n b}
    (hst : GrayChargedBlockTailCertified q L e A sm t st)
    (hlimit : st.frozen.length < grayChargedAdvantageRoundCount q)
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
    (hpGoal : grayChargedBlockGoalAtB q L e p.roundIndex
      p.slots.length p.unavailable p.move
        (grayTailLocalServerMove (p.epsDepth + L) p.slots
          (sm p.serverTime)) = true)
    (hpNodup : p.slots.Nodup)
    (hpRound : forall s, s ∈ p.slots -> grayInAdvBlock q L p.roundIndex s.2.2.val)
    (next : List (GrayTailSlot n b)) (hnext : next.Nodup)
    (hnextRound : forall s, s ∈ next ->
      grayInAdvBlock q L (st.frozen.length + 1) s.2.2.val)
    (anchoringSlots : List (GrayTailSlot n b))
    (history : FamilyGameHistory)
    (hdone_bound : done = false ->
      (st.frozen ++ [p]).length < grayChargedAdvantageRoundCount q) :
    GrayChargedBlockTailCertified q L e A sm (t + 1)
      ({ time := t + 1
         roundStart := t + 1
         done := done
         frozen := st.frozen ++ [p]
         unavailable := A ++
           grayHarvest (grayTailRoundDelta q L e (st.frozen ++ [p]).length)
             next n (sm t)
         slots := next
         anchoringSlots := anchoringSlots
         history := history } : GrayTailState n b) := by
  have hbound_next : (st.frozen ++ [p]).length <= grayChargedAdvantageRoundCount q ∧
      (done = false -> (st.frozen ++ [p]).length < grayChargedAdvantageRoundCount q) := by
    refine ⟨?_, hdone_bound⟩
    rw [List.length_append, List.length_singleton]
    omega
  refine ⟨grayBlockTailShape_freeze hst.shape (t + 1) (t + 1)
      done p hpSlots next hnext hnextRound anchoringSlots history _,
    rfl, ?_, ?_, hbound_next, ?_, ?_, ?_⟩
  · apply grayTailHarvestChain_append hst.frozen_chain
    rw [hpUnavailable, hpDepth, hpIndex, hpSlots]
    exact hst.unavailable_snap
  · simp only [List.getLast?_concat, Option.map_some, grayHarvestSnapshot,
      hpTime]
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
      exact (hst.round_valid _ hmem).2.2.1

/-- **The V2 certificate is preserved by the wide-block step.** -/
lemma grayChargedBlockTailCertified_step {n b q L a e t : Nat}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    {st : GrayTailState n b} (sigma : FamilyStrategyScheme)
    (hst : GrayChargedBlockTailCertified q L e A sm t st) :
    GrayChargedBlockTailCertified q L e A sm (t + 1)
      (grayChargedBlockTailStep q L a e sigma A st (sm t)) := by
  have hrestate (done : Bool) (hdone_eq : done = st.done) (history : FamilyGameHistory) :
      GrayChargedBlockTailCertified q L e A sm (t + 1)
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
    · exact ⟨hst.shape.frozen_nodup, hst.shape.frozen_round_range,
        hst.shape.slots_nodup, hst.shape.slots_range⟩
    intro p hp
    rcases hst.round_valid p hp with
      ⟨hindex, hdepth, htime, halloc, hgoal, hnodup, hround⟩
    exact ⟨hindex, hdepth, by omega, halloc, hgoal, hnodup, hround⟩
  by_cases hd : st.done = true
  · simpa [grayChargedBlockTailStep, grayTailWaitingB, hd] using
      hrestate st.done rfl st.history
  · by_cases hs : st.slots.isEmpty = true
    · simpa [grayChargedBlockTailStep, grayTailWaitingB, hd, hs] using
        hrestate st.done rfl st.history
    · by_cases hg : grayChargedBlockGoalAtB q L e st.frozen.length
        st.slots.length st.unavailable
        (grayBlockCurrentMove q L e sigma st)
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
            move := grayBlockCurrentMove q L e sigma st
            allocated :=
              grayTailLocalAllocatedList (grayTailLocalServerMove (grayTailRoundDelta q L e
              (List.length st.frozen)) st.slots (sm t))
            unavailable := st.unavailable }
        let candidates :=
          grayBlockNextSlots q L e (grayChargedSourceCount a e) (st.frozen
          ++ [p]).length (dyadicScale e - dyadicScale e / (6 * halfAmplification q)) A (st.frozen
          ++ [p]) (sm t)
        let done :=
          grayTailGlobalQuarterB (grayChargedSourceCount a e) (grayTailNextSlots e
          (grayChargedSourceCount a e) (st.frozen ++ [p]).length (dyadicScale e - dyadicScale e / (6
          * halfAmplification q)) A (st.frozen ++ [p]) (sm t))
          || decide (grayChargedAdvantageRoundCount q <= (st.frozen ++ [p]).length)
        have hdone_bound : done = false -> (st.frozen ++ [p]).length
          < grayChargedAdvantageRoundCount q := by
          intro hnext_not_done
          have htr := (Bool.or_eq_false_iff.mp hnext_not_done).2
          have hge := of_decide_eq_false htr
          omega
        have hstep : grayChargedBlockTailStep q L a e sigma A st (sm t) =
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
          dsimp [grayChargedBlockTailStep, grayTailWaitingB, p, done, candidates]
          rw [show st.done = false from Bool.eq_false_of_not_eq_true hd]
          rw [show st.slots.isEmpty = false from Bool.eq_false_of_not_eq_true hs]
          rw [hst.time_eq]
          dsimp
          rw [hg]
          dsimp
        rw [hstep]
        exact grayChargedBlockTailCertified_freeze hst hlimit done p
          rfl rfl rfl (by dsimp [p]) (by dsimp [p, grayTailRoundDelta])
          rfl (by dsimp [p, grayTailRoundDelta]; exact hg)
          hst.shape.slots_nodup (fun s hs' => hst.shape.slots_range s hs')
          candidates (grayBlockNextSlots_nodup _ _ _ _ _ _ _ _ _)
          (fun s hs' => by
            have := grayBlockNextSlots_mem_range hs'
            simpa [List.length_append] using this)
          []
          ([], [])
          hdone_bound
      · simpa [grayChargedBlockTailStep, grayTailWaitingB, hd, hs, hg] using
          hrestate st.done rfl
            (st.history.1 ++ [grayBlockCurrentMove q L e sigma st],
              st.history.2 ++
                [grayTailLocalServerMove
                  (grayTailRoundDelta q L e st.frozen.length)
                  st.slots (sm t)])

/-- The V2 wide-block advantage state after `t` server rounds. -/
def grayChargedBlockTailStateAt {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (t : Nat) : GrayTailState n b :=
  grayChargedBlockTailFold q L a e sigma A (grayTailServerPrefix sm t)

/-- The block tail state at time `t + 1` is one block tail step applied to the state at time `t`. -/
lemma grayChargedBlockTailStateAt_succ {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (t : Nat) :
    grayChargedBlockTailStateAt (n := n) (b := b) q L a e sigma A sm (t + 1) =
      grayChargedBlockTailStep q L a e sigma A
        (grayChargedBlockTailStateAt q L a e sigma A sm t) (sm t) := by
  simp [grayChargedBlockTailStateAt, grayChargedBlockTailFold,
    grayTailServerPrefix_succ]

/-- **The V2 certificate holds at every stage of the wide-block run.** -/
lemma grayChargedBlockTailCertified_stateAt {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (t : Nat) :
    GrayChargedBlockTailCertified q L e A sm t
      (grayChargedBlockTailStateAt (n := n) (b := b) q L a e sigma A sm t) := by
  induction t with
  | zero => exact grayChargedBlockTailCertified_initial q L a e A sm
  | succ t ih =>
      rw [grayChargedBlockTailStateAt_succ]
      exact grayChargedBlockTailCertified_step sigma ih

/-- The V2 wide-block step preserves the source-son invariant. -/
lemma grayChargedBlockSourceInvariant_step {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (st : GrayTailState n b) (sm : FamilyServerMove)
    (hst : GrayTailSourceInvariant (grayChargedSourceCount a e) st) :
    GrayTailSourceInvariant (grayChargedSourceCount a e)
      (grayChargedBlockTailStep q L a e sigma A st sm) := by
  unfold grayChargedBlockTailStep
  simp only [grayTailWaitingB, Bool.false_eq_true, ite_false]
  split
  · exact ⟨hst.current, hst.frozen⟩
  · split
    · exact ⟨hst.current, hst.frozen⟩
    · split
      · constructor
        · intro s hs
          exact grayBlockNextSlots_source hs
        · intro p hp
          rcases List.mem_append.mp hp with hp | hp
          · exact hst.frozen p hp
          · simp only [List.mem_singleton] at hp
            subst p
            simpa using hst.current
      · exact ⟨hst.current, hst.frozen⟩

/-- The source-son invariant holds at every stage of the V2 run. -/
theorem grayChargedBlockSourceInvariant_stateAt {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (t : Nat) :
    GrayTailSourceInvariant (grayChargedSourceCount a e)
      (grayChargedBlockTailStateAt (n := n) (b := b) q L a e sigma A sm t) := by
  induction t with
  | zero =>
      refine ⟨?_, ?_⟩
      · intro s hs
        change s ∈ grayAdvBlockSlots n b (grayChargedSourceCount a e) q L 0 at hs
        exact (grayAdvBlockSlots_mem hs).1
      · intro p hp
        simp [grayChargedBlockTailStateAt, grayChargedBlockTailFold,
          grayChargedBlockTailInitialState] at hp
  | succ t ih =>
      rw [grayChargedBlockTailStateAt_succ]
      exact grayChargedBlockSourceInvariant_step q L a e sigma A _ (sm t) ih

end Kolmogorov
