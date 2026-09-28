import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailController
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailReplay.Invariants

/-!
# Replaying the tail controller

The state of the tail controller after a history is obtained by folding the step function
(`grayTailFold_append_one`), and the invariants of the previous module travel along that fold:
the shape, replay, trace and certification invariants each hold initially and are preserved by one
step (`grayTailShape_step`, `grayTailHistoryOK_step`, `grayTailTrace_initial`,
`grayTailTrace_step`, `grayTailCertified_step`). The consequences used downstream describe the
entry list of a state: its keys are exactly the frozen and current slots
(`map_fst_grayTailFrozenEntries`, `map_fst_grayTailEntries`) and, under the shape invariant, have
no repetitions, so lookups in it are unambiguous (`grayTailEntries_keys_nodup`).
-/

namespace Kolmogorov

/-- One controller step preserves the shape invariant. -/
lemma grayTailShape_step {n b : ℕ}
    (q L a e : ℕ) (sigma : FamilyStrategyScheme) (A : Allocation)
    (st : GrayTailState n b) (sm : FamilyServerMove)
    (hst : GrayTailShape st) :
    GrayTailShape (grayTailStep q L a e sigma A st sm) := by
  by_cases hw : grayTailWaitingB st = true
  · by_cases ha : grayTailAllAnchoredB e A st.anchoringSlots sm = true
    · simp only [grayTailStep, hw, ha, ↓reduceIte]
      exact ⟨hst.frozen_nodup, hst.frozen_round_lt,
        by simp, by simp⟩
    · simp only [grayTailStep, Bool.false_eq_true, hw, ha, ↓reduceIte]
      exact ⟨hst.frozen_nodup, hst.frozen_round_lt,
        hst.slots_nodup, hst.slots_round⟩
  · by_cases hd : st.done = true
    · simp only [grayTailStep, Bool.false_eq_true, hw, hd, ↓reduceIte]
      exact ⟨hst.frozen_nodup, hst.frozen_round_lt,
        hst.slots_nodup, hst.slots_round⟩
    · by_cases hs : st.slots.isEmpty = true
      · simp only [grayTailStep, Bool.false_eq_true, hw, hd, hs, ↓reduceIte]
        exact ⟨hst.frozen_nodup, hst.frozen_round_lt,
          hst.slots_nodup, hst.slots_round⟩
      · by_cases hg : familyRobustGrayGoalAtB (halfAmplification q)
          ((3 / 4 : ℚ) * dyadicScale (grayCallDepth q e))
          (grayTailRoundEps q L e st.frozen.length)
          (grayTailRoundDelta q L e st.frozen.length)
          st.slots.length st.unavailable
          (grayTailCurrentMove q L e sigma st)
          (grayTailLocalServerMove
            (grayTailRoundDelta q L e st.frozen.length) st.slots sm) = true
        · simp only [grayTailStep, Bool.false_eq_true, hw, hd, hs, hg, ↓reduceIte]
          apply grayTailShape_freeze hst
          · exact grayTailNextSlots_nodup _ _ _ _ _ _ _
          · intro s hs'
            simpa using grayTailNextSlots_round hs'
        · simp only [grayTailStep, Bool.false_eq_true, hw, hd, hs, hg, ↓reduceIte]
          exact ⟨hst.frozen_nodup, hst.frozen_round_lt,
            hst.slots_nodup, hst.slots_round⟩

/-- One controller step preserves the replay invariant. -/
lemma grayTailHistoryOK_step {n b : ℕ}
    (q L a e : ℕ) (sigma : FamilyStrategyScheme) (A : Allocation)
    (st : GrayTailState n b) (sm : FamilyServerMove)
    (hst : GrayTailHistoryOK q L e sigma st) :
    GrayTailHistoryOK q L e sigma
      (grayTailStep q L a e sigma A st sm) := by
  by_cases hw : grayTailWaitingB st = true
  · by_cases ha : grayTailAllAnchoredB e A st.anchoringSlots sm = true
    · simp [grayTailStep, hw, ha, GrayTailHistoryOK]
    · simp [grayTailStep, hw, ha, GrayTailHistoryOK]
  · by_cases hd : st.done = true
    · simpa [grayTailStep, hw, hd] using hst
    · by_cases hs : st.slots.isEmpty = true
      · simpa [grayTailStep, hw, hd, hs] using hst
      · by_cases hg : familyRobustGrayGoalAtB (halfAmplification q)
          ((3 / 4 : ℚ) * dyadicScale (grayCallDepth q e))
          (grayTailRoundEps q L e st.frozen.length)
          (grayTailRoundDelta q L e st.frozen.length)
          st.slots.length st.unavailable
          (grayTailCurrentMove q L e sigma st)
          (grayTailLocalServerMove
            (grayTailRoundDelta q L e st.frozen.length) st.slots sm) = true
        · simp [grayTailStep, hw, hd, hs, hg, GrayTailHistoryOK]
        · simpa [grayTailStep, hw, hd, hs, hg] using
            grayTailHistoryOK_append q L e sigma st hst _ _

/-- The initial state satisfies the trace invariant at time zero. -/
lemma grayTailTrace_initial {n b : ℕ}
    (q L a e : ℕ) (A : Allocation)
    (sm : ℕ → FamilyServerMove) :
    GrayTailTrace q L e sm 0
      (grayTailInitialState n b a e A) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · simp [grayTailInitialState]
  · simp [grayTailInitialState]
  · simp [grayTailInitialState]
  · simp [grayTailInitialState]

/-- One controller step preserves the trace invariant. -/
lemma grayTailTrace_step {n b q L a e t : ℕ}
    {A : Allocation} {sm : ℕ → FamilyServerMove}
    {st : GrayTailState n b} (sigma : FamilyStrategyScheme)
    (hst : GrayTailTrace q L e sm t st) :
    GrayTailTrace q L e sm (t + 1)
      (grayTailStep q L a e sigma A st (sm t)) := by
  by_cases hw : grayTailWaitingB st = true
  · simp [grayTailWaitingB] at hw
  · by_cases hd : st.done = true
    · have hterminal : (st.done || st.slots.isEmpty) = true := by
        simp [hd]
      simp only [grayTailStep, Bool.false_eq_true, hw, hd, ↓reduceIte]
      refine ⟨by simp [hst.time_eq], ?_, hst.servers_eq,
        hst.frozen_before, ?_⟩
      · intro hactive
        simp at hactive
      · intro _
        exact hst.terminal_empty hterminal
    · by_cases hs : st.slots.isEmpty = true
      · have hterminal : (st.done || st.slots.isEmpty) = true := by
          simp [hs]
        simp only [grayTailStep, Bool.false_eq_true, hw, hd, hs, ↓reduceIte]
        refine ⟨by simp [hst.time_eq], ?_, hst.servers_eq,
          hst.frozen_before, ?_⟩
        · intro hactive
          exact (hactive (by simp [hs])).elim
        · intro _
          exact hst.terminal_empty hterminal
      · have hactive :
          (st.done || st.slots.isEmpty) ≠ true := by
          simp [hd, hs]
        have hbefore :
            ∀ p ∈ st.frozen, p.serverTime < st.time + 1 := by
          intro p hp
          have htime := hst.active_time hactive
          have hpStart := hst.frozen_before p hp
          rw [hst.time_eq]
          omega
        by_cases hg : familyRobustGrayGoalAtB (halfAmplification q)
            ((3 / 4 : ℚ) * dyadicScale (grayCallDepth q e))
            (grayTailRoundEps q L e st.frozen.length)
            (grayTailRoundDelta q L e st.frozen.length)
            st.slots.length st.unavailable
            (grayTailCurrentMove q L e sigma st)
            (grayTailLocalServerMove
              (grayTailRoundDelta q L e st.frozen.length)
              st.slots (sm t)) = true
        · simp only [grayTailStep, Bool.false_eq_true, hw, hd, hs, hg,
            ↓reduceIte]
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
        · simp only [grayTailStep, Bool.false_eq_true, hw, hd, hs, hg,
            ↓reduceIte]
          refine ⟨by simp [hst.time_eq], ?_, ?_,
            hst.frozen_before, ?_⟩
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
            rw [hdecomp, ← hst.servers_eq]
            congr 2
            rw [hst.active_time hactive]
          · intro hterminal
            simp [hs] at hterminal
/-- One controller step preserves the certification invariant. -/
lemma grayTailCertified_step {n b q L a e t : ℕ}
    {A : Allocation} {sm : ℕ → FamilyServerMove}
    {st : GrayTailState n b} (sigma : FamilyStrategyScheme)
    (hst : GrayTailCertified q L e A sm t st) :
    GrayTailCertified q L e A sm (t + 1)
      (grayTailStep q L a e sigma A st (sm t)) := by
  have hrestate (roundStart : ℕ) (done : Bool)
      (slots : List (GrayTailSlot n b))
      (hslotsNodup : slots.Nodup)
      (hslotsRound :
        ∀ s ∈ slots, s.2.2.val = st.frozen.length)
      (history : FamilyGameHistory) :
      GrayTailCertified q L e A sm (t + 1)
        ({ time := st.time + 1
           roundStart := roundStart
           done := done
           frozen := st.frozen
           unavailable := st.unavailable
           slots := slots
           anchoringSlots := st.anchoringSlots
           history := history } : GrayTailState n b) := by
    refine ⟨?_, by simp [hst.time_eq], hst.frozen_chain,
      hst.unavailable_eq, ?_⟩
    · exact ⟨hst.shape.frozen_nodup, hst.shape.frozen_round_lt,
        hslotsNodup, hslotsRound⟩
    · intro p hp
      rcases hst.round_valid p hp with
        ⟨hindex, hdepth, htime, halloc, hgoal, hnodup, hround⟩
      exact ⟨hindex, hdepth, by omega, halloc, hgoal, hnodup, hround⟩
  have htick (done : Bool) (history : FamilyGameHistory) :=
    hrestate st.roundStart done st.slots hst.shape.slots_nodup
      hst.shape.slots_round history
  by_cases hw : grayTailWaitingB st = true
  · by_cases ha :
        grayTailAllAnchoredB e A st.anchoringSlots (sm t) = true
    · simpa [grayTailStep, hw, ha] using
        hrestate (st.time + 1) true [] (by simp) (by simp) ([], [])
    · simpa [grayTailStep, hw, ha] using
        hrestate (st.time + 1) st.done st.slots hst.shape.slots_nodup
          hst.shape.slots_round ([], [])
  · by_cases hd : st.done = true
    · simpa [grayTailStep, hw, hd] using htick st.done st.history
    · by_cases hs : st.slots.isEmpty = true
      · simpa [grayTailStep, hw, hd, hs] using htick st.done st.history
      · by_cases hg : familyRobustGrayGoalAtB (halfAmplification q)
          ((3 / 4 : ℚ) * dyadicScale (grayCallDepth q e))
          (grayTailRoundEps q L e st.frozen.length)
          (grayTailRoundDelta q L e st.frozen.length)
          st.slots.length st.unavailable
          (grayTailCurrentMove q L e sigma st)
          (grayTailLocalServerMove
            (grayTailRoundDelta q L e st.frozen.length)
            st.slots (sm t)) = true
        · simp only [grayTailStep, Bool.false_eq_true, hw, hd, hs, hg,
            ↓reduceIte, hst.time_eq]
          apply grayTailCertified_freeze hst
          · rfl
          · rfl
          · simp
          · rfl
          · simp [grayTailRoundDelta]
          · rfl
          · simpa [grayTailRoundDelta, hst.time_eq]
          · exact hst.shape.slots_nodup
          · intro s hs'
            exact hst.shape.slots_round s hs'
          · exact grayTailNextSlots_nodup _ _ _ _ _ _ _
          · intro s hs'
            simpa using grayTailNextSlots_round hs'
        · simpa [grayTailStep, hw, hd, hs, hg] using
            htick st.done
              (st.history.1 ++ [grayTailCurrentMove q L e sigma st],
                st.history.2 ++
                  [grayTailLocalServerMove
                    (grayTailRoundDelta q L e st.frozen.length)
                    st.slots (sm t)])

/-- Folding the controller over a history with one more move is one step applied to the previous
fold. -/
lemma grayTailFold_append_one {n b : ℕ}
    (q L a e : ℕ) (sigma : FamilyStrategyScheme) (A : Allocation)
    (hs : List FamilyServerMove) (s : FamilyServerMove) :
    grayTailFold (n := n) (b := b) q L a e sigma A (hs ++ [s]) =
      grayTailStep q L a e sigma A
        (grayTailFold q L a e sigma A hs) s := by
  simp [grayTailFold]

/-- The list of the first `t` moves of a server play. -/
def grayTailServerPrefix (sm : ℕ → FamilyServerMove) (t : ℕ) :
    List FamilyServerMove :=
  List.ofFn fun i : Fin t => sm i.val

/-- The empty prefix of a server play is the empty list. -/
@[simp] lemma grayTailServerPrefix_zero (sm : ℕ → FamilyServerMove) :
    grayTailServerPrefix sm 0 = [] := rfl

/-- The prefix of length `t + 1` is the prefix of length `t` followed by the move at time `t`. -/
lemma grayTailServerPrefix_succ (sm : ℕ → FamilyServerMove) (t : ℕ) :
    grayTailServerPrefix sm (t + 1) = grayTailServerPrefix sm t ++ [sm t] := by
  exact List.ofFn_succ_last

/-- Controller state after the first `t` moves of a fixed outer server play. -/
def grayTailStateAt {n b : ℕ}
    (q L a e : ℕ) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : ℕ → FamilyServerMove) (t : ℕ) : GrayTailState n b :=
  grayTailFold q L a e sigma A (grayTailServerPrefix sm t)

/-- At time zero the controller is in its initial state. -/
@[simp] lemma grayTailStateAt_zero {n b : ℕ}
    (q L a e : ℕ) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : ℕ → FamilyServerMove) :
    grayTailStateAt (n := n) (b := b) q L a e sigma A sm 0 =
      grayTailInitialState n b a e A := rfl

/-- The state at time `t + 1` is one step from the state at time `t`. -/
lemma grayTailStateAt_succ {n b : ℕ}
    (q L a e : ℕ) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : ℕ → FamilyServerMove) (t : ℕ) :
    grayTailStateAt (n := n) (b := b) q L a e sigma A sm (t + 1) =
      grayTailStep q L a e sigma A
        (grayTailStateAt q L a e sigma A sm t) (sm t) := by
  rw [grayTailStateAt, grayTailServerPrefix_succ,
    grayTailFold_append_one,
    grayTailStateAt]

/-- Once the number of frozen rounds reaches the round budget the controller is flagged done. -/
lemma grayTail_done_of_roundCount_stateAt_core
    {n b q L a e t : ℕ} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : ℕ → FamilyServerMove}
    (hcount : grayTailRoundCount q ≤
      (grayTailStateAt (n := n) (b := b)
        q L a e sigma A sm t).frozen.length) :
    (grayTailStateAt (n := n) (b := b)
      q L a e sigma A sm t).done = true := by
  induction t with
  | zero =>
      simp [grayTailStateAt, grayTailServerPrefix, grayTailFold,
        grayTailInitialState, grayTailRoundCount] at hcount
  | succ t ih =>
      rw [grayTailStateAt_succ] at hcount ⊢
      let st := grayTailStateAt (n := n) (b := b)
        q L a e sigma A sm t
      have ihst : grayTailRoundCount q ≤ st.frozen.length →
          st.done = true := by
        simpa [st] using ih
      change grayTailRoundCount q ≤
        (grayTailStep q L a e sigma A st (sm t)).frozen.length at hcount
      change (grayTailStep q L a e sigma A st (sm t)).done = true
      by_cases hw : grayTailWaitingB st = true
      · by_cases ha :
          grayTailAllAnchoredB e A st.anchoringSlots (sm t) = true
        · simp [grayTailStep, hw, ha]
        · have hprev : grayTailRoundCount q ≤ st.frozen.length := by
            simpa [grayTailStep, hw, ha] using hcount
          have hdone := ihst hprev
          simp [grayTailStep, hw, ha, hdone]
      · by_cases hd : st.done = true
        · simp [grayTailStep, hw, hd]
        · by_cases hs : st.slots.isEmpty = true
          · have hprev : grayTailRoundCount q ≤ st.frozen.length := by
              simpa [grayTailStep, hw, hd, hs] using hcount
            exact (hd (ihst hprev)).elim
          · by_cases hg : familyRobustGrayGoalAtB (halfAmplification q)
              ((3 / 4 : ℚ) * dyadicScale (grayCallDepth q e))
              (grayTailRoundEps q L e st.frozen.length)
              (grayTailRoundDelta q L e st.frozen.length)
              st.slots.length st.unavailable
              (grayTailCurrentMove q L e sigma st)
              (grayTailLocalServerMove
                (grayTailRoundDelta q L e st.frozen.length)
                st.slots (sm t)) = true
            · have hnext : grayTailRoundCount q ≤
                  st.frozen.length + 1 := by
                simpa [grayTailStep, hw, hd, hs, hg] using hcount
              simp [grayTailStep, hw, hd, hs, hg, hnext]
            · have hprev : grayTailRoundCount q ≤ st.frozen.length := by
                simpa [grayTailStep, hw, hd, hs, hg] using hcount
              exact (hd (ihst hprev)).elim

/-- Folding the controller over any history preserves the shape invariant. -/
lemma grayTailShape_fold {n b : ℕ}
    (q L a e : ℕ) (sigma : FamilyStrategyScheme) (A : Allocation)
    (history : List FamilyServerMove) :
    GrayTailShape (grayTailFold (n := n) (b := b)
      q L a e sigma A history) := by
  induction history using List.reverseRecOn with
  | nil => exact grayTailShape_initial n b a e A
  | append_singleton history sm ih =>
      rw [grayTailFold_append_one]
      exact grayTailShape_step q L a e sigma A _ sm ih

/-- The state at every time satisfies the shape invariant. -/
lemma grayTailShape_stateAt {n b : ℕ}
    (q L a e : ℕ) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : ℕ → FamilyServerMove) (t : ℕ) :
    GrayTailShape
      (grayTailStateAt (n := n) (b := b) q L a e sigma A sm t) :=
  grayTailShape_fold q L a e sigma A _

/-- The state at every time satisfies the certification invariant. -/
lemma grayTailCertified_stateAt {n b : ℕ}
    (q L a e : ℕ) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : ℕ → FamilyServerMove) (t : ℕ) :
    GrayTailCertified q L e A sm t
      (grayTailStateAt (n := n) (b := b) q L a e sigma A sm t) := by
  induction t with
  | zero =>
      exact grayTailCertified_initial q L a e A sm
  | succ t ih =>
      rw [grayTailStateAt_succ]
      exact grayTailCertified_step sigma ih

/-- The state at every time satisfies the replay invariant. -/
lemma grayTailHistoryOK_stateAt {n b : ℕ}
    (q L a e : ℕ) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : ℕ → FamilyServerMove) (t : ℕ) :
    GrayTailHistoryOK q L e sigma
      (grayTailStateAt (n := n) (b := b)
        q L a e sigma A sm t) := by
  induction t with
  | zero =>
      exact grayTailHistoryOK_empty q L e sigma 0 0 false [] A
        (grayTailSlots n b (2 ^ (e - a)) 0)
        []
  | succ t ih =>
      rw [grayTailStateAt_succ]
      exact grayTailHistoryOK_step q L a e sigma A _ (sm t) ih

/-- The state at every time satisfies the trace invariant. -/
lemma grayTailTrace_stateAt {n b : ℕ}
    (q L a e : ℕ) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : ℕ → FamilyServerMove) (t : ℕ) :
    GrayTailTrace q L e sm t
      (grayTailStateAt (n := n) (b := b)
        q L a e sigma A sm t) := by
  induction t with
  | zero =>
      exact grayTailTrace_initial q L a e A sm
  | succ t ih =>
      rw [grayTailStateAt_succ]
      exact grayTailTrace_step sigma ih

/-- Frozen and current slots together have no repetitions. -/
lemma GrayTailShape.allSlots_nodup {n b : ℕ}
    {st : GrayTailState n b} (hst : GrayTailShape st) :
    (grayTailFrozenSlots st.frozen ++ st.slots).Nodup := by
  rw [List.nodup_append]
  refine ⟨hst.frozen_nodup, hst.slots_nodup, ?_⟩
  intro s hs t ht hEq
  have hslt := hst.frozen_round_lt s hs
  have hteq := hst.slots_round t ht
  rw [hEq, hteq] at hslt
  omega

/-- The entry list built from a slot list has exactly those slots as keys. -/
lemma map_fst_grayTailSlotEntries {n b : ℕ}
    (slots : List (GrayTailSlot n b)) (move : FamilyClientMove) :
    (grayTailSlotEntries slots move).map Prod.fst = slots := by
  apply List.ext_get
  · simp [grayTailSlotEntries]
  · intro i hleft hright
    simp [grayTailSlotEntries]

/-- The entry list built from the frozen rounds has exactly the frozen slots as keys. -/
lemma map_fst_grayTailFrozenEntries {n b : ℕ}
    (frozen : GrayTailFrozen n b) :
    (grayTailFrozenEntries frozen).map Prod.fst =
      grayTailFrozenSlots frozen := by
  induction frozen with
  | nil => rfl
  | cons p frozen ih =>
      simp only [grayTailFrozenEntries, grayTailFrozenSlots,
        List.flatMap_cons, List.map_append]
      rw [map_fst_grayTailSlotEntries]
      congr 1

/-- The full entry list has exactly the frozen and current slots as keys. -/
lemma map_fst_grayTailEntries {n b : ℕ}
    (frozen : GrayTailFrozen n b)
    (slots : List (GrayTailSlot n b)) (move : FamilyClientMove) :
    (grayTailEntries frozen slots move).map Prod.fst =
      grayTailFrozenSlots frozen ++ slots := by
  simp [grayTailEntries, map_fst_grayTailFrozenEntries,
    map_fst_grayTailSlotEntries]

/-- Under the shape invariant the keys of the entry list have no repetitions, so lookups are
unambiguous. -/
lemma grayTailEntries_keys_nodup {n b : ℕ}
    {st : GrayTailState n b} (hst : GrayTailShape st)
    (move : FamilyClientMove) :
    ((grayTailEntries st.frozen st.slots move).map Prod.fst).Nodup := by
  rw [map_fst_grayTailEntries]
  exact hst.allSlots_nodup

end Kolmogorov
